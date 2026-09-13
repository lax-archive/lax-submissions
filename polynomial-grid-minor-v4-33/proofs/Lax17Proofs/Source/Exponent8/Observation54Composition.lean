import Lax17Proofs.Source.Exponent8.Observation54Recursive

namespace Lax17Proofs

/-!
# Composition of recursive slice refinements

This module formalizes Chuzhoy--Tan Section 5's phrase "by combining the
slicings".  A local refinement first supplies cuts on the retained rows of
one parent slice.  `ExtendedParentRefinement` records the result after those
cuts have been extended trivially across discarded rows.  The main theorem
then flattens refinements of an ordered, not necessarily consecutive,
selection of parent slices.

The first global cell absorbs the initial gap, the first cell of every later
selected parent absorbs the intervening gap, and the last global cell absorbs
the final gap.  All path localization statements remain strict.
-/

namespace SimpleGraph
namespace Exponent8

universe u

open Finset

namespace PathSlicing

variable {W : Type u} [Fintype W] [DecidableEq W]
variable {H : _root_.SimpleGraph W}
variable {Abar Bbar Sbar Tbar : Finset W}
variable {Rbar : PerfectPathPacking H Abar Bbar}
variable {Qbar : PathPacking H Sbar Tbar}
variable {M : ℕ}

/-- A local `f`-slicing of one parent slice after extending its cuts to all
global rows.  On retained rows these cuts come from the exact-support
Observation 5.4 graph; on discarded rows the first cut is the parent source
and every later cut is the parent target. -/
structure ExtendedParentRefinement
    (sigma : PathSlicing Rbar M) (Qbar : PathPacking H Sbar Tbar)
    (parent : Fin M) (f w : ℕ) where
  cut : Rbar.Index → Fin (f + 1) → W
  cut_mem_main :
    ∀ r t, cut r t ∈ (Rbar.path r).vertexSet
  cut_zero :
    ∀ r, cut r 0 = (sigma.sliceRowPath parent r).source
  cut_last :
    ∀ r,
      cut r (Fin.last f) = (sigma.sliceRowPath parent r).target
  cut_monotone :
    ∀ r ⦃s t : Fin (f + 1)⦄, s ≤ t →
      (Rbar.path r).Before (cut r s) (cut r t)
  cellPaths : Fin f → Finset Qbar.Index
  cell_card :
    ∀ j, w ≤ (cellPaths j).card
  cell_parent_localized :
    ∀ j, cellPaths j ⊆ sigma.pathsInSlice Qbar parent
  cell_strict_localized :
    ∀ j q, q ∈ cellPaths j →
      ∀ r v,
        v ∈ (Qbar.path q).vertexSet →
        v ∈ (Rbar.path r).vertexSet →
        (Rbar.path r).Before (cut r j.castSucc) v ∧
          (Rbar.path r).Before v (cut r j.succ) ∧
          v ≠ cut r j.castSucc ∧
          v ≠ cut r j.succ

namespace ExtendedParentRefinement

variable {K f w : ℕ}

theorem cut_before_last
    {sigma : PathSlicing Rbar M} {parent : Fin M}
    (E : ExtendedParentRefinement sigma Qbar parent f w)
    (r : Rbar.Index) (t : Fin (f + 1)) :
    (Rbar.path r).Before (E.cut r t)
      (sigma.sliceRowPath parent r).target := by
  rw [← E.cut_last r]
  exact E.cut_monotone r (Fin.le_last t)

theorem zero_before_cut
    {sigma : PathSlicing Rbar M} {parent : Fin M}
    (E : ExtendedParentRefinement sigma Qbar parent f w)
    (r : Rbar.Index) (t : Fin (f + 1)) :
    (Rbar.path r).Before
      (sigma.sliceRowPath parent r).source (E.cut r t) := by
  rw [← E.cut_zero r]
  exact E.cut_monotone r (Fin.zero_le t)

end ExtendedParentRefinement

/- Number of selected parent slices, local fanout, and local width.  These
parameters are explicit because the submission builds with `autoImplicit`
disabled. -/
variable {K f w : ℕ}

/-- The target of a half-open earlier slice precedes the source of every
strictly later slice.  Unlike the older connector lemma, this version also
handles a degenerate earlier slice. -/
theorem sliceRowPath_target_before_source_of_lt_general
    (sigma : PathSlicing Rbar M) {i j : Fin M} (hij : i < j)
    (r : Rbar.Index) :
    (Rbar.path r).Before (sigma.sliceRowPath i r).target
      (sigma.sliceRowPath j r).source := by
  let hcut :=
    sigma.cut_monotone r (Fin.castSucc_le_succ i)
  let closed := (Rbar.path r).segmentOfBefore hcut
  have htargetClosed :
      (sigma.sliceRowPath i r).target ∈ closed.vertexSet := by
    apply closed.dropLast_vertexSet_subset
    exact GraphPath.target_mem_vertexSet closed.dropLast
  have htargetRight :
      (Rbar.path r).Before
        (sigma.sliceRowPath i r).target (sigma.cut r i.succ) := by
    exact
      (Rbar.path r).before_of_mem_segmentOfBefore_right
        hcut htargetClosed
  have hrightLeft :
      (Rbar.path r).Before
        (sigma.cut r i.succ) (sigma.cut r j.castSucc) :=
    sigma.cut_monotone r (by
      apply Fin.mk_le_mk.2
      exact Nat.succ_le_iff.2 hij)
  simpa [SimpleGraph.PathSlicing.sliceRowPath_source] using
    (Rbar.path r).before_trans htargetRight hrightLeft

/-- Parent and local coordinates of a flattened cell. -/
def flatParent (j : Fin (K * f)) : Fin K :=
  j.divNat

def flatLocal (j : Fin (K * f)) : Fin f :=
  j.modNat

/-- Row-major flattening of a selected parent and one of its local cells. -/
def flattenCell (a : Fin K) (b : Fin f) : Fin (K * f) :=
  finProdFinEquiv (a, b)

@[simp] theorem flatParent_val (j : Fin (K * f)) :
    (flatParent j).val = j.val / f := rfl

@[simp] theorem flatLocal_val (j : Fin (K * f)) :
    (flatLocal j).val = j.val % f := rfl

@[simp] theorem flatParent_flattenCell (a : Fin K) (b : Fin f) :
    flatParent (flattenCell a b) = a := by
  exact congrArg Prod.fst (finProdFinEquiv.symm_apply_apply (a, b))

@[simp] theorem flatLocal_flattenCell (a : Fin K) (b : Fin f) :
    flatLocal (flattenCell a b) = b := by
  exact congrArg Prod.snd (finProdFinEquiv.symm_apply_apply (a, b))

theorem flatParent_mono {x y : Fin (K * f)} (hxy : x ≤ y) :
    flatParent x ≤ flatParent y := by
  exact Fin.mk_le_mk.mpr (Nat.div_le_div_right (Fin.mk_le_mk.mp hxy))

theorem flatLocal_mono_of_flatParent_eq
    {x y : Fin (K * f)} (hxy : x ≤ y)
    (hparent : flatParent x = flatParent y) :
    flatLocal x ≤ flatLocal y := by
  apply Fin.mk_le_mk.mpr
  have hdiv : x.val / f = y.val / f :=
    congrArg Fin.val hparent
  have hx := Nat.mod_add_div x.val f
  have hy := Nat.mod_add_div y.val f
  rw [← hdiv] at hy
  omega

/-- Strict flattened order inside one parent gives strict local order. -/
theorem flatLocal_lt_of_lt_flatParent_eq
    {x y : Fin (K * f)} (hxy : x < y)
    (hparent : flatParent x = flatParent y) :
    flatLocal x < flatLocal y := by
  apply Fin.mk_lt_mk.mpr
  have hdiv : x.val / f = y.val / f :=
    congrArg Fin.val hparent
  have hx := Nat.mod_add_div x.val f
  have hy := Nat.mod_add_div y.val f
  rw [← hdiv] at hy
  omega

/-- Left boundary of one flattened local cell. -/
noncomputable def refinementCellLeft
    {sigma : PathSlicing Rbar M}
    (selected : Fin K → Fin M)
    (refine :
      ∀ a : Fin K,
        ExtendedParentRefinement sigma Qbar (selected a) f w)
    (r : Rbar.Index) (j : Fin (K * f)) : W :=
  (refine (flatParent j)).cut r (flatLocal j).castSucc

theorem refinementCellLeft_mem
    {sigma : PathSlicing Rbar M}
    (selected : Fin K → Fin M)
    (refine :
      ∀ a : Fin K,
        ExtendedParentRefinement sigma Qbar (selected a) f w)
    (r : Rbar.Index) (j : Fin (K * f)) :
    refinementCellLeft selected refine r j ∈
      (Rbar.path r).vertexSet :=
  (refine (flatParent j)).cut_mem_main r (flatLocal j).castSucc

/-- Right boundary of a flattened local cell, before the global initial and
final gaps are absorbed. -/
noncomputable def refinementCellRight
    {sigma : PathSlicing Rbar M}
    (selected : Fin K → Fin M)
    (refine :
      ∀ a : Fin K,
        ExtendedParentRefinement sigma Qbar (selected a) f w)
    (r : Rbar.Index) (j : Fin (K * f)) : W :=
  (refine (flatParent j)).cut r (flatLocal j).succ

theorem refinementCellRight_mem
    {sigma : PathSlicing Rbar M}
    (selected : Fin K → Fin M)
    (refine :
      ∀ a : Fin K,
        ExtendedParentRefinement sigma Qbar (selected a) f w)
    (r : Rbar.Index) (j : Fin (K * f)) :
    refinementCellRight selected refine r j ∈
      (Rbar.path r).vertexSet :=
  (refine (flatParent j)).cut_mem_main r (flatLocal j).succ

/-- Cell-right boundaries are monotone in row-major flattened order. -/
theorem refinementCellRight_monotone
    {sigma : PathSlicing Rbar M}
    (selected : Fin K → Fin M)
    (hselected : StrictMono selected)
    (refine :
      ∀ a : Fin K,
        ExtendedParentRefinement sigma Qbar (selected a) f w)
    (r : Rbar.Index) {x y : Fin (K * f)} (hxy : x ≤ y) :
    (Rbar.path r).Before
      (refinementCellRight selected refine r x)
      (refinementCellRight selected refine r y) := by
  have hparent :
      flatParent x ≤ flatParent y :=
    flatParent_mono hxy
  rcases hparent.eq_or_lt with heq | hlt
  · have hlocal :
        flatLocal x ≤ flatLocal y :=
      flatLocal_mono_of_flatParent_eq hxy heq
    change
      (Rbar.path r).Before
        ((refine (flatParent x)).cut r (flatLocal x).succ)
        ((refine (flatParent y)).cut r (flatLocal y).succ)
    rw [← heq]
    exact
      (refine (flatParent x)).cut_monotone r
        (Fin.succ_le_succ_iff.mpr hlocal)
  · have htoEarlierTarget :
        (Rbar.path r).Before
          (refinementCellRight selected refine r x)
          (sigma.sliceRowPath (selected (flatParent x)) r).target :=
      (refine (flatParent x)).cut_before_last r (flatLocal x).succ
    have hbetween :
        (Rbar.path r).Before
          (sigma.sliceRowPath (selected (flatParent x)) r).target
          (sigma.sliceRowPath (selected (flatParent y)) r).source :=
      sliceRowPath_target_before_source_of_lt_general sigma
        (hselected hlt) r
    have hfromLaterSource :
        (Rbar.path r).Before
          (sigma.sliceRowPath (selected (flatParent y)) r).source
          (refinementCellRight selected refine r y) :=
      (refine (flatParent y)).zero_before_cut r (flatLocal y).succ
    exact
      (Rbar.path r).before_trans htoEarlierTarget
        ((Rbar.path r).before_trans hbetween hfromLaterSource)

/-- Cell-left boundaries are monotone in row-major flattened order. -/
theorem refinementCellLeft_monotone
    {sigma : PathSlicing Rbar M}
    (selected : Fin K → Fin M)
    (hselected : StrictMono selected)
    (refine :
      ∀ a : Fin K,
        ExtendedParentRefinement sigma Qbar (selected a) f w)
    (r : Rbar.Index) {x y : Fin (K * f)} (hxy : x ≤ y) :
    (Rbar.path r).Before
      (refinementCellLeft selected refine r x)
      (refinementCellLeft selected refine r y) := by
  have hparent :
      flatParent x ≤ flatParent y :=
    flatParent_mono hxy
  rcases hparent.eq_or_lt with heq | hlt
  · have hlocal :
        flatLocal x ≤ flatLocal y :=
      flatLocal_mono_of_flatParent_eq hxy heq
    change
      (Rbar.path r).Before
        ((refine (flatParent x)).cut r (flatLocal x).castSucc)
        ((refine (flatParent y)).cut r (flatLocal y).castSucc)
    rw [← heq]
    exact
      (refine (flatParent x)).cut_monotone r
        (Fin.castSucc_le_castSucc_iff.mpr hlocal)
  · have htoEarlierTarget :
        (Rbar.path r).Before
          (refinementCellLeft selected refine r x)
          (sigma.sliceRowPath (selected (flatParent x)) r).target :=
      (refine (flatParent x)).cut_before_last r
        (flatLocal x).castSucc
    have hbetween :
        (Rbar.path r).Before
          (sigma.sliceRowPath (selected (flatParent x)) r).target
          (sigma.sliceRowPath (selected (flatParent y)) r).source :=
      sliceRowPath_target_before_source_of_lt_general sigma
        (hselected hlt) r
    have hfromLaterSource :
        (Rbar.path r).Before
          (sigma.sliceRowPath (selected (flatParent y)) r).source
          (refinementCellLeft selected refine r y) :=
      (refine (flatParent y)).zero_before_cut r
        (flatLocal y).castSucc
    exact
      (Rbar.path r).before_trans htoEarlierTarget
        ((Rbar.path r).before_trans hbetween hfromLaterSource)

/-- The local right cut of a flattened cell precedes the local left cut of
the next flattened cell.  Equality occurs inside one parent refinement; a
strict row interval containing all skipped parent slices occurs at a parent
transition. -/
theorem refinementCellRight_before_nextLeft
    {sigma : PathSlicing Rbar M}
    (selected : Fin K → Fin M)
    (hselected : StrictMono selected)
    (refine :
      ∀ a : Fin K,
        ExtendedParentRefinement sigma Qbar (selected a) f w)
    (r : Rbar.Index) (j : Fin (K * f))
    (hnext : j.val + 1 < K * f) :
    (Rbar.path r).Before
      (refinementCellRight selected refine r j)
      (refinementCellLeft selected refine r
        ⟨j.val + 1, hnext⟩) := by
  let jnext : Fin (K * f) := ⟨j.val + 1, hnext⟩
  have hjlt : j < jnext := by
    exact Fin.mk_lt_mk.mpr (by simp [jnext])
  have hparent :
      flatParent j ≤ flatParent jnext :=
    flatParent_mono hjlt.le
  rcases hparent.eq_or_lt with heq | hlt
  · have hlocal :
        flatLocal j < flatLocal jnext :=
      flatLocal_lt_of_lt_flatParent_eq hjlt heq
    change
      (Rbar.path r).Before
        ((refine (flatParent j)).cut r (flatLocal j).succ)
        ((refine (flatParent jnext)).cut r
          (flatLocal jnext).castSucc)
    rw [← heq]
    exact
      (refine (flatParent j)).cut_monotone r
        (Fin.succ_le_castSucc_iff.mpr hlocal)
  · have htoEarlierTarget :
        (Rbar.path r).Before
          (refinementCellRight selected refine r j)
          (sigma.sliceRowPath (selected (flatParent j)) r).target :=
      (refine (flatParent j)).cut_before_last r (flatLocal j).succ
    have hbetween :
        (Rbar.path r).Before
          (sigma.sliceRowPath (selected (flatParent j)) r).target
          (sigma.sliceRowPath (selected (flatParent jnext)) r).source :=
      sliceRowPath_target_before_source_of_lt_general sigma
        (hselected hlt) r
    have hfromLaterSource :
        (Rbar.path r).Before
          (sigma.sliceRowPath (selected (flatParent jnext)) r).source
          (refinementCellLeft selected refine r jnext) :=
      (refine (flatParent jnext)).zero_before_cut r
        (flatLocal jnext).castSucc
    exact
      (Rbar.path r).before_trans htoEarlierTarget
        ((Rbar.path r).before_trans hbetween hfromLaterSource)

/-- Global cut system obtained from the left cuts of all local cells.

The source replaces the left cut of the first selected cell, thereby
absorbing the initial gap.  The target replaces the right boundary after the
last selected cell, thereby absorbing the final gap.  At a transition between
selected parents, the preceding global cell extends through the intervening
unselected parent slices. -/
noncomputable def flattenedRefinementCut
    {sigma : PathSlicing Rbar M}
    (selected : Fin K → Fin M)
    (refine :
      ∀ a : Fin K,
        ExtendedParentRefinement sigma Qbar (selected a) f w)
    (r : Rbar.Index) (t : Fin (K * f + 1)) : W :=
  if hzero : t.val = 0 then
    (Rbar.path r).source
  else if hlast : t.val = K * f then
    (Rbar.path r).target
  else
    refinementCellLeft selected refine r
      ⟨t.val, by omega⟩

theorem flattenedRefinementCut_mem
    {sigma : PathSlicing Rbar M}
    (selected : Fin K → Fin M)
    (refine :
      ∀ a : Fin K,
        ExtendedParentRefinement sigma Qbar (selected a) f w)
    (r : Rbar.Index) (t : Fin (K * f + 1)) :
    flattenedRefinementCut selected refine r t ∈
      (Rbar.path r).vertexSet := by
  unfold flattenedRefinementCut
  split
  · exact GraphPath.source_mem_vertexSet _
  · split
    · exact GraphPath.target_mem_vertexSet _
    · exact refinementCellLeft_mem selected refine r _

@[simp] theorem flattenedRefinementCut_zero
    {sigma : PathSlicing Rbar M}
    (selected : Fin K → Fin M)
    (refine :
      ∀ a : Fin K,
        ExtendedParentRefinement sigma Qbar (selected a) f w)
    (r : Rbar.Index) :
    flattenedRefinementCut selected refine r 0 =
      (Rbar.path r).source := by
  simp [flattenedRefinementCut]

theorem flattenedRefinementCut_last
    {sigma : PathSlicing Rbar M}
    (selected : Fin K → Fin M)
    (refine :
      ∀ a : Fin K,
        ExtendedParentRefinement sigma Qbar (selected a) f w)
    (hK : 0 < K) (hf : 0 < f)
    (r : Rbar.Index) :
    flattenedRefinementCut selected refine r (Fin.last (K * f)) =
      (Rbar.path r).target := by
  have hprod : 0 < K * f := Nat.mul_pos hK hf
  simp [flattenedRefinementCut, hprod.ne']

/-- Adjacent flattened cuts occur in row order. -/
theorem flattenedRefinementCut_adjacent
    {sigma : PathSlicing Rbar M}
    (selected : Fin K → Fin M)
    (hselected : StrictMono selected)
    (refine :
      ∀ a : Fin K,
        ExtendedParentRefinement sigma Qbar (selected a) f w)
    (r : Rbar.Index) (j : Fin (K * f)) :
    (Rbar.path r).Before
      (flattenedRefinementCut selected refine r j.castSucc)
      (flattenedRefinementCut selected refine r j.succ) := by
  have hprod : 0 < K * f :=
    lt_of_le_of_lt (Nat.zero_le j.val) j.isLt
  by_cases hjzero : j.val = 0
  · have hleft :
        flattenedRefinementCut selected refine r j.castSucc =
          (Rbar.path r).source := by
      simp [flattenedRefinementCut, hjzero]
    rw [hleft]
    exact
      (Rbar.path r).source_before_of_mem
        (flattenedRefinementCut_mem selected refine r j.succ)
  by_cases hjlast : j.val + 1 = K * f
  · have hright :
        flattenedRefinementCut selected refine r j.succ =
          (Rbar.path r).target := by
      simp [flattenedRefinementCut, hjlast, hprod.ne']
    rw [hright]
    exact
      (Rbar.path r).before_target_of_mem
        (flattenedRefinementCut_mem selected refine r j.castSucc)
  · have hjNotLast : j.val ≠ K * f :=
      Nat.ne_of_lt j.isLt
    have hleft :
        flattenedRefinementCut selected refine r j.castSucc =
          refinementCellLeft selected refine r j := by
      simp [flattenedRefinementCut, hjzero, hjNotLast]
    let jnext : Fin (K * f) :=
      ⟨j.val + 1, by omega⟩
    have hright :
        flattenedRefinementCut selected refine r j.succ =
          refinementCellLeft selected refine r jnext := by
      simp [flattenedRefinementCut, hjlast, jnext]
    rw [hleft, hright]
    exact
      refinementCellLeft_monotone selected hselected refine r
        (show j ≤ jnext by
          apply Fin.mk_le_mk.mpr
          simp [jnext])

/-- The global `K*f` slicing obtained by flattening the selected local
refinements. -/
noncomputable def flattenedRefinementSlicing
    (sigma : PathSlicing Rbar M)
    (selected : Fin K → Fin M)
    (hselected : StrictMono selected)
    (refine :
      ∀ a : Fin K,
        ExtendedParentRefinement sigma Qbar (selected a) f w)
    (hK : 0 < K) (hf : 0 < f) :
    PathSlicing Rbar (K * f) where
  cut := flattenedRefinementCut selected refine
  cut_mem := flattenedRefinementCut_mem selected refine
  cut_zero := flattenedRefinementCut_zero selected refine
  cut_last := flattenedRefinementCut_last selected refine hK hf
  cut_monotone := by
    intro r s t hst
    have hadj :
        ∀ j : Fin (K * f),
          (Rbar.path r).Before
            (flattenedRefinementCut selected refine r j.castSucc)
            (flattenedRefinementCut selected refine r j.succ) :=
      flattenedRefinementCut_adjacent selected hselected refine r
    have hindexMono :
        Monotone
          (fun z : Fin (K * f + 1) =>
            (Rbar.path r).vertexIndex
              (flattenedRefinementCut selected refine r z)) := by
      apply Fin.monotone_iff_le_succ.mpr
      intro j
      exact
        ((Rbar.path r).before_iff_vertexIndex_le.mp (hadj j)).2.2
    apply (Rbar.path r).before_iff_vertexIndex_le.mpr
    exact
      ⟨flattenedRefinementCut_mem selected refine r s,
        flattenedRefinementCut_mem selected refine r t,
        hindexMono hst⟩

@[simp] theorem flattenedRefinementSlicing_cut
    (sigma : PathSlicing Rbar M)
    (selected : Fin K → Fin M)
    (hselected : StrictMono selected)
    (refine :
      ∀ a : Fin K,
        ExtendedParentRefinement sigma Qbar (selected a) f w)
    (hK : 0 < K) (hf : 0 < f)
    (r : Rbar.Index) (t : Fin (K * f + 1)) :
    (flattenedRefinementSlicing
      sigma selected hselected refine hK hf).cut r t =
        flattenedRefinementCut selected refine r t := rfl

/-- The enlarged global left boundary precedes the original local left
boundary. -/
theorem flattened_left_before_local_left
    (sigma : PathSlicing Rbar M)
    (selected : Fin K → Fin M)
    (hselected : StrictMono selected)
    (refine :
      ∀ a : Fin K,
        ExtendedParentRefinement sigma Qbar (selected a) f w)
    (hK : 0 < K) (hf : 0 < f)
    (r : Rbar.Index) (j : Fin (K * f)) :
    (Rbar.path r).Before
      ((flattenedRefinementSlicing
        sigma selected hselected refine hK hf).cut r j.castSucc)
      ((refine (flatParent j)).cut r (flatLocal j).castSucc) := by
  by_cases hjzero : j.val = 0
  · have hcut :
        (flattenedRefinementSlicing
          sigma selected hselected refine hK hf).cut r j.castSucc =
            (Rbar.path r).source := by
      simp [flattenedRefinementSlicing, flattenedRefinementCut, hjzero]
    rw [hcut]
    exact
      (Rbar.path r).source_before_of_mem
        ((refine (flatParent j)).cut_mem_main r (flatLocal j).castSucc)
  · have hjNotLast : j.val ≠ K * f :=
      Nat.ne_of_lt j.isLt
    have hcut :
        (flattenedRefinementSlicing
          sigma selected hselected refine hK hf).cut r j.castSucc =
            refinementCellLeft selected refine r j := by
      simp [flattenedRefinementSlicing, flattenedRefinementCut,
        hjzero, hjNotLast]
    rw [hcut]
    exact
      (Rbar.path r).before_refl
        (refinementCellLeft_mem selected refine r j)

/-- The original local right boundary precedes the enlarged global right
boundary. -/
theorem local_right_before_flattened_right
    (sigma : PathSlicing Rbar M)
    (selected : Fin K → Fin M)
    (hselected : StrictMono selected)
    (refine :
      ∀ a : Fin K,
        ExtendedParentRefinement sigma Qbar (selected a) f w)
    (hK : 0 < K) (hf : 0 < f)
    (r : Rbar.Index) (j : Fin (K * f)) :
    (Rbar.path r).Before
      ((refine (flatParent j)).cut r (flatLocal j).succ)
      ((flattenedRefinementSlicing
        sigma selected hselected refine hK hf).cut r j.succ) := by
  by_cases hjlast : j.val + 1 = K * f
  · have hcut :
        (flattenedRefinementSlicing
          sigma selected hselected refine hK hf).cut r j.succ =
            (Rbar.path r).target := by
      have hprod : 0 < K * f := Nat.mul_pos hK hf
      simp [flattenedRefinementSlicing, flattenedRefinementCut,
        hjlast, hprod.ne']
    rw [hcut]
    exact
      (Rbar.path r).before_target_of_mem
        ((refine (flatParent j)).cut_mem_main r (flatLocal j).succ)
  · let jnext : Fin (K * f) :=
      ⟨j.val + 1, by omega⟩
    have hcut :
        (flattenedRefinementSlicing
          sigma selected hselected refine hK hf).cut r j.succ =
            refinementCellLeft selected refine r jnext := by
      simp [flattenedRefinementSlicing, flattenedRefinementCut,
        hjlast, jnext]
    rw [hcut]
    exact
      refinementCellRight_before_nextLeft
        selected hselected refine r j (by simpa [jnext] using jnext.isLt)

/-- Every path assigned to a local cell remains strictly localized in the
corresponding flattened global cell. -/
theorem cellPaths_subset_flattened_pathsInSlice
    (sigma : PathSlicing Rbar M)
    (selected : Fin K → Fin M)
    (hselected : StrictMono selected)
    (refine :
      ∀ a : Fin K,
        ExtendedParentRefinement sigma Qbar (selected a) f w)
    (hK : 0 < K) (hf : 0 < f)
    (a : Fin K) (b : Fin f) :
    (refine a).cellPaths b ⊆
      (flattenedRefinementSlicing
        sigma selected hselected refine hK hf).pathsInSlice
          Qbar (flattenCell a b) := by
  classical
  intro q hq
  rw [(flattenedRefinementSlicing
    sigma selected hselected refine hK hf).mem_pathsInSlice]
  intro r v hvQ hvR
  have hlocal :=
    (refine a).cell_strict_localized b q hq r v hvQ hvR
  have hleft :
      (Rbar.path r).Before
        ((flattenedRefinementSlicing
          sigma selected hselected refine hK hf).cut r
            (flattenCell a b).castSucc)
        ((refine a).cut r b.castSucc) := by
    have h :=
      flattened_left_before_local_left
        sigma selected hselected refine hK hf r (flattenCell a b)
    rw [flatParent_flattenCell, flatLocal_flattenCell] at h
    exact h
  have hright :
      (Rbar.path r).Before
        ((refine a).cut r b.succ)
        ((flattenedRefinementSlicing
          sigma selected hselected refine hK hf).cut r
            (flattenCell a b).succ) := by
    have h :=
      local_right_before_flattened_right
        sigma selected hselected refine hK hf r (flattenCell a b)
    rw [flatParent_flattenCell, flatLocal_flattenCell] at h
    exact h
  refine
    ⟨hvR,
      (Rbar.path r).before_trans hleft hlocal.1,
      (Rbar.path r).before_trans hlocal.2.1 hright,
      ?_, ?_⟩
  · intro hvEq
    have hback :
        (Rbar.path r).Before
          ((refine a).cut r b.castSucc)
          ((flattenedRefinementSlicing
            sigma selected hselected refine hK hf).cut r
              (flattenCell a b).castSucc) := by
      simpa [hvEq] using hlocal.1
    have heq :=
      (Rbar.path r).before_antisymm hleft hback
    exact hlocal.2.2.1 (hvEq.trans heq)
  · intro hvEq
    have hback :
        (Rbar.path r).Before
          ((flattenedRefinementSlicing
            sigma selected hselected refine hK hf).cut r
              (flattenCell a b).succ)
          ((refine a).cut r b.succ) := by
      simpa [hvEq] using hlocal.2.1
    have heq :=
      (Rbar.path r).before_antisymm hback hright
    exact hlocal.2.2.2 (hvEq.trans heq)

/-- Compose local refinements of an ordered family of possibly
nonconsecutive parent slices into one global `K*f` slicing. -/
theorem composeSelectedSliceRefinements
    (sigma : PathSlicing Rbar M)
    (selected : Fin K → Fin M)
    (hselected : StrictMono selected)
    (refine :
      ∀ a : Fin K,
        ExtendedParentRefinement sigma Qbar (selected a) f w)
    (hK : 0 < K) (hf : 0 < f) :
    ∃ tau : PathSlicing Rbar (K * f),
      tau.WidthAtLeast Qbar w ∧
        ∀ (a : Fin K) (b : Fin f),
          (refine a).cellPaths b ⊆
            tau.pathsInSlice Qbar (flattenCell a b) := by
  let tau :=
    flattenedRefinementSlicing
      sigma selected hselected refine hK hf
  refine ⟨tau, ?_, ?_⟩
  · intro j
    let ab : Fin K × Fin f := finProdFinEquiv.symm j
    have hsub :
        (refine ab.1).cellPaths ab.2 ⊆
          tau.pathsInSlice Qbar j := by
      have h :=
        cellPaths_subset_flattened_pathsInSlice
          sigma selected hselected refine hK hf ab.1 ab.2
      have hj : flattenCell ab.1 ab.2 = j := by
        exact finProdFinEquiv.apply_symm_apply j
      rw [hj] at h
      exact h
    exact
      (refine ab.1).cell_card ab.2 |>.trans
        (Finset.card_le_card hsub)
  · intro a b
    exact
      cellPaths_subset_flattened_pathsInSlice
        sigma selected hselected refine hK hf a b

section PrefixCoarsening

variable {L mNext : ℕ}

/-- Cut system obtained by retaining the first `mNext` cuts and replacing
the new final cut by the original row target. -/
noncomputable def prefixCoarsenedCut
    (tau : PathSlicing Rbar L)
    (hm : 0 < mNext) (hle : mNext ≤ L)
    (r : Rbar.Index) (t : Fin (mNext + 1)) : W :=
  if hlast : t.val = mNext then
    (Rbar.path r).target
  else
    tau.cut r ⟨t.val, by omega⟩

theorem prefixCoarsenedCut_mem
    (tau : PathSlicing Rbar L)
    (hm : 0 < mNext) (hle : mNext ≤ L)
    (r : Rbar.Index) (t : Fin (mNext + 1)) :
    prefixCoarsenedCut tau hm hle r t ∈
      (Rbar.path r).vertexSet := by
  unfold prefixCoarsenedCut
  split
  · exact GraphPath.target_mem_vertexSet _
  · exact tau.cut_mem r _

@[simp] theorem prefixCoarsenedCut_zero
    (tau : PathSlicing Rbar L)
    (hm : 0 < mNext) (hle : mNext ≤ L)
    (r : Rbar.Index) :
    prefixCoarsenedCut tau hm hle r 0 =
      (Rbar.path r).source := by
  simp [prefixCoarsenedCut, hm.ne', hm.ne'.symm, tau.cut_zero]

@[simp] theorem prefixCoarsenedCut_last
    (tau : PathSlicing Rbar L)
    (hm : 0 < mNext) (hle : mNext ≤ L)
    (r : Rbar.Index) :
    prefixCoarsenedCut tau hm hle r (Fin.last mNext) =
      (Rbar.path r).target := by
  simp [prefixCoarsenedCut]

theorem prefixCoarsenedCut_adjacent
    (tau : PathSlicing Rbar L)
    (hm : 0 < mNext) (hle : mNext ≤ L)
    (r : Rbar.Index) (j : Fin mNext) :
    (Rbar.path r).Before
      (prefixCoarsenedCut tau hm hle r j.castSucc)
      (prefixCoarsenedCut tau hm hle r j.succ) := by
  have hjNotLast : j.val ≠ mNext :=
    Nat.ne_of_lt j.isLt
  by_cases hjlast : j.val + 1 = mNext
  · have hleft :
        prefixCoarsenedCut tau hm hle r j.castSucc =
          tau.cut r ⟨j.val, by omega⟩ := by
      simp [prefixCoarsenedCut, hjNotLast]
    have hright :
        prefixCoarsenedCut tau hm hle r j.succ =
          (Rbar.path r).target := by
      simp [prefixCoarsenedCut, hjlast]
    rw [hleft, hright]
    exact
      (Rbar.path r).before_target_of_mem (tau.cut_mem r _)
  · have hleft :
        prefixCoarsenedCut tau hm hle r j.castSucc =
          tau.cut r ⟨j.val, by omega⟩ := by
      simp [prefixCoarsenedCut, hjNotLast]
    have hright :
        prefixCoarsenedCut tau hm hle r j.succ =
          tau.cut r ⟨j.val + 1, by omega⟩ := by
      simp [prefixCoarsenedCut, hjlast]
    rw [hleft, hright]
    exact
      tau.cut_monotone r (by
        apply Fin.mk_le_mk.mpr
        omega)

/-- Coarsen an `L`-slicing to its first `mNext` cells, absorbing every
remaining old cell into the new final cell. -/
noncomputable def prefixCoarsenedSlicing
    (tau : PathSlicing Rbar L)
    (hm : 0 < mNext) (hle : mNext ≤ L) :
    PathSlicing Rbar mNext where
  cut := prefixCoarsenedCut tau hm hle
  cut_mem := prefixCoarsenedCut_mem tau hm hle
  cut_zero := prefixCoarsenedCut_zero tau hm hle
  cut_last := prefixCoarsenedCut_last tau hm hle
  cut_monotone := by
    intro r s t hst
    have hadj :
        ∀ j : Fin mNext,
          (Rbar.path r).Before
            (prefixCoarsenedCut tau hm hle r j.castSucc)
            (prefixCoarsenedCut tau hm hle r j.succ) :=
      prefixCoarsenedCut_adjacent tau hm hle r
    have hindexMono :
        Monotone
          (fun z : Fin (mNext + 1) =>
            (Rbar.path r).vertexIndex
              (prefixCoarsenedCut tau hm hle r z)) := by
      apply Fin.monotone_iff_le_succ.mpr
      intro j
      exact
        ((Rbar.path r).before_iff_vertexIndex_le.mp (hadj j)).2.2
    apply (Rbar.path r).before_iff_vertexIndex_le.mpr
    exact
      ⟨prefixCoarsenedCut_mem tau hm hle r s,
        prefixCoarsenedCut_mem tau hm hle r t,
        hindexMono hst⟩

def prefixOldIndex (hle : mNext ≤ L) (j : Fin mNext) : Fin L :=
  ⟨j.val, lt_of_lt_of_le j.isLt hle⟩

/-- Every path localized in an old prefix cell remains localized after the
final right boundary is enlarged. -/
theorem pathsInSlice_subset_prefixCoarsened
    (tau : PathSlicing Rbar L)
    (Qbar : PathPacking H Sbar Tbar)
    (hm : 0 < mNext) (hle : mNext ≤ L)
    (j : Fin mNext) :
    tau.pathsInSlice Qbar (prefixOldIndex hle j) ⊆
      (prefixCoarsenedSlicing tau hm hle).pathsInSlice Qbar j := by
  classical
  intro q hq
  rw [(prefixCoarsenedSlicing tau hm hle).mem_pathsInSlice]
  intro r v hvQ hvR
  have hold :=
    (tau.mem_pathsInSlice Qbar (prefixOldIndex hle j) q).1 hq hvQ hvR
  have hleft :
      (prefixCoarsenedSlicing tau hm hle).cut r j.castSucc =
        tau.cut r (prefixOldIndex hle j).castSucc := by
    change
      prefixCoarsenedCut tau hm hle r j.castSucc =
        tau.cut r (prefixOldIndex hle j).castSucc
    have hjNotLast : j.val ≠ mNext :=
      Nat.ne_of_lt j.isLt
    simp [prefixCoarsenedCut, prefixOldIndex, hjNotLast]
  have hright :
      (Rbar.path r).Before
        (tau.cut r (prefixOldIndex hle j).succ)
        ((prefixCoarsenedSlicing tau hm hle).cut r j.succ) := by
    by_cases hjlast : j.val + 1 = mNext
    · have hnew :
          (prefixCoarsenedSlicing tau hm hle).cut r j.succ =
            (Rbar.path r).target := by
        change
          prefixCoarsenedCut tau hm hle r j.succ =
            (Rbar.path r).target
        simp [prefixCoarsenedCut, hjlast]
      rw [hnew]
      exact
        (Rbar.path r).before_target_of_mem
          (tau.cut_mem r (prefixOldIndex hle j).succ)
    · have hnew :
          (prefixCoarsenedSlicing tau hm hle).cut r j.succ =
            tau.cut r (prefixOldIndex hle j).succ := by
        change
          prefixCoarsenedCut tau hm hle r j.succ =
            tau.cut r (prefixOldIndex hle j).succ
        simp [prefixCoarsenedCut, prefixOldIndex, hjlast]
      rw [hnew]
      exact
        (Rbar.path r).before_refl
          (tau.cut_mem r (prefixOldIndex hle j).succ)
  refine
    ⟨hvR,
      by simpa [hleft] using hold.2.1,
      (Rbar.path r).before_trans hold.2.2.1 hright,
      ?_, ?_⟩
  · intro hvEq
    apply hold.2.2.2.1
    simpa [hleft] using hvEq
  · intro hvEq
    have hback :
        (Rbar.path r).Before
          ((prefixCoarsenedSlicing tau hm hle).cut r j.succ)
          (tau.cut r (prefixOldIndex hle j).succ) := by
      simpa [hvEq] using hold.2.2.1
    have heq :=
      (Rbar.path r).before_antisymm hback hright
    exact hold.2.2.2.2 (hvEq.trans heq)

/-- Exact-slice-count corollary: a width certificate on at least
`mNext` cells gives one on exactly `mNext` cells. -/
theorem takePrefixCoarsening
    (tau : PathSlicing Rbar L)
    (Qbar : PathPacking H Sbar Tbar)
    (hm : 0 < mNext) (hle : mNext ≤ L)
    (hwidth : tau.WidthAtLeast Qbar w) :
    ∃ tau' : PathSlicing Rbar mNext,
      tau'.WidthAtLeast Qbar w := by
  let tau' := prefixCoarsenedSlicing tau hm hle
  refine ⟨tau', ?_⟩
  intro j
  exact
    (hwidth (prefixOldIndex hle j)).trans
      (Finset.card_le_card
        (pathsInSlice_subset_prefixCoarsened tau Qbar hm hle j))

end PrefixCoarsening

end PathSlicing
end Exponent8
end SimpleGraph

end Lax17Proofs
