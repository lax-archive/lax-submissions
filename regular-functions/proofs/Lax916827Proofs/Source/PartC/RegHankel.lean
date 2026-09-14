/-
The Hankel decomposition of the value of a two-way transducer, for Theorem
`thm:decidable-equivalence-regular` of *Transducers* (M. Bojańczyk).

Let `M` be a two-way transducer with a finite state set `Q` over finite
alphabets, computing a total function `f`, and let `oval` be the base-`K`
encoding of output strings by rational numbers
(`RequestProject/PartC/RegVal.lean`).  Cutting the input as `u ++ v` and using
the crossing decomposition of `RequestProject/PartC/RegCross.lean`, the value
`oval (f (u ++ v))` is a sum, over the pieces of the run, of products of a
factor depending only on `u` and a factor depending only on `v`; summing also
over the finitely many *candidate* crossing sequences, each of which is either
the true one or contributes zero, gives a Hankel decomposition

  `oval (f (u ++ v)) = ∑ ι, g ι u * h ι v`

over an index set whose size is bounded explicitly by the number of states and
the size of the input alphabet.  This is
`Transducers.RegHankel.hankel_decomp`; Schützenberger's criterion in the form
`Transducers.HankelRank.zero_of_short` turns it, in
`RequestProject/PartC/RegShort.lean`, into a bound on the length of a shortest
input on which two such transducers differ.
-/
import Lax916827Proofs.Source.PartC.RegVal
import Lax916827Proofs.Source.Common.HankelRank
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace RegHankel

open RegPos TwoWay

/-! ## Locality of a step at a cut -/

section Locality

variable {A : Type}

lemma loc_zl (u v : List A) :
    ∀ p ≤ u.length, leftLet (u ++ v.head?.toList) p = leftLet (u ++ v) p := by
  intro p hp
  rcases Nat.eq_zero_or_pos p with rfl | hpos
  · simp [leftLet]
  · have h1 : p - 1 < u.length := by omega
    rw [leftLet, leftLet, if_neg hpos.ne', if_neg hpos.ne',
      List.getElem?_append_left h1, List.getElem?_append_left h1]

lemma head?_toList_getElem? (v : List A) : v.head?.toList[0]? = v[0]? := by
  cases v with
  | nil => simp
  | cons b t => simp

lemma loc_zr (u v : List A) :
    ∀ p ≤ u.length, (u ++ v.head?.toList)[p]? = (u ++ v)[p]? := by
  intro p hp
  rcases lt_or_eq_of_le hp with hlt | heq
  · rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]
  · subst heq
    rw [List.getElem?_append_right le_rfl, List.getElem?_append_right le_rfl]
    simpa using head?_toList_getElem? v

lemma loc_zlen (u v : List A) : ∀ p < u.length, p < (u ++ v.head?.toList).length := by
  intro p hp
  simp only [List.length_append]
  omega

lemma loc_vl (u v : List A) :
    ∀ p, 1 ≤ p → leftLet v p = leftLet (u ++ v) (u.length + p) := by
  intro p hp
  rw [leftLet, leftLet, if_neg (by omega), if_neg (by omega)]
  have h : u.length + p - 1 = u.length + (p - 1) := by omega
  rw [h, List.getElem?_append_right (by omega)]
  congr 1
  omega

lemma loc_vr (u v : List A) : ∀ p, v[p]? = (u ++ v)[u.length + p]? := by
  intro p
  rw [List.getElem?_append_right (by omega)]
  congr 1
  omega

lemma loc_vlen (u v : List A) : ∀ p, p < v.length ↔ u.length + p < (u ++ v).length := by
  intro p
  simp only [List.length_append]
  omega

end Locality

noncomputable section

open Classical

variable {A B Q : Type} [Fintype A] [Fintype B] [Fintype Q]

/-! ## The index set -/

/-- The bound on the length of a crossing sequence. -/
abbrev csN (Q : Type) [Fintype Q] : ℕ := 2 * Fintype.card Q

/-- The index set of the Hankel decomposition: the first letter of the suffix,
a candidate crossing sequence given as a bounded list of states, and the number
of the piece. -/
abbrev Idx (A Q : Type) [Fintype A] [Fintype Q] : Type :=
  Option A × (Fin (csN Q) → Q) × Fin (csN Q + 1) × Fin (csN Q + 2)

/-- The candidate crossing sequence described by an index. -/
def csOf (fn : Fin (csN Q) → Q) (m : Fin (csN Q + 1)) : List Q := (List.ofFn fn).take (m : ℕ)

lemma csOf_length (fn : Fin (csN Q) → Q) (m : Fin (csN Q + 1)) : (csOf fn m).length = (m : ℕ) := by
  have := m.isLt
  simp only [csOf, List.length_take, List.length_ofFn]
  omega

/-- The description of a crossing sequence is normalised, so that a crossing
sequence has exactly one index describing it. -/
def canon (M : TwoWay A B Q) (fn : Fin (csN Q) → Q) (m : Fin (csN Q + 1)) : Prop :=
  ∀ i : Fin (csN Q), (m : ℕ) ≤ (i : ℕ) → fn i = M.init

/-- The condition on the prefix: the pieces of the run on the left of the cut
fit the candidate crossing sequence. -/
def LOK (M : TwoWay A B Q) (u : List A) (a : Option A) (cs : List Q) : Prop :=
  ∀ i ≤ cs.length, flipn true i = true →
    regRes M (u ++ a.toList) u.length true (entryL M.init u.length cs i) = some cs[i]?

/-- The condition on the suffix: the pieces of the run on the right of the cut
fit the candidate crossing sequence. -/
def ROK (M : TwoWay A B Q) (v : List A) (cs : List Q) : Prop :=
  ∀ i ≤ cs.length, flipn true i = false →
    regRes M v 1 false (entryR M.init cs i) = some cs[i]?

/-! ## The two factors -/

/-- The factor of the `j`-th piece that depends only on the prefix. -/
def gterm (M : TwoWay A B Q) (a : Option A) (cs : List Q) (j : ℕ) (u : List A) : ℚ :=
  if j ≤ cs.length then
    (∏ i ∈ (Finset.range j).filter (fun i => flipn true i = true),
        owt (regOut M (u ++ a.toList) u.length true (entryL M.init u.length cs i)))
      * (if flipn true j = true then
          oval (regOut M (u ++ a.toList) u.length true (entryL M.init u.length cs j))
        else 1)
  else 0

/-- The factor of the `j`-th piece that depends only on the suffix. -/
def hterm (M : TwoWay A B Q) (cs : List Q) (j : ℕ) (v : List A) : ℚ :=
  (∏ i ∈ (Finset.range j).filter (fun i => ¬ (flipn true i = true)),
      owt (regOut M v 1 false (entryR M.init cs i)))
    * (if flipn true j = true then 1
       else oval (regOut M v 1 false (entryR M.init cs j)))

/-- The prefix side of the Hankel decomposition. -/
def gfun (M : TwoWay A B Q) (a : Option A) (fn : Fin (csN Q) → Q) (m : Fin (csN Q + 1))
    (j : Fin (csN Q + 2)) (u : List A) : ℚ :=
  if canon M fn m ∧ LOK M u a (csOf fn m) then gterm M a (csOf fn m) (j : ℕ) u else 0

/-- The suffix side of the Hankel decomposition. -/
def hfun (M : TwoWay A B Q) (a : Option A) (fn : Fin (csN Q) → Q) (m : Fin (csN Q + 1))
    (j : Fin (csN Q + 2)) (v : List A) : ℚ :=
  if v.head? = a ∧ ROK M v (csOf fn m) then hterm M (csOf fn m) (j : ℕ) v else 0

/-! ## The decomposition -/

omit [Fintype A] [Fintype Q] in
/-- The product of the two factors of the `j`-th piece is the term of the value
that belongs to that piece. -/
lemma gterm_mul_hterm (M : TwoWay A B Q) (u v : List A) (cs : List Q) {j : ℕ}
    (hj : j ≤ cs.length) :
    gterm M v.head? cs j u * hterm M cs j v
      = (∏ i ∈ Finset.range j, owt (blkOut M (u ++ v.head?.toList) v u.length
            (flipn true i) (entryC M.init u.length true (0, M.init) cs i)))
        * oval (blkOut M (u ++ v.head?.toList) v u.length
            (flipn true j) (entryC M.init u.length true (0, M.init) cs j)) := by
  have hb : ∀ i : ℕ, blkOut M (u ++ v.head?.toList) v u.length (flipn true i)
      (entryC M.init u.length true (0, M.init) cs i)
      = if flipn true i = true then
          regOut M (u ++ v.head?.toList) u.length true (entryL M.init u.length cs i)
        else regOut M v 1 false (entryR M.init cs i) := by
    intro i
    cases hfl : flipn true i with
    | true => rw [entryC_eq_entryL M.init u.length cs hfl]; simp
    | false => rw [entryC_eq_entryR M.init u.length cs hfl]; simp
  rw [gterm, if_pos hj, hterm]
  simp only [hb]
  rw [mul_mul_mul_comm]
  congr 1
  · rw [← Finset.prod_filter_mul_prod_filter_not (Finset.range j) (fun i => flipn true i = true)]
    congr 1
    · exact Finset.prod_congr rfl (fun i hi => by rw [if_pos (Finset.mem_filter.1 hi).2])
    · exact Finset.prod_congr rfl (fun i hi => by rw [if_neg (Finset.mem_filter.1 hi).2])
  · cases flipn true j with
    | true => simp
    | false => simp

/-- **The Hankel decomposition of the value of a two-way transducer.** -/
theorem hankel_decomp (M : TwoWay A B Q) (f : List A → List B) (hf : ∀ w, M.Computes w (f w))
    (u v : List A) :
    oval (f (u ++ v)) = ∑ ι : Idx A Q,
      gfun M ι.1 ι.2.1 ι.2.2.1 ι.2.2.2 u * hfun M ι.1 ι.2.1 ι.2.2.1 ι.2.2.2 v := by
  classical
  -- the crossing decomposition of the run on `u ++ v`
  obtain ⟨n, hrun⟩ := (computes_iff_runP M (u ++ v) (f (u ++ v))).1 (hf (u ++ v))
  obtain ⟨cs, hAlt⟩ := (alt_of_runP (loc_zl u v) (loc_zr u v) (loc_zlen u v)
    (loc_vl u v) (loc_vr u v) (loc_vlen u v) n (0, M.init) (f (u ++ v)) hrun).1 (by simp)
  have hlen : cs.length ≤ csN Q := hAlt.length_le
  obtain ⟨hOK, hflat⟩ := hAlt.blk_eq M.init
  -- the two conditions hold for the true crossing sequence
  have hLOK : LOK M u v.head? cs := by
    intro i hi hfl
    have h := hOK i hi
    rw [entryC_eq_entryL M.init u.length cs hfl, hfl] at h
    simpa using h
  have hROK : ROK M v cs := by
    intro i hi hfl
    have h := hOK i hi
    rw [entryC_eq_entryR M.init u.length cs hfl, hfl] at h
    simpa using h
  -- the index describing the true crossing sequence
  set fn₀ : Fin (csN Q) → Q := fun i => cs.getD (i : ℕ) M.init with hfn₀
  set m₀ : Fin (csN Q + 1) := ⟨cs.length, by omega⟩ with hm₀
  have hm₀v : (m₀ : ℕ) = cs.length := rfl
  have hcs : csOf fn₀ m₀ = cs := by
    refine List.ext_getElem ?_ ?_
    · rw [csOf_length, hm₀v]
    · intro i h1 h2
      simp only [csOf, List.getElem_take, List.getElem_ofFn, hfn₀]
      rw [List.getD_eq_getElem _ _ h2]
  have hcanon : canon M fn₀ m₀ := by
    intro i hi
    rw [hm₀v] at hi
    simp only [hfn₀]
    exact List.getD_eq_default _ _ hi
  -- the value of the run, piece by piece
  have hval : oval (f (u ++ v)) = ∑ j ∈ Finset.range (cs.length + 1),
      (∏ i ∈ Finset.range j, owt (blkOut M (u ++ v.head?.toList) v u.length
          (flipn true i) (entryC M.init u.length true (0, M.init) cs i)))
        * oval (blkOut M (u ++ v.head?.toList) v u.length
          (flipn true j) (entryC M.init u.length true (0, M.init) cs j)) := by
    rw [hflat, oval_flatten]
  -- only the index of the true crossing sequence contributes
  have hzero : ∀ ι : Idx A Q, ¬(ι.1 = v.head? ∧ ι.2.1 = fn₀ ∧ ι.2.2.1 = m₀) →
      gfun M ι.1 ι.2.1 ι.2.2.1 ι.2.2.2 u * hfun M ι.1 ι.2.1 ι.2.2.1 ι.2.2.2 v = 0 := by
    rintro ⟨a, fn, m, j⟩ hne
    by_contra hprod
    have hg : gfun M a fn m j u ≠ 0 := fun h => hprod (by rw [h, zero_mul])
    have hh : hfun M a fn m j v ≠ 0 := fun h => hprod (by rw [h, mul_zero])
    rw [gfun] at hg
    rw [hfun] at hh
    by_cases hcond : canon M fn m ∧ LOK M u a (csOf fn m)
    swap
    · exact hg (if_neg hcond)
    by_cases hcond' : v.head? = a ∧ ROK M v (csOf fn m)
    swap
    · exact hh (if_neg hcond')
    obtain ⟨hcan, hlok⟩ := hcond
    obtain ⟨hahd, hrok⟩ := hcond'
    subst hahd
    -- the candidate crossing sequence is the true one
    have hfull : ∀ i ≤ (csOf fn m).length,
        blkRes M (u ++ v.head?.toList) v u.length (flipn true i)
          (entryC M.init u.length true (0, M.init) (csOf fn m) i) = some (csOf fn m)[i]? := by
      intro i hi
      cases hfl : flipn true i with
      | true =>
          rw [entryC_eq_entryL M.init u.length (csOf fn m) hfl]
          simpa using hlok i hi hfl
      | false =>
          rw [entryC_eq_entryR M.init u.length (csOf fn m) hfl]
          simpa using hrok i hi hfl
    obtain ⟨o', hAlt'⟩ := alt_of_blkRes M.init (csOf fn m) true (0, M.init) hfull
    have hcseq : csOf fn m = cs := (Alt.det hAlt' hAlt).1
    have hm : m = m₀ := by
      apply Fin.ext
      have hl := csOf_length fn m
      rw [hcseq] at hl
      rw [hm₀v, ← hl]
    subst hm
    have hfneq : fn = fn₀ := by
      funext i
      by_cases hik : (i : ℕ) < (m₀ : ℕ)
      · have hik' : (i : ℕ) < cs.length := by rwa [hm₀v] at hik
        have h2 : cs.getD (i : ℕ) M.init = (csOf fn m₀).getD (i : ℕ) M.init := by rw [hcseq]
        simp only [hfn₀]
        rw [h2, List.getD_eq_getElem _ _ (by rw [csOf_length]; exact hik)]
        simp only [csOf, List.getElem_take, List.getElem_ofFn]
      · rw [hcan i (by omega)]
        simp only [hfn₀]
        refine (List.getD_eq_default _ _ ?_).symm
        rw [hm₀v] at hik
        omega
    exact hne ⟨rfl, hfneq, rfl⟩
  -- the sum over the index set collapses to a sum over the number of the piece
  have hsum : (∑ ι : Idx A Q,
        gfun M ι.1 ι.2.1 ι.2.2.1 ι.2.2.2 u * hfun M ι.1 ι.2.1 ι.2.2.1 ι.2.2.2 v)
      = ∑ j : Fin (csN Q + 2),
        gfun M v.head? fn₀ m₀ j u * hfun M v.head? fn₀ m₀ j v := by
    rw [← Finset.sum_image
      (f := fun ι : Idx A Q =>
        gfun M ι.1 ι.2.1 ι.2.2.1 ι.2.2.2 u * hfun M ι.1 ι.2.1 ι.2.2.1 ι.2.2.2 v)
      (g := fun j : Fin (csN Q + 2) => ((v.head?, fn₀, m₀, j) : Idx A Q))
      (s := (Finset.univ : Finset (Fin (csN Q + 2))))
      (by intro x _ y _ h; simpa using h)]
    refine (Finset.sum_subset (Finset.subset_univ _) ?_).symm
    intro ι _ hnot
    refine hzero ι ?_
    rintro ⟨h1, h2, h3⟩
    refine hnot ?_
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    exact ⟨ι.2.2.2, by rw [← h1, ← h2, ← h3]⟩
  rw [hsum]
  have hgh : ∀ j : Fin (csN Q + 2),
      gfun M v.head? fn₀ m₀ j u * hfun M v.head? fn₀ m₀ j v
        = gterm M v.head? cs (j : ℕ) u * hterm M cs (j : ℕ) v := by
    intro j
    rw [gfun, hfun, hcs, if_pos ⟨hcanon, hLOK⟩, if_pos ⟨rfl, hROK⟩]
  simp only [hgh]
  rw [Fin.sum_univ_eq_sum_range (fun j => gterm M v.head? cs j u * hterm M cs j v), hval]
  have hsub : Finset.range (cs.length + 1) ⊆ Finset.range (csN Q + 2) := by
    intro j hj
    simp only [Finset.mem_range] at hj ⊢
    omega
  have hz : ∀ j ∈ Finset.range (csN Q + 2), j ∉ Finset.range (cs.length + 1) →
      gterm M v.head? cs j u * hterm M cs j v = 0 := by
    intro j _ hjn
    simp only [Finset.mem_range, not_lt] at hjn
    rw [gterm, if_neg (by omega), zero_mul]
  rw [← Finset.sum_subset hsub hz]
  refine Finset.sum_congr rfl ?_
  intro j hj
  simp only [Finset.mem_range] at hj
  exact (gterm_mul_hterm M u v cs (by omega)).symm

end

end RegHankel

end Lax916827Proofs.Transducers
