import Mathlib.Data.List.GetD
import Lax3Proofs.SolveBlocks

/-!
# F6c/2 — `restrict` and `isolate` as IMP+ programs (draft header)

Placeholder module docstring; written out at the end of the leaf.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax13Proofs.Codegen (arrOf_getD getD_eq_getElem)
open Lax3.ColoredGraphs (Coloring)
open Lax12.UniformQuasiWideness (deleteVerts)

/-! ## §1 The rank encoding

The one scratch array holds, at parent name `w`, the *rank-plus-one* of
`w` in the child's enumeration — `0` for a non-member. One lookup is
both the membership test and the renaming, which is how the membership
test rides the one scratch array. -/

section Rank

variable {n : ℕ}

open Classical in
/-- The renaming at plain numbers: the local name of parent name `w`,
if it has one. -/
private noncomputable def rkOpt (S : Set (Fin n)) (w : ℕ) : Option ℕ :=
  if hw : w < n then (Impl.toLocal S ⟨w, hw⟩).map Fin.val else none

/-- The scratch encoding: rank plus one for members, `0` otherwise. -/
private noncomputable def rk (S : Set (Fin n)) (w : ℕ) : ℕ :=
  ((rkOpt S w).map (· + 1)).getD 0

/-- The member list at plain numbers (total; `0` beyond the count). -/
private noncomputable def embN (S : Set (Fin n)) (t : ℕ) : ℕ :=
  if ht : t < S.ncard then (Impl.restrictEmb S ⟨t, ht⟩ : ℕ) else 0

private theorem embN_of_lt (S : Set (Fin n)) {t : ℕ} (ht : t < S.ncard) :
    embN S t = (Impl.restrictEmb S ⟨t, ht⟩ : ℕ) := dif_pos ht

private theorem embN_lt (S : Set (Fin n)) {t : ℕ} (ht : t < S.ncard) :
    embN S t < n := by
  rw [embN_of_lt S ht]
  exact (Impl.restrictEmb S ⟨t, ht⟩).2

/-- Cluster size never exceeds the carrier. -/
private theorem ncard_le_carrier (S : Set (Fin n)) : S.ncard ≤ n := by
  have := Set.ncard_le_ncard (Set.subset_univ S) Set.finite_univ
  simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using this

private theorem toLocal_emb (S : Set (Fin n)) (t : Fin S.ncard) :
    Impl.toLocal S (Impl.restrictEmb S t) = some t := by
  rw [Impl.toLocal, dif_pos (Impl.restrictEmb_mem S t)]
  congr 1
  have h : (⟨Impl.restrictEmb S t, Impl.restrictEmb_mem S t⟩ : ↥S)
      = Driver.setEquiv S t := Subtype.ext rfl
  rw [h, Equiv.symm_apply_apply]

private theorem toLocal_mem (S : Set (Fin n)) {x : Fin n} {b : Fin S.ncard}
    (h : Impl.toLocal S x = some b) : x ∈ S := by
  by_contra hx
  rw [Impl.toLocal_eq_none S hx] at h
  simp at h

/-- Reading the scratch at a member: rank plus one. -/
private theorem rk_emb (S : Set (Fin n)) (t : Fin S.ncard) :
    rk S (Impl.restrictEmb S t) = (t : ℕ) + 1 := by
  have hw : (Impl.restrictEmb S t : ℕ) < n := (Impl.restrictEmb S t).2
  have hfin : (⟨(Impl.restrictEmb S t : ℕ), hw⟩ : Fin n) = Impl.restrictEmb S t :=
    Fin.ext rfl
  rw [rk, rkOpt, dif_pos hw, hfin, toLocal_emb]
  rfl

private theorem rkOpt_eq_none (S : Set (Fin n)) {w : ℕ}
    (h : ∀ hw : w < n, (⟨w, hw⟩ : Fin n) ∉ S) : rkOpt S w = none := by
  rw [rkOpt]
  split
  · rename_i hw
    rw [Impl.toLocal_eq_none S (h hw)]
    rfl
  · rfl

/-- A non-member (or an out-of-carrier number) reads `0`. -/
private theorem rk_eq_zero (S : Set (Fin n)) {w : ℕ}
    (h : ∀ hw : w < n, (⟨w, hw⟩ : Fin n) ∉ S) : rk S w = 0 := by
  rw [rk, rkOpt_eq_none S h]
  rfl

/-- What a `some` read means: the parent name is the enumeration's. -/
private theorem rkOpt_eq_some (S : Set (Fin n)) {w m : ℕ}
    (h : rkOpt S w = some m) :
    ∃ (hm : m < S.ncard) (hw : w < n),
      Impl.restrictEmb S ⟨m, hm⟩ = ⟨w, hw⟩ := by
  rw [rkOpt] at h
  split at h
  · rename_i hw
    obtain ⟨b, hb, rfl⟩ := Option.map_eq_some_iff.mp h
    have hmem : (⟨w, hw⟩ : Fin n) ∈ S := toLocal_mem S hb
    have := Impl.restrictEmb_toLocal S hmem hb
    exact ⟨b.2, hw, by rw [show (⟨(b : ℕ), b.2⟩ : Fin S.ncard) = b from Fin.ext rfl, this]⟩
  · simp at h

/-- The scratch value at a member, through `rkOpt`. -/
private theorem rkOpt_emb (S : Set (Fin n)) (t : Fin S.ncard) :
    rkOpt S (Impl.restrictEmb S t) = some (t : ℕ) := by
  have hw : (Impl.restrictEmb S t : ℕ) < n := (Impl.restrictEmb S t).2
  have hfin : (⟨(Impl.restrictEmb S t : ℕ), hw⟩ : Fin n) = Impl.restrictEmb S t :=
    Fin.ext rfl
  rw [rkOpt, dif_pos hw, hfin, toLocal_emb]
  rfl

/-- The two readings agree: `rk` is `rkOpt` plus one. -/
private theorem rk_eq_rkOpt (S : Set (Fin n)) (w : ℕ) :
    rk S w = ((rkOpt S w).map (· + 1)).getD 0 := rfl

private theorem rkOpt_eq_none_iff_rk (S : Set (Fin n)) (w : ℕ) :
    rkOpt S w = none ↔ rk S w = 0 := by
  rw [rk]
  cases h : rkOpt S w <;> simp

private theorem rk_pos_elim (S : Set (Fin n)) {w x : ℕ} (h : rk S w = x)
    (hx : 0 < x) : rkOpt S w = some (x - 1) := by
  rw [rk] at h
  cases hopt : rkOpt S w with
  | none => rw [hopt] at h; simp at h; omega
  | some m =>
    rw [hopt] at h
    simp at h
    congr 1
    omega

/-- Ranks stay below the cluster size (plus one for the encoding). -/
private theorem rk_le (S : Set (Fin n)) (w : ℕ) : rk S w ≤ S.ncard := by
  rw [rk]
  cases h : rkOpt S w with
  | none => simp
  | some m =>
    obtain ⟨hm, -, -⟩ := rkOpt_eq_some S h
    simp
    omega

/-- Partial injectivity of the renaming — what row `Nodup`s ride on. -/
private theorem rkOpt_inj (S : Set (Fin n)) {a b c : ℕ}
    (ha : rkOpt S a = some c) (hb : rkOpt S b = some c) : a = b := by
  obtain ⟨hm, hwa, hea⟩ := rkOpt_eq_some S ha
  obtain ⟨hm', hwb, heb⟩ := rkOpt_eq_some S hb
  have : (⟨c, hm⟩ : Fin S.ncard) = ⟨c, hm'⟩ := Fin.ext rfl
  rw [this, heb] at hea
  exact (congrArg Fin.val hea).symm

end Rank

/-! ## §2 The flattened row store

The generic slice arithmetic of a CSR built row by row: `offList f a`
is where row `a` starts when the rows are the lists `f 0, f 1, …` laid
end to end. -/

section Flat

/-- Where row `a` starts in the flattened store. -/
private def offList (f : ℕ → List ℕ) (a : ℕ) : ℕ :=
  ((List.range a).map fun u => (f u).length).sum

@[simp] private theorem offList_zero (f : ℕ → List ℕ) : offList f 0 = 0 := rfl

private theorem offList_succ (f : ℕ → List ℕ) (a : ℕ) :
    offList f (a + 1) = offList f a + (f a).length := by
  rw [offList, List.range_succ, List.map_append, List.sum_append]
  rfl

private theorem offList_mono (f : ℕ → List ℕ) {a b : ℕ} (h : a ≤ b) :
    offList f a ≤ offList f b := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact le_trans ih (by rw [offList_succ]; omega)

private theorem length_flatMap_range (f : ℕ → List ℕ) (a : ℕ) :
    ((List.range a).flatMap f).length = offList f a := by
  rw [List.length_flatMap]
  rfl

/-- Reading the flattened store inside row `t`. -/
private theorem getD_flatMap_range (f : ℕ → List ℕ) :
    ∀ {a t : ℕ}, t < a → ∀ {m : ℕ}, m < (f t).length →
      ((List.range a).flatMap f).getD (offList f t + m) 0 = (f t).getD m 0 := by
  intro a
  induction a with
  | zero => omega
  | succ a ih =>
    intro t ht m hm
    rw [List.range_succ, List.flatMap_append]
    rcases Nat.lt_or_ge t a with h | h
    · rw [List.getD_append]
      · exact ih h hm
      · rw [length_flatMap_range]
        calc offList f t + m < offList f t + (f t).length := by omega
          _ = offList f (t + 1) := (offList_succ f t).symm
          _ ≤ offList f a := offList_mono f (by omega)
    · have hta : t = a := by omega
      subst hta
      rw [List.getD_append_right _ _ _ _ (by rw [length_flatMap_range]; omega)]
      rw [length_flatMap_range, Nat.add_sub_cancel_left]
      simp [List.flatMap]

/-- Every entry of the flattened store is an entry of some row. -/
private theorem mem_flatMap_range {f : ℕ → List ℕ} {a x : ℕ}
    (h : x ∈ (List.range a).flatMap f) : ∃ t < a, x ∈ f t := by
  obtain ⟨t, ht, hx⟩ := List.mem_flatMap.mp h
  exact ⟨t, List.mem_range.mp ht, hx⟩

/-- The list-world sums are the `Finset` sums the cost side quotes. -/
private theorem offList_eq_sum (f : ℕ → List ℕ) (a : ℕ) :
    offList f a = ∑ t ∈ Finset.range a, (f t).length := by
  induction a with
  | zero => simp
  | succ a ih => rw [offList_succ, Finset.sum_range_succ, ih]

end Flat

/-! ## §3 The child rows

`crowL t` is what the machine emits as row `t` of the child CSR: the
parent row of the `t`-th member, scanned in slot order, keeping members
and renaming them local. `coff`/`ctgt` are the CSR functions the
existential of `GraphCsr` is discharged with. -/

section ChildRows

variable {n : ℕ}

/-- Row `t` of the child CSR: the parent row of the `t`-th member,
filtered through the scratch. -/
private noncomputable def crowL (S : Set (Fin n)) (off tgt : ℕ → ℕ) (t : ℕ) :
    List ℕ :=
  (Csr.row off tgt (embN S t)).filterMap (rkOpt S)

/-- The whole child target zone, rows laid end to end. -/
private noncomputable def callL (S : Set (Fin n)) (off tgt : ℕ → ℕ) : List ℕ :=
  (List.range S.ncard).flatMap (crowL S off tgt)

/-- The child offsets. -/
private noncomputable def coff (S : Set (Fin n)) (off tgt : ℕ → ℕ) (a : ℕ) : ℕ :=
  offList (crowL S off tgt) (min a S.ncard)

/-- The child targets. -/
private noncomputable def ctgt (S : Set (Fin n)) (off tgt : ℕ → ℕ) (p : ℕ) : ℕ :=
  (callL S off tgt).getD p 0

/-- The child slot count. -/
private noncomputable def cns (S : Set (Fin n)) (off tgt : ℕ → ℕ) : ℕ :=
  coff S off tgt S.ncard

variable (S : Set (Fin n)) (off tgt : ℕ → ℕ)

@[simp] private theorem coff_zero : coff S off tgt 0 = 0 := by
  simp [coff]

private theorem coff_succ {t : ℕ} (ht : t < S.ncard) :
    coff S off tgt (t + 1) = coff S off tgt t + (crowL S off tgt t).length := by
  rw [coff, coff, min_eq_left (by omega), min_eq_left (by omega), offList_succ]

private theorem coff_eq_offList {a : ℕ} (ha : a ≤ S.ncard) :
    coff S off tgt a = offList (crowL S off tgt) a := by
  rw [coff, min_eq_left ha]

private theorem coff_mono {a b : ℕ} (h : a ≤ b) :
    coff S off tgt a ≤ coff S off tgt b :=
  offList_mono _ (by omega)

private theorem coff_last : coff S off tgt S.ncard = cns S off tgt := rfl

private theorem callL_length : (callL S off tgt).length = cns S off tgt := by
  rw [callL, length_flatMap_range, cns, coff_eq_offList S off tgt le_rfl]

/-- The slice reading: the child target at `coff t + m` is row `t`'s
`m`-th entry. -/
private theorem ctgt_slice {t m : ℕ} (ht : t < S.ncard)
    (hm : m < (crowL S off tgt t).length) :
    ctgt S off tgt (coff S off tgt t + m) = (crowL S off tgt t).getD m 0 := by
  rw [ctgt, callL, coff_eq_offList S off tgt (by omega)]
  exact getD_flatMap_range _ ht hm

/-- The row view of the child CSR functions is the emitted row. -/
private theorem row_coff_ctgt {t : ℕ} (ht : t < S.ncard) :
    Csr.row (coff S off tgt) (ctgt S off tgt) t = crowL S off tgt t := by
  have hlen : Csr.rowLen (coff S off tgt) t = (crowL S off tgt t).length := by
    rw [Csr.rowLen, coff_succ S off tgt ht]
    omega
  rw [Csr.row, hlen]
  have hpt : ∀ m < (crowL S off tgt t).length,
      ctgt S off tgt (coff S off tgt t + m) = (crowL S off tgt t).getD m 0 :=
    fun m hm => ctgt_slice S off tgt ht hm
  calc arrOf (crowL S off tgt t).length (fun m => ctgt S off tgt (coff S off tgt t + m))
      = arrOf (crowL S off tgt t).length (fun m => (crowL S off tgt t).getD m 0) :=
        arrOf_congr fun m hm => hpt m hm
    _ = crowL S off tgt t := arrOf_getD _

/-! ### §3a What the child rows are: the induced adjacency, renamed -/

/-- A `Nodup` list that lists exactly the neighbours has the degree as
its length (the counting step of `GraphCsr.ns_eq_sum_degree`, factored
for reuse at both CSRs). -/
private theorem length_eq_degree {N : ℕ} {G : SimpleGraph (Fin N)} [DecidableRel G.Adj]
    (v : Fin N) {L : List ℕ} (hnd : L.Nodup)
    (hadj : ∀ w : ℕ, w ∈ L ↔ ∃ hw : w < N, G.Adj v ⟨w, hw⟩) :
    L.length = G.degree v := by
  classical
  have hcard : L.toFinset.card = L.length := List.toFinset_card_of_nodup hnd
  have hset : L.toFinset
      = (G.neighborFinset v).map (⟨Fin.val, Fin.val_injective⟩ : Fin N ↪ ℕ) := by
    ext w
    simp only [List.mem_toFinset, hadj, Finset.mem_map,
      SimpleGraph.mem_neighborFinset, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hw, hAdj⟩
      exact ⟨⟨w, hw⟩, hAdj, rfl⟩
    · rintro ⟨u, hAdj, rfl⟩
      exact ⟨u.2, by simpa using hAdj⟩
  rw [← hcard, hset, Finset.card_map]
  rfl

/-- Reading a row entry back as a target. -/
private theorem row_getD {off tgt : ℕ → ℕ} {v m : ℕ} (hm : m < Csr.rowLen off v) :
    (Csr.row off tgt v).getD m 0 = tgt (off v + m) := by
  rw [Csr.row, getD_arrOf _ hm]

variable {G : SimpleGraph (Fin n)}

/-- **The emitted row is the induced adjacency, renamed**: `w'` is in
child row `t` iff the two members are adjacent in the parent. -/
private theorem mem_crowL_iff
    (hadj : ∀ (v : Fin n) (w : ℕ), w ∈ Csr.row off tgt v ↔ ∃ hw : w < n, G.Adj v ⟨w, hw⟩)
    {t : ℕ} (ht : t < S.ncard) (w' : ℕ) :
    w' ∈ crowL S off tgt t ↔
      ∃ hw' : w' < S.ncard,
        G.Adj (Impl.restrictEmb S ⟨t, ht⟩) (Impl.restrictEmb S ⟨w', hw'⟩) := by
  rw [crowL, List.mem_filterMap]
  constructor
  · rintro ⟨w, hwrow, hopt⟩
    obtain ⟨hm, hw, hemb⟩ := rkOpt_eq_some S hopt
    refine ⟨hm, ?_⟩
    rw [embN_of_lt S ht] at hwrow
    obtain ⟨hw2, hA⟩ := (hadj _ w).mp hwrow
    rw [hemb]
    exact hA
  · rintro ⟨hw', hA⟩
    refine ⟨(Impl.restrictEmb S ⟨w', hw'⟩ : ℕ), ?_, ?_⟩
    · rw [embN_of_lt S ht]
      refine (hadj _ _).mpr ⟨(Impl.restrictEmb S ⟨w', hw'⟩).2, ?_⟩
      simpa using hA
    · simpa using rkOpt_emb S ⟨w', hw'⟩

/-- The emitted rows are duplicate-free (the parent rows are, and the
renaming is injective). -/
private theorem crowL_nodup (hnd : ∀ v : Fin n, (Csr.row off tgt v).Nodup)
    {t : ℕ} (ht : t < S.ncard) : (crowL S off tgt t).Nodup := by
  refine List.Nodup.filterMap
    (fun a a' b hb hb' => rkOpt_inj S (Option.mem_def.mp hb) (Option.mem_def.mp hb')) ?_
  have := hnd ⟨embN S t, embN_lt S ht⟩
  simpa using this

/-- Every emitted entry is a local name. -/
private theorem crowL_lt {t w' : ℕ} (h : w' ∈ crowL S off tgt t) : w' < S.ncard := by
  rw [crowL, List.mem_filterMap] at h
  obtain ⟨w, -, hopt⟩ := h
  obtain ⟨hm, -, -⟩ := rkOpt_eq_some S hopt
  exact hm

private theorem ctgt_lt {p : ℕ} (hp : p < cns S off tgt) :
    ctgt S off tgt p < S.ncard := by
  have hlen : p < (callL S off tgt).length := by rw [callL_length]; exact hp
  have hmem : ctgt S off tgt p ∈ callL S off tgt := by
    rw [ctgt, getD_eq_getElem hlen]
    exact List.getElem_mem hlen
  obtain ⟨u, hu, hx⟩ := mem_flatMap_range hmem
  exact crowL_lt S off tgt hx

private theorem coff_le_cns (a : ℕ) : coff S off tgt a ≤ cns S off tgt := by
  rw [cns, coff_eq_offList S off tgt le_rfl, coff]
  exact offList_mono _ (min_le_right a _)

/-! ### §3b The counting side: slot count and the row-scan bill -/

/-- The child slot count never exceeds the parent's — the machine's
write cursor stays inside the child target region. -/
private theorem cns_le_ns {o t' : String} {ns : ℕ} {σ : Env}
    (hc : Csr o t' n ns n off tgt σ) : cns S off tgt ≤ ns := by
  classical
  have h1 : cns S off tgt = ∑ u ∈ Finset.range S.ncard, (crowL S off tgt u).length := by
    rw [cns, coff_eq_offList S off tgt le_rfl, offList_eq_sum]
  have h2 : ∀ u ∈ Finset.range S.ncard,
      (crowL S off tgt u).length ≤ Csr.rowLen off (embN S u) := by
    intro u _
    rw [crowL]
    calc ((Csr.row off tgt (embN S u)).filterMap (rkOpt S)).length
        ≤ (Csr.row off tgt (embN S u)).length := List.length_filterMap_le _ _
      _ = Csr.rowLen off (embN S u) := Csr.length_row off tgt _
  have hinj : ∀ a ∈ Finset.range S.ncard, ∀ b ∈ Finset.range S.ncard,
      embN S a = embN S b → a = b := by
    intro a ha b hb hab
    have ha' := Finset.mem_range.mp ha
    have hb' := Finset.mem_range.mp hb
    rw [embN_of_lt S ha', embN_of_lt S hb'] at hab
    have h4 : Impl.restrictEmb S ⟨a, ha'⟩ = Impl.restrictEmb S ⟨b, hb'⟩ :=
      Fin.val_injective hab
    exact congrArg Fin.val ((Impl.restrictEmb S).injective h4)
  have h3 : ∑ u ∈ Finset.range S.ncard, Csr.rowLen off (embN S u)
      = ∑ v ∈ (Finset.range S.ncard).image (embN S), Csr.rowLen off v :=
    (Finset.sum_image hinj).symm
  have hsub : (Finset.range S.ncard).image (embN S) ⊆ Finset.range n := by
    intro v hv
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
    exact Finset.mem_range.mpr (embN_lt S (Finset.mem_range.mp hu))
  have h5 : ∑ v ∈ (Finset.range S.ncard).image (embN S), Csr.rowLen off v
      ≤ ∑ v ∈ Finset.range n, Csr.rowLen off v :=
    Finset.sum_le_sum_of_subset hsub
  have h6 : ∑ v ∈ Finset.range n, Csr.rowLen off v = off n - off 0 :=
    Csr.sum_rowLen hc n le_rfl
  have h7 : off n = ns := hc.last
  calc cns S off tgt
      = ∑ u ∈ Finset.range S.ncard, (crowL S off tgt u).length := h1
    _ ≤ ∑ u ∈ Finset.range S.ncard, Csr.rowLen off (embN S u) := Finset.sum_le_sum h2
    _ = ∑ v ∈ (Finset.range S.ncard).image (embN S), Csr.rowLen off v := h3
    _ ≤ ∑ v ∈ Finset.range n, Csr.rowLen off v := h5
    _ = off n - off 0 := h6
    _ ≤ ns := by omega

/-- **The row-scan bill IS `Σ_{s∈S} deg_A(s)`** — the machine's scans
sum the *parent* row lengths of the members, and that sum is exactly
`Impl.degSum` (the `O(‖A[S]‖+|S|)` shape never appears). -/
private theorem sum_rowLen_emb_eq_degSum [DecidableRel G.Adj]
    (hnd : ∀ v : Fin n, (Csr.row off tgt v).Nodup)
    (hadj : ∀ (v : Fin n) (w : ℕ), w ∈ Csr.row off tgt v ↔ ∃ hw : w < n, G.Adj v ⟨w, hw⟩) :
    ∑ u ∈ Finset.range S.ncard, Csr.rowLen off (embN S u) = Impl.degSum G S := by
  classical
  have hrl : ∀ v : Fin n, Csr.rowLen off (v : ℕ) = G.degree v := by
    intro v
    have hlen : (Csr.row off tgt (v : ℕ)).length = Csr.rowLen off (v : ℕ) :=
      Csr.length_row off tgt _
    rw [← hlen]
    exact length_eq_degree v (hnd v) (hadj v)
  have h1 : ∑ u ∈ Finset.range S.ncard, Csr.rowLen off (embN S u)
      = ∑ u : Fin S.ncard, Csr.rowLen off (embN S (u : ℕ)) :=
    (Fin.sum_univ_eq_sum_range (fun u => Csr.rowLen off (embN S u)) S.ncard).symm
  have h2 : ∀ u : Fin S.ncard,
      Csr.rowLen off (embN S (u : ℕ)) = G.degree (Impl.restrictEmb S u) := by
    intro u
    rw [embN_of_lt S u.2, show (⟨(u : ℕ), u.2⟩ : Fin S.ncard) = u from Fin.ext rfl]
    exact hrl _
  haveI : Fintype ↥S := (Set.toFinite S).fintype
  have h3 : ∑ u : Fin S.ncard, G.degree (Impl.restrictEmb S u)
      = ∑ x : ↥S, G.degree (x : Fin n) := by
    have h := Equiv.sum_comp (Driver.setEquiv S) (fun x : ↥S => G.degree (x : Fin n))
    calc ∑ u : Fin S.ncard, G.degree (Impl.restrictEmb S u)
        = ∑ u : Fin S.ncard, G.degree ((Driver.setEquiv S u : ↥S) : Fin n) :=
          Finset.sum_congr rfl fun u _ => by rw [Impl.restrictEmb_apply]
      _ = ∑ x : ↥S, G.degree (x : Fin n) := h
  have h4 : ∑ x : ↥S, G.degree (x : Fin n)
      = ∑ s ∈ (Set.toFinite S).toFinset, G.degree s := by
    rw [← Finset.sum_coe_sort ((Set.toFinite S).toFinset) (fun s => G.degree s)]
    refine Fintype.sum_equiv
      (Equiv.setCongr (Set.Finite.coe_toFinset (Set.toFinite S)).symm) _ _ ?_
    intro x
    rfl
  rw [h1, Finset.sum_congr rfl fun u _ => h2 u, h3, h4, Impl.degSum]

end ChildRows

/-! ## §4 Kept prefixes

The bookkeeping of a filtered fill: after the machine has consumed `m`
slots of a source list, the destination holds the filtered prefix. -/

section Kept

/-- How many of the first `m` entries the partial map keeps. -/
private def keptLen (F : ℕ → Option ℕ) (l : List ℕ) (m : ℕ) : ℕ :=
  ((l.take m).filterMap F).length

@[simp] private theorem keptLen_zero (F : ℕ → Option ℕ) (l : List ℕ) :
    keptLen F l 0 = 0 := rfl

private theorem take_succ_getD {l : List ℕ} {m : ℕ} (hm : m < l.length) :
    l.take (m + 1) = l.take m ++ [l.getD m 0] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hm, getD_eq_getElem hm]
  rfl

private theorem filterMap_singleton_none {F : ℕ → Option ℕ} {x : ℕ}
    (h : F x = none) : List.filterMap F [x] = [] := by
  simp [h]

private theorem filterMap_singleton_some {F : ℕ → Option ℕ} {x v : ℕ}
    (h : F x = some v) : List.filterMap F [x] = [v] := by
  simp [h]

private theorem keptLen_succ_none {F : ℕ → Option ℕ} {l : List ℕ} {m : ℕ}
    (hm : m < l.length) (h : F (l.getD m 0) = none) :
    keptLen F l (m + 1) = keptLen F l m := by
  rw [keptLen, take_succ_getD hm, List.filterMap_append,
    filterMap_singleton_none h, List.append_nil]
  rfl

private theorem keptLen_succ_some {F : ℕ → Option ℕ} {l : List ℕ} {m v : ℕ}
    (hm : m < l.length) (h : F (l.getD m 0) = some v) :
    keptLen F l (m + 1) = keptLen F l m + 1 := by
  rw [keptLen, take_succ_getD hm, List.filterMap_append,
    filterMap_singleton_some h, List.length_append]
  rfl

/-- The kept prefix never outgrows the whole filtered list. -/
private theorem keptLen_le (F : ℕ → Option ℕ) (l : List ℕ) (m : ℕ) :
    keptLen F l m ≤ (l.filterMap F).length := by
  conv_rhs => rw [← List.take_append_drop m l]
  rw [List.filterMap_append, List.length_append]
  exact Nat.le_add_right _ _

/-- Consuming the whole source keeps the whole filtered list. -/
private theorem keptLen_full (F : ℕ → Option ℕ) (l : List ℕ) :
    keptLen F l l.length = (l.filterMap F).length := by
  rw [keptLen, List.take_length]

/-- **The write-target identity**: when slot `m` is kept with value `v`,
the filtered list's entry at the current kept count is `v`. -/
private theorem filterMap_getD_kept {F : ℕ → Option ℕ} {l : List ℕ} {m v : ℕ}
    (hm : m < l.length) (h : F (l.getD m 0) = some v) :
    (l.filterMap F).getD (keptLen F l m) 0 = v := by
  have hsplit : l.filterMap F
      = (l.take m).filterMap F ++ ([l.getD m 0].filterMap F ++ (l.drop (m + 1)).filterMap F) := by
    conv_lhs => rw [← List.take_append_drop (m + 1) l]
    rw [take_succ_getD hm, List.filterMap_append, List.filterMap_append,
      List.append_assoc]
  have hlen : keptLen F l m = ((l.take m).filterMap F).length := rfl
  rw [hsplit, hlen, List.getD_append_right _ _ _ _ le_rfl, Nat.sub_self,
    filterMap_singleton_some h]
  rfl

end Kept

/-! ## §5 The programs -/

/-- The routine's scratch cells (fixed names; every array is a
parameter): outer index, round index, entry index, the member's parent
name, the slot pointer, the row end, the slot value, the rank read, the
write cursor, the kept count, the two block bases, and the four inputs
`|S|`/`Λ`/`ℓp`/`hb`. -/
def rsScalars : List String :=
  ["rs.i", "rs.q", "rs.d", "rs.s", "rs.j", "rs.e", "rs.w", "rs.x",
    "rs.c", "rs.t", "rs.a", "rs.b", "rs.k", "rs.l", "rs.p", "rs.h"]

/-- Mark the cluster on the rank scratch: entry `la[i]` gets `i + 1` —
`|S|` writes, never a carrier-sized wipe. -/
def rankMark (la ra : String) : Com :=
  .seq (.assign "rs.i" (.lit 0))
    (.while (.lt (.var "rs.i") (.var "rs.k"))
      (.seq (.assign "rs.s" (.get la (.var "rs.i")))
        (.seq (.store ra (.var "rs.s") (.add (.var "rs.i") (.lit 1)))
          (.assign "rs.i" (.add (.var "rs.i") (.lit 1))))))

/-- Clear the scratch at exactly the `|S|` touched entries — the
self-cleaning half of the one-scratch-array contract. -/
def rankClear (la ra : String) : Com :=
  .seq (.assign "rs.i" (.lit 0))
    (.while (.lt (.var "rs.i") (.var "rs.k"))
      (.seq (.assign "rs.s" (.get la (.var "rs.i")))
        (.seq (.store ra (.var "rs.s") (.lit 0))
          (.assign "rs.i" (.add (.var "rs.i") (.lit 1))))))

/-- One slot of a member's row scan: read the target, read its rank;
if marked, emit the local name and advance the cursor; advance the
slot pointer. The membership test IS the rank read. -/
def csrSlot (nmP nmC : ArenaNames) (ra : String) : Com :=
  .seq (Csr.slot nmP.tgt "rs.j" "rs.w")
    (.seq (.assign "rs.x" (.get ra (.var "rs.w")))
      (.seq (.ite (.lt (.lit 0) (.var "rs.x"))
          (.seq (.store nmC.tgt (.var "rs.c") (.sub (.var "rs.x") (.lit 1)))
            (.assign "rs.c" (.add (.var "rs.c") (.lit 1))))
          .skip)
        (.assign "rs.j" (.add (.var "rs.j") (.lit 1)))))

/-- One member of the CSR build: load the parent row's bounds, scan it
through the scratch, seal the child row boundary. -/
def csrFillBody (nmP nmC : ArenaNames) (la ra : String) : Com :=
  .seq (.assign "rs.s" (.get la (.var "rs.i")))
    (.seq (Csr.loadRow nmP.off "rs.s" "rs.j" "rs.e")
      (.seq (Csr.scan "rs.j" "rs.e" (csrSlot nmP nmC ra))
        (.seq (.store nmC.off (.add (.var "rs.i") (.lit 1)) (.var "rs.c"))
          (.assign "rs.i" (.add (.var "rs.i") (.lit 1))))))

/-- The child CSR, built in one fused count/fill pass: rows are emitted
in enumeration order, so each row's boundary is sealed as the cursor
passes it. -/
def csrFill (nmP nmC : ArenaNames) (la ra : String) : Com :=
  .seq (.assign "rs.c" (.lit 0))
    (.seq (.store nmC.off (.lit 0) (.lit 0))
      (.seq (.assign "rs.i" (.lit 0))
        (.while (.lt (.var "rs.i") (.var "rs.k")) (csrFillBody nmP nmC la ra))))

/-- One member of the color copy: the member's whole color row, cell by
cell. -/
def colCopyBody (nmP nmC : ArenaNames) (la : String) : Com :=
  .seq (.assign "rs.s" (.get la (.var "rs.i")))
    (.seq (.seq (.assign "rs.q" (.lit 0))
        (.while (.lt (.var "rs.q") (.var "rs.l"))
          (.seq (.store nmC.col
              (.add (.mul (.var "rs.i") (.var "rs.l")) (.var "rs.q"))
              (.get nmP.col (.add (.mul (.var "rs.s") (.var "rs.l")) (.var "rs.q"))))
            (.assign "rs.q" (.add (.var "rs.q") (.lit 1))))))
      (.assign "rs.i" (.add (.var "rs.i") (.lit 1))))

/-- The color rows, copied. -/
def colCopy (nmP nmC : ArenaNames) (la : String) : Com :=
  .seq (.assign "rs.i" (.lit 0))
    (.while (.lt (.var "rs.i") (.var "rs.k")) (colCopyBody nmP nmC la))

/-- The root renaming, composed: the child's entry is the parent's at
the member. -/
def upCopy (nmP nmC : ArenaNames) (la : String) : Com :=
  .seq (.assign "rs.i" (.lit 0))
    (.while (.lt (.var "rs.i") (.var "rs.k"))
      (.seq (.assign "rs.s" (.get la (.var "rs.i")))
        (.seq (.store nmC.up (.var "rs.i") (.get nmP.up (.var "rs.s")))
          (.assign "rs.i" (.add (.var "rs.i") (.lit 1))))))

/-- One stored name of a channel list: read it, read its rank; if
marked, emit the local name. -/
def histSlot (nmP nmC : ArenaNames) (ra : String) : Com :=
  .seq (.assign "rs.w" (.get nmP.hist (.add (.var "rs.a") (.add (.var "rs.d") (.lit 1)))))
    (.seq (.assign "rs.x" (.get ra (.var "rs.w")))
      (.seq (.ite (.lt (.lit 0) (.var "rs.x"))
          (.seq (.store nmC.hist (.add (.var "rs.b") (.add (.var "rs.t") (.lit 1)))
              (.sub (.var "rs.x") (.lit 1)))
            (.assign "rs.t" (.add (.var "rs.t") (.lit 1))))
          .skip)
        (.assign "rs.d" (.add (.var "rs.d") (.lit 1)))))

/-- One `(member, round)` slot of the channel filter: locate the two
blocks, read the stored length, filter the list in order, store the
kept count as the child's length prefix. -/
def histRound (nmP nmC : ArenaNames) (ra : String) : Com :=
  .seq (.assign "rs.a" (.mul (.add (.mul (.var "rs.s") (.var "rs.p")) (.var "rs.q"))
      (.add (.var "rs.h") (.lit 1))))
    (.seq (.assign "rs.b" (.mul (.add (.mul (.var "rs.i") (.var "rs.p")) (.var "rs.q"))
        (.add (.var "rs.h") (.lit 1))))
      (.seq (.assign "rs.e" (.get nmP.hist (.var "rs.a")))
        (.seq (.assign "rs.t" (.lit 0))
          (.seq (.seq (.assign "rs.d" (.lit 0))
              (.while (.lt (.var "rs.d") (.var "rs.e")) (histSlot nmP nmC ra)))
            (.store nmC.hist (.var "rs.b") (.var "rs.t"))))))

/-- One member of the channel filter: all its rounds. -/
def histBody (nmP nmC : ArenaNames) (la ra : String) : Com :=
  .seq (.assign "rs.s" (.get la (.var "rs.i")))
    (.seq (.seq (.assign "rs.q" (.lit 0))
        (.while (.lt (.var "rs.q") (.var "rs.p"))
          (.seq (histRound nmP nmC ra)
            (.assign "rs.q" (.add (.var "rs.q") (.lit 1))))))
      (.assign "rs.i" (.add (.var "rs.i") (.lit 1))))

/-- The channel, filtered per vertex and per round, in order. -/
def histFilter (nmP nmC : ArenaNames) (la ra : String) : Com :=
  .seq (.assign "rs.i" (.lit 0))
    (.while (.lt (.var "rs.i") (.var "rs.k")) (histBody nmP nmC la ra))

/-- The child's two scalar cells: the carrier size and the slot count. -/
def sizeCells (nmC : ArenaNames) : Com :=
  .seq (.assign nmC.nN (.var "rs.k")) (.assign nmC.nS (.var "rs.c"))

/-- **`restrict`, as IMP+**: mark the cluster on the one scratch array,
build the child CSR by row scans through it, copy the color rows,
compose the renaming, filter the channel, clear the scratch at exactly
the touched entries, seal the child's scalar cells. -/
def restrictCom (nmP nmC : ArenaNames) (la ra : String) : Com :=
  .seq (rankMark la ra)
    (.seq (csrFill nmP nmC la ra)
      (.seq (colCopy nmP nmC la)
        (.seq (upCopy nmP nmC la)
          (.seq (histFilter nmP nmC la ra)
            (.seq (rankClear la ra) (sizeCells nmC))))))

/-! ## §6 The cluster region, and two evaluation helpers -/

/-- **The cluster's enumeration region** (the cover slot's output, as
`restrict` consumes it): entry `t` is the `t`-th member in the child
enumeration `restrictEmb`'s order. The enumeration is *data* — see the
module docstring's seam note on `Driver.setEquiv`. -/
def ClusterList (la : String) {n : ℕ} (S : Set (Fin n)) (σ : Env) : Prop :=
  S.ncard ≤ (σ.arrs la).length ∧
    ∀ t : ℕ, ∀ ht : t < S.ncard,
      (σ.arrs la).getD t 0 = (Impl.restrictEmb S ⟨t, ht⟩ : ℕ)

section Phases

variable {B n : ℕ} {S : Set (Fin n)} {la ra : String}

private theorem getElem?_eq_getD {l : List ℕ} {i : ℕ} (h : i < l.length) :
    l[i]? = some (l.getD i 0) := by
  rw [List.getElem?_eq_getElem h, getD_eq_getElem h]

private theorem evalB_incr {B : ℕ} {x : String} {σ : Env}
    (hx : σ.vars x + 1 < B) :
    (Expr.add (.var x) (.lit 1)).evalB B σ = some (σ.vars x + 1) := by
  have h := evalB_bin (B := B) (op := .add) (e := .var x) (f := .lit 1) (σ := σ)
    (evalB_var (by omega)) (evalB_lit (by omega)) (by simpa using hx)
  simpa using h

private theorem clusterList_read {σ : Env} (h : ClusterList la S σ) {t : ℕ}
    (ht : t < S.ncard) : (σ.arrs la)[t]? = some (embN S t) := by
  rw [getElem?_eq_getD (lt_of_lt_of_le ht h.1), h.2 t ht, embN_of_lt S ht]

/-! ## §7 The mark and the clear -/

/-- The mark's progress: ranks up to the counter are on the scratch,
everything else still reads `0`. -/
private noncomputable def rkP (S : Set (Fin n)) (i w : ℕ) : ℕ :=
  if rk S w ≤ i then rk S w else 0

private theorem rkP_zero (S : Set (Fin n)) (w : ℕ) : rkP S 0 w = 0 := by
  rw [rkP]
  split <;> omega

private theorem rkP_full (S : Set (Fin n)) {i : ℕ} (hi : S.ncard ≤ i) (w : ℕ) :
    rkP S i w = rk S w := by
  rw [rkP, if_pos (le_trans (rk_le S w) hi)]

/-- Nobody but the `i`-th member carries rank `i + 1`. -/
private theorem rk_eq_succ_elim (S : Set (Fin n)) {i w : ℕ} (hi : i < S.ncard)
    (h : rk S w = i + 1) : w = embN S i := by
  have hopt := rk_pos_elim S h (by omega)
  simp only [Nat.add_sub_cancel] at hopt
  obtain ⟨hm, hw, hemb⟩ := rkOpt_eq_some S hopt
  rw [embN_of_lt S hi]
  rw [show (⟨i, hi⟩ : Fin S.ncard) = ⟨i, hm⟩ from Fin.ext rfl, hemb]

/-- One mark extends the progress function by one rank. -/
private theorem rkP_step (S : Set (Fin n)) {i : ℕ} (hi : i < S.ncard) :
    ∀ p, p < n → (if p = embN S i then i + 1 else rkP S i p) = rkP S (i + 1) p := by
  intro p _
  by_cases hp : p = embN S i
  · subst hp
    have hrk : rk S (embN S i) = i + 1 := by
      rw [embN_of_lt S hi]
      exact rk_emb S ⟨i, hi⟩
    rw [if_pos rfl, rkP, hrk, if_pos le_rfl]
  · rw [if_neg hp, rkP, rkP]
    by_cases hle : rk S p ≤ i
    · rw [if_pos hle, if_pos (by omega)]
    · rw [if_neg hle, if_neg ?_]
      intro hle'
      have : rk S p = i + 1 := by omega
      exact hp (rk_eq_succ_elim S hi this)

/-- **The mark pass**: from a clean scratch, the rank table — `|S|`
writes, cost linear in `|S|` alone. -/
private theorem rankMark_spec (hNB : n < B) (hla_ra : la ≠ ra) :
    Spec B
      (fun σ => ClusterList la S σ ∧ σ.vars "rs.k" = S.ncard ∧
        σ.arrs ra = arrOf n fun _ => 0)
      (rankMark la ra)
      (fun _ σ' => ClusterList la S σ' ∧ σ'.vars "rs.k" = S.ncard ∧
        σ'.arrs ra = arrOf n (rk S))
      (16 * S.ncard + 6) := by
  have hkn : S.ncard ≤ n := ncard_le_carrier S
  set I : Env → Prop := fun σ =>
    ClusterList la S σ ∧ σ.vars "rs.k" = S.ncard ∧ σ.vars "rs.i" ≤ S.ncard ∧
      σ.arrs ra = arrOf n (rkP S (σ.vars "rs.i")) with hI
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "rs.i" < S.ncard)
      (.seq (.assign "rs.s" (.get la (.var "rs.i")))
        (.seq (.store ra (.var "rs.s") (.add (.var "rs.i") (.lit 1)))
          (.assign "rs.i" (.add (.var "rs.i") (.lit 1)))))
      (fun σ σ' => I σ' ∧ σ'.vars "rs.i" = σ.vars "rs.i" + 1) 12 := by
    intro σ hσ
    obtain ⟨⟨hcl, hk, hiN, hra⟩, hlt⟩ := hσ
    set i := σ.vars "rs.i" with hi_def
    have hsN : embN S i < n := embN_lt S hlt
    -- the member read
    have hread : Run B (.assign "rs.s" (.get la (.var "rs.i"))) σ
        (σ.setVar "rs.s" (embN S i)) 3 := by
      refine (Run.assign (evalB_get (evalB_var (by omega)) ?_ (by omega))).mono (by simp)
      exact clusterList_read hcl hlt
    set σ₁ := σ.setVar "rs.s" (embN S i) with hσ₁
    -- the mark
    have hst : Run B (.store ra (.var "rs.s") (.add (.var "rs.i") (.lit 1))) σ₁
        (σ₁.setArr ra (embN S i) (i + 1)) 5 := by
      have h1s : σ₁.vars "rs.s" = embN S i := by rw [hσ₁]; simp
      have hsev : (Expr.var "rs.s").evalB B σ₁ = some (embN S i) := by
        rw [← h1s]
        exact evalB_var (by rw [h1s]; omega)
      have hiev : (Expr.add (.var "rs.i") (.lit 1)).evalB B σ₁ = some (i + 1) := by
        have h1i : σ₁.vars "rs.i" = i := by rw [hσ₁]; simp [hi_def]
        have h := evalB_incr (B := B) (x := "rs.i") (σ := σ₁) (by rw [h1i]; omega)
        rwa [h1i] at h
      refine (Run.store hsev hiev ?_).mono (by simp)
      rw [hσ₁]
      simp only [arrs_setVar]
      rw [hra, length_arrOf]
      exact hsN
    set σ₂ := σ₁.setArr ra (embN S i) (i + 1) with hσ₂
    -- the counter
    have hinc : Run B (.assign "rs.i" (.add (.var "rs.i") (.lit 1))) σ₂
        (σ₂.setVar "rs.i" (i + 1)) 4 := by
      have h2i : σ₂.vars "rs.i" = i := by rw [hσ₂, hσ₁]; simp [hi_def]
      have hev := evalB_incr (B := B) (x := "rs.i") (σ := σ₂) (by rw [h2i]; omega)
      rw [h2i] at hev
      exact (Run.assign hev).mono (by simp)
    refine ⟨_, (hread.seq (hst.seq hinc)).mono (by omega), ⟨?_, ?_, ?_, ?_⟩,
      by simp [hσ₂, hσ₁, ← hi_def]⟩
    · -- the list region is untouched
      refine ⟨?_, ?_⟩ <;>
        simp only [hσ₂, hσ₁, arrs_setVar, arrs_setArr, if_neg hla_ra]
      · exact hcl.1
      · exact hcl.2
    · simp [hσ₂, hσ₁, hk]
    · simp [hσ₂, hσ₁]; omega
    · have h'i : (σ₂.setVar "rs.i" (i + 1)).vars "rs.i" = i + 1 := by simp
      have h'ra : (σ₂.setVar "rs.i" (i + 1)).arrs ra
          = (σ.arrs ra).set (embN S i) (i + 1) := by
        rw [arrs_setVar, hσ₂, hσ₁]
        simp
      rw [h'ra, h'i, hra, set_arrOf]
      exact arrOf_congr fun p hp => rkP_step S hlt p hp
  have hmain := Spec.forRangeZero (B := B) "rs.i" "rs.k" I S.ncard 12
    (by omega) (fun σ hσ => hσ.2.2.1) (fun σ hσ => hσ.2.1) hbody
  refine ((hmain.pre ?_).post ?_).mono le_rfl
  · rintro σ ⟨hcl, hk, hra⟩
    refine ⟨⟨by simpa using hcl.1, fun t ht => by simpa using hcl.2 t ht⟩,
      by simp [hk], by simp, ?_⟩
    simp only [arrs_setVar, vars_setVar, if_pos rfl]
    rw [hra]
    exact arrOf_congr fun p hp => (rkP_zero S p).symm
  · rintro σ σ' - ⟨⟨hcl, hk, -, hra⟩, hie⟩
    refine ⟨hcl, hk, ?_⟩
    rw [hra, hie]
    exact arrOf_congr fun p hp => rkP_full S le_rfl p

/-- The clear's progress: ranks up to the counter are wiped again. -/
private noncomputable def rkC (S : Set (Fin n)) (i w : ℕ) : ℕ :=
  if rk S w ≤ i then 0 else rk S w

private theorem rkC_zero (S : Set (Fin n)) (w : ℕ) : rkC S 0 w = rk S w := by
  rw [rkC]
  split <;> omega

private theorem rkC_full (S : Set (Fin n)) {i : ℕ} (hi : S.ncard ≤ i) (w : ℕ) :
    rkC S i w = 0 := by
  rw [rkC, if_pos (le_trans (rk_le S w) hi)]

private theorem rkC_step (S : Set (Fin n)) {i : ℕ} (hi : i < S.ncard) :
    ∀ p, p < n → (if p = embN S i then 0 else rkC S i p) = rkC S (i + 1) p := by
  intro p _
  by_cases hp : p = embN S i
  · subst hp
    have hrk : rk S (embN S i) = i + 1 := by
      rw [embN_of_lt S hi]
      exact rk_emb S ⟨i, hi⟩
    rw [if_pos rfl, rkC, hrk, if_pos (by omega)]
  · rw [if_neg hp, rkC, rkC]
    by_cases hle : rk S p ≤ i
    · rw [if_pos hle, if_pos (by omega)]
    · rw [if_neg hle, if_neg ?_]
      intro hle'
      have : rk S p = i + 1 := by omega
      exact hp (rk_eq_succ_elim S hi this)

/-- **The clear pass** — the self-cleaning seam rule: the scratch is
restored to all-zeros by touching exactly the `|S|` marked entries. -/
private theorem rankClear_spec (hNB : n < B) (hla_ra : la ≠ ra) :
    Spec B
      (fun σ => ClusterList la S σ ∧ σ.vars "rs.k" = S.ncard ∧
        σ.arrs ra = arrOf n (rk S))
      (rankClear la ra)
      (fun _ σ' => ClusterList la S σ' ∧ σ'.vars "rs.k" = S.ncard ∧
        σ'.arrs ra = arrOf n fun _ => 0)
      (14 * S.ncard + 6) := by
  have hkn : S.ncard ≤ n := ncard_le_carrier S
  set I : Env → Prop := fun σ =>
    ClusterList la S σ ∧ σ.vars "rs.k" = S.ncard ∧ σ.vars "rs.i" ≤ S.ncard ∧
      σ.arrs ra = arrOf n (rkC S (σ.vars "rs.i")) with hI
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "rs.i" < S.ncard)
      (.seq (.assign "rs.s" (.get la (.var "rs.i")))
        (.seq (.store ra (.var "rs.s") (.lit 0))
          (.assign "rs.i" (.add (.var "rs.i") (.lit 1)))))
      (fun σ σ' => I σ' ∧ σ'.vars "rs.i" = σ.vars "rs.i" + 1) 10 := by
    intro σ hσ
    obtain ⟨⟨hcl, hk, hiN, hra⟩, hlt⟩ := hσ
    set i := σ.vars "rs.i" with hi_def
    have hsN : embN S i < n := embN_lt S hlt
    have hread : Run B (.assign "rs.s" (.get la (.var "rs.i"))) σ
        (σ.setVar "rs.s" (embN S i)) 3 := by
      refine (Run.assign (evalB_get (evalB_var (by omega)) ?_ (by omega))).mono (by simp)
      exact clusterList_read hcl hlt
    set σ₁ := σ.setVar "rs.s" (embN S i) with hσ₁
    have hst : Run B (.store ra (.var "rs.s") (.lit 0)) σ₁
        (σ₁.setArr ra (embN S i) 0) 3 := by
      have h1s : σ₁.vars "rs.s" = embN S i := by rw [hσ₁]; simp
      have hsev : (Expr.var "rs.s").evalB B σ₁ = some (embN S i) := by
        rw [← h1s]
        exact evalB_var (by rw [h1s]; omega)
      refine (Run.store hsev (evalB_lit (by omega)) ?_).mono (by simp)
      rw [hσ₁]
      simp only [arrs_setVar]
      rw [hra, length_arrOf]
      exact hsN
    set σ₂ := σ₁.setArr ra (embN S i) 0 with hσ₂
    have hinc : Run B (.assign "rs.i" (.add (.var "rs.i") (.lit 1))) σ₂
        (σ₂.setVar "rs.i" (i + 1)) 4 := by
      have h2i : σ₂.vars "rs.i" = i := by rw [hσ₂, hσ₁]; simp [hi_def]
      have hev := evalB_incr (B := B) (x := "rs.i") (σ := σ₂) (by rw [h2i]; omega)
      rw [h2i] at hev
      exact (Run.assign hev).mono (by simp)
    refine ⟨_, (hread.seq (hst.seq hinc)).mono (by omega), ⟨?_, ?_, ?_, ?_⟩,
      by simp [hσ₂, hσ₁, ← hi_def]⟩
    · refine ⟨?_, ?_⟩ <;>
        simp only [hσ₂, hσ₁, arrs_setVar, arrs_setArr, if_neg hla_ra]
      · exact hcl.1
      · exact hcl.2
    · simp [hσ₂, hσ₁, hk]
    · simp [hσ₂, hσ₁]; omega
    · have h'i : (σ₂.setVar "rs.i" (i + 1)).vars "rs.i" = i + 1 := by simp
      have h'ra : (σ₂.setVar "rs.i" (i + 1)).arrs ra
          = (σ.arrs ra).set (embN S i) 0 := by
        rw [arrs_setVar, hσ₂, hσ₁]
        simp
      rw [h'ra, h'i, hra, set_arrOf]
      exact arrOf_congr fun p hp => rkC_step S hlt p hp
  have hmain := Spec.forRangeZero (B := B) "rs.i" "rs.k" I S.ncard 10
    (by omega) (fun σ hσ => hσ.2.2.1) (fun σ hσ => hσ.2.1) hbody
  refine ((hmain.pre ?_).post ?_).mono le_rfl
  · rintro σ ⟨hcl, hk, hra⟩
    refine ⟨⟨by simpa using hcl.1, fun t ht => by simpa using hcl.2 t ht⟩,
      by simp [hk], by simp, ?_⟩
    simp only [arrs_setVar, vars_setVar, if_pos rfl]
    rw [hra]
    exact arrOf_congr fun p hp => (rkC_zero S p).symm
  · rintro σ σ' - ⟨⟨hcl, hk, -, hra⟩, hie⟩
    refine ⟨hcl, hk, ?_⟩
    rw [hra, hie]
    exact arrOf_congr fun p hp => rkC_full S le_rfl p

/-! ## §8 The CSR fill

One fused count/fill pass: rows are emitted in enumeration order, each
row a parent-row scan through the scratch, priced at the **parent**
degree of the member (the `O(‖A[S]‖+|S|)` shape is false — module
docstring). -/

/-- The mid-row state of the fill: parent CSR and inputs intact, the
member's row bounds loaded, the cursor at the emitted prefix, the two
child regions holding what has been sealed so far. -/
private structure RowSt (nmP nmC : ArenaNames) (la ra : String) (n ns : ℕ)
    (S : Set (Fin n)) (off tgt : ℕ → ℕ) (i : ℕ) (σ : Env) : Prop where
  hc : Csr nmP.off nmP.tgt n ns n off tgt σ
  hcl : ClusterList la S σ
  hk : σ.vars "rs.k" = S.ncard
  hra : σ.arrs ra = arrOf n (rk S)
  hiv : σ.vars "rs.i" = i
  hs : σ.vars "rs.s" = embN S i
  he : σ.vars "rs.e" = off (embN S i + 1)
  hjlo : off (embN S i) ≤ σ.vars "rs.j"
  hjhi : σ.vars "rs.j" ≤ off (embN S i + 1)
  hcv : σ.vars "rs.c" = coff S off tgt i
    + keptLen (rkOpt S) (Csr.row off tgt (embN S i)) (σ.vars "rs.j" - off (embN S i))
  hoff : ∃ f, σ.arrs nmC.off = arrOf (S.ncard + 1) f ∧
    ∀ a ≤ i, f a = coff S off tgt a
  htgt : ∃ g, σ.arrs nmC.tgt = arrOf (cns S off tgt) g ∧
    ∀ p < σ.vars "rs.c", g p = ctgt S off tgt p

/-- The between-members state of the fill. -/
private structure FillSt (nmP nmC : ArenaNames) (la ra : String) (n ns : ℕ)
    (S : Set (Fin n)) (off tgt : ℕ → ℕ) (σ : Env) : Prop where
  hc : Csr nmP.off nmP.tgt n ns n off tgt σ
  hcl : ClusterList la S σ
  hk : σ.vars "rs.k" = S.ncard
  hra : σ.arrs ra = arrOf n (rk S)
  hiN : σ.vars "rs.i" ≤ S.ncard
  hcv : σ.vars "rs.c" = coff S off tgt (σ.vars "rs.i")
  hoff : ∃ f, σ.arrs nmC.off = arrOf (S.ncard + 1) f ∧
    ∀ a ≤ σ.vars "rs.i", f a = coff S off tgt a
  htgt : ∃ g, σ.arrs nmC.tgt = arrOf (cns S off tgt) g ∧
    ∀ p < σ.vars "rs.c", g p = ctgt S off tgt p

section CsrFill

variable {B n ns : ℕ} {S : Set (Fin n)} {nmP nmC : ArenaNames} {la ra : String}
  {off tgt : ℕ → ℕ}

/-- **One slot of a member's row scan**: read the target, one scratch
lookup deciding membership and local name together; emit if marked. -/
private theorem csrSlot_step (hNB : n < B) (hnsB : ns < B)
    (h3 : nmC.tgt ≠ la) (h4 : nmC.tgt ≠ ra) (h5 : nmC.tgt ≠ nmC.off)
    (h1 : nmC.tgt ≠ nmP.off) (h2 : nmC.tgt ≠ nmP.tgt)
    {i : ℕ} (hik : i < S.ncard) :
    ∀ σ, RowSt nmP nmC la ra n ns S off tgt i σ →
      σ.vars "rs.j" < off (embN S i + 1) →
      ∃ σ' K', Run B (csrSlot nmP nmC ra) σ σ' K' ∧
        RowSt nmP nmC la ra n ns S off tgt i σ' ∧
        σ'.vars "rs.j" = σ.vars "rs.j" + 1 ∧ K' ≤ 23 := by
  intro σ hR hjlt
  obtain ⟨hc, hcl, hk, hra, hiv, hs, he, hjlo, hjhi, hcv, hoff, htgt⟩ := hR
  have hkn : S.ncard ≤ n := ncard_le_carrier S
  set s' := embN S i with hs'_def
  set jv := σ.vars "rs.j" with hjv_def
  have hs'n : s' < n := embN_lt S hik
  have hjns : jv < ns := lt_of_lt_of_le hjlt (hc.row_le hs'n)
  set w := tgt jv with hw_def
  have hwn : w < n := hc.target hjns
  set x := rk S w with hx_def
  have hxk : x ≤ S.ncard := rk_le S w
  -- the slot read
  have hread : Run B (Csr.slot nmP.tgt "rs.j" "rs.w") σ (σ.setVar "rs.w" w) 3 := by
    refine (Run.assign (evalB_get (evalB_var (by omega)) ?_ (by omega))).mono (by simp)
    rw [hc.tgtArr, getElem?_arrOf tgt hjns]
  set σa := σ.setVar "rs.w" w with hσa
  -- the rank read: the membership test and the renaming in one lookup
  have hxread : Run B (.assign "rs.x" (.get ra (.var "rs.w"))) σa
      (σa.setVar "rs.x" x) 3 := by
    have haw : σa.vars "rs.w" = w := by rw [hσa]; simp
    have hwev : (Expr.var "rs.w").evalB B σa = some w := by
      rw [← haw]
      exact evalB_var (by rw [haw]; omega)
    refine (Run.assign (evalB_get hwev ?_ (by omega))).mono (by simp)
    rw [hσa]
    simp only [arrs_setVar]
    rw [hra, getElem?_arrOf _ hwn]
  set σb := σa.setVar "rs.x" x with hσb
  have hbx : σb.vars "rs.x" = x := by rw [hσb]; simp
  have hbc : σb.vars "rs.c" = σ.vars "rs.c" := by rw [hσb, hσa]; simp
  have hbj : σb.vars "rs.j" = jv := by rw [hσb, hσa]; simp [hjv_def]
  have hbarrs : ∀ b, σb.arrs b = σ.arrs b := by intro b; rw [hσb, hσa]; simp
  -- the guard
  have hcond : (Cond.lt (.lit 0) (.var "rs.x")).evalB B σb
      = some (decide (0 < x)) := by
    refine evalB_condLt (evalB_lit (by omega)) ?_
    rw [← hbx]
    exact evalB_var (by rw [hbx]; omega)
  -- the row entry under the pointer
  set row := Csr.row off tgt s' with hrow_def
  set m := jv - off s' with hm_def
  have hmrow : m < row.length := by
    rw [hrow_def, Csr.length_row, Csr.rowLen]
    omega
  have hrow_m : row.getD m 0 = w := by
    rw [hrow_def, row_getD (by rw [Csr.rowLen]; omega)]
    congr 1
    omega
  obtain ⟨g, hgarr, hgpre⟩ := htgt
  by_cases hx0 : 0 < x
  · -- kept: emit the local name, advance the cursor
    have hcondT : (Cond.lt (.lit 0) (.var "rs.x")).evalB B σb = some true := by
      rw [hcond]
      congr 1
      simpa using hx0
    have hsome : rkOpt S (row.getD m 0) = some (x - 1) := by
      rw [hrow_m]
      exact rk_pos_elim S rfl hx0
    -- the cursor's bounds
    have hkept1 : keptLen (rkOpt S) row (m + 1) = keptLen (rkOpt S) row m + 1 :=
      keptLen_succ_some hmrow hsome
    have hkle : keptLen (rkOpt S) row m + 1 ≤ (crowL S off tgt i).length := by
      have h := keptLen_le (rkOpt S) row (m + 1)
      rw [hkept1] at h
      exact h
    have hclt : σ.vars "rs.c" < cns S off tgt := by
      rw [hcv]
      calc coff S off tgt i + keptLen (rkOpt S) row m
          < coff S off tgt i + (crowL S off tgt i).length := by omega
        _ = coff S off tgt (i + 1) := (coff_succ S off tgt hik).symm
        _ ≤ cns S off tgt := coff_le_cns S off tgt _
    have hcns_ns : cns S off tgt ≤ ns := cns_le_ns S off tgt hc
    -- the store
    have hst : Run B (.store nmC.tgt (.var "rs.c") (.sub (.var "rs.x") (.lit 1)))
        σb (σb.setArr nmC.tgt (σ.vars "rs.c") (x - 1)) 5 := by
      have hcev : (Expr.var "rs.c").evalB B σb = some (σ.vars "rs.c") := by
        rw [← hbc]
        exact evalB_var (by rw [hbc]; have := hcns_ns; omega)
      have hxev : (Expr.sub (.var "rs.x") (.lit 1)).evalB B σb = some (x - 1) := by
        have hxv : (Expr.var "rs.x").evalB B σb = some x := by
          rw [← hbx]
          exact evalB_var (by rw [hbx]; omega)
        have h1v : (Expr.lit 1).evalB B σb = some 1 := evalB_lit (by omega)
        have h := evalB_bin (B := B) (op := .sub) hxv h1v (by simp; omega)
        simpa using h
      refine (Run.store hcev hxev ?_).mono (by simp)
      rw [hbarrs, hgarr, length_arrOf]
      exact hclt
    set σc := σb.setArr nmC.tgt (σ.vars "rs.c") (x - 1) with hσc
    have hbump : Run B (.assign "rs.c" (.add (.var "rs.c") (.lit 1))) σc
        (σc.setVar "rs.c" (σ.vars "rs.c" + 1)) 4 := by
      have hcc : σc.vars "rs.c" = σ.vars "rs.c" := by rw [hσc]; simpa using hbc
      have hev := evalB_incr (B := B) (x := "rs.c") (σ := σc)
        (by rw [hcc]; omega)
      rw [hcc] at hev
      exact (Run.assign hev).mono (by simp)
    set σd := σc.setVar "rs.c" (σ.vars "rs.c" + 1) with hσd
    have hite : Run B (.ite (.lt (.lit 0) (.var "rs.x"))
        (.seq (.store nmC.tgt (.var "rs.c") (.sub (.var "rs.x") (.lit 1)))
          (.assign "rs.c" (.add (.var "rs.c") (.lit 1)))) .skip) σb σd 13 :=
      (Run.ite_true hcondT (hst.seq hbump)).mono (by simp)
    have hinc : Run B (.assign "rs.j" (.add (.var "rs.j") (.lit 1))) σd
        (σd.setVar "rs.j" (jv + 1)) 4 := by
      have hdj : σd.vars "rs.j" = jv := by rw [hσd, hσc]; simpa using hbj
      have hev := evalB_incr (B := B) (x := "rs.j") (σ := σd)
        (by rw [hdj]; omega)
      rw [hdj] at hev
      exact (Run.assign hev).mono (by simp)
    set σ' := σd.setVar "rs.j" (jv + 1) with hσ'
    have hrun : Run B (csrSlot nmP nmC ra) σ σ' 23 :=
      (hread.seq (hxread.seq (hite.seq hinc))).mono (by omega)
    -- the surviving state
    have h'vars : ∀ y, y ≠ "rs.w" → y ≠ "rs.x" → y ≠ "rs.c" → y ≠ "rs.j" →
        σ'.vars y = σ.vars y := by
      intro y hy1 hy2 hy3 hy4
      rw [hσ', hσd, hσc, hσb, hσa]
      simp [hy1, hy2, hy3, hy4]
    have h'arrs : ∀ b, b ≠ nmC.tgt → σ'.arrs b = σ.arrs b := by
      intro b hb
      rw [hσ', hσd, hσc, hσb, hσa]
      simp [hb]
    have h'j : σ'.vars "rs.j" = jv + 1 := by rw [hσ']; simp
    have h'c : σ'.vars "rs.c" = σ.vars "rs.c" + 1 := by rw [hσ', hσd]; simp
    have h'tgt : σ'.arrs nmC.tgt = (arrOf (cns S off tgt) g).set (σ.vars "rs.c") (x - 1) := by
      rw [hσ', hσd, hσc]
      simp only [arrs_setVar]
      rw [arrs_setArr, if_pos rfl, hbarrs, hgarr]
    refine ⟨σ', 23, hrun,
      ⟨hc.of_eq (h'arrs _ (Ne.symm h1)) (h'arrs _ (Ne.symm h2)),
        ⟨by rw [h'arrs _ (Ne.symm h3)]; exact hcl.1,
          fun t ht => by rw [h'arrs _ (Ne.symm h3)]; exact hcl.2 t ht⟩,
        by rw [h'vars _ (by decide) (by decide) (by decide) (by decide)]; exact hk,
        by rw [h'arrs _ (Ne.symm h4)]; exact hra,
        by rw [h'vars _ (by decide) (by decide) (by decide) (by decide)]; exact hiv,
        by rw [h'vars _ (by decide) (by decide) (by decide) (by decide)]; exact hs,
        by rw [h'vars _ (by decide) (by decide) (by decide) (by decide)]; exact he,
        by rw [h'j, ← hs'_def]; omega,
        by rw [h'j, ← hs'_def]; omega,
        ?_, ?_, ?_⟩,
      by rw [h'j], le_rfl⟩
    · -- the cursor tracks the kept prefix
      rw [h'j, h'c, hcv, ← hs'_def, ← hrow_def,
        show jv + 1 - off s' = m + 1 by omega, hkept1]
      omega
    · obtain ⟨f, hfarr, hfpre⟩ := hoff
      exact ⟨f, by rw [h'arrs _ (Ne.symm h5)]; exact hfarr, hfpre⟩
    · -- the emitted prefix grows by the new local name
      refine ⟨fun p => if p = σ.vars "rs.c" then x - 1 else g p, ?_, ?_⟩
      · rw [h'tgt, set_arrOf]
      · intro p hp
        rw [h'c] at hp
        show (if p = σ.vars "rs.c" then x - 1 else g p) = ctgt S off tgt p
        by_cases hpc : p = σ.vars "rs.c"
        · subst hpc
          rw [if_pos rfl, hcv, ctgt_slice S off tgt hik (by omega)]
          exact (filterMap_getD_kept hmrow hsome).symm
        · rw [if_neg hpc]
          exact hgpre p (by omega)
  · -- not a member: the slot is skipped
    have hcondF : (Cond.lt (.lit 0) (.var "rs.x")).evalB B σb = some false := by
      rw [hcond]
      congr 1
      simpa using hx0
    have hnone : rkOpt S (row.getD m 0) = none := by
      rw [hrow_m]
      exact (rkOpt_eq_none_iff_rk S w).mpr (by omega)
    have hite : Run B (.ite (.lt (.lit 0) (.var "rs.x"))
        (.seq (.store nmC.tgt (.var "rs.c") (.sub (.var "rs.x") (.lit 1)))
          (.assign "rs.c" (.add (.var "rs.c") (.lit 1)))) .skip) σb σb 13 :=
      (Run.ite_false hcondF Run.skip).mono (by simp)
    have hinc : Run B (.assign "rs.j" (.add (.var "rs.j") (.lit 1))) σb
        (σb.setVar "rs.j" (jv + 1)) 4 := by
      have hev := evalB_incr (B := B) (x := "rs.j") (σ := σb)
        (by rw [hbj]; omega)
      rw [hbj] at hev
      exact (Run.assign hev).mono (by simp)
    set σ' := σb.setVar "rs.j" (jv + 1) with hσ'
    have hrun : Run B (csrSlot nmP nmC ra) σ σ' 23 :=
      (hread.seq (hxread.seq (hite.seq hinc))).mono (by omega)
    have h'vars : ∀ y, y ≠ "rs.w" → y ≠ "rs.x" → y ≠ "rs.j" →
        σ'.vars y = σ.vars y := by
      intro y hy1 hy2 hy3
      rw [hσ', hσb, hσa]
      simp [hy1, hy2, hy3]
    have h'arrs : ∀ b, σ'.arrs b = σ.arrs b := by
      intro b
      rw [hσ', hσb, hσa]
      simp
    have h'j : σ'.vars "rs.j" = jv + 1 := by rw [hσ']; simp
    have h'c : σ'.vars "rs.c" = σ.vars "rs.c" :=
      h'vars _ (by decide) (by decide) (by decide)
    refine ⟨σ', 23, hrun,
      ⟨hc.of_eq (h'arrs _) (h'arrs _),
        ⟨by rw [h'arrs]; exact hcl.1, fun t ht => by rw [h'arrs]; exact hcl.2 t ht⟩,
        by rw [h'vars _ (by decide) (by decide) (by decide)]; exact hk,
        by rw [h'arrs]; exact hra,
        by rw [h'vars _ (by decide) (by decide) (by decide)]; exact hiv,
        by rw [h'vars _ (by decide) (by decide) (by decide)]; exact hs,
        by rw [h'vars _ (by decide) (by decide) (by decide)]; exact he,
        by rw [h'j, ← hs'_def]; omega,
        by rw [h'j, ← hs'_def]; omega,
        ?_, ?_, ?_⟩,
      by rw [h'j], le_rfl⟩
    · rw [h'j, h'c, hcv, ← hs'_def, ← hrow_def,
        show jv + 1 - off s' = m + 1 by omega,
        keptLen_succ_none hmrow hnone]
    · obtain ⟨f, hfarr, hfpre⟩ := hoff
      exact ⟨f, by rw [h'arrs]; exact hfarr, hfpre⟩
    · exact ⟨g, by rw [h'arrs]; exact hgarr, fun p hp => hgpre p (by rwa [h'c] at hp)⟩

/-- **One member of the fill**: load the row bounds, scan the row at
the parent degree, seal the child row boundary. Costs
`27·deg_A(member) + 24`. -/
private theorem csrFillBody_run (hNB : n < B) (hnsB : ns < B)
    (h3 : nmC.tgt ≠ la) (h4 : nmC.tgt ≠ ra) (h5 : nmC.tgt ≠ nmC.off)
    (h1 : nmC.tgt ≠ nmP.off) (h2 : nmC.tgt ≠ nmP.tgt)
    (h6 : nmC.off ≠ nmP.off) (h7 : nmC.off ≠ nmP.tgt) (h8 : nmC.off ≠ la)
    (h9 : nmC.off ≠ ra) :
    ∀ σ, FillSt nmP nmC la ra n ns S off tgt σ → σ.vars "rs.i" < S.ncard →
      ∃ σ', Run B (csrFillBody nmP nmC la ra) σ σ'
          (27 * Csr.rowLen off (embN S (σ.vars "rs.i")) + 24) ∧
        FillSt nmP nmC la ra n ns S off tgt σ' ∧
        σ'.vars "rs.i" = σ.vars "rs.i" + 1 := by
  intro σ hF hlt
  obtain ⟨hc, hcl, hk, hra, hiN, hcv, hoff, htgt⟩ := hF
  have hkn : S.ncard ≤ n := ncard_le_carrier S
  set i := σ.vars "rs.i" with hi_def
  set s' := embN S i with hs'_def
  have hs'n : s' < n := embN_lt S hlt
  -- the member read
  have hread : Run B (.assign "rs.s" (.get la (.var "rs.i"))) σ
      (σ.setVar "rs.s" s') 3 := by
    refine (Run.assign (evalB_get (evalB_var (by omega)) ?_ (by omega))).mono (by simp)
    exact clusterList_read hcl hlt
  set σ₁ := σ.setVar "rs.s" s' with hσ₁
  -- the row bounds
  have h1c : Csr nmP.off nmP.tgt n ns n off tgt σ₁ := by
    refine hc.of_eq ?_ ?_ <;> (rw [hσ₁]; simp)
  have h1s : σ₁.vars "rs.s" = s' := by rw [hσ₁]; simp
  obtain ⟨σ₂, hload, hpost⟩ :=
    (Csr.loadRow_spec B n ns n nmP.off nmP.tgt "rs.s" "rs.j" "rs.e" off tgt
      (by decide) (by decide)).run
      (σ := σ₁) ⟨⟨h1c, by omega, hnsB⟩, by rw [h1s]; omega, by rw [h1s]; omega⟩
  obtain ⟨-, -, -, hσ₂⟩ := hpost
  rw [h1s] at hσ₂
  -- the row state at the row's start
  have hR₂ : RowSt nmP nmC la ra n ns S off tgt i σ₂ := by
    have h2vars : ∀ y, y ≠ "rs.j" → y ≠ "rs.e" → y ≠ "rs.s" → σ₂.vars y = σ.vars y := by
      intro y hy1 hy2 hy3
      rw [hσ₂, hσ₁]
      simp [hy1, hy2, hy3]
    have h2arrs : ∀ b, σ₂.arrs b = σ.arrs b := by
      intro b
      rw [hσ₂, hσ₁]
      simp
    have h2j : σ₂.vars "rs.j" = off s' := by rw [hσ₂]; simp
    have h2e : σ₂.vars "rs.e" = off (s' + 1) := by rw [hσ₂]; simp
    have h2s : σ₂.vars "rs.s" = s' := by rw [hσ₂, hσ₁]; simp
    refine ⟨hc.of_eq (h2arrs _) (h2arrs _),
      ⟨by rw [h2arrs]; exact hcl.1, fun t ht => by rw [h2arrs]; exact hcl.2 t ht⟩,
      by rw [h2vars "rs.k" (by decide) (by decide) (by decide)]; exact hk,
      by rw [h2arrs]; exact hra,
      by have := h2vars "rs.i" (by decide) (by decide) (by decide); omega,
      h2s, h2e,
      by rw [h2j, hs'_def],
      by rw [h2j, hs'_def]; exact hc.off_le_succ (by rw [← hs'_def]; exact hs'n),
      ?_, ?_, ?_⟩
    · rw [h2vars "rs.c" (by decide) (by decide) (by decide), h2j, hs'_def,
        Nat.sub_self, keptLen_zero, Nat.add_zero, hcv]
    · obtain ⟨f, hfarr, hfpre⟩ := hoff
      exact ⟨f, by rw [h2arrs]; exact hfarr, hfpre⟩
    · obtain ⟨g, hgarr, hgpre⟩ := htgt
      refine ⟨g, by rw [h2arrs]; exact hgarr, ?_⟩
      intro p hp
      refine hgpre p ?_
      rwa [h2vars "rs.c" (by decide) (by decide) (by decide)] at hp
  -- the row scan
  have hscan := Csr.rowScan_spec B (27 * Csr.rowLen off s' + 4) (off (s' + 1)) 23
    "rs.j" "rs.e" (csrSlot nmP nmC ra)
    (P := fun τ => τ = σ₂)
    (I := RowSt nmP nmC la ra n ns S off tgt i)
    (hc.off_lt hnsB (by omega))
    (fun τ hτ => ⟨hτ.he, hτ.hjhi⟩)
    (fun τ hτ hjlt => csrSlot_step hNB hnsB h3 h4 h5 h1 h2 hlt τ hτ hjlt)
    (fun τ hτ => by rw [hτ]; exact hR₂)
    (fun τ hτ => by
      have hj₂ : σ₂.vars "rs.j" = off s' := by rw [hσ₂]; simp
      rw [hτ, hj₂, Csr.rowLen])
  obtain ⟨σ₃, hrscan, hR₃, hj₃⟩ := hscan.run rfl
  obtain ⟨hc₃, hcl₃, hk₃, hra₃, hiv₃, hs₃, he₃, hjlo₃, hjhi₃, hcv₃, hoff₃, htgt₃⟩ := hR₃
  -- the cursor has sealed the whole row
  have hcfin : σ₃.vars "rs.c" = coff S off tgt (i + 1) := by
    have hlenrow : (Csr.row off tgt s').length = Csr.rowLen off s' :=
      Csr.length_row off tgt s'
    have hkfull : keptLen (rkOpt S) (Csr.row off tgt s') (σ₃.vars "rs.j" - off s')
        = (crowL S off tgt i).length := by
      rw [hj₃, show off (s' + 1) - off s' = Csr.rowLen off s' from rfl, ← hlenrow,
        keptLen_full]
      rfl
    rw [hcv₃, hkfull, coff_succ S off tgt hlt]
  obtain ⟨f, hfarr, hfpre⟩ := hoff₃
  have hcns_ns : cns S off tgt ≤ ns := cns_le_ns S off tgt hc
  have hcoffB : coff S off tgt (i + 1) ≤ ns :=
    le_trans (coff_le_cns S off tgt _) hcns_ns
  -- seal the row boundary
  have hst : Run B (.store nmC.off (.add (.var "rs.i") (.lit 1)) (.var "rs.c"))
      σ₃ (σ₃.setArr nmC.off (i + 1) (coff S off tgt (i + 1))) 5 := by
    have hiev : (Expr.add (.var "rs.i") (.lit 1)).evalB B σ₃ = some (i + 1) := by
      have h := evalB_incr (B := B) (x := "rs.i") (σ := σ₃) (by rw [hiv₃]; omega)
      rwa [hiv₃] at h
    have hcev : (Expr.var "rs.c").evalB B σ₃ = some (coff S off tgt (i + 1)) := by
      rw [← hcfin]
      exact evalB_var (by rw [hcfin]; omega)
    refine (Run.store hiev hcev ?_).mono (by simp)
    rw [hfarr, length_arrOf]
    omega
  set σ₄ := σ₃.setArr nmC.off (i + 1) (coff S off tgt (i + 1)) with hσ₄
  have hinc : Run B (.assign "rs.i" (.add (.var "rs.i") (.lit 1))) σ₄
      (σ₄.setVar "rs.i" (i + 1)) 4 := by
    have h4i : σ₄.vars "rs.i" = i := by rw [hσ₄]; simpa using hiv₃
    have hev := evalB_incr (B := B) (x := "rs.i") (σ := σ₄) (by rw [h4i]; omega)
    rw [h4i] at hev
    exact (Run.assign hev).mono (by simp)
  set σ₅ := σ₄.setVar "rs.i" (i + 1) with hσ₅
  have hrun : Run B (csrFillBody nmP nmC la ra) σ σ₅
      (27 * Csr.rowLen off s' + 24) := by
    have h := hread.seq (hload.seq (hrscan.seq (hst.seq hinc)))
    exact h.mono (by omega)
  have h5arrs : ∀ b, b ≠ nmC.off → σ₅.arrs b = σ₃.arrs b := by
    intro b hb
    rw [hσ₅, hσ₄]
    simp [hb]
  have h5vars : ∀ y, y ≠ "rs.i" → σ₅.vars y = σ₃.vars y := by
    intro y hy
    rw [hσ₅, hσ₄]
    simp [hy]
  have h5i : σ₅.vars "rs.i" = i + 1 := by rw [hσ₅]; simp
  refine ⟨σ₅, hrun,
    ⟨hc₃.of_eq (h5arrs _ (Ne.symm h6)) (h5arrs _ (Ne.symm h7)),
      ⟨by rw [h5arrs _ (Ne.symm h8)]; exact hcl₃.1,
        fun t ht => by rw [h5arrs _ (Ne.symm h8)]; exact hcl₃.2 t ht⟩,
      by rw [h5vars "rs.k" (by decide)]; exact hk₃,
      by rw [h5arrs _ (Ne.symm h9)]; exact hra₃,
      by rw [h5i]; omega,
      by rw [h5i, h5vars "rs.c" (by decide), hcfin],
      ?_, ?_⟩, h5i⟩
  · -- the sealed boundaries
    refine ⟨fun a => if a = i + 1 then coff S off tgt (i + 1) else f a, ?_, ?_⟩
    · rw [hσ₅, arrs_setVar, hσ₄, arrs_setArr, if_pos rfl, hfarr, set_arrOf]
    · intro a ha
      rw [h5i] at ha
      show (if a = i + 1 then coff S off tgt (i + 1) else f a) = coff S off tgt a
      by_cases hae : a = i + 1
      · rw [if_pos hae, hae]
      · rw [if_neg hae]
        exact hfpre a (by omega)
  · -- the emitted prefix survives the boundary store
    obtain ⟨g, hgarr, hgpre⟩ := htgt₃
    refine ⟨g, by rw [h5arrs _ h5]; exact hgarr, ?_⟩
    intro p hp
    refine hgpre p ?_
    rwa [h5vars "rs.c" (by decide)] at hp

/-- **The CSR fill, discharged**: from the parent CSR, the enumeration
region and the marked scratch, the two child regions end at exactly the
child CSR (`coff`/`ctgt`), the cursor at the child slot count. The
budget's row-scan half is the sum of the **parent** row lengths of the
members. -/
private theorem csrFill_spec (hNB : n < B) (hnsB : ns < B)
    (h3 : nmC.tgt ≠ la) (h4 : nmC.tgt ≠ ra) (h5 : nmC.tgt ≠ nmC.off)
    (h1 : nmC.tgt ≠ nmP.off) (h2 : nmC.tgt ≠ nmP.tgt)
    (h6 : nmC.off ≠ nmP.off) (h7 : nmC.off ≠ nmP.tgt) (h8 : nmC.off ≠ la)
    (h9 : nmC.off ≠ ra) :
    Spec B
      (fun σ => Csr nmP.off nmP.tgt n ns n off tgt σ ∧ ClusterList la S σ ∧
        σ.vars "rs.k" = S.ncard ∧ σ.arrs ra = arrOf n (rk S) ∧
        (σ.arrs nmC.off).length = S.ncard + 1 ∧
        (σ.arrs nmC.tgt).length = cns S off tgt)
      (csrFill nmP nmC la ra)
      (fun _ σ' => Csr nmP.off nmP.tgt n ns n off tgt σ' ∧ ClusterList la S σ' ∧
        σ'.vars "rs.k" = S.ncard ∧ σ'.arrs ra = arrOf n (rk S) ∧
        σ'.arrs nmC.off = arrOf (S.ncard + 1) (coff S off tgt) ∧
        σ'.arrs nmC.tgt = arrOf (cns S off tgt) (ctgt S off tgt) ∧
        σ'.vars "rs.c" = cns S off tgt)
      (27 * (∑ t ∈ Finset.range S.ncard, Csr.rowLen off (embN S t))
        + 52 * S.ncard + 11) := by
  intro σ hσ
  obtain ⟨hc, hcl, hk, hra, hlo, hlt⟩ := hσ
  have hkn : S.ncard ≤ n := ncard_le_carrier S
  -- the three initializations
  have h1r : Run B (.assign "rs.c" (.lit 0)) σ (σ.setVar "rs.c" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  set σ₁ := σ.setVar "rs.c" 0 with hσ₁
  have h2r : Run B (.store nmC.off (.lit 0) (.lit 0)) σ₁ (σ₁.setArr nmC.off 0 0) 3 := by
    refine (Run.store (evalB_lit (by omega)) (evalB_lit (by omega)) ?_).mono (by simp)
    rw [hσ₁]
    simp only [arrs_setVar]
    omega
  set σ₂ := σ₁.setArr nmC.off 0 0 with hσ₂
  have h3r : Run B (.assign "rs.i" (.lit 0)) σ₂ (σ₂.setVar "rs.i" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  set σ₃ := σ₂.setVar "rs.i" 0 with hσ₃
  have h3arrs : ∀ b, b ≠ nmC.off → σ₃.arrs b = σ.arrs b := by
    intro b hb
    rw [hσ₃, hσ₂, hσ₁]
    simp [hb]
  have h3off : σ₃.arrs nmC.off = (σ.arrs nmC.off).set 0 0 := by
    rw [hσ₃, hσ₂, hσ₁]
    simp
  have h3vars : ∀ y, y ≠ "rs.c" → y ≠ "rs.i" → σ₃.vars y = σ.vars y := by
    intro y hy1 hy2
    rw [hσ₃, hσ₂, hσ₁]
    simp [hy1, hy2]
  -- the fill state at entry
  have hF₃ : FillSt nmP nmC la ra n ns S off tgt σ₃ := by
    refine ⟨hc.of_eq (h3arrs _ (Ne.symm h6)) (h3arrs _ (Ne.symm h7)),
      ⟨by rw [h3arrs _ (Ne.symm h8)]; exact hcl.1,
        fun t ht => by rw [h3arrs _ (Ne.symm h8)]; exact hcl.2 t ht⟩,
      by rw [h3vars _ (by decide) (by decide)]; exact hk,
      by rw [h3arrs _ (Ne.symm h9)]; exact hra,
      by rw [hσ₃]; simp,
      by rw [hσ₃]; simp [hσ₂, hσ₁],
      ?_, ?_⟩
    · refine ⟨fun a => if a = 0 then 0 else (σ.arrs nmC.off).getD a 0, ?_, ?_⟩
      · rw [h3off]
        conv_lhs => rw [show σ.arrs nmC.off
            = arrOf (S.ncard + 1) (fun p => (σ.arrs nmC.off).getD p 0) by
          rw [← hlo]; exact (arrOf_getD _).symm]
        rw [set_arrOf]
      · intro a ha
        have hia : σ₃.vars "rs.i" = 0 := by rw [hσ₃]; simp
        rw [hia] at ha
        have ha0 : a = 0 := by omega
        subst ha0
        show (if 0 = 0 then 0 else (σ.arrs nmC.off).getD 0 0) = coff S off tgt 0
        rw [if_pos rfl, coff_zero]
    · refine ⟨fun p => (σ.arrs nmC.tgt).getD p 0, ?_, ?_⟩
      · rw [h3arrs _ h5, ← hlt]
        exact (arrOf_getD _).symm
      · intro p hp
        have hc0 : σ₃.vars "rs.c" = 0 := by rw [hσ₃, hσ₂, hσ₁]; simp
        rw [hc0] at hp
        omega
  -- the loop, amortized at the parent degrees
  have hloop := Run.while_potential (B := B)
    (b := .lt (.var "rs.i") (.var "rs.k")) (c := csrFillBody nmP nmC la ra)
    (FillSt nmP nmC la ra n ns S off tgt)
    (fun τ => ∑ t ∈ Finset.Ico (τ.vars "rs.i") S.ncard,
      (27 * Csr.rowLen off (embN S t) + 52))
    (fun τ hτ => evalB_condLt_vars (by have := hτ.hiN; omega) (by rw [hτ.hk]; omega))
    (fun τ hτ hcond => by
      have hlt' : τ.vars "rs.i" < S.ncard := by
        have := lt_of_condLt_true hcond
        rwa [hτ.hk] at this
      obtain ⟨τ', hrun, hF', hi'⟩ :=
        csrFillBody_run hNB hnsB h3 h4 h5 h1 h2 h6 h7 h8 h9 τ hτ hlt'
      refine ⟨τ', _, hrun, hF', ?_⟩
      have hsplit : ∑ t ∈ Finset.Ico (τ.vars "rs.i") S.ncard,
          (27 * Csr.rowLen off (embN S t) + 52)
          = (27 * Csr.rowLen off (embN S (τ.vars "rs.i")) + 52)
            + ∑ t ∈ Finset.Ico (τ.vars "rs.i" + 1) S.ncard,
              (27 * Csr.rowLen off (embN S t) + 52) :=
        Finset.sum_eq_sum_Ico_succ_bot hlt' _
      show 1 + (Cond.lt (.var "rs.i") (.var "rs.k")).size
          + (27 * Csr.rowLen off (embN S (τ.vars "rs.i")) + 24)
          + (∑ t ∈ Finset.Ico (τ'.vars "rs.i") S.ncard,
              (27 * Csr.rowLen off (embN S t) + 52))
          ≤ ∑ t ∈ Finset.Ico (τ.vars "rs.i") S.ncard,
              (27 * Csr.rowLen off (embN S t) + 52)
      rw [hi', hsplit]
      simp only [size_condLt, size_var]
      omega)
    hF₃
  obtain ⟨σf, Kf, hwrun, hFf, hcondf, hKf⟩ := hloop
  -- the exit state
  have hif : σf.vars "rs.i" = S.ncard := by
    have h1 := le_of_condLt_false hcondf
    have h2 := hFf.hk
    have h3' := hFf.hiN
    omega
  obtain ⟨f, hfarr, hfpre⟩ := hFf.hoff
  obtain ⟨g, hgarr, hgpre⟩ := hFf.htgt
  have hofffin : σf.arrs nmC.off = arrOf (S.ncard + 1) (coff S off tgt) := by
    rw [hfarr]
    exact arrOf_congr fun a ha => hfpre a (by rw [hif]; omega)
  have hcvfin : σf.vars "rs.c" = cns S off tgt := by
    rw [hFf.hcv, hif, coff_last]
  have htgtfin : σf.arrs nmC.tgt = arrOf (cns S off tgt) (ctgt S off tgt) := by
    rw [hgarr]
    exact arrOf_congr fun p hp => hgpre p (by rw [hcvfin]; omega)
  refine ⟨σf, ?_, hFf.hc, hFf.hcl, hFf.hk, hFf.hra, hofffin, htgtfin, hcvfin⟩
  have hrun := h1r.seq (h2r.seq (h3r.seq hwrun))
  refine hrun.mono ?_
  have hi₃ : σ₃.vars "rs.i" = 0 := by rw [hσ₃]; simp
  have hΦ₃ : (∑ t ∈ Finset.Ico (σ₃.vars "rs.i") S.ncard,
      (27 * Csr.rowLen off (embN S t) + 52))
      = 27 * (∑ t ∈ Finset.range S.ncard, Csr.rowLen off (embN S t))
        + 52 * S.ncard := by
    rw [hi₃, ← Finset.range_eq_Ico, Finset.sum_add_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_comm S.ncard 52]
  simp only [size_condLt, size_var] at hKf
  rw [hΦ₃] at hKf
  omega

end CsrFill

/-! ## §9 The color copy -/

/-- Unique decomposition of a strided index — what keeps one block's
writes out of every other block. -/
private theorem grid_inj {L a b c q : ℕ} (hc : c < L) (hq : q < L)
    (h : a * L + c = b * L + q) : a = b ∧ c = q := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exfalso
    have h1 := Nat.mul_le_mul_right L (show a + 1 ≤ b by omega)
    have h2 : (a + 1) * L = a * L + L := by ring
    omega
  · subst hab
    omega
  · exfalso
    have h1 := Nat.mul_le_mul_right L (show b + 1 ≤ a by omega)
    have h2 : (b + 1) * L = b * L + L := by ring
    omega

section ColCopy

variable {B n n₀ Lc : ℕ} {S : Set (Fin n)} {nmP nmC : ArenaNames} {la : String}

open Classical in
/-- The parent color bit at plain numbers. -/
private noncomputable def pbit (colP : Coloring n Lc) (w c' : ℕ) : ℕ :=
  if h : w < n ∧ c' < Lc then
    (if (⟨w, h.1⟩ : Fin n) ∈ colP ⟨c', h.2⟩ then 1 else 0) else 0

private theorem colBits_getD {colP : Coloring n Lc} {a : String} {σ : Env}
    (h : ColBits a colP σ) {w c' : ℕ} (hw : w < n) (hc : c' < Lc) :
    (σ.arrs a).getD (w * Lc + c') 0 = pbit colP w c' := by
  have := h.2 ⟨w, hw⟩ ⟨c', hc⟩
  rw [pbit, dif_pos ⟨hw, hc⟩]
  simpa using this

private theorem pbit_lt_two (colP : Coloring n Lc) (w c' : ℕ) :
    pbit colP w c' ≤ 1 := by
  rw [pbit]
  split
  · split <;> omega
  · omega

/-- The outer state of the color copy. -/
private structure ColSt (nmP nmC : ArenaNames) (la : String) (n Lc : ℕ)
    (S : Set (Fin n)) (colP : Coloring n Lc) (σ : Env) : Prop where
  hcolP : ColBits nmP.col colP σ
  hcl : ClusterList la S σ
  hk : σ.vars "rs.k" = S.ncard
  hl : σ.vars "rs.l" = Lc
  hiN : σ.vars "rs.i" ≤ S.ncard
  harr : ∃ f, σ.arrs nmC.col = arrOf (S.ncard * Lc) f ∧
    ∀ a < σ.vars "rs.i", ∀ c' < Lc, f (a * Lc + c') = pbit colP (embN S a) c'

/-- The inner state: member `i`'s block, filled below the round
counter. -/
private structure ColInSt (nmP nmC : ArenaNames) (la : String) (n Lc : ℕ)
    (S : Set (Fin n)) (colP : Coloring n Lc) (i : ℕ) (σ : Env) : Prop where
  hcolP : ColBits nmP.col colP σ
  hcl : ClusterList la S σ
  hk : σ.vars "rs.k" = S.ncard
  hl : σ.vars "rs.l" = Lc
  hiv : σ.vars "rs.i" = i
  hs : σ.vars "rs.s" = embN S i
  hq : σ.vars "rs.q" ≤ Lc
  harr : ∃ f, σ.arrs nmC.col = arrOf (S.ncard * Lc) f ∧
    (∀ a < i, ∀ c' < Lc, f (a * Lc + c') = pbit colP (embN S a) c') ∧
    ∀ c' < σ.vars "rs.q", f (i * Lc + c') = pbit colP (embN S i) c'

variable {colP : Coloring n Lc}

/-- One cell of a member's color row. -/
private theorem colCell_spec (hNB : n < B) (hLB : n * Lc < B)
    (hcc : nmC.col ≠ nmP.col) (hcla : nmC.col ≠ la)
    {i : ℕ} (hik : i < S.ncard) :
    Spec B
      (fun σ => ColInSt nmP nmC la n Lc S colP i σ ∧ σ.vars "rs.q" < Lc)
      (.seq (.store nmC.col
          (.add (.mul (.var "rs.i") (.var "rs.l")) (.var "rs.q"))
          (.get nmP.col (.add (.mul (.var "rs.s") (.var "rs.l")) (.var "rs.q"))))
        (.assign "rs.q" (.add (.var "rs.q") (.lit 1))))
      (fun σ σ' => ColInSt nmP nmC la n Lc S colP i σ' ∧
        σ'.vars "rs.q" = σ.vars "rs.q" + 1) 16 := by
  intro σ hσ
  obtain ⟨⟨hcolP, hcl, hk, hl, hiv, hs, hqLc, f, hfarr, hfdone, hfcur⟩, hlt⟩ := hσ
  have hkn : S.ncard ≤ n := ncard_le_carrier S
  have hn1 : 1 ≤ n := by have := embN_lt S hik; omega
  have hLcB : Lc < B := by
    calc Lc = 1 * Lc := (Nat.one_mul Lc).symm
      _ ≤ n * Lc := Nat.mul_le_mul_right Lc hn1
      _ < B := hLB
  set q := σ.vars "rs.q" with hq_def
  set s' := embN S i with hs'_def
  have hs'n : s' < n := embN_lt S hik
  -- the destination index
  have hdstv : i * Lc + q < S.ncard * Lc := by
    have h1 : i * Lc + q < (i + 1) * Lc := by
      have : (i + 1) * Lc = i * Lc + Lc := by ring
      omega
    have h2 : (i + 1) * Lc ≤ S.ncard * Lc := Nat.mul_le_mul_right Lc (by omega)
    omega
  have hdstB : i * Lc + q < B := by
    have : S.ncard * Lc ≤ n * Lc := Nat.mul_le_mul_right Lc hkn
    omega
  have hdst : (Expr.add (.mul (.var "rs.i") (.var "rs.l")) (.var "rs.q")).evalB B σ
      = some (i * Lc + q) := by
    have hmul : (Expr.mul (.var "rs.i") (.var "rs.l")).evalB B σ = some (i * Lc) := by
      have h := evalB_bin (B := B) (op := .mul)
        (evalB_var (x := "rs.i") (by rw [hiv]; omega))
        (evalB_var (x := "rs.l") (by rw [hl]; omega))
        (by
          rw [hiv, hl]
          have h1 : i * Lc ≤ n * Lc := Nat.mul_le_mul_right Lc (by omega)
          simp
          omega)
      rw [hiv, hl] at h
      simpa using h
    have h := evalB_bin (B := B) (op := .add) hmul
      (evalB_var (x := "rs.q") (by omega)) (by rw [← hq_def]; simp; omega)
    rw [← hq_def] at h
    simpa using h
  -- the source read
  have hsrcv : s' * Lc + q < n * Lc := by
    have h1 : s' * Lc + q < (s' + 1) * Lc := by
      have : (s' + 1) * Lc = s' * Lc + Lc := by ring
      omega
    have h2 : (s' + 1) * Lc ≤ n * Lc := Nat.mul_le_mul_right Lc (by omega)
    omega
  have hsrc : (Expr.get nmP.col
      (.add (.mul (.var "rs.s") (.var "rs.l")) (.var "rs.q"))).evalB B σ
      = some (pbit colP s' q) := by
    have hmul : (Expr.mul (.var "rs.s") (.var "rs.l")).evalB B σ = some (s' * Lc) := by
      have h := evalB_bin (B := B) (op := .mul)
        (evalB_var (x := "rs.s") (by rw [hs]; omega))
        (evalB_var (x := "rs.l") (by rw [hl]; omega))
        (by
          rw [hs, hl]
          have h1 : s' * Lc ≤ n * Lc := Nat.mul_le_mul_right Lc (by omega)
          simp
          omega)
      rw [hs, hl] at h
      simpa using h
    have hidx : (Expr.add (.mul (.var "rs.s") (.var "rs.l")) (.var "rs.q")).evalB B σ
        = some (s' * Lc + q) := by
      have h := evalB_bin (B := B) (op := .add) hmul
        (evalB_var (x := "rs.q") (by omega)) (by rw [← hq_def]; simp; omega)
      rw [← hq_def] at h
      simpa using h
    refine evalB_get hidx ?_ (by have := pbit_lt_two colP s' q; omega)
    rw [getElem?_eq_getD (by rw [hcolP.1]; omega), colBits_getD hcolP hs'n hlt]
  have hst : Run B (.store nmC.col
      (.add (.mul (.var "rs.i") (.var "rs.l")) (.var "rs.q"))
      (.get nmP.col (.add (.mul (.var "rs.s") (.var "rs.l")) (.var "rs.q"))))
      σ (σ.setArr nmC.col (i * Lc + q) (pbit colP s' q)) 12 := by
    refine (Run.store hdst hsrc ?_).mono (by simp)
    rw [hfarr, length_arrOf]
    exact hdstv
  set σ₁ := σ.setArr nmC.col (i * Lc + q) (pbit colP s' q) with hσ₁
  have hinc : Run B (.assign "rs.q" (.add (.var "rs.q") (.lit 1))) σ₁
      (σ₁.setVar "rs.q" (q + 1)) 4 := by
    have h1q : σ₁.vars "rs.q" = q := by rw [hσ₁]; simp [hq_def]
    have hev := evalB_incr (B := B) (x := "rs.q") (σ := σ₁) (by rw [h1q]; omega)
    rw [h1q] at hev
    exact (Run.assign hev).mono (by simp)
  set σ' := σ₁.setVar "rs.q" (q + 1) with hσ'
  have h'vars : ∀ y, y ≠ "rs.q" → σ'.vars y = σ.vars y := by
    intro y hy
    rw [hσ', hσ₁]
    simp [hy]
  have h'arrs : ∀ b, b ≠ nmC.col → σ'.arrs b = σ.arrs b := by
    intro b hb
    rw [hσ', hσ₁]
    simp [hb]
  have h'q : σ'.vars "rs.q" = q + 1 := by rw [hσ']; simp
  refine ⟨σ', (hst.seq hinc).mono (by omega),
    ⟨⟨by rw [h'arrs _ (Ne.symm hcc)]; exact hcolP.1,
        fun v c => by rw [h'arrs _ (Ne.symm hcc)]; exact hcolP.2 v c⟩,
      ⟨by rw [h'arrs _ (Ne.symm hcla)]; exact hcl.1,
        fun t ht => by rw [h'arrs _ (Ne.symm hcla)]; exact hcl.2 t ht⟩,
      by rw [h'vars "rs.k" (by decide)]; exact hk,
      by rw [h'vars "rs.l" (by decide)]; exact hl,
      by rw [h'vars "rs.i" (by decide)]; exact hiv,
      by rw [h'vars "rs.s" (by decide)]; exact hs,
      by rw [h'q]; omega, ?_⟩, by rw [h'q]⟩
  refine ⟨fun p => if p = i * Lc + q then pbit colP s' q else f p, ?_, ?_, ?_⟩
  · rw [hσ', arrs_setVar, hσ₁, arrs_setArr, if_pos rfl, hfarr, set_arrOf]
  · intro a ha c' hc'
    show (if a * Lc + c' = i * Lc + q then pbit colP s' q else f (a * Lc + c'))
      = pbit colP (embN S a) c'
    rw [if_neg fun hcon => by have := (grid_inj hc' hlt hcon).1; omega]
    exact hfdone a ha c' hc'
  · intro c' hc'
    rw [h'q] at hc'
    show (if i * Lc + c' = i * Lc + q then pbit colP s' q else f (i * Lc + c'))
      = pbit colP (embN S i) c'
    by_cases hcq : c' = q
    · subst hcq
      rw [if_pos rfl, hs'_def]
    · rw [if_neg fun hcon => hcq (grid_inj (by omega) hlt hcon).2]
      exact hfcur c' (by omega)

/-- One member of the color copy. -/
private theorem colCopyBody_spec (hNB : n < B) (hLB : n * Lc < B)
    (hcc : nmC.col ≠ nmP.col) (hcla : nmC.col ≠ la) :
    Spec B
      (fun σ => ColSt nmP nmC la n Lc S colP σ ∧ σ.vars "rs.i" < S.ncard)
      (colCopyBody nmP nmC la)
      (fun σ σ' => ColSt nmP nmC la n Lc S colP σ' ∧
        σ'.vars "rs.i" = σ.vars "rs.i" + 1) (20 * Lc + 13) := by
  intro σ hσ
  obtain ⟨⟨hcolP, hcl, hk, hl, hiN, f, hfarr, hfdone⟩, hlt⟩ := hσ
  have hkn : S.ncard ≤ n := ncard_le_carrier S
  set i := σ.vars "rs.i" with hi_def
  -- the member read
  have hread : Run B (.assign "rs.s" (.get la (.var "rs.i"))) σ
      (σ.setVar "rs.s" (embN S i)) 3 := by
    refine (Run.assign (evalB_get (evalB_var (by omega)) ?_
      (by have := embN_lt S hlt; omega))).mono (by simp)
    exact clusterList_read hcl hlt
  set σ₁ := σ.setVar "rs.s" (embN S i) with hσ₁
  -- the inner loop over the palette
  have hin₁ : ColInSt nmP nmC la n Lc S colP i (σ₁.setVar "rs.q" 0) := by
    refine ⟨⟨by rw [hσ₁]; simpa using hcolP.1,
        fun v c => by rw [hσ₁]; simpa using hcolP.2 v c⟩,
      ⟨by rw [hσ₁]; simpa using hcl.1,
        fun t ht => by rw [hσ₁]; simpa using hcl.2 t ht⟩,
      by rw [hσ₁]; simpa using hk,
      by rw [hσ₁]; simpa using hl,
      by rw [hσ₁]; simpa using hi_def.symm,
      by rw [hσ₁]; simp,
      by simp, f, by rw [hσ₁]; simpa using hfarr, hfdone, ?_⟩
    intro c' hc'
    simp at hc'
  have hinner := Spec.forRangeZero (B := B) "rs.q" "rs.l"
    (ColInSt nmP nmC la n Lc S colP i) Lc 16
    (by
      have hn1 : 1 ≤ n := by have := embN_lt S hlt; omega
      have h1 : 1 * Lc ≤ n * Lc := Nat.mul_le_mul_right Lc hn1
      omega)
    (fun τ hτ => hτ.hq) (fun τ hτ => hτ.hl)
    (colCell_spec hNB hLB hcc hcla hlt)
  obtain ⟨σ₂, hinrun, hin₂, hq₂⟩ := hinner.run hin₁
  obtain ⟨hcolP₂, hcl₂, hk₂, hl₂, hiv₂, hs₂, hq₂', f₂, hfarr₂, hfdone₂, hfcur₂⟩ := hin₂
  -- the counter
  have hinc : Run B (.assign "rs.i" (.add (.var "rs.i") (.lit 1))) σ₂
      (σ₂.setVar "rs.i" (i + 1)) 4 := by
    have hev := evalB_incr (B := B) (x := "rs.i") (σ := σ₂) (by rw [hiv₂]; omega)
    rw [hiv₂] at hev
    exact (Run.assign hev).mono (by simp)
  refine ⟨σ₂.setVar "rs.i" (i + 1), ?_, ⟨⟨by simpa using hcolP₂.1,
      fun v c => by simpa using hcolP₂.2 v c⟩,
    ⟨by simpa using hcl₂.1, fun t ht => by simpa using hcl₂.2 t ht⟩,
    by simpa using hk₂,
    by simpa using hl₂,
    by simp; omega, ?_⟩, by simp [← hi_def]⟩
  · have h := hread.seq (hinrun.seq hinc)
    exact h.mono (by omega)
  · refine ⟨f₂, by simpa using hfarr₂, ?_⟩
    intro a ha c' hc'
    simp at ha
    rcases Nat.lt_or_ge a i with hai | hai
    · exact hfdone₂ a hai c' hc'
    · have hae : a = i := by omega
      subst hae
      exact hfcur₂ c' (by omega)

/-- **The color copy, discharged**: the child color region ends at the
copied rows — `(A.restrict S).col`, cell by cell. Cost `|S|·O(Λ)`. -/
private theorem colCopy_spec (hNB : n < B) (hLB : n * Lc < B)
    (hcc : nmC.col ≠ nmP.col) (hcla : nmC.col ≠ la) :
    Spec B
      (fun σ => ColBits nmP.col colP σ ∧ ClusterList la S σ ∧
        σ.vars "rs.k" = S.ncard ∧ σ.vars "rs.l" = Lc ∧
        (σ.arrs nmC.col).length = S.ncard * Lc)
      (colCopy nmP nmC la)
      (fun _ σ' => ColBits nmP.col colP σ' ∧ ClusterList la S σ' ∧
        σ'.vars "rs.k" = S.ncard ∧ σ'.vars "rs.l" = Lc ∧
        ColBits nmC.col
          (fun c => {a | Impl.restrictEmb S a ∈ colP c} :
            Coloring S.ncard Lc) σ')
      ((20 * Lc + 17) * S.ncard + 6) := by
  have hmain := Spec.forRangeZero (B := B) "rs.i" "rs.k"
    (ColSt nmP nmC la n Lc S colP) S.ncard (20 * Lc + 13)
    (by have := ncard_le_carrier S; omega)
    (fun τ hτ => hτ.hiN) (fun τ hτ => hτ.hk)
    (colCopyBody_spec hNB hLB hcc hcla)
  refine ((hmain.pre ?_).post ?_).mono le_rfl
  · rintro σ ⟨hcolP, hcl, hk, hl, hlen⟩
    refine ⟨⟨by simpa using hcolP.1, fun v c => by simpa using hcolP.2 v c⟩,
      ⟨by simpa using hcl.1, fun t ht => by simpa using hcl.2 t ht⟩,
      by simpa using hk, by simpa using hl, by simp,
      fun p => (σ.arrs nmC.col).getD p 0, ?_, ?_⟩
    · simp only [arrs_setVar]
      rw [← hlen]
      exact (arrOf_getD _).symm
    · intro a ha
      simp at ha
  · rintro σ σ' - ⟨⟨hcolP, hcl, hk, hl, -, f, hfarr, hfdone⟩, hie⟩
    refine ⟨hcolP, hcl, hk, hl, by rw [hfarr, length_arrOf], ?_⟩
    intro v c
    rw [hfarr, getD_arrOf]
    · rw [hfdone (v : ℕ) (by rw [hie]; exact v.2) (c : ℕ) c.2, pbit,
        dif_pos ⟨embN_lt S v.2, c.2⟩]
      have hv : (⟨embN S (v : ℕ), embN_lt S v.2⟩ : Fin n)
          = Impl.restrictEmb S v := Fin.ext (embN_of_lt S v.2)
      have hcfin : (⟨(c : ℕ), c.2⟩ : Fin Lc) = c := Fin.ext rfl
      rw [hv, hcfin]
      rfl
    · have h1 : (v : ℕ) * Lc + (c : ℕ) < ((v : ℕ) + 1) * Lc := by
        have : ((v : ℕ) + 1) * Lc = (v : ℕ) * Lc + Lc := by ring
        have := c.2
        omega
      have h2 : ((v : ℕ) + 1) * Lc ≤ S.ncard * Lc :=
        Nat.mul_le_mul_right Lc v.2
      omega

end ColCopy

/-! ## §10 The renaming, composed -/

section UpCopy

variable {B n n₀ : ℕ} {S : Set (Fin n)} {nmP nmC : ArenaNames} {la : String}

/-- The child's root name at plain numbers. -/
private noncomputable def upN (upP : Fin n ↪ Fin n₀) (S : Set (Fin n)) (a : ℕ) : ℕ :=
  if h : a < S.ncard then (upP (Impl.restrictEmb S ⟨a, h⟩) : ℕ) else 0

private structure UpSt (nmP nmC : ArenaNames) (la : String) (n : ℕ) {n₀ : ℕ}
    (S : Set (Fin n)) (upP : Fin n ↪ Fin n₀) (σ : Env) : Prop where
  hupP : UpArr nmP.up upP σ
  hcl : ClusterList la S σ
  hk : σ.vars "rs.k" = S.ncard
  hiN : σ.vars "rs.i" ≤ S.ncard
  harr : ∃ f, σ.arrs nmC.up = arrOf S.ncard f ∧
    ∀ a < σ.vars "rs.i", f a = upN upP S a

variable {upP : Fin n ↪ Fin n₀}

/-- **The renaming, discharged**: the child's `up` region ends at the
composite `(restrictEmb S).trans upP` — E6's never-re-typed record. -/
private theorem upCopy_spec (hNB : n < B) (hn0B : n₀ < B)
    (huu : nmC.up ≠ nmP.up) (hula : nmC.up ≠ la) :
    Spec B
      (fun σ => UpArr nmP.up upP σ ∧ ClusterList la S σ ∧
        σ.vars "rs.k" = S.ncard ∧ (σ.arrs nmC.up).length = S.ncard)
      (upCopy nmP nmC la)
      (fun _ σ' => UpArr nmP.up upP σ' ∧ ClusterList la S σ' ∧
        σ'.vars "rs.k" = S.ncard ∧
        UpArr nmC.up ((Impl.restrictEmb S).trans upP) σ')
      (16 * S.ncard + 6) := by
  have hkn : S.ncard ≤ n := ncard_le_carrier S
  have hbody : Spec B
      (fun σ => UpSt nmP nmC la n S upP σ ∧ σ.vars "rs.i" < S.ncard)
      (.seq (.assign "rs.s" (.get la (.var "rs.i")))
        (.seq (.store nmC.up (.var "rs.i") (.get nmP.up (.var "rs.s")))
          (.assign "rs.i" (.add (.var "rs.i") (.lit 1)))))
      (fun σ σ' => UpSt nmP nmC la n S upP σ' ∧
        σ'.vars "rs.i" = σ.vars "rs.i" + 1) 12 := by
    intro σ hσ
    obtain ⟨⟨hupP, hcl, hk, hiN, f, hfarr, hfpre⟩, hlt⟩ := hσ
    set i := σ.vars "rs.i" with hi_def
    have hsN : embN S i < n := embN_lt S hlt
    have hread : Run B (.assign "rs.s" (.get la (.var "rs.i"))) σ
        (σ.setVar "rs.s" (embN S i)) 3 := by
      refine (Run.assign (evalB_get (evalB_var (by omega)) ?_ (by omega))).mono
        (by simp)
      exact clusterList_read hcl hlt
    set σ₁ := σ.setVar "rs.s" (embN S i) with hσ₁
    have hst : Run B (.store nmC.up (.var "rs.i") (.get nmP.up (.var "rs.s")))
        σ₁ (σ₁.setArr nmC.up i (upN upP S i)) 5 := by
      have h1i : σ₁.vars "rs.i" = i := by rw [hσ₁]; simp [hi_def]
      have h1s : σ₁.vars "rs.s" = embN S i := by rw [hσ₁]; simp
      have hiev : (Expr.var "rs.i").evalB B σ₁ = some i := by
        rw [← h1i]
        exact evalB_var (by rw [h1i]; omega)
      have hsev : (Expr.get nmP.up (.var "rs.s")).evalB B σ₁
          = some (upN upP S i) := by
        refine evalB_get (k := embN S i) ?_ ?_ ?_
        · rw [← h1s]
          exact evalB_var (by rw [h1s]; omega)
        · rw [hσ₁]
          simp only [arrs_setVar]
          rw [getElem?_eq_getD (by rw [hupP.1]; omega)]
          congr 1
          calc (σ.arrs nmP.up).getD (embN S i) 0
              = (upP (⟨embN S i, hsN⟩ : Fin n) : ℕ) := hupP.2 ⟨embN S i, hsN⟩
            _ = upN upP S i := by
                rw [upN, dif_pos hlt]
                have harg : (⟨embN S i, hsN⟩ : Fin n) = Impl.restrictEmb S ⟨i, hlt⟩ :=
                  Fin.ext (embN_of_lt S hlt)
                rw [harg]
        · rw [upN, dif_pos hlt]
          have := (upP (Impl.restrictEmb S ⟨i, hlt⟩)).2
          omega
      refine (Run.store hiev hsev ?_).mono (by simp)
      rw [hσ₁]
      simp only [arrs_setVar]
      rw [hfarr, length_arrOf]
      omega
    set σ₂ := σ₁.setArr nmC.up i (upN upP S i) with hσ₂
    have hinc : Run B (.assign "rs.i" (.add (.var "rs.i") (.lit 1))) σ₂
        (σ₂.setVar "rs.i" (i + 1)) 4 := by
      have h2i : σ₂.vars "rs.i" = i := by rw [hσ₂, hσ₁]; simp [hi_def]
      have hev := evalB_incr (B := B) (x := "rs.i") (σ := σ₂) (by rw [h2i]; omega)
      rw [h2i] at hev
      exact (Run.assign hev).mono (by simp)
    set σ₃ := σ₂.setVar "rs.i" (i + 1) with hσ₃
    have h3vars : ∀ y, y ≠ "rs.s" → y ≠ "rs.i" → σ₃.vars y = σ.vars y := by
      intro y hy1 hy2
      rw [hσ₃, hσ₂, hσ₁]
      simp [hy1, hy2]
    have h3arrs : ∀ b, b ≠ nmC.up → σ₃.arrs b = σ.arrs b := by
      intro b hb
      rw [hσ₃, hσ₂, hσ₁]
      simp [hb]
    have h3i : σ₃.vars "rs.i" = i + 1 := by rw [hσ₃]; simp
    have h3up : σ₃.arrs nmC.up = (σ.arrs nmC.up).set i (upN upP S i) := by
      rw [hσ₃, hσ₂, hσ₁]
      simp
    refine ⟨σ₃, (hread.seq (hst.seq hinc)).mono (by omega),
      ⟨⟨by rw [h3arrs _ (Ne.symm huu)]; exact hupP.1,
        fun v => by rw [h3arrs _ (Ne.symm huu)]; exact hupP.2 v⟩,
      ⟨by rw [h3arrs _ (Ne.symm hula)]; exact hcl.1,
        fun t ht => by rw [h3arrs _ (Ne.symm hula)]; exact hcl.2 t ht⟩,
      by rw [h3vars "rs.k" (by decide) (by decide)]; exact hk,
      by rw [h3i]; omega, ?_⟩, h3i⟩
    refine ⟨fun p => if p = i then upN upP S i else f p, ?_, ?_⟩
    · rw [h3up, hfarr, set_arrOf]
    · intro a ha
      rw [h3i] at ha
      show (if a = i then upN upP S i else f a) = upN upP S a
      by_cases hae : a = i
      · rw [if_pos hae, hae]
      · rw [if_neg hae]
        exact hfpre a (by omega)
  have hmain := Spec.forRangeZero (B := B) "rs.i" "rs.k"
    (UpSt nmP nmC la n S upP) S.ncard 12 (by omega)
    (fun τ hτ => hτ.hiN) (fun τ hτ => hτ.hk) hbody
  refine ((hmain.pre ?_).post ?_).mono le_rfl
  · rintro σ ⟨hupP, hcl, hk, hlen⟩
    refine ⟨⟨by simpa using hupP.1, fun v => by simpa using hupP.2 v⟩,
      ⟨by simpa using hcl.1, fun t ht => by simpa using hcl.2 t ht⟩,
      by simpa using hk, by simp,
      fun p => (σ.arrs nmC.up).getD p 0, ?_, ?_⟩
    · simp only [arrs_setVar]
      rw [← hlen]
      exact (arrOf_getD _).symm
    · intro a ha
      simp at ha
  · rintro σ σ' - ⟨⟨hupP, hcl, hk, -, f, hfarr, hfpre⟩, hie⟩
    refine ⟨hupP, hcl, hk, by rw [hfarr, length_arrOf], ?_⟩
    intro v
    rw [hfarr, getD_arrOf _ v.2, hfpre (v : ℕ) (by rw [hie]; exact v.2), upN,
      dif_pos v.2]
    congr 2

end UpCopy

/-! ## §11 The channel filter

Per member and per ancestor round, the stored list is filtered through
the scratch **in order** — `Impl.restrict_hist_map`'s in-order
intersection, on the machine. -/

section HistFilter

variable {B n ℓp hb : ℕ} {S : Set (Fin n)} {nmP nmC : ArenaNames} {la ra : String}

/-- The parent's stored list at plain numbers (total; `[]` out of
range). -/
private noncomputable def histN (histP : Fin n → Fin ℓp → List (Fin n))
    (v r : ℕ) : List ℕ :=
  if h : v < n ∧ r < ℓp then (histP ⟨v, h.1⟩ ⟨r, h.2⟩).map Fin.val else []

/-- The child's stored list at plain numbers: the parent's, filtered
through the scratch. -/
private noncomputable def chN (histP : Fin n → Fin ℓp → List (Fin n))
    (S : Set (Fin n)) (a r : ℕ) : List ℕ :=
  (histN histP (embN S a) r).filterMap (rkOpt S)

variable {histP : Fin n → Fin ℓp → List (Fin n)}

/-- The machine filter at numbers IS the abstract `filterMap toLocal`,
renamed down — `restrict_hist_map`'s machine half. -/
private theorem filterMap_rkOpt_map_val (l : List (Fin n)) :
    (l.map Fin.val).filterMap (rkOpt S)
      = (l.filterMap (Impl.toLocal S)).map Fin.val := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx : rkOpt S (x : ℕ) = (Impl.toLocal S x).map Fin.val := by
      rw [rkOpt]
      exact dif_pos x.2
    rw [List.map_cons, List.filterMap_cons, List.filterMap_cons, hx]
    cases hto : Impl.toLocal S x with
    | none => simpa using ih
    | some b => simp [ih]

private theorem chN_eq {a r : ℕ} (ha : a < S.ncard) (hr : r < ℓp) :
    chN histP S a r
      = ((histP (Impl.restrictEmb S ⟨a, ha⟩) ⟨r, hr⟩).filterMap
          (Impl.toLocal S)).map Fin.val := by
  have h1 : (⟨embN S a, embN_lt S ha⟩ : Fin n) = Impl.restrictEmb S ⟨a, ha⟩ :=
    Fin.ext (embN_of_lt S ha)
  rw [chN, histN, dif_pos ⟨embN_lt S ha, hr⟩, h1, filterMap_rkOpt_map_val]

private theorem histN_len_le {a' : String} {σ : Env}
    (hh : HistArr a' ℓp hb histP σ) (v r : ℕ) :
    (histN histP v r).length ≤ hb := by
  rw [histN]
  split
  · rename_i h
    rw [List.length_map]
    exact (hh.2 ⟨v, h.1⟩ ⟨r, h.2⟩).1
  · simp

private theorem histN_entry_lt {v r m : ℕ}
    (hm : m < (histN histP v r).length) : (histN histP v r).getD m 0 < n := by
  have hall : ∀ x ∈ histN histP v r, x < n := by
    intro x hx
    rw [histN] at hx
    split at hx
    · obtain ⟨y, -, rfl⟩ := List.mem_map.mp hx
      exact y.2
    · simp at hx
  have hmem : (histN histP v r).getD m 0 ∈ histN histP v r := by
    rw [getD_eq_getElem hm]
    exact List.getElem_mem hm
  exact hall _ hmem

/-- Reading the parent's length prefix. -/
private theorem histArr_base {σ : Env} (hh : HistArr nmP.hist ℓp hb histP σ)
    {v r : ℕ} (hv : v < n) (hr : r < ℓp) :
    (σ.arrs nmP.hist).getD ((v * ℓp + r) * (hb + 1)) 0
      = (histN histP v r).length := by
  have h := (hh.2 ⟨v, hv⟩ ⟨r, hr⟩).2.1
  rw [histN, dif_pos ⟨hv, hr⟩, List.length_map]
  exact h

/-- Reading one stored name. -/
private theorem histArr_entry {σ : Env} (hh : HistArr nmP.hist ℓp hb histP σ)
    {v r m : ℕ} (hv : v < n) (hr : r < ℓp)
    (hm : m < (histN histP v r).length) :
    (σ.arrs nmP.hist).getD ((v * ℓp + r) * (hb + 1) + 1 + m) 0
      = (histN histP v r).getD m 0 := by
  have hm' : m < (histP ⟨v, hv⟩ ⟨r, hr⟩).length := by
    rw [histN, dif_pos ⟨hv, hr⟩, List.length_map] at hm
    exact hm
  have h := (hh.2 ⟨v, hv⟩ ⟨r, hr⟩).2.2 m hm'
  rw [histN, dif_pos ⟨hv, hr⟩,
    getD_eq_getElem (show m < ((histP ⟨v, hv⟩ ⟨r, hr⟩).map Fin.val).length by
      rw [List.length_map]; exact hm'),
    List.getElem_map]
  exact h

/-- The block index arithmetic: any in-block cell stays inside the
region. -/
private theorem hist_idx_lt {v r c : ℕ} (hv : v < n) (hr : r < ℓp)
    (hc : c < hb + 1) :
    (v * ℓp + r) * (hb + 1) + c < n * ℓp * (hb + 1) := by
  have h2 : (v + 1) * ℓp ≤ n * ℓp := Nat.mul_le_mul_right ℓp (by omega)
  have h3 : (v + 1) * ℓp = v * ℓp + ℓp := by ring
  have h4 : (v * ℓp + r + 1) * (hb + 1) ≤ n * ℓp * (hb + 1) :=
    Nat.mul_le_mul_right (hb + 1) (by omega)
  have h5 : (v * ℓp + r + 1) * (hb + 1) = (v * ℓp + r) * (hb + 1) + (hb + 1) := by
    ring
  omega

/-- Two in-block cells coincide only in the same block at the same
offset. -/
private theorem hist_idx_inj {a r c a' r' c' : ℕ} (hr : r < ℓp)
    (hc : c < hb + 1) (hr' : r' < ℓp) (hc' : c' < hb + 1)
    (h : (a * ℓp + r) * (hb + 1) + c = (a' * ℓp + r') * (hb + 1) + c') :
    a = a' ∧ r = r' ∧ c = c' := by
  obtain ⟨h1, h2⟩ := grid_inj hc hc' h
  obtain ⟨h3, h4⟩ := grid_inj hr hr' h1
  exact ⟨h3, h4, h2⟩

private theorem keptLen_le_self (F : ℕ → Option ℕ) (l : List ℕ) (m : ℕ) :
    keptLen F l m ≤ m :=
  le_trans (List.length_filterMap_le _ _) (by rw [List.length_take]; omega)

/-- One filled channel block. -/
private def blockDone (ℓp hb : ℕ) (L : List ℕ) (a r : ℕ) (f : ℕ → ℕ) : Prop :=
  f ((a * ℓp + r) * (hb + 1)) = L.length ∧
    ∀ m < L.length, f ((a * ℓp + r) * (hb + 1) + 1 + m) = L.getD m 0

/-- The outer state of the channel filter. -/
private structure HistSt (nmP nmC : ArenaNames) (la ra : String) (n ℓp hb : ℕ)
    (S : Set (Fin n)) (histP : Fin n → Fin ℓp → List (Fin n)) (σ : Env) : Prop where
  hh : HistArr nmP.hist ℓp hb histP σ
  hcl : ClusterList la S σ
  hk : σ.vars "rs.k" = S.ncard
  hp : σ.vars "rs.p" = ℓp
  hhb : σ.vars "rs.h" = hb
  hra : σ.arrs ra = arrOf n (rk S)
  hiN : σ.vars "rs.i" ≤ S.ncard
  harr : ∃ f, σ.arrs nmC.hist = arrOf (S.ncard * ℓp * (hb + 1)) f ∧
    ∀ a < σ.vars "rs.i", ∀ r < ℓp, blockDone ℓp hb (chN histP S a r) a r f

/-- The middle state: member `i`'s rounds, done below the round
counter. -/
private structure HistMidSt (nmP nmC : ArenaNames) (la ra : String) (n ℓp hb : ℕ)
    (S : Set (Fin n)) (histP : Fin n → Fin ℓp → List (Fin n)) (i : ℕ)
    (σ : Env) : Prop where
  hh : HistArr nmP.hist ℓp hb histP σ
  hcl : ClusterList la S σ
  hk : σ.vars "rs.k" = S.ncard
  hp : σ.vars "rs.p" = ℓp
  hhb : σ.vars "rs.h" = hb
  hra : σ.arrs ra = arrOf n (rk S)
  hiv : σ.vars "rs.i" = i
  hs : σ.vars "rs.s" = embN S i
  hq : σ.vars "rs.q" ≤ ℓp
  harr : ∃ f, σ.arrs nmC.hist = arrOf (S.ncard * ℓp * (hb + 1)) f ∧
    (∀ a < i, ∀ r < ℓp, blockDone ℓp hb (chN histP S a r) a r f) ∧
    ∀ r < σ.vars "rs.q", blockDone ℓp hb (chN histP S i r) i r f

/-- The inner state: one list, filtered up to the read cursor. -/
private structure HistInSt (nmP nmC : ArenaNames) (ra : String) (n ℓp hb : ℕ)
    (S : Set (Fin n)) (histP : Fin n → Fin ℓp → List (Fin n)) (i q : ℕ)
    (σ : Env) : Prop where
  hh : HistArr nmP.hist ℓp hb histP σ
  hra : σ.arrs ra = arrOf n (rk S)
  hav : σ.vars "rs.a" = (embN S i * ℓp + q) * (hb + 1)
  hbv : σ.vars "rs.b" = (i * ℓp + q) * (hb + 1)
  hev : σ.vars "rs.e" = (histN histP (embN S i) q).length
  hdN : σ.vars "rs.d" ≤ (histN histP (embN S i) q).length
  htv : σ.vars "rs.t"
    = keptLen (rkOpt S) (histN histP (embN S i) q) (σ.vars "rs.d")
  harr : ∃ f, σ.arrs nmC.hist = arrOf (S.ncard * ℓp * (hb + 1)) f ∧
    (∀ a < i, ∀ r < ℓp, blockDone ℓp hb (chN histP S a r) a r f) ∧
    (∀ r < q, blockDone ℓp hb (chN histP S i r) i r f) ∧
    ∀ m < σ.vars "rs.t",
      f ((i * ℓp + q) * (hb + 1) + 1 + m) = (chN histP S i q).getD m 0

/-- **One stored name of the filter**: read it, one scratch lookup, emit
its local name if marked. -/
private theorem histSlot_spec (hNB : n < B) (hHB : n * ℓp * (hb + 1) < B)
    (hhc : nmC.hist ≠ nmP.hist) (hhra : nmC.hist ≠ ra)
    {i q : ℕ} (hik : i < S.ncard) (hqp : q < ℓp) :
    Spec B
      (fun σ => HistInSt nmP nmC ra n ℓp hb S histP i q σ ∧
        σ.vars "rs.d" < (histN histP (embN S i) q).length)
      (histSlot nmP nmC ra)
      (fun σ σ' => HistInSt nmP nmC ra n ℓp hb S histP i q σ' ∧
        σ'.vars "rs.d" = σ.vars "rs.d" + 1) 32 := by
  intro σ hσ
  obtain ⟨⟨hh, hra, hav, hbv, hev, hdN, htv, f, hfarr, hdoneA, hdoneR, hcur⟩, hlt⟩ := hσ
  have hkn : S.ncard ≤ n := ncard_le_carrier S
  have hn1 : 1 ≤ n := by have := embN_lt S hik; omega
  have hp1 : 1 ≤ ℓp := by omega
  have hnpB : n * ℓp * (hb + 1) < B := hHB
  have hhbB : hb + 1 < B := by
    have h1 : 1 * 1 * (hb + 1) ≤ n * ℓp * (hb + 1) :=
      Nat.mul_le_mul_right (hb + 1) (by
        calc 1 * 1 = 1 := by ring
          _ ≤ n * ℓp := Nat.one_le_iff_ne_zero.mpr (by positivity))
    have h2 : 1 * 1 * (hb + 1) = hb + 1 := by ring
    omega
  set L := histN histP (embN S i) q with hL_def
  have hLhb : L.length ≤ hb := histN_len_le hh _ _
  set d := σ.vars "rs.d" with hd_def
  set A := (embN S i * ℓp + q) * (hb + 1) with hA_def
  set Bb := (i * ℓp + q) * (hb + 1) with hBb_def
  set t := σ.vars "rs.t" with ht_def
  have hsn : embN S i < n := embN_lt S hik
  have htle : t ≤ d := by
    rw [htv]
    exact keptLen_le_self _ _ _
  -- the stored-name read
  have hidxsrc : A + 1 + d < n * ℓp * (hb + 1) := by
    have h := hist_idx_lt (hb := hb) hsn hqp (show 1 + d < hb + 1 by omega)
    rw [← hA_def] at h
    omega
  have hwval : (σ.arrs nmP.hist).getD (A + 1 + d) 0 = L.getD d 0 :=
    histArr_entry hh hsn hqp hlt
  have hwlt : L.getD d 0 < n := histN_entry_lt hlt
  have hread : Run B (.assign "rs.w"
      (.get nmP.hist (.add (.var "rs.a") (.add (.var "rs.d") (.lit 1)))))
      σ (σ.setVar "rs.w" (L.getD d 0)) 8 := by
    have hidx : (Expr.add (.var "rs.a") (.add (.var "rs.d") (.lit 1))).evalB B σ
        = some (A + (d + 1)) := by
      have h1 : (Expr.add (.var "rs.d") (.lit 1)).evalB B σ = some (d + 1) := by
        have h := evalB_incr (B := B) (x := "rs.d") (σ := σ)
          (by rw [← hd_def]; omega)
        rwa [← hd_def] at h
      have h2 := evalB_bin (B := B) (op := .add)
        (evalB_var (x := "rs.a") (by rw [hav]; omega)) h1
        (by rw [hav]; simp; omega)
      rw [hav] at h2
      simpa using h2
    refine (Run.assign (evalB_get hidx ?_ (by omega))).mono (by simp)
    rw [show A + (d + 1) = A + 1 + d by omega,
      getElem?_eq_getD (by rw [hh.1]; omega), hwval]
  set σa := σ.setVar "rs.w" (L.getD d 0) with hσa
  set x := rk S (L.getD d 0) with hx_def
  have hxk : x ≤ S.ncard := rk_le S _
  -- the rank read
  have hxread : Run B (.assign "rs.x" (.get ra (.var "rs.w"))) σa
      (σa.setVar "rs.x" x) 3 := by
    have haw : σa.vars "rs.w" = L.getD d 0 := by rw [hσa]; simp
    have hwev : (Expr.var "rs.w").evalB B σa = some (L.getD d 0) := by
      rw [← haw]
      exact evalB_var (by rw [haw]; omega)
    refine (Run.assign (evalB_get hwev ?_ (by omega))).mono (by simp)
    rw [hσa]
    simp only [arrs_setVar]
    rw [hra, getElem?_arrOf _ hwlt]
  set σb := σa.setVar "rs.x" x with hσb
  have hbx : σb.vars "rs.x" = x := by rw [hσb]; simp
  have hbt : σb.vars "rs.t" = t := by rw [hσb, hσa]; simp [ht_def]
  have hbd : σb.vars "rs.d" = d := by rw [hσb, hσa]; simp [hd_def]
  have hbb : σb.vars "rs.b" = Bb := by rw [hσb, hσa]; simp [hbv]
  have hbarrs : ∀ b, σb.arrs b = σ.arrs b := by intro b; rw [hσb, hσa]; simp
  have hcond : (Cond.lt (.lit 0) (.var "rs.x")).evalB B σb
      = some (decide (0 < x)) := by
    refine evalB_condLt (evalB_lit (by omega)) ?_
    rw [← hbx]
    exact evalB_var (by rw [hbx]; omega)
  by_cases hx0 : 0 < x
  · -- kept: emit and advance the kept count
    have hcondT : (Cond.lt (.lit 0) (.var "rs.x")).evalB B σb = some true := by
      rw [hcond]
      congr 1
      simpa using hx0
    have hsome : rkOpt S (L.getD d 0) = some (x - 1) := rk_pos_elim S rfl hx0
    have hkept1 : keptLen (rkOpt S) L (d + 1) = keptLen (rkOpt S) L d + 1 :=
      keptLen_succ_some hlt hsome
    have hkle : keptLen (rkOpt S) L d + 1 ≤ (L.filterMap (rkOpt S)).length := by
      have h := keptLen_le (rkOpt S) L (d + 1)
      rw [hkept1] at h
      exact h
    have hthb : t < hb := by
      have h1 : (L.filterMap (rkOpt S)).length ≤ L.length :=
        List.length_filterMap_le _ _
      rw [htv]
      omega
    have hidxdst : Bb + 1 + t < S.ncard * ℓp * (hb + 1) := by
      have h1 : i * ℓp + q < S.ncard * ℓp := by
        have h2 : (i + 1) * ℓp ≤ S.ncard * ℓp := Nat.mul_le_mul_right ℓp (by omega)
        have h3 : (i + 1) * ℓp = i * ℓp + ℓp := by ring
        omega
      have h4 : (i * ℓp + q + 1) * (hb + 1) ≤ S.ncard * ℓp * (hb + 1) :=
        Nat.mul_le_mul_right (hb + 1) (by omega)
      have h5 : (i * ℓp + q + 1) * (hb + 1) = Bb + (hb + 1) := by
        rw [hBb_def]; ring
      omega
    have hdstB : Bb + 1 + t < B := by
      have : S.ncard * ℓp * (hb + 1) ≤ n * ℓp * (hb + 1) :=
        Nat.mul_le_mul_right (hb + 1) (Nat.mul_le_mul_right ℓp hkn)
      omega
    have hst : Run B (.store nmC.hist
        (.add (.var "rs.b") (.add (.var "rs.t") (.lit 1)))
        (.sub (.var "rs.x") (.lit 1)))
        σb (σb.setArr nmC.hist (Bb + 1 + t) (x - 1)) 9 := by
      have hidx : (Expr.add (.var "rs.b") (.add (.var "rs.t") (.lit 1))).evalB B σb
          = some (Bb + (t + 1)) := by
        have h1 : (Expr.add (.var "rs.t") (.lit 1)).evalB B σb = some (t + 1) := by
          have h := evalB_incr (B := B) (x := "rs.t") (σ := σb)
            (by rw [hbt]; omega)
          rwa [hbt] at h
        have h2 := evalB_bin (B := B) (op := .add)
          (evalB_var (x := "rs.b") (by rw [hbb]; omega)) h1
          (by rw [hbb]; simp; omega)
        rw [hbb] at h2
        simpa using h2
      have hxv : (Expr.var "rs.x").evalB B σb = some x := by
        rw [← hbx]
        exact evalB_var (by rw [hbx]; omega)
      have h1v : (Expr.lit 1).evalB B σb = some 1 := evalB_lit (by omega)
      have hval : (Expr.sub (.var "rs.x") (.lit 1)).evalB B σb = some (x - 1) := by
        have h := evalB_bin (B := B) (op := .sub) hxv h1v (by simp; omega)
        simpa using h
      have h := Run.store (a := nmC.hist) hidx hval
        (by rw [hbarrs, hfarr, length_arrOf]; omega)
      rw [show Bb + (t + 1) = Bb + 1 + t by omega] at h
      exact h.mono (by simp)
    set σc := σb.setArr nmC.hist (Bb + 1 + t) (x - 1) with hσc
    have hbump : Run B (.assign "rs.t" (.add (.var "rs.t") (.lit 1))) σc
        (σc.setVar "rs.t" (t + 1)) 4 := by
      have hct : σc.vars "rs.t" = t := by rw [hσc]; simpa using hbt
      have hev := evalB_incr (B := B) (x := "rs.t") (σ := σc) (by rw [hct]; omega)
      rw [hct] at hev
      exact (Run.assign hev).mono (by simp)
    set σd := σc.setVar "rs.t" (t + 1) with hσd
    have hite : Run B (.ite (.lt (.lit 0) (.var "rs.x"))
        (.seq (.store nmC.hist (.add (.var "rs.b") (.add (.var "rs.t") (.lit 1)))
            (.sub (.var "rs.x") (.lit 1)))
          (.assign "rs.t" (.add (.var "rs.t") (.lit 1)))) .skip) σb σd 17 :=
      (Run.ite_true hcondT (hst.seq hbump)).mono (by simp)
    have hinc : Run B (.assign "rs.d" (.add (.var "rs.d") (.lit 1))) σd
        (σd.setVar "rs.d" (d + 1)) 4 := by
      have hdd : σd.vars "rs.d" = d := by rw [hσd, hσc]; simpa using hbd
      have hev := evalB_incr (B := B) (x := "rs.d") (σ := σd) (by rw [hdd]; omega)
      rw [hdd] at hev
      exact (Run.assign hev).mono (by simp)
    set σ' := σd.setVar "rs.d" (d + 1) with hσ'
    have hrun : Run B (histSlot nmP nmC ra) σ σ' 32 :=
      (hread.seq (hxread.seq (hite.seq hinc))).mono (by omega)
    have h'vars : ∀ y, y ≠ "rs.w" → y ≠ "rs.x" → y ≠ "rs.t" → y ≠ "rs.d" →
        σ'.vars y = σ.vars y := by
      intro y hy1 hy2 hy3 hy4
      rw [hσ', hσd, hσc, hσb, hσa]
      simp [hy1, hy2, hy3, hy4]
    have h'arrs : ∀ b, b ≠ nmC.hist → σ'.arrs b = σ.arrs b := by
      intro b hb'
      rw [hσ', hσd, hσc, hσb, hσa]
      simp [hb']
    have h'd : σ'.vars "rs.d" = d + 1 := by rw [hσ']; simp
    have h't : σ'.vars "rs.t" = t + 1 := by rw [hσ', hσd]; simp
    have h'hist : σ'.arrs nmC.hist = (arrOf (S.ncard * ℓp * (hb + 1)) f).set
        (Bb + 1 + t) (x - 1) := by
      rw [hσ', hσd, hσc]
      simp only [arrs_setVar]
      rw [arrs_setArr, if_pos rfl, hbarrs, hfarr]
    refine ⟨σ', hrun,
      ⟨⟨by rw [h'arrs _ (Ne.symm hhc)]; exact hh.1,
          fun v p => by rw [h'arrs _ (Ne.symm hhc)]; exact hh.2 v p⟩,
        by rw [h'arrs _ (Ne.symm hhra)]; exact hra,
        by rw [h'vars "rs.a" (by decide) (by decide) (by decide) (by decide)]; exact hav,
        by rw [h'vars "rs.b" (by decide) (by decide) (by decide) (by decide)]; exact hbv,
        by rw [h'vars "rs.e" (by decide) (by decide) (by decide) (by decide)]; exact hev,
        by rw [h'd, ← hL_def]; omega,
        ?_, ?_⟩, by rw [h'd]⟩
    · rw [h'd, h't, htv, ← hL_def, hkept1]
    · refine ⟨fun p => if p = Bb + 1 + t then x - 1 else f p, ?_, ?_, ?_, ?_⟩
      · rw [h'hist, set_arrOf]
      · intro a ha r hr
        obtain ⟨hbase, hents⟩ := hdoneA a ha r hr
        refine ⟨?_, ?_⟩
        · show (if (a * ℓp + r) * (hb + 1) = Bb + 1 + t then x - 1
              else f ((a * ℓp + r) * (hb + 1))) = _
          rw [if_neg, hbase]
          intro hcon
          have hcon' : (a * ℓp + r) * (hb + 1) + 0
              = (i * ℓp + q) * (hb + 1) + (1 + t) := by
            rw [hBb_def] at hcon
            omega
          have hinj := hist_idx_inj (hr := hr) (hc := Nat.zero_lt_succ hb)
            (hr' := hqp) (hc' := show 1 + t < hb + 1 by omega) hcon'
          omega
        · intro m hm
          show (if (a * ℓp + r) * (hb + 1) + 1 + m = Bb + 1 + t then x - 1
              else f ((a * ℓp + r) * (hb + 1) + 1 + m)) = _
          rw [if_neg, hents m hm]
          intro hcon
          have hmhb : m < hb := by
            have := histN_len_le hh (embN S a) r
            have hle : (chN histP S a r).length ≤ (histN histP (embN S a) r).length :=
              List.length_filterMap_le _ _
            omega
          have hcon' : (a * ℓp + r) * (hb + 1) + (1 + m)
              = (i * ℓp + q) * (hb + 1) + (1 + t) := by
            rw [hBb_def] at hcon
            omega
          have hinj := hist_idx_inj (hr := hr) (hc := show 1 + m < hb + 1 by omega)
            (hr' := hqp) (hc' := show 1 + t < hb + 1 by omega) hcon'
          omega
      · intro r hr
        obtain ⟨hbase, hents⟩ := hdoneR r hr
        refine ⟨?_, ?_⟩
        · show (if (i * ℓp + r) * (hb + 1) = Bb + 1 + t then x - 1
              else f ((i * ℓp + r) * (hb + 1))) = _
          rw [if_neg, hbase]
          intro hcon
          have hcon' : (i * ℓp + r) * (hb + 1) + 0
              = (i * ℓp + q) * (hb + 1) + (1 + t) := by
            rw [hBb_def] at hcon
            omega
          have hinj := hist_idx_inj (hr := lt_trans hr hqp)
            (hc := Nat.zero_lt_succ hb)
            (hr' := hqp) (hc' := show 1 + t < hb + 1 by omega) hcon'
          omega
        · intro m hm
          show (if (i * ℓp + r) * (hb + 1) + 1 + m = Bb + 1 + t then x - 1
              else f ((i * ℓp + r) * (hb + 1) + 1 + m)) = _
          rw [if_neg, hents m hm]
          intro hcon
          have hmhb : m < hb := by
            have := histN_len_le hh (embN S i) r
            have hle : (chN histP S i r).length ≤ (histN histP (embN S i) r).length :=
              List.length_filterMap_le _ _
            omega
          have hcon' : (i * ℓp + r) * (hb + 1) + (1 + m)
              = (i * ℓp + q) * (hb + 1) + (1 + t) := by
            rw [hBb_def] at hcon
            omega
          have hinj := hist_idx_inj (hr := lt_trans hr hqp)
            (hc := show 1 + m < hb + 1 by omega)
            (hr' := hqp) (hc' := show 1 + t < hb + 1 by omega) hcon'
          omega
      · intro m hm
        rw [h't] at hm
        show (if Bb + 1 + m = Bb + 1 + t then x - 1 else f (Bb + 1 + m))
          = (chN histP S i q).getD m 0
        by_cases hmt : m = t
        · subst hmt
          rw [if_pos rfl, chN, ← hL_def, htv]
          exact (filterMap_getD_kept hlt hsome).symm
        · rw [if_neg (by omega)]
          exact hcur m (by omega)
  · -- unmarked: skipped
    have hcondF : (Cond.lt (.lit 0) (.var "rs.x")).evalB B σb = some false := by
      rw [hcond]
      congr 1
      simpa using hx0
    have hnone : rkOpt S (L.getD d 0) = none :=
      (rkOpt_eq_none_iff_rk S _).mpr (by omega)
    have hite : Run B (.ite (.lt (.lit 0) (.var "rs.x"))
        (.seq (.store nmC.hist (.add (.var "rs.b") (.add (.var "rs.t") (.lit 1)))
            (.sub (.var "rs.x") (.lit 1)))
          (.assign "rs.t" (.add (.var "rs.t") (.lit 1)))) .skip) σb σb 17 :=
      (Run.ite_false hcondF Run.skip).mono (by simp)
    have hinc : Run B (.assign "rs.d" (.add (.var "rs.d") (.lit 1))) σb
        (σb.setVar "rs.d" (d + 1)) 4 := by
      have hev := evalB_incr (B := B) (x := "rs.d") (σ := σb) (by rw [hbd]; omega)
      rw [hbd] at hev
      exact (Run.assign hev).mono (by simp)
    set σ' := σb.setVar "rs.d" (d + 1) with hσ'
    have hrun : Run B (histSlot nmP nmC ra) σ σ' 32 :=
      (hread.seq (hxread.seq (hite.seq hinc))).mono (by omega)
    have h'vars : ∀ y, y ≠ "rs.w" → y ≠ "rs.x" → y ≠ "rs.d" →
        σ'.vars y = σ.vars y := by
      intro y hy1 hy2 hy3
      rw [hσ', hσb, hσa]
      simp [hy1, hy2, hy3]
    have h'arrs : ∀ b, σ'.arrs b = σ.arrs b := by
      intro b
      rw [hσ', hσb, hσa]
      simp
    have h'd : σ'.vars "rs.d" = d + 1 := by rw [hσ']; simp
    refine ⟨σ', hrun,
      ⟨⟨by rw [h'arrs]; exact hh.1, fun v p => by rw [h'arrs]; exact hh.2 v p⟩,
        by rw [h'arrs]; exact hra,
        by rw [h'vars "rs.a" (by decide) (by decide) (by decide)]; exact hav,
        by rw [h'vars "rs.b" (by decide) (by decide) (by decide)]; exact hbv,
        by rw [h'vars "rs.e" (by decide) (by decide) (by decide)]; exact hev,
        by rw [h'd, ← hL_def]; omega,
        ?_, ?_⟩, by rw [h'd]⟩
    · rw [h'd, h'vars "rs.t" (by decide) (by decide) (by decide), ← ht_def, htv,
        ← hL_def, keptLen_succ_none hlt hnone]
    · exact ⟨f, by rw [h'arrs]; exact hfarr, hdoneA, hdoneR,
        fun m hm => hcur m (by
          rwa [h'vars "rs.t" (by decide) (by decide) (by decide)] at hm)⟩

private theorem getD_map_val {k' : ℕ} (l : List (Fin k')) {m : ℕ}
    (hm : m < l.length) : (l.map Fin.val).getD m 0 = (l[m] : ℕ) := by
  rw [getD_eq_getElem (by rw [List.length_map]; exact hm), List.getElem_map]

/-- **One round of a member's filter**: locate the two blocks, filter
the stored list in order, seal the kept count. -/
private theorem histRoundStep_spec (hNB : n < B) (hHB : n * ℓp * (hb + 1) < B)
    (hhc : nmC.hist ≠ nmP.hist) (hhra : nmC.hist ≠ ra) (hhla : nmC.hist ≠ la)
    {i : ℕ} (hik : i < S.ncard) :
    Spec B
      (fun σ => HistMidSt nmP nmC la ra n ℓp hb S histP i σ ∧
        σ.vars "rs.q" < ℓp)
      (.seq (histRound nmP nmC ra) (.assign "rs.q" (.add (.var "rs.q") (.lit 1))))
      (fun σ σ' => HistMidSt nmP nmC la ra n ℓp hb S histP i σ' ∧
        σ'.vars "rs.q" = σ.vars "rs.q" + 1)
      (36 * hb + 38) := by
  intro σ hσ
  obtain ⟨⟨hh, hcl, hk, hp, hhb, hra, hiv, hs, hq, f, hfarr, hdoneA, hdoneR⟩, hlt⟩ := hσ
  have hkn : S.ncard ≤ n := ncard_le_carrier S
  have hn1 : 1 ≤ n := by have := embN_lt S hik; omega
  have hsn : embN S i < n := embN_lt S hik
  set q₀ := σ.vars "rs.q" with hq0_def
  set A₀ := (embN S i * ℓp + q₀) * (hb + 1) with hA0_def
  set B₀ := (i * ℓp + q₀) * (hb + 1) with hB0_def
  set L := histN histP (embN S i) q₀ with hL_def
  have hLhb : L.length ≤ hb := histN_len_le hh _ _
  have hA0lt : A₀ < n * ℓp * (hb + 1) := by
    have h := hist_idx_lt (hb := hb) hsn hlt (show 0 < hb + 1 by omega)
    rw [← hA0_def] at h
    omega
  have hB0lt : B₀ < S.ncard * ℓp * (hb + 1) := by
    have h := hist_idx_lt (n := S.ncard) (hb := hb) hik hlt
      (show 0 < hb + 1 by omega)
    rw [← hB0_def] at h
    omega
  have hkregion : S.ncard * ℓp * (hb + 1) ≤ n * ℓp * (hb + 1) :=
    Nat.mul_le_mul_right (hb + 1) (Nat.mul_le_mul_right ℓp hkn)
  have hhbB : hb + 1 < B := by
    have h1 : 1 * (hb + 1) ≤ n * ℓp * (hb + 1) :=
      Nat.mul_le_mul_right (hb + 1)
        (by have := Nat.mul_le_mul (show 1 ≤ n by omega) (show 1 ≤ ℓp by omega)
            simpa using this)
    omega
  have hpB : ℓp < B := by
    have h1 : n * ℓp ≤ n * ℓp * (hb + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have h2 : 1 * ℓp ≤ n * ℓp := Nat.mul_le_mul_right ℓp (by omega)
    omega
  have hslpq : embN S i * ℓp + q₀ < n * ℓp := by
    have h2 : (embN S i + 1) * ℓp ≤ n * ℓp := Nat.mul_le_mul_right ℓp (by omega)
    have h3 : (embN S i + 1) * ℓp = embN S i * ℓp + ℓp := by ring
    omega
  have hilpq : i * ℓp + q₀ < S.ncard * ℓp := by
    have h2 : (i + 1) * ℓp ≤ S.ncard * ℓp := Nat.mul_le_mul_right ℓp (by omega)
    have h3 : (i + 1) * ℓp = i * ℓp + ℓp := by ring
    omega
  have hnlp_le : n * ℓp ≤ n * ℓp * (hb + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hklp_le : S.ncard * ℓp ≤ S.ncard * ℓp * (hb + 1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  -- 1. the source base
  have hr1 : Run B (.assign "rs.a"
      (.mul (.add (.mul (.var "rs.s") (.var "rs.p")) (.var "rs.q"))
        (.add (.var "rs.h") (.lit 1)))) σ (σ.setVar "rs.a" A₀) 10 := by
    have hm1 : (Expr.mul (.var "rs.s") (.var "rs.p")).evalB B σ
        = some (embN S i * ℓp) := by
      have h := evalB_bin (B := B) (op := .mul)
        (evalB_var (x := "rs.s") (by rw [hs]; omega))
        (evalB_var (x := "rs.p") (by rw [hp]; omega))
        (by rw [hs, hp]; simp; omega)
      rw [hs, hp] at h
      simpa using h
    have hm2 : (Expr.add (.mul (.var "rs.s") (.var "rs.p")) (.var "rs.q")).evalB B σ
        = some (embN S i * ℓp + q₀) := by
      have h := evalB_bin (B := B) (op := .add) hm1
        (evalB_var (x := "rs.q") (by omega)) (by rw [← hq0_def]; simp; omega)
      rw [← hq0_def] at h
      simpa using h
    have hm3 : (Expr.add (.var "rs.h") (.lit 1)).evalB B σ = some (hb + 1) := by
      have h := evalB_incr (B := B) (x := "rs.h") (σ := σ) (by rw [hhb]; omega)
      rwa [hhb] at h
    have h := evalB_bin (B := B) (op := .mul) hm2 hm3
      (by simp; rw [← hA0_def]; omega)
    have h' : (Expr.mul (.add (.mul (.var "rs.s") (.var "rs.p")) (.var "rs.q"))
        (.add (.var "rs.h") (.lit 1))).evalB B σ = some A₀ := by
      rw [hA0_def]
      simpa using h
    exact (Run.assign h').mono (by simp)
  set σ₁ := σ.setVar "rs.a" A₀ with hσ₁
  have h1vars : ∀ y, y ≠ "rs.a" → σ₁.vars y = σ.vars y := by
    intro y hy
    rw [hσ₁]
    simp [hy]
  -- 2. the destination base
  have hr2 : Run B (.assign "rs.b"
      (.mul (.add (.mul (.var "rs.i") (.var "rs.p")) (.var "rs.q"))
        (.add (.var "rs.h") (.lit 1)))) σ₁ (σ₁.setVar "rs.b" B₀) 10 := by
    have h1i : σ₁.vars "rs.i" = i := by rw [h1vars _ (by decide)]; exact hiv
    have h1p : σ₁.vars "rs.p" = ℓp := by rw [h1vars _ (by decide)]; exact hp
    have h1q : σ₁.vars "rs.q" = q₀ := by rw [h1vars _ (by decide)]
    have h1h : σ₁.vars "rs.h" = hb := by rw [h1vars _ (by decide)]; exact hhb
    have hm1 : (Expr.mul (.var "rs.i") (.var "rs.p")).evalB B σ₁
        = some (i * ℓp) := by
      have h := evalB_bin (B := B) (op := .mul)
        (evalB_var (x := "rs.i") (by rw [h1i]; omega))
        (evalB_var (x := "rs.p") (by rw [h1p]; omega))
        (by rw [h1i, h1p]; simp
            have : i * ℓp ≤ S.ncard * ℓp := Nat.mul_le_mul_right ℓp (by omega)
            omega)
      rw [h1i, h1p] at h
      simpa using h
    have hm2 : (Expr.add (.mul (.var "rs.i") (.var "rs.p")) (.var "rs.q")).evalB B σ₁
        = some (i * ℓp + q₀) := by
      have h := evalB_bin (B := B) (op := .add) hm1
        (evalB_var (x := "rs.q") (by rw [h1q]; omega)) (by rw [h1q]; simp; omega)
      rw [h1q] at h
      simpa using h
    have hm3 : (Expr.add (.var "rs.h") (.lit 1)).evalB B σ₁ = some (hb + 1) := by
      have h := evalB_incr (B := B) (x := "rs.h") (σ := σ₁) (by rw [h1h]; omega)
      rwa [h1h] at h
    have h := evalB_bin (B := B) (op := .mul) hm2 hm3
      (by simp; rw [← hB0_def]; omega)
    have h' : (Expr.mul (.add (.mul (.var "rs.i") (.var "rs.p")) (.var "rs.q"))
        (.add (.var "rs.h") (.lit 1))).evalB B σ₁ = some B₀ := by
      rw [hB0_def]
      simpa using h
    exact (Run.assign h').mono (by simp)
  set σ₂ := σ₁.setVar "rs.b" B₀ with hσ₂
  have h2vars : ∀ y, y ≠ "rs.a" → y ≠ "rs.b" → σ₂.vars y = σ.vars y := by
    intro y hy1 hy2
    rw [hσ₂, hσ₁]
    simp [hy1, hy2]
  have h2arrs : ∀ b, σ₂.arrs b = σ.arrs b := by
    intro b
    rw [hσ₂, hσ₁]
    simp
  -- 3. the stored length
  have hr3 : Run B (.assign "rs.e" (.get nmP.hist (.var "rs.a"))) σ₂
      (σ₂.setVar "rs.e" L.length) 3 := by
    have h2a : σ₂.vars "rs.a" = A₀ := by rw [hσ₂]; simp [hσ₁]
    have haev : (Expr.var "rs.a").evalB B σ₂ = some A₀ := by
      rw [← h2a]
      exact evalB_var (by rw [h2a]; omega)
    refine (Run.assign (evalB_get haev ?_ (by omega))).mono (by simp)
    rw [h2arrs, getElem?_eq_getD (by rw [hh.1]; omega)]
    rw [histArr_base hh hsn hlt]
  set σ₃ := σ₂.setVar "rs.e" L.length with hσ₃
  -- 4. reset the kept count
  have hr4 : Run B (.assign "rs.t" (.lit 0)) σ₃ (σ₃.setVar "rs.t" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  set σ₄ := σ₃.setVar "rs.t" 0 with hσ₄
  have h4vars : ∀ y, y ≠ "rs.a" → y ≠ "rs.b" → y ≠ "rs.e" → y ≠ "rs.t" →
      σ₄.vars y = σ.vars y := by
    intro y hy1 hy2 hy3 hy4
    rw [hσ₄, hσ₃, hσ₂, hσ₁]
    simp [hy1, hy2, hy3, hy4]
  have h4arrs : ∀ b, σ₄.arrs b = σ.arrs b := by
    intro b
    rw [hσ₄, hσ₃, hσ₂, hσ₁]
    simp
  -- 5. the filter loop
  have hIn : HistInSt nmP nmC ra n ℓp hb S histP i q₀ (σ₄.setVar "rs.d" 0) := by
    have hv : ∀ y, y ≠ "rs.d" → (σ₄.setVar "rs.d" 0).vars y = σ₄.vars y := by
      intro y hy
      simp [hy]
    have ha : ∀ b, (σ₄.setVar "rs.d" 0).arrs b = σ.arrs b := by
      intro b
      simp only [arrs_setVar]
      exact h4arrs b
    have h4a : σ₄.vars "rs.a" = A₀ := by rw [hσ₄, hσ₃, hσ₂]; simp [hσ₁]
    have h4b : σ₄.vars "rs.b" = B₀ := by rw [hσ₄, hσ₃]; simp [hσ₂]
    have h4e : σ₄.vars "rs.e" = L.length := by rw [hσ₄]; simp [hσ₃]
    have h4t : σ₄.vars "rs.t" = 0 := by rw [hσ₄]; simp
    refine ⟨⟨by rw [ha]; exact hh.1, fun v p => by rw [ha]; exact hh.2 v p⟩,
      by rw [ha]; exact hra,
      by rw [hv "rs.a" (by decide)]; exact h4a,
      by rw [hv "rs.b" (by decide)]; exact h4b,
      by rw [hv "rs.e" (by decide)]; exact h4e,
      by simp,
      ?_,
      f, by rw [ha]; exact hfarr, hdoneA, hdoneR, ?_⟩
    · have h1 : (σ₄.setVar "rs.d" 0).vars "rs.t" = 0 := by
        rw [vars_setVar, if_neg (by decide)]
        exact h4t
      have h2 : (σ₄.setVar "rs.d" 0).vars "rs.d" = 0 := by simp
      rw [h1, h2, keptLen_zero]
    · intro m hm
      have h1 : (σ₄.setVar "rs.d" 0).vars "rs.t" = 0 := by
        rw [vars_setVar, if_neg (by decide)]
        exact h4t
      rw [h1] at hm
      omega
  have hinner := Spec.forRangeZero (B := B) "rs.d" "rs.e"
    (HistInSt nmP nmC ra n ℓp hb S histP i q₀) L.length 32 (by omega)
    (fun τ hτ => hτ.hdN) (fun τ hτ => hτ.hev)
    (histSlot_spec hNB hHB hhc hhra hik hlt)
  obtain ⟨σ₅, hr5, hpost5⟩ := (hinner.frame).run hIn
  obtain ⟨⟨hIn5, hd5⟩, hfv5, hfa5, -, -⟩ := hpost5
  obtain ⟨hh5, hra5, hav5, hbv5, hev5, hdN5, htv5, f5, hfarr5, hdoneA5, hdoneR5, hcur5⟩ := hIn5
  have hwv : (Com.seq (.assign "rs.d" (.lit 0))
      (.while (.lt (.var "rs.d") (.var "rs.e")) (histSlot nmP nmC ra))).wvars
      = ["rs.d", "rs.w", "rs.x", "rs.t", "rs.d"] := rfl
  have hwa : (Com.seq (.assign "rs.d" (.lit 0))
      (.while (.lt (.var "rs.d") (.var "rs.e")) (histSlot nmP nmC ra))).warrs
      = [nmC.hist] := rfl
  have h5keep : ∀ y, y ∈ (["rs.q", "rs.i", "rs.s", "rs.k", "rs.p", "rs.h"] :
      List String) → σ₅.vars y = σ₄.vars y := by
    intro y hy
    refine hfv5 y ?_
    rw [hwv]
    fin_cases hy <;> decide
  have h5la : σ₅.arrs la = σ₄.arrs la := by
    refine hfa5 la ?_
    rw [hwa]
    simp [Ne.symm hhla]
  -- the kept count sealed the whole list
  have ht5 : σ₅.vars "rs.t" = (chN histP S i q₀).length := by
    rw [htv5, hd5]
    have h := keptLen_full (rkOpt S) (histN histP (embN S i) q₀)
    rw [← hL_def] at h ⊢
    rw [h]
    rfl
  have hchlen : (chN histP S i q₀).length ≤ hb := by
    have h1 : (chN histP S i q₀).length ≤ L.length := by
      rw [chN, ← hL_def]
      exact List.length_filterMap_le _ _
    omega
  -- 6. seal the length prefix
  have hr6 : Run B (.store nmC.hist (.var "rs.b") (.var "rs.t")) σ₅
      (σ₅.setArr nmC.hist B₀ ((chN histP S i q₀).length)) 3 := by
    have hbev : (Expr.var "rs.b").evalB B σ₅ = some B₀ := by
      have h := evalB_var (B := B) (x := "rs.b") (σ := σ₅)
        (by rw [hbv5, ← hB0_def]; omega)
      rw [hbv5, ← hB0_def] at h
      exact h
    have htev : (Expr.var "rs.t").evalB B σ₅
        = some ((chN histP S i q₀).length) := by
      rw [← ht5]
      exact evalB_var (by rw [ht5]; omega)
    refine (Run.store hbev htev ?_).mono (by simp)
    rw [hfarr5, length_arrOf]
    omega
  set σ₆ := σ₅.setArr nmC.hist B₀ ((chN histP S i q₀).length) with hσ₆
  -- 7. the round counter
  have hr7 : Run B (.assign "rs.q" (.add (.var "rs.q") (.lit 1))) σ₆
      (σ₆.setVar "rs.q" (q₀ + 1)) 4 := by
    have h6q : σ₆.vars "rs.q" = q₀ := by
      rw [hσ₆]
      simp only [vars_setArr]
      rw [h5keep "rs.q" (by simp), h4vars "rs.q" (by decide) (by decide) (by decide)
        (by decide)]
    have hev := evalB_incr (B := B) (x := "rs.q") (σ := σ₆) (by rw [h6q]; omega)
    rw [h6q] at hev
    exact (Run.assign hev).mono (by simp)
  set σ₇ := σ₆.setVar "rs.q" (q₀ + 1) with hσ₇
  have h7vars : ∀ y, y ∈ (["rs.i", "rs.s", "rs.k", "rs.p", "rs.h"] : List String) →
      σ₇.vars y = σ.vars y := by
    intro y hy
    have hyq : y ≠ "rs.q" := by fin_cases hy <;> decide
    rw [hσ₇, vars_setVar, if_neg hyq, hσ₆, vars_setArr, h5keep y (by fin_cases hy <;> simp)]
    refine h4vars y ?_ ?_ ?_ ?_ <;> fin_cases hy <;> decide
  have h7arrs : ∀ b, b ≠ nmC.hist → σ₇.arrs b = σ₅.arrs b := by
    intro b hb'
    rw [hσ₇, hσ₆]
    simp [hb']
  have h7q : σ₇.vars "rs.q" = q₀ + 1 := by rw [hσ₇]; simp
  -- assemble
  refine ⟨σ₇, ?_, ⟨⟨by rw [h7arrs _ (Ne.symm hhc)]; exact hh5.1,
      fun v p => by rw [h7arrs _ (Ne.symm hhc)]; exact hh5.2 v p⟩,
    ⟨by rw [h7arrs _ (Ne.symm hhla), h5la]; simpa using hcl.1,
      fun t' ht' => by rw [h7arrs _ (Ne.symm hhla), h5la]; simpa using hcl.2 t' ht'⟩,
    by rw [h7vars "rs.k" (by simp)]; exact hk,
    by rw [h7vars "rs.p" (by simp)]; exact hp,
    by rw [h7vars "rs.h" (by simp)]; exact hhb,
    by rw [h7arrs _ (Ne.symm hhra)]; exact hra5,
    by rw [h7vars "rs.i" (by simp)]; exact hiv,
    by rw [h7vars "rs.s" (by simp)]; exact hs,
    by rw [h7q]; omega, ?_⟩, by rw [h7q]⟩
  · -- the run, at the round budget
    have h := (hr1.seq (hr2.seq (hr3.seq (hr4.seq (hr5.seq hr6))))).seq hr7
    refine h.mono ?_
    have : (32 + 4) * L.length + 6 ≤ 36 * hb + 6 := by
      have := Nat.mul_le_mul_left 36 hLhb
      omega
    omega
  · -- the sealed round joins the done set
    refine ⟨fun p => if p = B₀ then (chN histP S i q₀).length else f5 p, ?_, ?_, ?_⟩
    · rw [hσ₇, arrs_setVar, hσ₆, arrs_setArr, if_pos rfl, hfarr5, set_arrOf]
    · intro a ha r hr
      obtain ⟨hbase, hents⟩ := hdoneA5 a ha r hr
      refine ⟨?_, ?_⟩
      · show (if (a * ℓp + r) * (hb + 1) = B₀ then _ else f5 ((a * ℓp + r) * (hb + 1)))
          = _
        rw [if_neg, hbase]
        intro hcon
        have hcon' : (a * ℓp + r) * (hb + 1) + 0
            = (i * ℓp + q₀) * (hb + 1) + 0 := by
          rw [hB0_def] at hcon
          omega
        have hinj := hist_idx_inj (hr := hr) (hc := Nat.zero_lt_succ hb)
          (hr' := hlt) (hc' := Nat.zero_lt_succ hb) hcon'
        omega
      · intro m hm
        show (if (a * ℓp + r) * (hb + 1) + 1 + m = B₀ then _
            else f5 ((a * ℓp + r) * (hb + 1) + 1 + m)) = _
        rw [if_neg, hents m hm]
        intro hcon
        have hmhb : m < hb := by
          have := histN_len_le hh (embN S a) r
          have hle : (chN histP S a r).length ≤ (histN histP (embN S a) r).length :=
            List.length_filterMap_le _ _
          omega
        have hcon' : (a * ℓp + r) * (hb + 1) + (1 + m)
            = (i * ℓp + q₀) * (hb + 1) + 0 := by
          rw [hB0_def] at hcon
          omega
        have hinj := hist_idx_inj (hr := hr) (hc := show 1 + m < hb + 1 by omega)
          (hr' := hlt) (hc' := Nat.zero_lt_succ hb) hcon'
        omega
    · intro r hr
      rw [h7q] at hr
      rcases Nat.lt_or_ge r q₀ with hrq | hrq
      · obtain ⟨hbase, hents⟩ := hdoneR5 r hrq
        refine ⟨?_, ?_⟩
        · show (if (i * ℓp + r) * (hb + 1) = B₀ then _
              else f5 ((i * ℓp + r) * (hb + 1))) = _
          rw [if_neg, hbase]
          intro hcon
          have hcon' : (i * ℓp + r) * (hb + 1) + 0
              = (i * ℓp + q₀) * (hb + 1) + 0 := by
            rw [hB0_def] at hcon
            omega
          have hinj := hist_idx_inj (hr := lt_trans hrq hlt)
            (hc := Nat.zero_lt_succ hb)
            (hr' := hlt) (hc' := Nat.zero_lt_succ hb) hcon'
          omega
        · intro m hm
          show (if (i * ℓp + r) * (hb + 1) + 1 + m = B₀ then _
              else f5 ((i * ℓp + r) * (hb + 1) + 1 + m)) = _
          rw [if_neg, hents m hm]
          intro hcon
          have hmhb : m < hb := by
            have := histN_len_le hh (embN S i) r
            have hle : (chN histP S i r).length ≤ (histN histP (embN S i) r).length :=
              List.length_filterMap_le _ _
            omega
          have hcon' : (i * ℓp + r) * (hb + 1) + (1 + m)
              = (i * ℓp + q₀) * (hb + 1) + 0 := by
            rw [hB0_def] at hcon
            omega
          have hinj := hist_idx_inj (hr := lt_trans hrq hlt)
            (hc := show 1 + m < hb + 1 by omega)
            (hr' := hlt) (hc' := Nat.zero_lt_succ hb) hcon'
          omega
      · have hre : r = q₀ := by omega
        refine ⟨?_, ?_⟩
        · show (if (i * ℓp + r) * (hb + 1) = B₀ then (chN histP S i q₀).length
              else f5 ((i * ℓp + r) * (hb + 1))) = (chN histP S i r).length
          rw [hre, if_pos (by rw [hB0_def])]
        · intro m hm
          show (if (i * ℓp + r) * (hb + 1) + 1 + m = B₀
                then (chN histP S i q₀).length
              else f5 ((i * ℓp + r) * (hb + 1) + 1 + m)) = (chN histP S i r).getD m 0
          rw [hre, if_neg, hcur5 m (by rw [ht5, ← hre]; exact hm)]
          intro hcon
          rw [hB0_def] at hcon
          omega

/-- One member of the channel filter: all its rounds, in order. -/
private theorem histBody_spec (hNB : n < B) (hHB : n * ℓp * (hb + 1) < B)
    (hhc : nmC.hist ≠ nmP.hist) (hhra : nmC.hist ≠ ra) (hhla : nmC.hist ≠ la) :
    Spec B
      (fun σ => HistSt nmP nmC la ra n ℓp hb S histP σ ∧
        σ.vars "rs.i" < S.ncard)
      (histBody nmP nmC la ra)
      (fun σ σ' => HistSt nmP nmC la ra n ℓp hb S histP σ' ∧
        σ'.vars "rs.i" = σ.vars "rs.i" + 1)
      ((36 * hb + 42) * ℓp + 13) := by
  intro σ hσ
  obtain ⟨⟨hh, hcl, hk, hp, hhb, hra, hiN, f, hfarr, hdone⟩, hlt⟩ := hσ
  have hkn : S.ncard ≤ n := ncard_le_carrier S
  have hn1 : 1 ≤ n := by have := embN_lt S hlt; omega
  set i := σ.vars "rs.i" with hi_def
  -- the member read
  have hread : Run B (.assign "rs.s" (.get la (.var "rs.i"))) σ
      (σ.setVar "rs.s" (embN S i)) 3 := by
    refine (Run.assign (evalB_get (evalB_var (by omega)) ?_
      (by have := embN_lt S hlt; omega))).mono (by simp)
    exact clusterList_read hcl hlt
  set σ₁ := σ.setVar "rs.s" (embN S i) with hσ₁
  -- the rounds
  have hMid₁ : HistMidSt nmP nmC la ra n ℓp hb S histP i (σ₁.setVar "rs.q" 0) := by
    have hv : ∀ y, y ≠ "rs.q" → y ≠ "rs.s" →
        ((σ₁.setVar "rs.q" 0)).vars y = σ.vars y := by
      intro y hy1 hy2
      rw [hσ₁]
      simp [hy1, hy2]
    have ha : ∀ b, ((σ₁.setVar "rs.q" 0)).arrs b = σ.arrs b := by
      intro b
      rw [hσ₁]
      simp
    refine ⟨⟨by rw [ha]; exact hh.1, fun v p => by rw [ha]; exact hh.2 v p⟩,
      ⟨by rw [ha]; exact hcl.1, fun t ht => by rw [ha]; exact hcl.2 t ht⟩,
      by rw [hv "rs.k" (by decide) (by decide)]; exact hk,
      by rw [hv "rs.p" (by decide) (by decide)]; exact hp,
      by rw [hv "rs.h" (by decide) (by decide)]; exact hhb,
      by rw [ha]; exact hra,
      by rw [hv "rs.i" (by decide) (by decide)],
      by rw [vars_setVar, if_neg (by decide), hσ₁]; simp,
      by simp,
      f, by rw [ha]; exact hfarr, hdone, ?_⟩
    intro r hr
    rw [vars_setVar, if_pos rfl] at hr
    omega
  have hmid := Spec.forRangeZero (B := B) "rs.q" "rs.p"
    (HistMidSt nmP nmC la ra n ℓp hb S histP i) ℓp (36 * hb + 38)
    (by
      have h1 : 1 * ℓp ≤ n * ℓp := Nat.mul_le_mul_right ℓp (by omega)
      have h2 : n * ℓp ≤ n * ℓp * (hb + 1) := Nat.le_mul_of_pos_right _ (by omega)
      omega)
    (fun τ hτ => hτ.hq) (fun τ hτ => hτ.hp)
    (histRoundStep_spec hNB hHB hhc hhra hhla hlt)
  obtain ⟨σ₂, hmrun, hMid₂, hq₂⟩ := hmid.run hMid₁
  obtain ⟨hh₂, hcl₂, hk₂, hp₂, hhb₂, hra₂, hiv₂, hs₂, -, f₂, hfarr₂, hdoneA₂, hdoneR₂⟩ := hMid₂
  -- the member counter
  have hinc : Run B (.assign "rs.i" (.add (.var "rs.i") (.lit 1))) σ₂
      (σ₂.setVar "rs.i" (i + 1)) 4 := by
    have hev := evalB_incr (B := B) (x := "rs.i") (σ := σ₂) (by rw [hiv₂]; omega)
    rw [hiv₂] at hev
    exact (Run.assign hev).mono (by simp)
  refine ⟨σ₂.setVar "rs.i" (i + 1), ?_,
    ⟨⟨by simpa using hh₂.1, fun v p => by simpa using hh₂.2 v p⟩,
      ⟨by simpa using hcl₂.1, fun t ht => by simpa using hcl₂.2 t ht⟩,
      by simpa using hk₂,
      by simpa using hp₂,
      by simpa using hhb₂,
      by simpa using hra₂,
      by simp; omega, ?_⟩, by simp [← hi_def]⟩
  · have h := hread.seq (hmrun.seq hinc)
    refine h.mono ?_
    have heq : (36 * hb + 38 + 4) * ℓp = (36 * hb + 42) * ℓp := by ring
    omega
  · refine ⟨f₂, by simpa using hfarr₂, ?_⟩
    intro a ha r hr
    simp at ha
    rcases Nat.lt_or_ge a i with hai | hai
    · exact hdoneA₂ a hai r hr
    · have hae : a = i := by omega
      subst hae
      exact hdoneR₂ r (by omega)

/-- **The channel filter, discharged**: the child channel region ends at
`(A.restrict S).hist` — per vertex and per round, the stored list's
in-order intersection with the cluster, renamed local. Cost
`|S|·O(ℓp·(hb+1))`. -/
private theorem histFilter_spec (hNB : n < B) (hHB : n * ℓp * (hb + 1) < B)
    (hhc : nmC.hist ≠ nmP.hist) (hhra : nmC.hist ≠ ra) (hhla : nmC.hist ≠ la) :
    Spec B
      (fun σ => HistArr nmP.hist ℓp hb histP σ ∧ ClusterList la S σ ∧
        σ.vars "rs.k" = S.ncard ∧ σ.vars "rs.p" = ℓp ∧ σ.vars "rs.h" = hb ∧
        σ.arrs ra = arrOf n (rk S) ∧
        (σ.arrs nmC.hist).length = S.ncard * ℓp * (hb + 1))
      (histFilter nmP nmC la ra)
      (fun _ σ' => HistArr nmP.hist ℓp hb histP σ' ∧ ClusterList la S σ' ∧
        σ'.vars "rs.k" = S.ncard ∧ σ'.arrs ra = arrOf n (rk S) ∧
        HistArr nmC.hist ℓp hb
          (fun a r => (histP (Impl.restrictEmb S a) r).filterMap
            (Impl.toLocal S)) σ')
      (((36 * hb + 42) * ℓp + 17) * S.ncard + 6) := by
  have hmain := Spec.forRangeZero (B := B) "rs.i" "rs.k"
    (HistSt nmP nmC la ra n ℓp hb S histP) S.ncard ((36 * hb + 42) * ℓp + 13)
    (by have := ncard_le_carrier S; omega)
    (fun τ hτ => hτ.hiN) (fun τ hτ => hτ.hk)
    (histBody_spec hNB hHB hhc hhra hhla)
  refine ((hmain.pre ?_).post ?_).mono le_rfl
  · rintro σ ⟨hh, hcl, hk, hp, hhb, hra, hlen⟩
    refine ⟨⟨by simpa using hh.1, fun v p => by simpa using hh.2 v p⟩,
      ⟨by simpa using hcl.1, fun t ht => by simpa using hcl.2 t ht⟩,
      by simpa using hk, by simpa using hp, by simpa using hhb,
      by simpa using hra, by simp,
      fun p => (σ.arrs nmC.hist).getD p 0, ?_, ?_⟩
    · simp only [arrs_setVar]
      rw [← hlen]
      exact (arrOf_getD _).symm
    · intro a ha
      simp at ha
  · rintro σ σ' - ⟨⟨hh, hcl, hk, -, -, hra, -, f, hfarr, hdone⟩, hie⟩
    refine ⟨hh, hcl, hk, hra, by rw [hfarr, length_arrOf], ?_⟩
    intro v p
    show ((histP (Impl.restrictEmb S v) p).filterMap (Impl.toLocal S)).length ≤ hb ∧
      (σ'.arrs nmC.hist).getD (((v : ℕ) * ℓp + (p : ℕ)) * (hb + 1)) 0
        = ((histP (Impl.restrictEmb S v) p).filterMap (Impl.toLocal S)).length ∧
      ∀ m : ℕ,
        ∀ _ : m < ((histP (Impl.restrictEmb S v) p).filterMap
          (Impl.toLocal S)).length,
        (σ'.arrs nmC.hist).getD (((v : ℕ) * ℓp + (p : ℕ)) * (hb + 1) + 1 + m) 0
          = (((histP (Impl.restrictEmb S v) p).filterMap (Impl.toLocal S))[m] : ℕ)
    have hvk : (v : ℕ) < S.ncard := v.2
    have hpl : (p : ℕ) < ℓp := p.2
    obtain ⟨hbase, hents⟩ := hdone (v : ℕ) (by rw [hie]; exact hvk) (p : ℕ) hpl
    have hch : chN histP S (v : ℕ) (p : ℕ)
        = ((histP (Impl.restrictEmb S v) p).filterMap (Impl.toLocal S)).map
            Fin.val := by
      have h := chN_eq (S := S) (histP := histP) hvk hpl
      rw [show (⟨(v : ℕ), hvk⟩ : Fin S.ncard) = v from Fin.ext rfl,
        show (⟨(p : ℕ), hpl⟩ : Fin ℓp) = p from Fin.ext rfl] at h
      exact h
    have hlen_eq : (chN histP S (v : ℕ) (p : ℕ)).length
        = ((histP (Impl.restrictEmb S v) p).filterMap (Impl.toLocal S)).length := by
      rw [hch, List.length_map]
    have hlenhb : (chN histP S (v : ℕ) (p : ℕ)).length ≤ hb := by
      have h1 : (chN histP S (v : ℕ) (p : ℕ)).length
          ≤ (histN histP (embN S (v : ℕ)) (p : ℕ)).length :=
        List.length_filterMap_le _ _
      have h2 := histN_len_le hh (embN S (v : ℕ)) (p : ℕ)
      omega
    refine ⟨by omega, ?_, ?_⟩
    · rw [hfarr, getD_arrOf _ (by
        have := hist_idx_lt (n := S.ncard) (hb := hb) hvk hpl
          (show 0 < hb + 1 by omega)
        omega), hbase, hlen_eq]
    · intro m hm
      have hmch : m < (chN histP S (v : ℕ) (p : ℕ)).length := by omega
      rw [hfarr, getD_arrOf _ (by
        have := hist_idx_lt (n := S.ncard) (hb := hb) hvk hpl
          (show 1 + m < hb + 1 by omega)
        omega), hents m hmch, hch, getD_map_val _ (by omega)]

end HistFilter

end Phases

end Lax3Proofs.Prog
