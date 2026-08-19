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

end Phases

end Lax3Proofs.Prog
