import Mathlib.Data.List.GetD
import Lax3Proofs.SolveBlocks

/-!
# F6c/2 — `restrict` and `isolate` as IMP+ programs, discharged

The first two rows of §4's operation table, on the machine.
**`restrictCom`** builds, from a parent frame state `ArenaSt nmP hb A`
and the cluster's enumeration region, the child frame state — and
`restrictCom_spec`'s postcondition is `ArenaSt nmC hb (A.restrict S)`:
the machine child **IS** the abstract `Impl.MArena.restrict`, whose
identities to `Driver.preG`/`childArena` are already landed
(`ImplRestrict` §1c), so E13 plugs this program where the abstract
driver holds its child. **`isolateCom`** rebuilds the child CSR into
fresh names skipping the batch's vertices and edges, postcondition
`ArenaSt {nmI with off, tgt, nS} hb (Bar.isolate W)` — `deleteVerts` at
the machine, with the input state (the `preG` arena the profiles were
measured in) intact beside it.

## The seam rules, obeyed and visible

* **One scratch array, self-cleaning.** The rank scratch `ra` arrives
  **clean** (`arrOf A.N (fun _ => 0)`) and the postcondition returns it
  clean — `rankMark` writes exactly the `|S|` entries `la[i] ← i+1` and
  `rankClear` wipes exactly those `|S|` entries again (`rkP`/`rkC` are
  the two progress functions; no carrier-sized wipe appears anywhere in
  the program text). Cleanliness is load-bearing, exactly as
  `ImplRestrict`'s `restrictSweep_fst` warns: a stale nonzero entry
  would be read as membership and the child graph would be *wrong*, not
  slow.
* **The membership test rides the scratch.** The scratch holds
  *rank-plus-one* (`rk`): one lookup per scanned target decides
  membership (`0 <`) and yields the local name (`− 1`) together —
  `csrSlot` and `histSlot` are that one lookup each.
* **Row scans are priced at the parent degree.** `csrFill`'s budget is
  `27·Σ_{t<|S|} rowLen_A(member t)` and the file proves that sum **is**
  `Impl.degSum A.G S` (`sum_rowLen_emb_eq_degSum`) — `Σ_{s∈S} deg_A(s)`,
  never the false `O(‖A[S]‖+|S|)` shape (`K_{3,n−3}`, §4's hazard).
  The outer loop is amortized (`Run.while_potential` with the remaining
  members' parent degrees as the potential), because a member's row
  scan has no uniform bound.
* **The budget's terms mirror `Impl.childCharge` by name.**
  `restrictK dS k Λ ℓp hb = 27·dS + k·(20·Λ + (36·hb+42)·ℓp + 132) + 45`:
  the `dS = degSum` row-scan term, the `|S|·Λ` color-copy term, the
  `|S|·ℓp·O(hb)` channel term, and the `|S|`-proportional mark/rename/
  clear — no `A.N` term (the allocation is the node's `nodeCharge`, not
  the child's). `restrictK_le_childCharge` closes the correspondence at
  `hb := 2R+1`: `restrictK ≤ 132·(childCharge + 1)`. Likewise
  `isolateK N ns = 25·ns + 33·N + 13` is `isolateCharge`'s
  `Σ_v (deg v + 1)` shape, `isolateK_le_isolateCharge`.

## The programs

`restrictCom = rankMark; csrFill; colCopy; upCopy; histFilter;
rankClear; sizeCells`. The child CSR is built in one **fused
count/fill pass** (`csrFill`): rows are emitted in enumeration order,
so each row's boundary is sealed as the write cursor passes it — the
count/prefix/fill pattern with the prefix sums coming out of the single
sweep. `histFilter` filters each stored list **in order**
(`filterMap_rkOpt_map_val` is `Impl.restrict_hist_map`'s in-order
intersection at plain numbers). `isolateCom` is one sweep of the child
CSR: a batched vertex's output row is empty and its input row is never
scanned; a kept row is filtered by the batch bits.

## Stored values (the `mcB` hazard, per write)

* `rankMark` stores ranks `i+1 ≤ |S| ≤ A.N` into `ra`; `rankClear`
  stores `0`.
* `csrFill` stores offsets `coff a ≤ cns ≤ ns = 2M` into the child
  `off` region and local names `< |S| ≤ A.N` into the child `tgt`
  region.
* `colCopy` stores bits `≤ 1`; its indices are `< |S|·Λ ≤ A.N·Λ`
  (hypothesis `A.N·Λ < B`).
* `upCopy` stores root names `< n₀`.
* `histFilter` stores length prefixes `≤ hb` and local names `< |S|`;
  its indices are `< |S|·ℓp·(hb+1) ≤ A.N·ℓp·(hb+1)` (hypothesis
  `A.N·ℓp·(hb+1) < B` — the two-carrier-factor indices of the head
  file's stored-value paragraph).
* `sizeCells` stores `|S| ≤ A.N` and `cns ≤ ns`; `isolateCom` stores
  offsets/targets `≤ ns`/`< N` and the new slot count `≤ ns`.

## Two seam findings (loudly)

1. **`Driver.setEquiv` is `Classical`-chosen, not the sorted
   enumeration.** `ImplRestrict`'s docstring calls `restrictEmb` "the
   sorted enumeration", but the theorem (`DriverArena.setEquiv`, built
   from `Finset.equivFin`, i.e. `Trunc.out`) pins **no** concrete
   order — its own docstring says `Classical`-chosen. Consequence: no
   machine program can *compute* the abstract local names, so the
   enumeration must enter as **data**. `ClusterList la S σ` is that
   seam: the cluster region is preconditioned to hold `restrictEmb S`'s
   order, and the program realizes the renaming by reading it. The
   cover slot therefore owes the cluster *in the child's enumeration
   order* (the "bit-vectors alongside the order" of the head file's
   item (b)); since its own sweep discovers members in some concrete
   order, the campaign will need either to repin `setEquiv` to the
   monotone enumeration (`Finset.orderIsoOfFin`; then an ascending
   member list discharges `ClusterList` by a lemma, and this file needs
   no change) or to thread an enumeration parameter through the driver
   layer. Flagged for the supervisor; not fixable from this file's
   ownership.
2. **`ArenaSt`'s exact-length `Csr` forces per-child region sizes.**
   `Csr` demands `σ.arrs off = arrOf (N+1) _` — exact length — and IMP+
   array lengths are immutable (`Env.setArr` preserves them). So the
   level-`(j+1)` regions can satisfy `ArenaSt (arenaNames (j+1))` only
   if their allocated lengths equal *this* child's dimensions; two
   different-sized clusters at the same level in one run cannot both.
   This spec takes the exact child lengths as preconditions (the only
   honest reading of the landed contract); the frame-block composition
   will need max-size regions with a windowed/prefix variant of the
   contract's CSR. Flagged; the contract file is the supervisor's.

Both specs otherwise compose exactly as the head file plans: state in,
state out, scratch clean, everything else framed
(`warrs_restrictCom`/`wvars_restrictCom_subset` and the isolate pair
are the frame surface).
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
    simp only [arrs_setVar, vars_setVar]
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
    simp only [arrs_setVar, vars_setVar]
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

/-! ## §12 The frame data of the phases -/

section FrameData

variable (nmP nmC : ArenaNames) (la ra : String)

private theorem wvars_rankMark : (rankMark la ra).wvars = ["rs.i", "rs.s", "rs.i"] := rfl
private theorem warrs_rankMark : (rankMark la ra).warrs = [ra] := rfl
private theorem wvars_rankClear : (rankClear la ra).wvars = ["rs.i", "rs.s", "rs.i"] := rfl
private theorem warrs_rankClear : (rankClear la ra).warrs = [ra] := rfl
private theorem wvars_csrFill : (csrFill nmP nmC la ra).wvars
    = ["rs.c", "rs.i", "rs.s", "rs.j", "rs.e", "rs.w", "rs.x", "rs.c", "rs.j",
      "rs.i"] := rfl
private theorem warrs_csrFill : (csrFill nmP nmC la ra).warrs
    = [nmC.off, nmC.tgt, nmC.off] := rfl
private theorem wvars_colCopy : (colCopy nmP nmC la).wvars
    = ["rs.i", "rs.s", "rs.q", "rs.q", "rs.i"] := rfl
private theorem warrs_colCopy : (colCopy nmP nmC la).warrs = [nmC.col] := rfl
private theorem wvars_upCopy : (upCopy nmP nmC la).wvars
    = ["rs.i", "rs.s", "rs.i"] := rfl
private theorem warrs_upCopy : (upCopy nmP nmC la).warrs = [nmC.up] := rfl
private theorem wvars_histFilter : (histFilter nmP nmC la ra).wvars
    = ["rs.i", "rs.s", "rs.q", "rs.a", "rs.b", "rs.e", "rs.t", "rs.d", "rs.w",
      "rs.x", "rs.t", "rs.d", "rs.q", "rs.i"] := rfl
private theorem warrs_histFilter : (histFilter nmP nmC la ra).warrs
    = [nmC.hist, nmC.hist] := rfl
private theorem wvars_sizeCells : (sizeCells nmC).wvars = [nmC.nN, nmC.nS] := rfl
private theorem warrs_sizeCells : (sizeCells nmC).warrs = ([] : List String) := rfl

/-- Every scalar the routine writes is scratch or one of the child's
two cells. -/
theorem wvars_restrictCom_subset :
    ∀ y ∈ (restrictCom nmP nmC la ra).wvars,
      y ∈ rsScalars ∨ y = nmC.nN ∨ y = nmC.nS := by
  intro y hy
  have h : (restrictCom nmP nmC la ra).wvars
      = ["rs.i", "rs.s", "rs.i"] ++ (["rs.c", "rs.i", "rs.s", "rs.j", "rs.e",
        "rs.w", "rs.x", "rs.c", "rs.j", "rs.i"] ++ (["rs.i", "rs.s", "rs.q",
        "rs.q", "rs.i"] ++ (["rs.i", "rs.s", "rs.i"] ++ (["rs.i", "rs.s",
        "rs.q", "rs.a", "rs.b", "rs.e", "rs.t", "rs.d", "rs.w", "rs.x",
        "rs.t", "rs.d", "rs.q", "rs.i"] ++ (["rs.i", "rs.s", "rs.i"]
        ++ [nmC.nN, nmC.nS]))))) := rfl
  rw [h] at hy
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with hy | hy | hy | hy | hy | hy | hy <;>
    first
      | (left; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          | rfl | rfl | rfl | rfl | rfl <;> decide)
      | (rcases hy with rfl | rfl
         · right; left; rfl
         · right; right; rfl)

/-- Every array the routine stores into is the scratch or a child
region. -/
theorem warrs_restrictCom :
    (restrictCom nmP nmC la ra).warrs
      = [ra, nmC.off, nmC.tgt, nmC.off, nmC.col, nmC.up, nmC.hist, nmC.hist,
        ra] := rfl

/-- The routine never writes the output tape. -/
theorem noWrite_restrictCom : (restrictCom nmP nmC la ra).NoWrite := by
  simp [restrictCom, rankMark, rankClear, csrFill, csrFillBody, csrSlot,
    colCopy, colCopyBody, upCopy, histFilter, histBody, histRound, histSlot,
    sizeCells, Csr.loadRow, Csr.scan, Csr.slot, Com.NoWrite]

/-- The routine never reads the input tape. -/
theorem not_reads_restrictCom : ¬ (restrictCom nmP nmC la ra).reads := by
  simp [restrictCom, rankMark, rankClear, csrFill, csrFillBody, csrSlot,
    colCopy, colCopyBody, upCopy, histFilter, histBody, histRound, histSlot,
    sizeCells, Csr.loadRow, Csr.scan, Csr.slot, Com.reads]

end FrameData

/-! ## §13 The budget -/

/-- **The routine's budget**, its terms mirroring `Impl.childCharge` by
name: `27·dS` for the row scans with `dS := Σ_{s∈S} deg_A(s)` — the
**parent** degrees, never `‖A[S]‖` — then `|S|` times the per-member
work of the mark, the color-row copy (`Λ`), the renaming, the channel
filter (`ℓp·O(hb)`) and the clear, and a constant tail. **No `A.N`
term**: the carrier-sized wipe that would make a node `Θ(A.N²)` is
visibly absent. -/
def restrictK (dS k Λc ℓp hb : ℕ) : ℕ :=
  27 * dS + k * (20 * Λc + (36 * hb + 42) * ℓp + 132) + 45

/-- The budget against the abstract per-child account, at the channel
bound `hb := 2R+1` (§4's stored-list bound): one schedule constant. -/
theorem restrictK_le_childCharge {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (Lc ℓp R : ℕ) (S : Set (Fin n)) :
    restrictK (Impl.degSum G S) S.ncard Lc ℓp (2 * R + 1)
      ≤ 132 * (Impl.childCharge G Lc ℓp R S + 1) := by
  rw [restrictK, Impl.childCharge]
  have h1 : 36 * (2 * R + 1) + 42 ≤ 132 * (2 * R + 1) := by omega
  have h2 : (36 * (2 * R + 1) + 42) * ℓp ≤ 132 * (ℓp * (2 * R + 1)) := by
    calc (36 * (2 * R + 1) + 42) * ℓp ≤ (132 * (2 * R + 1)) * ℓp :=
          Nat.mul_le_mul_right ℓp h1
      _ = 132 * (ℓp * (2 * R + 1)) := by ring
  have h3 : S.ncard * (20 * Lc + (36 * (2 * R + 1) + 42) * ℓp + 132)
      ≤ S.ncard * (132 * Lc + 132 * (ℓp * (2 * R + 1)) + 132) :=
    Nat.mul_le_mul_left _ (by omega)
  have h4 : S.ncard * (132 * Lc + 132 * (ℓp * (2 * R + 1)) + 132)
      = 132 * (S.ncard * (Lc + ℓp * (2 * R + 1))) + 132 * S.ncard := by ring
  have h5 : 132 * (Impl.degSum G S + S.ncard * (Lc + ℓp * (2 * R + 1))
        + 2 * S.ncard + 1)
      = 132 * Impl.degSum G S + 132 * (S.ncard * (Lc + ℓp * (2 * R + 1)))
        + 264 * S.ncard + 132 := by ring
  omega

/-! ## §14 `restrictCom`, discharged -/

section RestrictSpec

variable {B n₀ Λc ℓp : ℕ}

set_option maxHeartbeats 1600000 in
open Classical in
/-- **`restrict`, discharged end to end** (F6c2's head deliverable):
from the parent frame state `ArenaSt nmP hb A`, the cluster's
enumeration region and size cell, the schedule cells, five child
regions of the child's exact sizes, and the ONE rank scratch **clean**,
`restrictCom` leaves the machine child that **IS** the abstract
`MArena.restrict A S` — `ArenaSt nmC hb (A.restrict S)` — with the
child's slot count in its cell, the parent state intact, and **the
scratch clean again** (the self-cleaning seam rule: exactly the `|S|`
touched entries were wiped). Budget `restrictK`, whose terms mirror
`Impl.childCharge` by name. -/
theorem restrictCom_spec {hb : ℕ} {A : Impl.MArena Λc n₀ ℓp}
    {S : Set (Fin A.N)} {nmP nmC : ArenaNames} {la ra : String} {ns : ℕ}
    (hNB : A.N < B) (hnsB : ns < B) (hn0B : n₀ < B)
    (hLB : A.N * Λc < B) (hHB : A.N * ℓp * (hb + 1) < B)
    -- the child regions, the scratch and the list are mutually distinct
    -- and touch neither the parent regions nor the list
    (hdisj : ∀ x ∈ [nmC.off, nmC.tgt, nmC.col, nmC.up, nmC.hist, ra],
      ∀ y ∈ [nmP.off, nmP.tgt, nmP.col, nmP.up, nmP.hist, la], x ≠ y)
    (hpair : ([nmC.off, nmC.tgt, nmC.col, nmC.up, nmC.hist, ra]).Pairwise (· ≠ ·))
    -- the child's two cells are neither scratch nor the parent's cells
    (hCn : nmC.nN ∉ rsScalars) (hCs : nmC.nS ∉ rsScalars)
    (hCns : nmC.nN ≠ nmC.nS)
    (hPn : nmP.nN ∉ rsScalars) (hPs : nmP.nS ∉ rsScalars)
    (hPn1 : nmP.nN ≠ nmC.nN) (hPn2 : nmP.nN ≠ nmC.nS)
    (hPs1 : nmP.nS ≠ nmC.nN) (hPs2 : nmP.nS ≠ nmC.nS) :
    Spec B
      (fun σ => ArenaSt nmP hb A σ ∧ σ.vars nmP.nS = ns ∧
        ClusterList la S σ ∧ σ.vars "rs.k" = S.ncard ∧
        σ.vars "rs.l" = Λc ∧ σ.vars "rs.p" = ℓp ∧ σ.vars "rs.h" = hb ∧
        σ.arrs ra = arrOf A.N (fun _ => 0) ∧
        (σ.arrs nmC.off).length = S.ncard + 1 ∧
        (σ.arrs nmC.tgt).length
          = ∑ v : Fin (A.restrict S).N, (A.restrict S).G.degree v ∧
        (σ.arrs nmC.col).length = S.ncard * Λc ∧
        (σ.arrs nmC.up).length = S.ncard ∧
        (σ.arrs nmC.hist).length = S.ncard * ℓp * (hb + 1))
      (restrictCom nmP nmC la ra)
      (fun _ σ' => ArenaSt nmC hb (A.restrict S) σ' ∧
        σ'.vars nmC.nS
          = ∑ v : Fin (A.restrict S).N, (A.restrict S).G.degree v ∧
        ArenaSt nmP hb A σ' ∧ σ'.vars nmP.nS = ns ∧
        ClusterList la S σ' ∧ σ'.vars "rs.k" = S.ncard ∧
        σ'.arrs ra = arrOf A.N (fun _ => 0))
      (restrictK (Impl.degSum A.G S) S.ncard Λc ℓp hb) := by
  classical
  intro σ₀ hσ₀
  obtain ⟨hA, hns, hcl, hk, hl, hp, hhb, hraz, hLoff, hLtgt, hLcol, hLup, hLhist⟩ := hσ₀
  obtain ⟨off, tgt, hc0, hoff0, hnd, hadj⟩ := hA.csr
  rw [hns] at hc0
  have hkn : S.ncard ≤ A.N := ncard_le_carrier S
  -- the pairwise distinctness, spelled out
  have hpo_pt : nmC.off ≠ nmC.tgt := List.rel_of_pairwise_cons hpair (by simp)
  have hpo_pc : nmC.off ≠ nmC.col := List.rel_of_pairwise_cons hpair (by simp)
  have hpo_pu : nmC.off ≠ nmC.up := List.rel_of_pairwise_cons hpair (by simp)
  have hpo_ph : nmC.off ≠ nmC.hist := List.rel_of_pairwise_cons hpair (by simp)
  have hpo_ra : nmC.off ≠ ra := List.rel_of_pairwise_cons hpair (by simp)
  have hpair₁ := List.Pairwise.of_cons hpair
  have hpt_pc : nmC.tgt ≠ nmC.col := List.rel_of_pairwise_cons hpair₁ (by simp)
  have hpt_pu : nmC.tgt ≠ nmC.up := List.rel_of_pairwise_cons hpair₁ (by simp)
  have hpt_ph : nmC.tgt ≠ nmC.hist := List.rel_of_pairwise_cons hpair₁ (by simp)
  have hpt_ra : nmC.tgt ≠ ra := List.rel_of_pairwise_cons hpair₁ (by simp)
  have hpair₂ := List.Pairwise.of_cons hpair₁
  have hpc_pu : nmC.col ≠ nmC.up := List.rel_of_pairwise_cons hpair₂ (by simp)
  have hpc_ph : nmC.col ≠ nmC.hist := List.rel_of_pairwise_cons hpair₂ (by simp)
  have hpc_ra : nmC.col ≠ ra := List.rel_of_pairwise_cons hpair₂ (by simp)
  have hpair₃ := List.Pairwise.of_cons hpair₂
  have hpu_ph : nmC.up ≠ nmC.hist := List.rel_of_pairwise_cons hpair₃ (by simp)
  have hpu_ra : nmC.up ≠ ra := List.rel_of_pairwise_cons hpair₃ (by simp)
  have hpair₄ := List.Pairwise.of_cons hpair₃
  have hph_ra : nmC.hist ≠ ra := List.rel_of_pairwise_cons hpair₄ (by simp)
  -- the child-versus-parent disequalities
  have hdo : ∀ y ∈ [nmP.off, nmP.tgt, nmP.col, nmP.up, nmP.hist, la],
      nmC.off ≠ y := fun y hy => hdisj _ (by simp) y hy
  have hdt : ∀ y ∈ [nmP.off, nmP.tgt, nmP.col, nmP.up, nmP.hist, la],
      nmC.tgt ≠ y := fun y hy => hdisj _ (by simp) y hy
  have hdc : ∀ y ∈ [nmP.off, nmP.tgt, nmP.col, nmP.up, nmP.hist, la],
      nmC.col ≠ y := fun y hy => hdisj _ (by simp) y hy
  have hdu : ∀ y ∈ [nmP.off, nmP.tgt, nmP.col, nmP.up, nmP.hist, la],
      nmC.up ≠ y := fun y hy => hdisj _ (by simp) y hy
  have hdh : ∀ y ∈ [nmP.off, nmP.tgt, nmP.col, nmP.up, nmP.hist, la],
      nmC.hist ≠ y := fun y hy => hdisj _ (by simp) y hy
  have hdra : ∀ y ∈ [nmP.off, nmP.tgt, nmP.col, nmP.up, nmP.hist, la],
      ra ≠ y := fun y hy => hdisj _ (by simp) y hy
  have hCn' : ∀ y ∈ rsScalars, nmC.nN ≠ y := fun y hy h => hCn (h ▸ hy)
  have hCs' : ∀ y ∈ rsScalars, nmC.nS ≠ y := fun y hy h => hCs (h ▸ hy)
  have hPn' : ∀ y ∈ rsScalars, nmP.nN ≠ y := fun y hy h => hPn (h ▸ hy)
  have hPs' : ∀ y ∈ rsScalars, nmP.nS ≠ y := fun y hy h => hPs (h ▸ hy)
  -- the child CSR's dimensions
  have hrowlen : ∀ v : Fin S.ncard, (crowL S off tgt (v : ℕ)).length
      = (A.restrict S).G.degree v := by
    intro v
    refine length_eq_degree v (crowL_nodup S off tgt hnd v.2) ?_
    intro w
    rw [mem_crowL_iff S off tgt hadj v.2 w]
    constructor
    · rintro ⟨hw, hAdj⟩
      exact ⟨hw, hAdj⟩
    · rintro ⟨hw, hAdj⟩
      exact ⟨hw, hAdj⟩
  have hcns_deg : cns S off tgt
      = ∑ v : Fin (A.restrict S).N, (A.restrict S).G.degree v := by
    rw [cns, coff_eq_offList S off tgt le_rfl, offList_eq_sum,
      ← Fin.sum_univ_eq_sum_range (fun t => (crowL S off tgt t).length) S.ncard]
    exact Finset.sum_congr rfl fun v _ => hrowlen v
  have hcns_ns : cns S off tgt ≤ ns := cns_le_ns S off tgt hc0
  -- ── P1: the mark
  obtain ⟨σ₁, run1, hpost1⟩ :=
    ((rankMark_spec (S := S) hNB (Ne.symm (hdra la (by simp)))).frame).run
      ⟨hcl, hk, hraz⟩
  obtain ⟨⟨hcl₁, hk₁, hra₁⟩, hfv₁, hfa₁, -, -⟩ := hpost1
  have hv₁ : ∀ y, y ≠ "rs.i" → y ≠ "rs.s" → σ₁.vars y = σ₀.vars y := by
    intro y h1 h2
    refine hfv₁ y ?_
    rw [wvars_rankMark]
    simp [h1, h2]
  have ha₁ : ∀ b, b ≠ ra → σ₁.arrs b = σ₀.arrs b := by
    intro b hb
    refine hfa₁ b ?_
    rw [warrs_rankMark]
    simp [hb]
  -- ── P2: the CSR fill
  have hc₁ : Csr nmP.off nmP.tgt A.N ns A.N off tgt σ₁ :=
    hc0.of_eq (ha₁ _ (Ne.symm (hdra _ (by simp)))) (ha₁ _ (Ne.symm (hdra _ (by simp))))
  obtain ⟨σ₂, run2, hpost2⟩ :=
    ((csrFill_spec (S := S) hNB hnsB (hdt _ (by simp)) hpt_ra hpo_pt.symm
      (hdt _ (by simp)) (hdt _ (by simp)) (hdo _ (by simp)) (hdo _ (by simp))
      (hdo _ (by simp)) hpo_ra).frame).run
      ⟨hc₁, hcl₁, hk₁, hra₁,
        by rw [ha₁ _ hpo_ra]; exact hLoff,
        by rw [ha₁ _ hpt_ra, hLtgt, hcns_deg]⟩
  obtain ⟨⟨hc₂, hcl₂, hk₂, hra₂, hoff₂, htgt₂, hcv₂⟩, hfv₂, hfa₂, -, -⟩ := hpost2
  have hv₂ : ∀ y, y ∉ (["rs.c", "rs.i", "rs.s", "rs.j", "rs.e", "rs.w", "rs.x"] :
      List String) → σ₂.vars y = σ₁.vars y := by
    intro y hy
    refine hfv₂ y ?_
    rw [wvars_csrFill]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    push Not at hy ⊢
    exact ⟨hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2.1,
      hy.2.2.2.2.2.2, hy.1, hy.2.2.2.1, hy.2.1⟩
  have ha₂ : ∀ b, b ≠ nmC.off → b ≠ nmC.tgt → σ₂.arrs b = σ₁.arrs b := by
    intro b h1 h2
    refine hfa₂ b ?_
    rw [warrs_csrFill]
    simp [h1, h2]
  -- ── P3: the color copy
  have hcol₂ : ColBits nmP.col A.col σ₂ := by
    have h := hA.col
    rw [ColBits] at h ⊢
    rw [ha₂ _ (Ne.symm (hdo _ (by simp))) (Ne.symm (hdt _ (by simp))),
      ha₁ _ (Ne.symm (hdra _ (by simp)))]
    exact h
  obtain ⟨σ₃, run3, hpost3⟩ :=
    ((colCopy_spec (S := S) hNB hLB (hdc _ (by simp)) (hdc _ (by simp))).frame).run
      ⟨hcol₂, hcl₂, hk₂,
        by rw [hv₂ _ (by decide), hv₁ _ (by decide) (by decide)]; exact hl,
        by rw [ha₂ _ hpo_pc.symm hpt_pc.symm, ha₁ _ hpc_ra]; exact hLcol⟩
  obtain ⟨⟨hcol₃, hcl₃, hk₃, -, hccol₃⟩, hfv₃, hfa₃, -, -⟩ := hpost3
  have hv₃ : ∀ y, y ∉ (["rs.i", "rs.s", "rs.q"] : List String) →
      σ₃.vars y = σ₂.vars y := by
    intro y hy
    refine hfv₃ y ?_
    rw [wvars_colCopy]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    push Not at hy ⊢
    exact ⟨hy.1, hy.2.1, hy.2.2, hy.2.2, hy.1⟩
  have ha₃ : ∀ b, b ≠ nmC.col → σ₃.arrs b = σ₂.arrs b := by
    intro b hb
    refine hfa₃ b ?_
    rw [warrs_colCopy]
    simp [hb]
  -- ── P4: the renaming
  have hup₃ : UpArr nmP.up A.up σ₃ := by
    have h := hA.up
    rw [UpArr] at h ⊢
    rw [ha₃ _ (Ne.symm (hdc _ (by simp))),
      ha₂ _ (Ne.symm (hdo _ (by simp))) (Ne.symm (hdt _ (by simp))),
      ha₁ _ (Ne.symm (hdra _ (by simp)))]
    exact h
  obtain ⟨σ₄, run4, hpost4⟩ :=
    ((upCopy_spec (S := S) hNB hn0B (hdu _ (by simp)) (hdu _ (by simp))).frame).run
      ⟨hup₃, hcl₃, hk₃,
        by rw [ha₃ _ hpc_pu.symm, ha₂ _ hpo_pu.symm hpt_pu.symm, ha₁ _ hpu_ra]
           exact hLup⟩
  obtain ⟨⟨hup₄, hcl₄, hk₄, hcup₄⟩, hfv₄, hfa₄, -, -⟩ := hpost4
  have hv₄ : ∀ y, y ∉ (["rs.i", "rs.s"] : List String) →
      σ₄.vars y = σ₃.vars y := by
    intro y hy
    refine hfv₄ y ?_
    rw [wvars_upCopy]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    push Not at hy ⊢
    exact ⟨hy.1, hy.2, hy.1⟩
  have ha₄ : ∀ b, b ≠ nmC.up → σ₄.arrs b = σ₃.arrs b := by
    intro b hb
    refine hfa₄ b ?_
    rw [warrs_upCopy]
    simp [hb]
  -- ── P5: the channel filter
  have hhist₄ : HistArr nmP.hist ℓp hb A.hist σ₄ := by
    have h := hA.hist
    rw [HistArr] at h ⊢
    rw [ha₄ _ (Ne.symm (hdu _ (by simp))), ha₃ _ (Ne.symm (hdc _ (by simp))),
      ha₂ _ (Ne.symm (hdo _ (by simp))) (Ne.symm (hdt _ (by simp))),
      ha₁ _ (Ne.symm (hdra _ (by simp)))]
    exact h
  have hra₄ : σ₄.arrs ra = arrOf A.N (rk S) := by
    rw [ha₄ _ hpu_ra.symm, ha₃ _ hpc_ra.symm]
    exact hra₂
  obtain ⟨σ₅, run5, hpost5⟩ :=
    ((histFilter_spec (S := S) hNB hHB (hdh _ (by simp)) hph_ra
      (hdh _ (by simp))).frame).run
      ⟨hhist₄, hcl₄, hk₄,
        by rw [hv₄ _ (by decide), hv₃ _ (by decide), hv₂ _ (by decide),
          hv₁ _ (by decide) (by decide)]; exact hp,
        by rw [hv₄ _ (by decide), hv₃ _ (by decide), hv₂ _ (by decide),
          hv₁ _ (by decide) (by decide)]; exact hhb,
        hra₄,
        by rw [ha₄ _ hpu_ph.symm, ha₃ _ hpc_ph.symm, ha₂ _ hpo_ph.symm hpt_ph.symm,
          ha₁ _ hph_ra]; exact hLhist⟩
  obtain ⟨⟨hhist₅, hcl₅, hk₅, hra₅, hchist₅⟩, hfv₅, hfa₅, -, -⟩ := hpost5
  have hv₅ : ∀ y, y ∉ (["rs.i", "rs.s", "rs.q", "rs.a", "rs.b", "rs.e", "rs.t",
      "rs.d", "rs.w", "rs.x"] : List String) → σ₅.vars y = σ₄.vars y := by
    intro y hy
    refine hfv₅ y ?_
    rw [wvars_histFilter]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
    push Not at hy ⊢
    exact ⟨hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2.1,
      hy.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.2.1,
      hy.2.2.2.2.2.2.2.2.2, hy.2.2.2.2.2.2.1, hy.2.2.2.2.2.2.2.1, hy.2.2.1,
      hy.1⟩
  have ha₅ : ∀ b, b ≠ nmC.hist → σ₅.arrs b = σ₄.arrs b := by
    intro b hb
    refine hfa₅ b ?_
    rw [warrs_histFilter]
    simp [hb]
  -- ── P6: the clear
  obtain ⟨σ₆, run6, hpost6⟩ :=
    ((rankClear_spec (S := S) hNB (Ne.symm (hdra la (by simp)))).frame).run
      ⟨hcl₅, hk₅, hra₅⟩
  obtain ⟨⟨hcl₆, hk₆, hra₆⟩, hfv₆, hfa₆, -, -⟩ := hpost6
  have hv₆ : ∀ y, y ≠ "rs.i" → y ≠ "rs.s" → σ₆.vars y = σ₅.vars y := by
    intro y h1 h2
    refine hfv₆ y ?_
    rw [wvars_rankClear]
    simp [h1, h2]
  have ha₆ : ∀ b, b ≠ ra → σ₆.arrs b = σ₅.arrs b := by
    intro b hb
    refine hfa₆ b ?_
    rw [warrs_rankClear]
    simp [hb]
  -- ── P7: the child's two cells
  have hcv₆ : σ₆.vars "rs.c" = cns S off tgt := by
    rw [hv₆ _ (by decide) (by decide), hv₅ _ (by decide), hv₄ _ (by decide),
      hv₃ _ (by decide)]
    exact hcv₂
  have hr7a : Run B (.assign nmC.nN (.var "rs.k")) σ₆
      (σ₆.setVar nmC.nN S.ncard) 2 := by
    have hev : (Expr.var "rs.k").evalB B σ₆ = some S.ncard := by
      rw [← hk₆]
      exact evalB_var (by rw [hk₆]; omega)
    exact (Run.assign hev).mono (by simp)
  set σ₇a := σ₆.setVar nmC.nN S.ncard with hσ₇a
  have hr7b : Run B (.assign nmC.nS (.var "rs.c")) σ₇a
      (σ₇a.setVar nmC.nS (cns S off tgt)) 2 := by
    have h7c : σ₇a.vars "rs.c" = cns S off tgt := by
      rw [hσ₇a, vars_setVar, if_neg (Ne.symm (hCn' "rs.c" (by decide)))]
      exact hcv₆
    have hev : (Expr.var "rs.c").evalB B σ₇a = some (cns S off tgt) := by
      rw [← h7c]
      exact evalB_var (by rw [h7c]; omega)
    exact (Run.assign hev).mono (by simp)
  set σ₇ := σ₇a.setVar nmC.nS (cns S off tgt) with hσ₇
  have run7 : Run B (sizeCells nmC) σ₆ σ₇ 4 := (hr7a.seq hr7b).mono (by omega)
  have hv₇ : ∀ y, y ≠ nmC.nN → y ≠ nmC.nS → σ₇.vars y = σ₆.vars y := by
    intro y h1 h2
    rw [hσ₇, hσ₇a]
    simp [h1, h2]
  have ha₇ : ∀ b, σ₇.arrs b = σ₆.arrs b := by
    intro b
    rw [hσ₇, hσ₇a]
    simp
  -- the whole-run transports back to the initial state
  have hvars_scr : ∀ y, y ∈ rsScalars → y ≠ "rs.k" →
      True := fun _ _ _ => trivial
  have hArrsP : ∀ b, b ∈ [nmP.off, nmP.tgt, nmP.col, nmP.up, nmP.hist] →
      σ₇.arrs b = σ₀.arrs b := by
    intro b hb
    have hb6 : b ∈ [nmP.off, nmP.tgt, nmP.col, nmP.up, nmP.hist, la] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hb ⊢
      tauto
    rw [ha₇, ha₆ _ (Ne.symm (hdra _ hb6)), ha₅ _ (Ne.symm (hdh _ hb6)),
      ha₄ _ (Ne.symm (hdu _ hb6)), ha₃ _ (Ne.symm (hdc _ hb6)),
      ha₂ _ (Ne.symm (hdo _ hb6)) (Ne.symm (hdt _ hb6)),
      ha₁ _ (Ne.symm (hdra _ hb6))]
  have hVarsP : ∀ y, y ∉ rsScalars → y ≠ nmC.nN → y ≠ nmC.nS →
      σ₇.vars y = σ₀.vars y := by
    intro y hy h1 h2
    have hne : ∀ z ∈ rsScalars, y ≠ z := fun z hz h => hy (h ▸ hz)
    rw [hv₇ _ h1 h2,
      hv₆ _ (hne _ (by decide)) (hne _ (by decide)),
      hv₅ _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        push Not
        exact ⟨hne _ (by decide), hne _ (by decide), hne _ (by decide),
          hne _ (by decide), hne _ (by decide), hne _ (by decide),
          hne _ (by decide), hne _ (by decide), hne _ (by decide),
          hne _ (by decide)⟩),
      hv₄ _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        push Not
        exact ⟨hne _ (by decide), hne _ (by decide)⟩),
      hv₃ _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        push Not
        exact ⟨hne _ (by decide), hne _ (by decide), hne _ (by decide)⟩),
      hv₂ _ (by
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        push Not
        exact ⟨hne _ (by decide), hne _ (by decide), hne _ (by decide),
          hne _ (by decide), hne _ (by decide), hne _ (by decide),
          hne _ (by decide)⟩),
      hv₁ _ (hne _ (by decide)) (hne _ (by decide))]
  -- the child regions, carried to the end
  have hoff₇ : σ₇.arrs nmC.off = arrOf (S.ncard + 1) (coff S off tgt) := by
    rw [ha₇, ha₆ _ hpo_ra, ha₅ _ hpo_ph, ha₄ _ hpo_pu, ha₃ _ hpo_pc]
    exact hoff₂
  have htgt₇ : σ₇.arrs nmC.tgt = arrOf (cns S off tgt) (ctgt S off tgt) := by
    rw [ha₇, ha₆ _ hpt_ra, ha₅ _ hpt_ph, ha₄ _ hpt_pu, ha₃ _ hpt_pc]
    exact htgt₂
  have hcol₇ : σ₇.arrs nmC.col = σ₃.arrs nmC.col := by
    rw [ha₇, ha₆ _ hpc_ra, ha₅ _ hpc_ph, ha₄ _ hpc_pu]
  have hup₇ : σ₇.arrs nmC.up = σ₄.arrs nmC.up := by
    rw [ha₇, ha₆ _ hpu_ra, ha₅ _ hpu_ph]
  have hhist₇ : σ₇.arrs nmC.hist = σ₅.arrs nmC.hist := by
    rw [ha₇, ha₆ _ hph_ra]
  have hnN₇ : σ₇.vars nmC.nN = S.ncard := by
    rw [hσ₇, vars_setVar, if_neg hCns, hσ₇a]
    simp
  have hnS₇ : σ₇.vars nmC.nS = cns S off tgt := by
    rw [hσ₇]
    simp
  refine ⟨σ₇, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the run at the announced budget
    have h := run1.seq (run2.seq (run3.seq (run4.seq (run5.seq (run6.seq run7)))))
    refine h.mono ?_
    have hdSum : ∑ t ∈ Finset.range S.ncard, Csr.rowLen off (embN S t)
        = Impl.degSum A.G S := sum_rowLen_emb_eq_degSum S off tgt hnd hadj
    have hsplit : S.ncard * (20 * Λc + (36 * hb + 42) * ℓp + 132)
        = (20 * Λc + 17) * S.ncard + ((36 * hb + 42) * ℓp + 17) * S.ncard
          + 16 * S.ncard + 52 * S.ncard + 16 * S.ncard + 14 * S.ncard := by ring
    rw [restrictK]
    omega
  · -- the child arena state
    refine ⟨hnN₇, ⟨coff S off tgt, ctgt S off tgt, ?_, coff_zero S off tgt, ?_, ?_⟩,
      ?_, ?_, ?_⟩
    · -- the CSR relation
      rw [hnS₇]
      refine ⟨hoff₇, htgt₇, ?_, ?_, ?_⟩
      · intro i hi
        exact coff_mono S off tgt (by omega)
      · rfl
      · intro pp hpp
        exact ctgt_lt S off tgt hpp
    · -- the rows are duplicate-free
      intro v
      rw [row_coff_ctgt S off tgt v.2]
      exact crowL_nodup S off tgt hnd v.2
    · -- the rows are the child adjacency
      intro v w
      rw [row_coff_ctgt S off tgt v.2, mem_crowL_iff S off tgt hadj v.2 w]
      constructor
      · rintro ⟨hw, hAdj⟩
        exact ⟨hw, hAdj⟩
      · rintro ⟨hw, hAdj⟩
        exact ⟨hw, hAdj⟩
    · -- the color rows
      have h := hccol₃
      rw [ColBits] at h ⊢
      rw [hcol₇]
      exact h
    · -- the renaming
      have h := hcup₄
      rw [UpArr] at h ⊢
      rw [hup₇]
      exact h
    · -- the channel
      have h := hchist₅
      rw [HistArr] at h ⊢
      rw [hhist₇]
      exact h
  · rw [hnS₇, hcns_deg]
  · -- the parent arena state survives
    refine ⟨?_, ⟨off, tgt, ?_, hoff0, hnd, hadj⟩, ?_, ?_, ?_⟩
    · rw [hVarsP _ hPn hPn1 hPn2]
      exact hA.n_eq
    · have hnsv : σ₇.vars nmP.nS = ns := by
        rw [hVarsP _ hPs hPs1 hPs2]
        exact hns
      rw [hnsv]
      exact hc0.of_eq (hArrsP _ (by simp)) (hArrsP _ (by simp))
    · have h := hA.col
      rw [ColBits] at h ⊢
      rw [hArrsP _ (by simp)]
      exact h
    · have h := hA.up
      rw [UpArr] at h ⊢
      rw [hArrsP _ (by simp)]
      exact h
    · have h := hA.hist
      rw [HistArr] at h ⊢
      rw [hArrsP _ (by simp)]
      exact h
  · rw [hVarsP _ hPs hPs1 hPs2]
    exact hns
  · -- the cluster region survives
    refine ⟨?_, ?_⟩ <;> rw [ha₇]
    · exact hcl₆.1
    · exact hcl₆.2
  · rw [hv₇ _ (Ne.symm (hCn' _ (by decide))) (Ne.symm (hCs' _ (by decide))),
      hv₆ _ (by decide) (by decide)]
    exact hk₅
  · -- the scratch is clean again
    rw [ha₇]
    exact hra₆

end RestrictSpec

end Phases

/-! ## §15 `isolate` — drop the edges incident to the batch

One CSR sweep: every row is rebuilt into the output pair, skipping the
batch's rows outright and the batch-incident targets inside kept rows —
`deleteVerts` at the machine, priced `O(‖B‖)`. -/

section Isolate

variable {B n ns : ℕ}

open Classical in
/-- The batch bit at plain numbers (out of range reads as batched —
never consulted there). -/
private noncomputable def bbit (W : Set (Fin n)) (w : ℕ) : ℕ :=
  if h : w < n then (if (⟨w, h⟩ : Fin n) ∈ W then 1 else 0) else 1

private theorem finBits_getD {W : Set (Fin n)} {a : String} {σ : Env}
    (h : FinBits a W σ) {w : ℕ} (hw : w < n) :
    (σ.arrs a).getD w 0 = bbit W w := by
  have := h.2 ⟨w, hw⟩
  rw [bbit, dif_pos hw]
  simpa using this

private theorem bbit_le_one_of_lt {W : Set (Fin n)} {w : ℕ} (hw : w < n) :
    bbit W w ≤ 1 := by
  rw [bbit, dif_pos hw]
  split <;> omega

private theorem bbit_eq_zero_iff {W : Set (Fin n)} {w : ℕ} (hw : w < n) :
    bbit W w = 0 ↔ (⟨w, hw⟩ : Fin n) ∉ W := by
  rw [bbit, dif_pos hw]
  split <;> rename_i h
  · simp [h]
  · simp [h]

/-- The per-target filter: keep unbatched targets, unrenamed. -/
private noncomputable def ibit (W : Set (Fin n)) (w : ℕ) : Option ℕ :=
  if bbit W w = 0 then some w else none

private theorem ibit_inj (W : Set (Fin n)) {a b c : ℕ}
    (ha : ibit W a = some c) (hb : ibit W b = some c) : a = b := by
  rw [ibit] at ha hb
  split at ha
  · split at hb
    · obtain rfl := Option.some_injective _ ha
      obtain rfl := Option.some_injective _ hb
      rfl
    · simp at hb
  · simp at ha

/-- Row `v` of the isolated CSR: empty for a batched vertex, otherwise
the input row with batched targets dropped. -/
private noncomputable def irowL (W : Set (Fin n)) (off tgt : ℕ → ℕ) (v : ℕ) :
    List ℕ :=
  if bbit W v = 0 then (Csr.row off tgt v).filterMap (ibit W) else []

/-- The isolated offsets. -/
private noncomputable def ioff (W : Set (Fin n)) (off tgt : ℕ → ℕ) (a : ℕ) : ℕ :=
  offList (irowL W off tgt) (min a n)

/-- The isolated target zone. -/
private noncomputable def icallL (W : Set (Fin n)) (off tgt : ℕ → ℕ) : List ℕ :=
  (List.range n).flatMap (irowL W off tgt)

private noncomputable def itgt (W : Set (Fin n)) (off tgt : ℕ → ℕ) (p : ℕ) : ℕ :=
  (icallL W off tgt).getD p 0

/-- The isolated slot count. -/
private noncomputable def ins (W : Set (Fin n)) (off tgt : ℕ → ℕ) : ℕ :=
  ioff W off tgt n

variable (W : Set (Fin n)) (off tgt : ℕ → ℕ)

@[simp] private theorem ioff_zero : ioff W off tgt 0 = 0 := by simp [ioff]

private theorem ioff_succ {t : ℕ} (ht : t < n) :
    ioff W off tgt (t + 1) = ioff W off tgt t + (irowL W off tgt t).length := by
  rw [ioff, ioff, min_eq_left (by omega), min_eq_left (by omega), offList_succ]

private theorem ioff_eq_offList {a : ℕ} (ha : a ≤ n) :
    ioff W off tgt a = offList (irowL W off tgt) a := by
  rw [ioff, min_eq_left ha]

private theorem ioff_mono {a b : ℕ} (h : a ≤ b) :
    ioff W off tgt a ≤ ioff W off tgt b :=
  offList_mono _ (by omega)

private theorem ioff_le_ins (a : ℕ) : ioff W off tgt a ≤ ins W off tgt := by
  rw [ins, ioff_eq_offList W off tgt le_rfl, ioff]
  exact offList_mono _ (min_le_right a _)

private theorem icallL_length : (icallL W off tgt).length = ins W off tgt := by
  rw [icallL, length_flatMap_range, ins, ioff_eq_offList W off tgt le_rfl]

private theorem itgt_slice {t m : ℕ} (ht : t < n)
    (hm : m < (irowL W off tgt t).length) :
    itgt W off tgt (ioff W off tgt t + m) = (irowL W off tgt t).getD m 0 := by
  rw [itgt, icallL, ioff_eq_offList W off tgt (by omega)]
  exact getD_flatMap_range _ ht hm

private theorem row_ioff_itgt {t : ℕ} (ht : t < n) :
    Csr.row (ioff W off tgt) (itgt W off tgt) t = irowL W off tgt t := by
  have hlen : Csr.rowLen (ioff W off tgt) t = (irowL W off tgt t).length := by
    rw [Csr.rowLen, ioff_succ W off tgt ht]
    omega
  rw [Csr.row, hlen]
  calc arrOf (irowL W off tgt t).length
        (fun m => itgt W off tgt (ioff W off tgt t + m))
      = arrOf (irowL W off tgt t).length (fun m => (irowL W off tgt t).getD m 0) :=
        arrOf_congr fun m hm => itgt_slice W off tgt ht hm
    _ = irowL W off tgt t := arrOf_getD _

variable {G : SimpleGraph (Fin n)}

/-- **The rebuilt row is `deleteVerts`' adjacency.** -/
private theorem mem_irowL_iff
    (hadj : ∀ (v : Fin n) (w : ℕ), w ∈ Csr.row off tgt v ↔ ∃ hw : w < n, G.Adj v ⟨w, hw⟩)
    {t : ℕ} (ht : t < n) (w : ℕ) :
    w ∈ irowL W off tgt t ↔
      ∃ hw : w < n, (deleteVerts G W).Adj ⟨t, ht⟩ ⟨w, hw⟩ := by
  rw [irowL]
  constructor
  · intro hmem
    split at hmem
    · rename_i hbv
      obtain ⟨w', hwrow, hopt⟩ := List.mem_filterMap.mp hmem
      rw [ibit] at hopt
      split at hopt
      · rename_i hbw
        have heq : w' = w := Option.some_injective _ hopt
        rw [heq] at hwrow hbw
        obtain ⟨hw, hAdj⟩ := (hadj ⟨t, ht⟩ w).mp hwrow
        refine ⟨hw, hAdj, ?_, ?_⟩
        · exact (bbit_eq_zero_iff ht).mp hbv
        · exact (bbit_eq_zero_iff hw).mp hbw
      · simp at hopt
    · simp at hmem
  · rintro ⟨hw, hAdj, htW, hwW⟩
    rw [if_pos ((bbit_eq_zero_iff ht).mpr htW)]
    refine List.mem_filterMap.mpr ⟨w, ?_, ?_⟩
    · exact (hadj ⟨t, ht⟩ w).mpr ⟨hw, hAdj⟩
    · rw [ibit, if_pos ((bbit_eq_zero_iff hw).mpr hwW)]

private theorem irowL_nodup (hnd : ∀ v : Fin n, (Csr.row off tgt v).Nodup)
    {t : ℕ} (ht : t < n) : (irowL W off tgt t).Nodup := by
  rw [irowL]
  split
  · refine List.Nodup.filterMap
      (fun a a' b hb hb' => ibit_inj W (Option.mem_def.mp hb) (Option.mem_def.mp hb')) ?_
    have := hnd ⟨t, ht⟩
    simpa using this
  · exact List.nodup_nil

private theorem irowL_lt {t w : ℕ} (h : w ∈ irowL W off tgt t) : w < n := by
  rw [irowL] at h
  split at h
  · obtain ⟨w', -, hopt⟩ := List.mem_filterMap.mp h
    rw [ibit] at hopt
    split at hopt
    · obtain rfl := Option.some_injective _ hopt
      rename_i hbw
      by_contra hn
      rw [bbit, dif_neg hn] at hbw
      omega
    · simp at hopt
  · simp at h

private theorem itgt_lt {p : ℕ} (hp : p < ins W off tgt) : itgt W off tgt p < n := by
  have hlen : p < (icallL W off tgt).length := by
    rw [icallL_length]
    exact hp
  have hmem : itgt W off tgt p ∈ icallL W off tgt := by
    rw [itgt, getD_eq_getElem hlen]
    exact List.getElem_mem hlen
  obtain ⟨u, hu, hx⟩ := mem_flatMap_range hmem
  exact irowL_lt W off tgt hx

/-- The isolated slot count never exceeds the input's. -/
private theorem ins_le_ns {o t' : String} {σ : Env}
    (hc : Csr o t' n ns n off tgt σ) : ins W off tgt ≤ ns := by
  have h1 : ins W off tgt = ∑ u ∈ Finset.range n, (irowL W off tgt u).length := by
    rw [ins, ioff_eq_offList W off tgt le_rfl, offList_eq_sum]
  have h2 : ∀ u ∈ Finset.range n, (irowL W off tgt u).length ≤ Csr.rowLen off u := by
    intro u _
    rw [irowL]
    split
    · calc ((Csr.row off tgt u).filterMap (ibit W)).length
          ≤ (Csr.row off tgt u).length := List.length_filterMap_le _ _
        _ = Csr.rowLen off u := Csr.length_row off tgt u
    · simp
  have h3 : ∑ u ∈ Finset.range n, Csr.rowLen off u = off n - off 0 :=
    Csr.sum_rowLen hc n le_rfl
  have h4 : off n = ns := hc.last
  calc ins W off tgt = ∑ u ∈ Finset.range n, (irowL W off tgt u).length := h1
    _ ≤ ∑ u ∈ Finset.range n, Csr.rowLen off u := Finset.sum_le_sum h2
    _ = off n - off 0 := h3
    _ ≤ ns := by omega

end Isolate

/-! ### §15a The program -/

/-- One slot of a kept row: read the target, read its batch bit, keep
it if unbatched. -/
def isoSlot (nmI : ArenaNames) (taO ba : String) : Com :=
  .seq (Csr.slot nmI.tgt "rs.j" "rs.w")
    (.seq (.assign "rs.d" (.get ba (.var "rs.w")))
      (.seq (.ite (.lt (.var "rs.d") (.lit 1))
          (.seq (.store taO (.var "rs.c") (.var "rs.w"))
            (.assign "rs.c" (.add (.var "rs.c") (.lit 1))))
          .skip)
        (.assign "rs.j" (.add (.var "rs.j") (.lit 1)))))

/-- One row of the sweep: a batched vertex's row is skipped outright
(its output row is empty); a kept vertex's row is scanned and filtered;
either way the output boundary is sealed. -/
def isoBody (nmI : ArenaNames) (oaO taO ba : String) : Com :=
  .seq (.assign "rs.x" (.get ba (.var "rs.i")))
    (.seq (.ite (.lt (.var "rs.x") (.lit 1))
        (.seq (Csr.loadRow nmI.off "rs.i" "rs.j" "rs.e")
          (Csr.scan "rs.j" "rs.e" (isoSlot nmI taO ba)))
        .skip)
      (.seq (.store oaO (.add (.var "rs.i") (.lit 1)) (.var "rs.c"))
        (.assign "rs.i" (.add (.var "rs.i") (.lit 1)))))

/-- **`isolate`, as IMP+**: one sweep of the input CSR into the output
pair, then the new slot count into its cell. -/
def isolateCom (nmI : ArenaNames) (oaO taO nsO ba : String) : Com :=
  .seq (.assign "rs.c" (.lit 0))
    (.seq (.store oaO (.lit 0) (.lit 0))
      (.seq (.assign "rs.i" (.lit 0))
        (.seq (.while (.lt (.var "rs.i") (.var nmI.nN)) (isoBody nmI oaO taO ba))
          (.assign nsO (.var "rs.c")))))

/-- Every array the sweep stores into is an output region. -/
theorem warrs_isolateCom (nmI : ArenaNames) (oaO taO nsO ba : String) :
    (isolateCom nmI oaO taO nsO ba).warrs = [oaO, taO, oaO] := rfl

/-- Every scalar the sweep writes is scratch or the output cell. -/
theorem wvars_isolateCom_subset (nmI : ArenaNames) (oaO taO nsO ba : String) :
    ∀ y ∈ (isolateCom nmI oaO taO nsO ba).wvars, y ∈ rsScalars ∨ y = nsO := by
  intro y hy
  have h : (isolateCom nmI oaO taO nsO ba).wvars
      = ["rs.c", "rs.i", "rs.x", "rs.j", "rs.e", "rs.w", "rs.d", "rs.c",
        "rs.j", "rs.i", nsO] := rfl
  rw [h] at hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | (left; decide)
      | (right; rfl)

theorem noWrite_isolateCom (nmI : ArenaNames) (oaO taO nsO ba : String) :
    (isolateCom nmI oaO taO nsO ba).NoWrite := by
  simp [isolateCom, isoBody, isoSlot, Csr.loadRow, Csr.scan, Csr.slot, Com.NoWrite]

theorem not_reads_isolateCom (nmI : ArenaNames) (oaO taO nsO ba : String) :
    ¬ (isolateCom nmI oaO taO nsO ba).reads := by
  simp [isolateCom, isoBody, isoSlot, Csr.loadRow, Csr.scan, Csr.slot, Com.reads]

/-! ### §15a′ The sweep, discharged -/

/-- The mid-row state of the isolation sweep (the row is a kept one). -/
private structure IsoRowSt (nmI : ArenaNames) (oaO taO ba : String) (n ns : ℕ)
    (W : Set (Fin n)) (off tgt : ℕ → ℕ) (i : ℕ) (σ : Env) : Prop where
  hc : Csr nmI.off nmI.tgt n ns n off tgt σ
  hnN : σ.vars nmI.nN = n
  hbb : FinBits ba W σ
  hiv : σ.vars "rs.i" = i
  hbv0 : bbit W i = 0
  he : σ.vars "rs.e" = off (i + 1)
  hjlo : off i ≤ σ.vars "rs.j"
  hjhi : σ.vars "rs.j" ≤ off (i + 1)
  hcv : σ.vars "rs.c" = ioff W off tgt i
    + keptLen (ibit W) (Csr.row off tgt i) (σ.vars "rs.j" - off i)
  hoff : ∃ f, σ.arrs oaO = arrOf (n + 1) f ∧ ∀ a ≤ i, f a = ioff W off tgt a
  htgt : ∃ g, σ.arrs taO = arrOf (ins W off tgt) g ∧
    ∀ p < σ.vars "rs.c", g p = itgt W off tgt p

/-- The between-rows state of the isolation sweep. -/
private structure IsoSt (nmI : ArenaNames) (oaO taO ba : String) (n ns : ℕ)
    (W : Set (Fin n)) (off tgt : ℕ → ℕ) (σ : Env) : Prop where
  hc : Csr nmI.off nmI.tgt n ns n off tgt σ
  hnN : σ.vars nmI.nN = n
  hbb : FinBits ba W σ
  hiN : σ.vars "rs.i" ≤ n
  hcv : σ.vars "rs.c" = ioff W off tgt (σ.vars "rs.i")
  hoff : ∃ f, σ.arrs oaO = arrOf (n + 1) f ∧
    ∀ a ≤ σ.vars "rs.i", f a = ioff W off tgt a
  htgt : ∃ g, σ.arrs taO = arrOf (ins W off tgt) g ∧
    ∀ p < σ.vars "rs.c", g p = itgt W off tgt p

section IsolateSpec

variable {B n ns : ℕ} {W : Set (Fin n)} {nmI : ArenaNames}
  {oaO taO nsO ba : String} {off tgt : ℕ → ℕ}

/-- One slot of a kept row: keep the target iff its batch bit is off. -/
private theorem isoSlot_step (hNB : n < B) (hnsB : ns < B)
    (h1 : taO ≠ nmI.off) (h2 : taO ≠ nmI.tgt) (h3 : taO ≠ ba) (h4 : taO ≠ oaO)
    (hnNs : ∀ y ∈ rsScalars, nmI.nN ≠ y)
    {i : ℕ} (hik : i < n) :
    ∀ σ, IsoRowSt nmI oaO taO ba n ns W off tgt i σ →
      σ.vars "rs.j" < off (i + 1) →
      ∃ σ' K', Run B (isoSlot nmI taO ba) σ σ' K' ∧
        IsoRowSt nmI oaO taO ba n ns W off tgt i σ' ∧
        σ'.vars "rs.j" = σ.vars "rs.j" + 1 ∧ K' ≤ 21 := by
  intro σ hR hjlt
  obtain ⟨hc, hnN, hbb, hiv, hbv0, he, hjlo, hjhi, hcv, hoff, htgt⟩ := hR
  set jv := σ.vars "rs.j" with hjv_def
  have hjns : jv < ns := lt_of_lt_of_le hjlt (hc.row_le hik)
  set w := tgt jv with hw_def
  have hwn : w < n := hc.target hjns
  have hins_ns : ins W off tgt ≤ ns := ins_le_ns W off tgt hc
  -- the slot read
  have hread : Run B (Csr.slot nmI.tgt "rs.j" "rs.w") σ (σ.setVar "rs.w" w) 3 := by
    refine (Run.assign (evalB_get (evalB_var (by omega)) ?_ (by omega))).mono (by simp)
    rw [hc.tgtArr, getElem?_arrOf tgt hjns]
  set σa := σ.setVar "rs.w" w with hσa
  -- the batch bit
  have hbread : Run B (.assign "rs.d" (.get ba (.var "rs.w"))) σa
      (σa.setVar "rs.d" (bbit W w)) 3 := by
    have haw : σa.vars "rs.w" = w := by rw [hσa]; simp
    have hwev : (Expr.var "rs.w").evalB B σa = some w := by
      rw [← haw]
      exact evalB_var (by rw [haw]; omega)
    refine (Run.assign (evalB_get hwev ?_
      (by have := bbit_le_one_of_lt (W := W) hwn; omega))).mono (by simp)
    rw [hσa]
    simp only [arrs_setVar]
    rw [getElem?_eq_getD (by rw [hbb.1]; omega), finBits_getD hbb hwn]
  set σb := σa.setVar "rs.d" (bbit W w) with hσb
  have hbd : σb.vars "rs.d" = bbit W w := by rw [hσb]; simp
  have hbc : σb.vars "rs.c" = σ.vars "rs.c" := by rw [hσb, hσa]; simp
  have hbj : σb.vars "rs.j" = jv := by rw [hσb, hσa]; simp [hjv_def]
  have hbw : σb.vars "rs.w" = w := by rw [hσb, hσa]; simp
  have hbarrs : ∀ b, σb.arrs b = σ.arrs b := by intro b; rw [hσb, hσa]; simp
  have hcond : (Cond.lt (.var "rs.d") (.lit 1)).evalB B σb
      = some (decide (bbit W w < 1)) := by
    refine evalB_condLt ?_ (evalB_lit (by omega))
    rw [← hbd]
    exact evalB_var (by rw [hbd]; have := bbit_le_one_of_lt (W := W) hwn; omega)
  -- the row entry under the pointer
  set row := Csr.row off tgt i with hrow_def
  set m := jv - off i with hm_def
  have hmrow : m < row.length := by
    rw [hrow_def, Csr.length_row, Csr.rowLen]
    omega
  have hrow_m : row.getD m 0 = w := by
    rw [hrow_def, row_getD (by rw [Csr.rowLen]; omega)]
    congr 1
    omega
  have hirow : irowL W off tgt i = row.filterMap (ibit W) := by
    rw [irowL, if_pos hbv0, hrow_def]
  obtain ⟨g, hgarr, hgpre⟩ := htgt
  by_cases hbw0 : bbit W w = 0
  · -- unbatched: keep the target
    have hcondT : (Cond.lt (.var "rs.d") (.lit 1)).evalB B σb = some true := by
      rw [hcond]
      congr 1
      simp [hbw0]
    have hsome : ibit W (row.getD m 0) = some w := by
      rw [hrow_m, ibit, if_pos hbw0]
    have hkept1 : keptLen (ibit W) row (m + 1) = keptLen (ibit W) row m + 1 :=
      keptLen_succ_some hmrow hsome
    have hkle : keptLen (ibit W) row m + 1 ≤ (row.filterMap (ibit W)).length := by
      have h := keptLen_le (ibit W) row (m + 1)
      rw [hkept1] at h
      exact h
    have hclt : σ.vars "rs.c" < ins W off tgt := by
      rw [hcv]
      calc ioff W off tgt i + keptLen (ibit W) row m
          < ioff W off tgt i + (irowL W off tgt i).length := by
            rw [hirow]; omega
        _ = ioff W off tgt (i + 1) := (ioff_succ W off tgt hik).symm
        _ ≤ ins W off tgt := ioff_le_ins W off tgt _
    -- the store
    have hst : Run B (.store taO (.var "rs.c") (.var "rs.w")) σb
        (σb.setArr taO (σ.vars "rs.c") w) 3 := by
      have hcev : (Expr.var "rs.c").evalB B σb = some (σ.vars "rs.c") := by
        rw [← hbc]
        exact evalB_var (by rw [hbc]; omega)
      have hwev : (Expr.var "rs.w").evalB B σb = some w := by
        rw [← hbw]
        exact evalB_var (by rw [hbw]; omega)
      refine (Run.store hcev hwev ?_).mono (by simp)
      rw [hbarrs, hgarr, length_arrOf]
      exact hclt
    set σc := σb.setArr taO (σ.vars "rs.c") w with hσc
    have hbump : Run B (.assign "rs.c" (.add (.var "rs.c") (.lit 1))) σc
        (σc.setVar "rs.c" (σ.vars "rs.c" + 1)) 4 := by
      have hcc : σc.vars "rs.c" = σ.vars "rs.c" := by rw [hσc]; simpa using hbc
      have hev := evalB_incr (B := B) (x := "rs.c") (σ := σc) (by rw [hcc]; omega)
      rw [hcc] at hev
      exact (Run.assign hev).mono (by simp)
    set σd := σc.setVar "rs.c" (σ.vars "rs.c" + 1) with hσd
    have hite : Run B (.ite (.lt (.var "rs.d") (.lit 1))
        (.seq (.store taO (.var "rs.c") (.var "rs.w"))
          (.assign "rs.c" (.add (.var "rs.c") (.lit 1)))) .skip) σb σd 11 :=
      (Run.ite_true hcondT (hst.seq hbump)).mono (by simp)
    have hinc : Run B (.assign "rs.j" (.add (.var "rs.j") (.lit 1))) σd
        (σd.setVar "rs.j" (jv + 1)) 4 := by
      have hdj : σd.vars "rs.j" = jv := by rw [hσd, hσc]; simpa using hbj
      have hev := evalB_incr (B := B) (x := "rs.j") (σ := σd) (by rw [hdj]; omega)
      rw [hdj] at hev
      exact (Run.assign hev).mono (by simp)
    set σ' := σd.setVar "rs.j" (jv + 1) with hσ'
    have hrun : Run B (isoSlot nmI taO ba) σ σ' 21 :=
      (hread.seq (hbread.seq (hite.seq hinc))).mono (by omega)
    have h'vars : ∀ y, y ≠ "rs.w" → y ≠ "rs.d" → y ≠ "rs.c" → y ≠ "rs.j" →
        σ'.vars y = σ.vars y := by
      intro y hy1 hy2 hy3 hy4
      rw [hσ', hσd, hσc, hσb, hσa]
      simp [hy1, hy2, hy3, hy4]
    have h'arrs : ∀ b, b ≠ taO → σ'.arrs b = σ.arrs b := by
      intro b hb
      rw [hσ', hσd, hσc, hσb, hσa]
      simp [hb]
    have h'j : σ'.vars "rs.j" = jv + 1 := by rw [hσ']; simp
    have h'c : σ'.vars "rs.c" = σ.vars "rs.c" + 1 := by rw [hσ', hσd]; simp
    have h'tgt : σ'.arrs taO
        = (arrOf (ins W off tgt) g).set (σ.vars "rs.c") w := by
      rw [hσ', hσd, hσc]
      simp only [arrs_setVar]
      rw [arrs_setArr, if_pos rfl, hbarrs, hgarr]
    refine ⟨σ', 21, hrun,
      ⟨hc.of_eq (h'arrs _ (Ne.symm h1)) (h'arrs _ (Ne.symm h2)),
        by rw [h'vars _ (hnNs _ (by decide)) (hnNs _ (by decide))
          (hnNs _ (by decide)) (hnNs _ (by decide))]; exact hnN,
        ⟨by rw [h'arrs _ (Ne.symm h3)]; exact hbb.1,
          fun v => by rw [h'arrs _ (Ne.symm h3)]; exact hbb.2 v⟩,
        by rw [h'vars "rs.i" (by decide) (by decide) (by decide) (by decide)]
           exact hiv,
        hbv0,
        by rw [h'vars "rs.e" (by decide) (by decide) (by decide) (by decide)]
           exact he,
        by rw [h'j]; omega,
        by rw [h'j]; omega,
        ?_, ?_, ?_⟩,
      by rw [h'j], le_rfl⟩
    · rw [h'j, h'c, hcv, ← hrow_def,
        show jv + 1 - off i = m + 1 by omega, hkept1]
      omega
    · obtain ⟨f, hfarr, hfpre⟩ := hoff
      exact ⟨f, by rw [h'arrs _ (Ne.symm h4)]; exact hfarr, hfpre⟩
    · refine ⟨fun p => if p = σ.vars "rs.c" then w else g p, ?_, ?_⟩
      · rw [h'tgt, set_arrOf]
      · intro p hp
        rw [h'c] at hp
        show (if p = σ.vars "rs.c" then w else g p) = itgt W off tgt p
        by_cases hpc : p = σ.vars "rs.c"
        · subst hpc
          rw [if_pos rfl, hcv, itgt_slice W off tgt hik (by rw [hirow]; omega)]
          rw [hirow]
          exact (filterMap_getD_kept hmrow hsome).symm
        · rw [if_neg hpc]
          exact hgpre p (by omega)
  · -- batched: the target is dropped
    have hcondF : (Cond.lt (.var "rs.d") (.lit 1)).evalB B σb = some false := by
      rw [hcond]
      congr 1
      have := bbit_le_one_of_lt (W := W) hwn
      simp
      omega
    have hnone : ibit W (row.getD m 0) = none := by
      rw [hrow_m, ibit, if_neg hbw0]
    have hite : Run B (.ite (.lt (.var "rs.d") (.lit 1))
        (.seq (.store taO (.var "rs.c") (.var "rs.w"))
          (.assign "rs.c" (.add (.var "rs.c") (.lit 1)))) .skip) σb σb 11 :=
      (Run.ite_false hcondF Run.skip).mono (by simp)
    have hinc : Run B (.assign "rs.j" (.add (.var "rs.j") (.lit 1))) σb
        (σb.setVar "rs.j" (jv + 1)) 4 := by
      have hev := evalB_incr (B := B) (x := "rs.j") (σ := σb) (by rw [hbj]; omega)
      rw [hbj] at hev
      exact (Run.assign hev).mono (by simp)
    set σ' := σb.setVar "rs.j" (jv + 1) with hσ'
    have hrun : Run B (isoSlot nmI taO ba) σ σ' 21 :=
      (hread.seq (hbread.seq (hite.seq hinc))).mono (by omega)
    have h'vars : ∀ y, y ≠ "rs.w" → y ≠ "rs.d" → y ≠ "rs.j" →
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
    refine ⟨σ', 21, hrun,
      ⟨hc.of_eq (h'arrs _) (h'arrs _),
        by rw [h'vars _ (hnNs _ (by decide)) (hnNs _ (by decide))
          (hnNs _ (by decide))]; exact hnN,
        ⟨by rw [h'arrs]; exact hbb.1, fun v => by rw [h'arrs]; exact hbb.2 v⟩,
        by rw [h'vars "rs.i" (by decide) (by decide) (by decide)]; exact hiv,
        hbv0,
        by rw [h'vars "rs.e" (by decide) (by decide) (by decide)]; exact he,
        by rw [h'j]; omega,
        by rw [h'j]; omega,
        ?_, ?_, ?_⟩,
      by rw [h'j], le_rfl⟩
    · rw [h'j, h'c, hcv, ← hrow_def,
        show jv + 1 - off i = m + 1 by omega, keptLen_succ_none hmrow hnone]
    · obtain ⟨f, hfarr, hfpre⟩ := hoff
      exact ⟨f, by rw [h'arrs]; exact hfarr, hfpre⟩
    · exact ⟨g, by rw [h'arrs]; exact hgarr,
        fun p hp => hgpre p (by rwa [h'c] at hp)⟩

/-- **One row of the sweep**: skip a batched vertex outright, filter a
kept one; seal the output boundary either way. Costs
`25·deg(row) + 28`. -/
private theorem isoBody_run (hNB : n < B) (hnsB : ns < B)
    (h1 : taO ≠ nmI.off) (h2 : taO ≠ nmI.tgt) (h3 : taO ≠ ba) (h4 : taO ≠ oaO)
    (h5 : oaO ≠ nmI.off) (h6 : oaO ≠ nmI.tgt) (h7 : oaO ≠ ba)
    (hnNs : ∀ y ∈ rsScalars, nmI.nN ≠ y) :
    ∀ σ, IsoSt nmI oaO taO ba n ns W off tgt σ → σ.vars "rs.i" < n →
      ∃ σ', Run B (isoBody nmI oaO taO ba) σ σ'
          (25 * Csr.rowLen off (σ.vars "rs.i") + 28) ∧
        IsoSt nmI oaO taO ba n ns W off tgt σ' ∧
        σ'.vars "rs.i" = σ.vars "rs.i" + 1 := by
  intro σ hF hlt
  obtain ⟨hc, hnN, hbb, hiN, hcv, hoff, htgt⟩ := hF
  set i := σ.vars "rs.i" with hi_def
  have hins_ns : ins W off tgt ≤ ns := ins_le_ns W off tgt hc
  -- the row's own bit
  have hbread : Run B (.assign "rs.x" (.get ba (.var "rs.i"))) σ
      (σ.setVar "rs.x" (bbit W i)) 3 := by
    refine (Run.assign (evalB_get (evalB_var (by omega)) ?_
      (by have := bbit_le_one_of_lt (W := W) hlt; omega))).mono (by simp)
    rw [getElem?_eq_getD (by rw [hbb.1]; omega), finBits_getD hbb hlt]
  set σ₁ := σ.setVar "rs.x" (bbit W i) with hσ₁
  have h1x : σ₁.vars "rs.x" = bbit W i := by rw [hσ₁]; simp
  have h1vars : ∀ y, y ≠ "rs.x" → σ₁.vars y = σ.vars y := by
    intro y hy
    rw [hσ₁]
    simp [hy]
  have h1arrs : ∀ b, σ₁.arrs b = σ.arrs b := by intro b; rw [hσ₁]; simp
  have hcond : (Cond.lt (.var "rs.x") (.lit 1)).evalB B σ₁
      = some (decide (bbit W i < 1)) := by
    refine evalB_condLt ?_ (evalB_lit (by omega))
    rw [← h1x]
    exact evalB_var (by rw [h1x]; have := bbit_le_one_of_lt (W := W) hlt; omega)
  -- the branch: scan or skip
  have hbranch : ∃ σ₂, Run B (.ite (.lt (.var "rs.x") (.lit 1))
      (.seq (Csr.loadRow nmI.off "rs.i" "rs.j" "rs.e")
        (Csr.scan "rs.j" "rs.e" (isoSlot nmI taO ba)))
      .skip) σ₁ σ₂ (25 * Csr.rowLen off i + 16) ∧
      Csr nmI.off nmI.tgt n ns n off tgt σ₂ ∧
      σ₂.vars nmI.nN = n ∧ FinBits ba W σ₂ ∧ σ₂.vars "rs.i" = i ∧
      σ₂.vars "rs.c" = ioff W off tgt (i + 1) ∧
      (∃ f, σ₂.arrs oaO = arrOf (n + 1) f ∧ ∀ a ≤ i, f a = ioff W off tgt a) ∧
      (∃ g, σ₂.arrs taO = arrOf (ins W off tgt) g ∧
        ∀ p < σ₂.vars "rs.c", g p = itgt W off tgt p) := by
    by_cases hb0 : bbit W i = 0
    · -- a kept row: load its bounds and filter it
      have hcondT : (Cond.lt (.var "rs.x") (.lit 1)).evalB B σ₁ = some true := by
        rw [hcond]
        congr 1
        simp [hb0]
      have h1c : Csr nmI.off nmI.tgt n ns n off tgt σ₁ :=
        hc.of_eq (h1arrs _) (h1arrs _)
      have h1i : σ₁.vars "rs.i" = i := h1vars _ (by decide)
      obtain ⟨σload, hload, hpostl⟩ :=
        (Csr.loadRow_spec B n ns n nmI.off nmI.tgt "rs.i" "rs.j" "rs.e" off tgt
          (by decide) (by decide)).run
          (σ := σ₁) ⟨⟨h1c, by omega, hnsB⟩, by rw [h1i]; omega, by rw [h1i]; omega⟩
      obtain ⟨-, -, -, hσload⟩ := hpostl
      rw [h1i] at hσload
      have hR : IsoRowSt nmI oaO taO ba n ns W off tgt i σload := by
        have hlv : ∀ y, y ≠ "rs.j" → y ≠ "rs.e" → σload.vars y = σ₁.vars y := by
          intro y hy1 hy2
          rw [hσload]
          simp [hy1, hy2]
        have hla : ∀ b, σload.arrs b = σ₁.arrs b := by
          intro b
          rw [hσload]
          simp
        have hlj : σload.vars "rs.j" = off i := by rw [hσload]; simp
        have hle : σload.vars "rs.e" = off (i + 1) := by rw [hσload]; simp
        refine ⟨h1c.of_eq (hla _) (hla _),
          by rw [hlv _ (hnNs _ (by decide)) (hnNs _ (by decide)),
            h1vars _ (hnNs _ (by decide))]; exact hnN,
          ⟨by rw [hla, h1arrs]; exact hbb.1,
            fun v => by rw [hla, h1arrs]; exact hbb.2 v⟩,
          by rw [hlv _ (by decide) (by decide)]; exact h1i,
          hb0, hle,
          by rw [hlj],
          by rw [hlj]; exact hc.off_le_succ hlt,
          ?_, ?_, ?_⟩
        · rw [hlv _ (by decide) (by decide), h1vars _ (by decide), hlj,
            Nat.sub_self, keptLen_zero, Nat.add_zero, hcv]
        · obtain ⟨f, hfarr, hfpre⟩ := hoff
          exact ⟨f, by rw [hla, h1arrs]; exact hfarr, hfpre⟩
        · obtain ⟨g, hgarr, hgpre⟩ := htgt
          refine ⟨g, by rw [hla, h1arrs]; exact hgarr, ?_⟩
          intro p hp
          refine hgpre p ?_
          rwa [hlv _ (by decide) (by decide), h1vars _ (by decide)] at hp
      have hscan := Csr.rowScan_spec B (25 * Csr.rowLen off i + 4) (off (i + 1)) 21
        "rs.j" "rs.e" (isoSlot nmI taO ba)
        (P := fun τ => τ = σload)
        (I := IsoRowSt nmI oaO taO ba n ns W off tgt i)
        (hc.off_lt hnsB (by omega))
        (fun τ hτ => ⟨hτ.he, hτ.hjhi⟩)
        (fun τ hτ hjlt => isoSlot_step hNB hnsB h1 h2 h3 h4 hnNs hlt τ hτ hjlt)
        (fun τ hτ => by rw [hτ]; exact hR)
        (fun τ hτ => by
          have hj : σload.vars "rs.j" = off i := by rw [hσload]; simp
          rw [hτ, hj, Csr.rowLen])
      obtain ⟨σ₂, hrscan, hR₂, hj₂⟩ := hscan.run rfl
      obtain ⟨hc₂, hnN₂, hbb₂, hiv₂, -, -, -, -, hcv₂, hoff₂, htgt₂⟩ := hR₂
      have hcfin : σ₂.vars "rs.c" = ioff W off tgt (i + 1) := by
        have hirow : irowL W off tgt i = (Csr.row off tgt i).filterMap (ibit W) := by
          rw [irowL, if_pos hb0]
        have hkfull : keptLen (ibit W) (Csr.row off tgt i)
            (σ₂.vars "rs.j" - off i) = (irowL W off tgt i).length := by
          rw [hj₂, show off (i + 1) - off i = Csr.rowLen off i from rfl,
            ← Csr.length_row off tgt i, keptLen_full, hirow]
        rw [hcv₂, hkfull, ioff_succ W off tgt hlt]
      refine ⟨σ₂, ?_, hc₂, hnN₂, hbb₂, hiv₂, hcfin, hoff₂, htgt₂⟩
      have h := hload.seq hrscan
      refine (Run.ite_true hcondT h).mono ?_
      simp only [size_condLt, size_var, size_lit]
      omega
    · -- a batched row: nothing is scanned, the row comes out empty
      have hcondF : (Cond.lt (.var "rs.x") (.lit 1)).evalB B σ₁ = some false := by
        rw [hcond]
        congr 1
        have := bbit_le_one_of_lt (W := W) hlt
        simp
        omega
      have hempty : irowL W off tgt i = [] := by
        rw [irowL, if_neg hb0]
      have hcfin : σ₁.vars "rs.c" = ioff W off tgt (i + 1) := by
        rw [h1vars _ (by decide), hcv, ioff_succ W off tgt hlt, hempty]
        simp
      refine ⟨σ₁, (Run.ite_false hcondF Run.skip).mono
        (by simp only [size_condLt, size_var, size_lit]; omega),
        hc.of_eq (h1arrs _) (h1arrs _),
        by rw [h1vars _ (hnNs _ (by decide))]; exact hnN,
        ⟨by rw [h1arrs]; exact hbb.1, fun v => by rw [h1arrs]; exact hbb.2 v⟩,
        h1vars _ (by decide),
        hcfin, ?_, ?_⟩
      · obtain ⟨f, hfarr, hfpre⟩ := hoff
        exact ⟨f, by rw [h1arrs]; exact hfarr, hfpre⟩
      · obtain ⟨g, hgarr, hgpre⟩ := htgt
        refine ⟨g, by rw [h1arrs]; exact hgarr, ?_⟩
        intro p hp
        refine hgpre p ?_
        rwa [h1vars _ (by decide)] at hp
  obtain ⟨σ₂, hbr, hc₂, hnN₂, hbb₂, hiv₂, hcv₂, hoff₂, htgt₂⟩ := hbranch
  obtain ⟨f, hfarr, hfpre⟩ := hoff₂
  -- seal the output boundary
  have hioffB : ioff W off tgt (i + 1) ≤ ns :=
    le_trans (ioff_le_ins W off tgt _) hins_ns
  have hst : Run B (.store oaO (.add (.var "rs.i") (.lit 1)) (.var "rs.c"))
      σ₂ (σ₂.setArr oaO (i + 1) (ioff W off tgt (i + 1))) 5 := by
    have hiev : (Expr.add (.var "rs.i") (.lit 1)).evalB B σ₂ = some (i + 1) := by
      have h := evalB_incr (B := B) (x := "rs.i") (σ := σ₂) (by rw [hiv₂]; omega)
      rwa [hiv₂] at h
    have hcev : (Expr.var "rs.c").evalB B σ₂ = some (ioff W off tgt (i + 1)) := by
      rw [← hcv₂]
      exact evalB_var (by rw [hcv₂]; omega)
    refine (Run.store hiev hcev ?_).mono (by simp)
    rw [hfarr, length_arrOf]
    omega
  set σ₃ := σ₂.setArr oaO (i + 1) (ioff W off tgt (i + 1)) with hσ₃
  have hinc : Run B (.assign "rs.i" (.add (.var "rs.i") (.lit 1))) σ₃
      (σ₃.setVar "rs.i" (i + 1)) 4 := by
    have h3i : σ₃.vars "rs.i" = i := by rw [hσ₃]; simpa using hiv₂
    have hev := evalB_incr (B := B) (x := "rs.i") (σ := σ₃) (by rw [h3i]; omega)
    rw [h3i] at hev
    exact (Run.assign hev).mono (by simp)
  set σ₄ := σ₃.setVar "rs.i" (i + 1) with hσ₄
  have h4arrs : ∀ b, b ≠ oaO → σ₄.arrs b = σ₂.arrs b := by
    intro b hb
    rw [hσ₄, hσ₃]
    simp [hb]
  have h4vars : ∀ y, y ≠ "rs.i" → σ₄.vars y = σ₂.vars y := by
    intro y hy
    rw [hσ₄, hσ₃]
    simp [hy]
  have h4i : σ₄.vars "rs.i" = i + 1 := by rw [hσ₄]; simp
  refine ⟨σ₄, ?_,
    ⟨hc₂.of_eq (h4arrs _ (Ne.symm h5)) (h4arrs _ (Ne.symm h6)),
      by rw [h4vars _ (hnNs _ (by decide))]; exact hnN₂,
      ⟨by rw [h4arrs _ (Ne.symm h7)]; exact hbb₂.1,
        fun v => by rw [h4arrs _ (Ne.symm h7)]; exact hbb₂.2 v⟩,
      by rw [h4i]; omega,
      by rw [h4i, h4vars _ (by decide), hcv₂],
      ?_, ?_⟩, h4i⟩
  · have h := hbread.seq (hbr.seq (hst.seq hinc))
    exact h.mono (by omega)
  · refine ⟨fun a => if a = i + 1 then ioff W off tgt (i + 1) else f a, ?_, ?_⟩
    · rw [hσ₄, arrs_setVar, hσ₃, arrs_setArr, if_pos rfl, hfarr, set_arrOf]
    · intro a ha
      rw [h4i] at ha
      show (if a = i + 1 then ioff W off tgt (i + 1) else f a) = ioff W off tgt a
      by_cases hae : a = i + 1
      · rw [if_pos hae, hae]
      · rw [if_neg hae]
        exact hfpre a (by omega)
  · obtain ⟨g, hgarr, hgpre⟩ := htgt₂
    refine ⟨g, by rw [h4arrs _ h4]; exact hgarr, ?_⟩
    intro p hp
    refine hgpre p ?_
    rwa [h4vars _ (by decide)] at hp

end IsolateSpec

/-! ### §15b The budget -/

/-- **`isolate`'s budget** — `Impl.isolateCharge`'s `Σ_v (deg v + 1)`
shape at machine constants: linear in slots plus carrier, nothing
else. -/
def isolateK (N ns : ℕ) : ℕ := 25 * ns + 33 * N + 13

/-- The budget against the abstract charge: one constant. -/
theorem isolateK_le_isolateCharge {Λc n₀ ℓp : ℕ} (Bar : Impl.MArena Λc n₀ ℓp)
    [DecidableRel Bar.G.Adj] :
    isolateK Bar.N (∑ v : Fin Bar.N, Bar.G.degree v)
      ≤ 33 * (Impl.isolateCharge Bar + 1) := by
  rw [isolateK, Impl.isolateCharge, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one]
  have h : 25 * (∑ v : Fin Bar.N, Bar.G.degree v)
      ≤ 33 * (∑ v : Fin Bar.N, Bar.G.degree v) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

section IsolateMain

variable {B n₀ Λc ℓp : ℕ}

set_option maxHeartbeats 800000 in
open Classical in
/-- **`isolate`, discharged end to end**: from the child frame state
and the batch's bit region, one CSR sweep leaves, at the output names,
the arena that **IS** `MArena.isolate` — the carrier kept, the batch's
edges gone — with the new slot count in its cell and everything else
intact. Budget `isolateK`, `Impl.isolateCharge`'s `O(‖B‖)` shape. -/
theorem isolateCom_spec {hb : ℕ} {Bar : Impl.MArena Λc n₀ ℓp}
    {W : Set (Fin Bar.N)} {nmI : ArenaNames} {oaO taO nsO ba : String} {nsI : ℕ}
    (hNB : Bar.N < B) (hnsB : nsI < B)
    (h1 : taO ≠ nmI.off) (h2 : taO ≠ nmI.tgt) (h3 : taO ≠ ba) (h4 : taO ≠ oaO)
    (h5 : oaO ≠ nmI.off) (h6 : oaO ≠ nmI.tgt) (h7 : oaO ≠ ba)
    (h8 : oaO ≠ nmI.col) (h9 : oaO ≠ nmI.up) (h10 : oaO ≠ nmI.hist)
    (h11 : taO ≠ nmI.col) (h12 : taO ≠ nmI.up) (h13 : taO ≠ nmI.hist)
    (hs1 : nsO ∉ rsScalars) (hs2 : nsO ≠ nmI.nN) (hs3 : nsO ≠ nmI.nS)
    (hs4 : nmI.nN ∉ rsScalars) (hs5 : nmI.nS ∉ rsScalars) :
    Spec B
      (fun σ => ArenaSt nmI hb Bar σ ∧ σ.vars nmI.nS = nsI ∧ FinBits ba W σ ∧
        (σ.arrs oaO).length = Bar.N + 1 ∧
        (σ.arrs taO).length = ∑ v : Fin Bar.N, (deleteVerts Bar.G W).degree v)
      (isolateCom nmI oaO taO nsO ba)
      (fun _ σ' =>
        ArenaSt { nmI with off := oaO, tgt := taO, nS := nsO } hb
          (Bar.isolate W) σ' ∧
        σ'.vars nsO = ∑ v : Fin Bar.N, (deleteVerts Bar.G W).degree v ∧
        ArenaSt nmI hb Bar σ' ∧ σ'.vars nmI.nS = nsI ∧ FinBits ba W σ')
      (isolateK Bar.N nsI) := by
  classical
  intro σ₀ hσ₀
  obtain ⟨hA, hns, hbb, hLoff, hLtgt⟩ := hσ₀
  obtain ⟨off, tgt, hc0, hoff0, hnd, hadj⟩ := hA.csr
  rw [hns] at hc0
  have hnNs : ∀ y ∈ rsScalars, nmI.nN ≠ y := fun y hy h => hs4 (h ▸ hy)
  have hnSs : ∀ y ∈ rsScalars, nmI.nS ≠ y := fun y hy h => hs5 (h ▸ hy)
  have hnOs : ∀ y ∈ rsScalars, nsO ≠ y := fun y hy h => hs1 (h ▸ hy)
  -- the isolated dimensions
  have hirowlen : ∀ v : Fin Bar.N, (irowL W off tgt (v : ℕ)).length
      = (deleteVerts Bar.G W).degree v := by
    intro v
    refine length_eq_degree v (irowL_nodup W off tgt hnd v.2) ?_
    intro w
    exact mem_irowL_iff W off tgt hadj v.2 w
  have hins_deg : ins W off tgt
      = ∑ v : Fin Bar.N, (deleteVerts Bar.G W).degree v := by
    rw [ins, ioff_eq_offList W off tgt le_rfl, offList_eq_sum,
      ← Fin.sum_univ_eq_sum_range (fun t => (irowL W off tgt t).length) Bar.N]
    exact Finset.sum_congr rfl fun v _ => hirowlen v
  have hins_ns : ins W off tgt ≤ nsI := ins_le_ns W off tgt hc0
  -- the three initializations
  have h1r : Run B (.assign "rs.c" (.lit 0)) σ₀ (σ₀.setVar "rs.c" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  set σ₁ := σ₀.setVar "rs.c" 0 with hσ₁
  have h2r : Run B (.store oaO (.lit 0) (.lit 0)) σ₁ (σ₁.setArr oaO 0 0) 3 := by
    refine (Run.store (evalB_lit (by omega)) (evalB_lit (by omega)) ?_).mono (by simp)
    rw [hσ₁]
    simp only [arrs_setVar]
    omega
  set σ₂ := σ₁.setArr oaO 0 0 with hσ₂
  have h3r : Run B (.assign "rs.i" (.lit 0)) σ₂ (σ₂.setVar "rs.i" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  set σ₃ := σ₂.setVar "rs.i" 0 with hσ₃
  have h3arrs : ∀ b, b ≠ oaO → σ₃.arrs b = σ₀.arrs b := by
    intro b hb
    rw [hσ₃, hσ₂, hσ₁]
    simp [hb]
  have h3off : σ₃.arrs oaO = (σ₀.arrs oaO).set 0 0 := by
    rw [hσ₃, hσ₂, hσ₁]
    simp
  have h3vars : ∀ y, y ≠ "rs.c" → y ≠ "rs.i" → σ₃.vars y = σ₀.vars y := by
    intro y hy1 hy2
    rw [hσ₃, hσ₂, hσ₁]
    simp [hy1, hy2]
  -- the sweep state at entry
  have hF₃ : IsoSt nmI oaO taO ba Bar.N nsI W off tgt σ₃ := by
    refine ⟨hc0.of_eq (h3arrs _ (Ne.symm h5)) (h3arrs _ (Ne.symm h6)),
      by rw [h3vars _ (hnNs _ (by decide)) (hnNs _ (by decide))]; exact hA.n_eq,
      ⟨by rw [h3arrs _ (Ne.symm h7)]; exact hbb.1,
        fun v => by rw [h3arrs _ (Ne.symm h7)]; exact hbb.2 v⟩,
      by rw [hσ₃]; simp,
      by rw [hσ₃]; simp [hσ₂, hσ₁],
      ?_, ?_⟩
    · refine ⟨fun a => if a = 0 then 0 else (σ₀.arrs oaO).getD a 0, ?_, ?_⟩
      · rw [h3off]
        conv_lhs => rw [show σ₀.arrs oaO
            = arrOf (Bar.N + 1) (fun p => (σ₀.arrs oaO).getD p 0) by
          rw [← hLoff]; exact (arrOf_getD _).symm]
        rw [set_arrOf]
      · intro a ha
        have hia : σ₃.vars "rs.i" = 0 := by rw [hσ₃]; simp
        rw [hia] at ha
        have ha0 : a = 0 := by omega
        subst ha0
        show (if 0 = 0 then 0 else (σ₀.arrs oaO).getD 0 0) = ioff W off tgt 0
        rw [if_pos rfl, ioff_zero]
    · refine ⟨fun p => (σ₀.arrs taO).getD p 0, ?_, ?_⟩
      · rw [h3arrs _ h4, hins_deg, ← hLtgt]
        exact (arrOf_getD _).symm
      · intro p hp
        have hc0' : σ₃.vars "rs.c" = 0 := by rw [hσ₃, hσ₂, hσ₁]; simp
        rw [hc0'] at hp
        omega
  -- the sweep, amortized at the input rows
  have hloop := Run.while_potential (B := B)
    (b := .lt (.var "rs.i") (.var nmI.nN)) (c := isoBody nmI oaO taO ba)
    (IsoSt nmI oaO taO ba Bar.N nsI W off tgt)
    (fun τ => ∑ t ∈ Finset.Ico (τ.vars "rs.i") Bar.N,
      (25 * Csr.rowLen off t + 33))
    (fun τ hτ => evalB_condLt_vars (by have := hτ.hiN; omega) (by rw [hτ.hnN]; omega))
    (fun τ hτ hcond => by
      have hlt' : τ.vars "rs.i" < Bar.N := by
        have := lt_of_condLt_true hcond
        rwa [hτ.hnN] at this
      obtain ⟨τ', hrun, hF', hi'⟩ :=
        isoBody_run hNB hnsB h1 h2 h3 h4 h5 h6 h7 hnNs τ hτ hlt'
      refine ⟨τ', _, hrun, hF', ?_⟩
      have hsplit : ∑ t ∈ Finset.Ico (τ.vars "rs.i") Bar.N,
          (25 * Csr.rowLen off t + 33)
          = (25 * Csr.rowLen off (τ.vars "rs.i") + 33)
            + ∑ t ∈ Finset.Ico (τ.vars "rs.i" + 1) Bar.N,
              (25 * Csr.rowLen off t + 33) :=
        Finset.sum_eq_sum_Ico_succ_bot hlt' _
      show 1 + (Cond.lt (.var "rs.i") (.var nmI.nN)).size
          + (25 * Csr.rowLen off (τ.vars "rs.i") + 28)
          + (∑ t ∈ Finset.Ico (τ'.vars "rs.i") Bar.N,
              (25 * Csr.rowLen off t + 33))
          ≤ ∑ t ∈ Finset.Ico (τ.vars "rs.i") Bar.N,
              (25 * Csr.rowLen off t + 33)
      rw [hi', hsplit]
      simp only [size_condLt, size_var]
      omega)
    hF₃
  obtain ⟨σf, Kf, hwrun, hFf, hcondf, hKf⟩ := hloop
  have hif : σf.vars "rs.i" = Bar.N := by
    have hle := le_of_condLt_false hcondf
    have h1' := hFf.hnN
    have h2' := hFf.hiN
    omega
  obtain ⟨f, hfarr, hfpre⟩ := hFf.hoff
  obtain ⟨g, hgarr, hgpre⟩ := hFf.htgt
  have hofffin : σf.arrs oaO = arrOf (Bar.N + 1) (ioff W off tgt) := by
    rw [hfarr]
    exact arrOf_congr fun a ha => hfpre a (by rw [hif]; omega)
  have hcvfin : σf.vars "rs.c" = ins W off tgt := by
    rw [hFf.hcv, hif]
    rfl
  have htgtfin : σf.arrs taO = arrOf (ins W off tgt) (itgt W off tgt) := by
    rw [hgarr]
    exact arrOf_congr fun p hp => hgpre p (by rw [hcvfin]; omega)
  -- the output cell
  have hr5 : Run B (.assign nsO (.var "rs.c")) σf
      (σf.setVar nsO (ins W off tgt)) 2 := by
    have hev : (Expr.var "rs.c").evalB B σf = some (ins W off tgt) := by
      rw [← hcvfin]
      exact evalB_var (by rw [hcvfin]; omega)
    exact (Run.assign hev).mono (by simp)
  set σ' := σf.setVar nsO (ins W off tgt) with hσ'
  have h'arrs : ∀ b, σ'.arrs b = σf.arrs b := by intro b; rw [hσ']; simp
  have h'vars : ∀ y, y ≠ nsO → σ'.vars y = σf.vars y := by
    intro y hy
    rw [hσ']
    simp [hy]
  -- the whole-run transports
  have hwv : ∀ y, y ∈ rsScalars → True := fun _ _ => trivial
  have hVarsAll : ∀ y, y ∉ rsScalars → y ≠ nsO → σ'.vars y = σ₀.vars y := by
    intro y hy hyO
    have hne : ∀ z ∈ rsScalars, y ≠ z := fun z hz h => hy (h ▸ hz)
    have hfv := hwrun
    -- the loop writes only scratch (frame off the loop's own syntax)
    have hfr : σf.vars y = σ₃.vars y := by
      refine hwrun.frame_var y ?_
      intro hmem
      have hsub : ∀ z ∈ (Com.while (.lt (.var "rs.i") (.var nmI.nN))
          (isoBody nmI oaO taO ba)).wvars, z ∈ rsScalars := by
        intro z hz
        have hzl : (Com.while (.lt (.var "rs.i") (.var nmI.nN))
            (isoBody nmI oaO taO ba)).wvars
            = ["rs.x", "rs.j", "rs.e", "rs.w", "rs.d", "rs.c", "rs.j", "rs.i"] := rfl
        rw [hzl] at hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact hy (hsub y hmem)
    rw [h'vars _ hyO, hfr, h3vars _ (hne _ (by decide)) (hne _ (by decide))]
  have hArrsAll : ∀ b, b ≠ oaO → b ≠ taO → σ'.arrs b = σ₀.arrs b := by
    intro b hb1 hb2
    have hfr : σf.arrs b = σ₃.arrs b := by
      refine hwrun.frame_arr b ?_
      have hzl : (Com.while (.lt (.var "rs.i") (.var nmI.nN))
          (isoBody nmI oaO taO ba)).warrs = [taO, oaO] := rfl
      rw [hzl]
      simp [hb1, hb2]
    rw [h'arrs, hfr, h3arrs _ hb1]
  refine ⟨σ', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the run at the announced budget
    have h := h1r.seq (h2r.seq (h3r.seq (hwrun.seq hr5)))
    refine h.mono ?_
    have hΦ₃ : (∑ t ∈ Finset.Ico (σ₃.vars "rs.i") Bar.N,
        (25 * Csr.rowLen off t + 33))
        = 25 * (∑ t ∈ Finset.range Bar.N, Csr.rowLen off t) + 33 * Bar.N := by
      have hi₃ : σ₃.vars "rs.i" = 0 := by rw [hσ₃]; simp
      rw [hi₃, ← Finset.range_eq_Ico, Finset.sum_add_distrib, ← Finset.mul_sum,
        Finset.sum_const, Finset.card_range, smul_eq_mul,
        Nat.mul_comm Bar.N 33]
    have hsum_ns : ∑ t ∈ Finset.range Bar.N, Csr.rowLen off t = nsI := by
      have h6' := Csr.sum_rowLen hc0 Bar.N le_rfl
      have h7' := hc0.last
      omega
    simp only [size_condLt, size_var] at hKf
    rw [hΦ₃, hsum_ns] at hKf
    rw [isolateK]
    omega
  · -- the isolated arena, at the output names
    refine ⟨?_, ⟨ioff W off tgt, itgt W off tgt, ?_, ioff_zero W off tgt, ?_, ?_⟩,
      ?_, ?_, ?_⟩
    · show σ'.vars nmI.nN = (Bar.isolate W).N
      rw [hVarsAll _ hs4 (Ne.symm hs2)]
      exact hA.n_eq
    · -- the CSR relation at the new slot count
      show Csr oaO taO (Bar.isolate W).N (σ'.vars nsO) (Bar.isolate W).N
        (ioff W off tgt) (itgt W off tgt) σ'
      have h'ns : σ'.vars nsO = ins W off tgt := by rw [hσ']; simp
      rw [h'ns]
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · rw [h'arrs]
        exact hofffin
      · rw [h'arrs]
        exact htgtfin
      · intro i hi
        exact ioff_mono W off tgt (by omega)
      · rfl
      · intro pp hpp
        exact itgt_lt W off tgt hpp
    · intro v
      rw [row_ioff_itgt W off tgt v.2]
      exact irowL_nodup W off tgt hnd v.2
    · intro v w
      rw [row_ioff_itgt W off tgt v.2]
      exact mem_irowL_iff W off tgt hadj v.2 w
    · -- the color rows are the input's, untouched
      show ColBits nmI.col (Bar.isolate W).col σ'
      have h := hA.col
      rw [ColBits] at h ⊢
      rw [hArrsAll _ (Ne.symm h8) (Ne.symm h11)]
      exact h
    · show UpArr nmI.up (Bar.isolate W).up σ'
      have h := hA.up
      rw [UpArr] at h ⊢
      rw [hArrsAll _ (Ne.symm h9) (Ne.symm h12)]
      exact h
    · show HistArr nmI.hist ℓp hb (Bar.isolate W).hist σ'
      have h := hA.hist
      rw [HistArr] at h ⊢
      rw [hArrsAll _ (Ne.symm h10) (Ne.symm h13)]
      exact h
  · rw [hσ']
    simp only [vars_setVar]
    exact hins_deg
  · -- the input arena survives
    refine ⟨?_, ⟨off, tgt, ?_, hoff0, hnd, hadj⟩, ?_, ?_, ?_⟩
    · rw [hVarsAll _ hs4 (Ne.symm hs2)]
      exact hA.n_eq
    · have hnsv : σ'.vars nmI.nS = nsI := by
        rw [hVarsAll _ hs5 (Ne.symm hs3)]
        exact hns
      rw [hnsv]
      exact hc0.of_eq (hArrsAll _ (Ne.symm h5) (Ne.symm h1))
        (hArrsAll _ (Ne.symm h6) (Ne.symm h2))
    · have h := hA.col
      rw [ColBits] at h ⊢
      rw [hArrsAll _ (Ne.symm h8) (Ne.symm h11)]
      exact h
    · have h := hA.up
      rw [UpArr] at h ⊢
      rw [hArrsAll _ (Ne.symm h9) (Ne.symm h12)]
      exact h
    · have h := hA.hist
      rw [HistArr] at h ⊢
      rw [hArrsAll _ (Ne.symm h10) (Ne.symm h13)]
      exact h
  · rw [hVarsAll _ hs5 (Ne.symm hs3)]
    exact hns
  · refine ⟨?_, fun v => ?_⟩ <;> rw [hArrsAll _ (Ne.symm h7) (Ne.symm h3)]
    · exact hbb.1
    · exact hbb.2 v

end IsolateMain


end Lax3Proofs.Prog
