import Lax3Proofs.SolveMachPrep

/-!
# F6c12 (residual 1) — the child-building pass: the batch, from the channel

`SolveMachPrep` named **`ChildLoadParts`** (and `ChildLoadPartsAll`) —
the child-building pass restated at the shape the composed stage lifts
hand over — and left its discharge open. This file supplies the facts
that discharge *was* blocked on, and prices the pass.

**What was blocked, and what changed.** For four waves the leaf was
blocked by the ⟨D⟩ finding: the batch was defined through
`SplitterWin.pathSet`, a `Classical.choose`-picked walk that no program
can output, while `profilesCom_specW`'s precondition demands the batch
region hold `batchFn`'s values *exactly*. Leaf G1 (2026-08-24) replaced
that definition: `Arena` now carries `chan : Fin N → ℕ → List (Fin N)`,
and

```
  batchPar A u = {u} ∪ {z | ∃ e < A.hist.length, z ∈ A.chan u e}
```

(`DriverArena`). **The batch now comes from the channel** — from data
the machine already holds.

This file makes that concrete at the machine's own objects:

* **§1** — the batch's trace on the child carrier is a scan of the
  *restricted child's own* channel row at `centreChild`. `MArena.restrict`
  carries the parent's columns down filtered and renumbered
  (`ImplRestrict`: `hist a r = (A.hist (restrictEmb S a) r).filterMap
  (toLocal S)`), and `restrictEmb (cluster) centreChild = u`, so row
  `centreChild` of the restricted channel is exactly `A.chan u ·`
  cut to the cluster. `mem_batchSet_iff_restrictHist` is §5 line 19
  verbatim — `W := pad_m({u} ∪ ⋃_{e ∈ rounds} B₀.hist[u][e])`, with
  `B₀.hist` the restricted child's, not the parent's.
* **§2** — `batchFn` is the **ascending** enumeration of that trace,
  padded. `Driver.setEquiv` is `Finset.orderIsoOfFin` (F6c2's pin), so
  the `i`-th padded slot is the `i`-th smallest member;
  `setEquiv_strictMono` and `batchFn_eq_of_ncard_lt` are the two
  facts a left-to-right carrier scan's invariant consumes — the scan
  emits members in increasing order, so slot `i` receives the member
  with exactly `i` members below it.
* **§3** — the pass's stage budget and its envelope. `prepStageK` is the
  honest sum of the five landed stage budgets at the dimensions each
  stage actually sees, and `prepStageK_le` closes it as
  **`restrictK` + (schedule constant)·(‖B₀‖ + 1)**: §6.1's own column,
  which §7 absorbs into the leading coefficient
  `a := c + (2 + ℓ·R)·c_D`, plus a term of the `c·Σ_u N_u` children
  column. No `A.N` term is introduced — `restrictK`'s visible absence of
  one (the `Θ(A.N²)` trap of §6.1's scratch paragraph) survives the sum.

## What this file does **not** do

`ChildLoadPartsAll` is **not** discharged here, and no weakened variant
of it is stated. Three machine passes the pass needs have no landed
program, and each is a leaf in its own right:

1. the cluster-row copy (`ClusterCsr.read_row` is a *lemma*; the copy
   loop that turns row `u` into `restrictCom_specW`'s `ClusterList` is
   not written);
2. the batch builder — the scan §1/§2 describe, producing both
   `profilesCom_specW`'s index region (length **exactly** `S.width`)
   and `isolateCom_specW`'s bit region at `Set.range batchFn`;
3. the colour-region writer — the child's `ColBits` region at
   `Impl.recordProfilesMS` over the `isoPal` layout. `profilesCom_specW`
   leaves the pd/pu tables in *separate* arrays and does not touch the
   arena's colour region, so nothing landed assembles `machChild`'s
   colouring.

The report accompanying this file records the seam hypotheses the
composition additionally needs (the channel pin `htabF j A = A.chan`,
the round-count pin `A.hist.length = j`, and the column-count pin
`ℓp (j+1) = ℓp j`), none of which `ChildLoadParts` currently carries.

## Hazards honoured

* Profiles are measured in **`preG`, before isolation**: nothing here
  moves the batch past `restrict`, and §1's identity is stated at
  `MArena.restrict`'s output, which is `preG`'s arena.
* The batch is the **padded** `batchFn` — §2 is stated at `pad`, width
  `S.width`, duplicates included.
* **Supports runs at radius `2R`.** `prepStageK` instantiates `bfsK`
  and `supportsK` at `2 * R`, never `S.R`.
* **Inherit-and-patch, one BFS.** §3 prices *one* BFS and *one*
  supports call. The per-round recompute described at
  `SolveMachPrep.lean:23-26` (a false docstring, corrected in place) is
  not priced, because it is not what the pass does.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.Driver

variable {L n₀ : ℕ}

/-! ## §1 The batch, read off the restricted child's channel row -/

section Batch

variable (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀) (π : Equiv.Perm (Fin A.N))
  (u : Fin A.N)

/-- The centre's own child name enumerates back to the centre: the
cluster's enumeration `restrictEmb` and the driver's compaction
bijection `childEquiv` are the same map (both `Driver.setEquiv` of the
cluster), so row `centreChild` of any restricted table is row `u` of the
parent's. -/
theorem restrictEmb_centreChild :
    Impl.restrictEmb (cluster S A π u) (centreChild S A π u) = u := by
  rw [Impl.restrictEmb_apply]
  show ((childEquiv S A π u)
    ((childEquiv S A π u).symm ⟨u, self_mem_cluster S A π u⟩) : Fin A.N) = u
  rw [Equiv.apply_symm_apply]

/-- The batch's trace on the child carrier, at the child's own names:
`A.up` is an embedding, so passing through the root names of
`batchRoot` is invisible. -/
theorem mem_batchSet_iff (a : Fin (childN S A π u)) :
    a ∈ batchSet S A π u ↔ ((childEquiv S A π u) a : Fin A.N) ∈ batchPar A u := by
  show A.up ((childEquiv S A π u) a : Fin A.N) ∈ ⇑A.up '' batchPar A u ↔ _
  exact A.up.injective.mem_set_image

/-- The centre's child name is the only one that enumerates to `u`. -/
theorem childEquiv_eq_centre_iff (a : Fin (childN S A π u)) :
    ((childEquiv S A π u) a : Fin A.N) = u ↔ a = centreChild S A π u := by
  constructor
  · intro h
    have : (childEquiv S A π u) a = ⟨u, self_mem_cluster S A π u⟩ := Subtype.ext h
    rw [show a = (childEquiv S A π u).symm ((childEquiv S A π u) a) from
      (Equiv.symm_apply_apply _ _).symm, this]
    rfl
  · rintro rfl
    show ((childEquiv S A π u)
      ((childEquiv S A π u).symm ⟨u, self_mem_cluster S A π u⟩) : Fin A.N) = u
    rw [Equiv.apply_symm_apply]

end Batch

open Classical in
/-- **Membership of a filtered channel row**, at local names: a local
name is in `filterMap (toLocal X)` of a list exactly when its parent
name is in the list. (`restrictEmb X a ∈ X` always, so the filter never
loses it.) -/
theorem mem_filterMap_toLocal {n : ℕ} (X : Set (Fin n)) (l : List (Fin n))
    (a : Fin X.ncard) :
    a ∈ l.filterMap (Impl.toLocal X) ↔ (Impl.restrictEmb X a : Fin n) ∈ l := by
  constructor
  · intro ha
    have hmem : (Impl.restrictEmb X a : Fin n)
        ∈ (l.filterMap (Impl.toLocal X)).map
            (fun b => (Impl.restrictEmb X b : Fin n)) :=
      List.mem_map.mpr ⟨a, ha, rfl⟩
    rw [Impl.map_restrictEmb_filterMap_toLocal X l] at hmem
    exact List.mem_of_mem_filter hmem
  · intro ha
    have hmemF : (Impl.restrictEmb X a : Fin n)
        ∈ l.filter (fun x => decide (x ∈ X)) :=
      List.mem_filter.mpr ⟨ha, by simp⟩
    rw [← Impl.map_restrictEmb_filterMap_toLocal X l] at hmemF
    obtain ⟨b, hb, hEq⟩ := List.mem_map.mp hmemF
    have hba : b = a := (Impl.restrictEmb X).injective hEq
    exact hba ▸ hb

section BatchRow

variable (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀) (π : Equiv.Perm (Fin A.N))
  (u : Fin A.N) {ℓpj : ℕ} (htab : Fin A.N → Fin ℓpj → List (Fin A.N))

/-- **Row `centreChild` of the restricted child's channel is row `u` of
the parent's, cut to the cluster** — `MArena.restrict`'s `hist` field
(`ImplRestrict.lean:161`) at `restrictEmb (cluster) centreChild = u`.
This is the row §5 line 19 reads (`B₀.hist[u][e]`): the pass never has
to reach back into the parent's region. -/
theorem restrict_hist_centreChild (e : Fin ℓpj) :
    ((Impl.ofArena A htab).restrict (cluster S A π u)).hist
        (centreChild S A π u) e
      = (htab u e).filterMap (Impl.toLocal (cluster S A π u)) := by
  show ((Impl.ofArena A htab).hist
      (Impl.restrictEmb (cluster S A π u) (centreChild S A π u)) e).filterMap
        (Impl.toLocal (cluster S A π u)) = _
  rw [restrictEmb_centreChild]
  rfl

/-- **§5 line 19, at the machine's objects**: the batch's trace on the
child carrier is `{centreChild} ∪ ⋃_{e < rounds} B₀.hist[centreChild][e]`
— a scan of the restricted child's own channel columns. Both hypotheses
are pins on `ProgDriver`'s free channel parameter: the region holds the
driver's channel on the rounds that carry data (`hchan`), and the arena
has no more rounds than the region has columns (`hlen`). -/
theorem mem_batchSet_iff_restrictHist
    (hlen : A.hist.length ≤ ℓpj)
    (hchan : ∀ (v : Fin A.N) (e : Fin ℓpj), (e : ℕ) < A.hist.length →
      htab v e = A.chan v (e : ℕ))
    (a : Fin (childN S A π u)) :
    a ∈ batchSet S A π u ↔
      a = centreChild S A π u ∨
        ∃ e : Fin ℓpj, (e : ℕ) < A.hist.length ∧
          a ∈ ((Impl.ofArena A htab).restrict (cluster S A π u)).hist
                (centreChild S A π u) e := by
  rw [mem_batchSet_iff]
  show (((childEquiv S A π u) a : Fin A.N) ∈ {u} ∪
      {z | ∃ e < A.hist.length, z ∈ A.chan u e}) ↔ _
  rw [Set.mem_union, Set.mem_singleton_iff, Set.mem_setOf_eq,
    childEquiv_eq_centre_iff]
  refine or_congr Iff.rfl ⟨?_, ?_⟩
  · rintro ⟨e, he, hz⟩
    refine ⟨⟨e, lt_of_lt_of_le he hlen⟩, he, ?_⟩
    rw [restrict_hist_centreChild S A π u htab,
      hchan u ⟨e, lt_of_lt_of_le he hlen⟩ he]
    exact (mem_filterMap_toLocal (cluster S A π u) (A.chan u e) a).mpr hz
  · rintro ⟨e, he, hz⟩
    rw [restrict_hist_centreChild S A π u htab, hchan u e he] at hz
    exact ⟨(e : ℕ), he,
      (mem_filterMap_toLocal (cluster S A π u) (A.chan u (e : ℕ)) a).mp hz⟩

end BatchRow

/-! ## §2 `batchFn` is the ascending enumeration, padded -/

/-- **The compaction bijection is ascending.** `Driver.setEquiv` is
`Finset.orderIsoOfFin` (F6c2's pin: the previous `equivFin` route was
`Classical`-chosen and no program could realize it), so slot `i` of a
padded batch is the `i`-th *smallest* member — which is what makes a
left-to-right carrier scan able to emit it. -/
theorem setEquiv_strictMono {k : ℕ} (X : Set (Fin k)) :
    StrictMono (fun i : Fin X.ncard => ((setEquiv X i : Fin k))) := by
  intro i j hij
  simp only [setEquiv, Equiv.trans_apply]
  simp only [Equiv.setCongr, Equiv.subtypeEquivProp, Equiv.subtypeEquiv_apply,
    Equiv.refl_apply, RelIso.coe_fn_toEquiv, finCongr_apply,
    OrderIso.lt_iff_lt, Subtype.coe_lt_coe]
  exact hij

/-- The enumeration is onto: every member has a local name. -/
theorem exists_setEquiv {k : ℕ} {X : Set (Fin k)} {y : Fin k} (hy : y ∈ X) :
    ∃ i : Fin X.ncard, (setEquiv X i : Fin k) = y :=
  ⟨(setEquiv X).symm ⟨y, hy⟩, by rw [Equiv.apply_symm_apply]⟩

/-- **The local name counts the members below it.** With the
enumeration ascending, the members strictly below `setEquiv X i` are
exactly `setEquiv X j` for `j < i`, so there are `i` of them. This is
the invariant a scan carries: the running count of members already
emitted is the slot the next member belongs in. -/
theorem ncard_lt_setEquiv {k : ℕ} (X : Set (Fin k)) (i : Fin X.ncard) :
    {y | y ∈ X ∧ y < (setEquiv X i : Fin k)}.ncard = (i : ℕ) := by
  have himg : {y | y ∈ X ∧ y < (setEquiv X i : Fin k)}
      = (fun j : Fin X.ncard => ((setEquiv X j : Fin k))) ''
          {j : Fin X.ncard | (j : ℕ) < (i : ℕ)} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨hyX, hlt⟩
      refine ⟨(setEquiv X).symm ⟨y, hyX⟩, ?_, by rw [Equiv.apply_symm_apply]⟩
      by_contra hge
      rw [not_lt] at hge
      have hle : ((setEquiv X i : Fin k)) ≤ y := by
        rcases Nat.eq_or_lt_of_le hge with h | h
        · have hi : i = (setEquiv X).symm ⟨y, hyX⟩ := Fin.ext h
          rw [hi, Equiv.apply_symm_apply]
        · have hs := setEquiv_strictMono X
            (show i < (setEquiv X).symm ⟨y, hyX⟩ from h)
          simp only [Equiv.apply_symm_apply] at hs
          exact le_of_lt hs
      exact absurd hlt (not_lt.mpr hle)
    · rintro ⟨j, hj, rfl⟩
      exact ⟨(setEquiv X j).2, setEquiv_strictMono X (show j < i from hj)⟩
  have hcount : ({j : Fin X.ncard | (j : ℕ) < (i : ℕ)}).ncard = (i : ℕ) := by
    have hinj : Set.InjOn Fin.val {j : Fin X.ncard | (j : ℕ) < (i : ℕ)} :=
      fun a _ b _ h => Fin.ext h
    have himg2 : (Fin.val '' {j : Fin X.ncard | (j : ℕ) < (i : ℕ)})
        = ↑(Finset.range (i : ℕ)) := by
      ext a
      simp only [Set.mem_image, Set.mem_setOf_eq, Finset.coe_range, Set.mem_Iio]
      exact ⟨by rintro ⟨b, hb, rfl⟩; exact hb,
        fun ha => ⟨⟨a, lt_trans ha i.2⟩, ha, rfl⟩⟩
    rw [← Set.InjOn.ncard_image hinj, himg2, Set.ncard_coe_finset,
      Finset.card_range]
  rw [himg, Set.ncard_image_of_injective _ (setEquiv_strictMono X).injective,
    hcount]

/-- **The slot the scan fills** (hazard 2's shape): a member with
exactly `c` members below it *is* padded slot `c`, provided the count
fits the width. The `else` branch of `pad` — the connector repeated
beyond the members — is untouched. -/
theorem pad_eq_of_ncard_lt {k mb : ℕ} {X : Set (Fin k)} {x₀ x : Fin k}
    (hx : x ∈ X) {c : ℕ} (hc : {y | y ∈ X ∧ y < x}.ncard = c) (hcmb : c < mb) :
    pad (mb := mb) X x₀ ⟨c, hcmb⟩ = x := by
  obtain ⟨i, hi⟩ := exists_setEquiv hx
  have hic : (i : ℕ) = c := by
    rw [← hc, ← hi, ncard_lt_setEquiv]
  have hlt : c < X.ncard := hic ▸ i.2
  show (if h : ((⟨c, hcmb⟩ : Fin mb) : ℕ) < X.ncard
    then (setEquiv X ⟨((⟨c, hcmb⟩ : Fin mb) : ℕ), h⟩ : Fin k) else x₀) = x
  rw [dif_pos hlt, show (⟨c, hlt⟩ : Fin X.ncard) = i from Fin.ext hic.symm, hi]

section BatchScan

variable (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀) (π : Equiv.Perm (Fin A.N))
  (u : Fin A.N)

/-- **`batchFn`'s slot `c`, from a scan.** Combined with §1: a scan of
the child carrier in increasing order, emitting each `a` whose parent
name lies in the channel row (or is the centre), fills `batchFn`'s slots
in order. The width bound `c < S.width` is the schedule's — `pad` is a
`Fin S.width` function, duplicates and all. -/
theorem batchFn_eq_of_ncard_lt {a : Fin (childN S A π u)}
    (ha : a ∈ batchSet S A π u) {c : ℕ}
    (hc : {y | y ∈ batchSet S A π u ∧ y < a}.ncard = c) (hcw : c < S.width) :
    batchFn S A π u ⟨c, hcw⟩ = a :=
  pad_eq_of_ncard_lt ha hc hcw

end BatchScan

/-! ## §3 The pass's stage budget, and its envelope -/

/-- **The five landed stage budgets, summed at the dimensions each stage
sees.** `dS` is the *parent* degree sum over the cluster and `k` the
cluster's size (`restrictK`'s own arguments — §6.1 charges parent
degrees, never `‖A[X_u]‖`); `cN`/`cns` are the **pre-isolation child**
`B₀`'s carrier and degree sum, which is what `bfsCom`, `supportsCom`,
`profilesCom` and `isolateCom` all run on; `mb` is the batch width
`S.width` and `Λc` the parent palette, so the profiles stage's class
count is `Λc + 1` (the marker's slot).

**One** BFS and **one** supports call, both at radius `2 * R` — §5 line
17's figure, never `S.R` — matching the inherit-and-patch channel
`Driver.childChan` writes: column `hist.length` from this round's walk,
every older column inherited through `restrict`'s filter. -/
def prepStageK (cN cns dS k Λc ℓp hb mb R : ℕ) : ℕ :=
  restrictK dS k Λc ℓp hb
    + bfsK cN cns (2 * R)
    + supportsK cN cns (2 * R)
    + profilesK mb (Λc + 1) cN cns R
    + isolateK cN cns

/-- The BFS at radius `2R`, closed against the child's weight. -/
theorem bfsK_two_mul_le (cN cns R : ℕ) :
    bfsK cN cns (2 * R) ≤ (76 * R + 15) * (cN + cns + 1) := by
  unfold bfsK
  nlinarith [Nat.zero_le R, Nat.zero_le cN, Nat.zero_le cns]

/-- The isolation, closed against the child's weight. -/
theorem isolateK_le (cN cns : ℕ) : isolateK cN cns ≤ 33 * (cN + cns + 1) := by
  unfold isolateK
  omega

/-- **The pass's budget fits §7's envelope.** The sum of the five stage
budgets is `restrictK` — §6.1's own column, whose per-node aggregate
`Σ_u Σ_{s∈X_u} deg_A(s) ≤ 2c_D‖A‖^{1+δ}` plus the channel copy is what
§7 puts in the leading coefficient `a := c + (2 + ℓ·R)·c_D` — plus a
**schedule constant** times the child's own weight `‖B₀‖ + 1`, which is
a term of §7's children column `c·Σ_u N_u`, closed by `(★)`. The
constant `800·(R+1)·(m + L + 2)` depends only on the schedule
(`R`, `S.width`, the palette), never on the input.

**No `A.N` term is introduced.** `restrictK`'s visible absence of one
(§6.1's scratch paragraph: a per-child carrier-sized wipe would make a
node `Θ(A.N²)`) survives the sum, because every other stage is priced at
the *child's* dimensions. -/
theorem prepStageK_le (cN cns dS k Λc ℓp hb mb R : ℕ) :
    prepStageK cN cns dS k Λc ℓp hb mb R
      ≤ restrictK dS k Λc ℓp hb
        + 800 * (R + 1) * (mb + Λc + 2) * (cN + cns + 1) := by
  have hb1 := bfsK_two_mul_le cN cns R
  have hb2 : supportsK cN cns (2 * R) ≤ (70 * R + 70) * (cN + cns + 1) := by
    have := supportsK_le cN cns (2 * R)
    calc supportsK cN cns (2 * R) ≤ 35 * (2 * R + 2) * (cN + cns + 1) := this
      _ = (70 * R + 70) * (cN + cns + 1) := by ring
  have hb3 : profilesK mb (Λc + 1) cN cns R
      ≤ (mb + (Λc + 1)) * (600 * (R + 1)) * (cN + cns + 1) := by
    have := profilesK_le mb (Λc + 1) cN cns R
    calc profilesK mb (Λc + 1) cN cns R
        ≤ (mb + (Λc + 1)) * (600 * (R + 1) * (cN + cns + 1)) := this
      _ = (mb + (Λc + 1)) * (600 * (R + 1)) * (cN + cns + 1) := by ring
  have hb4 := isolateK_le cN cns
  have hcoef : (76 * R + 15) + (70 * R + 70) + (mb + (Λc + 1)) * (600 * (R + 1))
      + 33 ≤ 800 * (R + 1) * (mb + Λc + 2) := by
    nlinarith [Nat.zero_le R, Nat.zero_le mb, Nat.zero_le Λc]
  calc prepStageK cN cns dS k Λc ℓp hb mb R
      ≤ restrictK dS k Λc ℓp hb
        + ((76 * R + 15) * (cN + cns + 1) + (70 * R + 70) * (cN + cns + 1)
          + (mb + (Λc + 1)) * (600 * (R + 1)) * (cN + cns + 1)
          + 33 * (cN + cns + 1)) := by
        unfold prepStageK
        omega
    _ = restrictK dS k Λc ℓp hb
        + ((76 * R + 15) + (70 * R + 70) + (mb + (Λc + 1)) * (600 * (R + 1))
          + 33) * (cN + cns + 1) := by ring
    _ ≤ restrictK dS k Λc ℓp hb
        + 800 * (R + 1) * (mb + Λc + 2) * (cN + cns + 1) :=
        Nat.add_le_add_left (Nat.mul_le_mul_right _ hcoef) _

end Lax3Proofs.Prog
