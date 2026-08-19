import Lax3Proofs.SolveBfs
import Lax3Proofs.ImplMultiSource

/-!
# F6c5 — the profilesMS stage as IMP+

§5 line 20 on the machine: from the pre-isolation child arena (`preG` —
**BEFORE `isolateCom`**, the campaign's oldest hazard) the stage leaves
the `mb + L` distance tables whose thresholded rows ARE the profile
slots: `mb` batch tables (`{z | Dp j z ≤ a}` is the `pd` slot `(j, a)`,
cumulative `≤ a`, never `= a`) and `L` virtual-source tables (`{z |
Dc c z.castSucc ≤ b + 1}` is the `pu` slot `(c, b)` — the `+1` is
`vsrc_withinDist_succ_iff`'s shift, landed; nothing here re-derives the
boundary). The assembled coloring is `Impl.recordProfilesMS` *by
definition of the seam* `Impl.ProfileTablesMS`, and the frozen identity
`recordProfilesMS_eq_childCol` lands it on `Driver.childCol` —
`profilesCom_spec_childCol` states both.

## The three routines

1. **`vsrcCom`** materializes the `vsrc H X` CSR on carrier `N + 1`
   from the child CSR and a class bit array: one offsets pass (`voff i
   = off i + cnt i`, the running member count as the prefix sum), one
   owner-advancing fill over the `ns` slots (each embedded row keeps
   its targets, a member's row gains the back-edge `N` at its end), a
   tail loop for the empty trailing rows, and the source-row pass (the
   members in increasing order — `Nodup` for free). The slot count is
   the honest `ns + 2·|X|`; the `vt` region's exact length is a
   precondition, exactly as `bfsCom` takes its region at exact length
   `N`. `vsrcCom_spec`'s postcondition is `GraphCsr vo vt (Impl.vsrc H
   X) (ns + 2·|X|)` — the seam `bfsCom_spec_graphCsr` consumes as its
   arena, so the colour half is *one* landed-BFS call per class from
   the source `Fin.last` (machine index `N`, the carrier cell's value)
   at radius `R + 1`.
2. **The batch half** is `mb` calls of the landed `bfsCom` on the child
   CSR at radius `R`, source loaded from the batch region (`batchFn`,
   padded — a duplicate costs another call, per E12d), each writing its
   own `pd j` region directly (`bfsCom` cleans the region it is handed,
   so no copy and no caller-side wipe).
3. **The marker class spends no BFS**: `markerCom` writes
   `Impl.markerTable` — source `0`, everything else `1` — in one `O(N)`
   pass; `markerTable_ballTable` is its whole discharge.

Empty classes need no branch: `vsrcCom` on an all-zero bit array builds
`vsrc H ∅` (isolated source) and the BFS leaves the sentinel table,
correct by the same generic spec.

## The regions

Per-class `vt` regions carry class-dependent exact lengths (`ns +
2·|X_c|`), so the class fold is *static* — one code copy per colour,
`E10`-conformant (the machine loops are over the carrier and the slots
only; the palette is schedule data). `pd`/`pu`/`vt` are name families
(`ProfNames`), their disjointness one `Ok` bundle that `lv`-style
names discharge. Scratch scalars are `pwScalars` (fresh prefix `"pw."`)
plus `bfsCom`'s own `bfScalars`.

## The budget (§6.3's two-term shape)

`profilesK mb L N ns R = mb · batchK + L · msK` — `profilesChargeMS`'s
`mb·callCost + L·callCostMS` shape verbatim, the marker's `markerK`
absorbed by its uniform `msK` slot (charging the free class a full call
only over-approximates, as `profilesChargeMS` itself does). Per stage:
`classBitsK` (the column extraction), `vsrcK = O(N + ns)` (the CSR
build — `O(N + M + |X|)` with `|X| ≤ N`), `bfsK` per call (landed),
`markerK = O(N)`. The closed envelope is
`profilesK_le : profilesK mb L N ns R ≤ (mb + L) · 600·(R+1)·(N+ns+1)`
— the machine mirror of `profilesChargeMS_le`'s
`(mb + L) · 6(R+1)(‖B₀‖+1)`.

Stored values, cited at the writes: distances `≤ R + 2` (`bfsCom`'s
sentinel at cap `R + 1`), CSR cells `≤ ns + 2N` (offsets) and `≤ N`
(targets), bits `≤ 1`, counters `≤ N` or `≤ ns + 2N` — all inside the
explicit `< B` hypotheses (`N·Λ < B` for the row-major colour reads,
`ns + 2N + 1 < B`, `R + 3 < B`), all `mcB`-shaped at schedule
constants.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax13Proofs.Codegen (arrOf_getD getD_eq_getElem)
open Lax3.ColoredGraphs (Coloring WithinDist)
open Lax3Proofs.WalkDistance

/-! ## §0 Small helpers -/

/-- A `getD` read in the `getElem?` form `evalB_get` consumes. -/
private theorem getElem?_getD {l : List ℕ} {k : ℕ} (h : k < l.length) :
    l[k]? = some (l.getD k 0) := by
  rw [List.getElem?_eq_getElem h, getD_eq_getElem h]

/-- Extending an array-as-function by its next cell. -/
private theorem arrOf_succ (n : ℕ) (f : ℕ → ℕ) :
    arrOf (n + 1) f = arrOf n f ++ [f n] := by
  simp [arrOf, List.range_succ]

/-! Deterministic single-step readings of an updated environment — the
`if`-free forms every state-reading line below rewrites with. -/

private theorem vars_setVar_self (σ : Env) (x : String) (v : ℕ) :
    (σ.setVar x v).vars x = v := by simp

private theorem vars_setVar_ne {x y : String} (h : y ≠ x) (σ : Env) (v : ℕ) :
    (σ.setVar x v).vars y = σ.vars y := by simp [h]

private theorem arrs_setArr_self (σ : Env) (a : String) (i v : ℕ) :
    (σ.setArr a i v).arrs a = (σ.arrs a).set i v := by simp

private theorem arrs_setArr_ne {a b : String} (h : b ≠ a) (σ : Env) (i v : ℕ) :
    (σ.setArr a i v).arrs b = σ.arrs b := by simp [h]

private theorem evalB_incr {B : ℕ} {x : String} {σ : Env}
    (hx : σ.vars x + 1 < B) :
    (Expr.add (.var x) (.lit 1)).evalB B σ = some (σ.vars x + 1) := by
  have h := evalB_bin (B := B) (op := .add) (e := .var x) (f := .lit 1) (σ := σ)
    (evalB_var (by omega)) (evalB_lit (by omega)) (by simpa using hx)
  simpa using h

/-! ### The indicator and its prefix sums -/

open Classical in
/-- The indicator of a vertex set, at machine indices. -/
noncomputable def xbit {N : ℕ} (X : Set (Fin N)) : ℕ → ℕ := fun v =>
  if h : v < N then (if (⟨v, h⟩ : Fin N) ∈ X then 1 else 0) else 0

/-- The number of members strictly below `i` — the offset shift of the
`vsrc` CSR. -/
noncomputable def xcnt {N : ℕ} (X : Set (Fin N)) (i : ℕ) : ℕ :=
  ∑ q ∈ Finset.range i, xbit X q

section Indicator

variable {N : ℕ} {X : Set (Fin N)}

theorem xbit_le_one (v : ℕ) : xbit X v ≤ 1 := by
  unfold xbit
  split <;> [split <;> omega; omega]

theorem xbit_eq_one_iff {v : ℕ} :
    xbit X v = 1 ↔ ∃ h : v < N, (⟨v, h⟩ : Fin N) ∈ X := by
  unfold xbit
  split
  · split
    · simp_all
    · simp_all
  · simp_all

@[simp] theorem xcnt_zero : xcnt X 0 = 0 := by simp [xcnt]

theorem xcnt_succ (i : ℕ) : xcnt X (i + 1) = xcnt X i + xbit X i :=
  Finset.sum_range_succ _ i

theorem xcnt_mono {i j : ℕ} (h : i ≤ j) : xcnt X i ≤ xcnt X j := by
  refine Finset.sum_le_sum_of_subset ?_
  intro x hx
  simp only [Finset.mem_range] at hx ⊢
  omega

theorem xcnt_le (i : ℕ) : xcnt X i ≤ i := by
  induction i with
  | zero => simp
  | succ i ih =>
    have := xbit_le_one (X := X) i
    rw [xcnt_succ]
    omega

/-- A member strictly below `N` leaves room above its own count: its
slot in the source row is inside the region. -/
theorem xcnt_lt_of_bit {v : ℕ} (hv : v < N) (h : xbit X v = 1) :
    xcnt X v < xcnt X N := by
  have h1 : xcnt X (v + 1) = xcnt X v + 1 := by rw [xcnt_succ, h]
  have h2 : xcnt X (v + 1) ≤ xcnt X N := xcnt_mono (by omega)
  omega

/-- The total count is the class's cardinality — what prices the `vt`
region's exact length. -/
theorem xcnt_eq_ncard (X : Set (Fin N)) : xcnt X N = X.ncard := by
  classical
  have h1 : xcnt X N = ∑ v : Fin N, xbit X (v : ℕ) :=
    (Fin.sum_univ_eq_sum_range (fun q => xbit X q) N).symm
  have h2 : ∀ v : Fin N, xbit X (v : ℕ) = if v ∈ X then 1 else 0 := by
    intro v
    by_cases hv : v ∈ X <;> simp [xbit, v.isLt, hv]
  rw [h1, Finset.sum_congr rfl fun v _ => h2 v, ← Finset.card_filter,
    Set.ncard_eq_toFinset_card']
  congr 1
  ext v
  simp

/-- The source row of the `vsrc` CSR: the members, in increasing
order. -/
noncomputable def memList {N : ℕ} (X : Set (Fin N)) : List ℕ :=
  (List.range N).filter (fun y => xbit X y == 1)

theorem length_memList_aux (i : ℕ) :
    (((List.range i).filter (fun y => xbit X y == 1))).length = xcnt X i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [List.range_succ, List.filter_append, List.length_append, ih, xcnt_succ]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (xbit_le_one (X := X) i)
      with h | h <;> simp [h]

theorem length_memList : (memList X).length = xcnt X N :=
  length_memList_aux N

theorem mem_memList {w : ℕ} : w ∈ memList X ↔ w < N ∧ xbit X w = 1 := by
  simp [memList]

theorem nodup_memList : (memList X).Nodup :=
  (List.nodup_range).filter _

end Indicator

/-! ## §1 Names and budgets -/

/-- The stage's own scratch cells; `bfsCom` brings `bfScalars` on top. -/
def pwScalars : List String := ["pw.i", "pw.k", "pw.t", "pw.u", "pw.j"]

/-- Every scalar the composed stage may write. -/
def profScalars : List String := pwScalars ++ bfScalars

/-- The stage's region names: the read-only arena (`oa`/`ta` the child
CSR, `ca` the colour rows, `ba` the padded batch) and its carrier/slot
cells, the two shared scratch regions, and the three name families —
`pd j` the batch tables, `vt c` the per-class `vsrc` target scratch
(class-dependent exact length, hence per class), `pu c` the
virtual-source tables (`pu Λ` the marker's). -/
structure ProfNames where
  /-- The child CSR offsets (read-only). -/
  oa : String
  /-- The child CSR targets (read-only). -/
  ta : String
  /-- The colour rows, row-major (read-only). -/
  ca : String
  /-- The padded batch region (read-only). -/
  ba : String
  /-- Scratch: one class's bit array. -/
  xb : String
  /-- Scratch: the `vsrc` offsets region. -/
  vo : String
  /-- The carrier cell. -/
  nN : String
  /-- The slot-count cell. -/
  nS : String
  /-- The batch distance tables, one per batch slot. -/
  pd : ℕ → String
  /-- The per-class `vsrc` target regions. -/
  vt : ℕ → String
  /-- The virtual-source distance tables, one per class. -/
  pu : ℕ → String

/-- The disjointness bundle: what keeps every write in its own region.
`mb` is the batch width, `L = Λ + 1` the palette with the marker
(classes `c < L - 1` get `vt`/BFS, class `L - 1` is the marker). All
clauses are `lv`-style-name dischargeable. -/
structure ProfNames.Ok (pn : ProfNames) (mb L : ℕ) : Prop where
  /-- The write targets avoid the four read-only regions. -/
  xb_ro : pn.xb ∉ [pn.oa, pn.ta, pn.ca, pn.ba]
  vo_ro : pn.vo ∉ [pn.oa, pn.ta, pn.ca, pn.ba]
  pd_ro : ∀ j < mb, pn.pd j ∉ [pn.oa, pn.ta, pn.ca, pn.ba]
  vt_ro : ∀ c, c + 1 < L → pn.vt c ∉ [pn.oa, pn.ta, pn.ca, pn.ba]
  pu_ro : ∀ c < L, pn.pu c ∉ [pn.oa, pn.ta, pn.ca, pn.ba]
  /-- Scratch distinctness. -/
  xb_vo : pn.xb ≠ pn.vo
  pd_xb : ∀ j < mb, pn.pd j ≠ pn.xb
  pd_vo : ∀ j < mb, pn.pd j ≠ pn.vo
  vt_xb : ∀ c, c + 1 < L → pn.vt c ≠ pn.xb
  vt_vo : ∀ c, c + 1 < L → pn.vt c ≠ pn.vo
  pu_xb : ∀ c < L, pn.pu c ≠ pn.xb
  pu_vo : ∀ c < L, pn.pu c ≠ pn.vo
  /-- The families: injective and pairwise disjoint. -/
  pd_inj : ∀ i < mb, ∀ j < mb, pn.pd i = pn.pd j → i = j
  pu_inj : ∀ i < L, ∀ j < L, pn.pu i = pn.pu j → i = j
  vt_inj : ∀ c, c + 1 < L → ∀ c', c' + 1 < L → pn.vt c = pn.vt c' → c = c'
  vt_pu : ∀ c, c + 1 < L → ∀ c' < L, pn.vt c ≠ pn.pu c'
  pd_pu : ∀ j < mb, ∀ c < L, pn.pd j ≠ pn.pu c
  pd_vt : ∀ j < mb, ∀ c, c + 1 < L → pn.pd j ≠ pn.vt c
  /-- The two cells stay off the stage's scratch scalars. -/
  nN_scr : pn.nN ∉ profScalars
  nS_scr : pn.nS ∉ profScalars

/-! The per-stage budgets. `bfsK` is the landed per-call BFS budget. -/

/-- Extracting one colour column into the bit array. -/
def classBitsK (N : ℕ) : ℕ := 16 * N + 6

/-- Materializing one `vsrc` CSR: `O(N + M + |X|)` at `|X| ≤ N`. -/
def vsrcK (N ns : ℕ) : ℕ := 100 * N + 21 * ns + 46

/-- One batch call: load the source, run the landed BFS at radius `R`. -/
def batchK (N ns R : ℕ) : ℕ := bfsK N ns R + 9

/-- One colour-class call, uniform over the classes: extract the
column, build the `vsrc` CSR, one landed BFS at radius `R + 1` on the
augmented arena (`≤ N + 1` vertices, `≤ ns + 2N` slots — the
`gsize_vsrc_le` shape at machine size). -/
def msK (N ns R : ℕ) : ℕ :=
  classBitsK N + vsrcK N ns + 14 + bfsK (N + 1) (ns + 2 * N) (R + 1)

/-- The marker's closed-form row: no BFS, one carrier pass. -/
def markerK (N : ℕ) : ℕ := 11 * N + 25

/-- **The stage's budget** — `profilesChargeMS`'s two-term
`mb·callCost + L·callCostMS` shape verbatim: `mb` batch calls, `L`
uniform class slots (the marker's free row rides in its slot). -/
def profilesK (mb L N ns R : ℕ) : ℕ :=
  mb * batchK N ns R + L * msK N ns R

/-- The marker's pass (and the fold's constant slack) fits inside one
uniform class slot — what lets `profilesK` keep the exact two-term
shape. -/
theorem markerK_add_lt_msK (N ns R : ℕ) : markerK N + 4 ≤ msK N ns R := by
  unfold markerK msK classBitsK vsrcK bfsK
  nlinarith

/-- **The closed envelope** — the machine mirror of
`profilesChargeMS_le`'s `(mb + L) · 6(R+1)(‖B₀‖+1)`. -/
theorem profilesK_le (mb L N ns R : ℕ) :
    profilesK mb L N ns R ≤ (mb + L) * (600 * (R + 1) * (N + ns + 1)) := by
  have hb : batchK N ns R ≤ 600 * (R + 1) * (N + ns + 1) := by
    have h := bfsK_le N ns R
    unfold batchK
    nlinarith
  have hm : msK N ns R ≤ 600 * (R + 1) * (N + ns + 1) := by
    have h := bfsK_le (N + 1) (ns + 2 * N) (R + 1)
    have h2 : 69 * (R + 1 + 1) * (N + 1 + (ns + 2 * N) + 1)
        ≤ 414 * (R + 1) * (N + ns + 1) := by nlinarith
    unfold msK classBitsK vsrcK
    nlinarith
  calc profilesK mb L N ns R
      ≤ mb * (600 * (R + 1) * (N + ns + 1)) + L * (600 * (R + 1) * (N + ns + 1)) :=
        Nat.add_le_add (Nat.mul_le_mul_left mb hb) (Nat.mul_le_mul_left L hm)
    _ = (mb + L) * (600 * (R + 1) * (N + ns + 1)) := (Nat.add_mul ..).symm

/-! ## §2 The colour column extraction -/

/-- Extract colour `c`'s column of the row-major colour region into the
bit array: `xb[i] := ca[i·Λ + c]`, one pass. -/
def classBitsCom (ca xb nN : String) (Λl c : ℕ) : Com :=
  .seq (.assign "pw.i" (.lit 0))
    (.while (.lt (.var "pw.i") (.var nN))
      (.seq (.store xb (.var "pw.i")
          (.get ca (.add (.mul (.var "pw.i") (.lit Λl)) (.lit c))))
        (.assign "pw.i" (.add (.var "pw.i") (.lit 1)))))

theorem wvars_classBitsCom (ca xb nN : String) (Λl c : ℕ) :
    (classBitsCom ca xb nN Λl c).wvars = ["pw.i", "pw.i"] := rfl

theorem warrs_classBitsCom (ca xb nN : String) (Λl c : ℕ) :
    (classBitsCom ca xb nN Λl c).warrs = [xb] := rfl

theorem noWrite_classBitsCom (ca xb nN : String) (Λl c : ℕ) :
    (classBitsCom ca xb nN Λl c).NoWrite := by
  simp [classBitsCom, Com.NoWrite]

theorem not_reads_classBitsCom (ca xb nN : String) (Λl c : ℕ) :
    ¬ (classBitsCom ca xb nN Λl c).reads := by
  simp [classBitsCom, Com.reads]

/-- **The extraction's spec**: from the colour region, the bit array of
class `c`. Stored values are bits (`≤ 1`); the read index `i·Λ + c <
N·Λ` is the row-major bound — the `< B` hypothesis is the `mcB`-shaped
one. -/
theorem classBitsCom_spec {B N Λl : ℕ} {col : Coloring N Λl}
    (ca xb nN : String) (c : Fin Λl)
    (hca_xb : ca ≠ xb) (hnN : nN ≠ "pw.i")
    (hNB : N < B) (hΛB : N * Λl < B) :
    Spec B
      (fun σ => ColBits ca col σ ∧ σ.vars nN = N ∧ (σ.arrs xb).length = N)
      (classBitsCom ca xb nN Λl (c : ℕ))
      (fun _ σ' => FinBits xb (col c) σ')
      (classBitsK N) := by
  classical
  set I : Env → Prop := fun σ =>
    ColBits ca col σ ∧ σ.vars nN = N ∧ σ.vars "pw.i" ≤ N ∧
      ∃ f, σ.arrs xb = arrOf N f ∧
        ∀ p < σ.vars "pw.i", f p = xbit (col c) p with hI
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "pw.i" < N)
      (.seq (.store xb (.var "pw.i")
          (.get ca (.add (.mul (.var "pw.i") (.lit Λl)) (.lit (c : ℕ)))))
        (.assign "pw.i" (.add (.var "pw.i") (.lit 1))))
      (fun σ σ' => I σ' ∧ σ'.vars "pw.i" = σ.vars "pw.i" + 1) 12 := by
    intro σ hσ
    obtain ⟨⟨hcb, hn, hiN, f, hf, hpre⟩, hlt⟩ := hσ
    set i := σ.vars "pw.i" with hi_def
    have hiB : i < B := by omega
    have hΛpos : 0 < Λl := c.pos
    have hmulN : i * Λl ≤ N * Λl := Nat.mul_le_mul_right _ (by omega)
    have hΛleN : Λl ≤ N * Λl := Nat.le_mul_of_pos_left Λl (by omega)
    have hidxB : i * Λl + (c : ℕ) < N * Λl := by
      have h1 : (i + 1) * Λl ≤ N * Λl := Nat.mul_le_mul_right _ (by omega)
      have h3 : i * Λl + Λl = (i + 1) * Λl := by ring
      have := c.isLt
      omega
    set bitv := (σ.arrs ca).getD (i * Λl + (c : ℕ)) 0 with hbitv
    have hbit : bitv = if (⟨i, hlt⟩ : Fin N) ∈ col c then 1 else 0 :=
      hcb.2 ⟨i, hlt⟩ c
    have hbitle : bitv ≤ 1 := by rw [hbit]; split <;> omega
    have hcalen : i * Λl + (c : ℕ) < (σ.arrs ca).length := by
      rw [hcb.1]; omega
    have hmul : (Expr.mul (.var "pw.i") (.lit Λl)).evalB B σ
        = some (i * Λl) := by
      have h := evalB_bin (B := B) (op := .mul) (e := .var "pw.i")
        (f := .lit Λl) (σ := σ) (evalB_var hiB) (evalB_lit (by omega))
        (by simp only [Bop.apply_mul, ← hi_def]; omega)
      simp only [Bop.apply_mul, ← hi_def] at h
      exact h
    have hidx : (Expr.add (.mul (.var "pw.i") (.lit Λl))
        (.lit (c : ℕ))).evalB B σ = some (i * Λl + (c : ℕ)) := by
      have hc := c.isLt
      have h := evalB_bin (B := B) (op := .add)
        (e := .mul (.var "pw.i") (.lit Λl)) (f := .lit (c : ℕ)) (σ := σ)
        hmul (evalB_lit (by omega)) (by simp only [Bop.apply_add]; omega)
      simp only [Bop.apply_add] at h
      exact h
    have hread : (Expr.get ca (.add (.mul (.var "pw.i") (.lit Λl))
        (.lit (c : ℕ)))).evalB B σ = some bitv :=
      evalB_get hidx (getElem?_getD hcalen) (by omega)
    have hstore : Run B (.store xb (.var "pw.i")
        (.get ca (.add (.mul (.var "pw.i") (.lit Λl)) (.lit (c : ℕ))))) σ
        (σ.setArr xb i bitv) 8 := by
      refine (Run.store (evalB_var hiB) hread ?_).mono (by simp)
      rw [hf, length_arrOf]
      exact hlt
    set σ₁ := σ.setArr xb i bitv with hσ₁
    have hinc : Run B (.assign "pw.i" (.add (.var "pw.i") (.lit 1)))
        σ₁ (σ₁.setVar "pw.i" (i + 1)) 4 := by
      have hσ₁i : σ₁.vars "pw.i" = i := by rw [hσ₁, vars_setArr]
      have hev := evalB_incr (B := B) (x := "pw.i") (σ := σ₁)
        (by rw [hσ₁i]; omega)
      rw [hσ₁i] at hev
      exact (Run.assign hev).mono (by simp)
    set σ' := σ₁.setVar "pw.i" (i + 1) with hσ'
    have h'i : σ'.vars "pw.i" = i + 1 := by rw [hσ', vars_setVar_self]
    have h'nN : σ'.vars nN = σ.vars nN := by
      rw [hσ', vars_setVar_ne hnN, hσ₁, vars_setArr]
    have h'ca : σ'.arrs ca = σ.arrs ca := by
      rw [hσ', arrs_setVar, hσ₁, arrs_setArr_ne hca_xb]
    have h'xb : σ'.arrs xb = (σ.arrs xb).set i bitv := by
      rw [hσ', arrs_setVar, hσ₁, arrs_setArr_self]
    refine ⟨σ', (hstore.seq hinc).mono (by omega),
      ⟨⟨by rw [h'ca]; exact hcb.1, fun v c' => by rw [h'ca]; exact hcb.2 v c'⟩,
        by rw [h'nN]; exact hn,
        by rw [h'i]; omega, ?_⟩, h'i⟩
    refine ⟨fun p => if p = i then bitv else f p, ?_, ?_⟩
    · rw [h'xb, hf, set_arrOf]
    · intro p hp
      rw [h'i] at hp
      show (if p = i then bitv else f p) = xbit (col c) p
      by_cases hpe : p = i
      · subst hpe
        rw [if_pos rfl, hbit]
        by_cases hmem : (⟨i, hlt⟩ : Fin N) ∈ col c <;>
          simp [xbit, hlt, hmem]
      · rw [if_neg hpe]
        exact hpre p (by omega)
  have hmain := Spec.forRangeZero (B := B) "pw.i" nN I N 12 hNB
    (fun σ hσ => hσ.2.2.1) (fun σ hσ => hσ.2.1) hbody
  refine ((hmain.pre ?_).post ?_).mono (by unfold classBitsK; omega)
  · rintro σ ⟨hcb, hn, hlen⟩
    refine ⟨⟨by simpa using hcb.1, fun v c' => by simpa using hcb.2 v c'⟩,
      by rw [vars_setVar_ne hnN]; exact hn,
      by rw [vars_setVar_self]; omega, ?_⟩
    refine ⟨fun p => (σ.arrs xb).getD p 0, ?_, ?_⟩
    · simp only [arrs_setVar]
      rw [← hlen]
      exact (arrOf_getD (σ.arrs xb)).symm
    · intro p hp
      rw [vars_setVar_self] at hp
      exact absurd hp (by omega)
  · rintro σ σ' hσ ⟨⟨hcb, hn, hiN, f, hf, hall⟩, hiv⟩
    refine ⟨by rw [hf, length_arrOf], fun v => ?_⟩
    rw [hf, getD_arrOf _ v.isLt, hall (v : ℕ) (by omega)]
    by_cases hv : v ∈ col c <;> simp [xbit, v.isLt, hv]

/-! ## §3 The marker's closed-form row (no BFS) -/

/-- Write `Impl.markerTable` — the source at `0`, everything else at
`1` — into the marker's table region: one carrier pass, no BFS
(`marker_pu_row`: the marker's rows are `univ` at every threshold, and
`markerTable_ballTable` is a valid `BallTable` for free). -/
def markerCom (pu nN : String) : Com :=
  .seq (.assign "pw.u" (.add (.var nN) (.lit 1)))
    (.seq (.seq (.assign "pw.i" (.lit 0))
      (.while (.lt (.var "pw.i") (.var "pw.u"))
        (.seq (.store pu (.var "pw.i") (.lit 1))
          (.assign "pw.i" (.add (.var "pw.i") (.lit 1))))))
      (.store pu (.var nN) (.lit 0)))

theorem wvars_markerCom (pu nN : String) :
    (markerCom pu nN).wvars = ["pw.u", "pw.i", "pw.i"] := rfl

theorem warrs_markerCom (pu nN : String) :
    (markerCom pu nN).warrs = [pu, pu] := rfl

theorem noWrite_markerCom (pu nN : String) : (markerCom pu nN).NoWrite := by
  simp [markerCom, Com.NoWrite]

theorem not_reads_markerCom (pu nN : String) : ¬ (markerCom pu nN).reads := by
  simp [markerCom, Com.reads]

/-- **The marker row, discharged without a BFS**: the region reads
exactly `Impl.markerTable N`. Stored values are `≤ 1`. -/
theorem markerCom_spec {B N : ℕ} (pu nN : String)
    (hnN1 : nN ≠ "pw.i") (hnN2 : nN ≠ "pw.u") (hNB : N + 2 < B) :
    Spec B
      (fun σ => σ.vars nN = N ∧ (σ.arrs pu).length = N + 1)
      (markerCom pu nN)
      (fun _ σ' => (σ'.arrs pu).length = N + 1 ∧
        ∀ v : Fin (N + 1), (σ'.arrs pu).getD (v : ℕ) 0 = Impl.markerTable N v)
      (markerK N) := by
  classical
  set I : Env → Prop := fun σ =>
    σ.vars nN = N ∧ σ.vars "pw.u" = N + 1 ∧ σ.vars "pw.i" ≤ N + 1 ∧
      ∃ f, σ.arrs pu = arrOf (N + 1) f ∧
        ∀ p < σ.vars "pw.i", f p = 1 with hI
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "pw.i" < N + 1)
      (.seq (.store pu (.var "pw.i") (.lit 1))
        (.assign "pw.i" (.add (.var "pw.i") (.lit 1))))
      (fun σ σ' => I σ' ∧ σ'.vars "pw.i" = σ.vars "pw.i" + 1) 7 := by
    intro σ hσ
    obtain ⟨⟨hn, hu, hiN, f, hf, hpre⟩, hlt⟩ := hσ
    set i := σ.vars "pw.i" with hi_def
    have hstore : Run B (.store pu (.var "pw.i") (.lit 1)) σ
        (σ.setArr pu i 1) 3 := by
      refine (Run.store (evalB_var (by omega)) (evalB_lit (by omega))
        ?_).mono (by simp)
      rw [hf, length_arrOf]
      exact hlt
    set σ₁ := σ.setArr pu i 1 with hσ₁
    have hinc : Run B (.assign "pw.i" (.add (.var "pw.i") (.lit 1)))
        σ₁ (σ₁.setVar "pw.i" (i + 1)) 4 := by
      have hσ₁i : σ₁.vars "pw.i" = i := by rw [hσ₁, vars_setArr]
      have hev := evalB_incr (B := B) (x := "pw.i") (σ := σ₁)
        (by rw [hσ₁i]; omega)
      rw [hσ₁i] at hev
      exact (Run.assign hev).mono (by simp)
    set σ' := σ₁.setVar "pw.i" (i + 1) with hσ'
    have h'i : σ'.vars "pw.i" = i + 1 := by rw [hσ', vars_setVar_self]
    have h'nN : σ'.vars nN = σ.vars nN := by
      rw [hσ', vars_setVar_ne hnN1, hσ₁, vars_setArr]
    have h'u : σ'.vars "pw.u" = σ.vars "pw.u" := by
      rw [hσ', vars_setVar_ne (by decide), hσ₁, vars_setArr]
    have h'pu : σ'.arrs pu = (σ.arrs pu).set i 1 := by
      rw [hσ', arrs_setVar, hσ₁, arrs_setArr_self]
    refine ⟨σ', (hstore.seq hinc).mono (by omega),
      ⟨by rw [h'nN]; exact hn, by rw [h'u]; exact hu,
        by rw [h'i]; omega, ?_⟩, h'i⟩
    refine ⟨fun p => if p = i then 1 else f p, ?_, ?_⟩
    · rw [h'pu, hf, set_arrOf]
    · intro p hp
      rw [h'i] at hp
      show (if p = i then 1 else f p) = 1
      by_cases hpe : p = i
      · rw [if_pos hpe]
      · rw [if_neg hpe]
        exact hpre p (by omega)
  have hloop := Spec.forRangeZero (B := B) "pw.i" "pw.u" I (N + 1) 7
    (by omega) (fun σ hσ => hσ.2.2.1) (fun σ hσ => hσ.2.1) hbody
  intro σ hσ
  obtain ⟨hn, hlen⟩ := hσ
  -- the header assignment
  have hass : Run B (.assign "pw.u" (.add (.var nN) (.lit 1))) σ
      (σ.setVar "pw.u" (N + 1)) 4 := by
    have hev : (Expr.add (.var nN) (.lit 1)).evalB B σ = some (N + 1) := by
      have h := evalB_bin (B := B) (op := .add) (e := .var nN) (f := .lit 1)
        (σ := σ) (evalB_var (by omega)) (evalB_lit (by omega))
        (by simp only [Bop.apply_add]; omega)
      rw [hn] at h
      simpa using h
    exact (Run.assign hev).mono (by simp)
  set σ₀ := σ.setVar "pw.u" (N + 1) with hσ₀
  -- the loop
  have hpre : I (σ₀.setVar "pw.i" 0) := by
    refine ⟨?_, ?_, by rw [vars_setVar_self]; omega, ?_⟩
    · rw [vars_setVar_ne hnN1, hσ₀, vars_setVar_ne hnN2]
      exact hn
    · rw [vars_setVar_ne (by decide), hσ₀, vars_setVar_self]
    · refine ⟨fun p => (σ.arrs pu).getD p 0, ?_, ?_⟩
      · simp only [arrs_setVar, hσ₀]
        rw [← hlen]
        exact (arrOf_getD (σ.arrs pu)).symm
      · intro p hp
        rw [vars_setVar_self] at hp
        exact absurd hp (by omega)
  obtain ⟨σ₁, hr1, hI1, hi1⟩ := hloop.run hpre
  obtain ⟨hn1, hu1, hiN1, f, hf, hall⟩ := hI1
  -- the final store at the source
  have hst : Run B (.store pu (.var nN) (.lit 0)) σ₁
      (σ₁.setArr pu N 0) 3 := by
    have hev : (Expr.var nN).evalB B σ₁ = some N := by
      rw [← hn1]
      exact evalB_var (by rw [hn1]; omega)
    refine (Run.store hev (evalB_lit (by omega)) ?_).mono (by simp)
    rw [hf, length_arrOf]
    omega
  refine ⟨σ₁.setArr pu N 0, ?_, ?_, ?_⟩
  · have h := hass.seq (hr1.seq hst)
    refine h.mono ?_
    unfold markerK
    have he : (7 + 4) * (N + 1) + 6 = 11 * N + 17 := by ring
    omega
  · rw [arrs_setArr_self, List.length_set, hf, length_arrOf]
  · intro v
    rw [arrs_setArr_self, hf, set_arrOf, getD_arrOf _ v.isLt]
    unfold Impl.markerTable
    by_cases hv : (v : ℕ) = N
    · rw [if_pos hv, if_pos (show v = Fin.last N from Fin.ext (by simpa using hv))]
    · rw [if_neg hv, if_neg (fun h => hv (by rw [h]; rfl)),
        hall (v : ℕ) (by omega)]

/-! ## §4 The `vsrc` CSR materialization

From the child CSR (`oa`/`ta`, functions `off`/`tgt`) and a class bit
array (`xb`, set `X`), build the CSR of `Impl.vsrc H X` on carrier
`N + 1` into `vo`/`vt`: offsets `voff i = off i + cnt i` (the running
member count shifts each row by the back-edges inserted before it),
rows `row i ++ [N]?` for the embedded vertices, the member list as the
source row. Slot count `ns + 2·|X|`, honest and exact. -/

/-- The `vsrc` CSR's offsets: the child offsets shifted by the member
count; the end of the source row last. -/
noncomputable def vsOff {N : ℕ} (off : ℕ → ℕ) (X : Set (Fin N)) (ns : ℕ) :
    ℕ → ℕ :=
  fun i => if i ≤ N then off i + xcnt X i else ns + 2 * xcnt X N

/-- Row `i < N` of the `vsrc` CSR is materialized in the cell function
`g`: the embedded targets at the shifted positions, the back-edge `N`
at the row's end when `i` is a member. -/
def VRowDone {N : ℕ} (off tgt : ℕ → ℕ) (X : Set (Fin N)) (i : ℕ)
    (g : ℕ → ℕ) : Prop :=
  (∀ q, off i ≤ q → q < off (i + 1) → g (q + xcnt X i) = tgt q) ∧
  (xbit X i = 1 → g (off (i + 1) + xcnt X i) = N)

section VsrcBuild

variable {B N ns : ℕ} {X : Set (Fin N)} {off tgt : ℕ → ℕ}
  {oa ta xb vo vt nN nS : String}

/-! ### §4a The offsets pass -/

/-- One turn of the offsets pass: `vo[i] := oa[i] + k`, `k += xb[i]`. -/
def vsOffBody (oa xb vo : String) : Com :=
  .seq (.store vo (.var "pw.i") (.add (.get oa (.var "pw.i")) (.var "pw.k")))
    (.seq (.assign "pw.k" (.add (.var "pw.k") (.get xb (.var "pw.i"))))
      (.assign "pw.i" (.add (.var "pw.i") (.lit 1))))

/-- The offsets pass over the embedded rows: `vo[i] := off i + cnt i`
for `i < N`, the member count left in `"pw.k"`. -/
def vsOffCom (oa xb vo nN : String) : Com :=
  .seq (.assign "pw.k" (.lit 0))
    (.seq (.assign "pw.i" (.lit 0))
      (.while (.lt (.var "pw.i") (.var nN)) (vsOffBody oa xb vo)))

/-- The offsets pass, discharged: writes `off i + cnt i` below `N`,
counts the members, leaves the CSR, the bits and the cells alone. -/
theorem vsOffCom_spec
    (hvo_oa : vo ≠ oa) (hvo_ta : vo ≠ ta) (hvo_xb : vo ≠ xb)
    (hnN_i : nN ≠ "pw.i") (hnN_k : nN ≠ "pw.k")
    (hnS_i : nS ≠ "pw.i") (hnS_k : nS ≠ "pw.k")
    (hNB : N + 2 < B) (hnsB : ns + 2 * N + 1 < B) :
    Spec B
      (fun σ => Csr oa ta N ns N off tgt σ ∧ FinBits xb X σ ∧
        σ.vars nN = N ∧ σ.vars nS = ns ∧ (σ.arrs vo).length = N + 2)
      (vsOffCom oa xb vo nN)
      (fun _ σ' => Csr oa ta N ns N off tgt σ' ∧ FinBits xb X σ' ∧
        σ'.vars nN = N ∧ σ'.vars nS = ns ∧ σ'.vars "pw.k" = xcnt X N ∧
        ∃ f, σ'.arrs vo = arrOf (N + 2) f ∧
          ∀ p < N, f p = off p + xcnt X p)
      (19 * N + 8) := by
  classical
  set I : Env → Prop := fun σ =>
    Csr oa ta N ns N off tgt σ ∧ FinBits xb X σ ∧
      σ.vars nN = N ∧ σ.vars nS = ns ∧ σ.vars "pw.i" ≤ N ∧
      σ.vars "pw.k" = xcnt X (σ.vars "pw.i") ∧
      ∃ f, σ.arrs vo = arrOf (N + 2) f ∧
        ∀ p < σ.vars "pw.i", f p = off p + xcnt X p with hI
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "pw.i" < N)
      (vsOffBody oa xb vo)
      (fun σ σ' => I σ' ∧ σ'.vars "pw.i" = σ.vars "pw.i" + 1) 15 := by
    intro σ hσ
    obtain ⟨⟨hc, hxb, hn, hs, hiN, hk, f, hf, hpre⟩, hlt⟩ := hσ
    set i := σ.vars "pw.i" with hi_def
    have hiB : i < B := by omega
    have hoffi : (σ.arrs oa).getD i 0 = off i := hc.getD_off (by omega)
    have hoffiB : off i ≤ ns := hc.le_ns (by omega)
    have hkN : σ.vars "pw.k" ≤ N := by
      rw [hk]
      exact le_trans (xcnt_le _) hiN
    -- the store `vo[i] := oa[i] + k`
    have hoalen : i < (σ.arrs oa).length := by rw [hc.length_off]; omega
    have hval : (Expr.add (.get oa (.var "pw.i")) (.var "pw.k")).evalB B σ
        = some (off i + σ.vars "pw.k") := by
      have hget : (Expr.get oa (.var "pw.i")).evalB B σ = some (off i) := by
        have h := evalB_get (i := Expr.var "pw.i") (evalB_var hiB)
          (getElem?_getD hoalen) (by rw [hoffi]; omega)
        rwa [hoffi] at h
      have h := evalB_bin (B := B) (op := .add) hget
        (evalB_var (x := "pw.k") (by omega))
        (by simp only [Bop.apply_add]; omega)
      simp only [Bop.apply_add] at h
      exact h
    have hstore : Run B
        (.store vo (.var "pw.i") (.add (.get oa (.var "pw.i")) (.var "pw.k")))
        σ (σ.setArr vo i (off i + σ.vars "pw.k")) 6 := by
      refine (Run.store (evalB_var hiB) hval ?_).mono (by simp)
      rw [hf, length_arrOf]
      omega
    set σ₁ := σ.setArr vo i (off i + σ.vars "pw.k") with hσ₁
    -- the count update `k += xb[i]`
    have hbitval : (σ.arrs xb).getD i 0 = xbit X i := by
      have h := hxb.2 ⟨i, hlt⟩
      rw [h]
      by_cases hm : (⟨i, hlt⟩ : Fin N) ∈ X <;> simp [xbit, hlt, hm]
    have hxblen : i < (σ.arrs xb).length := by rw [hxb.1]; omega
    have hbB : xbit X i ≤ 1 := xbit_le_one i
    have hkval : (Expr.add (.var "pw.k") (.get xb (.var "pw.i"))).evalB B σ₁
        = some (σ.vars "pw.k" + xbit X i) := by
      have h1k : σ₁.vars "pw.k" = σ.vars "pw.k" := by rw [hσ₁, vars_setArr]
      have h1i : σ₁.vars "pw.i" = i := by rw [hσ₁, vars_setArr]
      have h1xb : σ₁.arrs xb = σ.arrs xb := by
        rw [hσ₁, arrs_setArr_ne (Ne.symm hvo_xb)]
      have hvi : (Expr.var "pw.i").evalB B σ₁ = some i := by
        have h := evalB_var (B := B) (x := "pw.i") (σ := σ₁) (by rw [h1i]; omega)
        rwa [h1i] at h
      have hget : (Expr.get xb (.var "pw.i")).evalB B σ₁ = some (xbit X i) := by
        refine evalB_get hvi ?_ (by omega)
        rw [h1xb, ← hbitval]
        exact getElem?_getD hxblen
      have hvk : (Expr.var "pw.k").evalB B σ₁ = some (σ.vars "pw.k") := by
        have h := evalB_var (B := B) (x := "pw.k") (σ := σ₁) (by rw [h1k]; omega)
        rwa [h1k] at h
      have h := evalB_bin (B := B) (op := .add) hvk hget
        (by simp only [Bop.apply_add]; omega)
      simp only [Bop.apply_add] at h
      exact h
    have hkassign : Run B (.assign "pw.k" (.add (.var "pw.k") (.get xb (.var "pw.i"))))
        σ₁ (σ₁.setVar "pw.k" (σ.vars "pw.k" + xbit X i)) 5 :=
      (Run.assign hkval).mono (by simp)
    set σ₂ := σ₁.setVar "pw.k" (σ.vars "pw.k" + xbit X i) with hσ₂
    -- the counter
    have hinc : Run B (.assign "pw.i" (.add (.var "pw.i") (.lit 1)))
        σ₂ (σ₂.setVar "pw.i" (i + 1)) 4 := by
      have h2i : σ₂.vars "pw.i" = i := by
        rw [hσ₂, vars_setVar_ne (by decide), hσ₁, vars_setArr]
      have hev := evalB_incr (B := B) (x := "pw.i") (σ := σ₂)
        (by rw [h2i]; omega)
      rw [h2i] at hev
      exact (Run.assign hev).mono (by simp)
    set σ' := σ₂.setVar "pw.i" (i + 1) with hσ'
    have h'i : σ'.vars "pw.i" = i + 1 := by rw [hσ', vars_setVar_self]
    have h'k : σ'.vars "pw.k" = σ.vars "pw.k" + xbit X i := by
      rw [hσ', vars_setVar_ne (by decide), hσ₂, vars_setVar_self]
    have h'nN : σ'.vars nN = σ.vars nN := by
      rw [hσ', vars_setVar_ne hnN_i, hσ₂, vars_setVar_ne hnN_k, hσ₁, vars_setArr]
    have h'nS : σ'.vars nS = σ.vars nS := by
      rw [hσ', vars_setVar_ne hnS_i, hσ₂, vars_setVar_ne hnS_k, hσ₁, vars_setArr]
    have h'arr : ∀ b, b ≠ vo → σ'.arrs b = σ.arrs b := by
      intro b hb
      rw [hσ', arrs_setVar, hσ₂, arrs_setVar, hσ₁, arrs_setArr_ne hb]
    have h'vo : σ'.arrs vo = (σ.arrs vo).set i (off i + σ.vars "pw.k") := by
      rw [hσ', arrs_setVar, hσ₂, arrs_setVar, hσ₁, arrs_setArr_self]
    refine ⟨σ', (hstore.seq (hkassign.seq hinc)).mono (by omega),
      ⟨hc.of_eq (h'arr oa (Ne.symm hvo_oa)) (h'arr ta (Ne.symm hvo_ta)),
        ⟨by rw [h'arr xb (Ne.symm hvo_xb)]; exact hxb.1,
          fun v => by rw [h'arr xb (Ne.symm hvo_xb)]; exact hxb.2 v⟩,
        by rw [h'nN]; exact hn, by rw [h'nS]; exact hs,
        by rw [h'i]; omega,
        by rw [h'k, h'i, hk, xcnt_succ], ?_⟩, h'i⟩
    refine ⟨fun p => if p = i then off i + σ.vars "pw.k" else f p, ?_, ?_⟩
    · rw [h'vo, hf, set_arrOf]
    · intro p hp
      rw [h'i] at hp
      show (if p = i then off i + σ.vars "pw.k" else f p) = off p + xcnt X p
      by_cases hpe : p = i
      · subst hpe
        rw [if_pos rfl, hk]
      · rw [if_neg hpe]
        exact hpre p (by omega)
  have hmain := Spec.forRangeZero (B := B) "pw.i" nN I N 15 (by omega)
    (fun σ hσ => hσ.2.2.2.2.1) (fun σ hσ => hσ.2.2.1) hbody
  -- assemble with the `k := 0` header
  intro σ hσ
  obtain ⟨hc, hxb, hn, hs, hlen⟩ := hσ
  have hk0 : Run B (.assign "pw.k" (.lit 0)) σ (σ.setVar "pw.k" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  set σ₀ := σ.setVar "pw.k" 0 with hσ₀
  have hpre : I (σ₀.setVar "pw.i" 0) := by
    refine ⟨(hc.setVar _ _).setVar _ _,
      ⟨by simpa using hxb.1, fun v => by simpa using hxb.2 v⟩,
      ?_, ?_, by rw [vars_setVar_self]; omega, ?_, ?_⟩
    · rw [vars_setVar_ne hnN_i, hσ₀, vars_setVar_ne hnN_k]
      exact hn
    · rw [vars_setVar_ne hnS_i, hσ₀, vars_setVar_ne hnS_k]
      exact hs
    · rw [vars_setVar_ne (by decide), hσ₀, vars_setVar_self, vars_setVar_self]
      simp
    · refine ⟨fun p => (σ.arrs vo).getD p 0, ?_, ?_⟩
      · simp only [arrs_setVar, hσ₀]
        rw [← hlen]
        exact (arrOf_getD (σ.arrs vo)).symm
      · intro p hp
        rw [vars_setVar_self] at hp
        exact absurd hp (by omega)
  obtain ⟨σ', hr, hI', hi'⟩ := hmain.run hpre
  obtain ⟨hc', hxb', hn', hs', hi'N, hk', f, hf, hall⟩ := hI'
  refine ⟨σ', (hk0.seq hr).mono (by omega), hc', hxb', hn', hs', ?_, f, hf, ?_⟩
  · rw [hk', hi']
  · intro p hp
    exact hall p (by omega)

end VsrcBuild

/-! ### §4b The fill pass: one owner-advancing scan over the slots -/

/-- Transporting a done row across a write that misses it: the embedded
positions and (when the row has one) the back-edge position each agree. -/
private theorem vrowdone_of_agree {N : ℕ} {off tgt : ℕ → ℕ} {X : Set (Fin N)}
    {i : ℕ} {g g' : ℕ → ℕ} (h : VRowDone off tgt X i g)
    (hemb : ∀ q, off i ≤ q → q < off (i + 1) →
      g' (q + xcnt X i) = g (q + xcnt X i))
    (hback : xbit X i = 1 →
      g' (off (i + 1) + xcnt X i) = g (off (i + 1) + xcnt X i)) :
    VRowDone off tgt X i g' :=
  ⟨fun q h1 h2 => by rw [hemb q h1 h2]; exact h.1 q h1 h2,
   fun hb => by rw [hback hb]; exact h.2 hb⟩

/-- One turn of the fill: inside the owner's row, copy the slot to its
shifted position; at the row's end, write the back-edge if the owner is
a member (advancing the running count), and move the owner on. -/
def vsFillTurn (oa ta xb vt nN : String) : Com :=
  .ite (.lt (.var "pw.j") (.get oa (.add (.var "pw.u") (.lit 1))))
    (.seq (.store vt (.add (.var "pw.j") (.var "pw.k")) (.get ta (.var "pw.j")))
      (.assign "pw.j" (.add (.var "pw.j") (.lit 1))))
    (.seq (.ite (.eq (.get xb (.var "pw.u")) (.lit 1))
        (.seq (.store vt
            (.add (.get oa (.add (.var "pw.u") (.lit 1))) (.var "pw.k"))
            (.var nN))
          (.assign "pw.k" (.add (.var "pw.k") (.lit 1))))
        .skip)
      (.assign "pw.u" (.add (.var "pw.u") (.lit 1))))

/-- The fill pass's invariant: the inputs, the cells, the owner
discipline (`off u ≤ j ≤ off (u+1)`), the count tracking the owner, and
the materialized prefix — every row below the owner done, the owner's
row done below the slot pointer. -/
def FillInv (oa ta xb vt nN nS : String) {N : ℕ} (ns : ℕ)
    (off tgt : ℕ → ℕ) (X : Set (Fin N)) (σ : Env) : Prop :=
  Csr oa ta N ns N off tgt σ ∧ FinBits xb X σ ∧
    σ.vars nN = N ∧ σ.vars nS = ns ∧ σ.vars "pw.t" = xcnt X N ∧
    σ.vars "pw.u" ≤ N ∧ σ.vars "pw.j" ≤ ns ∧
    off (σ.vars "pw.u") ≤ σ.vars "pw.j" ∧
    (σ.vars "pw.u" < N → σ.vars "pw.j" ≤ off (σ.vars "pw.u" + 1)) ∧
    σ.vars "pw.k" = xcnt X (σ.vars "pw.u") ∧
    ∃ g, σ.arrs vt = arrOf (ns + 2 * xcnt X N) g ∧
      (∀ i < σ.vars "pw.u", VRowDone off tgt X i g) ∧
      (∀ q, off (σ.vars "pw.u") ≤ q → q < σ.vars "pw.j" →
        g (q + xcnt X (σ.vars "pw.u")) = tgt q)

section VsrcBuild2

variable {B N ns : ℕ} {X : Set (Fin N)} {off tgt : ℕ → ℕ}
  {oa ta xb vo vt nN nS : String}

variable (hvt_oa : vt ≠ oa) (hvt_ta : vt ≠ ta) (hvt_xb : vt ≠ xb)
  (hnN_scr : nN ∉ pwScalars) (hnS_scr : nS ∉ pwScalars)
  (hNB : N + 2 < B) (hnsB : ns + 2 * N + 1 < B)

include hvt_oa hvt_ta hvt_xb hnN_scr hnS_scr hNB hnsB in
/-- **One turn of the fill**, in `ownerScan_spec`'s step form. -/
theorem vsFillTurn_step :
    ∀ σ, FillInv oa ta xb vt nN nS ns off tgt X σ → σ.vars "pw.j" < ns →
      ∃ σ' K', Run B (vsFillTurn oa ta xb vt nN) σ σ' K' ∧
        FillInv oa ta xb vt nN nS ns off tgt X σ' ∧
        σ.vars "pw.j" ≤ σ'.vars "pw.j" ∧ σ.vars "pw.u" ≤ σ'.vars "pw.u" ∧
        (σ.vars "pw.j" < σ'.vars "pw.j" ∨ σ.vars "pw.u" < σ'.vars "pw.u") ∧
        K' ≤ 17 * (σ'.vars "pw.j" - σ.vars "pw.j")
          + 28 * (σ'.vars "pw.u" - σ.vars "pw.u") := by
  have hnN_j : nN ≠ "pw.j" := fun h => hnN_scr (by rw [h]; decide)
  have hnN_k : nN ≠ "pw.k" := fun h => hnN_scr (by rw [h]; decide)
  have hnN_u : nN ≠ "pw.u" := fun h => hnN_scr (by rw [h]; decide)
  have hnN_t : nN ≠ "pw.t" := fun h => hnN_scr (by rw [h]; decide)
  have hnS_j : nS ≠ "pw.j" := fun h => hnS_scr (by rw [h]; decide)
  have hnS_k : nS ≠ "pw.k" := fun h => hnS_scr (by rw [h]; decide)
  have hnS_u : nS ≠ "pw.u" := fun h => hnS_scr (by rw [h]; decide)
  have hnS_t : nS ≠ "pw.t" := fun h => hnS_scr (by rw [h]; decide)
  rintro σ ⟨hc, hxb, hn, hs, ht, hu, hj, hlo, hhi, hk, g, hg, hdone, hpart⟩ hjns
  have huN : σ.vars "pw.u" < N := hc.owner_lt hu hlo hjns
  set u := σ.vars "pw.u" with hu_def
  set j := σ.vars "pw.j" with hj_def
  have hoffu1 : off (u + 1) ≤ ns := hc.le_ns (by omega)
  have hxcu : xcnt X u ≤ xcnt X N := xcnt_mono (by omega)
  have hxcuN : xcnt X u ≤ N := le_trans (xcnt_le u) (by omega)
  have hlen_vt : (σ.arrs vt).length = ns + 2 * xcnt X N := by
    rw [hg, length_arrOf]
  -- the outer test `j < oa[u+1]`
  have hoffval : (Expr.get oa (.add (.var "pw.u") (.lit 1))).evalB B σ
      = some (off (u + 1)) := by
    refine evalB_get (k := u + 1) (evalB_incr (by omega)) ?_
      (hc.off_lt (by omega) (by omega))
    rw [hc.offArr, getElem?_arrOf off (by omega)]
  have hcond := evalB_condLt (evalB_var (x := "pw.j") (σ := σ) (by omega)) hoffval
  by_cases hslot : j < off (u + 1)
  · -- inside the row: copy the slot to its shifted position
    have hcondT : (Cond.lt (.var "pw.j")
        (.get oa (.add (.var "pw.u") (.lit 1)))).evalB B σ = some true := by
      rw [hcond]
      congr 1
      simpa using hslot
    set wpos := j + xcnt X u with hwpos
    have hidxval : (Expr.add (.var "pw.j") (.var "pw.k")).evalB B σ
        = some wpos := by
      have h := evalB_bin (B := B) (op := .add)
        (evalB_var (x := "pw.j") (σ := σ) (by omega))
        (evalB_var (x := "pw.k") (σ := σ) (by rw [hk]; omega))
        (by simp only [Bop.apply_add]; rw [hk]; omega)
      simp only [Bop.apply_add] at h
      rw [hk] at h
      exact h
    have htgtj : (σ.arrs ta).getD j 0 = tgt j := hc.getD_tgt hjns
    have htgtjN : tgt j < N := hc.target hjns
    have hval : (Expr.get ta (.var "pw.j")).evalB B σ = some (tgt j) := by
      refine evalB_get (evalB_var (by omega)) ?_ (by omega)
      rw [← htgtj]
      exact getElem?_getD (by rw [hc.length_tgt]; omega)
    have hstore : Run B (.store vt (.add (.var "pw.j") (.var "pw.k"))
        (.get ta (.var "pw.j"))) σ (σ.setArr vt wpos (tgt j)) 6 :=
      (Run.store hidxval hval (by rw [hlen_vt, hwpos]; omega)).mono (by simp)
    set σ₁ := σ.setArr vt wpos (tgt j) with hσ₁
    have hinc : Run B (.assign "pw.j" (.add (.var "pw.j") (.lit 1)))
        σ₁ (σ₁.setVar "pw.j" (j + 1)) 4 := by
      have h1j : σ₁.vars "pw.j" = j := by rw [hσ₁, vars_setArr]
      have hev := evalB_incr (B := B) (x := "pw.j") (σ := σ₁)
        (by rw [h1j]; omega)
      rw [h1j] at hev
      exact (Run.assign hev).mono (by simp)
    set σ' := σ₁.setVar "pw.j" (j + 1) with hσ'
    have hrun : Run B (vsFillTurn oa ta xb vt nN) σ σ' 17 :=
      (Run.ite_true hcondT (hstore.seq hinc)).mono (by simp)
    have h'j : σ'.vars "pw.j" = j + 1 := by rw [hσ', vars_setVar_self]
    have h'vars : ∀ y, y ≠ "pw.j" → σ'.vars y = σ.vars y := by
      intro y hy
      rw [hσ', vars_setVar_ne hy, hσ₁, vars_setArr]
    have h'arr : ∀ b, b ≠ vt → σ'.arrs b = σ.arrs b := by
      intro b hb
      rw [hσ', arrs_setVar, hσ₁, arrs_setArr_ne hb]
    have h'vt : σ'.arrs vt = (σ.arrs vt).set wpos (tgt j) := by
      rw [hσ', arrs_setVar, hσ₁, arrs_setArr_self]
    set g' : ℕ → ℕ := fun p => if p = wpos then tgt j else g p with hg'
    have hg'arr : σ'.arrs vt = arrOf (ns + 2 * xcnt X N) g' := by
      rw [h'vt, hg, set_arrOf]
    have hg'ne : ∀ p, p ≠ wpos → g' p = g p := by
      intro p hp
      show (if p = wpos then tgt j else g p) = g p
      rw [if_neg hp]
    have hg'w : g' wpos = tgt j := by
      show (if wpos = wpos then tgt j else g wpos) = tgt j
      rw [if_pos rfl]
    refine ⟨σ', 17, hrun,
      ⟨hc.of_eq (h'arr oa (Ne.symm hvt_oa)) (h'arr ta (Ne.symm hvt_ta)),
        ⟨by rw [h'arr xb (Ne.symm hvt_xb)]; exact hxb.1,
          fun v => by rw [h'arr xb (Ne.symm hvt_xb)]; exact hxb.2 v⟩,
        by rw [h'vars nN hnN_j]; exact hn,
        by rw [h'vars nS hnS_j]; exact hs,
        by rw [h'vars "pw.t" (by decide)]; exact ht,
        by rw [h'vars "pw.u" (by decide)]; exact hu,
        by rw [h'j]; omega,
        by rw [h'vars "pw.u" (by decide), h'j, ← hu_def]; omega,
        by rw [h'vars "pw.u" (by decide), h'j, ← hu_def]; intro h; omega,
        by rw [h'vars "pw.k" (by decide), h'vars "pw.u" (by decide)]; exact hk,
        g', hg'arr, ?_, ?_⟩,
      by rw [h'j]; omega,
      by rw [h'vars "pw.u" (by decide)],
      by rw [h'j]; omega,
      by rw [h'j, h'vars "pw.u" (by decide)]; omega⟩
    · -- rows below the owner survive the write
      rw [h'vars "pw.u" (by decide)]
      intro i hi
      have hoffi1u : off (i + 1) ≤ off u := hc.mono (by omega) (by omega)
      have hxci : xcnt X i ≤ xcnt X u := xcnt_mono (by omega)
      refine vrowdone_of_agree (hdone i hi) ?_ ?_
      · intro q h1 h2
        refine hg'ne _ ?_
        rw [hwpos]
        omega
      · intro hb
        refine hg'ne _ ?_
        have hxci1 : xcnt X (i + 1) ≤ xcnt X u := xcnt_mono (by omega)
        rw [xcnt_succ, hb] at hxci1
        rw [hwpos]
        omega
    · -- the owner's partial row gains the slot
      rw [h'vars "pw.u" (by decide), h'j, ← hu_def]
      intro q h1 h2
      rcases Nat.lt_or_ge q j with hq | hq
      · rw [hg'ne _ (by rw [hwpos]; omega)]
        exact hpart q h1 hq
      · have hqj : q = j := by omega
        subst hqj
        exact hg'w
  · -- the row's end: back-edge if the owner is a member, owner moves on
    have hcondF : (Cond.lt (.var "pw.j")
        (.get oa (.add (.var "pw.u") (.lit 1)))).evalB B σ = some false := by
      rw [hcond]
      congr 1
      simpa using hslot
    have hjeq : j = off (u + 1) := by
      have := hhi huN
      omega
    have hbitval : (σ.arrs xb).getD u 0 = xbit X u := by
      have h := hxb.2 ⟨u, huN⟩
      rw [h]
      by_cases hm : (⟨u, huN⟩ : Fin N) ∈ X <;> simp [xbit, huN, hm]
    have hbitle : xbit X u ≤ 1 := xbit_le_one u
    have hbev : (Cond.eq (.get xb (.var "pw.u")) (.lit 1)).evalB B σ
        = some (xbit X u == 1) := by
      refine evalB_condEq ?_ (evalB_lit (by omega))
      refine evalB_get (evalB_var (by omega)) ?_ (by omega)
      rw [← hbitval]
      exact getElem?_getD (by rw [hxb.1]; omega)
    by_cases hbit : xbit X u = 1
    · -- a member: write the back-edge at the row's end, count up
      have hbevT : (Cond.eq (.get xb (.var "pw.u")) (.lit 1)).evalB B σ
          = some true := by
        rw [hbev, hbit]
        rfl
      set wpos := off (u + 1) + xcnt X u with hwpos
      have hxltN : xcnt X u < xcnt X N := xcnt_lt_of_bit huN hbit
      have hidxval : (Expr.add (.get oa (.add (.var "pw.u") (.lit 1)))
          (.var "pw.k")).evalB B σ = some wpos := by
        have h := evalB_bin (B := B) (op := .add) hoffval
          (evalB_var (x := "pw.k") (σ := σ) (by rw [hk]; omega))
          (by simp only [Bop.apply_add]; rw [hk]; omega)
        simp only [Bop.apply_add] at h
        rw [hk] at h
        exact h
      have hnval : (Expr.var nN).evalB B σ = some N := by
        have h := evalB_var (B := B) (x := nN) (σ := σ) (by rw [hn]; omega)
        rwa [hn] at h
      have hstore : Run B (.store vt
          (.add (.get oa (.add (.var "pw.u") (.lit 1))) (.var "pw.k"))
          (.var nN)) σ (σ.setArr vt wpos N) 8 :=
        (Run.store hidxval hnval (by rw [hlen_vt, hwpos]; omega)).mono (by simp)
      set σ₁ := σ.setArr vt wpos N with hσ₁
      have hkinc : Run B (.assign "pw.k" (.add (.var "pw.k") (.lit 1)))
          σ₁ (σ₁.setVar "pw.k" (xcnt X u + 1)) 4 := by
        have h1k : σ₁.vars "pw.k" = xcnt X u := by rw [hσ₁, vars_setArr, hk]
        have hev := evalB_incr (B := B) (x := "pw.k") (σ := σ₁)
          (by rw [h1k]; omega)
        rw [h1k] at hev
        exact (Run.assign hev).mono (by simp)
      set σ₂ := σ₁.setVar "pw.k" (xcnt X u + 1) with hσ₂
      have huinc : Run B (.assign "pw.u" (.add (.var "pw.u") (.lit 1)))
          σ₂ (σ₂.setVar "pw.u" (u + 1)) 4 := by
        have h2u : σ₂.vars "pw.u" = u := by
          rw [hσ₂, vars_setVar_ne (by decide), hσ₁, vars_setArr]
        have hev := evalB_incr (B := B) (x := "pw.u") (σ := σ₂)
          (by rw [h2u]; omega)
        rw [h2u] at hev
        exact (Run.assign hev).mono (by simp)
      set σ' := σ₂.setVar "pw.u" (u + 1) with hσ'
      have hrun : Run B (vsFillTurn oa ta xb vt nN) σ σ' 28 := by
        have hInner : Run B (.ite (.eq (.get xb (.var "pw.u")) (.lit 1))
            (.seq (.store vt
                (.add (.get oa (.add (.var "pw.u") (.lit 1))) (.var "pw.k"))
                (.var nN))
              (.assign "pw.k" (.add (.var "pw.k") (.lit 1))))
            .skip) σ σ₂ 17 :=
          (Run.ite_true hbevT (hstore.seq hkinc)).mono (by simp)
        exact (Run.ite_false hcondF (hInner.seq huinc)).mono (by simp)
      have h'u : σ'.vars "pw.u" = u + 1 := by rw [hσ', vars_setVar_self]
      have h'k : σ'.vars "pw.k" = xcnt X u + 1 := by
        rw [hσ', vars_setVar_ne (by decide), hσ₂, vars_setVar_self]
      have h'vars : ∀ y, y ≠ "pw.u" → y ≠ "pw.k" → σ'.vars y = σ.vars y := by
        intro y h1 h2
        rw [hσ', vars_setVar_ne h1, hσ₂, vars_setVar_ne h2, hσ₁, vars_setArr]
      have h'arr : ∀ b, b ≠ vt → σ'.arrs b = σ.arrs b := by
        intro b hb
        rw [hσ', arrs_setVar, hσ₂, arrs_setVar, hσ₁, arrs_setArr_ne hb]
      have h'vt : σ'.arrs vt = (σ.arrs vt).set wpos N := by
        rw [hσ', arrs_setVar, hσ₂, arrs_setVar, hσ₁, arrs_setArr_self]
      set g' : ℕ → ℕ := fun p => if p = wpos then N else g p with hg'
      have hg'arr : σ'.arrs vt = arrOf (ns + 2 * xcnt X N) g' := by
        rw [h'vt, hg, set_arrOf]
      have hg'ne : ∀ p, p ≠ wpos → g' p = g p := by
        intro p hp
        show (if p = wpos then N else g p) = g p
        rw [if_neg hp]
      have hg'w : g' wpos = N := by
        show (if wpos = wpos then N else g wpos) = N
        rw [if_pos rfl]
      refine ⟨σ', 28, hrun,
        ⟨hc.of_eq (h'arr oa (Ne.symm hvt_oa)) (h'arr ta (Ne.symm hvt_ta)),
          ⟨by rw [h'arr xb (Ne.symm hvt_xb)]; exact hxb.1,
            fun v => by rw [h'arr xb (Ne.symm hvt_xb)]; exact hxb.2 v⟩,
          by rw [h'vars nN hnN_u hnN_k]; exact hn,
          by rw [h'vars nS hnS_u hnS_k]; exact hs,
          by rw [h'vars "pw.t" (by decide) (by decide)]; exact ht,
          by rw [h'u]; omega,
          by rw [h'vars "pw.j" (by decide) (by decide)]; omega,
          by rw [h'vars "pw.j" (by decide) (by decide), h'u]; omega,
          by rw [h'vars "pw.j" (by decide) (by decide), h'u]
             intro h
             have := hc.off_le_succ (i := u + 1) h
             omega,
          by rw [h'k, h'u, xcnt_succ, hbit],
          g', hg'arr, ?_, ?_⟩,
        by rw [h'vars "pw.j" (by decide) (by decide)],
        by rw [h'u]; omega,
        by rw [h'u]; omega,
        by rw [h'u, h'vars "pw.j" (by decide) (by decide)]; omega⟩
      · -- every row below the new owner is done
        rw [h'u]
        intro i hi
        rcases Nat.lt_or_ge i u with hiu | hiu
        · -- the old rows survive the back-edge write
          have hoffi1u : off (i + 1) ≤ off u := hc.mono (by omega) (by omega)
          have hoffu1 : off u ≤ off (u + 1) := hc.off_le_succ (by omega)
          have hxci : xcnt X i ≤ xcnt X u := xcnt_mono (by omega)
          refine vrowdone_of_agree (hdone i hiu) ?_ ?_
          · intro q h1 h2
            refine hg'ne _ ?_
            rw [hwpos]
            omega
          · intro hb
            refine hg'ne _ ?_
            have hxci1 : xcnt X (i + 1) ≤ xcnt X u := xcnt_mono (by omega)
            rw [xcnt_succ, hb] at hxci1
            rw [hwpos]
            omega
        · -- the owner's row: embedded part from the partial clause, the
          -- back-edge from this turn's write
          have hieq : i = u := by omega
          subst hieq
          constructor
          · intro q h1 h2
            rw [hg'ne _ (by rw [hwpos]; omega)]
            exact hpart q h1 (by omega)
          · intro _
            exact hg'w
      · -- the fresh owner's partial row is empty
        rw [h'u, h'vars "pw.j" (by decide) (by decide)]
        intro q h1 h2
        have := hc.off_le_succ (i := u) (by omega)
        omega
    · -- not a member: no write, count carries, owner moves on
      have hbit0 : xbit X u = 0 := by omega
      have hbevF : (Cond.eq (.get xb (.var "pw.u")) (.lit 1)).evalB B σ
          = some false := by
        rw [hbev, hbit0]
        rfl
      set σ' := σ.setVar "pw.u" (u + 1) with hσ'
      have hrun : Run B (vsFillTurn oa ta xb vt nN) σ σ' 28 := by
        have hass : Run B (.assign "pw.u" (.add (.var "pw.u") (.lit 1)))
            σ σ' 4 := by
          have hev := evalB_incr (B := B) (x := "pw.u") (σ := σ) (by omega)
          exact (Run.assign hev).mono (by simp)
        have hInner : Run B (.ite (.eq (.get xb (.var "pw.u")) (.lit 1))
            (.seq (.store vt
                (.add (.get oa (.add (.var "pw.u") (.lit 1))) (.var "pw.k"))
                (.var nN))
              (.assign "pw.k" (.add (.var "pw.k") (.lit 1))))
            .skip) σ σ 6 :=
          (Run.ite_false hbevF Run.skip).mono (by simp)
        exact (Run.ite_false hcondF (hInner.seq hass)).mono (by simp)
      have h'u : σ'.vars "pw.u" = u + 1 := by rw [hσ', vars_setVar_self]
      have h'vars : ∀ y, y ≠ "pw.u" → σ'.vars y = σ.vars y := by
        intro y hy
        rw [hσ', vars_setVar_ne hy]
      have h'arr : ∀ b, σ'.arrs b = σ.arrs b := by
        intro b
        rw [hσ', arrs_setVar]
      refine ⟨σ', 28, hrun,
        ⟨hc.of_eq (h'arr oa) (h'arr ta),
          ⟨by rw [h'arr xb]; exact hxb.1,
            fun v => by rw [h'arr xb]; exact hxb.2 v⟩,
          by rw [h'vars nN hnN_u]; exact hn,
          by rw [h'vars nS hnS_u]; exact hs,
          by rw [h'vars "pw.t" (by decide)]; exact ht,
          by rw [h'u]; omega,
          by rw [h'vars "pw.j" (by decide)]; omega,
          by rw [h'vars "pw.j" (by decide), h'u]; omega,
          by rw [h'vars "pw.j" (by decide), h'u]
             intro h
             have := hc.off_le_succ (i := u + 1) h
             omega,
          by rw [h'vars "pw.k" (by decide), h'u, hk, xcnt_succ, hbit0]; omega,
          g, by rw [h'arr vt]; exact hg, ?_, ?_⟩,
        by rw [h'vars "pw.j" (by decide)],
        by rw [h'u]; omega,
        by rw [h'u]; omega,
        by rw [h'u, h'vars "pw.j" (by decide)]; omega⟩
      · -- rows below the new owner: the old ones, plus the owner's own
        rw [h'u]
        intro i hi
        rcases Nat.lt_or_ge i u with hiu | hiu
        · exact hdone i hiu
        · have hieq : i = u := by omega
          subst hieq
          constructor
          · intro q h1 h2
            exact hpart q h1 (by omega)
          · intro hb
            exact absurd hb (by omega)
      · -- the fresh owner's partial row is empty
        rw [h'u, h'vars "pw.j" (by decide)]
        intro q h1 h2
        have := hc.off_le_succ (i := u) (by omega)
        omega

include hvt_oa hvt_ta hvt_xb hnN_scr hnS_scr hNB hnsB in
/-- **The fill pass**: one owner-advancing scan over all `ns` slots —
`Lib.Csr.ownerScan_spec` at the turn above. -/
theorem vsFillCom_spec :
    Spec B (FillInv oa ta xb vt nN nS ns off tgt X)
      (Csr.scan "pw.j" nS (vsFillTurn oa ta xb vt nN))
      (fun _ σ' => FillInv oa ta xb vt nN nS ns off tgt X σ' ∧
        σ'.vars "pw.j" = ns)
      (21 * ns + 32 * N + 4) := by
  refine Csr.ownerScan_spec B (21 * ns + 32 * N + 4) N ns 17 28
    "pw.j" nS "pw.u" (vsFillTurn oa ta xb vt nN)
    (FillInv oa ta xb vt nN nS ns off tgt X) (by omega)
    (fun σ hσ => ⟨hσ.2.2.2.1, hσ.2.2.2.2.2.2.1, hσ.2.2.2.2.2.1⟩)
    (vsFillTurn_step hvt_oa hvt_ta hvt_xb hnN_scr hnS_scr hNB hnsB)
    (fun σ hσ => hσ) (fun σ hσ => ?_)
  have h1 : (17 + 4) * (ns - σ.vars "pw.j") ≤ 21 * ns :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : (28 + 4) * (N - σ.vars "pw.u") ≤ 32 * N :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-! ### §4c The tail: back-edges of the empty trailing rows -/

/-- The row-end work alone: back-edge if the owner is a member, owner
moves on — what the scan's exit leaves undone for the trailing empty
rows. -/
def vsTailBody (oa xb vt nN : String) : Com :=
  .seq (.ite (.eq (.get xb (.var "pw.u")) (.lit 1))
      (.seq (.store vt
          (.add (.get oa (.add (.var "pw.u") (.lit 1))) (.var "pw.k"))
          (.var nN))
        (.assign "pw.k" (.add (.var "pw.k") (.lit 1))))
      .skip)
    (.assign "pw.u" (.add (.var "pw.u") (.lit 1)))

def vsTailCom (oa xb vt nN : String) : Com :=
  .while (.lt (.var "pw.u") (.var nN)) (vsTailBody oa xb vt nN)

/-- The tail's invariant: the scan's exit state, owner-indexed — every
remaining row is empty (`off (u+1) = ns`), so only back-edges are
left. -/
def TailInv (oa ta xb vt nN nS : String) {N : ℕ} (ns : ℕ)
    (off tgt : ℕ → ℕ) (X : Set (Fin N)) (σ : Env) : Prop :=
  Csr oa ta N ns N off tgt σ ∧ FinBits xb X σ ∧
    σ.vars nN = N ∧ σ.vars nS = ns ∧ σ.vars "pw.t" = xcnt X N ∧
    σ.vars "pw.u" ≤ N ∧
    (σ.vars "pw.u" < N → off (σ.vars "pw.u" + 1) = ns) ∧
    σ.vars "pw.k" = xcnt X (σ.vars "pw.u") ∧
    ∃ g, σ.arrs vt = arrOf (ns + 2 * xcnt X N) g ∧
      (∀ i < σ.vars "pw.u", VRowDone off tgt X i g) ∧
      (∀ q, off (σ.vars "pw.u") ≤ q → q < ns →
        g (q + xcnt X (σ.vars "pw.u")) = tgt q)

include hvt_oa hvt_ta hvt_xb hnN_scr hnS_scr hNB hnsB in
/-- **The tail loop**: finishes every row's back-edge; at exit all `N`
embedded rows are done. -/
theorem vsTailCom_spec :
    Spec B (TailInv oa ta xb vt nN nS ns off tgt X)
      (vsTailCom oa xb vt nN)
      (fun _ σ' => TailInv oa ta xb vt nN nS ns off tgt X σ' ∧
        σ'.vars "pw.u" = N)
      (25 * N + 4) := by
  have hnN_k : nN ≠ "pw.k" := fun h => hnN_scr (by rw [h]; decide)
  have hnN_u : nN ≠ "pw.u" := fun h => hnN_scr (by rw [h]; decide)
  have hnS_k : nS ≠ "pw.k" := fun h => hnS_scr (by rw [h]; decide)
  have hnS_u : nS ≠ "pw.u" := fun h => hnS_scr (by rw [h]; decide)
  refine Spec.forRange "pw.u" nN (TailInv oa ta xb vt nN nS ns off tgt X)
    N 21 (25 * N + 4)
    (fun σ hσ => by have := hσ.2.2.2.2.2.1; omega)
    (fun σ hσ => by rw [hσ.2.2.1]; omega)
    (fun σ hσ => hσ.2.2.1) (fun σ hσ => hσ.2.2.2.2.2.1) ?_
    (fun σ hσ => hσ)
    (fun σ hσ => by
      have h : (21 + 4) * (N - σ.vars "pw.u") ≤ 25 * N :=
        Nat.mul_le_mul_left _ (by omega)
      omega)
  -- one turn of the tail
  intro σ hσ
  obtain ⟨⟨hc, hxb, hn, hs, ht, hu, hend, hk, g, hg, hdone, hpart⟩, hltN⟩ := hσ
  set u := σ.vars "pw.u" with hu_def
  have huN : u < N := hltN
  have hoffu1 : off (u + 1) ≤ ns := hc.le_ns (by omega)
  have hoffu1eq : off (u + 1) = ns := hend huN
  have hlen_vt : (σ.arrs vt).length = ns + 2 * xcnt X N := by
    rw [hg, length_arrOf]
  have hoffval : (Expr.get oa (.add (.var "pw.u") (.lit 1))).evalB B σ
      = some (off (u + 1)) := by
    refine evalB_get (k := u + 1) (evalB_incr (by omega)) ?_
      (hc.off_lt (by omega) (by omega))
    rw [hc.offArr, getElem?_arrOf off (by omega)]
  have hbitval : (σ.arrs xb).getD u 0 = xbit X u := by
    have h := hxb.2 ⟨u, huN⟩
    rw [h]
    by_cases hm : (⟨u, huN⟩ : Fin N) ∈ X <;> simp [xbit, huN, hm]
  have hbitle : xbit X u ≤ 1 := xbit_le_one u
  have hbev : (Cond.eq (.get xb (.var "pw.u")) (.lit 1)).evalB B σ
      = some (xbit X u == 1) := by
    refine evalB_condEq ?_ (evalB_lit (by omega))
    refine evalB_get (evalB_var (by omega)) ?_ (by omega)
    rw [← hbitval]
    exact getElem?_getD (by rw [hxb.1]; omega)
  by_cases hbit : xbit X u = 1
  · -- write the back-edge, count up, owner on
    have hbevT : (Cond.eq (.get xb (.var "pw.u")) (.lit 1)).evalB B σ
        = some true := by
      rw [hbev, hbit]
      rfl
    set wpos := off (u + 1) + xcnt X u with hwpos
    have hxltN : xcnt X u < xcnt X N := xcnt_lt_of_bit huN hbit
    have hidxval : (Expr.add (.get oa (.add (.var "pw.u") (.lit 1)))
        (.var "pw.k")).evalB B σ = some wpos := by
      have hkN : xcnt X u ≤ N := le_trans (xcnt_le u) (by omega)
      have h := evalB_bin (B := B) (op := .add) hoffval
        (evalB_var (x := "pw.k") (σ := σ) (by rw [hk]; omega))
        (by simp only [Bop.apply_add]; rw [hk]; omega)
      simp only [Bop.apply_add] at h
      rw [hk] at h
      exact h
    have hnval : (Expr.var nN).evalB B σ = some N := by
      have h := evalB_var (B := B) (x := nN) (σ := σ) (by rw [hn]; omega)
      rwa [hn] at h
    have hstore : Run B (.store vt
        (.add (.get oa (.add (.var "pw.u") (.lit 1))) (.var "pw.k"))
        (.var nN)) σ (σ.setArr vt wpos N) 8 :=
      (Run.store hidxval hnval (by rw [hlen_vt, hwpos]; omega)).mono (by simp)
    set σ₁ := σ.setArr vt wpos N with hσ₁
    have hkinc : Run B (.assign "pw.k" (.add (.var "pw.k") (.lit 1)))
        σ₁ (σ₁.setVar "pw.k" (xcnt X u + 1)) 4 := by
      have h1k : σ₁.vars "pw.k" = xcnt X u := by rw [hσ₁, vars_setArr, hk]
      have hev := evalB_incr (B := B) (x := "pw.k") (σ := σ₁)
        (by rw [h1k]; have := xcnt_le (X := X) u; omega)
      rw [h1k] at hev
      exact (Run.assign hev).mono (by simp)
    set σ₂ := σ₁.setVar "pw.k" (xcnt X u + 1) with hσ₂
    have huinc : Run B (.assign "pw.u" (.add (.var "pw.u") (.lit 1)))
        σ₂ (σ₂.setVar "pw.u" (u + 1)) 4 := by
      have h2u : σ₂.vars "pw.u" = u := by
        rw [hσ₂, vars_setVar_ne (by decide), hσ₁, vars_setArr]
      have hev := evalB_incr (B := B) (x := "pw.u") (σ := σ₂)
        (by rw [h2u]; omega)
      rw [h2u] at hev
      exact (Run.assign hev).mono (by simp)
    set σ' := σ₂.setVar "pw.u" (u + 1) with hσ'
    have hrun : Run B (vsTailBody oa xb vt nN) σ σ' 21 :=
      ((Run.ite_true hbevT (hstore.seq hkinc)).seq huinc).mono (by simp)
    have h'u : σ'.vars "pw.u" = u + 1 := by rw [hσ', vars_setVar_self]
    have h'k : σ'.vars "pw.k" = xcnt X u + 1 := by
      rw [hσ', vars_setVar_ne (by decide), hσ₂, vars_setVar_self]
    have h'vars : ∀ y, y ≠ "pw.u" → y ≠ "pw.k" → σ'.vars y = σ.vars y := by
      intro y h1 h2
      rw [hσ', vars_setVar_ne h1, hσ₂, vars_setVar_ne h2, hσ₁, vars_setArr]
    have h'arr : ∀ b, b ≠ vt → σ'.arrs b = σ.arrs b := by
      intro b hb
      rw [hσ', arrs_setVar, hσ₂, arrs_setVar, hσ₁, arrs_setArr_ne hb]
    have h'vt : σ'.arrs vt = (σ.arrs vt).set wpos N := by
      rw [hσ', arrs_setVar, hσ₂, arrs_setVar, hσ₁, arrs_setArr_self]
    set g' : ℕ → ℕ := fun p => if p = wpos then N else g p with hg'
    have hg'arr : σ'.arrs vt = arrOf (ns + 2 * xcnt X N) g' := by
      rw [h'vt, hg, set_arrOf]
    have hg'ne : ∀ p, p ≠ wpos → g' p = g p := by
      intro p hp
      show (if p = wpos then N else g p) = g p
      rw [if_neg hp]
    have hg'w : g' wpos = N := by
      show (if wpos = wpos then N else g wpos) = N
      rw [if_pos rfl]
    refine ⟨σ', hrun,
      ⟨hc.of_eq (h'arr oa (Ne.symm hvt_oa)) (h'arr ta (Ne.symm hvt_ta)),
        ⟨by rw [h'arr xb (Ne.symm hvt_xb)]; exact hxb.1,
          fun v => by rw [h'arr xb (Ne.symm hvt_xb)]; exact hxb.2 v⟩,
        by rw [h'vars nN hnN_u hnN_k]; exact hn,
        by rw [h'vars nS hnS_u hnS_k]; exact hs,
        by rw [h'vars "pw.t" (by decide) (by decide)]; exact ht,
        by rw [h'u]; omega,
        by rw [h'u]
           intro h
           have h1 := hc.off_le_succ (i := u + 1) h
           have h2 := hc.le_ns (i := u + 1 + 1) (by omega)
           omega,
        by rw [h'k, h'u, xcnt_succ, hbit],
        g', hg'arr, ?_, ?_⟩, h'u⟩
    · -- rows below the new owner are done
      rw [h'u]
      intro i hi
      rcases Nat.lt_or_ge i u with hiu | hiu
      · have hoffi1u : off (i + 1) ≤ off u := hc.mono (by omega) (by omega)
        have hoffuu1 : off u ≤ off (u + 1) := hc.off_le_succ (by omega)
        have hxci : xcnt X i ≤ xcnt X u := xcnt_mono (by omega)
        refine vrowdone_of_agree (hdone i hiu) ?_ ?_
        · intro q h1 h2
          refine hg'ne _ ?_
          rw [hwpos]
          omega
        · intro hb
          refine hg'ne _ ?_
          have hxci1 : xcnt X (i + 1) ≤ xcnt X u := xcnt_mono (by omega)
          rw [xcnt_succ, hb] at hxci1
          rw [hwpos]
          omega
      · have hieq : i = u := by omega
        subst hieq
        constructor
        · intro q h1 h2
          rw [hg'ne _ (by rw [hwpos]; omega)]
          exact hpart q h1 (by omega)
        · intro _
          exact hg'w
    · -- the new owner's remaining stretch is empty
      rw [h'u]
      intro q h1 h2
      have := hc.off_le_succ (i := u) (by omega)
      omega
  · -- not a member: only the owner moves
    have hbit0 : xbit X u = 0 := by omega
    have hbevF : (Cond.eq (.get xb (.var "pw.u")) (.lit 1)).evalB B σ
        = some false := by
      rw [hbev, hbit0]
      rfl
    set σ' := σ.setVar "pw.u" (u + 1) with hσ'
    have hrun : Run B (vsTailBody oa xb vt nN) σ σ' 21 := by
      have hass : Run B (.assign "pw.u" (.add (.var "pw.u") (.lit 1)))
          σ σ' 4 := by
        have hev := evalB_incr (B := B) (x := "pw.u") (σ := σ) (by omega)
        exact (Run.assign hev).mono (by simp)
      exact ((Run.ite_false hbevF Run.skip).seq hass).mono (by simp)
    have h'u : σ'.vars "pw.u" = u + 1 := by rw [hσ', vars_setVar_self]
    have h'vars : ∀ y, y ≠ "pw.u" → σ'.vars y = σ.vars y := by
      intro y hy
      rw [hσ', vars_setVar_ne hy]
    have h'arr : ∀ b, σ'.arrs b = σ.arrs b := by
      intro b
      rw [hσ', arrs_setVar]
    refine ⟨σ', hrun,
      ⟨hc.of_eq (h'arr oa) (h'arr ta),
        ⟨by rw [h'arr xb]; exact hxb.1,
          fun v => by rw [h'arr xb]; exact hxb.2 v⟩,
        by rw [h'vars nN hnN_u]; exact hn,
        by rw [h'vars nS hnS_u]; exact hs,
        by rw [h'vars "pw.t" (by decide)]; exact ht,
        by rw [h'u]; omega,
        by rw [h'u]
           intro h
           have h1 := hc.off_le_succ (i := u + 1) h
           have h2 := hc.le_ns (i := u + 1 + 1) (by omega)
           omega,
        by rw [h'vars "pw.k" (by decide), h'u, hk, xcnt_succ, hbit0]; omega,
        g, by rw [h'arr vt]; exact hg, ?_, ?_⟩, h'u⟩
    · rw [h'u]
      intro i hi
      rcases Nat.lt_or_ge i u with hiu | hiu
      · exact hdone i hiu
      · have hieq : i = u := by omega
        subst hieq
        constructor
        · intro q h1 h2
          exact hpart q h1 (by omega)
        · intro hb
          exact absurd hb (by omega)
    · rw [h'u]
      intro q h1 h2
      have := hc.off_le_succ (i := u) (by omega)
      omega

/-! ### §4d The source row: the members, in increasing order -/

/-- One turn of the source pass: a member is appended to the source
row at position `ns + |X| + (its rank)`, the rank counter up. -/
def vsSrcBody (xb vt nS : String) : Com :=
  .seq (.ite (.eq (.get xb (.var "pw.i")) (.lit 1))
      (.seq (.store vt (.add (.add (.var nS) (.var "pw.t")) (.var "pw.k"))
          (.var "pw.i"))
        (.assign "pw.k" (.add (.var "pw.k") (.lit 1))))
      .skip)
    (.assign "pw.i" (.add (.var "pw.i") (.lit 1)))

/-- The source pass: scan the bit array, append each member. -/
def vsSrcCom (xb vt nN nS : String) : Com :=
  .seq (.assign "pw.k" (.lit 0))
    (.seq (.assign "pw.i" (.lit 0))
      (.while (.lt (.var "pw.i") (.var nN)) (vsSrcBody xb vt nS)))

include hvt_xb hnN_scr hnS_scr hNB hnsB in
/-- **The source pass, discharged** (relationally): everything below
the source row survives, and the source row becomes exactly the member
list — increasing, `Nodup` for free. -/
theorem vsSrcCom_spec :
    Spec B
      (fun σ => FinBits xb X σ ∧ σ.vars nN = N ∧ σ.vars nS = ns ∧
        σ.vars "pw.t" = xcnt X N ∧
        (σ.arrs vt).length = ns + 2 * xcnt X N)
      (vsSrcCom xb vt nN nS)
      (fun σ σ' => FinBits xb X σ' ∧ σ'.vars nN = N ∧ σ'.vars nS = ns ∧
        σ'.vars "pw.t" = xcnt X N ∧
        ∃ g, σ'.arrs vt = arrOf (ns + 2 * xcnt X N) g ∧
          (∀ p < ns + xcnt X N, g p = (σ.arrs vt).getD p 0) ∧
          arrOf (xcnt X N) (fun k => g (ns + xcnt X N + k)) = memList X)
      (24 * N + 8) := by
  have hnN_i : nN ≠ "pw.i" := fun h => hnN_scr (by rw [h]; decide)
  have hnN_k : nN ≠ "pw.k" := fun h => hnN_scr (by rw [h]; decide)
  have hnS_i : nS ≠ "pw.i" := fun h => hnS_scr (by rw [h]; decide)
  have hnS_k : nS ≠ "pw.k" := fun h => hnS_scr (by rw [h]; decide)
  intro σ₀ hσ₀
  obtain ⟨hxb0, hn0, hs0, ht0, hlen0⟩ := hσ₀
  set g₀ : ℕ → ℕ := fun p => (σ₀.arrs vt).getD p 0 with hg₀
  set I : Env → Prop := fun σ =>
    FinBits xb X σ ∧ σ.vars nN = N ∧ σ.vars nS = ns ∧
      σ.vars "pw.t" = xcnt X N ∧ σ.vars "pw.i" ≤ N ∧
      σ.vars "pw.k" = xcnt X (σ.vars "pw.i") ∧
      ∃ g, σ.arrs vt = arrOf (ns + 2 * xcnt X N) g ∧
        (∀ p < ns + xcnt X N, g p = g₀ p) ∧
        arrOf (xcnt X (σ.vars "pw.i")) (fun k => g (ns + xcnt X N + k))
          = (List.range (σ.vars "pw.i")).filter (fun y => xbit X y == 1)
    with hI
  have hbody : Spec B (fun σ => I σ ∧ σ.vars "pw.i" < N)
      (vsSrcBody xb vt nS)
      (fun σ σ' => I σ' ∧ σ'.vars "pw.i" = σ.vars "pw.i" + 1) 20 := by
    intro σ hσ
    obtain ⟨⟨hxb, hn, hs, ht, hiN, hk, g, hg, hagree, hlist⟩, hlt⟩ := hσ
    set i := σ.vars "pw.i" with hi_def
    have hxcN : xcnt X N ≤ N := xcnt_le N
    have hxci : xcnt X i ≤ xcnt X N := xcnt_mono (by omega)
    have hlen_vt : (σ.arrs vt).length = ns + 2 * xcnt X N := by
      rw [hg, length_arrOf]
    have hbitval : (σ.arrs xb).getD i 0 = xbit X i := by
      have h := hxb.2 ⟨i, hlt⟩
      rw [h]
      by_cases hm : (⟨i, hlt⟩ : Fin N) ∈ X <;> simp [xbit, hlt, hm]
    have hbitle : xbit X i ≤ 1 := xbit_le_one i
    have hbev : (Cond.eq (.get xb (.var "pw.i")) (.lit 1)).evalB B σ
        = some (xbit X i == 1) := by
      refine evalB_condEq ?_ (evalB_lit (by omega))
      refine evalB_get (evalB_var (by omega)) ?_ (by omega)
      rw [← hbitval]
      exact getElem?_getD (by rw [hxb.1]; omega)
    by_cases hbit : xbit X i = 1
    · -- a member: append it to the source row
      have hbevT : (Cond.eq (.get xb (.var "pw.i")) (.lit 1)).evalB B σ
          = some true := by
        rw [hbev, hbit]
        rfl
      set wpos := ns + xcnt X N + xcnt X i with hwpos
      have hxlt : xcnt X i < xcnt X N := xcnt_lt_of_bit hlt hbit
      have hidxval : (Expr.add (.add (.var nS) (.var "pw.t"))
          (.var "pw.k")).evalB B σ = some wpos := by
        have h1 := evalB_bin (B := B) (op := .add)
          (evalB_var (x := nS) (σ := σ) (by rw [hs]; omega))
          (evalB_var (x := "pw.t") (σ := σ) (by rw [ht]; omega))
          (by simp only [Bop.apply_add]; rw [hs, ht]; omega)
        simp only [Bop.apply_add] at h1
        rw [hs, ht] at h1
        have h := evalB_bin (B := B) (op := .add) h1
          (evalB_var (x := "pw.k") (σ := σ) (by rw [hk]; omega))
          (by simp only [Bop.apply_add]; rw [hk]; omega)
        simp only [Bop.apply_add] at h
        rw [hk] at h
        exact h
      have hstore : Run B (.store vt
          (.add (.add (.var nS) (.var "pw.t")) (.var "pw.k")) (.var "pw.i"))
          σ (σ.setArr vt wpos i) 7 :=
        (Run.store hidxval (evalB_var (by omega))
          (by rw [hlen_vt, hwpos]; omega)).mono (by simp)
      set σ₁ := σ.setArr vt wpos i with hσ₁
      have hkinc : Run B (.assign "pw.k" (.add (.var "pw.k") (.lit 1)))
          σ₁ (σ₁.setVar "pw.k" (xcnt X i + 1)) 4 := by
        have h1k : σ₁.vars "pw.k" = xcnt X i := by rw [hσ₁, vars_setArr, hk]
        have hev := evalB_incr (B := B) (x := "pw.k") (σ := σ₁)
          (by rw [h1k]; omega)
        rw [h1k] at hev
        exact (Run.assign hev).mono (by simp)
      set σ₂ := σ₁.setVar "pw.k" (xcnt X i + 1) with hσ₂
      have hiinc : Run B (.assign "pw.i" (.add (.var "pw.i") (.lit 1)))
          σ₂ (σ₂.setVar "pw.i" (i + 1)) 4 := by
        have h2i : σ₂.vars "pw.i" = i := by
          rw [hσ₂, vars_setVar_ne (by decide), hσ₁, vars_setArr]
        have hev := evalB_incr (B := B) (x := "pw.i") (σ := σ₂)
          (by rw [h2i]; omega)
        rw [h2i] at hev
        exact (Run.assign hev).mono (by simp)
      set σ' := σ₂.setVar "pw.i" (i + 1) with hσ'
      have hrun : Run B (vsSrcBody xb vt nS) σ σ' 20 :=
        ((Run.ite_true hbevT (hstore.seq hkinc)).seq hiinc).mono (by simp)
      have h'i : σ'.vars "pw.i" = i + 1 := by rw [hσ', vars_setVar_self]
      have h'k : σ'.vars "pw.k" = xcnt X i + 1 := by
        rw [hσ', vars_setVar_ne (by decide), hσ₂, vars_setVar_self]
      have h'vars : ∀ y, y ≠ "pw.i" → y ≠ "pw.k" → σ'.vars y = σ.vars y := by
        intro y h1 h2
        rw [hσ', vars_setVar_ne h1, hσ₂, vars_setVar_ne h2, hσ₁, vars_setArr]
      have h'arr : ∀ b, b ≠ vt → σ'.arrs b = σ.arrs b := by
        intro b hb
        rw [hσ', arrs_setVar, hσ₂, arrs_setVar, hσ₁, arrs_setArr_ne hb]
      have h'vt : σ'.arrs vt = (σ.arrs vt).set wpos i := by
        rw [hσ', arrs_setVar, hσ₂, arrs_setVar, hσ₁, arrs_setArr_self]
      set g' : ℕ → ℕ := fun p => if p = wpos then i else g p with hg'
      have hg'arr : σ'.arrs vt = arrOf (ns + 2 * xcnt X N) g' := by
        rw [h'vt, hg, set_arrOf]
      have hg'ne : ∀ p, p ≠ wpos → g' p = g p := by
        intro p hp
        show (if p = wpos then i else g p) = g p
        rw [if_neg hp]
      have hg'w : g' wpos = i := by
        show (if wpos = wpos then i else g wpos) = i
        rw [if_pos rfl]
      refine ⟨σ', hrun,
        ⟨⟨by rw [h'arr xb (Ne.symm hvt_xb)]; exact hxb.1,
            fun v => by rw [h'arr xb (Ne.symm hvt_xb)]; exact hxb.2 v⟩,
          by rw [h'vars nN hnN_i hnN_k]; exact hn,
          by rw [h'vars nS hnS_i hnS_k]; exact hs,
          by rw [h'vars "pw.t" (by decide) (by decide)]; exact ht,
          by rw [h'i]; omega,
          by rw [h'k, h'i, xcnt_succ, hbit],
          g', hg'arr, ?_, ?_⟩, h'i⟩
      · intro p hp
        rw [hg'ne _ (by rw [hwpos]; omega)]
        exact hagree p hp
      · rw [h'i, xcnt_succ, hbit, List.range_succ, List.filter_append]
        have hfilt : List.filter (fun y => xbit X y == 1) [i] = [i] := by
          simp [hbit]
        rw [hfilt, arrOf_succ, ← hlist]
        congr 1
        · refine arrOf_congr fun p hp => ?_
          exact hg'ne _ (by rw [hwpos]; omega)
        · rw [hg'w]
    · -- not a member: only the scan counter moves
      have hbit0 : xbit X i = 0 := by omega
      have hbevF : (Cond.eq (.get xb (.var "pw.i")) (.lit 1)).evalB B σ
          = some false := by
        rw [hbev, hbit0]
        rfl
      set σ' := σ.setVar "pw.i" (i + 1) with hσ'
      have hrun : Run B (vsSrcBody xb vt nS) σ σ' 20 := by
        have hass : Run B (.assign "pw.i" (.add (.var "pw.i") (.lit 1)))
            σ σ' 4 := by
          have hev := evalB_incr (B := B) (x := "pw.i") (σ := σ) (by omega)
          exact (Run.assign hev).mono (by simp)
        exact ((Run.ite_false hbevF Run.skip).seq hass).mono (by simp)
      have h'i : σ'.vars "pw.i" = i + 1 := by rw [hσ', vars_setVar_self]
      have h'vars : ∀ y, y ≠ "pw.i" → σ'.vars y = σ.vars y := by
        intro y hy
        rw [hσ', vars_setVar_ne hy]
      have h'arr : ∀ b, σ'.arrs b = σ.arrs b := by
        intro b
        rw [hσ', arrs_setVar]
      refine ⟨σ', hrun,
        ⟨⟨by rw [h'arr xb]; exact hxb.1,
            fun v => by rw [h'arr xb]; exact hxb.2 v⟩,
          by rw [h'vars nN hnN_i]; exact hn,
          by rw [h'vars nS hnS_i]; exact hs,
          by rw [h'vars "pw.t" (by decide)]; exact ht,
          by rw [h'i]; omega,
          by rw [h'vars "pw.k" (by decide), h'i, hk, xcnt_succ, hbit0]; omega,
          g, by rw [h'arr vt]; exact hg, hagree, ?_⟩, h'i⟩
      rw [h'i, xcnt_succ, hbit0, List.range_succ, List.filter_append]
      have hfilt : List.filter (fun y => xbit X y == 1) [i] = [] := by
        simp [hbit0]
      rw [hfilt, List.append_nil, Nat.add_zero]
      exact hlist
  -- assemble: `k := 0`, then the counted scan
  have hk0 : Run B (.assign "pw.k" (.lit 0)) σ₀ (σ₀.setVar "pw.k" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  set σa := σ₀.setVar "pw.k" 0 with hσa
  have hloop := Spec.forRangeZero (B := B) "pw.i" nN I N 20 (by omega)
    (fun σ hσ => hσ.2.2.2.2.1) (fun σ hσ => hσ.2.1) hbody
  have hpre : I (σa.setVar "pw.i" 0) := by
    refine ⟨⟨by simpa using hxb0.1, fun v => by simpa using hxb0.2 v⟩,
      ?_, ?_, ?_, by rw [vars_setVar_self]; omega, ?_, ?_⟩
    · rw [vars_setVar_ne hnN_i, hσa, vars_setVar_ne hnN_k]
      exact hn0
    · rw [vars_setVar_ne hnS_i, hσa, vars_setVar_ne hnS_k]
      exact hs0
    · rw [vars_setVar_ne (by decide), hσa, vars_setVar_ne (by decide)]
      exact ht0
    · rw [vars_setVar_self, vars_setVar_ne (by decide), hσa, vars_setVar_self]
      simp
    · refine ⟨g₀, ?_, fun p _ => rfl, ?_⟩
      · simp only [arrs_setVar, hσa]
        rw [← hlen0]
        exact (arrOf_getD (σ₀.arrs vt)).symm
      · rw [vars_setVar_self]
        simp [arrOf]
  obtain ⟨σ', hr, hI', hi'⟩ := hloop.run hpre
  obtain ⟨hxb', hn', hs', ht', hiN', hk', g, hg, hagree, hlist⟩ := hI'
  refine ⟨σ', (hk0.seq hr).mono (by omega), hxb', hn', hs', ht',
    g, hg, hagree, ?_⟩
  rw [hi'] at hlist
  exact hlist

end VsrcBuild2

/-! ### §4e The readout: the materialized regions ARE a CSR of
`Impl.vsrc H X` -/

section VsrcReadout

variable {N ns : ℕ} {X : Set (Fin N)} {off tgt : ℕ → ℕ}
  {H : SimpleGraph (Fin N)} {g : ℕ → ℕ}

private theorem exists_owner {f : ℕ → ℕ} {n p : ℕ}
    (hmono : ∀ i < n, f i ≤ f (i + 1)) (h0 : f 0 = 0) (hp : p < f n) :
    ∃ i < n, f i ≤ p ∧ p < f (i + 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge p (f n) with h | h
    · obtain ⟨i, hi, h1, h2⟩ := ih (fun i hi => hmono i (by omega)) h
      exact ⟨i, by omega, h1, h2⟩
    · exact ⟨n, by omega, h, hp⟩

theorem vsOff_of_le {i : ℕ} (hi : i ≤ N) :
    vsOff off X ns i = off i + xcnt X i := if_pos hi

theorem vsOff_top : vsOff off X ns (N + 1) = ns + 2 * xcnt X N :=
  if_neg (by omega)

variable (hmono : ∀ i < N, off i ≤ off (i + 1)) (hlast : off N = ns)

include hmono in
/-- An embedded row of the materialized CSR is the child's row plus,
for a member, the back-edge — as lists. -/
theorem vsrc_row_embedded (hrows : ∀ i < N, VRowDone off tgt X i g)
    {i : ℕ} (hi : i < N) :
    Csr.row (vsOff off X ns) g i
      = Csr.row off tgt i ++ (if xbit X i = 1 then [(N : ℕ)] else []) := by
  have hm := hmono i hi
  have hro : Csr.rowLen (vsOff off X ns) i = Csr.rowLen off i + xbit X i := by
    unfold Csr.rowLen
    rw [vsOff_of_le (by omega), vsOff_of_le (by omega), xcnt_succ]
    omega
  have hbase : ∀ k, k < Csr.rowLen off i →
      g (vsOff off X ns i + k) = tgt (off i + k) := by
    intro k hk
    rw [vsOff_of_le (by omega)]
    have hpos : off i + xcnt X i + k = (off i + k) + xcnt X i := by omega
    rw [hpos]
    refine (hrows i hi).1 (off i + k) (by omega) ?_
    unfold Csr.rowLen at hk
    omega
  by_cases hb : xbit X i = 1
  · rw [if_pos hb]
    show arrOf (Csr.rowLen (vsOff off X ns) i)
        (fun k => g (vsOff off X ns i + k)) = _
    rw [hro, hb, arrOf_succ]
    congr 1
    · exact arrOf_congr fun k hk => hbase k hk
    · have hpos : vsOff off X ns i + Csr.rowLen off i
          = off (i + 1) + xcnt X i := by
        rw [vsOff_of_le (by omega)]
        unfold Csr.rowLen
        omega
      rw [hpos, (hrows i hi).2 hb]
  · rw [if_neg hb, List.append_nil]
    show arrOf (Csr.rowLen (vsOff off X ns) i)
        (fun k => g (vsOff off X ns i + k)) = _
    have hb0 : xbit X i = 0 := by
      have := xbit_le_one (X := X) i
      omega
    rw [hro, hb0, Nat.add_zero]
    exact arrOf_congr fun k hk => hbase k hk

include hlast in
/-- The source row of the materialized CSR is the member list. -/
theorem vsrc_row_source
    (hsrc : arrOf (xcnt X N) (fun k => g (ns + xcnt X N + k)) = memList X) :
    Csr.row (vsOff off X ns) g N = memList X := by
  have hro : Csr.rowLen (vsOff off X ns) N = xcnt X N := by
    unfold Csr.rowLen
    rw [vsOff_of_le le_rfl, vsOff_top, hlast]
    omega
  show arrOf (Csr.rowLen (vsOff off X ns) N)
      (fun k => g (vsOff off X ns N + k)) = _
  rw [hro, ← hsrc]
  refine arrOf_congr fun k hk => ?_
  rw [vsOff_of_le le_rfl, hlast]

variable (hadj : ∀ (v : Fin N) (w : ℕ),
    w ∈ Csr.row off tgt v ↔ ∃ hw : w < N, H.Adj v ⟨w, hw⟩)
  (hrows : ∀ i < N, VRowDone off tgt X i g)
  (hsrc : arrOf (xcnt X N) (fun k => g (ns + xcnt X N + k)) = memList X)

include hmono hlast hadj hrows hsrc in
/-- **The adjacency readout**: row membership in the materialized
regions is exactly `Impl.vsrc H X`'s adjacency — the E6 dead ends
(`vsrc_adj_castSucc_iff`/`vsrc_adj_last_iff`) discharged at the CSR. -/
theorem vsrc_mem_row :
    ∀ (v : Fin (N + 1)) (w : ℕ),
      w ∈ Csr.row (vsOff off X ns) g (v : ℕ) ↔
        ∃ hw : w < N + 1, (Impl.vsrc H X).Adj v ⟨w, hw⟩ := by
  intro v w
  induction v using Fin.lastCases with
  | last =>
    have hval : ((Fin.last N : Fin (N + 1)) : ℕ) = N := rfl
    rw [hval, vsrc_row_source hlast hsrc]
    constructor
    · intro hw
      obtain ⟨hwN, hbit⟩ := mem_memList.mp hw
      obtain ⟨h, hmem⟩ := xbit_eq_one_iff.mp hbit
      refine ⟨by omega, ?_⟩
      rw [Impl.vsrc_adj_last_iff]
      exact ⟨⟨w, h⟩, hmem, Fin.ext rfl⟩
    · rintro ⟨hw, hAdj⟩
      rw [Impl.vsrc_adj_last_iff] at hAdj
      obtain ⟨y, hy, hcast⟩ := hAdj
      have hwy : w = (y : ℕ) := by
        have := congrArg Fin.val hcast
        simpa using this
      subst hwy
      exact mem_memList.mpr ⟨y.isLt, xbit_eq_one_iff.mpr ⟨y.isLt, by
        simpa using hy⟩⟩
  | cast i =>
    have hval : ((Fin.castSucc i : Fin (N + 1)) : ℕ) = (i : ℕ) := rfl
    rw [hval, vsrc_row_embedded hmono hrows i.isLt]
    rw [List.mem_append]
    constructor
    · rintro (hmem | hopt)
      · obtain ⟨hw, hA⟩ := (hadj i w).mp hmem
        refine ⟨by omega, ?_⟩
        have : (⟨w, by omega⟩ : Fin (N + 1)) = (⟨w, hw⟩ : Fin N).castSucc :=
          Fin.ext rfl
        rw [this]
        exact Impl.vsrc_adj_castSucc.mpr hA
      · by_cases hb : xbit X (i : ℕ) = 1
        · rw [if_pos hb] at hopt
          have hwN : w = N := by simpa using hopt
          obtain ⟨h, hmem⟩ := xbit_eq_one_iff.mp hb
          refine ⟨by omega, ?_⟩
          have h1 : (⟨w, by omega⟩ : Fin (N + 1)) = Fin.last N :=
            Fin.ext (by simpa using hwN)
          have h2 : (⟨(i : ℕ), h⟩ : Fin N) = i := Fin.ext rfl
          rw [h1]
          rw [h2] at hmem
          exact (Impl.vsrc_adj_last_iff.mpr ⟨i, hmem, rfl⟩).symm
        · rw [if_neg hb] at hopt
          exact absurd hopt (List.not_mem_nil)
    · rintro ⟨hw, hAdj⟩
      rw [Impl.vsrc_adj_castSucc_iff] at hAdj
      rcases hAdj with ⟨v', hA, hcast⟩ | ⟨hmem, hlastw⟩
      · left
        have hwv : w = (v' : ℕ) := by
          have := congrArg Fin.val hcast
          simpa using this
        refine (hadj i w).mpr ⟨by omega, ?_⟩
        have : (⟨w, by omega⟩ : Fin N) = v' := Fin.ext hwv
        rw [this]
        exact hA
      · right
        have hwN : w = N := by
          have := congrArg Fin.val hlastw
          simpa using this
        have hb : xbit X (i : ℕ) = 1 :=
          xbit_eq_one_iff.mpr ⟨i.isLt, by simpa using hmem⟩
        rw [if_pos hb]
        simp [hwN]

include hmono hlast hadj hrows hsrc in
/-- Row `Nodup`: the child's rows are `Nodup`, the back-edge is fresh
(every embedded target is `< N`), the member list is increasing. -/
theorem vsrc_row_nodup (hnd : ∀ v : Fin N, (Csr.row off tgt v).Nodup) :
    ∀ v : Fin (N + 1), (Csr.row (vsOff off X ns) g (v : ℕ)).Nodup := by
  intro v
  induction v using Fin.lastCases with
  | last =>
    have hval : ((Fin.last N : Fin (N + 1)) : ℕ) = N := rfl
    rw [hval, vsrc_row_source hlast hsrc]
    exact nodup_memList
  | cast i =>
    have hval : ((Fin.castSucc i : Fin (N + 1)) : ℕ) = (i : ℕ) := rfl
    rw [hval, vsrc_row_embedded hmono hrows i.isLt]
    refine (hnd i).append ?_ ?_
    · split <;> simp
    · intro a ha hb
      obtain ⟨haN, -⟩ := (hadj i a).mp ha
      by_cases hx : xbit X (i : ℕ) = 1
      · rw [if_pos hx] at hb
        have : a = N := by simpa using hb
        omega
      · rw [if_neg hx] at hb
        exact absurd hb (List.not_mem_nil)

include hmono hlast in
/-- The `vsrc` offsets are monotone (with the extent, the `Csr` shape
of the materialized regions). -/
theorem vsOff_mono : ∀ i < N + 1, vsOff off X ns i ≤ vsOff off X ns (i + 1) := by
  intro i hi
  rcases Nat.lt_or_ge i N with h | h
  · rw [vsOff_of_le (by omega), vsOff_of_le (by omega), xcnt_succ]
    have := hmono i h
    have := xbit_le_one (X := X) i
    omega
  · have hieq : i = N := by omega
    rw [hieq, vsOff_of_le le_rfl, vsOff_top, hlast]
    have := xcnt_le (X := X) N
    omega

include hmono hlast hadj hrows hsrc in
/-- Every stored slot value is a `vsrc` vertex name (`< N + 1`) — read
off the adjacency readout, row by row. -/
theorem vsrc_target_lt (hoff0 : off 0 = 0) :
    ∀ p < ns + 2 * xcnt X N, g p < N + 1 := by
  intro p hp
  have hmono' := vsOff_mono (X := X) (ns := ns) (off := off) hmono hlast
  have h0 : vsOff off X ns 0 = 0 := by
    rw [vsOff_of_le (by omega), hoff0]
    simp
  have htop : p < vsOff off X ns (N + 1) := by
    rw [vsOff_top]
    exact hp
  obtain ⟨i, hi, h1, h2⟩ := exists_owner hmono' h0 htop
  have hmem : g p ∈ Csr.row (vsOff off X ns) g i := by
    have hk : p - vsOff off X ns i < Csr.rowLen (vsOff off X ns) i := by
      unfold Csr.rowLen
      omega
    have hgp : g p = g (vsOff off X ns i + (p - vsOff off X ns i)) := by
      congr 1
      omega
    rw [hgp]
    unfold Csr.row arrOf
    exact List.mem_map.mpr ⟨p - vsOff off X ns i, List.mem_range.mpr hk, rfl⟩
  have hv : ((⟨i, hi⟩ : Fin (N + 1)) : ℕ) = i := rfl
  obtain ⟨hw, -⟩ := (vsrc_mem_row hmono hlast hadj hrows hsrc ⟨i, hi⟩ (g p)).mp
    (by rw [hv]; exact hmem)
  exact hw

include hmono hlast hadj hrows hsrc in
/-- **The readout, bundled**: regions holding the pass facts are
`GraphCsr`-related to `Impl.vsrc H X` at the honest slot count. -/
theorem vsrcCsr_readout (hoff0 : off 0 = 0)
    (hnd : ∀ v : Fin N, (Csr.row off tgt v).Nodup)
    {vo vt : String} {σ : Env}
    (hvo : σ.arrs vo = arrOf (N + 2) (vsOff off X ns))
    (hvt : σ.arrs vt = arrOf (ns + 2 * xcnt X N) g) :
    GraphCsr vo vt (Impl.vsrc H X) (ns + 2 * xcnt X N) σ := by
  refine ⟨vsOff off X ns, g,
    ⟨hvo, hvt, vsOff_mono hmono hlast, vsOff_top,
      vsrc_target_lt hmono hlast hadj hrows hsrc hoff0⟩,
    ?_, vsrc_row_nodup hmono hlast hadj hrows hsrc hnd,
    vsrc_mem_row hmono hlast hadj hrows hsrc⟩
  rw [vsOff_of_le (by omega), hoff0]
  simp

end VsrcReadout

/-! ### §4f `vsrcCom`, assembled -/

/-- **The `vsrc` CSR materialization**: offsets pass, the two closing
offsets (`ns + |X|` and `ns + 2|X|`), the member total saved to
`"pw.t"`, the fill scan, the tail, the source row. -/
def vsrcCom (oa ta xb vo vt nN nS : String) : Com :=
  .seq (vsOffCom oa xb vo nN)
    (.seq (.store vo (.var nN) (.add (.var nS) (.var "pw.k")))
      (.seq (.store vo (.add (.var nN) (.lit 1))
          (.add (.var nS) (.add (.var "pw.k") (.var "pw.k"))))
        (.seq (.assign "pw.t" (.var "pw.k"))
          (.seq (.assign "pw.k" (.lit 0))
            (.seq (.assign "pw.u" (.lit 0))
              (.seq (.assign "pw.j" (.lit 0))
                (.seq (Csr.scan "pw.j" nS (vsFillTurn oa ta xb vt nN))
                  (.seq (vsTailCom oa xb vt nN)
                    (vsSrcCom xb vt nN nS)))))))))

theorem warrs_vsrcCom (oa ta xb vo vt nN nS : String) :
    (vsrcCom oa ta xb vo vt nN nS).warrs = [vo, vo, vo, vt, vt, vt, vt] := rfl

theorem wvars_vsrcCom_subset (oa ta xb vo vt nN nS : String) :
    ∀ y ∈ (vsrcCom oa ta xb vo vt nN nS).wvars, y ∈ pwScalars := by
  intro y hy
  simp only [vsrcCom, vsOffCom, vsOffBody, Csr.scan, vsFillTurn, vsTailCom,
    vsTailBody, vsSrcCom, vsSrcBody, Com.wvars, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hy
  simp only [pwScalars, List.mem_cons, List.not_mem_nil]
  tauto

theorem noWrite_vsrcCom (oa ta xb vo vt nN nS : String) :
    (vsrcCom oa ta xb vo vt nN nS).NoWrite := by
  simp [vsrcCom, vsOffCom, vsOffBody, Csr.scan, vsFillTurn, vsTailCom,
    vsTailBody, vsSrcCom, vsSrcBody, Com.NoWrite]

theorem not_reads_vsrcCom (oa ta xb vo vt nN nS : String) :
    ¬ (vsrcCom oa ta xb vo vt nN nS).reads := by
  simp [vsrcCom, vsOffCom, vsOffBody, Csr.scan, vsFillTurn, vsTailCom,
    vsTailBody, vsSrcCom, vsSrcBody, Com.reads]

section VsrcSpec

variable {B N ns : ℕ} {X : Set (Fin N)} {oa ta xb vo vt nN nS : String}
  {H : SimpleGraph (Fin N)}

/-- **The `vsrc` CSR materialization, discharged**: from the child CSR,
the class bit array and the two exact-length scratch regions, the
regions `vo`/`vt` become `GraphCsr`-related to `Impl.vsrc H X` at the
honest slot count `ns + 2·|X|`, the member total in `"pw.t"`. Charge
`vsrcK = O(N + M + |X|)` (`|X| ≤ N`). Stored values: offsets
`≤ ns + 2N`, targets `≤ N`, counters `≤ N`/`≤ ns` — inside the two `< B`
hypotheses. -/
theorem vsrcCom_spec
    (hvo_oa : vo ≠ oa) (hvo_ta : vo ≠ ta) (hvo_xb : vo ≠ xb)
    (hvt_oa : vt ≠ oa) (hvt_ta : vt ≠ ta) (hvt_xb : vt ≠ xb) (hvt_vo : vt ≠ vo)
    (hnN_scr : nN ∉ pwScalars) (hnS_scr : nS ∉ pwScalars)
    (hNB : N + 2 < B) (hnsB : ns + 2 * N + 1 < B) :
    Spec B
      (fun σ => GraphCsr oa ta H ns σ ∧ FinBits xb X σ ∧
        σ.vars nN = N ∧ σ.vars nS = ns ∧
        (σ.arrs vo).length = N + 2 ∧ (σ.arrs vt).length = ns + 2 * X.ncard)
      (vsrcCom oa ta xb vo vt nN nS)
      (fun _ σ' => GraphCsr vo vt (Impl.vsrc H X) (ns + 2 * X.ncard) σ' ∧
        σ'.vars nN = N ∧ σ'.vars nS = ns ∧ σ'.vars "pw.t" = X.ncard)
      (vsrcK N ns) := by
  have hnN_i : nN ≠ "pw.i" := fun h => hnN_scr (by rw [h]; decide)
  have hnN_k : nN ≠ "pw.k" := fun h => hnN_scr (by rw [h]; decide)
  have hnN_t : nN ≠ "pw.t" := fun h => hnN_scr (by rw [h]; decide)
  have hnN_u : nN ≠ "pw.u" := fun h => hnN_scr (by rw [h]; decide)
  have hnN_j : nN ≠ "pw.j" := fun h => hnN_scr (by rw [h]; decide)
  have hnS_i : nS ≠ "pw.i" := fun h => hnS_scr (by rw [h]; decide)
  have hnS_k : nS ≠ "pw.k" := fun h => hnS_scr (by rw [h]; decide)
  have hnS_t : nS ≠ "pw.t" := fun h => hnS_scr (by rw [h]; decide)
  have hnS_u : nS ≠ "pw.u" := fun h => hnS_scr (by rw [h]; decide)
  have hnS_j : nS ≠ "pw.j" := fun h => hnS_scr (by rw [h]; decide)
  have hvo_vt : vo ≠ vt := Ne.symm hvt_vo
  intro σ hσ
  obtain ⟨⟨off, tgt, hc, hoff0, hnd, hadj⟩, hxb, hn, hs, hvolen, hvtlen⟩ := hσ
  have hxcard : xcnt X N = X.ncard := xcnt_eq_ncard X
  have hxcnN : xcnt X N ≤ N := xcnt_le N
  have hvtlen' : (σ.arrs vt).length = ns + 2 * xcnt X N := by
    rw [hvtlen, hxcard]
  -- 1. the offsets pass (framed: `vt` untouched)
  obtain ⟨σ₁, hr1, hpost1⟩ := ((vsOffCom_spec (X := X) (off := off) (tgt := tgt)
      hvo_oa hvo_ta hvo_xb hnN_i hnN_k hnS_i hnS_k hNB hnsB).frame).run
    ⟨hc, hxb, hn, hs, hvolen⟩
  obtain ⟨⟨hc1, hxb1, hn1, hs1, hk1, f, hf, hfall⟩, hfv1, hfa1, -, -⟩ := hpost1
  have hvt1 : σ₁.arrs vt = σ.arrs vt := by
    refine hfa1 vt ?_
    show vt ∉ (vsOffCom oa xb vo nN).warrs
    simp [vsOffCom, vsOffBody, Com.warrs, hvt_vo]
  -- 2. the row-`N` offset: `ns + |X|`
  have hnval : (Expr.var nN).evalB B σ₁ = some N := by
    have h := evalB_var (B := B) (x := nN) (σ := σ₁) (by rw [hn1]; omega)
    rwa [hn1] at h
  have hval2 : (Expr.add (.var nS) (.var "pw.k")).evalB B σ₁
      = some (ns + xcnt X N) := by
    have h := evalB_bin (B := B) (op := .add)
      (evalB_var (x := nS) (σ := σ₁) (by rw [hs1]; omega))
      (evalB_var (x := "pw.k") (σ := σ₁) (by rw [hk1]; omega))
      (by simp only [Bop.apply_add]; rw [hs1, hk1]; omega)
    simp only [Bop.apply_add] at h
    rw [hs1, hk1] at h
    exact h
  have hst2 : Run B (.store vo (.var nN) (.add (.var nS) (.var "pw.k")))
      σ₁ (σ₁.setArr vo N (ns + xcnt X N)) 5 :=
    (Run.store hnval hval2 (by rw [hf, length_arrOf]; omega)).mono (by simp)
  set σ₂ := σ₁.setArr vo N (ns + xcnt X N) with hσ₂
  -- 3. the end offset: `ns + 2|X|`
  have hidx3 : (Expr.add (.var nN) (.lit 1)).evalB B σ₂ = some (N + 1) := by
    have h2n : σ₂.vars nN = N := by rw [hσ₂, vars_setArr]; exact hn1
    have hev := evalB_incr (B := B) (x := nN) (σ := σ₂) (by rw [h2n]; omega)
    rwa [h2n] at hev
  have hval3 : (Expr.add (.var nS) (.add (.var "pw.k") (.var "pw.k"))).evalB B σ₂
      = some (ns + 2 * xcnt X N) := by
    have h2s : σ₂.vars nS = ns := by rw [hσ₂, vars_setArr]; exact hs1
    have h2k : σ₂.vars "pw.k" = xcnt X N := by rw [hσ₂, vars_setArr]; exact hk1
    have hkk := evalB_bin (B := B) (op := .add)
      (evalB_var (x := "pw.k") (σ := σ₂) (by rw [h2k]; omega))
      (evalB_var (x := "pw.k") (σ := σ₂) (by rw [h2k]; omega))
      (by simp only [Bop.apply_add]; rw [h2k]; omega)
    simp only [Bop.apply_add] at hkk
    rw [h2k] at hkk
    have h := evalB_bin (B := B) (op := .add)
      (evalB_var (x := nS) (σ := σ₂) (by rw [h2s]; omega)) hkk
      (by simp only [Bop.apply_add]; rw [h2s]; omega)
    simp only [Bop.apply_add] at h
    rw [h2s] at h
    have he : xcnt X N + xcnt X N = 2 * xcnt X N := by omega
    rwa [he] at h
  have hst3 : Run B (.store vo (.add (.var nN) (.lit 1))
      (.add (.var nS) (.add (.var "pw.k") (.var "pw.k"))))
      σ₂ (σ₂.setArr vo (N + 1) (ns + 2 * xcnt X N)) 9 :=
    (Run.store hidx3 hval3
      (by rw [hσ₂, length_arrs_setArr, hf, length_arrOf]; omega)).mono (by simp)
  set σ₃ := σ₂.setArr vo (N + 1) (ns + 2 * xcnt X N) with hσ₃
  -- 4. the four scalar headers
  have h3k : σ₃.vars "pw.k" = xcnt X N := by
    rw [hσ₃, vars_setArr, hσ₂, vars_setArr]
    exact hk1
  have ht4 : Run B (.assign "pw.t" (.var "pw.k")) σ₃
      (σ₃.setVar "pw.t" (xcnt X N)) 2 := by
    have hev := evalB_var (B := B) (x := "pw.k") (σ := σ₃) (by rw [h3k]; omega)
    rw [h3k] at hev
    exact (Run.assign hev).mono (by simp)
  set σ₄ := σ₃.setVar "pw.t" (xcnt X N) with hσ₄
  have hk5 : Run B (.assign "pw.k" (.lit 0)) σ₄ (σ₄.setVar "pw.k" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  set σ₅ := σ₄.setVar "pw.k" 0 with hσ₅
  have hu6 : Run B (.assign "pw.u" (.lit 0)) σ₅ (σ₅.setVar "pw.u" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  set σ₆ := σ₅.setVar "pw.u" 0 with hσ₆
  have hj7 : Run B (.assign "pw.j" (.lit 0)) σ₆ (σ₆.setVar "pw.j" 0) 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  set σ₇ := σ₆.setVar "pw.j" 0 with hσ₇
  -- the state before the fill, read back
  have h7vars : ∀ y, y ≠ "pw.t" → y ≠ "pw.k" → y ≠ "pw.u" → y ≠ "pw.j" →
      σ₇.vars y = σ₁.vars y := by
    intro y h1 h2 h3 h4
    rw [hσ₇, vars_setVar_ne h4, hσ₆, vars_setVar_ne h3, hσ₅, vars_setVar_ne h2,
      hσ₄, vars_setVar_ne h1, hσ₃, vars_setArr, hσ₂, vars_setArr]
  have h7arr : ∀ b, b ≠ vo → σ₇.arrs b = σ₁.arrs b := by
    intro b hb
    rw [hσ₇, arrs_setVar, hσ₆, arrs_setVar, hσ₅, arrs_setVar, hσ₄, arrs_setVar,
      hσ₃, arrs_setArr_ne hb, hσ₂, arrs_setArr_ne hb]
  have h7vo : σ₇.arrs vo = ((arrOf (N + 2) f).set N (ns + xcnt X N)).set (N + 1)
      (ns + 2 * xcnt X N) := by
    rw [hσ₇, arrs_setVar, hσ₆, arrs_setVar, hσ₅, arrs_setVar, hσ₄, arrs_setVar,
      hσ₃, arrs_setArr_self, hσ₂, arrs_setArr_self, hf]
  have h7n : σ₇.vars nN = N := by
    rw [h7vars nN hnN_t hnN_k hnN_u hnN_j]
    exact hn1
  have h7s : σ₇.vars nS = ns := by
    rw [h7vars nS hnS_t hnS_k hnS_u hnS_j]
    exact hs1
  have h7t : σ₇.vars "pw.t" = xcnt X N := by
    rw [hσ₇, vars_setVar_ne (by decide), hσ₆, vars_setVar_ne (by decide),
      hσ₅, vars_setVar_ne (by decide), hσ₄, vars_setVar_self]
  have h7k : σ₇.vars "pw.k" = 0 := by
    rw [hσ₇, vars_setVar_ne (by decide), hσ₆, vars_setVar_ne (by decide),
      hσ₅, vars_setVar_self]
  have h7u : σ₇.vars "pw.u" = 0 := by
    rw [hσ₇, vars_setVar_ne (by decide), hσ₆, vars_setVar_self]
  have h7j : σ₇.vars "pw.j" = 0 := by
    rw [hσ₇, vars_setVar_self]
  -- 5. the fill
  have hFill7 : FillInv oa ta xb vt nN nS ns off tgt X σ₇ := by
    refine ⟨hc1.of_eq (h7arr oa (Ne.symm hvo_oa)) (h7arr ta (Ne.symm hvo_ta)),
      ⟨by rw [h7arr xb (Ne.symm hvo_xb)]; exact hxb1.1,
        fun v => by rw [h7arr xb (Ne.symm hvo_xb)]; exact hxb1.2 v⟩,
      h7n, h7s, h7t,
      by rw [h7u]; omega, by rw [h7j]; omega,
      by rw [h7u, h7j, hoff0], by rw [h7u, h7j]; intro _; omega,
      by rw [h7k, h7u]; simp,
      ?_⟩
    refine ⟨fun p => (σ.arrs vt).getD p 0, ?_, ?_, ?_⟩
    · rw [h7arr vt hvt_vo, hvt1, ← hvtlen']
      exact (arrOf_getD (σ.arrs vt)).symm
    · intro i hi
      rw [h7u] at hi
      omega
    · intro q h1 h2
      rw [h7j] at h2
      omega
  obtain ⟨σ₈, hr8, hpost8⟩ :=
    ((vsFillCom_spec hvt_oa hvt_ta hvt_xb hnN_scr hnS_scr hNB hnsB).frame).run hFill7
  obtain ⟨⟨hI8, hj8⟩, hfv8, hfa8, -, -⟩ := hpost8
  have hvo8 : σ₈.arrs vo = σ₇.arrs vo := by
    refine hfa8 vo ?_
    show vo ∉ (Csr.scan "pw.j" nS (vsFillTurn oa ta xb vt nN)).warrs
    simp [vsFillTurn, Com.warrs, hvo_vt]
  -- 6. the tail
  obtain ⟨hc8, hxb8, hn8, hs8, ht8, hu8, hj8', hlo8, hhi8, hk8, g8, hg8, hdone8,
    hpart8⟩ := hI8
  have hTail8 : TailInv oa ta xb vt nN nS ns off tgt X σ₈ := by
    refine ⟨hc8, hxb8, hn8, hs8, ht8, hu8, ?_, hk8, g8, hg8, hdone8, ?_⟩
    · intro h
      have h1 := hhi8 h
      have h2 := hc8.le_ns (i := σ₈.vars "pw.u" + 1) (by omega)
      omega
    · intro q h1 h2
      exact hpart8 q h1 (by omega)
  obtain ⟨σ₉, hr9, hpost9⟩ :=
    ((vsTailCom_spec hvt_oa hvt_ta hvt_xb hnN_scr hnS_scr hNB hnsB).frame).run hTail8
  obtain ⟨⟨hI9, hu9⟩, hfv9, hfa9, -, -⟩ := hpost9
  have hvo9 : σ₉.arrs vo = σ₈.arrs vo := by
    refine hfa9 vo ?_
    show vo ∉ (vsTailCom oa xb vt nN).warrs
    simp [vsTailCom, vsTailBody, Com.warrs, hvo_vt]
  obtain ⟨hc9, hxb9, hn9, hs9, ht9, -, -, -, g9, hg9, hdone9, -⟩ := hI9
  -- 7. the source row
  obtain ⟨σz, hr10, hpost10⟩ :=
    ((vsSrcCom_spec (X := X) hvt_xb hnN_scr hnS_scr hNB hnsB).frame).run
    ⟨hxb9, hn9, hs9, ht9, by rw [hg9, length_arrOf]⟩
  obtain ⟨⟨hxb10, hn10, hs10, ht10, g', hg', hagree, hsrc⟩, hfv10, hfa10, -, -⟩ :=
    hpost10
  have hvo10 : σz.arrs vo = σ₉.arrs vo := by
    refine hfa10 vo ?_
    show vo ∉ (vsSrcCom xb vt nN nS).warrs
    simp [vsSrcCom, vsSrcBody, Com.warrs, hvo_vt]
  -- the rows transfer onto the final cell function
  have hag : ∀ p, p < ns + xcnt X N → g' p = g9 p := by
    intro p hp
    rw [hagree p hp, hg9, getD_arrOf _ (by omega)]
  have hrows' : ∀ i < N, VRowDone off tgt X i g' := by
    intro i hi
    have hoffN : off (i + 1) ≤ ns := hc.le_ns (by omega)
    have hxci : xcnt X i ≤ xcnt X N := xcnt_mono (by omega)
    refine vrowdone_of_agree (hdone9 i (by omega)) ?_ ?_
    · intro q h1 h2
      exact hag _ (by omega)
    · intro hb
      have := xcnt_lt_of_bit hi hb
      exact hag _ (by omega)
  -- the offsets region, in `vsOff` form
  have hvoF : σz.arrs vo = arrOf (N + 2) (vsOff off X ns) := by
    rw [hvo10, hvo9, hvo8, h7vo, set_arrOf, set_arrOf]
    refine arrOf_congr fun p hp => ?_
    by_cases hp1 : p = N + 1
    · rw [if_pos hp1, hp1, vsOff_top]
    · rw [if_neg hp1]
      by_cases hp0 : p = N
      · rw [if_pos hp0, hp0, vsOff_of_le le_rfl, hc.last]
      · rw [if_neg hp0, vsOff_of_le (by omega), hfall p (by omega)]
  -- assemble
  refine ⟨σz, ?_, ?_, hn10, hs10, by rw [ht10, hxcard]⟩
  · -- the run, at the announced cost
    have h := hr1.seq (hst2.seq (hst3.seq (ht4.seq (hk5.seq (hu6.seq
      (hj7.seq (hr8.seq (hr9.seq hr10))))))))
    refine h.mono ?_
    unfold vsrcK
    omega
  · -- the `GraphCsr` at `Impl.vsrc H X`
    rw [← hxcard]
    exact vsrcCsr_readout (N := N) (ns := ns) (X := X) (off := off) (tgt := tgt)
      (H := H) (g := g') (fun i hi => hc.off_le_succ hi) hc.last hadj hrows'
      hsrc hoff0 hnd hvoF hg'

end VsrcSpec

end Lax3Proofs.Prog
