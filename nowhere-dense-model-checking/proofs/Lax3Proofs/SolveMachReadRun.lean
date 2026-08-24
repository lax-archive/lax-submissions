import Lax3Proofs.SolveMachRead
import Lax3Proofs.SolveSeamTop

/-!
# F6c12 (residual 2) — the scatter-and-readback pass, as a program

`SolveSegRead` named **`ReadRows`** — the machine pass that, from the
loop invariant at centre `u` plus the inner block's postcondition at the
child, writes **exactly the centre-`u` rows** of the level table at the
recursive clause's bits and touches nothing else — and `SolveMachRead`
landed the per-atom bit bridges. What was left is *programs and frames*,
and that is what this file supplies.

* **`rowAtoms S j`** is the level's compile-time scatter-atom list: the
  scatter atoms of every schedule row's decomposition, concatenated over
  `F S j`. Duplicated atoms are harmless (a later occurrence rewrites its
  own slot with the same bit and `memIdx` reads the first occurrence's).
* **The per-atom scatters are the landed stage, verbatim**: the pass runs
  `topAtomsCom` (`SolveSeamTop`, F6c9b) at the **level-`(j+1)` names** —
  the isolated child's regions — over `rowAtoms S j`. Its `t = 0` guard
  and its budget `topScatK` are the landed ones, unweakened.
* **`readLoopCom`** is the readback: a counted scan over the child's own
  carrier. `CLInv`'s `ClusterCsr` row of `u` holds `Impl.restrictEmb`'s
  enumeration of `cluster S A π u`, and `restrictEmb` and `childEquiv`
  are the **same map** (both are `Driver.setEquiv` of the cluster —
  `restrictEmb_eq_childName` is `rfl`), so cell `cm[base + t]` is the
  parent name of child name `t`: the `v ↔ vc` correspondence the compiled
  row needs, read as data rather than computed. The centre guard
  `ca[v] = u` keeps the write-once discipline: `cluster u` is a superset
  of `{v | centre v = u}` (covers overlap by design — that is what the
  cover degree `D(N)` counts), and only the fibre is written.
* **`rowsCom`** unrolls the schedule family: one store per row, of the
  compiled combination `bcExprA` over the child's table cells and the
  scatter slots. `bcExprA_evalB_rowEval` plus the two landed bit bridges
  pin its value to `RowEval`'s bit.
* **`readRows_of`** concludes `ReadRows` and **`readRowsAll_of`**
  concludes **verbatim `ReadRowsAll`**, at the honest budget `readK`
  (the landed `topScatK` at the child's dimensions plus the scan).

All five postcondition clauses are proved: the centre's rows, every
other row's cells, the level's scalars, the cover's three arrays and the
five non-table regions, and **no reallocation** — the last for free,
since every command of the pass is an assignment or a store.

## Findings

1. `SolveBlocksRestrict`'s seam finding 1 ("`Driver.setEquiv` is
   `Classical`-chosen, not the sorted enumeration") is **stale**:
   `DriverArena.setEquiv` is now built from `Finset.orderIsoOfFin`, so
   the repin it asked for has happened. This file does not depend on the
   *order*, only on the identity `restrictEmb = childEquiv`, which is
   `rfl` for any pin; the order is what the cover stage owes when it
   emits the row.
2. `SolveStep`'s docstring calls the cluster row "the `v ↔ vc`
   correspondence carried by `CLInv`'s `ClusterCsr`" — accurate, but it
   does not say that the row enumerates `cluster u`, which is *larger*
   than `{v | centre v = u}`. The centre guard is therefore not
   optional; without it the pass would write rows it does not own, and
   `ReadRows`'s second clause would fail.
3. `ReadRows` quantifies over every `(k, j, A)` on the diagonal, but the
   pass needs neither the diagonal, nor `Adm`, nor `¬ A.G = ⊥`:
   `readRows_of` discharges the residual with those three hypotheses
   unused. They are still in the residual's statement, so nothing is
   weakened — the pass simply holds on more inputs than asked.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.LocalityFun

variable {L n₀ : ℕ}

/-! ## §0 Arithmetic and list plumbing -/

/-- Indexing at equal positions. -/
theorem getElem_of_eq_idx {α : Type*} {l : List α} {a b : ℕ}
    (ha : a < l.length) (hb : b < l.length) (h : a = b) : l[a]'ha = l[b]'hb := by
  subst h; rfl

/-- Every cluster of a cover of `Fin N` has at most `N` members. -/
theorem ncard_le_carrier {N : ℕ} (X : Set (Fin N)) : X.ncard ≤ N := by
  have h1 := Set.ncard_le_ncard (Set.subset_univ X) Set.finite_univ
  simpa [Set.ncard_univ, Nat.card_eq_fintype_card] using h1

/-- **The cluster row, with its offset bounded**: `ClusterCsr.read_row`
plus the quadratic bound on the offsets — `offC m = Σ_{u<m} |X_u| ≤ m·N`
straight off the CSR's own step equation. The bound is what makes the
row's cells addressable under the word bound `N² < B` without a new
hypothesis. -/
theorem clusterCsr_row_le {co cm : String} {N : ℕ} {Xf : Fin N → Set (Fin N)}
    {σ : Env} (h : ClusterCsr co cm Xf σ) (u : Fin N) :
    ∃ base : ℕ, base + (Xf u).ncard ≤ N * N ∧
      base + (Xf u).ncard ≤ (σ.arrs cm).length ∧
      (σ.arrs co).getD (u : ℕ) 0 = base ∧
      ∀ t : ℕ, ∀ ht : t < (Xf u).ncard,
        (σ.arrs cm).getD (base + t) 0 = (Impl.restrictEmb (Xf u) ⟨t, ht⟩ : ℕ) := by
  obtain ⟨base, hlen, hbase, hcell⟩ := h.read_row u
  obtain ⟨offC, h0, -, hco, hstep, -, -⟩ := h
  have hbe : base = offC (u : ℕ) := by
    rw [← hbase]
    exact hco (u : ℕ) (le_of_lt u.2)
  have hoff : ∀ m, m ≤ N → offC m ≤ m * N := by
    intro m
    induction m with
    | zero => intro _; omega
    | succ m ih =>
      intro hm
      have h1 : offC (m + 1) = offC m + (Xf ⟨m, by omega⟩).ncard := hstep ⟨m, by omega⟩
      have h2 := ih (by omega)
      have h3 := ncard_le_carrier (Xf ⟨m, by omega⟩)
      have h4 : (m + 1) * N = m * N + N := by ring
      omega
  refine ⟨base, ?_, hlen, hbase, hcell⟩
  have h1 : offC ((u : ℕ) + 1) = offC (u : ℕ) + (Xf u).ncard := hstep u
  have h2 := hoff ((u : ℕ) + 1) (by have := u.2; omega)
  have h3 : ((u : ℕ) + 1) * N ≤ N * N :=
    Nat.mul_le_mul_right _ (by have := u.2; omega)
  omega

/-! ## §1 The child's names, as the cluster row reads them -/

/-- The parent name of a child name — the value `ClusterCsr`'s row
holds. -/
noncomputable def childName (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) (t : Fin (childN S A π u)) : Fin A.N :=
  ((childEquiv S A π u) t : Fin A.N)

/-- **The cluster row IS the child's enumeration** — definitional, after
the `setEquiv` repin to `Finset.orderIsoOfFin`: `Impl.restrictEmb` and
`childEquiv` are the same map. -/
theorem restrictEmb_eq_childName (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) (t : Fin (childN S A π u)) :
    (Impl.restrictEmb (cluster S A π u) t : Fin A.N) = childName S A π u t := rfl

/-- The child's enumeration is injective — one write per child name. -/
theorem childName_inj (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) {s t : Fin (childN S A π u)}
    (h : childName S A π u s = childName S A π u t) : s = t := by
  have h' : (childEquiv S A π u) s = (childEquiv S A π u) t := Subtype.ext h
  exact (childEquiv S A π u).injective h'

/-- Reading the child name back off the parent name — the rewrite the
local-atom bridge's index needs. -/
theorem childEquiv_symm_childName (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) (t : Fin (childN S A π u))
    (h : childName S A π u t ∈ cluster S A π u) :
    (childEquiv S A π u).symm ⟨childName S A π u t, h⟩ = t := by
  have he : (⟨childName S A π u t, h⟩ : ↥(cluster S A π u)) = (childEquiv S A π u) t :=
    Subtype.ext rfl
  rw [he, Equiv.symm_apply_apply]

/-- The child carrier is the cluster, counted. -/
theorem childN_eq_ncard (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    childN S A π u = (cluster S A π u).ncard := rfl

/-- A child name is below the parent carrier. -/
theorem childN_le (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) : childN S A π u ≤ A.N :=
  ncard_le_carrier _

/-! ## §2 The level's scatter atoms -/

/-- **The level's scatter-atom list**: every scatter atom of every
schedule row's decomposition, concatenated over `F S j`. Duplicates are
kept — `memIdx` reads the first occurrence's slot and every occurrence
stores the same bit. -/
noncomputable def rowAtoms (S : Setup L) (j : ℕ) :
    List (ScatterSentence (S.pal (j + 1))) :=
  (F S j).flatMap fun γ =>
    scatterAtoms S.choice (stepFml S γ.fml) (drank_stepFml S γ.drank)

/-- Every scatter atom of a schedule row's decomposition is in the
list. -/
theorem mem_rowAtoms {S : Setup L} {j : ℕ} {γ : Fml S j} (hγ : γ ∈ F S j)
    {σa : ScatterSentence (S.pal (j + 1))} (hσ : Sum.inr σa ∈ (dec S γ).atoms) :
    σa ∈ rowAtoms S j :=
  List.mem_flatMap.mpr ⟨γ, hγ, mem_scatterAtoms.mpr hσ⟩

/-- Every listed atom's `β`-formula is a column of the child's family —
the column the scatter stage extracts. -/
theorem beta_mem_of_mem_rowAtoms {S : Setup L} {j : ℕ}
    {σa : ScatterSentence (S.pal (j + 1))} (h : σa ∈ rowAtoms S j) :
    σa.β ∈ levelFml S (j + 1) := by
  obtain ⟨γ, hγ, hmem⟩ := List.mem_flatMap.mp h
  exact scatterAtom_beta_mem_levelFml hγ (mem_scatterAtoms.mp hmem)

/-! ## §3 The programs -/

/-- **The atom reads of a compiled row**: a local atom is a cell of the
child's table region at the current child name `rd.t`; a scatter atom is
its slot of the stage's bit region. -/
noncomputable def readAv (S : Setup L) (j : ℕ) (tb1 rsb : String) :
    DistFO (S.pal (j + 1)) 1 ⊕ ScatterSentence (S.pal (j + 1)) → Expr
  | .inl ψ => .get tb1 (.add (.mul (.var "rd.t") (.lit (levelFml S (j + 1)).length))
      (.lit (memIdx (levelFml S (j + 1)) ψ)))
  | .inr σa => .get rsb (.lit (memIdx (rowAtoms S j) σa))

/-- One schedule row's store: the compiled combination into the current
parent row's cell `i`. -/
noncomputable def rowStoreCom (S : Setup L) (j : ℕ) (tb0 tb1 rsb : String)
    (γ : Fml S j) (i : ℕ) : Com :=
  .store tb0 (.add (.mul (.var "rd.v") (.lit (levelFml S j).length)) (.lit i))
    (bcExprA (readAv S j tb1 rsb) (dec S γ))

/-- **One parent row, written**: one store per schedule formula, slots by
list position. -/
noncomputable def rowsCom (S : Setup L) (j : ℕ) (tb0 tb1 rsb : String) :
    List (Fml S j) → ℕ → Com
  | [], _ => .skip
  | γ :: rest, i =>
    .seq (rowStoreCom S j tb0 tb1 rsb γ i) (rowsCom S j tb0 tb1 rsb rest (i + 1))

/-- One turn of the readback scan: the parent name of the current child
name, the centre guard, the row, the bump. -/
def readTurnCom (j : ℕ) (ca cm : String) (rows : Com) : Com :=
  .seq (.assign "rd.v" (.get cm (.add (.var "rd.b") (.var "rd.t"))))
    (.seq (.ite (.eq (.get ca (.var "rd.v")) (.var (ctrName j))) rows .skip)
      (.assign "rd.t" (.add (.var "rd.t") (.lit 1))))

/-- **The readback**: load the cluster row's base, then scan the child's
carrier. -/
def readLoopCom (j : ℕ) (ca co cm : String) (rows : Com) : Com :=
  .seq (.assign "rd.b" (.get co (.var (ctrName j))))
    (.seq (.assign "rd.t" (.lit 0))
      (.while (.lt (.var "rd.t") (.var (arenaNames (j + 1)).nN))
        (readTurnCom j ca cm rows)))

/-- **The scatter-and-readback pass**: the landed per-atom scatter stage
on the isolated child, then the readback of the centre's rows. -/
noncomputable def readPassCom (S : Setup L) (j : ℕ)
    (ca co cm pa ma da rsb : String) : Com :=
  .seq
    (topAtomsCom (arenaNames (j + 1)) pa ma da rsb (levelFml S (j + 1)).length
      (fun σa => memIdx (levelFml S (j + 1)) σa.β) (rowAtoms S j) 0)
    (readLoopCom j ca co cm
      (rowsCom S j (arenaNames j).tab (arenaNames (j + 1)).tab rsb (F S j) 0))

/-! ## §4 The budgets -/

/-- One parent row's price: per schedule formula, a store of the
compiled combination (`1 + 5` for the index plus the expression). -/
noncomputable def rowsK (S : Setup L) (j : ℕ) (tb1 rsb : String) :
    List (Fml S j) → ℕ
  | [] => 1
  | γ :: rest =>
    6 + (bcExprA (readAv S j tb1 rsb) (dec S γ)).size + rowsK S j tb1 rsb rest

/-- The readback's price: the base load, then one turn per child name —
the parent-name read (5), the guard (5), one row, the bump (4). -/
noncomputable def readLoopK (S : Setup L) (j : ℕ) (tb1 rsb : String)
    (cN : ℕ) : ℕ :=
  3 + ((14 + rowsK S j tb1 rsb (F S j)) + 4) * cN + 6

open Classical in
/-- **The pass's budget**: the landed scatter stage at the child's own
dimensions (`topScatK`, whose `t = 0` guard is priced inside `scatterK`)
plus the readback's scan over the child's carrier. Off the carrier the
value is `0` — there is no centre there and the `Spec` is vacuous. -/
noncomputable def readK (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (rsb : String) (_k j : ℕ) (A : Arena (S.pal j) n₀) (m : ℕ) : ℕ :=
  if h : m < A.N then
    topScatK (childN S A ((ord A.N A.G).order) ⟨m, h⟩)
        (∑ z : Fin (childArena S A ((ord A.N A.G).order) ⟨m, h⟩).N,
          (childArena S A ((ord A.N A.G).order) ⟨m, h⟩).G.degree z)
        (rowAtoms S j)
      + readLoopK S j (arenaNames (j + 1)).tab rsb
          (childN S A ((ord A.N A.G).order) ⟨m, h⟩)
  else 0

/-! ## §5 One parent row, written -/

/-- A row-major index expression, evaluated. -/
theorem evalB_rowIdx {B : ℕ} {σ : Env} {x : String} {F i : ℕ}
    (hxB : σ.vars x < B) (hF : F < B) (hi : i < B)
    (hsum : σ.vars x * F + i < B) :
    (Expr.add (.mul (.var x) (.lit F)) (.lit i)).evalB B σ
      = some (σ.vars x * F + i) := by
  have hmul : (Expr.mul (.var x) (.lit F)).evalB B σ = some (σ.vars x * F) := by
    rw [Expr.mul_def]
    have h := evalB_bin (op := .mul) (evalB_var hxB) (evalB_lit hF)
      (by rw [Bop.apply_mul]; omega)
    rwa [Bop.apply_mul] at h
  rw [Expr.add_def]
  have h := evalB_bin (op := .add) hmul (evalB_lit hi)
    (by rw [Bop.apply_add]; omega)
  rwa [Bop.apply_add] at h

open Classical in
/-- **What one parent row's writes run in**: the scan's two cells, the
child's table region, the stage's scatter slots and the level table's
allocation. Every clause survives a store into the level table. -/
def RowSt (S : Setup L) (ord : CoverSpec.OrderingRoutine) (k j : ℕ)
    (A : Arena (S.pal j) n₀) (u : Fin A.N) (tb0 tb1 rsb : String)
    (t : ℕ) (v : Fin A.N) (σ : Env) : Prop :=
  σ.vars "rd.t" = t ∧ σ.vars "rd.v" = (v : ℕ) ∧
  TableBitsW tb1 (levelFml S (j + 1))
    (Unroll.unrollAux S ord k (j + 1)
      (childArena S A ((ord A.N A.G).order) u)) σ ∧
  (rowAtoms S j).length ≤ (σ.arrs rsb).length ∧
  (∀ (m : ℕ) (hm : m < (rowAtoms S j).length),
    (σ.arrs rsb).getD m 0
      = if (rowAtoms S j)[m].t ≤ Impl.greedyScatter
          (childArena S A ((ord A.N A.G).order) u).G (rowAtoms S j)[m].r
          {z | Unroll.unrollAux S ord k (j + 1)
            (childArena S A ((ord A.N A.G).order) u) z (rowAtoms S j)[m].β}
          (rowAtoms S j)[m].t then 1 else 0) ∧
  A.N * (levelFml S j).length ≤ (σ.arrs tb0).length

open Classical in
/-- **Every atom of a schedule row reads its bit**: the local atoms off
the child's table region at the scan's child name (`rowAsn_local_bit`),
the scatter atoms off the stage's slot region (`rowAsn_scatter_bit`,
through the choice seam). This is `bcExprA_evalB_rowEval`'s `hav`
premise, at the addresses `readAv` names. -/
theorem readAv_evalB {B : ℕ} (h1B : 1 < B) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (k j : ℕ) (A : Arena (S.pal j) n₀)
    (u : Fin A.N) (tb0 tb1 rsb : String) (hchoice : S.choice = greedyChoice)
    (hcB : childN S A ((ord A.N A.G).order) u < B)
    (hF1B : (levelFml S (j + 1)).length < B)
    (hNF1 : childN S A ((ord A.N A.G).order) u * (levelFml S (j + 1)).length < B)
    (hMB : (rowAtoms S j).length < B)
    {t : ℕ} (ht : t < childN S A ((ord A.N A.G).order) u)
    {v : Fin A.N} (hvt : childName S A ((ord A.N A.G).order) u ⟨t, ht⟩ = v)
    (hv : centre S A ((ord A.N A.G).order) v = u)
    {γ : Fml S j} (hγ : γ ∈ F S j)
    {σ : Env} (hσ : RowSt S ord k j A u tb0 tb1 rsb t v σ) :
    ∀ a ∈ (dec S γ).atoms,
      (readAv S j tb1 rsb a).evalB B σ
        = some (if rowAsn S ord k j A v a then 1 else 0) := by
  obtain ⟨hrt, -, hT1, hrsbL, hrsbV, -⟩ := hσ
  rintro (ψ | σa) hmem
  · -- a local atom: a cell of the child's table region
    have hψ : ψ ∈ levelFml S (j + 1) := localAtom_mem_levelFml hγ hmem
    have hbi : memIdx (levelFml S (j + 1)) ψ < (levelFml S (j + 1)).length :=
      memIdx_lt hψ
    have hiψ : (levelFml S (j + 1))[memIdx (levelFml S (j + 1)) ψ]'hbi = ψ :=
      getElem_memIdx hψ
    have hsym : ((childEquiv S A ((ord A.N A.G).order) u).symm
        ⟨v, hv ▸ mem_cluster_centre S A ((ord A.N A.G).order) v⟩
        : Fin (childN S A ((ord A.N A.G).order) u)) = ⟨t, ht⟩ := by
      subst hvt
      exact childEquiv_symm_childName S A ((ord A.N A.G).order) u ⟨t, ht⟩ _
    have hbit := rowAsn_local_bit S ord hv hT1 hbi hiψ
    rw [hsym] at hbit
    -- the index is inside the region and below the bound
    have hidxlt : t * (levelFml S (j + 1)).length
        + memIdx (levelFml S (j + 1)) ψ
        < childN S A ((ord A.N A.G).order) u * (levelFml S (j + 1)).length :=
      tableIdx_lt (⟨t, ht⟩ : Fin (childN S A ((ord A.N A.G).order) u)) hbi
    have hlen : t * (levelFml S (j + 1)).length
        + memIdx (levelFml S (j + 1)) ψ < (σ.arrs tb1).length :=
      lt_of_lt_of_le hidxlt hT1.1
    have hidx : (Expr.add (.mul (.var "rd.t") (.lit (levelFml S (j + 1)).length))
        (.lit (memIdx (levelFml S (j + 1)) ψ))).evalB B σ
        = some (t * (levelFml S (j + 1)).length
          + memIdx (levelFml S (j + 1)) ψ) := by
      have h := evalB_rowIdx (σ := σ) (x := "rd.t")
        (F := (levelFml S (j + 1)).length)
        (i := memIdx (levelFml S (j + 1)) ψ)
        (by rw [hrt]; omega) hF1B (by omega) (by rw [hrt]; omega)
      rwa [hrt] at h
    show (Expr.get tb1 _).evalB B σ = _
    refine evalB_get hidx ?_ (by split <;> omega)
    rw [List.getElem?_eq_getElem hlen]
    refine congrArg some ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen,
      Option.getD_some] at hbit
    exact hbit
  · -- a scatter atom: its slot of the stage's bit region
    have hσa : σa ∈ rowAtoms S j := mem_rowAtoms hγ hmem
    have hm : memIdx (rowAtoms S j) σa < (rowAtoms S j).length := memIdx_lt hσa
    have hgm : (rowAtoms S j)[memIdx (rowAtoms S j) σa]'hm = σa :=
      getElem_memIdx hσa
    have hcell := hrsbV (memIdx (rowAtoms S j) σa) hm
    rw [hgm] at hcell
    rw [rowAsn_scatter_bit S ord hv hchoice σa] at hcell
    have hlen : memIdx (rowAtoms S j) σa < (σ.arrs rsb).length := by omega
    show (Expr.get rsb _).evalB B σ = _
    refine evalB_get (evalB_lit (by omega)) ?_ (by split <;> omega)
    rw [List.getElem?_eq_getElem hlen]
    refine congrArg some ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlen,
      Option.getD_some] at hcell
    exact hcell

open Classical in
/-- **One parent row's `Spec`**: from `RowSt`, the unrolled store
sequence writes cells `i₀ … i₀+|l|−1` of row `v` at the recursive
clause's bits, touches no other cell of the level table, no other array
and no scalar, and preserves every length. -/
theorem rowsCom_spec {B : ℕ} (h1B : 1 < B) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (k j : ℕ) (A : Arena (S.pal j) n₀)
    (u : Fin A.N) (tb0 tb1 rsb : String) (hchoice : S.choice = greedyChoice)
    (htb01 : tb1 ≠ tb0) (htb0r : rsb ≠ tb0)
    (hcB : childN S A ((ord A.N A.G).order) u < B)
    (hF1B : (levelFml S (j + 1)).length < B)
    (hNF1 : childN S A ((ord A.N A.G).order) u * (levelFml S (j + 1)).length < B)
    (hMB : (rowAtoms S j).length < B) (hNB : A.N < B)
    (hF0B : (levelFml S j).length < B)
    (hNF0 : A.N * (levelFml S j).length < B)
    {t : ℕ} (ht : t < childN S A ((ord A.N A.G).order) u)
    {v : Fin A.N} (hvt : childName S A ((ord A.N A.G).order) u ⟨t, ht⟩ = v)
    (hv : centre S A ((ord A.N A.G).order) v = u) :
    ∀ (l : List (Fml S j)) (i0 : ℕ),
    (∀ (m : ℕ) (hm : m < l.length), ∃ h : i0 + m < (F S j).length,
      (F S j)[i0 + m]'h = l[m]'hm) →
    Spec B (RowSt S ord k j A u tb0 tb1 rsb t v)
      (rowsCom S j tb0 tb1 rsb l i0)
      (fun σ σ' => RowSt S ord k j A u tb0 tb1 rsb t v σ' ∧
        (∀ (m : ℕ) (hm : m < l.length),
          (σ'.arrs tb0).getD ((v : ℕ) * (levelFml S j).length + (i0 + m)) 0
            = if RowEval S ord k j A v (l[m]'hm).fml then 1 else 0) ∧
        (∀ b, b ≠ tb0 → σ'.arrs b = σ.arrs b) ∧
        (∀ y, σ'.vars y = σ.vars y) ∧
        (∀ p, ¬ ((v : ℕ) * (levelFml S j).length + i0 ≤ p ∧
            p < (v : ℕ) * (levelFml S j).length + i0 + l.length) →
          (σ'.arrs tb0).getD p 0 = (σ.arrs tb0).getD p 0) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (rowsK S j tb1 rsb l) := by
  intro l
  induction l with
  | nil =>
    intro i0 _
    refine Spec.skip.post ?_
    rintro σ σ' hσ rfl
    exact ⟨hσ, fun m hm => absurd hm (Nat.not_lt_zero m), fun b _ => rfl,
      fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
  | cons γ rest ih =>
    intro i0 hl
    obtain ⟨hi0, hγeq⟩ := hl 0 (by simp)
    have hγ : γ ∈ F S j := by
      have := List.getElem_mem hi0
      rwa [hγeq] at this
    have hi0F : i0 < (levelFml S j).length := by
      rw [levelFml_length]; omega
    -- the value of the compiled row
    have hval : ∀ σ, RowSt S ord k j A u tb0 tb1 rsb t v σ →
        (bcExprA (readAv S j tb1 rsb) (dec S γ)).evalB B σ
          = some (if RowEval S ord k j A v γ.fml then 1 else 0) := by
      intro σ hσ
      exact bcExprA_evalB_rowEval h1B S ord k j A v ⟨γ.isLocal, γ.drank⟩
        (readAv_evalB h1B S ord k j A u tb0 tb1 rsb hchoice hcB hF1B hNF1 hMB
          ht hvt hv hγ hσ)
    -- the store's index
    have hrow : (v : ℕ) * (levelFml S j).length + i0
        < A.N * (levelFml S j).length := tableIdx_lt v hi0F
    have hidxE : ∀ σ, RowSt S ord k j A u tb0 tb1 rsb t v σ →
        (Expr.add (.mul (.var "rd.v") (.lit (levelFml S j).length))
          (.lit i0)).evalB B σ
          = some ((v : ℕ) * (levelFml S j).length + i0) := by
      intro σ hσ
      have hrv : σ.vars "rd.v" = (v : ℕ) := hσ.2.1
      have hvB : σ.vars "rd.v" < B := by rw [hrv]; have := v.2; omega
      have hsB : σ.vars "rd.v" * (levelFml S j).length + i0 < B := by
        rw [hrv]; omega
      have h := evalB_rowIdx (σ := σ) (x := "rd.v")
        (F := (levelFml S j).length) (i := i0) hvB hF0B (by omega) hsB
      rw [hrv] at h
      exact h
    -- the store
    have hstore : Spec B (RowSt S ord k j A u tb0 tb1 rsb t v)
        (rowStoreCom S j tb0 tb1 rsb γ i0)
        (fun σ σ' => σ' = σ.setArr tb0
          ((v : ℕ) * (levelFml S j).length + i0)
          (if RowEval S ord k j A v γ.fml then 1 else 0))
        (6 + (bcExprA (readAv S j tb1 rsb) (dec S γ)).size) := by
      have h := Spec.store (B := B) (a := tb0)
        (i := Expr.add (.mul (.var "rd.v") (.lit (levelFml S j).length))
          (.lit i0))
        (e := bcExprA (readAv S j tb1 rsb) (dec S γ))
        (idx := fun _ => (v : ℕ) * (levelFml S j).length + i0)
        (f := fun _ => if RowEval S ord k j A v γ.fml then 1 else 0)
        (P := RowSt S ord k j A u tb0 tb1 rsb t v)
        hidxE hval (fun σ hσ => lt_of_lt_of_le hrow hσ.2.2.2.2.2)
      exact h.mono (by simp [Expr.size])
    -- the rest of the row
    have hrest := ih (i0 + 1) (fun m hm => by
      obtain ⟨h1, h2⟩ := hl (m + 1) (by simpa using hm)
      refine ⟨by omega, ?_⟩
      refine (getElem_of_eq_idx _ h1 (by omega)).trans ?_
      simpa using h2)
    refine (Spec.seq hstore hrest ?_ ?_).mono (by rw [rowsK])
    · -- `RowSt` survives one store
      rintro σ σ' hσ rfl
      obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hσ
      refine ⟨h1, h2, ?_, ?_, ?_, ?_⟩
      · exact tableBitsW_of_eq h3 (by simp [htb01])
      · simpa [htb0r] using h4
      · intro m hm
        rw [arrs_setArr, if_neg htb0r]
        exact h5 m hm
      · simpa using h6
    · rintro σ σ' σ'' hP rfl ⟨hSt'', hcells'', hoth'', hvars'', hrange'', hlen''⟩
      have hlenσ' : ∀ b, ((σ.setArr tb0
          ((v : ℕ) * (levelFml S j).length + i0)
          (if RowEval S ord k j A v γ.fml then 1 else 0)).arrs b).length
          = (σ.arrs b).length := fun b => length_arrs_setArr σ tb0 _ _ b
      have hlt : (v : ℕ) * (levelFml S j).length + i0 < (σ.arrs tb0).length :=
        lt_of_lt_of_le hrow hP.2.2.2.2.2
      refine ⟨hSt'', ?_, ?_, ?_, ?_, fun b => (hlen'' b).trans (hlenσ' b)⟩
      · intro m hm
        cases m with
        | zero =>
          have hout := hrange'' ((v : ℕ) * (levelFml S j).length + i0) (by omega)
          simp only [Nat.add_zero, List.getElem_cons_zero]
          rw [hout, arrs_setArr, if_pos rfl, getD_set_self hlt]
          exact if_congr Iff.rfl rfl rfl
        | succ m =>
          have hm' : m < rest.length := by simpa using hm
          have h2 := hcells'' m hm'
          rw [show i0 + (m + 1) = i0 + 1 + m by omega]
          simpa using h2
      · intro b hb
        rw [hoth'' b hb, arrs_setArr, if_neg hb]
      · intro y
        rw [hvars'']
        simp
      · intro p hp
        have hp1 : ¬ ((v : ℕ) * (levelFml S j).length + (i0 + 1) ≤ p ∧
            p < (v : ℕ) * (levelFml S j).length + (i0 + 1) + rest.length) := by
          simp only [List.length_cons] at hp
          omega
        rw [hrange'' p hp1, arrs_setArr, if_pos rfl,
          getD_set_ne (by simp only [List.length_cons] at hp; omega)]

/-! ## §6 The readback scan -/

/-- A row's cells lie outside every other row's block. -/
theorem rowIdx_out {F w v i : ℕ} (hwv : w ≠ v) (hi : i < F) :
    ¬ (v * F ≤ w * F + i ∧ w * F + i < v * F + F) := by
  rintro ⟨h1, h2⟩
  rcases Nat.lt_or_ge w v with hlt | hge
  · have h3 : (w + 1) * F ≤ v * F := Nat.mul_le_mul_right _ hlt
    rw [Nat.succ_mul] at h3
    omega
  · have hgt : v + 1 ≤ w := by omega
    have h3 : (v + 1) * F ≤ w * F := Nat.mul_le_mul_right _ hgt
    rw [Nat.succ_mul] at h3
    omega

/-- Adding two cells. -/
theorem evalB_addVars {B : ℕ} {σ : Env} {x y : String}
    (hx : σ.vars x < B) (hy : σ.vars y < B) (hs : σ.vars x + σ.vars y < B) :
    (Expr.add (.var x) (.var y)).evalB B σ = some (σ.vars x + σ.vars y) := by
  rw [Expr.add_def]
  have h := evalB_bin (op := .add) (evalB_var hx) (evalB_var hy)
    (by rw [Bop.apply_add]; omega)
  rwa [Bop.apply_add] at h

/-- Bumping a cell. -/
theorem evalB_incVar {B : ℕ} {σ : Env} {x : String} (h1B : 1 < B)
    (hs : σ.vars x + 1 < B) :
    (Expr.add (.var x) (.lit 1)).evalB B σ = some (σ.vars x + 1) := by
  rw [Expr.add_def]
  have hv : (Expr.var x).evalB B σ = some (σ.vars x) := evalB_var (by omega)
  have h := evalB_bin (op := .add) hv (evalB_lit h1B)
    (by rw [Bop.apply_add]; omega)
  rwa [Bop.apply_add] at h

/-- A tagged name differs from any untagged name of the same base
length. -/
theorem lv_ne_base {b s : String} (hlen : b.length = s.length) (hne : b ≠ s)
    (j : ℕ) : lv b j ≠ s := by
  have h := lv_ne_of_base_ne hlen hne j 0
  rwa [lv_zero] at h

open Classical in
/-- **The readback scan's invariant** at centre `u`: the scan's three
cells and the level's counter, the cover's assignment region, the
cluster row of `u` (read as the child's own enumeration), the child's
table region and the stage's scatter slots, and the level table —
allocated, holding the recursive clause's bits on every processed
centre-`u` row, and untouched on every row whose centre is not `u`. -/
def RdInv (S : Setup L) (ord : CoverSpec.OrderingRoutine) (k j : ℕ)
    (A : Arena (S.pal j) n₀) (u : Fin A.N) (ca cm tb0 tb1 rsb : String)
    (base : ℕ) (T0 : List ℕ) (σ : Env) : Prop :=
  σ.vars "rd.t" ≤ childN S A ((ord A.N A.G).order) u ∧
  σ.vars (arenaNames (j + 1)).nN = childN S A ((ord A.N A.G).order) u ∧
  σ.vars "rd.b" = base ∧
  σ.vars (ctrName j) = (u : ℕ) ∧
  CtrArr ca (centre S A ((ord A.N A.G).order)) σ ∧
  base + childN S A ((ord A.N A.G).order) u ≤ (σ.arrs cm).length ∧
  (∀ (s : ℕ) (hs : s < childN S A ((ord A.N A.G).order) u),
    (σ.arrs cm).getD (base + s) 0
      = ((childName S A ((ord A.N A.G).order) u ⟨s, hs⟩ : Fin A.N) : ℕ)) ∧
  TableBitsW tb1 (levelFml S (j + 1))
    (Unroll.unrollAux S ord k (j + 1)
      (childArena S A ((ord A.N A.G).order) u)) σ ∧
  (rowAtoms S j).length ≤ (σ.arrs rsb).length ∧
  (∀ (m : ℕ) (hm : m < (rowAtoms S j).length),
    (σ.arrs rsb).getD m 0
      = if (rowAtoms S j)[m].t ≤ Impl.greedyScatter
          (childArena S A ((ord A.N A.G).order) u).G (rowAtoms S j)[m].r
          {z | Unroll.unrollAux S ord k (j + 1)
            (childArena S A ((ord A.N A.G).order) u) z (rowAtoms S j)[m].β}
          (rowAtoms S j)[m].t then 1 else 0) ∧
  A.N * (levelFml S j).length ≤ (σ.arrs tb0).length ∧
  (∀ (s : ℕ) (hs : s < childN S A ((ord A.N A.G).order) u), s < σ.vars "rd.t" →
    centre S A ((ord A.N A.G).order)
        (childName S A ((ord A.N A.G).order) u ⟨s, hs⟩) = u →
    ∀ (i : ℕ) (hi : i < (levelFml S j).length),
      (σ.arrs tb0).getD
          (((childName S A ((ord A.N A.G).order) u ⟨s, hs⟩ : Fin A.N) : ℕ)
            * (levelFml S j).length + i) 0
        = if RowEval S ord k j A
            (childName S A ((ord A.N A.G).order) u ⟨s, hs⟩)
            (levelFml S j)[i] then 1 else 0) ∧
  (∀ w : Fin A.N, ¬ centre S A ((ord A.N A.G).order) w = u →
    ∀ i, i < (levelFml S j).length →
      (σ.arrs tb0).getD ((w : ℕ) * (levelFml S j).length + i) 0
        = T0.getD ((w : ℕ) * (levelFml S j).length + i) 0)

open Classical in
/-- **One turn of the readback scan**: read the parent name of the
current child name off the cluster row, and — only if its centre is `u`
— write its whole row. The invariant is re-established at the bumped
counter; every row the turn does not own keeps its cells. -/
theorem readTurn_spec {B : ℕ} (h1B : 1 < B) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (k j : ℕ) (A : Arena (S.pal j) n₀)
    (u : Fin A.N) (ca cm tb0 tb1 rsb : String) (base : ℕ) (T0 : List ℕ)
    (hchoice : S.choice = greedyChoice)
    (htb01 : tb1 ≠ tb0) (htb0r : rsb ≠ tb0) (hcatb : ca ≠ tb0)
    (hcmtb : cm ≠ tb0)
    (hNB : A.N < B) (hNNB : A.N * A.N < B)
    (hF1B : (levelFml S (j + 1)).length < B)
    (hNF1 : childN S A ((ord A.N A.G).order) u * (levelFml S (j + 1)).length < B)
    (hMB : (rowAtoms S j).length < B)
    (hF0B : (levelFml S j).length < B)
    (hNF0 : A.N * (levelFml S j).length < B)
    (hbase : base + childN S A ((ord A.N A.G).order) u ≤ A.N * A.N) :
    Spec B
      (fun σ => RdInv S ord k j A u ca cm tb0 tb1 rsb base T0 σ ∧
        σ.vars "rd.t" < childN S A ((ord A.N A.G).order) u)
      (readTurnCom j ca cm (rowsCom S j tb0 tb1 rsb (F S j) 0))
      (fun σ σ' => RdInv S ord k j A u ca cm tb0 tb1 rsb base T0 σ' ∧
        σ'.vars "rd.t" = σ.vars "rd.t" + 1)
      (14 + rowsK S j tb1 rsb (F S j)) := by
  -- the scan's own cells are fresh against the level's
  have hnN1t : (arenaNames (j + 1)).nN ≠ "rd.t" :=
    lv_ne_base (by rfl) (by decide) (j + 1)
  have hnN1v : (arenaNames (j + 1)).nN ≠ "rd.v" :=
    lv_ne_base (by rfl) (by decide) (j + 1)
  have hctrt : ctrName j ≠ "rd.t" := lv_ne_base (by rfl) (by decide) j
  have hctrv : ctrName j ≠ "rd.v" := lv_ne_base (by rfl) (by decide) j
  have hcNB : childN S A ((ord A.N A.G).order) u < B :=
    lt_of_le_of_lt (childN_le S A ((ord A.N A.G).order) u) hNB
  rintro σ ⟨hI, hlt⟩
  obtain ⟨hle, hnN, hb, hctr, hCtr, hcmL, hcmV, hT1, hrsbL, hrsbV, htb0L,
    hproc, hkeep⟩ := hI
  -- the parent name of the current child name
  have hvcell := hcmV (σ.vars "rd.t") hlt
  set v : Fin A.N :=
    childName S A ((ord A.N A.G).order) u ⟨σ.vars "rd.t", hlt⟩ with hvdef
  have hbtB : σ.vars "rd.b" + σ.vars "rd.t" < B := by rw [hb]; omega
  have hidx : (Expr.add (.var "rd.b") (.var "rd.t")).evalB B σ
      = some (base + σ.vars "rd.t") := by
    have h := evalB_addVars (σ := σ) (x := "rd.b") (y := "rd.t")
      (by omega) (by omega) hbtB
    rwa [hb] at h
  have hcmlt : base + σ.vars "rd.t" < (σ.arrs cm).length := by omega
  have hread : (Expr.get cm (.add (.var "rd.b") (.var "rd.t"))).evalB B σ
      = some (v : ℕ) := by
    refine evalB_get hidx ?_ (by have := v.2; omega)
    rw [List.getElem?_eq_getElem hcmlt]
    refine congrArg some ?_
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcmlt,
      Option.getD_some] at hvcell
    exact hvcell
  have hr1 : Run B (.assign "rd.v" (.get cm (.add (.var "rd.b") (.var "rd.t"))))
      σ (σ.setVar "rd.v" (v : ℕ)) 5 := by
    have h := Run.assign (B := B) (x := "rd.v") hread
    exact h.mono (by simp [Expr.size])
  set σ1 := σ.setVar "rd.v" (v : ℕ) with hσ1
  -- the guard
  have hσ1v : σ1.vars "rd.v" = (v : ℕ) := by simp [hσ1]
  have hσ1t : σ1.vars "rd.t" = σ.vars "rd.t" := by simp [hσ1]
  have hσ1arr : ∀ b, σ1.arrs b = σ.arrs b := fun _ => rfl
  have hvlt : (v : ℕ) < (σ.arrs ca).length := lt_of_lt_of_le v.2 hCtr.1
  have hcaread : (Expr.get ca (.var "rd.v")).evalB B σ1
      = some ((centre S A ((ord A.N A.G).order) v : Fin A.N) : ℕ) := by
    have hrv : (Expr.var "rd.v").evalB B σ1 = some (v : ℕ) := by
      rw [← hσ1v]
      exact evalB_var (by rw [hσ1v]; have := v.2; omega)
    have hcell : (σ1.arrs ca)[(v : ℕ)]?
        = some ((centre S A ((ord A.N A.G).order) v : Fin A.N) : ℕ) := by
      show (σ.arrs ca)[(v : ℕ)]? = _
      rw [List.getElem?_eq_getElem hvlt]
      refine congrArg some ?_
      have h := hCtr.2 v
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hvlt,
        Option.getD_some] at h
      exact h
    exact evalB_get hrv hcell
      (by have := (centre S A ((ord A.N A.G).order) v).2; omega)
  have hctrread : (Expr.var (ctrName j)).evalB B σ1 = some (u : ℕ) := by
    have h : σ1.vars (ctrName j) = (u : ℕ) := by simp [hσ1, hctrv, hctr]
    rw [← h]
    exact evalB_var (by rw [h]; have := u.2; omega)
  have hcond := evalB_condEq hcaread hctrread
  -- what the row-store sequence is handed
  have hRowSt : RowSt S ord k j A u tb0 tb1 rsb (σ.vars "rd.t") v σ1 :=
    ⟨hσ1t, hσ1v, tableBitsW_of_eq hT1 (hσ1arr _), by rw [hσ1arr]; exact hrsbL,
      fun m hm => by rw [hσ1arr]; exact hrsbV m hm, by rw [hσ1arr]; exact htb0L⟩
  -- the level table's rows, unchanged outside the current one
  have hF0len : (levelFml S j).length = (F S j).length := levelFml_length S j
  by_cases hcv : centre S A ((ord A.N A.G).order) v = u
  · -- the current child name is a centre-`u` vertex: write its row
    have hrows := rowsCom_spec h1B S ord k j A u tb0 tb1 rsb hchoice htb01 htb0r
      hcNB hF1B hNF1 hMB hNB hF0B hNF0 hlt rfl hcv (F S j) 0
      (fun m hm => ⟨by omega, getElem_of_eq_idx _ hm (by omega)⟩)
    obtain ⟨σ2, hr2, hSt2, hcells, hoth, hvars, hrange, hlen2⟩ := hrows σ1 hRowSt
    have hbtrue : (((centre S A ((ord A.N A.G).order) v : Fin A.N) : ℕ)
        == ((u : Fin A.N) : ℕ)) = true := by rw [hcv]; simp
    have hr3 : Run B (.ite (.eq (.get ca (.var "rd.v")) (.var (ctrName j)))
        (rowsCom S j tb0 tb1 rsb (F S j) 0) .skip) σ1 σ2
        (5 + rowsK S j tb1 rsb (F S j)) := by
      have h := Run.ite_true (d := Com.skip) (by rw [hcond, hbtrue]) hr2
      exact h.mono (by simp [Cond.size, Expr.size])
    have hσ2t : σ2.vars "rd.t" = σ.vars "rd.t" := by rw [hvars, hσ1t]
    have hincB : σ2.vars "rd.t" + 1 < B := by rw [hσ2t]; omega
    have hr4 : Run B (.assign "rd.t" (.add (.var "rd.t") (.lit 1)))
        σ2 (σ2.setVar "rd.t" (σ2.vars "rd.t" + 1)) 4 :=
      (Run.assign (evalB_incVar h1B hincB)).mono (by simp [Expr.size])
    refine ⟨_, ((hr1.seq (hr3.seq hr4)).mono (by omega)), ?_, ?_⟩
    · -- the invariant, at the bumped counter
      have harr : ∀ b, b ≠ tb0 → (σ2.setVar "rd.t"
          (σ2.vars "rd.t" + 1)).arrs b = σ.arrs b := by
        intro b hbne
        rw [arrs_setVar, hoth b hbne, hσ1arr]
      have hvar : ∀ y, y ≠ "rd.t" → (σ2.setVar "rd.t"
          (σ2.vars "rd.t" + 1)).vars y = σ1.vars y := by
        intro y hy
        rw [vars_setVar, if_neg hy, hvars]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [vars_setVar, if_pos rfl, hσ2t]; omega
      · rw [hvar _ hnN1t, hσ1, vars_setVar, if_neg hnN1v]; exact hnN
      · rw [hvar _ (by decide), hσ1, vars_setVar, if_neg (by decide)]; exact hb
      · rw [hvar _ hctrt, hσ1, vars_setVar, if_neg hctrv]; exact hctr
      · exact ctrArr_of_eq hCtr (harr _ hcatb)
      · rw [harr _ hcmtb]; exact hcmL
      · intro s hs; rw [harr _ hcmtb]; exact hcmV s hs
      · exact tableBitsW_of_eq hT1 (harr _ htb01)
      · rw [harr _ htb0r]; exact hrsbL
      · intro m hm; rw [harr _ htb0r]; exact hrsbV m hm
      · rw [arrs_setVar]
        rw [hlen2 tb0, hσ1arr]
        exact htb0L
      · -- the processed rows
        intro s hs hst hcs i hi
        rw [vars_setVar, if_pos rfl, hσ2t] at hst
        rcases Nat.lt_or_ge s (σ.vars "rd.t") with hslt | hsge
        · -- an earlier row: outside the block just written
          have hne : childName S A ((ord A.N A.G).order) u ⟨s, hs⟩ ≠ v := by
            intro hEq
            exact absurd (childName_inj S A ((ord A.N A.G).order) u hEq)
              (by simp only [Fin.mk.injEq]; omega)
          have hout := hrange
            (((childName S A ((ord A.N A.G).order) u ⟨s, hs⟩ : Fin A.N) : ℕ)
              * (levelFml S j).length + i)
            (by
              have := rowIdx_out (F := (levelFml S j).length)
                (w := ((childName S A ((ord A.N A.G).order) u ⟨s, hs⟩
                  : Fin A.N) : ℕ)) (v := (v : ℕ))
                (fun hEq => hne (Fin.ext hEq)) hi
              simpa [hF0len] using this)
          rw [arrs_setVar, hout, hσ1arr]
          exact hproc s hs hslt hcs i hi
        · -- the current row, just written
          have hfin : (⟨s, hs⟩ : Fin (childN S A ((ord A.N A.G).order) u))
              = ⟨σ.vars "rd.t", hlt⟩ := by
            simp only [Fin.mk.injEq]
            omega
          have hi' : i < (F S j).length := by omega
          have hcell := hcells i hi'
          rw [show ((v : Fin A.N) : ℕ) * (levelFml S j).length + (0 + i)
              = ((v : Fin A.N) : ℕ) * (levelFml S j).length + i by omega]
            at hcell
          rw [arrs_setVar, hfin, ← hvdef, hcell]
          refine if_congr ?_ rfl rfl
          have hmap : (levelFml S j)[i]'hi = ((F S j)[i]'hi').fml := by
            simp only [levelFml, List.getElem_map]
          rw [hmap]
      · -- the rows of other centres, untouched
        intro w hw i hi
        have hne : (w : ℕ) ≠ (v : ℕ) := by
          intro hEq
          exact hw (by rw [Fin.ext hEq]; exact hcv)
        have hout := hrange ((w : ℕ) * (levelFml S j).length + i)
          (by
            have := rowIdx_out (F := (levelFml S j).length) (w := (w : ℕ))
              (v := (v : ℕ)) hne hi
            simpa [hF0len] using this)
        rw [arrs_setVar, hout, hσ1arr]
        exact hkeep w hw i hi
    · rw [vars_setVar, if_pos rfl, hσ2t]
  · -- not a centre-`u` vertex: nothing is written
    have hbfalse : (((centre S A ((ord A.N A.G).order) v : Fin A.N) : ℕ)
        == ((u : Fin A.N) : ℕ)) = false := by
      simp only [beq_eq_false_iff_ne, ne_eq]
      exact fun h => hcv (Fin.ext h)
    have hr3 : Run B (.ite (.eq (.get ca (.var "rd.v")) (.var (ctrName j)))
        (rowsCom S j tb0 tb1 rsb (F S j) 0) .skip) σ1 σ1
        (5 + rowsK S j tb1 rsb (F S j)) := by
      have h := Run.ite_false (c := rowsCom S j tb0 tb1 rsb (F S j) 0)
        (by rw [hcond, hbfalse]) Run.skip
      refine h.mono ?_
      have : 1 ≤ rowsK S j tb1 rsb (F S j) := by
        cases hFl : F S j with
        | nil => rw [rowsK]
        | cons γ rest => rw [rowsK]; omega
      simp only [Cond.size, Expr.size]
      omega
    have hincB : σ1.vars "rd.t" + 1 < B := by rw [hσ1t]; omega
    have hr4 : Run B (.assign "rd.t" (.add (.var "rd.t") (.lit 1)))
        σ1 (σ1.setVar "rd.t" (σ1.vars "rd.t" + 1)) 4 :=
      (Run.assign (evalB_incVar h1B hincB)).mono (by simp [Expr.size])
    refine ⟨_, ((hr1.seq (hr3.seq hr4)).mono (by omega)), ?_, ?_⟩
    · have harr : ∀ b, (σ1.setVar "rd.t" (σ1.vars "rd.t" + 1)).arrs b
          = σ.arrs b := fun _ => rfl
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [vars_setVar, if_pos rfl, hσ1t]; omega
      · rw [vars_setVar, if_neg hnN1t, hσ1, vars_setVar, if_neg hnN1v]; exact hnN
      · rw [vars_setVar, if_neg (by decide), hσ1, vars_setVar,
          if_neg (by decide)]
        exact hb
      · rw [vars_setVar, if_neg hctrt, hσ1, vars_setVar, if_neg hctrv]; exact hctr
      · exact ctrArr_of_eq hCtr (harr _)
      · rw [harr]; exact hcmL
      · intro s hs; rw [harr]; exact hcmV s hs
      · exact tableBitsW_of_eq hT1 (harr _)
      · rw [harr]; exact hrsbL
      · intro m hm; rw [harr]; exact hrsbV m hm
      · rw [harr]; exact htb0L
      · intro s hs hst hcs i hi
        rw [vars_setVar, if_pos rfl, hσ1t] at hst
        rcases Nat.lt_or_ge s (σ.vars "rd.t") with hslt | hsge
        · rw [harr]; exact hproc s hs hslt hcs i hi
        · exfalso
          have hseq : s = σ.vars "rd.t" := by omega
          subst hseq
          exact hcv hcs
      · intro w hw i hi
        rw [harr]
        exact hkeep w hw i hi
    · rw [vars_setVar, if_pos rfl, hσ1t]

/-- **Every centre-`u` vertex has a child name** — `ball_R(v) ⊆ X_{ctr v}`
(§5, "why every table entry is written exactly once"), so the scan over
the child's carrier reaches every row the pass owns. -/
theorem exists_childName (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) {u w : Fin A.N} (hw : centre S A π w = u) :
    ∃ (s : ℕ) (hs : s < childN S A π u), childName S A π u ⟨s, hs⟩ = w := by
  have hmem : w ∈ cluster S A π u := hw ▸ mem_cluster_centre S A π w
  refine ⟨(((childEquiv S A π u).symm ⟨w, hmem⟩ : Fin (childN S A π u)) : ℕ),
    ((childEquiv S A π u).symm ⟨w, hmem⟩).2, ?_⟩
  show ((childEquiv S A π u) ((childEquiv S A π u).symm ⟨w, hmem⟩) : Fin A.N) = w
  rw [Equiv.apply_symm_apply]

open Classical in
/-- **What the readback scan starts from**: the level's counter at `u`,
the cover's two output regions, the child's table region at the inner
block's deliverable, the stage's scatter slots, and the level table's
allocation. -/
def RdPre (S : Setup L) (ord : CoverSpec.OrderingRoutine) (k j : ℕ)
    (A : Arena (S.pal j) n₀) (u : Fin A.N) (ca co cm tb0 tb1 rsb : String)
    (σ : Env) : Prop :=
  σ.vars (arenaNames (j + 1)).nN = childN S A ((ord A.N A.G).order) u ∧
  σ.vars (ctrName j) = (u : ℕ) ∧
  CtrArr ca (centre S A ((ord A.N A.G).order)) σ ∧
  ClusterCsr co cm (cluster S A ((ord A.N A.G).order)) σ ∧
  TableBitsW tb1 (levelFml S (j + 1))
    (Unroll.unrollAux S ord k (j + 1)
      (childArena S A ((ord A.N A.G).order) u)) σ ∧
  (rowAtoms S j).length ≤ (σ.arrs rsb).length ∧
  (∀ (m : ℕ) (hm : m < (rowAtoms S j).length),
    (σ.arrs rsb).getD m 0
      = if (rowAtoms S j)[m].t ≤ Impl.greedyScatter
          (childArena S A ((ord A.N A.G).order) u).G (rowAtoms S j)[m].r
          {z | Unroll.unrollAux S ord k (j + 1)
            (childArena S A ((ord A.N A.G).order) u) z (rowAtoms S j)[m].β}
          (rowAtoms S j)[m].t then 1 else 0) ∧
  A.N * (levelFml S j).length ≤ (σ.arrs tb0).length

open Classical in
/-- **The readback's `Spec`**: the scan writes exactly the centre-`u`
rows of the level table, at the recursive clause's bits, and leaves
every other row's cells as it found them. -/
theorem readLoop_spec {B : ℕ} (h1B : 1 < B) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (k j : ℕ) (A : Arena (S.pal j) n₀)
    (u : Fin A.N) (ca co cm tb0 tb1 rsb : String)
    (hchoice : S.choice = greedyChoice)
    (htb01 : tb1 ≠ tb0) (htb0r : rsb ≠ tb0) (hcatb : ca ≠ tb0)
    (hcmtb : cm ≠ tb0)
    (hNB : A.N < B) (hNNB : A.N * A.N < B)
    (hF1B : (levelFml S (j + 1)).length < B)
    (hNF1 : childN S A ((ord A.N A.G).order) u * (levelFml S (j + 1)).length < B)
    (hMB : (rowAtoms S j).length < B)
    (hF0B : (levelFml S j).length < B)
    (hNF0 : A.N * (levelFml S j).length < B) :
    Spec B (RdPre S ord k j A u ca co cm tb0 tb1 rsb)
      (readLoopCom j ca co cm (rowsCom S j tb0 tb1 rsb (F S j) 0))
      (fun σ σ' =>
        (∀ w : Fin A.N, centre S A ((ord A.N A.G).order) w = u →
          ∀ (i : ℕ) (hi : i < (levelFml S j).length),
            (σ'.arrs tb0).getD ((w : ℕ) * (levelFml S j).length + i) 0
              = if RowEval S ord k j A w (levelFml S j)[i] then 1 else 0) ∧
        (∀ w : Fin A.N, ¬ centre S A ((ord A.N A.G).order) w = u →
          ∀ i, i < (levelFml S j).length →
            (σ'.arrs tb0).getD ((w : ℕ) * (levelFml S j).length + i) 0
              = (σ.arrs tb0).getD ((w : ℕ) * (levelFml S j).length + i) 0))
      (readLoopK S j tb1 rsb (childN S A ((ord A.N A.G).order) u)) := by
  have hctrb : ctrName j ≠ "rd.b" := lv_ne_base (by rfl) (by decide) j
  have hctrt : ctrName j ≠ "rd.t" := lv_ne_base (by rfl) (by decide) j
  have hnN1b : (arenaNames (j + 1)).nN ≠ "rd.b" :=
    lv_ne_base (by rfl) (by decide) (j + 1)
  have hnN1t : (arenaNames (j + 1)).nN ≠ "rd.t" :=
    lv_ne_base (by rfl) (by decide) (j + 1)
  have hcNB : childN S A ((ord A.N A.G).order) u < B :=
    lt_of_le_of_lt (childN_le S A ((ord A.N A.G).order) u) hNB
  intro σ hσ
  obtain ⟨hnN, hctr, hCtr, hcsr, hT1, hrsbL, hrsbV, htb0L⟩ := hσ
  obtain ⟨base, hbaseSq, hbaseLen, hbaseCell, hcells⟩ := clusterCsr_row_le hcsr u
  -- the cluster row's base, loaded
  have hcoL : (u : ℕ) < (σ.arrs co).length := by
    obtain ⟨-, -, hcoL, -, -, -, -⟩ := hcsr
    have := u.2
    omega
  have hcoread : (Expr.get co (.var (ctrName j))).evalB B σ = some base := by
    have hce : (Expr.var (ctrName j)).evalB B σ = some (u : ℕ) := by
      rw [← hctr]
      exact evalB_var (by rw [hctr]; have := u.2; omega)
    have hcell : (σ.arrs co)[(u : ℕ)]? = some base := by
      rw [List.getElem?_eq_getElem hcoL]
      refine congrArg some ?_
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hcoL,
        Option.getD_some] at hbaseCell
      exact hbaseCell
    exact evalB_get hce hcell (by omega)
  have hr1 : Run B (.assign "rd.b" (.get co (.var (ctrName j)))) σ
      (σ.setVar "rd.b" base) 3 :=
    (Run.assign hcoread).mono (by simp [Expr.size])
  -- the scan
  have hbody := readTurn_spec h1B S ord k j A u ca cm tb0 tb1 rsb base
    (σ.arrs tb0) hchoice htb01 htb0r hcatb hcmtb hNB hNNB hF1B hNF1 hMB hF0B
    hNF0 (by rw [childN_eq_ncard]; exact hbaseSq)
  have hloop := Spec.forRangeZero (B := B) "rd.t" (arenaNames (j + 1)).nN
    (RdInv S ord k j A u ca cm tb0 tb1 rsb base (σ.arrs tb0))
    (childN S A ((ord A.N A.G).order) u) (14 + rowsK S j tb1 rsb (F S j))
    hcNB (fun τ hτ => hτ.1) (fun τ hτ => hτ.2.1) hbody
  obtain ⟨σ', hr2, hI', hend⟩ := hloop (σ.setVar "rd.b" base) (by
    refine ⟨by simp, ?_, by simp, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [vars_setVar, if_neg hnN1t, vars_setVar, if_neg hnN1b]; exact hnN
    · rw [vars_setVar, if_neg hctrt, vars_setVar, if_neg hctrb]; exact hctr
    · exact ctrArr_of_eq hCtr rfl
    · exact hbaseLen
    · exact fun s hs => hcells s hs
    · exact tableBitsW_of_eq hT1 rfl
    · exact hrsbL
    · exact hrsbV
    · exact htb0L
    · intro s hs hst
      exfalso
      have hz : ((σ.setVar "rd.b" base).setVar "rd.t" 0).vars "rd.t" = 0 := by simp
      rw [hz] at hst
      omega
    · intro w hw i hi; rfl)
  refine ⟨σ', (hr1.seq hr2).mono ?_, ?_, ?_⟩
  · rw [readLoopK]; omega
  · -- every centre-`u` row, at the recursive clause's bits
    intro w hw i hi
    obtain ⟨s, hs, hsw⟩ := exists_childName S A ((ord A.N A.G).order) hw
    have hproc := hI'.2.2.2.2.2.2.2.2.2.2.2.1 s hs (by rw [hend]; exact hs)
      (by rw [hsw]; exact hw) i hi
    rw [hsw] at hproc
    exact hproc
  · -- every other row, untouched
    intro w hw i hi
    exact hI'.2.2.2.2.2.2.2.2.2.2.2.2 w hw i hi

/-! ## §7 What the pass writes -/

theorem wvars_rowsCom (S : Setup L) (j : ℕ) (tb0 tb1 rsb : String)
    (l : List (Fml S j)) (i : ℕ) :
    (rowsCom S j tb0 tb1 rsb l i).wvars = [] := by
  induction l generalizing i with
  | nil => rfl
  | cons γ rest ih =>
    rw [rowsCom, Com.wvars, rowStoreCom, Com.wvars, ih (i + 1)]
    rfl

theorem warrs_rowsCom (S : Setup L) (j : ℕ) (tb0 tb1 rsb : String)
    (l : List (Fml S j)) (i : ℕ) :
    ∀ a ∈ (rowsCom S j tb0 tb1 rsb l i).warrs, a = tb0 := by
  induction l generalizing i with
  | nil => intro a ha; simp [rowsCom] at ha
  | cons γ rest ih =>
    intro a ha
    rw [rowsCom, Com.warrs, List.mem_append] at ha
    rcases ha with h | h
    · rw [rowStoreCom, Com.warrs] at h
      simpa using h
    · exact ih (i + 1) a h

theorem wvars_readLoopCom (S : Setup L) (j : ℕ)
    (ca co cm tb0 tb1 rsb : String) (l : List (Fml S j)) (i : ℕ) :
    ∀ y ∈ (readLoopCom j ca co cm (rowsCom S j tb0 tb1 rsb l i)).wvars,
      y ∈ (["rd.b", "rd.t", "rd.v"] : List String) := by
  intro y hy
  simp only [readLoopCom, readTurnCom, Com.wvars,
    wvars_rowsCom S j tb0 tb1 rsb l i, List.append_nil, List.nil_append,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem warrs_readLoopCom (S : Setup L) (j : ℕ)
    (ca co cm tb0 tb1 rsb : String) (l : List (Fml S j)) (i : ℕ) :
    ∀ a ∈ (readLoopCom j ca co cm (rowsCom S j tb0 tb1 rsb l i)).warrs,
      a = tb0 := by
  intro a ha
  simp only [readLoopCom, readTurnCom, Com.warrs, List.append_nil,
    List.nil_append] at ha
  exact warrs_rowsCom S j tb0 tb1 rsb l i a ha

theorem wvars_topAtomCom (nm : ArenaNames) (pa ma da tsb : String)
    (Fl i bi r t : ℕ) :
    ∀ y ∈ (topAtomCom nm pa ma da tsb Fl i bi r t).wvars, y ∈ gsScalars := by
  intro y hy
  simp only [topAtomCom, topGlueCom, topColCom, topBitCom, Com.wvars,
    Lib.Fill.wvars_put, wvars_scatterCom, List.append_nil,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hy
  simp only [gsScalars, List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem warrs_topAtomCom (nm : ArenaNames) (pa ma da tsb : String)
    (Fl i bi r t : ℕ) :
    ∀ a ∈ (topAtomCom nm pa ma da tsb Fl i bi r t).warrs,
      a ∈ ([pa, ma, da, tsb] : List String) := by
  intro a ha
  simp only [topAtomCom, topGlueCom, topColCom, topBitCom, Com.warrs,
    Lib.Fill.warrs_put, warrs_scatterCom, List.append_nil, List.nil_append,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at ha
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  tauto

theorem wvars_topAtomsCom {Λc : ℕ} (nm : ArenaNames) (pa ma da tsb : String)
    (Fl : ℕ) (bIdx : ScatterSentence Λc → ℕ) :
    ∀ (l : List (ScatterSentence Λc)) (i : ℕ),
    ∀ y ∈ (topAtomsCom nm pa ma da tsb Fl bIdx l i).wvars, y ∈ gsScalars := by
  intro l
  induction l with
  | nil => intro i y hy; simp [topAtomsCom] at hy
  | cons σa rest ih =>
    intro i y hy
    rw [topAtomsCom, Com.wvars, List.mem_append] at hy
    rcases hy with h | h
    · exact wvars_topAtomCom nm pa ma da tsb Fl i (bIdx σa) σa.r σa.t y h
    · exact ih (i + 1) y h

theorem warrs_topAtomsCom {Λc : ℕ} (nm : ArenaNames) (pa ma da tsb : String)
    (Fl : ℕ) (bIdx : ScatterSentence Λc → ℕ) :
    ∀ (l : List (ScatterSentence Λc)) (i : ℕ),
    ∀ a ∈ (topAtomsCom nm pa ma da tsb Fl bIdx l i).warrs,
      a ∈ ([pa, ma, da, tsb] : List String) := by
  intro l
  induction l with
  | nil => intro i a ha; simp [topAtomsCom] at ha
  | cons σa rest ih =>
    intro i a ha
    rw [topAtomsCom, Com.warrs, List.mem_append] at ha
    rcases ha with h | h
    · exact warrs_topAtomCom nm pa ma da tsb Fl i (bIdx σa) σa.r σa.t a h
    · exact ih (i + 1) a h

/-! ## §8 The named residual, discharged -/

open Classical in
/-- **`ReadRows`, discharged with a real pass** — the landed per-atom
scatter stage on the isolated child followed by the readback scan, at
the honest budget `readK`. Every hypothesis is of an F7-suppliable
kind: the choice seam, the word bounds, the scratch descriptor's four
length clauses, and the scratch names' freshness against the level
families. The pass never mentions the answer: the bits it stores are
read out of the child's table region and the counts the scatter stage
wrote. -/
theorem readRows_of {B : ℕ} (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (pa ma da rsb : String)
    (hchoice : S.choice = greedyChoice)
    (h1B : 1 < B) (hnB : n₀ < B) (hnnB : n₀ * n₀ < B)
    (hFB : ∀ i, (levelFml S i).length < B ∧ n₀ * (levelFml S i).length < B)
    (hAB : ∀ i, (rowAtoms S i).length < B ∧
      ∀ σa ∈ rowAtoms S i, σa.r + 2 < B ∧ σa.t < B)
    (hscrR : ∀ i σ, Scr i σ → n₀ ≤ (σ.arrs pa).length ∧
      n₀ ≤ (σ.arrs ma).length ∧ n₀ ≤ (σ.arrs da).length ∧
      (rowAtoms S i).length ≤ (σ.arrs rsb).length)
    (hpa : ∀ i, pa ∉ levelArrays i) (hma : ∀ i, ma ∉ levelArrays i)
    (hda : ∀ i, da ∉ levelArrays i) (hrsb : ∀ i, rsb ∉ levelArrays i)
    (hda_ma : da ≠ ma) (hda_pa : da ≠ pa) (hma_pa : ma ≠ pa)
    (hrsb_pa : rsb ≠ pa) (hrsb_ma : rsb ≠ ma) (hrsb_da : rsb ≠ da)
    (hcaF : ∀ i, ca i ∉ ([pa, ma, da, rsb] : List String) ∧
      ca i ∉ levelArrays i)
    (hcoF : ∀ i, co i ∉ ([pa, ma, da, rsb] : List String) ∧
      co i ∉ levelArrays i)
    (hcmF : ∀ i, cm i ∉ ([pa, ma, da, rsb] : List String) ∧
      cm i ∉ levelArrays i) :
    ReadRows B S ord ℓp htabF hbf Adm Scr ca co cm
      (fun i => readPassCom S i (ca i) (co i) (cm i) pa ma da rsb)
      (readK S ord rsb) := by
  intro k j A _ _ _ u
  -- the level's own names, spelled out
  have hpaM := hpa (j + 1)
  have hmaM := hma (j + 1)
  have hdaM := hda (j + 1)
  have hrsbM := hrsb (j + 1)
  simp only [levelArrays, List.mem_cons, List.not_mem_nil, or_false, not_or]
    at hpaM hmaM hdaM hrsbM
  obtain ⟨hpa_o, hpa_t, hpa_c, hpa_u, hpa_h, hpa_b⟩ := hpaM
  obtain ⟨hma_o, hma_t, hma_c, hma_u, hma_h, hma_b⟩ := hmaM
  obtain ⟨hda_o, hda_t, hda_c, hda_u, hda_h, hda_b⟩ := hdaM
  obtain ⟨hrsb_o, hrsb_t, hrsb_c, hrsb_u, hrsb_h, hrsb_b⟩ := hrsbM
  have hpa5 : pa ∉ ([(arenaNames (j + 1)).off, (arenaNames (j + 1)).tgt,
      (arenaNames (j + 1)).col, (arenaNames (j + 1)).up,
      (arenaNames (j + 1)).hist] : List String) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hpa_o, hpa_t, hpa_c, hpa_u, hpa_h⟩
  have hma5 : ma ∉ ([(arenaNames (j + 1)).off, (arenaNames (j + 1)).tgt,
      (arenaNames (j + 1)).col, (arenaNames (j + 1)).up,
      (arenaNames (j + 1)).hist] : List String) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hma_o, hma_t, hma_c, hma_u, hma_h⟩
  have hda5 : da ∉ ([(arenaNames (j + 1)).off, (arenaNames (j + 1)).tgt,
      (arenaNames (j + 1)).col, (arenaNames (j + 1)).up,
      (arenaNames (j + 1)).hist] : List String) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hda_o, hda_t, hda_c, hda_u, hda_h⟩
  have hrsb5 : rsb ∉ ([(arenaNames (j + 1)).off, (arenaNames (j + 1)).tgt,
      (arenaNames (j + 1)).col, (arenaNames (j + 1)).up,
      (arenaNames (j + 1)).hist] : List String) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨hrsb_o, hrsb_t, hrsb_c, hrsb_u, hrsb_h⟩
  -- the level-`j` names, against the pass's scratch and the level table
  have hpaJ := hpa j
  have hmaJ := hma j
  have hdaJ := hda j
  have hrsbJ := hrsb j
  simp only [levelArrays, List.mem_cons, List.not_mem_nil, or_false, not_or]
    at hpaJ hmaJ hdaJ hrsbJ
  have hfresh4 : ∀ a : String, a ≠ pa → a ≠ ma → a ≠ da → a ≠ rsb →
      a ∉ ([pa, ma, da, rsb] : List String) := by
    intro a h1 h2 h3 h4
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨h1, h2, h3, h4⟩
  have hbase : ∀ s : String, s.length = 4 → s ≠ "sa.b" →
      lv s j ≠ (arenaNames j).tab :=
    fun s hs hne => lv_ne_of_base_ne (by rw [hs]; rfl) hne j j
  have hL : ∀ a ∈ ([ca j, co j, cm j, (arenaNames j).off, (arenaNames j).tgt,
      (arenaNames j).col, (arenaNames j).up, (arenaNames j).hist] :
        List String),
      a ∉ ([pa, ma, da, rsb] : List String) ∧ a ≠ (arenaNames j).tab := by
    intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨(hcaF j).1, fun h => (hcaF j).2 (by rw [h]; simp [levelArrays])⟩
    · exact ⟨(hcoF j).1, fun h => (hcoF j).2 (by rw [h]; simp [levelArrays])⟩
    · exact ⟨(hcmF j).1, fun h => (hcmF j).2 (by rw [h]; simp [levelArrays])⟩
    · exact ⟨hfresh4 _ (fun h => hpaJ.1 h.symm) (fun h => hmaJ.1 h.symm)
        (fun h => hdaJ.1 h.symm) (fun h => hrsbJ.1 h.symm),
        hbase "sa.o" (by decide) (by decide)⟩
    · exact ⟨hfresh4 _ (fun h => hpaJ.2.1 h.symm) (fun h => hmaJ.2.1 h.symm)
        (fun h => hdaJ.2.1 h.symm) (fun h => hrsbJ.2.1 h.symm),
        hbase "sa.t" (by decide) (by decide)⟩
    · exact ⟨hfresh4 _ (fun h => hpaJ.2.2.1 h.symm)
        (fun h => hmaJ.2.2.1 h.symm) (fun h => hdaJ.2.2.1 h.symm)
        (fun h => hrsbJ.2.2.1 h.symm), hbase "sa.c" (by decide) (by decide)⟩
    · exact ⟨hfresh4 _ (fun h => hpaJ.2.2.2.1 h.symm)
        (fun h => hmaJ.2.2.2.1 h.symm) (fun h => hdaJ.2.2.2.1 h.symm)
        (fun h => hrsbJ.2.2.2.1 h.symm), hbase "sa.u" (by decide) (by decide)⟩
    · exact ⟨hfresh4 _ (fun h => hpaJ.2.2.2.2.1 h.symm)
        (fun h => hmaJ.2.2.2.2.1 h.symm) (fun h => hdaJ.2.2.2.2.1 h.symm)
        (fun h => hrsbJ.2.2.2.2.1 h.symm),
        hbase "sa.h" (by decide) (by decide)⟩
  -- the level's scalars, against the pass's
  have hSc : ∀ y ∈ ctrName j :: levelScalars j,
      y ∉ gsScalars ∧ y ∉ (["rd.b", "rd.t", "rd.v"] : List String) := by
    intro y hy
    simp only [levelScalars, List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact ⟨lv_not_mem (by decide) (by decide) j,
        lv_not_mem (by decide) (by decide) j⟩
    · exact ⟨lv_not_mem (by decide) (by decide) j,
        lv_not_mem (by decide) (by decide) j⟩
    · exact ⟨lv_not_mem (by decide) (by decide) j,
        lv_not_mem (by decide) (by decide) j⟩
  -- the word bounds at this arena
  have hANle : A.N ≤ n₀ := arenaN_le A
  have hNB : A.N < B := lt_of_le_of_lt hANle hnB
  have hNNB : A.N * A.N < B :=
    lt_of_le_of_lt (Nat.mul_le_mul hANle hANle) hnnB
  have hcNle : childN S A ((ord A.N A.G).order) u ≤ A.N :=
    childN_le S A ((ord A.N A.G).order) u
  have hcNB : childN S A ((ord A.N A.G).order) u < B := by omega
  have hcNNB : childN S A ((ord A.N A.G).order) u
      * childN S A ((ord A.N A.G).order) u < B :=
    lt_of_le_of_lt (Nat.mul_le_mul (le_trans hcNle hANle) (le_trans hcNle hANle))
      hnnB
  have hNF0 : A.N * (levelFml S j).length < B :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ hANle) (hFB j).2
  have hcNF1 : childN S A ((ord A.N A.G).order) u
      * (levelFml S (j + 1)).length < B :=
    lt_of_le_of_lt (Nat.mul_le_mul_right _ (le_trans hcNle hANle)) (hFB (j + 1)).2
  -- the level-`(j+1)` name facts the landed stage asks for
  have hot : (arenaNames (j + 1)).tgt ≠ (arenaNames (j + 1)).off :=
    lv_ne_of_base_ne (by decide) (by decide) (j + 1) (j + 1)
  have hnN1 : (arenaNames (j + 1)).nN ∉ gsScalars :=
    lv_not_mem (by decide) (by decide) (j + 1)
  have hnS1 : (arenaNames (j + 1)).nS ∉ gsScalars :=
    lv_not_mem (by decide) (by decide) (j + 1)
  have htb01 : (arenaNames (j + 1)).tab ≠ (arenaNames j).tab :=
    lv_ne_of_level_ne (by decide) (by omega)
  have hrsb_tb0 : rsb ≠ (arenaNames j).tab := fun h => hrsbJ.2.2.2.2.2 h
  have hca_tb0 : ca j ≠ (arenaNames j).tab := (hL _ (by simp)).2
  have hcm_tb0 : cm j ≠ (arenaNames j).tab := (hL _ (by simp)).2
  -- the two stages
  have hstage := (topAtomsCom_spec
      (B := B) (hb := hbf (j + 1))
      (A := Impl.ofArena (childArena S A ((ord A.N A.G).order) u)
        (htabF (j + 1) (childArena S A ((ord A.N A.G).order) u)))
      (nm := arenaNames (j + 1)) (pa := pa) (ma := ma) (da := da) (tsb := rsb)
      (Fl := levelFml S (j + 1))
      (T := Unroll.unrollAux S ord k (j + 1)
        (childArena S A ((ord A.N A.G).order) u))
      (rowAtoms S j).length (fun σa => memIdx (levelFml S (j + 1)) σa.β)
      hcNB hcNNB hcNF1 (hAB j).1 h1B hot hda5 hma5 hpa5 hda_ma hda_pa hma_pa
      hnN1 hnS1 (Ne.symm hpa_b) (Ne.symm hma_b) (Ne.symm hda_b)
      hrsb_pa hrsb_ma hrsb_da hrsb_b hrsb5
      (rowAtoms S j) 0 (by exact le_of_eq (Nat.zero_add _))
      (fun σa hmem => ⟨⟨memIdx_lt (beta_mem_of_mem_rowAtoms hmem),
        getElem_memIdx (beta_mem_of_mem_rowAtoms hmem)⟩, (hAB j).2 σa hmem⟩)).frame
  have hloop := (specArrsLength ((readLoop_spec h1B S ord k j A u (ca j) (co j)
    (cm j) (arenaNames j).tab (arenaNames (j + 1)).tab rsb hchoice htb01
    hrsb_tb0 hca_tb0 hcm_tb0 hNB hNNB (hFB (j + 1)).1 hcNF1 (hAB j).1
    (hFB j).1 hNF0).frame))
  -- what neither stage writes
  have hnotwv1 : ∀ y, y ∉ gsScalars →
      y ∉ (topAtomsCom (arenaNames (j + 1)) pa ma da rsb
        (levelFml S (j + 1)).length
        (fun σa => memIdx (levelFml S (j + 1)) σa.β) (rowAtoms S j) 0).wvars :=
    fun y hy hmem => hy (wvars_topAtomsCom _ _ _ _ _ _ _ _ _ y hmem)
  have hnotwa1 : ∀ a, a ∉ ([pa, ma, da, rsb] : List String) →
      a ∉ (topAtomsCom (arenaNames (j + 1)) pa ma da rsb
        (levelFml S (j + 1)).length
        (fun σa => memIdx (levelFml S (j + 1)) σa.β) (rowAtoms S j) 0).warrs :=
    fun a ha hmem => ha (warrs_topAtomsCom _ _ _ _ _ _ _ _ _ a hmem)
  have hnotwv2 : ∀ y, y ∉ (["rd.b", "rd.t", "rd.v"] : List String) →
      y ∉ (readLoopCom j (ca j) (co j) (cm j)
        (rowsCom S j (arenaNames j).tab (arenaNames (j + 1)).tab rsb
          (F S j) 0)).wvars :=
    fun y hy hmem => hy (wvars_readLoopCom S j _ _ _ _ _ _ _ _ y hmem)
  have hnotwa2 : ∀ a, a ≠ (arenaNames j).tab →
      a ∉ (readLoopCom j (ca j) (co j) (cm j)
        (rowsCom S j (arenaNames j).tab (arenaNames (j + 1)).tab rsb
          (F S j) 0)).warrs :=
    fun a ha hmem => ha (warrs_readLoopCom S j _ _ _ _ _ _ _ _ a hmem)
  have htb0F : (arenaNames j).tab ∉ ([pa, ma, da, rsb] : List String) :=
    hfresh4 _ (fun h => hpaJ.2.2.2.2.2 h.symm) (fun h => hmaJ.2.2.2.2.2 h.symm)
      (fun h => hdaJ.2.2.2.2.2 h.symm) (fun h => hrsbJ.2.2.2.2.2 h.symm)
  refine (Spec.seq (hstage.pre ?_) hloop ?_ ?_).mono ?_
  · -- the stage's precondition, from the invariant and the block's post
    rintro σ ⟨⟨⟨-, -, hscr⟩, -, -, -⟩, -, hAW1, hT1⟩
    obtain ⟨hpaL, hmaL, hdaL, hrsbL⟩ := hscrR j σ hscr
    exact ⟨hAW1, hT1, le_trans hcNle (le_trans hANle hpaL),
      le_trans hcNle (le_trans hANle hmaL),
      le_trans hcNle (le_trans hANle hdaL), hrsbL⟩
  · -- the readback's precondition, from the stage's deliverable
    rintro σ σ' ⟨⟨⟨-, htabLen, -⟩, hCtr, hcsr, -⟩, hctr, -, -⟩
      ⟨⟨⟨hAW1', hT1', -, -, -, hrsbL'⟩, hcells, -, hlen1⟩, hfv1, hfa1, -, -⟩
    refine ⟨hAW1'.n_eq, ?_, ?_, ?_, hT1', hrsbL', ?_, ?_⟩
    · rw [hfv1 _ (hnotwv1 _ (hSc _ (by simp)).1)]
      exact hctr
    · exact ctrArr_of_eq hCtr (hfa1 _ (hnotwa1 _ (hL _ (by simp)).1))
    · exact clusterCsr_of_eq hcsr (hfa1 _ (hnotwa1 _ (hL _ (by simp)).1))
        (hfa1 _ (hnotwa1 _ (hL _ (by simp)).1))
    · intro m hm
      have h := hcells m hm
      rwa [Nat.zero_add] at h
    · rw [hlen1]
      exact htabLen
  · -- the five clauses of the residual
    rintro σ σ' σ'' -
      ⟨⟨-, -, -, hlen1⟩, hfv1, hfa1, -, -⟩
      ⟨⟨⟨hrows2, hoth2⟩, hfv2, hfa2, -, -⟩, hlen2⟩
    refine ⟨hrows2, ?_, ?_, ?_, fun b => (hlen2 b).trans (hlen1 b)⟩
    · intro w hw i hi
      rw [hoth2 w hw i hi, hfa1 _ (hnotwa1 _ htb0F)]
    · intro y hy
      rw [hfv2 _ (hnotwv2 _ (hSc y hy).2), hfv1 _ (hnotwv1 _ (hSc y hy).1)]
    · intro a ha
      rw [hfa2 _ (hnotwa2 _ (hL a ha).2), hfa1 _ (hnotwa1 _ (hL a ha).1)]
  · -- the budget: the landed scatter stage plus the scan
    rw [readK, dif_pos u.2]
    simp only [Fin.eta]
    rfl

/-! ## §9 The headline: `ReadRowsAll`, verbatim -/

open Classical in
/-- **Verbatim `ReadRowsAll`** — residual 2 of the read segment,
discharged with the real pass `readPassCom` (the landed per-atom scatter
stage on the isolated child, then the readback scan) at the honest
budget `readK`, from F7-suppliable hypotheses only: the word bounds per
admissible input, the scratch descriptor's four length clauses, and the
scratch names' freshness against the level families. The choice seam is
`headlineSetup_choice`, definitional. -/
theorem readRowsAll_of (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (pa ma da rsb : String)
    (hq : 1 ≤ q)
    -- the word bounds, per admissible input
    (hB : ∀ x ∈ mcD n G c w, n < mcB q x ∧ n * n < mcB q x)
    (hFB : ∀ x ∈ mcD n G c w, ∀ i,
      (levelFml (Headline.headlineSetup C hC φ) i).length < mcB q x ∧
      n * (levelFml (Headline.headlineSetup C hC φ) i).length < mcB q x)
    (hAB : ∀ x ∈ mcD n G c w, ∀ i,
      (rowAtoms (Headline.headlineSetup C hC φ) i).length < mcB q x ∧
      ∀ σa ∈ rowAtoms (Headline.headlineSetup C hC φ) i,
        σa.r + 2 < mcB q x ∧ σa.t < mcB q x)
    -- the scratch descriptor's four length clauses
    (hscrR : ∀ i σ, Scr i σ → n ≤ (σ.arrs pa).length ∧
      n ≤ (σ.arrs ma).length ∧ n ≤ (σ.arrs da).length ∧
      (rowAtoms (Headline.headlineSetup C hC φ) i).length ≤ (σ.arrs rsb).length)
    -- the scratch names, fresh against the level families
    (hpa : ∀ i, pa ∉ levelArrays i) (hma : ∀ i, ma ∉ levelArrays i)
    (hda : ∀ i, da ∉ levelArrays i) (hrsb : ∀ i, rsb ∉ levelArrays i)
    (hda_ma : da ≠ ma) (hda_pa : da ≠ pa) (hma_pa : ma ≠ pa)
    (hrsb_pa : rsb ≠ pa) (hrsb_ma : rsb ≠ ma) (hrsb_da : rsb ≠ da)
    (hcaF : ∀ i, ca i ∉ ([pa, ma, da, rsb] : List String) ∧
      ca i ∉ levelArrays i)
    (hcoF : ∀ i, co i ∉ ([pa, ma, da, rsb] : List String) ∧
      co i ∉ levelArrays i)
    (hcmF : ∀ i, cm i ∉ ([pa, ma, da, rsb] : List String) ∧
      cm i ∉ levelArrays i) :
    ReadRowsAll C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm
      (fun i => readPassCom (Headline.headlineSetup C hC φ) i
        (ca i) (co i) (cm i) pa ma da rsb)
      (readK (Headline.headlineSetup C hC φ) ord rsb) := by
  intro x hx
  exact readRows_of (Headline.headlineSetup C hC φ) ord ℓp htabF hbf Adm Scr
    ca co cm pa ma da rsb (headlineSetup_choice C hC φ)
    (one_lt_mcB (three_le_length hx.1) hq) (hB x hx).1 (hB x hx).2
    (hFB x hx) (hAB x hx) hscrR hpa hma hda hrsb hda_ma hda_pa hma_pa
    hrsb_pa hrsb_ma hrsb_da hcaF hcoF hcmF

end Lax3Proofs.Prog
