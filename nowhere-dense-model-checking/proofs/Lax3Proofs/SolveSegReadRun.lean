import Lax3Proofs.SolveMachRead
import Lax3Proofs.SolveSeamTop

/-!
# F6c12 — the scatter-and-readback machine pass, discharged

`SolveSegRead` named **`ReadRows`** — the per-centre machine pass of the
return path: from the loop invariant at centre `u` (counter at `u`) plus
the child block's postcondition, run the per-atom scatters on the
isolated child and write exactly the centre-`u` rows of the level table
at `RowEval`'s bits. This file discharges **`ReadRowsAll`** with a real
program:

* **Stage A — the atoms.** The level's scatter atoms (`levelAtoms`, the
  scatter atoms of every schedule row's decomposition, concatenated) are
  compile-time data; the stage is the landed `topAtomsCom` of the top
  seam (`SolveSeamTop`), verbatim, instantiated at the **child's**
  region names `arenaNames (j+1)`: per atom, glue → β-column copy from
  the child's `TableBitsW` into the bit region `pa`
  (`tableBitsW_column`'s bits) → the landed `scatterCom` on the isolated
  child CSR (`scatterCom_specW` inside `topAtomCom_spec`) → guard bit
  into slot `memIdx (levelAtoms S j) σa` of `tsb`.
* **Stage B — the rows.** Read the centre's cluster row bounds off the
  cover's CSR (`co[u]`, `co[u+1]`), then scan the row: entry `t` is the
  parent name of child name `t` (`ClusterCsr` rows are `restrictEmb`'s
  ascending enumeration, which **is** `childEquiv`'s —
  `childEquiv_symm_restrictEmb` below), so the guarded row store
  (`ca[v] = u` — the first-hit discipline: cluster membership does not
  imply ownership) writes row `v` as the compiled combination
  `bcExprA av (dec S γ)` per schedule row, with the local atoms read off
  the child table at child name `rb.i` (`rowAsn_local_bit`) and the
  scatter atoms off the kept slots (`rowAsn_scatter_bit`, the choice
  seam `headlineSetup_choice`). `bcExprA_evalB` pins each stored value
  to `RowEval`'s bit through `rowEval_eq_dec_eval`.

The frame is per-cell by construction: the store loop's invariant
carries "every cell outside `{(v, i) | ca[v] = u, i < |ℱ_j|}` reads as
at entry" in both directions, and the level's scalars, the cover's
three arrays and the five non-table regions ride `Run.frame` off the
program's write sets (`warrs_readSegCom` / `wvars_readSegCom`).

`readRowsAll_of` is the headline: verbatim `ReadRowsAll` at the program
family `readSegCom` and the budget `readSegK` — per centre, the summed
per-atom scatter budget `topScatK` over the child plus
`(cluster size) × (row-evaluation cost)` — from F7-suppliable
hypotheses only: `1 ≤ q`, the word bounds per admissible input, the
scratch descriptor's four length clauses, and name freshness.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

variable {L n₀ : ℕ}

/-! ## §0 Helpers -/

/-- Reading a cell as `getElem?`, from a `getD` fact and the range. -/
theorem getElem?_of_getD {l : List ℕ} {i v : ℕ} (h : i < l.length)
    (hg : l.getD i 0 = v) : l[i]? = some v := by
  rw [List.getElem?_eq_getElem h]
  refine congrArg some ?_
  rw [← hg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- A subset of `Fin N` has at most `N` members. -/
theorem ncard_le_card {N : ℕ} (X : Set (Fin N)) : X.ncard ≤ N :=
  le_of_le_of_eq
    (Set.ncard_le_ncard (Set.subset_univ _) Set.finite_univ)
    (by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin])

/-- Row-major row disjointness: a cell of row `v` is a cell of row `w`
only for `v = w`. -/
theorem row_cell_inj {F v w i m : ℕ} (hi : i < F) (hm : m < F)
    (h : v * F + i = w * F + m) : v = w := by
  rcases Nat.lt_trichotomy v w with hvw | hvw | hvw
  · exfalso
    have : (v + 1) * F ≤ w * F := Nat.mul_le_mul_right F hvw
    rw [Nat.succ_mul] at this
    omega
  · exact hvw
  · exfalso
    have : (w + 1) * F ≤ v * F := Nat.mul_le_mul_right F hvw
    rw [Nat.succ_mul] at this
    omega

/-! ## §0b The cluster CSR, read for one centre

`ClusterCsr.read_row` delivers the row's base and entries; the loop
additionally reads the **next** offset (for the row's extent) and needs
the offsets bounded by `N²` (the word-bound side condition of every
offset read). Both follow from the stored offset recurrence. -/

open Classical in
/-- One centre's row of the cluster CSR, with the next offset and the
`N²` bound: `co[u] = base`, `co[u+1] = base + |X_u|`, the row fits the
membership array, offsets stay `≤ N²`, and entry `t` is the `t`-th
local name's parent name. -/
theorem clusterCsr_row_bounds {co cm : String} {N : ℕ}
    {Xf : Fin N → Set (Fin N)} {σ : Env} (h : ClusterCsr co cm Xf σ)
    (u : Fin N) :
    ∃ base : ℕ,
      (σ.arrs co).getD (u : ℕ) 0 = base ∧
      (σ.arrs co).getD ((u : ℕ) + 1) 0 = base + (Xf u).ncard ∧
      base + (Xf u).ncard ≤ (σ.arrs cm).length ∧
      base + (Xf u).ncard ≤ N * N ∧
      N + 1 ≤ (σ.arrs co).length ∧
      ∀ t : ℕ, ∀ ht : t < (Xf u).ncard,
        (σ.arrs cm).getD (base + t) 0
          = (Impl.restrictEmb (Xf u) ⟨t, ht⟩ : ℕ) := by
  obtain ⟨base, hfit, hbase, hrow⟩ := h.read_row u
  obtain ⟨offC, h0, hcoL, hco, hstep, hcmL, hcm⟩ := h
  -- `base` is the stored offset at `u`
  have hbase' : offC (u : ℕ) = base := by
    rw [← hbase, hco (u : ℕ) (le_of_lt u.2)]
  -- offsets grow by at most `N` a step
  have hgrow : ∀ i, i ≤ N → offC i ≤ i * N := by
    intro i
    induction i with
    | zero => intro _; simp [h0]
    | succ i ih =>
      intro hiN
      have hci : offC (i + 1) = offC i + (Xf ⟨i, by omega⟩).ncard :=
        hstep ⟨i, by omega⟩
      have h1 := ih (by omega)
      have h2 := ncard_le_card (Xf ⟨i, by omega⟩)
      rw [hci, Nat.succ_mul]
      omega
  have hnext : offC ((u : ℕ) + 1) = base + (Xf u).ncard := by
    rw [hstep u, hbase']
  refine ⟨base, hbase, ?_, hfit, ?_, hcoL, hrow⟩
  · rw [hco ((u : ℕ) + 1) u.2, hnext]
  · rw [← hnext]
    have := hgrow ((u : ℕ) + 1) u.2
    have h2 : ((u : ℕ) + 1) * N ≤ N * N := Nat.mul_le_mul_right N u.2
    omega

/-! ## §0c The child-name seam

Cluster CSR rows enumerate `restrictEmb`'s ascending order, which is
`setEquiv`'s — the very bijection `childEquiv` is. So the row position
**is** the child name, in both directions. -/

/-- `childEquiv` undoes the row read: the parent name at row position
`t` has child name `t`. -/
theorem childEquiv_symm_restrictEmb (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) {t : ℕ}
    (ht : t < childN S A π u)
    (hmem : Impl.restrictEmb (cluster S A π u) ⟨t, ht⟩ ∈ cluster S A π u) :
    (childEquiv S A π u).symm
        ⟨Impl.restrictEmb (cluster S A π u) ⟨t, ht⟩, hmem⟩ = ⟨t, ht⟩ := by
  rw [Equiv.symm_apply_eq]
  exact Subtype.ext rfl

/-- The row read undoes `childEquiv`: a cluster member is the row entry
at its child name. -/
theorem restrictEmb_childEquiv_symm (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) {v : Fin A.N}
    (hmem : v ∈ cluster S A π u) :
    Impl.restrictEmb (cluster S A π u)
      ((childEquiv S A π u).symm ⟨v, hmem⟩) = v := by
  show ((childEquiv S A π u) ((childEquiv S A π u).symm ⟨v, hmem⟩) : Fin A.N)
    = v
  rw [Equiv.apply_symm_apply]

/-! ## §0d The level's scatter atoms -/

open Classical in
/-- **The level's scatter atoms**: the scatter atoms of every schedule
row's decomposition, concatenated in schedule order — the compile-time
list stage A iterates and the row evaluation's slot index family. -/
noncomputable def levelAtoms (S : Setup L) (j : ℕ) :
    List (ScatterSentence (S.pal (j + 1))) :=
  (F S j).flatMap fun γ => (dec S γ).atoms.filterMap fun a =>
    match a with
    | .inl _ => none
    | .inr σa => some σa

theorem mem_levelAtoms {S : Setup L} {j : ℕ} {γ : Fml S j}
    (hγ : γ ∈ F S j) {σa : ScatterSentence (S.pal (j + 1))}
    (hσ : Sum.inr σa ∈ (dec S γ).atoms) : σa ∈ levelAtoms S j := by
  rw [levelAtoms, List.mem_flatMap]
  exact ⟨γ, hγ, List.mem_filterMap.mpr ⟨Sum.inr σa, hσ, rfl⟩⟩

theorem exists_of_mem_levelAtoms {S : Setup L} {j : ℕ}
    {σa : ScatterSentence (S.pal (j + 1))} (h : σa ∈ levelAtoms S j) :
    ∃ γ ∈ F S j, Sum.inr σa ∈ (dec S γ).atoms := by
  rw [levelAtoms, List.mem_flatMap] at h
  obtain ⟨γ, hγ, hmem⟩ := h
  obtain ⟨a, ha, heq⟩ := List.mem_filterMap.mp hmem
  refine ⟨γ, hγ, ?_⟩
  match a, heq with
  | .inr σa', heq =>
    obtain rfl : σa' = σa := by
      simpa using heq
    exact ha

/-- Every level atom's `β`-formula is a column of the child's family —
where stage A's column copy reads. -/
theorem levelAtoms_beta_mem {S : Setup L} {j : ℕ}
    {σa : ScatterSentence (S.pal (j + 1))} (h : σa ∈ levelAtoms S j) :
    σa.β ∈ levelFml S (j + 1) := by
  obtain ⟨γ, hγ, hσ⟩ := exists_of_mem_levelAtoms h
  exact scatterAtom_beta_mem_levelFml hγ hσ

/-! ## §1 The programs -/

open Classical in
/-- **The row evaluation's read family**: a local atom is a child-table
read at child name `rb.i` and the atom's column; a scatter atom is a
slot read off the kept guard bits. -/
noncomputable def avC (ct tsb : String) (S : Setup L) (j : ℕ) :
    DistFO (S.pal (j + 1)) 1 ⊕ ScatterSentence (S.pal (j + 1)) → Expr :=
  Sum.elim
    (fun ψ => .get ct (.add
      (.mul (.var "rb.i") (.lit (levelFml S (j + 1)).length))
      (.lit (memIdx (levelFml S (j + 1)) ψ))))
    (fun σa => .get tsb (.lit (memIdx (levelAtoms S j) σa)))

open Classical in
/-- **The row store**: one compiled combination per schedule row, into
the level table's row `rb.v` at compile-time column indices. -/
noncomputable def rowStores (tb ct tsb : String) (S : Setup L) (j : ℕ) :
    List (Fml S j) → ℕ → Com
  | [], _ => .skip
  | γ :: rest, i =>
    .seq (.store tb
        (.add (.mul (.var "rb.v") (.lit (levelFml S j).length)) (.lit i))
        (bcExprA (avC ct tsb S j) (dec S γ)))
      (rowStores tb ct tsb S j rest (i + 1))

open Classical in
/-- The row store's budget: `6` a store plus the compiled expression's
own size, summed over the schedule. -/
noncomputable def rowStoresK (ct tsb : String) (S : Setup L) (j : ℕ) :
    List (Fml S j) → ℕ
  | [] => 1
  | γ :: rest =>
    6 + (bcExprA (avC ct tsb S j) (dec S γ)).size + rowStoresK ct tsb S j rest

theorem one_le_rowStoresK (ct tsb : String) (S : Setup L) (j : ℕ) :
    ∀ l : List (Fml S j), 1 ≤ rowStoresK ct tsb S j l
  | [] => le_rfl
  | _ :: _ => by rw [rowStoresK]; omega

open Classical in
/-- **One turn of the row scan**: read the row entry, store its row iff
the assignment owns it, bump the counter. -/
noncomputable def rowBody (caj cmj tb ct tsb ctr : String) (S : Setup L)
    (j : ℕ) : Com :=
  .seq (.assign "rb.v" (.get cmj (.add (.var "rb.b") (.var "rb.i"))))
    (.seq (.ite (.eq (.get caj (.var "rb.v")) (.var ctr))
        (rowStores tb ct tsb S j (F S j) 0) .skip)
      (.assign "rb.i" (.add (.var "rb.i") (.lit 1))))

open Classical in
/-- **The whole pass**: stage A (the landed `topAtomsCom` at the child's
names over the level's atoms), then the row bounds off the cover CSR and
the guarded row scan. -/
noncomputable def readSegCom (caj coj cmj pa ma da tsb : String)
    (S : Setup L) (j : ℕ) : Com :=
  .seq (topAtomsCom (arenaNames (j + 1)) pa ma da tsb
      (levelFml S (j + 1)).length
      (fun σa => memIdx (levelFml S (j + 1)) σa.β) (levelAtoms S j) 0)
    (.seq (.assign "rb.b" (.get coj (.var (ctrName j))))
      (.seq (.assign "rb.s"
          (.sub (.get coj (.add (.var (ctrName j)) (.lit 1))) (.var "rb.b")))
        (.seq (.assign "rb.i" (.lit 0))
          (.while (.lt (.var "rb.i") (.var "rb.s"))
            (rowBody caj cmj (arenaNames j).tab (arenaNames (j + 1)).tab
              tsb (ctrName j) S j)))))

open Classical in
/-- **The pass's budget**, closed form per centre `u`: the summed
per-atom scatter budget over the child (`topScatK` at the child's
carrier and slot count), plus one row-scan turn — the row read, the
ownership test, the compiled row stores — per cluster member, plus the
scan's own overhead. -/
noncomputable def readSegK (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ct tsb : String) (j : ℕ) (A : Arena (S.pal j) n₀) (u : ℕ) : ℕ :=
  if h : u < A.N then
    topScatK (childN S A ((ord A.N A.G).order) ⟨u, h⟩)
        (∑ v : Fin (childN S A ((ord A.N A.G).order) ⟨u, h⟩),
          (childArena S A ((ord A.N A.G).order) ⟨u, h⟩).G.degree v)
        (levelAtoms S j)
      + ((14 + rowStoresK ct tsb S j (F S j) + 4)
          * childN S A ((ord A.N A.G).order) ⟨u, h⟩ + 16)
  else 0

open Classical in
/-- The budget at a genuine centre, the `Fin`-coercion cleared. -/
theorem readSegK_coe (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ct tsb : String) (j : ℕ) (A : Arena (S.pal j) n₀) (u : Fin A.N) :
    readSegK S ord ct tsb j A (u : ℕ)
      = topScatK (childN S A ((ord A.N A.G).order) u)
          (∑ v : Fin (childN S A ((ord A.N A.G).order) u),
            (childArena S A ((ord A.N A.G).order) u).G.degree v)
          (levelAtoms S j)
        + ((14 + rowStoresK ct tsb S j (F S j) + 4)
            * childN S A ((ord A.N A.G).order) u + 16) := by
  unfold readSegK
  rw [dif_pos u.2]

/-! ## §2 The write sets -/

theorem warrs_topAtomCom {nm : ArenaNames} {pa ma da tsb : String}
    {F i bi r t : ℕ} :
    ∀ b ∈ (topAtomCom nm pa ma da tsb F i bi r t).warrs,
      b = pa ∨ b = ma ∨ b = da ∨ b = tsb := by
  intro b hb
  simp only [topAtomCom, topGlueCom, topColCom, topBitCom, Com.warrs,
    Fill.warrs_put, warrs_scatterCom, List.append_nil, List.nil_append,
    List.mem_append, List.mem_cons, List.mem_singleton,
    List.not_mem_nil, or_false] at hb
  tauto

theorem warrs_topAtomsCom {nm : ArenaNames} {pa ma da tsb : String}
    {F : ℕ} {Λc : ℕ} {bIdx : ScatterSentence Λc → ℕ} :
    ∀ (l : List (ScatterSentence Λc)) (i : ℕ),
      ∀ b ∈ (topAtomsCom nm pa ma da tsb F bIdx l i).warrs,
        b = pa ∨ b = ma ∨ b = da ∨ b = tsb := by
  intro l
  induction l with
  | nil =>
    intro i b hb
    simp [topAtomsCom, Com.warrs] at hb
  | cons σa rest ih =>
    intro i b hb
    simp only [topAtomsCom, Com.warrs, List.mem_append] at hb
    rcases hb with hb | hb
    · exact warrs_topAtomCom b hb
    · exact ih (i + 1) b hb

theorem wvars_topAtomCom {nm : ArenaNames} {pa ma da tsb : String}
    {F i bi r t : ℕ} :
    ∀ y ∈ (topAtomCom nm pa ma da tsb F i bi r t).wvars, y ∈ gsScalars := by
  intro y hy
  simp only [topAtomCom, topGlueCom, topColCom, topBitCom, Com.wvars,
    Fill.wvars_put, List.append_nil, List.nil_append, List.mem_append,
    List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hy
  rcases hy with (rfl | rfl | rfl | rfl) | (rfl | rfl) | hy
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · exact wvars_scatterCom_subset _ _ _ _ _ y hy

theorem wvars_topAtomsCom {nm : ArenaNames} {pa ma da tsb : String}
    {F : ℕ} {Λc : ℕ} {bIdx : ScatterSentence Λc → ℕ} :
    ∀ (l : List (ScatterSentence Λc)) (i : ℕ),
      ∀ y ∈ (topAtomsCom nm pa ma da tsb F bIdx l i).wvars, y ∈ gsScalars := by
  intro l
  induction l with
  | nil =>
    intro i y hy
    simp [topAtomsCom, Com.wvars] at hy
  | cons σa rest ih =>
    intro i y hy
    simp only [topAtomsCom, Com.wvars, List.mem_append] at hy
    rcases hy with hy | hy
    · exact wvars_topAtomCom y hy
    · exact ih (i + 1) y hy

theorem warrs_rowStores {tb ct tsb : String} {S : Setup L} {j : ℕ} :
    ∀ (l : List (Fml S j)) (i : ℕ),
      ∀ b ∈ (rowStores tb ct tsb S j l i).warrs, b = tb := by
  intro l
  induction l with
  | nil => intro i b hb; simp [rowStores, Com.warrs] at hb
  | cons γ rest ih =>
    intro i b hb
    simp only [rowStores, Com.warrs, List.mem_append,
      List.mem_singleton] at hb
    rcases hb with rfl | hb
    · rfl
    · exact ih (i + 1) b hb

theorem wvars_rowStores {tb ct tsb : String} {S : Setup L} {j : ℕ} :
    ∀ (l : List (Fml S j)) (i : ℕ),
      (rowStores tb ct tsb S j l i).wvars = [] := by
  intro l
  induction l with
  | nil => intro i; simp [rowStores, Com.wvars]
  | cons γ rest ih =>
    intro i
    simp [rowStores, Com.wvars, ih (i + 1)]

/-- The pass's scratch scalars — the row scan's four cells plus the
scatter stage's shared pool. -/
def rbScalars : List String := ["rb.b", "rb.s", "rb.i", "rb.v"] ++ gsScalars

theorem wvars_readSegCom {caj coj cmj pa ma da tsb : String} {S : Setup L}
    {j : ℕ} :
    ∀ y ∈ (readSegCom caj coj cmj pa ma da tsb S j).wvars, y ∈ rbScalars := by
  intro y hy
  simp only [readSegCom, rowBody, Com.wvars, wvars_rowStores,
    List.append_nil, List.nil_append, List.mem_append, List.mem_cons,
    List.mem_singleton, List.not_mem_nil, or_false] at hy
  rcases hy with hy | rfl | rfl | rfl | rfl | rfl
  · exact List.mem_append_right _ (wvars_topAtomsCom _ _ y hy)
  · decide
  · decide
  · decide
  · decide
  · decide

theorem warrs_readSegCom {caj coj cmj pa ma da tsb : String} {S : Setup L}
    {j : ℕ} :
    ∀ b ∈ (readSegCom caj coj cmj pa ma da tsb S j).warrs,
      b = pa ∨ b = ma ∨ b = da ∨ b = tsb ∨ b = (arenaNames j).tab := by
  intro b hb
  simp only [readSegCom, rowBody, Com.warrs, List.append_nil,
    List.nil_append, List.mem_append] at hb
  rcases hb with hb | hb
  · rcases warrs_topAtomsCom _ _ b hb with h | h | h | h <;> tauto
  · have := warrs_rowStores _ _ b (by
      simpa using hb)
    tauto

/-! ## §3 The kept guard bits, and the per-atom reads -/

/-- A child never has an empty carrier: the centre is its own cluster
member. -/
theorem childN_pos (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) : 0 < childN S A π u :=
  (Set.ncard_pos (Set.toFinite _)).mpr ⟨u, self_mem_cluster S A π u⟩

open Classical in
/-- **The kept guard bits**: slot `m` of the slot region holds atom
`m`'s thresholded guarded-greedy count over the isolated child graph
and the atom's `β`-row set of the child's fuel-`k` table — exactly what
stage A leaves (`topAtomsCom_spec`'s cells, at the child instantiation)
and exactly what `rowAsn_scatter_bit` converts to the row assignment's
bit. -/
def SlotBits (tsb : String) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (k j : ℕ) (A : Arena (S.pal j) n₀) (u : Fin A.N) (τ : Env) : Prop :=
  ∀ m, (hm : m < (levelAtoms S j).length) →
    (τ.arrs tsb).getD m 0
      = if (levelAtoms S j)[m].t ≤ Impl.greedyScatter
            (childArena S A ((ord A.N A.G).order) u).G
            (levelAtoms S j)[m].r
            {z | Unroll.unrollAux S ord k (j + 1)
              (childArena S A ((ord A.N A.G).order) u) z
              (levelAtoms S j)[m].β}
            (levelAtoms S j)[m].t
        then 1 else 0

/-- `SlotBits` reads one array; it transports along agreement. -/
theorem slotBits_of_eq {tsb : String} {S : Setup L}
    {ord : CoverSpec.OrderingRoutine} {k j : ℕ} {A : Arena (S.pal j) n₀}
    {u : Fin A.N} {τ τ' : Env} (h : SlotBits tsb S ord k j A u τ)
    (ha : τ'.arrs tsb = τ.arrs tsb) : SlotBits tsb S ord k j A u τ' :=
  fun m hm => by rw [ha]; exact h m hm

open Classical in
/-- **Every atom's read delivers its bit of the row assignment** — the
`hav` premise of `bcExprA_evalB`, at the machine's actual reads: with
the counter `rb.i` at the child name of the centre-`u` vertex `vt`, a
local atom's child-table read is `rowAsn_local_bit`'s cell and a
scatter atom's slot read is `rowAsn_scatter_bit`'s guard bit. -/
theorem avC_evalB {B : ℕ} (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    {k j : ℕ} {A : Arena (S.pal j) n₀} {vt u : Fin A.N}
    (hv : centre S A ((ord A.N A.G).order) vt = u)
    (hchoice : S.choice = greedyChoice)
    {t : ℕ} (ht : t < childN S A ((ord A.N A.G).order) u)
    (hidx : (((childEquiv S A ((ord A.N A.G).order) u).symm
        ⟨vt, hv ▸ mem_cluster_centre S A ((ord A.N A.G).order) vt⟩ :
          Fin (childN S A ((ord A.N A.G).order) u)) : ℕ) = t)
    (h1B : 1 < B) (hcNB : childN S A ((ord A.N A.G).order) u < B)
    (hcNF1B : childN S A ((ord A.N A.G).order) u
      * (levelFml S (j + 1)).length < B)
    (hMB : (levelAtoms S j).length < B)
    {ct tsb : String} {τ : Env}
    (hT : TableBitsW ct (levelFml S (j + 1))
      (Unroll.unrollAux S ord k (j + 1)
        (childArena S A ((ord A.N A.G).order) u)) τ)
    (hslot : SlotBits tsb S ord k j A u τ)
    (htsbL : (levelAtoms S j).length ≤ (τ.arrs tsb).length)
    (hrbi : τ.vars "rb.i" = t)
    {γ : Fml S j} (hγ : γ ∈ F S j) :
    ∀ a ∈ (dec S γ).atoms,
      (avC ct tsb S j a).evalB B τ
        = some (if rowAsn S ord k j A vt a then 1 else 0) := by
  have hF1B : (levelFml S (j + 1)).length < B := by
    have h1 : 1 * (levelFml S (j + 1)).length
        ≤ childN S A ((ord A.N A.G).order) u
          * (levelFml S (j + 1)).length :=
      Nat.mul_le_mul_right _ (childN_pos S A _ u)
    omega
  intro a ha
  match a with
  | .inl ψ =>
    have hψF : ψ ∈ levelFml S (j + 1) := localAtom_mem_levelFml hγ ha
    have hiψ : memIdx (levelFml S (j + 1)) ψ
        < (levelFml S (j + 1)).length := memIdx_lt hψF
    have hbit := rowAsn_local_bit S ord hv hT hiψ (getElem_memIdx hψF)
    rw [hidx] at hbit
    have hlt : t * (levelFml S (j + 1)).length
          + memIdx (levelFml S (j + 1)) ψ
        < childN S A ((ord A.N A.G).order) u
          * (levelFml S (j + 1)).length :=
      tableIdx_lt (⟨t, ht⟩ : Fin (childN S A ((ord A.N A.G).order) u)) hiψ
    have hlen : t * (levelFml S (j + 1)).length
          + memIdx (levelFml S (j + 1)) ψ
        < (τ.arrs ct).length := lt_of_lt_of_le hlt hT.1
    show (Expr.get ct (.add
        (.mul (.var "rb.i") (.lit (levelFml S (j + 1)).length))
        (.lit (memIdx (levelFml S (j + 1)) ψ)))).evalB B τ = _
    have hvar : (Expr.var "rb.i").evalB B τ = some t := by
      rw [← hrbi]
      exact evalB_var (by rw [hrbi]; exact lt_trans ht hcNB)
    have hmul := evalB_bin (op := .mul) hvar (evalB_lit hF1B)
      (by rw [Bop.apply_mul]; omega)
    rw [Bop.apply_mul] at hmul
    have hadd := evalB_bin (op := .add) hmul
      (evalB_lit (lt_trans hiψ hF1B)) (by rw [Bop.apply_add]; omega)
    rw [Bop.apply_add] at hadd
    exact evalB_get hadd (getElem?_of_getD hlen hbit) (by split <;> omega)
  | .inr σa =>
    have hmemA : σa ∈ levelAtoms S j := mem_levelAtoms hγ ha
    have hsl : memIdx (levelAtoms S j) σa < (levelAtoms S j).length :=
      memIdx_lt hmemA
    have hcell := hslot _ hsl
    simp only [getElem_memIdx hmemA] at hcell
    rw [rowAsn_scatter_bit S ord hv hchoice σa] at hcell
    show (Expr.get tsb
        (.lit (memIdx (levelAtoms S j) σa))).evalB B τ = _
    exact evalB_get (evalB_lit (lt_trans hsl hMB))
      (getElem?_of_getD (lt_of_lt_of_le hsl htsbL) hcell)
      (by split <;> omega)

/-! ## §4 The row store, by induction over the schedule -/

open Classical in
/-- **The row store's `Spec`**: with `rb.v` at the parent name and
`rb.i` at the child name of one centre-`u` vertex, the compile-time
store sequence writes exactly the row's cells at indices `i0 + m` to
the decompositions' bits — every other cell of the table region, every
other array, and every scalar untouched, every length preserved. -/
theorem rowStores_spec {B : ℕ} (S : Setup L)
    (ord : CoverSpec.OrderingRoutine)
    {k j : ℕ} {A : Arena (S.pal j) n₀} {vt u : Fin A.N} {t : ℕ}
    (hv : centre S A ((ord A.N A.G).order) vt = u)
    (ht : t < childN S A ((ord A.N A.G).order) u)
    (hidx : (((childEquiv S A ((ord A.N A.G).order) u).symm
        ⟨vt, hv ▸ mem_cluster_centre S A ((ord A.N A.G).order) vt⟩ :
          Fin (childN S A ((ord A.N A.G).order) u)) : ℕ) = t)
    (hchoice : S.choice = greedyChoice)
    (h1B : 1 < B) (hANB : A.N < B)
    (hNF0B : A.N * (levelFml S j).length < B)
    (hcNB : childN S A ((ord A.N A.G).order) u < B)
    (hcNF1B : childN S A ((ord A.N A.G).order) u
      * (levelFml S (j + 1)).length < B)
    (hMB : (levelAtoms S j).length < B)
    {tb ct tsb : String} (hct_tb : ct ≠ tb) (htsb_tb : tsb ≠ tb)
    (l : List (Fml S j)) (i0 : ℕ)
    (hl : ∀ γ ∈ l, γ ∈ F S j)
    (hi0 : i0 + l.length ≤ (levelFml S j).length) :
    Spec B
      (fun τ =>
        TableBitsW ct (levelFml S (j + 1))
          (Unroll.unrollAux S ord k (j + 1)
            (childArena S A ((ord A.N A.G).order) u)) τ ∧
        SlotBits tsb S ord k j A u τ ∧
        (levelAtoms S j).length ≤ (τ.arrs tsb).length ∧
        A.N * (levelFml S j).length ≤ (τ.arrs tb).length ∧
        τ.vars "rb.v" = (vt : ℕ) ∧ τ.vars "rb.i" = t)
      (rowStores tb ct tsb S j l i0)
      (fun τ τ' =>
        (∀ m, (hm : m < l.length) →
          (τ'.arrs tb).getD
              ((vt : ℕ) * (levelFml S j).length + (i0 + m)) 0
            = if (dec S l[m]).eval (rowAsn S ord k j A vt)
              then 1 else 0) ∧
        (∀ c : ℕ, (∀ m, m < l.length →
            c ≠ (vt : ℕ) * (levelFml S j).length + (i0 + m)) →
          (τ'.arrs tb).getD c 0 = (τ.arrs tb).getD c 0) ∧
        (∀ b, b ≠ tb → τ'.arrs b = τ.arrs b) ∧
        (∀ b, (τ'.arrs b).length = (τ.arrs b).length) ∧
        τ'.vars = τ.vars)
      (rowStoresK ct tsb S j l) := by
  revert hl hi0
  induction l generalizing i0 with
  | nil =>
    intro hl hi0
    refine (Spec.skip.post ?_).mono (le_of_eq (by rw [rowStoresK]))
    rintro τ τ' - rfl
    exact ⟨fun m hm => absurd hm (Nat.not_lt_zero m),
      fun c _ => rfl, fun b _ => rfl, fun b => rfl, rfl⟩
  | cons γ rest ih =>
    intro hl hi0
    have hi0F : i0 < (levelFml S j).length := by
      rw [List.length_cons] at hi0
      omega
    have hγF : γ ∈ F S j := hl γ (List.mem_cons_self ..)
    -- the head store
    have hstore : Spec B
        (fun τ =>
          TableBitsW ct (levelFml S (j + 1))
            (Unroll.unrollAux S ord k (j + 1)
              (childArena S A ((ord A.N A.G).order) u)) τ ∧
          SlotBits tsb S ord k j A u τ ∧
          (levelAtoms S j).length ≤ (τ.arrs tsb).length ∧
          A.N * (levelFml S j).length ≤ (τ.arrs tb).length ∧
          τ.vars "rb.v" = (vt : ℕ) ∧ τ.vars "rb.i" = t)
        (.store tb
          (.add (.mul (.var "rb.v") (.lit (levelFml S j).length))
            (.lit i0))
          (bcExprA (avC ct tsb S j) (dec S γ)))
        (fun τ τ' => τ' = τ.setArr tb
          ((vt : ℕ) * (levelFml S j).length + i0)
          (if (dec S γ).eval (rowAsn S ord k j A vt) then 1 else 0))
        (1 + 5 + (bcExprA (avC ct tsb S j) (dec S γ)).size) := by
      have hidxlt : (vt : ℕ) * (levelFml S j).length + i0
          < A.N * (levelFml S j).length := tableIdx_lt vt hi0F
      have hF0B : (levelFml S j).length < B := by
        have h1 : 1 * (levelFml S j).length
            ≤ A.N * (levelFml S j).length :=
          Nat.mul_le_mul_right _ vt.pos
        omega
      refine Spec.store
        (idx := fun _ => (vt : ℕ) * (levelFml S j).length + i0)
        (f := fun _ =>
          if (dec S γ).eval (rowAsn S ord k j A vt) then 1 else 0)
        ?_ ?_ ?_
      · rintro τ ⟨-, -, -, -, hrbv, -⟩
        have hvar : (Expr.var "rb.v").evalB B τ = some (vt : ℕ) := by
          rw [← hrbv]
          exact evalB_var (by rw [hrbv]; exact lt_trans vt.2 hANB)
        have hmul := evalB_bin (op := .mul) hvar (evalB_lit hF0B)
          (by rw [Bop.apply_mul]; omega)
        rw [Bop.apply_mul] at hmul
        have hadd := evalB_bin (op := .add) hmul
          (evalB_lit (lt_trans hi0F hF0B))
          (by rw [Bop.apply_add]; omega)
        rw [Bop.apply_add] at hadd
        exact hadd
      · rintro τ ⟨hT, hslot, htsbL, -, -, hrbi⟩
        exact bcExprA_evalB h1B (dec S γ)
          (avC_evalB S ord hv hchoice ht hidx h1B hcNB hcNF1B hMB
            hT hslot htsbL hrbi hγF)
      · rintro τ ⟨-, -, -, htbL, -, -⟩
        exact lt_of_lt_of_le hidxlt htbL
    -- the tail, from the stored state
    have htail := ih (i0 + 1)
      (fun γ' h => hl γ' (List.mem_cons_of_mem _ h))
      (by rw [List.length_cons] at hi0; omega)
    refine ((hstore.seq htail ?_ ?_).mono ?_)
    · -- the store preserves the precondition
      rintro τ τ' ⟨hT, hslot, htsbL, htbL, hrbv, hrbi⟩ rfl
      refine ⟨tableBitsW_of_eq hT (by simp [hct_tb]),
        slotBits_of_eq hslot (by simp [htsb_tb]), ?_, ?_, ?_, ?_⟩
      · rw [arrs_setArr, if_neg htsb_tb]
        exact htsbL
      · rw [length_arrs_setArr]
        exact htbL
      · rw [vars_setArr]
        exact hrbv
      · rw [vars_setArr]
        exact hrbi
    · -- the composite postcondition
      rintro τ τ' τ'' ⟨-, -, -, htbL, -, -⟩ rfl
        ⟨hnew, hkeep, hoth, hlen, hvars⟩
      have hrange : (vt : ℕ) * (levelFml S j).length + i0
          < (τ.arrs tb).length :=
        lt_of_lt_of_le (tableIdx_lt vt hi0F) htbL
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- the new cells
        intro m hm
        cases m with
        | zero =>
          have hk := hkeep ((vt : ℕ) * (levelFml S j).length + i0)
            (fun m' hm' => by omega)
          rw [Nat.add_zero, hk, arrs_setArr, if_pos rfl,
            getD_set_self hrange]
          simp only [List.getElem_cons_zero]
          exact if_congr Iff.rfl rfl rfl
        | succ m =>
          have hm' : m < rest.length := by
            rw [List.length_cons] at hm
            omega
          have h2 := hnew m hm'
          have harith : i0 + (m + 1) = i0 + 1 + m := by omega
          rw [harith]
          simpa only [List.getElem_cons_succ] using h2
      · -- the untouched cells
        intro c hc
        have hc0 : c ≠ (vt : ℕ) * (levelFml S j).length + i0 := by
          have := hc 0 (by rw [List.length_cons]; omega)
          rwa [Nat.add_zero] at this
        have hcrest : ∀ m, m < rest.length →
            c ≠ (vt : ℕ) * (levelFml S j).length + (i0 + 1 + m) := by
          intro m hm
          have := hc (m + 1) (by rw [List.length_cons]; omega)
          have harith : i0 + (m + 1) = i0 + 1 + m := by omega
          rwa [harith] at this
        rw [hkeep c hcrest, arrs_setArr, if_pos rfl, getD_set_ne hc0]
      · -- the other arrays
        intro b hb
        rw [hoth b hb, arrs_setArr, if_neg hb]
      · -- the lengths
        intro b
        rw [hlen b, length_arrs_setArr]
      · -- the scalars
        rw [hvars, vars_setArr]
    · -- the cost
      rw [rowStoresK]

/-! ## §5 The row scan's invariant, and one turn -/

open Classical in
/-- **The row scan's invariant**: the counter cells, the read regions
(child table, kept slots, the cover's assignment and membership arrays
as at entry), no reallocation, and the table region's cells in both
directions — rows of already-scanned positions whose entry the
assignment owns hold `RowEval`'s bits; rows of unowned vertices and of
not-yet-scanned positions read as at entry. Positions index the
cluster row (`restrictEmb`'s ascending enumeration), so the write-set
bookkeeping is on plain naturals. -/
def RowLoopInv (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (k j : ℕ) (A : Arena (S.pal j) n₀) (u : Fin A.N)
    (caj cmj tsb : String) (base : ℕ) (σ1 : Env) (τ : Env) : Prop :=
  τ.vars (ctrName j) = (u : ℕ) ∧
  τ.vars "rb.b" = base ∧
  τ.vars "rb.s" = childN S A ((ord A.N A.G).order) u ∧
  τ.vars "rb.i" ≤ childN S A ((ord A.N A.G).order) u ∧
  TableBitsW (arenaNames (j + 1)).tab (levelFml S (j + 1))
    (Unroll.unrollAux S ord k (j + 1)
      (childArena S A ((ord A.N A.G).order) u)) τ ∧
  SlotBits tsb S ord k j A u τ ∧
  τ.arrs caj = σ1.arrs caj ∧
  τ.arrs cmj = σ1.arrs cmj ∧
  (∀ b, (τ.arrs b).length = (σ1.arrs b).length) ∧
  -- scanned and owned: the bits
  (∀ p : ℕ, ∀ hp : p < childN S A ((ord A.N A.G).order) u,
    p < τ.vars "rb.i" →
    centre S A ((ord A.N A.G).order)
        (Impl.restrictEmb (cluster S A ((ord A.N A.G).order) u) ⟨p, hp⟩)
      = u →
    ∀ (m : ℕ), ∀ hm : m < (levelFml S j).length,
      (τ.arrs (arenaNames j).tab).getD
          ((Impl.restrictEmb (cluster S A ((ord A.N A.G).order) u)
              ⟨p, hp⟩ : ℕ) * (levelFml S j).length + m) 0
        = if RowEval S ord k j A
            (Impl.restrictEmb (cluster S A ((ord A.N A.G).order) u)
              ⟨p, hp⟩)
            (levelFml S j)[m] then 1 else 0) ∧
  -- unowned: as at entry
  (∀ v : Fin A.N, ¬ centre S A ((ord A.N A.G).order) v = u →
    ∀ m, m < (levelFml S j).length →
      (τ.arrs (arenaNames j).tab).getD
          ((v : ℕ) * (levelFml S j).length + m) 0
        = (σ1.arrs (arenaNames j).tab).getD
          ((v : ℕ) * (levelFml S j).length + m) 0) ∧
  -- not yet scanned: as at entry
  (∀ p : ℕ, ∀ hp : p < childN S A ((ord A.N A.G).order) u,
    τ.vars "rb.i" ≤ p →
    ∀ m, m < (levelFml S j).length →
      (τ.arrs (arenaNames j).tab).getD
          ((Impl.restrictEmb (cluster S A ((ord A.N A.G).order) u)
              ⟨p, hp⟩ : ℕ) * (levelFml S j).length + m) 0
        = (σ1.arrs (arenaNames j).tab).getD
          ((Impl.restrictEmb (cluster S A ((ord A.N A.G).order) u)
              ⟨p, hp⟩ : ℕ) * (levelFml S j).length + m) 0)

open Classical in
/-- **One turn of the row scan**: read the position's entry, store its
row iff the assignment owns it, bump the counter — the invariant is
maintained and the counter steps, within the uniform per-turn budget. -/
theorem rowBody_spec {B : ℕ} (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (k j : ℕ) (A : Arena (S.pal j) n₀) (u : Fin A.N)
    {caj cmj tsb : String} (σ1 : Env) (base : ℕ)
    (hchoice : S.choice = greedyChoice)
    (h1B : 1 < B) (hANB : A.N < B) (hANNB : A.N * A.N < B)
    (hNF0B : A.N * (levelFml S j).length < B)
    (hcNF1B : childN S A ((ord A.N A.G).order) u
      * (levelFml S (j + 1)).length < B)
    (hMB : (levelAtoms S j).length < B)
    (hca_tb : caj ≠ (arenaNames j).tab)
    (hcm_tb : cmj ≠ (arenaNames j).tab)
    (htsb_tb : tsb ≠ (arenaNames j).tab)
    (hctrA1 : CtrArr caj (centre S A ((ord A.N A.G).order)) σ1)
    (hbase_le : base + childN S A ((ord A.N A.G).order) u ≤ A.N * A.N)
    (hcmL1 : base + childN S A ((ord A.N A.G).order) u
      ≤ (σ1.arrs cmj).length)
    (hrow : ∀ t : ℕ, ∀ ht : t < childN S A ((ord A.N A.G).order) u,
      (σ1.arrs cmj).getD (base + t) 0
        = (Impl.restrictEmb (cluster S A ((ord A.N A.G).order) u)
            ⟨t, ht⟩ : ℕ))
    (htbL1 : A.N * (levelFml S j).length
      ≤ (σ1.arrs (arenaNames j).tab).length)
    (htsbL1 : (levelAtoms S j).length ≤ (σ1.arrs tsb).length) :
    Spec B
      (fun τ => RowLoopInv S ord k j A u caj cmj tsb base σ1 τ ∧
        τ.vars "rb.i" < childN S A ((ord A.N A.G).order) u)
      (rowBody caj cmj (arenaNames j).tab (arenaNames (j + 1)).tab tsb
        (ctrName j) S j)
      (fun τ τ' => RowLoopInv S ord k j A u caj cmj tsb base σ1 τ' ∧
        τ'.vars "rb.i" = τ.vars "rb.i" + 1)
      (14 + rowStoresK (arenaNames (j + 1)).tab tsb S j (F S j)) := by
  have hcNle : childN S A ((ord A.N A.G).order) u ≤ A.N := ncard_le_card _
  have hctr_rbv : ctrName j ≠ "rb.v" :=
    lv_ne_of_base_ne (by decide) (by decide) j 0
  have hctr_rbi : ctrName j ≠ "rb.i" :=
    lv_ne_of_base_ne (by decide) (by decide) j 0
  have hctr_rbb : ctrName j ≠ "rb.b" :=
    lv_ne_of_base_ne (by decide) (by decide) j 0
  have hctr_rbs : ctrName j ≠ "rb.s" :=
    lv_ne_of_base_ne (by decide) (by decide) j 0
  have hct_tb : (arenaNames (j + 1)).tab ≠ (arenaNames j).tab :=
    lv_ne_of_level_ne (by decide) (by omega)
  rintro τ ⟨hInv, hlt⟩
  obtain ⟨hctr, hrbb, hrbs, hrbile, hT, hslot, hcaEq, hcmEq, hlenEq,
    hdone, hnotc, hnotyet⟩ := hInv
  have huB : (u : ℕ) < B := lt_trans u.2 hANB
  have htB : τ.vars "rb.i" < B := by
    have := lt_of_lt_of_le hlt hcNle
    omega
  -- §1 the entry read: `rb.v := cm[rb.b + rb.i]`
  have haddv : (Expr.add (.var "rb.b") (.var "rb.i")).evalB B τ
      = some (base + τ.vars "rb.i") := by
    have h := evalB_bin (op := .add)
      (evalB_var (x := "rb.b") (by rw [hrbb]; omega))
      (evalB_var (x := "rb.i") htB)
      (by rw [Bop.apply_add, hrbb]; omega)
    rwa [Bop.apply_add, hrbb] at h
  have hread : (τ.arrs cmj).getD (base + τ.vars "rb.i") 0
      = (Impl.restrictEmb (cluster S A ((ord A.N A.G).order) u)
          ⟨τ.vars "rb.i", hlt⟩ : ℕ) := by
    rw [hcmEq]
    exact hrow _ hlt
  have hcmLτ : base + τ.vars "rb.i" < (τ.arrs cmj).length := by
    rw [hcmEq]
    omega
  have hgetv : (Expr.get cmj (.add (.var "rb.b") (.var "rb.i"))).evalB B τ
      = some (Impl.restrictEmb (cluster S A ((ord A.N A.G).order) u)
          ⟨τ.vars "rb.i", hlt⟩ : ℕ) :=
    evalB_get haddv (getElem?_of_getD hcmLτ hread)
      (lt_trans (Impl.restrictEmb _ _).2 hANB)
  -- the scanned vertex
  set vt : Fin A.N :=
    Impl.restrictEmb (cluster S A ((ord A.N A.G).order) u)
      ⟨τ.vars "rb.i", hlt⟩ with hvt_def
  have hvtmem : vt ∈ cluster S A ((ord A.N A.G).order) u :=
    Impl.restrictEmb_mem _ _
  -- §2 the ownership test's evaluation
  have hcond : ∀ τa : Env, τa.vars "rb.v" = (vt : ℕ) →
      τa.arrs caj = σ1.arrs caj → τa.vars (ctrName j) = (u : ℕ) →
      (Cond.eq (.get caj (.var "rb.v")) (.var (ctrName j))).evalB B τa
        = some (((centre S A ((ord A.N A.G).order) vt : ℕ)) == (u : ℕ)) := by
    intro τa hrbv hcaEq' hctr'
    have hcaval : (τa.arrs caj).getD (vt : ℕ) 0
        = (centre S A ((ord A.N A.G).order) vt : ℕ) := by
      rw [hcaEq']
      exact hctrA1.2 vt
    have hcaLτ : (vt : ℕ) < (τa.arrs caj).length := by
      rw [hcaEq']
      exact lt_of_lt_of_le vt.2 hctrA1.1
    have hvarv : (Expr.var "rb.v").evalB B τa = some (vt : ℕ) := by
      rw [← hrbv]
      exact evalB_var (by rw [hrbv]; exact lt_trans vt.2 hANB)
    have hgetca : (Expr.get caj (.var "rb.v")).evalB B τa
        = some (centre S A ((ord A.N A.G).order) vt : ℕ) :=
      evalB_get hvarv (getElem?_of_getD hcaLτ hcaval)
        (lt_trans (centre S A ((ord A.N A.G).order) vt).2 hANB)
    have hvarc : (Expr.var (ctrName j)).evalB B τa = some (u : ℕ) := by
      rw [← hctr']
      exact evalB_var (by rw [hctr']; exact huB)
    exact evalB_condEq hgetca hvarc
  -- the state after the entry read
  have hτa_rbv : (τ.setVar "rb.v" (vt : ℕ)).vars "rb.v" = (vt : ℕ) := by
    simp
  have hτa_rbi : (τ.setVar "rb.v" (vt : ℕ)).vars "rb.i" = τ.vars "rb.i" := by
    simp
  have hτa_ctr : (τ.setVar "rb.v" (vt : ℕ)).vars (ctrName j) = (u : ℕ) := by
    rw [vars_setVar, if_neg hctr_rbv]
    exact hctr
  -- §3 the branch
  by_cases hvu : centre S A ((ord A.N A.G).order) vt = u
  · -- the assignment owns the entry: store the row
    have htrue : (Cond.eq (.get caj (.var "rb.v"))
        (.var (ctrName j))).evalB B (τ.setVar "rb.v" (vt : ℕ))
        = some true := by
      rw [hcond _ hτa_rbv (by simp [hcaEq]) hτa_ctr, hvu]
      exact congrArg some (beq_self_eq_true _)
    -- the child-name seam: `vt`'s child name is the counter
    have hidx : (((childEquiv S A ((ord A.N A.G).order) u).symm
        ⟨vt, hvu ▸ mem_cluster_centre S A ((ord A.N A.G).order) vt⟩ :
          Fin (childN S A ((ord A.N A.G).order) u)) : ℕ) = τ.vars "rb.i" :=
      congrArg Fin.val
        (childEquiv_symm_restrictEmb S A ((ord A.N A.G).order) u hlt hvtmem)
    -- the row store
    have hrs := rowStores_spec S ord hvu hlt hidx hchoice h1B hANB hNF0B
      (lt_of_le_of_lt hcNle hANB)
      hcNF1B hMB hct_tb htsb_tb (F S j) 0 (fun γ h => h)
      (by rw [levelFml_length]; omega)
    obtain ⟨τb, hr2, hnew, hkeep, hoth, hlen2, hvars2⟩ :=
      hrs (τ.setVar "rb.v" (vt : ℕ))
        ⟨tableBitsW_of_eq hT (by simp),
          slotBits_of_eq hslot (by simp),
          by simp only [arrs_setVar]; rw [hlenEq]; exact htsbL1,
          by simp only [arrs_setVar]; rw [hlenEq]; exact htbL1,
          hτa_rbv, hτa_rbi⟩
    -- the increment
    have hrbi_b : τb.vars "rb.i" = τ.vars "rb.i" := by
      rw [hvars2]
      exact hτa_rbi
    have hinc : (Expr.add (.var "rb.i") (.lit 1)).evalB B τb
        = some (τ.vars "rb.i" + 1) := by
      have h := evalB_bin (op := .add)
        (evalB_var (x := "rb.i") (σ := τb) (by rw [hrbi_b]; exact htB))
        (evalB_lit h1B)
        (by rw [Bop.apply_add, hrbi_b]
            have := lt_of_lt_of_le hlt hcNle
            omega)
      rwa [Bop.apply_add, hrbi_b] at h
    refine ⟨(τb.setVar "rb.i" (τ.vars "rb.i" + 1)),
      ((Run.assign hgetv).seq
        ((Run.ite_true htrue hr2).seq (Run.assign hinc))).mono ?_,
      ?_, by simp⟩
    · -- the cost
      show 1 + 4 + (1 + 4 + rowStoresK (arenaNames (j + 1)).tab tsb S j
        (F S j) + (1 + 3)) ≤ _
      omega
    · -- the invariant, re-established
      have harr_c : ∀ b, b ≠ (arenaNames j).tab →
          (τb.setVar "rb.i" (τ.vars "rb.i" + 1)).arrs b = τ.arrs b := by
        intro b hb
        simp only [arrs_setVar]
        rw [hoth b hb]
      have harr_tb : (τb.setVar "rb.i" (τ.vars "rb.i" + 1)).arrs
          (arenaNames j).tab = τb.arrs (arenaNames j).tab := by
        simp
      have hvars_c : ∀ y, y ≠ "rb.i" →
          (τb.setVar "rb.i" (τ.vars "rb.i" + 1)).vars y
            = (τ.setVar "rb.v" (vt : ℕ)).vars y := by
        intro y hy
        rw [vars_setVar, if_neg hy, hvars2]
      refine ⟨?_, ?_, ?_, by simp; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hvars_c _ hctr_rbi]
        exact hτa_ctr
      · rw [hvars_c _ (by decide), vars_setVar, if_neg (by decide)]
        exact hrbb
      · rw [hvars_c _ (by decide), vars_setVar, if_neg (by decide)]
        exact hrbs
      · exact tableBitsW_of_eq hT (harr_c _ hct_tb)
      · exact slotBits_of_eq hslot (harr_c _ htsb_tb)
      · rw [harr_c _ hca_tb]
        exact hcaEq
      · rw [harr_c _ hcm_tb]
        exact hcmEq
      · intro b
        simp only [arrs_setVar]
        rw [hlen2 b]
        simp only [arrs_setVar]
        exact hlenEq b
      · -- scanned-and-owned rows hold the bits
        intro p hp hplt hcen m hm
        rw [vars_setVar, if_pos rfl] at hplt
        rcases Nat.lt_succ_iff_lt_or_eq.mp hplt with hplt' | hpe
        · -- an earlier position: untouched this turn
          have hvne : Impl.restrictEmb
              (cluster S A ((ord A.N A.G).order) u) ⟨p, hp⟩ ≠ vt := by
            intro h
            have := (Impl.restrictEmb _).injective h
            have hpt : p = τ.vars "rb.i" := by
              simpa using congrArg Fin.val this
            omega
          rw [harr_tb, hkeep _ ?_]
          · exact hdone p hp hplt' hcen m hm
          · intro m' hm' heq
            have := row_cell_inj hm
              (by rw [← levelFml_length]; exact hm')
              (by rw [Nat.zero_add] at heq ⊢; exact heq)
            exact hvne (Fin.val_injective this)
        · -- the freshly stored row
          subst hpe
          have h2 := hnew m (by rw [← levelFml_length]; exact hm)
          rw [Nat.zero_add] at h2
          have hconv : RowEval S ord k j A
              (Impl.restrictEmb (cluster S A ((ord A.N A.G).order) u)
                ⟨τ.vars "rb.i", hp⟩) (levelFml S j)[m]
              = ((dec S ((F S j)[m]'(by rw [← levelFml_length]; exact hm))).eval
                (rowAsn S ord k j A
                  (Impl.restrictEmb (cluster S A ((ord A.N A.G).order) u)
                    ⟨τ.vars "rb.i", hp⟩))) := by
            have hβ : (levelFml S j)[m]
                = ((F S j)[m]'(by rw [← levelFml_length]; exact hm)).fml := by
              simp [levelFml]
            rw [hβ]
            exact rowEval_eq_dec_eval S ord k j A _ ⟨Fml.isLocal _, Fml.drank _⟩
          rw [harr_tb, hconv]
          exact h2
      · -- unowned rows untouched
        intro v hvne m hm
        have hvvt : v ≠ vt := fun h => hvne (h ▸ hvu)
        rw [harr_tb, hkeep _ ?_]
        · exact hnotc v hvne m hm
        · intro m' hm' heq
          exact hvvt (Fin.val_injective (row_cell_inj hm
            (by rw [← levelFml_length]; exact hm')
            (by rw [Nat.zero_add] at heq ⊢; exact heq)))
      · -- not-yet-scanned rows untouched
        intro p hp hple m hm
        rw [vars_setVar, if_pos rfl] at hple
        have hvne : Impl.restrictEmb
            (cluster S A ((ord A.N A.G).order) u) ⟨p, hp⟩ ≠ vt := by
          intro h
          have := (Impl.restrictEmb _).injective h
          have hpt : p = τ.vars "rb.i" := by
            simpa using congrArg Fin.val this
          omega
        rw [harr_tb, hkeep _ ?_]
        · exact hnotyet p hp (by omega) m hm
        · intro m' hm' heq
          exact hvne (Fin.val_injective (row_cell_inj hm
            (by rw [← levelFml_length]; exact hm')
            (by rw [Nat.zero_add] at heq ⊢; exact heq)))
  · -- the assignment does not own the entry: skip
    have hfalse : (Cond.eq (.get caj (.var "rb.v"))
        (.var (ctrName j))).evalB B (τ.setVar "rb.v" (vt : ℕ))
        = some false := by
      rw [hcond _ hτa_rbv (by simp [hcaEq]) hτa_ctr]
      exact congrArg some (beq_eq_false_iff_ne.mpr
        (fun h => hvu (Fin.ext h)))
    have hinc : (Expr.add (.var "rb.i") (.lit 1)).evalB B
        (τ.setVar "rb.v" (vt : ℕ)) = some (τ.vars "rb.i" + 1) := by
      have h := evalB_bin (op := .add)
        (evalB_var (x := "rb.i") (σ := τ.setVar "rb.v" (vt : ℕ))
          (by rw [hτa_rbi]; exact htB))
        (evalB_lit h1B)
        (by rw [Bop.apply_add, hτa_rbi]
            have := lt_of_lt_of_le hlt hcNle
            omega)
      rwa [Bop.apply_add, hτa_rbi] at h
    refine ⟨((τ.setVar "rb.v" (vt : ℕ)).setVar "rb.i" (τ.vars "rb.i" + 1)),
      ((Run.assign hgetv).seq
        ((Run.ite_false hfalse Run.skip).seq (Run.assign hinc))).mono ?_,
      ?_, by simp⟩
    · -- the cost
      show 1 + 4 + (1 + 4 + 1 + (1 + 3)) ≤ _
      have := one_le_rowStoresK (arenaNames (j + 1)).tab tsb S j (F S j)
      omega
    · -- the invariant, re-established (no cell moved)
      have harr : ∀ b,
          ((τ.setVar "rb.v" (vt : ℕ)).setVar "rb.i"
            (τ.vars "rb.i" + 1)).arrs b = τ.arrs b := by
        intro b
        simp
      have hvars_c : ∀ y, y ≠ "rb.i" → y ≠ "rb.v" →
          ((τ.setVar "rb.v" (vt : ℕ)).setVar "rb.i"
            (τ.vars "rb.i" + 1)).vars y = τ.vars y := by
        intro y h1 h2
        rw [vars_setVar, if_neg h1, vars_setVar, if_neg h2]
      refine ⟨?_, ?_, ?_, by simp; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hvars_c _ hctr_rbi hctr_rbv]
        exact hctr
      · rw [hvars_c _ (by decide) (by decide)]
        exact hrbb
      · rw [hvars_c _ (by decide) (by decide)]
        exact hrbs
      · exact tableBitsW_of_eq hT (harr _)
      · exact slotBits_of_eq hslot (harr _)
      · rw [harr]
        exact hcaEq
      · rw [harr]
        exact hcmEq
      · intro b
        rw [harr]
        exact hlenEq b
      · -- scanned-and-owned rows: the new position is not owned
        intro p hp hplt hcen m hm
        rw [vars_setVar, if_pos rfl] at hplt
        rcases Nat.lt_succ_iff_lt_or_eq.mp hplt with hplt' | hpe
        · rw [harr]
          exact hdone p hp hplt' hcen m hm
        · subst hpe
          exact absurd hcen hvu
      · intro v hvne m hm
        rw [harr]
        exact hnotc v hvne m hm
      · intro p hp hple m hm
        rw [vars_setVar, if_pos rfl] at hple
        rw [harr]
        exact hnotyet p hp (by omega) m hm

end Lax3Proofs.Prog
