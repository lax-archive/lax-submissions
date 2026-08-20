import Lax3Proofs.SolveSegPrep

/-!
# F6c10a (part 2) — the return path: the recursive clause and the
partial table, discharged

The read segment's residual `CentreRead` asserts three genuinely
different things: (i) the machine pass — the per-atom scatters on the
isolated child and the readback of the rows `{v | centre v = u}` via
the compiled combination per schedule row; (ii) that what the pass
writes into a row **is** `frameEval`'s recursive clause — the seam
`Unroll.unrollAux (k+1)` closes over; and (iii) that the loop invariant
survives to `u + 1`. This file discharges (ii) and (iii) and names (i):

* **`RowEval`** is the recursive clause, written as the machine
  computes it: the chosen decomposition of the schedule row evaluated
  over the **child's fuel-`k` tables** (`BlockPost`'s deliverable) at
  the child name of `v`, and the scatter-atom counts over the child's
  graph — the body of `Unroll.frameEval`'s non-leaf branch with the
  oracle instantiated at `unrollAux k (j+1)`, verbatim.
  `unrollAux_succ_of_ne_bot` proves it **equals `unrollAux (k+1)`** on
  a non-edgeless arena — definitionally, once the leaf guard is
  discharged — so a pass that lands `RowEval`'s bits has landed the
  contract's table values on the nose.
* **`tablePartial_succ`** is the write-once step of the partial table:
  rows of centres below `u` untouched, rows of centre `u` newly at the
  target values, gives `TablePartial` at `u + 1`.
* **`ReadRows`** is the named machine residual: from the invariant at
  `u` (counter at `u`) plus the child's `BlockPost`, the pass writes
  exactly the centre-`u` rows of the level table at `RowEval`'s bits
  (every other row's cells untouched), leaves the level's cells, the
  cover's three arrays and the five non-table regions alone, and
  reallocates nothing. `centreRead_of_rows` then concludes **verbatim
  `CentreRead`**: the invariant's windowed contract, assignment region,
  cluster CSR and table length cross by the frame clauses, the partial
  table steps by `tablePartial_succ` through
  `unrollAux_succ_of_ne_bot`, and the counter clause is the frame's.
* **`centreReadAll_of_rows`** concludes **verbatim `CentreReadAll`**,
  and **`centreStepAll_of_childLoad_rows`** wires both segment files
  end to end: verbatim `CentreStepAll` at the canonical body
  `centreBody prepC readC` from the two named machine passes
  (`ChildLoadAll`, `ReadRowsAll`) plus `SolveStep`'s F7-suppliable
  hypotheses.

No cost is restated: `ReadRows` carries `KR` itself.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

variable {L n₀ : ℕ}

/-! ## §1 The recursive clause, as the machine computes it -/

/-- **The row assignment**: the valuation of the decomposition's atoms
at vertex `v` over the child's **fuel-`k`** tables — the local atoms
read at `v`'s child name, the scatter atoms as threshold tests of the
choice's count over the child's graph. Exactly the `Sum.elim` of
`Unroll.frameEval`'s non-leaf branch with the oracle instantiated at
`unrollAux k (j+1)`. -/
noncomputable def rowAsn (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (k j : ℕ) (A : Arena (S.pal j) n₀) (v : Fin A.N) :
    DistFO (S.pal (j + 1)) 1 ⊕ ScatterSentence (S.pal (j + 1)) → Prop :=
  Sum.elim
    (fun ψ => Unroll.unrollAux S ord k (j + 1)
      (childArena S A ((ord A.N A.G).order)
        (centre S A ((ord A.N A.G).order) v))
      ((childEquiv S A ((ord A.N A.G).order)
          (centre S A ((ord A.N A.G).order) v)).symm
        ⟨v, mem_cluster_centre S A ((ord A.N A.G).order) v⟩) ψ)
    (fun σa => σa.t ≤ S.choice.size
      (childArena S A ((ord A.N A.G).order)
        (centre S A ((ord A.N A.G).order) v)).G σa.r
      {a | Unroll.unrollAux S ord k (j + 1)
        (childArena S A ((ord A.N A.G).order)
          (centre S A ((ord A.N A.G).order) v)) a σa.β})

/-- **The row assignment at a centre-`u` vertex reads the child of
`u`** — the dependent rewrite the readback discharger needs: for `v`
with `centre v = u`, every atom's bit is data of `childArena … u`
(whose `BlockPost` the pass holds) at `v`'s child name. -/
theorem rowAsn_of_centre {S : Setup L} {ord : CoverSpec.OrderingRoutine}
    {k j : ℕ} {A : Arena (S.pal j) n₀} {v u : Fin A.N}
    (hv : centre S A ((ord A.N A.G).order) v = u) :
    rowAsn S ord k j A v = Sum.elim
      (fun ψ => Unroll.unrollAux S ord k (j + 1)
        (childArena S A ((ord A.N A.G).order) u)
        ((childEquiv S A ((ord A.N A.G).order) u).symm
          ⟨v, hv ▸ mem_cluster_centre S A ((ord A.N A.G).order) v⟩) ψ)
      (fun σa => σa.t ≤ S.choice.size
        (childArena S A ((ord A.N A.G).order) u).G σa.r
        {a | Unroll.unrollAux S ord k (j + 1)
          (childArena S A ((ord A.N A.G).order) u) a σa.β}) := by
  subst hv
  rfl

open Classical in
/-- **The recursive clause of one table row, at the machine's seam**:
the chosen decomposition of `β` evaluated at the row assignment —
exactly the body of `Unroll.frameEval`'s non-leaf branch with the
oracle instantiated at `unrollAux k (j+1)`. A readback pass that
computes the compiled combination per schedule row over `BlockPost`'s
table region and the scatter counts lands exactly these bits
(`bcExprA_evalB_rowEval` below). -/
def RowEval (S : Setup L) (ord : CoverSpec.OrderingRoutine) (k j : ℕ)
    (A : Arena (S.pal j) n₀) (v : Fin A.N) (β : DistFO (S.pal j) 1) : Prop :=
  if h : IsLocal β ∧ DRank 1 (S.q - 1) β then
    (dec S (j := j) ⟨β, h.1, h.2⟩).eval (rowAsn S ord k j A v)
  else True

/-- **The seam closes**: on a non-edgeless arena, the machine's
recursive clause IS `unrollAux (k+1)` — `frameEval`'s leaf guard is
discharged by the hypothesis and the rest is definitional. This is the
"must match `frameEval`'s recursive clause on the nose" fact: a pass
landing `RowEval`'s bits has landed the contract's table. -/
theorem unrollAux_succ_of_ne_bot (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) {k j : ℕ} {A : Arena (S.pal j) n₀}
    (hbot : ¬ A.G = ⊥) (v : Fin A.N) (β : DistFO (S.pal j) 1) :
    Unroll.unrollAux S ord (k + 1) j A v β = RowEval S ord k j A v β := by
  show Unroll.frameEval S ord j
      (fun B => Unroll.unrollAux S ord k (j + 1) B) A v β
    = RowEval S ord k j A v β
  simp only [Unroll.frameEval]
  rw [if_neg hbot]
  rfl

/-! ## §1b The compiled row: the code generator and its evaluation

The readback computes each row as one compiled boolean combination
over the child's data. `bcExprA` is `SolveMatTop.bcExpr`'s move with
the atoms fully abstract (the per-level combination has no compile-time
atoms: the local atoms are table reads, not sentence constants), and
`bcExprA_evalB` prices nothing and evaluates everything: given that
every atom's read expression delivers its bit, the compiled expression
delivers the combination's bit. `bcExprA_evalB_rowEval` instantiates it
at the row assignment: the compiled row delivers exactly `RowEval`'s
bit — the value `ReadRows` stores. The two membership lemmas place
every atom's data in the child's own table region: each local atom and
each scatter atom's `β`-formula is a column of `levelFml S (j+1)` —
`TableBitsW`'s index family in the child's `BlockPost`. -/

open Classical in
/-- **The code generator for an abstract-atom combination**: atoms are
the caller's read expressions, negation is `1 − ·`, conjunction is
multiplication on `{0,1}` — `bcExpr` with no compile-time atom kind. -/
noncomputable def bcExprA {α : Type*} (av : α → Expr) : BC α → Expr
  | .atom a => av a
  | .tru => .lit 1
  | .not b => .sub (.lit 1) (bcExprA av b)
  | .and b c => .mul (bcExprA av b) (bcExprA av c)

open Lax3Proofs.BCAlgebra in
open Classical in
/-- **The compiled combination evaluates to the truth bit**, by one
induction: given that every atom's read expression delivers its atom's
bit, the whole expression delivers the combination's — and every
intermediate value is `0` or `1`, so `1 < B` is the only bound ever
consumed. -/
theorem bcExprA_evalB {B : ℕ} (h1B : 1 < B) {σ : Env} {α : Type*}
    {v : α → Prop} {av : α → Expr} (b : BC α)
    (hav : ∀ a ∈ b.atoms, (av a).evalB B σ = some (if v a then 1 else 0)) :
    (bcExprA av b).evalB B σ = some (if b.eval v then 1 else 0) := by
  induction b with
  | atom a =>
    simp only [bcExprA]
    rw [hav a (by rw [atoms_atom]; exact List.mem_singleton_self _)]
    rfl
  | tru =>
    simp only [bcExprA]
    rw [evalB_lit h1B]
    exact congrArg some (if_pos trivial).symm
  | not b ih =>
    simp only [bcExprA]
    have hb := ih (fun a h => hav a h)
    have hev := evalB_bin (op := .sub) (e := Expr.lit 1) (f := bcExprA av b)
      (evalB_lit h1B) hb (by simp only [Bop.apply_sub]; split <;> omega)
    rw [Expr.sub_def, hev]
    simp only [Bop.apply_sub]
    by_cases h : BC.eval v b
    · rw [if_pos h, if_neg (fun hn => ((eval_not b).mp hn) h)]
    · rw [if_neg h, if_pos ((eval_not b).mpr h)]
  | and b c ihb ihc =>
    simp only [bcExprA]
    have hb := ihb
      (fun a h => hav a (by rw [atoms_and]; exact List.mem_append_left _ h))
    have hc := ihc
      (fun a h => hav a (by rw [atoms_and]; exact List.mem_append_right _ h))
    have hev := evalB_bin (op := .mul) (e := bcExprA av b) (f := bcExprA av c)
      hb hc (by simp only [Bop.apply_mul]; split <;> split <;> omega)
    rw [Expr.mul_def, hev]
    simp only [Bop.apply_mul]
    by_cases hbv : BC.eval v b <;> by_cases hcv : BC.eval v c <;>
      simp [eval_and b c, hbv, hcv]

open Classical in
/-- `RowEval` at a rank-checked formula is the decomposition's
evaluation at the row assignment — the `dif_pos` reduction, packaged. -/
theorem rowEval_eq_dec_eval (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (k j : ℕ) (A : Arena (S.pal j) n₀) (v : Fin A.N)
    {β : DistFO (S.pal j) 1} (h : IsLocal β ∧ DRank 1 (S.q - 1) β) :
    RowEval S ord k j A v β
      = (dec S (j := j) ⟨β, h.1, h.2⟩).eval (rowAsn S ord k j A v) := by
  simp only [RowEval]
  rw [dif_pos h]

open Classical in
/-- **The compiled row delivers `RowEval`'s bit**: given that every
atom of the row's decomposition reads its bit of the row assignment —
the local atoms off the child's table region, the scatter atoms off the
scatter counts — the compiled row expression evaluates to exactly the
bit `ReadRows` stores. -/
theorem bcExprA_evalB_rowEval {B : ℕ} (h1B : 1 < B) {σ : Env}
    (S : Setup L) (ord : CoverSpec.OrderingRoutine) (k j : ℕ)
    (A : Arena (S.pal j) n₀) (v : Fin A.N) {β : DistFO (S.pal j) 1}
    (h : IsLocal β ∧ DRank 1 (S.q - 1) β)
    {av : DistFO (S.pal (j + 1)) 1 ⊕ ScatterSentence (S.pal (j + 1)) → Expr}
    (hav : ∀ a ∈ (dec S (j := j) ⟨β, h.1, h.2⟩).atoms,
      (av a).evalB B σ = some (if rowAsn S ord k j A v a then 1 else 0)) :
    (bcExprA av (dec S (j := j) ⟨β, h.1, h.2⟩)).evalB B σ
      = some (if RowEval S ord k j A v β then 1 else 0) := by
  rw [rowEval_eq_dec_eval S ord k j A v h]
  exact bcExprA_evalB h1B _ hav

open Lax3Proofs.LocalityFun in
/-- **Every local atom of a schedule row's decomposition is a column of
the next level's family** — the child's `BlockPost` table
(`TableBitsW` over `levelFml S (j+1)`) carries its bit. -/
theorem localAtom_mem_levelFml {S : Setup L} {j : ℕ} {γ : Fml S j}
    (hγ : γ ∈ F S j) {ψ : DistFO (S.pal (j + 1)) 1}
    (hψ : Sum.inl ψ ∈ (dec S γ).atoms) : ψ ∈ levelFml S (j + 1) := by
  have hψ' : ψ ∈ localAtoms S.choice (stepFml S γ.fml)
      (drank_stepFml S γ.drank) := mem_localAtoms.mpr hψ
  have hspec := localAtoms_spec S.choice (stepFml S γ.fml)
    (drank_stepFml S γ.drank) ψ hψ'
  refine mem_levelFml.mpr ⟨⟨ψ, hspec.1, hspec.2⟩, ?_, rfl⟩
  show _ ∈ (F S j).flatMap (next S)
  refine List.mem_flatMap.mpr ⟨γ, hγ, ?_⟩
  unfold next
  exact List.mem_append_left _
    (List.mem_map.mpr ⟨⟨ψ, hψ'⟩, List.mem_attach _ _, rfl⟩)

open Lax3Proofs.LocalityFun in
/-- **Every scatter atom's `β`-formula of a schedule row's
decomposition is a column of the next level's family** — the scatter
pass's batch sets are readable off the child's `BlockPost` table. -/
theorem scatterAtom_beta_mem_levelFml {S : Setup L} {j : ℕ} {γ : Fml S j}
    (hγ : γ ∈ F S j) {σa : ScatterSentence (S.pal (j + 1))}
    (hσ : Sum.inr σa ∈ (dec S γ).atoms) : σa.β ∈ levelFml S (j + 1) := by
  have hσ' : σa ∈ scatterAtoms S.choice (stepFml S γ.fml)
      (drank_stepFml S γ.drank) := mem_scatterAtoms.mpr hσ
  have hspec := scatterAtoms_spec S.choice (stepFml S γ.fml)
    (drank_stepFml S γ.drank) σa hσ'
  refine mem_levelFml.mpr
    ⟨⟨σa.β, Lax3Proofs.ScatterFml.isLocal_beta_of_drank hspec,
      drank_beta_node hspec⟩, ?_, rfl⟩
  show _ ∈ (F S j).flatMap (next S)
  refine List.mem_flatMap.mpr ⟨γ, hγ, ?_⟩
  unfold next
  exact List.mem_append_right _
    (List.mem_map.mpr ⟨⟨σa, hσ'⟩, List.mem_attach _ _, rfl⟩)

/-! ## §2 The write-once step of the partial table -/

open Classical in
/-- **The partial table steps by one centre**: if the rows of every
vertex with centre below `u` kept their cells and the rows of every
centre-`u` vertex newly hold the target bits, the table is partial at
`u + 1`. The write-once discipline of the readback, as one lemma. -/
theorem tablePartial_succ {a : String} {N Λ : ℕ} {Fl : List (DistFO Λ 1)}
    {T : Fin N → DistFO Λ 1 → Prop} {ctrF : Fin N → Fin N} {u : ℕ}
    {σ σ' : Env}
    (hold : TablePartial a Fl T (fun v => (ctrF v : ℕ) < u) σ)
    (hkeep : ∀ v : Fin N, (ctrF v : ℕ) < u → ∀ i, i < Fl.length →
      (σ'.arrs a).getD ((v : ℕ) * Fl.length + i) 0
        = (σ.arrs a).getD ((v : ℕ) * Fl.length + i) 0)
    (hnew : ∀ v : Fin N, (ctrF v : ℕ) = u → ∀ (i : ℕ),
      ∀ hi : i < Fl.length,
      (σ'.arrs a).getD ((v : ℕ) * Fl.length + i) 0
        = if T v Fl[i] then 1 else 0) :
    TablePartial a Fl T (fun v => (ctrF v : ℕ) < u + 1) σ' := by
  intro v hv i hi
  rcases Nat.lt_or_ge (ctrF v : ℕ) u with h | h
  · rw [hkeep v h i hi]
    exact hold v h i hi
  · exact hnew v (by omega) i hi

/-! ## §3 The named residual: the scatter-and-readback machine pass -/

open Classical in
/-- **The scatter-and-readback machine pass** (named residual): from
the loop invariant at centre `u` (counter at `u`) plus the inner
block's postcondition at the child — the child regions intact, the
child table at fuel `k` — the pass runs the per-atom scatters on the
isolated child graph and writes **exactly the centre-`u` rows** of the
level table at the recursive clause's bits (`RowEval` — the compiled
combination per schedule row over the child's tables and scatter
counts); every other row's cells, the level's cells (the counter and
the two arena cells), the cover's three arrays and the five non-table
regions are untouched, and no array is reallocated. -/
def ReadRows (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (readC : ℕ → Com)
    (KR : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ) : Prop :=
  ∀ (k j : ℕ) (A : Arena (S.pal j) n₀), j + (k + 1) = S.depth →
    Adm j A → ¬ A.G = ⊥ → ∀ u : Fin A.N,
    Spec B
      (fun σ => CLInv S ord ℓp htabF hbf Scr ca co cm k j A (u : ℕ) σ ∧
        σ.vars (ctrName j) = (u : ℕ) ∧
        BlockPost S ord k (j + 1) (hbf (j + 1))
          (childArena S A ((ord A.N A.G).order) u)
          (htabF (j + 1) (childArena S A ((ord A.N A.G).order) u))
          (arenaNames (j + 1)) σ)
      (readC j)
      (fun σ σ' =>
        -- the centre's rows, at the recursive clause's bits
        (∀ v : Fin A.N, centre S A ((ord A.N A.G).order) v = u →
          ∀ (i : ℕ), ∀ hi : i < (levelFml S j).length,
          (σ'.arrs (arenaNames j).tab).getD
              ((v : ℕ) * (levelFml S j).length + i) 0
            = if RowEval S ord k j A v (levelFml S j)[i] then 1 else 0) ∧
        -- every other row's cells, untouched
        (∀ v : Fin A.N, ¬ centre S A ((ord A.N A.G).order) v = u →
          ∀ i, i < (levelFml S j).length →
          (σ'.arrs (arenaNames j).tab).getD
              ((v : ℕ) * (levelFml S j).length + i) 0
            = (σ.arrs (arenaNames j).tab).getD
              ((v : ℕ) * (levelFml S j).length + i) 0) ∧
        -- the level's cells, untouched
        (∀ y ∈ ctrName j :: levelScalars j, σ'.vars y = σ.vars y) ∧
        -- the cover's three arrays and the five non-table regions,
        -- untouched
        (∀ a ∈ ([ca j, co j, cm j, (arenaNames j).off, (arenaNames j).tgt,
          (arenaNames j).col, (arenaNames j).up, (arenaNames j).hist] :
            List String), σ'.arrs a = σ.arrs a) ∧
        -- no reallocation
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (KR k j A (u : ℕ))

/-! ## §4 `CentreRead`, from the machine pass -/

open Classical in
/-- **`CentreRead` from the scatter-and-readback pass**: the return
path's invariant seam discharged. The windowed contract, the assignment
region, the cluster CSR and the table allocation cross the pass by its
frame clauses; the partial table steps to `u + 1` by
`tablePartial_succ`, its new rows converted from `RowEval` to
`unrollAux (k+1)` by `unrollAux_succ_of_ne_bot` (the arena has an edge
— the contract's own hypothesis); the counter clause is the frame's;
`Scr` crosses by its length-only transport. -/
theorem centreRead_of_rows (B : ℕ) (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena (S.pal j) n₀ → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (readC : ℕ → Com)
    (KR : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ → ℕ)
    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    (hrows : ReadRows B S ord ℓp htabF hbf Adm Scr ca co cm readC KR) :
    CentreRead B S ord ℓp htabF hbf Adm Scr ca co cm readC KR := by
  intro k j A hdiag hAdm hbot u
  refine (hrows k j A hdiag hAdm hbot u).post ?_
  rintro σ σ' ⟨hCL, -, -⟩ ⟨hnew, hkeep, hvars, harrs, hlen⟩
  obtain ⟨⟨hA, htab, hscr⟩, hctrA, hcsr, hpart⟩ := hCL
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩, hvars _ (by simp)⟩
  · -- the windowed contract, off the frame clauses
    exact arenaStW_of_eq hA (hvars _ (by simp [levelScalars]))
      (hvars _ (by simp [levelScalars])) (harrs _ (by simp))
      (harrs _ (by simp)) (harrs _ (by simp)) (harrs _ (by simp))
      (harrs _ (by simp))
  · -- the table allocation's length, preserved
    rw [hlen]
    exact htab
  · -- the scratch descriptor, transported
    exact hscrLen j σ σ' hscr hlen
  · -- the assignment region, untouched
    exact ctrArr_of_eq hctrA (harrs _ (by simp))
  · -- the cluster CSR, untouched
    exact clusterCsr_of_eq hcsr (harrs _ (by simp)) (harrs _ (by simp))
  · -- the partial table, stepped to `u + 1`
    refine tablePartial_succ hpart ?_ ?_
    · -- the old rows: their centres are not `u`, so their cells kept
      intro v hv i hi
      refine hkeep v (fun heq => ?_) i hi
      rw [heq] at hv
      exact absurd hv (lt_irrefl _)
    · -- the new rows: the recursive clause's bits are the contract's
      intro v hv i hi
      rw [unrollAux_succ_of_ne_bot S ord hbot v _]
      exact hnew v (Fin.ext hv) i hi

/-! ## §5 The headline: `CentreReadAll` from the pass -/

/-- The scatter-and-readback pass, quantified per admissible input. -/
def ReadRowsAll (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (readC : ℕ → Com)
    (KR : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ → ℕ) : Prop :=
  ∀ x ∈ mcD n G c w,
    ReadRows (mcB q x) (Headline.headlineSetup C hC φ) ord ℓp htabF hbf
      Adm Scr ca co cm readC KR

open Classical in
/-- **Verbatim `CentreReadAll`, from the scatter-and-readback pass** —
the read segment's residual, reduced to the machine pass plus the
length-only scratch transport. -/
theorem centreReadAll_of_rows (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (Scr : ℕ → Env → Prop) (ca co cm : ℕ → String) (readC : ℕ → Com)
    (KR : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ → ℕ)
    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    (hrows : ReadRowsAll C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm
      readC KR) :
    CentreReadAll C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm readC
      KR := by
  intro x hx
  exact centreRead_of_rows (mcB q x) (Headline.headlineSetup C hC φ) ord ℓp
    htabF hbf Adm Scr ca co cm readC KR hscrLen (hrows x hx)

/-! ## §6 End to end: the per-centre step from the two machine passes -/

open Classical in
/-- **`CentreStepAll` from the two named machine passes**, wired end to
end through `SolveStep`: verbatim, at the canonical body
`centreBody prepC readC` and budget `centreKC`, from `ChildLoadAll`
(the child construction's machine pass) and `ReadRowsAll` (the
scatter-and-readback machine pass) plus hypotheses only of the
F7-suppliable kinds `SolveStep` already takes — the descriptor tower's
length facts, the `lv` freshness facts, the run tree's two facts at the
child, and the segments' write discipline. -/
theorem centreStepAll_of_childLoad_rows (C : GraphClass)
    (hC : NowhereDense C) (φ : FO 0) (ord : CoverSpec.OrderingRoutine)
    {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (KB : (k j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (Scr : ℕ → Env → Prop) (LS LA : ℕ → List String)
    (ca co cm : ℕ → String) (prepC readC : ℕ → Com)
    (KP KR : (k j : ℕ) →
      Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ → ℕ)
    (hscrLen : ∀ j σ σ', Scr j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → Scr j σ')
    (hscrDown : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth →
      ∀ σ, Scr j σ → Scr (j + 1) σ)
    (htabLen : ∀ j, j + 1 ≤ (Headline.headlineSetup C hC φ).depth → ∀ σ,
      Scr j σ →
      n * (levelFml (Headline.headlineSetup C hC φ) (j + 1)).length
        ≤ (σ.arrs (arenaNames (j + 1)).tab).length)
    (hfreshS : ∀ j i, j < i → ∀ y ∈ ctrName j :: levelScalars j, y ∉ LS i)
    (hfreshA : ∀ j i, j < i →
      ∀ a ∈ ca j :: co j :: cm j :: levelArrays j, a ∉ LA i)
    (hAdmChild : ∀ (j : ℕ)
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n), Adm j A →
      ¬ A.G = ⊥ → ∀ u : Fin A.N,
      Adm (j + 1) (childArena (Headline.headlineSetup C hC φ) A
        ((ord A.N A.G).order) u))
    (hleafChild : ∀ (j : ℕ)
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n), Adm j A →
      ¬ A.G = ⊥ → j + 1 = (Headline.headlineSetup C hC φ).depth →
      ∀ u : Fin A.N,
      (childArena (Headline.headlineSetup C hC φ) A
        ((ord A.N A.G).order) u).G = ⊥)
    (hprepOwn : ∀ j, OwnedFrom LS LA j (prepC j))
    (hreadOwn : ∀ j, OwnedFrom LS LA j (readC j))
    (hload : ChildLoadAll C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm
      prepC KP)
    (hrows : ReadRowsAll C hC φ ord G c w q ℓp htabF hbf Adm Scr ca co cm
      readC KR) :
    CentreStepAll C hC φ ord G c w q ℓp htabF hbf Adm KB Scr LS LA
      ca co cm (centreBody prepC readC)
      (centreKC (Headline.headlineSetup C hC φ) ord KB KP KR) :=
  centreStepAll_of_prep_read C hC φ ord G c w q ℓp htabF hbf Adm KB Scr
    LS LA ca co cm prepC readC KP KR hscrLen hfreshS hfreshA hAdmChild
    hleafChild hprepOwn hreadOwn
    (centrePrepAll_of_childLoad C hC φ ord G c w q ℓp htabF hbf Adm Scr
      ca co cm prepC KP hscrLen hscrDown htabLen hload)
    (centreReadAll_of_rows C hC φ ord G c w q ℓp htabF hbf Adm Scr
      ca co cm readC KR hscrLen hrows)

end Lax3Proofs.Prog
