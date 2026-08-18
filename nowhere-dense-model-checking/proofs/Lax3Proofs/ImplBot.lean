import Lax3Proofs.BotEval
import Lax3Proofs.DriverArena

/-!
# `BotTables` — the finite row evaluator at the leaf (E12, §6.4)

`algorithm-v2.md` §6.4: in an edgeless arena every distance is `0` or
`∞`, so a formula sees only the *rows* of the environment's entries —
which colors each carries — and their equalities. `Lax3Proofs.BotEval`
proves the collapse lemmas; this file assembles them into the evaluator
the machine runs, and proves it computes `Sat ⊥` — which is exactly what
`Driver.tablesAux` returns at its leaf (fuel `0`, or an edgeless arena).

## The evaluator

`botEval colB m φ` is a `Bool`-valued structural recursion over the
formula, against the machine's color rows `colB : Fin N → Fin L → Bool`
(§4's `col` field, bridged to the abstract `Coloring` by the hypothesis
`hcol`). Every clause is finite:

* the five atoms are row lookups and equality tests (`sat_adj_bot`,
  `sat_eq_bot`, `sat_color_bot`, `sat_distLe_bot`,
  `sat_distColorLt_bot`);
* a local quantifier is a disjunction over its guard set
  (`sat_exL_bot`) — no search at all;
* an unrestricted quantifier searches `candidates colB m`: the `k`
  environment entries plus `reps colB m`, the *first off-environment
  representative of each realized row* — sound by
  `sat_exU_bot_of_repr`, whose representative-system hypothesis
  `reps_spec` discharges by a `Finset.min'` argument.

## The charge (§4: `O(‖A‖)`; §6.4's `k + 2^L` witness bound)

The witness search is over at most `k + 2^L` candidates however large
the arena — `length_candidates_le`, the computable counterpart of
`BotEval.ncard_le_of_injOn_rowOf`. `k`, `L` and the formula are
schedule data, constant in `n`; the machine builds the representative
table in one row scan and then evaluates each of the `N` table entries
in constant time, which is §4's `O(‖A‖)` charge for the whole table.
(The Lean spelling of `reps` re-scans `Fin n` per quantifier because it
is a *definition of the candidate set*, not the program's schedule of
row scans; the charge statement is the candidate bound.)

## Headline

* `botEval_eq_sat` — the evaluator IS satisfaction on the edgeless
  arena: `botEval colB m φ = true ↔ Sat ⊥ col m φ`.
* `tablesAux_bot_eq_botEval` — the identity to the abstract driver:
  at an edgeless arena the leaf `Driver.tablesAux` returns, at every
  fuel, is decided by `botEval` over the arena's rows.
-/

namespace Lax3Proofs.Impl

open Lax3.ColoredGraphs Lax3.DistFO
open Lax3Proofs.SyntaxLemmas Lax3Proofs.BotEval

variable {L n : ℕ}

/-! ### The representative system, computably -/

/-- `v` is the first off-environment representative of its row: it lies
off the environment's range, and every earlier vertex with the same row
lies on it. One per realized row (`reps_row_injOn`), and every
off-environment vertex has one with its row (`reps_spec`). -/
def FirstRep (colB : Fin n → Fin L → Bool) {k : ℕ} (m : Fin k → Fin n)
    (v : Fin n) : Prop :=
  (¬ ∃ i, m i = v) ∧ ∀ u, u < v → (∀ c, colB u c = colB v c) → ∃ i, m i = u

instance (colB : Fin n → Fin L → Bool) {k : ℕ} (m : Fin k → Fin n) :
    DecidablePred (FirstRep colB m) := fun _ => by
  unfold FirstRep; infer_instance

/-- The representative list: the first off-environment member of each
row realized off the environment. -/
def reps (colB : Fin n → Fin L → Bool) {k : ℕ} (m : Fin k → Fin n) : List (Fin n) :=
  (List.finRange n).filter fun v => decide (FirstRep colB m v)

/-- The candidate list of an unrestricted quantifier: the environment's
entries, then the representatives. -/
def candidates (colB : Fin n → Fin L → Bool) {k : ℕ} (m : Fin k → Fin n) :
    List (Fin n) :=
  List.ofFn m ++ reps colB m

theorem mem_reps_iff (colB : Fin n → Fin L → Bool) {k : ℕ} {m : Fin k → Fin n}
    {v : Fin n} : v ∈ reps colB m ↔ FirstRep colB m v := by
  simp [reps, List.mem_filter, List.mem_finRange]

/-- **The representative-system property** — the hypothesis of
`BotEval.sat_exU_bot_of_repr`, discharged for `reps`: every vertex off
the environment has a same-row representative off the environment. The
representative is the `Finset.min'` of the vertex's off-environment row
class. -/
theorem reps_spec (colB : Fin n → Fin L → Bool) {col : Coloring n L}
    (hcol : ∀ v c, colB v c = true ↔ v ∈ col c) {k : ℕ} (m : Fin k → Fin n) :
    ∀ v ∉ Set.range m, ∃ w ∈ {w | w ∈ reps colB m}, w ∉ Set.range m ∧
      ∀ c : Fin L, v ∈ col c ↔ w ∈ col c := by
  intro v hv
  classical
  -- the off-environment row class of `v`, as a `Finset`
  set F : Finset (Fin n) :=
    Finset.univ.filter (fun u => (∀ c, colB u c = colB v c) ∧ ¬ ∃ i, m i = u) with hF
  have hvF : v ∈ F := by
    rw [hF, Finset.mem_filter]
    exact ⟨Finset.mem_univ v, fun _ => rfl, by simpa [Set.mem_range] using hv⟩
  have hne : F.Nonempty := ⟨v, hvF⟩
  set w := F.min' hne with hw
  have hmem : w ∈ F := F.min'_mem hne
  rw [hF, Finset.mem_filter] at hmem
  obtain ⟨-, hrow, hwoff⟩ := hmem
  refine ⟨w, ?_, by simpa [Set.mem_range] using hwoff, fun c => ?_⟩
  · -- `w` is the first off-environment member of its row
    show w ∈ reps colB m
    rw [mem_reps_iff]
    refine ⟨hwoff, fun u hu hurow => ?_⟩
    by_contra huoff
    have huF : u ∈ F := by
      rw [hF, Finset.mem_filter]
      exact ⟨Finset.mem_univ u, fun c => (hurow c).trans (hrow c), huoff⟩
    have hle : w ≤ u := F.min'_le u huF
    exact absurd hle (not_le.mpr hu)
  · rw [← hcol, ← hcol, hrow c]

/-! ### The witness bound (§6.4: `k + 2 ^ L` candidates) -/

/-- Two representatives with equal rows coincide: the earlier one would
witness the later one's "every earlier same-row vertex is on the
environment" clause against its own off-environment clause. -/
theorem reps_row_injOn (colB : Fin n → Fin L → Bool) {k : ℕ} (m : Fin k → Fin n) :
    ∀ u ∈ reps colB m, ∀ w ∈ reps colB m,
      (fun c => colB u c) = (fun c => colB w c) → u = w := by
  intro u hu w hw hrow
  have hrow' : ∀ c, colB u c = colB w c := fun c => congrFun hrow c
  rcases lt_trichotomy u w with h | h | h
  · exact absurd (((mem_reps_iff colB).mp hw).2 u h hrow')
      ((mem_reps_iff colB).mp hu).1
  · exact h
  · exact absurd (((mem_reps_iff colB).mp hu).2 w h (fun c => (hrow' c).symm))
      ((mem_reps_iff colB).mp hw).1

/-- There are at most `2 ^ L` representatives: their rows are distinct
functions `Fin L → Bool`. -/
theorem length_reps_le (colB : Fin n → Fin L → Bool) {k : ℕ} (m : Fin k → Fin n) :
    (reps colB m).length ≤ 2 ^ L := by
  classical
  have hnd : (reps colB m).Nodup := (List.nodup_finRange n).filter _
  have hmap : ((reps colB m).map (fun v => fun c => colB v c)).Nodup :=
    hnd.map_on fun u hu w hw h => reps_row_injOn colB m u hu w hw h
  calc (reps colB m).length
      = ((reps colB m).map (fun v => fun c => colB v c)).length :=
        (List.length_map ..).symm
    _ ≤ Fintype.card (Fin L → Bool) := hmap.length_le_card
    _ = 2 ^ L := by simp

/-- **§6.4's witness bound**: the search of an unrestricted quantifier
runs over at most `k + 2 ^ L` candidates, however large the arena. -/
theorem length_candidates_le (colB : Fin n → Fin L → Bool) {k : ℕ}
    (m : Fin k → Fin n) : (candidates colB m).length ≤ k + 2 ^ L := by
  rw [candidates, List.length_append, List.length_ofFn]
  exact Nat.add_le_add_left (length_reps_le colB m) k

/-! ### The evaluator -/

/-- **`BotTables`'s row evaluator** (§6.4): satisfaction on an edgeless
arena, computed from the machine's color rows. Atoms are row lookups and
equality tests, a local quantifier is a disjunction over its guard set,
an unrestricted one searches the `≤ k + 2 ^ L` candidates. -/
def botEval (colB : Fin n → Fin L → Bool) : {k : ℕ} → (Fin k → Fin n) →
    DistFO L k → Bool
  | _, _, .adj _ _ => false
  | _, m, .eq i j => decide (m i = m j)
  | _, m, .color c i => colB (m i) c
  | _, m, .distLe _ i j => decide (m i = m j)
  | _, m, .distColorLt r c i => decide (0 < r) && colB (m i) c
  | _, m, .not φ => ! botEval colB m φ
  | _, m, .and φ ψ => botEval colB m φ && botEval colB m ψ
  | _, m, .exU φ => (candidates colB m).any fun w => botEval colB (Fin.snoc m w) φ
  | _, m, .exL _ g φ => decide (∃ i ∈ g, botEval colB (Fin.snoc m (m i)) φ = true)

/-- **The evaluator computes `Sat ⊥`** — the §6.4 identity: against rows
`colB` matching the coloring (`hcol`), `botEval` decides satisfaction on
the edgeless arena, clause by clause through `BotEval`'s collapse
lemmas, with `sat_exU_bot_of_repr` at the unrestricted quantifier. -/
theorem botEval_eq_sat (colB : Fin n → Fin L → Bool) (col : Coloring n L)
    (hcol : ∀ v c, colB v c = true ↔ v ∈ col c) :
    ∀ {k : ℕ} (φ : DistFO L k) (m : Fin k → Fin n),
      botEval colB m φ = true ↔ Sat (⊥ : SimpleGraph (Fin n)) col m φ := by
  intro k φ
  induction φ with
  | adj i j => intro m; simp [botEval, sat_adj_bot]
  | eq i j => intro m; simp [botEval, sat_eq_bot]
  | color c i => intro m; simp [botEval, sat_color_bot, hcol]
  | distLe r i j => intro m; simp [botEval, sat_distLe_bot]
  | distColorLt r c i => intro m; simp [botEval, sat_distColorLt_bot, hcol]
  | not φ ih => intro m; simp [botEval, sat_not, ← ih m]
  | and φ ψ ih₁ ih₂ => intro m; simp [botEval, sat_and, ih₁, ih₂]
  | exU φ ih =>
      intro m
      rw [show botEval colB m (.exU φ)
          = (candidates colB m).any (fun w => botEval colB (Fin.snoc m w) φ) from rfl,
        List.any_eq_true]
      constructor
      · rintro ⟨w, -, hw⟩
        exact (sat_exU φ).mpr ⟨w, (ih (Fin.snoc m w)).mp hw⟩
      · intro hsat
        rcases (sat_exU_bot_of_repr φ {w | w ∈ reps colB m}
            (reps_spec colB hcol m)).mp hsat with ⟨i, hi⟩ | ⟨w, hwW, -, hw⟩
        · exact ⟨m i, List.mem_append.mpr (Or.inl (List.mem_ofFn.mpr ⟨i, rfl⟩)),
            (ih (Fin.snoc m (m i))).mpr hi⟩
        · exact ⟨w, List.mem_append.mpr (Or.inr hwW), (ih (Fin.snoc m w)).mpr hw⟩
  | exL r g φ ih =>
      intro m
      simp only [botEval, decide_eq_true_eq, sat_exL_bot]
      constructor
      · rintro ⟨i, hi, h⟩
        exact ⟨i, hi, (ih (Fin.snoc m (m i))).mp h⟩
      · rintro ⟨i, hi, h⟩
        exact ⟨i, hi, (ih (Fin.snoc m (m i))).mpr h⟩

/-! ### The identity to the driver's leaf -/

open Lax3Proofs.Driver in
/-- **What `Driver.tablesAux` returns at its leaf is what `botEval`
computes.** On an edgeless arena — every leaf of the recursion, whether
reached through the fuel-`0` clause or the edgeless branch — the
abstract driver's table entry at `(v, β)` is decided by the row
evaluator over the arena's color rows, at every fuel. -/
theorem tablesAux_bot_eq_botEval {n₀ : ℕ} (S : Setup L)
    (ord : Lax3Proofs.CoverSpec.OrderingRoutine) (fuel j : ℕ)
    (A : Arena (S.pal j) n₀) (hbot : A.G = ⊥)
    (colB : Fin A.N → Fin (S.pal j) → Bool)
    (hcol : ∀ v c, colB v c = true ↔ v ∈ A.col c)
    (v : Fin A.N) (β : DistFO (S.pal j) 1) :
    tablesAux S ord fuel j A v β ↔ botEval colB (fun _ => v) β = true := by
  have hleaf : tablesAux S ord fuel j A v β = Sat A.G A.col (fun _ => v) β := by
    cases fuel with
    | zero => rfl
    | succ fuel => rw [tablesAux, if_pos hbot]
  rw [hleaf, hbot]
  exact (botEval_eq_sat colB A.col hcol β (fun _ => v)).symm

end Lax3Proofs.Impl
