import Lax185574.MergeToConstruction
import Lax185574Proofs.FormulaRank
import Lax185574Proofs.WithinDistBasics
import Lax185574Proofs.Legacy

/-!
The construction sequence of cl:from-merge-to-construction, as an explicit
function of the graph and the merge sequence.

Write the merge sequence as (𝒫₀, R₀), …, (𝒫_{m−1}, R_{m−1}), counted from
0, and put 𝒫_m = {V} and R_m = all pairs. The colors of a partition are
the least vertices of its parts. The initial partial graph gives vertex
v the color v. Stage j, for j < m, starts with the coloring of 𝒫_j and
does the following.

1. For every pair of parts X, Y of 𝒫_j, with least vertices a ≤ b, such
   that XY ⊆ R_{j+1} and some pair of XY was not resolved at the start of
   the stage, resolve X with Y: positively if some pair of XY unresolved
   at the start of the stage is an edge of G, and negatively otherwise.
   The pairs (a, b) are taken in lexicographic order.
2. For every vertex v that is least in its part of 𝒫_j but not in its
   part of 𝒫_{j+1}, in increasing order, merge the color of v into the
   color of the least vertex of its part of 𝒫_{j+1}.

After stage j the coloring is that of 𝒫_{j+1}. The pairs resolved at the
start of stage j are those of the blocks D_i, i < j, where D_i is the
union of all rectangles XY of parts of 𝒫_i with XY ⊆ R_{i+1}.
-/

namespace Lax185574Proofs.Conversions.MergeConstruction

open Lax185574.PartialGraphs Lax185574.ConstructionSequences Lax185574.SequenceEncoding
open Lax185574.MergeSequences Lax185574.Partitions Lax185574.GraphBalls

open Classical

noncomputable section

variable {n : ℕ}

/-! ### Least vertices of parts -/

/-- The least vertex of the part of `x`. -/
def rep (P : Setoid (Fin n)) (x : Fin n) : Fin n :=
  (Finset.univ.filter fun u => P u x).min' ⟨x, by simp⟩

theorem rep_rel (P : Setoid (Fin n)) (x : Fin n) : P (rep P x) x := by
  unfold rep
  exact (Finset.mem_filter.1 (Finset.min'_mem (Finset.univ.filter fun u => P u x) _)).2

theorem rep_le (P : Setoid (Fin n)) {u x : Fin n} (h : P u x) : rep P x ≤ u :=
  Finset.min'_le _ _ (by simp [h])

theorem rep_eq_of_rel (P : Setoid (Fin n)) {x y : Fin n} (h : P x y) : rep P x = rep P y := by
  apply le_antisymm
  · exact rep_le P (P.trans (rep_rel P y) (P.symm h))
  · exact rep_le P (P.trans (rep_rel P x) h)

theorem rep_eq_iff (P : Setoid (Fin n)) (x y : Fin n) : rep P x = rep P y ↔ P x y := by
  refine ⟨fun h => ?_, rep_eq_of_rel P⟩
  have h1 := rep_rel P x
  have h2 := rep_rel P y
  rw [h] at h1
  exact P.trans (P.symm h1) h2

theorem rep_rep (P : Setoid (Fin n)) (x : Fin n) : rep P (rep P x) = rep P x :=
  rep_eq_of_rel P (rep_rel P x)

theorem rep_rep_of_le {P Q : Setoid (Fin n)} (h : P ≤ Q) (x : Fin n) :
    rep Q (rep P x) = rep Q x :=
  rep_eq_of_rel Q (h (rep_rel P x))

/-- A vertex least in its part of a coarser partition is least in its
part of a finer one. -/
theorem rep_self_of_le {P Q : Setoid (Fin n)} (h : P ≤ Q) {v : Fin n} (hv : rep Q v = v) :
    rep P v = v :=
  le_antisymm (rep_le P (P.refl v)) (by
    calc v = rep Q v := hv.symm
      _ ≤ rep P v := rep_le Q (h (rep_rel P v)))

theorem rep_bot (x : Fin n) : rep ⊥ x = x := by
  have := rep_rel (⊥ : Setoid (Fin n)) x
  rw [Setoid.bot_def] at this
  exact this

/-! ### The stages -/

variable (G : SimpleGraph (Fin n)) (ms : List (Setoid (Fin n) × SimpleGraph (Fin n)))

/-- The partition `𝒫_j`, and `{V}` from `j = m` on. -/
def part (j : ℕ) : Setoid (Fin n) := if h : j < ms.length then ms[j].1 else ⊤

/-- The relation `R_j`, and all pairs from `j = m` on. -/
def rel (j : ℕ) : SimpleGraph (Fin n) := if h : j < ms.length then ms[j].2 else ⊤

/-- The coloring of `𝒫_j`: the least vertex of the part. -/
def col (j : ℕ) (x : Fin n) : ℕ := (rep (part ms j) x : ℕ)

/-- The rectangle `XY` of the parts with least vertices `a` and `b` of
`𝒫_j`: the pairs of distinct vertices with one end in each. -/
def rect (j a b : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun x y => col ms j x = a ∧ col ms j y = b

/-- The block `D_j`: the union of the rectangles `XY` of parts of `𝒫_j`
with `XY ⊆ R_{j+1}`. -/
def block (j : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun x y =>
    ∀ a b, part ms j a x → part ms j b y → a ≠ b → (rel ms (j + 1)).Adj a b

/-- The pairs resolved at the start of stage `j`: the union of the
blocks `D_i` for `i < j`. -/
def resolvedAt (j : ℕ) : SimpleGraph (Fin n) :=
  SimpleGraph.fromRel fun x y => ∃ i < j, (block ms i).Adj x y

/-- Stage `j` resolves the parts with least vertices `a ≤ b` of `𝒫_j`:
their rectangle lies in `R_{j+1}` and was not resolved at the start of
the stage. -/
def Resolves (j : ℕ) (p : Fin n × Fin n) : Prop :=
  p.1 ≤ p.2 ∧ rep (part ms j) p.1 = p.1 ∧ rep (part ms j) p.2 = p.2 ∧
    rect ms j p.1 p.2 ≤ rel ms (j + 1) ∧ ¬ rect ms j p.1 p.2 ≤ resolvedAt ms j

/-- The sign of the resolve: positive if some pair of the rectangle that
is unresolved at the start of the stage is an edge. -/
def Positive (j : ℕ) (p : Fin n × Fin n) : Prop :=
  ∃ x y, (rect ms j p.1 p.2).Adj x y ∧ ¬ (resolvedAt ms j).Adj x y ∧ G.Adj x y

/-- The resolve step for the parts with least vertices `p`. -/
def resolveStep (j : ℕ) (p : Fin n × Fin n) : Step :=
  if Positive G ms j p then .resolvePos p.1 p.2 else .resolveNeg p.1 p.2

/-- The pairs of least vertices resolved in stage `j`, in lexicographic
order. -/
def resolvePairs (j : ℕ) : List (Fin n × Fin n) :=
  ((List.finRange n).flatMap fun a => (List.finRange n).map fun b => (a, b)).filter
    fun p => decide (Resolves ms j p)

/-- A vertex least in its part of `𝒫_j` but not of `𝒫_{j+1}`. -/
def IsSource (j : ℕ) (v : Fin n) : Prop :=
  rep (part ms j) v = v ∧ rep (part ms (j + 1)) v ≠ v

/-- The vertices whose parts are merged away in stage `j`, in increasing
order. -/
def mergeSources (j : ℕ) : List (Fin n) :=
  (List.finRange n).filter fun v => decide (IsSource ms j v)

/-- The merge step for the source `v`. -/
def mergeStep (j : ℕ) (v : Fin n) : Step :=
  .merge (rep (part ms (j + 1)) v : ℕ) (v : ℕ)

/-- The steps of stage `j`: the resolves, then the merges. -/
def stageSteps (j : ℕ) : List Step :=
  (resolvePairs ms j).map (resolveStep G ms j) ++ (mergeSources ms j).map (mergeStep ms j)

/-- **The construction script of cl:from-merge-to-construction.** -/
def script : Script n where
  colors := fun v => (v : ℕ)
  steps := (List.range ms.length).flatMap (stageSteps G ms)

end

end Lax185574Proofs.Conversions.MergeConstruction
