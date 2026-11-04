import Lax185574Proofs.RamSwitch
import Lax185574Proofs.LoopGlue
import Lax185574Proofs.MC.Localize
import Lax185574Proofs.Words.Computes
import Lax185574.ConstructionModelChecking
import Lax185574.ResolveLift
import Lax185574.Evaluation
import Lax185574.MergeLift
import Lax185574Proofs.Words.SelectLen
import Lax185574Proofs.LegacyInputs

/-!
Interfaces of the assembly of thm:mc.

The program is `par P₀ P₁`, two threads run in parallel at the same
word length. Thread `P₀` is the pipeline, the loop driver alternating a
glue program `G` with the callee `switch ML RL Ev D`. Thread `P₁` is a
brute-force evaluator. This file fixes what the assembly needs of the
three programs that are built separately:

* `Par2Spec`: the parallel combinator. Both threads run at word length
  `w - K`, every halting run of the combinator outputs the answer of a
  thread that halted with `1 :: y`, and the combinator halts within
  `K (t + 1)` steps if one thread halts with `1 :: y` in `t` steps.
* `BruteSpec`: the brute-force evaluator, sound at every admissible word
  length with an exponent fixed before the sentence, and fast in the
  number of vertices.
* `GlueAt`: the rounds of the glue program along the calls `pcalls` of
  the algorithm, which are defined here.

The calls follow the proof of thm:mc. For every step `t` of the script,
a merge `merge_{P,Q}` with `P ≠ Q` gives one call that runs the merge
lift on the trees of all vertices (a list of jobs, one per vertex), a
merge `merge_{P,P}` gives one call with the fixed empty list of jobs, a
resolve gives one call of the resolve lift on the partial graph, its
distance matrix and the family of trees, and at the end one call of the
evaluation on the tree of vertex `0` and the localization of the
sentence. So every step has exactly one call. The other two callees get
fixed small queries.
-/

namespace Lax185574Proofs.MC

open Lax185574Proofs.RamSim
open Lax808846.Ram Lax185574Proofs.Simulate Lax185574Proofs.Words Lax185574Proofs.RamSim
open Lax271696.GraphEncoding Lax185574.WordEncoding Lax185574.SequenceEncoding
open Lax185574.PartialGraphs Lax185574.ConstructionSequences Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574.DistanceMatrix
open Lax185574.ConstructionModelChecking

/-! ### The answer and the two outer interfaces -/

open Classical in
/-- The answer word of thm:mc. -/
noncomputable def mcAns {n : ℕ} (G : SimpleGraph (Fin n)) (φ : Lax3.FirstOrder.FO 0) : List ℕ :=
  if Lax3.FirstOrder.Sat G Fin.elim0 φ then [1] else [0]

/-- **Two threads in parallel.** -/
def Par2Spec (par : Program → Program → Program) (K : ℕ) : Prop :=
  ∀ (P₀ P₁ : Program) (w : ℕ) (x : List ℕ), K < w → x.length < 2 ^ (w - K) →
    (∀ (b : Bool) (y : List ℕ) (t : ℕ), RunsTo (w - K) (cond b P₁ P₀) x (1 :: y) t →
      y.length ≤ 1 → ∃ T ≤ K * (t + 1), ∃ y', RunsTo w (par P₀ P₁) x y' T) ∧
    (∀ z T, RunsTo w (par P₀ P₁) x z T →
      ∃ (b : Bool) (t : ℕ), RunsTo (w - K) (cond b P₁ P₀) x (1 :: z) t)

/-- **The brute-force evaluator.** The exponent `eb` of the word-length
condition comes before the sentence, the constant `cb` and the degree
`ab` after it. -/
def BruteSpec (Br : Program) : Prop :=
  ∃ eb : ℕ, ∀ φ : Lax3.FirstOrder.FO 0, ∃ cb ab : ℕ,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : List (PartialGraph (Fin n))) (x : List ℕ) (w : ℕ),
      EncodesInput x n G s φ → (∀ v ∈ x, cb * (x.length + v + 1) ^ eb ≤ 2 ^ w) →
        (∀ z t, RunsTo w Br x z t → z = 1 :: mcAns G φ) ∧
        ∃ t ≤ cb * (x.length + 1) * (n + 1) ^ ab, RunsTo w Br x (1 :: mcAns G φ) t

/-! ### The calls of the pipeline -/

/-- A call of the pipeline: the merge lift on the trees of all vertices
at step `t`, the resolve lift at step `t`, or the evaluation on the tree
of vertex `a` in the last partial graph. -/
inductive PCall (n : ℕ)
  | merge (t : ℕ) (P Q : ℕ)
  | resolve (t : ℕ) (sg : Bool) (P Q : ℕ)
  | eval (a : Fin n)

/-- The calls of step `t`. -/
def stepCalls (n t : ℕ) : Step → List (PCall n)
  | .merge P Q => [.merge t P Q]
  | .resolvePos P Q => [.resolve t true P Q]
  | .resolveNeg P Q => [.resolve t false P Q]

/-- The calls of the steps from step `t` on. -/
def callsFrom (n : ℕ) : ℕ → List Step → List (PCall n)
  | _, [] => []
  | t, st :: r => stepCalls n t st ++ callsFrom n (t + 1) r

/-- All calls: the steps, then the evaluation at vertex `0`. -/
def pcalls (n : ℕ) (steps : List Step) : List (PCall n) :=
  callsFrom n 0 steps ++ if h : 0 < n then [.eval ⟨0, h⟩] else []

/-! ### Fixed small queries -/

/-- The partial graph on no vertices. -/
def G0 : PartialGraph (Fin 0) := unresolved fun i => i.elim0

/-- The partial graph on one vertex of color `0`. -/
def G1 : PartialGraph (Fin 1) := unresolved fun _ => 0

/-- The jobs of a merge step: the tree of every vertex with the two
colors. -/
noncomputable def mjobs {n : ℕ} (G : PartialGraph (Fin n)) (q P Q : ℕ) : List (List ℕ) :=
  List.ofFn fun v : Fin n => toWord (tree G 1 q ![v], P, Q)

/-- The answers of the jobs of a merge step: the tree of every vertex
after the merge. -/
noncomputable def mans {n : ℕ} (G : PartialGraph (Fin n)) (q P Q : ℕ) : List (List ℕ) :=
  List.ofFn fun v : Fin n => toWord (tree (merge G P Q) 1 q ![v])

/-- The fixed query of the batched merge lift, the empty list of jobs,
and its answer. -/
def qM0 : List ℕ := [0]
def yM0 : List ℕ := [0]

theorem qM0_eq : qM0 = toWord ([] : List (List ℕ)) := rfl
theorem yM0_eq : yM0 = toWord ([] : List (List ℕ)) := rfl

/-- The fixed query of the resolve lift and its answer. -/
noncomputable def qR0 : List ℕ := toWord (G0, distMatrix G0, (0 : ℕ), (0 : ℕ), false, family G0 1 0)
noncomputable def zR0 : List ℕ :=
  toWord (resolveBy G0 false 0 0, distMatrix (resolveBy G0 false 0 0),
    family (resolveBy G0 false 0 0) 1 0)

/-- The fixed query of the evaluation and its answer. -/
noncomputable def qE0 : List ℕ :=
  toWord (tree G1 1 0 ![(0 : Fin 1)], (Lax185574.DistanceLogic.DistFO.eq 0 0 : Lax185574.DistanceLogic.DistFO 1))

open Classical in
noncomputable def uE0 : List ℕ :=
  toWord (decide (Lax185574.DistanceLogic.DistFO.Sat G1 ![(0 : Fin 1)]
    (Lax185574.DistanceLogic.DistFO.eq 0 0 : Lax185574.DistanceLogic.DistFO 1)))

/-! ### Queries and answers of the calls -/

section calls

variable {n : ℕ} (s : List (PartialGraph (Fin n))) (q : ℕ) (φ : Lax3.FirstOrder.FO 0)

/-- The partial graph at position `t` of the sequence. -/
def sAt (t : ℕ) : PartialGraph (Fin n) := s.getD t (unresolved fun _ => 0)

/-- The query of the batched merge lift in a call. -/
noncomputable def callQM : PCall n → List ℕ
  | .merge t P Q => if P = Q then qM0 else toWord (mjobs (sAt s t) q P Q)
  | _ => qM0

/-- The query of the resolve lift in a call. -/
noncomputable def callQR : PCall n → List ℕ
  | .resolve t sg P Q =>
      toWord (sAt s t, distMatrix (sAt s t), P, Q, sg, family (sAt s t) 1 q)
  | _ => qR0

/-- The query of the evaluation in a call. -/
noncomputable def callQE : PCall n → List ℕ
  | .eval a => toWord (tree (sAt s (s.length - 1)) 1 q ![a], loc q φ)
  | _ => qE0

/-- The query to the callee in a call. -/
noncomputable def callQ (c : PCall n) : List ℕ := swIn (callQM s q c) (callQR s q c) (callQE s q φ c)

/-- The answer of the batched merge lift in a call. -/
noncomputable def callYM : PCall n → List ℕ
  | .merge t P Q => if P = Q then yM0 else toWord (mans (sAt s t) q P Q)
  | _ => yM0

/-- The answer of the resolve lift in a call. -/
noncomputable def callYR : PCall n → List ℕ
  | .resolve t sg P Q =>
      toWord (resolveBy (sAt s t) sg P Q, distMatrix (resolveBy (sAt s t) sg P Q),
        family (resolveBy (sAt s t) sg P Q) 1 q)
  | _ => zR0

open Classical in
/-- The answer of the evaluation in a call. -/
noncomputable def callYE : PCall n → List ℕ
  | .eval a => toWord (decide (Lax185574.DistanceLogic.DistFO.Sat (sAt s (s.length - 1)) ![a] (loc q φ)))
  | _ => uE0

/-- The answer of the callee in a call. -/
noncomputable def callY (c : PCall n) : List ℕ := callYM s q c ++ callYR s q c ++ callYE s q φ c

/-- The guard of a call at word length `v` with shift `sQ`: the query of
the callee that does real work is small for the literal exponent of that
callee. -/
def GuardOK (eM eR eE v sQ : ℕ) : PCall n → Prop
  | c@(.merge ..) => let u := callQM s q c
      (u.length + maxEntry u + 1) ^ (eM + 1) ≤ 2 ^ (v - sQ)
  | c@(.resolve ..) => let u := callQR s q c
      (u.length + maxEntry u + 1) ^ (eR + 1) ≤ 2 ^ (v - sQ)
  | c@(.eval _) => let u := callQE s q φ c
      (u.length + maxEntry u + 1) ^ (eE + 1) ≤ 2 ^ (v - sQ)

end calls

/-! ### The rounds of the glue program -/

section rounds

variable {n : ℕ} (x : List ℕ) (s : List (PartialGraph (Fin n))) (q : ℕ)
  (φ : Lax3.FirstOrder.FO 0) (cs : List (PCall n)) (hd : ℕ → List ℕ) (ans : List ℕ)

/-- The output of round `j` of the glue program: the head `hd j` (tag,
state length, window length, state) and the query of call `j`, and after
the last call the answer with the tags `0, 1`. -/
noncomputable def glueOut (j : ℕ) : List ℕ :=
  match cs[j]? with
  | some c => hd j ++ callQ s q φ c
  | none => 0 :: ans

/-- The state `a` of the loop driver before round `j`. -/
noncomputable def pA : ℕ → List ℕ
  | 0 => lpA0 x
  | j + 1 => glueOut s q φ cs hd ans j

/-- The callee output `b` of the loop driver before round `j`. -/
noncomputable def pB : ℕ → List ℕ
  | 0 => []
  | j + 1 => match cs[j]? with
    | some c => callY s q φ c
    | none => []

/-- The input of round `j` of the glue program. -/
noncomputable def pU (j : ℕ) : List ℕ :=
  lpU x (pA x s q φ cs hd ans j) (pB s q φ cs j)

end rounds

/-- The final output of the pipeline after the tags `0`: `1` and the
answer of the evaluation call. -/
noncomputable def finAns {n : ℕ} (s : List (PartialGraph (Fin n))) (q : ℕ)
    (φ : Lax3.FirstOrder.FO 0) : List ℕ :=
  if h : 0 < n then 1 :: callYE s q φ (.eval ⟨0, h⟩) else []

/-- The largest word length of a tree of a vertex along the sequence. -/
noncomputable def treeMax {n : ℕ} (s : List (PartialGraph (Fin n))) (q : ℕ) : ℕ :=
  ((List.range s.length).map fun t =>
    Finset.univ.sup fun a : Fin n => wordLength (tree (sAt s t) 1 q ![a])).foldr max 0

/-- **The glue program at one instance.** `sI` is the input shift (the
input entries of a round are below `2 ^ (v - sI)`), `sQ` the query shift
of the guards, `eM eR eE` the literal exponents of the guards and `cG`
the constant of the sentence. -/
structure GlueAt (G : Program) (sI sQ eM eR eE cG : ℕ) (φ : Lax3.FirstOrder.FO 0) {n : ℕ}
    (x : List ℕ) (s : List (PartialGraph (Fin n))) (steps : List Step) : Prop where
  /-- Without vertices the glue program never halts. -/
  empty : n = 0 → ∀ v o t, sI ≤ v → (∀ e ∈ lpU x (lpA0 x) [], e < 2 ^ (v - sI)) →
    ¬ RunsTo v G (lpU x (lpA0 x) []) o t
  /-- With vertices it follows the calls, with heads `hd`. The length of
  a head and the length of the window it asks for do not depend on `x`
  (beyond `n`), which the time bound of thm:mc needs. -/
  rounds : 1 ≤ n → ∃ hd : ℕ → List ℕ,
    let q := Lax3.FirstOrder.rank φ
    let cs := pcalls n steps
    let R := cs.length
    let ans := finAns s q φ
    (∀ j < R, hd j ≠ [] ∧ (hd j).head? ≠ some 0 ∧ (hd j).getD 1 0 + 3 = (hd j).length) ∧
    (∀ j < R, (hd j).length + maxEntry (hd j) ≤
      cG * (x.length + maxEntry x + n * treeMax s q + (n + 1) ^ 2)) ∧
    (∀ j < R, (hd j).length + (hd j).getD 2 0 ≤ cG * (n * treeMax s q + (n + 1) ^ 2)) ∧
    (∀ j ≤ R, ∀ v, sI ≤ v → (∀ e ∈ pU x s q φ cs hd ans j, e < 2 ^ (v - sI)) →
      (∀ o t, RunsTo v G (pU x s q φ cs hd ans j) o t →
        o = glueOut s q φ cs hd ans j ∧ (∀ e ∈ o, e < 2 ^ (v - sI - 4)) ∧
        ∀ c, cs[j]? = some c → GuardOK s q φ eM eR eE v sQ c) ∧
      (cG * (((pU x s q φ cs hd ans j).length + (glueOut s q φ cs hd ans j).length +
          maxEntry (pU x s q φ cs hd ans j ++ glueOut s q φ cs hd ans j) + 1) ^
          (eM + eR + eE + 1)) ≤ 2 ^ (v - sQ) →
        ∃ t ≤ cG * ((pU x s q φ cs hd ans j).length + (glueOut s q φ cs hd ans j).length + 1),
          RunsTo v G (pU x s q φ cs hd ans j) (glueOut s q φ cs hd ans j) t))

/-- **The hypothesis on the glue program.** There is an input shift `sI`
such that for all literal exponents of the guards and every `D ≥ sI + 4`
some glue program meets `GlueAt` with query shift `D + 16` on every word
`[n] ++ toWord σ ++ toWord φ`, with a constant `cG` of the sentence. This
is the input of thm:mc without the graph word, which a skip program
removes in front of the pipeline. The pipeline does not need the graph,
since the initial trees depend only on the colors and the partial graphs
come from the script. -/
def GlueHyp : Prop :=
  ∃ sI : ℕ, ∀ eM eR eE D : ℕ, sI + 4 ≤ D → ∃ G : Program, ∀ φ : Lax3.FirstOrder.FO 0, ∃ cG : ℕ,
    ∀ (n : ℕ) (σ : Script n),
      GlueAt G sI (D + 16) eM eR eE cG φ ([n] ++ toWord σ ++ toWord φ) σ.run σ.steps

end Lax185574Proofs.MC
