import Lax185574Proofs.MC.Glue.Next

/-!
The words of the state of the glue program of thm:mc from one call to
the next.

The answer of the merge lift on all vertices is the family of trees of
step `t + 1`. The partial graph of step `t + 1` after a merge is the old
one with recolored colors (`toWord_merge`), and its matrix of distances
is the old one. After a resolve the answer is the partial graph, its
matrix of distances and the family of step `t + 1`.
-/

namespace Lax185574Proofs.MC.Glue

open Lax185574Proofs.MC Lax185574Proofs.Words
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.PartialGraphEncoding Lax185574.TypeTrees Lax185574.ConstructionSequences
open Lax185574.ResolveLift

variable {n : ℕ}

/-! ### The sequence of a script -/

theorem sAt_succ (σ : Script n) {t : ℕ} {st : Step} (h : σ.steps[t]? = some st) :
    sAt σ.run (t + 1) = apply (sAt σ.run t) st := by
  have ht : t < σ.steps.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; simp at h
  have h0 : σ.run[t]? = some (sAt σ.run t) := by
    rw [List.getElem?_eq_getElem (by simp [Script.run]; omega)]
    simp [sAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show t < σ.run.length by
      simp [Script.run]; omega)]
  have h1 := List.getElem?_succ_scanl (f := apply) (b := unresolved σ.colors) (l := σ.steps) (i := t)
  rw [show List.scanl apply (unresolved σ.colors) σ.steps = σ.run from rfl, h0, h] at h1
  simp only [Option.bind_some, Option.map_some] at h1
  simp [sAt, List.getD_eq_getElem?_getD, h1]

theorem merge_self (G : PartialGraph (Fin n)) (P : ℕ) : merge G P P = G := by
  cases G with
  | mk edge nonEdge disjoint color =>
    simp only [merge, PartialGraph.mk.injEq, true_and]
    funext v; split_ifs with h <;> simp [h]

/-! ### The partial graph after a merge -/

theorem toWord_merge (G : PartialGraph (Fin n)) (P Q : ℕ) :
    toWord (merge G P Q) = (n :: (List.ofFn G.color).map (recol 1 P Q)) ++
      (toWord G.edge ++ toWord G.nonEdge) := by
  rw [toWord_pg]
  congr 2
  rw [List.map_ofFn]
  congr 1
  funext v
  simp [merge, recol, Function.comp]

theorem recol_zero (P Q : ℕ) : recol 0 P Q = id := by
  funext c; simp [recol]

/-! ### Segments -/

theorem seg_of_drop {X : List ℕ} {a : ℕ} {A R : List ℕ} (h : X.drop a = A ++ R) {i k : ℕ}
    (hk : i + k ≤ A.length) : seg X (a + i) k = (A.drop i).take k := by
  rw [seg, ← List.drop_drop, h, List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by simp; omega)]

/-! ### The words of the state after a step -/

open Lax185574.DistanceMatrix in
theorem gwOf_after (σ : Script n) (q : ℕ) (hn : 0 < n) {t : ℕ} (ht : t < σ.steps.length) :
    gwOf σ.run σ.steps.length (afterStep hn σ.steps t) =
      toWord (sAt σ.run (t + 1)) ++ toWord (distMatrix (sAt σ.run (t + 1))) := by
  unfold afterStep
  split_ifs with h
  · generalize σ.steps[t + 1] = st
    cases st <;> rfl
  · simp only [gwOf, ctOf]; rw [show σ.steps.length = t + 1 by omega]

theorem fwOf_after (σ : Script n) (q : ℕ) (hn : 0 < n) {t : ℕ} (ht : t < σ.steps.length) :
    fwOf σ.run q σ.steps.length (afterStep hn σ.steps t) = toWord (family (sAt σ.run (t + 1)) 1 q) := by
  unfold afterStep
  split_ifs with h
  · generalize σ.steps[t + 1] = st
    cases st <;> rfl
  · simp only [fwOf, ctOf]; rw [show σ.steps.length = t + 1 by omega]

end Lax185574Proofs.MC.Glue
