import Lax185574Proofs.MC.Glue.NextF

/-!
The words of the state of the next call, in terms of the words a round
of the glue program of thm:mc builds from the answer of the current
call.

`merge_next`: after a merge with `P ≠ Q`, the partial graph of the next
call is the old one recolored, with the same matrix of distances, and
its family consists of the answers of the merge lift. `self_next`:
after `merge_{P,P}` nothing changes. `resolve_next`: after a resolve the
words are those of the answer. `tsOf`: the family of a call as a list of
trees (`tsOf_eval`).
-/

namespace Lax185574Proofs.MC.Glue

open Lax185574Proofs.MC Lax185574Proofs.Words
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.PartialGraphEncoding Lax185574.TypeTrees Lax185574.ConstructionSequences
open Lax185574.ResolveLift

variable {n : ℕ}

theorem step_lt {steps : List Step} {t : ℕ} {st : Step} (h : steps[t]? = some st) :
    t < steps.length := by
  by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; simp at h

open Lax185574.DistanceMatrix in
theorem merge_next (σ : Script n) (q : ℕ) (hn : 0 < n) {t P Q : ℕ}
    (hst : σ.steps[t]? = some (.merge P Q)) {c' : PCall n}
    (hc' : nextCall hn σ.steps (.merge t P Q) = some c') :
    gwOf σ.run σ.steps.length c' = (n :: (List.ofFn (sAt σ.run t).color).map (recol 1 P Q)) ++
        (toWord (sAt σ.run t).edge ++ toWord (sAt σ.run t).nonEdge ++
          toWord (distMatrix (sAt σ.run t))) ∧
    fwOf σ.run q σ.steps.length c' = n :: (mans (sAt σ.run t) q P Q).flatten := by
  have ht := step_lt hst
  have hs1 : sAt σ.run (t + 1) = merge (sAt σ.run t) P Q := sAt_succ σ hst
  simp only [nextCall] at hc'
  cases hc'
  refine ⟨?_, ?_⟩
  · rw [gwOf_after σ q hn ht, hs1]
    rw [toWord_merge, Lax185574Proofs.DistMatrix.distMatrix_merge]
    simp only [List.append_assoc]
  · rw [fwOf_after σ q hn ht, hs1, toWord_family, mans, List.map_ofFn]
    rfl

theorem self_next (σ : Script n) (q : ℕ) (hn : 0 < n) {t P : ℕ}
    (hst : σ.steps[t]? = some (.merge P P)) {c' : PCall n}
    (hc' : nextCall hn σ.steps (.merge t P P) = some c') :
    gwOf σ.run σ.steps.length c' = gwOf σ.run σ.steps.length (.merge t P P) ∧
    fwOf σ.run q σ.steps.length c' = fwOf σ.run q σ.steps.length (.merge t P P) := by
  have ht := step_lt hst
  have hs1 : sAt σ.run (t + 1) = sAt σ.run t := by rw [sAt_succ σ hst]; exact merge_self _ _
  simp only [nextCall] at hc'
  cases hc'
  refine ⟨by rw [gwOf_after σ q hn ht, hs1]; rfl, ?_⟩
  rw [fwOf_after σ q hn ht, hs1]; rfl

open Lax185574.DistanceMatrix in
theorem resolve_next (σ : Script n) (q : ℕ) (hn : 0 < n) {t P Q : ℕ} {sg : Bool}
    (hst : σ.steps[t]? = some (if sg then .resolvePos P Q else .resolveNeg P Q)) {c' : PCall n}
    (hc' : nextCall hn σ.steps (.resolve t sg P Q) = some c') :
    gwOf σ.run σ.steps.length c' = toWord (resolveBy (sAt σ.run t) sg P Q) ++
      toWord (distMatrix (resolveBy (sAt σ.run t) sg P Q)) ∧
    fwOf σ.run q σ.steps.length c' = toWord (family (resolveBy (sAt σ.run t) sg P Q) 1 q) := by
  have ht := step_lt hst
  have hs1 : sAt σ.run (t + 1) = resolveBy (sAt σ.run t) sg P Q := by
    rw [sAt_succ σ hst]; cases sg <;> rfl
  simp only [nextCall] at hc'
  cases hc'
  exact ⟨by rw [gwOf_after σ q hn ht, hs1], by rw [fwOf_after σ q hn ht, hs1]⟩

/-! ### The trees of a call -/

/-- The family of trees of a call, as a list. -/
noncomputable def tsOf (s : List (PartialGraph (Fin n))) (q m : ℕ) (c : PCall n) : List TypeTree :=
  List.ofFn fun a : Fin n => tree (sAt s (ctOf m c)) 1 q ![a]

theorem length_tsOf (s : List (PartialGraph (Fin n))) (q m : ℕ) (c : PCall n) :
    (tsOf s q m c).length = n := by
  simp [tsOf]

theorem fwOf_tsOf (s : List (PartialGraph (Fin n))) (q m : ℕ) (c : PCall n) :
    fwOf s q m c = n :: ((tsOf s q m c).map toWord).flatten :=
  toWord_family _ _

theorem tsOf_eval (σ : Script n) (q : ℕ) (a : Fin n) :
    (tsOf σ.run q σ.steps.length (.eval a))[a.val]'(by rw [length_tsOf]; exact a.2) =
      tree (sAt σ.run (σ.run.length - 1)) 1 q ![a] := by
  simp [tsOf, ctOf, length_run]

end Lax185574Proofs.MC.Glue
