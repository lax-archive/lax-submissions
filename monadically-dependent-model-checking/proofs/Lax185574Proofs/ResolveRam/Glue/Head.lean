import Lax185574Proofs.ResolveRam.Glue.StateUp

/-!
The heads of the glue program of lem:resolve-lift and the inputs of its
rounds.

The state at a position `c` is the list of scalars `scW` (the window
start `0`, the size `X` of the input, `|x|`, `n`, `P`, `Q`, the sign,
`k₀`, `q₀`, the phase, the level `d`, the item `i`, the step `m` and the
numbers of words of the scatter type, of the filtered far tree, of the
compositions and of the levels) followed by the word of the list
`(swAt c).ws`. The head `hdOf c` is the tag, the length of the state,
the length of the window and the state. The window is the whole input
after round `0` and after the last call, and empty otherwise, and the
tag is one more than the length of the window, so that the round knows
how much of its input is the window. So round `1` and the final
round read the input again (`gU_succ`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.TreeAlgo
open Lax185574Proofs.ResolveRam Lax185574Proofs.Words Lax185574Proofs.Simulate

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The phase, level, item and step of a position. -/
def curW : Cur → List ℕ
  | .stp => [0, 0, 0, 0]
  | .dn d i m => [1, d, i, m]
  | .up d i m => [2, d, i, m]
  | .fin => [3, 0, 0, 0]

/-- The scalars of the state. -/
noncomputable def scW (c : Cur) : List ℕ :=
  let x := xIn G k₀ q₀ P Q s
  let w := swAt G P Q s k₀ q₀ c
  [0, ySz x, x.length, n, P, Q, if s then 1 else 0, k₀, q₀] ++ curW c ++
    [w.SG.length, w.FA.length, w.CO.length, w.LV.length]

/-- The state at a position. -/
noncomputable def stOf (c : Cur) : List ℕ := scW G P Q s k₀ q₀ c ++ toWord (swAt G P Q s k₀ q₀ c).ws

/-- The length of the window that the round after position `c` reads. -/
noncomputable def winOf (c : Cur) : ℕ :=
  if c = .stp ∨ next G P Q s k₀ q₀ c = .fin then (xIn G k₀ q₀ P Q s).length else 0

/-- The tag of the head: one more than the length of the window, so that
the round knows how much of its input is the window. -/
noncomputable def tagOf (c : Cur) : ℕ := winOf G P Q s k₀ q₀ c + 1

theorem winOf_eq (c : Cur) : winOf G P Q s k₀ q₀ c = tagOf G P Q s k₀ q₀ c - 1 := by
  simp [tagOf]

/-- The head written by the round that issues the call at `c`. -/
noncomputable def hdOf (c : Cur) : List ℕ :=
  tagOf G P Q s k₀ q₀ c :: (stOf G P Q s k₀ q₀ c).length :: winOf G P Q s k₀ q₀ c :: stOf G P Q s k₀ q₀ c

/-- The heads of the rounds. -/
noncomputable def hdJ (j : ℕ) : List ℕ := hdOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)

/-- **The shape of the heads.** -/
theorem hdJ_shape (j : ℕ) :
    hdJ G P Q s k₀ q₀ j ≠ [] ∧ (hdJ G P Q s k₀ q₀ j).head? ≠ some 0 ∧
      (hdJ G P Q s k₀ q₀ j).getD 1 0 + 3 = (hdJ G P Q s k₀ q₀ j).length := by
  refine ⟨by simp [hdJ, hdOf], ?_, ?_⟩
  · simp [hdJ, hdOf, tagOf]
  · simp [hdJ, hdOf]

theorem stOf_head (c : Cur) : (stOf G P Q s k₀ q₀ c).getD 0 0 = 0 := by
  simp [stOf, scW]

/-- **The input of the first round.** -/
theorem gU_zero (cs : List RCall) (hd : ℕ → List ℕ) (z : List ℕ) :
    gU G k₀ q₀ (xIn G k₀ q₀ P Q s) cs hd z 0 =
      [0, (xIn G k₀ q₀ P Q s).length] ++ xIn G k₀ q₀ P Q s ++ [0] := by
  simp [gU, gA, gB, RamSim.lpU, RamSim.lpA0]

/-- **The input of round `j + 1`.** After call `j` at position `c`, the
round reads the tag, the length of the state, the window, the state, and
the answer of the switch with its length. -/
theorem gU_succ (z : List ℕ) {j : ℕ} {c : RCall}
    (hc : (rcalls G P Q s k₀ q₀)[j]? = some c) :
    gU G k₀ q₀ (xIn G k₀ q₀ P Q s) (rcalls G P Q s k₀ q₀) (hdJ G P Q s k₀ q₀) z (j + 1) =
      [tagOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j), (stOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)).length] ++
        (xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)) ++
        stOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j) ++ ((rY G k₀ q₀ c).length :: rY G k₀ q₀ c) := by
  simp only [gU, gA, gB, gOut, hc, RamSim.lpU, hdJ, hdOf]
  have h0 : (stOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j)).getD 0 0 = 0 := stOf_head G P Q s k₀ q₀ _
  have hne : stOf G P Q s k₀ q₀ (cur G P Q s k₀ q₀ j) ≠ [] := by simp [stOf, scW]
  obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil hne
  rw [hl] at h0 ⊢
  simp only [List.getD_cons_zero] at h0
  subst h0
  simp

end Lax185574Proofs.ResolveRam.Glue
