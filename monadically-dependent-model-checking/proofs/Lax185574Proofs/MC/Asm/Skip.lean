import Lax185574Proofs.RamSimulateBack
import Lax185574Proofs.Legacy
import Lax185574.ConstructionModelChecking
import Lax185574Proofs.LegacyInputs

/-!
Skipping the graph word.

The input of thm:mc starts with a graph word in compressed sparse row
form, whose length `3 + n + 2 E` is read off its first two entries, the
number `n` of vertices and the declared number `E` of edges. Since a
block of the target array may repeat a neighbor, `E` is not bounded in
`n`. The pipeline of thm:mc needs only `n` and the rest of the input.
`skip` runs a program on `[n] ++ y` for the input `g ++ y`, by a
simulation on the rewrite that keeps the first entry and drops the
first `3 + x[0] + 2 x[1]` entries. The rewrite has constant cost, so
the time does not depend on the length of the graph word.
-/

namespace Lax185574Proofs.MC

open Lax808846.Ram Lax185574Proofs.Simulate Lax185574Proofs.RamSim
open Lax271696.GraphEncoding

/-- The start of the rest of the input: `3 + x[0] + 2 x[1]`. -/
def skipStart : HExpr 1 :=
  .add (.add (.lit 3) (.entry 0 0)) (.mul (.lit 2) (.entry 0 1))

/-- The rewrite: the first entry, then the input from `skipStart` on. -/
def skipRw : Rewrite 1 := [.expr (.entry 0 0), .slice 0 skipStart none]

theorem getD_append_lt {l u : List ℕ} {i : ℕ} (h : i < l.length) :
    (l ++ u).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem skipRw_cost (x : List ℕ) : skipRw.cost (fun _ => x) = 11 := by
  simp [skipRw, skipStart, Rewrite.cost, Segment.cost, HExpr.cost]

theorem skipStart_eval {g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} (hg : EncodesGraph g n G)
    (y : List ℕ) : skipStart.eval (fun _ => g ++ y) = g.length := by
  have hl := hg.length_eq
  have h0 : (g ++ y).getD 0 0 = n := by
    rw [getD_append_lt (by omega)]; exact hg.vertexCount_eq
  have h1 : (g ++ y).getD 1 0 = edgeCount g := by
    rw [getD_append_lt (by omega)]; rfl
  simp only [skipStart, HExpr.eval, h0, h1]
  omega

theorem skipRw_apply {g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} (hg : EncodesGraph g n G)
    (y : List ℕ) : skipRw.apply (fun _ => g ++ y) = [n] ++ y := by
  have hl := hg.length_eq
  have h0 : (g ++ y).getD 0 0 = n := by
    rw [getD_append_lt (by omega)]; exact hg.vertexCount_eq
  have hs := skipStart_eval hg y
  simp only [skipRw, Rewrite.apply, List.map_cons, List.map_nil, Segment.apply, HExpr.eval, h0, hs,
    List.drop_left, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem skipRw_fits {g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} (hg : EncodesGraph g n G)
    {y : List ℕ} {w : ℕ} (hx : (g ++ y).length < 2 ^ w) : skipRw.Fits w (fun _ => g ++ y) := by
  have hl := hg.length_eq
  have h1 : 1 < 2 ^ w := by
    have : (g ++ y).length = g.length + y.length := List.length_append
    omega
  refine ⟨fun _ => hx, ?_, ?_⟩
  · rw [skipRw_apply hg]; simp only [List.length_append, List.length_singleton] at hx ⊢; omega
  · intro seg hseg
    simp only [skipRw, List.mem_cons, List.mem_nil_iff, or_false] at hseg
    rcases hseg with rfl | rfl
    · show 0 < 2 ^ w; omega
    · refine ⟨⟨⟨trivial, show 0 < 2 ^ w by omega⟩, trivial, show 1 < 2 ^ w from h1⟩, ?_⟩
      rw [skipStart_eval hg]; simp only [List.length_append] at hx; omega

/-- **Skipping the graph word, both directions.** For every program
`P₀` there is a program `p` that, on `g ++ y` for a graph word `g` of
`n` vertices, runs `P₀` on `[n] ++ y` one word bit lower. The time is
`K (t + 1)` for a run of `P₀` in `t` steps, without a term in the
length of `g`, and every halting run of `p` comes from a halting run of
`P₀` with the same output. -/
theorem skip (P₀ : Program) : ∃ (p : Program) (K : ℕ), 1 ≤ K ∧
    ∀ (w n : ℕ) (G : SimpleGraph (Fin n)) (g y : List ℕ), EncodesGraph g n G →
      K ≤ 2 ^ (w - 1) → (g ++ y).length < 2 ^ w →
      (∀ z t, RunsTo (w - 1) P₀ ([n] ++ y) z t → ∃ t' ≤ K * (t + 1), RunsTo w p (g ++ y) z t') ∧
      (∀ z T, RunsTo w p (g ++ y) z T → ∃ t ≤ T, RunsTo (w - 1) P₀ ([n] ++ y) z t) := by
  obtain ⟨p, K, hs⟩ := simulate_sound P₀ skipRw
  refine ⟨p, 11 * K + 1, by omega, fun w n G g y hg hK hx => ?_⟩
  obtain ⟨hf, hb⟩ := hs w (g ++ y) (by omega) (skipRw_fits hg hx)
  rw [skipRw_apply hg, skipRw_cost] at hf
  rw [skipRw_apply hg] at hb
  refine ⟨fun z t h => ?_, hb⟩
  obtain ⟨t', ht', h'⟩ := hf z t h
  refine ⟨t', le_trans ht' ?_, h'⟩
  nlinarith

end Lax185574Proofs.MC
