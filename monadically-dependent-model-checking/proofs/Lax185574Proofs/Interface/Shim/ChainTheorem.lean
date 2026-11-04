import Lax185574.ChainTheorem
import Lax185574Proofs.LegacyComputing
import Lax185574Proofs.Interface.KitG3

/-!
The statement of `Lax185574.ChainTheorem` for the graph classes of the
archive, their monadic dependence and the older
`Lax185574.Computing.Computes`, derived from the concept. The
word-length exponent doubles, and the constant `c` becomes `3c`, so that
`⌊3c · (n+1)^(3+δ)⌋` bounds `c · n^(3+δ) + c`.
-/

namespace Lax185574Proofs.Shim.ChainTheorem

open Lax199508.GraphClasses Lax710763.MonadicDependence
open Lax808846.Ram Lax185574.Encoding Lax185574.Computing
open Lax185574.Partitions Lax185574.Flips Lax185574.ChainTheorem
open Lax185574Proofs.Interface Lax185574Proofs.Interface.KitG3

/-- A larger bound on the number of types in a ball holds a fortiori. -/
theorem BallsMeetFewTypes.mono {V : Type*} {G : SimpleGraph V} {r : ℕ} {K K' : ℝ}
    {B : List (Finset V)} (h : BallsMeetFewTypes G r K B) (hK : K ≤ K') :
    BallsMeetFewTypes G r K' B :=
  fun t ht u => (h t ht u).trans hK

theorem exists_program_decreasingChain :
    ∃ (p : Program) (e A : ℕ)
      (B : ∀ n : ℕ, ℕ → ℚ → SimpleGraph (Fin n) → List (Finset (Fin n))),
      (∀ (n r : ℕ) (ε : ℚ) (G : SimpleGraph (Fin n)), 1 ≤ r → 0 < ε →
        IsDecreasingChain (B n r ε G) ∧ ((B n r ε G).length : ℚ) ≤ A * r / ε + A) ∧
      ∀ (C : GraphClass), MonadicallyDependent C → ∀ (r : ℕ) (ε : ℚ), 1 ≤ r → 0 < ε →
        ∀ δ : ℝ, 0 < δ → ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
          BallsMeetFewTypes G r (c * ((n : ℝ) + 1) ^ (ε : ℝ)) (B n r ε G) ∧
          Computes p e c (r, ε, G) (B n r ε G)
            (fun _ => ⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + δ)⌋₊) := by
  obtain ⟨A, K, chain, hB, hcl⟩ := Lax185574.ChainTheorem.exists_program_decreasingChain
  refine ⟨A.program, 2 * A.wordExponent, K, fun n r ε G => chain r ε (toGraph G),
    fun n r ε G hr hε => hB r ε (toGraph G) hr hε, fun C hC r ε hr hε δ hδ => ?_⟩
  obtain ⟨c, hc⟩ := hcl (ofOld C) ((monadicallyDependent_ofOld_iff C).mpr hC) r ε hr hε δ hδ
  refine ⟨3 * c, fun n G hG => ?_⟩
  obtain ⟨h1, h2⟩ := hc (toGraph G) hG
  refine ⟨BallsMeetFewTypes.mono h1 ?_, ?_⟩
  · simp only [toGraph_n]
    push_cast
    have : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ (ε : ℝ) := by positivity
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
    nlinarith
  · have hA := computes_congr (a' := (r, ε, G)) (encode_triple_graph r ε (toGraph G)) rfl h2
    refine oldComputes_mono (Nat.le_mul_of_pos_left c (by norm_num)) (fun _ => le_rfl)
      (old_of_computes (encode_nat_pair_ne_nil r (ε, G)) ?_ hA)
    simp only [toGraph_n]
    exact le_floor_rpow c n (by linarith)

end Lax185574Proofs.Shim.ChainTheorem
