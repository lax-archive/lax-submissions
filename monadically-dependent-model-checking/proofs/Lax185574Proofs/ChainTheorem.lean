import Lax185574Proofs.Chain.Ram.ChainProgram
import Lax185574Proofs.Chain.Ram.ChainCost
import Lax185574Proofs.Interface.KitG3

/-!
Theorem 4.4 of the companion paper (`Lax185574.ChainTheorem`): the chain
`Lax185574Proofs.Chain.chainB` has the required properties, and the
program `Lax185574Proofs.Chain.Ram.chainProg` computes it in time
`c (n+1)^{3+δ}` on the members of a monadically dependent class.
-/

namespace Lax185574Proofs.ChainTheorem

open Finset Lax199508.GraphClasses Lax710763.MonadicDependence
open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing
open Lax185574Proofs.Chain Lax185574Proofs.Chain.Ram Lax185574Proofs.Words

theorem rpow_ge_pow (n k : ℕ) {δ : ℝ} (hk : k ≤ 3) (hδ : 0 ≤ δ) :
    (((n + 1) ^ k : ℕ) : ℝ) ≤ ((n : ℝ) + 1) ^ ((3 : ℝ) + δ) := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  push_cast
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le h1 (by have : (k : ℝ) ≤ 3 := by exact_mod_cast hk
                                                linarith)

theorem poly_le (n : ℕ) : n * (17 * n + 15) + 100 + n * 20 + n * (n * 60 + 200) +
    (n + 1) * (n * 100 + 200) + 100 ≤ 2000 * (n + 1) ^ 3 := by
  have h3 : (n + 1) ^ 3 = n * n * n + 3 * (n * n) + 3 * n + 1 := by ring
  rw [h3]
  have : 0 ≤ n * n * n := Nat.zero_le _
  nlinarith

theorem qCost_le (n a c P : ℕ) : qCost n a c P ≤
    (((c + 2) * (P * 30 + 30) + 20) + (a + 1) * (P * 30 + 30) + 40) * (n + 1) ^ 1 := by
  unfold qCost
  rw [pow_one]
  generalize (c + 2) * (P * 30 + 30) = u
  generalize (a + 1) * (P * 30 + 30) = v
  nlinarith

/-- The running time on the class. -/
theorem chainCost_bound (C : GraphClass) (hC : MonadicallyDependent C) (r : ℕ) (ε : ℚ)
    (hr : 1 ≤ r) (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ c : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
      ((@chainCost n r ε G (Classical.decRel _) : ℕ) : ℝ) ≤ c * ((n : ℝ) + 1) ^ ((3 : ℝ) + δ) := by
  obtain ⟨cS, hS⟩ := chain_cost_bound C hC r ε hr hε hδ
  obtain ⟨cW, hW⟩ := welzl_cost_bound C hC hδ
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = ((2 * r * ε.den + 2) * ((ε.num.natAbs + 2 * r * ε.den + 2) * 30 + 30)
      + 20) + (ε.num.natAbs + 1) * ((ε.num.natAbs + 2 * r * ε.den + 2) * 30 + 30) + 40 := ⟨_, rfl⟩
  refine ⟨2000 + Q + 300 * max cW 0 + max cS 0, fun n G hG => ?_⟩
  let _ := Classical.decRel G.Adj
  have hX : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ ((3 : ℝ) + δ) :=
    Real.one_le_rpow (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith) (by linarith)
  obtain ⟨X, hXd⟩ : ∃ X, X = ((n : ℝ) + 1) ^ ((3 : ℝ) + δ) := ⟨_, rfl⟩
  rw [← hXd] at hX ⊢
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hpoly := poly_le n
  have hpolyR := (rpow_ge_pow n 3 le_rfl hδ.le)
  rw [← hXd] at hpolyR
  have hq := qCost_le n ε.num.natAbs (2 * r * ε.den) (ε.num.natAbs + 2 * r * ε.den + 2)
  rw [← hQ] at hq
  have hqR := (rpow_ge_pow n 1 (by norm_num) hδ.le)
  rw [← hXd] at hqR
  rcases Nat.lt_or_ge n 2 with hn | hn
  · unfold chainCost; rw [if_pos hn]
    have : n * (17 * n + 15) + 100 + n * 20 ≤ 2000 * (n + 1) ^ 3 := le_trans (by omega) hpoly
    have h1 : ((n * (17 * n + 15) + 100 + n * 20 : ℕ) : ℝ) ≤ 2000 * X := by
      calc ((n * (17 * n + 15) + 100 + n * 20 : ℕ) : ℝ) ≤ ((2000 * (n + 1) ^ 3 : ℕ) : ℝ) := by
            exact_mod_cast this
        _ = 2000 * (((n + 1) ^ 3 : ℕ) : ℝ) := by push_cast; ring
        _ ≤ 2000 * X := by linarith
    have : (0 : ℝ) ≤ (Q : ℝ) + 300 * max cW 0 + max cS 0 := by positivity
    nlinarith
  · unfold chainCost; rw [if_neg (by omega)]
    have hs := hS n G hn hG
    have hw := hW n G hG
    rw [← hXd] at hs hw
    unfold tailCost
    push_cast
    have e1 : ((n : ℝ) * (17 * n + 15) + 100 + n * 20 + n * (n * 60 + 200) + (n + 1) * (n * 100 + 200) +
        100) ≤ 2000 * X := by
      have : ((n * (17 * n + 15) + 100 + n * 20 + n * (n * 60 + 200) + (n + 1) * (n * 100 + 200) +
        100 : ℕ) : ℝ) ≤ ((2000 * (n + 1) ^ 3 : ℕ) : ℝ) := by exact_mod_cast hpoly
      push_cast at this hpolyR; linarith
    have e2 : (qCost n ε.num.natAbs (2 * r * ε.den) (ε.num.natAbs + 2 * r * ε.den + 2) : ℝ) ≤
        Q * X := by
      have : (qCost n ε.num.natAbs (2 * r * ε.den) (ε.num.natAbs + 2 * r * ε.den + 2) : ℝ) ≤
          ((Q * (n + 1) ^ 1 : ℕ) : ℝ) := by exact_mod_cast hq
      push_cast at this hqR; nlinarith
    have e3 : ((n : ℝ) + 1) ^ 3 *
        (((univ.sup fun x => stepCross G x (welzlTree G).steps : ℕ) : ℝ) + 1) *
        (((univ.sup fun x => stepCross G x (welzlTree G).steps : ℕ) : ℝ) + (Nat.log 2 n : ℝ) + 2) ≤
        max cW 0 * X := hw.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hX0)
    have e4 := hs.trans (mul_le_mul_of_nonneg_right (le_max_left cS 0) hX0)
    push_cast at e4
    have hm : 0 ≤ max cW 0 := le_max_right _ _
    have hm' : 0 ≤ max cS 0 := le_max_right _ _
    nlinarith

/-- The statement for the graph classes of the archive, their monadic
dependence and the older `Lax185574.Computing.Computes`.

The sequence is `chainB` with `A = 2`, and its combinatorial properties
are `chainB_spec`. The program `chainProg` reads `(r, ε, G)` into an
adjacency matrix, computes `q` with digits in base `n + 2`, runs the
greedy Welzl procedure with binary big numbers, builds the ordering,
runs the damping sequence, each damping step trying `κ = 1, 2, …` and
each predamping procedure keeping pointers for rules (R2) and (R3), and
writes the suffix unions. Its cost is `chainCost`, which is at most
`c (n+1)^{3+δ}` on the class by `chainCost_bound`. Values stay below
`64 (|x| + M + 1)³`, so word-length exponent `3` suffices.
-/
theorem exists_program_decreasingChain_old :
    ∃ (p : Program) (e A : ℕ)
      (B : ∀ n : ℕ, ℕ → ℚ → SimpleGraph (Fin n) → List (Finset (Fin n))),
      (∀ (n r : ℕ) (ε : ℚ) (G : SimpleGraph (Fin n)), 1 ≤ r → 0 < ε →
        Lax185574.ChainTheorem.IsDecreasingChain (B n r ε G) ∧
          ((B n r ε G).length : ℚ) ≤ A * r / ε + A) ∧
      ∀ (C : GraphClass), MonadicallyDependent C → ∀ (r : ℕ) (ε : ℚ), 1 ≤ r → 0 < ε →
        ∀ δ : ℝ, 0 < δ → ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
          Lax185574.ChainTheorem.BallsMeetFewTypes G r (c * ((n : ℝ) + 1) ^ (ε : ℝ)) (B n r ε G) ∧
          Computes p e c (r, ε, G) (B n r ε G)
            (fun _ => ⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + δ)⌋₊) := by
  refine ⟨Lax808846Proofs.Compile.compileProgram chainLayout chainProg, 3, 2, chainB,
    fun n r ε G hr hε => ?_, fun C hC r ε hr hε δ hδ => ?_⟩
  · obtain ⟨h1, h2⟩ := chainB_spec.1 n r ε G hr hε
    exact ⟨h1, by push_cast at h2 ⊢; linarith⟩
  obtain ⟨cb, hcb⟩ := chainB_spec.2 C hC r ε hr hε
  obtain ⟨cc, hcc⟩ := chainCost_bound C hC r ε hr hε hδ
  set c : ℕ := max cb (⌈10 * max cc 0⌉₊ + 1 + layoutConst chainLayout 64) with hcdef
  refine ⟨c, fun n G hG => ⟨?_, ?_⟩⟩
  · intro t ht u
    refine (hcb n G hG t ht u).trans ?_
    have : (cb : ℝ) ≤ c := by exact_mod_cast le_max_left _ _
    exact mul_le_mul_of_nonneg_right this (by positivity)
  · refine computes_of_run_le chainProg_ok (A := 64) (by norm_num) (by norm_num)
      (le_trans (by omega) (le_max_right _ _)) ?_ ?_
    · rw [toWord_input hε G]; simp
    · obtain ⟨σ', K, hr', hout, hK⟩ := @chainProg_run n r ε hr hε G (Classical.decRel _)
      refine ⟨_, σ', K, hr', hout, ?_⟩
      simp only [Lax808846Proofs.Compile.Layout.const]
      have hX : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ ((3 : ℝ) + δ) :=
        Real.one_le_rpow (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith) (by linarith)
      have hKc := hcc n G hG
      have hKr : (K : ℝ) ≤ max cc 0 * ((n : ℝ) + 1) ^ ((3 : ℝ) + δ) := by
        have : (K : ℝ) ≤ ((@chainCost n r ε G (Classical.decRel _) : ℕ) : ℝ) := by exact_mod_cast hK
        exact this.trans (hKc.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)))
      refine Nat.le_floor ?_
      have hc1 : 10 * max cc 0 + 1 ≤ (c : ℝ) := by
        have h1 : 10 * max cc 0 ≤ (⌈10 * max cc 0⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : ((⌈10 * max cc 0⌉₊ + 1 + layoutConst chainLayout 64 : ℕ) : ℝ) ≤ c := by
          exact_mod_cast le_max_right _ _
        push_cast at h2
        have : (0 : ℝ) ≤ layoutConst chainLayout 64 := Nat.cast_nonneg _
        linarith
      push_cast
      have hm : 0 ≤ max cc 0 := le_max_right _ _
      nlinarith

open Lax185574.Graphs Lax185574.Algorithms Lax185574Proofs.Interface
open Lax185574Proofs.Interface.KitG3

/--
---
conclusion: Lax185574.ChainTheorem.exists_program_decreasingChain
---
The statement for graphs, graph classes and `Algorithm.Computes`, from
the version for simple graphs applied to the class of the simple graphs
of the members. The algorithm is the program with its exponent, the
sequence of a graph is that of its simple graph, and the
constant `c` becomes `⌈c · 2^(3+δ)⌉`, so that `c' · n^(3+δ) + c'` bounds
the time `⌊c · (n+1)^(3+δ)⌋`.
-/
theorem exists_program_decreasingChain :
    ∃ (A : Algorithm) (K : ℕ) (chain : ℕ → ℚ → (G : Graph) → List (Finset (Fin G.n))),
      (∀ (r : ℕ) (ε : ℚ) (G : Graph), 1 ≤ r → 0 < ε →
        Lax185574.ChainTheorem.IsDecreasingChain (chain r ε G) ∧
          ((chain r ε G).length : ℚ) ≤ K * r / ε + K) ∧
      ∀ C : Lax185574.Graphs.GraphClass, Lax185574.MonadicDependence.MonadicallyDependent C →
        ∀ (r : ℕ) (ε : ℚ), 1 ≤ r → 0 < ε →
        ∀ δ : ℝ, 0 < δ → ∃ c : ℕ, ∀ G ∈ C,
          Lax185574.ChainTheorem.BallsMeetFewTypes G.toSimpleGraph r
            (c * ((G.n : ℝ) + 1) ^ (ε : ℝ)) (chain r ε G) ∧
          A.Computes c (r, ε, G) (chain r ε G) ((G.n : ℝ) ^ (3 + δ)) := by
  obtain ⟨p, e, K, B, hB, hcl⟩ := exists_program_decreasingChain_old
  refine ⟨⟨p, e⟩, K, fun r ε G => B G.n r ε G.toSimpleGraph,
    fun r ε G hr hε => hB G.n r ε G.toSimpleGraph hr hε, fun C hC r ε hr hε δ hδ => ?_⟩
  obtain ⟨c, hc⟩ := hcl (toOld C) (monadicallyDependent_toOld hC) r ε hr hε δ hδ
  have hx : (0 : ℝ) ≤ 3 + δ := by linarith
  have hcc := le_ceil_mul_two_rpow c hx
  refine ⟨⌈(c : ℝ) * 2 ^ ((3 : ℝ) + δ)⌉₊, fun G hG => ?_⟩
  obtain ⟨h1, h2⟩ := hc G.n G.toSimpleGraph hG
  have hK : (c : ℝ) * ((G.n : ℝ) + 1) ^ (ε : ℝ) ≤
      (⌈(c : ℝ) * 2 ^ ((3 : ℝ) + δ)⌉₊ : ℝ) * ((G.n : ℝ) + 1) ^ (ε : ℝ) :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hcc) (by positivity)
  exact ⟨fun t ht u => (h1 t ht u).trans hK, computes_congr (encode_triple_graph r ε G).symm rfl
    (computes_of_old hcc (floor_rpow_le c G.n hx) h2)⟩

end Lax185574Proofs.ChainTheorem
