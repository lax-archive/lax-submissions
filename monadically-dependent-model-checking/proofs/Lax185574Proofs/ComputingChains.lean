import Lax185574.ComputingChains
import Lax185574.ChainTheorem
import Lax185574Proofs.RamPipe
import Lax185574Proofs.Compose.Reverse
import Lax185574Proofs.Compose.Basic
import Lax185574Proofs.ChainConstructionSequences
import Lax185574Proofs.Interface.Shim.ChainTheorem

/-!
Proof of `ComputingChains` from the chain theorem of the companion paper
(`ChainTheorem`). The companion paper computes a decreasing sequence
`V = B₀ ⊇ ⋯ ⊇ B_m = ∅`, and a chain is the same sequence read
backwards. The program pipes the program of the chain theorem into a
program that reverses a list of vertex sets.

The chain theorem bounds the running time by `c (n+1)^(3+δ)` for every
`δ > 0`. Its instance at `δ = 1` is a polynomial of degree four in the
input length, so with the word-length exponent at least four the program
halts at every admissible word length, which gives soundness by
determinism.
-/

namespace Lax185574Proofs.ComputingChains

open Lax199508.GraphClasses Lax710763.MonadicDependence
open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing Lax185574.Chains
open Lax185574.Partitions Lax185574.Flips Lax185574.ChainTheorem
open Lax185574Proofs.Simulate Lax185574Proofs.Compose Lax185574Proofs.Words
open Lax185574Proofs.ChainConstructionSequences (ρId ρId_apply ρId_cost ρId_fits
  toWord_graph_length_ge small)

variable {V : Type} [Fintype V]

/-- The reverse of a decreasing chain is a chain. -/
theorem isChain_reverse {B : List (Finset V)} (h : IsDecreasingChain B) : IsChain B.reverse := by
  obtain ⟨hne, hhd, hlast, hsub⟩ := h
  refine ⟨by simpa using hne, ?_, ?_, ?_⟩
  · rw [List.head_reverse]; exact hlast
  · rw [List.getLast_reverse]; exact hhd
  · intro t ht
    simp only [List.length_reverse] at ht
    rw [List.getElem_reverse, List.getElem_reverse]
    have := hsub (B.length - 1 - (t + 1)) (by omega)
    have e : B.length - 1 - (t + 1) + 1 = B.length - 1 - t := by omega
    simp only [e] at this
    exact this

omit [Fintype V] in
/-- The width of the reversed chain is bounded by the bound on the balls
of the decreasing chain. -/
theorem chainWidth_reverse_le (G : SimpleGraph V) (r : ℕ) {K : ℝ} (hK : 0 ≤ K)
    {B : List (Finset V)} (h : BallsMeetFewTypes G r K B) : (chainWidth G r B.reverse : ℝ) ≤ K := by
  have hle : chainWidth G r B.reverse ≤ ⌊K⌋₊ := by
    apply csSup_le'
    rintro k ⟨t, ht, v, rfl⟩
    simp only [List.length_reverse] at ht
    apply Nat.le_floor
    rw [List.getElem_reverse, List.getElem_reverse]
    have := h (B.length - 1 - (t + 1)) (by omega) v
    have e : B.length - 1 - (t + 1) + 1 = B.length - 1 - t := by omega
    simp only [e] at this
    exact this
  exact (Nat.cast_le.mpr hle).trans (Nat.floor_le hK)

/-- The output only, as a rewrite over the output and the input. -/
def ρOut : Rewrite 2 := [.slice 0 (.lit 0) none]

theorem ρOut_apply (y x : List ℕ) : ρOut.apply ![y, x] = y := by
  simp [ρOut, Rewrite.apply, Segment.apply, HExpr.eval]

theorem ρOut_cost (xs : Fin 2 → List ℕ) : ρOut.cost xs = 3 := by
  simp [ρOut, Rewrite.cost, Segment.cost, HExpr.cost]

theorem ρOut_fits {w : ℕ} {y x : List ℕ} (hy : y.length < 2 ^ w) (hx : x.length < 2 ^ w) :
    ρOut.Fits w ![y, x] := by
  refine ⟨fun i => ?_, by rw [ρOut_apply]; exact hy, ?_⟩
  · fin_cases i <;> simpa
  · intro seg hs
    simp only [ρOut, List.mem_singleton] at hs
    subst hs
    exact ⟨trivial, by show 0 < 2 ^ w; positivity⟩

/-- The word of the input `(r, ε, G)` for `ε > 0`. -/
theorem toWord_input (r : ℕ) {ε : ℚ} (hε : 0 < ε) {n : ℕ} (G : SimpleGraph (Fin n)) :
    toWord (r, ε, G) = r :: 0 :: ε.num.natAbs :: ε.den :: toWord G := by
  have hnum : 0 < ε.num := Rat.num_pos.mpr hε
  change [r] ++ (toWord (ε.num, ε.den) ++ toWord G) = _
  change [r] ++ ((toWord ε.num ++ [ε.den]) ++ toWord G) = _
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ε.num = Int.ofNat m :=
    ⟨ε.num.natAbs, (Int.natAbs_of_nonneg hnum.le).symm⟩
  rw [hm]
  simp [word_simps]

/-- The length of the chain, in terms of the entries `r` and the
denominator of `ε`. -/
theorem length_le_of_rat {A r L : ℕ} {ε : ℚ} (hε : 0 < ε) (h : (L : ℚ) ≤ A * r / ε + A) :
    L ≤ A * (r * ε.den + 1) := by
  have hnum : (1 : ℚ) ≤ ε.num := by exact_mod_cast Rat.num_pos.mpr hε
  have hden : (0 : ℚ) < ε.den := by exact_mod_cast ε.den_pos
  have hε' : (1 : ℚ) / ε.den ≤ ε :=
    calc (1 : ℚ) / ε.den ≤ ε.num / ε.den := div_le_div_of_nonneg_right hnum hden.le
      _ = ε := Rat.num_div_den ε
  have : (r : ℚ) / ε ≤ r * ε.den := by
    rw [div_le_iff₀ hε]
    calc (r : ℚ) = r * ε.den * (1 / ε.den) := by field_simp
      _ ≤ r * ε.den * ε := by gcongr
  have h2 : (L : ℚ) ≤ A * (r * ε.den + 1) := by
    calc (L : ℚ) ≤ A * r / ε + A := h
      _ = A * (r / ε) + A := by ring
      _ ≤ A * (r * ε.den) + A := by gcongr
      _ = A * (r * ε.den + 1) := by ring
  exact_mod_cast h2

set_option maxHeartbeats 1600000 in
/-- The statement for the graph classes of the archive, their monadic
dependence and the older `Lax185574.Computing.Computes`.

Compute the decreasing sequence of the companion paper's chain theorem
and reverse it. Reversal turns `V = B₀ ⊇ ⋯ ⊇ B_m = ∅` into a chain
`∅ = S₁ ⊆ ⋯ ⊆ S_m = V` of the same length, and the radius-`r` width of
the chain is the largest number of atomic types over `B_{i−1}` met by a
ball in the metric of `B_i`-flips, which the chain theorem bounds. The
reversal takes time linear in the output of the chain program.
-/
theorem exists_program_chain_old :
    ∃ (p : Program) (e A : ℕ)
      (S : ∀ n : ℕ, ℕ → ℚ → SimpleGraph (Fin n) → List (Finset (Fin n))),
      (∀ (n r : ℕ) (ε : ℚ) (G : SimpleGraph (Fin n)), 1 ≤ r → 0 < ε →
        IsChain (S n r ε G) ∧ ((S n r ε G).length : ℚ) ≤ A * r / ε + A) ∧
      ∀ (C : GraphClass), MonadicallyDependent C → ∀ (r : ℕ) (ε : ℚ), 1 ≤ r → 0 < ε →
        ∀ δ : ℝ, 0 < δ → ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
          (chainWidth G r (S n r ε G) : ℝ) ≤ c * ((n : ℝ) + 1) ^ (ε : ℝ) ∧
          Computes p e c (r, ε, G) (S n r ε G)
            (fun _ => ⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + δ)⌋₊) := by
  obtain ⟨p₀, e₀, A, B, hB, hclass⟩ :=
    Lax185574Proofs.Shim.ChainTheorem.exists_program_decreasingChain
  obtain ⟨pR, eR, cR, hR⟩ := exists_program_reverse
  obtain ⟨p, K, hpipe⟩ := pipe p₀ pR ρId ρOut
  refine ⟨p, e₀ + 3 * eR + 4, A, fun n r ε G => (B n r ε G).reverse, fun n r ε G hr hε => ?_, ?_⟩
  · obtain ⟨hdec, hlen⟩ := hB n r ε G hr hε
    exact ⟨isChain_reverse hdec, by simpa using hlen⟩
  intro C hC r ε hr hε δ hδ
  obtain ⟨cδ, hcδ⟩ := hclass C hC r ε hr hε δ hδ
  obtain ⟨c₁, hc₁⟩ := hclass C hC r ε hr hε 1 one_pos
  set Mr := A * (r * ε.den + 1)
  set c := 4 * (cδ + c₁ + cR * (12 * (Mr + 1)) ^ eR + 3 * cR * (Mr + 1) + 8 * (Mr + 1) + K + 4) +
    K * (cδ + 3 * cR * (Mr + 1) + 6) with hc
  refine ⟨c, fun n G hG => ⟨?_, ?_⟩⟩
  · refine (chainWidth_reverse_le G r (by positivity) (hcδ n G hG).1).trans ?_
    gcongr
    exact_mod_cast (show cδ ≤ c by omega)
  intro w hadm
  set e := e₀ + 3 * eR + 4
  set x := toWord (r, ε, G)
  set Bl := B n r ε G
  set y := toWord Bl
  have hx : x = r :: 0 :: ε.num.natAbs :: ε.den :: toWord G := toWord_input r hε G
  have hxne : x ≠ [] := by rw [hx]; simp
  have hLx : n + 5 ≤ x.length := by
    rw [hx]; simp only [List.length_cons]; have := toWord_graph_length_ge G; omega
  -- the admissibility at the largest entry
  set Mx := maxEntry x
  set A' := x.length + Mx + 1
  have hA1 : 1 ≤ A' := by omega
  have hcA : c * A' ^ e ≤ 2 ^ w := hadm Mx (maxEntry_mem hxne)
  set W := 2 ^ (w - 2)
  have hw2 : 2 ≤ w := by
    by_contra hlt
    have h1 : 2 ^ w ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : c ≤ c * A' ^ e := Nat.le_mul_of_pos_right _ (pow_pos hA1 _)
    omega
  have h2w : 2 ^ w = 4 * W := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  rw [h2w] at hcA
  have sm : ∀ k j, 4 * k ≤ c → j ≤ e → k * A' ^ j ≤ W := by
    intro k j hk hj
    have h1 : A' ^ j ≤ A' ^ e := Nat.pow_le_pow_right hA1 hj
    have h2 : 4 * (k * A' ^ j) ≤ c * A' ^ e := by
      calc 4 * (k * A' ^ j) = (4 * k) * A' ^ j := by ring
        _ ≤ c * A' ^ e := Nat.mul_le_mul hk h1
    omega
  have hrx : r ≤ Mx := le_maxEntry (by rw [hx]; simp)
  have hdx : ε.den ≤ Mx := le_maxEntry (by rw [hx]; simp)
  have hnA : n + 1 ≤ A' := by omega
  -- the chain program halts, at its instance `δ = 1`
  have hadm₀ : ∀ c' : ℕ, 4 * c' ≤ c → ∀ v ∈ x, c' * (x.length + v + 1) ^ e₀ ≤ 2 ^ (w - 2) := by
    intro c' hc' v hv
    have := hadm v hv
    rw [h2w] at this
    have h1 : (x.length + v + 1) ^ e₀ ≤ (x.length + v + 1) ^ e :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have h2 : 4 * (c' * (x.length + v + 1) ^ e₀) ≤ c * (x.length + v + 1) ^ e := by
      calc 4 * (c' * (x.length + v + 1) ^ e₀) = (4 * c') * (x.length + v + 1) ^ e₀ := by ring
        _ ≤ c * (x.length + v + 1) ^ e := Nat.mul_le_mul hc' h1
    omega
  have hT₁ : ⌊(c₁ : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + 1)⌋₊ ≤ W := by
    have h4 : ((n : ℝ) + 1) ^ ((3 : ℝ) + 1) = ((n + 1 : ℕ) : ℝ) ^ (4 : ℕ) := by
      rw [show (3 : ℝ) + 1 = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; push_cast; ring
    rw [h4, ← Nat.cast_pow, ← Nat.cast_mul, Nat.floor_natCast]
    calc c₁ * (n + 1) ^ 4 ≤ c₁ * A' ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnA _)
      _ ≤ W := sm c₁ 4 (by omega) (by omega)
  obtain ⟨t₀, ht₀, hrun₀⟩ := ((hc₁ n G hG).2 (w - 2) (hadm₀ c₁ (by omega))).2 hT₁ x rfl
  -- the sizes of the chain
  have hBlen : Bl.length ≤ Mr := length_le_of_rat hε (hB n r ε G hr hε).2
  have hy : y = Bl.length :: blocksWord (Bl.map setBlock) := toWord_setList Bl
  have hblocks : ∀ u ∈ Bl.map setBlock, u.length ≤ 2 * n := by
    intro u hu
    simp only [List.mem_map] at hu
    obtain ⟨S, -, rfl⟩ := hu
    rw [setBlock_length]
    have : (Finset.words S).length ≤ n := by
      simp only [Finset.words, Finset.length_sort]
      exact Finset.card_image_le.trans ((Finset.card_le_univ _).trans (by simp))
    omega
  have hbw : ∀ bs : List (List ℕ), (∀ u ∈ bs, u.length ≤ 2 * n) →
      (blocksWord bs).length ≤ bs.length * (2 * n + 1) := by
    intro bs
    induction bs with
    | nil => intro _; simp [blocksWord]
    | cons u bs ih =>
        intro h
        rw [blocksWord_cons, List.length_append, List.length_cons]
        have := ih (fun v hv => h v (List.mem_cons_of_mem _ hv))
        have := h u List.mem_cons_self
        simp only [blk, List.length_cons]
        nlinarith
  have hylen : y.length ≤ (Mr + 1) * (2 * n + 1) := by
    have := hbw _ hblocks
    rw [List.length_map] at this
    rw [hy, List.length_cons]
    nlinarith
  have hyent : ∀ v ∈ y, v ≤ Mr + n := by
    intro v hv
    rw [hy] at hv
    rcases List.mem_cons.mp hv with rfl | hv
    · omega
    · simp only [blocksWord, List.map_map, List.mem_flatten, List.mem_map, Function.comp] at hv
      obtain ⟨_, ⟨S, -, rfl⟩, hvu⟩ := hv
      rcases List.mem_cons.mp hvu with rfl | hvu
      · have : (Finset.words S).length ≤ n := by
          simp only [Finset.words, Finset.length_sort]
          exact Finset.card_image_le.trans ((Finset.card_le_univ _).trans (by simp))
        rw [setBlock_length]; omega
      · simp only [setBlock, List.mem_flatten, List.mem_map] at hvu
        obtain ⟨_, ⟨u, hu, rfl⟩, hvu⟩ := hvu
        simp only [Finset.words, Finset.mem_sort, Finset.mem_image] at hu
        obtain ⟨a, -, rfl⟩ := hu
        change v ∈ [1, a.val] at hvu
        simp at hvu
        have := a.isLt
        omega
  -- the reversal halts
  have hy3 : y.length + Mr + n + 1 ≤ 3 * (Mr + 1) * (n + 1) := by nlinarith
  have hadmR : WordAdmissible eR cR (w - 2) y := by
    intro v hv
    have h1 : y.length + v + 1 ≤ 12 * (Mr + 1) * A' := by
      have := hyent v hv
      have : 3 * (Mr + 1) * (n + 1) ≤ 12 * (Mr + 1) * A' := by nlinarith
      omega
    calc cR * (y.length + v + 1) ^ eR ≤ cR * (12 * (Mr + 1) * A') ^ eR := by gcongr
      _ = cR * (12 * (Mr + 1)) ^ eR * A' ^ eR := by rw [mul_pow]; ring
      _ ≤ W := sm _ _ (by omega) (by omega)
  have hTR : cR * (wordLength Bl + 1) ≤ W := by
    have h1 : wordLength Bl + 1 ≤ 3 * (Mr + 1) * A' := by
      have : wordLength Bl = y.length := rfl
      have : 3 * (Mr + 1) * (n + 1) ≤ 3 * (Mr + 1) * A' := Nat.mul_le_mul_left _ hnA
      omega
    calc cR * (wordLength Bl + 1) ≤ cR * (3 * (Mr + 1) * A') := Nat.mul_le_mul_left _ h1
      _ = (3 * cR * (Mr + 1)) * A' ^ 1 := by ring
      _ ≤ W := sm _ _ (by omega) (by omega)
  obtain ⟨tR, htR, hrunR⟩ := ((hR n Bl) (w - 2) hadmR).2 hTR y rfl
  -- the pipe
  have hylW : y.length < W := by
    have : 3 * (Mr + 1) * (n + 1) ≤ 3 * (Mr + 1) * A' := Nat.mul_le_mul_left _ hnA
    have := sm (3 * (Mr + 1)) 1 (by omega) (by omega)
    rw [pow_one] at this
    omega
  have hxW : x.length < W := by
    have := sm 1 1 (by omega) (by omega)
    rw [pow_one, one_mul] at this
    omega
  have hKW : K ≤ W := by have := sm K 0 (by omega) (by omega); simpa using this
  have hrun₀' : RunsTo (w - 2) p₀ (ρId.apply fun _ => x) y t₀ := by rw [ρId_apply]; exact hrun₀
  have hrunR' : RunsTo (w - 2) pR (ρOut.apply ![y, x]) (toWord Bl.reverse) tR := by
    rw [ρOut_apply]; exact hrunR
  obtain ⟨t, ht, hrun⟩ := hpipe w x y (toWord Bl.reverse) t₀ tR hKW hylW
    (ρId_fits (by rw [h2w]; omega)) (ρOut_fits (by rw [h2w]; omega) (by rw [h2w]; omega))
    hrun₀' hrunR'
  rw [ρId_cost, ρOut_cost] at ht
  refine ⟨fun y' t' h => (Lax808846Proofs.Machine.runsTo_unique h hrun).1, fun hT y' hy' => ?_⟩
  rw [Set.mem_singleton_iff] at hy'
  subst hy'
  refine ⟨t, ?_, hrun⟩
  -- the time bound
  set P : ℝ := ((n : ℝ) + 1) ^ ((3 : ℝ) + δ)
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hnP : (n : ℝ) + 1 ≤ P := by
    calc (n : ℝ) + 1 = ((n : ℝ) + 1) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ P := Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hP0 : 0 ≤ P := by linarith
  have hTδ : ⌊(cδ : ℝ) * P⌋₊ ≤ W := by
    have h1 : 4 * ⌊(cδ : ℝ) * P⌋₊ ≤ ⌊(c : ℝ) * P⌋₊ := by
      apply Nat.le_floor
      push_cast
      have := Nat.floor_le (show (0 : ℝ) ≤ cδ * P by positivity)
      have hc4 : (4 * cδ : ℝ) ≤ c := by exact_mod_cast (show 4 * cδ ≤ c by omega)
      nlinarith
    have : ⌊(c : ℝ) * P⌋₊ ≤ 4 * W := by rw [← h2w]; exact hT
    omega
  obtain ⟨t₀', ht₀', hrun₀''⟩ := ((hcδ n G hG).2 (w - 2) (hadm₀ cδ (by omega))).2 hTδ x rfl
  have ht0 : t₀ ≤ ⌊(cδ : ℝ) * P⌋₊ := by
    have := (Lax808846Proofs.Machine.runsTo_unique hrun₀ hrun₀'').2
    rw [this]; exact ht₀'
  have htR' : tR ≤ 3 * cR * (Mr + 1) * (n + 1) := by
    have h1 : wordLength Bl + 1 ≤ 3 * (Mr + 1) * (n + 1) := by
      have : wordLength Bl = y.length := rfl
      omega
    calc tR ≤ cR * (wordLength Bl + 1) := htR
      _ ≤ cR * (3 * (Mr + 1) * (n + 1)) := Nat.mul_le_mul_left _ h1
      _ = 3 * cR * (Mr + 1) * (n + 1) := by ring
  apply Nat.le_floor
  have h1 : (t : ℝ) ≤ K * (⌊(cδ : ℝ) * P⌋₊ + 3 * cR * (Mr + 1) * (n + 1) + 6) := by
    have : t ≤ K * (⌊(cδ : ℝ) * P⌋₊ + 3 * cR * (Mr + 1) * (n + 1) + 6) := by
      refine ht.trans (Nat.mul_le_mul_left _ ?_)
      omega
    exact_mod_cast this
  have h2 : (⌊(cδ : ℝ) * P⌋₊ : ℝ) ≤ cδ * P := Nat.floor_le (by positivity)
  have h3 : ((n : ℕ) : ℝ) + 1 ≤ P := hnP
  have hcK : ((K * (cδ + 3 * cR * (Mr + 1) + 6) : ℕ) : ℝ) ≤ c := by
    exact_mod_cast (show K * (cδ + 3 * cR * (Mr + 1) + 6) ≤ c by omega)
  push_cast at h1 hcK ⊢
  have hP1 : 1 ≤ P := le_trans hn1 hnP
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  have hX : (3 * (cR : ℝ) * (Mr + 1)) * ((n : ℝ) + 1) ≤ (3 * (cR : ℝ) * (Mr + 1)) * P :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have hY : (K : ℝ) * (⌊(cδ : ℝ) * P⌋₊ + 3 * cR * (Mr + 1) * (n + 1) + 6) ≤
      K * (cδ + 3 * cR * (Mr + 1) + 6) * P := by
    have : (⌊(cδ : ℝ) * P⌋₊ : ℝ) + 3 * cR * (Mr + 1) * (n + 1) + 6 ≤
        (cδ + 3 * cR * (Mr + 1) + 6) * P := by nlinarith
    calc (K : ℝ) * (⌊(cδ : ℝ) * P⌋₊ + 3 * cR * (Mr + 1) * (n + 1) + 6)
        ≤ K * ((cδ + 3 * cR * (Mr + 1) + 6) * P) := mul_le_mul_of_nonneg_left this hK0
      _ = K * (cδ + 3 * cR * (Mr + 1) + 6) * P := by ring
  calc (t : ℝ) ≤ _ := h1
    _ ≤ K * (cδ + 3 * cR * (Mr + 1) + 6) * P := hY
    _ ≤ c * P := mul_le_mul_of_nonneg_right hcK hP0

open Lax185574.Graphs Lax185574.Algorithms Lax185574Proofs.Interface
open Lax185574Proofs.Interface.KitG3

/--
---
conclusion: Lax185574.ComputingChains.exists_program_chain
---
The statement for graphs, graph classes and `Algorithm.Computes`, from
the version for simple graphs applied to the class of the simple graphs
of the members. The algorithm is the program with its exponent, the
chain of a graph is that of its simple graph, and the constant `c`
becomes `⌈c · 2^(3+δ)⌉`, so that `c' · n^(3+δ) + c'` bounds the time `⌊c · (n+1)^(3+δ)⌋`.
-/
theorem exists_program_chain :
    ∃ (A : Algorithm) (K : ℕ) (chain : ℕ → ℚ → (G : Graph) → List (Finset (Fin G.n))),
      (∀ (r : ℕ) (ε : ℚ) (G : Graph), 1 ≤ r → 0 < ε →
        IsChain (chain r ε G) ∧ ((chain r ε G).length : ℚ) ≤ K * r / ε + K) ∧
      ∀ C : Lax185574.Graphs.GraphClass, Lax185574.MonadicDependence.MonadicallyDependent C →
        ∀ (r : ℕ) (ε : ℚ), 1 ≤ r → 0 < ε →
        ∀ δ : ℝ, 0 < δ → ∃ c : ℕ, ∀ G ∈ C,
          (chainWidth G.toSimpleGraph r (chain r ε G) : ℝ) ≤ c * ((G.n : ℝ) + 1) ^ (ε : ℝ) ∧
          A.Computes c (r, ε, G) (chain r ε G) ((G.n : ℝ) ^ (3 + δ)) := by
  obtain ⟨p, e, K, S, hS, hcl⟩ := exists_program_chain_old
  refine ⟨⟨p, e⟩, K, fun r ε G => S G.n r ε G.toSimpleGraph,
    fun r ε G hr hε => hS G.n r ε G.toSimpleGraph hr hε, fun C hC r ε hr hε δ hδ => ?_⟩
  obtain ⟨c, hc⟩ := hcl (toOld C) (monadicallyDependent_toOld hC) r ε hr hε δ hδ
  have hx : (0 : ℝ) ≤ 3 + δ := by linarith
  have hcc := le_ceil_mul_two_rpow c hx
  refine ⟨⌈(c : ℝ) * 2 ^ ((3 : ℝ) + δ)⌉₊, fun G hG => ?_⟩
  obtain ⟨h1, h2⟩ := hc G.n G.toSimpleGraph hG
  refine ⟨h1.trans ?_, computes_congr (encode_triple_graph r ε G).symm rfl
    (computes_of_old hcc (floor_rpow_le c G.n hx) h2)⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcc) (by positivity)

end Lax185574Proofs.ComputingChains
