import Lax185574Proofs.Chain.Algorithm
import Lax185574Proofs.Chain.TypeGrowth

/-!
The combinatorial part of the chain theorem of the companion paper
(Theorem 4.4): an explicit function `chainB` that produces, for `r ≥ 1`,
rational `ε > 0` and every graph, a decreasing chain of length at most
`2 r/ε + 2`, such that on the members of a monadically dependent class
every radius-`r` flip-metric ball of `B_{i}` meets at most `c (n+1)^ε`
atomic types over `B_{i-1}`.

The width bound of `chainAlg_ball` is `γ₁ · m · (200 (q+1)(α+1)K²)^r`.
Here `(q+1)^r ≤ 3^r n^{ε/2}` and `m ≤ 2 + 2r/ε`, while `γ₁`, `α` and `K`
are subpolynomial on the class: `γ₁` and the growth ratio of
`(r+1)`-types by `exists_typeGrowth`, and `α` and the packing bound are
polynomial in `γ₁` and `log₂ n`.
-/

set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain

open Finset
open Lax199508.GraphClasses Lax710763.MonadicDependence

/-- **The chain of the companion paper's Theorem 4.4.** -/
noncomputable def chainB (n r : ℕ) (ε : ℚ) (G : SimpleGraph (Fin n)) : List (Finset (Fin n)) :=
  @chainAlg (Fin n) _ _ _ G (Classical.decRel _) r ε

/-! ### Subpolynomial bounds on a class -/

/-- `f` is bounded by `c (n+1)^η` on `C`, for every `η > 0`. -/
def SubpolyOn (C : GraphClass) (f : ∀ n : ℕ, SimpleGraph (Fin n) → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ c : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
    f n G ≤ c * ((n : ℝ) + 1) ^ η

section Subpoly

variable {C : GraphClass} {f g : ∀ n : ℕ, SimpleGraph (Fin n) → ℝ}

theorem one_le_rpow_succ (n : ℕ) {η : ℝ} (hη : 0 ≤ η) : 1 ≤ ((n : ℝ) + 1) ^ η :=
  Real.one_le_rpow (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]) hη

theorem SubpolyOn.mono (hg : SubpolyOn C g) (h : ∀ n G, C n G → f n G ≤ g n G) :
    SubpolyOn C f := fun η hη => by
  obtain ⟨c, hc⟩ := hg η hη
  exact ⟨c, fun n G hG => (h n G hG).trans (hc n G hG)⟩

theorem SubpolyOn.const (a : ℝ) : SubpolyOn C (fun _ _ => a) := fun _ hη =>
  ⟨max a 0, fun n _ _ => (le_max_left a 0).trans
    (le_mul_of_one_le_right (le_max_right _ _) (one_le_rpow_succ n hη.le))⟩

theorem SubpolyOn.add (hf : SubpolyOn C f) (hg : SubpolyOn C g) :
    SubpolyOn C (fun n G => f n G + g n G) := fun η hη => by
  obtain ⟨c1, h1⟩ := hf η hη
  obtain ⟨c2, h2⟩ := hg η hη
  exact ⟨c1 + c2, fun n G hG => by have := h1 n G hG; have := h2 n G hG; linarith⟩

theorem SubpolyOn.mul (hf : SubpolyOn C f) (hg : SubpolyOn C g)
    (hf0 : ∀ n G, C n G → 0 ≤ f n G) (hg0 : ∀ n G, C n G → 0 ≤ g n G) :
    SubpolyOn C (fun n G => f n G * g n G) := fun η hη => by
  obtain ⟨c1, h1⟩ := hf (η / 2) (by linarith)
  obtain ⟨c2, h2⟩ := hg (η / 2) (by linarith)
  refine ⟨c1 * c2, fun n G hG => ?_⟩
  have hn : (0 : ℝ) ≤ (n : ℝ) + 1 := by positivity
  calc f n G * g n G ≤ (c1 * ((n : ℝ) + 1) ^ (η / 2)) * (c2 * ((n : ℝ) + 1) ^ (η / 2)) :=
        mul_le_mul (h1 n G hG) (h2 n G hG) (hg0 n G hG) ((hf0 n G hG).trans (h1 n G hG))
    _ = c1 * c2 * (((n : ℝ) + 1) ^ (η / 2) * ((n : ℝ) + 1) ^ (η / 2)) := by ring
    _ = c1 * c2 * ((n : ℝ) + 1) ^ η := by
        rw [← Real.rpow_add (by positivity)]; ring_nf

theorem SubpolyOn.pow (hf : SubpolyOn C f) (hf0 : ∀ n G, C n G → 0 ≤ f n G) (k : ℕ) :
    SubpolyOn C (fun n G => f n G ^ k) := by
  induction k with
  | zero => simpa using SubpolyOn.const (C := C) 1
  | succ k ih =>
    simp only [pow_succ]
    exact ih.mul hf (fun n G hG => pow_nonneg (hf0 n G hG) k) hf0

/-- `log₂ n + 1` is subpolynomial. -/
theorem subpolyOn_log : SubpolyOn C (fun n _ => ((Nat.log 2 n : ℕ) : ℝ) + 1) := by
  refine SubpolyOn.add ?_ (SubpolyOn.const 1)
  intro η hη
  refine ⟨1 / (η * Real.log 2), fun n _ _ => ?_⟩
  set k := Nat.log 2 n
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h2k : ((2 : ℝ) ^ k) ≤ (n : ℝ) + 1 := by
    have : 2 ^ k ≤ n + 1 := by
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [k, h]
      · exact (Nat.pow_log_le_self 2 (by omega)).trans (by omega)
    exact_mod_cast this
  have hl := Real.log_le_rpow_div (x := (2 : ℝ) ^ k) (by positivity) hη
  rw [Real.log_pow] at hl
  have hmono : ((2 : ℝ) ^ k) ^ η ≤ ((n : ℝ) + 1) ^ η :=
    Real.rpow_le_rpow (by positivity) h2k hη.le
  have h1 : (k : ℝ) * Real.log 2 ≤ ((n : ℝ) + 1) ^ η / η :=
    hl.trans (div_le_div_of_nonneg_right hmono hη.le)
  show (k : ℝ) ≤ 1 / (η * Real.log 2) * ((n : ℝ) + 1) ^ η
  calc (k : ℝ) = (k : ℝ) * Real.log 2 / Real.log 2 := by field_simp
    _ ≤ (((n : ℝ) + 1) ^ η / η) / Real.log 2 := div_le_div_of_nonneg_right h1 hlog2.le
    _ = 1 / (η * Real.log 2) * ((n : ℝ) + 1) ^ η := by field_simp

end Subpoly

/-! ### The growth ratios are subpolynomial -/

section Growth

/-- The growth ratio of `(k+1)`-types is subpolynomial on a monadically
dependent class. -/
theorem subpolyOn_growth (C : GraphClass) (hC : MonadicallyDependent C) (k : ℕ) :
    SubpolyOn C (fun n G => (@growth (Fin n) _ _
      (fun B => @tpRel (Fin n) _ _ G (Classical.decRel _) B k) : ℝ)) := by
  intro η hη
  obtain ⟨c, hc0, hc⟩ := exists_typeGrowth C hC k η hη
  refine ⟨c + 1, fun n G hG => ?_⟩
  let _ := Classical.decRel G.Adj
  set g := ⌈c * ((n : ℝ) + 1) ^ η⌉₊
  have hgrowth : growth (fun B => tpRel G B k) ≤ g := by
    refine growth_le fun A hA => ?_
    have h := hc n G hG A hA
    have ha : (0 : ℝ) < A.card := by exact_mod_cast card_pos.2 hA
    have han : (A.card : ℝ) ≤ (n : ℝ) + 1 := by
      have := card_le_univ A; simp at this; exact_mod_cast this.trans (Nat.le_succ n)
    have hpow : (A.card : ℝ) ^ (1 + η) ≤ (A.card : ℝ) * ((n : ℝ) + 1) ^ η := by
      rw [Real.rpow_add ha, Real.rpow_one]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow ha.le han hη.le) ha.le
    have : (numCls (tpRel G A k) univ : ℝ) ≤ (g : ℝ) * A.card := by
      calc (numCls (tpRel G A k) univ : ℝ) ≤ c * (A.card : ℝ) ^ (1 + η) := h
        _ ≤ c * ((A.card : ℝ) * ((n : ℝ) + 1) ^ η) := mul_le_mul_of_nonneg_left hpow hc0
        _ = (c * ((n : ℝ) + 1) ^ η) * A.card := by ring
        _ ≤ (g : ℝ) * A.card := mul_le_mul_of_nonneg_right (Nat.le_ceil _) ha.le
    exact_mod_cast this
  have h1 : (growth (fun B => tpRel G B k) : ℝ) ≤ c * ((n : ℝ) + 1) ^ η + 1 := by
    calc (growth (fun B => tpRel G B k) : ℝ) ≤ g := by exact_mod_cast hgrowth
      _ ≤ c * ((n : ℝ) + 1) ^ η + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have h2 := one_le_rpow_succ n hη.le
  calc _ ≤ c * ((n : ℝ) + 1) ^ η + 1 := h1
    _ ≤ (c + 1) * ((n : ℝ) + 1) ^ η := by nlinarith

end Growth

/-! ### `q` -/

theorem q_add_one_pow_le {n r : ℕ} (hr : 1 ≤ r) {ε : ℚ} (hn : 2 ≤ n) (hε : 0 < ε) :
    ((qOf n r ε : ℝ) + 1) ^ r ≤ 3 ^ r * ((n : ℝ) + 1) ^ ((ε : ℝ) / 2) := by
  obtain ⟨hq2, -, hq3, -⟩ := qOf_spec (r := r) hn hε
  set q := qOf n r ε
  set a := ε.num.natAbs
  set b := ε.den
  have hapos : 0 < (ε.num : ℝ) := by exact_mod_cast Rat.num_pos.2 hε
  have ha : (a : ℝ) = ε.num := by
    simp only [a, Nat.cast_natAbs]; push_cast; exact abs_of_pos hapos
  have hbpos : (0 : ℝ) < b := by exact_mod_cast ε.den_pos
  have hεab : (ε : ℝ) = a / b := by
    rw [ha]; exact_mod_cast (Rat.num_div_den ε).symm
  set N := 2 * r * b
  have hN : N ≠ 0 := by simp only [N]; positivity
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  -- `q - 1 ≤ n^{ε/2r}`
  have hq1 : ((q - 1 : ℕ) : ℝ) ≤ (n : ℝ) ^ ((a : ℝ) / N) := by
    have h : (((q - 1 : ℕ) : ℝ)) ^ N ≤ (n : ℝ) ^ a := by exact_mod_cast hq3
    have := Real.rpow_le_rpow (by positivity) h (show (0 : ℝ) ≤ (N : ℝ)⁻¹ by positivity)
    rw [Real.pow_rpow_inv_natCast (by positivity) hN, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)] at this
    simpa [div_eq_mul_inv] using this
  have hexp : (a : ℝ) / N = (ε : ℝ) / 2 / r := by
    rw [hεab]; simp only [N]; push_cast; field_simp
  rw [hexp] at hq1
  have hcast : ((q - 1 : ℕ) : ℝ) = q - 1 := by rw [Nat.cast_sub (by omega)]; simp
  rw [hcast] at hq1
  set y := ((n : ℝ) + 1) ^ ((ε : ℝ) / 2 / r)
  have hy1 : 1 ≤ y := one_le_rpow_succ n (by positivity)
  have hny : (n : ℝ) ^ ((ε : ℝ) / 2 / r) ≤ y :=
    Real.rpow_le_rpow (by positivity) (by linarith) (by positivity)
  have hqy : (q : ℝ) + 1 ≤ 3 * y := by linarith
  have hyr : y ^ r = ((n : ℝ) + 1) ^ ((ε : ℝ) / 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
    congr 1; field_simp
  calc ((q : ℝ) + 1) ^ r ≤ (3 * y) ^ r := pow_le_pow_left₀ (by positivity) hqy r
    _ = 3 ^ r * ((n : ℝ) + 1) ^ ((ε : ℝ) / 2) := by rw [mul_pow, hyr]

/-! ### The theorem -/

/-- **Part (a) of the chain theorem.** The chain `chainB` is decreasing
and has at most `2r/ε + 2` sets, and on a monadically dependent class its
radius-`r` balls meet at most `c (n+1)^ε` atomic types. -/
theorem chainB_spec :
    (∀ (n r : ℕ) (ε : ℚ) (G : SimpleGraph (Fin n)), 1 ≤ r → 0 < ε →
      Lax185574.ChainTheorem.IsDecreasingChain (chainB n r ε G) ∧
        ((chainB n r ε G).length : ℚ) ≤ (2 : ℕ) * r / ε + (2 : ℕ)) ∧
    ∀ (C : GraphClass), MonadicallyDependent C → ∀ (r : ℕ) (ε : ℚ), 1 ≤ r → 0 < ε →
      ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)), C n G →
        Lax185574.ChainTheorem.BallsMeetFewTypes G r (c * ((n : ℝ) + 1) ^ (ε : ℝ))
          (chainB n r ε G) := by
  refine ⟨fun n r ε G hr hε => ?_, fun C hC r ε hr hε => ?_⟩
  · let _ := Classical.decRel G.Adj
    refine ⟨chainAlg_isDecreasingChain r hε, ?_⟩
    have := chainAlg_length (G := G) (r := r) hε
    push_cast; exact this
  -- the subpolynomial part of the bound
  have he : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  set e : ℝ := (ε : ℝ)
  have hγ1 := subpolyOn_growth C hC 0
  have hγr := subpolyOn_growth C hC r
  have hL := subpolyOn_log (C := C)
  let γ1f : ∀ n : ℕ, SimpleGraph (Fin n) → ℝ := fun n G =>
    (@growth (Fin n) _ _ (fun B => @tpRel (Fin n) _ _ G (Classical.decRel _) B 0) : ℝ)
  let γrf : ∀ n : ℕ, SimpleGraph (Fin n) → ℝ := fun n G =>
    (@growth (Fin n) _ _ (fun B => @tpRel (Fin n) _ _ G (Classical.decRel _) B r) : ℝ)
  let Lf : ∀ n : ℕ, SimpleGraph (Fin n) → ℝ := fun n _ => ((Nat.log 2 n : ℕ) : ℝ) + 1
  have h0γ1 : ∀ n G, C n G → 0 ≤ γ1f n G := fun _ _ _ => Nat.cast_nonneg _
  have h0γr : ∀ n G, C n G → 0 ≤ γrf n G := fun _ _ _ => Nat.cast_nonneg _
  have h0L : ∀ n G, C n G → 0 ≤ Lf n G := fun _ _ _ => by positivity
  -- `α + 1 ≤ 2 (4 γ₁ L + 1) L + 3` and `K ≤ γ_r + 4 γ₁ L + 1`
  let αf : ∀ n : ℕ, SimpleGraph (Fin n) → ℝ := fun n G =>
    2 * ((4 * γ1f n G * Lf n G + 1) * Lf n G) + 3
  let Kf : ∀ n : ℕ, SimpleGraph (Fin n) → ℝ := fun n G => γrf n G + 4 * γ1f n G * Lf n G + 1
  have hγ1L : SubpolyOn C (fun n G => γ1f n G * Lf n G) := hγ1.mul hL h0γ1 h0L
  have hαf : SubpolyOn C αf := by
    refine SubpolyOn.add (SubpolyOn.mul (SubpolyOn.const 2) ?_ (fun _ _ _ => by norm_num)
      (fun n G hG => by positivity)) (SubpolyOn.const 3)
    refine SubpolyOn.mul (SubpolyOn.add ?_ (SubpolyOn.const 1)) hL
      (fun n G hG => by positivity) h0L
    have := (SubpolyOn.const (C := C) 4).mul hγ1L (fun _ _ _ => by norm_num)
      (fun n G hG => mul_nonneg (h0γ1 n G hG) (h0L n G hG))
    refine this.mono fun n G _ => le_of_eq ?_
    ring
  have hKf : SubpolyOn C Kf := by
    refine SubpolyOn.add (SubpolyOn.add hγr ?_) (SubpolyOn.const 1)
    have := (SubpolyOn.const (C := C) 4).mul hγ1L (fun _ _ _ => by norm_num)
      (fun n G hG => mul_nonneg (h0γ1 n G hG) (h0L n G hG))
    refine this.mono fun n G _ => le_of_eq ?_
    ring
  have h0α : ∀ n G, C n G → 0 ≤ αf n G := fun n G hG => by positivity
  have h0K : ∀ n G, C n G → 0 ≤ Kf n G := fun n G hG => by positivity
  have hS : SubpolyOn C (fun n G => γ1f n G * (αf n G ^ r * Kf n G ^ (2 * r))) :=
    hγ1.mul ((hαf.pow h0α r).mul (hKf.pow h0K (2 * r)) (fun n G hG => pow_nonneg (h0α n G hG) _)
      (fun n G hG => pow_nonneg (h0K n G hG) _)) h0γ1
      (fun n G hG => mul_nonneg (pow_nonneg (h0α n G hG) _) (pow_nonneg (h0K n G hG) _))
  obtain ⟨cS, hcS⟩ := hS (e / 2) (by positivity)
  set D : ℝ := (2 * r / e + 2) * 200 ^ r * 3 ^ r * max cS 0
  refine ⟨⌈D⌉₊ + 1, fun n G hG => ?_⟩
  let _ := Classical.decRel G.Adj
  show Lax185574.ChainTheorem.BallsMeetFewTypes G r _ (chainAlg G r ε)
  intro t ht u
  have hD : D ≤ (⌈D⌉₊ + 1 : ℕ) := by push_cast; linarith [Nat.le_ceil D]
  have hc1 : (1 : ℝ) ≤ ((⌈D⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast; linarith [(Nat.cast_nonneg ⌈D⌉₊ : (0 : ℝ) ≤ _)]
  have hpowe : 1 ≤ ((n : ℝ) + 1) ^ e := one_le_rpow_succ n he.le
  rcases Nat.lt_or_ge n 2 with hn | hn
  · -- at most one vertex: the ball has at most one vertex
    have hcount : Lax185574.Partitions.partCount
        (Lax185574.Partitions.atomicTypes G ((chainAlg G r ε)[t] : Set (Fin n)))
        (Lax185574.Flips.flipBall G
          (Lax185574.Partitions.atomicTypes G ((chainAlg G r ε)[t + 1] : Set (Fin n))) r u) ≤ 1 := by
      unfold Lax185574.Partitions.partCount
      refine (Set.ncard_image_le (Set.toFinite _)).trans ?_
      refine (Set.ncard_le_ncard (Set.subset_univ _)).trans ?_
      rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]; omega
    calc (Lax185574.Partitions.partCount _ _ : ℝ) ≤ 1 := by exact_mod_cast hcount
      _ ≤ ((⌈D⌉₊ + 1 : ℕ) : ℝ) * ((n : ℝ) + 1) ^ e := by nlinarith
  -- the per-graph bound
  have hball := chainAlg_ball (G := G) hr hε (by rw [Fintype.card_fin]; exact hn) t ht u
  rw [Fintype.card_fin] at hball
  have hlen := chainAlg_length (G := G) (r := r) hε
  have hq := q_add_one_pow_le (n := n) hr hn hε
  set γ1 := growth (fun B => tpRel G B 0)
  set γr := growth (fun B => tpRel G B r)
  set α := alternation G (welzlOrder G)
  set q := qOf n r ε
  set K := max γr (max (min n (4 * γ1 * (Nat.log 2 n + 1))) 1)
  set N := (chainAlg G r ε).length
  have hcardn : Fintype.card (Fin n) = n := Fintype.card_fin n
  -- bounds on `α` and `K`
  have hαle : (α : ℝ) + 1 ≤ αf n G := by
    have h := alternation_welzlOrder_le (G := G) (γ := γ1)
      (fun Y hY => numCls_le_growth_mul (fun B => tpRel G B 0) hY)
    rw [hcardn] at h
    have : (α : ℝ) ≤ 2 * ((4 * γ1 * ((Nat.log 2 n : ℕ) + 1) + 1) * ((Nat.log 2 n : ℕ) + 1)) + 2 := by
      exact_mod_cast h
    simp only [αf, Lf, γ1f]; linarith
  have hKle : (K : ℝ) ≤ Kf n G := by
    have : K ≤ γr + 4 * γ1 * (Nat.log 2 n + 1) + 1 := by
      simp only [K]
      refine max_le (by omega) (max_le ((min_le_right _ _).trans (by omega)) (by omega))
    have : (K : ℝ) ≤ γr + 4 * γ1 * ((Nat.log 2 n : ℕ) + 1) + 1 := by exact_mod_cast this
    simp only [Kf, Lf, γ1f, γrf]; linarith
  have hS' := hcS n G hG
  have hγ1' : (γ1 : ℝ) = γ1f n G := rfl
  -- assemble
  have hN : (N : ℝ) ≤ 2 * r / e + 2 := by
    have : ((N : ℚ) : ℝ) ≤ ((2 * r / ε + 2 : ℚ) : ℝ) := by exact_mod_cast hlen
    push_cast at this; exact this
  have hmain : (Lax185574.Partitions.partCount
      (Lax185574.Partitions.atomicTypes G ((chainAlg G r ε)[t] : Set (Fin n)))
      (Lax185574.Flips.flipBall G
        (Lax185574.Partitions.atomicTypes G ((chainAlg G r ε)[t + 1] : Set (Fin n))) r u) : ℝ) ≤
      (γ1 : ℝ) * N * (200 * ((q : ℝ) + 1) * ((α : ℝ) + 1) * (K : ℝ) ^ 2) ^ r := by
    exact_mod_cast hball
  refine hmain.trans ?_
  have hpos1 : (0 : ℝ) ≤ γ1 := Nat.cast_nonneg _
  have hpos2 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hfac : ((γ1 : ℝ) * N * (200 * ((q : ℝ) + 1) * ((α : ℝ) + 1) * (K : ℝ) ^ 2) ^ r) =
      (N : ℝ) * 200 ^ r * ((q : ℝ) + 1) ^ r * ((γ1 : ℝ) * (((α : ℝ) + 1) ^ r * (K : ℝ) ^ (2 * r))) := by
    rw [mul_pow, mul_pow, mul_pow, ← pow_mul, Nat.mul_comm 2 r]; ring
  rw [hfac]
  have hSle : (γ1 : ℝ) * (((α : ℝ) + 1) ^ r * (K : ℝ) ^ (2 * r)) ≤
      γ1f n G * (αf n G ^ r * Kf n G ^ (2 * r)) := by
    rw [hγ1']
    refine mul_le_mul_of_nonneg_left (mul_le_mul (pow_le_pow_left₀ (by positivity) hαle r)
      (pow_le_pow_left₀ (by positivity) hKle _) (by positivity) (by positivity)) (h0γ1 n G hG)
  have hSc : (γ1 : ℝ) * (((α : ℝ) + 1) ^ r * (K : ℝ) ^ (2 * r)) ≤
      max cS 0 * ((n : ℝ) + 1) ^ (e / 2) :=
    hSle.trans (hS'.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)))
  have hsplit : ((n : ℝ) + 1) ^ (e / 2) * ((n : ℝ) + 1) ^ (e / 2) = ((n : ℝ) + 1) ^ e := by
    rw [← Real.rpow_add (by positivity)]; ring_nf
  calc (N : ℝ) * 200 ^ r * ((q : ℝ) + 1) ^ r *
        ((γ1 : ℝ) * (((α : ℝ) + 1) ^ r * (K : ℝ) ^ (2 * r)))
      ≤ (2 * r / e + 2) * 200 ^ r * (3 ^ r * ((n : ℝ) + 1) ^ (e / 2)) *
          (max cS 0 * ((n : ℝ) + 1) ^ (e / 2)) := by
        gcongr
    _ = D * (((n : ℝ) + 1) ^ (e / 2) * ((n : ℝ) + 1) ^ (e / 2)) := by simp only [D]; ring
    _ = D * ((n : ℝ) + 1) ^ e := by rw [hsplit]
    _ ≤ ((⌈D⌉₊ + 1 : ℕ) : ℝ) * ((n : ℝ) + 1) ^ e :=
        mul_le_mul_of_nonneg_right hD (by positivity)

end Lax185574Proofs.Chain
