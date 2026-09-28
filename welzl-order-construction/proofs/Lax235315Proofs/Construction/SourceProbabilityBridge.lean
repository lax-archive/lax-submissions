import Lax235315Proofs.Construction.SourceGoodPathCoupling
import Lax235315Proofs.Construction.InitialRoundStateSource
import Lax235315Proofs.Construction.SourceAdaptiveState

/-! Compose a fixed canonical start, a good adaptive path, and the guarded
source driver into a successful literal source execution. -/

namespace Lax235315Proofs.Construction.SourceProbabilityBridge

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax11.GraphEncoding
open Lax195003.WordRamRandomness
open Lax235315Proofs.Construction.WelzlSetup
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.MachineBridge
open Lax235315Proofs.Construction.RoundInvariant
open Lax235315Proofs.Construction.StoredHistory
open Lax235315Proofs.Construction.SourceAdaptiveState
open Lax235315Proofs.Construction.SourceGoodPathCoupling
open Lax235315Proofs.Construction.InitialRoundStateSource
open Lax235315Proofs.Construction.SmallInputSource
open Lax235315Proofs.Construction.AdaptiveStateProtocol
open Lax235315Proofs.Construction.AdaptiveTapeCounting
open Lax235315Proofs.Construction.AdaptiveBitBlocks
open Lax235315.ConstructionContracts

/-- The last source-level implication needed by the finite-tape count,
assuming the two local facts that the canonical setup state is shared by all
tapes and that a nonbad block is accepted by the literal source round. -/
lemma sourceGoodTapes_of_goodPath_from_uniform_start
    {c n T : ℕ} {x : List ℕ} {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c) (hT : sourceCost 6000 n x ≤ T)
    (s : RoundState c n x G) (hround : s.env.vars "round" = 0)
    (hsource : ∀ ρ : Fin T → Bool,
      ∃ σ τ₀ : Env,
        Run (sourceBound c x) setup
          (initEnv (welzlExt n (edgeCount x) (2 ^ Nat.clog 2 n))
            ((c :: x) ++ bitTape ρ)) σ
          (40 * (x.length + Nat.clog 2 n + 1)) ∧
        τ₀ = withInput s.env (bitTape ρ) ∧
        (∀ {τ k}, Run (sourceBound c x)
            (.while (.lt (.var "threshold") (.var "acount")) reductionRound)
            τ₀ τ k → ∃ K, Run (sourceBound c x) reduceAll σ τ K))
    (haccepted : ∀ (s' : RoundState c n x G)
      (bits : Fin (sourceWidth (some s')) → Bool),
      bits ∉ sourceBad (G := G) (x := x) (c := c)
        (Nat.clog_pos (by omega) s.nontrivial) (some s') →
      Accepted s' (roundOutput s' hx hG hc bits))
    (hfit : Fits
      (protocol sourceWidth
        (sourceBad (G := G) (x := x) (c := c)
          (Nat.clog_pos (by omega) s.nontrivial))
        (nextState hx hG hc) (Nat.clog 2 n) (some s)) T)
    (ρ : Fin T → Bool)
    (hgood : GoodPath
      (protocol sourceWidth
        (sourceBad (G := G) (x := x) (c := c)
          (Nat.clog_pos (by omega) s.nontrivial))
        (nextState hx hG hc) (Nat.clog 2 n) (some s)) T hfit ρ) :
    ρ ∈ sourceGoodTapes c n x (sourceCost 6000 n x) T := by
  obtain ⟨σ, τ₀, rsetup, hboundary, hcontinue⟩ := hsource ρ
  have hround' : s.env.vars "round" + Nat.clog 2 n = Nat.clog 2 n := by
    rw [hround]; omega
  obtain ⟨τ, K, remN, rem, rloop, _, hfront, ⟨hstore⟩, _, hsmall⟩ :=
    goodPath_sourceWhile hx hG hc
      (Nat.clog_pos (by omega) s.nontrivial) s hround' hfit ρ hgood haccepted
  have rloop' : Run (sourceBound c x)
      (.while (.lt (.var "threshold") (.var "acount")) reductionRound)
      τ₀ τ K := by
    rw [hboundary]
    exact rloop
  obtain ⟨Kr, rreduce⟩ := hcontinue rloop'
  have hthreshold : τ.vars "threshold" = 12 * c ^ 2 * Nat.clog 2 n := by
    have hframe := rloop.frame_var "threshold" (by decide)
    exact hframe.trans (by simpa [withInput] using s.threshold)
  have hsmall' : τ.vars "acount" ≤ 12 * c ^ 2 * Nat.clog 2 n := by
    rw [← hthreshold]
    exact hsmall
  exact sourceGoodTapes_of_good_reduceAll hx hG hc s.nontrivial hT ρ
    rsetup rreduce hfront hstore hsmall'

lemma machine_probability_of_small_input {K c n w : ℕ}
    {x : List ℕ} {G : SimpleGraph (Fin n)}
    (hK : 60001 ≤ K) (hvalid : ValidInput K c n w G x)
    (hn : n ≤ 1) :
    (2 / 3 : ℚ) * 2 ^ timeBudget K n x ≤
      ((goodTapes w c x (timeBudget K n x)).ncard : ℚ) := by
  have hsource := smallInput_sourceGoodTapes_ncard hvalid.2.2.1 hvalid.1 hn
    (T := timeBudget K n x)
  have hsub := sourceGoodTapes_subset (by omega : 2500 ≤ K) hvalid
    (cost_lift (by omega : 10 * 6000 + 1 ≤ K))
  have hcard := Set.ncard_le_ncard hsub
  rw [hsource] at hcard
  have hcard' : (2 ^ timeBudget K n x : ℚ) ≤
      ((goodTapes w c x (timeBudget K n x)).ncard : ℚ) := by
    exact_mod_cast hcard
  have hbase : (0 : ℚ) ≤ 2 ^ timeBudget K n x := by positivity
  nlinarith

lemma machine_probability_of_large_accepted {K c n w : ℕ}
    {x : List ℕ} {G : SimpleGraph (Fin n)}
    (hK : 60001 ≤ K) (hvalid : ValidInput K c n w G x)
    (hn : 1 < n) (hlarge : 12 * c ^ 2 * Nat.clog 2 n < n)
    (haccepted : ∀ (s' : RoundState c n x G)
      (bits : Fin (sourceWidth (some s')) → Bool),
      bits ∉ sourceBad (G := G) (x := x) (c := c)
        (Nat.clog_pos (by omega) s'.nontrivial) (some s') →
      Accepted s' (roundOutput s' hvalid.2.2.1 hvalid.2.1 hvalid.1 bits)) :
    (2 / 3 : ℚ) * 2 ^ timeBudget K n x ≤
      ((goodTapes w c x (timeBudget K n x)).ncard : ℚ) := by
  obtain ⟨s, hround, huniform⟩ :=
    initial_round_state_uniform_tapes hvalid.2.2.1 hvalid.1 hn hlarge
  apply machine_probability_of_source_good_paths hK hvalid s
  intro ρ hgood
  have hT : sourceCost 6000 n x ≤ timeBudget K n x :=
    sourceCost_le_timeBudget (by omega)
  apply sourceGoodTapes_of_goodPath_from_uniform_start
    hvalid.2.2.1 hvalid.2.1 hvalid.1 hT s hround
  · intro ρ'
    obtain ⟨σ, τ, rsetup, _, hboundary, hcontinue⟩ := huniform ρ'
    exact ⟨σ, τ, rsetup, hboundary.symm, hcontinue⟩
  · intro s' bits hgoodBits
    exact haccepted s' bits hgoodBits
  · exact hgood

lemma eventually_hasSuccessProbability_of_accepted
    (haccepted : ∀ {c n : ℕ} {x : List ℕ}
      {G : SimpleGraph (Fin n)},
      (hx : EncodesGraph x n G) →
      (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c) →
      (hc : 1 ≤ c) →
      ∀ (s : RoundState c n x G)
        (bits : Fin (sourceWidth (some s)) → Bool),
        bits ∉ sourceBad (G := G) (x := x) (c := c)
          (Nat.clog_pos (by omega) s.nontrivial) (some s) →
        Accepted s (roundOutput s hx hG hc bits)) :
    ∃ K₀ : ℕ, 1 ≤ K₀ ∧ ∀ K : ℕ, K₀ ≤ K → HasSuccessProbability K := by
  refine ⟨60001, by omega, ?_⟩
  intro K hK c n w G x hvalid
  by_cases hnsmall : n ≤ 1
  · exact machine_probability_of_small_input hK hvalid hnsmall
  by_cases hguard : n ≤ 12 * c ^ 2 * Nat.clog 2 n
  · exact machine_probability_of_small_guard hK hvalid hguard
  · exact machine_probability_of_large_accepted hK hvalid (by omega)
      (by omega) (fun s bits hbits =>
        haccepted hvalid.2.2.1 hvalid.2.1 hvalid.1 s bits hbits)

end Lax235315Proofs.Construction.SourceProbabilityBridge
