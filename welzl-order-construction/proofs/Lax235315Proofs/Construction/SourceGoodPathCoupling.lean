import Lax235315Proofs.Construction.SourceAdaptiveState
import Mathlib.Tactic

set_option maxRecDepth 4096

/-! Source-loop execution along tapes that are good in the adaptive query tree. -/

namespace Lax235315Proofs.Construction.SourceGoodPathCoupling

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax195003.WordRamRandomness
open Lax11.GraphEncoding
open Lax235315Proofs.Construction.RoundInvariant
open Lax235315Proofs.Construction.StoredHistory
open Lax235315Proofs.Construction.SourceBounds
open Lax235315Proofs.Construction.MachineBridge
open Lax235315Proofs.Construction.SourceAdaptiveState
open Lax235315Proofs.Construction.AdaptiveTapeCounting
open Lax235315Proofs.Construction.AdaptiveStateProtocol

lemma bitTape_splitEquiv {k T : ℕ} (hk : k ≤ T) (ρ : Fin T → Bool) :
    bitTape ρ = bitTape (splitEquiv hk ρ).1 ++ bitTape (splitEquiv hk ρ).2 := by
  apply List.ext_get
  · simp only [bitTape, List.length_ofFn, List.length_append]
    omega
  · intro i hi₁ hi₂
    by_cases hik : i < k
    · have hlen : (bitTape (splitEquiv hk ρ).1).length = k := by simp [bitTape]
      have hleft : i < (bitTape (splitEquiv hk ρ).1).length := by omega
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_left (by simpa [hlen] using hik)]
      simp only [bitTape, List.getElem_ofFn]
      simp [splitEquiv]
      rfl
    · have hik' : k ≤ i := by omega
      have hlen : (bitTape (splitEquiv hk ρ).1).length = k := by simp [bitTape]
      simp only [List.get_eq_getElem]
      rw [List.getElem_append_right (by simp [hlen]; omega)]
      simp only [bitTape, List.getElem_ofFn]
      simp [splitEquiv]
      have hiT : i < T := by simpa [bitTape] using hi₁
      have hindex : (⟨i, hiT⟩ : Fin T) =
          ⟨k + (i - k), by omega⟩ := by
        apply Fin.ext
        simp
        omega
      rw [hindex]


lemma goodPath_sourceWhile_bigStep {c n T R : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c) (hL : 0 < Nat.clog 2 n)
    (s : RoundState c n x G)
    (hround : s.env.vars "round" + R = Nat.clog 2 n)
    (hfit : Fits
      (protocol sourceWidth (sourceBad (G := G) (x := x) (c := c) hL)
        (nextState hx hG hc) R (some s)) T)
    (ρ : Fin T → Bool)
    (hgood : GoodPath
      (protocol sourceWidth (sourceBad (G := G) (x := x) (c := c) hL)
        (nextState hx hG hc) R (some s)) T hfit ρ)
    (haccepted : ∀ (s : RoundState c n x G)
      (bits : Fin (sourceWidth (some s)) → Bool),
      bits ∉ sourceBad (G := G) (x := x) (c := c) hL (some s) →
      Accepted s (roundOutput s hx hG hc bits)) :
    ∃ τ t remN, ∃ (rem : Fin remN → Bool),
      BigStepB (sourceBound c x)
        (Com.while (.lt (.var "threshold") (.var "acount")) WelzlProgram.reductionRound)
        (withInput s.env (bitTape ρ)) τ t ∧
      τ.inp = bitTape rem ∧
      Frontier (sourceBound c x) c n x τ ∧
      Nonempty (Stored G (6 * c ^ 2 * Nat.clog 2 n) τ) ∧
      τ.vars "good" = 1 ∧
      τ.vars "acount" ≤ τ.vars "threshold" := by
  induction R generalizing s T ρ with
  | zero =>
      have hrounds := s.frontier.shrinking.rounds_succ_le_clog hc s.nontrivial
      omega
  | succ R ih =>
      change sourceWidth (some s) ≤ T ∧
        (∀ bits, Fits
          (protocol sourceWidth (sourceBad (G := G) (x := x) (c := c) hL)
            (nextState hx hG hc) R (nextState hx hG hc (some s) bits))
          (T - sourceWidth (some s))) at hfit
      rcases hfit with ⟨hk, hchild⟩
      let parts := splitEquiv hk ρ
      dsimp [protocol, GoodPath, parts] at hgood
      have hacc : Accepted s (roundOutput s hx hG hc parts.1) :=
        haccepted s parts.1 hgood.1
      have hinput : bitTape ρ = bitTape parts.1 ++ bitTape parts.2 := by
        simpa [parts] using bitTape_splitEquiv hk ρ
      have hbodyRun : Run (sourceBound c x) WelzlProgram.reductionRound
          (withInput s.env (bitTape ρ))
          (withInput (roundOutput s hx hG hc parts.1) (bitTape parts.2))
          (4500 * (x.length + 1) +
            120 * Nat.clog 2 n * s.env.vars "acount") := by
        rw [hinput]
        exact roundOutput_on_tail s hx hG hc parts.1 (bitTape parts.2)
      obtain ⟨kb, hkb, hbody⟩ := hbodyRun
      have htrue :
          (Cond.lt (.var "threshold") (.var "acount")).evalB (sourceBound c x)
            (withInput s.env (bitTape ρ)) = some true := by
        have ht := loopTest_withInput s.frontier (bitTape ρ)
        have hlarge : s.env.vars "threshold" < s.env.vars "acount" := by
          rw [s.threshold]
          exact s.large
        simpa [hlarge] using ht
      cases hnext : nextState hx hG hc (some s) parts.1 with
      | none =>
          have hstop := nextState_stops_after_accepted hx hG hc s parts.1 hacc hnext
          let out := roundOutput s hx hG hc parts.1
          have hfront : Frontier (sourceBound c x) c n x
              (withInput out (bitTape parts.2)) :=
            (hacc.withBitTape parts.2).1
          have hstored : Nonempty (Stored G (6 * c ^ 2 * Nat.clog 2 n)
              (withInput out (bitTape parts.2))) := by
            rcases hacc.2.2.2 with ⟨hs⟩
            exact ⟨stored_withInput hs (bitTape parts.2)⟩
          have hgoodout : (withInput out (bitTape parts.2)).vars "good" = 1 := by
            exact (hacc.withBitTape parts.2).good
          have hthreshold : out.vars "threshold" =
              12 * c ^ 2 * Nat.clog 2 n := by
            calc
              out.vars "threshold" = s.env.vars "threshold" := by
                exact (roundOutput_spec s hx hG hc parts.1).1.frame_var
                  "threshold" (by decide)
              _ = 12 * c ^ 2 * Nat.clog 2 n := s.threshold
          have hacount :
              (withInput out (bitTape parts.2)).vars "acount" ≤
                (withInput out (bitTape parts.2)).vars "threshold" := by
            simpa [withInput, out, hthreshold] using hstop
          have hfalse :
              (Cond.lt (.var "threshold") (.var "acount")).evalB (sourceBound c x)
                (withInput out (bitTape parts.2)) = some false := by
            have ht := loopTest_withInput hfront (bitTape parts.2)
            have hnot : ¬ out.vars "threshold" < out.vars "acount" := by
              simpa [withInput] using hacount
            simpa [hnot, withInput] using ht
          refine ⟨withInput out (bitTape parts.2), 1 +
              (Cond.lt (.var "threshold") (.var "acount")).size + kb +
              (1 + (Cond.lt (.var "threshold") (.var "acount")).size),
            T - sourceWidth (some s), parts.2, ?_, rfl, hfront, hstored,
            hgoodout, hacount⟩
          exact BigStepB.while_true htrue hbody (BigStepB.while_false hfalse)
      | some s' =>
          have hstepRound := nextState_some_round hx hG hc s parts.1 s' hnext
          have hround' : s'.env.vars "round" + R = Nat.clog 2 n := by
            rw [hstepRound]
            omega
          have hrecfit : Fits
              (protocol sourceWidth (sourceBad (G := G) (x := x) (c := c) hL)
                (nextState hx hG hc) R (some s')) (T - sourceWidth (some s)) := by
            simpa only [hnext] using hchild parts.1
          have hrecgood : GoodPath
              (protocol sourceWidth (sourceBad (G := G) (x := x) (c := c) hL)
                (nextState hx hG hc) R (some s'))
              (T - sourceWidth (some s)) hrecfit parts.2 := by
            simpa [parts, hnext] using hgood.2
          obtain ⟨τ, kt, remN, rem, hloop, hinp, hfront, hstored,
            hgoodτ, hacountτ⟩ := ih s' hround' hrecfit parts.2 hrecgood
          have hstepEnv := nextState_some_env hx hG hc s parts.1 s' hnext
          have hstart : withInput s'.env (bitTape parts.2) =
              withInput (roundOutput s hx hG hc parts.1) (bitTape parts.2) := by
            simp [hstepEnv]
          have htrue' :
              (Cond.lt (.var "threshold") (.var "acount")).evalB (sourceBound c x)
                (withInput s.env (bitTape ρ)) = some true := htrue
          refine ⟨τ, 1 + (Cond.lt (.var "threshold") (.var "acount")).size +
              kb + kt, remN, rem, ?_, hinp, hfront, hstored, hgoodτ, hacountτ⟩
          have hloop' : BigStepB (sourceBound c x)
              (Com.while (.lt (.var "threshold") (.var "acount")) WelzlProgram.reductionRound)
              (withInput (roundOutput s hx hG hc parts.1) (bitTape parts.2)) τ kt := by
            rw [← hstart]
            exact hloop
          exact BigStepB.while_true htrue' hbody hloop'


lemma goodPath_sourceWhile {c n T R : ℕ} {x : List ℕ}
    {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G)
    (hG : Lax195003.WelzlOrdersNeighborhoodComplexity.HasLinearNeighborhoodComplexityWithConstant G c)
    (hc : 1 ≤ c) (hL : 0 < Nat.clog 2 n)
    (s : RoundState c n x G)
    (hround : s.env.vars "round" + R = Nat.clog 2 n)
    (hfit : Fits
      (protocol sourceWidth (sourceBad (G := G) (x := x) (c := c) hL)
        (nextState hx hG hc) R (some s)) T)
    (ρ : Fin T → Bool)
    (hgood : GoodPath
      (protocol sourceWidth (sourceBad (G := G) (x := x) (c := c) hL)
        (nextState hx hG hc) R (some s)) T hfit ρ)
    (haccepted : ∀ (s : RoundState c n x G)
      (bits : Fin (sourceWidth (some s)) → Bool),
      bits ∉ sourceBad (G := G) (x := x) (c := c) hL (some s) →
      Accepted s (roundOutput s hx hG hc bits)) :
    ∃ τ K remN, ∃ (rem : Fin remN → Bool),
      Run (sourceBound c x)
        (Com.while (.lt (.var "threshold") (.var "acount")) WelzlProgram.reductionRound)
        (withInput s.env (bitTape ρ)) τ K ∧
      τ.inp = bitTape rem ∧
      Frontier (sourceBound c x) c n x τ ∧
      Nonempty (Stored G (6 * c ^ 2 * Nat.clog 2 n) τ) ∧
      τ.vars "good" = 1 ∧
      τ.vars "acount" ≤ τ.vars "threshold" := by
  obtain ⟨τ, k, remN, rem, hbig, hinp, hfront, hstored, hgoodτ, hacount⟩ :=
    goodPath_sourceWhile_bigStep hx hG hc hL s hround hfit ρ hgood haccepted
  exact ⟨τ, k, remN, rem, ⟨k, le_rfl, hbig⟩, hinp, hfront, hstored,
    hgoodτ, hacount⟩

end Lax235315Proofs.Construction.SourceGoodPathCoupling
