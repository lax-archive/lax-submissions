/-
Theorem `thm:decide-if-mealy` of *Transducers* (M. Bojańczyk): one can decide whether a rational
function is computed by a Mealy machine.

By Theorem `thm:mealy-machine-independent` a function is computed by a Mealy machine exactly when it
is continuous, prefix preserving and length preserving, and a rational function is automatically
continuous (Theorem `thm:continuity-rational-relations`, used through Theorem
`thm:rational-is-mealy-characterisation` in `RequestProject/PartB/CodeRat.lean`).  Length
preservation is decided by Lemma `lem:decide-if-length-preserving`
(`RequestProject/PartB/LenDec.lean`), and prefix preservation of a length preserving function is the
equality

  `dropLast (f w) = f (dropLast w)`

of two rational functions, for which `RequestProject/PartB/PrefixCodes.lean`
builds codes; the equality is decided by Theorem `thm:equivalence-rational-functions`.
-/
import Lax132576Proofs.Source.PartB.CodeRat
import Lax132576Proofs.Source.PartB.RatEqDec
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers
namespace MealyDec

open PrefixCodes CodeRat

/-- The decision procedure for Theorem `thm:decide-if-mealy`, built from a decision procedure
`D` for equivalence of coded rational functions (Theorem `thm:equivalence-rational-functions`). -/
def mealyDecB (D : RelCode × RelCode → Bool) (c : RelCode) : Bool :=
  LenDec.lenDec c && D (dropCode c, shiftCode c)

lemma mealyDecB_iff {D : RelCode × RelCode → Bool}
    (hD : ∀ p : RelCode × RelCode, CodeFunctional p.1 → CodeFunctional p.2 →
      (D p = true ↔ codeRel p.1 = codeRel p.2))
    {c : RelCode} (hc : CodeFunctional c) :
    mealyDecB D c = true ↔
      (∃ f : List ℕ → List ℕ,
        (∀ w, CodeWord c w → ∀ v, (codeRel c w v ↔ v = f w)) ∧ IsMealy f) := by
  rw [mealyProperty_iff hc, isMealy_codeFun_iff hc, mealyDecB, Bool.and_eq_true,
    LenDec.lenDec_iff]
  constructor
  · rintro ⟨hlen, hd⟩
    exact ⟨hlen, (prefixCrit_iff hc hlen).2
      (hD _ (codeFunctional_dropCode hc) (codeFunctional_shiftCode hc) |>.1 hd)⟩
  · rintro ⟨hlen, hpre⟩
    refine ⟨hlen, ?_⟩
    exact (hD _ (codeFunctional_dropCode hc) (codeFunctional_shiftCode hc)).2
      ((prefixCrit_iff hc hlen).1 hpre)

lemma computable_mealyDecB {D : RelCode × RelCode → Bool} (hD : Computable D) :
    Computable (mealyDecB D) := by
  have h1 : Computable (fun c : RelCode => LenDec.lenDec c) := LenDec.computable_lenDec
  have h2 : Computable (fun c : RelCode => D (dropCode c, shiftCode c)) :=
    hD.comp (Computable.pair primrec_dropCode.to_comp primrec_shiftCode.to_comp)
  exact (Primrec.and.to_comp.comp h1 h2).of_eq (fun _ => rfl)

end MealyDec

/-- **Theorem `thm:decide-if-mealy`** from the effectivity hypotheses of
`RequestProject/PartB/Effective.lean`: one can decide whether a rational
function is computed by a Mealy machine. -/
theorem rationalFun_isMealy_decidable_aux :
    DecidableUnderPromise CodeFunctional
      (fun c => ∃ f : List ℕ → List ℕ,
        (∀ w, CodeWord c w → ∀ v, (codeRel c w v ↔ v = f w)) ∧ IsMealy f) := by
  obtain ⟨D, hDcomp, hD⟩ := rationalFun_equivalence_decidable_aux
  exact ⟨MealyDec.mealyDecB D, MealyDec.computable_mealyDecB hDcomp,
    fun c hc => MealyDec.mealyDecB_iff (fun p hp₁ hp₂ => hD p ⟨hp₁, hp₂⟩) hc⟩

end Lax132576Proofs.Transducers
