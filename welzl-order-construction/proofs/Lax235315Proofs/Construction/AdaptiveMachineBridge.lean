import Lax235315Proofs.Construction.AdaptiveTapeCounting
import Lax235315Proofs.Construction.MachineBridge

/-! Connecting adaptive bit-block failure counts to the actual machine
success event. The remaining application premise is a successful source
execution on each tape outside the protocol's failing set. -/

namespace Lax235315Proofs.Construction.AdaptiveMachineBridge
open Lax235315Proofs.Construction.AdaptiveBitBlocks
open Lax235315Proofs.Construction.AdaptiveTapeCounting
open Lax235315Proofs.Construction.MachineBridge
open Lax235315.ConstructionContracts

lemma success_count_of_protocol {R T : ℕ} (p : Protocol R) (ε : ℚ)
    (hε : 0 ≤ ε) (hlocal : LocallyBounded ε p)
    (hbits : maxConsumedBits p ≤ T) (hbudget : (R : ℚ) * ε ≤ 1 / 3)
    (good : Set (Fin T → Bool))
    (hsuccess : ∀ ρ, ρ ∉ failingTapes p T (fits_of_maxConsumedBits p T hbits) →
      ρ ∈ good) : (2 / 3 : ℚ) * 2 ^ T ≤ (good.ncard : ℚ) := by
  classical
  let bad := failingTapes p T (fits_of_maxConsumedBits p T hbits)
  have hsub : (↑badᶜ : Set (Fin T → Bool)) ⊆ good := by
    intro ρ hρ
    apply hsuccess ρ
    simpa [bad] using hρ
  have hcard : badᶜ.card ≤ good.ncard := by
    simpa only [Set.ncard_coe_finset] using Set.ncard_le_ncard hsub
  have hsum : (badᶜ.card : ℚ) + bad.card = (2 : ℚ) ^ T := by
    exact_mod_cast (by simpa [Tape] using Finset.card_compl_add_card bad :
      badᶜ.card + bad.card = 2 ^ T)
  have hfail := failingTapes_card_le p ε hε hlocal T hbits
  have hfail' : (bad.card : ℚ) ≤ (1 / 3 : ℚ) * 2 ^ T :=
    hfail.trans (mul_le_mul_of_nonneg_right hbudget (by positivity))
  have hcard' : (badᶜ.card : ℚ) ≤ good.ncard := by exact_mod_cast hcard
  linarith

/-- A protocol with failure budget at most one third proves the exact
registered machine-tape count once every other tape has a successful bounded
source execution. No public probability claim is used as a premise. -/
lemma machine_success_count_of_protocol {R K c n w C : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hK : 2500 ≤ K) (hvalid : ValidInput K c n w G x)
    (hcost : 10 * C + 1 ≤ timeBudget K n x)
    (p : Protocol R) (ε : ℚ) (hε : 0 ≤ ε) (hlocal : LocallyBounded ε p)
    (hbits : maxConsumedBits p ≤ timeBudget K n x)
    (hbudget : (R : ℚ) * ε ≤ 1 / 3)
    (hsuccess : ∀ ρ,
      ρ ∉ failingTapes p (timeBudget K n x)
        (fits_of_maxConsumedBits p (timeBudget K n x) hbits) →
      ρ ∈ sourceGoodTapes c n x C (timeBudget K n x)) :
    (2 / 3 : ℚ) * 2 ^ timeBudget K n x ≤
      ((goodTapes w c x (timeBudget K n x)).ncard : ℚ) := by
  apply success_count_of_protocol p ε hε hlocal hbits hbudget
  intro ρ hρ
  exact sourceGoodTapes_subset hK hvalid hcost (hsuccess ρ hρ)

end Lax235315Proofs.Construction.AdaptiveMachineBridge
