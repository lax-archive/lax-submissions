import Lax457868Proofs.ExceptionRepairCharge

/-! Collect the explicit component charges of the repair loop. The repeated
representative-row term remains visible until it is averaged over selection. -/
namespace Lax457868Proofs.RefinedRepairCharges
open Lax457868Proofs.ExceptionRepairLoop
open Lax457868Proofs.ExceptionRepairCharge
open Lax457868Proofs.ExceptionPhaseSource
open Lax457868Proofs.SamplerPhases

lemma repair_mean_charge_le_input
    {B n s t bufferCap targetCap q cap k e : ℕ}
    {G : SimpleGraph (Fin n)} {x : List ℕ}
    {E groupedB Wbase A Wcurrent : Finset ℕ}
    (R : LoopInput B n s t bufferCap targetCap q cap k e
      G x E groupedB Wbase A Wcurrent)
    (hsize : E.card * (s+1) ≤ A.card)
    (hseparate : ∀ u ∈ E, ∀ v ∈ E,
      trace (numericNeighborhood G) Wbase u =
        trace (numericNeighborhood G) Wbase v → u = v) :
    23 + 20*n + (∑ b ∈ E,
      (domainCharge x G A R.rep b + 2*classScanCharge x R.size R.label R.ord b +
        (12+60*s)*Nat.clog 2 n + 278*s+157)) ≤
      495*(x.length+1) + 90*(∑ b ∈ E, Lax11Proofs.CC.deg x (R.rep b)) +
        435*A.card*(Nat.clog 2 n+1) := by
  have hd := sum_domainCharge_le R.hgraph A E R.rep R.hErange R.hrepRange
  have hs := sum_classScanCharge_le_input R E subset_rfl hseparate
  have he : E.card ≤ A.card := by nlinarith
  have hes : E.card*s ≤ A.card := by nlinarith
  have heL := Nat.mul_le_mul_right (Nat.clog 2 n) he
  have hesL := Nat.mul_le_mul_right (Nat.clog 2 n) hes
  have hterm : E.card*((12+60*s)*Nat.clog 2 n+278*s+157) ≤
      435*A.card*(Nat.clog 2 n+1) := by nlinarith
  have hsum : (∑ b ∈ E,
      (domainCharge x G A R.rep b + 2*classScanCharge x R.size R.label R.ord b +
        (12+60*s)*Nat.clog 2 n + 278*s+157)) =
      (∑ b ∈ E, domainCharge x G A R.rep b) +
        2*(∑ b ∈ E, classScanCharge x R.size R.label R.ord b) +
        E.card*((12+60*s)*Nat.clog 2 n+278*s+157) := by
    simp [Finset.sum_add_distrib,Finset.mul_sum]
    ring
  rw [hsum]
  have hlen := R.hgraph.length_eq
  omega

/-- The paper's accepted exception cap implies the size budget used above. -/
lemma accepted_exception_budget (m c s e : ℕ)
    (hc : 0 < c) (he : e ≤ m/(4*c^2*(s+1))) : e*(s+1) ≤ m := by
  have h := Nat.mul_le_mul_right (4*c^2*(s+1)) he
  have hdiv := Nat.div_mul_le_self m (4*c^2*(s+1))
  have hc4 : 1 ≤ 4*c^2 := by nlinarith
  have hp := Nat.mul_le_mul_left (e*(s+1)) hc4
  nlinarith

end Lax457868Proofs.RefinedRepairCharges
