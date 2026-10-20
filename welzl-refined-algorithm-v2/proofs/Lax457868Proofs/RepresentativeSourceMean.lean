import Lax457868Proofs.ClassTraceMean
import Lax457868Proofs.InitialSamplerAttempt

/-! The actual representative-selection command has a linear mean cost
from each fixed partition state, with arbitrary unread input appended. -/
namespace Lax457868Proofs.RepresentativeSourceMean
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax457868Proofs.InitialSamplerAttempt
open Lax457868Proofs.ClassRepresentativeTrace
open Lax457868Proofs.ClassRepresentativeLoop
open Lax457868Proofs.ReusedOriginal.Construction.MarkingMath
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting

/-- Change only the input tape of a fixed partition state. -/
def reinput {B n q Q t : ℕ} (I : RepresentativeInput B n q Q t)
    (bits : List Bool) (hb : bitBudget I.size t 0 q ≤ bits.length) :
    RepresentativeInput B n q Q t :=
  { I with σ := {I.σ with inp := bits.map Bool.toNat ++ I.rest}
           bits := bits
           hinput := rfl
           hbudget := hb }

lemma class_sizes_sum {B n q Q t : ℕ} (I : RepresentativeInput B n q Q t) :
    (∑ j ∈ Finset.range q, I.size j) = (activeVertices n I.active).card := by
  calc
    _ = ∑ j ∈ Finset.range q, classMultiplicity I.label (activeVertices n I.active) j := by
      apply Finset.sum_congr rfl
      intro j hj
      exact I.hsizes.2 j (Finset.mem_range.mp hj)
    _ = _ := sum_classMultiplicity_of_bounded (by
      intro v hv
      obtain ⟨hn,ha⟩ := mem_activeVertices.mp hv
      exact I.hsizes.1 v hn ha)

/-- The bound includes packing, the radix pass, actual selector retries,
and writing the representative array. -/
lemma representative_source_mean {B n q Q t N : ℕ}
    (I : RepresentativeInput B n q Q t)
    (hb : bitBudget I.size t 0 q ≤ N) :
    ∃ (final : Tape N → Env) (cost : Tape N → ℕ),
      (∀ ρ, Run B initialRepresentativeSelection
        {I.σ with inp := (List.ofFn ρ).map Bool.toNat ++ I.rest} (final ρ) (cost ρ)) ∧
      (∑ ρ, cost ρ) ≤ (351*n+64*Q+97)*2^N := by
  classical
  have hr (ρ : Tape N) : ∃ τ charge,
      Run B initialRepresentativeSelection
        {I.σ with inp := (List.ofFn ρ).map Bool.toNat ++ I.rest} τ
        (20*n+9+charge+64*((activeVertices n I.active).card+Q+1)+104*n+24) ∧
      ∃ v u f, ClassTrace I.size t (classStart I.size) 0 q (List.ofFn ρ) v u charge f := by
    let J := reinput I (List.ofFn ρ) (by simpa using hb)
    obtain ⟨τ,xs,sorted,v,u,c,f,hrun,_,_,hlen,htrace,_⟩ :=
      initialRepresentativeSelection_run_bits J
    exact ⟨τ,c,by simpa only [hlen, J, reinput] using hrun,v,u,f,htrace⟩
  choose final charge hrun htrace using hr
  have hmean := ClassTraceMean.sum_actual_charge_le I.size t (classStart I.size)
    0 q N (fun j _ hj => I.hoccupied j (by omega)) hb charge htrace
  simp only [Nat.zero_add, class_sizes_sum I] at hmean
  let cost (ρ : Tape N) :=
    20*n+9+charge ρ+64*((activeVertices n I.active).card+Q+1)+104*n+24
  refine ⟨final,cost,hrun,?_⟩
  have hcard : (activeVertices n I.active).card ≤ n := by
    have hs : activeVertices n I.active ⊆ Finset.range n := by
      intro v hv
      exact Finset.mem_range.mpr (mem_activeVertices.mp hv).1
    simpa using Finset.card_le_card hs
  simp only [cost, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    card_tape, nsmul_eq_mul]
  have hh := Nat.mul_le_mul_right (227*2^N) hcard
  nlinarith

end Lax457868Proofs.RepresentativeSourceMean
