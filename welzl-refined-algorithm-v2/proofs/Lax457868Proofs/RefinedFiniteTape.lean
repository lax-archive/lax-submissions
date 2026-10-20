import Lax457868Proofs.RefinedMachineBridge
import Lax457868Proofs.SourceTapePrefix
import Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
import Mathlib.Tactic

/-! Transfer a bounded source execution and its success count from a long
analysis tape to the shorter tape in the public RAM contract. The unused
suffix has no effect on a run whose cost fits in the retained prefix. -/
namespace Lax457868Proofs.RefinedFiniteTape

open Lax808846.Ram
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Compile Lax808846Proofs.Simulation
open Lax195003.WordRamRandomness
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting

lemma bitTape_split {r N : ℕ} (h : r ≤ N) (ρ : Tape N) :
    bitTape ρ = bitTape ((splitEquiv h ρ).1) ++
      bitTape ((splitEquiv h ρ).2) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [bitTape, splitEquiv, Equiv.coe_fn_mk, Nat.add_sub_cancel_left]
  rw [List.ofFn_add]
  congr 2

/-- Remove the random suffix from a bounded source run. This uses the
already checked source-prefix theorem, including reads in nested loops. -/
lemma run_on_short_tape {B C r N : ℕ} {c : Com}
    {ext : String → ℕ} {input : List ℕ} {σ : Env}
    (h : r ≤ N) (hC : C ≤ r) (ρ : Tape N)
    (hr : Run B c (initEnv ext (input ++ bitTape ρ)) σ C) :
    ∃ τ, Run B c
      (initEnv ext (input ++ bitTape ((splitEquiv h ρ).1))) τ C ∧
      τ.out = σ.out := by
  have hin : (initEnv ext (input ++ bitTape ρ)).inp =
      (input ++ bitTape ((splitEquiv h ρ).1)) ++
        bitTape ((splitEquiv h ρ).2) := by
    simp only [initEnv, bitTape_split h ρ, List.append_assoc]
  have hlen : C ≤ (input ++ bitTape ((splitEquiv h ρ).1)).length := by
    simp only [List.length_append, bitTape, List.length_ofFn]
    omega
  obtain ⟨τ, ht, _, _, ho⟩ := SourceTapePrefix.run_without_padding
    (input ++ bitTape ((splitEquiv h ρ).1))
    (bitTape ((splitEquiv h ρ).2)) hin hlen hr
  exact ⟨τ, by simpa [initEnv] using ht, ho⟩

/-- Projecting a set of good long tapes onto their prefixes cannot decrease
its probability. Every short prefix has exactly the same number of suffixes. -/
lemma prefix_success_count {r N : ℕ} (h : r ≤ N)
    (good : Finset (Tape N)) (shortGood : Finset (Tape r))
    (hgood : ∀ ρ ∈ good, (splitEquiv h ρ).1 ∈ shortGood)
    (q : ℚ) (hcount : q * (2 : ℚ) ^ N ≤ good.card) :
    q * (2 : ℚ) ^ r ≤ shortGood.card := by
  classical
  have hcard : good.card ≤ shortGood.card * 2 ^ (N - r) := by
    have hinj := Finset.card_le_card_of_injOn (splitEquiv h)
      (s := good) (t := shortGood ×ˢ (Finset.univ : Finset (Tape (N-r))))
      (by intro ρ hρ; exact Finset.mem_product.mpr ⟨hgood ρ hρ, Finset.mem_univ _⟩)
      (fun _ _ _ _ he => (splitEquiv h).injective he)
    simpa [Finset.card_product, card_tape] using hinj
  have hp : (2 : ℚ) ^ N = (2 : ℚ) ^ r * (2 : ℚ) ^ (N-r) := by
    rw [← pow_add, Nat.add_sub_of_le h]
  have hc : (good.card : ℚ) ≤ shortGood.card * (2 : ℚ) ^ (N-r) := by
    exact_mod_cast hcard
  rw [hp, ← mul_assoc] at hcount
  exact (mul_le_mul_iff_left₀ (by positivity : (0 : ℚ) < 2 ^ (N-r))).mp
    (hcount.trans hc)

/-- The public RAM tape may be only as long as the time bound, even when
the source probability analysis used a longer tape. -/
lemma succeeds_of_long_tapes {L : Layout} {B w C r N T : ℕ} {c : Com}
    {ext : String → ℕ} {input : List ℕ} {q : ℚ}
    {Accept : List ℕ → Prop} (good : Finset (Tape N))
    (hfit : L.FitsWords B w) (hok : Com.Ok L c)
    (hin : ∀ ρ : Tape r, ∀ v ∈ input ++ bitTape ρ, v < B)
    (hrN : r ≤ N) (hCr : C ≤ r) (hcost : L.const * C + 1 ≤ T)
    (htotal : ∀ ρ : Tape N,
      ∃ σ, Run B c (initEnv ext (input ++ bitTape ρ)) σ C)
    (hgood : ∀ ρ ∈ good, ∃ σ,
      Run B c (initEnv ext (input ++ bitTape ρ)) σ C ∧ Accept σ.out)
    (hcount : q * (2 : ℚ) ^ N ≤ good.card) :
    SucceedsWithProbabilityAtLeastInTime q w (compileProgram L c)
      input r T Accept := by
  classical
  let shortGood : Finset (Tape r) := Finset.univ.filter fun ρ =>
    ∃ σ, Run B c (initEnv ext (input ++ bitTape ρ)) σ C ∧ Accept σ.out
  have hproj (ρ : Tape N) (hρ : ρ ∈ good) :
      (splitEquiv hrN ρ).1 ∈ shortGood := by
    obtain ⟨σ, hr, ha⟩ := hgood ρ hρ
    obtain ⟨τ, ht, ho⟩ := run_on_short_tape hrN hCr ρ hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, τ, ht, ho ▸ ha⟩
  apply RefinedMachineBridge.succeeds_of_source
    (good := (shortGood : Set (Tape r))) hfit hok hin hcost
  · intro ρ
    let long := (splitEquiv hrN).symm (ρ, fun _ => false)
    obtain ⟨σ, hr⟩ := htotal long
    obtain ⟨τ, ht, _⟩ := run_on_short_tape hrN hCr long hr
    exact ⟨τ, by simpa [long] using ht⟩
  · intro ρ hρ
    exact (Finset.mem_filter.mp hρ).2
  · rw [Set.ncard_coe_finset]
    exact prefix_success_count hrN good shortGood hproj q hcount

end Lax457868Proofs.RefinedFiniteTape
