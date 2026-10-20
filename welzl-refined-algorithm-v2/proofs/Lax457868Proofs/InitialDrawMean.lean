import Lax457868Proofs.ClassTraceMean
import Lax457868Proofs.InitialDrawSampleSource

/-! Mean source cost of the initial with-replacement sample, reusing the
same chronological selector estimate as the representatives. -/
namespace Lax457868Proofs.InitialDrawMean
open Lax457868Proofs.FairBitIndices
open Lax457868Proofs.SequentialDraws
open Lax457868Proofs.ClassRepresentativeTrace
open Lax457868Proofs.InitialDrawSampleSource
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting

lemma DrawTrace.to_classTrace (m : ℕ) (hm : 0 < m) (t : ℕ)
    {r : ℕ} {blocks : List (Fin (Nat.clog 2 m) → Bool)}
    {values : List (Fin m)} {used : ℕ} {failed : Bool}
    (h : DrawTrace m hm t r blocks values used failed) (tail : List Bool) (d : ℕ) :
    ClassTrace (fun _ => m) t (fun _ => 0) d r
      (blocks.flatMap List.ofFn ++ tail) (values.map Fin.val)
      (used * Nat.clog 2 m)
      ((15 * Nat.clog 2 m+30)*used + (12*Nat.clog 2 m+61)*
        (values.length + if failed then 1 else 0)) failed := by
  induction h generalizing d with
  | done blocks =>
    simpa using ClassTrace.done (size := fun _ => m)
      (t := t) (start := fun _ => 0) d (blocks.flatMap List.ofFn ++ tail)
  | failed tape rest u hsel =>
    simpa [List.flatMap_append, tapeBits, Nat.add_assoc] using
      ClassTrace.failed (size := fun _ => m) (start := fun _ => 0)
        (d := d) tape (rest.flatMap List.ofFn ++ tail) u hm hsel
  | @accepted r tape rest i u values used failed hsel hnext ih =>
    have hh := ClassTrace.accepted (size := fun _ => m) (start := fun _ => 0)
      (d := d) tape (rest.flatMap List.ofFn ++ tail) i u hm hsel
      (by simpa only [List.flatMap_append, LocalFlatLaw.flatMap_drop_blocks,
        ← List.append_assoc, tapeBits] using ih (d+1))
    convert hh using 1 <;>
      simp [List.flatMap_append, tapeBits, Nat.add_mul, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma bitBudget_const (m t d r : ℕ) :
    bitBudget (fun _ => m) t d r = r*t*Nat.clog 2 m := by
  induction r generalizing d with
  | zero => simp [bitBudget]
  | succ r ih => simp only [bitBudget, ih]; ring

lemma meanBudget_const (m d r : ℕ) :
    ClassTraceMean.meanBudget (fun _ => m) d r = r*(42*Nat.clog 2 m+121) := by
  induction r generalizing d with
  | zero => simp [ClassTraceMean.meanBudget]
  | succ r ih => simp only [ClassTraceMean.meanBudget, ih]; ring

/-- All actual draw-family charges are averaged over the original flat
input tapes. Unused cap bits remain part of the following input suffix. -/
lemma sum_draw_cost_le (n m r t N : ℕ) (hm : 0 < m)
    (hb : r*t*Nat.clog 2 m ≤ N)
    (values : Tape N → List (Fin m)) (used : Tape N → ℕ) (failed : Tape N → Bool)
    (htrace : ∀ ρ, ∃ tape : BitTape m (r*t), ∃ tail : List Bool,
      List.ofFn ρ = tapeBits tape ++ tail ∧
      DrawTrace m hm t r (List.ofFn tape) (values ρ) (used ρ) (failed ρ)) :
    (∑ ρ, initialDrawSampleCost n m (used ρ)
      ((values ρ).length + if failed ρ then 1 else 0) (values ρ).length (failed ρ)) ≤
      (r*(42*Nat.clog 2 m+133)+12*Nat.clog 2 m+31*n+57)*2^N := by
  classical
  let C (ρ : Tape N) := (15*Nat.clog 2 m+30)*used ρ +
    (12*Nat.clog 2 m+61)*((values ρ).length + if failed ρ then 1 else 0)
  have hc (ρ : Tape N) : ClassTraceMean.charge (fun _ => m) t (fun _ => 0)
      0 r (List.ofFn ρ) = C ρ := by
    obtain ⟨tape,tail,he,htr⟩ := htrace ρ
    rw [he]
    exact ClassTraceMean.charge_eq (DrawTrace.to_classTrace m hm t htr tail 0)
  have hmean := ClassTraceMean.sum_charge_le (fun _ => m) t (fun _ => 0) r 0 N
    (by intros; exact hm) (by simpa only [bitBudget_const] using hb)
  simp_rw [hc, meanBudget_const] at hmean
  have hmeanN : (∑ ρ, C ρ) ≤ (r*(42*Nat.clog 2 m+121))*2^N := by
    exact_mod_cast hmean
  have hpoint (ρ : Tape N) : initialDrawSampleCost n m (used ρ)
      ((values ρ).length + if failed ρ then 1 else 0) (values ρ).length (failed ρ) ≤
        C ρ+12*Nat.clog 2 m+31*n+12*r+57 := by
    obtain ⟨tape,tail,he,htr⟩ := htrace ρ
    have hlen := (DrawTrace.length_and_status m hm t htr).1
    dsimp [initialDrawSampleCost, C]
    cases failed ρ <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> nlinarith
  have hsum := Finset.sum_le_sum (fun ρ (_ : ρ ∈ Finset.univ) => hpoint ρ)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    card_tape, nsmul_eq_mul] at hsum
  nlinarith

end Lax457868Proofs.InitialDrawMean
