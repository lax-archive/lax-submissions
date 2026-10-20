import Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
import Lax457868Proofs.SourceTapePrefix
import Mathlib.Tactic

/-! Finite averaging after a variable stopping prefix. A deterministic
source run fixes its consumed prefix and leaves a uniformly counted suffix.
This lemma composes retry and round estimates without discarding rejected
bits or replacing an adaptive process by an independent product. -/
namespace Lax457868Proofs.StoppedPrefixAveraging
open Lax457868Proofs.ReusedOriginal.Construction.AdaptiveTapeCounting
open scoped BigOperators

lemma boolTape_split {k N : ℕ} (h : k ≤ N) (ρ : Tape N) :
    List.ofFn ρ = List.ofFn ((splitEquiv h ρ).1) ++
      List.ofFn ((splitEquiv h ρ).2) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [splitEquiv, Equiv.coe_fn_mk, Nat.add_sub_cancel_left]
  rw [List.ofFn_add]
  congr 2

lemma prefix_of_split {k N : ℕ} (h : k ≤ N) (ρ : Tape N) :
    (List.ofFn ρ).take k = List.ofFn ((splitEquiv h ρ).1) := by
  rw [boolTape_split h ρ]
  simp

/-- Replay the actual source execution after replacing exactly its unread
suffix. Its memory and output are unchanged. -/
lemma run_replace_consumed_suffix {B K : ℕ}
    {c : Lax808846Proofs.Imp.Com} {σ τ : Lax808846Proofs.Imp.Env}
    (hrun : Lax808846Proofs.Reasoning.Run B c σ τ K)
    (pre : List ℕ) (hin : σ.inp = pre ++ τ.inp) (tail : List ℕ) :
    Lax808846Proofs.Reasoning.Run B c
      {σ with inp := pre ++ tail} {τ with inp := tail} K := by
  obtain ⟨k, hk, hbig⟩ := hrun
  obtain ⟨actual, hactual, _, hreplay⟩ := SourceTapePrefix.consumed_prefix hbig
  have heq : actual = pre := List.append_cancel_right (hactual.symm.trans hin)
  subst actual
  exact ⟨k, hk, hreplay tail⟩

/-- A second run on the same observed prefix has the same final memory and
output, even if its unread suffix and supplied cost bound differ. -/
lemma run_result_same_prefix {B K J : ℕ}
    {c : Lax808846Proofs.Imp.Com} {σ τ υ : Lax808846Proofs.Imp.Env}
    (hrun : Lax808846Proofs.Reasoning.Run B c σ τ K)
    (pre : List ℕ) (hin : σ.inp = pre ++ τ.inp) (tail : List ℕ)
    (hother : Lax808846Proofs.Reasoning.Run B c
      {σ with inp := pre ++ tail} υ J) :
    υ = {τ with inp := tail} := by
  have hrep := run_replace_consumed_suffix hrun pre hin tail
  obtain ⟨_, _, ha⟩ := hrep
  obtain ⟨_, _, hb⟩ := hother
  exact (Lax808846Proofs.Imp.BigStep.unique ha.bigStep hb.bigStep).1.symm

/-- Stopping positions of two source runs agree when the second input
extends the first run's consumed Boolean prefix. -/
lemma bool_run_same_prefix {B K J d e : ℕ}
    {c : Lax808846Proofs.Imp.Com} {σ τ υ : Lax808846Proofs.Imp.Env}
    (bits other : List Bool) (rest : List ℕ)
    (hr : Lax808846Proofs.Reasoning.Run B c
      {σ with inp := bits.map Bool.toNat ++ rest} τ K)
    (hs : Lax808846Proofs.Reasoning.Run B c
      {σ with inp := other.map Bool.toNat ++ rest} υ J)
    (hi : τ.inp = (bits.drop d).map Bool.toNat ++ rest)
    (hj : υ.inp = (other.drop e).map Bool.toNat ++ rest)
    (hd : d ≤ other.length) (he : e ≤ other.length)
    (hp : bits.take d = other.take d) :
    e = d ∧ υ = {τ with inp := (other.drop d).map Bool.toNat ++ rest} := by
  let pre := (bits.take d).map Bool.toNat
  let tail := (other.drop d).map Bool.toNat ++ rest
  have hsplit (xs : List Bool) : xs.map Bool.toNat =
      (xs.take d).map Bool.toNat ++ (xs.drop d).map Bool.toNat := by
    simpa only [List.map_append] using congrArg (List.map Bool.toNat)
      (List.take_append_drop d xs).symm
  have hin : ({σ with inp := bits.map Bool.toNat ++ rest} :
      Lax808846Proofs.Imp.Env).inp = pre ++ τ.inp := by
    change bits.map Bool.toNat ++ rest = pre ++ τ.inp
    rw [hi]
    dsimp [pre]
    rw [hsplit bits]
    simp only [List.append_assoc]
  have hother : ({σ with inp := other.map Bool.toNat ++ rest} :
      Lax808846Proofs.Imp.Env) = {σ with inp := pre ++ tail} := by
    have hh : other.map Bool.toNat ++ rest = pre ++ tail := by
      rw [hsplit other, ← hp]
      simp [pre, tail, List.append_assoc]
    simp only [hh]
  have hsame : υ = {τ with inp := tail} := by
    apply run_result_same_prefix hr pre hin tail
    simpa only [hother] using hs
  have hlen := congrArg List.length (congrArg Lax808846Proofs.Imp.Env.inp hsame)
  rw [hj] at hlen
  simp only [tail, List.length_append, List.length_map, List.length_drop] at hlen
  exact ⟨by omega, hsame⟩

/-- The complete observed prefix includes rejected random blocks. -/
def stoppedPrefix {N : ℕ} (used : Tape N → ℕ) (ρ : Tape N) : List Bool :=
  (List.ofFn ρ).take (used ρ)

lemma prefix_eq_iff_split {N : ℕ} (used : Tape N → ℕ)
    (hbound : ∀ ρ, used ρ ≤ N)
    (hcausal : ∀ ρ τ, (List.ofFn ρ).take (used ρ) =
      (List.ofFn τ).take (used ρ) → used τ = used ρ)
    (ρ τ : Tape N) :
    stoppedPrefix used τ = stoppedPrefix used ρ ↔
      (splitEquiv (hbound ρ) τ).1 = (splitEquiv (hbound ρ) ρ).1 := by
  constructor
  · intro heq
    have hlen := congrArg List.length heq
    simp only [stoppedPrefix, List.length_take, List.length_ofFn,
      Nat.min_eq_left (hbound τ), Nat.min_eq_left (hbound ρ)] at hlen
    have hh : (List.ofFn τ).take (used ρ) =
        (List.ofFn ρ).take (used ρ) := by
      simpa only [stoppedPrefix, hlen] using heq
    rw [prefix_of_split (hbound ρ), prefix_of_split (hbound ρ)] at hh
    exact List.ofFn_injective hh
  · intro heq
    have hh : (List.ofFn ρ).take (used ρ) =
        (List.ofFn τ).take (used ρ) := by
      rw [prefix_of_split (hbound ρ), prefix_of_split (hbound ρ), heq]
    have hu := hcausal ρ τ hh
    simpa only [stoppedPrefix, hu] using hh.symm

/-- A stopped-prefix fiber consists of exactly all completions of that
prefix, each once. -/
lemma sum_prefix_fiber {N : ℕ} (used : Tape N → ℕ)
    (hbound : ∀ ρ, used ρ ≤ N)
    (hcausal : ∀ ρ τ, (List.ofFn ρ).take (used ρ) =
      (List.ofFn τ).take (used ρ) → used τ = used ρ)
    (X : Tape N → ℚ) (ρ : Tape N) :
    (∑ τ ∈ (Finset.univ.filter fun τ =>
      stoppedPrefix used τ = stoppedPrefix used ρ), X τ) =
    ∑ tail : Tape (N - used ρ),
      X ((splitEquiv (hbound ρ)).symm ((splitEquiv (hbound ρ) ρ).1, tail)) := by
  classical
  let E := splitEquiv (hbound ρ)
  rw [Finset.sum_filter]
  calc
    (∑ τ, if stoppedPrefix used τ = stoppedPrefix used ρ then X τ else 0) =
      ∑ pair : Tape (used ρ) × Tape (N - used ρ),
        if pair.1 = (E ρ).1 then X (E.symm pair) else 0 := by
          apply Fintype.sum_equiv E
          intro τ
          simp only [Equiv.symm_apply_apply]
          simp only [prefix_eq_iff_split used hbound hcausal ρ τ, E]
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      simp [E]

/-- Conditional bounds on every actual stopped-prefix fiber combine into
an unconditional mean bound. `Y` may be a state potential or the indicator
of an already-observed rejection event times a tail bound. -/
lemma sum_le_of_stopped_prefix {N : ℕ} (used : Tape N → ℕ)
    (hbound : ∀ ρ, used ρ ≤ N)
    (hcausal : ∀ ρ τ, (List.ofFn ρ).take (used ρ) =
      (List.ofFn τ).take (used ρ) → used τ = used ρ)
    (X Y : Tape N → ℚ)
    (hY : ∀ ρ τ, (List.ofFn ρ).take (used ρ) =
      (List.ofFn τ).take (used ρ) → Y τ = Y ρ)
    (hmean : ∀ ρ, (∑ tail : Tape (N - used ρ),
      X ((splitEquiv (hbound ρ)).symm ((splitEquiv (hbound ρ) ρ).1, tail))) ≤
        Y ρ * 2 ^ (N - used ρ)) :
    (∑ ρ, X ρ) ≤ ∑ ρ, Y ρ := by
  classical
  let prefixes := Finset.univ.image (stoppedPrefix used)
  have maps : ∀ ρ ∈ (Finset.univ : Finset (Tape N)),
      stoppedPrefix used ρ ∈ prefixes := fun ρ hρ => Finset.mem_image_of_mem _ hρ
  rw [← Finset.sum_fiberwise_of_maps_to maps X,
    ← Finset.sum_fiberwise_of_maps_to maps Y]
  apply Finset.sum_le_sum
  intro pre hpre
  obtain ⟨ρ, _, rfl⟩ := Finset.mem_image.mp hpre
  rw [sum_prefix_fiber used hbound hcausal X ρ,
    sum_prefix_fiber used hbound hcausal Y ρ]
  have hy (tail : Tape (N - used ρ)) :
      Y ((splitEquiv (hbound ρ)).symm
        ((splitEquiv (hbound ρ) ρ).1, tail)) = Y ρ := by
    apply hY
    rw [prefix_of_split (hbound ρ), prefix_of_split (hbound ρ)]
    simp
  simp only [hy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simpa [card_tape, mul_comm] using hmean ρ

end Lax457868Proofs.StoppedPrefixAveraging
