import Lax185574Proofs.Lib.BallFlipsDefs
import Lax185574Proofs.Lib.DefinableFlips
import Mathlib.Data.Finset.Powerset

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


namespace Lax185574Proofs.Lib.BallFlipTraces

open Lax185574Proofs.Lib.BallFlips Lax185574Proofs.Lib.DefinableFlips

universe u v

theorem trace_eq_iff {V : Type u} (G : SimpleGraph V) (A : Finset V) (x y : V) :
    trace G A x = trace G A y ↔ ∀ a ∈ A, (G.Adj x a ↔ G.Adj y a) := by
  classical
  simp only [trace, Finset.ext_iff, Finset.mem_filter]
  exact ⟨fun h a ha => (and_iff_right ha).symm.trans ((h a).trans (and_iff_right ha)),
    fun h a => and_congr_right (h a)⟩

theorem profile_adj {V : Type u} {G : SimpleGraph V} {S : Finset V} {x y a : V}
    (h : atomicProfile G S x = atomicProfile G S y) (ha : a ∈ S) :
    G.Adj x a ↔ G.Adj y a :=
  ((DefinableFlips.atomicProfile_eq_iff G S x y).mp h a ha).1

noncomputable def traceClass {V : Type u} (G : SimpleGraph V) (A B : Finset V)
    (a : V) : Finset V := by
  classical
  exact A.filter (fun x => trace G B x = trace G B a)

theorem mem_traceClass {V : Type u} {G : SimpleGraph V} {A B : Finset V} {x a : V} :
    x ∈ traceClass G A B a ↔ x ∈ A ∧ trace G B x = trace G B a := by
  classical
  simp [traceClass]

theorem self_mem_traceClass {V : Type u} {G : SimpleGraph V} {A B : Finset V}
    {a : V} (ha : a ∈ A) : a ∈ traceClass G A B a := mem_traceClass.mpr ⟨ha, rfl⟩

theorem profile_trace {V : Type u} {G : SimpleGraph V} {A B S : Finset V}
    (hreps : ∀ b ∈ B, ∃ b₀ ∈ S, b₀ ∈ B ∧ trace G A b₀ = trace G A b)
    {a a' : V} (ha : a ∈ A) (ha' : a' ∈ A)
    (heq : atomicProfile G S a = atomicProfile G S a') : trace G B a = trace G B a' := by
  apply (trace_eq_iff G B a a').mpr
  intro b hb
  obtain ⟨b₀, hb₀S, _, htr⟩ := hreps b hb
  have h₁ := (trace_eq_iff G A b₀ b).mp htr a ha
  have h₂ := (trace_eq_iff G A b₀ b).mp htr a' ha'
  have hp := profile_adj heq hb₀S
  have hp' : G.Adj b₀ a ↔ G.Adj b₀ a' := by simpa only [G.adj_comm] using hp
  simpa only [G.adj_comm] using h₁.symm.trans (hp'.trans h₂)

theorem exists_representatives {V : Type u} {W : Type v} [DecidableEq W]
    (A : Finset V) (f : V → W) :
    ∃ R : Finset V, R ⊆ A ∧ R.card ≤ (A.image f).card ∧
      ∀ a ∈ A, ∃ b ∈ R, f b = f a := by
  classical
  let I := A.image f
  have hr (i : I) : ∃ a ∈ A, f a = i.val := Finset.mem_image.mp i.property
  choose rep hrep using hr
  let R := Finset.univ.image rep
  refine ⟨R, ?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact (hrep i).1
  · calc R.card ≤ (Finset.univ : Finset I).card := Finset.card_image_le
         _ = I.card := by simp
  · intro a ha
    let i : I := ⟨f a, Finset.mem_image_of_mem f ha⟩
    exact ⟨rep i, Finset.mem_image_of_mem rep (Finset.mem_univ i), (hrep i).2⟩

/-- Representatives on both sides, with the elementary dual trace bound. -/
theorem exists_trace_representatives {V : Type u} (G : SimpleGraph V) (A B : Finset V)
    (t : ℕ) (ht : (traces G A B).card ≤ t) :
    ∃ A₀ B₀ : Finset V,
      A₀ ⊆ A ∧ B₀ ⊆ B ∧ A₀.card ≤ 2 ^ t ∧ B₀.card ≤ t ∧
      (∀ a ∈ A, ∃ a₀ ∈ A₀, trace G B a₀ = trace G B a) ∧
      (∀ b ∈ B, ∃ b₀ ∈ B₀, trace G A b₀ = trace G A b) := by
  classical
  obtain ⟨B₀, hB₀, hcardB, hrepB⟩ := exists_representatives B (trace G A)
  have hBt : B₀.card ≤ t := hcardB.trans ht
  obtain ⟨A₀, hA₀, hcardA, hrepA⟩ := exists_representatives A (trace G B₀)
  have hpow : (A.image (trace G B₀)).card ≤ 2 ^ B₀.card := by
    rw [← Finset.card_powerset]
    apply Finset.card_le_card
    intro X hX
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hX
    exact Finset.mem_powerset.mpr (Finset.filter_subset _ _)
  refine ⟨A₀, B₀, hA₀, hB₀,
    hcardA.trans (hpow.trans (Nat.pow_le_pow_right (by decide) hBt)), hBt, ?_, hrepB⟩
  intro a ha
  obtain ⟨a₀, ha₀, heq⟩ := hrepA a ha
  refine ⟨a₀, ha₀, (trace_eq_iff G B a₀ a).mpr ?_⟩
  intro b hb
  obtain ⟨b₀, hb₀, hbeq⟩ := hrepB b hb
  have hb₁ := (trace_eq_iff G A b₀ b).mp hbeq a₀ (hA₀ ha₀)
  have hb₂ := (trace_eq_iff G A b₀ b).mp hbeq a ha
  have ha₁ := (trace_eq_iff G B₀ a₀ a).mp heq b₀ hb₀
  have ha₂ : G.Adj b₀ a₀ ↔ G.Adj b₀ a := by simpa only [G.adj_comm] using ha₁
  simpa only [G.adj_comm] using hb₁.symm.trans (ha₂.trans hb₂)

end Lax185574Proofs.Lib.BallFlipTraces
