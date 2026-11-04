import Lax185574Proofs.Lib.BallFlipParameters

/-! Adapted from an earlier formalization by Szymon Toruńczyk, see PROVENANCE.md. -/


namespace Lax185574Proofs.Lib.BallFlipConstruction

open Lax185574Proofs.Lib.BallFlips Lax185574Proofs.Lib.DefinableFlips Lax185574Proofs.Lib.BoundedVCDuality
open BallFlipTraces

universe u

def edgeToggle {V : Type u} (G : SimpleGraph V) (A B S : Finset V) (x y : V) : Prop :=
  ∃ a ∈ A, ∃ b ∈ B, G.Adj a b ∧
    ((atomicProfile G S x = atomicProfile G S a ∧
      atomicProfile G S y = atomicProfile G S b) ∨
     (atomicProfile G S x = atomicProfile G S b ∧
      atomicProfile G S y = atomicProfile G S a))

theorem edgeToggle_symm {V : Type u} (G : SimpleGraph V) (A B S : Finset V) (x y : V) :
    edgeToggle G A B S x y ↔ edgeToggle G A B S y x := by
  simp only [edgeToggle]
  congr! 5
  tauto

def edgeFlip {V : Type u} (G : SimpleGraph V) (A B S : Finset V) : SimpleGraph V where
  Adj x y := x ≠ y ∧ Xor (G.Adj x y) (edgeToggle G A B S x y)
  symm := ⟨by
    intro x y h
    exact ⟨h.1.symm, by
      simpa only [G.adj_comm, edgeToggle_symm G A B S y x] using h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

theorem edgeFlip_isBased {V : Type u} (G : SimpleGraph V) (A B S : Finset V) :
    IsBasedFlip G S (edgeFlip G A B S) := by
  refine ⟨edgeToggle G A B S, edgeToggle_symm G A B S, ?_, fun _ _ => Iff.rfl⟩
  intro x x' y y' hx hy
  simp only [edgeToggle, hx, hy]

section

variable {V : Type u} [DecidableEq V] {G : SimpleGraph V} {A B D S : Finset V}
variable (hrepA : ∀ a ∈ A, ∃ a₀ ∈ S, a₀ ∈ A ∧ trace G B a₀ = trace G B a)
variable (hrepB : ∀ b ∈ B, ∃ b₀ ∈ S, b₀ ∈ B ∧ trace G A b₀ = trace G A b)

include hrepA hrepB

theorem no_edges_AB
    (hdual : ∀ a ∈ A, ∀ a' ∈ A,
      Dominates G (S ∩ traceClass G A B a) (traceClass G A B a') ∨
      Antidominates G (S ∩ traceClass G A B a') (traceClass G A B a)) :
    ∀ a ∈ A, ∀ b ∈ B, ¬ (edgeFlip G A B S).Adj a b := by
  intro a ha b hb hH
  rcases hH.2 with ⟨hab, hn⟩ | ⟨ht, hn⟩
  · exact hn ⟨a, ha, b, hb, hab, Or.inl ⟨rfl, rfl⟩⟩
  · obtain ⟨a', ha', b', hb', hab', hor⟩ := ht
    rcases hor with ⟨haa', hbb'⟩ | ⟨hapb', hba'⟩
    · have htA := profile_trace hrepB ha ha' haa'
      have htB := profile_trace hrepA hb hb' hbb'
      have h₁ := (trace_eq_iff G B a a').mp htA b hb
      have h₂ := (trace_eq_iff G A b b').mp htB a' ha'
      exact hn (h₁.mpr ((h₂.mpr hab'.symm).symm))
    · rcases hdual a ha a' ha' with hdom | hanti
      · obtain ⟨z, hz, hza'⟩ := hdom a' (self_mem_traceClass ha')
        obtain ⟨hzS, hzX⟩ := Finset.mem_inter.mp hz
        have hztr := (mem_traceClass.mp hzX).2
        have hzb := (trace_eq_iff G B z a).mp hztr b hb
        have hba := profile_adj hba' hzS
        exact hn (hzb.mp ((hba.mpr hza'.symm).symm))
      · obtain ⟨z, hz, hnaz⟩ := hanti a (self_mem_traceClass ha)
        obtain ⟨hzS, hzX⟩ := Finset.mem_inter.mp hz
        have hztr := (mem_traceClass.mp hzX).2
        have hzb' := (trace_eq_iff G B z a').mp hztr b' hb'
        exact hnaz ((profile_adj hapb' hzS).mpr (hzb'.mpr hab').symm)

omit [DecidableEq V] in
theorem no_toggle_far {b : V} (hb : b ∈ B)
    (hfar₁ : ∀ a ∈ A, ¬ G.Adj b a)
    (hfar₂ : ∀ z a, a ∈ A → G.Adj b z → ¬ G.Adj z a) :
    ∀ x, ¬ edgeToggle G A B S b x := by
  intro x ht
  obtain ⟨a, ha, b', hb', hab', hor⟩ := ht
  rcases hor with ⟨hba, _⟩ | ⟨hbb', _⟩
  · obtain ⟨b₀, hb₀S, _, hb₀tr⟩ := hrepB b' hb'
    have hb₀a := (trace_eq_iff G A b₀ b').mp hb₀tr a ha
    have hab₀ := (hb₀a.mpr hab'.symm).symm
    exact hfar₂ b₀ a ha ((profile_adj hba hb₀S).mpr hab₀) hab₀.symm
  · have htB := profile_trace hrepA hb hb' hbb'
    exact hfar₁ a ha ((trace_eq_iff G A b b').mp htB a ha |>.mpr hab'.symm)

omit hrepB in
theorem no_edges_D_outside (hDB : D ⊆ B)
    (hDA : ∀ a ∈ A, a ∉ B)
    (hclosed : ∀ d ∈ D, ∀ x, G.Adj d x → x ∈ B)
    (hdual : ∀ b ∈ B,
      Dominates G (S ∩ D) (traceClass G B A b) ∨
      Antidominates G (S ∩ traceClass G B A b) D) :
    ∀ d ∈ D, ∀ x, (edgeFlip G A B S).Adj d x → x ∈ B := by
  intro d hd x hH
  by_contra hx
  have hnot : ¬ G.Adj d x := fun h => hx (hclosed d hd x h)
  have ht : edgeToggle G A B S d x := by
    rcases hH.2 with ⟨h, _⟩ | ⟨h, _⟩
    · exact (hnot h).elim
    · exact h
  obtain ⟨a, ha, b, hb, hab, hor⟩ := ht
  rcases hor with ⟨hda, hxb⟩ | ⟨hdb, _⟩
  · rcases hdual b hb with hdom | hanti
    · obtain ⟨z, hz, hzb⟩ := hdom b (self_mem_traceClass hb)
      obtain ⟨hzS, hzD⟩ := Finset.mem_inter.mp hz
      exact hx (hclosed z hzD x ((profile_adj hxb hzS).mpr hzb.symm).symm)
    · obtain ⟨z, hz, hndz⟩ := hanti d hd
      obtain ⟨hzS, hzY⟩ := Finset.mem_inter.mp hz
      have hztr := (mem_traceClass.mp hzY).2
      have hza := (trace_eq_iff G A z b).mp hztr a ha
      exact hndz ((profile_adj hda hzS).mpr (hza.mpr hab.symm).symm)
  · have htB := profile_trace hrepA (hDB hd) hb hdb
    have hda := (trace_eq_iff G A d b).mp htB a ha |>.mpr hab.symm
    exact hDA a ha (hclosed d hd a hda)

end

end Lax185574Proofs.Lib.BallFlipConstruction
