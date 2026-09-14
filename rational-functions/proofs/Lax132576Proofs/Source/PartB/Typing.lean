/- Claim `claim:typing-length-preserving`: for an nfa with output all of whose states are
productive, the computed function is length preserving if and only if the states can be typed by
integers measuring the difference between the length of the output and the length of the input. -/
import Lax132576Proofs.Source.PartB.LabAut
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace Typing

variable {A B Q : Type} (M : NFAO A B Q)

/-- The difference between the length of the output and the length of the input
of a path. -/
def defect (ts : List (Q × List A × List B × Q)) : ℤ :=
  ((NFAO.outputOf ts).length : ℤ) - (LabAut.inputOf ts).length

@[simp] lemma defect_nil : defect ([] : List (Q × List A × List B × Q)) = 0 := by
  simp [defect]

lemma defect_append (ts ts' : List (Q × List A × List B × Q)) :
    defect (ts ++ ts') = defect ts + defect ts' := by
  simp [defect]
  have h1 : NFAO.outputOf (ts ++ ts') = NFAO.outputOf ts ++ NFAO.outputOf ts' := by
    suffices ∀ l₁ l₂, NFAO.outputOf (l₁ ++ l₂) = NFAO.outputOf l₁ ++ NFAO.outputOf l₂ by
      apply this
    intro l₁ l₂
    induction l₁ with
    | nil => simp [NFAO.outputOf]
    | cons t ts ih => simp [NFAO.outputOf_cons, List.append_assoc, ih]
  have h2 : LabAut.inputOf (ts ++ ts') = LabAut.inputOf ts ++ LabAut.inputOf ts' := by
    suffices ∀ l₁ l₂, LabAut.inputOf (l₁ ++ l₂) = LabAut.inputOf l₁ ++ LabAut.inputOf l₂ by
      apply this
    intro l₁ l₂
    induction l₁ with
    | nil => simp [LabAut.inputOf]
    | cons t ts ih => simp [LabAut.inputOf_cons, List.append_assoc, ih]
  simp [h1, h2]
  ring

/-- If the computed function is length preserving, then all runs from an initial
state to a given state have the same defect. -/
lemma defect_well_defined {f : List A → List B} (hM : ∀ w v, M.rel w v ↔ v = f w)
    (hlen : LengthPreserving f) {q : Q} (hprod : Productive M q)
    {q₁ q₂ : Q} {ts₁ ts₂ : List (Q × List A × List B × Q)}
    (h₁ : q₁ ∈ M.init) (h₂ : q₂ ∈ M.init)
    (hp₁ : M.Path q₁ ts₁ q) (hp₂ : M.Path q₂ ts₂ q) : defect ts₁ = defect ts₂ := by
  -- Since q is productive, there's a path from some initial state to q and from q to some final state
  obtain ⟨q₀, hq₀, p, hp, ts_a, ts_b, hpa, hpb⟩ := hprod
  -- The complete run ts_a ++ ts_b is accepting, so output = f input
  have hrel : M.rel (LabAut.inputOf (ts_a ++ ts_b)) (NFAO.outputOf (ts_a ++ ts_b)) := by
    refine ⟨ts_a ++ ts_b, ⟨q₀, hq₀, p, hp, LabAut.Path.append hpa hpb⟩, rfl, rfl⟩
  rw [hM] at hrel
  -- f is length-preserving, so lengths are equal
  have hlen_eq : (f (LabAut.inputOf (ts_a ++ ts_b))).length = (LabAut.inputOf (ts_a ++ ts_b)).length := hlen _
  rw [hrel.symm] at hlen_eq
  -- defect(ts_a ++ ts_b) = 0
  have hdefect_ab : defect (ts_a ++ ts_b) = 0 := by simp [defect]; rw [hlen_eq]; ring
  rw [defect_append] at hdefect_ab
  -- Similarly, ts₁ ++ ts_b is also an accepting run, so defect ts₁ + defect ts_b = 0
  have hrel1 : M.rel (LabAut.inputOf (ts₁ ++ ts_b)) (NFAO.outputOf (ts₁ ++ ts_b)) := by
    refine ⟨ts₁ ++ ts_b, ⟨q₁, h₁, p, hp, LabAut.Path.append hp₁ hpb⟩, rfl, rfl⟩
  rw [hM] at hrel1
  have hlen_eq1 : (f (LabAut.inputOf (ts₁ ++ ts_b))).length = (LabAut.inputOf (ts₁ ++ ts_b)).length := hlen _
  rw [hrel1.symm] at hlen_eq1
  have hdefect_1b : defect (ts₁ ++ ts_b) = 0 := by simp [defect]; rw [hlen_eq1]; ring
  rw [defect_append] at hdefect_1b
  -- Similarly for ts₂
  have hrel2 : M.rel (LabAut.inputOf (ts₂ ++ ts_b)) (NFAO.outputOf (ts₂ ++ ts_b)) := by
    refine ⟨ts₂ ++ ts_b, ⟨q₂, h₂, p, hp, LabAut.Path.append hp₂ hpb⟩, rfl, rfl⟩
  rw [hM] at hrel2
  have hlen_eq2 : (f (LabAut.inputOf (ts₂ ++ ts_b))).length = (LabAut.inputOf (ts₂ ++ ts_b)).length := hlen _
  rw [hrel2.symm] at hlen_eq2
  have hdefect_2b : defect (ts₂ ++ ts_b) = 0 := by simp [defect]; rw [hlen_eq2]; ring
  rw [defect_append] at hdefect_2b
  linarith

end Typing

/-- **Claim `claim:typing-length-preserving`.**  For an nfa with output whose states are all
productive, the computed function is length-preserving if and only if a typing `τ : Q → ℤ` exists
(i.e. every run from an initial state to `q` satisfies `|output| = |input| + τ q`) and all accepting
states are mapped to zero. -/
theorem lengthPreserving_iff_typing_aux {A B Q : Type} (M : NFAO A B Q)
    (hprod : ∀ q, Productive M q) {f : List A → List B} (hM : ∀ w v, M.rel w v ↔ v = f w) :
    LengthPreserving f ↔
      ∃ τ : Q → ℤ,
        (∀ q ∈ M.init, ∀ ts p, M.Path q ts p →
          ((NFAO.outputOf ts).length : ℤ) = (LabAut.inputOf ts).length + τ p) ∧
        ∀ p ∈ M.final, τ p = 0 := by
  constructor
  · intro hlength
    -- Every state is productive, so there's a path from an initial state to any state
    -- We use this to define τ
    -- τ(p) = defect of some path from an initial state to p
    -- By defect_well_defined, this is independent of the path chosen
    -- First, we need that every state is reachable from an initial state
    have hreach : ∀ q : Q, ∃ q₀ ∈ M.init, ∃ ts : List (Q × List A × List B × Q), M.Path q₀ ts q := by
      intro q
      obtain ⟨q₀, hq₀, _, _, ts₁, _, hts₁, _⟩ := hprod q
      exact ⟨q₀, hq₀, ts₁, hts₁⟩
    -- Pick for each state a witness (initial state, path)
    choose q₀ hq₀ ts hp using hreach
    -- Define τ based on defect of the chosen path
    let τ : Q → ℤ := fun p => Typing.defect (ts p)
    use τ
    refine ⟨?_, ?_⟩
    · intro q hq ts' p hpath'
      have hdefect_eq : Typing.defect (ts p) = Typing.defect ts' := by
        apply Typing.defect_well_defined M hM hlength (hprod p) (hq₀ p) hq (hp p) hpath'
      show _ = _ + Typing.defect (ts p)
      rw [hdefect_eq]
      simp [Typing.defect]
    · intro p hf
      show Typing.defect (ts p) = 0
      -- ts p is a path from q₀ p ∈ M.init to p ∈ M.final, so it's accepting
      -- Therefore defect(ts p) = 0
      have h_accept : M.rel (LabAut.inputOf (ts p)) (NFAO.outputOf (ts p)) := by
        refine ⟨ts p, ⟨q₀ p, hq₀ p, p, hf, hp p⟩, rfl, rfl⟩
      rw [hM] at h_accept
      have hlen : (f (LabAut.inputOf (ts p))).length = (LabAut.inputOf (ts p)).length := hlength _
      rw [h_accept.symm] at hlen
      simp [Typing.defect, hlen]
  · intro ⟨τ, hτ_path, hτ_final⟩ w
    -- By hM, M.rel w (f w) holds
    have hrel : M.rel w (f w) := (hM w (f w)).mpr rfl
    -- Parse the rel relation to get an accepting run
    rw [NFAO.rel_iff_relFrom] at hrel
    obtain ⟨q, hq, p, hp, ts, hpath, hw_eq, hv_eq⟩ := hrel
    rw [hv_eq.symm] at ⊢
    have heq := hτ_path q hq ts p hpath
    rw [hw_eq] at heq
    linarith [hτ_final p hp]

end Lax132576Proofs.Transducers
