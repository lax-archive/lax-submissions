/-
Closure of rational relations under composition (Theorem `thm:composition-rational-relations`).

Both relations are first put in the atomic normal form of
`RequestProject/PartB/Atomize.lean`, so that a transition reads at most one letter and
writes at most one letter.  The composition is then computed by the product
automaton, whose transitions either

* combine a transition of the first automaton writing a letter `b` with a
  transition of the second automaton reading `b`,
* use a transition of the first automaton writing nothing, or
* use a transition of the second automaton reading nothing.
-/
import Lax132576Proofs.Source.PartB.Atomize
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace RatComp

variable {A B C Q P : Type} (M : NFAO A B Q) (N : NFAO B C P)

/-- The transitions of the product automaton. -/
def prodDelta : Set ((Q × P) × List A × List C × (Q × P)) :=
  {x | ∃ q u b q' p y p', (q, u, [b], q') ∈ M.δ ∧ (p, [b], y, p') ∈ N.δ ∧
        x = ((q, p), u, y, (q', p'))} ∪
  {x | ∃ q u q' p, (q, u, [], q') ∈ M.δ ∧ x = ((q, p), u, [], (q', p))} ∪
  {x | ∃ p y p' q, (p, [], y, p') ∈ N.δ ∧ x = ((q, p), [], y, (q, p'))}

lemma prodDelta_finite [Finite Q] [Finite P] : (prodDelta M N).Finite := by
  apply Set.Finite.union
  · apply Set.Finite.union
    · -- First set: combined transitions
      have h : ∀ x : (Q × P) × List A × List C × (Q × P),
          (∃ q u b q' p y p', (q, u, [b], q') ∈ M.δ ∧ (p, [b], y, p') ∈ N.δ ∧ x = ((q, p), u, y, (q', p'))) →
          x ∈ Set.image (fun (z : ((Q × List A × List B × Q) × (P × List B × List C × P))) =>
            ((z.1.1, z.2.1), z.1.2.1, z.2.2.2.1, (z.1.2.2.2, z.2.2.2.2)) :
            ((Q × List A × List B × Q) × (P × List B × List C × P)) → (Q × P) × List A × List C × (Q × P))
          ({t | t.1.2.2.1 = t.2.2.1} ∩ (M.δ ×ˢ N.δ)) := by
        intro x hx
        obtain ⟨q, u, b, q', p, y, p', hM, hN, rfl⟩ := hx
        refine ⟨((q, u, [b], q'), (p, [b], y, p')), ?_, rfl⟩
        simp [hM, hN]
      apply Set.Finite.subset _ h
      apply Set.Finite.image _
      exact Set.Finite.subset (M.δ_finite.prod N.δ_finite) (fun x hx => hx.2)
    · -- Second set: M transition only
      have h : ∀ x : (Q × P) × List A × List C × (Q × P),
          (∃ q u q' p, (q, u, ([] : List B), q') ∈ M.δ ∧ x = ((q, p), u, ([] : List C), (q', p))) →
          x ∈ Set.image (fun (z : (Q × List A × List B × Q) × P) => ((z.1.1, z.2), z.1.2.1, ([] : List C), (z.1.2.2.2, z.2))) (M.δ ×ˢ Set.univ) := by
        intro x hx
        obtain ⟨q, u, q', p, ht, rfl⟩ := hx
        exact ⟨((q, u, [], q'), p), ⟨ht, trivial⟩, rfl⟩
      exact Set.Finite.subset ((M.δ_finite.prod Set.finite_univ).image _) h
  · -- Third set: N transition only
    have h : ∀ x : (Q × P) × List A × List C × (Q × P),
        (∃ p y p' q, (p, ([] : List B), y, p') ∈ N.δ ∧ x = ((q, p), ([] : List A), y, (q, p'))) →
        x ∈ Set.image (fun (z : (P × List B × List C × P) × Q) => ((z.2, z.1.1), ([] : List A), z.1.2.2.1, (z.2, z.1.2.2.2)) :
          ((P × List B × List C × P) × Q) → (Q × P) × List A × List C × (Q × P)) (N.δ ×ˢ (Set.univ : Set Q)) := by
      intro x hx
      obtain ⟨p, y, p', q, ht, rfl⟩ := hx
      exact ⟨((p, [], y, p'), q), ⟨ht, trivial⟩, rfl⟩
    exact Set.Finite.subset ((N.δ_finite.prod (Set.finite_univ : Set.Finite (Set.univ : Set Q))).image _) h

/-- The product automaton computing the composition of the two relations. -/
def prodAut [Finite Q] [Finite P] : NFAO A C (Q × P) where
  init := {s | s.1 ∈ M.init ∧ s.2 ∈ N.init}
  final := {s | s.1 ∈ M.final ∧ s.2 ∈ N.final}
  δ := prodDelta M N
  δ_finite := prodDelta_finite M N

/-! ### The product automaton computes the composition -/

/-- Soundness: every run of the product automaton splits into a run of `M` and a
run of `N`. -/
lemma prod_sound [Finite Q] [Finite P] {q q' : Q} {p p' : P} {w : List A} {y : List C}
    (h : (prodAut M N).relFrom (q, p) w y (q', p')) :
    ∃ v : List B, M.relFrom q w v q' ∧ N.relFrom p v y p' := by
  have := NFAO.relFrom_induction (M := prodAut M N)
    (motive := fun q w v => ∃ v' : List B, M.relFrom (q.1) w v' q' ∧ N.relFrom (q.2) v' v p')
    (hnil := by
      use []
      exact ⟨NFAO.relFrom_nil M q', NFAO.relFrom_nil N p'⟩)
    (hcons := by
      intro qs qst u x w v ht ih
      rcases qs with ⟨q₁, p₁⟩
      rcases qst with ⟨q₂, p₂⟩
      simp only [prodAut, prodDelta] at ht
      simp only [Set.union_assoc, Set.mem_union, Set.mem_setOf_eq] at ht
      rcases ht with ⟨q, u₁, b, q₃, p, y, p₃, hM, hN, heq⟩ | ⟨q, u₁, q₃, p, hM, heq⟩ | ⟨p, y, p₃, q, hN, heq⟩
      · -- Case 1: combined transition
        simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩
        intro ih
        obtain ⟨v', ⟨hM', hN'⟩⟩ := ih
        use [b] ++ v'
        exact ⟨M.relFrom_trans (NFAO.relFrom_single hM) hM', N.relFrom_trans (NFAO.relFrom_single hN) hN'⟩
      · -- Case 2: M transition only
        simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩
        intro ih
        obtain ⟨v', ⟨hM', hN'⟩⟩ := ih
        use v'
        exact ⟨M.relFrom_trans (NFAO.relFrom_single hM) hM', hN'⟩
      · -- Case 3: N transition only
        simp only [Prod.mk.injEq] at heq
        rcases heq with ⟨⟨rfl, rfl⟩, ⟨rfl, rfl, rfl, rfl⟩⟩
        intro ih
        obtain ⟨v', ⟨hM', hN'⟩⟩ := ih
        use v'
        exact ⟨hM', N.relFrom_trans (NFAO.relFrom_single hN) hN'⟩)
    h
  exact this

/-- The product automaton can follow the transitions of `N` that read nothing. -/
lemma prod_epsN [Finite Q] [Finite P] (q : Q) {p p' : P}
    {ts₂ : List (P × List B × List C × P)} (h : N.Path p ts₂ p')
    (hin : LabAut.inputOf ts₂ = []) :
    (prodAut M N).relFrom (q, p) [] (NFAO.outputOf ts₂) (q, p') := by
  induction h with
  | nil p => exact NFAO.relFrom_nil _ _
  | @cons p1 u y p2 ts pend ht hpath ih =>
      simp only [LabAut.inputOf_cons, List.append_eq_nil_iff] at hin
      obtain ⟨hu, hts⟩ := hin
      have hmem : ((q, p1), ([] : List A), y, (q, p2)) ∈ (prodAut M N).δ := by
        show _ ∈ prodDelta M N
        refine Or.inr ⟨p1, y, p2, q, ?_, rfl⟩
        simpa [hu] using ht
      simpa using NFAO.relFrom_step (M := prodAut M N) hmem (ih hts)

/-- Completeness, stated for paths so that it can be proved by induction on the
total number of transitions used. -/
lemma prod_complete_aux [Finite Q] [Finite P]
    (hM : ∀ t ∈ M.δ, t.2.1.length ≤ 1 ∧ t.2.2.1.length ≤ 1)
    (hN : ∀ t ∈ N.δ, t.2.1.length ≤ 1 ∧ t.2.2.1.length ≤ 1) :
    ∀ (n : ℕ) (ts₁ : List (Q × List A × List B × Q)) (ts₂ : List (P × List B × List C × P))
      (q q' : Q) (p p' : P), ts₁.length + ts₂.length ≤ n →
      M.Path q ts₁ q' → N.Path p ts₂ p' → LabAut.inputOf ts₂ = NFAO.outputOf ts₁ →
      (prodAut M N).relFrom (q, p) (LabAut.inputOf ts₁) (NFAO.outputOf ts₂) (q', p') := by
  intro n
  induction n with
  | zero =>
      intro ts₁ ts₂ q q' p p' hlen h₁ h₂ _
      have e1 : ts₁ = [] := List.eq_nil_of_length_eq_zero (by omega)
      have e2 : ts₂ = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst e1; subst e2
      cases h₁; cases h₂
      simpa using NFAO.relFrom_nil (prodAut M N) (q, p)
  | succ n ih =>
      intro ts₁ ts₂ q q' p p' hlen h₁ h₂ heq
      cases h₁ with
      | nil q =>
          simp only [NFAO.outputOf_nil] at heq
          simpa using prod_epsN M N q h₂ heq
      | cons ht hrest =>
          rename_i u x q1 rest
          have hx : x.length ≤ 1 := (hM _ ht).2
          rcases x with _ | ⟨b, x'⟩
          · -- the transition of `M` writes nothing
            have hmem : ((q, p), u, ([] : List C), (q1, p)) ∈ (prodAut M N).δ :=
              Or.inl (Or.inr ⟨q, u, q1, p, ht, rfl⟩)
            have hrec := ih rest ts₂ q1 q' p p' (by simp at hlen ⊢; omega) hrest h₂
              (by simpa using heq)
            simpa using NFAO.relFrom_step (M := prodAut M N) hmem hrec
          · have hx' : x' = [] := by
              simp only [List.length_cons] at hx
              exact List.eq_nil_of_length_eq_zero (by omega)
            subst hx'
            simp only [NFAO.outputOf_cons, List.cons_append, List.nil_append] at heq
            cases h₂ with
            | nil p => simp at heq
            | cons ht2 hrest2 =>
                rename_i u2 y p2 rest2
                have hu2 : u2.length ≤ 1 := (hN _ ht2).1
                rcases u2 with _ | ⟨b', u2'⟩
                · -- the transition of `N` reads nothing
                  have hmem : ((q, p), ([] : List A), y, (q, p2)) ∈ (prodAut M N).δ :=
                    Or.inr ⟨p, y, p2, q, ht2, rfl⟩
                  have heq' : LabAut.inputOf rest2
                      = NFAO.outputOf ((q, u, [b], q1) :: rest) := by simpa using heq
                  have hrec := ih ((q, u, [b], q1) :: rest) rest2 q q' p2 p'
                    (by simp at hlen ⊢; omega) (LabAut.Path.cons ht hrest) hrest2 heq'
                  simpa using NFAO.relFrom_step (M := prodAut M N) hmem hrec
                · -- the two transitions are combined
                  have hu2' : u2' = [] := by
                    simp only [List.length_cons] at hu2
                    exact List.eq_nil_of_length_eq_zero (by omega)
                  subst hu2'
                  simp only [LabAut.inputOf_cons, List.cons_append, List.nil_append,
                    List.cons.injEq] at heq
                  obtain ⟨rfl, heq2⟩ := heq
                  have hmem : ((q, p), u, y, (q1, p2)) ∈ (prodAut M N).δ :=
                    Or.inl (Or.inl ⟨q, u, b', q1, p, y, p2, ht, ht2, rfl⟩)
                  have hrec := ih rest rest2 q1 q' p2 p' (by simp at hlen ⊢; omega)
                    hrest hrest2 (by simpa using heq2)
                  simpa using NFAO.relFrom_step (M := prodAut M N) hmem hrec

lemma prod_complete [Finite Q] [Finite P]
    (hM : ∀ t ∈ M.δ, t.2.1.length ≤ 1 ∧ t.2.2.1.length ≤ 1)
    (hN : ∀ t ∈ N.δ, t.2.1.length ≤ 1 ∧ t.2.2.1.length ≤ 1)
    {q q' : Q} {p p' : P} {w : List A} {v : List B} {y : List C}
    (h₁ : M.relFrom q w v q') (h₂ : N.relFrom p v y p') :
    (prodAut M N).relFrom (q, p) w y (q', p') := by
  obtain ⟨ts₁, hp₁, rfl, rfl⟩ := h₁
  obtain ⟨ts₂, hp₂, hin₂, rfl⟩ := h₂
  exact prod_complete_aux M N hM hN (ts₁.length + ts₂.length) ts₁ ts₂ q q' p p' le_rfl hp₁ hp₂ hin₂

lemma prodAut_rel [Finite Q] [Finite P]
    (hM : ∀ t ∈ M.δ, t.2.1.length ≤ 1 ∧ t.2.2.1.length ≤ 1)
    (hN : ∀ t ∈ N.δ, t.2.1.length ≤ 1 ∧ t.2.2.1.length ≤ 1) (w : List A) (y : List C) :
    (prodAut M N).rel w y ↔ ∃ v, M.rel w v ∧ N.rel v y := by
  rw [NFAO.rel_iff_relFrom]
  constructor
  · rintro ⟨⟨q, p⟩, ⟨hq, hp⟩, ⟨q', p'⟩, ⟨hq', hp'⟩, hrel⟩
    obtain ⟨v, h₁, h₂⟩ := prod_sound M N hrel
    exact ⟨v, (M.rel_iff_relFrom w v).2 ⟨q, hq, q', hq', h₁⟩,
      (N.rel_iff_relFrom v y).2 ⟨p, hp, p', hp', h₂⟩⟩
  · rintro ⟨v, h₁, h₂⟩
    rw [NFAO.rel_iff_relFrom] at h₁ h₂
    obtain ⟨q, hq, q', hq', h₁⟩ := h₁
    obtain ⟨p, hp, p', hp', h₂⟩ := h₂
    exact ⟨(q, p), ⟨hq, hp⟩, (q', p'), ⟨hq', hp'⟩, prod_complete M N hM hN h₁ h₂⟩

end RatComp

/-- **Theorem `thm:composition-rational-relations`.**  Rational relations are closed under
relational composition. -/
theorem rationalRel_comp_aux {A B C : Type} {R : List A → List B → Prop}
    {S : List B → List C → Prop} (hR : IsRationalRel R) (hS : IsRationalRel S) :
    IsRationalRel (fun w v => ∃ u, R w u ∧ S u v) := by
  obtain ⟨Q, hQ, M, hMatom, hMrel⟩ := exists_atomic_nfao hR
  obtain ⟨P, hP, N, hNatom, hNrel⟩ := exists_atomic_nfao hS
  refine ⟨Q × P, inferInstance, RatComp.prodAut M N, fun w y => ?_⟩
  rw [RatComp.prodAut_rel M N hMatom hNatom]
  constructor
  · rintro ⟨u, hu, hv⟩
    exact ⟨u, (hMrel w u).1 hu, (hNrel u y).1 hv⟩
  · rintro ⟨u, hu, hv⟩
    exact ⟨u, (hMrel w u).2 hu, (hNrel u y).2 hv⟩

end Lax132576Proofs.Transducers
