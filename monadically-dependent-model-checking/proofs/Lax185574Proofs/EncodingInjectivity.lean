import Lax185574Proofs.Legacy
import Lax185574Proofs.Words.PrefixFree

/-!
The encodings of type trees, partial graphs, formulas and construction
scripts are prefix codes. Each is built from the basic encodings, whose
prefix property is in `Lax185574Proofs.Words.PrefixFree`, by products,
lists and finite sets, or by a structural recursion with one opcode per
constructor and fixed arities, which is decoded by induction.
-/

namespace Lax185574Proofs.EncodingInjectivity

open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574.DistanceLogic
open Lax185574.SequenceEncoding Lax185574.InstanceEncoding
open Lax185574Proofs.Words

/-- A graph on `Fin n` is a prefix code: the family of its neighborhoods
determines it. -/
instance prefixFree_simpleGraph (n : ℕ) : PrefixFree (SimpleGraph (Fin n)) where
  prefix_inj G H r s h := by
    classical
    obtain ⟨h1, h2⟩ := prefix_inj' (α := Fin n → Finset (Fin n)) h
    refine ⟨?_, h2⟩
    ext u v
    have := congrArg (v ∈ ·) (congrFun h1 u)
    simpa using this

/-- The steps of a script are a prefix code. -/
instance prefixFree_step : PrefixFree Step :=
  prefixFree_of_length 3 (fun a => by cases a <;> rfl) (fun a b h => by
    cases a <;> cases b <;>
      simp_all [word_simps, stepCode])

/-- The prefix property of the code of distance formulas, by induction. -/
theorem distFO_code_prefix {ℓ : ℕ} (φ : DistFO ℓ) :
    ∀ (ψ : DistFO ℓ) (r s : List ℕ), DistFO.code φ ++ r = DistFO.code ψ ++ s → φ = ψ ∧ r = s := by
  induction φ with
  | not φ ih =>
    intro ψ r s h
    cases ψ <;> simp only [DistFO.code, List.cons_append, List.cons.injEq] at h <;>
      first | omega | skip
    obtain ⟨h1, h2⟩ := ih _ _ _ h.2
    exact ⟨by rw [h1], h2⟩
  | and φ φ' ih ih' =>
    intro ψ r s h
    cases ψ <;> simp only [DistFO.code, List.cons_append, List.cons.injEq,
      List.append_assoc] at h <;> first | omega | skip
    obtain ⟨h1, h'⟩ := ih _ _ _ h.2
    obtain ⟨h2, h3⟩ := ih' _ _ _ h'
    exact ⟨by rw [h1, h2], h3⟩
  | exLocal i t φ ih =>
    intro ψ r s h
    cases ψ <;> simp only [DistFO.code, List.cons_append, List.cons.injEq] at h <;>
      first | omega | skip
    obtain ⟨h1, h2⟩ := ih _ _ _ h.2.2.2
    obtain rfl : i = _ := Fin.ext h.2.1
    obtain rfl := h.2.2.1
    exact ⟨by rw [h1], h2⟩
  | _ =>
    intro ψ r s h
    cases ψ <;> simp only [DistFO.code, List.cons_append, List.cons.injEq, List.nil_append] at h <;>
      first | omega | skip
    all_goals simp_all [Fin.val_inj]

/-- The prefix property of the code of first-order formulas, by
induction. -/
theorem fo_code_prefix {k : ℕ} (φ : Lax3.FirstOrder.FO k) :
    ∀ (ψ : Lax3.FirstOrder.FO k) (r s : List ℕ), code φ ++ r = code ψ ++ s → φ = ψ ∧ r = s := by
  induction φ with
  | not φ ih =>
    intro ψ r s h
    cases ψ <;> simp only [code, List.cons_append, List.cons.injEq] at h <;>
      first | omega | skip
    obtain ⟨h1, h2⟩ := ih _ _ _ h.2
    exact ⟨by rw [h1], h2⟩
  | and φ φ' ih ih' =>
    intro ψ r s h
    cases ψ <;> simp only [code, List.cons_append, List.cons.injEq,
      List.append_assoc] at h <;> first | omega | skip
    obtain ⟨h1, h'⟩ := ih _ _ _ h.2
    obtain ⟨h2, h3⟩ := ih' _ _ _ h'
    exact ⟨by rw [h1, h2], h3⟩
  | ex φ ih =>
    intro ψ r s h
    cases ψ <;> simp only [code, List.cons_append, List.cons.injEq] at h <;>
      first | omega | skip
    obtain ⟨h1, h2⟩ := ih _ _ _ h.2
    exact ⟨by rw [h1], h2⟩
  | _ =>
    intro ψ r s h
    cases ψ <;> simp only [code, List.cons_append, List.cons.injEq, List.nil_append] at h <;>
      first | omega | skip
    all_goals simp_all [Fin.val_inj]

/-- Distance formulas form a prefix code. -/
instance prefixFree_distFO' (ℓ : ℕ) : PrefixFree (DistFO ℓ) :=
  ⟨fun φ ψ r s h => distFO_code_prefix φ ψ r s (by
    rwa [Lax185574Proofs.Legacy.encode_eq_code, Lax185574Proofs.Legacy.encode_eq_code] at h)⟩

/-- The roots of type trees form a prefix code, by induction on the
depth. -/
theorem prefixFree_node : ∀ (q ℓ : ℕ), PrefixFree (Node q ℓ)
  | 0, ℓ => inferInstanceAs (PrefixFree (Finset (DistFO ℓ)))
  | q + 1, ℓ =>
      haveI := prefixFree_node q (ℓ + 1)
      inferInstanceAs (PrefixFree (Finset (DistFO ℓ) × Finset (Fin ℓ × Node q (ℓ + 1))))

/-- The header `k, q, ℓ` is a prefix code of three numbers. Once it is read,
the root is a root of a known depth and arity, and roots of every depth
form a prefix code by induction on the depth, through products, finite
sets and the code of distance formulas.
-/
theorem prefixFree_typeTree : PrefixFree TypeTree where
  prefix_inj a b r s h := by
    obtain ⟨k, q, ℓ, x⟩ := a
    obtain ⟨k', q', ℓ', y⟩ := b
    change toWord (k, q, ℓ) ++ toWord x ++ r = toWord (k', q', ℓ') ++ toWord y ++ s at h
    rw [List.append_assoc, List.append_assoc] at h
    obtain ⟨h1, h'⟩ := prefix_inj' h
    simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl, rfl⟩ := h1
    have := prefixFree_node q ℓ
    obtain ⟨rfl, h2⟩ := prefix_inj' h'
    exact ⟨rfl, h2⟩

/-- The word of a partial graph is the word of its colors, its edges and its
non-edges, and these determine the partial graph.
-/
theorem prefixFree_partialGraph (n : ℕ) : PrefixFree (PartialGraph (Fin n)) where
  prefix_inj G H r s h := by
    obtain ⟨h1, h2⟩ := prefix_inj'
      (α := (Fin n → ℕ) × SimpleGraph (Fin n) × SimpleGraph (Fin n)) h
    refine ⟨?_, h2⟩
    obtain ⟨e, ne, d, c⟩ := G
    obtain ⟨e', ne', d', c'⟩ := H
    simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl, rfl⟩ := h1
    rfl

/-- By induction on the formula: the opcode determines the constructor, and
the arguments follow in fixed number.
-/
theorem prefixFree_distFO (ℓ : ℕ) : PrefixFree (DistFO ℓ) := prefixFree_distFO' ℓ

/-- By induction on the formula: the opcode determines the constructor, and
the arguments follow in fixed number.
-/
theorem prefixFree_fo (k : ℕ) : PrefixFree (Lax3.FirstOrder.FO k) :=
  ⟨fun φ ψ r s h => fo_code_prefix φ ψ r s (by
    rwa [Lax185574Proofs.Legacy.encode_eq_foCode, Lax185574Proofs.Legacy.encode_eq_foCode] at h)⟩

/-- The word of a script is the word of the family of its colors followed by
the list of its steps, and every step is three numbers.
-/
theorem prefixFree_script (n : ℕ) : PrefixFree (Script n) where
  prefix_inj a b r s h := by
    obtain ⟨h1, h2⟩ := prefix_inj' (α := (Fin n → ℕ) × List Step) (a := (a.colors, a.steps)) (b := (b.colors, b.steps)) h
    refine ⟨?_, h2⟩
    obtain ⟨c, l⟩ := a
    obtain ⟨c', l'⟩ := b
    simp only [Prod.mk.injEq] at h1
    obtain ⟨rfl, rfl⟩ := h1
    rfl

end Lax185574Proofs.EncodingInjectivity
