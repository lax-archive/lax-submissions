/- Claim `claim:homomorphism-complement-rational`: the complement of the graph of a string
homomorphism is a rational relation.

The automaton has four states:

* `0` — the output produced so far is the image of the input read so far;
* `1` — a mismatch has already been found, so both the remaining input and the
  remaining output are arbitrary;
* `2` — the output is already too short and is finished (only input is read);
* `3` — the input is finished and the output is still growing.
-/
import Lax132576Proofs.Source.PartB.LabAut
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace HomCompl

variable {A B : Type} (φ : A → List B)

/-- The transitions of the automaton computing `{(w, v) | v ≠ homOf φ w}`. -/
def delta : Set (Fin 4 × List A × List B × Fin 4) :=
  {x | ∃ a : A, x = (0, [a], φ a, 0)} ∪
  {x | ∃ (a : A) (y : List B), y.length = (φ a).length ∧ y ≠ φ a ∧ x = (0, [a], y, 1)} ∪
  {x | ∃ (a : A) (y : List B), y.length < (φ a).length ∧ x = (0, [a], y, 2)} ∪
  {x | ∃ b : B, x = (0, [], [b], 3)} ∪
  {x | ∃ a : A, x = (1, [a], [], 1)} ∪
  {x | ∃ b : B, x = (1, [], [b], 1)} ∪
  {x | ∃ a : A, x = (2, [a], [], 2)} ∪
  {x | ∃ b : B, x = (3, [], [b], 3)}

lemma delta_finite [Finite A] [Finite B] : (delta φ).Finite := by
  apply Set.Finite.union
  apply Set.Finite.union
  apply Set.Finite.union
  apply Set.Finite.union
  apply Set.Finite.union
  apply Set.Finite.union
  apply Set.Finite.union
  · -- {x | ∃ a : A, x = (0, [a], φ a, 0)}
    exact Set.Finite.subset (Set.finite_range fun a : A => (0, [a], φ a, 0)) (by
      rintro x ⟨a, rfl⟩
      exact ⟨a, rfl⟩)
  · -- {x | ∃ (a : A) (y : List B), y.length = (φ a).length ∧ y ≠ φ a ∧ x = (0, [a], y, 1)}
    let T : A → Set (List B) := fun a => {y | y.length = (φ a).length ∧ y ≠ φ a}
    let f : A → List B → Fin 4 × List A × List B × Fin 4 := fun a y => ((0 : Fin 4), [a], y, (1 : Fin 4))
    have hsub : {x | ∃ a y, y.length = (φ a).length ∧ y ≠ φ a ∧ x = (0, [a], y, 1)} ⊆
        ⋃ a ∈ Set.univ, Set.image (f a) (T a) := by
      rintro x ⟨a, y, hlen, hne, rfl⟩
      exact Set.mem_biUnion (Set.mem_univ a) (Set.mem_image_of_mem _ ⟨hlen, hne⟩)
    apply Set.Finite.subset _ hsub
    refine Set.Finite.biUnion (Set.finite_univ (α := A)) ?_
    intro a _
    apply Set.Finite.image _
    haveI : Finite ((Fin (φ a).length) → B) := inferInstance
    have hfin : Finite {y : List B | y.length = (φ a).length} := by
      haveI : Fintype ((Fin (φ a).length) → B) := Fintype.ofFinite _
      let toFn : {y : List B | y.length = (φ a).length} → ((Fin (φ a).length) → B) :=
        fun ⟨y, hy⟩ i => y[i]'(by simpa using hy.symm ▸ i.2)
      let fromFn : ((Fin (φ a).length) → B) → {y : List B | y.length = (φ a).length} :=
        fun g => ⟨List.ofFn g, by simp⟩
      have hinv : ∀ g, toFn (fromFn g) = g := fun g => funext fun i => by
        simp only [fromFn, toFn]
        have hlen : (i : ℕ) < (List.ofFn g).length := by simp [Fin.is_lt]
        exact List.getElem_ofFn hlen
      have hinj : Function.Injective toFn := fun x y hxy => by
        obtain ⟨x1, hx1⟩ := x
        obtain ⟨y1, hy1⟩ := y
        simp only [toFn, Set.mem_setOf_eq] at hxy ⊢
        have hx1' := hx1
        have hy1' := hy1
        simp only [Set.mem_setOf_eq] at hx1' hy1'
        have hlen : x1.length = y1.length := hx1'.trans hy1'.symm
        refine Subtype.ext (List.ext_getElem hlen fun j hj₁ hj₂ => ?_)
        have : j < (φ a).length := hy1' ▸ hj₂
        simpa using congr_fun hxy ⟨j, this⟩
      exact Finite.of_injective _ hinj
    exact Set.Finite.subset hfin (by rintro y ⟨hlen, -⟩; exact hlen)
  · -- {x | ∃ (a : A) (y : List B), y.length < (φ a).length ∧ x = (0, [a], y, 2)}
    let T' : A → Set (List B) := fun a => {y | y.length < (φ a).length}
    let f2 : A → List B → Fin 4 × List A × List B × Fin 4 := fun a y => ((0 : Fin 4), [a], y, (2 : Fin 4))
    have hsub2 : {x | ∃ a y, y.length < (φ a).length ∧ x = (0, [a], y, 2)} ⊆
        ⋃ a ∈ Set.univ, Set.image (f2 a) (T' a) := by
      rintro x ⟨a, y, hlen, rfl⟩
      exact Set.mem_biUnion (Set.mem_univ a) (Set.mem_image_of_mem _ hlen)
    apply Set.Finite.subset _ hsub2
    apply Set.Finite.biUnion (Set.finite_univ (α := A))
    intro a _
    apply Set.Finite.image _
    -- T' a = {y | y.length < (φ a).length} is a finite union of finite sets
    have hT' : T' a ⊆ ⋃ n < (φ a).length, {y | y.length = n} := by
      rintro y hy
      simp only [Set.mem_iUnion, Set.mem_setOf_eq] at hy ⊢
      exact ⟨y.length, hy, rfl⟩
    apply Set.Finite.subset _ hT'
    apply Set.Finite.biUnion (by exact Set.finite_lt_nat (φ a).length)
    intro n _
    haveI : Finite ((Fin n) → B) := inferInstance
    have hfin : Finite {y : List B | y.length = n} := by
      haveI : Fintype ((Fin n) → B) := Fintype.ofFinite _
      let toFn : {y : List B | y.length = n} → ((Fin n) → B) :=
        fun ⟨y, hy⟩ i => y[i]'(by rw [Set.mem_setOf_eq] at hy; exact hy ▸ i.2)
      let fromFn : ((Fin n) → B) → {y : List B | y.length = n} :=
        fun g => ⟨List.ofFn g, by simp⟩
      have hinv : ∀ g, toFn (fromFn g) = g := fun g => funext fun i => by
        simp only [fromFn, toFn]
        have hlen : (i : ℕ) < (List.ofFn g).length := by simp [Fin.is_lt]
        exact List.getElem_ofFn hlen
      have hinj : Function.Injective toFn := fun x y hxy => by
        obtain ⟨x1, hx1⟩ := x
        obtain ⟨y1, hy1⟩ := y
        simp only [toFn, Set.mem_setOf_eq] at hxy ⊢
        have hx1' := hx1
        have hy1' := hy1
        simp only [Set.mem_setOf_eq] at hx1' hy1'
        have hlen : x1.length = y1.length := hx1'.trans hy1'.symm
        refine Subtype.ext (List.ext_getElem hlen fun j hj₁ hj₂ => ?_)
        have : j < n := hy1' ▸ hj₂
        simpa using congr_fun hxy ⟨j, this⟩
      exact Finite.of_injective _ hinj
    exact Set.toFinite _
  · -- {x | ∃ b : B, x = (0, [], [b], 3)}
    exact Set.Finite.subset (Set.finite_range fun b : B => (0, [], [b], 3)) (by
      rintro x ⟨b, rfl⟩
      exact ⟨b, rfl⟩)
  · -- {x | ∃ a : A, x = (1, [a], [], 1)}
    exact Set.Finite.subset (Set.finite_range fun a : A => (1, [a], [], 1)) (by
      rintro x ⟨a, rfl⟩
      exact ⟨a, rfl⟩)
  · -- {x | ∃ b : B, x = (1, [], [b], 1)}
    exact Set.Finite.subset (Set.finite_range fun b : B => (1, [], [b], 1)) (by
      rintro x ⟨b, rfl⟩
      exact ⟨b, rfl⟩)
  · -- {x | ∃ a : A, x = (2, [a], [], 2)}
    exact Set.Finite.subset (Set.finite_range fun a : A => (2, [a], [], 2)) (by
      rintro x ⟨a, rfl⟩
      exact ⟨a, rfl⟩)
  · -- {x | ∃ b : B, x = (3, [], [b], 3)}
    exact Set.Finite.subset (Set.finite_range fun b : B => (3, [], [b], 3)) (by
      rintro x ⟨b, rfl⟩
      exact ⟨b, rfl⟩)

/-- The automaton computing `{(w, v) | v ≠ homOf φ w}`. -/
def aut [Finite A] [Finite B] : NFAO A B (Fin 4) where
  init := {0}
  final := {1, 2, 3}
  δ := delta φ
  δ_finite := delta_finite φ

variable [Finite A] [Finite B]

/-! ### Runs that the automaton has -/

lemma relFrom_zero_hom (w : List A) : (aut φ).relFrom 0 w (homOf φ w) 0 := by
  induction w with
  | nil => exact NFAO.relFrom_nil _ _
  | cons a w' ih =>
    have h : (0, [a], φ a, 0) ∈ (aut φ).δ := by
      simp [aut, delta]
    apply NFAO.relFrom_step h ih

lemma relFrom_one (w : List A) (v : List B) : (aut φ).relFrom 1 w v 1 := by
  induction w generalizing v with
  | nil =>
    induction v with
    | nil => exact (aut φ).relFrom_nil 1
    | cons b v' ih =>
      have h : (1, [], [b], 1) ∈ (aut φ).δ := by
        simp [aut, delta]
      exact (aut φ).relFrom_step h ih
  | cons a w' ihw =>
    have h : (1, [a], [], 1) ∈ (aut φ).δ := by
      simp [aut, delta]
    exact (aut φ).relFrom_step h (ihw v)

lemma relFrom_two (w : List A) : (aut φ).relFrom 2 w [] 2 := by
  induction w with
  | nil => exact (aut φ).relFrom_nil 2
  | cons a w' ihw =>
    have h : (2, [a], [], 2) ∈ (aut φ).δ := by
      simp [aut, delta]
    exact (aut φ).relFrom_step h ihw

lemma relFrom_three (v : List B) : (aut φ).relFrom 3 [] v 3 := by
  induction v with
  | nil => exact (aut φ).relFrom_nil 3
  | cons b v' ih =>
    have h : (3, [], [b], 3) ∈ (aut φ).δ := by
      simp [aut, delta]
    exact (aut φ).relFrom_step h ih

/-- The three ways in which a pair with `v ≠ homOf φ w` is accepted, proved by
induction on the input string.

If `φ a` is a prefix of `v`, the first letter is processed by a transition of
the automaton that mimics `φ` and the induction hypothesis is applied.  If it is
not, then either the output is long enough to exhibit a mismatching block, and
the run continues in the state `1`, or the output is too short, and the run
continues in the state `2`.  The base case is an output which is nonempty while
the input is empty, and uses the state `3`. -/
lemma aut_complete_aux : ∀ (w : List A) (v : List B), v ≠ homOf φ w →
    (aut φ).relFrom 0 w v 1 ∨ (aut φ).relFrom 0 w v 2 ∨ (aut φ).relFrom 0 w v 3 := by
  intro w
  induction w with
  | nil =>
      intro v hv
      have hv' : v ≠ [] := by simpa [homOf] using hv
      rcases v with _ | ⟨b, v'⟩
      · exact absurd rfl hv'
      · have hmem : ((0 : Fin 4), ([] : List A), [b], (3 : Fin 4)) ∈ (aut φ).δ := by
          simp [aut, delta]
        exact Or.inr (Or.inr (by simpa using NFAO.relFrom_step hmem (relFrom_three φ v')))
  | cons a w' ih =>
      intro v hv
      by_cases hpre : φ a <+: v
      · -- the first block of the output agrees with `φ a`
        obtain ⟨v'', rfl⟩ := hpre
        have hne : v'' ≠ homOf φ w' := by
          intro h; exact hv (by simp [homOf, h])
        have hmem : ((0 : Fin 4), [a], φ a, (0 : Fin 4)) ∈ (aut φ).δ := by
          simp [aut, delta]
        rcases ih v'' hne with h | h | h
        · exact Or.inl (by simpa using NFAO.relFrom_step hmem h)
        · exact Or.inr (Or.inl (by simpa using NFAO.relFrom_step hmem h))
        · exact Or.inr (Or.inr (by simpa using NFAO.relFrom_step hmem h))
      · by_cases hlen : v.length < (φ a).length
        · -- the output is too short
          have hmem : ((0 : Fin 4), [a], v, (2 : Fin 4)) ∈ (aut φ).δ :=
            Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨a, v, hlen, rfl⟩)))))
          exact Or.inr (Or.inl (by simpa using NFAO.relFrom_step hmem (relFrom_two φ w')))
        · -- the first block of the output has the right length but is wrong
          push_neg at hlen
          have hylen : (v.take (φ a).length).length = (φ a).length := by simp [hlen]
          have hyne : v.take (φ a).length ≠ φ a := fun h =>
            hpre (h ▸ List.take_prefix (φ a).length v)
          have hmem : ((0 : Fin 4), [a], v.take (φ a).length, (1 : Fin 4)) ∈ (aut φ).δ :=
            Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
              (Or.inr ⟨a, v.take (φ a).length, hylen, hyne, rfl⟩))))))
          have hstep := NFAO.relFrom_step hmem (relFrom_one φ w' (v.drop (φ a).length))
          rw [List.take_append_drop] at hstep
          exact Or.inl (by simpa using hstep)

/-- Completeness: every pair with `v ≠ homOf φ w` is accepted. -/
lemma aut_complete (w : List A) (v : List B) (h : v ≠ homOf φ w) : (aut φ).rel w v := by
  rw [NFAO.rel_iff_relFrom]
  rcases aut_complete_aux φ w v h with h' | h' | h'
  · exact ⟨0, rfl, 1, by simp [aut], h'⟩
  · exact ⟨0, rfl, 2, by simp [aut], h'⟩
  · exact ⟨0, rfl, 3, by simp [aut], h'⟩

/-! ### Soundness -/

/-- The invariant used to analyse the runs of the automaton, for a run ending in
a final state. -/
def inv : Fin 4 → List A → List B → Prop
  | 0, w, v => v ≠ homOf φ w
  | 1, _, _ => True
  | 2, _, v => v = []
  | 3, w, _ => w = []

lemma aut_sound_aux {p : Fin 4} (hp : p ≠ 0) {s : Fin 4} {w : List A} {v : List B}
    (h : (aut φ).relFrom s w v p) : inv φ s w v := by
  have hbase : inv φ p [] [] := by
    fin_cases p
    · contradiction
    · trivial
    · simp [inv]
    · simp [inv]
  have hstep : ∀ (q q' : Fin 4) (u : List A) (x : List B) (w : List A) (v : List B),
      (q, u, x, q') ∈ (aut φ).δ → (aut φ).relFrom q' w v p → inv φ q' w v → inv φ q (u ++ w) (x ++ v) := by
    intro q q' u x w v ht _ hi
    simp only [] at ht
    induction ht with
    | inl h => induction h with
      | inl h => induction h with
        | inl h => induction h with
          | inl h => induction h with
            | inl h => induction h with
              | inl h => induction h with
                | inl h => obtain ⟨q_eq, u_eq, x_eq, q'_eq⟩ := h; simp [inv, homOf]; exact hi
                | inr h =>
                  obtain ⟨a, x, hlen, hne, rfl, rfl, rfl, rfl⟩ := h
                  simp [inv, homOf]
                  intro heq
                  have hx : x = (φ a ++ (List.map φ w).flatten).take (φ a).length := by
                    rw [← heq]
                    simp [hlen]
                  simp at hx
                  exact hne hx
              | inr h =>
                obtain ⟨a, x, hlen, rfl, rfl, rfl⟩ := h
                have hinv2 : inv φ 2 w v := hi
                simp only [inv] at hinv2
                simp [hinv2] at hlen ⊢
                intro heq
                simp [heq, homOf] at hlen
            | inr h => obtain ⟨_, _, rfl, ⟨b, rfl⟩, rfl⟩ := h; simp_all [inv, homOf]
          | inr h => simp_all [inv]  -- (1, [a], [], 1): inv φ 1 _ _ = True
        | inr h => simp_all [inv]  -- (1, [], [b], 1): inv φ 1 _ _ = True
      | inr h => simp_all [inv]  -- (2, [a], [], 2): w = [] from hi
    | inr h => simp_all [inv]  -- (3, [], [b], 3): w = [] from hi
  exact (aut φ).relFrom_induction hbase hstep h

/-- Soundness: every accepted pair satisfies `v ≠ homOf φ w`. -/
lemma aut_sound (w : List A) (v : List B) (h : (aut φ).rel w v) : v ≠ homOf φ w := by
  rw [NFAO.rel_iff_relFrom] at h
  obtain ⟨q, hq, p, hp, hrel⟩ := h
  have hq0 : q = 0 := hq
  subst hq0
  have hp0 : p ≠ 0 := by
    simp only [aut, Set.mem_insert_iff, Set.mem_singleton_iff] at hp
    rcases hp with rfl | rfl | rfl <;> decide
  exact aut_sound_aux φ hp0 hrel

end HomCompl

/-- **Claim `claim:homomorphism-complement-rational`.**  If `h : A* → B*` is a homomorphism, then
its complement `{(w, v) | v ≠ h w}` is a rational relation. -/
theorem hom_complement_rational_aux {A B : Type} [Finite A] [Finite B] (φ : A → List B) :
    IsRationalRel (fun (w : List A) (v : List B) => v ≠ homOf φ w) :=
  ⟨Fin 4, inferInstance, HomCompl.aut φ,
    fun w v => ⟨HomCompl.aut_complete φ w v, HomCompl.aut_sound φ w v⟩⟩

end Lax132576Proofs.Transducers
