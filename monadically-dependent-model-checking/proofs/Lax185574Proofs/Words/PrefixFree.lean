import Lax185574Proofs.Legacy

/-!
The basic encodings of `Lax185574.Encodings` are prefix codes, and
the constructions of that module preserve this. Finite sets need it for
their elements, since the word of a finite set only records the words of
the elements.
-/

namespace Lax185574Proofs.Words

open Lax185574.WordEncoding

universe u v

/-- A prefix code is injective. -/
theorem toWord_injective {α : Type u} [WordEncoding α] [PrefixFree α] :
    Function.Injective (toWord : α → List ℕ) := fun a b h =>
  (PrefixFree.prefix_inj a b [] [] (by simp [h])).1

/-- A prefix code splits a word uniquely. -/
theorem prefix_inj' {α : Type u} [WordEncoding α] [PrefixFree α] {a b : α} {r s : List ℕ}
    (h : toWord a ++ r = toWord b ++ s) : a = b ∧ r = s :=
  PrefixFree.prefix_inj a b r s h

/-- An encoding into words of one fixed length is a prefix code if it is
injective. -/
theorem prefixFree_of_length {α : Type u} [WordEncoding α] (n : ℕ)
    (hlen : ∀ a : α, (toWord a).length = n) (hinj : Function.Injective (toWord : α → List ℕ)) :
    PrefixFree α where
  prefix_inj a b r s h := by
    have h1 := congrArg (List.take n) h
    have h2 := congrArg (List.drop n) h
    rw [List.take_append_of_le_length (by rw [hlen]),
      List.take_append_of_le_length (by rw [hlen])] at h1
    rw [List.drop_append_of_le_length (by rw [hlen]),
      List.drop_append_of_le_length (by rw [hlen])] at h2
    simp only [← hlen a, List.take_length, List.drop_length, List.nil_append] at h1 h2
    have hab : a = b := hinj (by rw [h1, List.take_of_length_le (by rw [hlen, hlen])])
    subst hab
    simpa [← hlen a] using h2

instance : PrefixFree ℕ :=
  prefixFree_of_length 1 (fun _ => rfl) (fun a b h => by
    simpa [word_simps] using h)

instance {n : ℕ} : PrefixFree (Fin n) :=
  prefixFree_of_length 1 (fun _ => rfl) (fun a b h => by
    simp only [word_simps, List.cons.injEq, and_true] at h
    exact Fin.ext h)

instance : PrefixFree Bool :=
  prefixFree_of_length 1 (fun b => by cases b <;> rfl) (fun a b h => by
    cases a <;> cases b <;> simp_all [word_simps])

instance {α : Type u} {β : Type v} [WordEncoding α] [WordEncoding β] [PrefixFree α]
    [PrefixFree β] : PrefixFree (α × β) where
  prefix_inj a b r s h := by
    change (toWord a.1 ++ toWord a.2) ++ r = (toWord b.1 ++ toWord b.2) ++ s at h
    rw [List.append_assoc, List.append_assoc] at h
    obtain ⟨h1, h⟩ := prefix_inj' h
    obtain ⟨h2, h⟩ := prefix_inj' h
    exact ⟨Prod.ext h1 h2, h⟩

instance {α : Type u} {β : Type v} [WordEncoding α] [WordEncoding β] [PrefixFree α]
    [PrefixFree β] : PrefixFree (α ⊕ β) where
  prefix_inj a b r s h := by
    cases a <;> cases b <;>
      simp only [word_simps, List.cons_append, List.cons.injEq] at h
    · obtain ⟨h1, h2⟩ := prefix_inj' h.2; exact ⟨by rw [h1], h2⟩
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · obtain ⟨h1, h2⟩ := prefix_inj' h.2; exact ⟨by rw [h1], h2⟩

instance {α : Type u} [WordEncoding α] [PrefixFree α] : PrefixFree (Option α) where
  prefix_inj a b r s h := by
    cases a <;> cases b <;>
      simp only [word_simps, List.cons_append, List.cons.injEq,
        List.nil_append] at h
    · exact ⟨rfl, h.2⟩
    · exact absurd h.1 (by omega)
    · exact absurd h.1 (by omega)
    · obtain ⟨h1, h2⟩ := prefix_inj' h.2; exact ⟨by rw [h1], h2⟩

/-- The word of a list. -/
theorem toWord_list {α : Type u} [WordEncoding α] (l : List α) :
    toWord l = l.length :: (l.map toWord).flatten := rfl

/-- The concatenated words of two lists of equal length split uniquely. -/
theorem flatten_prefix_inj {α : Type u} [WordEncoding α] [PrefixFree α] :
    ∀ (l l' : List α) (r s : List ℕ), l.length = l'.length →
      (l.map toWord).flatten ++ r = (l'.map toWord).flatten ++ s → l = l' ∧ r = s
  | [], [], _, _, _, h => ⟨rfl, by simpa using h⟩
  | a :: l, b :: l', r, s, hl, h => by
    simp only [List.map_cons, List.flatten_cons, List.append_assoc] at h
    obtain ⟨hab, hrest⟩ := prefix_inj' h
    obtain ⟨hl', hrs⟩ := flatten_prefix_inj l l' r s (by simpa using hl) hrest
    exact ⟨by rw [hab, hl'], hrs⟩
  | [], _ :: _, _, _, hl, _ => by simp at hl
  | _ :: _, [], _, _, hl, _ => by simp at hl

instance {α : Type u} [WordEncoding α] [PrefixFree α] : PrefixFree (List α) where
  prefix_inj a b r s h := by
    rw [toWord_list, toWord_list, List.cons_append, List.cons_append, List.cons.injEq] at h
    exact flatten_prefix_inj a b r s h.1 h.2

instance {α : Type u} {n : ℕ} [WordEncoding α] [PrefixFree α] : PrefixFree (Fin n → α) where
  prefix_inj a b r s h := by
    obtain ⟨h1, h2⟩ := prefix_inj' (α := List α) h
    exact ⟨List.ofFn_injective h1, h2⟩

instance : PrefixFree ℤ :=
  prefixFree_of_length 2 (fun a => by cases a <;> rfl) (fun a b h => by
    cases a <;> cases b <;> simp_all [word_simps])

instance : PrefixFree ℚ where
  prefix_inj a b r s h := by
    obtain ⟨h1, h2⟩ := prefix_inj' (α := ℤ × ℕ) (a := (a.num, a.den)) (b := (b.num, b.den)) h
    simp only [Prod.mk.injEq] at h1
    exact ⟨Rat.ext h1.1 h1.2, h2⟩

/-- The words of a finite set determine the set of words of its
elements. -/
theorem image_eq_of_words_eq {α : Type u} [WordEncoding α] {S T : Finset α}
    (h : Finset.words S = Finset.words T) : S.image toWord = T.image toWord := by
  ext x
  rw [← Finset.mem_sort (· ≤ ·), ← Finset.mem_sort (s := T.image toWord) (· ≤ ·)]
  exact Iff.of_eq (congrArg (x ∈ ·) h)

instance {α : Type u} [WordEncoding α] [PrefixFree α] : PrefixFree (Finset α) where
  prefix_inj a b r s h := by
    obtain ⟨h1, h2⟩ := prefix_inj' (α := List (List ℕ)) h
    exact ⟨Finset.image_injective toWord_injective (image_eq_of_words_eq h1), h2⟩

end Lax185574Proofs.Words
