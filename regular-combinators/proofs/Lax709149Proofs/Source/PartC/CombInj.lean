/-
The string representation of Section *Combinators* of *Transducers* (M. Bojańczyk) is injective,
and indeed prefix-free.

This is what makes the representation a representation, and it is needed for the atomic term of
group prefix multiplication: the machine of that term has to recover the element of the group from
the string that represents it.

The statement proved here is the stronger one, that the representation is a *code*: if
`repr x · u = repr y · v` then `x = y` and `u = v`.  It is the form that the induction needs, since
the representation of a pair or of a list contains the representations of its components followed
by the rest of the string.
-/
import Lax709149Proofs.Source.PartC.CombDepth
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax709149Proofs.Transducers
namespace Comb

/-- **The string representation is prefix-free.**  If the representation of `x` followed by `u` is
the representation of `y` followed by `v`, then `x = y` and `u = v`. -/
theorem repr_append_inj : ∀ (t : Ty) (x y : t.Elt) (u v : List Sym8),
    t.repr x ++ u = t.repr y ++ v → x = y ∧ u = v := by
  intro t
  induction t with
  | one =>
      intro x y u v h
      refine ⟨by cases x; cases y; rfl, ?_⟩
      rw [Ty.repr_one, Ty.repr_one] at h
      exact List.cons.inj h |>.2
  | prod A B ihA ihB =>
      intro x y u v h
      obtain ⟨a, b⟩ := x
      obtain ⟨a', b'⟩ := y
      rw [Ty.repr_prod, Ty.repr_prod] at h
      have h1 : A.repr a ++ (Sym8.comma :: (B.repr b ++ (Sym8.rpar :: u)))
          = A.repr a' ++ (Sym8.comma :: (B.repr b' ++ (Sym8.rpar :: v))) := by
        have h2 := (List.cons.inj h).2
        simpa [List.append_assoc] using h2
      obtain ⟨haa, h3⟩ := ihA a a' _ _ h1
      have h4 : B.repr b ++ (Sym8.rpar :: u) = B.repr b' ++ (Sym8.rpar :: v) :=
        (List.cons.inj h3).2
      obtain ⟨hbb, h5⟩ := ihB b b' _ _ h4
      exact ⟨by rw [haa, hbb], (List.cons.inj h5).2⟩
  | sum A B ihA ihB =>
      intro x y u v h
      cases x with
      | inl a =>
          cases y with
          | inl a' =>
              rw [Ty.repr_inl, Ty.repr_inl] at h
              obtain ⟨haa, huv⟩ := ihA a a' u v (by simpa using (List.cons.inj h).2)
              exact ⟨by rw [haa], huv⟩
          | inr b' =>
              rw [Ty.repr_inl, Ty.repr_inr] at h
              exact absurd (List.cons.inj h).1 (by simp)
      | inr b =>
          cases y with
          | inl a' =>
              rw [Ty.repr_inr, Ty.repr_inl] at h
              exact absurd (List.cons.inj h).1 (by simp)
          | inr b' =>
              rw [Ty.repr_inr, Ty.repr_inr] at h
              obtain ⟨hbb, huv⟩ := ihB b b' u v (by simpa using (List.cons.inj h).2)
              exact ⟨by rw [hbb], huv⟩
  | list A ihA =>
      have key : ∀ (l l' : List A.Elt) (u v : List Sym8),
          joinSep (l.map A.repr) ++ Sym8.rbrack :: u
            = joinSep (l'.map A.repr) ++ Sym8.rbrack :: v → l = l' ∧ u = v := by
        intro l
        induction l with
        | nil =>
            intro l' u v h
            cases l' with
            | nil => exact ⟨rfl, by simpa using h⟩
            | cons a' l'' =>
                exfalso
                obtain ⟨c, w, hcw, hc⟩ := repr_eq_cons A a'
                rw [joinSep_cons, hcw] at h
                have h3 : Sym8.rbrack :: u
                    = c :: ((w ++ joinSepTail A l'') ++ Sym8.rbrack :: v) := h
                rw [← (List.cons.inj h3).1] at hc
                exact absurd hc (by simp [transparent])
        | cons a l₁ ih =>
            intro l' u v h
            cases l' with
            | nil =>
                exfalso
                obtain ⟨c, w, hcw, hc⟩ := repr_eq_cons A a
                rw [joinSep_cons, hcw] at h
                have h3 : c :: ((w ++ joinSepTail A l₁) ++ Sym8.rbrack :: u)
                    = Sym8.rbrack :: v := h
                rw [(List.cons.inj h3).1] at hc
                exact absurd hc (by simp [transparent])
            | cons a' l₁' =>
                rw [joinSep_cons, joinSep_cons] at h
                have h1 : A.repr a ++ (joinSepTail A l₁ ++ Sym8.rbrack :: u)
                    = A.repr a' ++ (joinSepTail A l₁' ++ Sym8.rbrack :: v) := by
                  simpa [List.append_assoc] using h
                obtain ⟨haa, h2⟩ := ihA a a' _ _ h1
                cases l₁ with
                | nil =>
                    cases l₁' with
                    | nil =>
                        have h3 : Sym8.rbrack :: u = Sym8.rbrack :: v := h2
                        exact ⟨by rw [haa], (List.cons.inj h3).2⟩
                    | cons b' l₂' =>
                        exfalso
                        have h3 : Sym8.rbrack :: u
                            = Sym8.comma :: (joinSep ((b' :: l₂').map A.repr)
                              ++ Sym8.rbrack :: v) := h2
                        exact absurd (List.cons.inj h3).1 (by simp)
                | cons b l₂ =>
                    cases l₁' with
                    | nil =>
                        exfalso
                        have h3 : Sym8.comma :: (joinSep ((b :: l₂).map A.repr)
                              ++ Sym8.rbrack :: u) = Sym8.rbrack :: v := h2
                        exact absurd (List.cons.inj h3).1 (by simp)
                    | cons b' l₂' =>
                        have h3 : Sym8.comma :: (joinSep ((b :: l₂).map A.repr)
                              ++ Sym8.rbrack :: u)
                            = Sym8.comma :: (joinSep ((b' :: l₂').map A.repr)
                              ++ Sym8.rbrack :: v) := h2
                        obtain ⟨hl, huv⟩ := ih (b' :: l₂') u v (List.cons.inj h3).2
                        exact ⟨by rw [haa, hl], huv⟩
      intro l l' u v h
      rw [Ty.repr_list, Ty.repr_list] at h
      have h1 : joinSep (l.map A.repr) ++ Sym8.rbrack :: u
          = joinSep (l'.map A.repr) ++ Sym8.rbrack :: v := by
        simpa [List.append_assoc] using (List.cons.inj h).2
      exact key l l' u v h1

/-- **The string representation is injective.** -/
theorem repr_injective (t : Ty) {x y : t.Elt} (h : t.repr x = t.repr y) : x = y :=
  (repr_append_inj t x y [] [] (by rw [h])).1

end Comb
end Lax709149Proofs.Transducers
