import Lax235315Proofs.Construction.ConcreteReconstruction
import Lax235315Proofs.Construction.WelzlProgram
import Mathlib.Tactic

/-! A pointer-level account of the linked-list insertions in the source
reconstruction loop.  The list representation constrains only pointers from a
vertex that has a successor in the represented list.  In particular, it does
not make any assertion about the final vertex's pointer cell: the program
writes exactly the output vertices and does not initialize that cell. -/

namespace Lax235315Proofs.Construction.LinkedReconstruction

open Lax235315Proofs.Construction.ConcreteReconstruction
open Lax235315Proofs.Construction.ListCrossing
open Lax235315Proofs.Construction.Reconstruction
open Lax235315Proofs.Construction.WelzlProgram

variable {α : Type*} [DecidableEq α]

/-- The pointer cells for all consecutive pairs in a list have their expected
values; the last cell is intentionally unconstrained. -/
def SuccessorLinks (next : α → α) : List α → Prop
  | [] => True
  | [_] => True
  | a :: b :: rest => next a = b ∧ SuccessorLinks next (b :: rest)

/-- A pointer array represents an ordered, duplicate-free list when its head
is the first list element and every internal successor link is correct. -/
def Represents (head : α) (next : α → α) (l : List α) : Prop :=
  l.Nodup ∧ l.head? = some head ∧ SuccessorLinks next l

/-- The two writes performed by the source inner loop for representative `r`
and fresh vertex `x`. -/
def writeAfter (next : α → α) (r x : α) : α → α :=
  Function.update (Function.update next x (next r)) r x

/-- Replay a list of source inner-loop writes, in the order in which the
removed vertices are scanned. -/
def writeRestored (representative : α → α) :
    (next : α → α) → List α → α → α
  | next, [] => next
  | next, x :: xs =>
      writeRestored representative (writeAfter next (representative x) x) xs

omit [DecidableEq α] in
lemma SuccessorLinks.congr {next next' : α → α} {l : List α}
    (hlinks : SuccessorLinks next l)
    (heq : ∀ a ∈ l, next' a = next a) : SuccessorLinks next' l := by
  induction l with
  | nil => trivial
  | cons a tail ih =>
      cases tail with
      | nil => trivial
      | cons b rest =>
          simp only [SuccessorLinks] at hlinks ⊢
          rcases hlinks with ⟨hab, htail⟩
          refine ⟨?_, ih htail ?_⟩
          · rw [heq a (by simp), hab]
          · intro y hy
            apply heq y
            simp [hy]

omit [DecidableEq α] in
lemma SuccessorLinks.cons_of_head {next : α → α} {a b : α} {l : List α}
    (hhead : l.head? = some b) (hfirstLink : next a = b)
    (hlinks : SuccessorLinks next l) :
    SuccessorLinks next (a :: l) := by
  cases l with
  | nil => simp at hhead
  | cons c tail =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      have hcb : c = b := hhead
      subst c
      change next a = b ∧ SuccessorLinks next (b :: tail)
      exact ⟨hfirstLink, hlinks⟩

lemma writeAfter_apply_x (next : α → α) (r x : α) (hrx : r ≠ x) :
    writeAfter next r x x = next r := by
  simp [writeAfter, hrx.symm]

lemma writeAfter_apply_r (next : α → α) (r x : α) :
    writeAfter next r x r = x := by
  simp [writeAfter]

lemma writeAfter_apply_of_ne (next : α → α) (r x y : α)
    (hyr : y ≠ r) (hyx : y ≠ x) :
    writeAfter next r x y = next y := by
  simp [writeAfter, hyr, hyx]

lemma writeAfter_links_insertAfter (next : α → α) (r x : α)
    (l : List α) (hr : r ∈ l) (hx : x ∉ l)
    (hnodup : l.Nodup) (hlinks : SuccessorLinks next l) :
    SuccessorLinks (writeAfter next r x) (insertAfter r x l) := by
  induction l with
  | nil => simp at hr
  | cons a tail ih =>
      cases tail with
      | nil =>
          have har : r = a := by simpa using hr
          subst r
          rw [insertAfter_cons, if_pos rfl]
          apply SuccessorLinks.cons_of_head (l := [x]) (b := x) rfl
          · exact writeAfter_apply_r next a x
          · trivial
      | cons b rest =>
          by_cases har : a = r
          · subst a
            rcases List.nodup_cons.mp hnodup with ⟨hrNotTail, htailNodup⟩
            rcases hlinks with ⟨hrb, hrest⟩
            have htailEq : ∀ y ∈ b :: rest,
                writeAfter next r x y = next y := by
              intro y hy
              have hyr : y ≠ r := by
                intro heq
                subst y
                exact hrNotTail hy
              have hyx : y ≠ x := by
                intro heq
                subst y
                exact hx (by simp [hy])
              exact writeAfter_apply_of_ne next r x y hyr hyx
            have hrest' := SuccessorLinks.congr hrest htailEq
            have htailLinks : SuccessorLinks (writeAfter next r x) (x :: b :: rest) :=
              SuccessorLinks.cons_of_head (l := b :: rest) (b := b) rfl
                (by rw [writeAfter_apply_x next r x (by
                    intro h
                    subst x
                    exact hx (by simp)), hrb]) hrest'
            rw [insertAfter_cons, if_pos rfl]
            exact SuccessorLinks.cons_of_head rfl
              (writeAfter_apply_r next r x) htailLinks
          · have hrTail : r ∈ b :: rest := by
              rcases List.mem_cons.mp hr with h | h
              · exact False.elim (har h.symm)
              · exact h
            have hxTail : x ∉ b :: rest := by
              intro hxb
              exact hx (by simp [hxb])
            have hax : a ≠ x := by
              intro h
              subst x
              exact hx (by simp)
            rcases List.nodup_cons.mp hnodup with ⟨_, htailNodup⟩
            rcases hlinks with ⟨hab, htail⟩
            have hinsert := ih hrTail hxTail htailNodup htail
            rw [insertAfter_cons, if_neg har]
            apply SuccessorLinks.cons_of_head
              (l := insertAfter r x (b :: rest)) (b := b)
              (insertAfter_head (a := r) (x := x))
            · rw [writeAfter_apply_of_ne next r x a har hax]
              exact hab
            · exact hinsert

lemma Represents.writeAfter_insertAfter
    {head r x : α} {next : α → α} {l : List α}
    (hrep : Represents head next l) (hr : r ∈ l) (hx : x ∉ l) :
    Represents head (writeAfter next r x) (insertAfter r x l) := by
  rcases hrep with ⟨hnodup, hhead, hlinks⟩
  refine ⟨nodup_insertAfter hnodup hr hx, ?_,
    writeAfter_links_insertAfter next r x l hr hx hnodup hlinks⟩
  cases l with
  | nil => simp at hhead
  | cons a tail =>
      simp only [insertAfter_head]
      simpa using hhead

/-- Under the restoration freshness and representative conditions, replaying
the literal pair of pointer writes for each removed vertex represents exactly
`ConcreteReconstruction.restoreAfter`. -/
lemma Represents.writeRestored_restoreAfter
    {representative : α → α} {head : α} {next : α → α}
    {current removed : List α}
    (hcurrent : Represents head next current)
    (hremoved : removed.Nodup)
    (hfresh : ∀ x ∈ removed, x ∉ current)
    (hreps : ∀ x ∈ removed, representative x ∈ current) :
    Represents head (writeRestored representative next removed)
      (restoreAfter representative current removed) := by
  induction removed generalizing next current with
  | nil => exact hcurrent
  | cons x xs ih =>
      rcases List.nodup_cons.mp hremoved with ⟨hxTail, htailNodup⟩
      have hxFresh : x ∉ current := hfresh x (by simp)
      have hxRep : representative x ∈ current := hreps x (by simp)
      have hnext : Represents head (writeAfter next (representative x) x)
          (insertAfter (representative x) x current) :=
        hcurrent.writeAfter_insertAfter hxRep hxFresh
      have htailFresh : ∀ y ∈ xs,
          y ∉ insertAfter (representative x) x current := by
        intro y hy hyInserted
        rcases (mem_insertAfter_iff hxRep).mp hyInserted with hyx | hyCurrent
        · exact hxTail (by simpa [hyx] using hy)
        · exact hfresh y (by simp [hy]) hyCurrent
      have htailReps : ∀ y ∈ xs,
          representative y ∈ insertAfter (representative x) x current := by
        intro y hy
        apply (mem_insertAfter_iff hxRep).mpr
        exact Or.inr (hreps y (by simp [hy]))
      exact ih hnext htailNodup htailFresh htailReps

lemma writeAfter_eq_of_ne (next : α → α) (r x y : α)
    (hyx : y ≠ x) (hyr : y ≠ r) :
    writeAfter next r x y = next y :=
  writeAfter_apply_of_ne next r x y hyr hyx

/-- Each source insertion changes only the two cells named by its writes. -/
lemma writeAfter_eq_outside (next : α → α) (r x y : α)
    (hyx : y ≠ x) (hyr : y ≠ r) :
    writeAfter next r x y = next y :=
  writeAfter_apply_of_ne next r x y hyr hyx

end Lax235315Proofs.Construction.LinkedReconstruction
