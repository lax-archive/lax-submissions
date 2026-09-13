import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Tactic
import Lax17Proofs.Source.Theorem46

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy--Tan Section 4.3: intersecting path sets

This file formalizes the path-set pruning lemma used in Section 4.3.  The
main combinatorial content is independent of graph theory: it is a finite
bipartite pruning argument.  We prove that generic lemma first, and then
instantiate the bipartite relation by nonempty intersection of two graph paths.
-/

namespace SimpleGraph


namespace FiniteBipartitePruning

open Finset

variable {α β : Type*} [DecidableEq α] [DecidableEq β]
variable (rel : α → β → Prop) [∀ a b, Decidable (rel a b)]
variable {w D : ℕ}

/-- A finite pruning trace for the bipartite deletion process in Lemma 4.8.
At every step we delete a left vertex of current right-degree `< w`, if one
exists; otherwise we delete a right vertex of current left-degree `< D`, if one
exists. -/
inductive PruneTrace :
    Finset α → Finset β → Finset α → Finset β → Type _
  | done {A : Finset α} {B : Finset β}
      (hA : ∀ a ∈ A, w ≤ (B.bipartiteAbove rel a).card)
      (hB : ∀ b ∈ B, D ≤ (A.bipartiteBelow rel b).card) :
      PruneTrace A B A B
  | deleteLeft {A Afinal : Finset α} {B Bfinal : Finset β}
      (a : α) (ha : a ∈ A)
      (hbad : (B.bipartiteAbove rel a).card < w)
      (tail : PruneTrace (A.erase a) B Afinal Bfinal) :
      PruneTrace A B Afinal Bfinal
  | deleteRight {A Afinal : Finset α} {B Bfinal : Finset β}
      (hleft : ∀ a ∈ A, w ≤ (B.bipartiteAbove rel a).card)
      (b : β) (hb : b ∈ B)
      (hbad : (A.bipartiteBelow rel b).card < D)
      (tail : PruneTrace A (B.erase b) Afinal Bfinal) :
      PruneTrace A B Afinal Bfinal

namespace PruneTrace

variable {rel}

noncomputable def build (A : Finset α) (B : Finset β) :
    Σ Afinal : Finset α, Σ Bfinal : Finset β,
      PruneTrace (rel := rel) (w := w) (D := D) A B Afinal Bfinal := by
  classical
  by_cases hbadLeft :
      ∃ a ∈ A, (B.bipartiteAbove rel a).card < w
  · let a := Classical.choose hbadLeft
    have ha : a ∈ A := (Classical.choose_spec hbadLeft).1
    have hbad : (B.bipartiteAbove rel a).card < w :=
      (Classical.choose_spec hbadLeft).2
    let tail := build (A.erase a) B
    exact ⟨tail.1, tail.2.1,
      PruneTrace.deleteLeft (rel := rel) (w := w) (D := D)
        a ha hbad tail.2.2⟩
  · have hleft : ∀ a ∈ A, w ≤ (B.bipartiteAbove rel a).card := by
      intro a ha
      exact le_of_not_gt (by
        intro hlt
        exact hbadLeft ⟨a, ha, hlt⟩)
    by_cases hbadRight :
        ∃ b ∈ B, (A.bipartiteBelow rel b).card < D
    · let b := Classical.choose hbadRight
      have hb : b ∈ B := (Classical.choose_spec hbadRight).1
      have hbad : (A.bipartiteBelow rel b).card < D :=
        (Classical.choose_spec hbadRight).2
      let tail := build A (B.erase b)
      exact ⟨tail.1, tail.2.1,
        PruneTrace.deleteRight (rel := rel) (w := w) (D := D)
          hleft b hb hbad tail.2.2⟩
    · have hright : ∀ b ∈ B, D ≤ (A.bipartiteBelow rel b).card := by
        intro b hb
        exact le_of_not_gt (by
          intro hlt
          exact hbadRight ⟨b, hb, hlt⟩)
      exact ⟨A, B, PruneTrace.done (rel := rel) (A := A) (B := B) hleft hright⟩
termination_by A.card + B.card
decreasing_by
  · simp_wf
    exact Finset.card_erase_lt_of_mem ha
  · simp_wf
    exact Finset.card_erase_lt_of_mem hb

theorem final_left_subset
    {A Afinal : Finset α} {B Bfinal : Finset β}
    (h : PruneTrace (rel := rel) (w := w) (D := D) A B Afinal Bfinal) :
    Afinal ⊆ A := by
  induction h with
  | done => intro a ha; exact ha
  | deleteLeft x hx hbad tail ih =>
      exact ih.trans (Finset.erase_subset x _)
  | deleteRight hleft y hy hbad tail ih =>
      exact ih

theorem final_right_subset
    {A Afinal : Finset α} {B Bfinal : Finset β}
    (h : PruneTrace (rel := rel) (w := w) (D := D) A B Afinal Bfinal) :
    Bfinal ⊆ B := by
  induction h with
  | done => intro b hb; exact hb
  | deleteLeft x hx hbad tail ih =>
      exact ih
  | deleteRight hleft y hy hbad tail ih =>
      exact ih.trans (Finset.erase_subset y _)

theorem final_left_good
    {A Afinal : Finset α} {B Bfinal : Finset β}
    (h : PruneTrace (rel := rel) (w := w) (D := D) A B Afinal Bfinal) :
    ∀ a ∈ Afinal, w ≤ (Bfinal.bipartiteAbove rel a).card := by
  induction h with
  | done hA hB => exact hA
  | deleteLeft a ha hbad tail ih => exact ih
  | deleteRight hleft b hb hbad tail ih => exact ih

theorem final_right_good
    {A Afinal : Finset α} {B Bfinal : Finset β}
    (h : PruneTrace (rel := rel) (w := w) (D := D) A B Afinal Bfinal) :
    ∀ b ∈ Bfinal, D ≤ (Afinal.bipartiteBelow rel b).card := by
  induction h with
  | done hA hB => exact hB
  | deleteLeft a ha hbad tail ih => exact ih
  | deleteRight hleft b hb hbad tail ih => exact ih

omit [DecidableEq α] [DecidableEq β] in
theorem bipartiteAbove_card_mono
    {B₁ B₂ : Finset β} (hB : B₁ ⊆ B₂) (a : α) :
    (B₁.bipartiteAbove rel a).card ≤
      (B₂.bipartiteAbove rel a).card := by
  exact Finset.card_le_card (by
    intro b hb
    exact (Finset.mem_bipartiteAbove (r := rel)).2
      ⟨hB ((Finset.mem_bipartiteAbove (r := rel)).1 hb).1,
        ((Finset.mem_bipartiteAbove (r := rel)).1 hb).2⟩)

omit [DecidableEq α] [DecidableEq β] in
theorem bipartiteBelow_card_mono
    {A₁ A₂ : Finset α} (hA : A₁ ⊆ A₂) (b : β) :
    (A₁.bipartiteBelow rel b).card ≤
      (A₂.bipartiteBelow rel b).card := by
  exact Finset.card_le_card (by
    intro a ha
    exact (Finset.mem_bipartiteBelow (r := rel)).2
      ⟨hA ((Finset.mem_bipartiteBelow (r := rel)).1 ha).1,
        ((Finset.mem_bipartiteBelow (r := rel)).1 ha).2⟩)

theorem deleted_left_hits_final_le
    {A Afinal : Finset α} {B Bfinal : Finset β}
    (h : PruneTrace (rel := rel) (w := w) (D := D) A B Afinal Bfinal) :
    ∀ a ∈ A \ Afinal,
      (Bfinal.bipartiteAbove rel a).card ≤ w := by
  induction h with
  | done hA hB =>
      intro a ha
      simp at ha
  | deleteLeft x hx hbad tail ih =>
      intro a ha
      have haA := (Finset.mem_sdiff.1 ha).1
      have haAf := (Finset.mem_sdiff.1 ha).2
      by_cases hax : a = x
      · subst a
        exact (bipartiteAbove_card_mono (rel := rel)
          (final_right_subset (rel := rel) tail) x).trans hbad.le
      · have haTail := by
          exact Finset.mem_sdiff.2
            ⟨Finset.mem_erase.2 ⟨hax, haA⟩, haAf⟩
        exact ih a haTail
  | deleteRight hleft y hy hbad tail ih =>
      intro a ha
      exact ih a ha

/-- The right-deletion charges used in the counting proof.  The accumulator
`P` is the set of left vertices deleted before the current trace begins.  When
a right vertex is deleted, it is charged to all earlier deleted left vertices
that are adjacent to it. -/
def ChargedAux :
    {A Afinal : Finset α} → {B Bfinal : Finset β} →
      PruneTrace (rel := rel) (w := w) (D := D) A B Afinal Bfinal →
        Finset α → α → β → Prop
  | _, _, _, _, PruneTrace.done _ _, _P, _a, _b => False
  | _, _, _, _, PruneTrace.deleteLeft x _ _ tail, P, a, b =>
      ChargedAux tail (insert x P) a b
  | _, _, _, _, PruneTrace.deleteRight _ y _ _ tail, P, a, b =>
      (b = y ∧ a ∈ P ∧ rel a y) ∨ ChargedAux tail P a b

noncomputable instance chargedAuxDecidable
    {A Afinal : Finset α} {B Bfinal : Finset β}
    (h : PruneTrace (rel := rel) (w := w) (D := D) A B Afinal Bfinal)
    (P : Finset α) (a : α) (b : β) :
    Decidable (ChargedAux (rel := rel) h P a b) :=
  Classical.dec _

theorem charged_right_mem
    {A Afinal : Finset α} {B Bfinal : Finset β}
    (h : PruneTrace (rel := rel) (w := w) (D := D) A B Afinal Bfinal)
    (P : Finset α) {a : α} {b : β}
    (hc : ChargedAux (rel := rel) h P a b) :
    b ∈ B \ Bfinal := by
  induction h generalizing P with
  | done hA hB =>
      cases hc
  | deleteLeft x _ _ tail ih =>
      exact ih (insert x P) hc
  | deleteRight _ y hy _ tail ih =>
      rcases hc with hnew | htail
      · rcases hnew with ⟨hby, _haP, _hrel⟩
        refine Finset.mem_sdiff.2 ⟨hby ▸ hy, ?_⟩
        intro hbFinal
        have hyFinal := by simpa [hby] using hbFinal
        have hyErase := final_right_subset (rel := rel) tail hyFinal
        exact (Finset.mem_erase.1 hyErase).1 rfl
      · have hbTail := ih P htail
        exact Finset.mem_sdiff.2
          ⟨(Finset.mem_erase.1 (Finset.mem_sdiff.1 hbTail).1).2,
            (Finset.mem_sdiff.1 hbTail).2⟩

theorem charged_left_mem
    {A Afinal : Finset α} {B Bfinal : Finset β}
    (h : PruneTrace (rel := rel) (w := w) (D := D) A B Afinal Bfinal)
    (P : Finset α) {a : α} {b : β}
    (hc : ChargedAux (rel := rel) h P a b) :
    a ∈ P ∪ (A \ Afinal) := by
  induction h generalizing P with
  | done hA hB =>
      cases hc
  | deleteLeft x hx hbad tail ih =>
      have hmem := ih (insert x P) hc
      rcases Finset.mem_union.1 hmem with hprev | hdel
      · rcases Finset.mem_insert.1 hprev with hax | haP
        · refine Finset.mem_union.2 (Or.inr (Finset.mem_sdiff.2 ⟨hax ▸ hx, ?_⟩))
          intro haFinal
          have hxFinal := by simpa [hax] using haFinal
          have hxErase := final_left_subset (rel := rel) tail hxFinal
          exact (Finset.mem_erase.1 hxErase).1 rfl
        · exact Finset.mem_union.2 (Or.inl haP)
      · have haErase := (Finset.mem_sdiff.1 hdel).1
        exact Finset.mem_union.2
          (Or.inr (Finset.mem_sdiff.2
            ⟨(Finset.mem_erase.1 haErase).2,
              (Finset.mem_sdiff.1 hdel).2⟩))
  | deleteRight hleft y hy hbad tail ih =>
      rcases hc with hnew | htail
      · exact Finset.mem_union.2 (Or.inl hnew.2.1)
      · exact ih P htail

theorem charged_rel
    {A Afinal : Finset α} {B Bfinal : Finset β}
    (h : PruneTrace (rel := rel) (w := w) (D := D) A B Afinal Bfinal)
    (P : Finset α) {a : α} {b : β}
    (hc : ChargedAux (rel := rel) h P a b) :
    rel a b := by
  induction h generalizing P with
  | done hA hB =>
      cases hc
  | deleteLeft x hx hbad tail ih =>
      exact ih (insert x P) hc
  | deleteRight hleft y hy hbad tail ih =>
      rcases hc with hnew | htail
      · rcases hnew with ⟨rfl, _haP, hrel⟩
        exact hrel
      · exact ih P htail

theorem charged_fiber_subset_current_neighbors
    {A Afinal : Finset α} {B Bfinal : Finset β}
    (h : PruneTrace (rel := rel) (w := w) (D := D) A B Afinal Bfinal)
    (P : Finset α) {a : α} (_haP : a ∈ P) :
    ((B \ Bfinal).bipartiteAbove (ChargedAux (rel := rel) h P) a) ⊆
      B.bipartiteAbove rel a := by
  intro b hb
  exact (Finset.mem_bipartiteAbove (r := rel)).2
    ⟨(Finset.mem_sdiff.1
        ((Finset.mem_bipartiteAbove
          (r := ChargedAux (rel := rel) h P)).1 hb).1).1,
      charged_rel (rel := rel) h P
        ((Finset.mem_bipartiteAbove
          (r := ChargedAux (rel := rel) h P)).1 hb).2⟩

theorem charged_upper
    {A Afinal : Finset α} {B Bfinal : Finset β}
    (h : PruneTrace (rel := rel) (w := w) (D := D) A B Afinal Bfinal)
    (P : Finset α)
    (hPbad : ∀ a ∈ P, (B.bipartiteAbove rel a).card < w) :
    ∀ a ∈ P ∪ (A \ Afinal),
      ((B \ Bfinal).bipartiteAbove (ChargedAux (rel := rel) h P) a).card ≤ w := by
  induction h generalizing P with
  | done hA hB =>
      intro a ha
      simp [ChargedAux, Finset.bipartiteAbove]
  | deleteLeft x hx hbad tail ih =>
      intro a ha
      simpa [ChargedAux] using
        ih (insert x P)
          (by
            intro a ha
            rcases Finset.mem_insert.1 ha with rfl | haP
            · exact hbad
            · exact hPbad a haP)
          a (by
            rcases Finset.mem_union.1 ha with haP | hdel
            · exact Finset.mem_union.2 (Or.inl (Finset.mem_insert.2 (Or.inr haP)))
            · rcases Finset.mem_sdiff.1 hdel with ⟨haA, haAf⟩
              by_cases hax : a = x
              · subst a
                exact Finset.mem_union.2 (Or.inl (Finset.mem_insert_self x P))
              · exact Finset.mem_union.2
                  (Or.inr (Finset.mem_sdiff.2
                    ⟨Finset.mem_erase.2 ⟨hax, haA⟩, haAf⟩)))
  | deleteRight hleft y hy hbad tail ih =>
      rename_i Acur Afinalcur Bcur Bfinalcur
      intro a ha
      by_cases haP : a ∈ P
      · exact (Finset.card_le_card
          (charged_fiber_subset_current_neighbors (rel := rel)
            (PruneTrace.deleteRight (rel := rel) hleft y hy hbad tail)
            P haP)).trans (hPbad a haP).le
      · have hdel : a ∈ Acur \ Afinalcur := by
          rcases Finset.mem_union.1 ha with haP' | hdel
          · exact False.elim (haP haP')
          · exact hdel
        have htail := ih P
          (by
            intro a haP
            exact lt_of_le_of_lt
              (bipartiteAbove_card_mono (rel := rel)
                (Finset.erase_subset y _) a)
              (hPbad a haP))
          a (Finset.mem_union.2 (Or.inr hdel))
        exact (Finset.card_le_card (by
          intro b hb
          rcases (Finset.mem_bipartiteAbove
              (r := ChargedAux (rel := rel)
                (PruneTrace.deleteRight (rel := rel) hleft y hy hbad tail) P)).1 hb
            with ⟨hbDel, hchg⟩
          rcases hchg with hnew | htailchg
          · exact False.elim (haP hnew.2.1)
          · have hbne : b ≠ y := by
              intro hby
              subst b
              have hyErase : y ∈ Bcur.erase y := by
                have hbTail := charged_right_mem (rel := rel) tail P htailchg
                exact (Finset.mem_sdiff.1 hbTail).1
              exact (Finset.mem_erase.1 hyErase).1 rfl
            exact (Finset.mem_bipartiteAbove
                (r := ChargedAux (rel := rel) tail P)).2
              ⟨Finset.mem_sdiff.2
                ⟨Finset.mem_erase.2 ⟨hbne, (Finset.mem_sdiff.1 hbDel).1⟩,
                  (Finset.mem_sdiff.1 hbDel).2⟩,
                htailchg⟩)).trans htail

theorem charged_lower
    {A Afinal : Finset α} {B Bfinal : Finset β}
    (h : PruneTrace (rel := rel) (w := w) (D := D) A B Afinal Bfinal)
    (P : Finset α)
    (hdisj : Disjoint P A)
    (hdense :
      ∀ b ∈ B, 2 * D ≤ ((P ∪ A).bipartiteBelow rel b).card) :
    ∀ b ∈ B \ Bfinal,
      D ≤ ((P ∪ (A \ Afinal)).bipartiteBelow
        (ChargedAux (rel := rel) h P) b).card := by
  induction h generalizing P with
  | done hA hB =>
      intro b hb
      simp at hb
  | deleteLeft x hx hbad tail ih =>
      rename_i Acur Afinalcur Bcur Bfinalcur
      have hdisj' : Disjoint (insert x P) (Acur.erase x) := by
        rw [Finset.disjoint_left]
        intro a haP haA
        rcases Finset.mem_insert.1 haP with rfl | haPold
        · exact (Finset.mem_erase.1 haA).1 rfl
        · exact Finset.disjoint_left.mp hdisj haPold
            (Finset.mem_erase.1 haA).2
      have hUnion :
          insert x P ∪ Acur.erase x = P ∪ Acur := by
        ext a
        constructor
        · intro ha
          rcases Finset.mem_union.1 ha with hprev | herase
          · rcases Finset.mem_insert.1 hprev with rfl | haP
            · exact Finset.mem_union.2 (Or.inr hx)
            · exact Finset.mem_union.2 (Or.inl haP)
          · exact Finset.mem_union.2
              (Or.inr (Finset.mem_erase.1 herase).2)
        · intro ha
          rcases Finset.mem_union.1 ha with haP | haA
          · exact Finset.mem_union.2
              (Or.inl (Finset.mem_insert.2 (Or.inr haP)))
          · by_cases hax : a = x
            · subst a
              exact Finset.mem_union.2
                (Or.inl (Finset.mem_insert_self x P))
            · exact Finset.mem_union.2
                (Or.inr (Finset.mem_erase.2 ⟨hax, haA⟩))
      have hdense' :
          ∀ b ∈ Bcur,
            2 * D ≤ (((insert x P) ∪ Acur.erase x).bipartiteBelow rel b).card := by
        intro b hb
        simpa [hUnion] using hdense b hb
      intro b hb
      have htail := ih (insert x P) hdisj' hdense' b hb
      have hLeftEq :
          insert x P ∪ (Acur.erase x \ Afinalcur) =
            P ∪ (Acur \ Afinalcur) := by
        ext a
        constructor
        · intro ha
          rcases Finset.mem_union.1 ha with hprev | hdel
          · rcases Finset.mem_insert.1 hprev with hax | haP
            · have hxNotFinal : x ∉ Afinalcur := by
                intro hxFinal
                have hxErase : x ∈ Acur.erase x :=
                  final_left_subset (rel := rel) tail hxFinal
                exact (Finset.mem_erase.1 hxErase).1 rfl
              have hxRight : x ∈ P ∪ (Acur \ Afinalcur) :=
                Finset.mem_union.2
                  (Or.inr (Finset.mem_sdiff.2 ⟨hx, hxNotFinal⟩))
              simpa [hax] using hxRight
            · exact Finset.mem_union.2 (Or.inl haP)
          · exact Finset.mem_union.2
              (Or.inr (Finset.mem_sdiff.2
                ⟨(Finset.mem_erase.1 (Finset.mem_sdiff.1 hdel).1).2,
                  (Finset.mem_sdiff.1 hdel).2⟩))
        · intro ha
          rcases Finset.mem_union.1 ha with haP | hdel
          · exact Finset.mem_union.2
              (Or.inl (Finset.mem_insert.2 (Or.inr haP)))
          · rcases Finset.mem_sdiff.1 hdel with ⟨haA, haAf⟩
            by_cases hax : a = x
            · subst a
              exact Finset.mem_union.2
                (Or.inl (Finset.mem_insert_self x P))
            · exact Finset.mem_union.2
                (Or.inr (Finset.mem_sdiff.2
                  ⟨Finset.mem_erase.2 ⟨hax, haA⟩, haAf⟩))
      simpa [ChargedAux, hLeftEq] using htail
  | deleteRight hleft y hy hbad tail ih =>
      rename_i Acur Afinalcur Bcur Bfinalcur
      have hdenseTail :
          ∀ b ∈ Bcur.erase y,
            2 * D ≤ ((P ∪ Acur).bipartiteBelow rel b).card := by
        intro b hb
        exact hdense b (Finset.mem_erase.1 hb).2
      intro b hb
      by_cases hby : b = y
      · subst b
        have hPA :
            ((P ∪ Acur).bipartiteBelow rel y).card =
              (P.bipartiteBelow rel y).card +
                (Acur.bipartiteBelow rel y).card := by
          have hdisjBelow :
              Disjoint (P.bipartiteBelow rel y) (Acur.bipartiteBelow rel y) := by
            rw [Finset.disjoint_left]
            intro a haP haA
            exact Finset.disjoint_left.mp hdisj
              ((Finset.mem_bipartiteBelow (r := rel)).1 haP).1
              ((Finset.mem_bipartiteBelow (r := rel)).1 haA).1
          have hUnionBelow :
              (P ∪ Acur).bipartiteBelow rel y =
                (P.bipartiteBelow rel y) ∪ (Acur.bipartiteBelow rel y) := by
            ext a
            simp only [Finset.mem_bipartiteBelow, Finset.mem_union]
            tauto
          rw [hUnionBelow, Finset.card_union_of_disjoint hdisjBelow]
        have hPdeg : D ≤ (P.bipartiteBelow rel y).card := by
          have hd := hdense y hy
          rw [hPA] at hd
          omega
        have hsubset :
            P.bipartiteBelow rel y ⊆
              ((P ∪ (Acur \ Afinalcur)).bipartiteBelow
                (ChargedAux (rel := rel)
                  (PruneTrace.deleteRight (rel := rel) hleft y hy hbad tail)
                  P) y) := by
          intro a ha
          rcases (Finset.mem_bipartiteBelow (r := rel)).1 ha with ⟨haP, hrel⟩
          exact (Finset.mem_bipartiteBelow
              (r := ChargedAux (rel := rel)
                (PruneTrace.deleteRight (rel := rel) hleft y hy hbad tail) P)).2
            ⟨Finset.mem_union.2 (Or.inl haP),
              Or.inl ⟨rfl, haP, hrel⟩⟩
        exact hPdeg.trans (Finset.card_le_card hsubset)
      · have hbTail : b ∈ Bcur.erase y \ Bfinalcur := by
          exact Finset.mem_sdiff.2
            ⟨Finset.mem_erase.2
              ⟨hby, (Finset.mem_sdiff.1 hb).1⟩,
              (Finset.mem_sdiff.1 hb).2⟩
        have htail := ih P hdisj hdenseTail b hbTail
        have hsubset :
            ((P ∪ (Acur \ Afinalcur)).bipartiteBelow
              (ChargedAux (rel := rel) tail P) b)
              ⊆
            ((P ∪ (Acur \ Afinalcur)).bipartiteBelow
              (ChargedAux (rel := rel)
                (PruneTrace.deleteRight (rel := rel) hleft y hy hbad tail)
                P) b) := by
          intro a ha
          rcases (Finset.mem_bipartiteBelow
              (r := ChargedAux (rel := rel) tail P)).1 ha with ⟨haLeft, hchg⟩
          exact (Finset.mem_bipartiteBelow
              (r := ChargedAux (rel := rel)
                (PruneTrace.deleteRight (rel := rel) hleft y hy hbad tail) P)).2
            ⟨haLeft, Or.inr hchg⟩
        exact htail.trans (Finset.card_le_card hsubset)

theorem deleted_right_mul_le_deleted_left_mul
    {A Afinal : Finset α} {B Bfinal : Finset β}
    (h : PruneTrace (rel := rel) (w := w) (D := D) A B Afinal Bfinal)
    (P : Finset α)
    (hdisj : Disjoint P A)
    (hPbad : ∀ a ∈ P, (B.bipartiteAbove rel a).card < w)
    (hdense :
      ∀ b ∈ B, 2 * D ≤ ((P ∪ A).bipartiteBelow rel b).card) :
    (B \ Bfinal).card * D ≤ (P ∪ (A \ Afinal)).card * w := by
  classical
  exact Finset.card_mul_le_card_mul'
    (r := ChargedAux (rel := rel) h P)
    (s := P ∪ (A \ Afinal)) (t := B \ Bfinal)
    (charged_lower (rel := rel) h P hdisj hdense)
    (charged_upper (rel := rel) h P hPbad)

/-- Generic finite bipartite version of Lemma 4.8.  The hypothesis
`2 * A.card * w ≤ D * B.card` is the integer cross-multiplied form of
`|B| ≥ 2|A|w/D`. -/
theorem exists_intersecting_subsets
    (A : Finset α) (B : Finset β)
    (hD : 0 < D)
    (hdense : ∀ b ∈ B, 2 * D ≤ (A.bipartiteBelow rel b).card)
    (hcard : 2 * A.card * w ≤ D * B.card) :
    ∃ Afinal : Finset α, ∃ Bfinal : Finset β,
      Afinal ⊆ A ∧
        Bfinal ⊆ B ∧
          (∀ a ∈ Afinal, w ≤ (Bfinal.bipartiteAbove rel a).card) ∧
            (∀ b ∈ Bfinal, D ≤ (Afinal.bipartiteBelow rel b).card) ∧
              B.card ≤ 2 * Bfinal.card ∧
                ∀ a ∈ A \ Afinal,
                  (Bfinal.bipartiteAbove rel a).card ≤ w := by
  classical
  let tr := build (rel := rel) (w := w) (D := D) A B
  rcases tr with ⟨Afinal, Bfinal, htrace⟩
  have hAsub := final_left_subset (rel := rel) htrace
  have hBsub := final_right_subset (rel := rel) htrace
  have hgoodA := final_left_good (rel := rel) htrace
  have hgoodB := final_right_good (rel := rel) htrace
  have hdeletedA := deleted_left_hits_final_le (rel := rel) htrace
  have hdenseRoot :
      ∀ b ∈ B, 2 * D ≤ (((∅ : Finset α) ∪ A).bipartiteBelow rel b).card := by
    simpa using hdense
  have hcharge :
      (B \ Bfinal).card * D ≤
        (((∅ : Finset α) ∪ (A \ Afinal)).card) * w :=
    deleted_right_mul_le_deleted_left_mul
      (rel := rel) htrace (∅ : Finset α)
      (by simp) (by simp) hdenseRoot
  have hcharge' : (B \ Bfinal).card * D ≤ (A \ Afinal).card * w := by
    simpa using hcharge
  have hAdelete_le : (A \ Afinal).card ≤ A.card :=
    Finset.card_le_card (Finset.sdiff_subset)
  have htwice_delete_mul :
      2 * ((B \ Bfinal).card * D) ≤ D * B.card := by
    calc
      2 * ((B \ Bfinal).card * D)
          ≤ 2 * ((A \ Afinal).card * w) := Nat.mul_le_mul_left 2 hcharge'
      _ ≤ 2 * (A.card * w) := by
        exact Nat.mul_le_mul_left 2 (Nat.mul_le_mul_right w hAdelete_le)
      _ ≤ D * B.card := by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcard
  have hdel_twice : 2 * (B \ Bfinal).card ≤ B.card := by
    have hrewrite :
        D * (2 * (B \ Bfinal).card) ≤ D * B.card := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        htwice_delete_mul
    exact Nat.le_of_mul_le_mul_left hrewrite hD
  have hsplit : B.card = Bfinal.card + (B \ Bfinal).card := by
    have := Finset.card_sdiff_add_card_eq_card hBsub
    omega
  have hhalf : B.card ≤ 2 * Bfinal.card := by
    rw [hsplit]
    omega
  exact ⟨Afinal, Bfinal, hAsub, hBsub, hgoodA, hgoodB, hhalf, hdeletedA⟩

end PruneTrace

end FiniteBipartitePruning

namespace PathPacking

variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}
variable {S T S' T' : Finset V}

/-- Two graph paths intersect when their vertex sets are not disjoint. -/
def PathsIntersect (P Q : GraphPath G) : Prop :=
  ¬ Disjoint P.vertexSet Q.vertexSet

/-- The indices of `Q`-paths in `Qset` that intersect the `R`-path `r`. -/
noncomputable def intersectingRightIndices
    (R : PathPacking G S T) (Q : PathPacking G S' T')
    (Qset : Finset Q.Index) (r : R.Index) : Finset Q.Index := by
  classical
  exact Qset.filter fun q => PathsIntersect (R.path r) (Q.path q)

theorem mem_intersectingRightIndices
    (R : PathPacking G S T) (Q : PathPacking G S' T')
    (Qset : Finset Q.Index) (r : R.Index) (q : Q.Index) :
    q ∈ R.intersectingRightIndices Q Qset r ↔
      q ∈ Qset ∧ PathsIntersect (R.path r) (Q.path q) := by
  classical
  simp [intersectingRightIndices]

/-- The indices of `R`-paths in `Rset` that intersect the `Q`-path `q`. -/
noncomputable def intersectingLeftIndices
    (R : PathPacking G S T) (Q : PathPacking G S' T')
    (Rset : Finset R.Index) (q : Q.Index) : Finset R.Index := by
  classical
  exact Rset.filter fun r => PathsIntersect (R.path r) (Q.path q)

theorem mem_intersectingLeftIndices
    (R : PathPacking G S T) (Q : PathPacking G S' T')
    (Rset : Finset R.Index) (q : Q.Index) (r : R.Index) :
    r ∈ R.intersectingLeftIndices Q Rset q ↔
      r ∈ Rset ∧ PathsIntersect (R.path r) (Q.path q) := by
  classical
  simp [intersectingLeftIndices]

/-- A pair of selected path subfamilies is `(w,D)`-intersecting if every
selected left path meets at least `w` selected right paths and every selected
right path meets at least `D` selected left paths. -/
def IntersectingPathSetPair
    (R : PathPacking G S T) (Q : PathPacking G S' T')
    (Rset : Finset R.Index) (Qset : Finset Q.Index)
    (w D : ℕ) : Prop :=
  (∀ r ∈ Rset, w ≤ (R.intersectingRightIndices Q Qset r).card) ∧
    ∀ q ∈ Qset, D ≤ (R.intersectingLeftIndices Q Rset q).card

theorem intersectingPathSetPair_iff
    (R : PathPacking G S T) (Q : PathPacking G S' T')
    (Rset : Finset R.Index) (Qset : Finset Q.Index)
    (w D : ℕ) :
    IntersectingPathSetPair R Q Rset Qset w D ↔
      (∀ r ∈ Rset, w ≤ (R.intersectingRightIndices Q Qset r).card) ∧
        ∀ q ∈ Qset, D ≤ (R.intersectingLeftIndices Q Rset q).card :=
  Iff.rfl

/-- Chuzhoy--Tan Lemma 4.8, in finite path-packing form.

The cardinality hypothesis is stated as
`2 * Rset.card * w ≤ D * Qset.card`, the cross-multiplied integer form of the
paper's `|Q| ≥ 2|R|w/D`. -/
theorem exists_intersecting_path_subfamilies
    (R : PathPacking G S T) (Q : PathPacking G S' T')
    (Rset : Finset R.Index) (Qset : Finset Q.Index)
    {w D : ℕ}
    (hD : 0 < D)
    (hdense :
      ∀ q ∈ Qset, 2 * D ≤ (R.intersectingLeftIndices Q Rset q).card)
    (hcard : 2 * Rset.card * w ≤ D * Qset.card) :
    ∃ R' : Finset R.Index, ∃ Q' : Finset Q.Index,
      R' ⊆ Rset ∧
        Q' ⊆ Qset ∧
          IntersectingPathSetPair R Q R' Q' w D ∧
            Qset.card ≤ 2 * Q'.card ∧
              ∀ r ∈ Rset \ R',
                (R.intersectingRightIndices Q Q' r).card ≤ w := by
  classical
  let rel : R.Index → Q.Index → Prop :=
    fun r q => PathsIntersect (R.path r) (Q.path q)
  have hdense' :
      ∀ q ∈ Qset,
        2 * D ≤ (Rset.bipartiteBelow rel q).card := by
    intro q hq
    simpa [intersectingLeftIndices, rel] using hdense q hq
  rcases
    FiniteBipartitePruning.PruneTrace.exists_intersecting_subsets
      (rel := rel) (w := w) (D := D) Rset Qset hD hdense' hcard
      with ⟨R', Q', hRsub, hQsub, hleft, hright, hhalf, hdeleted⟩
  refine ⟨R', Q', hRsub, hQsub, ?_, hhalf, ?_⟩
  · constructor
    · intro r hr
      simpa [intersectingRightIndices, rel] using hleft r hr
    · intro q hq
      simpa [intersectingLeftIndices, rel] using hright q hq
  · intro r hr
    simpa [intersectingRightIndices, rel] using hdeleted r hr

end PathPacking

namespace PathSlicing

variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V}
variable {A B S T : Finset V} {M : ℕ}
variable {R : PerfectPathPacking G A B}

/-- The half-open row segment between the two cut vertices bounding slice
`i`.  The right cut is removed.  This is the paper's path family `Σ_i` with
the boundary convention that makes different slices vertex-disjoint and
leaves the boundary edge available to the later connector. -/
noncomputable def sliceRowPath
    (sigma : PathSlicing R M) (i : Fin M) (r : R.Index) :
    GraphPath G :=
  ((R.path r).segmentOfBefore
    (sigma.cut_monotone r (Fin.castSucc_le_succ i))).dropLast

@[simp] theorem sliceRowPath_source
    (sigma : PathSlicing R M) (i : Fin M) (r : R.Index) :
    (sigma.sliceRowPath i r).source = sigma.cut r i.castSucc := by
  simp [sliceRowPath]

theorem sliceRowPath_vertexSet_subset
    (sigma : PathSlicing R M) (i : Fin M) (r : R.Index) :
    (sigma.sliceRowPath i r).vertexSet ⊆ (R.path r).vertexSet :=
  fun _ hv =>
    (R.path r).segmentOfBefore_vertexSet_subset
      (sigma.cut_monotone r (Fin.castSucc_le_succ i))
      (((R.path r).segmentOfBefore
        (sigma.cut_monotone r (Fin.castSucc_le_succ i)))
        |>.dropLast_vertexSet_subset hv)

/-- The actual path packing of all closed row segments in slice `i`. -/
noncomputable def sliceRowPacking
    [Fintype V]
    (sigma : PathSlicing R M) (i : Fin M) :
    PathPacking G Finset.univ Finset.univ where
  Index := R.Index
  path := sigma.sliceRowPath i
  connects := by
    intro r
    exact Or.inl ⟨Finset.mem_univ _, Finset.mem_univ _⟩
  node_disjoint := by
    intro r s hrs
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro v hvr hvs
    exact Finset.disjoint_left.mp (R.toPathPacking.node_disjoint hrs)
      (sigma.sliceRowPath_vertexSet_subset i r hvr)
      (sigma.sliceRowPath_vertexSet_subset i s hvs)

@[simp] theorem sliceRowPacking_card
    [Fintype V]
    (sigma : PathSlicing R M) (i : Fin M) :
    (sigma.sliceRowPacking i).card = R.card := rfl

/-- A path of `Qpack` intersects the row segment `σ_i(R_r)` when it has a
vertex in the strict slice interior on row `r`.  This is the formal
replacement for treating the paper's sliced row segment as a separate path. -/
def SliceSegmentIntersectsPath
    (sigma : PathSlicing R M) (Qpack : PathPacking G S T)
    (i : Fin M) (r : R.Index) (q : Qpack.Index) : Prop :=
  ∃ v : V, v ∈ (Qpack.path q).vertexSet ∧ sigma.SliceInterior r i v

/-- For a path assigned to slice `i`, intersecting the whole row is equivalent
to intersecting that row's `i`th open segment. -/
theorem sliceSegmentIntersectsPath_iff_pathsIntersect_of_mem_pathsInSlice
    (sigma : PathSlicing R M) (Qpack : PathPacking G S T)
    {i : Fin M} {r : R.Index} {q : Qpack.Index}
    (hq : q ∈ sigma.pathsInSlice Qpack i) :
    SliceSegmentIntersectsPath sigma Qpack i r q ↔
      PathPacking.PathsIntersect (R.path r) (Qpack.path q) := by
  constructor
  · rintro ⟨v, hvQ, hvSlice⟩
    exact Finset.not_disjoint_iff.2 ⟨v, hvSlice.1, hvQ⟩
  · intro hmeet
    rcases Finset.not_disjoint_iff.1 hmeet with ⟨v, hvR, hvQ⟩
    exact ⟨v, hvQ, (sigma.mem_pathsInSlice Qpack i q).1 hq hvQ hvR⟩

/-- A path meeting the linkage belongs to at most one strict slice. -/
theorem pathsInSlice_disjoint
    (sigma : PathSlicing R M) (Qpack : PathPacking G S T)
    (hintersects : PathPackingIntersectsLinkage R Qpack)
    {i j : Fin M} (hij : i ≠ j) :
    Disjoint (sigma.pathsInSlice Qpack i)
      (sigma.pathsInSlice Qpack j) := by
  classical
  rw [Finset.disjoint_left]
  intro q hqi hqj
  rcases hintersects q with ⟨r, hmeet⟩
  rcases Finset.not_disjoint_iff.1 hmeet with ⟨v, hvQ, hvR⟩
  have hvi :=
    (sigma.mem_pathsInSlice Qpack i q).1 hqi hvQ hvR
  have hvj :=
    (sigma.mem_pathsInSlice Qpack j q).1 hqj hvQ hvR
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · have hcuts :
        (R.path r).Before (sigma.cut r i.succ)
          (sigma.cut r j.castSucc) :=
      sigma.cut_monotone r (by
        apply Fin.mk_le_mk.2
        exact Nat.succ_le_iff.2 hijlt)
    have hvBefore :
        (R.path r).Before v (sigma.cut r j.castSucc) :=
      (R.path r).before_trans hvi.2.2.1 hcuts
    exact hvj.2.2.2.1
      ((R.path r).before_antisymm hvBefore hvj.2.1)
  · have hcuts :
        (R.path r).Before (sigma.cut r j.succ)
          (sigma.cut r i.castSucc) :=
      sigma.cut_monotone r (by
        apply Fin.mk_le_mk.2
        exact Nat.succ_le_iff.2 hjilt)
    have hvBefore :
        (R.path r).Before v (sigma.cut r i.castSucc) :=
      (R.path r).before_trans hvj.2.2.1 hcuts
    exact hvi.2.2.2.1
      ((R.path r).before_antisymm hvBefore hvi.2.1)

/-- On a path assigned to the slice, the strict-interior relation used by the
cleanup step is exactly intersection with the actual closed row segment.  A
path assigned to the slice cannot meet either boundary cut, because every
row-linkage intersection is required to be in the strict interior. -/
theorem sliceSegmentIntersectsPath_iff_sliceRowPath_intersects
    [Fintype V]
    (sigma : PathSlicing R M) (Qpack : PathPacking G S T)
    {i : Fin M} {r : R.Index} {q : Qpack.Index}
    (hq : q ∈ sigma.pathsInSlice Qpack i) :
    SliceSegmentIntersectsPath sigma Qpack i r q ↔
      PathPacking.PathsIntersect
        (sigma.sliceRowPacking i |>.path r) (Qpack.path q) := by
  constructor
  · rintro ⟨v, hvQ, hvSlice⟩
    rw [PathPacking.PathsIntersect, Finset.not_disjoint_iff]
    refine ⟨v, ?_, hvQ⟩
    let hcut :=
      sigma.cut_monotone r (Fin.castSucc_le_succ i)
    have hcuts_ne :
        sigma.cut r i.castSucc ≠ sigma.cut r i.succ := by
      intro hcuts
      have hvback :
          (R.path r).Before v (sigma.cut r i.castSucc) := by
        simpa [hcuts] using hvSlice.2.2.1
      exact hvSlice.2.2.2.1
        ((R.path r).before_antisymm hvback hvSlice.2.1)
    have hvClosed :
        v ∈ ((R.path r).segmentOfBefore hcut).vertexSet :=
      (R.path r).mem_segmentOfBefore_of_before_of_before
        hcut hvSlice.2.1 hvSlice.2.2.1
    rcases
        (((R.path r).segmentOfBefore hcut)
          |>.mem_vertexSet_iff_mem_dropLast_or_eq_target
            (by simpa [hcut] using hcuts_ne) v).1 hvClosed with
      hvDrop | hvRight
    · simpa [sliceRowPacking, sliceRowPath, hcut] using hvDrop
    · exact (hvSlice.2.2.2.2 (by simpa [hcut] using hvRight)).elim
  · intro hmeet
    rcases Finset.not_disjoint_iff.1 hmeet with ⟨v, hvSegment, hvQ⟩
    have hvR : v ∈ (R.path r).vertexSet :=
      sigma.sliceRowPath_vertexSet_subset i r hvSegment
    exact ⟨v, hvQ, (sigma.mem_pathsInSlice Qpack i q).1 hq hvQ hvR⟩

/-- The selected auxiliary paths meeting row segment `r` in slice `i`. -/
noncomputable def segmentIntersectingRightIndices
    (sigma : PathSlicing R M) (Qpack : PathPacking G S T)
    (i : Fin M) (Qset : Finset Qpack.Index) (r : R.Index) :
    Finset Qpack.Index := by
  classical
  exact Qset.filter fun q => SliceSegmentIntersectsPath sigma Qpack i r q

theorem mem_segmentIntersectingRightIndices
    (sigma : PathSlicing R M) (Qpack : PathPacking G S T)
    (i : Fin M) (Qset : Finset Qpack.Index) (r : R.Index)
    (q : Qpack.Index) :
    q ∈ sigma.segmentIntersectingRightIndices Qpack i Qset r ↔
      q ∈ Qset ∧ SliceSegmentIntersectsPath sigma Qpack i r q := by
  classical
  simp [segmentIntersectingRightIndices]

/-- The selected row segments met by auxiliary path `q` in slice `i`. -/
noncomputable def segmentIntersectingLeftIndices
    (sigma : PathSlicing R M) (Qpack : PathPacking G S T)
    (i : Fin M) (Rset : Finset R.Index) (q : Qpack.Index) :
    Finset R.Index := by
  classical
  exact Rset.filter fun r => SliceSegmentIntersectsPath sigma Qpack i r q

theorem mem_segmentIntersectingLeftIndices
    (sigma : PathSlicing R M) (Qpack : PathPacking G S T)
    (i : Fin M) (Rset : Finset R.Index) (q : Qpack.Index)
    (r : R.Index) :
    r ∈ sigma.segmentIntersectingLeftIndices Qpack i Rset q ↔
      r ∈ Rset ∧ SliceSegmentIntersectsPath sigma Qpack i r q := by
  classical
  simp [segmentIntersectingLeftIndices]

/-- A pair of row segments and auxiliary paths in one slice is
`(w,D)`-intersecting when every retained row segment meets at least `w`
retained auxiliary paths and every retained auxiliary path meets at least `D`
retained row segments. -/
def SliceIntersectingPathSetPair
    (sigma : PathSlicing R M) (Qpack : PathPacking G S T)
    (i : Fin M) (Rset : Finset R.Index) (Qset : Finset Qpack.Index)
    (w D : ℕ) : Prop :=
  (∀ r ∈ Rset, w ≤ (sigma.segmentIntersectingRightIndices Qpack i Qset r).card) ∧
    ∀ q ∈ Qset, D ≤ (sigma.segmentIntersectingLeftIndices Qpack i Rset q).card

/-- A selected subfamily of `Qpack` in a fixed slice, together with the
subfamilies obtained from Lemma 4.8.  This is the formal output of Section 4.3
for one slice. -/
structure SliceIntersectingSubfamilies
    (sigma : PathSlicing R M) (Qpack : PathPacking G S T)
    (i : Fin M) (w D : ℕ) where
  /-- Row segments retained by Lemma 4.8, indexed by linkage rows. -/
  rows : Finset R.Index
  /-- Auxiliary paths retained by Lemma 4.8. -/
  paths : Finset Qpack.Index
  /-- Retained rows are rows of the linkage. -/
  rows_subset : rows ⊆ Finset.univ
  /-- Retained auxiliary paths lie in the slice. -/
  paths_subset : paths ⊆ sigma.pathsInSlice Qpack i
  /-- The retained row/path families are `(w,D)`-intersecting. -/
  intersecting :
    sigma.SliceIntersectingPathSetPair Qpack i rows paths w D
  /-- At least half the slice paths survive. -/
  half_paths :
    (sigma.pathsInSlice Qpack i).card ≤ 2 * paths.card
  /-- Every discarded row segment meets at most `w` retained paths. -/
  discarded_rows_sparse :
    ∀ r ∈ (Finset.univ : Finset R.Index) \ rows,
      (sigma.segmentIntersectingRightIndices Qpack i paths r).card ≤ w

/-- Section 4.3 applied to one slice.  The hypotheses say that every path in
the slice meets at least `2D` row segments and that the slice is large enough
for Lemma 4.8. -/
noncomputable def exists_slice_intersecting_subfamilies
    (sigma : PathSlicing R M) (Qpack : PathPacking G S T)
    (i : Fin M) {w D : ℕ}
    (hD : 0 < D)
    (hdense :
      ∀ q ∈ sigma.pathsInSlice Qpack i,
        2 * D ≤
          (sigma.segmentIntersectingLeftIndices Qpack i
            (Finset.univ : Finset R.Index) q).card)
    (hcard :
      2 * (Fintype.card R.Index) * w ≤
        D * (sigma.pathsInSlice Qpack i).card) :
    SliceIntersectingSubfamilies sigma Qpack i w D := by
  classical
  let rel : R.Index → Qpack.Index → Prop :=
    fun r q => SliceSegmentIntersectsPath sigma Qpack i r q
  have hdense' :
      ∀ q ∈ sigma.pathsInSlice Qpack i,
        2 * D ≤ ((Finset.univ : Finset R.Index).bipartiteBelow rel q).card := by
    intro q hq
    simpa [segmentIntersectingLeftIndices, rel] using hdense q hq
  let hex :=
    FiniteBipartitePruning.PruneTrace.exists_intersecting_subsets
      (rel := rel) (w := w) (D := D)
      (Finset.univ : Finset R.Index) (sigma.pathsInSlice Qpack i)
      hD hdense' (by simpa [PathPacking.card] using hcard)
  let rows := Classical.choose hex
  let hex2 := Classical.choose_spec hex
  let paths := Classical.choose hex2
  have hspec := Classical.choose_spec hex2
  have hrows : rows ⊆ (Finset.univ : Finset R.Index) := hspec.1
  have hpaths : paths ⊆ sigma.pathsInSlice Qpack i := hspec.2.1
  have hleft :
      ∀ r ∈ rows, w ≤ (paths.bipartiteAbove rel r).card :=
    hspec.2.2.1
  have hright :
      ∀ q ∈ paths, D ≤ (rows.bipartiteBelow rel q).card :=
    hspec.2.2.2.1
  have hhalf : (sigma.pathsInSlice Qpack i).card ≤ 2 * paths.card :=
    hspec.2.2.2.2.1
  have hsparse :
      ∀ r ∈ (Finset.univ : Finset R.Index) \ rows,
        (paths.bipartiteAbove rel r).card ≤ w :=
    hspec.2.2.2.2.2
  have hinter :
      sigma.SliceIntersectingPathSetPair Qpack i rows paths w D := by
    constructor
    · intro r hr
      simpa [segmentIntersectingRightIndices, rel] using hleft r hr
    · intro q hq
      simpa [segmentIntersectingLeftIndices, rel] using hright q hq
  have hsparse' :
      ∀ r ∈ (Finset.univ : Finset R.Index) \ rows,
        (sigma.segmentIntersectingRightIndices Qpack i paths r).card ≤ w := by
    intro r hr
    simpa [segmentIntersectingRightIndices, rel] using hsparse r hr
  exact
    { rows := rows
      paths := paths
      rows_subset := hrows
      paths_subset := hpaths
      intersecting := hinter
      half_paths := hhalf
      discarded_rows_sparse := hsparse' }

/-- The Section 4.3 cleanup output, converted from its strict-interior
relation to the actual row-segment packing consumed by Theorem 4.11. -/
theorem SliceIntersectingSubfamilies.actual_intersecting
    [Fintype V]
    (sigma : PathSlicing R M) (Qpack : PathPacking G S T)
    (i : Fin M) {w D : ℕ}
    (Output : SliceIntersectingSubfamilies sigma Qpack i w D) :
    (sigma.sliceRowPacking i).IntersectingPathSetPair
      Qpack Output.rows Output.paths w D := by
  classical
  constructor
  · intro r hr
    have h :=
      Output.intersecting.1 r hr
    apply h.trans_eq
    congr 1
    ext q
    rw [sigma.mem_segmentIntersectingRightIndices]
    rw [PathPacking.mem_intersectingRightIndices]
    constructor
    · rintro ⟨hq, hrel⟩
      exact
        ⟨hq,
          (sigma.sliceSegmentIntersectsPath_iff_sliceRowPath_intersects
            Qpack (Output.paths_subset hq)).1 hrel⟩
    · rintro ⟨hq, hrel⟩
      exact
        ⟨hq,
          (sigma.sliceSegmentIntersectsPath_iff_sliceRowPath_intersects
            Qpack (Output.paths_subset hq)).2 hrel⟩
  · intro q hq
    have h :=
      Output.intersecting.2 q hq
    apply h.trans_eq
    congr 1
    ext r
    rw [sigma.mem_segmentIntersectingLeftIndices]
    constructor
    · rintro ⟨hr, hrel⟩
      apply
        (PathPacking.mem_intersectingLeftIndices
          (sigma.sliceRowPacking i) Qpack Output.rows q r).2
      exact ⟨hr,
          (sigma.sliceSegmentIntersectsPath_iff_sliceRowPath_intersects
            Qpack (Output.paths_subset hq)).1 hrel⟩
    · intro hmem
      rcases
          (PathPacking.mem_intersectingLeftIndices
            (sigma.sliceRowPacking i) Qpack Output.rows q r).1 hmem with
        ⟨hr, hrel⟩
      exact
        ⟨hr,
          (sigma.sliceSegmentIntersectsPath_iff_sliceRowPath_intersects
            Qpack (Output.paths_subset hq)).2 hrel⟩

end PathSlicing

end SimpleGraph

end Lax17Proofs
