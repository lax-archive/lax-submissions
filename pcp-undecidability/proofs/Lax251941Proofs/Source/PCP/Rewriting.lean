/-
# String rewriting systems

Sipser's construction in Section 5.2 encodes the computation of a Turing machine as a
sequence of configurations, consecutive ones being related by a *local* rewriting of the
configuration string.  We isolate that combinatorial structure here: a string rewriting
system consists of a finite alphabet, a finite list of rewriting rules `u → v` (applied in
an arbitrary context `l _ r`), and a finite list of symbols that may be appended at the
right end of a string (this models the infinitely many blanks to the right of a Turing
machine configuration).
-/
import Lax251941Proofs.Source.PCP.Basic

namespace Lax251941Proofs.PCP

variable {α : Type*}

/-- A string rewriting system: a finite alphabet, a finite list of rewriting rules, and a
list of symbols that may be appended at the right end of a string. -/
structure SRS (α : Type*) where
  /-- The (finite) alphabet. -/
  alphabet : List α
  /-- The rewriting rules `u → v`. -/
  rules : List (List α × List α)
  /-- Symbols that may be appended at the right-hand end of a string. -/
  ext : List α

/-- Well-formedness of a string rewriting system: the rules use only letters of the
alphabet and have nonempty left- and right-hand sides, and the appendable symbols belong
to the alphabet. -/
structure SRS.WF (S : SRS α) : Prop where
  rules_left_sub : ∀ p ∈ S.rules, ∀ a ∈ p.1, a ∈ S.alphabet
  rules_right_sub : ∀ p ∈ S.rules, ∀ a ∈ p.2, a ∈ S.alphabet
  rules_left_ne : ∀ p ∈ S.rules, p.1 ≠ []
  rules_right_ne : ∀ p ∈ S.rules, p.2 ≠ []
  ext_sub : ∀ x ∈ S.ext, x ∈ S.alphabet

/-- One rewriting step using a rule of the system, applied in a context. -/
inductive StepRule (rules : List (List α × List α)) : List α → List α → Prop
  | mk (l u v r : List α) : (u, v) ∈ rules → StepRule rules (l ++ u ++ r) (l ++ v ++ r)

/-- One step of a string rewriting system: either an application of a rule, or the
appending of one of the designated symbols at the right end. -/
inductive Step (S : SRS α) : List α → List α → Prop
  | rule {a b : List α} : StepRule S.rules a b → Step S a b
  | ext {c : List α} {x : α} : x ∈ S.ext → Step S c (c ++ [x])

/-- Reachability: the reflexive transitive closure of `Step`. -/
def Reaches (S : SRS α) : List α → List α → Prop := Relation.ReflTransGen (Step S)

lemma Reaches.refl (S : SRS α) (a : List α) : Reaches S a a := Relation.ReflTransGen.refl

lemma Reaches.trans {S : SRS α} {a b c : List α} (h₁ : Reaches S a b) (h₂ : Reaches S b c) :
    Reaches S a c := Relation.ReflTransGen.trans h₁ h₂

lemma Reaches.single {S : SRS α} {a b : List α} (h : Step S a b) : Reaches S a b :=
  Relation.ReflTransGen.single h

/-- Rule steps are compatible with concatenation on the left. -/
lemma StepRule.append_left {rules : List (List α × List α)} {a b : List α} (z : List α)
    (h : StepRule rules a b) : StepRule rules (z ++ a) (z ++ b) := by
  cases h with
  | mk l u v r hm =>
    simpa [List.append_assoc] using StepRule.mk (z ++ l) u v r hm

/-- Rule steps are compatible with concatenation on the right. -/
lemma StepRule.append_right {rules : List (List α × List α)} {a b : List α} (z : List α)
    (h : StepRule rules a b) : StepRule rules (a ++ z) (b ++ z) := by
  cases h with
  | mk l u v r hm =>
    simpa [List.append_assoc] using StepRule.mk l u v (r ++ z) hm

/-- Reachability by rule steps only. -/
def ReachesRule (S : SRS α) : List α → List α → Prop :=
  Relation.ReflTransGen (StepRule S.rules)

lemma ReachesRule.toReaches {S : SRS α} {a b : List α} (h : ReachesRule S a b) :
    Reaches S a b := by
  induction h with
  | refl => exact Reaches.refl _ _
  | tail _ hstep ih => exact ih.trans (Reaches.single (Step.rule hstep))

lemma ReachesRule.append_left {S : SRS α} {a b : List α} (z : List α)
    (h : ReachesRule S a b) : ReachesRule S (z ++ a) (z ++ b) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (hstep.append_left z)

lemma ReachesRule.append_right {S : SRS α} {a b : List α} (z : List α)
    (h : ReachesRule S a b) : ReachesRule S (a ++ z) (b ++ z) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (hstep.append_right z)

/-- `BodyRel S δ B` holds when the string `δ` is transformed into `B` by a sequence of
"copy" moves (a letter is carried over unchanged) and rule applications, processed from
left to right.  This is exactly the relation realized by the dominos of parts 2, 3, 4
and 6 of Sipser's construction. -/
inductive BodyRel (S : SRS α) : List α → List α → Prop
  | nil : BodyRel S [] []
  | copy {δ B : List α} {a : α} : a ∈ S.alphabet → BodyRel S δ B →
      BodyRel S (δ ++ [a]) (B ++ [a])
  | rule {δ B u v : List α} : (u, v) ∈ S.rules → BodyRel S δ B →
      BodyRel S (δ ++ u) (B ++ v)

/-- A parallel left-to-right rewriting can be sequentialized. -/
lemma BodyRel.reachesRule {S : SRS α} {δ B : List α} (h : BodyRel S δ B) :
    ReachesRule S δ B := by
  induction h with
  | nil => exact Relation.ReflTransGen.refl
  | copy _ _ ih => exact ih.append_right _
  | @rule δ B u v hmem _ ih =>
    refine Relation.ReflTransGen.trans (ih.append_right u) ?_
    exact Relation.ReflTransGen.single (by simpa using StepRule.mk B u v [] hmem)

lemma BodyRel.reaches {S : SRS α} {δ B : List α} (h : BodyRel S δ B) : Reaches S δ B :=
  h.reachesRule.toReaches

/-- Letters produced by `BodyRel` come from the alphabet. -/
lemma BodyRel.mem_alphabet {S : SRS α} (hS : S.WF) {δ B : List α} (h : BodyRel S δ B) :
    ∀ a ∈ B, a ∈ S.alphabet := by
  induction h with
  | nil => simp
  | copy ha _ ih =>
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact ih b hb
    · simpa [List.mem_singleton.mp hb] using ha
  | @rule δ B u v hmem _ ih =>
    intro b hb
    rcases List.mem_append.mp hb with hb | hb
    · exact ih b hb
    · exact hS.rules_right_sub (u, v) hmem b hb

/-- If a left-to-right rewriting produces the empty string, it consumed the empty string. -/
lemma BodyRel.eq_nil_of_eq_nil {S : SRS α} (hS : S.WF) {δ B : List α} (h : BodyRel S δ B) :
    B = [] → δ = [] := by
  induction h with
  | nil => intro _; rfl
  | copy _ _ _ => intro hB; simp at hB
  | @rule δ B u v hmem _ _ =>
    intro hB
    exact absurd (List.append_eq_nil_iff.mp hB).2 (hS.rules_right_ne (u, v) hmem)

lemma BodyRel.eq_nil_of_nil {S : SRS α} (hS : S.WF) {δ : List α} (h : BodyRel S δ []) :
    δ = [] := h.eq_nil_of_eq_nil hS rfl

/-- Every string reachable from a string over the alphabet is again over the alphabet. -/
lemma Reaches.mem_alphabet {S : SRS α} (hS : S.WF) {a b : List α}
    (hab : Reaches S a b) (ha : ∀ x ∈ a, x ∈ S.alphabet) : ∀ x ∈ b, x ∈ S.alphabet := by
  induction hab with
  | refl => exact ha
  | tail _ hstep ih =>
    rename_i c d _
    cases hstep with
    | rule hr =>
      cases hr with
      | mk l u v r hmem =>
        intro z hz
        simp only [List.mem_append] at hz ⊢
        rcases hz with (hz | hz) | hz
        · exact ih z (by simp [hz])
        · exact hS.rules_right_sub (u, v) hmem z hz
        · exact ih z (by simp [hz])
    | @ext x hx =>
      intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact ih z hz
      · simpa [List.mem_singleton.mp hz] using hS.ext_sub x hx

end Lax251941Proofs.PCP
