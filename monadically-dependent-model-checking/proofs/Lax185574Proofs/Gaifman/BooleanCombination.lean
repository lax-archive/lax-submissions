import Lax185574Proofs.Gaifman.GaifmanNormalForm
import Mathlib.Data.List.Sublists

/-!
Algebra for the reified Boolean combinations used by the normal form.

Adapted from lax-512892 (faghasemi/gaifman-theorem-lax, commit 7c2b896), file
`proofs/Lax512892Proofs/BooleanCombination.lean`.
-/

namespace Lax185574Proofs.Gaifman.BooleanCombination

open Lax185574Proofs.Gaifman.GaifmanNormalForm

universe u v w

/-- Map every atom of a Boolean combination. -/
def map {α : Type u} {β : Type v} (f : α → β) :
    BooleanCombination α → BooleanCombination β
  | .atom a => .atom (f a)
  | .truth => .truth
  | .not b => .not (map f b)
  | .and b c => .and (map f b) (map f c)

@[simp] theorem eval_map {α : Type u} {β : Type v} (f : α → β)
    (value : β → Prop) (b : BooleanCombination α) :
    (map f b).eval value ↔ b.eval (value ∘ f) := by
  induction b with
  | atom a => rfl
  | truth => rfl
  | not b ih => simpa [map, BooleanCombination.eval] using not_congr ih
  | and b c ihb ihc =>
      simpa [map, BooleanCombination.eval] using and_congr ihb ihc

@[simp] theorem atoms_map {α : Type u} {β : Type v} (f : α → β)
    (b : BooleanCombination α) :
    (map f b).atoms = b.atoms.map f := by
  induction b with
  | atom a => rfl
  | truth => rfl
  | not b ih => simpa [map, BooleanCombination.atoms] using ih
  | and b c ihb ihc => simp [map, BooleanCombination.atoms, ihb, ihc]

theorem eval_map_inl {α : Type u} {γ : Type w}
    {left : α → Prop} {right : γ → Prop} (b : BooleanCombination α) :
    (map Sum.inl b).eval (Sum.elim left right) ↔ b.eval left := by
  rw [eval_map]
  rfl

theorem eval_map_inr {α : Type u} {γ : Type w}
    {left : α → Prop} {right : γ → Prop} (b : BooleanCombination γ) :
    (map Sum.inr b).eval (Sum.elim left right) ↔ b.eval right := by
  rw [eval_map]
  rfl

/-- Substitute a Boolean combination for every atom. -/
def bind {α : Type u} {β : Type v} (f : α → BooleanCombination β) :
    BooleanCombination α → BooleanCombination β
  | .atom a => f a
  | .truth => .truth
  | .not b => .not (bind f b)
  | .and b c => .and (bind f b) (bind f c)

@[simp] theorem eval_bind {α : Type u} {β : Type v}
    (f : α → BooleanCombination β) (value : β → Prop)
    (b : BooleanCombination α) :
    (bind f b).eval value ↔ b.eval (fun a => (f a).eval value) := by
  induction b with
  | atom a => rfl
  | truth => rfl
  | not b ih => simpa [bind, BooleanCombination.eval] using not_congr ih
  | and b c ihb ihc =>
      simpa [bind, BooleanCombination.eval] using and_congr ihb ihc

@[simp] theorem atoms_bind {α : Type u} {β : Type v}
    (f : α → BooleanCombination β) (b : BooleanCombination α) :
    (bind f b).atoms = b.atoms.flatMap (fun a => (f a).atoms) := by
  induction b with
  | atom a => simp [bind, BooleanCombination.atoms]
  | truth => rfl
  | not b ih => simpa [bind, BooleanCombination.atoms] using ih
  | and b c ihb ihc =>
      simp [bind, BooleanCombination.atoms, ihb, ihc, List.flatMap_append]

/-- Replace atom values pointwise without changing the value of a Boolean
combination. -/
theorem eval_congr {α : Type u} (b : BooleanCombination α)
    {value₁ value₂ : α → Prop}
    (h : ∀ a, a ∈ b.atoms → (value₁ a ↔ value₂ a)) :
    b.eval value₁ ↔ b.eval value₂ := by
  induction b with
  | atom a => exact h a (by simp [BooleanCombination.atoms])
  | truth => rfl
  | not b ih =>
      apply not_congr
      exact ih fun a ha => h a (by simpa [BooleanCombination.atoms] using ha)
  | and b c ihb ihc =>
      apply and_congr
      · exact ihb fun a ha => h a (by simp [BooleanCombination.atoms, ha])
      · exact ihc fun a ha => h a (by simp [BooleanCombination.atoms, ha])

/-- Disjunction expressed using the primitive `not` and `and` constructors. -/
def or {α : Type u} (b c : BooleanCombination α) : BooleanCombination α :=
  .not (.and (.not b) (.not c))

@[simp] theorem eval_or {α : Type u} (value : α → Prop)
    (b c : BooleanCombination α) :
    (or b c).eval value ↔ b.eval value ∨ c.eval value := by
  simp only [or, BooleanCombination.eval]
  tauto

/-- The always-false Boolean combination. -/
def falsity {α : Type u} : BooleanCombination α := .not .truth

@[simp] theorem eval_falsity {α : Type u} (value : α → Prop) :
    (falsity : BooleanCombination α).eval value ↔ False := by
  simp [falsity, BooleanCombination.eval]

/-- Conjunction of a finite list of combinations. -/
def all {α : Type u} : List (BooleanCombination α) → BooleanCombination α
  | [] => .truth
  | b :: bs => .and b (all bs)

/-- Disjunction of a finite list of combinations. -/
def any {α : Type u} : List (BooleanCombination α) → BooleanCombination α
  | [] => falsity
  | b :: bs => or b (any bs)

@[simp] theorem eval_all {α : Type u} (value : α → Prop)
    (bs : List (BooleanCombination α)) :
    (all bs).eval value ↔ ∀ b ∈ bs, b.eval value := by
  induction bs with
  | nil => simp [all, BooleanCombination.eval]
  | cons b bs ih => simp [all, BooleanCombination.eval, ih]

@[simp] theorem eval_any {α : Type u} (value : α → Prop)
    (bs : List (BooleanCombination α)) :
    (any bs).eval value ↔ ∃ b ∈ bs, b.eval value := by
  induction bs with
  | nil => simp [any]
  | cons b bs ih => simp [any, ih]

@[simp] theorem atoms_all {α : Type u} (bs : List (BooleanCombination α)) :
    (all bs).atoms = bs.flatMap BooleanCombination.atoms := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [all, BooleanCombination.atoms, ih]

@[simp] theorem atoms_any {α : Type u} (bs : List (BooleanCombination α)) :
    (any bs).atoms = bs.flatMap BooleanCombination.atoms := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [any, or, BooleanCombination.atoms, ih]

theorem mem_atoms_any {α : Type u} {a : α}
    (bs : List (BooleanCombination α)) :
    a ∈ (any bs).atoms ↔ ∃ b ∈ bs, a ∈ b.atoms := by
  rw [atoms_any, List.mem_flatMap]

/-- Interpret a Boolean combination using connectives carried by its atom
type. -/
def interp {α : Type u} (truth : α) (neg : α → α) (conj : α → α → α) :
    BooleanCombination α → α
  | .atom a => a
  | .truth => truth
  | .not b => neg (interp truth neg conj b)
  | .and b c => conj (interp truth neg conj b) (interp truth neg conj c)

theorem eval_interp {α : Type u} {value : α → Prop} {truth : α}
    {neg : α → α} {conj : α → α → α}
    (htruth : value truth) (hneg : ∀ a, value (neg a) ↔ ¬ value a)
    (hconj : ∀ a b, value (conj a b) ↔ value a ∧ value b)
    (bc : BooleanCombination α) :
    value (interp truth neg conj bc) ↔ bc.eval value := by
  induction bc with
  | atom a => rfl
  | truth => simpa [interp, BooleanCombination.eval] using htruth
  | not b ih => simpa [interp, BooleanCombination.eval, ih] using hneg (interp truth neg conj b)
  | and b c ihb ihc =>
      simpa [interp, BooleanCombination.eval, ihb, ihc] using
        hconj (interp truth neg conj b) (interp truth neg conj c)

/-- The right-hand atoms of a Boolean combination over a sum. -/
def rightAtoms {α : Type u} {γ : Type w}
    (b : BooleanCombination (α ⊕ γ)) : List γ :=
  b.atoms.filterMap Sum.getRight?

theorem mem_rightAtoms {α : Type u} {γ : Type w}
    {b : BooleanCombination (α ⊕ γ)} {g : γ} :
    g ∈ rightAtoms b ↔ Sum.inr g ∈ b.atoms := by
  simp only [rightAtoms, List.mem_filterMap]
  constructor
  · rintro ⟨x, hx, hxg⟩
    rcases x with a | g'
    · simp at hxg
    · rw [show g' = g by simpa using hxg] at hx
      exact hx
  · intro h
    exact ⟨Sum.inr g, h, by simp⟩

/-- Replace right-hand atoms by a fixed Boolean truth pattern. -/
def collapse {α : Type u} {γ : Type w} (τ : γ → Bool)
    (b : BooleanCombination (α ⊕ γ)) : BooleanCombination α :=
  bind (Sum.elim (fun a => .atom a)
    (fun g => if τ g then .truth else falsity)) b

theorem eval_collapse {α : Type u} {γ : Type w} {τ : γ → Bool}
    {left : α → Prop} {right : γ → Prop}
    (b : BooleanCombination (α ⊕ γ))
    (hτ : ∀ g, Sum.inr g ∈ b.atoms → (τ g = true ↔ right g)) :
    b.eval (Sum.elim left right) ↔ (collapse τ b).eval left := by
  rw [collapse, eval_bind]
  refine eval_congr b ?_
  rintro (a | g) ha
  · rfl
  · show right g ↔ (if τ g then BooleanCombination.truth else falsity).eval left
    by_cases h : τ g = true
    · simp [h, (hτ g ha).mp h, BooleanCombination.eval]
    · have hn : ¬ right g := fun hg => h ((hτ g ha).mpr hg)
      simp [h, hn]

theorem mem_atoms_collapse {α : Type u} {γ : Type w} {τ : γ → Bool}
    {b : BooleanCombination (α ⊕ γ)} {a : α} :
    a ∈ (collapse τ b).atoms ↔ Sum.inl a ∈ b.atoms := by
  induction b with
  | atom x =>
      rcases x with x | g
      · simp [collapse, bind, BooleanCombination.atoms]
      · by_cases h : τ g = true <;>
          simp [collapse, bind, h, falsity, BooleanCombination.atoms]
  | truth => simp [collapse, bind, BooleanCombination.atoms]
  | not b ih => simpa [collapse, bind, BooleanCombination.atoms] using ih
  | and b c ihb ihc =>
      show a ∈ ((collapse τ b).atoms ++ (collapse τ c).atoms) ↔
        Sum.inl a ∈ (b.atoms ++ c.atoms)
      simp [ihb, ihc]

/-- A Boolean combination asserting a truth pattern on the right atoms. -/
def pattern {α : Type u} {γ : Type w} (τ : γ → Bool)
    (b : BooleanCombination (α ⊕ γ)) : BooleanCombination γ :=
  all ((rightAtoms b).map fun g =>
    if τ g then .atom g else .not (.atom g))

theorem eval_pattern {α : Type u} {γ : Type w} {τ : γ → Bool}
    {right : γ → Prop} (b : BooleanCombination (α ⊕ γ)) :
    (pattern τ b).eval right ↔
      ∀ g, Sum.inr g ∈ b.atoms → (τ g = true ↔ right g) := by
  rw [pattern, eval_all]
  simp only [List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h g hg
    have hv := h _ g (mem_rightAtoms.mpr hg) rfl
    by_cases ht : τ g = true
    · rw [if_pos ht] at hv
      exact iff_of_true ht (by exact hv)
    · rw [if_neg ht] at hv
      exact iff_of_false ht (by exact hv)
  · rintro h x g hg rfl
    have hv := h g (mem_rightAtoms.mp hg)
    by_cases ht : τ g = true
    · rw [if_pos ht]
      exact hv.mp ht
    · rw [if_neg ht]
      exact fun hr => ht (hv.mpr hr)

theorem mem_atoms_pattern {α : Type u} {γ : Type w} {τ : γ → Bool}
    {b : BooleanCombination (α ⊕ γ)} {g : γ} :
    g ∈ (pattern τ b).atoms ↔ Sum.inr g ∈ b.atoms := by
  rw [pattern, atoms_all]
  simp only [List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨x, ⟨g', hg', rfl⟩, hx⟩
    by_cases ht : τ g' = true
    · simp [ht, BooleanCombination.atoms] at hx
      subst hx
      exact mem_rightAtoms.mp hg'
    · simp [ht, BooleanCombination.atoms] at hx
      subst hx
      exact mem_rightAtoms.mp hg'
  · intro hg
    refine ⟨(if τ g then .atom g else .not (.atom g)), ?_, ?_⟩
    · exact ⟨g, mem_rightAtoms.mpr hg, rfl⟩
    · by_cases ht : τ g = true <;> simp [ht, BooleanCombination.atoms]

/-- The finitely many truth patterns relevant to the occurring right atoms. -/
noncomputable def assignments {α : Type u} {γ : Type w}
    (b : BooleanCombination (α ⊕ γ)) : List (γ → Bool) :=
  (rightAtoms b).sublists.map fun s g =>
    @decide (g ∈ s) (Classical.propDecidable _)

theorem exists_mem_assignments {α : Type u} {γ : Type w}
    (b : BooleanCombination (α ⊕ γ)) (right : γ → Prop) :
    ∃ τ ∈ assignments b,
      ∀ g, Sum.inr g ∈ b.atoms → (τ g = true ↔ right g) := by
  classical
  let s := (rightAtoms b).filter fun g => decide (right g)
  refine ⟨fun g => @decide (g ∈ s) (Classical.propDecidable _), ?_, ?_⟩
  · rw [assignments]
    exact List.mem_map.mpr ⟨s, List.mem_sublists.mpr List.filter_sublist, rfl⟩
  · intro g hg
    simp [s, mem_rightAtoms.mpr hg]

theorem exists_eval_sum_iff {α : Type u} {γ : Type w} {ι : Type*}
    (b : BooleanCombination (α ⊕ γ)) (left : ι → α → Prop)
    (right : γ → Prop) :
    (∃ x, b.eval (Sum.elim (left x) right)) ↔
      ∃ τ ∈ assignments b,
        (pattern τ b).eval right ∧ ∃ x, (collapse τ b).eval (left x) := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨τ, hτ, hagree⟩ := exists_mem_assignments b right
    exact ⟨τ, hτ, (eval_pattern b).mpr hagree, x,
      (eval_collapse b hagree).mp hx⟩
  · rintro ⟨τ, -, hpat, x, hx⟩
    exact ⟨x, (eval_collapse b ((eval_pattern b).mp hpat)).mpr hx⟩

/-- Rebuild the finite truth-pattern case split, replacing each collapsed
left formula by a supplied Boolean combination. -/
noncomputable def pullOut {α : Type u} {γ : Type w} {δ : Type v}
    (b : BooleanCombination (α ⊕ γ))
    (replacement : (γ → Bool) → BooleanCombination δ) :
    BooleanCombination (δ ⊕ γ) :=
  any ((assignments b).map fun τ =>
    .and (map Sum.inl (replacement τ)) (map Sum.inr (pattern τ b)))

theorem eval_pullOut {α : Type u} {γ : Type w} {δ : Type v} {ι : Type*}
    (b : BooleanCombination (α ⊕ γ))
    (replacement : (γ → Bool) → BooleanCombination δ)
    (left : ι → α → Prop) (right : γ → Prop) (newValue : δ → Prop)
    (h : ∀ τ, (replacement τ).eval newValue ↔
      ∃ x, (collapse τ b).eval (left x)) :
    (∃ x, b.eval (Sum.elim (left x) right)) ↔
      (pullOut b replacement).eval (Sum.elim newValue right) := by
  rw [pullOut, eval_any, exists_eval_sum_iff b left right]
  simp only [List.mem_map, exists_exists_and_eq_and, BooleanCombination.eval,
    eval_map_inl, eval_map_inr, h]
  exact exists_congr fun τ => and_congr_right fun _ => and_comm

theorem mem_atoms_pullOut_left {α : Type u} {γ : Type w} {δ : Type v}
    {b : BooleanCombination (α ⊕ γ)}
    {replacement : (γ → Bool) → BooleanCombination δ} {d : δ} :
    Sum.inl d ∈ (pullOut b replacement).atoms ↔
      ∃ τ ∈ assignments b, d ∈ (replacement τ).atoms := by
  rw [pullOut, mem_atoms_any]
  simp only [List.mem_map, exists_exists_and_eq_and,
    BooleanCombination.atoms, List.mem_append, atoms_map, List.mem_map]
  refine exists_congr fun τ => and_congr_right fun _ => ?_
  constructor
  · rintro (⟨d', hd', hde⟩ | ⟨g, -, hge⟩)
    · exact (Sum.inl_injective hde) ▸ hd'
    · exact absurd hge (by simp)
  · exact fun h => Or.inl ⟨d, h, rfl⟩

theorem mem_atoms_pullOut_right {α : Type u} {γ : Type w} {δ : Type v}
    {b : BooleanCombination (α ⊕ γ)}
    {replacement : (γ → Bool) → BooleanCombination δ} {g : γ}
    (h : Sum.inr g ∈ (pullOut b replacement).atoms) :
    Sum.inr g ∈ b.atoms := by
  rw [pullOut, mem_atoms_any] at h
  simp only [List.mem_map, exists_exists_and_eq_and,
    BooleanCombination.atoms, List.mem_append, atoms_map, List.mem_map] at h
  obtain ⟨τ, -, (⟨d, -, hde⟩ | ⟨g', hg', hge⟩)⟩ := h
  · exact absurd hde (by simp)
  · exact mem_atoms_pattern.mp ((Sum.inr_injective hge) ▸ hg')

end Lax185574Proofs.Gaifman.BooleanCombination
