import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1CorridorCore

namespace Lax17Proofs

universe u v w

/-!
# Finite measures for the Appendix B.1 rerouting proof

The paper uses two finite descents.  Both have the same finite-set core: new
edges may be taken from a fixed support, while at least one old edge outside
that support disappears.  The cardinality of `current \ fixed` then strictly
decreases.  Keeping this lemma independent of paths avoids duplicating the
arithmetic in the bump, cross, and hill steps.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy
namespace AppendixB1


/-- A finite-descent eliminator with an external successful outcome.

This is the form used twice in Appendix B.1.  At a nonterminal state, a local
switch either already lowers the number of degree-two auxiliary vertices, or
returns a new state with a strictly smaller edge measure. -/
theorem output_or_exists_terminal_of_nat_descent
    {State : Type*} {Output : Prop}
    (measure : State → ℕ) (Terminal : State → Prop)
    (step : ∀ s : State, ¬ Terminal s →
      Output ∨ ∃ s' : State, measure s' < measure s)
    (s₀ : State) :
    Output ∨ ∃ s : State, Terminal s := by
  classical
  let motive : State → Prop := fun _ =>
    Output ∨ ∃ s : State, Terminal s
  change motive s₀
  refine (InvImage.wf measure <| (Nat.lt_wfRel).2).induction
    (C := motive) s₀ ?_
  intro s ih
  by_cases hterminal : Terminal s
  · exact Or.inr ⟨s, hterminal⟩
  · rcases step s hterminal with hout | ⟨s', hlt⟩
    · exact Or.inl hout
    · exact ih s' hlt

/-- The number of currently used elements outside a fixed support. -/
def outsideFixedMeasure {α : Type u} [DecidableEq α]
    (current fixed : Finset α) : ℕ :=
  (current \ fixed).card

/-- Adding only fixed-support elements while deleting one old non-fixed
element strictly decreases `outsideFixedMeasure`. -/
theorem outsideFixedMeasure_lt
    {α : Type u} [DecidableEq α]
    {old new fixed : Finset α} {e : α}
    (hnew : new ⊆ old ∪ fixed)
    (he_old : e ∈ old) (he_fixed : e ∉ fixed) (he_new : e ∉ new) :
    outsideFixedMeasure new fixed < outsideFixedMeasure old fixed := by
  classical
  have hsub : new \ fixed ⊆ old \ fixed := by
    intro x hx
    have hxnew : x ∈ new := (Finset.mem_sdiff.mp hx).1
    have hxnot : x ∉ fixed := (Finset.mem_sdiff.mp hx).2
    rcases Finset.mem_union.mp (hnew hxnew) with hxold | hxfixed
    · exact Finset.mem_sdiff.mpr ⟨hxold, hxnot⟩
    · exact False.elim (hxnot hxfixed)
  have he_old_diff : e ∈ old \ fixed :=
    Finset.mem_sdiff.mpr ⟨he_old, he_fixed⟩
  have he_new_diff : e ∉ new \ fixed := by
    intro he
    exact he_new (Finset.mem_sdiff.mp he).1
  have hstrict : new \ fixed ⊂ old \ fixed := by
    refine ⟨hsub, ?_⟩
    intro hreverse
    exact he_new_diff (hreverse he_old_diff)
  exact Finset.card_lt_card hstrict

/-- A convenient form when the new set is already a subset of the old set. -/
theorem outsideFixedMeasure_lt_of_subset
    {α : Type u} [DecidableEq α]
    {old new fixed : Finset α} {e : α}
    (hnew : new ⊆ old)
    (he_old : e ∈ old) (he_fixed : e ∉ fixed) (he_new : e ∉ new) :
    outsideFixedMeasure new fixed < outsideFixedMeasure old fixed :=
  outsideFixedMeasure_lt
    (fun _ hx => Finset.mem_union_left fixed (hnew hx))
    he_old he_fixed he_new

/-- Replacing one member of a finite union by elements from the old union or
the fixed support gives the subset hypothesis used by
`outsideFixedMeasure_lt`. -/
theorem biUnion_replace_subset_union_fixed
    {ι α : Type u} [Fintype ι] [DecidableEq ι] [DecidableEq α]
    (oldPart newPart : ι → Finset α) (fixed : Finset α) (changed : ι)
    (hchanged : newPart changed ⊆ oldPart changed ∪ fixed)
    (hunchanged : ∀ i, i ≠ changed → newPart i = oldPart i) :
    (Finset.univ.biUnion newPart) ⊆
      (Finset.univ.biUnion oldPart) ∪ fixed := by
  classical
  intro x hx
  rcases Finset.mem_biUnion.mp hx with ⟨i, _hi, hxi⟩
  by_cases hic : i = changed
  · subst i
    rcases Finset.mem_union.mp (hchanged hxi) with hxo | hxf
    · exact Finset.mem_union.mpr
        (Or.inl (Finset.mem_biUnion.mpr
          ⟨changed, Finset.mem_univ _, hxo⟩))
    · exact Finset.mem_union.mpr (Or.inr hxf)
  · exact Finset.mem_union.mpr
      (Or.inl (Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _, by simpa [hunchanged i hic] using hxi⟩))

end AppendixB1
end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
