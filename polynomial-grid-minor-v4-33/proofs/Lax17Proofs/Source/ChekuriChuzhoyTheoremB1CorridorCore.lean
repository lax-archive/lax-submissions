import Lax17Proofs.Source.ChekuriChuzhoyTheoremB1

namespace Lax17Proofs

universe u v w

/-!
# The degree-two corridor used in Chekuri--Chuzhoy Theorem B.1

This module isolates the graph-theoretic invariant behind Appendix B,
Theorem B.1.  A corridor consists of an ordered list of linkage paths, all of
whose auxiliary vertices have degree two, together with one fixed auxiliary
neighbour beyond each end.  Keeping the two outside neighbours is important:
it makes "the only corridor neighbours are the consecutive ones" true also at
the two boundary rows.

The structure is deliberately independent of the paper's type-one/type-two
index arithmetic.  Both branches will be converted to this common form.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy
namespace AppendixB1


variable {V : Type u} [DecidableEq V]
variable {G : _root_.SimpleGraph V} {A B : Finset V}

/-- An ordered degree-two corridor in the auxiliary graph of a linkage.

`activeRows` is the number of internal rows.  Positions `0` and
`activeRows + 1` are the two boundary rows. -/
structure AuxiliaryCorridor
    (M : PerfectPathPacking G A B) (activeRows : ℕ) where
  index : Fin (activeRows + 2) → M.Index
  index_injective : Function.Injective index
  degree_two :
    ∀ i : Fin (activeRows + 2),
      DegreeEquals (linkageAuxGraph M) (index i) 2
  consecutive_adj :
    ∀ i : Fin (activeRows + 1),
      (linkageAuxGraph M).Adj
        (index ⟨i.1, by omega⟩)
        (index ⟨i.1 + 1, by omega⟩)
  lowerOutside : M.Index
  upperOutside : M.Index
  lower_adj_outside :
    (linkageAuxGraph M).Adj (index ⟨0, by omega⟩) lowerOutside
  upper_adj_outside :
    (linkageAuxGraph M).Adj
      (index ⟨activeRows + 1, by omega⟩) upperOutside
  lowerOutside_ne_index : ∀ i, lowerOutside ≠ index i
  upperOutside_ne_index : ∀ i, upperOutside ≠ index i

namespace AuxiliaryCorridor

variable {M : PerfectPathPacking G A B} {activeRows : ℕ}

/-- The linkage path occupying a displayed corridor position. -/
def path (C : AuxiliaryCorridor M activeRows)
    (i : Fin (activeRows + 2)) : GraphPath G :=
  M.path (C.index i)

/-- Embed an active-row index between the two boundary positions. -/
def activePosition (_C : AuxiliaryCorridor M activeRows)
    (i : Fin activeRows) : Fin (activeRows + 2) :=
  ⟨i.1 + 1, by omega⟩

/-- The path occupying an active row of the corridor. -/
def activePath (C : AuxiliaryCorridor M activeRows)
    (i : Fin activeRows) : GraphPath G :=
  C.path (C.activePosition i)

/-- The union of the active-row vertex sets. -/
noncomputable def activeVertexSet
    (C : AuxiliaryCorridor M activeRows) : Finset V :=
  Finset.univ.biUnion fun i : Fin activeRows => (C.activePath i).vertexSet

/-- The union of the active-row edge sets. -/
noncomputable def activeEdgeSet
    (C : AuxiliaryCorridor M activeRows) : Finset (Sym2 V) :=
  Finset.univ.biUnion fun i : Fin activeRows => (C.activePath i).edgeSet

/-- Distinct displayed corridor paths are vertex-disjoint because they are
distinct members of the linkage. -/
theorem path_nodeDisjoint
    (C : AuxiliaryCorridor M activeRows)
    {i j : Fin (activeRows + 2)} (hij : i ≠ j) :
    (C.path i).NodeDisjoint (C.path j) := by
  exact M.toPathPacking.node_disjoint
    (fun h => hij (C.index_injective h))

/-- Every active-row path lies in the active-row vertex union. -/
theorem activePath_vertexSet_subset
    (C : AuxiliaryCorridor M activeRows) (i : Fin activeRows) :
    (C.activePath i).vertexSet ⊆ C.activeVertexSet := by
  classical
  intro v hv
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, hv⟩

/-- Consecutive corridor positions are adjacent in the linkage auxiliary
graph. -/
theorem adj_of_consecutive
    (C : AuxiliaryCorridor M activeRows)
    {i j : Fin (activeRows + 2)}
    (hij : FinConsecutive i j) :
    (linkageAuxGraph M).Adj (C.index i) (C.index j) := by
  rcases hij with hij | hij
  · have hi : i.1 < activeRows + 1 := by omega
    have h := C.consecutive_adj (⟨i.1, hi⟩ : Fin (activeRows + 1))
    have hj :
        (⟨i.1 + 1, by omega⟩ : Fin (activeRows + 2)) = j := by
      apply Fin.ext
      exact hij
    simpa [hj] using h
  · have hj : j.1 < activeRows + 1 := by omega
    have h := C.consecutive_adj (⟨j.1, hj⟩ : Fin (activeRows + 1))
    have hi :
        (⟨j.1 + 1, by omega⟩ : Fin (activeRows + 2)) = i := by
      apply Fin.ext
      exact hij
    simpa [hi] using h.symm

/-- The lower boundary has no corridor neighbour except the first active
row. -/
theorem lower_neighbor_eq_first
    (C : AuxiliaryCorridor M activeRows)
    {j : Fin (activeRows + 2)}
    (hadj :
      (linkageAuxGraph M).Adj (C.index ⟨0, by omega⟩) (C.index j)) :
    j = ⟨1, by omega⟩ := by
  have hfirst :
      (linkageAuxGraph M).Adj
        (C.index ⟨0, by omega⟩) (C.index ⟨1, by omega⟩) :=
    C.adj_of_consecutive (Or.inl rfl)
  have hne : C.index ⟨1, by omega⟩ ≠ C.lowerOutside := by
    intro h
    exact C.lowerOutside_ne_index ⟨1, by omega⟩ h.symm
  rcases DegreeEquals.two_adj_eq_or_eq
      (C.degree_two ⟨0, by omega⟩)
      hfirst C.lower_adj_outside hne hadj with h | h
  · exact C.index_injective h
  · exact False.elim (C.lowerOutside_ne_index j h.symm)

/-- The upper boundary has no corridor neighbour except the last active
row. -/
theorem upper_neighbor_eq_last
    (C : AuxiliaryCorridor M activeRows)
    {j : Fin (activeRows + 2)}
    (hadj :
      (linkageAuxGraph M).Adj
        (C.index ⟨activeRows + 1, by omega⟩) (C.index j)) :
    j = ⟨activeRows, by omega⟩ := by
  have hlast :
      (linkageAuxGraph M).Adj
        (C.index ⟨activeRows + 1, by omega⟩)
        (C.index ⟨activeRows, by omega⟩) :=
    C.adj_of_consecutive (Or.inr rfl)
  have hne : C.index ⟨activeRows, by omega⟩ ≠ C.upperOutside := by
    intro h
    exact C.upperOutside_ne_index ⟨activeRows, by omega⟩ h.symm
  rcases DegreeEquals.two_adj_eq_or_eq
      (C.degree_two ⟨activeRows + 1, by omega⟩)
      hlast C.upper_adj_outside hne hadj with h | h
  · exact C.index_injective h
  · exact False.elim (C.upperOutside_ne_index j h.symm)

/-- An internal corridor vertex has exactly its predecessor and successor as
corridor neighbours. -/
theorem interior_neighbor_eq_prev_or_next
    (C : AuxiliaryCorridor M activeRows)
    {i j : Fin (activeRows + 2)}
    (hi0 : 0 < i.1) (hilast : i.1 < activeRows + 1)
    (hadj : (linkageAuxGraph M).Adj (C.index i) (C.index j)) :
    j = ⟨i.1 - 1, by omega⟩ ∨ j = ⟨i.1 + 1, by omega⟩ := by
  let prev : Fin (activeRows + 2) := ⟨i.1 - 1, by omega⟩
  let next : Fin (activeRows + 2) := ⟨i.1 + 1, by omega⟩
  have hprevCon : FinConsecutive i prev := by
    right
    dsimp [prev]
    omega
  have hnextCon : FinConsecutive i next := by
    left
    rfl
  have hprev :
      (linkageAuxGraph M).Adj (C.index i) (C.index prev) :=
    C.adj_of_consecutive hprevCon
  have hnext :
      (linkageAuxGraph M).Adj (C.index i) (C.index next) :=
    C.adj_of_consecutive hnextCon
  have hpne : C.index prev ≠ C.index next := by
    intro h
    have := C.index_injective h
    have := congrArg Fin.val this
    dsimp [prev, next] at this
    omega
  rcases DegreeEquals.two_adj_eq_or_eq
      (C.degree_two i) hprev hnext hpne hadj with h | h
  · exact Or.inl (C.index_injective h)
  · exact Or.inr (C.index_injective h)

/-- Inside the displayed corridor, auxiliary adjacency is exactly
consecutiveness of the displayed positions. -/
theorem adj_iff_consecutive
    (C : AuxiliaryCorridor M activeRows)
    {i j : Fin (activeRows + 2)} :
    (linkageAuxGraph M).Adj (C.index i) (C.index j) ↔
      FinConsecutive i j := by
  constructor
  · intro hadj
    by_cases hi0 : i.1 = 0
    · have hi : i = ⟨0, by omega⟩ := by
        apply Fin.ext
        exact hi0
      have hj : j = ⟨1, by omega⟩ :=
        C.lower_neighbor_eq_first (by simpa [hi] using hadj)
      rw [hi, hj]
      exact Or.inl rfl
    · by_cases hilast : i.1 = activeRows + 1
      · have hi : i = ⟨activeRows + 1, by omega⟩ := by
          apply Fin.ext
          exact hilast
        have hj : j = ⟨activeRows, by omega⟩ :=
          C.upper_neighbor_eq_last (by simpa [hi] using hadj)
        rw [hi, hj]
        exact Or.inr rfl
      · have hi0' : 0 < i.1 := by omega
        have hilast' : i.1 < activeRows + 1 := by
          have hi := i.2
          omega
        rcases C.interior_neighbor_eq_prev_or_next hi0' hilast' hadj with
          hj | hj
        · right
          have hjval := congrArg Fin.val hj
          simp only [Fin.val_mk] at hjval
          omega
        · left
          have hjval := congrArg Fin.val hj
          simp only [Fin.val_mk] at hjval
          omega
  · exact C.adj_of_consecutive

/-- Transport a corridor across an isomorphism of linkage auxiliary graphs.
The row paths themselves may have been rerouted; this construction transports
only their ordered auxiliary labels and the two outside neighbours. -/
noncomputable def transport
    {M' : PerfectPathPacking G A B}
    (C : AuxiliaryCorridor M activeRows)
    (e : M.Index ≃ M'.Index)
    (hadj :
      ∀ i j : M.Index,
        (linkageAuxGraph M).Adj i j ↔
          (linkageAuxGraph M').Adj (e i) (e j)) :
    AuxiliaryCorridor M' activeRows where
  index i := e (C.index i)
  index_injective := e.injective.comp C.index_injective
  degree_two := by
    intro i
    exact
      (IndexedAuxiliaryPrefix.degreeEquals_equiv_iff e hadj).1
        (C.degree_two i)
  consecutive_adj := by
    intro i
    exact (hadj _ _).1 (C.consecutive_adj i)
  lowerOutside := e C.lowerOutside
  upperOutside := e C.upperOutside
  lower_adj_outside := (hadj _ _).1 C.lower_adj_outside
  upper_adj_outside := (hadj _ _).1 C.upper_adj_outside
  lowerOutside_ne_index := by
    intro i heq
    exact C.lowerOutside_ne_index i (e.injective heq)
  upperOutside_ne_index := by
    intro i heq
    exact C.upperOutside_ne_index i (e.injective heq)

/-- The transported corridor has the transported row index at every
position. -/
@[simp] theorem transport_index
    {M' : PerfectPathPacking G A B}
    (C : AuxiliaryCorridor M activeRows)
    (e : M.Index ≃ M'.Index)
    (hadj :
      ∀ i j : M.Index,
        (linkageAuxGraph M).Adj i j ↔
          (linkageAuxGraph M').Adj (e i) (e j))
    (i : Fin (activeRows + 2)) :
    (C.transport e hadj).index i = e (C.index i) :=
  rfl

end AuxiliaryCorridor

/-! ## The two initial corridors from the displayed `8h` two-path -/

/-- The type-one corridor `P₀,P₁,...,P_z,P_{z+1}` with one auxiliary
neighbour retained beyond each boundary. -/
noncomputable def IndexedAuxiliaryPrefix.typeOneAuxiliaryCorridor
    {L : PerfectPathPacking G A B} {h : ℕ}
    (R : IndexedAuxiliaryPrefix L h) (hpos : 0 < h) :
    AuxiliaryCorridor L (z h) where
  index i := R.indexAt i.1 (by
    have hi := i.2
    dsimp [z] at hi ⊢
    omega)
  index_injective := by
    intro i j hij
    apply Fin.ext
    exact (R.indexAt_eq_indexAt_iff _ _).1 hij
  degree_two := by
    intro i
    simpa [IndexedAuxiliaryPrefix.indexAt,
      IndexedAuxiliaryPrefix.posOfNat] using
      R.degree_two
        (R.posOfNat i.1 (by
          have hi := i.2
          dsimp [z] at hi ⊢
          omega))
  consecutive_adj := by
    intro i
    simpa using
      R.adj_indexAt_succ (k := i.1) (by
        have hi := i.2
        dsimp [z] at hi ⊢
        omega)
  lowerOutside := R.p0OutsideIndex hpos
  upperOutside := R.indexAt (z h + 2) (by
    dsimp [z]
    omega)
  lower_adj_outside := by
    simpa [IndexedAuxiliaryPrefix.p0Index,
      IndexedAuxiliaryPrefix.indexAt,
      IndexedAuxiliaryPrefix.posOfNat, p0Pos] using
      R.p0_adj_outsideIndex hpos
  upper_adj_outside := by
    have h :=
      R.adj_indexAt_succ (k := z h + 1) (by
        dsimp [z]
        omega)
    simpa using h
  lowerOutside_ne_index := by
    intro i
    by_cases hi0 : i.1 = 0
    · intro heq
      have hloop :
          (linkageAuxGraph L).Adj
            (R.indexAt i.1 (by
              have hi := i.2
              dsimp [z] at hi ⊢
              omega))
            (R.indexAt i.1 (by
              have hi := i.2
              dsimp [z] at hi ⊢
              omega)) := by
        have hadj := R.p0_adj_outsideIndex hpos
        rw [heq] at hadj
        simpa [hi0, IndexedAuxiliaryPrefix.p0Index,
          IndexedAuxiliaryPrefix.indexAt,
          IndexedAuxiliaryPrefix.posOfNat, p0Pos] using hadj
      exact (linkageAuxGraph L).loopless.irrefl _ hloop
    · exact R.p0OutsideIndex_ne_indexAt hpos
        (k := i.1)
        (by omega)
        (by
          have hi := i.2
          dsimp [z] at hi ⊢
          omega)
  upperOutside_ne_index := by
    intro i hidx
    have hval :=
      (R.indexAt_eq_indexAt_iff
        (a := z h + 2) (b := i.1) (by
          dsimp [z]
          omega) (by
          have hi := i.2
          dsimp [z] at hi ⊢
          omega)).1 hidx
    have hi := i.2
    omega

/-- The symmetric type-two corridor
`P_{2z},P_{2z+1},...,P_{3z},P_{3z+1}` with one auxiliary neighbour retained
beyond each boundary. -/
noncomputable def IndexedAuxiliaryPrefix.typeTwoAuxiliaryCorridor
    {L : PerfectPathPacking G A B} {h : ℕ}
    (R : IndexedAuxiliaryPrefix L h) (hpos : 0 < h) :
    AuxiliaryCorridor L (z h) where
  index i := R.indexAt (2 * z h + i.1) (by
    have hi := i.2
    dsimp [z] at hi ⊢
    omega)
  index_injective := by
    intro i j hij
    apply Fin.ext
    have hval := (R.indexAt_eq_indexAt_iff _ _).1 hij
    omega
  degree_two := by
    intro i
    simpa [IndexedAuxiliaryPrefix.indexAt,
      IndexedAuxiliaryPrefix.posOfNat] using
      R.degree_two
        (R.posOfNat (2 * z h + i.1) (by
          have hi := i.2
          dsimp [z] at hi ⊢
          omega))
  consecutive_adj := by
    intro i
    have h :=
      R.adj_indexAt_succ (k := 2 * z h + i.1) (by
        have hi := i.2
        dsimp [z] at hi ⊢
        omega)
    simpa [Nat.add_assoc] using h
  lowerOutside := R.indexAt (2 * z h - 1) (by
    dsimp [z]
    omega)
  upperOutside := R.indexAt (3 * z h + 2) (by
    dsimp [z]
    omega)
  lower_adj_outside := by
    have hadj :=
      R.adj_indexAt_succ (k := 2 * z h - 1) (by
        dsimp [z]
        omega)
    have heq : 2 * z h - 1 + 1 = 2 * z h := by
      dsimp [z]
      omega
    simpa [heq] using hadj.symm
  upper_adj_outside := by
    have hadj :=
      R.adj_indexAt_succ (k := 3 * z h + 1) (by
        dsimp [z]
        omega)
    have heq : 2 * z h + (z h + 1) = 3 * z h + 1 := by
      omega
    simpa [heq] using hadj
  lowerOutside_ne_index := by
    intro i hidx
    have hval :=
      (R.indexAt_eq_indexAt_iff
        (a := 2 * z h - 1) (b := 2 * z h + i.1)
        (by dsimp [z]; omega)
        (by
          have hi := i.2
          dsimp [z] at hi ⊢
          omega)).1 hidx
    dsimp [z] at hval
    omega
  upperOutside_ne_index := by
    intro i hidx
    have hval :=
      (R.indexAt_eq_indexAt_iff
        (a := 3 * z h + 2) (b := 2 * z h + i.1)
        (by dsimp [z]; omega)
        (by
          have hi := i.2
          dsimp [z] at hi ⊢
          omega)).1 hidx
    have hi := i.2
    dsimp [z] at hval hi
    omega

end AppendixB1
end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
