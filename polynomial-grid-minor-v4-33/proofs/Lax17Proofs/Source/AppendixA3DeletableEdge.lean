import Lax17Proofs.Source.EdgeMenger
import Lax17Proofs.Source.Section44

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy Section 7: deletable-edge preliminaries

This file contains bounded edge-Menger consequences used in the proof of
Chuzhoy's Section 7 Lemma 7.2.
-/

namespace SimpleGraph
namespace AppendixA3DeletableEdge


variable {V : Type u} [DecidableEq V] {G : _root_.SimpleGraph V}

/-- Edge-Menger wrapper for the first step of Chuzhoy, Section 7, Lemma 7.2.

The source chooses a minimum edge cut separating `T` from `Gamma`.  This
contrapositive form isolates the Menger step: if every such cut inside `C` has
at least `r` edges, then there are exactly `r` edge-disjoint `T`--`Gamma`
paths inside `C`. -/
theorem exists_exact_edgePathPacking_of_cut_lower_bound [Fintype V]
    {C T Gamma : Finset V} {r : ℕ}
    (hT : T ⊆ C) (hGamma : Gamma ⊆ C)
    (hdisjoint : Disjoint T Gamma)
    (hcut :
      ∀ X Y : Finset V,
        X ∪ Y = C →
          Disjoint X Y →
            T ⊆ X →
              Gamma ⊆ Y →
                r ≤ (EdgeMenger.edgeBoundary G X Y).card) :
    ∃ P : EdgePathPacking G T Gamma,
      P.card = r ∧ P.StaysIn C := by
  classical
  have hpaths : EdgeMenger.HasEdgeDisjointPathsIn G C T Gamma r := by
    by_contra hno
    rcases EdgeMenger.edge_menger_cut
        (G := G) (C := C) (A := T) (B := Gamma) (k := r)
        hT hGamma hdisjoint hno with
      ⟨cut⟩
    exact (Nat.not_lt_of_ge
      (hcut cut.X cut.Y cut.cover cut.disjoint
        cut.left_subset cut.right_subset)) cut.boundary_lt
  exact EdgeMenger.exists_exact_edgePathPacking_of_hasEdgeDisjointPathsIn hpaths

/-! ## The minimum set in Lemma 7.2 -/

/-- The three conditions imposed on the set `M` in the proof of Chuzhoy's
Lemma 7.2: `M` avoids the terminals, contains at least half of `Gamma`, and
has at most `gamma` edges leaving it in the ambient graph. -/
structure Lemma72SetConditions [Fintype V]
    (G : _root_.SimpleGraph V) (T Gamma : Finset V) (gamma : ℕ)
    (M : Finset V) : Prop where
  /-- No terminal lies in `M`. -/
  disjoint_terminals : Disjoint M T
  /-- At least half of `Gamma` lies in `M`, written without division. -/
  half_gamma : Gamma.card ≤ 2 * (M ∩ Gamma).card
  /-- At most `gamma` ambient edges have exactly one endpoint in `M`. -/
  boundary_card_le : (Section44.clusterBoundary G M).card ≤ gamma

/-- A set satisfying the three Lemma 7.2 conditions and having minimum
cardinality among every set satisfying those same conditions. -/
structure IsMinimumLemma72Set [Fintype V]
    (G : _root_.SimpleGraph V) (T Gamma : Finset V) (gamma : ℕ)
    (M : Finset V) : Prop extends Lemma72SetConditions G T Gamma gamma M where
  /-- The cardinality of `M` is no larger than that of any other candidate. -/
  card_minimal :
    ∀ ⦃N : Finset V⦄, Lemma72SetConditions G T Gamma gamma N → M.card ≤ N.card

/-- Chuzhoy's minimum set `M` exists whenever an explicit set `U` satisfies
the three required conditions.  The minimization is over candidate
cardinalities, so it assumes no minimum object in advance. -/
theorem exists_minimumLemma72Set [Fintype V]
    {T Gamma U : Finset V} {gamma : ℕ}
    (hU : Lemma72SetConditions G T Gamma gamma U) :
    ∃ M : Finset V, IsMinimumLemma72Set G T Gamma gamma M := by
  classical
  let HasCard : ℕ → Prop := fun n =>
    ∃ M : Finset V, Lemma72SetConditions G T Gamma gamma M ∧ M.card = n
  have hExists : ∃ n : ℕ, HasCard n :=
    ⟨U.card, U, hU, rfl⟩
  rcases Nat.find_spec hExists with ⟨M, hM, hMcard⟩
  refine ⟨M, hM, ?_⟩
  intro N hN
  have hNCard : HasCard N.card := ⟨N, hN, rfl⟩
  have hmin : Nat.find hExists ≤ N.card :=
    Nat.find_min' (H := hExists) hNCard
  simpa [hMcard] using hmin

/-- Raw witness form of `exists_minimumLemma72Set`, convenient at the point
where the separating set `U` is constructed in Lemma 7.2. -/
theorem exists_minimumLemma72Set_of_witness [Fintype V]
    {T Gamma U : Finset V} {gamma : ℕ}
    (hdisjoint : Disjoint U T)
    (hhalf : Gamma.card ≤ 2 * (U ∩ Gamma).card)
    (hboundary : (Section44.clusterBoundary G U).card ≤ gamma) :
    ∃ M : Finset V, IsMinimumLemma72Set G T Gamma gamma M :=
  exists_minimumLemma72Set
    (G := G) ⟨hdisjoint, hhalf, hboundary⟩

/-- The minimum-cut setup at the start of Chuzhoy's proof of Lemma 7.2.

If there are not `r` edge-disjoint `T`--`Gamma` paths, finite edge-Menger
gives a cut of size `gamma < r`.  Its `Gamma`-side is the source's set `U`:
it contains `Gamma`, avoids `T`, and its ambient boundary is exactly the
Menger cut boundary.  Therefore a minimum-cardinality Lemma 7.2 set exists. -/
theorem exists_minimumLemma72Set_of_not_hasEdgeDisjointPathsIn [Fintype V]
    {T Gamma : Finset V} {r : ℕ}
    (hdisjoint : Disjoint T Gamma)
    (hno :
      ¬ EdgeMenger.HasEdgeDisjointPathsIn
        G (Finset.univ : Finset V) T Gamma r) :
    ∃ gamma < r, ∃ M : Finset V,
      IsMinimumLemma72Set G T Gamma gamma M := by
  classical
  rcases EdgeMenger.edge_menger_cut
      (G := G) (C := (Finset.univ : Finset V))
      (A := T) (B := Gamma) (k := r)
      (by simp) (by simp) hdisjoint hno with
    ⟨cut⟩
  let gamma := (EdgeMenger.edgeBoundary G cut.X cut.Y).card
  have hcomplement : (Finset.univ : Finset V) \ cut.Y = cut.X := by
    calc
      (Finset.univ : Finset V) \ cut.Y =
          (cut.X ∪ cut.Y) \ cut.Y :=
        congrArg (fun S : Finset V => S \ cut.Y) cut.cover.symm
      _ = cut.X := Finset.union_sdiff_cancel_right cut.disjoint
  have hboundary :
      Section44.clusterBoundary G cut.Y =
        EdgeMenger.edgeBoundary G cut.X cut.Y := by
    calc
      Section44.clusterBoundary G cut.Y =
          Section44.edgeBoundary G cut.Y
            ((Finset.univ : Finset V) \ cut.Y) := rfl
      _ = Section44.edgeBoundary G cut.Y cut.X := by rw [hcomplement]
      _ = Section44.edgeBoundary G cut.X cut.Y :=
        Section44.edgeBoundary_comm (G := G) cut.Y cut.X
      _ = EdgeMenger.edgeBoundary G cut.X cut.Y :=
        Section44.edgeBoundary_eq_edgeMenger (G := G) cut.X cut.Y
  refine ⟨gamma, ?_, ?_⟩
  · simpa [gamma] using cut.boundary_lt
  · apply exists_minimumLemma72Set (G := G) (U := cut.Y)
    refine ⟨cut.disjoint.symm.mono_right cut.left_subset, ?_, ?_⟩
    · rw [Finset.inter_eq_right.mpr cut.right_subset]
      exact Nat.le_mul_of_pos_left Gamma.card (by norm_num)
    · simp [gamma, hboundary]

end AppendixA3DeletableEdge
end SimpleGraph

end Lax17Proofs
