import Lax185574Proofs.Conversions.Ram.Reach
import Lax185574Proofs.Conversions.Ram.Walk5
import Lax185574Proofs.Words.FinsetRead
import Lax185574Proofs.Conversions.BetterMergeFunction
import Lax185574Proofs.Conversions.MergeConstructionDefs

/-!
The relations the programs compute, against the definitions.

The programs work with vertices as numbers below `n`. This module
translates the partition into atomic types, its split along the least
vertices of the parts, and the pair relation into the relations `RAtom`,
`RSplit` and `Reach5` that the commands of the conversions compute.
-/

namespace Lax185574Proofs.Conversions.Ram

open Lax185574.Partitions Lax185574.TypeSplitting Lax185574.SplittingMonotone
open Lax185574.PairRelation Lax185574.BipartiteGraphs Lax185574.GaifmanGraph
open Lax185574Proofs.Words Lax185574Proofs.Conversions.MergeConstruction

variable {n : ℕ}

/-- Adjacency of a graph on `Fin n`, on numbers. -/
def gA (G : SimpleGraph (Fin n)) (u v : ℕ) : Prop := ∃ (hu : u < n) (hv : v < n), G.Adj ⟨u, hu⟩ ⟨v, hv⟩

theorem gA_fin (G : SimpleGraph (Fin n)) (u v : Fin n) : gA G u v ↔ G.Adj u v :=
  ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨u.2, v.2, h⟩⟩

/-- The least vertex of the part of a number below `n`, and `0` above. -/
noncomputable def repN (P : Setoid (Fin n)) (z : ℕ) : ℕ := if h : z < n then (rep P ⟨z, h⟩ : ℕ) else 0

theorem repN_fin (P : Setoid (Fin n)) (z : Fin n) : repN P z = rep P z := by simp [repN]

theorem repN_lt (P : Setoid (Fin n)) {z : ℕ} (hz : z < n) : repN P z < n := by
  simp [repN, hz]

theorem repN_eq_iff (P : Setoid (Fin n)) (u v : Fin n) : repN P u = repN P v ↔ P u v := by
  rw [repN_fin, repN_fin, Fin.val_inj, rep_eq_iff]

/-- The labels computed by `classify` are the least vertices of the parts. -/
theorem leastBelow_eq_repN (P : Setoid (Fin n)) (R : ℕ → ℕ → Prop)
    (hR : ∀ u v (hu : u < n) (hv : v < n), R u v ↔ P ⟨u, hu⟩ ⟨v, hv⟩) {v : ℕ} (hv : v < n) :
    leastBelow (fun u => R u v) n n = repN P v := by
  have hex : ∃ u, u < n ∧ R u v := ⟨v, hv, (hR v v hv hv).mpr (P.refl _)⟩
  obtain ⟨h1, h2, h3⟩ := leastBelow_spec (d := n) hex
  set w := leastBelow (fun u => R u v) n n
  have hw : P ⟨w, h1⟩ ⟨v, hv⟩ := (hR w v h1 hv).mp h2
  rw [repN, dif_pos hv]
  apply le_antisymm
  · by_contra hc
    exact h3 _ (by omega) ((hR _ v (rep P ⟨v, hv⟩).2 hv).mpr (rep_rel P _))
  · exact rep_le P hw

theorem atomic_iff (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) (u v : Fin n) :
    atomicTypes G (X : Set (Fin n)) u v ↔ RAtom n (· ∈ sortedVals X) (gA G) u v := by
  have hX : ∀ z : Fin n, (z : ℕ) ∈ sortedVals X ↔ z ∈ X := fun z => by
    rw [mem_sortedVals]; exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨z.2, h⟩⟩
  change ((X : Set (Fin n)) ∩ {u}, (X : Set (Fin n)) ∩ G.neighborSet u) =
    ((X : Set (Fin n)) ∩ {v}, (X : Set (Fin n)) ∩ G.neighborSet v) ↔ _
  rw [Prod.mk.injEq, RAtom, hX, hX, Fin.val_inj]
  constructor
  · rintro ⟨h1, h2⟩
    by_cases huv : u = v
    · exact Or.inl huv
    right
    have hu : u ∉ X := fun hu => huv (by
      have : u ∈ (X : Set (Fin n)) ∩ {v} := h1 ▸ ⟨hu, rfl⟩
      exact this.2)
    have hv : v ∉ X := fun hv => huv (by
      have : v ∈ (X : Set (Fin n)) ∩ {u} := h1.symm ▸ ⟨hv, rfl⟩
      exact this.2.symm)
    refine ⟨hu, hv, fun z hz hzX => ?_⟩
    have hzX' : (⟨z, hz⟩ : Fin n) ∈ X := (hX ⟨z, hz⟩).mp hzX
    have := Set.ext_iff.mp h2 ⟨z, hz⟩
    simp only [Set.mem_inter_iff, Finset.mem_coe, SimpleGraph.mem_neighborSet] at this
    rw [show gA G u z ↔ G.Adj u ⟨z, hz⟩ from gA_fin G u ⟨z, hz⟩,
      show gA G v z ↔ G.Adj v ⟨z, hz⟩ from gA_fin G v ⟨z, hz⟩]
    exact ⟨fun h => (this.mp ⟨hzX', h⟩).2, fun h => (this.mpr ⟨hzX', h⟩).2⟩
  · rintro (rfl | ⟨hu, hv, h⟩)
    · exact ⟨rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · ext z
      simp only [Set.mem_inter_iff, Finset.mem_coe, Set.mem_singleton_iff]
      constructor
      · rintro ⟨hz, rfl⟩; exact absurd hz hu
      · rintro ⟨hz, rfl⟩; exact absurd hz hv
    · ext z
      simp only [Set.mem_inter_iff, Finset.mem_coe, SimpleGraph.mem_neighborSet]
      constructor
      · rintro ⟨hz, ha⟩
        exact ⟨hz, (gA_fin G v z).mp ((h z z.2 ((hX z).mpr hz)).mp ((gA_fin G u z).mpr ha))⟩
      · rintro ⟨hz, ha⟩
        exact ⟨hz, (gA_fin G u z).mp ((h z z.2 ((hX z).mpr hz)).mpr ((gA_fin G v z).mpr ha))⟩

theorem minimal_iff (P : Setoid (Fin n)) (z : Fin n) : z ∈ minimalVertices P ↔ rep P z = z := by
  constructor
  · intro h
    exact le_antisymm (rep_le P (P.refl z)) (h _ (rep_rel P z))
  · intro h w hw
    rw [← h]; exact rep_le P hw

theorem split_iff' (G : SimpleGraph (Fin n)) (P : Setoid (Fin n)) (u v : Fin n) :
    split G P (minimalVertices P) u v ↔ RSplit n (repN P) (gA G) u v := by
  rw [BetterMerge.split_iff, RSplit, repN_eq_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h z hz hmin hne
    have hmin' : rep P ⟨z, hz⟩ = ⟨z, hz⟩ := by
      apply Fin.ext; simpa [repN, hz] using hmin
    have hz' : (⟨z, hz⟩ : Fin n) ∈ minimalVertices P := (minimal_iff P _).mpr hmin'
    have hnP : ¬ P ⟨z, hz⟩ u := fun hp => hne (by
      have := (repN_eq_iff P ⟨z, hz⟩ u).mpr hp; simpa using this)
    rw [show gA G u z ↔ G.Adj u ⟨z, hz⟩ from gA_fin G u ⟨z, hz⟩,
      show gA G v z ↔ G.Adj v ⟨z, hz⟩ from gA_fin G v ⟨z, hz⟩]
    exact h _ hz' hnP
  · intro h z hz hnP
    have hmin := (minimal_iff P z).mp hz
    have := h z z.2 (by rw [repN_fin, hmin]) (fun he => hnP ((repN_eq_iff P z u).mp he))
    rwa [gA_fin, gA_fin] at this

theorem within5_iff (P : Setoid (Fin n)) (Eg : Fin n → Fin n → Prop) (EN : ℕ → ℕ → Prop)
    (hE : ∀ a b : Fin n, EN a b ↔ Eg a b) (u v : Fin n) :
    WithinDist (bipartiteGraph fun a b => a ∈ part P u ∧ b ∈ part P v ∧ Eg a b) 5
      (.inl u) (.inr v) ↔ Reach5 n (repN P) EN u v := by
  have hp : ∀ a w : Fin n, a ∈ part P w ↔ repN P a = repN P w := fun a w => by
    rw [repN_eq_iff]; rfl
  rw [Ram.withinDist5_iff]
  simp only [Reach5, RStep, LStep]
  constructor
  · rintro ⟨b1, a2, b3, a4, ⟨-, hb1, e1⟩, ⟨ha2, -, e2⟩, ⟨-, hb3, e3⟩, ⟨ha4, -, e4⟩, ⟨-, -, e5⟩⟩
    rw [hp] at hb1 hb3 ha2 ha4
    refine ⟨a4, a4.2, ha4, ⟨ha4, b3, b3.2, hb3, ⟨a2, a2.2, ha2, ⟨ha2, b1, b1.2, ?_, (hE _ _).mpr e1,
      (hE _ _).mpr e2⟩, (hE _ _).mpr e3⟩, (hE _ _).mpr e4⟩, (hE _ _).mpr e5⟩
    rw [hb1, hb3]
  · rintro ⟨a4, ha4n, ha4, ⟨-, b3, hb3n, hb3, ⟨a2, ha2n, ha2, ⟨-, b1, hb1n, hb1, e1, e2⟩, e3⟩, e4⟩, e5⟩
    refine ⟨⟨b1, hb1n⟩, ⟨a2, ha2n⟩, ⟨b3, hb3n⟩, ⟨a4, ha4n⟩, ⟨P.refl _, ?_, (hE _ _).mp e1⟩,
      ⟨?_, ?_, (hE _ _).mp e2⟩, ⟨?_, ?_, (hE _ _).mp e3⟩, ⟨?_, ?_, (hE _ _).mp e4⟩,
      ⟨?_, P.refl _, (hE _ _).mp e5⟩⟩
    all_goals (rw [hp]; simp only; omega)

/-- The edge relations of the two polarities: equal, or adjacent in `G`
(`pol = true`) or non-adjacent (`pol = false`). -/
def EPol (G : SimpleGraph (Fin n)) (pol : Bool) (a b : ℕ) : Prop := a = b ∨ (gA G a b ↔ pol = true)

/-- **The pair relation, as the program computes it.** -/
theorem pairRelation_iff (G : SimpleGraph (Fin n)) (P : Setoid (Fin n)) (u v : Fin n) :
    (pairRelation G P).Adj u v ↔ u ≠ v ∧
      ((Reach5 n (repN P) (EPol G true) u v ∧ Reach5 n (repN P) (EPol G false) u v) ∨
        (Reach5 n (repN P) (EPol G true) v u ∧ Reach5 n (repN P) (EPol G false) v u)) := by
  have h1 : ∀ x y : Fin n, WithinDist (pairGraph G (part P x) (part P y)) 5 (.inl x) (.inr y) ↔
      Reach5 n (repN P) (EPol G true) x y := fun x y =>
    within5_iff P (fun a b => a = b ∨ G.Adj a b) _ (fun a b => by
      simp [EPol, gA_fin, Fin.val_inj]) x y
  have h2 : ∀ x y : Fin n, WithinDist (coPairGraph G (part P x) (part P y)) 5 (.inl x) (.inr y) ↔
      Reach5 n (repN P) (EPol G false) x y := fun x y =>
    within5_iff P (fun a b => a = b ∨ ¬ G.Adj a b) _ (fun a b => by
      simp [EPol, gA_fin, Fin.val_inj]) x y
  simp only [pairRelation, SimpleGraph.fromRel_adj, h1, h2]

end Lax185574Proofs.Conversions.Ram
