import Lax214022.Cographs
import Lax48Proofs.Main
import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.Nat.Log

/-!
# Cotrees extracted from width-zero contraction sequences

The submitted definition of a cograph supplies a partition sequence.  This
file turns the merge history into the usual binary cotree.  The construction
is deliberately proof-side: cotrees are a convenient certificate, whereas
the concept defines cographs by the already endorsed twin-width notion.
-/

namespace Lax214022Proofs.Cotree

open Lax48.TwinWidth
open Lax48Proofs.Main

noncomputable section

/-- A binary cotree.  A `true` node joins its children and a `false` node
takes their disjoint union. -/
inductive Tree (V : Type) where
  | leaf : V → Tree V
  | node : Bool → Tree V → Tree V → Tree V

namespace Tree

variable {V : Type}

/-- The leaves, from left to right. -/
def leaves : Tree V → List V
  | leaf v => [v]
  | node _ l r => l.leaves ++ r.leaves

/-- The set of leaves. -/
def leafSet [DecidableEq V] (t : Tree V) : Finset V :=
  t.leaves.toFinset

/-- The number of leaves, counting multiplicity. -/
def leafCount : Tree V → ℕ
  | leaf _ => 1
  | node _ l r => l.leafCount + r.leafCount

/-- The Strahler rank: unequal-rank children inherit the larger rank, while
equal-rank children increase it by one. -/
def rank : Tree V → ℕ
  | leaf _ => 0
  | node _ l r =>
      if l.rank = r.rank then l.rank + 1 else max l.rank r.rank

@[simp] theorem leaves_leaf (v : V) : (leaf v).leaves = [v] := rfl

@[simp] theorem leaves_node (b : Bool) (l r : Tree V) :
    (node b l r).leaves = l.leaves ++ r.leaves := rfl

@[simp] theorem leafCount_leaf (v : V) : (leaf v).leafCount = 1 := rfl

@[simp] theorem leafCount_node (b : Bool) (l r : Tree V) :
    (node b l r).leafCount = l.leafCount + r.leafCount := rfl

@[simp] theorem length_leaves (t : Tree V) : t.leaves.length = t.leafCount := by
  induction t <;> simp_all [leaves, leafCount]

@[simp] theorem leafSet_leaf [DecidableEq V] (v : V) :
    (leaf v).leafSet = {v} := by
  simp [leafSet, leaves]

@[simp] theorem leafSet_node [DecidableEq V] (b : Bool) (l r : Tree V) :
    (node b l r).leafSet = l.leafSet ∪ r.leafSet := by
  simp [leafSet, leaves]

/-- A cotree represents a graph on its leaves when its two subtrees are
disjoint and every cross pair has the adjacency prescribed by the node. -/
def Represents (G : SimpleGraph V) [DecidableEq V] : Tree V → Prop
  | leaf _ => True
  | node joined l r =>
      Represents G l ∧ Represents G r ∧ Disjoint l.leafSet r.leafSet ∧
        if joined then CompleteBetween G l.leafSet r.leafSet
        else EmptyBetween G l.leafSet r.leafSet

theorem nodup_leaves_of_represents [DecidableEq V] {G : SimpleGraph V}
    {t : Tree V} (ht : t.Represents G) : t.leaves.Nodup := by
  induction t with
  | leaf v => simp [leaves]
  | node b l r ihl ihr =>
      simp only [Represents] at ht
      rw [leaves]
      apply List.Nodup.append (ihl ht.1) (ihr ht.2.1)
      rw [List.disjoint_left]
      intro x hxl hxr
      exact (Finset.disjoint_left.mp ht.2.2.1)
        (by simpa [leafSet] using hxl) (by simpa [leafSet] using hxr)

theorem leafCount_eq_card_leafSet [DecidableEq V] {G : SimpleGraph V}
    {t : Tree V} (ht : t.Represents G) : t.leafCount = t.leafSet.card := by
  rw [← length_leaves]
  exact (List.toFinset_card_of_nodup (nodup_leaves_of_represents ht)).symm

/-- A cotree of rank `r` has at least `2^r` leaves. -/
theorem pow_rank_le_leafCount (t : Tree V) : 2 ^ t.rank ≤ t.leafCount := by
  induction t with
  | leaf v => simp [rank, leafCount]
  | node b l r ihl ihr =>
      simp only [rank, leafCount]
      by_cases h : l.rank = r.rank
      · rw [if_pos h, Nat.pow_succ]
        rw [Nat.mul_two]
        exact Nat.add_le_add ihl (by simpa [h] using ihr)
      · rw [if_neg h]
        rcases lt_or_gt_of_ne h with hlt | hgt
        · rw [max_eq_right hlt.le]
          exact ihr.trans (Nat.le_add_left _ _)
        · rw [max_eq_left hgt.le]
          exact ihl.trans (Nat.le_add_right _ _)

theorem rank_le_clog_leafCount (t : Tree V) :
    t.rank ≤ Nat.clog 2 t.leafCount := by
  exact (Nat.le_log_of_pow_le Nat.one_lt_two (pow_rank_le_leafCount t)).trans
    (Nat.log_le_clog 2 t.leafCount)

end Tree

variable {V : Type} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V}

/-- Every current part has a representing cotree. -/
def PartsRepresented (G : SimpleGraph V) (P : Finset (Finset V)) : Prop :=
  ∀ A ∈ P, ∃ t : Tree V, t.leafSet = A ∧ t.Represents G

theorem partsRepresented_singletons :
    PartsRepresented G (singletonPartition V) := by
  intro A hA
  rcases Lax48Proofs.TwinWidth.TrigraphState.mem_singletonBags.mp hA with ⟨v, rfl⟩
  exact ⟨Tree.leaf v, by simp, by simp [Tree.Represents]⟩

/-- At width zero, every pair of distinct current parts is homogeneous. -/
theorem homogeneous_of_width_zero
    (S : PartitionSequence G 0) {i : ℕ} (hi : i ≤ S.stepCount)
    {A B : Finset V} (hA : A ∈ S.partition i) (hB : B ∈ S.partition i)
    (hAB : A ≠ B) : Homogeneous G A B := by
  by_contra hhom
  have hmem : B ∈ {C : Finset V |
      C ∈ S.partition i ∧ C ≠ A ∧ ¬ Homogeneous G A C} :=
    ⟨hB, hAB.symm, hhom⟩
  have hfinite : Set.Finite {C : Finset V |
      C ∈ S.partition i ∧ C ≠ A ∧ ¬ Homogeneous G A C} :=
    (S.partition i).finite_toSet.subset (fun _ h => h.1)
  have hpos : 0 < ({C : Finset V |
      C ∈ S.partition i ∧ C ≠ A ∧ ¬ Homogeneous G A C} : Set (Finset V)).ncard :=
    (Set.ncard_pos hfinite).2 ⟨B, hmem⟩
  have hzero : redDegree G (S.partition i) A = 0 :=
    Nat.eq_zero_of_le_zero (S.redDegree_le i hi hA)
  have : 0 < redDegree G (S.partition i) A := by
    simpa [redDegree] using hpos
  omega

omit [Fintype V] in
theorem partsRepresented_merge
    {P : Finset (Finset V)} (hP : IsPartitionFamily P)
    (hrep : PartsRepresented G P) {A B : Finset V}
    (hA : A ∈ P) (hB : B ∈ P) (hAB : A ≠ B)
    (hhom : Homogeneous G A B) :
    PartsRepresented G (insert (A ∪ B) ((P.erase A).erase B)) := by
  intro C hC
  rcases Finset.mem_insert.mp hC with hCeq | hCrest
  · subst C
    obtain ⟨l, hlset, hlrep⟩ := hrep A hA
    obtain ⟨r, hrset, hrrep⟩ := hrep B hB
    have hdisj : Disjoint l.leafSet r.leafSet := by
      rw [hlset, hrset]
      exact hP.2.1 hA hB hAB
    rcases hhom with hcomplete | hempty
    · refine ⟨Tree.node true l r, ?_, ?_⟩
      · simp [hlset, hrset]
      · simpa [Tree.Represents, hlset, hrset] using
          And.intro hlrep (And.intro hrrep (And.intro hdisj hcomplete))
    · refine ⟨Tree.node false l r, ?_, ?_⟩
      · simp [hlset, hrset]
      · simpa [Tree.Represents, hlset, hrset] using
          And.intro hlrep (And.intro hrrep (And.intro hdisj hempty))
  · have h1 := Finset.mem_erase.mp hCrest
    have h2 := Finset.mem_erase.mp h1.2
    exact hrep C h2.2

theorem partsRepresented_partition (S : PartitionSequence G 0) :
    ∀ i, i ≤ S.stepCount → PartsRepresented G (S.partition i) := by
  intro i
  induction i with
  | zero =>
      intro _
      simpa [S.starts] using (partsRepresented_singletons (G := G))
  | succ i ih =>
      intro hi
      have hlt : i < S.stepCount := by omega
      obtain ⟨A, hA, B, hB, hAB, hmerge⟩ := S.step_merges i hlt
      rw [hmerge]
      exact partsRepresented_merge
        (isPartitionFamily_partition S i (by omega)) (ih (by omega))
        hA hB hAB (homogeneous_of_width_zero S (by omega) hA hB hAB)

/-- A nonempty graph of twin-width zero has a binary cotree whose leaves are
exactly its vertices. -/
theorem exists_represents_of_hasTwinWidthAtMost_zero [Nonempty V]
    (hG : HasTwinWidthAtMost G 0) :
    ∃ t : Tree V, t.leafSet = Finset.univ ∧ t.Represents G := by
  obtain ⟨S⟩ := hG
  have hpart := isPartitionFamily_partition S S.stepCount le_rfl
  let v : V := Classical.choice (inferInstance : Nonempty V)
  obtain ⟨A, hA, hvA⟩ := hpart.2.2 v
  obtain ⟨t, htA, htrep⟩ :=
    partsRepresented_partition S S.stepCount le_rfl A hA
  refine ⟨t, ?_, htrep⟩
  rw [htA]
  apply Finset.eq_univ_of_forall
  intro x
  obtain ⟨B, hB, hxB⟩ := hpart.2.2 x
  have hBA : B = A := (Finset.card_le_one.mp S.ends) B hB A hA
  simpa [hBA] using hxB

end

end Lax214022Proofs.Cotree
