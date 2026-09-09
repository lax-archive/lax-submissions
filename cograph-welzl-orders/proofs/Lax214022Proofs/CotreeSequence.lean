import Lax214022Proofs.Cotree

/-!
# Cotrees give width-zero contraction sequences

This is the converse to the extraction result in Cotree. A frontier of a
cotree is obtained by stopping independently in its two children. Its blocks
are therefore leaf sets of pairwise incomparable subtrees. Such blocks are
pairwise homogeneous, and unless only the root block remains, two sibling
frontier blocks can be merged.
-/

namespace Lax214022Proofs.CotreeSequence

open Lax48.TwinWidth
open Lax48Proofs.Main
open Lax214022Proofs.Cotree

noncomputable section

variable {V : Type} [DecidableEq V]

namespace Tree

/-- A family of blocks obtained by cutting a cotree at an antichain. -/
inductive Frontier : Tree V → Finset (Finset V) → Prop
  | whole (t : Tree V) : Frontier t {t.leafSet}
  | split {b : Bool} {l r : Tree V} {P Q : Finset (Finset V)} :
      Frontier l P → Frontier r Q → Frontier (Tree.node b l r) (P ∪ Q)

namespace Frontier

variable {G : SimpleGraph V} {t : Tree V} {P : Finset (Finset V)}

theorem leafSet_nonempty (t : Tree V) : t.leafSet.Nonempty := by
  induction t with
  | leaf v => exact ⟨v, by simp⟩
  | node b l r ihl ihr =>
      exact ⟨Classical.choose ihl, by
        simp only [Tree.leafSet_node, Finset.mem_union]
        exact Or.inl (Classical.choose_spec ihl)⟩

theorem block_nonempty (h : Frontier t P) {A : Finset V} (hA : A ∈ P) :
    A.Nonempty := by
  induction h with
  | whole t =>
      rw [Finset.mem_singleton] at hA
      subst A
      exact leafSet_nonempty t
  | @split b l r PL PR hL hR ihL ihR =>
      rcases Finset.mem_union.mp hA with hA | hA
      · exact ihL hA
      · exact ihR hA

theorem block_subset (h : Frontier t P) {A : Finset V} (hA : A ∈ P) :
    A ⊆ t.leafSet := by
  induction h with
  | whole t =>
      rw [Finset.mem_singleton] at hA
      simp [hA]
  | @split b l r PL PR hL hR ihL ihR =>
      rcases Finset.mem_union.mp hA with hA | hA
      · exact (ihL hA).trans (by intro x hx; simp [hx])
      · exact (ihR hA).trans (by intro x hx; simp [hx])

theorem covers (h : Frontier t P) : ∀ v, v ∈ t.leafSet → ∃ A ∈ P, v ∈ A := by
  induction h with
  | whole t =>
      intro v hv
      exact ⟨t.leafSet, Finset.mem_singleton_self _, hv⟩
  | @split b l r PL PR hL hR ihL ihR =>
      intro v hv
      rcases Finset.mem_union.mp (by simpa using hv) with hv | hv
      · obtain ⟨A, hA, hvA⟩ := ihL v hv
        exact ⟨A, Finset.mem_union_left _ hA, hvA⟩
      · obtain ⟨A, hA, hvA⟩ := ihR v hv
        exact ⟨A, Finset.mem_union_right _ hA, hvA⟩

theorem disjoint_blocks (h : Frontier t P) (ht : t.Represents G)
    {A B : Finset V} (hA : A ∈ P) (hB : B ∈ P) (hAB : A ≠ B) :
    Disjoint A B := by
  induction h generalizing A B with
  | whole t =>
      rw [Finset.mem_singleton] at hA hB
      exact (hAB (hA.trans hB.symm)).elim
  | @split b l r PL PR hL hR ihL ihR =>
      simp only [Tree.Represents] at ht
      rcases Finset.mem_union.mp hA with hAPL | hAPR <;>
        rcases Finset.mem_union.mp hB with hBPL | hBPR
      · exact ihL ht.1 hAPL hBPL hAB
      · exact ht.2.2.1.mono (hL.block_subset hAPL) (hR.block_subset hBPR)
      · exact ht.2.2.1.symm.mono (hR.block_subset hAPR) (hL.block_subset hBPL)
      · exact ihR ht.2.1 hAPR hBPR hAB

theorem homogeneous_blocks (h : Frontier t P) (ht : t.Represents G)
    {A B : Finset V} (hA : A ∈ P) (hB : B ∈ P) (hAB : A ≠ B) :
    Homogeneous G A B := by
  induction h generalizing A B with
  | whole t =>
      rw [Finset.mem_singleton] at hA hB
      exact (hAB (hA.trans hB.symm)).elim
  | @split b l r PL PR hL hR ihL ihR =>
      simp only [Tree.Represents] at ht
      rcases Finset.mem_union.mp hA with hAPL | hAPR <;>
        rcases Finset.mem_union.mp hB with hBPL | hBPR
      · exact ihL ht.1 hAPL hBPL hAB
      · split at ht
        · left
          intro a ha b hb
          exact ht.2.2.2 a (hL.block_subset hAPL ha) b (hR.block_subset hBPR hb)
        · right
          intro a ha b hb
          exact ht.2.2.2 a (hL.block_subset hAPL ha) b (hR.block_subset hBPR hb)
      · split at ht
        · left
          intro a ha b hb
          exact (ht.2.2.2 b (hL.block_subset hBPL hb)
            a (hR.block_subset hAPR ha)).symm
        · right
          intro a ha b hb hab
          exact ht.2.2.2 b (hL.block_subset hBPL hb)
            a (hR.block_subset hAPR ha) hab.symm
      · exact ihR ht.2.1 hAPR hBPR hAB

theorem isPartitionFamily [Fintype V] (h : Frontier t P) (ht : t.Represents G)
    (hroot : t.leafSet = Finset.univ) : IsPartitionFamily P := by
  refine ⟨(fun _ hA => h.block_nonempty hA),
    (fun {_ _} hA hB hAB => h.disjoint_blocks ht hA hB hAB), ?_⟩
  intro v
  apply h.covers v
  simp [hroot]

/-- The singleton leaf blocks form a frontier. -/
theorem singletons (t : Tree V) :
    Frontier t (t.leafSet.image fun v => ({v} : Finset V)) := by
  induction t with
  | leaf v => simpa using Frontier.whole (Tree.leaf v)
  | node b l r ihl ihr =>
      simpa [Finset.image_union] using Frontier.split ihl ihr

theorem singletons_eq_singletonPartition [Fintype V] {t : Tree V}
    (hroot : t.leafSet = Finset.univ) :
    t.leafSet.image (fun v => ({v} : Finset V)) = singletonPartition V := by
  simp [singletonPartition, hroot]

/-- Merge two members of a finite block family. -/
def merge (P : Finset (Finset V)) (A B : Finset V) : Finset (Finset V) :=
  insert (A ∪ B) ((P.erase A).erase B)

private theorem mem_other_of_disjoint_roots {l r : Tree V}
    {P Q : Finset (Finset V)} (hP : Frontier l P) (hQ : Frontier r Q)
    (hdisj : Disjoint l.leafSet r.leafSet) {A : Finset V} (hA : A ∈ P) :
    A ∉ Q := by
  intro hAQ
  obtain ⟨a, ha⟩ := hP.block_nonempty hA
  exact Finset.disjoint_left.mp hdisj (hP.block_subset hA ha)
    (hQ.block_subset hAQ ha)

private theorem merge_union_left {l r : Tree V}
    {P Q : Finset (Finset V)} (hP : Frontier l P) (hQ : Frontier r Q)
    (hdisj : Disjoint l.leafSet r.leafSet)
    {A B : Finset V} (hA : A ∈ P) (hB : B ∈ P) :
    merge (P ∪ Q) A B = merge P A B ∪ Q := by
  have hAnQ := mem_other_of_disjoint_roots hP hQ hdisj hA
  have hBnQ := mem_other_of_disjoint_roots hP hQ hdisj hB
  ext X
  simp only [merge, Finset.mem_insert, Finset.mem_erase, Finset.mem_union]
  aesop

private theorem merge_union_right {l r : Tree V}
    {P Q : Finset (Finset V)} (hP : Frontier l P) (hQ : Frontier r Q)
    (hdisj : Disjoint l.leafSet r.leafSet)
    {A B : Finset V} (hA : A ∈ Q) (hB : B ∈ Q) :
    merge (P ∪ Q) A B = P ∪ merge Q A B := by
  have hAnP := mem_other_of_disjoint_roots hQ hP hdisj.symm hA
  have hBnP := mem_other_of_disjoint_roots hQ hP hdisj.symm hB
  ext X
  simp only [merge, Finset.mem_insert, Finset.mem_erase, Finset.mem_union]
  aesop

/-- Every nonfinal frontier contains two blocks whose merge is again a
frontier. -/
theorem merge_or_whole (h : Frontier t P) (ht : t.Represents G) :
    P = {t.leafSet} ∨
      ∃ A ∈ P, ∃ B ∈ P, A ≠ B ∧ Frontier t (merge P A B) := by
  induction h with
  | whole t => exact Or.inl rfl
  | @split b l r PL PR hL hR ihL ihR =>
      simp only [Tree.Represents] at ht
      rcases ihL ht.1 with hPL | ⟨A, hA, B, hB, hAB, hmerge⟩
      · rcases ihR ht.2.1 with hPR | ⟨A, hA, B, hB, hAB, hmerge⟩
        · subst PL
          subst PR
          right
          have hlr : l.leafSet ≠ r.leafSet := by
            intro heq
            obtain ⟨x, hx⟩ := leafSet_nonempty l
            exact Finset.disjoint_left.mp ht.2.2.1 hx (heq ▸ hx)
          refine ⟨l.leafSet, by simp, r.leafSet, by simp, hlr, ?_⟩
          simpa [merge, hlr, hlr.symm] using Frontier.whole (Tree.node b l r)
        · right
          refine ⟨A, Finset.mem_union_right _ hA,
            B, Finset.mem_union_right _ hB, hAB, ?_⟩
          rw [merge_union_right hL hR ht.2.2.1 hA hB]
          exact Frontier.split hL hmerge
      · right
        refine ⟨A, Finset.mem_union_left _ hA,
          B, Finset.mem_union_left _ hB, hAB, ?_⟩
        rw [merge_union_left hL hR ht.2.2.1 hA hB]
        exact Frontier.split hmerge hR

end Frontier

end Tree

open Tree

/-- A suffix of a cotree contraction process, starting at a given frontier. -/
structure FrontierSequence (G : SimpleGraph V) (t : Tree V)
    (P : Finset (Finset V)) where
  stepCount : ℕ
  partition : ℕ → Finset (Finset V)
  starts : partition 0 = P
  ends : partition stepCount = {t.leafSet}
  step_merges : ∀ i, i < stepCount →
    ∃ A ∈ partition i, ∃ B ∈ partition i, A ≠ B ∧
      partition (i + 1) = Tree.Frontier.merge (partition i) A B
  frontier : ∀ i, i ≤ stepCount → Tree.Frontier t (partition i)

namespace FrontierSequence

variable {G : SimpleGraph V} {t : Tree V} {P : Finset (Finset V)}

def done (h : P = {t.leafSet}) (hfront : Tree.Frontier t P) :
    FrontierSequence G t P where
  stepCount := 0
  partition _ := P
  starts := rfl
  ends := h
  step_merges i hi := by omega
  frontier _ _ := hfront

def cons {A B : Finset V} (hA : A ∈ P) (hB : B ∈ P) (hAB : A ≠ B)
    (hfront : Tree.Frontier t P)
    (S : FrontierSequence G t (Tree.Frontier.merge P A B)) :
    FrontierSequence G t P where
  stepCount := S.stepCount + 1
  partition i := if i = 0 then P else S.partition (i - 1)
  starts := by simp
  ends := by
    rw [if_neg (by omega : S.stepCount + 1 ≠ 0)]
    simpa using S.ends
  step_merges i hi := by
    by_cases hi0 : i = 0
    · subst i
      refine ⟨A, by simp [hA], B, by simp [hB], hAB, ?_⟩
      simp [S.starts]
    · obtain ⟨A', hA', B', hB', hAB', hm⟩ :=
        S.step_merges (i - 1) (by omega)
      refine ⟨A', by simpa [hi0] using hA',
        B', by simpa [hi0] using hB', hAB', ?_⟩
      rw [if_neg (by omega : i + 1 ≠ 0), if_neg hi0]
      have hi1 : 1 ≤ i := Nat.one_le_iff_ne_zero.mpr hi0
      have hpred : i - 1 + 1 = i := Nat.sub_add_cancel hi1
      have hsucc : i + 1 - 1 = i := by omega
      simpa only [hpred, hsucc] using hm
  frontier i hi := by
    by_cases hi0 : i = 0
    · simpa [hi0] using hfront
    · rw [if_neg hi0]
      exact S.frontier (i - 1) (by omega)

end FrontierSequence

private theorem merge_card_add_one {G : SimpleGraph V} {t : Tree V}
    {P : Finset (Finset V)} (hfront : Tree.Frontier t P) (ht : t.Represents G)
    {A B : Finset V} (hA : A ∈ P) (hB : B ∈ P) (hAB : A ≠ B) :
    (Tree.Frontier.merge P A B).card + 1 = P.card := by
  have hB_eraseA : B ∈ P.erase A := Finset.mem_erase.mpr ⟨hAB.symm, hB⟩
  have hUnion_not_rest : A ∪ B ∉ (P.erase A).erase B := by
    intro hU
    have hUold : A ∪ B ∈ P :=
      (Finset.mem_erase.mp (Finset.mem_erase.mp hU).2).2
    have hneA : A ≠ A ∪ B := by
      intro heq
      obtain ⟨b, hb⟩ := hfront.block_nonempty hB
      have hbA : b ∈ A := by simpa [← heq] using Finset.mem_union_right A hb
      exact Finset.disjoint_left.mp (hfront.disjoint_blocks ht hA hB hAB) hbA hb
    obtain ⟨a, ha⟩ := hfront.block_nonempty hA
    exact Finset.disjoint_left.mp
      (hfront.disjoint_blocks ht hA hUold hneA)
      ha (Finset.mem_union_left _ ha)
  calc
    (Tree.Frontier.merge P A B).card + 1 =
        ((P.erase A).erase B).card + 2 := by
      unfold Tree.Frontier.merge
      rw [Finset.card_insert_of_notMem hUnion_not_rest]
    _ = (P.erase A).card + 1 := by
      rw [Finset.card_erase_of_mem hB_eraseA]
      have hpos' : 0 < (P.erase A).card :=
        Finset.card_pos.mpr ⟨B, hB_eraseA⟩
      omega
    _ = P.card := by
      rw [Finset.card_erase_of_mem hA]
      have hpos : 0 < P.card := Finset.card_pos.mpr ⟨A, hA⟩
      omega

/-- Repeatedly merge sibling frontier blocks. -/
theorem exists_frontierSequence {G : SimpleGraph V} {t : Tree V}
    {P : Finset (Finset V)} (hfront : Tree.Frontier t P) (ht : t.Represents G) :
    Nonempty (FrontierSequence G t P) := by
  induction hcard : P.card using Nat.strong_induction_on generalizing P with
  | h n ih =>
      rcases hfront.merge_or_whole ht with hdone |
        ⟨A, hA, B, hB, hAB, hnext⟩
      · exact ⟨FrontierSequence.done hdone hfront⟩
      · have hlt : (Tree.Frontier.merge P A B).card < P.card := by
          have hc := merge_card_add_one hfront ht hA hB hAB
          omega
        obtain ⟨S⟩ := ih _ (hcard ▸ hlt) hnext rfl
        exact ⟨FrontierSequence.cons hA hB hAB hfront S⟩

theorem redDegree_eq_zero_of_frontier {G : SimpleGraph V} {t : Tree V}
    {P : Finset (Finset V)} (hfront : Tree.Frontier t P) (ht : t.Represents G)
    {A : Finset V} (hA : A ∈ P) : redDegree G P A = 0 := by
  classical
  unfold redDegree
  rw [Set.ncard_eq_zero]
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro B hB
  exact hB.2.2 (hfront.homogeneous_blocks ht hA hB.1 hB.2.1.symm)

/-- A cotree whose leaves are all vertices yields a width-zero partition
sequence. Thus the project convention is genuinely twin-width 0, not 1. -/
theorem hasTwinWidthAtMost_zero_of_represents [Fintype V]
    {G : SimpleGraph V} {t : Tree V}
    (hroot : t.leafSet = Finset.univ) (ht : t.Represents G) :
    HasTwinWidthAtMost G 0 := by
  have hfront : Tree.Frontier t
      (t.leafSet.image fun v => ({v} : Finset V)) :=
    Tree.Frontier.singletons t
  obtain ⟨S⟩ := exists_frontierSequence hfront ht
  exact ⟨{
    stepCount := S.stepCount
    partition := S.partition
    starts := by
      rw [S.starts]
      exact Tree.Frontier.singletons_eq_singletonPartition hroot
    ends := by rw [S.ends]; simp
    step_merges := S.step_merges
    redDegree_le := by
      intro i hi A hA
      rw [redDegree_eq_zero_of_frontier (S.frontier i hi) ht hA]
  }⟩

end

end Lax214022Proofs.CotreeSequence
