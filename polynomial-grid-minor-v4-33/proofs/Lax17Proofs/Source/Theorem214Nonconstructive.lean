import Lax17Proofs.Source.BalancedSeparation
import Lax17Proofs.Source.Section46Flow

namespace Lax17Proofs

universe u v w

/-!
# Nonconstructive proof infrastructure for Chekuri--Chuzhoy Theorem 2.14

This file follows the nonconstructive proof of Chekuri--Chuzhoy Theorem 2.14
(Appendix A.1 in `chekuri-chuzhoy-2.pdf`).  The key argument starts with a
minimum balanced separation, proves that its separator is node-well-linked, and
then uses flow routing to obtain a large node-well-linked terminal subset.

The first part formalizes the reachable sides obtained after deleting a
candidate separator inside one side of a balanced separation.  These are the
sets used in Claim A.1 to replace a minimum balanced separation by a smaller
one, yielding a contradiction.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-! ## Reachable sides after deleting a candidate separator -/

/-- Vertices of `Y \ S` reachable from the seed set `A` in the graph induced
on `Y \ S`.

This is the non-terminal version of
`Section46.reachableTerminalsAfterDeleting`: it represents the union of
components of `G[Y \ S]` that contain a seed vertex of `A`. -/
noncomputable def reachableSide
    (G : _root_.SimpleGraph V) (Y S A : Finset V) : Finset V := by
  classical
  exact (Y \ S).filter fun v =>
    ∃ a ∈ A, a ∈ Y \ S ∧
      (inducedOnFinset G (Y \ S)).Reachable a v

namespace reachableSide

variable {Y S A B : Finset V}

omit [Fintype V] in
theorem subset_deleted :
    reachableSide G Y S A ⊆ Y \ S := by
  classical
  intro v hv
  exact (Finset.mem_filter.mp hv).1

omit [Fintype V] in
theorem subset_left :
    reachableSide G Y S A ⊆ Y := by
  intro v hv
  exact (Finset.mem_sdiff.mp (subset_deleted (G := G) (Y := Y) (S := S) (A := A) hv)).1

omit [Fintype V] in
theorem disjoint_deleted :
    Disjoint (reachableSide G Y S A) S := by
  classical
  rw [Finset.disjoint_left]
  intro v hv hS
  exact (Finset.mem_sdiff.mp
    (subset_deleted (G := G) (Y := Y) (S := S) (A := A) hv)).2 hS

omit [Fintype V] in
theorem not_mem_deleted {v : V}
    (hv : v ∈ reachableSide G Y S A) :
    v ∉ S :=
  (Finset.mem_sdiff.mp
    (subset_deleted (G := G) (Y := Y) (S := S) (A := A) hv)).2

omit [Fintype V] in
theorem exists_seed_reachable {v : V}
    (hv : v ∈ reachableSide G Y S A) :
    ∃ a ∈ A, a ∈ Y \ S ∧
      (inducedOnFinset G (Y \ S)).Reachable a v := by
  classical
  exact (Finset.mem_filter.mp hv).2

omit [Fintype V] in
theorem mem_of_reachable {a v : V}
    (haA : a ∈ A) (haYS : a ∈ Y \ S)
    (hreach : (inducedOnFinset G (Y \ S)).Reachable a v) :
    v ∈ reachableSide G Y S A := by
  classical
  have hvYS : v ∈ Y \ S := by
    rcases hreach with ⟨W⟩
    exact Section46.InducedOnFinset.walk_support_subset
      (G := G) (C := Y \ S) W haYS v (by simp)
  rw [reachableSide, Finset.mem_filter]
  exact ⟨hvYS, a, haA, haYS, hreach⟩

omit [Fintype V] in
theorem seed_subset (hA : A ⊆ Y \ S) :
    A ⊆ reachableSide G Y S A := by
  intro a ha
  exact mem_of_reachable (G := G) (Y := Y) (S := S) (A := A)
    ha (hA ha) ⟨_root_.SimpleGraph.Walk.nil⟩

omit [Fintype V] in
/-- Reachable sides from two seed sets are disjoint when `S` separates the seed
sets in the induced graph on `Y`. -/
theorem disjoint_of_separator
    (hsep : STSeparator (inducedOnFinset G Y) A B S) :
    Disjoint (reachableSide G Y S A) (reachableSide G Y S B) := by
  classical
  rw [Finset.disjoint_left]
  intro v hvA hvB
  rcases exists_seed_reachable (G := G) (Y := Y) (S := S) (A := A) hvA with
    ⟨a, haA, haYS, hreachA⟩
  rcases exists_seed_reachable (G := G) (Y := Y) (S := S) (A := B) hvB with
    ⟨b, hbB, _hbYS, hreachB⟩
  have hreachAB :
      (inducedOnFinset G (Y \ S)).Reachable a b :=
    hreachA.trans hreachB.symm
  exact Section46.not_separator_of_reachable_avoiding
    (G := G) (C := Y) (X := S) (A := A) (B := B)
    hsep haA hbB haYS hreachAB

omit [Fintype V] in
/-- Reachable sides are closed under one more edge inside `Y \ S`. -/
theorem mem_of_adj
    {u v : V}
    (hu : u ∈ reachableSide G Y S A)
    (hvYS : v ∈ Y \ S)
    (huv : G.Adj u v) :
    v ∈ reachableSide G Y S A := by
  classical
  rcases exists_seed_reachable (G := G) (Y := Y) (S := S) (A := A) hu with
    ⟨a, haA, haYS, hreach⟩
  have huYS : u ∈ Y \ S :=
    subset_deleted (G := G) (Y := Y) (S := S) (A := A) hu
  have huvH : (inducedOnFinset G (Y \ S)).Adj u v := by
    exact ⟨huv, huYS, hvYS⟩
  exact mem_of_reachable (G := G) (Y := Y) (S := S) (A := A)
    haA haYS (hreach.trans huvH.reachable)

omit [Fintype V] in
/-- No edge goes from a reachable side to an unreached vertex of `Y \ S`. -/
theorem not_adj_of_not_mem
    {u v : V}
    (hu : u ∈ reachableSide G Y S A)
    (hvYS : v ∈ Y \ S)
    (hvnot : v ∉ reachableSide G Y S A) :
    ¬ G.Adj u v := by
  intro huv
  exact hvnot (mem_of_adj (G := G) (Y := Y) (S := S) (A := A)
    hu hvYS huv)

end reachableSide

/-! ## Separator surgery from Claim A.1 -/

/-- The residual part of `Y \ S` not assigned to either reachable side. -/
def surgeryMiddle (Y S R₁ R₂ : Finset V) : Finset V :=
  Y \ (S ∪ R₁ ∪ R₂)

/-- The left side of the separation used in Claim A.1:
`R₁ ∪ R₃ ∪ S`. -/
def surgeryLeft (Y S R₁ R₂ : Finset V) : Finset V :=
  (R₁ ∪ surgeryMiddle Y S R₁ R₂) ∪ S

/-- The right side of the separation used in Claim A.1:
`Z ∪ R₂ ∪ S`. -/
def surgeryRight (Z S R₂ : Finset V) : Finset V :=
  (Z ∪ R₂) ∪ S

namespace surgery

variable {C Y Z S A B : Finset V}

omit [Fintype V] in
theorem middle_subset_left {R₁ R₂ : Finset V} :
    surgeryMiddle Y S R₁ R₂ ⊆ Y := by
  intro v hv
  exact (Finset.mem_sdiff.mp hv).1

omit [Fintype V] in
theorem left_subset_original
    {R₁ R₂ : Finset V}
    (hR₁ : R₁ ⊆ Y) (hS : S ⊆ Y) :
    surgeryLeft Y S R₁ R₂ ⊆ Y := by
  intro v hv
  rw [surgeryLeft] at hv
  rcases Finset.mem_union.mp hv with hv | hvS
  · rcases Finset.mem_union.mp hv with hvR₁ | hvM
    · exact hR₁ hvR₁
    · exact middle_subset_left hvM
  · exact hS hvS

omit [Fintype V] in
theorem right_subset_ambient
    {R₂ : Finset V}
    (hZ : Z ⊆ C) (hR₂ : R₂ ⊆ C) (hS : S ⊆ C) :
    surgeryRight Z S R₂ ⊆ C := by
  intro v hv
  rw [surgeryRight] at hv
  rcases Finset.mem_union.mp hv with hv | hvS
  · rcases Finset.mem_union.mp hv with hvZ | hvR₂
    · exact hZ hvZ
    · exact hR₂ hvR₂
  · exact hS hvS

omit [Fintype V] in
theorem left_subset_ambient
    {R₁ R₂ : Finset V}
    (hY : Y ⊆ C) (hR₁ : R₁ ⊆ Y) (hS : S ⊆ Y) :
    surgeryLeft Y S R₁ R₂ ⊆ C :=
  subset_trans (left_subset_original (Y := Y) (S := S) hR₁ hS) hY

omit [Fintype V] in
/-- The vertex-set surgery in Claim A.1 preserves the separation property.

This is the structural half of the minimum-separation contradiction.  The
right reachable side `R₂` is instantiated as
`reachableSide G Y S B`; its closure in `G[Y \ S]` rules out new crossing
edges from the modified left side to the moved component side. -/
theorem vertexSeparation
    (hYZ : VertexSeparation G C Y Z)
    (hS : S ⊆ Y) :
    VertexSeparation G C
      (surgeryLeft Y S (reachableSide G Y S A) (reachableSide G Y S B))
      (surgeryRight Z S (reachableSide G Y S B)) := by
  classical
  let R₁ := reachableSide G Y S A
  let R₂ := reachableSide G Y S B
  let L := surgeryLeft Y S R₁ R₂
  let R := surgeryRight Z S R₂
  have hR₁Y : R₁ ⊆ Y :=
    reachableSide.subset_left (G := G) (Y := Y) (S := S) (A := A)
  have hR₂Y : R₂ ⊆ Y :=
    reachableSide.subset_left (G := G) (Y := Y) (S := S) (A := B)
  have hSC : S ⊆ C := subset_trans hS hYZ.left_subset
  have hR₂C : R₂ ⊆ C := subset_trans hR₂Y hYZ.left_subset
  refine ⟨?_, ?_, ?_, ?_⟩
  · change L ⊆ C
    exact left_subset_ambient (Y := Y) (S := S) (R₁ := R₁) (R₂ := R₂)
      hYZ.left_subset hR₁Y hS
  · change R ⊆ C
    exact right_subset_ambient (Z := Z) (S := S) (R₂ := R₂)
      hYZ.right_subset hR₂C hSC
  · change L ∪ R = C
    apply Finset.Subset.antisymm
    · intro v hv
      rcases Finset.mem_union.mp hv with hvL | hvR
      · exact left_subset_ambient (Y := Y) (S := S) (R₁ := R₁) (R₂ := R₂)
          hYZ.left_subset hR₁Y hS hvL
      · exact right_subset_ambient (Z := Z) (S := S) (R₂ := R₂)
          hYZ.right_subset hR₂C hSC hvR
    · intro v hvC
      have hvYZ : v ∈ Y ∪ Z := by
        rw [hYZ.cover]
        exact hvC
      rcases Finset.mem_union.mp hvYZ with hvY | hvZ
      · by_cases hvS : v ∈ S
        · exact Finset.mem_union_left R (by
            simp [L, surgeryLeft, hvS])
        · by_cases hvR₁ : v ∈ R₁
          · exact Finset.mem_union_left R (by
              simp [L, surgeryLeft, hvR₁])
          · by_cases hvR₂ : v ∈ R₂
            · exact Finset.mem_union_right L (by
                simp [R, surgeryRight, hvR₂])
            · have hvM : v ∈ surgeryMiddle Y S R₁ R₂ := by
                exact Finset.mem_sdiff.mpr ⟨hvY, by simp [hvS, hvR₁, hvR₂]⟩
              exact Finset.mem_union_left R (by
                simp [L, surgeryLeft, hvM])
      · exact Finset.mem_union_right L (by
          simp [R, surgeryRight, hvZ])
  · intro u v huL huRnot hvR hvLnot
    change u ∈ L at huL
    change u ∉ R at huRnot
    change v ∈ R at hvR
    change v ∉ L at hvLnot
    have huY : u ∈ Y :=
      left_subset_original (Y := Y) (S := S) (R₁ := R₁) (R₂ := R₂)
        hR₁Y hS huL
    have huSnot : u ∉ S := by
      intro huS
      exact huRnot (by
        simp [R, surgeryRight, huS])
    have huZnot : u ∉ Z := by
      intro huZ
      exact huRnot (by
        simp [R, surgeryRight, huZ])
    have huYS : u ∈ Y \ S := Finset.mem_sdiff.mpr ⟨huY, huSnot⟩
    by_cases hvR₂ : v ∈ R₂
    · have huR₂not : u ∉ R₂ := by
        intro huR₂
        exact huRnot (by
          simp [R, surgeryRight, huR₂])
      have hno_vu : ¬ G.Adj v u :=
        reachableSide.not_adj_of_not_mem (G := G) (Y := Y) (S := S) (A := B)
          hvR₂ huYS huR₂not
      intro huv
      exact hno_vu (G.symm huv)
    · have hvSnot : v ∉ S := by
        intro hvS
        exact hvLnot (by
          simp [L, surgeryLeft, hvS])
      have hvZ : v ∈ Z := by
        rcases Finset.mem_union.mp (show v ∈ (Z ∪ R₂) ∪ S by simpa [R, surgeryRight] using hvR)
          with hvZR | hvS
        · rcases Finset.mem_union.mp hvZR with hvZ | hvR₂'
          · exact hvZ
          · exact False.elim (hvR₂ hvR₂')
        · exact False.elim (hvSnot hvS)
      have hvYnot : v ∉ Y := by
        intro hvY
        by_cases hvR₁ : v ∈ R₁
        · exact hvLnot (by
            simp [L, surgeryLeft, hvR₁])
        · have hvM : v ∈ surgeryMiddle Y S R₁ R₂ := by
            exact Finset.mem_sdiff.mpr ⟨hvY, by simp [hvSnot, hvR₁, hvR₂]⟩
          exact hvLnot (by
            simp [L, surgeryLeft, hvM])
      exact hYZ.no_cross huY huZnot hvZ hvYnot

omit [Fintype V] in
theorem left_union_moved_covers_original
    {R₁ R₂ : Finset V} :
    Y ⊆ surgeryLeft Y S R₁ R₂ ∪ R₂ := by
  classical
  intro v hvY
  by_cases hvS : v ∈ S
  · exact Finset.mem_union_left R₂ (by simp [surgeryLeft, hvS])
  · by_cases hvR₁ : v ∈ R₁
    · exact Finset.mem_union_left R₂ (by simp [surgeryLeft, hvR₁])
    · by_cases hvR₂ : v ∈ R₂
      · exact Finset.mem_union_right (surgeryLeft Y S R₁ R₂) hvR₂
      · have hvM : v ∈ surgeryMiddle Y S R₁ R₂ := by
          exact Finset.mem_sdiff.mpr ⟨hvY, by simp [hvS, hvR₁, hvR₂]⟩
        exact Finset.mem_union_left R₂ (by simp [surgeryLeft, hvM])

omit [Fintype V] in
theorem reachable_subset_left_surgery
    {R₁ R₂ : Finset V} :
    R₁ ⊆ surgeryLeft Y S R₁ R₂ := by
  intro v hv
  simp [surgeryLeft, hv]

/-- The separator surgery remains balanced if the retained side of `Y` has at
least as many terminals as the moved reachable side.

The hypothesis `κ ≤ 2 * |Y ∩ T|` is the scaled form of the paper's choice of
the larger side, `|Y ∩ T| ≥ κ / 2`. -/
theorem balancedSeparation
    {T : Finset V} {κ : ℕ}
    (hYZ : BalancedSeparation G C T κ Y Z)
    (hS : S ⊆ Y)
    (hYhalf : κ ≤ 2 * (Y ∩ T).card)
    (hR₂_le_R₁ :
      ((reachableSide G Y S B) ∩ T).card ≤
        ((reachableSide G Y S A) ∩ T).card) :
    BalancedSeparation G C T κ
      (surgeryLeft Y S (reachableSide G Y S A) (reachableSide G Y S B))
      (surgeryRight Z S (reachableSide G Y S B)) := by
  classical
  let R₁ := reachableSide G Y S A
  let R₂ := reachableSide G Y S B
  let L := surgeryLeft Y S R₁ R₂
  let R := surgeryRight Z S R₂
  have hvertex : VertexSeparation G C L R :=
    vertexSeparation (G := G) (C := C) (Y := Y) (Z := Z) (S := S) (A := A) (B := B)
      hYZ.toVertexSeparation hS
  refine
    { toVertexSeparation := hvertex
      left_balanced := ?_
      right_balanced := ?_ }
  · have hYcover : Y ∩ T ⊆ (L ∩ T) ∪ (R₂ ∩ T) := by
      intro v hv
      have hvY : v ∈ Y := (Finset.mem_inter.mp hv).1
      have hvT : v ∈ T := (Finset.mem_inter.mp hv).2
      have hvLR := left_union_moved_covers_original
        (Y := Y) (S := S) (R₁ := R₁) (R₂ := R₂) hvY
      rcases Finset.mem_union.mp hvLR with hvL | hvR₂
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvL, hvT⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvR₂, hvT⟩)
    have hYcard_le :
        (Y ∩ T).card ≤ (L ∩ T).card + (R₂ ∩ T).card := by
      calc
        (Y ∩ T).card ≤ ((L ∩ T) ∪ (R₂ ∩ T)).card :=
          Finset.card_le_card hYcover
        _ ≤ (L ∩ T).card + (R₂ ∩ T).card := Finset.card_union_le _ _
    have hR₁L : R₁ ∩ T ⊆ L ∩ T := by
      intro v hv
      exact Finset.mem_inter.mpr
        ⟨reachable_subset_left_surgery (Y := Y) (S := S) (R₁ := R₁) (R₂ := R₂)
          (Finset.mem_inter.mp hv).1,
          (Finset.mem_inter.mp hv).2⟩
    have hR₂_le_L : (R₂ ∩ T).card ≤ (L ∩ T).card :=
      hR₂_le_R₁.trans (Finset.card_le_card hR₁L)
    have hY_le_twoL : (Y ∩ T).card ≤ 2 * (L ∩ T).card := by
      omega
    calc
      κ ≤ 2 * (Y ∩ T).card := hYhalf
      _ ≤ 2 * (2 * (L ∩ T).card) := Nat.mul_le_mul_left 2 hY_le_twoL
      _ = 4 * (L ∩ T).card := by ring
  · have hZR : Z ∩ T ⊆ R ∩ T := by
      intro v hv
      exact Finset.mem_inter.mpr
        ⟨by
          have hvZ : v ∈ Z := (Finset.mem_inter.mp hv).1
          simp [R, surgeryRight, hvZ],
          (Finset.mem_inter.mp hv).2⟩
    exact hYZ.right_balanced.trans
      (Nat.mul_le_mul_left 4 (Finset.card_le_card hZR))

omit [Fintype V] in
theorem overlap_subset_old_without_moved_union_deleted
    (hdisj : Disjoint (reachableSide G Y S A) (reachableSide G Y S B))
    (hB : B ⊆ Y ∩ Z) :
    (surgeryLeft Y S (reachableSide G Y S A) (reachableSide G Y S B) ∩
      surgeryRight Z S (reachableSide G Y S B)) ⊆
        ((Y ∩ Z) \ B) ∪ S := by
  classical
  let R₁ := reachableSide G Y S A
  let R₂ := reachableSide G Y S B
  let L := surgeryLeft Y S R₁ R₂
  let R := surgeryRight Z S R₂
  intro v hv
  have hvL : v ∈ L := (Finset.mem_inter.mp hv).1
  have hvR : v ∈ R := (Finset.mem_inter.mp hv).2
  by_cases hvS : v ∈ S
  · exact Finset.mem_union_right _ hvS
  · have hvL' : v ∈ (R₁ ∪ surgeryMiddle Y S R₁ R₂) ∪ S := by
      simpa [L, surgeryLeft] using hvL
    have hvY' : v ∈ Y := by
      rcases Finset.mem_union.mp hvL' with hvLM | hvS'
      · rcases Finset.mem_union.mp hvLM with hvR₁ | hvM
        · exact reachableSide.subset_left (G := G) (Y := Y) (S := S) (A := A) hvR₁
        · exact (Finset.mem_sdiff.mp hvM).1
      · exact False.elim (hvS hvS')
    have hvR₂not : v ∉ R₂ := by
      intro hvR₂
      rcases Finset.mem_union.mp hvL' with hvLM | hvS'
      · rcases Finset.mem_union.mp hvLM with hvR₁ | hvM
        · exact Finset.disjoint_left.mp hdisj hvR₁ hvR₂
        · exact (by
            have hnot : v ∉ S ∪ R₁ ∪ R₂ := (Finset.mem_sdiff.mp hvM).2
            exact hnot (by simp [hvR₂]))
      · exact hvS hvS'
    have hvZ : v ∈ Z := by
      have hvR' : v ∈ (Z ∪ R₂) ∪ S := by
        simpa [R, surgeryRight] using hvR
      rcases Finset.mem_union.mp hvR' with hvZR | hvS'
      · rcases Finset.mem_union.mp hvZR with hvZ | hvR₂
        · exact hvZ
        · exact False.elim (hvR₂not hvR₂)
      · exact False.elim (hvS hvS')
    have hvBnot : v ∉ B := by
      intro hvB
      have hvYS : v ∈ Y \ S :=
        Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp (hB hvB)).1, hvS⟩
      have hvR₂ : v ∈ R₂ :=
        reachableSide.mem_of_reachable (G := G) (Y := Y) (S := S) (A := B)
          hvB hvYS ⟨_root_.SimpleGraph.Walk.nil⟩
      exact hvR₂not hvR₂
    exact Finset.mem_union_left S
      (Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hvY', hvZ⟩, hvBnot⟩)

omit [Fintype V] in
theorem order_lt
    (hdisj : Disjoint (reachableSide G Y S A) (reachableSide G Y S B))
    (hB : B ⊆ Y ∩ Z)
    (hSlt : S.card < B.card) :
    (surgeryLeft Y S (reachableSide G Y S A) (reachableSide G Y S B) ∩
      surgeryRight Z S (reachableSide G Y S B)).card < (Y ∩ Z).card := by
  classical
  let XY := Y ∩ Z
  let L := surgeryLeft Y S (reachableSide G Y S A) (reachableSide G Y S B)
  let R := surgeryRight Z S (reachableSide G Y S B)
  have hsubset :
      L ∩ R ⊆ (XY \ B) ∪ S := by
    simpa [XY, L, R] using
      overlap_subset_old_without_moved_union_deleted
        (G := G) (Y := Y) (Z := Z) (S := S) (A := A) (B := B)
        hdisj hB
  have hcard₁ : (L ∩ R).card ≤ ((XY \ B) ∪ S).card :=
    Finset.card_le_card hsubset
  have hcard₂ : ((XY \ B) ∪ S).card ≤ (XY \ B).card + S.card :=
    Finset.card_union_le _ _
  have hsdiff : (XY \ B).card = XY.card - B.card := by
    rw [Finset.card_sdiff]
    have hinter : B ∩ XY = B := by
      ext v
      constructor
      · intro hv
        exact (Finset.mem_inter.mp hv).1
      · intro hv
        exact Finset.mem_inter.mpr ⟨hv, hB hv⟩
    rw [hinter]
  have hBcard_le : B.card ≤ XY.card := Finset.card_le_card hB
  calc
    (L ∩ R).card ≤ ((XY \ B) ∪ S).card := hcard₁
    _ ≤ (XY \ B).card + S.card := hcard₂
    _ = XY.card - B.card + S.card := by rw [hsdiff]
    _ < XY.card := by omega

end surgery

/-! ## Claim A.1: the minimum overlap is node-well-linked -/

omit [Fintype V] in
theorem stSeparator_symm
    {H : _root_.SimpleGraph V} {A B S : Finset V}
    (hsep : STSeparator H A B S) :
    STSeparator H B A S := by
  intro P hP
  apply hsep P
  rcases hP with h | h
  · exact Or.inr h
  · exact Or.inl h

omit [Fintype V] in
theorem stSeparator_inter_induced_region
    {Y A B S : Finset V}
    (hA : A ⊆ Y) (hB : B ⊆ Y)
    (hsep : STSeparator (inducedOnFinset G Y) A B S) :
    STSeparator (inducedOnFinset G Y) A B (S ∩ Y) := by
  classical
  intro P hP
  rcases hsep P hP with ⟨v, hvP, hvS⟩
  have hvY : v ∈ Y :=
    Section46.InducedOnFinset.graphPath_vertexSet_subset_of_connects
      (G := G) (C := Y) (A := A) (B := B) P hP hA hB hvP
  exact ⟨v, hvP, Finset.mem_inter.mpr ⟨hvS, hvY⟩⟩

omit [Fintype V] in
theorem stSeparator_inter_induced_region_card_le
    {Y S : Finset V} :
    (S ∩ Y).card ≤ S.card :=
  Finset.card_le_card Finset.inter_subset_left

/-- Claim A.1 of the nonconstructive proof of Chekuri--Chuzhoy Theorem 2.14.

Let `(Y,Z)` be a minimum balanced separation, and suppose `Y` is the side with
at least half of the terminals.  Then the overlap `Y ∩ Z` is node-well-linked
inside `G[Y]`.

The proof is by contradiction through vertex Menger.  A separator of size less
than the smaller terminal side yields the reachable-side surgery above.  One
of the two reachable sides contains no more terminals than the other; moving
that side to `Z` gives another balanced separation of strictly smaller order,
contradicting minimality. -/
theorem minimum_overlap_nodeWellLinkedIn_left
    {C T Y Z : Finset V} {κ : ℕ}
    (hYZ : BalancedSeparation G C T κ Y Z)
    (hmin : BalancedSeparation.IsMinimum hYZ)
    (hYhalf : κ ≤ 2 * (Y ∩ T).card) :
    NodeWellLinkedIn G Y (Y ∩ Z) := by
  classical
  refine Section46.nodeWellLinkedIn_of_induced_separator_lower_bound
    (G := G) (C := Y) (T := Y ∩ Z) Finset.inter_subset_left ?_
  intro A B S hA hB hABdisj hsep
  by_contra hnot
  have hSlt_min : S.card < min A.card B.card := Nat.lt_of_not_ge hnot
  let S₀ := S ∩ Y
  have hS₀Y : S₀ ⊆ Y := Finset.inter_subset_right
  have hA_Y : A ⊆ Y := subset_trans hA Finset.inter_subset_left
  have hB_Y : B ⊆ Y := subset_trans hB Finset.inter_subset_left
  have hsep₀ : STSeparator (inducedOnFinset G Y) A B S₀ := by
    simpa [S₀] using
      stSeparator_inter_induced_region (G := G) (Y := Y) (A := A) (B := B)
        hA_Y hB_Y hsep
  have hS₀card_le : S₀.card ≤ S.card := by
    simpa [S₀] using stSeparator_inter_induced_region_card_le (Y := Y) (S := S)
  have hS₀lt_min : S₀.card < min A.card B.card := lt_of_le_of_lt hS₀card_le hSlt_min
  have hS₀ltA : S₀.card < A.card := hS₀lt_min.trans_le (Nat.min_le_left _ _)
  have hS₀ltB : S₀.card < B.card := hS₀lt_min.trans_le (Nat.min_le_right _ _)
  let R_A := reachableSide G Y S₀ A
  let R_B := reachableSide G Y S₀ B
  have hdisjAB : Disjoint R_A R_B := by
    simpa [R_A, R_B] using
      reachableSide.disjoint_of_separator
        (G := G) (Y := Y) (S := S₀) (A := A) (B := B) hsep₀
  by_cases hle : (R_B ∩ T).card ≤ (R_A ∩ T).card
  · have hbalanced :
        BalancedSeparation G C T κ
          (surgeryLeft Y S₀ R_A R_B)
          (surgeryRight Z S₀ R_B) := by
      simpa [R_A, R_B] using
        surgery.balancedSeparation
          (G := G) (C := C) (Y := Y) (Z := Z) (S := S₀)
          (A := A) (B := B) (T := T) (κ := κ)
          hYZ hS₀Y hYhalf hle
    have hlt :
        (surgeryLeft Y S₀ R_A R_B ∩ surgeryRight Z S₀ R_B).card <
          (Y ∩ Z).card := by
      simpa [R_A, R_B] using
        surgery.order_lt
          (G := G) (Y := Y) (Z := Z) (S := S₀) (A := A) (B := B)
          hdisjAB hB hS₀ltB
    exact (BalancedSeparation.not_order_lt_of_isMinimum
      (hYZ := hYZ) hmin hbalanced) hlt
  · have hle' : (R_A ∩ T).card ≤ (R_B ∩ T).card := Nat.le_of_not_ge hle
    have hsep₀_symm : STSeparator (inducedOnFinset G Y) B A S₀ :=
      stSeparator_symm hsep₀
    have hdisjBA : Disjoint R_B R_A := by
      simpa [R_A, R_B] using
        reachableSide.disjoint_of_separator
          (G := G) (Y := Y) (S := S₀) (A := B) (B := A) hsep₀_symm
    have hbalanced :
        BalancedSeparation G C T κ
          (surgeryLeft Y S₀ R_B R_A)
          (surgeryRight Z S₀ R_A) := by
      simpa [R_A, R_B] using
        surgery.balancedSeparation
          (G := G) (C := C) (Y := Y) (Z := Z) (S := S₀)
          (A := B) (B := A) (T := T) (κ := κ)
          hYZ hS₀Y hYhalf hle'
    have hlt :
        (surgeryLeft Y S₀ R_B R_A ∩ surgeryRight Z S₀ R_A).card <
          (Y ∩ Z).card := by
      simpa [R_A, R_B] using
        surgery.order_lt
          (G := G) (Y := Y) (Z := Z) (S := S₀) (A := B) (B := A)
          hdisjBA hA hS₀ltA
    exact (BalancedSeparation.not_order_lt_of_isMinimum
      (hYZ := hYZ) hmin hbalanced) hlt

theorem balancedSeparation_isMinimum_symm {C T Y Z : Finset V} {κ : ℕ}
    {hYZ : BalancedSeparation G C T κ Y Z}
    (hmin : BalancedSeparation.IsMinimum hYZ) :
    BalancedSeparation.IsMinimum hYZ.symm := by
  intro Y' Z' hY'Z'
  have h := hmin hY'Z'.symm
  simpa [Finset.inter_comm] using h

/-- Choose a minimum balanced separation and orient it so that the left side
contains at least half of the terminals.  Its overlap is node-well-linked in
the left side by Claim A.1. -/
theorem exists_minimum_balancedSeparation_overlap_nodeWellLinked
    {C T : Finset V} {κ : ℕ}
    (hT : T ⊆ C) (hcard : T.card = κ) :
    ∃ Y Z : Finset V,
      ∃ hYZ : BalancedSeparation G C T κ Y Z,
        BalancedSeparation.IsMinimum hYZ ∧
          κ ≤ 2 * (Y ∩ T).card ∧
            NodeWellLinkedIn G Y (Y ∩ Z) := by
  classical
  rcases BalancedSeparation.minOrder_spec (G := G) (C := C) (T := T) (κ := κ)
      hT hcard with ⟨Y, Z, hYZ, horder⟩
  have hmin : BalancedSeparation.IsMinimum hYZ :=
    BalancedSeparation.isMinimum_of_order_eq_minOrder
      (G := G) (C := C) (T := T) (κ := κ)
      hT hcard hYZ horder
  have hT_cover : T ⊆ (Y ∩ T) ∪ (Z ∩ T) := by
    intro v hvT
    have hvC : v ∈ C := hT hvT
    have hvYZ : v ∈ Y ∪ Z := by
      rw [hYZ.toVertexSeparation.cover]
      exact hvC
    rcases Finset.mem_union.mp hvYZ with hvY | hvZ
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hvY, hvT⟩)
    · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨hvZ, hvT⟩)
  have hκ_le_sum : κ ≤ (Y ∩ T).card + (Z ∩ T).card := by
    rw [← hcard]
    calc
      T.card ≤ ((Y ∩ T) ∪ (Z ∩ T)).card := Finset.card_le_card hT_cover
      _ ≤ (Y ∩ T).card + (Z ∩ T).card := Finset.card_union_le _ _
  have hhalf :
      κ ≤ 2 * (Y ∩ T).card ∨ κ ≤ 2 * (Z ∩ T).card := by
    omega
  rcases hhalf with hYhalf | hZhalf
  · exact
      ⟨Y, Z, hYZ, hmin, hYhalf,
        minimum_overlap_nodeWellLinkedIn_left
          (G := G) (C := C) (T := T) (Y := Y) (Z := Z) (κ := κ)
          hYZ hmin hYhalf⟩
  · have hmin_symm : BalancedSeparation.IsMinimum hYZ.symm :=
      balancedSeparation_isMinimum_symm (G := G) hmin
    have hnode :
        NodeWellLinkedIn G Z (Z ∩ Y) :=
      minimum_overlap_nodeWellLinkedIn_left
        (G := G) (C := C) (T := T) (Y := Z) (Z := Y) (κ := κ)
        hYZ.symm hmin_symm (by simpa [Finset.inter_comm] using hZhalf)
    exact
      ⟨Z, Y, hYZ.symm, hmin_symm,
        by simpa [Finset.inter_comm] using hZhalf,
        hnode⟩

/-! ## Terminal subsets on the two sides of a balanced separation -/

/-- In the nonconstructive proof, after orienting the minimum separation so
that `Y` contains at least half of the terminals, we choose equal-size disjoint
terminal subsets from `Z` and `Y`.  This lemma packages that finite-set
selection.

The hypothesis `4 * q ≤ κ` is the division-free form of `q ≤ κ / 4`. -/
theorem exists_disjoint_terminal_subsets_of_balancedSeparation
    {C T Y Z : Finset V} {κ q : ℕ}
    (hYZ : BalancedSeparation G C T κ Y Z)
    (hYhalf : κ ≤ 2 * (Y ∩ T).card)
    (hq : 4 * q ≤ κ) :
    ∃ Tz Ty : Finset V,
      Tz ⊆ Z ∩ T ∧ Ty ⊆ Y ∩ T ∧ Disjoint Tz Ty ∧
        Tz.card = q ∧ Ty.card = q := by
  classical
  have hqZ : q ≤ (Z ∩ T).card := by
    have hmain := hYZ.right_balanced
    omega
  rcases Finset.exists_subset_card_eq hqZ with ⟨Tz, hTz, hTzcard⟩
  have htwoqY : 2 * q ≤ (Y ∩ T).card := by
    omega
  have hdiff_ge : q ≤ ((Y ∩ T) \ Tz).card := by
    rw [Finset.card_sdiff]
    have hinter_le : (Tz ∩ (Y ∩ T)).card ≤ q := by
      calc
        (Tz ∩ (Y ∩ T)).card ≤ Tz.card :=
          Finset.card_le_card Finset.inter_subset_left
        _ = q := hTzcard
    omega
  rcases Finset.exists_subset_card_eq hdiff_ge with ⟨Ty, hTy, hTycard⟩
  have hTyYT : Ty ⊆ Y ∩ T := by
    intro v hv
    exact (Finset.mem_sdiff.mp (hTy hv)).1
  have hdisj : Disjoint Tz Ty := by
    rw [Finset.disjoint_left]
    intro v hvZ hvY
    exact (Finset.mem_sdiff.mp (hTy hvY)).2 hvZ
  exact ⟨Tz, Ty, hTz, hTyYT, hdisj, hTzcard, hTycard⟩

/-- A variant of the side-subset selection lemma that allows the rounded-up
quarter size.  The extra hypothesis says that the overlap terminals are small
enough that, after choosing `q` terminals on the `Z` side, at least `q`
terminals remain on the `Y` side. -/
theorem exists_disjoint_terminal_subsets_of_balancedSeparation_of_overlap_bound
    {C T Y Z : Finset V} {κ q : ℕ}
    (_hYZ : BalancedSeparation G C T κ Y Z)
    (hqZ : q ≤ (Z ∩ T).card)
    (hoverlap : q + ((Y ∩ Z) ∩ T).card ≤ (Y ∩ T).card) :
    ∃ Tz Ty : Finset V,
      Tz ⊆ Z ∩ T ∧ Ty ⊆ Y ∩ T ∧ Disjoint Tz Ty ∧
        Tz.card = q ∧ Ty.card = q := by
  classical
  rcases Finset.exists_subset_card_eq hqZ with ⟨Tz, hTz, hTzcard⟩
  have hinter_le : (Tz ∩ (Y ∩ T)).card ≤ ((Y ∩ Z) ∩ T).card := by
    refine Finset.card_le_card ?_
    intro v hv
    have hvTz : v ∈ Tz := (Finset.mem_inter.mp hv).1
    have hvYT : v ∈ Y ∩ T := (Finset.mem_inter.mp hv).2
    have hvZT : v ∈ Z ∩ T := hTz hvTz
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_inter.mpr
        ⟨(Finset.mem_inter.mp hvYT).1, (Finset.mem_inter.mp hvZT).1⟩,
        (Finset.mem_inter.mp hvYT).2⟩
  have hdiff_ge : q ≤ ((Y ∩ T) \ Tz).card := by
    rw [Finset.card_sdiff]
    omega
  rcases Finset.exists_subset_card_eq hdiff_ge with ⟨Ty, hTy, hTycard⟩
  have hTyYT : Ty ⊆ Y ∩ T := by
    intro v hv
    exact (Finset.mem_sdiff.mp (hTy hv)).1
  have hdisj : Disjoint Tz Ty := by
    rw [Finset.disjoint_left]
    intro v hvZ hvY
    exact (Finset.mem_sdiff.mp (hTy hvY)).2 hvZ
  exact ⟨Tz, Ty, hTz, hTyYT, hdisj, hTzcard, hTycard⟩

/-! ## Paths crossing a separation -/

/-- Any path staying in the ambient set of a separation and going from the
right side to the left side must meet the overlap. -/
theorem GraphPath.exists_mem_overlap_of_source_mem_right_target_mem_left
    {C Y Z : Finset V} (hYZ : VertexSeparation G C Y Z)
    (P : GraphPath G) (hstay : P.vertexSet ⊆ C)
    (hsourceZ : P.source ∈ Z) (htargetY : P.target ∈ Y) :
    ∃ x ∈ P.vertexSet, x ∈ Y ∩ Z := by
  classical
  by_cases hsourceY : P.source ∈ Y
  · exact ⟨P.source, GraphPath.source_mem_vertexSet P,
      Finset.mem_inter.mpr ⟨hsourceY, hsourceZ⟩⟩
  by_cases htargetZ : P.target ∈ Z
  · exact ⟨P.target, GraphPath.target_mem_vertexSet P,
      Finset.mem_inter.mpr ⟨htargetY, htargetZ⟩⟩
  by_contra hnone
  have hno_overlap :
      ∀ ⦃x : V⦄, x ∈ P.vertexSet → x ∉ Y ∩ Z := by
    intro x hx hXZ
    exact hnone ⟨x, hx, hXZ⟩
  have hsub :
      P.vertexSet ⊆ (Z \ Y) ∪ (Y \ Z) := by
    intro x hx
    have hxC : x ∈ C := hstay hx
    have hxYZ : x ∈ Y ∪ Z := by
      rw [hYZ.cover]
      exact hxC
    rcases Finset.mem_union.mp hxYZ with hxY | hxZ
    · have hxZnot : x ∉ Z := by
        intro hxZ
        exact hno_overlap hx (Finset.mem_inter.mpr ⟨hxY, hxZ⟩)
      exact Finset.mem_union_right _
        (Finset.mem_sdiff.mpr ⟨hxY, hxZnot⟩)
    · have hxYnot : x ∉ Y := by
        intro hxY
        exact hno_overlap hx (Finset.mem_inter.mpr ⟨hxY, hxZ⟩)
      exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨hxZ, hxYnot⟩)
  have hsourceLeft : P.source ∈ Z \ Y :=
    Finset.mem_sdiff.mpr ⟨hsourceZ, hsourceY⟩
  have hnot_subset_left : ¬ P.vertexSet ⊆ Z \ Y := by
    intro hPZ
    exact htargetZ (Finset.mem_sdiff.mp (hPZ (GraphPath.target_mem_vertexSet P))).1
  rcases Section44.GraphPath.exists_edgeBoundary_of_source_mem_left_of_not_subset_left
      (G := G) (P := P) (X := Z \ Y) (Y := Y \ Z)
      hsub hsourceLeft hnot_subset_left with ⟨e, _heP, heB⟩
  rcases (Section44.mem_edgeBoundary (G := G) (Z \ Y) (Y \ Z) e).1 heB with
    ⟨heG, x, hx, y, hy, rfl⟩
  have hxy : G.Adj x y := by
    simpa [_root_.SimpleGraph.mem_edgeSet] using heG
  exact hYZ.no_cross
    (u := y) (v := x)
    (Finset.mem_sdiff.mp hy).1 (Finset.mem_sdiff.mp hy).2
    (Finset.mem_sdiff.mp hx).1 (Finset.mem_sdiff.mp hx).2
    (G.symm hxy)

omit [Fintype V] in
/-- For a path staying in a separation and going from the right side `Z` to
the left side `Y`, the first hit of `Y` lies in the overlap `Y ∩ Z`. -/
theorem GraphPath.cleanPrefixToLeft_target_mem_overlap
    {C Y Z : Finset V} (hYZ : VertexSeparation G C Y Z)
    (P : GraphPath G) (hstay : P.vertexSet ⊆ C)
    (hsourceZ : P.source ∈ Z) (hhit : (P.vertexSet ∩ Y).Nonempty) :
    (P.cleanPrefixToSet Y hhit).target ∈ Y ∩ Z := by
  classical
  have htargetY' : (P.cleanPrefixToSet Y hhit).target ∈ Y :=
    P.cleanPrefixToSet_target_mem Y hhit
  refine Finset.mem_inter.mpr ⟨htargetY', ?_⟩
  by_cases hsourceY : P.source ∈ Y
  · have hsource_prefix :
        P.source ∈ (P.cleanPrefixToSet Y hhit).vertexSet :=
      GraphPath.source_mem_vertexSet (P.cleanPrefixToSet Y hhit)
    have hfirst :
        P.source = P.firstHitVertex Y hhit :=
      P.eq_firstHitVertex_of_mem_takeUntil_of_mem_set Y hhit
        hsource_prefix hsourceY
    simpa [GraphPath.cleanPrefixToSet, hfirst.symm] using hsourceZ
  · by_contra htargetZ
    let Q := P.cleanPrefixToSet Y hhit
    have hQsourceZ : Q.source ∈ Z := by simpa [Q] using hsourceZ
    have hQsourceY : Q.source ∉ Y := by simpa [Q] using hsourceY
    have hQtargetY : Q.target ∈ Y := by
      simpa [Q] using htargetY'
    have hQtargetZ : Q.target ∉ Z := by
      simpa [Q] using htargetZ
    have hQne : Q.source ≠ Q.target := by
      intro hst
      exact hQsourceY (by simpa [hst] using hQtargetY)
    have hpen_mem : Q.penultimate ∈ Q.vertexSet :=
      Q.penultimate_mem_vertexSet hQne
    have hpen_notY : Q.penultimate ∉ Y := by
      intro hpenY
      have hQint : Q.InternallyDisjointFromSet Y := by
        simpa [Q] using P.cleanPrefixToSet_internallyDisjointFromSet Y hhit
      rcases hQint hpen_mem hpenY with hsrc | htgt
      · exact hQsourceY (by simpa [hsrc] using hpenY)
      · have hadj := Q.penultimate_adj_target hQne
        have hloop : G.Adj Q.target Q.target := by
          rw [htgt] at hadj
          exact hadj
        exact G.loopless.irrefl Q.target hloop
    have hpenC : Q.penultimate ∈ C := by
      have hpenP : Q.penultimate ∈ P.vertexSet := by
        exact P.cleanPrefixToSet_vertexSet_subset Y hhit hpen_mem
      exact hstay hpenP
    have hpenZ : Q.penultimate ∈ Z := by
      have hpenYZ : Q.penultimate ∈ Y ∪ Z := by
        rw [hYZ.cover]
        exact hpenC
      rcases Finset.mem_union.mp hpenYZ with hY | hZ
      · exact False.elim (hpen_notY hY)
      · exact hZ
    have hadj : G.Adj Q.penultimate Q.target :=
      Q.penultimate_adj_target hQne
    exact hYZ.no_cross
      (u := Q.target) (v := Q.penultimate)
      hQtargetY hQtargetZ hpenZ hpen_notY (G.symm hadj)

/-- Truncate a path packing from the right side of a separation to the left
side at the first vertex of the overlap. -/
noncomputable def truncatePackingToSeparationOverlap
    {C Y Z S T : Finset V} (hYZ : VertexSeparation G C Y Z)
    (P : PathPacking G S T) (hstay : P.StaysIn C)
    (hS : S ⊆ Z) (hT : T ⊆ Y) :
    PathPacking G S (Y ∩ Z) where
  Index := P.Index
  path := by
    intro i
    let O := P.orient.path i
    have hsourceS : O.source ∈ S := by
      simpa [O] using GraphPath.orient_source_mem (P.path i) (P.connects i)
    have htargetT : O.target ∈ T := by
      simpa [O] using GraphPath.orient_target_mem (P.path i) (P.connects i)
    have hstayO : O.vertexSet ⊆ C := by
      intro v hv
      exact hstay i (by simpa [O, PathPacking.orient_path_vertexSet] using hv)
    have hhit :
        (O.vertexSet ∩ (Y ∩ Z)).Nonempty := by
      rcases GraphPath.exists_mem_overlap_of_source_mem_right_target_mem_left
          (G := G) (C := C) (Y := Y) (Z := Z) hYZ O hstayO
          (hS hsourceS) (hT htargetT) with ⟨x, hxO, hxYZ⟩
      exact ⟨x, Finset.mem_inter.mpr ⟨hxO, hxYZ⟩⟩
    exact O.cleanPrefixToSet (Y ∩ Z) hhit
  connects := by
    intro i
    let O := P.orient.path i
    have hsourceS : O.source ∈ S := by
      simpa [O] using GraphPath.orient_source_mem (P.path i) (P.connects i)
    have htargetT : O.target ∈ T := by
      simpa [O] using GraphPath.orient_target_mem (P.path i) (P.connects i)
    have hstayO : O.vertexSet ⊆ C := by
      intro v hv
      exact hstay i (by simpa [O, PathPacking.orient_path_vertexSet] using hv)
    have hhit :
        (O.vertexSet ∩ (Y ∩ Z)).Nonempty := by
      rcases GraphPath.exists_mem_overlap_of_source_mem_right_target_mem_left
          (G := G) (C := C) (Y := Y) (Z := Z) hYZ O hstayO
          (hS hsourceS) (hT htargetT) with ⟨x, hxO, hxYZ⟩
      exact ⟨x, Finset.mem_inter.mpr ⟨hxO, hxYZ⟩⟩
    exact Or.inl
      ⟨by simpa [O] using hsourceS,
        by
          change (O.cleanPrefixToSet (Y ∩ Z) hhit).target ∈ Y ∩ Z
          exact O.cleanPrefixToSet_target_mem (Y ∩ Z) hhit⟩
  node_disjoint := by
    intro i j hij
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro v hvi hvj
    let Oi := P.orient.path i
    let Oj := P.orient.path j
    have hviO : v ∈ Oi.vertexSet := by
      exact Oi.cleanPrefixToSet_vertexSet_subset (Y ∩ Z) _ hvi
    have hvjO : v ∈ Oj.vertexSet := by
      exact Oj.cleanPrefixToSet_vertexSet_subset (Y ∩ Z) _ hvj
    exact Finset.disjoint_left.mp (P.orient.node_disjoint hij) hviO hvjO

@[simp] theorem truncatePackingToSeparationOverlap_card
    {C Y Z S T : Finset V} (hYZ : VertexSeparation G C Y Z)
    (P : PathPacking G S T) (hstay : P.StaysIn C)
    (hS : S ⊆ Z) (hT : T ⊆ Y) :
    (truncatePackingToSeparationOverlap (G := G) hYZ P hstay hS hT).card = P.card := rfl

theorem truncatePackingToSeparationOverlap_staysIn
    {C Y Z S T : Finset V} (hYZ : VertexSeparation G C Y Z)
    (P : PathPacking G S T) (hstay : P.StaysIn C)
    (hS : S ⊆ Z) (hT : T ⊆ Y) :
    (truncatePackingToSeparationOverlap (G := G) hYZ P hstay hS hT).StaysIn C := by
  classical
  intro i v hv
  let O := P.orient.path i
  have hvO : v ∈ O.vertexSet := by
    exact O.cleanPrefixToSet_vertexSet_subset (Y ∩ Z) _ hv
  exact hstay i (by simpa [O, PathPacking.orient_path_vertexSet] using hvO)

/-- The truncated prefixes meet the overlap only at their terminal endpoint. -/
theorem truncatePackingToSeparationOverlap_internallyDisjointFrom_overlap
    {C Y Z S T : Finset V} (hYZ : VertexSeparation G C Y Z)
    (P : PathPacking G S T) (hstay : P.StaysIn C)
    (hS : S ⊆ Z) (hT : T ⊆ Y) :
    (truncatePackingToSeparationOverlap (G := G) hYZ P hstay hS hT).InternallyDisjointFromSet
      (Y ∩ Z) := by
  classical
  intro i v hv hvX
  let O := P.orient.path i
  have hvPrefix :
      v ∈ (O.cleanPrefixToSet (Y ∩ Z) _).vertexSet := hv
  have hclean :=
    O.cleanPrefixToSet_internallyDisjointFromSet (Y ∩ Z) _
      hvPrefix hvX
  rcases hclean with hsource | htarget
  · exact Or.inl (by simpa [O] using hsource)
  · exact Or.inr htarget

/-- Truncate a path packing from the right side of a separation to the first
vertex in the left side.  The separation property forces that first left-side
vertex to lie in the overlap, while the resulting prefixes are internally
disjoint from the whole left side `Y`. -/
noncomputable def truncatePackingToSeparationLeft
    {C Y Z S T : Finset V} (hYZ : VertexSeparation G C Y Z)
    (P : PathPacking G S T) (hstay : P.StaysIn C)
    (hS : S ⊆ Z) (hT : T ⊆ Y) :
    PathPacking G S (Y ∩ Z) where
  Index := P.Index
  path := by
    intro i
    let O := P.orient.path i
    have htargetT : O.target ∈ T := by
      simpa [O] using GraphPath.orient_target_mem (P.path i) (P.connects i)
    have hhit : (O.vertexSet ∩ Y).Nonempty :=
      ⟨O.target, Finset.mem_inter.mpr
        ⟨GraphPath.target_mem_vertexSet O, hT htargetT⟩⟩
    exact O.cleanPrefixToSet Y hhit
  connects := by
    intro i
    let O := P.orient.path i
    have hsourceS : O.source ∈ S := by
      simpa [O] using GraphPath.orient_source_mem (P.path i) (P.connects i)
    have htargetT : O.target ∈ T := by
      simpa [O] using GraphPath.orient_target_mem (P.path i) (P.connects i)
    have hstayO : O.vertexSet ⊆ C := by
      intro v hv
      exact hstay i (by simpa [O, PathPacking.orient_path_vertexSet] using hv)
    have hhit : (O.vertexSet ∩ Y).Nonempty :=
      ⟨O.target, Finset.mem_inter.mpr
        ⟨GraphPath.target_mem_vertexSet O, hT htargetT⟩⟩
    exact Or.inl
      ⟨by simpa [O] using hsourceS,
        GraphPath.cleanPrefixToLeft_target_mem_overlap
          (G := G) hYZ O hstayO (hS hsourceS) hhit⟩
  node_disjoint := by
    intro i j hij
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro v hvi hvj
    let Oi := P.orient.path i
    let Oj := P.orient.path j
    have hviO : v ∈ Oi.vertexSet := by
      exact Oi.cleanPrefixToSet_vertexSet_subset Y _ hvi
    have hvjO : v ∈ Oj.vertexSet := by
      exact Oj.cleanPrefixToSet_vertexSet_subset Y _ hvj
    exact Finset.disjoint_left.mp (P.orient.node_disjoint hij) hviO hvjO

omit [Fintype V] in
@[simp] theorem truncatePackingToSeparationLeft_card
    {C Y Z S T : Finset V} (hYZ : VertexSeparation G C Y Z)
    (P : PathPacking G S T) (hstay : P.StaysIn C)
    (hS : S ⊆ Z) (hT : T ⊆ Y) :
    (truncatePackingToSeparationLeft (G := G) hYZ P hstay hS hT).card = P.card := rfl

omit [Fintype V] in
theorem truncatePackingToSeparationLeft_staysIn
    {C Y Z S T : Finset V} (hYZ : VertexSeparation G C Y Z)
    (P : PathPacking G S T) (hstay : P.StaysIn C)
    (hS : S ⊆ Z) (hT : T ⊆ Y) :
    (truncatePackingToSeparationLeft (G := G) hYZ P hstay hS hT).StaysIn C := by
  classical
  intro i v hv
  let O := P.orient.path i
  have hvO : v ∈ O.vertexSet := by
    exact O.cleanPrefixToSet_vertexSet_subset Y _ hv
  exact hstay i (by simpa [O, PathPacking.orient_path_vertexSet] using hvO)

omit [Fintype V] in
/-- The left-side truncation enters `Y` only at its terminal endpoint. -/
theorem truncatePackingToSeparationLeft_internallyDisjointFrom_left
    {C Y Z S T : Finset V} (hYZ : VertexSeparation G C Y Z)
    (P : PathPacking G S T) (hstay : P.StaysIn C)
    (hS : S ⊆ Z) (hT : T ⊆ Y) :
    (truncatePackingToSeparationLeft (G := G) hYZ P hstay hS hT).InternallyDisjointFromSet
      Y := by
  classical
  intro i v hv hvY
  let O := P.orient.path i
  have hhit : (O.vertexSet ∩ Y).Nonempty := by
    have htargetT : O.target ∈ T := by
      simpa [O] using GraphPath.orient_target_mem (P.path i) (P.connects i)
    exact ⟨O.target, Finset.mem_inter.mpr
      ⟨GraphPath.target_mem_vertexSet O, hT htargetT⟩⟩
  exact O.cleanPrefixToSet_internallyDisjointFromSet Y hhit hv hvY

omit [Fintype V] in
/-- If a truncated source already lies in `Y`, then the left-side truncation is
trivial up to its target. -/
theorem truncatePackingToSeparationLeft_source_mem_left_eq_target
    {C Y Z S T : Finset V} (hYZ : VertexSeparation G C Y Z)
    (P : PathPacking G S T) (hstay : P.StaysIn C)
    (hS : S ⊆ Z) (hT : T ⊆ Y) :
    ∀ i : (truncatePackingToSeparationLeft (G := G) hYZ P hstay hS hT).Index,
      (((truncatePackingToSeparationLeft (G := G) hYZ P hstay hS hT).orient.path i).source ∈ Y) →
        ((truncatePackingToSeparationLeft (G := G) hYZ P hstay hS hT).orient.path i).source =
          ((truncatePackingToSeparationLeft (G := G) hYZ P hstay hS hT).orient.path i).target := by
  classical
  intro i hsourceY
  let Q := truncatePackingToSeparationLeft (G := G) hYZ P hstay hS hT
  let O := P.orient.path i
  have hsourceS : O.source ∈ S := by
    simpa [O] using GraphPath.orient_source_mem (P.path i) (P.connects i)
  have htargetT : O.target ∈ T := by
    simpa [O] using GraphPath.orient_target_mem (P.path i) (P.connects i)
  have hstayO : O.vertexSet ⊆ C := by
    intro v hv
    exact hstay i (by simpa [O, PathPacking.orient_path_vertexSet] using hv)
  have hhit : (O.vertexSet ∩ Y).Nonempty :=
    ⟨O.target, Finset.mem_inter.mpr
      ⟨GraphPath.target_mem_vertexSet O, hT htargetT⟩⟩
  have hst :
      (Q.path i).source ∈ S ∧ (Q.path i).target ∈ Y ∩ Z := by
    exact ⟨by simpa [Q, truncatePackingToSeparationLeft, O] using hsourceS,
      by
        simpa [Q, truncatePackingToSeparationLeft, O] using
          GraphPath.cleanPrefixToLeft_target_mem_overlap
            (G := G) hYZ O hstayO (hS hsourceS) hhit⟩
  have horient :
      Q.orient.path i = Q.path i := by
    change (Q.path i).orient (Q.connects i) = Q.path i
    rw [GraphPath.orient, if_pos hst]
  have hsourceY_Q : (Q.path i).source ∈ Y := by
    rw [← horient]
    exact hsourceY
  have hsourceY' : O.source ∈ Y := by
    simpa [Q, truncatePackingToSeparationLeft, O] using hsourceY_Q
  have hsource_prefix :
      O.source ∈ (O.cleanPrefixToSet Y hhit).vertexSet :=
    GraphPath.source_mem_vertexSet (O.cleanPrefixToSet Y hhit)
  have hfirst :
      O.source = O.firstHitVertex Y hhit :=
    O.eq_firstHitVertex_of_mem_takeUntil_of_mem_set Y hhit
      hsource_prefix hsourceY'
  change (Q.orient.path i).source = (Q.orient.path i).target
  rw [horient]
  change (O.cleanPrefixToSet Y hhit).source =
    (O.cleanPrefixToSet Y hhit).target
  simp [GraphPath.cleanPrefixToSet, hfirst.symm]

/-- Flow routing across a separation, followed by truncation at the first
overlap vertex.  This is the formal version of the paragraph in the
nonconstructive proof that routes from `T₁' ⊆ Z` to `T₂' ⊆ Y` and then
truncates every path to its first vertex in `X = Y ∩ Z`. -/
theorem exists_truncated_paths_to_overlap_of_scaledEdgeWellLinkedIn
    {C Y Z Terminals Tz Ty : Finset V} {alphaNum alphaDen Δ k : ℕ}
    (hYZ : VertexSeparation G C Y Z)
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (hwell : Section46.ScaledEdgeWellLinkedIn G C Terminals alphaNum alphaDen)
    (hTzTerminals : Tz ⊆ Terminals)
    (hTyTerminals : Ty ⊆ Terminals)
    (hTzZ : Tz ⊆ Z)
    (hTyY : Ty ⊆ Y)
    (hcard : Tz.card = Ty.card)
    (hk : 10 * Δ * alphaDen * k ≤ 3 * alphaNum * Tz.card) :
    ∃ P : PathPacking G Tz (Y ∩ Z), k ≤ P.card ∧ P.StaysIn C := by
  classical
  rcases Section46.exists_pathPacking_staysIn_of_scaledEdgeWellLinkedIn
      (G := G) (C := C) (Terminals := Terminals) (S := Tz) (T := Ty)
      (alphaNum := alphaNum) (alphaDen := alphaDen) (Δ := Δ) (k := k)
      hdegree hDelta hwell hTzTerminals hTyTerminals hcard hk with
    ⟨P, hPcard, hPstay⟩
  let Q := truncatePackingToSeparationOverlap
    (G := G) hYZ P hPstay hTzZ hTyY
  refine ⟨Q, ?_, ?_⟩
  · simpa [Q] using hPcard
  · simpa [Q] using
      truncatePackingToSeparationOverlap_staysIn
        (G := G) hYZ P hPstay hTzZ hTyY

/-- Exact-size version of
`exists_truncated_paths_to_overlap_of_scaledEdgeWellLinkedIn`, obtained by
discarding all but `k` truncated paths. -/
theorem exists_exact_truncated_paths_to_overlap_of_scaledEdgeWellLinkedIn
    {C Y Z Terminals Tz Ty : Finset V} {alphaNum alphaDen Δ k : ℕ}
    (hYZ : VertexSeparation G C Y Z)
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (hwell : Section46.ScaledEdgeWellLinkedIn G C Terminals alphaNum alphaDen)
    (hTzTerminals : Tz ⊆ Terminals)
    (hTyTerminals : Ty ⊆ Terminals)
    (hTzZ : Tz ⊆ Z)
    (hTyY : Ty ⊆ Y)
    (hcard : Tz.card = Ty.card)
    (hk : 10 * Δ * alphaDen * k ≤ 3 * alphaNum * Tz.card) :
    ∃ P : PathPacking G Tz (Y ∩ Z),
      P.card = k ∧ P.StaysIn C ∧ P.InternallyDisjointFromSet (Y ∩ Z) := by
  classical
  rcases Section46.exists_pathPacking_staysIn_of_scaledEdgeWellLinkedIn
      (G := G) (C := C) (Terminals := Terminals) (S := Tz) (T := Ty)
      (alphaNum := alphaNum) (alphaDen := alphaDen) (Δ := Δ) (k := k)
      hdegree hDelta hwell hTzTerminals hTyTerminals hcard hk with
    ⟨P₀, hP₀card, hP₀stay⟩
  let P := truncatePackingToSeparationOverlap
    (G := G) hYZ P₀ hP₀stay hTzZ hTyY
  have hPcard : k ≤ P.card := by
    simpa [P] using hP₀card
  rcases P.exists_indexSet_card_eq hPcard with ⟨I, _hIcard, hrestrict_card⟩
  let Q := P.restrictIndexSet I
  refine ⟨Q, by simpa [Q] using hrestrict_card, ?_, ?_⟩
  · intro i v hv
    exact truncatePackingToSeparationOverlap_staysIn
      (G := G) hYZ P₀ hP₀stay hTzZ hTyY i.1 hv
  · have hPint : P.InternallyDisjointFromSet (Y ∩ Z) := by
      simpa [P] using
        truncatePackingToSeparationOverlap_internallyDisjointFrom_overlap
          (G := G) hYZ P₀ hP₀stay hTzZ hTyY
    intro i v hv hvX
    exact hPint i.1 hv hvX

/-- Sharpened exact-size truncated routing across a separation, for disjoint
source and target terminal subsets.  This is the form with the constants from
Chekuri--Chuzhoy Theorem 2.14. -/
theorem exists_exact_truncated_paths_to_overlap_of_scaledEdgeWellLinkedIn_disjoint
    {C Y Z Terminals Tz Ty : Finset V} {alphaNum alphaDen Δ k : ℕ}
    (hYZ : VertexSeparation G C Y Z)
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (hwell : Section46.ScaledEdgeWellLinkedIn G C Terminals alphaNum alphaDen)
    (hTzTerminals : Tz ⊆ Terminals)
    (hTyTerminals : Ty ⊆ Terminals)
    (hTzZ : Tz ⊆ Z)
    (hTyY : Ty ⊆ Y)
    (hcard : Tz.card = Ty.card)
    (hdisj : Disjoint Tz Ty)
    (hk : 5 * Δ * alphaDen * k ≤ 6 * alphaNum * Tz.card) :
    ∃ P : PathPacking G Tz (Y ∩ Z),
      P.card = k ∧ P.StaysIn C ∧ P.InternallyDisjointFromSet (Y ∩ Z) := by
  classical
  rcases Section46.exists_pathPacking_staysIn_of_scaledEdgeWellLinkedIn_disjoint
      (G := G) (C := C) (Terminals := Terminals) (S := Tz) (T := Ty)
      (alphaNum := alphaNum) (alphaDen := alphaDen) (Δ := Δ) (k := k)
      hdegree hDelta hwell hTzTerminals hTyTerminals hcard hdisj hk with
    ⟨P₀, hP₀card, hP₀stay⟩
  let P := truncatePackingToSeparationOverlap
    (G := G) hYZ P₀ hP₀stay hTzZ hTyY
  have hPcard : k ≤ P.card := by
    simpa [P] using hP₀card
  rcases P.exists_indexSet_card_eq hPcard with ⟨I, _hIcard, hrestrict_card⟩
  let Q := P.restrictIndexSet I
  refine ⟨Q, by simpa [Q] using hrestrict_card, ?_, ?_⟩
  · intro i v hv
    exact truncatePackingToSeparationOverlap_staysIn
      (G := G) hYZ P₀ hP₀stay hTzZ hTyY i.1 hv
  · have hPint : P.InternallyDisjointFromSet (Y ∩ Z) := by
      simpa [P] using
        truncatePackingToSeparationOverlap_internallyDisjointFrom_overlap
          (G := G) hYZ P₀ hP₀stay hTzZ hTyY
    intro i v hv hvX
    exact hPint i.1 hv hvX

omit [Fintype V] in
/-- Exact-size routed prefixes obtained by stopping an existing path packing
at the first vertex of the left side.  These prefixes are internally disjoint
from `Y`, not just from the overlap. -/
theorem exists_exact_left_truncated_paths_to_overlap_of_pathPacking
    {C Y Z Tz Ty : Finset V} {k : ℕ}
    (hYZ : VertexSeparation G C Y Z)
    (P₀ : PathPacking G Tz Ty)
    (hP₀card : k ≤ P₀.card)
    (hP₀stay : P₀.StaysIn C)
    (hTzZ : Tz ⊆ Z)
    (hTyY : Ty ⊆ Y) :
    ∃ P : PathPacking G Tz (Y ∩ Z),
      P.card = k ∧ P.StaysIn C ∧ P.InternallyDisjointFromSet Y ∧
        (∀ i : P.Index,
          (P.orient.path i).source ∈ Y →
            (P.orient.path i).source = (P.orient.path i).target) := by
  classical
  let P := truncatePackingToSeparationLeft
    (G := G) hYZ P₀ hP₀stay hTzZ hTyY
  have hPcard : k ≤ P.card := by
    simpa [P] using hP₀card
  rcases P.exists_indexSet_card_eq hPcard with ⟨I, _hIcard, hrestrict_card⟩
  let Q := P.restrictIndexSet I
  refine ⟨Q, by simpa [Q] using hrestrict_card, ?_, ?_, ?_⟩
  · intro i v hv
    exact truncatePackingToSeparationLeft_staysIn
      (G := G) hYZ P₀ hP₀stay hTzZ hTyY i.1 hv
  · have hPint : P.InternallyDisjointFromSet Y := by
      simpa [P] using
        truncatePackingToSeparationLeft_internallyDisjointFrom_left
          (G := G) hYZ P₀ hP₀stay hTzZ hTyY
    intro i v hv hvY
    exact hPint i.1 hv hvY
  · have hPsource :=
      truncatePackingToSeparationLeft_source_mem_left_eq_target
        (G := G) hYZ P₀ hP₀stay hTzZ hTyY
    intro i hiY
    exact hPsource i.1 (by simpa [Q, P, PathPacking.restrictIndexSet] using hiY)

/-- Exact-size routed prefixes obtained by stopping at the first vertex of the
left side, starting from the scaled well-linkedness routing theorem. -/
theorem exists_exact_left_truncated_paths_to_overlap_of_scaledEdgeWellLinkedIn_disjoint
    {C Y Z Terminals Tz Ty : Finset V} {alphaNum alphaDen Δ k : ℕ}
    (hYZ : VertexSeparation G C Y Z)
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (hwell : Section46.ScaledEdgeWellLinkedIn G C Terminals alphaNum alphaDen)
    (hTzTerminals : Tz ⊆ Terminals)
    (hTyTerminals : Ty ⊆ Terminals)
    (hTzZ : Tz ⊆ Z)
    (hTyY : Ty ⊆ Y)
    (hcard : Tz.card = Ty.card)
    (hdisj : Disjoint Tz Ty)
    (hk : 5 * Δ * alphaDen * k ≤ 6 * alphaNum * Tz.card) :
    ∃ P : PathPacking G Tz (Y ∩ Z),
      P.card = k ∧ P.StaysIn C ∧ P.InternallyDisjointFromSet Y ∧
        (∀ i : P.Index,
          (P.orient.path i).source ∈ Y →
            (P.orient.path i).source = (P.orient.path i).target) := by
  classical
  rcases Section46.exists_pathPacking_staysIn_of_scaledEdgeWellLinkedIn_disjoint
      (G := G) (C := C) (Terminals := Terminals) (S := Tz) (T := Ty)
      (alphaNum := alphaNum) (alphaDen := alphaDen) (Δ := Δ) (k := k)
      hdegree hDelta hwell hTzTerminals hTyTerminals hcard hdisj hk with
    ⟨P₀, hP₀card, hP₀stay⟩
  let P := truncatePackingToSeparationLeft
    (G := G) hYZ P₀ hP₀stay hTzZ hTyY
  have hPcard : k ≤ P.card := by
    simpa [P] using hP₀card
  rcases P.exists_indexSet_card_eq hPcard with ⟨I, _hIcard, hrestrict_card⟩
  let Q := P.restrictIndexSet I
  refine ⟨Q, by simpa [Q] using hrestrict_card, ?_, ?_, ?_⟩
  · intro i v hv
    exact truncatePackingToSeparationLeft_staysIn
      (G := G) hYZ P₀ hP₀stay hTzZ hTyY i.1 hv
  · have hPint : P.InternallyDisjointFromSet Y := by
      simpa [P] using
        truncatePackingToSeparationLeft_internallyDisjointFrom_left
          (G := G) hYZ P₀ hP₀stay hTzZ hTyY
    intro i v hv hvY
    exact hPint i.1 hv hvY
  · have hPsource :=
      truncatePackingToSeparationLeft_source_mem_left_eq_target
        (G := G) hYZ P₀ hP₀stay hTzZ hTyY
    intro i hiY
    exact hPsource i.1 (by simpa [Q, P, PathPacking.restrictIndexSet] using hiY)

omit [Fintype V] in
/-- Node-well-linkedness remains true when the allowed ambient region is
enlarged. -/
theorem nodeWellLinkedIn_mono_region
    {C D T : Finset V}
    (h : NodeWellLinkedIn G C T) (hCD : C ⊆ D) :
    NodeWellLinkedIn G D T := by
  refine ⟨subset_trans h.1 hCD, ?_⟩
  intro A B hA hB hdisj
  rcases h.2 hA hB hdisj with ⟨P, hPcard, hPstay⟩
  exact ⟨P, hPcard, fun i v hv => hCD (hPstay i hv)⟩

omit [Fintype V] in
/-- Pull node-well-linkedness back through a disjoint linkage.

The linkage `P` runs from a set of source terminals to a node-well-linked
target set inside `Y`.  Its paths stay in the ambient region `C`, are
internally disjoint from `Y`, and if a source already lies in `Y` then the
corresponding linkage path is trivial up to its target.  Under these
hypotheses the used source terminals are node-well-linked in `C`.

This is the formal version of the final "pull back along the truncated
prefixes" step in Chekuri--Chuzhoy Theorem 2.14. -/
theorem nodeWellLinkedIn_sourceSet_of_linkage_to_nodeWellLinked
    {C Y S X : Finset V}
    (P : PathPacking G S X)
    (hPstay : P.StaysIn C)
    (hPintY : P.InternallyDisjointFromSet Y)
    (hsource_only :
      ∀ i : P.Index,
        (P.orient.path i).source ∈ Y →
          (P.orient.path i).source = (P.orient.path i).target)
    (hYC : Y ⊆ C)
    (hXnode : NodeWellLinkedIn G Y P.targetSet) :
    NodeWellLinkedIn G C P.sourceSet := by
  classical
  let L := P.toPerfectUsedTerminals
  have hLintY : L.toPathPacking.InternallyDisjointFromSet Y := by
    change P.orient.InternallyDisjointFromSet Y
    exact PathPacking.orient_internallyDisjointFromSet hPintY
  have hLstayC : L.toPathPacking.StaysIn C := by
    change P.orient.StaysIn C
    exact PathPacking.orient_staysIn hPstay
  have hLsource_only :
      ∀ i : L.Index,
        (L.path i).source ∈ Y → (L.path i).source = (L.path i).target := by
    intro i hiY
    exact hsource_only i hiY
  have hsourceC : P.sourceSet ⊆ C := by
    intro v hv
    rcases P.exists_orient_source_eq_of_mem_sourceSet hv with ⟨i, rfl⟩
    exact hLstayC i (GraphPath.source_mem_vertexSet (L.path i))
  refine ⟨hsourceC, ?_⟩
  intro A B hA hB hAB
  have hlink_equal :
      ∀ ⦃A₀ B₀ : Finset V⦄,
        A₀ ⊆ P.sourceSet → B₀ ⊆ P.sourceSet → Disjoint A₀ B₀ →
          A₀.card = B₀.card →
            ∃ Q : PathPacking G A₀ B₀, Q.card = A₀.card ∧ Q.StaysIn C := by
    intro A₀ B₀ hA₀ hB₀ hA₀B₀ hcard_eq
    let RA := L.restrictSourceSet A₀ hA₀
    let RB := L.restrictSourceSet B₀ hB₀
    let XA := L.targetSet (L.sourceIndexSetOfSubset A₀)
    let XB := L.targetSet (L.sourceIndexSetOfSubset B₀)
    have hXA_X : XA ⊆ P.targetSet := by
      simpa [L, XA] using
        L.targetSet_subset_right (L.sourceIndexSetOfSubset A₀)
    have hXB_X : XB ⊆ P.targetSet := by
      simpa [L, XB] using
        L.targetSet_subset_right (L.sourceIndexSetOfSubset B₀)
    have hXA_Y : XA ⊆ Y := subset_trans hXA_X hXnode.1
    have hXB_Y : XB ⊆ Y := subset_trans hXB_X hXnode.1
    have hXA_card : XA.card = A₀.card := by
      simpa [XA] using L.sourceIndexSetOfSubset_card (S' := A₀) hA₀
    have hXB_card : XB.card = B₀.card := by
      simpa [XB] using L.sourceIndexSetOfSubset_card (S' := B₀) hB₀
    have hXA_XB : Disjoint XA XB := by
      rw [Finset.disjoint_left]
      intro v hvA hvB
      rcases Finset.mem_image.mp hvA with ⟨i, hiA, hiv⟩
      rcases Finset.mem_image.mp hvB with ⟨j, hjB, hjv⟩
      have hij : i = j := by
        apply L.target_bijective.1
        apply Subtype.ext
        exact hiv.trans hjv.symm
      have hsrcA : (L.path i).source ∈ A₀ :=
        (L.mem_sourceIndexSetOfSubset A₀ i).mp hiA
      have hsrcB : (L.path i).source ∈ B₀ := by
        simpa [hij] using (L.mem_sourceIndexSetOfSubset B₀ j).mp hjB
      exact Finset.disjoint_left.mp hA₀B₀ hsrcA hsrcB
    rcases hXnode.2 hXA_X hXB_X hXA_XB with ⟨Qpack, hQcard, hQstayY⟩
    have hQcard_XA : Qpack.card = XA.card := by
      have hcards : XA.card = XB.card := by omega
      simpa [hcards] using hQcard
    have hQcard_XB : Qpack.card = XB.card := by
      have hcards : XA.card = XB.card := by omega
      simpa [hcards] using hQcard
    let Qmid := Qpack.toPerfectOfCardEq hQcard_XA hQcard_XB
    have hQmidStayY : Qmid.toPathPacking.StaysIn Y := by
      change Qpack.orient.StaysIn Y
      exact PathPacking.orient_staysIn hQstayY
    have hRAintY : RA.toPathPacking.InternallyDisjointFromSet Y := by
      intro i v hv hvY
      exact hLintY i.1 hv hvY
    have hRBintY : RB.toPathPacking.InternallyDisjointFromSet Y := by
      intro i v hv hvY
      exact hLintY i.1 hv hvY
    have hRBrevIntY : RB.reverse.toPathPacking.InternallyDisjointFromSet Y := by
      intro i v hv hvY
      have hrev :=
        (GraphPath.reverse_internallyDisjointFromSet (RB.path i) Y).2
          (hRBintY i)
      exact hrev hv hvY
    have hRBrevStayRB :
        RB.reverse.toPathPacking.StaysIn RB.toPathPacking.vertexSet := by
      intro i v hv
      exact (RB.toPathPacking.mem_vertexSet).2 ⟨i, by simpa using hv⟩
    have htail_target_only :
        ∀ i : Qmid.Index, ∀ j : RB.reverse.Index,
          (RB.reverse.path j).target ∈ (Qmid.path i).vertexSet →
            (RB.reverse.path j).target = (RB.reverse.path j).source := by
      intro i j hmem
      have hYmem : (RB.reverse.path j).target ∈ Y :=
        hQmidStayY i hmem
      have htriv : (RB.path j).source = (RB.path j).target :=
        hLsource_only j.1 hYmem
      simpa [PerfectPathPacking.reverse] using htriv
    let Tail :=
      Qmid.concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource
        RB.reverse hQmidStayY hRBrevIntY htail_target_only
    let A₂ := Y ∪ RB.toPathPacking.vertexSet
    have hTailStayA₂ : Tail.toPathPacking.StaysIn A₂ := by
      simpa [Tail, A₂] using
        Qmid.concatOfFirstStaysInSecondInternallyDisjointTargetOnlyAtSource_staysIn_union
          RB.reverse hQmidStayY hRBrevIntY htail_target_only hRBrevStayRB
    have hRBvertexC : RB.toPathPacking.vertexSet ⊆ C := by
      intro v hv
      rcases (RB.toPathPacking.mem_vertexSet).1 hv with ⟨i, hvi⟩
      exact hLstayC i.1 hvi
    have hA₂C : A₂ ⊆ C := by
      intro v hv
      rcases Finset.mem_union.mp hv with hvY | hvRB
      · exact hYC hvY
      · exact hRBvertexC hvRB
    have hRA_RB_disjoint :
        ∀ i : RA.Index, ∀ j : RB.Index,
          Disjoint (RA.path i).vertexSet (RB.path j).vertexSet := by
      intro i j
      have hij : i.1 ≠ j.1 := by
        intro heq
        have hsrc_eq : (RA.path i).source = (RB.path j).source := by
          change (L.path i.1).source = (L.path j.1).source
          exact congrArg (fun k : L.Index => (L.path k).source) heq
        have hsrcA : (RA.path i).source ∈ A₀ := RA.source_mem i
        have hsrcB : (RA.path i).source ∈ B₀ := by
          simpa [hsrc_eq] using RB.source_mem j
        exact Finset.disjoint_left.mp hA₀B₀ hsrcA hsrcB
      exact L.toPathPacking.node_disjoint hij
    have hRAintA₂ : RA.toPathPacking.InternallyDisjointFromSet A₂ := by
      intro i v hv hvA₂
      rcases Finset.mem_union.mp hvA₂ with hvY | hvRB
      · exact hRAintY i hv hvY
      · rcases (RB.toPathPacking.mem_vertexSet).1 hvRB with ⟨j, hvj⟩
        exact False.elim
          (Finset.disjoint_left.mp (hRA_RB_disjoint i j) hv hvj)
    have hfull_source_only :
        ∀ i : RA.Index, ∀ j : Tail.Index,
          (RA.path i).source ∈ (Tail.path j).vertexSet →
            (RA.path i).source = (RA.path i).target := by
      intro i j hmem
      have hA₂mem : (RA.path i).source ∈ A₂ :=
        hTailStayA₂ j hmem
      rcases Finset.mem_union.mp hA₂mem with hYmem | hRBmem
      · exact hLsource_only i.1 hYmem
      · rcases (RB.toPathPacking.mem_vertexSet).1 hRBmem with ⟨k, hvk⟩
        have hdisj := hRA_RB_disjoint i k
        exact False.elim
          (Finset.disjoint_left.mp hdisj
            (GraphPath.source_mem_vertexSet (RA.path i)) hvk)
    let Full :=
      RA.concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget
        Tail hRAintA₂ hTailStayA₂ hfull_source_only
    refine ⟨Full.toPathPacking, ?_, ?_⟩
    · simp [Full, RA]
    · have hFullStay : Full.toPathPacking.StaysIn (C ∪ A₂) := by
        simpa [Full] using
          RA.concatOfFirstInternallyDisjointSecondStaysInSourceOnlyAtTarget_staysIn_union
            Tail hRAintA₂ hTailStayA₂ hfull_source_only
            (by
              intro i v hv
              exact hLstayC i.1 hv)
      intro i v hv
      have hvCA₂ : v ∈ C ∪ A₂ := hFullStay i hv
      rcases Finset.mem_union.mp hvCA₂ with hvC | hvA₂
      · exact hvC
      · exact hA₂C hvA₂
  by_cases hle : A.card ≤ B.card
  · rcases Finset.exists_subset_card_eq hle with ⟨B₀, hB₀B, hB₀card⟩
    have hAB₀ : Disjoint A B₀ := hAB.mono_right hB₀B
    rcases hlink_equal hA (subset_trans hB₀B hB) hAB₀ hB₀card.symm with
      ⟨Q, hQcard, hQstay⟩
    refine ⟨Q.widenTerminals subset_rfl hB₀B, ?_, ?_⟩
    · simp [hQcard, Nat.min_eq_left hle]
    · intro i
      exact hQstay i
  · have hle' : B.card ≤ A.card := Nat.le_of_not_ge hle
    rcases Finset.exists_subset_card_eq hle' with ⟨A₀, hA₀A, hA₀card⟩
    have hA₀B : Disjoint A₀ B := hAB.mono_left hA₀A
    rcases hlink_equal (subset_trans hA₀A hA) hB hA₀B hA₀card with
      ⟨Q, hQcard, hQstay⟩
    refine ⟨Q.widenTerminals hA₀A subset_rfl, ?_, ?_⟩
    · simp [hQcard, hA₀card, Nat.min_eq_right hle']
    · intro i
      exact hQstay i

omit [Fintype V] in
/-- The target vertices reached by a truncated packing form an exact-size
node-well-linked subset of the separation overlap. -/
theorem exists_nodeWellLinked_overlap_subset_of_truncated_paths
    {C Y Z Tz : Finset V} {k : ℕ}
    (hYC : Y ⊆ C)
    (hnode : NodeWellLinkedIn G Y (Y ∩ Z))
    (P : PathPacking G Tz (Y ∩ Z))
    (hPcard : P.card = k) :
    ∃ X' : Finset V,
      X' ⊆ Y ∩ Z ∧ X'.card = k ∧ NodeWellLinkedIn G C X' := by
  classical
  let X' := P.targetSet
  have hX' : X' ⊆ Y ∩ Z := by
    simpa [X'] using P.targetSet_subset_right
  have hX'card : X'.card = k := by
    simp [X', hPcard]
  have hnodeX' : NodeWellLinkedIn G Y X' :=
    hnode.mono_terminals hX'
  exact ⟨X', hX', hX'card, nodeWellLinkedIn_mono_region hnodeX' hYC⟩

/-- Combining sharpened routing with truncation gives a node-well-linked subset
of the separator overlap.  This is the part of Theorem 2.14 that is completely
inside the minimum-separation side; the final paper step transfers this
well-linkedness back to original terminals using the truncated prefix linkage. -/
theorem exists_nodeWellLinked_overlap_subset_of_scaledEdgeWellLinkedIn_disjoint
    {C Y Z Terminals Tz Ty : Finset V} {alphaNum alphaDen Δ k : ℕ}
    (hYZ : VertexSeparation G C Y Z)
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (hwell : Section46.ScaledEdgeWellLinkedIn G C Terminals alphaNum alphaDen)
    (hnode : NodeWellLinkedIn G Y (Y ∩ Z))
    (hTzTerminals : Tz ⊆ Terminals)
    (hTyTerminals : Ty ⊆ Terminals)
    (hTzZ : Tz ⊆ Z)
    (hTyY : Ty ⊆ Y)
    (hcard : Tz.card = Ty.card)
    (hdisj : Disjoint Tz Ty)
    (hk : 5 * Δ * alphaDen * k ≤ 6 * alphaNum * Tz.card) :
    ∃ X' : Finset V,
      X' ⊆ Y ∩ Z ∧ X'.card = k ∧ NodeWellLinkedIn G C X' := by
  classical
  rcases exists_exact_truncated_paths_to_overlap_of_scaledEdgeWellLinkedIn_disjoint
      (G := G) (C := C) (Y := Y) (Z := Z) (Terminals := Terminals)
      (Tz := Tz) (Ty := Ty) (alphaNum := alphaNum) (alphaDen := alphaDen)
      (Δ := Δ) (k := k)
      hYZ hdegree hDelta hwell hTzTerminals hTyTerminals hTzZ hTyY hcard hdisj hk with
    ⟨P, hPcard, _hPstay, _hPint⟩
  exact exists_nodeWellLinked_overlap_subset_of_truncated_paths
    (G := G) (C := C) (Y := Y) (Z := Z) (Tz := Tz) (k := k)
    hYZ.left_subset hnode P hPcard

/-- Sharpened routed-prefix version of the final step in Theorem 2.14: after
routing from terminals on the `Z` side to terminals on the `Y` side, the used
`Z`-side terminals themselves form a node-well-linked set. -/
theorem exists_nodeWellLinked_terminal_subset_of_scaledEdgeWellLinkedIn_disjoint
    {C Y Z Terminals Tz Ty : Finset V} {alphaNum alphaDen Δ k : ℕ}
    (hYZ : VertexSeparation G C Y Z)
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (hwell : Section46.ScaledEdgeWellLinkedIn G C Terminals alphaNum alphaDen)
    (hnode : NodeWellLinkedIn G Y (Y ∩ Z))
    (hTzTerminals : Tz ⊆ Terminals)
    (hTyTerminals : Ty ⊆ Terminals)
    (hTzZ : Tz ⊆ Z)
    (hTyY : Ty ⊆ Y)
    (hcard : Tz.card = Ty.card)
    (hdisj : Disjoint Tz Ty)
    (hk : 5 * Δ * alphaDen * k ≤ 6 * alphaNum * Tz.card) :
    ∃ T' : Finset V,
      T' ⊆ Terminals ∧ T'.card = k ∧ NodeWellLinkedIn G C T' := by
  classical
  rcases exists_exact_left_truncated_paths_to_overlap_of_scaledEdgeWellLinkedIn_disjoint
      (G := G) (C := C) (Y := Y) (Z := Z) (Terminals := Terminals)
      (Tz := Tz) (Ty := Ty) (alphaNum := alphaNum) (alphaDen := alphaDen)
      (Δ := Δ) (k := k)
      hYZ hdegree hDelta hwell hTzTerminals hTyTerminals hTzZ hTyY
      hcard hdisj hk with
    ⟨P, hPcard, hPstay, hPintY, hPsource⟩
  let T' := P.sourceSet
  have hT'sub : T' ⊆ Terminals := by
    intro v hv
    exact hTzTerminals (P.sourceSet_subset_left hv)
  have hT'card : T'.card = k := by
    simp [T', hPcard]
  have htarget_node : NodeWellLinkedIn G Y P.targetSet :=
    hnode.mono_terminals P.targetSet_subset_right
  have hT'node : NodeWellLinkedIn G C T' := by
    simpa [T'] using
      nodeWellLinkedIn_sourceSet_of_linkage_to_nodeWellLinked
        (G := G) (C := C) (Y := Y) (S := Tz) (X := Y ∩ Z)
        P hPstay hPintY hPsource hYZ.left_subset htarget_node
  exact ⟨T', hT'sub, hT'card, hT'node⟩

omit [Fintype V] in
/-- If the separation overlap already contains `k` original terminals, then a
`k`-subset of those terminals is node-well-linked in the ambient cluster. -/
theorem exists_nodeWellLinked_terminal_subset_of_large_overlap
    {C Y Z T : Finset V} {k : ℕ}
    (hYC : Y ⊆ C)
    (hnode : NodeWellLinkedIn G Y (Y ∩ Z))
    (hk : k ≤ ((Y ∩ Z) ∩ T).card) :
    ∃ T' : Finset V,
      T' ⊆ T ∧ T'.card = k ∧ NodeWellLinkedIn G C T' := by
  classical
  rcases Finset.exists_subset_card_eq hk with ⟨T', hT', hT'card⟩
  have hT'subT : T' ⊆ T := by
    intro v hv
    exact (Finset.mem_inter.mp (hT' hv)).2
  have hT'subOverlap : T' ⊆ Y ∩ Z := by
    intro v hv
    exact (Finset.mem_inter.mp (hT' hv)).1
  have hnodeT' : NodeWellLinkedIn G Y T' :=
    hnode.mono_terminals hT'subOverlap
  exact ⟨T', hT'subT, hT'card, nodeWellLinkedIn_mono_region hnodeT' hYC⟩

omit [Fintype V] in
/-- Any requested subset size at most three can be realized inside a connected
cluster, because terminal sets of cardinality at most three are
node-well-linked. -/
theorem exists_nodeWellLinked_terminal_subset_of_card_le_three
    {C T : Finset V} {m : ℕ}
    (hcluster : IsCluster G C)
    (hTC : T ⊆ C)
    (hmT : m ≤ T.card)
    (hm3 : m ≤ 3) :
    ∃ T' : Finset V, T' ⊆ T ∧ T'.card = m ∧ NodeWellLinkedIn G C T' := by
  classical
  rcases Finset.exists_subset_card_eq hmT with ⟨T', hT'T, hT'card⟩
  have hT'C : T' ⊆ C := subset_trans hT'T hTC
  have hT'card_le : T'.card ≤ 3 := by
    simpa [hT'card] using hm3
  exact ⟨T', hT'T, hT'card,
    Section46.nodeWellLinkedIn_of_card_le_three_of_isCluster hcluster hT'C hT'card_le⟩

/-- The rounded-up quarter `⌈κ / 4⌉`, written as a natural-number expression. -/
private def ceilQuarter (κ : ℕ) : ℕ :=
  (κ + 3) / 4

private theorem ceilQuarter_le_of_four_mul {κ n : ℕ} (h : κ ≤ 4 * n) :
    ceilQuarter κ ≤ n := by
  unfold ceilQuarter
  apply Nat.lt_succ_iff.mp
  rw [Nat.div_lt_iff_lt_mul (by norm_num : (0 : ℕ) < 4)]
  omega

private theorem le_four_mul_ceilQuarter (κ : ℕ) :
    κ ≤ 4 * ceilQuarter κ := by
  unfold ceilQuarter
  omega

private theorem theorem214_floorTarget_le_kappa
    {alphaNum alphaDen Δ κ : ℕ}
    (hDelta : 3 ≤ Δ)
    (_halpha_pos : 0 < alphaNum)
    (halpha_le : alphaNum ≤ alphaDen) :
    (3 * alphaNum * κ) / (10 * Δ * alphaDen) ≤ κ := by
  apply Nat.div_le_of_le_mul
  have hcoef : 3 * alphaNum ≤ 10 * Δ * alphaDen := by
    nlinarith
  calc
    3 * alphaNum * κ ≤ (10 * Δ * alphaDen) * κ :=
      Nat.mul_le_mul_right κ hcoef

private theorem theorem214_route_floor_of_quarter
    {alphaNum alphaDen Δ κ q : ℕ}
    (hκq : κ ≤ 4 * q) :
    5 * Δ * alphaDen * ((3 * alphaNum * κ) / (10 * Δ * alphaDen)) ≤
      6 * alphaNum * q := by
  let k := (3 * alphaNum * κ) / (10 * Δ * alphaDen)
  have hdiv :
      k * (10 * Δ * alphaDen) ≤ 3 * alphaNum * κ := by
    simpa [k] using Nat.div_mul_le_self (3 * alphaNum * κ) (10 * Δ * alphaDen)
  have hleft :
      2 * (5 * Δ * alphaDen * k) ≤ 3 * alphaNum * κ := by
    calc
      2 * (5 * Δ * alphaDen * k) = k * (10 * Δ * alphaDen) := by ring
      _ ≤ 3 * alphaNum * κ := hdiv
  have hright :
      3 * alphaNum * κ ≤ 2 * (6 * alphaNum * q) := by
    calc
      3 * alphaNum * κ ≤ 3 * alphaNum * (4 * q) :=
        Nat.mul_le_mul_left (3 * alphaNum) hκq
      _ = 2 * (6 * alphaNum * q) := by ring
  exact Nat.le_of_mul_le_mul_left (hleft.trans hright) (by norm_num : 0 < 2)

private theorem theorem214_two_mul_ceilQuarter_add_floorTarget_le
    {alphaNum alphaDen Δ κ : ℕ}
    (hDelta : 3 ≤ Δ)
    (halpha_pos : 0 < alphaNum)
    (halpha_le : alphaNum ≤ alphaDen)
    (hlarge : 3 < (3 * alphaNum * κ) / (10 * Δ * alphaDen)) :
    2 * (ceilQuarter κ + (3 * alphaNum * κ) / (10 * Δ * alphaDen)) ≤ κ := by
  let k := (3 * alphaNum * κ) / (10 * Δ * alphaDen)
  let q := ceilQuarter κ
  have h4q : 4 * q ≤ κ + 3 := by
    unfold q ceilQuarter
    have h := Nat.div_mul_le_self (κ + 3) 4
    simpa [Nat.mul_comm] using h
  have hD_ge : 30 * alphaNum ≤ 10 * Δ * alphaDen := by
    nlinarith
  have hdiv :
      k * (10 * Δ * alphaDen) ≤ 3 * alphaNum * κ := by
    simpa [k] using Nat.div_mul_le_self (3 * alphaNum * κ) (10 * Δ * alphaDen)
  have hleft_ge : 30 * alphaNum * k ≤ k * (10 * Δ * alphaDen) := by
    calc
      30 * alphaNum * k = k * (30 * alphaNum) := by ring
      _ ≤ k * (10 * Δ * alphaDen) := Nat.mul_le_mul_left k hD_ge
  have h30 : 30 * alphaNum * k ≤ 3 * alphaNum * κ :=
    hleft_ge.trans hdiv
  have h10k : 10 * k ≤ κ := by
    nlinarith
  have hκ40 : 40 ≤ κ := by
    omega
  change 2 * (q + k) ≤ κ
  omega

private theorem theorem214_two_mul_ceilQuarter_add_edgeFloor_le
    {Δ κ : ℕ}
    (hDelta : 3 ≤ Δ)
    (hlarge : 3 < κ / (4 * Δ)) :
    2 * (ceilQuarter κ + κ / (4 * Δ)) ≤ κ := by
  let k := κ / (4 * Δ)
  let q := ceilQuarter κ
  have h4q : 4 * q ≤ κ + 3 := by
    unfold q ceilQuarter
    have h := Nat.div_mul_le_self (κ + 3) 4
    simpa [Nat.mul_comm] using h
  have h4Dk : 4 * Δ * k ≤ κ := by
    have h := Nat.div_mul_le_self κ (4 * Δ)
    simpa [k, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
  have hk4 : 4 ≤ k := by
    simpa [k] using hlarge
  have h12k : 12 * k ≤ κ := by
    have h12_le : 12 * k ≤ 4 * Δ * k := by
      nlinarith
    exact h12_le.trans h4Dk
  have hκ48 : 48 ≤ κ := by
    nlinarith
  change 2 * (q + k) ≤ κ
  omega

/-- Theorem 2.14 in the branch where a three-terminal set is already large
enough for the desired lower bound. -/
theorem theorem214_nodeWellLinkedSubset_of_bound_le_three
    {C T : Finset V} {alphaNum alphaDen Δ κ : ℕ}
    (hcluster : IsCluster G C)
    (hDelta : 3 ≤ Δ)
    (_halpha_pos : 0 < alphaNum)
    (halpha_le : alphaNum ≤ alphaDen)
    (hcard : T.card = κ)
    (hwell : Section46.ScaledEdgeWellLinkedIn G C T alphaNum alphaDen)
    (hbound3 : 3 * alphaNum * κ ≤ 10 * Δ * alphaDen * 3) :
    ∃ T' : Finset V,
      T' ⊆ T ∧
        3 * alphaNum * κ ≤ 10 * Δ * alphaDen * T'.card ∧
          NodeWellLinkedIn G C T' := by
  classical
  by_cases hκ3 : κ ≤ 3
  · rcases Section46.theorem420_nodeWellLinkedBoosting_of_card_le_three
      (G := G) (C := C) (T := T) (alphaNum := alphaNum)
      (alphaDen := alphaDen) (Δ := Δ) (κ := κ)
      hcluster hDelta (by
        have hpos := hwell.1
        exact hpos) halpha_le hcard hwell hκ3 with
      ⟨T', hT'T, hineq, hnode⟩
    exact ⟨T', hT'T, hineq, hnode⟩
  · have h3κ : 3 ≤ κ := by omega
    have h3T : 3 ≤ T.card := by simpa [hcard] using h3κ
    rcases exists_nodeWellLinked_terminal_subset_of_card_le_three
        (G := G) (C := C) (T := T) (m := 3)
        hcluster hwell.2.2.1 h3T le_rfl with
      ⟨T', hT'T, hT'card, hnode⟩
    refine ⟨T', hT'T, ?_, hnode⟩
    simpa [hT'card] using hbound3

/-- Parameterized nonconstructive core of Chekuri--Chuzhoy Theorem 2.14.

The remaining numerical step in the paper is to choose `q` and `k` satisfying
the displayed routing inequality.  Once those parameters are available, the
minimum-separation and routing argument produces exactly `k` node-well-linked
terminals. -/
theorem theorem214_nodeWellLinkedSubset_card_of_parameters
    {C T : Finset V} {alphaNum alphaDen Δ κ q k : ℕ}
    (_hcluster : IsCluster G C)
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (_halpha_pos : 0 < alphaNum)
    (_halpha_le : alphaNum ≤ alphaDen)
    (hcard : T.card = κ)
    (hwell : Section46.ScaledEdgeWellLinkedIn G C T alphaNum alphaDen)
    (hq : 4 * q ≤ κ)
    (hk_route : 5 * Δ * alphaDen * k ≤ 6 * alphaNum * q) :
    ∃ T' : Finset V,
      T' ⊆ T ∧ T'.card = k ∧ NodeWellLinkedIn G C T' := by
  classical
  have hTC : T ⊆ C := hwell.2.2.1
  rcases exists_minimum_balancedSeparation_overlap_nodeWellLinked
      (G := G) (C := C) (T := T) (κ := κ) hTC hcard with
    ⟨Y, Z, hYZ, _hmin, hYhalf, hnode⟩
  rcases exists_disjoint_terminal_subsets_of_balancedSeparation
      (G := G) (C := C) (T := T) (Y := Y) (Z := Z) (κ := κ) (q := q)
      hYZ hYhalf hq with
    ⟨Tz, Ty, hTzZT, hTyYT, hdisj, hTzcard, hTycard⟩
  have hTzT : Tz ⊆ T := by
    intro v hv
    exact (Finset.mem_inter.mp (hTzZT hv)).2
  have hTyT : Ty ⊆ T := by
    intro v hv
    exact (Finset.mem_inter.mp (hTyYT hv)).2
  have hTzZ : Tz ⊆ Z := by
    intro v hv
    exact (Finset.mem_inter.mp (hTzZT hv)).1
  have hTyY : Ty ⊆ Y := by
    intro v hv
    exact (Finset.mem_inter.mp (hTyYT hv)).1
  have hTzTy_card : Tz.card = Ty.card := by
    rw [hTzcard, hTycard]
  have hk_route' : 5 * Δ * alphaDen * k ≤ 6 * alphaNum * Tz.card := by
    simpa [hTzcard] using hk_route
  rcases exists_nodeWellLinked_terminal_subset_of_scaledEdgeWellLinkedIn_disjoint
      (G := G) (C := C) (Y := Y) (Z := Z) (Terminals := T)
      (Tz := Tz) (Ty := Ty) (alphaNum := alphaNum) (alphaDen := alphaDen)
      (Δ := Δ) (k := k)
      hYZ.toVertexSeparation hdegree hDelta hwell hnode hTzT hTyT
      hTzZ hTyY hTzTy_card hdisj hk_route' with
    ⟨T', hT'T, hT'card, hT'node⟩
  exact ⟨T', hT'T, hT'card, hT'node⟩

/-- Parameterized nonconstructive form of Chekuri--Chuzhoy Theorem 2.14 with
an externally supplied target-size lower bound. -/
theorem theorem214_nodeWellLinkedSubset_of_parameters
    {C T : Finset V} {alphaNum alphaDen Δ κ q k : ℕ}
    (hcluster : IsCluster G C)
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (halpha_pos : 0 < alphaNum)
    (halpha_le : alphaNum ≤ alphaDen)
    (hcard : T.card = κ)
    (hwell : Section46.ScaledEdgeWellLinkedIn G C T alphaNum alphaDen)
    (hq : 4 * q ≤ κ)
    (hk_route : 5 * Δ * alphaDen * k ≤ 6 * alphaNum * q)
    (hk_goal : 3 * alphaNum * κ ≤ 10 * Δ * alphaDen * k) :
    ∃ T' : Finset V,
      T' ⊆ T ∧
        3 * alphaNum * κ ≤ 10 * Δ * alphaDen * T'.card ∧
          NodeWellLinkedIn G C T' := by
  classical
  rcases theorem214_nodeWellLinkedSubset_card_of_parameters
      (G := G) (C := C) (T := T) (alphaNum := alphaNum)
      (alphaDen := alphaDen) (Δ := Δ) (κ := κ) (q := q) (k := k)
      hcluster hdegree hDelta halpha_pos halpha_le hcard hwell hq hk_route with
    ⟨T', hT'T, hT'card, hT'node⟩
  refine ⟨T', hT'T, ?_, hT'node⟩
  simpa [hT'card] using hk_goal

/-- Chekuri--Chuzhoy Theorem 2.14 with the paper's hidden integer rounding
made explicit: the guaranteed subset has size at least
`⌊3 * alphaNum * κ / (10 * Δ * alphaDen)⌋`.

The proof uses the rounded-up quarter `ceilQuarter κ` for the two routed
terminal sides.  When too many terminals lie in the minimum-separation
overlap, the overlap itself supplies the desired node-well-linked subset;
otherwise the overlap is small enough that the rounded-up quarter subsets can
be chosen disjointly. -/
theorem theorem214_nodeWellLinkedSubset_floor
    {C T : Finset V} {alphaNum alphaDen Δ κ : ℕ}
    (hcluster : IsCluster G C)
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (halpha_pos : 0 < alphaNum)
    (halpha_le : alphaNum ≤ alphaDen)
    (hcard : T.card = κ)
    (hwell : Section46.ScaledEdgeWellLinkedIn G C T alphaNum alphaDen) :
    ∃ T' : Finset V,
      T' ⊆ T ∧
        (3 * alphaNum * κ) / (10 * Δ * alphaDen) ≤ T'.card ∧
          NodeWellLinkedIn G C T' := by
  classical
  let k := (3 * alphaNum * κ) / (10 * Δ * alphaDen)
  by_cases hk3 : k ≤ 3
  · have hkT : k ≤ T.card := by
      simpa [k, hcard] using
        theorem214_floorTarget_le_kappa
          (alphaNum := alphaNum) (alphaDen := alphaDen) (Δ := Δ) (κ := κ)
          hDelta halpha_pos halpha_le
    rcases exists_nodeWellLinked_terminal_subset_of_card_le_three
        (G := G) (C := C) (T := T) (m := k)
        hcluster hwell.2.2.1 hkT hk3 with
      ⟨T', hT'T, hT'card, hnode⟩
    exact ⟨T', hT'T, by simp [k, hT'card], hnode⟩
  · have hklarge : 3 < k := Nat.lt_of_not_ge hk3
    have hTC : T ⊆ C := hwell.2.2.1
    rcases exists_minimum_balancedSeparation_overlap_nodeWellLinked
        (G := G) (C := C) (T := T) (κ := κ) hTC hcard with
      ⟨Y, Z, hYZ, _hmin, hYhalf, hnode⟩
    let Xterm := (Y ∩ Z) ∩ T
    by_cases hover : k ≤ Xterm.card
    · rcases exists_nodeWellLinked_terminal_subset_of_large_overlap
          (G := G) (C := C) (Y := Y) (Z := Z) (T := T) (k := k)
          hYZ.left_subset hnode (by simpa [Xterm] using hover) with
        ⟨T', hT'T, hT'card, hT'node⟩
      exact ⟨T', hT'T, by simp [k, hT'card], hT'node⟩
    · have hxlt : Xterm.card < k := Nat.lt_of_not_ge hover
      let q := ceilQuarter κ
      have hqZ : q ≤ (Z ∩ T).card := by
        exact ceilQuarter_le_of_four_mul (κ := κ) (n := (Z ∩ T).card)
          hYZ.right_balanced
      have h2qk : 2 * (q + k) ≤ κ := by
        simpa [q, k] using
          theorem214_two_mul_ceilQuarter_add_floorTarget_le
            (alphaNum := alphaNum) (alphaDen := alphaDen) (Δ := Δ) (κ := κ)
            hDelta halpha_pos halpha_le (by simpa [k] using hklarge)
      have hoverlap_bound : q + Xterm.card ≤ (Y ∩ T).card := by
        have hxle : Xterm.card ≤ k := Nat.le_of_lt hxlt
        have h2qx : 2 * (q + Xterm.card) ≤ κ := by
          omega
        have h2qxY : 2 * (q + Xterm.card) ≤ 2 * (Y ∩ T).card :=
          h2qx.trans hYhalf
        exact Nat.le_of_mul_le_mul_left h2qxY (by norm_num : 0 < 2)
      rcases exists_disjoint_terminal_subsets_of_balancedSeparation_of_overlap_bound
          (G := G) (C := C) (T := T) (Y := Y) (Z := Z) (κ := κ) (q := q)
          hYZ hqZ (by simpa [Xterm] using hoverlap_bound) with
        ⟨Tz, Ty, hTzZT, hTyYT, hdisj, hTzcard, hTycard⟩
      have hTzT : Tz ⊆ T := by
        intro v hv
        exact (Finset.mem_inter.mp (hTzZT hv)).2
      have hTyT : Ty ⊆ T := by
        intro v hv
        exact (Finset.mem_inter.mp (hTyYT hv)).2
      have hTzZ : Tz ⊆ Z := by
        intro v hv
        exact (Finset.mem_inter.mp (hTzZT hv)).1
      have hTyY : Ty ⊆ Y := by
        intro v hv
        exact (Finset.mem_inter.mp (hTyYT hv)).1
      have hTzTy_card : Tz.card = Ty.card := by
        rw [hTzcard, hTycard]
      have hk_route : 5 * Δ * alphaDen * k ≤ 6 * alphaNum * Tz.card := by
        have hκq : κ ≤ 4 * q := by
          simpa [q] using le_four_mul_ceilQuarter κ
        simpa [k, hTzcard] using
          theorem214_route_floor_of_quarter
            (alphaNum := alphaNum) (alphaDen := alphaDen) (Δ := Δ)
            (κ := κ) (q := q) hκq
      rcases exists_nodeWellLinked_terminal_subset_of_scaledEdgeWellLinkedIn_disjoint
          (G := G) (C := C) (Y := Y) (Z := Z) (Terminals := T)
          (Tz := Tz) (Ty := Ty) (alphaNum := alphaNum) (alphaDen := alphaDen)
          (Δ := Δ) (k := k)
          hYZ.toVertexSeparation hdegree hDelta hwell hnode hTzT hTyT
          hTzZ hTyY hTzTy_card hdisj hk_route with
        ⟨T', hT'T, hT'card, hT'node⟩
      exact ⟨T', hT'T, by simp [k, hT'card], hT'node⟩

/-- A fully self-contained `α = 1` edge-well-linked boosting theorem with a
slightly weaker constant.

It is not the Chekuri--Chuzhoy flow constant `3/(10Δ)`: it avoids fractional
max-flow/min-cut entirely by using the path-based edge-well-linkedness
definition, finite vertex-Menger, and the maximum-degree counting lemma.
The guaranteed size is `⌊κ / (4Δ)⌋`. -/
theorem theorem214_nodeWellLinkedSubset_of_edgeWellLinked_floor
    {C T : Finset V} {Δ κ : ℕ}
    (hcluster : IsCluster G C)
    (hdegree : MaxDegreeAtMost G Δ)
    (hDelta : 3 ≤ Δ)
    (hcard : T.card = κ)
    (hwell : EdgeWellLinkedIn G C T) :
    ∃ T' : Finset V,
      T' ⊆ T ∧ κ / (4 * Δ) ≤ T'.card ∧ NodeWellLinkedIn G C T' := by
  classical
  let k := κ / (4 * Δ)
  by_cases hk3 : k ≤ 3
  · have hkT : k ≤ T.card := by
      simpa [k, hcard] using Nat.div_le_self κ (4 * Δ)
    rcases exists_nodeWellLinked_terminal_subset_of_card_le_three
        (G := G) (C := C) (T := T) (m := k)
        hcluster hwell.1 hkT hk3 with
      ⟨T', hT'T, hT'card, hnode⟩
    exact ⟨T', hT'T, by simp [k, hT'card], hnode⟩
  · have hklarge : 3 < k := Nat.lt_of_not_ge hk3
    have hTC : T ⊆ C := hwell.1
    rcases exists_minimum_balancedSeparation_overlap_nodeWellLinked
        (G := G) (C := C) (T := T) (κ := κ) hTC hcard with
      ⟨Y, Z, hYZ, _hmin, hYhalf, hnode⟩
    let Xterm := (Y ∩ Z) ∩ T
    by_cases hover : k ≤ Xterm.card
    · rcases exists_nodeWellLinked_terminal_subset_of_large_overlap
          (G := G) (C := C) (Y := Y) (Z := Z) (T := T) (k := k)
          hYZ.left_subset hnode (by simpa [Xterm] using hover) with
        ⟨T', hT'T, hT'card, hT'node⟩
      exact ⟨T', hT'T, by simp [k, hT'card], hT'node⟩
    · have hxlt : Xterm.card < k := Nat.lt_of_not_ge hover
      let q := ceilQuarter κ
      have hqZ : q ≤ (Z ∩ T).card := by
        exact ceilQuarter_le_of_four_mul (κ := κ) (n := (Z ∩ T).card)
          hYZ.right_balanced
      have h2qk : 2 * (q + k) ≤ κ := by
        simpa [q, k] using
          theorem214_two_mul_ceilQuarter_add_edgeFloor_le
            (Δ := Δ) (κ := κ) hDelta (by simpa [k] using hklarge)
      have hoverlap_bound : q + Xterm.card ≤ (Y ∩ T).card := by
        have hxle : Xterm.card ≤ k := Nat.le_of_lt hxlt
        have h2qx : 2 * (q + Xterm.card) ≤ κ := by
          omega
        have h2qxY : 2 * (q + Xterm.card) ≤ 2 * (Y ∩ T).card :=
          h2qx.trans hYhalf
        exact Nat.le_of_mul_le_mul_left h2qxY (by norm_num : 0 < 2)
      rcases exists_disjoint_terminal_subsets_of_balancedSeparation_of_overlap_bound
          (G := G) (C := C) (T := T) (Y := Y) (Z := Z) (κ := κ) (q := q)
          hYZ hqZ (by simpa [Xterm] using hoverlap_bound) with
        ⟨Tz, Ty, hTzZT, hTyYT, hdisj, hTzcard, hTycard⟩
      have hTzT : Tz ⊆ T := by
        intro v hv
        exact (Finset.mem_inter.mp (hTzZT hv)).2
      have hTyT : Ty ⊆ T := by
        intro v hv
        exact (Finset.mem_inter.mp (hTyYT hv)).2
      have hTzZ : Tz ⊆ Z := by
        intro v hv
        exact (Finset.mem_inter.mp (hTzZT hv)).1
      have hTyY : Ty ⊆ Y := by
        intro v hv
        exact (Finset.mem_inter.mp (hTyYT hv)).1
      have hTzTy_card : Tz.card = Ty.card := by
        rw [hTzcard, hTycard]
      have hk_route : Δ * k ≤ Tz.card := by
        have h4Dk : 4 * (Δ * k) ≤ κ := by
          have h := Nat.div_mul_le_self κ (4 * Δ)
          simpa [k, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using h
        have hκq : κ ≤ 4 * q := by
          simpa [q] using le_four_mul_ceilQuarter κ
        have h4Dk_q : 4 * (Δ * k) ≤ 4 * q := h4Dk.trans hκq
        have hDkq : Δ * k ≤ q :=
          Nat.le_of_mul_le_mul_left h4Dk_q (by norm_num : 0 < 4)
        simpa [hTzcard] using hDkq
      rcases Section46.exists_pathPacking_staysIn_of_edgeWellLinkedIn_disjoint
          (G := G) (C := C) (Terminals := T) (S := Tz) (T := Ty)
          (Δ := Δ) (k := k)
          hdegree (by omega : 0 < Δ) hwell hTzT hTyT hTzTy_card hdisj hk_route with
        ⟨P₀, hP₀card, hP₀stay⟩
      rcases exists_exact_left_truncated_paths_to_overlap_of_pathPacking
          (G := G) hYZ.toVertexSeparation P₀ hP₀card hP₀stay hTzZ hTyY with
        ⟨P, hPcard, hPstay, hPintY, hPsource⟩
      let T' := P.sourceSet
      have hT'sub : T' ⊆ T := by
        intro v hv
        exact hTzT (P.sourceSet_subset_left hv)
      have hT'card : T'.card = k := by
        simp [T', hPcard]
      have htarget_node : NodeWellLinkedIn G Y P.targetSet :=
        hnode.mono_terminals P.targetSet_subset_right
      have hT'node : NodeWellLinkedIn G C T' := by
        simpa [T'] using
          nodeWellLinkedIn_sourceSet_of_linkage_to_nodeWellLinked
            (G := G) (C := C) (Y := Y) (S := Tz) (X := Y ∩ Z)
            P hPstay hPintY hPsource hYZ.left_subset htarget_node
      exact ⟨T', hT'sub, by simp [k, hT'card], hT'node⟩

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
