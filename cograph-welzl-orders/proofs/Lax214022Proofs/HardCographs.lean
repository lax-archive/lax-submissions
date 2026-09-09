import Lax214022Proofs.CotreeSequence
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Prod

/-!
# The ternary family of hard cographs

Start with one vertex. At every round take three disjoint copies of the previous
graph, add no edges between the copies, and add one universal root. This is
the transitive closure of the complete rooted ternary tree of the given
height. Its order satisfies the useful coarse bounds between powers of three
and four.
-/

namespace Lax214022Proofs.HardCographs

open Lax48Proofs.Main
open Lax214022Proofs.Cotree
open Lax214022Proofs.CotreeSequence

noncomputable section

/-- Vertices of the height-k hard cograph. -/
def Vertex : ℕ → Type
  | 0 => Fin 1
  | k + 1 => Option (Fin 3 × Vertex k)

instance vertexDecidableEq (k : ℕ) : DecidableEq (Vertex k) := by
  induction k with
  | zero => simp only [Vertex]; infer_instance
  | succ k ih =>
      simp only [Vertex]
      letI : DecidableEq (Vertex k) := ih
      infer_instance

instance vertexFintype (k : ℕ) : Fintype (Vertex k) := by
  induction k with
  | zero => simp only [Vertex]; infer_instance
  | succ k ih =>
      simp only [Vertex]
      letI : Fintype (Vertex k) := ih
      infer_instance

/-- The universal-root/three-disjoint-copies recurrence. -/
def graph : (k : ℕ) → SimpleGraph (Vertex k)
  | 0 => ⊥
  | k + 1 =>
      { Adj := fun x y =>
          match x, y with
          | none, none => False
          | none, some _ => True
          | some _, none => True
          | some (i, u), some (j, v) => i = j ∧ (graph k).Adj u v
        symm := by
          intro x y
          cases x with
          | none => cases y <;> simp
          | some x =>
              rcases x with ⟨i, u⟩
              cases y with
              | none => simp
              | some y =>
                  rcases y with ⟨j, v⟩
                  simp only
                  rintro ⟨hij, huv⟩
                  exact ⟨hij.symm, huv.symm⟩
        loopless := by
          constructor
          intro x
          cases x with
          | none => simp
          | some x =>
              rcases x with ⟨i, u⟩
              simp only
              rintro ⟨-, huu⟩
              exact (graph k).irrefl huu }

@[simp] theorem graph_zero_adj (u v : Vertex 0) : ¬ (graph 0).Adj u v := by
  simp [graph]

@[simp] theorem graph_root_root (k : ℕ) :
    ¬ (graph (k + 1)).Adj none none := by simp [graph]

@[simp] theorem graph_root_branch (k : ℕ) (i : Fin 3) (v : Vertex k) :
    (graph (k + 1)).Adj none (some (i, v)) := by simp [graph]

@[simp] theorem graph_branch_root (k : ℕ) (i : Fin 3) (v : Vertex k) :
    (graph (k + 1)).Adj (some (i, v)) none := by simp [graph]

@[simp] theorem graph_branch_branch (k : ℕ) (i j : Fin 3) (u v : Vertex k) :
    (graph (k + 1)).Adj (some (i, u)) (some (j, v)) ↔
      i = j ∧ (graph k).Adj u v := by rfl

namespace CotreeMap

variable {A B : Type}

def map (f : A → B) : Tree A → Tree B
  | Tree.leaf v => Tree.leaf (f v)
  | Tree.node joined l r => Tree.node joined (map f l) (map f r)

@[simp] theorem leaves_map (f : A → B) (t : Tree A) :
    (map f t).leaves = t.leaves.map f := by
  induction t <;> simp_all [map]

@[simp] theorem leafSet_map [DecidableEq A] [DecidableEq B]
    (f : A → B) (t : Tree A) :
    (map f t).leafSet = t.leafSet.image f := by
  ext x
  simp only [Tree.leafSet, leaves_map, List.mem_toFinset, List.mem_map,
    Finset.mem_image]

theorem mem_leafSet_map_iff [DecidableEq A] [DecidableEq B]
    (f : A → B) (t : Tree A) (x : B) :
    x ∈ (map f t).leafSet ↔ ∃ a ∈ t.leafSet, f a = x := by
  simp [Tree.leafSet, leaves_map]

end CotreeMap

/-- A binary refinement of the natural 4-ary cotree node: one joined root
and three mutually disjoint recursive branches. -/
def cotree : (k : ℕ) → Tree (Vertex k)
  | 0 => Tree.leaf ⟨0, by omega⟩
  | k + 1 =>
      Tree.node true (Tree.leaf none)
        (Tree.node false
          (CotreeMap.map (fun v => some (0, v)) (cotree k))
          (Tree.node false
            (CotreeMap.map (fun v => some (1, v)) (cotree k))
            (CotreeMap.map (fun v => some (2, v)) (cotree k))))

theorem leafSet_cotree (k : ℕ) : (cotree k).leafSet = Finset.univ := by
  induction k with
  | zero =>
      ext v
      fin_cases v
      simp [cotree]
  | succ k ih =>
      ext x
      cases x with
      | none => simp [cotree]
      | some x =>
          rcases x with ⟨i, v⟩
          fin_cases i <;> simp [cotree, ih]

private theorem represents_map_branch (k : ℕ) (i : Fin 3)
    {t : Tree (Vertex k)} (h : t.Represents (graph k)) :
    (CotreeMap.map (fun v => some (i, v)) t).Represents
      (graph (k + 1)) := by
  induction t with
  | leaf v => simp [CotreeMap.map, Tree.Represents]
  | node joined l r ihl ihr =>
      simp only [Tree.Represents] at h ⊢
      refine ⟨ihl h.1, ihr h.2.1, ?_, ?_⟩
      · rw [Finset.disjoint_left]
        intro x hxl hxr
        obtain ⟨a, ha, hax⟩ :=
          (CotreeMap.mem_leafSet_map_iff _ _ _).mp hxl
        obtain ⟨b, hb, hbx⟩ :=
          (CotreeMap.mem_leafSet_map_iff _ _ _).mp hxr
        have hab : a = b :=
          congrArg Prod.snd (Option.some.inj (hax.trans hbx.symm))
        exact Finset.disjoint_left.mp h.2.2.1 ha (hab ▸ hb)
      · by_cases hj : joined = true
        · rw [if_pos hj] at h ⊢
          intro a ha b hb
          obtain ⟨a, hal, rfl⟩ :=
            (CotreeMap.mem_leafSet_map_iff _ _ _).mp ha
          obtain ⟨b, hbr, rfl⟩ :=
            (CotreeMap.mem_leafSet_map_iff _ _ _).mp hb
          exact ⟨rfl, h.2.2.2 a hal b hbr⟩
        · rw [if_neg hj] at h ⊢
          intro a ha b hb
          obtain ⟨a, hal, rfl⟩ :=
            (CotreeMap.mem_leafSet_map_iff _ _ _).mp ha
          obtain ⟨b, hbr, rfl⟩ :=
            (CotreeMap.mem_leafSet_map_iff _ _ _).mp hb
          intro hab
          exact h.2.2.2 a hal b hbr hab.2

private theorem branch_images_disjoint (k : ℕ) {i j : Fin 3} (hij : i ≠ j)
    (A B : Finset (Vertex k)) :
    Disjoint (A.image fun v => some (i, v))
      (B.image fun v => some (j, v)) := by
  rw [Finset.disjoint_left]
  intro x hxA hxB
  simp only [Finset.mem_image] at hxA hxB
  obtain ⟨a, ha, hxa⟩ := hxA
  obtain ⟨b, hb, hxb⟩ := hxB
  apply hij
  exact congrArg (fun z => z.1) (Option.some.inj (hxa.trans hxb.symm))

theorem represents_cotree (k : ℕ) : (cotree k).Represents (graph k) := by
  induction k with
  | zero => simp [cotree, Tree.Represents]
  | succ k ih =>
      have h0 := represents_map_branch k 0 ih
      have h1 := represents_map_branch k 1 ih
      have h2 := represents_map_branch k 2 ih
      simp only [cotree, Tree.Represents]
      refine ⟨by simp, ?_⟩
      refine ⟨⟨h0, ⟨h1, h2, ?_, ?_⟩, ?_, ?_⟩, ?_, ?_⟩
      · simpa only [CotreeMap.leafSet_map] using
          branch_images_disjoint k (by decide : (1 : Fin 3) ≠ 2)
            (cotree k).leafSet (cotree k).leafSet
      · intro a ha b hb
        simp only [CotreeMap.leafSet_map, Finset.mem_image] at ha hb
        obtain ⟨a, ha, rfl⟩ := ha
        obtain ⟨b, hb, rfl⟩ := hb
        simp
      · simp only [Tree.leafSet_node]
        rw [Finset.disjoint_union_right]
        constructor
        · simpa only [CotreeMap.leafSet_map] using
            branch_images_disjoint k (by decide : (0 : Fin 3) ≠ 1)
              (cotree k).leafSet (cotree k).leafSet
        · simpa only [CotreeMap.leafSet_map] using
            branch_images_disjoint k (by decide : (0 : Fin 3) ≠ 2)
              (cotree k).leafSet (cotree k).leafSet
      · intro a ha b hb
        simp only [Tree.leafSet_node, CotreeMap.leafSet_map, Finset.mem_image,
          Finset.mem_union] at ha hb
        obtain ⟨a, ha, rfl⟩ := ha
        rcases hb with ⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩ <;> simp
      · rw [Finset.disjoint_left]
        intro x hx hnone
        simp only [Tree.leafSet_leaf, Finset.mem_singleton] at hx
        subst x
        simp only [Tree.leafSet_node, CotreeMap.leafSet_map,
          Finset.mem_union, Finset.mem_image] at hnone
        rcases hnone with ⟨v, hv, h⟩ | ⟨v, hv, h⟩ | ⟨v, hv, h⟩ <;>
          simp at h
      · intro a ha b hb
        simp only [Tree.leafSet_leaf, Finset.mem_singleton] at ha
        subst a
        simp only [Tree.leafSet_node, CotreeMap.leafSet_map,
          Finset.mem_union, Finset.mem_image] at hb
        rcases hb with ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩ <;>
          simp

theorem isCograph_graph (k : ℕ) : Lax214022.Cographs.IsCograph (graph k) := by
  exact hasTwinWidthAtMost_zero_of_represents (leafSet_cotree k)
    (represents_cotree k)

@[simp] theorem card_vertex_zero : Fintype.card (Vertex 0) = 1 := by
  simp [Vertex]

@[simp] theorem card_vertex_succ (k : ℕ) :
    Fintype.card (Vertex (k + 1)) = 1 + 3 * Fintype.card (Vertex k) := by
  change Fintype.card (Option (Fin 3 × Vertex k)) =
    1 + 3 * Fintype.card (Vertex k)
  rw [Fintype.card_option, Fintype.card_prod, Fintype.card_fin]
  omega

theorem three_pow_le_card_vertex (k : ℕ) : 3 ^ k ≤ Fintype.card (Vertex k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [card_vertex_succ, Nat.pow_succ]
      omega

theorem card_vertex_le_four_pow (k : ℕ) : Fintype.card (Vertex k) ≤ 4 ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [card_vertex_succ, Nat.pow_succ]
      have hpos : 0 < 4 ^ k := Nat.pow_pos (by omega)
      omega

end

end Lax214022Proofs.HardCographs
