import Lax185574Proofs.ResolveRam.Glue.FarW
import Lax185574Proofs.ResolveRam.Expand

/-!
The expansion of an item on words.

The glue program computes the expansion `exAt` of a tree from the word
`X` of its root and the answers `C` of the compositions, one per member
of the filtered far tree. `exW` lists, as words `g :: toWord c` of a
guard and a child: the old extensions (their words are the extension
words of the root with the header of the child put in front of the
child root), the old extensions with every guard `i` whose test `hopW`
holds on the child root, and the answers of the compositions of depth `q`
and arity `ℓ + 1`, with every guard whose test holds on their root.
`exW_eq`: these are the words of `exAt`.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax185574.WordEncoding Lax185574.DistanceLogic Lax185574.TypeTrees
open Lax185574Proofs.TreeAlgo Lax185574Proofs.ResolveRam Lax185574Proofs.Words
open Lax185574Proofs.EvalRam
open Lax3.DistFO (rhoMinus rhoPlus)

/-- The word of a member `(g, c)` of an expansion. -/
def gcW (p : ℕ × TypeTree) : List ℕ := p.1 :: toWord p.2

/-- The guards `i < ℓ` at which the test holds between `xᵢ` and the new
vertex `x_ℓ` of the root with atom words `A`, with the child word `cw`. -/
def guardW (Dw : DW) (R ℓ : ℕ) (A : List (List ℕ)) (cw : List ℕ) : List (List ℕ) :=
  (List.range ℓ).filterMap fun i => if hopW Dw A R i ℓ then some (i :: cw) else none

/-- The child of an extension word, as the word of a type tree. -/
def childW (k q ℓ : ℕ) (ew : List ℕ) : List ℕ := [k + 1, q, ℓ + 1] ++ ew.tail

/-- **The expansion on words.** -/
def exW (Dw : DW) (k q ℓ : ℕ) (X : List ℕ) (C : List (List ℕ)) : List (List ℕ) :=
  let R := rhoPlus (k + 1) q
  let E := listWords X (listEnd X 0)
  E.map (fun ew => ew.headD 0 :: childW k q ℓ ew) ++
    E.flatMap (fun ew => guardW Dw R ℓ (listWords (childW k q ℓ ew) 3) (childW k q ℓ ew)) ++
    C.flatMap fun cw =>
      if cw.getD 1 0 = q ∧ cw.getD 2 0 = ℓ + 1 then guardW Dw R ℓ (listWords cw 3) cw else []

theorem listWords_tree_root {c : TypeTree} : listWords (toWord c) 3 = (Node.atoms c.root).words :=
  atoms_listWords (r := []) (by rw [FarRam.toWord_typeTree]; simp)

theorem guardW_eq {Dw : DW} {D : ResolveData} (h : Dw.OK D) {q ℓ : ℕ} (R : ℕ) (r : Node q (ℓ + 1))
    (c : TypeTree) (A : List (List ℕ)) (hA : A = (Node.atoms r).words) :
    (guarded D R r c).map gcW = guardW Dw R ℓ A (toWord c) := by
  subst hA
  unfold guarded guardW
  rw [List.map_filterMap, ← FarRam.map_val_finRange, List.filterMap_map]
  congr 1
  funext i
  have := hopW_eq h r R i.castSucc (Fin.last ℓ)
  simp only [Fin.val_castSucc, Fin.val_last] at this
  simp only [Function.comp, this]
  by_cases hh : hopTest D r R i.castSucc (Fin.last ℓ)
  · simp [hh, gcW]
  · simp [hh]

/-- The part of the composition answer `cw`. -/
theorem farPart_eq {Dw : DW} {D : ResolveData} (h : Dw.OK D) (q ℓ R : ℕ) (c : TypeTree) :
    ((TypeTree.rootAs c q (ℓ + 1)).toList.flatMap fun r => guarded D R r c).map gcW =
      if (toWord c).getD 1 0 = q ∧ (toWord c).getD 2 0 = ℓ + 1 then
        guardW Dw R ℓ (listWords (toWord c) 3) (toWord c) else [] := by
  obtain ⟨ck, cq, cℓ, cr⟩ := c
  have e1 : (toWord (⟨ck, cq, cℓ, cr⟩ : TypeTree)).getD 1 0 = cq := by
    rw [FarRam.toWord_typeTree]; rfl
  have e2 : (toWord (⟨ck, cq, cℓ, cr⟩ : TypeTree)).getD 2 0 = cℓ := by
    rw [FarRam.toWord_typeTree]; rfl
  rw [e1, e2]
  by_cases hc : cq = q ∧ cℓ = ℓ + 1
  · obtain ⟨rfl, rfl⟩ := hc
    rw [if_pos ⟨rfl, rfl⟩, TypeTree.rootAs_mk]
    simp only [Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact guardW_eq h R cr _ _ listWords_tree_root
  · rw [if_neg hc]
    have : TypeTree.rootAs ⟨ck, cq, cℓ, cr⟩ q (ℓ + 1) = none := by
      simp only [TypeTree.rootAs]; rw [dif_neg hc]
    rw [this]; rfl

/-- **The expansion on words.** -/
theorem exW_eq {Dw : DW} {D : ResolveData} (h : Dw.OK D) (sh : TypeTree → TypeTree)
    (fa : TypeTree → List TypeTree) (co : TypeTree → TypeTree → TypeTree) (k q ℓ : ℕ)
    (t : Node (q + 1) ℓ) :
    (exAt D sh fa co k q ℓ t).map gcW = exW Dw k q ℓ (toWord t)
      ((fa ⟨k, q + 1, ℓ, t⟩).map fun ν => toWord (co (sh ⟨k, q + 1, ℓ, t⟩) ν)) := by
  have := Lax185574Proofs.EncodingInjectivity.prefixFree_node q (ℓ + 1)
  have hE : listWords (toWord t) (listEnd (toWord t) 0) = (elems (Node.exts t)).map toWord := by
    rw [map_elems]
    have := (nodeSplit (x := toWord t) (p := 0) (t := t) (r := []) (by simp)).2
    rw [List.append_nil] at this
    exact listWords_eq (r := []) (by rw [this, List.append_nil])
  have hch : ∀ e : Fin ℓ × Node q (ℓ + 1),
      childW k q ℓ (toWord e) = toWord (⟨k + 1, q, ℓ + 1, e.2⟩ : TypeTree) := by
    intro e; rw [toWord_ext, FarRam.toWord_typeTree]; rfl
  unfold exAt exW
  simp only
  rw [List.map_append, List.map_append, hE]
  congr 1
  · congr 1
    · rw [List.map_map, List.map_map]
      refine List.map_congr_left fun e _ => ?_
      simp only [Function.comp, gcW, toWord_ext]
      rfl
    · rw [List.map_flatMap, List.flatMap_map]
      refine List.flatMap_congr fun e _ => ?_
      rw [hch]
      exact guardW_eq h _ e.2 _ _ listWords_tree_root
  · rw [List.map_flatMap, List.flatMap_map]
    exact List.flatMap_congr fun ν _ => farPart_eq h q ℓ _ _

end Lax185574Proofs.ResolveRam.Glue
