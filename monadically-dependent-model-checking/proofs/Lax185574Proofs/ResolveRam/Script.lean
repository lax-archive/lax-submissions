import Lax185574Proofs.ResolveRam.Core

/-!
The recursion of lem:resolve-lift, level by level.

The program does not follow the recursion of `resolveNodeF` depth first.
It builds the levels of the tree of candidates top down and assembles the
new trees bottom up. Level `0` holds the trees of the vertices. An item
of a level is a parent index, a guard and a type tree. Level `d + 1`
holds, for every item `x` of level `d`, the members `(g, c)` of the
expansion `ex x` with parent the index of `x` (`nextLevel`). The
expansion is the list of the candidate extensions, in any order and with
repetitions (`ExpandAt`). Then the outputs of the deepest level are the
new root labels, and the output of an item of a higher level is its new
root label with the outputs of its children as extensions (`outLevel`).

`outsAt_eq` shows that the outputs are the lifts `liftT` of the items, and
`script_family` that the outputs of level `0` are the trees of the
vertices in `H = resolve^±_{P,Q}(G)`, if the expansion is right on the
trees of tuples of `G`.
-/

namespace Lax185574Proofs.ResolveRam

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.WordEncoding
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.FarTrees Lax185574.ConstructionSequences
open Lax185574.ResolveLift Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo
open Lax3.DistFO (rhoMinus rhoPlus)

/-- The lift of a type tree through the resolve. -/
def liftT (D : ResolveData) (ft : FarMap) (τ : TypeTree) : TypeTree :=
  ⟨τ.k, τ.q, τ.ℓ, resolveNodeF D ft τ.k τ.q τ.root⟩

/-- An item of a level: the index of the parent, the guard and the tree. -/
abbrev Item := (ℕ × ℕ) × TypeTree

/-- The next level: the members of the expansions of the items, with the
index of the item as parent. -/
def nextLevel (ex : TypeTree → List (ℕ × TypeTree)) (L : List Item) : List Item :=
  L.zipIdx.flatMap fun x => (ex x.1.2).map fun gc => ((x.2, gc.1), gc.2)

/-- The children of item `i`, with their guards and outputs. -/
def kidsOf (Ln : List Item) (On : List TypeTree) (i : ℕ) : List (ℕ × TypeTree) :=
  ((Ln.zip On).filter fun y => y.1.1.1 = i).map fun y => (y.1.1.2, y.2)

/-- The extensions of arity `ℓ + 1` and depth `q` given by a list of
guards and trees. -/
def kidSet (q ℓ : ℕ) (kids : List (ℕ × TypeTree)) : Finset (Fin ℓ × Node q (ℓ + 1)) :=
  (kids.filterMap fun p =>
    if h : p.1 < ℓ then (TypeTree.rootAs p.2 q (ℓ + 1)).map fun r => ((⟨p.1, h⟩ : Fin ℓ), r)
    else none).toFinset

/-- The output of an item from the outputs of its children. -/
def asm (D : ResolveData) : TypeTree → List (ℕ × TypeTree) → TypeTree
  | ⟨k, 0, ℓ, t⟩, _ => ⟨k, 0, ℓ, newAtoms D k 0 t⟩
  | ⟨k, q + 1, ℓ, t⟩, kids => ⟨k, q + 1, ℓ, (newAtoms D k (q + 1) t, kidSet q ℓ kids)⟩

/-- The outputs of a level from the next level and its outputs. -/
def outLevel (D : ResolveData) (Ln : List Item) (On : List TypeTree) (L : List Item) :
    List TypeTree :=
  L.zipIdx.map fun x => asm D x.1.2 (kidsOf Ln On x.2)

/-- The expansion is right at a node: its members are the candidate
extensions, with the guard as a number and the child as a type tree. -/
def ExpandAt (D : ResolveData) (ft : FarMap) (ex : TypeTree → List (ℕ × TypeTree))
    (k q ℓ : ℕ) (t : Node (q + 1) ℓ) : Prop :=
  ∀ p, p ∈ ex ⟨k, q + 1, ℓ, t⟩ ↔
    ∃ e ∈ candidatesF D ft k q ℓ t, p = (e.1.val, (⟨k + 1, q, ℓ + 1, e.2⟩ : TypeTree))

/-- The levels. -/
def levels (ex : TypeTree → List (ℕ × TypeTree)) (L₀ : List Item) (d : ℕ) : List Item :=
  (nextLevel ex)^[d] L₀

/-- The outputs of level `d`, when `m` levels lie below it. -/
def outsAt (D : ResolveData) (ex : TypeTree → List (ℕ × TypeTree)) (L₀ : List Item) :
    ℕ → ℕ → List TypeTree
  | 0, d => (levels ex L₀ d).map fun x => asm D x.2 []
  | m + 1, d => outLevel D (levels ex L₀ (d + 1)) (outsAt D ex L₀ m (d + 1)) (levels ex L₀ d)

theorem levels_succ (ex : TypeTree → List (ℕ × TypeTree)) (L₀ : List Item) (d : ℕ) :
    levels ex L₀ (d + 1) = nextLevel ex (levels ex L₀ d) := by
  simp only [levels, Function.iterate_succ_apply']

theorem zip_map_self {α β : Type*} (l : List α) (f : α → β) :
    l.zip (l.map f) = l.map fun y => (y, f y) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

theorem mem_nextLevel {ex : TypeTree → List (ℕ × TypeTree)} {L : List Item} {y : Item} :
    y ∈ nextLevel ex L ↔ ∃ (i : ℕ) (h : i < L.length), ∃ gc ∈ ex L[i].2, y = ((i, gc.1), gc.2) := by
  simp only [nextLevel, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨x, hx, gc, hgc, rfl⟩
    rw [List.mem_zipIdx_iff_getElem?] at hx
    obtain ⟨h, hx'⟩ := List.getElem?_eq_some_iff.1 hx
    exact ⟨x.2, h, gc, by rw [hx']; exact hgc, rfl⟩
  · rintro ⟨i, h, gc, hgc, rfl⟩
    exact ⟨(L[i], i), List.mem_zipIdx_iff_getElem?.2 (List.getElem?_eq_getElem h), gc, hgc, rfl⟩

theorem mem_kidsOf {ex : TypeTree → List (ℕ × TypeTree)} {L : List Item} (f : Item → TypeTree)
    {i : ℕ} (hi : i < L.length) (p : ℕ × TypeTree) :
    p ∈ kidsOf (nextLevel ex L) ((nextLevel ex L).map f) i ↔
      ∃ gc ∈ ex L[i].2, p = (gc.1, f ((i, gc.1), gc.2)) := by
  simp only [kidsOf, zip_map_self, List.mem_map, List.mem_filter, decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨⟨y, hy, rfl⟩, hyi⟩, rfl⟩
    obtain ⟨j, hj, gc, hgc, rfl⟩ := mem_nextLevel.1 hy
    simp only at hyi
    subst hyi
    exact ⟨gc, hgc, rfl⟩
  · rintro ⟨gc, hgc, rfl⟩
    exact ⟨_, ⟨⟨_, mem_nextLevel.2 ⟨i, hi, gc, hgc, rfl⟩, rfl⟩, rfl⟩, rfl⟩

theorem mem_kidSet {q ℓ : ℕ} (kids : List (ℕ × TypeTree)) (e : Fin ℓ × Node q (ℓ + 1)) :
    e ∈ kidSet q ℓ kids ↔ ∃ p ∈ kids, p.1 = e.1.val ∧ TypeTree.rootAs p.2 q (ℓ + 1) = some e.2 := by
  simp only [kidSet, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, he⟩
    by_cases h : p.1 < ℓ
    · rw [dif_pos h] at he
      cases hr : TypeTree.rootAs p.2 q (ℓ + 1) with
      | none => rw [hr] at he; simp at he
      | some r =>
        rw [hr] at he
        simp only [Option.map_some, Option.some.injEq] at he
        subst he
        exact ⟨p, hp, rfl, hr⟩
    · rw [dif_neg h] at he; simp at he
  · rintro ⟨p, hp, h1, h2⟩
    refine ⟨p, hp, ?_⟩
    rw [dif_pos (by rw [h1]; exact e.1.isLt), h2]
    simp only [Option.map_some]
    congr 1
    exact Prod.ext (Fin.ext h1) rfl

theorem asm_zero (D : ResolveData) (ft : FarMap) (τ : TypeTree) (h : τ.q = 0)
    (kids : List (ℕ × TypeTree)) : asm D τ kids = liftT D ft τ := by
  rcases τ with ⟨k, _ | q, ℓ, t⟩
  · rfl
  · simp at h

/-- **One level.** If the expansion is right at every item, the outputs
of a level computed from the lifts of the next level are the lifts. -/
theorem outLevel_eq (D : ResolveData) (ft : FarMap) (ex : TypeTree → List (ℕ × TypeTree))
    (L : List Item)
    (hL : ∀ x ∈ L, ∃ (k q ℓ : ℕ) (t : Node (q + 1) ℓ), x.2 = ⟨k, q + 1, ℓ, t⟩ ∧
      ExpandAt D ft ex k q ℓ t) :
    outLevel D (nextLevel ex L) ((nextLevel ex L).map fun y => liftT D ft y.2) L =
      L.map fun x => liftT D ft x.2 := by
  refine List.ext_getElem (by simp [outLevel]) fun i h₁ h₂ => ?_
  simp only [outLevel, List.getElem_map, List.getElem_zipIdx, Nat.zero_add]
  have hi : i < L.length := by simpa using h₂
  obtain ⟨k, q, ℓ, t, hx, hex⟩ := hL L[i] (List.getElem_mem hi)
  have hk := fun p => mem_kidsOf (ex := ex) (fun y => liftT D ft y.2) hi p
  generalize kidsOf (nextLevel ex L) ((nextLevel ex L).map fun y => liftT D ft y.2) i = K at hk ⊢
  rw [hx] at hk ⊢
  simp only [ExpandAt] at hex
  simp only [asm, liftT, resolveNodeF]
  congr 2
  ext e
  simp only [mem_kidSet, hk, hex, Finset.mem_image]
  constructor
  · rintro ⟨p, ⟨gc, ⟨e', he', rfl⟩, rfl⟩, h1, h2⟩
    simp only [liftT, TypeTree.rootAs_mk, Option.some.injEq] at h1 h2
    exact ⟨e', he', Prod.ext (Fin.ext h1) h2⟩
  · rintro ⟨e', he', rfl⟩
    exact ⟨(e'.1.val, liftT D ft ⟨k + 1, q, ℓ + 1, e'.2⟩),
      ⟨(e'.1.val, ⟨k + 1, q, ℓ + 1, e'.2⟩), ⟨e', he', rfl⟩, rfl⟩, rfl,
      by simp only [liftT, TypeTree.rootAs_mk]⟩

variable {n : ℕ} {G : PartialGraph (Fin n)}

/-- The expansion is right at the trees of tuples of `G` below the top
rank `(k₀, q₀)`. -/
def ExpandOK (G : PartialGraph (Fin n)) (D : ResolveData) (ft : FarMap)
    (ex : TypeTree → List (ℕ × TypeTree)) (k₀ q₀ : ℕ) : Prop :=
  ∀ (k q ℓ : ℕ) (u : Fin ℓ → Fin n), 1 ≤ ℓ → ℓ ≤ k → k₀ ≤ k → k + (q + 1) = k₀ + q₀ →
    ExpandAt D ft ex k q ℓ (node G k (q + 1) u)

/-- The items of a level are trees of tuples of `G`. -/
def GoodAt (G : PartialGraph (Fin n)) (k₀ q₀ d : ℕ) (x : Item) : Prop :=
  ∃ (ℓ : ℕ) (u : Fin ℓ → Fin n), x.2 = tree G (k₀ + d) (q₀ - d) u ∧ 1 ≤ ℓ ∧ ℓ ≤ k₀ + d

theorem levels_good (D : ResolveData) (ft : FarMap) {k₀ q₀ : ℕ} (hD : D.Spec G k₀ q₀)
    (hft : FarSpec G ft) {ex : TypeTree → List (ℕ × TypeTree)} (hex : ExpandOK G D ft ex k₀ q₀)
    {L₀ : List Item} (h₀ : ∀ x ∈ L₀, GoodAt G k₀ q₀ 0 x) :
    ∀ d ≤ q₀, ∀ x ∈ levels ex L₀ d, GoodAt G k₀ q₀ d x := by
  intro d
  induction d with
  | zero => intro _; exact h₀
  | succ d ih =>
    intro hd x hx
    rw [levels_succ] at hx
    obtain ⟨i, hi, gc, hgc, rfl⟩ := mem_nextLevel.1 hx
    obtain ⟨ℓ, u, hu, h1, hk⟩ := ih (by omega) _ (List.getElem_mem hi)
    obtain ⟨q, hq⟩ : ∃ q, q₀ - d = q + 1 := ⟨q₀ - d - 1, by omega⟩
    rw [hq] at hu
    rw [hu] at hgc
    obtain ⟨e, he, rfl⟩ := (hex (k₀ + d) q ℓ u h1 hk (by omega) (by omega) gc).1 hgc
    obtain ⟨j, b, -, rfl⟩ := (mem_candidatesF D ft hD hft u h1 hk (by omega) (by omega) _).1 he
    refine ⟨ℓ + 1, Fin.snoc u b, ?_, by omega, by omega⟩
    simp only [tree]
    rw [show q₀ - (d + 1) = q by omega]
    rfl

/-- **The outputs are the lifts.** -/
theorem outsAt_eq (D : ResolveData) (ft : FarMap) {k₀ q₀ : ℕ} (hD : D.Spec G k₀ q₀)
    (hft : FarSpec G ft) {ex : TypeTree → List (ℕ × TypeTree)} (hex : ExpandOK G D ft ex k₀ q₀)
    {L₀ : List Item} (h₀ : ∀ x ∈ L₀, GoodAt G k₀ q₀ 0 x) :
    ∀ m d, d + m = q₀ → outsAt D ex L₀ m d = (levels ex L₀ d).map fun x => liftT D ft x.2 := by
  have hg := levels_good D ft hD hft hex h₀
  intro m
  induction m with
  | zero =>
    intro d hd
    simp only [outsAt]
    refine List.map_congr_left fun x hx => asm_zero D ft x.2 ?_ []
    obtain ⟨ℓ, u, hu, -⟩ := hg d (by omega) x hx
    rw [hu]; simp [tree]; omega
  | succ m ih =>
    intro d hd
    simp only [outsAt]
    rw [ih (d + 1) (by omega), levels_succ]
    refine outLevel_eq D ft ex _ fun x hx => ?_
    obtain ⟨ℓ, u, hu, h1, hk⟩ := hg d (by omega) x hx
    rw [show q₀ - d = m + 1 by omega] at hu
    exact ⟨k₀ + d, m, ℓ, node G (k₀ + d) (m + 1) u, hu,
      hex (k₀ + d) m ℓ u h1 hk (by omega) (by omega)⟩

/-- The first level: the trees of the vertices. -/
noncomputable def famItems (G : PartialGraph (Fin n)) (k q : ℕ) : List Item :=
  (List.finRange n).map fun b => ((0, 0), family G k q b)

/-- **The script computes the new family.** -/
theorem script_family (D : ResolveData) (ft : FarMap) {k₀ q₀ : ℕ} (hk : 1 ≤ k₀)
    (hD : D.Spec G k₀ q₀) (hft : FarSpec G ft) {ex : TypeTree → List (ℕ × TypeTree)}
    (hex : ExpandOK G D ft ex k₀ q₀) :
    outsAt D ex (famItems G k₀ q₀) q₀ 0 =
      (List.finRange n).map fun b => family (resolveBy G D.sign D.P D.Q) k₀ q₀ b := by
  have h₀ : ∀ x ∈ famItems G k₀ q₀, GoodAt G k₀ q₀ 0 x := by
    intro x hx
    simp only [famItems, List.mem_map] at hx
    obtain ⟨b, -, rfl⟩ := hx
    exact ⟨1, ![b], by simp [family], le_rfl, by omega⟩
  rw [outsAt_eq D ft hD hft hex h₀ q₀ 0 (by omega)]
  simp only [levels, Function.iterate_zero, id, famItems, List.map_map]
  refine List.map_congr_left fun b _ => ?_
  simp only [Function.comp, family, tree, liftT]
  rw [resolveNodeF_node D ft hD hft q₀ k₀ ![b] le_rfl hk le_rfl rfl]

end Lax185574Proofs.ResolveRam
