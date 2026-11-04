import Lax185574Proofs.TreeAlgo.ResolveDist
import Lax185574Proofs.TreeAlgo.FarComposition
import Lax185574Proofs.TreeAlgo.ComputeScatterType
import Lax185574.ResolveLift

/-!
The semantic core of lem:resolve-lift. The data computed once from `G` are
the colors that occur, the test `cd X Y s` whether some vertex of color
`X` is within distance `s` of some vertex of color `Y` in `G`, and the
scatter type `σ = stp_{k,q}`. From these and the tree `τ` of a tuple ā in
`G`, `resolveNode` computes the tree of ā in `H = resolve^±_{P,Q}(G)`:

* the root label is found by testing every atom of rank `(k, q)` whose
  color occurs. The tests rewrite an atom of `H` into atoms of `G`: the new
  pairs `P^G Q^G` for the edge or non-edge atom, and for the distance atoms
  the walks of `Hop`, which use at most two new pairs;
* the extensions are `F` applied to the old extensions, to the old
  extensions `(j, μ)` with `μ ⊨ γᵢ` relabeled with guard `i`, and to the
  trees `shift τ ∗ ν` with `ν` in the far tree and `shift τ ∗ ν ⊨ γᵢ`.
  Here `γᵢ` is the test `Hop` between `xᵢ` and the new vertex at radius
  `ρ⁺(k+1, q−1)`, read off the root of the child.

The correctness proof follows the proof of lem:resolve-lift. It uses the
cores of lem:shift, lem:compose and lem:to-ftree. The far tree is computed
from the scatter type `stp_{k₀,q₀}` of the top level at every depth, which
has the entries of `stp_{k,q}` that the far tree reads, as in
obs:stp-restrict.
-/

namespace Lax185574Proofs.TreeAlgo

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.WordEncoding
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.FarTrees Lax185574.ConstructionSequences
open Lax185574.ResolveLift Lax185574.PartialGraphEncoding
open Lax185574Proofs.WalkDistance
open Lax3.DistFO (rhoMinus rhoPlus)

/-- The data of a resolve that are computed once from the partial graph. -/
structure ResolveData where
  /-- The first color. -/
  P : ℕ
  /-- The second color. -/
  Q : ℕ
  /-- The sign, `true` for the positive resolve. -/
  sign : Bool
  /-- The colors that occur. -/
  cols : Finset ℕ
  /-- Whether some vertex of the first color is within the given distance
  of some vertex of the second color. -/
  cd : ℕ → ℕ → ℕ → Bool
  /-- The scatter type of the top level. -/
  σ : Finset ((ℕ × TypeTree) × ℕ)

/-- Membership of an atom in the root label. -/
def inA {q ℓ : ℕ} (t : Node q ℓ) (φ : DistFO ℓ) : Prop := φ ∈ Node.atoms t

instance {q ℓ : ℕ} (t : Node q ℓ) (φ : DistFO ℓ) : Decidable (inA t φ) :=
  inferInstanceAs (Decidable (φ ∈ Node.atoms t))

/-- The test `dist(xᵢ, X) < s + 1`. -/
def nearA {q ℓ : ℕ} (t : Node q ℓ) (X s : ℕ) (i : Fin ℓ) : Prop := inA t (.distColorLt (s + 1) X i)

instance {q ℓ : ℕ} (t : Node q ℓ) (X s : ℕ) (i : Fin ℓ) : Decidable (nearA t X s i) :=
  inferInstanceAs (Decidable (inA _ _))

/-- The test of `Hop` between the positions `i` and `j` at radius `s`. -/
def hopTest (D : ResolveData) {q ℓ : ℕ} (t : Node q ℓ) (s : ℕ) (i j : Fin ℓ) : Prop :=
  ∃ s₁ ∈ Finset.range (s + 1), ∃ s₂ ∈ Finset.range (s + 1),
    (s₁ + 1 + s₂ ≤ s ∧ ((nearA t D.P s₁ i ∧ nearA t D.Q s₂ j) ∨
      (nearA t D.Q s₁ i ∧ nearA t D.P s₂ j))) ∨
    (s₁ + 2 + s₂ ≤ s ∧ ((nearA t D.P s₁ i ∧ nearA t D.P s₂ j ∧ D.Q ∈ D.cols) ∨
      (nearA t D.Q s₁ i ∧ nearA t D.Q s₂ j ∧ D.P ∈ D.cols)))

instance (D : ResolveData) {q ℓ : ℕ} (t : Node q ℓ) (s : ℕ) (i j : Fin ℓ) :
    Decidable (hopTest D t s i j) := by unfold hopTest; infer_instance

/-- The test of `Hop` from the position `i` to the color class `Y` at
radius `s`. -/
def unaryHopTest (D : ResolveData) {q ℓ : ℕ} (t : Node q ℓ) (s Y : ℕ) (i : Fin ℓ) : Prop :=
  ∃ s₁ ∈ Finset.range (s + 1), ∃ s₂ ∈ Finset.range (s + 1),
    (s₁ + 1 + s₂ ≤ s ∧ ((nearA t D.P s₁ i ∧ D.cd D.Q Y s₂ = true) ∨
      (nearA t D.Q s₁ i ∧ D.cd D.P Y s₂ = true))) ∨
    (s₁ + 2 + s₂ ≤ s ∧ ((nearA t D.P s₁ i ∧ D.cd D.P Y s₂ = true ∧ D.Q ∈ D.cols) ∨
      (nearA t D.Q s₁ i ∧ D.cd D.Q Y s₂ = true ∧ D.P ∈ D.cols)))

instance (D : ResolveData) {q ℓ : ℕ} (t : Node q ℓ) (s Y : ℕ) (i : Fin ℓ) :
    Decidable (unaryHopTest D t s Y i) := by unfold unaryHopTest; infer_instance

/-- The positions `i` and `j` carry the colors `P` and `Q`. -/
def crossA (D : ResolveData) {q ℓ : ℕ} (t : Node q ℓ) (i j : Fin ℓ) : Prop :=
  (inA t (.color D.P i) ∧ inA t (.color D.Q j)) ∨ (inA t (.color D.Q i) ∧ inA t (.color D.P j))

instance (D : ResolveData) {q ℓ : ℕ} (t : Node q ℓ) (i j : Fin ℓ) :
    Decidable (crossA D t i j) := by unfold crossA; infer_instance

/-- Whether an atom holds after the resolve, read off the old root label. -/
def newAtomTest (D : ResolveData) {q ℓ : ℕ} (t : Node q ℓ) : DistFO ℓ → Prop
  | .eq i j => inA t (.eq i j)
  | .edge i j => inA t (.edge i j) ∨
      (D.sign = true ∧ crossA D t i j ∧ ¬ inA t (.eq i j) ∧ ¬ inA t (.nonEdge i j))
  | .nonEdge i j => inA t (.nonEdge i j) ∨
      (D.sign = false ∧ crossA D t i j ∧ ¬ inA t (.eq i j) ∧ ¬ inA t (.edge i j))
  | .color Y i => inA t (.color Y i)
  | .distLe s i j => inA t (.distLe s i j) ∨ hopTest D t s i j
  | .distColorLt s Y i => inA t (.distColorLt s Y i) ∨ (∃ s' ∈ Finset.range s,
      s = s' + 1 ∧ unaryHopTest D t s' Y i)
  | _ => False

instance (D : ResolveData) {q ℓ : ℕ} (t : Node q ℓ) (φ : DistFO ℓ) :
    Decidable (newAtomTest D t φ) := by
  cases φ <;> unfold newAtomTest <;> infer_instance

/-- The atoms of distance rank `(k, q)` with colors from `cols`. -/
def candidates (k q ℓ : ℕ) (cols : Finset ℕ) : Finset (DistFO ℓ) :=
  let pairs : Finset (Fin ℓ × Fin ℓ) := Finset.univ
  pairs.image (fun p => DistFO.eq p.1 p.2) ∪ pairs.image (fun p => DistFO.edge p.1 p.2) ∪
    pairs.image (fun p => DistFO.nonEdge p.1 p.2) ∪
    (cols ×ˢ (Finset.univ : Finset (Fin ℓ))).image (fun p => DistFO.color p.1 p.2) ∪
    (Finset.range (rhoMinus k q + 1) ×ˢ pairs).image (fun p => DistFO.distLe p.1 p.2.1 p.2.2) ∪
    (Finset.range (rhoPlus k q + 1) ×ˢ (cols ×ˢ (Finset.univ : Finset (Fin ℓ)))).image
      (fun p => DistFO.distColorLt p.1 p.2.1 p.2.2)

/-- The new root label. -/
def newAtoms (D : ResolveData) (k q : ℕ) {q' ℓ : ℕ} (t : Node q' ℓ) : Finset (DistFO ℓ) :=
  (candidates k q ℓ D.cols).filter fun φ => newAtomTest D t φ

/-- The root of a type tree of depth `q` and arity `ℓ`, if it has these. -/
def TypeTree.rootAs (ν : TypeTree) (q ℓ : ℕ) : Option (Node q ℓ) :=
  if h : ν.q = q ∧ ν.ℓ = ℓ then some (h.1 ▸ h.2 ▸ ν.root) else none

theorem TypeTree.rootAs_mk (k q ℓ : ℕ) (t : Node q ℓ) :
    TypeTree.rootAs ⟨k, q, ℓ, t⟩ q ℓ = some t := by
  simp [TypeTree.rootAs]

/-- The candidate extensions: old, near and far. -/
def resolveCandidates (D : ResolveData) (k q ℓ : ℕ) (t : Node (q + 1) ℓ) :
    Finset (Fin ℓ × Node q (ℓ + 1)) :=
  let R := rhoPlus (k + 1) q
  Node.exts t ∪
    ((Node.exts t ×ˢ (Finset.univ : Finset (Fin ℓ))).filter
      (fun p => hopTest D p.1.2 R p.2.castSucc (Fin.last ℓ))).image (fun p => (p.2, p.1.2)) ∪
    ((farTreeNode k q ℓ t D.σ) ×ˢ (Finset.univ : Finset (Fin ℓ))).biUnion fun p =>
      match TypeTree.rootAs p.1 q 1 with
      | none => ∅
      | some ν =>
        if hopTest D (composeNode (ℓ₁ := ℓ) (ℓ₂ := 1) (shiftNode t) ν) R p.2.castSucc (Fin.last ℓ)
        then {(p.2, composeNode (ℓ₁ := ℓ) (ℓ₂ := 1) (shiftNode t) ν)} else ∅

/-- The lift of a tree through the resolve. -/
def resolveNode (D : ResolveData) : (k q : ℕ) → {ℓ : ℕ} → Node q ℓ → Node q ℓ
  | k, 0, _, t => newAtoms D k 0 t
  | k, q + 1, ℓ, t => (newAtoms D k (q + 1) t,
      (resolveCandidates D k q ℓ t).image fun e => (e.1, resolveNode D (k + 1) q e.2))

/-- The lift of the family of type trees of all vertices. -/
def resolveFamily (D : ResolveData) (k q : ℕ) {n : ℕ} (fam : Fin n → TypeTree) :
    Fin n → TypeTree := fun b =>
  match TypeTree.rootAs (fam b) q 1 with
  | some t => ⟨k, q, 1, resolveNode D k q t⟩
  | none => fam b

/-! ### Correctness -/

section Correctness

variable {n : ℕ} {G : PartialGraph (Fin n)}

/-- The data of a resolve are correct for `G` and the top rank `(k₀, q₀)`. -/
def ResolveData.Spec (D : ResolveData) (G : PartialGraph (Fin n)) (k₀ q₀ : ℕ) : Prop :=
  (∀ Y, Y ∈ D.cols ↔ Occurs G Y) ∧
    (∀ X Y s, D.cd X Y s = true ↔
      ∃ x y, G.color x = X ∧ G.color y = Y ∧ WithinDist G.resolved s x y) ∧
    D.σ = stp G k₀ q₀

theorem resolveBy_color (G : PartialGraph (Fin n)) (s : Bool) (P Q : ℕ) :
    (resolveBy G s P Q).color = G.color := by cases s <;> rfl

theorem resolveBy_resolved (G : PartialGraph (Fin n)) (s : Bool) (P Q : ℕ) :
    (resolveBy G s P Q).resolved = G.resolved ⊔ between G P Q := by
  cases s
  · exact resolved_resolveNeg G P Q
  · exact resolved_resolvePos G P Q

theorem inA_node {k q ℓ : ℕ} (u : Fin ℓ → Fin n) {φ : DistFO ℓ} (hr : DRank k q φ)
    (hat : IsAtom φ) : inA (node G k q u) φ ↔ Sat G u φ := by
  rw [inA, mem_atoms_node]
  exact ⟨fun h => h.2.2, fun h => ⟨hat, hr, h⟩⟩

theorem withinDistLt_succ {W : Type*} {H : SimpleGraph W} {s : ℕ} {u v : W} :
    WithinDistLt H (s + 1) u v ↔ WithinDist H s u v := by
  simp only [WithinDistLt, WithinDist, Nat.lt_succ_iff]

theorem nearA_node {k q ℓ s : ℕ} (u : Fin ℓ → Fin n) (X : ℕ) (i : Fin ℓ)
    (hs : s + 1 ≤ rhoPlus k q) : nearA (node G k q u) X s i ↔ NearC G (u i) X s := by
  rw [nearA, inA_node u (.distColorLt (s + 1) X i hs) trivial]
  simp only [Sat, NearC, withinDistLt_succ]

theorem hopTest_node (D : ResolveData) (hD : ∀ Y, Y ∈ D.cols ↔ Occurs G Y) {k q ℓ s : ℕ}
    (u : Fin ℓ → Fin n) (i j : Fin ℓ) (hs : s ≤ rhoPlus k q) :
    hopTest D (node G k q u) s i j ↔ Hop G D.P D.Q s (u i) (u j) := by
  unfold hopTest Hop
  simp only [Finset.mem_range, hD]
  constructor
  · rintro ⟨s₁, -, s₂, -, h⟩
    refine ⟨s₁, s₂, ?_⟩
    rcases h with ⟨h0, h⟩ | ⟨h0, h⟩
    · left
      refine ⟨h0, ?_⟩
      rwa [nearA_node u _ _ (by omega), nearA_node u _ _ (by omega), nearA_node u _ _ (by omega),
        nearA_node u _ _ (by omega)] at h
    · right
      refine ⟨h0, ?_⟩
      rwa [nearA_node u _ _ (by omega), nearA_node u _ _ (by omega), nearA_node u _ _ (by omega),
        nearA_node u _ _ (by omega)] at h
  · rintro ⟨s₁, s₂, h⟩
    rcases h with ⟨h0, h⟩ | ⟨h0, h⟩
    · refine ⟨s₁, by omega, s₂, by omega, Or.inl ⟨h0, ?_⟩⟩
      rwa [nearA_node u _ _ (by omega), nearA_node u _ _ (by omega), nearA_node u _ _ (by omega),
        nearA_node u _ _ (by omega)]
    · refine ⟨s₁, by omega, s₂, by omega, Or.inr ⟨h0, ?_⟩⟩
      rwa [nearA_node u _ _ (by omega), nearA_node u _ _ (by omega), nearA_node u _ _ (by omega),
        nearA_node u _ _ (by omega)]

/-- Distance from a vertex to a color class after the resolve. -/
theorem unary_resolve_iff {D : ResolveData} {s : ℕ} {Y : ℕ} {v : Fin n} :
    (∃ y, G.color y = Y ∧ WithinDist (G.resolved ⊔ between G D.P D.Q) s v y) ↔
      (∃ y, G.color y = Y ∧ WithinDist G.resolved s v y) ∨
        ∃ s₁ s₂, (s₁ + 1 + s₂ ≤ s ∧
          ((NearC G v D.P s₁ ∧ ∃ x y, G.color x = D.Q ∧ G.color y = Y ∧
              WithinDist G.resolved s₂ x y) ∨
            (NearC G v D.Q s₁ ∧ ∃ x y, G.color x = D.P ∧ G.color y = Y ∧
              WithinDist G.resolved s₂ x y))) ∨
          (s₁ + 2 + s₂ ≤ s ∧
            ((NearC G v D.P s₁ ∧ (∃ x y, G.color x = D.P ∧ G.color y = Y ∧
                WithinDist G.resolved s₂ x y) ∧ Occurs G D.Q) ∨
              (NearC G v D.Q s₁ ∧ (∃ x y, G.color x = D.Q ∧ G.color y = Y ∧
                WithinDist G.resolved s₂ x y) ∧ Occurs G D.P))) := by
  have hn : ∀ {X t y}, NearC G y X t ↔ ∃ x, G.color x = X ∧ WithinDist G.resolved t x y :=
    fun {X t y} => ⟨fun ⟨x, hx, h⟩ => ⟨x, hx, withinDist_symm h⟩,
      fun ⟨x, hx, h⟩ => ⟨x, hx, withinDist_symm h⟩⟩
  simp only [withinDist_resolve_iff, Hop, hn]
  constructor
  · rintro ⟨y, hy, h | ⟨s₁, s₂, h⟩⟩
    · exact Or.inl ⟨y, hy, h⟩
    · right
      refine ⟨s₁, s₂, ?_⟩
      rcases h with ⟨h0, ⟨a, x, hx, b⟩ | ⟨a, x, hx, b⟩⟩ | ⟨h0, ⟨a, ⟨x, hx, b⟩, c⟩ | ⟨a, ⟨x, hx, b⟩, c⟩⟩
      · exact Or.inl ⟨h0, Or.inl ⟨a, x, y, hx, hy, b⟩⟩
      · exact Or.inl ⟨h0, Or.inr ⟨a, x, y, hx, hy, b⟩⟩
      · exact Or.inr ⟨h0, Or.inl ⟨a, ⟨x, y, hx, hy, b⟩, c⟩⟩
      · exact Or.inr ⟨h0, Or.inr ⟨a, ⟨x, y, hx, hy, b⟩, c⟩⟩
  · rintro (⟨y, hy, h⟩ | ⟨s₁, s₂, h⟩)
    · exact ⟨y, hy, Or.inl h⟩
    · rcases h with ⟨h0, ⟨a, x, y, hx, hy, b⟩ | ⟨a, x, y, hx, hy, b⟩⟩ |
        ⟨h0, ⟨a, ⟨x, y, hx, hy, b⟩, c⟩ | ⟨a, ⟨x, y, hx, hy, b⟩, c⟩⟩
      · exact ⟨y, hy, Or.inr ⟨s₁, s₂, Or.inl ⟨h0, Or.inl ⟨a, x, hx, b⟩⟩⟩⟩
      · exact ⟨y, hy, Or.inr ⟨s₁, s₂, Or.inl ⟨h0, Or.inr ⟨a, x, hx, b⟩⟩⟩⟩
      · exact ⟨y, hy, Or.inr ⟨s₁, s₂, Or.inr ⟨h0, Or.inl ⟨a, ⟨x, hx, b⟩, c⟩⟩⟩⟩
      · exact ⟨y, hy, Or.inr ⟨s₁, s₂, Or.inr ⟨h0, Or.inr ⟨a, ⟨x, hx, b⟩, c⟩⟩⟩⟩

theorem unaryHopTest_node (D : ResolveData) {k₀ q₀ : ℕ} (hD : D.Spec G k₀ q₀) {k q ℓ s : ℕ}
    (u : Fin ℓ → Fin n) (Y : ℕ) (i : Fin ℓ) (hs : s + 1 ≤ rhoPlus k q) :
    unaryHopTest D (node G k q u) s Y i ↔
      ∃ s₁ s₂, (s₁ + 1 + s₂ ≤ s ∧
          ((NearC G (u i) D.P s₁ ∧ ∃ x y, G.color x = D.Q ∧ G.color y = Y ∧
              WithinDist G.resolved s₂ x y) ∨
            (NearC G (u i) D.Q s₁ ∧ ∃ x y, G.color x = D.P ∧ G.color y = Y ∧
              WithinDist G.resolved s₂ x y))) ∨
          (s₁ + 2 + s₂ ≤ s ∧
            ((NearC G (u i) D.P s₁ ∧ (∃ x y, G.color x = D.P ∧ G.color y = Y ∧
                WithinDist G.resolved s₂ x y) ∧ Occurs G D.Q) ∨
              (NearC G (u i) D.Q s₁ ∧ (∃ x y, G.color x = D.Q ∧ G.color y = Y ∧
                WithinDist G.resolved s₂ x y) ∧ Occurs G D.P))) := by
  obtain ⟨hc, hcd, -⟩ := hD
  unfold unaryHopTest
  simp only [Finset.mem_range, hc, hcd]
  constructor
  · rintro ⟨s₁, -, s₂, -, h⟩
    refine ⟨s₁, s₂, ?_⟩
    rcases h with ⟨h0, h⟩ | ⟨h0, h⟩
    · left; refine ⟨h0, ?_⟩
      rwa [nearA_node u _ _ (by omega), nearA_node u _ _ (by omega)] at h
    · right; refine ⟨h0, ?_⟩
      rwa [nearA_node u _ _ (by omega), nearA_node u _ _ (by omega)] at h
  · rintro ⟨s₁, s₂, h⟩
    rcases h with ⟨h0, h⟩ | ⟨h0, h⟩
    · refine ⟨s₁, by omega, s₂, by omega, Or.inl ⟨h0, ?_⟩⟩
      rwa [nearA_node u _ _ (by omega), nearA_node u _ _ (by omega)]
    · refine ⟨s₁, by omega, s₂, by omega, Or.inr ⟨h0, ?_⟩⟩
      rwa [nearA_node u _ _ (by omega), nearA_node u _ _ (by omega)]

/-- The new root label is the root label of the tree after the resolve. -/
theorem newAtoms_node (D : ResolveData) {k₀ q₀ : ℕ} (hD : D.Spec G k₀ q₀) (k q : ℕ) {ℓ : ℕ}
    (u : Fin ℓ → Fin n) :
    newAtoms D k q (node G k q u) = Node.atoms (node (resolveBy G D.sign D.P D.Q) k q u) := by
  have hc := hD.1
  set H := resolveBy G D.sign D.P D.Q
  have hHc : H.color = G.color := resolveBy_color G _ _ _
  have hHr : H.resolved = G.resolved ⊔ between G D.P D.Q := resolveBy_resolved G _ _ _
  have hRm := rhoMinus_le_rhoPlus k q
  ext φ
  rw [newAtoms, Finset.mem_filter, mem_atoms_node]
  -- the test is satisfaction in `H`
  have htest : IsAtom φ → DRank k q φ → (newAtomTest D (node G k q u) φ ↔ Sat H u φ) := by
    intro hat hr
    cases φ with
    | eq i j => exact (inA_node u (.eq i j) trivial).trans Iff.rfl
    | color Y i =>
      rw [newAtomTest, inA_node u (.color Y i) trivial]
      simp [Sat, hHc]
    | edge i j =>
      rw [newAtomTest, inA_node u (.edge i j) trivial, inA_node u (.eq i j) trivial,
        inA_node u (.nonEdge i j) trivial]
      unfold crossA
      rw [inA_node u (.color D.P i) trivial, inA_node u (.color D.Q j) trivial,
        inA_node u (.color D.Q i) trivial, inA_node u (.color D.P j) trivial]
      simp only [Sat, H, resolveBy]
      cases D.sign <;> simp [resolvePos, resolveNeg, between, SimpleGraph.fromRel_adj]
      all_goals tauto
    | nonEdge i j =>
      rw [newAtomTest, inA_node u (.nonEdge i j) trivial, inA_node u (.eq i j) trivial,
        inA_node u (.edge i j) trivial]
      unfold crossA
      rw [inA_node u (.color D.P i) trivial, inA_node u (.color D.Q j) trivial,
        inA_node u (.color D.Q i) trivial, inA_node u (.color D.P j) trivial]
      simp only [Sat, H, resolveBy]
      cases D.sign <;> simp [resolvePos, resolveNeg, between, SimpleGraph.fromRel_adj]
      all_goals tauto
    | distLe s i j =>
      have hs : s ≤ rhoMinus k q := by cases hr; assumption
      rw [newAtomTest, inA_node u hr trivial, hopTest_node D hc u i j (by omega)]
      simp only [Sat, hHr, withinDist_resolve_iff]
    | distColorLt s Y i =>
      have hs : s ≤ rhoPlus k q := by cases hr; assumption
      rw [newAtomTest, inA_node u hr trivial]
      simp only [Sat, hHc, hHr]
      cases s with
      | zero => simp [WithinDistLt]
      | succ s =>
        simp only [withinDistLt_succ, Finset.mem_range]
        rw [unary_resolve_iff (D := D)]
        refine or_congr Iff.rfl ?_
        rw [← unaryHopTest_node D hD u Y i hs]
        constructor
        · rintro ⟨s', -, hs', h⟩
          obtain rfl : s' = s := by omega
          exact h
        · intro h
          exact ⟨s, by omega, rfl, h⟩
    | not => exact absurd hat id
    | and => exact absurd hat id
    | exLocal => exact absurd hat id
  constructor
  · rintro ⟨hcand, ht⟩
    have : IsAtom φ ∧ DRank k q φ := by
      simp only [candidates, Finset.mem_union, Finset.mem_image, Finset.mem_product,
        Finset.mem_univ, Finset.mem_range] at hcand
      rcases hcand with (((((⟨p, -, rfl⟩ | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩) | ⟨p, -, rfl⟩) |
        ⟨p, ⟨hp, -⟩, rfl⟩) | ⟨p, ⟨hp, -⟩, rfl⟩)
      · exact ⟨trivial, .eq _ _⟩
      · exact ⟨trivial, .edge _ _⟩
      · exact ⟨trivial, .nonEdge _ _⟩
      · exact ⟨trivial, .color _ _⟩
      · exact ⟨trivial, .distLe _ _ _ (by omega)⟩
      · exact ⟨trivial, .distColorLt _ _ _ (by omega)⟩
    exact ⟨this.1, this.2, (htest this.1 this.2).1 ht⟩
  · rintro ⟨hat, hr, hs⟩
    refine ⟨?_, (htest hat hr).2 hs⟩
    simp only [candidates, Finset.mem_union, Finset.mem_image, Finset.mem_product,
      Finset.mem_univ, Finset.mem_range, true_and, and_true]
    cases φ with
    | eq i j => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨(i, j), rfl⟩))))
    | edge i j => exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, j), rfl⟩))))
    | nonEdge i j => exact Or.inl (Or.inl (Or.inl (Or.inr ⟨(i, j), rfl⟩)))
    | color Y i =>
      refine Or.inl (Or.inl (Or.inr ⟨(Y, i), (hc Y).2 ⟨u i, ?_⟩, rfl⟩))
      simpa [Sat, hHc] using hs
    | distLe s i j =>
      have : s ≤ rhoMinus k q := by cases hr; assumption
      exact Or.inl (Or.inr ⟨(s, i, j), by omega, rfl⟩)
    | distColorLt s Y i =>
      have : s ≤ rhoPlus k q := by cases hr; assumption
      obtain ⟨v, hv, -⟩ := hs
      rw [hHc] at hv
      exact Or.inr ⟨(s, Y, i), ⟨by omega, (hc Y).2 ⟨v, hv⟩⟩, rfl⟩
    | not => exact absurd hat id
    | and => exact absurd hat id
    | exLocal => exact absurd hat id

theorem domain_iff {a b k q : ℕ} (ha : a ≤ k) (hab : a + b = k + (q + 1)) (x : ℕ × TypeTree)
    (hx : x.2.k = k + 1) : x ∈ domain G a b ↔
      1 ≤ x.1 ∧ x.1 ≤ 9 ^ (k + 1) * rhoMinus (k + 1) q ∧ ∃ c, x.2 = tree G (k + 1) q ![c] := by
  constructor
  · rintro ⟨i, c, hi1, hib, h1, h2, hx2⟩
    have hk : a + i = k + 1 := by rw [← hx, hx2]; rfl
    have hq : b - i = q := by omega
    rw [hk, hq] at h2 hx2
    exact ⟨h1, h2, c, hx2⟩
  · rintro ⟨h1, h2, c, hx2⟩
    refine ⟨k + 1 - a, c, by omega, by omega, h1, ?_, ?_⟩
    · rwa [show a + (k + 1 - a) = k + 1 by omega, show b - (k + 1 - a) = q by omega]
    · rwa [show a + (k + 1 - a) = k + 1 by omega, show b - (k + 1 - a) = q by omega]

/-- The far tree reads only the entries of rank `(k+1, q)` of the scatter
type, and these entries of `stp_{k₀,q₀}` are those of `stp_{k,q+1}`. -/
theorem farTreeNode_stp_eq {k₀ q₀ k q ℓ : ℕ} (t : Node (q + 1) ℓ) (hk : k₀ ≤ k)
    (hs : k + (q + 1) = k₀ + q₀) :
    farTreeNode k q ℓ t (stp G k₀ q₀) = farTreeNode k q ℓ t (stp G k (q + 1)) := by
  have key : ∀ p : (ℕ × TypeTree) × ℕ, p.1.2.k = k + 1 →
      (p ∈ stp G k₀ q₀ ↔ p ∈ stp G k (q + 1)) := by
    intro p hp
    rw [mem_stp, mem_stp, domain_iff hk hs.symm p.1 hp, domain_iff le_rfl rfl p.1 hp]
    have : value G k₀ q₀ p.1 = value G k (q + 1) p.1 := by simp only [value, hs]
    rw [this]
  unfold farTreeNode
  ext ν
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨p, ⟨hp, hc⟩, rfl⟩; exact ⟨p, ⟨(key p hc.2.1).1 hp, hc⟩, rfl⟩
  · rintro ⟨p, ⟨hp, hc⟩, rfl⟩; exact ⟨p, ⟨(key p hc.2.1).2 hp, hc⟩, rfl⟩

theorem mem_far_part {ℓ q : ℕ} {α : Type*} [DecidableEq α] (S : Finset (TypeTree × Fin ℓ))
    (c : TypeTree × Fin ℓ → Node q 1 → Prop) [∀ p ν, Decidable (c p ν)]
    (f : TypeTree × Fin ℓ → Node q 1 → α) (e : α) :
    e ∈ S.biUnion (fun p => match TypeTree.rootAs p.1 q 1 with
      | none => ∅
      | some ν => if c p ν then {f p ν} else ∅) ↔
      ∃ p ∈ S, ∃ ν, TypeTree.rootAs p.1 q 1 = some ν ∧ c p ν ∧ e = f p ν := by
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨p, hp, he⟩
    revert he
    cases hr : TypeTree.rootAs p.1 q 1 with
    | none => simp
    | some ν =>
      intro he
      simp only at he
      split_ifs at he with hc
      · exact ⟨p, hp, ν, hr, hc, Finset.mem_singleton.1 he⟩
      · simp at he
  · rintro ⟨p, hp, ν, hr, hc, rfl⟩
    refine ⟨p, hp, ?_⟩
    rw [hr]
    simp [hc]

/-- **lem:resolve-lift, semantic form.** For correct data, `resolveNode`
maps the tree of a nonempty tuple in `G` to its tree after the resolve. -/
theorem resolveNode_node (D : ResolveData) {k₀ q₀ : ℕ} (hD : D.Spec G k₀ q₀) :
    ∀ (q k : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin n), 1 ≤ ℓ → ℓ ≤ k → k₀ ≤ k → k + q = k₀ + q₀ →
      resolveNode D k q (node G k q u) = node (resolveBy G D.sign D.P D.Q) k q u
  | 0, k, ℓ, u, _, _, _, _ => newAtoms_node D hD k 0 u
  | q + 1, k, ℓ, u, h1, hk, hk0, hs => by
    refine Node.ext_succ (newAtoms_node D hD k (q + 1) u) ?_
    set H := resolveBy G D.sign D.P D.Q
    set t := node G k (q + 1) u
    have hR := rhoMinus_le_rhoPlus (k + 1) q
    have hgam : ∀ (i : Fin ℓ) (b : Fin n), hopTest D (node G (k + 1) q (Fin.snoc u b))
        (rhoPlus (k + 1) q) i.castSucc (Fin.last ℓ) ↔ Hop G D.P D.Q (rhoPlus (k + 1) q) (u i) b := by
      intro i b
      rw [hopTest_node D hD.1 (Fin.snoc u b) _ _ le_rfl, Fin.snoc_castSucc, Fin.snoc_last]
    have hHd : ∀ (i : Fin ℓ) (b : Fin n), WithinDist H.resolved (rhoPlus (k + 1) q) (u i) b ↔
        WithinDist G.resolved (rhoPlus (k + 1) q) (u i) b ∨
          Hop G D.P D.Q (rhoPlus (k + 1) q) (u i) b := by
      intro i b
      rw [resolveBy_resolved, withinDist_resolve_iff]
    have hfar : ∀ ν, ν ∈ farTreeNode k q ℓ t D.σ ↔ ∃ b,
        (∀ i, ¬ WithinDist G.resolved (rhoMinus (k + 1) q) (u i) b) ∧
          ν = tree G (k + 1) q ![b] := by
      intro ν
      rw [hD.2.2, farTreeNode_stp_eq t hk0 (by omega), farTreeNode_node k q u h1 hk, mem_ftree]
    have hcomp : ∀ b, (∀ i, ¬ WithinDist G.resolved (rhoMinus (k + 1) q) (u i) b) →
        composeNode (ℓ₁ := ℓ) (ℓ₂ := 1) (shiftNode t) (node G (k + 1) q ![b]) =
          node G (k + 1) q (Fin.snoc u b) := by
      intro b hb
      rw [shiftNode_node G k q h1 u, composeNode_node G q (k + 1) u ![b] h1 le_rfl
        (fun i j => by rw [Fin.fin_one_eq_zero j]; exact hb i), Fin.append_right_eq_snoc]
      rfl
    have hC : ∀ e, e ∈ resolveCandidates D k q ℓ t ↔ ∃ (i : Fin ℓ) (b : Fin n),
        WithinDist H.resolved (rhoPlus (k + 1) q) (u i) b ∧
          e = (i, node G (k + 1) q (Fin.snoc u b)) := by
      intro e
      unfold resolveCandidates
      rw [Finset.mem_union, Finset.mem_union, mem_far_part, Finset.mem_image]
      simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
      constructor
      · rintro ((he | ⟨p, ⟨hp, hpg⟩, rfl⟩) | ⟨p, hp, ν, hr, hc, rfl⟩)
        · obtain ⟨i, b, hb, rfl⟩ := (mem_exts_node G k q u e).1 he
          exact ⟨i, b, (hHd i b).2 (Or.inl hb), rfl⟩
        · obtain ⟨j, b, hb, he⟩ := (mem_exts_node G k q u p.1).1 hp
          rw [he] at hpg
          refine ⟨p.2, b, (hHd p.2 b).2 (Or.inr ((hgam p.2 b).1 hpg)), ?_⟩
          rw [he]
        · obtain ⟨b, hbfar, hν⟩ := (hfar p.1).1 hp
          rw [hν, tree, TypeTree.rootAs_mk, Option.some.injEq] at hr
          subst hr
          rw [hcomp b hbfar] at hc ⊢
          exact ⟨p.2, b, (hHd p.2 b).2 (Or.inr ((hgam p.2 b).1 hc)), rfl⟩
      · rintro ⟨i, b, hb, rfl⟩
        rcases (hHd i b).1 hb with hG | hhop
        · exact Or.inl (Or.inl ((mem_exts_node G k q u _).2 ⟨i, b, hG, rfl⟩))
        · by_cases hnear : ∃ j, WithinDist G.resolved (rhoPlus (k + 1) q) (u j) b
          · obtain ⟨j, hj⟩ := hnear
            exact Or.inl (Or.inr ⟨((j, node G (k + 1) q (Fin.snoc u b)), i),
              ⟨(mem_exts_node G k q u _).2 ⟨j, b, hj, rfl⟩, (hgam i b).2 hhop⟩, rfl⟩)
          · push Not at hnear
            have hbfar : ∀ j, ¬ WithinDist G.resolved (rhoMinus (k + 1) q) (u j) b :=
              fun j hj => hnear j (withinDist_mono hR hj)
            refine Or.inr ⟨(tree G (k + 1) q ![b], i), (hfar _).2 ⟨b, hbfar, rfl⟩,
              node G (k + 1) q ![b], TypeTree.rootAs_mk _ _ _ _, ?_, ?_⟩
            · rw [hcomp b hbfar]; exact (hgam i b).2 hhop
            · rw [hcomp b hbfar]
    ext e
    show e ∈ (resolveCandidates D k q ℓ t).image (fun e => (e.1, resolveNode D (k + 1) q e.2)) ↔ _
    rw [Finset.mem_image, mem_exts_node]
    constructor
    · rintro ⟨e', he', rfl⟩
      obtain ⟨i, b, hb, rfl⟩ := (hC e').1 he'
      exact ⟨i, b, hb, by
        rw [resolveNode_node D hD q (k + 1) (Fin.snoc u b) (by omega) (by omega) (by omega)
          (by omega)]⟩
    · rintro ⟨i, b, hb, rfl⟩
      exact ⟨_, (hC _).2 ⟨i, b, hb, rfl⟩, by
        rw [resolveNode_node D hD q (k + 1) (Fin.snoc u b) (by omega) (by omega) (by omega)
          (by omega)]⟩

/-- **lem:resolve-lift, the family.** For correct data, `resolveFamily`
maps the type trees of all vertices in `G` to those in the partial graph
after the resolve. -/
theorem resolveFamily_family (D : ResolveData) {k q : ℕ} (hk : 1 ≤ k) (hD : D.Spec G k q) :
    resolveFamily D k q (family G k q) = family (resolveBy G D.sign D.P D.Q) k q := by
  funext b
  simp only [resolveFamily, family, tree, TypeTree.rootAs_mk]
  rw [resolveNode_node D hD q k ![b] le_rfl hk le_rfl rfl]

/-! ### The data from the partial graph -/

/-- The colors that occur, from the colors of the vertices. -/
def colsCore (col : Fin n → ℕ) : Finset ℕ := Finset.univ.image col

/-- The test `cd`, by breadth-first search from every vertex. -/
def cdCore (adj : Fin n → List (Fin n)) (col : Fin n → ℕ) (X Y s : ℕ) : Bool :=
  decide (∃ x : Fin n, col x = X ∧ ∃ y ∈ ballFrom adj x s, col y = Y)

theorem resolveData_spec {adj : Fin n → List (Fin n)}
    (hadj : ∀ u v, v ∈ adj u ↔ G.resolved.Adj u v) (P Q : ℕ) (sign : Bool) (k q : ℕ) :
    ResolveData.Spec ⟨P, Q, sign, colsCore G.color, cdCore adj G.color,
      stpCore adj (family G k q) k q⟩ G k q := by
  refine ⟨fun Y => ?_, fun X Y s => ?_, stpCore_eq hadj k q⟩
  · simp [colsCore, Occurs]
  · simp only [cdCore, decide_eq_true_iff, mem_ballFrom hadj]
    constructor
    · rintro ⟨x, hx, y, hy, hc⟩; exact ⟨x, y, hx, hc, hy⟩
    · rintro ⟨x, y, hx, hy, hd⟩; exact ⟨x, hx, y, hd, hy⟩

end Correctness

end Lax185574Proofs.TreeAlgo
