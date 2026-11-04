import Lax185574.TypeTrees
import Lax185574Proofs.WalkDistance
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Fintype.Prod
import Lax185574Proofs.Legacy

/-!
Basic tools for the algorithms on type trees: decidable equality of
formulas and of type-tree nodes, the atoms and the extensions of a node,
the membership in the root of `tree_{k,q}(u)`, the renaming of the free
variables of a formula, and partial inverses of renamings, which turn an
atom over the positions of a tuple into an atom over the positions of a
subtuple.
-/

namespace Lax185574Proofs.TreeAlgo

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.WordEncoding
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO Lax185574.TypeTrees
open Lax3.DistFO (rhoMinus rhoPlus)

deriving instance DecidableEq for DistFO

/-- Decidable equality of nodes, by recursion on the depth. -/
@[instance_reducible] def Node.decEq : (q ℓ : ℕ) → DecidableEq (Node q ℓ)
  | 0, ℓ => inferInstanceAs (DecidableEq (Finset (DistFO ℓ)))
  | q + 1, ℓ =>
      letI := Node.decEq q (ℓ + 1)
      inferInstanceAs (DecidableEq (Finset (DistFO ℓ) × Finset (Fin ℓ × Node q (ℓ + 1))))

instance {q ℓ : ℕ} : DecidableEq (Node q ℓ) := Node.decEq q ℓ

/-- A type tree as a dependent pair of its header and its root. -/
def TypeTree.toSigma (t : TypeTree) : ℕ × Σ p : ℕ × ℕ, Node p.1 p.2 := (t.k, ⟨(t.q, t.ℓ), t.root⟩)

theorem TypeTree.toSigma_injective : Function.Injective TypeTree.toSigma := by
  rintro ⟨k, q, ℓ, r⟩ ⟨k', q', ℓ', r'⟩ h
  simp only [TypeTree.toSigma, Prod.mk.injEq] at h
  obtain ⟨rfl, h⟩ := h
  cases h
  rfl

instance : DecidableEq TypeTree := fun s t =>
  decidable_of_iff (TypeTree.toSigma s = TypeTree.toSigma t) TypeTree.toSigma_injective.eq_iff

/-- The atoms of a node, its root label. -/
def Node.atoms : {q ℓ : ℕ} → Node q ℓ → Finset (DistFO ℓ)
  | 0, _, t => t
  | _ + 1, _, t => t.1

/-- The extensions of a node of positive depth. -/
def Node.exts {q ℓ : ℕ} (t : Node (q + 1) ℓ) : Finset (Fin ℓ × Node q (ℓ + 1)) := t.2

/-- A node from its atoms, without extensions at depth `0`. -/
def Node.mk : {q ℓ : ℕ} → Finset (DistFO ℓ) →
    (match q with | 0 => Unit | q + 1 => Finset (Fin ℓ × Node q (ℓ + 1))) → Node q ℓ
  | 0, _, A, _ => A
  | _ + 1, _, A, E => (A, E)

@[simp] theorem Node.atoms_zero {ℓ : ℕ} (t : Node 0 ℓ) : Node.atoms t = t := rfl
@[simp] theorem Node.atoms_succ {q ℓ : ℕ} (t : Node (q + 1) ℓ) : Node.atoms t = t.1 := rfl
@[simp] theorem Node.exts_def {q ℓ : ℕ} (t : Node (q + 1) ℓ) : Node.exts t = t.2 := rfl

theorem Node.ext_succ {q ℓ : ℕ} {s t : Node (q + 1) ℓ} (h1 : Node.atoms s = Node.atoms t)
    (h2 : Node.exts s = Node.exts t) : s = t := Prod.ext h1 h2

/-- The number of nodes of a tree. -/
def Node.count : {q ℓ : ℕ} → Node q ℓ → ℕ
  | 0, _, _ => 1
  | _ + 1, _, t => 1 + ∑ e ∈ t.2, Node.count e.2

theorem Node.one_le_count : {q ℓ : ℕ} → (t : Node q ℓ) → 1 ≤ Node.count t
  | 0, _, _ => le_rfl
  | _ + 1, _, _ => Nat.le_add_right _ _

theorem Node.count_child_lt {q ℓ : ℕ} (t : Node (q + 1) ℓ) {e : Fin ℓ × Node q (ℓ + 1)}
    (he : e ∈ Node.exts t) : Node.count e.2 < Node.count t := by
  show _ < 1 + _
  have := Finset.single_le_sum (f := fun e : Fin ℓ × Node q (ℓ + 1) => Node.count e.2)
    (fun _ _ => Nat.zero_le _) he
  simp only [Node.exts_def] at this
  omega

theorem Node.card_exts_lt_count {q ℓ : ℕ} (t : Node (q + 1) ℓ) : (Node.exts t).card < Node.count t := by
  show _ < 1 + _
  have : (Node.exts t).card ≤ ∑ e ∈ t.2, Node.count e.2 := by
    rw [Finset.card_eq_sum_ones]
    exact Finset.sum_le_sum fun e _ => Node.one_le_count e.2
  simp only [Node.exts_def] at this ⊢
  omega

theorem sum_biUnion_le_nat {ι α : Type*} [DecidableEq α] (s : Finset ι) (t : ι → Finset α)
    (f : α → ℕ) : ∑ x ∈ s.biUnion t, f x ≤ ∑ i ∈ s, ∑ x ∈ t i, f x := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.biUnion_insert, Finset.sum_insert hi]
    have := Finset.sum_union_inter (s₁ := t i) (s₂ := s.biUnion t) (f := f)
    omega

theorem sum_image_le_nat {ι α : Type*} [DecidableEq α] (s : Finset ι) (g : ι → α)
    (f : α → ℕ) : ∑ x ∈ s.image g, f x ≤ ∑ i ∈ s, f (g i) := by
  classical
  have := sum_biUnion_le_nat s (fun i => {g i}) f
  rwa [Finset.biUnion_singleton] at this

/-! ### Finite sets of the definition -/

theorem mem_finsetOf {α : Type*} {S : Set α} (hS : S.Finite) {x : α} :
    x ∈ finsetOf S ↔ x ∈ S := by
  classical
  unfold finsetOf
  rw [dif_pos hS, hS.mem_toFinset]

variable {V : Type*}

/-- The atoms of distance rank `(k, q)` that a tuple satisfies form a finite
set on a finite vertex type: an atom is given by its kind, its positions,
a radius bounded by `ρ⁺(k, q)` and a color of some vertex. -/
theorem atp_finite [Finite V] (G : PartialGraph V) (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → V) :
    (atp G k q u).Finite := by
  have : Fintype V := Fintype.ofFinite V
  classical
  let R := rhoPlus k q
  let C : Finset ℕ := Finset.univ.image G.color
  let F : Finset (DistFO ℓ) :=
    (Finset.univ ×ˢ Finset.univ).image (fun p : Fin ℓ × Fin ℓ => DistFO.eq p.1 p.2) ∪
    (Finset.univ ×ˢ Finset.univ).image (fun p : Fin ℓ × Fin ℓ => DistFO.edge p.1 p.2) ∪
    (Finset.univ ×ˢ Finset.univ).image (fun p : Fin ℓ × Fin ℓ => DistFO.nonEdge p.1 p.2) ∪
    (C ×ˢ Finset.univ).image (fun p : ℕ × Fin ℓ => DistFO.color p.1 p.2) ∪
    (Finset.range (R + 1) ×ˢ (Finset.univ ×ˢ Finset.univ)).image
      (fun p : ℕ × Fin ℓ × Fin ℓ => DistFO.distLe p.1 p.2.1 p.2.2) ∪
    (Finset.range (R + 1) ×ˢ (C ×ˢ Finset.univ)).image
      (fun p : ℕ × ℕ × Fin ℓ => DistFO.distColorLt p.1 p.2.1 p.2.2)
  refine F.finite_toSet.subset ?_
  rintro φ ⟨hat, hr, hs⟩
  have hRm := Lax185574Proofs.WalkDistance.rhoMinus_le_rhoPlus k q
  cases φ with
  | eq i j => simp [F]
  | edge i j => simp [F]
  | nonEdge i j => simp [F]
  | color Y i =>
    simp only [Sat] at hs
    simp [F, C, ← hs]
  | distLe r i j =>
    cases hr with
    | distLe _ _ _ h => simp [F, R]; omega
  | distColorLt r Y i =>
    obtain ⟨v, hv, -⟩ := hs
    cases hr with
    | distColorLt _ _ _ h => simp [F, R, C]; exact ⟨by omega, v, hv⟩
  | not => exact absurd hat id
  | and => exact absurd hat id
  | exLocal => exact absurd hat id

theorem exts_set_finite [Finite V] (G : PartialGraph V) (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → V) :
    {e : Fin ℓ × Node q (ℓ + 1) | ∃ (i : Fin ℓ) (b : V),
      WithinDist G.resolved (rhoPlus (k + 1) q) (u i) b ∧
      e = (i, node G (k + 1) q (Fin.snoc u b))}.Finite := by
  refine (Set.finite_range fun p : Fin ℓ × V => (p.1, node G (k + 1) q (Fin.snoc u p.2))).subset ?_
  rintro e ⟨i, b, -, rfl⟩
  exact ⟨(i, b), rfl⟩

theorem mem_atoms_node [Finite V] (G : PartialGraph V) (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → V)
    (φ : DistFO ℓ) : φ ∈ Node.atoms (node G k q u) ↔ IsAtom φ ∧ DRank k q φ ∧ Sat G u φ := by
  cases q with
  | zero => exact mem_finsetOf (atp_finite G k 0 u)
  | succ q => exact mem_finsetOf (atp_finite G k (q + 1) u)

theorem mem_exts_node [Finite V] (G : PartialGraph V) (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → V)
    (e : Fin ℓ × Node q (ℓ + 1)) : e ∈ Node.exts (node G k (q + 1) u) ↔
      ∃ (i : Fin ℓ) (b : V), WithinDist G.resolved (rhoPlus (k + 1) q) (u i) b ∧
        e = (i, node G (k + 1) q (Fin.snoc u b)) :=
  mem_finsetOf (exts_set_finite G k q u)

/-! ### Renaming variables -/

/-- Renaming the free variables of a formula along `f`. A local quantifier
binds the new last variable, which is kept last. -/
def rename : {p ℓ : ℕ} → (Fin p → Fin ℓ) → DistFO p → DistFO ℓ
  | _, _, f, .eq i j => .eq (f i) (f j)
  | _, _, f, .edge i j => .edge (f i) (f j)
  | _, _, f, .nonEdge i j => .nonEdge (f i) (f j)
  | _, _, f, .color Y i => .color Y (f i)
  | _, _, f, .distLe r i j => .distLe r (f i) (f j)
  | _, _, f, .distColorLt r Y i => .distColorLt r Y (f i)
  | _, _, f, .not φ => .not (rename f φ)
  | _, _, f, .and φ ψ => .and (rename f φ) (rename f ψ)
  | _, _, f, .exLocal i s φ => .exLocal (f i) s (rename (Fin.lastCases (Fin.last _)
      (fun j => (f j).castSucc)) φ)

theorem sat_rename (G : PartialGraph V) : {p ℓ : ℕ} → (f : Fin p → Fin ℓ) → (u : Fin ℓ → V) →
    (φ : DistFO p) → (Sat G u (rename f φ) ↔ Sat G (u ∘ f) φ)
  | _, _, f, u, .eq i j => Iff.rfl
  | _, _, f, u, .edge i j => Iff.rfl
  | _, _, f, u, .nonEdge i j => Iff.rfl
  | _, _, f, u, .color Y i => Iff.rfl
  | _, _, f, u, .distLe r i j => Iff.rfl
  | _, _, f, u, .distColorLt r Y i => Iff.rfl
  | _, _, f, u, .not φ => not_congr (sat_rename G f u φ)
  | _, _, f, u, .and φ ψ => and_congr (sat_rename G f u φ) (sat_rename G f u ψ)
  | _, _, f, u, .exLocal i s φ => by
    simp only [rename, Sat]
    refine exists_congr fun v => and_congr Iff.rfl ?_
    rw [sat_rename G _ _ φ]
    have : (Fin.snoc u v ∘ Fin.lastCases (Fin.last _) fun j => (f j).castSucc) =
        (Fin.snoc (u ∘ f) v : _ → V) := by
      funext j
      refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
    rw [this]

theorem drank_rename : {k q p ℓ : ℕ} → (f : Fin p → Fin ℓ) → {φ : DistFO p} →
    DRank k q φ → DRank k q (rename f φ)
  | _, _, _, _, _, _, .eq i j => .eq _ _
  | _, _, _, _, _, _, .edge i j => .edge _ _
  | _, _, _, _, _, _, .nonEdge i j => .nonEdge _ _
  | _, _, _, _, _, _, .color Y i => .color _ _
  | _, _, _, _, _, _, .distLe r i j h => .distLe _ _ _ h
  | _, _, _, _, _, _, .distColorLt r Y i h => .distColorLt _ _ _ h
  | _, _, _, _, _, _, .not h => .not (drank_rename _ h)
  | _, _, _, _, _, _, .and h h' => .and (drank_rename _ h) (drank_rename _ h')
  | _, _, _, _, _, _, .exLocal i h => .exLocal _ (drank_rename _ h)

theorem isAtom_rename {p ℓ : ℕ} (f : Fin p → Fin ℓ) {φ : DistFO p} :
    IsAtom (rename f φ) ↔ IsAtom φ := by
  cases φ <;> simp [rename, IsAtom]

/-- On atoms, the distance rank depends only on the kind and the radius,
not on the positions. -/
theorem drank_rename_atom_iff {k q p ℓ : ℕ} (f : Fin p → Fin ℓ) {φ : DistFO p} (h : IsAtom φ) :
    DRank k q (rename f φ) ↔ DRank k q φ := by
  refine ⟨fun hr => ?_, drank_rename f⟩
  cases φ with
  | eq => exact .eq _ _
  | edge => exact .edge _ _
  | nonEdge => exact .nonEdge _ _
  | color => exact .color _ _
  | distLe r i j => cases hr with | distLe _ _ _ h => exact .distLe _ _ _ h
  | distColorLt r Y i => cases hr with | distColorLt _ _ _ h => exact .distColorLt _ _ _ h
  | not => exact absurd h id
  | and => exact absurd h id
  | exLocal => exact absurd h id

/-! ### Partial inverses -/

/-- `g` is a partial inverse of `f`: `g i = some j` exactly when `f j = i`.
Then `f` is injective. -/
def IsPInv {p ℓ : ℕ} (f : Fin p → Fin ℓ) (g : Fin ℓ → Option (Fin p)) : Prop :=
  ∀ i j, g i = some j ↔ f j = i

theorem IsPInv.injective {p ℓ : ℕ} {f : Fin p → Fin ℓ} {g : Fin ℓ → Option (Fin p)}
    (h : IsPInv f g) : Function.Injective f := by
  intro a b hab
  have h1 := (h (f a) a).2 rfl
  have h2 := (h (f a) b).2 hab.symm
  rw [h1] at h2
  exact Option.some_injective _ h2

/-- The partial inverse of the extension of `f` by the new last variable. -/
def liftPInv {p ℓ : ℕ} (g : Fin ℓ → Option (Fin p)) : Fin (ℓ + 1) → Option (Fin (p + 1)) :=
  Fin.lastCases (some (Fin.last p)) fun i => (g i).map Fin.castSucc

/-- The extension of `f` by the new last variable. -/
def liftMap {p ℓ : ℕ} (f : Fin p → Fin ℓ) : Fin (p + 1) → Fin (ℓ + 1) :=
  Fin.lastCases (Fin.last ℓ) fun j => (f j).castSucc

theorem IsPInv.lift {p ℓ : ℕ} {f : Fin p → Fin ℓ} {g : Fin ℓ → Option (Fin p)}
    (h : IsPInv f g) : IsPInv (liftMap f) (liftPInv g) := by
  intro i j
  refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
  · simp [liftPInv, liftMap]
  · simp only [liftPInv, liftMap, Fin.lastCases_last, Fin.lastCases_castSucc, Option.some.injEq,
      Fin.ext_iff, Fin.val_last, Fin.val_castSucc]
    have := j.isLt
    have := (f j).isLt
    omega
  · simp only [liftPInv, liftMap, Fin.lastCases_castSucc, Fin.lastCases_last, Option.map_eq_some_iff]
    constructor
    · rintro ⟨a, -, ha⟩
      exact absurd ha (Fin.castSucc_ne_last a)
    · intro hh
      exact absurd hh.symm (Fin.castSucc_ne_last i)
  · simp only [liftPInv, liftMap, Fin.lastCases_castSucc, Option.map_eq_some_iff,
      Fin.castSucc_inj]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact (h i a).1 ha
    · intro hh
      exact ⟨j, (h i j).2 hh, rfl⟩

theorem snoc_comp_liftMap {p ℓ : ℕ} (f : Fin p → Fin ℓ) (u : Fin ℓ → V) (b : V) :
    (Fin.snoc u b : Fin (ℓ + 1) → V) ∘ liftMap f = Fin.snoc (u ∘ f) b := by
  funext j
  refine Fin.lastCases ?_ (fun j => ?_) j <;> simp [liftMap]

/-- An atom over `Fin ℓ` with its positions mapped back along the partial
inverse `g`, if all positions have a preimage. Other formulas give
nothing. -/
def pullAtom {p ℓ : ℕ} (g : Fin ℓ → Option (Fin p)) : DistFO ℓ → Option (DistFO p)
  | .eq i j => do let a ← g i; let b ← g j; pure (.eq a b)
  | .edge i j => do let a ← g i; let b ← g j; pure (.edge a b)
  | .nonEdge i j => do let a ← g i; let b ← g j; pure (.nonEdge a b)
  | .color Y i => do let a ← g i; pure (.color Y a)
  | .distLe r i j => do let a ← g i; let b ← g j; pure (.distLe r a b)
  | .distColorLt r Y i => do let a ← g i; pure (.distColorLt r Y a)
  | _ => none

theorem pullAtom_eq_some {p ℓ : ℕ} {f : Fin p → Fin ℓ} {g : Fin ℓ → Option (Fin p)}
    (h : IsPInv f g) (φ : DistFO ℓ) (ψ : DistFO p) :
    pullAtom g φ = some ψ ↔ IsAtom ψ ∧ rename f ψ = φ := by
  cases φ <;> cases ψ <;>
    simp [pullAtom, rename, IsAtom, Option.bind_eq_some_iff, h _ _] <;> grind

end Lax185574Proofs.TreeAlgo
