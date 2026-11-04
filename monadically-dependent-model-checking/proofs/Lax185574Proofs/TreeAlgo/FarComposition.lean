import Lax185574Proofs.TreeAlgo.RankShift
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
The semantic core of lem:compose. The far composition of two trees has as
root label the atoms of both roots, with the positions of the second
shifted behind those of the first. Atoms that mention both tuples are false
for far tuples. An extension `(i, μ)` of the first tree gives the extension
`(i, (μ ∗ shift τ₂) ↾ J)`, where `J` moves the new vertex behind the second
tuple, and an extension `(i, μ)` of the second tree gives
`(ℓ₁ + i, shift τ₁ ∗ μ)`. This is the recursion of the proof of
lem:compose, which uses the cores of lem:restrict and lem:shift.
-/

namespace Lax185574Proofs.TreeAlgo

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.WordEncoding
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO Lax185574.TypeTrees
open Lax185574Proofs.WalkDistance
open Lax3.DistFO (rhoMinus rhoPlus)

/-- The positions of `ā₁ b ā₂` in the order of `ā₁ ā₂ b`. -/
def moveLast (ℓ₁ ℓ₂ : ℕ) (t : Fin (ℓ₁ + ℓ₂ + 1)) : Fin (ℓ₁ + 1 + ℓ₂) :=
  ⟨if t.val = ℓ₁ + ℓ₂ then ℓ₁ else if t.val < ℓ₁ then t.val else t.val + 1, by
    have := t.isLt; split_ifs <;> omega⟩

/-- The inverse of `moveLast`. -/
def moveLastInv (ℓ₁ ℓ₂ : ℕ) (s : Fin (ℓ₁ + 1 + ℓ₂)) : Option (Fin (ℓ₁ + ℓ₂ + 1)) :=
  some ⟨if s.val < ℓ₁ then s.val else if s.val = ℓ₁ then ℓ₁ + ℓ₂ else s.val - 1, by
    have := s.isLt; split_ifs <;> omega⟩

theorem isPInv_moveLast (ℓ₁ ℓ₂ : ℕ) : IsPInv (moveLast ℓ₁ ℓ₂) (moveLastInv ℓ₁ ℓ₂) := by
  intro s t
  simp only [moveLastInv, moveLast, Option.some.injEq, Fin.ext_iff]
  have := s.isLt
  have := t.isLt
  split_ifs <;> omega

theorem append_snoc_comp_moveLast {V : Type*} {ℓ₁ ℓ₂ : ℕ} (u₁ : Fin ℓ₁ → V) (u₂ : Fin ℓ₂ → V)
    (b : V) : Fin.append (Fin.snoc u₁ b) u₂ ∘ moveLast ℓ₁ ℓ₂ = Fin.snoc (Fin.append u₁ u₂) b := by
  funext t
  refine Fin.lastCases ?_ (fun t => ?_) t
  · have : moveLast ℓ₁ ℓ₂ (Fin.last _) = Fin.castAdd ℓ₂ (Fin.last ℓ₁) := by
      simp [moveLast, Fin.ext_iff]
    simp [this]
  · refine Fin.addCases (fun t => ?_) (fun t => ?_) t
    · have : moveLast ℓ₁ ℓ₂ (Fin.castAdd ℓ₂ t).castSucc = Fin.castAdd ℓ₂ t.castSucc := by
        have := t.isLt
        simp only [moveLast, Fin.ext_iff, Fin.val_castSucc, Fin.val_castAdd]
        split_ifs <;> omega
      simp [this]
    · have : moveLast ℓ₁ ℓ₂ (Fin.natAdd ℓ₁ t).castSucc = Fin.natAdd (ℓ₁ + 1) t := by
        have := t.isLt
        simp only [moveLast, Fin.ext_iff, Fin.val_castSucc, Fin.val_natAdd]
        split_ifs <;> omega
      rw [Function.comp_apply, this, Fin.append_right, Fin.snoc_castSucc, Fin.append_right]

/-- Far composition of trees. -/
def composeNode : {q ℓ₁ ℓ₂ : ℕ} → Node q ℓ₁ → Node q ℓ₂ → Node q (ℓ₁ + ℓ₂)
  | 0, ℓ₁, ℓ₂, t₁, t₂ =>
      ((Node.atoms t₁).image (rename (Fin.castAdd ℓ₂)) ∪
        (Node.atoms t₂).image (rename (Fin.natAdd ℓ₁)) : Finset (DistFO (ℓ₁ + ℓ₂)))
  | _ + 1, ℓ₁, ℓ₂, t₁, t₂ =>
      ((Node.atoms t₁).image (rename (Fin.castAdd ℓ₂)) ∪
          (Node.atoms t₂).image (rename (Fin.natAdd ℓ₁)),
        (Node.exts t₁).image (fun e => (Fin.castAdd ℓ₂ e.1,
            restrictNode (moveLastInv ℓ₁ ℓ₂)
              (composeNode (ℓ₁ := ℓ₁ + 1) (ℓ₂ := ℓ₂) e.2 (shiftNode t₂)))) ∪
          (Node.exts t₂).image (fun e => (Fin.natAdd ℓ₁ e.1,
            composeNode (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂ + 1) (shiftNode t₁) e.2)))

theorem atoms_composeNode {q ℓ₁ ℓ₂ : ℕ} (t₁ : Node q ℓ₁) (t₂ : Node q ℓ₂) :
    Node.atoms (composeNode t₁ t₂) = (Node.atoms t₁).image (rename (Fin.castAdd ℓ₂)) ∪
        (Node.atoms t₂).image (rename (Fin.natAdd ℓ₁)) := by
  cases q <;> rfl

theorem exts_composeNode {q ℓ₁ ℓ₂ : ℕ} (t₁ : Node (q + 1) ℓ₁) (t₂ : Node (q + 1) ℓ₂) :
    Node.exts (composeNode t₁ t₂) = (Node.exts t₁).image (fun e => (Fin.castAdd ℓ₂ e.1,
            restrictNode (moveLastInv ℓ₁ ℓ₂)
              (composeNode (ℓ₁ := ℓ₁ + 1) (ℓ₂ := ℓ₂) e.2 (shiftNode t₂)))) ∪
          (Node.exts t₂).image (fun e => (Fin.natAdd ℓ₁ e.1,
            composeNode (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂ + 1) (shiftNode t₁) e.2)) :=
  rfl

/-! ### Atoms of far tuples -/

/-- The positions mentioned by an atom. -/
def atomPos {ℓ : ℕ} : DistFO ℓ → List (Fin ℓ)
  | .eq i j | .edge i j | .nonEdge i j | .distLe _ i j => [i, j]
  | .color _ i | .distColorLt _ _ i => [i]
  | _ => []

theorem pullAtom_isSome {p ℓ : ℕ} (g : Fin ℓ → Option (Fin p)) {φ : DistFO ℓ} (h : IsAtom φ)
    (hg : ∀ i ∈ atomPos φ, (g i).isSome) : (pullAtom g φ).isSome := by
  cases φ <;> simp_all [atomPos, pullAtom, IsAtom, Option.isSome_iff_exists] <;>
    first
    | (obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := hg; simp [ha, hb])
    | (obtain ⟨a, ha⟩ := hg; simp [ha])

variable {V : Type*}

/-- The positions of a true atom of distance rank `(k, q)` lie within
distance `ρ⁻(k, q)` of each other. -/
theorem withinDist_of_atom (G : PartialGraph V) {k q ℓ : ℕ} {φ : DistFO ℓ} (w : Fin ℓ → V)
    (hr : DRank k q φ) (hs : Sat G w φ) :
    ∀ i ∈ atomPos φ, ∀ j ∈ atomPos φ, WithinDist G.resolved (rhoMinus k q) (w i) (w j) := by
  have h1 : 1 ≤ rhoMinus k q := Nat.one_le_pow _ _ (by norm_num)
  have hpair : ∀ a b : V, WithinDist G.resolved (rhoMinus k q) a b →
      ∀ i ∈ [a, b], ∀ j ∈ [a, b], WithinDist G.resolved (rhoMinus k q) i j := by
    intro a b hab i hi j hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
    · exact withinDist_refl _ _ _
    · exact hab
    · exact withinDist_symm hab
    · exact withinDist_refl _ _ _
  have hadj : ∀ a b : V, G.resolved.Adj a b → WithinDist G.resolved (rhoMinus k q) a b :=
    fun a b h => ⟨SimpleGraph.Walk.cons h .nil, by simpa using h1⟩
  intro i hi j hj
  cases φ with
  | eq a b =>
    simp only [atomPos, List.mem_cons, List.not_mem_nil, or_false] at hi hj
    have : WithinDist G.resolved (rhoMinus k q) (w a) (w b) := by
      simp only [Sat] at hs; rw [hs]; exact withinDist_refl _ _ _
    exact hpair _ _ this (w i) (by rcases hi with rfl | rfl <;> simp) (w j)
      (by rcases hj with rfl | rfl <;> simp)
  | edge a b =>
    simp only [atomPos, List.mem_cons, List.not_mem_nil, or_false] at hi hj
    have := hadj _ _ (Or.inl hs)
    exact hpair _ _ this (w i) (by rcases hi with rfl | rfl <;> simp) (w j)
      (by rcases hj with rfl | rfl <;> simp)
  | nonEdge a b =>
    simp only [atomPos, List.mem_cons, List.not_mem_nil, or_false] at hi hj
    have := hadj _ _ (Or.inr hs)
    exact hpair _ _ this (w i) (by rcases hi with rfl | rfl <;> simp) (w j)
      (by rcases hj with rfl | rfl <;> simp)
  | distLe r a b =>
    simp only [atomPos, List.mem_cons, List.not_mem_nil, or_false] at hi hj
    cases hr with
    | distLe _ _ _ hle =>
      have := withinDist_mono hle hs
      exact hpair _ _ this (w i) (by rcases hi with rfl | rfl <;> simp) (w j)
        (by rcases hj with rfl | rfl <;> simp)
  | color Y a =>
    simp only [atomPos, List.mem_cons, List.not_mem_nil, or_false] at hi hj
    subst hi hj; exact withinDist_refl _ _ _
  | distColorLt r Y a =>
    simp only [atomPos, List.mem_cons, List.not_mem_nil, or_false] at hi hj
    subst hi hj; exact withinDist_refl _ _ _
  | not => simp [atomPos] at hi
  | and => simp [atomPos] at hi
  | exLocal => simp [atomPos] at hi

/-- The partial inverse of `Fin.castAdd`. -/
def leftPInv (ℓ₁ ℓ₂ : ℕ) (s : Fin (ℓ₁ + ℓ₂)) : Option (Fin ℓ₁) :=
  if h : s.val < ℓ₁ then some ⟨s.val, h⟩ else none

/-- The partial inverse of `Fin.natAdd`. -/
def rightPInv (ℓ₁ ℓ₂ : ℕ) (s : Fin (ℓ₁ + ℓ₂)) : Option (Fin ℓ₂) :=
  if h : ℓ₁ ≤ s.val then some ⟨s.val - ℓ₁, by have := s.isLt; omega⟩ else none

theorem isPInv_left (ℓ₁ ℓ₂ : ℕ) : IsPInv (Fin.castAdd ℓ₂ : Fin ℓ₁ → _) (leftPInv ℓ₁ ℓ₂) := by
  intro s t
  simp only [leftPInv, Fin.ext_iff, Fin.val_castAdd]
  split_ifs with h
  · simp only [Option.some.injEq, Fin.ext_iff]; omega
  · simp only [false_iff]; have := t.isLt; omega

theorem isPInv_right (ℓ₁ ℓ₂ : ℕ) : IsPInv (Fin.natAdd ℓ₁ : Fin ℓ₂ → _) (rightPInv ℓ₁ ℓ₂) := by
  intro s t
  simp only [rightPInv, Fin.ext_iff, Fin.val_natAdd]
  split_ifs with h
  · simp only [Option.some.injEq, Fin.ext_iff]; omega
  · simp only [false_iff]; omega

theorem append_comp_castAdd {ℓ₁ ℓ₂ : ℕ} (u₁ : Fin ℓ₁ → V) (u₂ : Fin ℓ₂ → V) :
    Fin.append u₁ u₂ ∘ Fin.castAdd ℓ₂ = u₁ := by funext i; simp

theorem append_comp_natAdd {ℓ₁ ℓ₂ : ℕ} (u₁ : Fin ℓ₁ → V) (u₂ : Fin ℓ₂ → V) :
    Fin.append u₁ u₂ ∘ Fin.natAdd ℓ₁ = u₂ := by funext i; simp

/-- Far tuples: no entry of `u₁` is within distance `d` of an entry of
`u₂`. -/
def Far (G : PartialGraph V) (d : ℕ) {ℓ₁ ℓ₂ : ℕ} (u₁ : Fin ℓ₁ → V) (u₂ : Fin ℓ₂ → V) : Prop :=
  ∀ i j, ¬ WithinDist G.resolved d (u₁ i) (u₂ j)

/-- The root label of the concatenation of far tuples. -/
theorem atoms_append [Finite V] (G : PartialGraph V) (k q : ℕ) {ℓ₁ ℓ₂ : ℕ}
    (u₁ : Fin ℓ₁ → V) (u₂ : Fin ℓ₂ → V) (hfar : Far G (rhoMinus k q) u₁ u₂) :
    Node.atoms (node G k q (Fin.append u₁ u₂)) =
      (Node.atoms (node G k q u₁)).image (rename (Fin.castAdd ℓ₂)) ∪
        (Node.atoms (node G k q u₂)).image (rename (Fin.natAdd ℓ₁)) := by
  ext ψ
  simp only [Finset.mem_union, Finset.mem_image, mem_atoms_node]
  constructor
  · rintro ⟨hat, hr, hs⟩
    have hw := withinDist_of_atom G _ hr hs
    -- all positions on one side
    by_cases hL : ∀ i ∈ atomPos ψ, (leftPInv ℓ₁ ℓ₂ i).isSome
    · obtain ⟨φ, hφ⟩ := Option.isSome_iff_exists.1 (pullAtom_isSome _ hat hL)
      obtain ⟨hφa, rfl⟩ := (pullAtom_eq_some (isPInv_left ℓ₁ ℓ₂) ψ φ).1 hφ
      refine Or.inl ⟨φ, ⟨hφa, (drank_rename_atom_iff _ hφa).1 hr, ?_⟩, rfl⟩
      rw [← append_comp_castAdd u₁ u₂]
      exact (sat_rename G _ _ φ).1 hs
    · have hR : ∀ i ∈ atomPos ψ, (rightPInv ℓ₁ ℓ₂ i).isSome := by
        push Not at hL
        obtain ⟨i₀, hi₀, hi₀'⟩ := hL
        have hi₀l : ℓ₁ ≤ i₀.val := by
          by_contra hc; simp [leftPInv, hc] at hi₀'
        intro j hj
        by_contra hj'
        have hjl : j.val < ℓ₁ := by
          by_contra hc; simp [rightPInv, (by omega : ℓ₁ ≤ j.val)] at hj'
        have := hw j hj i₀ hi₀
        have e1 : Fin.append u₁ u₂ j = u₁ ⟨j.val, hjl⟩ :=
          (congrArg (Fin.append u₁ u₂) (Fin.ext rfl : j = Fin.castAdd ℓ₂ ⟨j.val, hjl⟩)).trans
            (Fin.append_left u₁ u₂ _)
        have hi₀r : i₀.val - ℓ₁ < ℓ₂ := by have := i₀.isLt; omega
        have e2 : Fin.append u₁ u₂ i₀ = u₂ ⟨i₀.val - ℓ₁, hi₀r⟩ :=
          (congrArg (Fin.append u₁ u₂)
            (Fin.ext (by simp; omega) : i₀ = Fin.natAdd ℓ₁ ⟨i₀.val - ℓ₁, hi₀r⟩)).trans
            (Fin.append_right u₁ u₂ _)
        rw [e1, e2] at this
        exact hfar _ _ this
      obtain ⟨φ, hφ⟩ := Option.isSome_iff_exists.1 (pullAtom_isSome _ hat hR)
      obtain ⟨hφa, rfl⟩ := (pullAtom_eq_some (isPInv_right ℓ₁ ℓ₂) ψ φ).1 hφ
      refine Or.inr ⟨φ, ⟨hφa, (drank_rename_atom_iff _ hφa).1 hr, ?_⟩, rfl⟩
      rw [← append_comp_natAdd u₁ u₂]
      exact (sat_rename G _ _ φ).1 hs
  · rintro (⟨φ, ⟨hat, hr, hs⟩, rfl⟩ | ⟨φ, ⟨hat, hr, hs⟩, rfl⟩)
    · refine ⟨(isAtom_rename _).2 hat, drank_rename _ hr, ?_⟩
      rw [sat_rename, append_comp_castAdd]; exact hs
    · refine ⟨(isAtom_rename _).2 hat, drank_rename _ hr, ?_⟩
      rw [sat_rename, append_comp_natAdd]; exact hs

theorem rhoMinus_succ_le (k q : ℕ) : rhoMinus (k + 1) q ≤ rhoMinus k (q + 1) :=
  (rhoMinus_le_rhoPlus (k + 1) q).trans (le_trans (by omega) (two_mul_rhoPlus_le_rhoMinus k q))

/-- **Correctness of far composition.** -/
theorem composeNode_node [Finite V] (G : PartialGraph V) :
    ∀ (q k : ℕ) {ℓ₁ ℓ₂ : ℕ} (u₁ : Fin ℓ₁ → V) (u₂ : Fin ℓ₂ → V), 1 ≤ ℓ₁ → 1 ≤ ℓ₂ →
      Far G (rhoMinus k q) u₁ u₂ →
      composeNode (node G k q u₁) (node G k q u₂) = node G k q (Fin.append u₁ u₂)
  | 0, k, ℓ₁, ℓ₂, u₁, u₂, _, _, hfar => by
    show Node.atoms (composeNode (node G k 0 u₁) (node G k 0 u₂)) =
      Node.atoms (node G k 0 (Fin.append u₁ u₂))
    rw [atoms_composeNode, atoms_append G k 0 u₁ u₂ hfar]
  | q + 1, k, ℓ₁, ℓ₂, u₁, u₂, h₁, h₂, hfar => by
    refine Node.ext_succ ?_ ?_
    · rw [atoms_composeNode, atoms_append G k (q + 1) u₁ u₂ hfar]
    have hfar' : Far G (rhoMinus (k + 1) q) u₁ u₂ :=
      fun i j h => hfar i j (withinDist_mono (rhoMinus_succ_le k q) h)
    have h2 := two_mul_rhoPlus_le_rhoMinus k q
    have hm := rhoMinus_le_rhoPlus (k + 1) q
    -- the extended tuples stay far
    have farL : ∀ i b, WithinDist G.resolved (rhoPlus (k + 1) q) (u₁ i) b →
        Far G (rhoMinus (k + 1) q) (Fin.snoc u₁ b) u₂ := by
      intro i b hb i' j h
      induction i' using Fin.lastCases with
      | last =>
        rw [Fin.snoc_last] at h
        exact hfar i j (withinDist_mono (by omega) (withinDist_trans hb h))
      | cast i' =>
        rw [Fin.snoc_castSucc] at h
        exact hfar' i' j h
    have farR : ∀ j b, WithinDist G.resolved (rhoPlus (k + 1) q) (u₂ j) b →
        Far G (rhoMinus (k + 1) q) u₁ (Fin.snoc u₂ b) := by
      intro j b hb i j' h
      induction j' using Fin.lastCases with
      | last =>
        rw [Fin.snoc_last] at h
        exact hfar i j (withinDist_mono (by omega) (withinDist_trans h (withinDist_symm hb)))
      | cast j' =>
        rw [Fin.snoc_castSucc] at h
        exact hfar' i j' h
    have sh₁ := shiftNode_node G k q h₁ u₁
    have sh₂ := shiftNode_node G k q h₂ u₂
    have eL : ∀ i b, WithinDist G.resolved (rhoPlus (k + 1) q) (u₁ i) b →
        restrictNode (moveLastInv ℓ₁ ℓ₂) (composeNode (node G (k + 1) q (Fin.snoc u₁ b))
          (shiftNode (node G k (q + 1) u₂))) =
          node G (k + 1) q (Fin.snoc (Fin.append u₁ u₂) b) := by
      intro i b hb
      rw [sh₂, composeNode_node G q (k + 1) _ _ (by omega) h₂ (farL i b hb),
        restrictNode_node G q (k + 1) (isPInv_moveLast ℓ₁ ℓ₂), append_snoc_comp_moveLast]
    have eR : ∀ j b, WithinDist G.resolved (rhoPlus (k + 1) q) (u₂ j) b →
        composeNode (shiftNode (node G k (q + 1) u₁)) (node G (k + 1) q (Fin.snoc u₂ b)) =
          node G (k + 1) q (Fin.snoc (Fin.append u₁ u₂) b) := by
      intro j b hb
      rw [sh₁, composeNode_node G q (k + 1) _ _ h₁ (by omega) (farR j b hb), Fin.append_snoc]
    ext e
    rw [exts_composeNode, Finset.mem_union, Finset.mem_image, Finset.mem_image, mem_exts_node]
    constructor
    · rintro (⟨e', he', rfl⟩ | ⟨e', he', rfl⟩)
      · obtain ⟨i, b, hb, rfl⟩ := (mem_exts_node G k q u₁ e').1 he'
        exact ⟨Fin.castAdd ℓ₂ i, b, by simpa using hb, by rw [eL i b hb]⟩
      · obtain ⟨j, b, hb, rfl⟩ := (mem_exts_node G k q u₂ e').1 he'
        exact ⟨Fin.natAdd ℓ₁ j, b, by simpa using hb, by rw [eR j b hb]⟩
    · rintro ⟨i, b, hb, rfl⟩
      refine Fin.addCases (fun i hb => ?_) (fun j hb => ?_) i hb
      · rw [Fin.append_left] at hb
        exact Or.inl ⟨(i, node G (k + 1) q (Fin.snoc u₁ b)),
          (mem_exts_node G k q u₁ _).2 ⟨i, b, hb, rfl⟩, by rw [eL i b hb]⟩
      · rw [Fin.append_right] at hb
        exact Or.inr ⟨(j, node G (k + 1) q (Fin.snoc u₂ b)),
          (mem_exts_node G k q u₂ _).2 ⟨j, b, hb, rfl⟩, by rw [eR j b hb]⟩

/-! ### Size -/

theorem sum_union_le_nat {α : Type*} [DecidableEq α] (s t : Finset α) (f : α → ℕ) :
    ∑ x ∈ s ∪ t, f x ≤ ∑ x ∈ s, f x + ∑ x ∈ t, f x := by
  have := Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)
  omega

/-- **Size of far composition.** The number of nodes of `τ₁ ∗ τ₂` is at
most `(N₁ + N₂)^(q+1)`, where `Nᵢ` is the number of nodes of `τᵢ`. -/
theorem count_composeNode_le : ∀ {q ℓ₁ ℓ₂ : ℕ} (t₁ : Node q ℓ₁) (t₂ : Node q ℓ₂),
    Node.count (composeNode t₁ t₂) ≤ (Node.count t₁ + Node.count t₂) ^ (q + 1)
  | 0, _, _, t₁, t₂ => by
    have := Node.one_le_count t₁
    show 1 ≤ _
    simp only [zero_add, pow_one]
    omega
  | q + 1, ℓ₁, ℓ₂, t₁, t₂ => by
    set c₁ := Node.count t₁
    set c₂ := Node.count t₂
    set M := c₁ + c₂ - 1
    have hc₁ := Node.one_le_count t₁
    have hc₂ := Node.one_le_count t₂
    have hE₁ := Node.card_exts_lt_count t₁
    have hE₂ := Node.card_exts_lt_count t₂
    have hS₁ : Node.count (shiftNode t₁) ≤ c₁ := count_shiftNode_le t₁
    have hS₂ : Node.count (shiftNode t₂) ≤ c₂ := count_shiftNode_le t₂
    have hsum : ∑ e ∈ Node.exts (composeNode t₁ t₂), Node.count e.2 ≤
        ((Node.exts t₁).card + (Node.exts t₂).card) * M ^ (q + 1) := by
      rw [exts_composeNode]
      refine (sum_union_le_nat _ _ _).trans ?_
      rw [add_mul]
      refine Nat.add_le_add ?_ ?_
      · refine (sum_image_le_nat _ _ _).trans ?_
        rw [Finset.card_eq_sum_ones, Finset.sum_mul]
        refine Finset.sum_le_sum fun e he => ?_
        have := Node.count_child_lt t₁ he
        refine (count_restrictNode_le _ _).trans ((count_composeNode_le _ _).trans ?_)
        simp only [one_mul]
        exact Nat.pow_le_pow_left (by omega) _
      · refine (sum_image_le_nat _ _ _).trans ?_
        rw [Finset.card_eq_sum_ones, Finset.sum_mul]
        refine Finset.sum_le_sum fun e he => ?_
        have := Node.count_child_lt t₂ he
        refine (count_composeNode_le _ _).trans ?_
        simp only [one_mul]
        exact Nat.pow_le_pow_left (by omega) _
    show 1 + ∑ e ∈ Node.exts (composeNode t₁ t₂), Node.count e.2 ≤ (c₁ + c₂) ^ (q + 1 + 1)
    have hM : 1 ≤ M := by omega
    have hcard : (Node.exts t₁).card + (Node.exts t₂).card + 1 ≤ M := by omega
    have hpos : 1 ≤ M ^ (q + 1) := Nat.one_le_pow _ _ hM
    calc 1 + ∑ e ∈ Node.exts (composeNode t₁ t₂), Node.count e.2
        ≤ 1 + ((Node.exts t₁).card + (Node.exts t₂).card) * M ^ (q + 1) := by omega
      _ ≤ M ^ (q + 1) + ((Node.exts t₁).card + (Node.exts t₂).card) * M ^ (q + 1) := by omega
      _ = ((Node.exts t₁).card + (Node.exts t₂).card + 1) * M ^ (q + 1) := by ring
      _ ≤ M * M ^ (q + 1) := Nat.mul_le_mul_right _ hcard
      _ = M ^ (q + 1 + 1) := by ring
      _ ≤ (c₁ + c₂) ^ (q + 1 + 1) := Nat.pow_le_pow_left (by omega) _

/-- Far composition at most adds the sizes of the root labels. -/
theorem card_atoms_composeNode_le {q ℓ₁ ℓ₂ : ℕ} (t₁ : Node q ℓ₁) (t₂ : Node q ℓ₂) :
    (Node.atoms (composeNode t₁ t₂)).card ≤ (Node.atoms t₁).card + (Node.atoms t₂).card := by
  rw [atoms_composeNode]
  exact (Finset.card_union_le _ _).trans (Nat.add_le_add Finset.card_image_le Finset.card_image_le)

end Lax185574Proofs.TreeAlgo
