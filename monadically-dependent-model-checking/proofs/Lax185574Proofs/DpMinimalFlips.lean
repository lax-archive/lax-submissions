import Lax185574.DefinableFlipFormula
import Lax185574.DpMinimalFlips
import Lax185574.DpMinimalInterpretations
import Lax185574Proofs.FlipBasics

/-!
Definable flips preserve dp-minimality. An `S`-flip of `G` with
`|S| ≤ s` is `G ⊕ (p̄, R)` for a tuple `p̄` listing `S` and a symmetric
relation `R`, and each `G ⊕ (p̄, R)` is an interpretation of `G` with the
parameters `p̄` by one formula that depends only on `s` and `R`.
-/

namespace Lax185574Proofs.DpMinimalFlips

open FirstOrder FirstOrder.Language
open Lax185574.Graphs Lax185574.PhiPsiPatterns Lax185574.DpMinimality
open Lax185574.AtomicTypes Lax185574.Partitions Lax185574.Flips Lax185574.DefinableFlips
open Lax185574.DpMinimalInterpretations Lax185574.FlipsMonadicallyDependent
open Lax185574Proofs.FlipBasics

universe u

variable {V : Type u}

/-- Clean patterns restrict to smaller orders. -/
theorem hasCleanPattern_mono {G : SimpleGraph V} {p p' : ℕ}
    {φ : Language.graph.Formula (Fin p ⊕ Fin 1)} {ψ : Language.graph.Formula (Fin p' ⊕ Fin 1)}
    {t t' : ℕ} (h : t' ≤ t) (hp : HasCleanPattern G φ ψ t t) :
    HasCleanPattern G φ ψ t' t' := by
  obtain ⟨a, b, c, hp⟩ := hp
  refine ⟨a ∘ Fin.castLE h, b ∘ Fin.castLE h, fun i j => c (Fin.castLE h i) (Fin.castLE h j),
    fun i j => ⟨fun i' => ?_, fun j' => ?_⟩⟩
  · exact ((hp _ _).1 _).trans (Fin.castLE_inj)
  · exact ((hp _ _).2 _).trans (Fin.castLE_inj)

/-- A set of at most `s` vertices of a nonempty graph is contained in
the entries of an `s`-tuple. -/
theorem exists_tuple_cover [Nonempty V] (S : Finset V) {s : ℕ} (hS : S.card ≤ s) :
    ∃ p : Fin s → V, (S : Set V) ⊆ Set.range p := by
  classical
  let g : S → Fin s := fun x => Fin.castLE hS (S.equivFin x)
  have hg : Function.Injective g := fun x y h =>
    S.equivFin.injective (Fin.castLE_injective hS h)
  refine ⟨Function.extend g Subtype.val fun _ => Classical.arbitrary V, fun x hx => ?_⟩
  exact ⟨g ⟨x, hx⟩, hg.extend_apply _ _ _⟩

theorem pairType_eq_eq_iff (G : SimpleGraph V) (x y : V) : pairType G x y = .eq ↔ x = y := by
  unfold pairType
  split_ifs <;> simp_all

theorem pairType_eq_adj_iff (G : SimpleGraph V) (x y : V) :
    pairType G x y = .adj ↔ x ≠ y ∧ G.Adj x y := by
  unfold pairType
  split_ifs <;> simp_all

/-- Equal atomic types over a tuple whose entries contain `S` give the
same part of the partition into atomic types over `S`. -/
theorem atomicTypes_of_atomicTypeOver_eq {G : SimpleGraph V} {s : ℕ} {p : Fin s → V}
    {S : Set V} (hS : S ⊆ Set.range p) {x y : V}
    (h : atomicTypeOver G p x = atomicTypeOver G p y) : atomicTypes G S x y := by
  have hi : ∀ i, pairType G x (p i) = pairType G y (p i) := fun i => congrFun h i
  rw [atomicTypes_rel_iff']
  by_cases hxy : x = y
  · exact Or.inl hxy
  right
  have hx : x ∉ S := fun hx => by
    obtain ⟨i, rfl⟩ := hS hx
    have := (pairType_eq_eq_iff G y (p i)).mp ((hi i).symm.trans ((pairType_eq_eq_iff G _ _).mpr rfl))
    exact hxy this.symm
  have hy : y ∉ S := fun hy => by
    obtain ⟨i, rfl⟩ := hS hy
    have := (pairType_eq_eq_iff G x (p i)).mp ((hi i).trans ((pairType_eq_eq_iff G _ _).mpr rfl))
    exact hxy this
  refine ⟨hx, hy, fun z hz => ?_⟩
  obtain ⟨i, rfl⟩ := hS hz
  have hxz : x ≠ p i := fun e => hx (e ▸ hz)
  have hyz : y ≠ p i := fun e => hy (e ▸ hz)
  have h1 := pairType_eq_adj_iff G x (p i)
  have h2 := pairType_eq_adj_iff G y (p i)
  rw [hi i] at h1
  rw [h2] at h1
  simp only [ne_eq, hxz, hyz, not_false_eq_true, true_and] at h1
  exact h1.symm

/-- The pairs of atomic types over `p̄` between which `H` differs from
`G` on some pair of distinct vertices. -/
def flipRel (G H : SimpleGraph V) {s : ℕ} (p : Fin s → V)
    (P Q : Fin s → PairType) : Prop :=
  ∃ x y, atomicTypeOver G p x = P ∧ atomicTypeOver G p y = Q ∧ x ≠ y ∧
    ¬ (H.Adj x y ↔ G.Adj x y)

theorem flipRel_symm (G H : SimpleGraph V) {s : ℕ} (p : Fin s → V)
    (P Q : Fin s → PairType) (h : flipRel G H p P Q) : flipRel G H p Q P := by
  obtain ⟨x, y, hx, hy, hxy, hd⟩ := h
  exact ⟨y, x, hy, hx, hxy.symm, by rwa [H.adj_comm, G.adj_comm]⟩

/-- An `S`-flip is `G ⊕ (p̄, R)` for a tuple `p̄` whose entries contain `S`. -/
theorem eq_flipOver {G H : SimpleGraph V} {s : ℕ} {p : Fin s → V} {S : Set V}
    (hS : S ⊆ Set.range p) (hH : IsFlip G (atomicTypes G S) H) :
    H = flipOver G p (flipRel G H p) := by
  have hkey : ∀ x y, x ≠ y → (H.Adj x y ↔
      Xor (G.Adj x y) (flipRel G H p (atomicTypeOver G p x) (atomicTypeOver G p y))) := by
    intro x y hxy
    rcases hH x y with h | h
    · have hn : ¬ flipRel G H p (atomicTypeOver G p x) (atomicTypeOver G p y) := by
        rintro ⟨x', y', hx', hy', hne, hd⟩
        exact hd (h x' y' (atomicTypes_of_atomicTypeOver_eq hS hx')
          (atomicTypes_of_atomicTypeOver_eq hS hy') hne)
      simp only [Xor, hn, h x y (Setoid.refl' _ x) (Setoid.refl' _ y) hxy]
      tauto
    · have hd := h x y (Setoid.refl' _ x) (Setoid.refl' _ y) hxy
      have hn : flipRel G H p (atomicTypeOver G p x) (atomicTypeOver G p y) :=
        ⟨x, y, rfl, rfl, hxy, by rw [hd]; tauto⟩
      simp only [Xor, hn, hd]
      tauto
  ext x y
  unfold flipOver
  rw [SimpleGraph.fromRel_adj]
  constructor
  · intro h
    exact ⟨h.ne, Or.inl ((hkey x y h.ne).mp h)⟩
  · rintro ⟨hne, h | h⟩
    · exact (hkey x y hne).mpr h
    · exact H.adj_comm _ _ |>.mp ((hkey y x hne.symm).mpr h)

/-- The graph `G ⊕ (p̄, R)` is `α(G, p̄)` for a formula `α` that defines
its edges. -/
theorem interpretedGraph_eq_flipOver {s : ℕ}
    (R : (Fin s → PairType) → (Fin s → PairType) → Prop)
    (α : Language.graph.Formula (Fin 2 ⊕ Fin s)) (G : SimpleGraph V) (p : Fin s → V)
    (hα : ∀ x y : V, (flipOver G p R).Adj x y ↔
      @Formula.Realize Language.graph V G.structure _ α (Sum.elim ![x, y] p)) :
    interpretedGraph G α p = flipOver G p R := by
  ext x y
  unfold interpretedGraph
  rw [SimpleGraph.fromRel_adj, ← hα, ← hα]
  constructor
  · rintro ⟨-, h | h⟩
    · exact h
    · exact h.symm
  · intro h
    exact ⟨h.ne, Or.inl h⟩

/-- For a fixed symmetric relation `R`, the order of clean patterns in
the graphs `G ⊕ (p̄, R)` is bounded uniformly in `G` and `p̄`. -/
theorem exists_bound_flipOver (C : GraphClass) (hC : DpMinimal C) {s p p' : ℕ}
    (φ : Language.graph.Formula (Fin p ⊕ Fin 1)) (ψ : Language.graph.Formula (Fin p' ⊕ Fin 1))
    (R : (Fin s → PairType) → (Fin s → PairType) → Prop) (hR : ∀ P Q, R P Q → R Q P) :
    ∃ t : ℕ, ∀ G ∈ C, ∀ q : Fin s → Fin G.n,
      ¬ HasCleanPattern (flipOver G.toSimpleGraph q R) φ ψ t t := by
  obtain ⟨α, -, hα⟩ := Lax185574.DefinableFlipFormula.exists_isQF_flipOver_formula.{0} s R hR
  obtain ⟨t, ht⟩ := Lax185574.DpMinimalInterpretations.dpMinimal_interpretationClass
    C hC α φ ψ
  refine ⟨t, fun G hG q h => ?_⟩
  rw [← interpretedGraph_eq_flipOver R α G.toSimpleGraph q (hα _ _ q)] at h
  exact ht _ ⟨G, hG, q, rfl⟩ h

/--
---
conclusion: Lax185574.DpMinimalFlips.dpMinimal_definableFlipClass
---
Fix formulas `φ(x̄, z)` and `ψ(ȳ, z)`. For each symmetric relation `R` on
`Π^s`, the formula `E_{⊕R}(x, y; z̄)` defines the graphs `G ⊕ (p̄, R)`, so
preservation under interpretations bounds the order of clean
`(φ, ψ)`-patterns in these graphs for `G` in the class by some `t_R`. There
are finitely many relations `R`; let `T` be the maximum of the `t_R`. Clean
patterns restrict to smaller orders, so `T` bounds the order for every `R`.

An `S`-flip `H` of a nonempty `G` with `|S| ≤ s` is `G ⊕ (p̄, R)`, where
`p̄` lists `S` with repetitions, padded by any vertex, and `R` holds for
`(P, Q)` if `H` and `G` differ on some pair of distinct vertices of types
`P` and `Q`: this is symmetric, and vertices of equal type over `p̄` lie in
one part of the partition into atomic types over `S`. An empty graph has no
clean pattern of order `(T + 1) × (T + 1)`, as it has no vertex `c_{0,0}`.
So no `s`-definable flip contains such a pattern.
-/
theorem dpMinimal_definableFlipClass (C : GraphClass) (hC : DpMinimal C) (s : ℕ) :
    DpMinimal (definableFlipClass C s) := by
  intro p p' φ ψ
  have key : ∀ R : {R : (Fin s → PairType) → (Fin s → PairType) → Prop //
      ∀ P Q, R P Q → R Q P}, ∃ t : ℕ, ∀ G ∈ C, ∀ q : Fin s → Fin G.n,
        ¬ HasCleanPattern (flipOver G.toSimpleGraph q R.1) φ ψ t t :=
    fun R => exists_bound_flipOver C hC φ ψ R.1 R.2
  choose t ht using key
  obtain ⟨T, hT⟩ := Finite.exists_le t
  refine ⟨T + 1, ?_⟩
  rintro _ ⟨G, hG, F, ⟨S, hS, hF⟩, rfl⟩ hpat
  change HasCleanPattern F φ ψ (T + 1) (T + 1) at hpat
  have : Nonempty (Fin G.n) := by
    obtain ⟨_, _, c, _⟩ := hpat
    exact ⟨c 0 0⟩
  obtain ⟨q, hq⟩ := exists_tuple_cover S hS
  have hpat' : HasCleanPattern (flipOver G.toSimpleGraph q (flipRel G.toSimpleGraph F q))
      φ ψ (T + 1) (T + 1) := by
    rw [← eq_flipOver hq hF]
    exact hpat
  exact ht ⟨_, flipRel_symm G.toSimpleGraph F q⟩ G hG q
    (hasCleanPattern_mono ((hT _).trans (Nat.le_succ T)) hpat')

end Lax185574Proofs.DpMinimalFlips
