import Lax185574Proofs.ResolveRam.StpCut
import Lax185574Proofs.TreeAlgo.ResolveLift

/-!
The recursion of lem:resolve-lift with the far tree as a parameter. The
core `TreeAlgo.resolveNode` computes the far tree by the core of
lem:to-ftree. Here the far tree is a function `ft` of the tree and of a
scatter type, as computed by the program of lem:to-ftree. At rank
`(k, q+1)` it receives the restriction `stpCut (k+1) σ` of the scatter
type `σ = stp_{k₀,q₀}` of the top level, which is `stp_{k,q+1}` by
obs:stp-restrict. If `ft` computes far trees, the recursion maps the tree
of a tuple in `G` to its tree in `H = resolve^±_{P,Q}(G)`.
-/

namespace Lax185574Proofs.ResolveRam

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.WordEncoding
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.FarTrees Lax185574.ConstructionSequences
open Lax185574.ResolveLift Lax185574Proofs.WalkDistance Lax185574Proofs.TreeAlgo
open Lax3.DistFO (rhoMinus rhoPlus)

/-- A far tree map: from a tree of rank `(k, q+1)` and arity `ℓ` and a
scatter type, a set of type trees. -/
abbrev FarMap := (k q ℓ : ℕ) → Node (q + 1) ℓ → Finset ((ℕ × TypeTree) × ℕ) → Finset TypeTree

/-- The far candidate from a member `ν` of the far tree and a guard `i`:
the tree `shift τ ∗ ν` with guard `i` if it satisfies `γᵢ`. -/
def farPick (D : ResolveData) (k q ℓ : ℕ) (t : Node (q + 1) ℓ) (p : TypeTree × Fin ℓ) :
    Finset (Fin ℓ × Node q (ℓ + 1)) :=
  match TypeTree.rootAs p.1 q 1 with
  | none => ∅
  | some ν =>
    if hopTest D (composeNode (ℓ₁ := ℓ) (ℓ₂ := 1) (shiftNode t) ν) (rhoPlus (k + 1) q)
      p.2.castSucc (Fin.last ℓ)
    then {(p.2, composeNode (ℓ₁ := ℓ) (ℓ₂ := 1) (shiftNode t) ν)} else ∅

theorem mem_farPick (D : ResolveData) (k q ℓ : ℕ) (t : Node (q + 1) ℓ) (p : TypeTree × Fin ℓ)
    (e : Fin ℓ × Node q (ℓ + 1)) : e ∈ farPick D k q ℓ t p ↔
      ∃ ν, TypeTree.rootAs p.1 q 1 = some ν ∧
        hopTest D (composeNode (ℓ₁ := ℓ) (ℓ₂ := 1) (shiftNode t) ν) (rhoPlus (k + 1) q)
          p.2.castSucc (Fin.last ℓ) ∧ e = (p.2, composeNode (ℓ₁ := ℓ) (ℓ₂ := 1) (shiftNode t) ν) := by
  unfold farPick
  cases TypeTree.rootAs p.1 q 1 with
  | none => simp
  | some ν =>
    by_cases hc : hopTest D (composeNode (ℓ₁ := ℓ) (ℓ₂ := 1) (shiftNode t) ν) (rhoPlus (k + 1) q)
      p.2.castSucc (Fin.last ℓ) <;> simp [hc]

/-- The candidate extensions: old, near and far, with the far tree from `ft`. -/
def candidatesF (D : ResolveData) (ft : FarMap) (k q ℓ : ℕ) (t : Node (q + 1) ℓ) :
    Finset (Fin ℓ × Node q (ℓ + 1)) :=
  let R := rhoPlus (k + 1) q
  Node.exts t ∪
    ((Node.exts t ×ˢ (Finset.univ : Finset (Fin ℓ))).filter
      (fun p => hopTest D p.1.2 R p.2.castSucc (Fin.last ℓ))).image (fun p => (p.2, p.1.2)) ∪
    ((ft k q ℓ t (stpCut (k + 1) D.σ)) ×ˢ (Finset.univ : Finset (Fin ℓ))).biUnion
      (farPick D k q ℓ t)

/-- The lift of a tree through the resolve, with the far tree from `ft`. -/
def resolveNodeF (D : ResolveData) (ft : FarMap) : (k q : ℕ) → {ℓ : ℕ} → Node q ℓ → Node q ℓ
  | k, 0, _, t => newAtoms D k 0 t
  | k, q + 1, ℓ, t => (newAtoms D k (q + 1) t,
      (candidatesF D ft k q ℓ t).image fun e => (e.1, resolveNodeF D ft (k + 1) q e.2))

variable {n : ℕ} {G : PartialGraph (Fin n)}

/-- `ft` computes far trees in `G` from the right scatter type. -/
def FarSpec (G : PartialGraph (Fin n)) (ft : FarMap) : Prop :=
  ∀ (k q ℓ : ℕ) (u : Fin ℓ → Fin n), 1 ≤ ℓ → ℓ ≤ k →
    ft k q ℓ (node G k (q + 1) u) (stp G k (q + 1)) = ftree G k (q + 1) u

/-- The candidate extensions at a tuple `u` are the trees of `u b` for
the vertices `b` within `ρ⁺(k+1, q)` of an entry of `u` after the resolve,
with the guard of that entry. -/
theorem mem_candidatesF (D : ResolveData) (ft : FarMap) {k₀ q₀ : ℕ} (hD : D.Spec G k₀ q₀)
    (hft : FarSpec G ft) {q k ℓ : ℕ} (u : Fin ℓ → Fin n) (h1 : 1 ≤ ℓ) (hk : ℓ ≤ k)
    (hk0 : k₀ ≤ k) (hs : k + (q + 1) = k₀ + q₀) (e : Fin ℓ × Node q (ℓ + 1)) :
    e ∈ candidatesF D ft k q ℓ (node G k (q + 1) u) ↔ ∃ (i : Fin ℓ) (b : Fin n),
      WithinDist (resolveBy G D.sign D.P D.Q).resolved (rhoPlus (k + 1) q) (u i) b ∧
        e = (i, node G (k + 1) q (Fin.snoc u b)) := by
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
  have hfar : ∀ ν, ν ∈ ft k q ℓ t (stpCut (k + 1) D.σ) ↔ ∃ b,
      (∀ i, ¬ WithinDist G.resolved (rhoMinus (k + 1) q) (u i) b) ∧
        ν = tree G (k + 1) q ![b] := by
    intro ν
    rw [hD.2.2, stpCut_stp' G hk0 (by omega), hft k q ℓ u h1 hk, mem_ftree]
  have hcomp : ∀ b, (∀ i, ¬ WithinDist G.resolved (rhoMinus (k + 1) q) (u i) b) →
      composeNode (ℓ₁ := ℓ) (ℓ₂ := 1) (shiftNode t) (node G (k + 1) q ![b]) =
        node G (k + 1) q (Fin.snoc u b) := by
    intro b hb
    rw [shiftNode_node G k q h1 u, composeNode_node G q (k + 1) u ![b] h1 le_rfl
      (fun i j => by rw [Fin.fin_one_eq_zero j]; exact hb i), Fin.append_right_eq_snoc]
    rfl
  unfold candidatesF
  rw [Finset.mem_union, Finset.mem_union, Finset.mem_biUnion, Finset.mem_image]
  simp only [mem_farPick, Finset.mem_filter, Finset.mem_product, Finset.mem_univ, and_true]
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

/-- **lem:resolve-lift, semantic form.** For correct data and a correct
far tree map, `resolveNodeF` maps the tree of a nonempty tuple in `G` to
its tree after the resolve. -/
theorem resolveNodeF_node (D : ResolveData) (ft : FarMap) {k₀ q₀ : ℕ} (hD : D.Spec G k₀ q₀)
    (hft : FarSpec G ft) :
    ∀ (q k : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin n), 1 ≤ ℓ → ℓ ≤ k → k₀ ≤ k → k + q = k₀ + q₀ →
      resolveNodeF D ft k q (node G k q u) = node (resolveBy G D.sign D.P D.Q) k q u
  | 0, k, ℓ, u, _, _, _, _ => newAtoms_node D hD k 0 u
  | q + 1, k, ℓ, u, h1, hk, hk0, hs => by
    refine Node.ext_succ (newAtoms_node D hD k (q + 1) u) ?_
    have hC := fun e => mem_candidatesF D ft hD hft u h1 hk hk0 hs e
    ext e
    show e ∈ (candidatesF D ft k q ℓ (node G k (q + 1) u)).image (fun e => (e.1, resolveNodeF D ft (k + 1) q e.2)) ↔ _
    rw [Finset.mem_image, mem_exts_node]
    constructor
    · rintro ⟨e', he', rfl⟩
      obtain ⟨i, b, hb, rfl⟩ := (hC e').1 he'
      exact ⟨i, b, hb, by
        rw [resolveNodeF_node D ft hD hft q (k + 1) (Fin.snoc u b) (by omega) (by omega)
          (by omega) (by omega)]⟩
    · rintro ⟨i, b, hb, rfl⟩
      exact ⟨_, (hC _).2 ⟨i, b, hb, rfl⟩, by
        rw [resolveNodeF_node D ft hD hft q (k + 1) (Fin.snoc u b) (by omega) (by omega)
          (by omega) (by omega)]⟩

end Lax185574Proofs.ResolveRam
