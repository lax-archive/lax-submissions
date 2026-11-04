import Lax185574Proofs.ResolveRam.Script
import Lax185574Proofs.EncodingInjectivity
import Lax185574Proofs.Words.TreeWord
import Lax185574Proofs.TreeAlgo.ToFarTree

/-!
The expansion of an item, as the program computes it.

The program reads the extensions of a node in the order of their words
(`elems`). It gets the shifted tree, the far tree and the compositions
from its callees: `sh`, `fa` and `co` stand for their answers. The
expansion `exG` lists the old extensions, the old extensions `(j, μ)`
with guard `i` whenever `Hop` holds between `xᵢ` and the new vertex in
the root of `μ`, and the compositions `shift τ ∗ ν` of the members `ν` of
the far tree with guard `i` under the same test. If the answers are right
on the trees of tuples of `G` (`AnsOK`), the expansion is right
(`expandOK_exG`).
-/

namespace Lax185574Proofs.ResolveRam

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.WordEncoding
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.FarTrees Lax185574.ConstructionSequences
open Lax185574.ResolveLift Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo
open Lax185574Proofs.WalkDistance Lax185574Proofs.Words
open Lax3.DistFO (rhoMinus rhoPlus)

section Elems

variable {α : Type*} [WordEncoding α]

/-- The elements of a finite set, in the order of their words. -/
noncomputable def elems (S : Finset α) : List α :=
  S.words.filterMap fun w => S.toList.find? fun x => toWord x = w

theorem find_words {S : Finset α} {w : List ℕ} (hw : w ∈ S.words) :
    ∃ x, (S.toList.find? fun x => toWord x = w) = some x ∧ toWord x = w := by
  obtain ⟨a, ha, haw⟩ := mem_words.1 hw
  cases h : S.toList.find? fun x => toWord x = w with
  | none =>
    rw [List.find?_eq_none] at h
    exact absurd (by simpa using haw) (h a (Finset.mem_toList.2 ha))
  | some x =>
    have := List.find?_some h
    exact ⟨x, rfl, by simpa using this⟩

theorem map_filterMap_words {l : List (List ℕ)} {f : List ℕ → Option α}
    (h : ∀ w ∈ l, ∃ x, f w = some x ∧ toWord x = w) : (l.filterMap f).map toWord = l := by
  induction l with
  | nil => rfl
  | cons w l ih =>
    obtain ⟨x, hx, hxw⟩ := h w (by simp)
    rw [List.filterMap_cons, hx]
    simp only [List.map_cons, hxw, ih fun w' hw' => h w' (by simp [hw'])]

theorem map_elems (S : Finset α) : (elems S).map toWord = S.words :=
  map_filterMap_words fun _ hw => find_words hw

theorem mem_elems [PrefixFree α] {S : Finset α} {x : α} : x ∈ elems S ↔ x ∈ S := by
  simp only [elems, List.mem_filterMap]
  constructor
  · rintro ⟨w, -, hx⟩
    exact Finset.mem_toList.1 (List.mem_of_find?_eq_some hx)
  · intro hx
    have hw : toWord x ∈ S.words := mem_words.2 ⟨x, hx, rfl⟩
    obtain ⟨y, hy, hyw⟩ := find_words hw
    exact ⟨_, hw, by rw [hy, toWord_injective hyw]⟩

end Elems

/-- The guards `i` at which the root `r` passes the test `γᵢ`, with the
child `c`. -/
def guarded (D : ResolveData) {q ℓ : ℕ} (R : ℕ) (r : Node q (ℓ + 1)) (c : TypeTree) :
    List (ℕ × TypeTree) :=
  (List.finRange ℓ).filterMap fun i =>
    if hopTest D r R i.castSucc (Fin.last ℓ) then some (i.val, c) else none

theorem mem_guarded (D : ResolveData) {q ℓ : ℕ} (R : ℕ) (r : Node q (ℓ + 1)) (c : TypeTree)
    (p : ℕ × TypeTree) :
    p ∈ guarded D R r c ↔ ∃ i : Fin ℓ, hopTest D r R i.castSucc (Fin.last ℓ) ∧ p = (i.val, c) := by
  simp only [guarded, List.mem_filterMap, List.mem_finRange, true_and]
  constructor
  · rintro ⟨i, hi⟩
    by_cases h : hopTest D r R i.castSucc (Fin.last ℓ)
    · rw [if_pos h, Option.some.injEq] at hi; exact ⟨i, h, hi.symm⟩
    · rw [if_neg h] at hi; exact absurd hi (by simp)
  · rintro ⟨i, h, rfl⟩
    exact ⟨i, by rw [if_pos h]⟩

/-- The expansion of a node of rank `(k, q+1)` and arity `ℓ`, from the
answers `sh`, `fa`, `co` of the callees. -/
noncomputable def exAt (D : ResolveData) (sh : TypeTree → TypeTree) (fa : TypeTree → List TypeTree)
    (co : TypeTree → TypeTree → TypeTree) (k q ℓ : ℕ) (t : Node (q + 1) ℓ) :
    List (ℕ × TypeTree) :=
  let τ : TypeTree := ⟨k, q + 1, ℓ, t⟩
  let R := rhoPlus (k + 1) q
  let ex := elems (Node.exts t)
  ex.map (fun e => (e.1.val, (⟨k + 1, q, ℓ + 1, e.2⟩ : TypeTree))) ++
    ex.flatMap (fun e => guarded D R e.2 ⟨k + 1, q, ℓ + 1, e.2⟩) ++
    (fa τ).flatMap fun ν =>
      (TypeTree.rootAs (co (sh τ) ν) q (ℓ + 1)).toList.flatMap fun r =>
        guarded D R r (co (sh τ) ν)

/-- The expansion of an item. -/
noncomputable def exG (D : ResolveData) (sh : TypeTree → TypeTree) (fa : TypeTree → List TypeTree)
    (co : TypeTree → TypeTree → TypeTree) : TypeTree → List (ℕ × TypeTree)
  | ⟨k, q + 1, ℓ, t⟩ => exAt D sh fa co k q ℓ t
  | ⟨_, 0, _, _⟩ => []

variable {n : ℕ} {G : PartialGraph (Fin n)}

/-- The answers of the callees are right on the trees of tuples of `G`:
the rank shift, the far tree (from the restricted scatter type, so only
below the top rank) and the composition with a far vertex. -/
structure AnsOK (G : PartialGraph (Fin n)) (sh : TypeTree → TypeTree)
    (fa : TypeTree → List TypeTree) (co : TypeTree → TypeTree → TypeTree) (k₀ q₀ : ℕ) : Prop where
  sh : ∀ (k q ℓ : ℕ) (u : Fin ℓ → Fin n), 1 ≤ ℓ → ℓ ≤ k →
    sh (tree G k (q + 1) u) = tree G (k + 1) q u
  fa : ∀ (k q ℓ : ℕ) (u : Fin ℓ → Fin n), 1 ≤ ℓ → ℓ ≤ k → k₀ ≤ k → k + (q + 1) = k₀ + q₀ →
    ∀ ν, ν ∈ fa (tree G k (q + 1) u) ↔ ν ∈ ftree G k (q + 1) u
  co : ∀ (k q ℓ : ℕ) (u : Fin ℓ → Fin n) (b : Fin n), 1 ≤ ℓ → ℓ ≤ k →
    (∀ i, ¬ WithinDist G.resolved (rhoMinus (k + 1) q) (u i) b) →
    co (tree G (k + 1) q u) (tree G (k + 1) q ![b]) = tree G (k + 1) q (Fin.snoc u b)

theorem mem_exAt (D : ResolveData) {k₀ q₀ : ℕ} (hD : D.Spec G k₀ q₀)
    {sh : TypeTree → TypeTree} {fa : TypeTree → List TypeTree}
    {co : TypeTree → TypeTree → TypeTree} (hA : AnsOK G sh fa co k₀ q₀) {k q ℓ : ℕ}
    (u : Fin ℓ → Fin n) (h1 : 1 ≤ ℓ) (hk : ℓ ≤ k) (hk0 : k₀ ≤ k) (hs : k + (q + 1) = k₀ + q₀)
    (p : ℕ × TypeTree) :
    p ∈ exAt D sh fa co k q ℓ (node G k (q + 1) u) ↔ ∃ (i : Fin ℓ) (b : Fin n),
      WithinDist (resolveBy G D.sign D.P D.Q).resolved (rhoPlus (k + 1) q) (u i) b ∧
        p = (i.val, tree G (k + 1) q (Fin.snoc u b)) := by
  have := Lax185574Proofs.EncodingInjectivity.prefixFree_node q (ℓ + 1)
  have hR := rhoMinus_le_rhoPlus (k + 1) q
  have hgam : ∀ (i : Fin ℓ) (b : Fin n), hopTest D (node G (k + 1) q (Fin.snoc u b))
      (rhoPlus (k + 1) q) i.castSucc (Fin.last ℓ) ↔ Hop G D.P D.Q (rhoPlus (k + 1) q) (u i) b := by
    intro i b
    rw [hopTest_node D hD.1 (Fin.snoc u b) _ _ le_rfl, Fin.snoc_castSucc, Fin.snoc_last]
  have hHd : ∀ (i : Fin ℓ) (b : Fin n),
      WithinDist (resolveBy G D.sign D.P D.Q).resolved (rhoPlus (k + 1) q) (u i) b ↔
        WithinDist G.resolved (rhoPlus (k + 1) q) (u i) b ∨
          Hop G D.P D.Q (rhoPlus (k + 1) q) (u i) b := by
    intro i b
    rw [resolveBy_resolved, withinDist_resolve_iff]
  have hτ : (⟨k, q + 1, ℓ, node G k (q + 1) u⟩ : TypeTree) = tree G k (q + 1) u := rfl
  have hfar : ∀ ν, ν ∈ fa (tree G k (q + 1) u) ↔ ∃ b,
      (∀ i, ¬ WithinDist G.resolved (rhoMinus (k + 1) q) (u i) b) ∧
        ν = tree G (k + 1) q ![b] := by
    intro ν
    rw [hA.fa k q ℓ u h1 hk hk0 hs, mem_ftree]
  simp only [exAt, hτ, List.mem_append, List.mem_map, List.mem_flatMap, mem_elems, mem_guarded,
    Option.mem_toList, hA.sh k q ℓ u h1 hk]
  constructor
  · rintro ((⟨e, he, rfl⟩ | ⟨e, he, i, hi, rfl⟩) | ⟨ν, hν, r, hr, i, hi, rfl⟩)
    · obtain ⟨i, b, hb, rfl⟩ := (mem_exts_node G k q u e).1 he
      exact ⟨i, b, (hHd i b).2 (Or.inl hb), rfl⟩
    · obtain ⟨j, b, -, rfl⟩ := (mem_exts_node G k q u e).1 he
      exact ⟨i, b, (hHd i b).2 (Or.inr ((hgam i b).1 hi)), rfl⟩
    · obtain ⟨b, hbfar, rfl⟩ := (hfar ν).1 hν
      rw [hA.co k q ℓ u b h1 hk hbfar] at hr ⊢
      simp only [tree, TypeTree.rootAs_mk, Option.some.injEq] at hr
      subst hr
      exact ⟨i, b, (hHd i b).2 (Or.inr ((hgam i b).1 hi)), rfl⟩
  · rintro ⟨i, b, hb, rfl⟩
    rcases (hHd i b).1 hb with hG | hhop
    · exact Or.inl (Or.inl ⟨_, (mem_exts_node G k q u _).2 ⟨i, b, hG, rfl⟩, rfl⟩)
    · by_cases hnear : ∃ j, WithinDist G.resolved (rhoPlus (k + 1) q) (u j) b
      · obtain ⟨j, hj⟩ := hnear
        exact Or.inl (Or.inr ⟨(j, node G (k + 1) q (Fin.snoc u b)),
          (mem_exts_node G k q u _).2 ⟨j, b, hj, rfl⟩, i, (hgam i b).2 hhop, rfl⟩)
      · push Not at hnear
        have hbfar : ∀ j, ¬ WithinDist G.resolved (rhoMinus (k + 1) q) (u j) b :=
          fun j hj => hnear j (withinDist_mono hR hj)
        refine Or.inr ⟨tree G (k + 1) q ![b], (hfar _).2 ⟨b, hbfar, rfl⟩, ?_⟩
        rw [hA.co k q ℓ u b h1 hk hbfar]
        exact ⟨node G (k + 1) q (Fin.snoc u b), TypeTree.rootAs_mk _ _ _ _, i, (hgam i b).2 hhop,
          rfl⟩

/-- **The expansion of the program is right.** -/
theorem expandOK_exG (D : ResolveData) (ft : FarMap) {k₀ q₀ : ℕ} (hD : D.Spec G k₀ q₀)
    (hft : FarSpec G ft) {sh : TypeTree → TypeTree} {fa : TypeTree → List TypeTree}
    {co : TypeTree → TypeTree → TypeTree} (hA : AnsOK G sh fa co k₀ q₀) :
    ExpandOK G D ft (exG D sh fa co) k₀ q₀ := by
  intro k q ℓ u h1 hk hk0 hs p
  show p ∈ exAt D sh fa co k q ℓ (node G k (q + 1) u) ↔ _
  rw [mem_exAt D hD hA u h1 hk hk0 hs]
  simp only [mem_candidatesF D ft hD hft u h1 hk hk0 hs]
  constructor
  · rintro ⟨i, b, hb, rfl⟩
    exact ⟨_, ⟨i, b, hb, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨i, b, hb, rfl⟩, rfl⟩
    exact ⟨i, b, hb, rfl⟩

end Lax185574Proofs.ResolveRam
