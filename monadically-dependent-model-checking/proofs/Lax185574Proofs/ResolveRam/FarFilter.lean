import Lax185574Proofs.ResolveRam.Answers

/-!
The far members that can give a candidate.

A member `ν = tree^G_{k+1,q}(b)` of the far tree of `ū` gives a candidate
extension with guard `i` exactly if `Hop` holds between `uᵢ` and `b`.
The test reads the distances of `uᵢ` and of `b` to the colors `P`, `Q`,
which the root of the shifted tree `tree^G_{k+1,q}(ū)` and the root of `ν`
record. So the program tests `hop2` on these two roots before it asks for
the composition, and composes only the members that pass (`faP`). This
does not change the expansion (`exAt_faP`), since the composition of a
member that does not pass has no guard. It bounds the number of
compositions by the number of candidates rather than by `|G|`.
-/

namespace Lax185574Proofs.ResolveRam

open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.WordEncoding
open Lax185574.DistanceLogic Lax185574.TypeTrees Lax185574.ScatterTypes Lax185574.FarTrees
open Lax185574.ResolveLift Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo
open Lax185574Proofs.WalkDistance
open Lax3.DistFO (rhoMinus rhoPlus)

/-- The test of `Hop` at radius `s` between position `i` of `t₁` and
position `j` of `t₂`. -/
def hop2 (D : ResolveData) {q₁ ℓ₁ q₂ ℓ₂ : ℕ} (t₁ : Node q₁ ℓ₁) (i : Fin ℓ₁) (t₂ : Node q₂ ℓ₂)
    (j : Fin ℓ₂) (s : ℕ) : Prop :=
  ∃ s₁ ∈ Finset.range (s + 1), ∃ s₂ ∈ Finset.range (s + 1),
    (s₁ + 1 + s₂ ≤ s ∧ ((nearA t₁ D.P s₁ i ∧ nearA t₂ D.Q s₂ j) ∨
      (nearA t₁ D.Q s₁ i ∧ nearA t₂ D.P s₂ j))) ∨
    (s₁ + 2 + s₂ ≤ s ∧ ((nearA t₁ D.P s₁ i ∧ nearA t₂ D.P s₂ j ∧ D.Q ∈ D.cols) ∨
      (nearA t₁ D.Q s₁ i ∧ nearA t₂ D.Q s₂ j ∧ D.P ∈ D.cols)))

instance (D : ResolveData) {q₁ ℓ₁ q₂ ℓ₂ : ℕ} (t₁ : Node q₁ ℓ₁) (i : Fin ℓ₁) (t₂ : Node q₂ ℓ₂)
    (j : Fin ℓ₂) (s : ℕ) : Decidable (hop2 D t₁ i t₂ j s) := by unfold hop2; infer_instance

variable {n : ℕ} {G : PartialGraph (Fin n)}

theorem hop2_node (D : ResolveData) (hD : ∀ Y, Y ∈ D.cols ↔ Occurs G Y) {k q ℓ₁ ℓ₂ s : ℕ}
    (u : Fin ℓ₁ → Fin n) (v : Fin ℓ₂ → Fin n) (i : Fin ℓ₁) (j : Fin ℓ₂)
    (hs : s ≤ rhoPlus k q) :
    hop2 D (node G k q u) i (node G k q v) j s ↔ Hop G D.P D.Q s (u i) (v j) := by
  unfold hop2 Hop
  simp only [Finset.mem_range, hD]
  constructor
  · rintro ⟨s₁, -, s₂, -, h⟩
    refine ⟨s₁, s₂, ?_⟩
    rcases h with ⟨h0, h⟩ | ⟨h0, h⟩
    · left
      refine ⟨h0, ?_⟩
      rwa [nearA_node u _ _ (by omega), nearA_node v _ _ (by omega), nearA_node u _ _ (by omega),
        nearA_node v _ _ (by omega)] at h
    · right
      refine ⟨h0, ?_⟩
      rwa [nearA_node u _ _ (by omega), nearA_node v _ _ (by omega), nearA_node u _ _ (by omega),
        nearA_node v _ _ (by omega)] at h
  · rintro ⟨s₁, s₂, h⟩
    rcases h with ⟨h0, h⟩ | ⟨h0, h⟩
    · refine ⟨s₁, by omega, s₂, by omega, Or.inl ⟨h0, ?_⟩⟩
      rwa [nearA_node u _ _ (by omega), nearA_node v _ _ (by omega), nearA_node u _ _ (by omega),
        nearA_node v _ _ (by omega)]
    · refine ⟨s₁, by omega, s₂, by omega, Or.inr ⟨h0, ?_⟩⟩
      rwa [nearA_node u _ _ (by omega), nearA_node v _ _ (by omega), nearA_node u _ _ (by omega),
        nearA_node v _ _ (by omega)]

/-- The member `ν` of the far tree passes the test against the shifted
tree `σ` for some guard. -/
def passF (D : ResolveData) (σ ν : TypeTree) : Bool :=
  if h : ν.ℓ = 1 then
    decide (∃ i : Fin σ.ℓ, hop2 D σ.root i ν.root ⟨0, by omega⟩ (rhoPlus σ.k σ.q))
  else false

/-- The members of the far tree that pass the test. -/
noncomputable def faP (G : PartialGraph (Fin n)) (D : ResolveData) (τ : TypeTree) : List TypeTree :=
  (faOf G τ).filter (passF D (shOf G τ))

theorem flatMap_filter_of {α β : Type*} (l : List α) (p : α → Bool) (f : α → List β)
    (h : ∀ a ∈ l, p a = false → f a = []) : (l.filter p).flatMap f = l.flatMap f := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ih' := ih fun b hb => h b (List.mem_cons_of_mem a hb)
    by_cases hp : p a = true
    · simp [List.filter_cons, hp, ih']
    · have hp' : p a = false := by simpa using hp
      simp [List.filter_cons, hp', ih', h a (by simp) hp']

/-- **Filtering the far tree does not change the expansion.** -/
theorem exAt_faP (D : ResolveData) {k₀ q₀ : ℕ} (hD : D.Spec G k₀ q₀) {k q ℓ : ℕ}
    (u : Fin ℓ → Fin n) (h1 : 1 ≤ ℓ) (hk : ℓ ≤ k) (hk0 : k₀ ≤ k) (hs : k + (q + 1) = k₀ + q₀) :
    exAt D (shOf G) (faP G D) (coOf G) k q ℓ (node G k (q + 1) u) =
      exAt D (shOf G) (faOf G) (coOf G) k q ℓ (node G k (q + 1) u) := by
  unfold exAt
  simp only
  congr 1
  have hτ : (⟨k, q + 1, ℓ, node G k (q + 1) u⟩ : TypeTree) = tree G k (q + 1) u := rfl
  rw [hτ, faP]
  refine flatMap_filter_of _ _ _ fun ν hν hp => ?_
  have hfa := ((ansOK_of G k₀ q₀).fa k q ℓ u h1 hk hk0 hs ν).1 hν
  obtain ⟨b, hb, rfl⟩ := (mem_ftree (G := G) k q u ν).1 hfa
  rw [shOf_tree G u h1 hk] at hp ⊢
  rw [coOf_tree G u b h1 hk hb]
  simp only [tree, TypeTree.rootAs_mk, Option.toList_some, List.flatMap_cons, List.flatMap_nil,
    List.append_nil]
  have hnot : ∀ i : Fin ℓ, ¬ Hop G D.P D.Q (rhoPlus (k + 1) q) (u i) b := by
    intro i hi
    have : passF D (tree G (k + 1) q u) (tree G (k + 1) q ![b]) = true := by
      unfold passF
      split_ifs with h0
      · rw [decide_eq_true_eq]
        exact ⟨i, (hop2_node D hD.1 u ![b] i 0 le_rfl).2 hi⟩
      · exact absurd rfl h0
    rw [this] at hp; exact Bool.noConfusion hp
  simp only [guarded, List.filterMap_eq_nil_iff]
  intro i _
  split_ifs with h
  · rw [hopTest_node D hD.1 (Fin.snoc u b) _ _ le_rfl, Fin.snoc_castSucc, Fin.snoc_last] at h
    exact absurd h (hnot i)
  · rfl

/-- **The expansion with the filtered far tree is right.** -/
theorem expandOK_faP (D : ResolveData) {k₀ q₀ : ℕ} (hD : D.Spec G k₀ q₀) :
    ExpandOK G D (farMapOf G) (exG D (shOf G) (faP G D) (coOf G)) k₀ q₀ := by
  intro k q ℓ u h1 hk hk0 hs p
  show p ∈ exAt D (shOf G) (faP G D) (coOf G) k q ℓ (node G k (q + 1) u) ↔ _
  rw [exAt_faP D hD u h1 hk hk0 hs]
  exact expandOK_exG D (farMapOf G) hD (farSpec_farMapOf G) (ansOK_of G k₀ q₀) k q ℓ u h1 hk hk0 hs p

end Lax185574Proofs.ResolveRam
