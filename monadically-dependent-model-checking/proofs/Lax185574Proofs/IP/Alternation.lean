import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Group.Nat.Even

/-!
Combinatorics of alternation along indiscernible sequences.

The lemma `shatters_of_alternation` is the finite core of the classical
fact that a formula alternating along an indiscernible sequence has the
independence property. It is stated for an arbitrary relation `R`
between witnesses and sequence elements. Indiscernibility is replaced by
the hypothesis that each relevant property takes the same value on all
increasing tuples of the sequence.

The lemma `exists_window` finds a long window on which finitely many
properties of increasing tuples are constant, given that none of them
alternates along `2D` successive blocks.

`concat` glues successive blocks into one increasing tuple.
-/

namespace Lax185574Proofs.IP

/-- Alternation along `2d` elements of a sequence on which the shattering
properties are constant gives shattering of every increasing `d`-tuple. -/
theorem shatters_of_alternation {X E : Type*} (R : X → E → Prop) {d T : ℕ} (e : Fin T → E)
    (hind : ∀ (S : Finset (Fin d)) (ρ ρ' : Fin d → Fin T), StrictMono ρ → StrictMono ρ' →
      ((∃ x, ∀ s, R x (e (ρ s)) ↔ s ∈ S) ↔ (∃ x, ∀ s, R x (e (ρ' s)) ↔ s ∈ S)))
    (x₀ : X) (τ : Fin (2 * d) → Fin T) (hτ : StrictMono τ)
    (halt : ∀ u, R x₀ (e (τ u)) ↔ Even u.val)
    (ρ : Fin d → Fin T) (hρ : StrictMono ρ) (S : Finset (Fin d)) :
    ∃ x, ∀ s, R x (e (ρ s)) ↔ s ∈ S := by
  classical
  let σ : Fin d → Fin (2 * d) := fun s =>
    ⟨2 * s.val + (if s ∈ S then 0 else 1), by have := s.isLt; split_ifs <;> omega⟩
  have hσ : StrictMono σ := by
    intro s t hst
    show 2 * s.val + _ < 2 * t.val + _
    have : s.val < t.val := hst
    split_ifs <;> omega
  refine (hind S (τ ∘ σ) ρ (hτ.comp hσ) hρ).mp ⟨x₀, fun s => ?_⟩
  simp only [Function.comp_apply]
  rw [halt]
  show Even (2 * s.val + (if s ∈ S then 0 else 1)) ↔ s ∈ S
  by_cases h : s ∈ S
  · simp only [h, if_true, iff_true]; rw [Nat.even_iff]; omega
  · simp only [h, if_false, iff_false]; rw [Nat.even_iff]; omega

/-- The tuple obtained by concatenating `D` blocks of length `r`. -/
def concat {D r L : ℕ} (B : Fin D → Fin r → Fin L) : Fin (D * r) → Fin L :=
  fun i => B (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

/-- Blocks are successive if every entry of an earlier block is smaller
than every entry of a later block. -/
def Successive {D r L : ℕ} (B : Fin D → Fin r → Fin L) : Prop :=
  ∀ u v, u < v → ∀ i i', B u i < B v i'

theorem concat_strictMono {D r L : ℕ} (B : Fin D → Fin r → Fin L)
    (hB : ∀ u, StrictMono (B u)) (hs : Successive B) : StrictMono (concat B) := by
  intro i j hij
  unfold concat
  set a := finProdFinEquiv.symm i
  set b := finProdFinEquiv.symm j
  have hi : i = finProdFinEquiv a := (Equiv.apply_symm_apply _ _).symm
  have hj : j = finProdFinEquiv b := (Equiv.apply_symm_apply _ _).symm
  have hv : a.2.val + r * a.1.val < b.2.val + r * b.1.val := by
    rw [hi, hj] at hij
    exact hij
  have ha2 := a.2.isLt
  have hb2 := b.2.isLt
  rcases lt_trichotomy a.1 b.1 with h | h | h
  · exact hs _ _ h _ _
  · have h' : a.1.val = b.1.val := congrArg Fin.val h
    rw [h]
    apply hB
    show a.2.val < b.2.val
    rw [h'] at hv
    omega
  · exfalso
    have h' : b.1.val + 1 ≤ a.1.val := h
    have : r * (b.1.val + 1) ≤ r * a.1.val := Nat.mul_le_mul_left r h'
    rw [Nat.mul_add, Nat.mul_one] at this
    omega

/-- Restricting a block system along an increasing map keeps it successive. -/
theorem Successive.comp {D D' r L : ℕ} {B : Fin D → Fin r → Fin L} (hs : Successive B)
    {ρ : Fin D' → Fin D} (hρ : StrictMono ρ) : Successive (B ∘ ρ) :=
  fun _ _ h i i' => hs _ _ (hρ h) i i'

/-- A long window on which finitely many properties of increasing tuples
are constant, if none of them alternates along `2D` successive blocks. -/
theorem exists_window {ι : Type*} [Fintype ι] {r L D W : ℕ}
    (Q : ι → (Fin r → Fin L) → Prop)
    (hQ : ∀ j, ¬ ∃ B : Fin (2 * D) → Fin r → Fin L, (∀ u, StrictMono (B u)) ∧ Successive B ∧
      ∀ u, (Q j (B u) ↔ Even u.val))
    (hL : (Fintype.card ι * (2 * D) + 1) * W ≤ L) :
    ∃ w₀, w₀ + W ≤ L ∧ ∀ j (σ σ' : Fin r → Fin L), StrictMono σ → StrictMono σ' →
      (∀ i, w₀ ≤ (σ i).val ∧ (σ i).val < w₀ + W) →
      (∀ i, w₀ ≤ (σ' i).val ∧ (σ' i).val < w₀ + W) → (Q j σ ↔ Q j σ') := by
  classical
  set K := Fintype.card ι * (2 * D) + 1
  let inW : Fin K → (Fin r → Fin L) → Prop := fun w σ =>
    StrictMono σ ∧ ∀ i, w.val * W ≤ (σ i).val ∧ (σ i).val < w.val * W + W
  let Bad : ι → Fin K → Prop := fun j w => ∃ σ σ', inW w σ ∧ inW w σ' ∧ Q j σ ∧ ¬ Q j σ'
  have hbad : ∀ j, (Finset.univ.filter (Bad j)).card ≤ 2 * D := by
    intro j
    by_contra hlt
    push Not at hlt
    obtain ⟨F, hF, hFc⟩ := Finset.exists_subset_card_eq hlt.le
    let g := F.orderEmbOfFin hFc
    have hg : ∀ u, Bad j (g u) := fun u => (Finset.mem_filter.mp (hF (F.orderEmbOfFin_mem hFc u))).2
    choose σT σF hT hF' hQT hQF using hg
    let B : Fin (2 * D) → Fin r → Fin L := fun u => if Even u.val then σT u else σF u
    apply hQ j
    refine ⟨B, fun u => ?_, ?_, fun u => ?_⟩
    · simp only [B]; split_ifs
      · exact (hT u).1
      · exact (hF' u).1
    · intro u v huv i i'
      have hgu : (g u).val + 1 ≤ (g v).val := g.strictMono huv
      have h1 : (B u i).val < (g u).val * W + W := by
        simp only [B]; split_ifs
        · exact ((hT u).2 i).2
        · exact ((hF' u).2 i).2
      have h2 : (g v).val * W ≤ (B v i').val := by
        simp only [B]; split_ifs
        · exact ((hT v).2 i').1
        · exact ((hF' v).2 i').1
      have : ((g u).val + 1) * W ≤ (g v).val * W := Nat.mul_le_mul_right W hgu
      show (B u i).val < (B v i').val
      rw [Nat.add_mul, Nat.one_mul] at this
      omega
    · simp only [B]
      split_ifs with h
      · simp [h, hQT u]
      · simp [h, hQF u]
  have hunion : (Finset.univ.biUnion fun j => Finset.univ.filter (Bad j)).card < K := by
    calc _ ≤ ∑ j, (Finset.univ.filter (Bad j)).card := Finset.card_biUnion_le
      _ ≤ ∑ _j : ι, 2 * D := Finset.sum_le_sum fun j _ => hbad j
      _ = Fintype.card ι * (2 * D) := by simp
      _ < K := Nat.lt_succ_self _
  obtain ⟨w, -, hw⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (t := (Finset.univ : Finset (Fin K))) (by simpa using hunion)
  have hw : ∀ j, ¬ Bad j w := fun j hb =>
    hw (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hb⟩⟩)
  refine ⟨w.val * W, ?_, fun j σ σ' hσ hσ' hσw hσ'w => ?_⟩
  · have : (w.val + 1) * W ≤ K * W := Nat.mul_le_mul_right W w.isLt
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  · by_contra hne
    by_cases h : Q j σ
    · exact hw j ⟨σ, σ', ⟨hσ, hσw⟩, ⟨hσ', hσ'w⟩, h, fun h' => hne (iff_of_true h h')⟩
    · exact hw j ⟨σ', σ, ⟨hσ', hσ'w⟩, ⟨hσ, hσw⟩, by tauto, h⟩

end Lax185574Proofs.IP
