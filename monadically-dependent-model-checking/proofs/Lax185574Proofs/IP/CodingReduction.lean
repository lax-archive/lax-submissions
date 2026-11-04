import Lax185574Proofs.IP.CodingFormulas
import Lax185574Proofs.IP.Columns

/-!
Reduction of a coding formula to a single left variable.

This is a finite form of Lemmas 4.11 and 4.12 of Braunfeld and Laskowski,
*Characterizations of monadic NIP*. Let `θ(x₀ … x_{p+1}, ȳ, z)` code on a
class. For a size `n`, take a long coding and make the truth of `θ` on
mixed tuples of its entries depend only on the order type of the indices
(Ramsey). Arrange the indices in `2n` columns of height `2n + 1`, and let
the candidate coding of `θ₁` use the middle positions of the columns.
Either `θ₁` codes, or a spurious witness exists. A spurious witness uses
the row of the coded pair, and moving the indices of that row inside its
column gives a coding of size `n` by a formula `θ_μ` with the other entries
as parameters.
-/

namespace Lax185574Proofs.IP

open FirstOrder FirstOrder.Language
open Lax199508.GraphClasses Lax710763.Transductions
open Lax185574Proofs.Interface.Old Lax185574Proofs.IndependenceProperty
open Lax185574Proofs.Lib.TupleRamsey

theorem coding_reduction_at {C : GraphClass} {k p q : ℕ}
    (θ : (CL k).Formula ((Fin (p + 2) ⊕ Fin q) ⊕ Fin 1)) (hθ : CodesAll C θ) (n : ℕ) :
    CodesAt C (theta₁ θ) n ∨ ∃ μ, CodesAt C (thetaParam θ μ) n := by
  classical
  -- the grid
  let N := 2 * n
  let g := 2 * n + 1
  let Pi := Fin (p + 2) → Fin (p + 2)
  let eP := Fintype.equivFin Pi
  obtain ⟨Nb, hNb⟩ := exists_homogeneous_seq_otp (p + 2 + 3) (Fintype.card Pi) (N * g)
  obtain ⟨N0, G, hG, colors, a, b, c, hc⟩ := hθ Nb
  let P : Fin (Fintype.card Pi) → (Fin (p + 2 + 3) → Fin Nb) → Prop := fun j τ =>
    RealizeIn G.structure colors θ
      (Sum.elim (Sum.elim (fun i => a (τ (Fin.castAdd 3 i)) (eP.symm j i))
        (b (τ (Fin.natAdd (p + 2) 0)))) (fun _ => c (τ (Fin.natAdd (p + 2) 1)) (τ (Fin.natAdd (p + 2) 2))))
  obtain ⟨ι, hι⟩ := hNb le_rfl P
  let Tr : Pi → (Fin (p + 2) → Fin (N * g)) → Fin (N * g) → Fin (N * g) → Fin (N * g) → Prop :=
    fun π r x y z => RealizeIn G.structure colors θ
      (Sum.elim (Sum.elim (fun i => a (ι (r i)) (π i)) (b (ι x))) (fun _ => c (ι y) (ι z)))
  have hTr : ∀ π r x y z r' x' y' z',
      otp (Fin.append r ![x, y, z]) = otp (Fin.append r' ![x', y', z']) →
      (Tr π r x y z ↔ Tr π r' x' y' z') := by
    intro π r x y z r' x' y' z' h
    have := hι (eP π) _ _ h
    simpa [P, Tr, Fin.append_left, Fin.append_right] using this
  have hcinj : ∀ u v u' v', c (ι u) (ι v) = c (ι u') (ι v') → u = u' ∧ v = v' := by
    intro u v u' v' h
    have h1 := (hc (ι u) (ι v) (ι u) (ι v)).mpr ⟨rfl, rfl⟩
    rw [h] at h1
    obtain ⟨h2, h3⟩ := (hc _ _ _ _).mp h1
    exact ⟨ι.injective h2, ι.injective h3⟩
  -- columns and heights
  let αc : Fin n → Fin N := fun s => ⟨s.val, by omega⟩
  let βc : Fin n → Fin N := fun s => ⟨n + s.val, by omega⟩
  let ctr : Fin g := ⟨n, by omega⟩
  have hαβ : ∀ s t, αc s ≠ βc t := by
    intro s t h; have := congrArg Fin.val h; simp [αc, βc] at this; omega
  have hαinj : ∀ s t, αc s = αc t → s = t := by
    intro s t h; have := congrArg Fin.val h; exact Fin.ext (by simpa [αc] using this)
  have hβinj : ∀ s t, βc s = βc t → s = t := by
    intro s t h; have := congrArg Fin.val h; ext; simp [βc] at this; omega
  let α : Fin n → Fin (N * g) := fun s => pos (αc s) ctr
  let β : Fin n → Fin (N * g) := fun s => pos (βc s) ctr
  -- the candidate coding of `θ₁`
  let Aset : Set (Fin N0) := {z | ∃ s t, z = a (ι (α s)) t}
  let Cset : Set (Fin N0) := {z | ∃ u v, z = c (ι u) (ι v)}
  let xs : Fin n → Fin 1 → Fin N0 := fun s _ => a (ι (α s)) 0
  let ys : Fin n → Fin q → Fin N0 := fun s => b (ι (β s))
  let zs : Fin n → Fin n → Fin N0 := fun s s' => c (ι (α s)) (ι (β s'))
  have htrue : ∀ i j, RealizeIn G.structure (Fin.append colors ![Aset, Cset]) (theta₁ θ)
      (Sum.elim (Sum.elim (xs i) (ys j)) (fun _ => zs i j)) := by
    intro i j
    rw [realizeIn_theta₁]
    refine ⟨Fin.tail (a (ι (α i))), fun t => ⟨i, t.succ, rfl⟩, ?_, ?_⟩
    · rw [Fin.cons_self_tail]
      exact (hc _ _ _ _).mpr ⟨rfl, rfl⟩
    · rintro z' ⟨u, v, rfl⟩ hne h
      rw [Fin.cons_self_tail] at h
      obtain ⟨h1, h2⟩ := (hc _ _ _ _).mp h
      exact hne (by rw [← h1, ← h2])
  by_cases hall : ∀ i j i' j', RealizeIn G.structure (Fin.append colors ![Aset, Cset]) (theta₁ θ)
      (Sum.elim (Sum.elim (xs i) (ys j)) (fun _ => zs i' j')) ↔ (i = i' ∧ j = j')
  · exact Or.inl ⟨N0, G, hG, _, xs, ys, zs, hall⟩
  right
  simp only [not_forall] at hall
  obtain ⟨i, j, i', j', hbad⟩ := hall
  have hne : ¬ (i = i' ∧ j = j') := by
    rintro ⟨rfl, rfl⟩
    exact hbad (iff_of_true (htrue i j) ⟨rfl, rfl⟩)
  have hR : RealizeIn G.structure (Fin.append colors ![Aset, Cset]) (theta₁ θ)
      (Sum.elim (Sum.elim (xs i) (ys j)) (fun _ => zs i' j')) := by
    by_contra hR
    exact hbad (iff_of_false hR hne)
  rw [realizeIn_theta₁] at hR
  obtain ⟨x', hxA, hθx, huniq⟩ := hR
  choose ρ π' hρ using hxA
  let rc : Fin (p + 2) → Fin N := Fin.cons (αc i) (fun t => αc (ρ t))
  let π : Pi := Fin.cons 0 π'
  let r : Fin (p + 2) → Fin (N * g) := fun m => pos (rc m) ((fun _ => ctr) (rc m))
  have hcons : (Fin.cons (a (ι (α i)) 0) x' : Fin (p + 2) → Fin N0) = fun m => a (ι (r m)) (π m) := by
    funext m
    cases m using Fin.cases with
    | zero => rfl
    | succ t => simp [r, rc, π, hρ t, α]
  have hU : ∀ u v, Tr π r (β j) u v ↔ (u = α i' ∧ v = β j') := by
    intro u v
    constructor
    · intro h
      by_contra hne'
      refine huniq (c (ι u) (ι v)) ⟨u, v, rfl⟩ (fun heq => hne' (hcinj _ _ _ _ heq)) ?_
      rw [hcons]
      exact h
    · rintro ⟨rfl, rfl⟩
      show RealizeIn _ _ _ _
      rw [← hcons]
      exact hθx
  have hrcα : ∀ m, ∃ s, rc m = αc s := by
    intro m
    cases m using Fin.cases with
    | zero => exact ⟨i, rfl⟩
    | succ t => exact ⟨ρ t, rfl⟩
  by_cases hii : i = i'
  · -- then `j ≠ j'`, and moving the last entry inside its column is a contradiction
    have hjj : j ≠ j' := fun h => hne ⟨hii, h⟩
    subst hii
    let up : Fin g := ⟨n + 1, by omega⟩
    have hmove := hTr π r (β j) (α i) (pos (βc j') up) r (β j) (α i) (β j')
      (otp_append_cols rc (fun _ => ctr) (fun _ => ctr) (βc j) (αc i) (βc j') ctr ctr up ctr ctr ctr
        (fun _ _ => ⟨Iff.rfl, Iff.rfl⟩) (fun _ _ => ⟨Iff.rfl, Iff.rfl⟩)
        (fun s h => by obtain ⟨t, ht⟩ := hrcα s; exact absurd (ht.symm.trans h) (hαβ _ _))
        (fun h => absurd h.symm (hαβ _ _))
        (fun h => absurd (hβinj _ _ h) hjj)
        (fun h => absurd h (hαβ _ _)))
    have h1 := (hU _ _).mpr ⟨rfl, rfl⟩
    have h2 := ((hU _ _).mp (hmove.mpr h1)).2
    have := (pos_injective h2).2
    simp [up, ctr] at this
  · -- the smaller coding
    let par : Fin (p + 2) → Fin N0 := fun m => a (ι (r m)) (π m)
    let μ : Fin (p + 2) → Fin (p + 1) ⊕ Fin (p + 2) :=
      Fin.cons (Sum.inr 0) (fun t => if ρ t = i' then Sum.inl t else Sum.inr t.succ)
    let dl : Fin n → Fin g := fun s => ⟨s.val, by omega⟩
    let D1 : Fin n → Fin N → Fin g := fun s col => if col = αc i' then dl s else ctr
    let A' : Fin n → Fin (p + 1) → Fin N0 := fun s t => a (ι (pos (αc i') (dl s))) (π t.succ)
    let B' : Fin n → Fin q → Fin N0 := fun s => b (ι (pos (βc j) (dl s)))
    let C' : Fin n → Fin n → Fin N0 := fun s s' => c (ι (pos (αc i') (dl s))) (ι (pos (βc j') (dl s')))
    refine ⟨μ, N0, G, hG, Fin.append colors fun s => {par s}, A', B', C', fun s1 s2 s3 s4 => ?_⟩
    rw [realizeIn_thetaParam]
    have hrow : (fun m => Sum.elim (A' s1) par (μ m)) =
        fun m => a (ι (pos (rc m) (D1 s1 (rc m)))) (π m) := by
      funext m
      cases m using Fin.cases with
      | zero =>
        have : rc 0 ≠ αc i' := fun h => hii (hαinj _ _ h)
        simp [μ, par, r, D1, this]
      | succ t =>
        by_cases ht : ρ t = i'
        · simp [μ, A', D1, rc, ht]
        · have : αc (ρ t) ≠ αc i' := fun h => ht (hαinj _ _ h)
          simp [μ, par, r, D1, rc, ht, this]
    rw [hrow]
    let dk : Fin g := ⟨s3.val + n - s1.val, by omega⟩
    let dz : Fin g := ⟨s4.val + n - s2.val, by omega⟩
    have hmove := hTr π (fun m => pos (rc m) (D1 s1 (rc m))) (pos (βc j) (dl s2))
      (pos (αc i') (dl s3)) (pos (βc j') (dl s4)) r (β j) (pos (αc i') dk) (pos (βc j') dz)
      (otp_append_cols rc (D1 s1) (fun _ => ctr) (βc j) (αc i') (βc j') (dl s2) (dl s3) (dl s4)
        ctr dk dz
        (fun s h => by obtain ⟨t, ht⟩ := hrcα s; exact absurd (ht.symm.trans h) (hαβ _ _))
        (fun s h => by
          simp only [D1, h, if_true, Fin.lt_def, dl, dk, ctr]
          constructor <;> constructor <;> intro <;> omega)
        (fun s h => by obtain ⟨t, ht⟩ := hrcα s; exact absurd (ht.symm.trans h) (hαβ _ _))
        (fun h => absurd h.symm (hαβ _ _))
        (fun h => by
          simp only [Fin.lt_def, dl, dz, ctr]
          constructor <;> constructor <;> intro <;> omega)
        (fun h => absurd h (hαβ _ _)))
    show Tr π _ _ _ _ ↔ _
    rw [hmove, hU]
    constructor
    · rintro ⟨h1, h2⟩
      have e1 := congrArg Fin.val (pos_injective h1).2
      have e2 := congrArg Fin.val (pos_injective h2).2
      simp only [dk, dz, ctr] at e1 e2
      exact ⟨Fin.ext (by omega), Fin.ext (by omega)⟩
    · rintro ⟨rfl, rfl⟩
      refine ⟨?_, ?_⟩
      · show pos (αc i') dk = pos (αc i') ctr
        congr 1; ext; simp [dk, ctr]
      · show pos (βc j') dz = pos (βc j') ctr
        congr 1; ext; simp [dz, ctr]

end Lax185574Proofs.IP
