import Lax185574Proofs.Lib.TupleRamsey
import Mathlib.Data.Finset.Sort

/-!
Ramsey's theorem for finitely many properties of increasing tuples.

Given `N` properties of `ℓ`-tuples of elements of `Fin n`, with `n` large
enough in terms of `N`, `ℓ` and `M` only, there is an increasing sequence
of length `M` on which each property takes the same value on all
increasing `ℓ`-tuples. This follows from the tuple form of Ramsey's
theorem in `Lib/TupleRamsey`, applied once per property.
-/

namespace Lax185574Proofs.IP

open Lax185574Proofs.Lib.TupleRamsey

/-- Increasing tuples have the same order type. -/
theorem otp_eq_of_strictMono {n ℓ : ℕ} {a a' : Fin ℓ → Fin n} (ha : StrictMono a)
    (ha' : StrictMono a') : otp a = otp a' := by
  funext p
  unfold otp
  rcases lt_trichotomy p.1 p.2 with h | h | h
  · rw [compare_lt_iff_lt.mpr (ha h), compare_lt_iff_lt.mpr (ha' h)]
  · rw [h, compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
  · rw [compare_gt_iff_gt.mpr (ha h), compare_gt_iff_gt.mpr (ha' h)]

/-- Ramsey for finitely many properties, inside a given set `S`. -/
theorem exists_homogeneous_subset (ℓ : ℕ) :
    ∀ (N M : ℕ), ∃ Nb : ℕ, ∀ {n : ℕ} (S : Finset (Fin n)), Nb ≤ S.card →
      ∀ P : Fin N → (Fin ℓ → Fin n) → Prop, ∃ I ⊆ S, M ≤ I.card ∧
        ∀ j (a a' : Fin ℓ → Fin n), (∀ i, a i ∈ I) → (∀ i, a' i ∈ I) →
          otp a = otp a' → (P j a ↔ P j a') := by
  classical
  intro N
  induction N with
  | zero =>
    intro M
    exact ⟨M, fun S hS _ => ⟨S, subset_rfl, hS, fun j => Fin.elim0 j⟩⟩
  | succ N ih =>
    intro M
    obtain ⟨Nb', hNb'⟩ := ih M
    obtain ⟨Nfin, hNfin⟩ := tupleRamseyAtSize 2 ℓ Nb' (by norm_num)
    refine ⟨Nfin, fun S hS P => ?_⟩
    let c : (Fin ℓ → Fin _) → Fin 2 := fun a => if P (Fin.last N) a then 1 else 0
    obtain ⟨I₁, hI₁S, hI₁, f, hf⟩ := hNfin S hS c
    obtain ⟨I, hII₁, hI, hP⟩ := hNb' I₁ hI₁ (fun j => P j.castSucc)
    refine ⟨I, hII₁.trans hI₁S, hI, fun j a a' ha ha' hot => ?_⟩
    induction j using Fin.lastCases with
    | last =>
      have h1 := hf a fun i => hII₁ (ha i)
      have h2 := hf a' fun i => hII₁ (ha' i)
      rw [hot] at h1
      have hc : c a = c a' := h1.trans h2.symm
      simp only [c] at hc
      by_cases h : P (Fin.last N) a <;> by_cases h' : P (Fin.last N) a' <;> simp_all
    | cast j => exact hP j a a' ha ha' hot

/-- An order embedding preserves order types. -/
theorem otp_comp_orderEmbedding {ℓ m n : ℕ} (ι : Fin m ↪o Fin n) (σ : Fin ℓ → Fin m) :
    otp (ι ∘ σ) = otp σ := by
  funext q
  unfold otp
  simp only [Function.comp_apply]
  rcases lt_trichotomy (σ q.1) (σ q.2) with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (ι.strictMono h)]
  · rw [h, compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (ι.strictMono h)]

/-- A map that is strictly monotone on the entries of a tuple preserves
its order type. -/
theorem otp_comp_of_strictMonoOn {ℓ m n : ℕ} (f : Fin m → Fin n) (σ : Fin ℓ → Fin m)
    (hf : ∀ a b, σ a < σ b → f (σ a) < f (σ b)) : otp (f ∘ σ) = otp σ := by
  funext q
  unfold otp
  simp only [Function.comp_apply]
  rcases lt_trichotomy (σ q.1) (σ q.2) with h | h | h
  · rw [compare_lt_iff_lt.mpr h, compare_lt_iff_lt.mpr (hf _ _ h)]
  · rw [h, compare_eq_iff_eq.mpr rfl, compare_eq_iff_eq.mpr rfl]
  · rw [compare_gt_iff_gt.mpr h, compare_gt_iff_gt.mpr (hf _ _ h)]

/-- Ramsey for finitely many properties of tuples, homogeneous up to order
type, as an increasing sequence. -/
theorem exists_homogeneous_seq_otp (ℓ N M : ℕ) :
    ∃ Nb : ℕ, ∀ {n : ℕ}, Nb ≤ n → ∀ P : Fin N → (Fin ℓ → Fin n) → Prop,
      ∃ ι : Fin M ↪o Fin n, ∀ j (σ σ' : Fin ℓ → Fin M), otp σ = otp σ' →
        (P j (ι ∘ σ) ↔ P j (ι ∘ σ')) := by
  classical
  obtain ⟨Nb, hNb⟩ := exists_homogeneous_subset ℓ N M
  refine ⟨Nb, fun {n} hn P => ?_⟩
  obtain ⟨I, -, hI, hP⟩ := hNb (Finset.univ : Finset (Fin n)) (by simpa using hn) P
  obtain ⟨I', hI'I, hI'⟩ := Finset.exists_subset_card_eq hI
  let ι := I'.orderEmbOfFin hI'
  refine ⟨ι, fun j σ σ' hσ => hP j _ _ (fun i => hI'I (I'.orderEmbOfFin_mem hI' _))
    (fun i => hI'I (I'.orderEmbOfFin_mem hI' _)) ?_⟩
  rw [otp_comp_orderEmbedding, otp_comp_orderEmbedding, hσ]

/-- Ramsey for finitely many properties, as an increasing sequence. -/
theorem exists_homogeneous_seq (ℓ N M : ℕ) :
    ∃ Nb : ℕ, ∀ {n : ℕ}, Nb ≤ n → ∀ P : Fin N → (Fin ℓ → Fin n) → Prop,
      ∃ ι : Fin M ↪o Fin n, ∀ j (σ σ' : Fin ℓ → Fin M), StrictMono σ → StrictMono σ' →
        (P j (ι ∘ σ) ↔ P j (ι ∘ σ')) := by
  classical
  obtain ⟨Nb, hNb⟩ := exists_homogeneous_seq_otp ℓ N M
  refine ⟨Nb, fun {n} hn P => ?_⟩
  obtain ⟨ι, hι⟩ := hNb hn P
  exact ⟨ι, fun j σ σ' hσ hσ' => hι j σ σ' (otp_eq_of_strictMono hσ hσ')⟩

end Lax185574Proofs.IP
