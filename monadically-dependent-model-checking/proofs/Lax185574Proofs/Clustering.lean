import Lax185574.Clustering
import Lax185574Proofs.WalkDistance
import Mathlib.Data.Finset.Card

/-!
Proof of the clustering lemma lem:clustering, in the form of the concept:
an admissible radius exists in the range `[r, 9^(ℓ−1) r]`, and every
admissible pair detects far vertices. The existence part is the grouping
argument of Corollary 3.4 of the locality note, adapted from lax-3
(nowhere-dense-model-checking), file `Lax3Proofs/Clusters.lean`. The
detection part is the argument of Lemma 3.5 of the locality note.
-/

namespace Lax185574Proofs.Clustering

open Lax185574.GaifmanGraph Lax185574.Clustering Lax185574Proofs.WalkDistance

variable {V : Type*}

/-- The grouping iteration. From a selection map at scale `r · 9^t` onto a
nonempty set `I` of surviving indices with `t + |I| ≤ ℓ`, an admissible
pair in the range `[r, 9^(ℓ−1) r]` is reached. Each round merges two
surviving entries within `8 r 9^t` of each other, which costs one index
and multiplies the scale by nine. Adapted from lax-3, file
`Lax3Proofs/Clusters.lean`. -/
theorem exists_admissible_of_card_le (G : SimpleGraph V) (r : ℕ) {ℓ : ℕ} (a : Fin ℓ → V) :
    ∀ (n t : ℕ) (I : Finset (Fin ℓ)) (sel : Fin ℓ → Fin ℓ), I.card ≤ n → I.Nonempty →
      t + I.card ≤ ℓ → (∀ i, sel i ∈ I) → (∀ i ∈ I, sel i = i) →
      (∀ i, WithinDist G (r * 9 ^ t) (a i) (a (sel i))) →
      ∃ ρ β, r ≤ ρ ∧ ρ ≤ 9 ^ (ℓ - 1) * r ∧ Admissible G r a ρ β := by
  intro n
  induction n with
  | zero =>
    intro t I sel hcard hne _ _ _ _
    exact absurd (Finset.card_pos.2 hne) (by omega)
  | succ n ih =>
    intro t I sel hcard hne hsum hmem hid hclose
    have hpos : 0 < I.card := Finset.card_pos.2 hne
    have hrR : r ≤ r * 9 ^ t := Nat.le_mul_of_pos_right r (Nat.pow_pos (by norm_num : 0 < 9))
    by_cases hfar : ∀ i ∈ I, ∀ j ∈ I, i ≠ j → ¬ WithinDist G (8 * (r * 9 ^ t)) (a i) (a j)
    · refine ⟨r * 9 ^ t, sel, hrR, ?_, fun i j => ⟨fun h => ?_, fun h hij => ?_⟩⟩
      · rw [mul_comm]
        exact Nat.mul_le_mul_right r (Nat.pow_le_pow_right (by norm_num) (by omega))
      · have h1 := hclose i
        have h2 := withinDist_symm (hclose j)
        rw [h] at h1
        exact withinDist_mono (by omega) (withinDist_trans h1 h2)
      · refine hfar _ (hmem i) _ (hmem j) h ?_
        have h1 := withinDist_symm (hclose i)
        have h2 := hclose j
        exact withinDist_mono (by omega) (withinDist_trans (withinDist_trans h1 hij) h2)
    · push Not at hfar
      obtain ⟨u, hu, v, hv, huv, hduv⟩ := hfar
      have herase : (I.erase u).card = I.card - 1 := Finset.card_erase_of_mem hu
      have hvI : v ∈ I.erase u := Finset.mem_erase.2 ⟨huv.symm, hv⟩
      have harith : r * 9 ^ t + 8 * (r * 9 ^ t) = r * 9 ^ (t + 1) := by
        rw [pow_succ]; ring
      have hmono : r * 9 ^ t ≤ r * 9 ^ (t + 1) :=
        Nat.mul_le_mul (Nat.le_refl r) (Nat.pow_le_pow_right (by omega) (by omega))
      refine ih (t + 1) (I.erase u) (fun i => if sel i = u then v else sel i)
        (by omega) ⟨v, hvI⟩ (by omega) ?_ ?_ ?_
      · intro i
        by_cases h : sel i = u
        · simpa [h] using hvI
        · simpa [h] using Finset.mem_erase.2 ⟨h, hmem i⟩
      · intro i hi
        have hiI : i ∈ I := Finset.mem_of_mem_erase hi
        have hne' : i ≠ u := (Finset.mem_erase.1 hi).1
        have : sel i = i := hid i hiI
        simp [this, hne']
      · intro i
        by_cases h : sel i = u
        · have h1 : WithinDist G (r * 9 ^ t) (a i) (a u) := by
            have := hclose i; rwa [h] at this
          have h2 := withinDist_trans h1 hduv
          simpa [h, harith] using h2
        · simpa [h] using withinDist_mono hmono (hclose i)

/-- An admissible pair with `r ≤ ρ ≤ 9^(ℓ−1) r` exists. -/
theorem exists_admissible (G : SimpleGraph V) (r ℓ : ℕ) (hℓ : 1 ≤ ℓ) (a : Fin ℓ → V) :
    ∃ ρ β, r ≤ ρ ∧ ρ ≤ 9 ^ (ℓ - 1) * r ∧ Admissible G r a ρ β :=
  exists_admissible_of_card_le G r a ℓ 0 Finset.univ id (by simp)
    ⟨⟨0, hℓ⟩, Finset.mem_univ _⟩ (by simp) (fun _ => Finset.mem_univ _) (fun _ _ => rfl)
    (fun i => withinDist_refl G _ (a i))

/-- The detection property of an admissible pair. -/
theorem detect [Finite V] (G : SimpleGraph V) (r : ℕ) {ℓ : ℕ} (a : Fin ℓ → V) (ρ : ℕ)
    (β : Fin ℓ → Fin ℓ) (hℓ : 1 ≤ ℓ) (hrρ : r ≤ ρ) (hadm : Admissible G r a ρ β)
    (X S : Set V) (H : ℕ) (hSX : S ⊆ X)
    (hscat : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ WithinDist G (4 * ρ) x y)
    (hmax : ∀ x ∈ X, ∃ y ∈ S, WithinDist G (4 * ρ) x y) (hH : 4 * ρ + r ≤ H) :
    ((∃ x ∈ X, ∀ i, ¬ WithinDist G r (a i) x) ↔
      (∃ x ∈ X, (∀ i, ¬ WithinDist G r (a i) x) ∧ ∃ i, WithinDist G H (a i) x) ∨
      (β '' {i | ∃ x ∈ X, WithinDist G r (a i) x}).ncard < S.ncard) := by
  classical
  have : Nonempty (Fin ℓ) := ⟨⟨0, hℓ⟩⟩
  set I := {i | ∃ x ∈ X, WithinDist G r (a i) x}
  have hfinS : S.Finite := Set.toFinite S
  constructor
  · rintro ⟨x₀, hx₀X, hx₀⟩
    have : Nonempty V := ⟨x₀⟩
    by_cases hnear : ∃ x ∈ X, (∀ i, ¬ WithinDist G r (a i) x) ∧ ∃ i, WithinDist G H (a i) x
    · exact Or.inl hnear
    right
    push Not at hnear
    -- every vertex of `X` within `H` of an entry is within `r` of an entry
    have hclose : ∀ x ∈ X, ∀ i, WithinDist G H (a i) x → ∃ m, WithinDist G r (a m) x := by
      intro x hx i hi
      by_contra hc
      push Not at hc
      exact hnear x hx hc i hi
    -- a vertex of `S` within `4ρ + r` of an entry is within `r` of an entry
    -- of the same block
    have hblock : ∀ s ∈ S, ∀ i, WithinDist G (r + 4 * ρ) (a i) s →
        ∃ m, WithinDist G r (a m) s ∧ β i = β m := by
      intro s hs i hi
      obtain ⟨m, hm⟩ := hclose s (hSX hs) i (withinDist_mono (by omega) hi)
      refine ⟨m, hm, ?_⟩
      by_contra hne
      exact (hadm i m).2 hne
        (withinDist_mono (by omega) (withinDist_trans hi (withinDist_symm hm)))
    -- every index of `I` reaches a vertex of `S` within `r + 4ρ`
    have hreach : ∀ i ∈ I, ∃ s ∈ S, WithinDist G (r + 4 * ρ) (a i) s := by
      rintro i ⟨x, hx, hix⟩
      obtain ⟨s, hs, hxs⟩ := hmax x hx
      exact ⟨s, hs, withinDist_trans hix hxs⟩
    choose! sf hsfS hsf using hreach
    have hrep : ∀ b ∈ β '' I, ∃ i ∈ I, β i = b := by
      rintro b ⟨i, hi, rfl⟩
      exact ⟨i, hi, rfl⟩
    choose! ib hibI hib using hrep
    obtain ⟨s₀, hs₀, hx₀s₀⟩ := hmax x₀ hx₀X
    -- the representative of `x₀` is not within `r` of any entry
    have hs₀far : ∀ m, ¬ WithinDist G r (a m) s₀ := by
      intro m hm
      have h1 : WithinDist G H (a m) x₀ :=
        withinDist_mono (by omega) (withinDist_trans hm (withinDist_symm hx₀s₀))
      exact hnear x₀ hx₀X hx₀ m h1
    have hle : (β '' I).ncard ≤ (S \ {s₀}).ncard := by
      refine Set.ncard_le_ncard_of_injOn (fun b => sf (ib b)) ?_ ?_ hfinS.sdiff
      · intro b hb
        refine ⟨hsfS _ (hibI b hb), fun h => ?_⟩
        obtain ⟨m, hm, -⟩ := hblock _ (hsfS _ (hibI b hb)) _ (hsf _ (hibI b hb))
        rw [Set.mem_singleton_iff.1 h] at hm
        exact hs₀far m hm
      · intro b hb b' hb' hbb
        simp only at hbb
        obtain ⟨m, hm, hβ⟩ := hblock _ (hsfS _ (hibI b hb)) _ (hsf _ (hibI b hb))
        obtain ⟨m', hm', hβ'⟩ := hblock _ (hsfS _ (hibI b' hb')) _ (hsf _ (hibI b' hb'))
        rw [← hib b hb, ← hib b' hb', hβ, hβ']
        rw [hbb] at hm
        by_contra hne
        exact (hadm m m').2 hne
          (withinDist_mono (by omega) (withinDist_trans hm (withinDist_symm hm')))
    have hlt : (S \ {s₀}).ncard < S.ncard := Set.ncard_sdiff_singleton_lt_of_mem hs₀ hfinS
    omega
  · rintro (⟨x, hx, hfar, -⟩ | hcard)
    · exact ⟨x, hx, hfar⟩
    by_contra hall
    push Not at hall
    have hnear : ∀ s ∈ S, ∃ i, WithinDist G r (a i) s := fun s hs => hall s (hSX hs)
    choose! idx hidx using hnear
    have hle : S.ncard ≤ (β '' I).ncard := by
      refine Set.ncard_le_ncard_of_injOn (fun s => β (idx s)) ?_ ?_ (Set.toFinite _)
      · intro s hs
        exact ⟨idx s, ⟨s, hSX hs, hidx s hs⟩, rfl⟩
      · intro s hs s' hs' hss
        by_contra hne
        refine hscat s hs s' hs' hne ?_
        have h1 := (hadm (idx s) (idx s')).1 hss
        have h2 := withinDist_trans (withinDist_trans (withinDist_symm (hidx s hs)) h1)
          (hidx s' hs')
        exact withinDist_mono (by omega) h2
    omega

/--
---
conclusion: Lax185574.Clustering.clustering
---
The existence of an admissible pair is the grouping iteration: start with
all indices surviving at scale `r`, and while two surviving entries are
within eight times the scale, drop one of them and multiply the scale by
nine. At the end, entries of one group are within twice the scale `ρ`,
hence within `4ρ − 2r`, and entries of different groups are farther apart
than `6ρ ≥ 4ρ + 2r`.

For the detection property, if every vertex of `X` is near the tuple,
then the vertices of `S` lie in distinct blocks, by the scattering of `S`.
Conversely, if some vertex `x₀` of `X` is far from the tuple and no vertex
of `X` is at a distance between `r` and `H`, then the blocks met by `X`
inject into `S` minus the representative of `x₀`.
-/
theorem clustering [Finite V] (G : SimpleGraph V) (r ℓ : ℕ) (hℓ : 1 ≤ ℓ) (a : Fin ℓ → V) :
    (∃ ρ β, r ≤ ρ ∧ ρ ≤ 9 ^ (ℓ - 1) * r ∧ Admissible G r a ρ β) ∧
    ∀ ρ β, r ≤ ρ → Admissible G r a ρ β →
      ∀ (X S : Set V) (H : ℕ), S ⊆ X →
        (∀ x ∈ S, ∀ y ∈ S, x ≠ y → ¬ WithinDist G (4 * ρ) x y) →
        (∀ x ∈ X, ∃ y ∈ S, WithinDist G (4 * ρ) x y) →
        4 * ρ + r ≤ H →
        ((∃ x ∈ X, ∀ i, ¬ WithinDist G r (a i) x) ↔
          (∃ x ∈ X, (∀ i, ¬ WithinDist G r (a i) x) ∧ ∃ i, WithinDist G H (a i) x) ∨
          (β '' {i | ∃ x ∈ X, WithinDist G r (a i) x}).ncard < S.ncard) :=
  ⟨exists_admissible G r ℓ hℓ a, fun ρ β hrρ hadm X S H hSX hscat hmax hH =>
    detect G r a ρ β hℓ hrρ hadm X S H hSX hscat hmax hH⟩

end Lax185574Proofs.Clustering
