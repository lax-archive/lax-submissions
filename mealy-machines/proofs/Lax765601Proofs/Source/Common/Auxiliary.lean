/-
Auxiliary lemmas of a general nature (lists, iteration of a function on a finite
set) that are used in the proofs of the results of *Transducers*
(M. Bojańczyk, June 25, 2026).
-/
import Lax765601Proofs.Source.Common.Basic

namespace Lax765601Proofs.Transducers

/-! ## Lists -/

/-- The last letter of a prefix of length `n + 1`. -/
lemma getLast?_take_succ {B : Type} (x : List B) {n : ℕ} (hn : n < x.length) :
    (x.take (n + 1)).getLast? = x[n]? := by
  simp [List.getLast?_take, List.getElem?_eq_getElem hn]

/-- Two lists of the same length are equal as soon as all their prefixes have
the same last letter. -/
lemma list_eq_of_take_getLast? {B : Type} (x y : List B) (hlen : x.length = y.length)
    (h : ∀ n : ℕ, (x.take n).getLast? = (y.take n).getLast?) : x = y := by
  apply List.ext_getElem hlen
  intro n h1 h2
  have hx := h (n + 1)
  rw [getLast?_take_succ x h1, getLast?_take_succ y h2] at hx
  simpa [List.getElem?_eq_getElem, h1, h2] using hx

/-- Dropping a proper prefix does not change the last letter. -/
lemma getLast?_drop {B : Type} (l : List B) {k : ℕ} (hk : k < l.length) :
    (l.drop k).getLast? = l.getLast? := by
  simp [List.getLast?_drop, Nat.not_le.mpr hk]

/-- The last letter of `x yⁿ z` does not depend on `n`, as long as `n ≥ 1`. -/
lemma getLast?_npow_const {B : Type} (x y z : List B) (m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    (x ++ npow y m ++ z).getLast? = (x ++ npow y n ++ z).getLast? := by
  by_cases hz : z = []
  · subst hz
    simp only [List.append_nil]
    by_cases hy : y = []
    · simp [hy]
    · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
      have h1 : (npow y (k + 1)).getLast? = y.getLast? := by
        rw [npow_succ']
        simp [List.getLast?_append]
        rcases h : y.getLast? with _ | a
        · simp_all [List.getLast?_eq_none_iff]
        · simp
      obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      have h2 : (npow y (j + 1)).getLast? = y.getLast? := by
        rw [npow_succ']
        simp [List.getLast?_append]
        rcases h : y.getLast? with _ | a
        · simp_all [List.getLast?_eq_none_iff]
        · simp
      rw [List.getLast?_append]
      simp_all
  · simp [List.getLast?_append]
    rcases h : z.getLast? with _ | a
    · simp_all [List.getLast?_eq_none_iff]
    · simp

/-! ## Iterating a function on a finite set -/

/-- If every point has a stabilising orbit, then the iterates of the function
stabilise. -/
lemma iterate_stabilises_of_pointwise {S : Type} [Finite S] (h : S → S)
    (hp : ∀ s : S, ∃ N : ℕ, ∀ n ≥ N, h^[n] s = h^[N] s) :
    ∃ N : ℕ, ∀ n ≥ N, h^[n] = h^[N] := by
  classical
  haveI : Fintype S := Fintype.ofFinite S
  choose N hN using hp
  by_cases hempty : (Finset.univ : Finset S) = ∅
  · refine ⟨0, fun n _ => ?_⟩
    funext s
    exact (Finset.univ_eq_empty_iff.mp hempty).elim s
  · let M := Finset.univ.image N |>.max' (Finset.nonempty_of_ne_empty (by simp [hempty]))
    refine ⟨M, fun n hn => ?_⟩
    funext s
    have hle : N s ≤ M := Finset.le_max' _ _ (Finset.mem_image_of_mem N (Finset.mem_univ s))
    have h1 : h^[n] s = h^[N s] s := hN s n (le_trans hle hn)
    have h2 : h^[M] s = h^[N s] s := hN s M hle
    rw [h1, h2.symm]

/-- A sequence with values in a finite set, whose elements are separated by a
family of tests, is eventually constant as soon as each test is eventually
constant along the sequence. -/
lemma eventually_const_of_tests {S V R : Type} [Finite S] (s : ℕ → S) (test : S → V → R)
    (hsep : ∀ x y : S, (∀ v : V, test x v = test y v) → x = y)
    (h : ∀ v : V, ∃ N : ℕ, ∀ n ≥ N, test (s n) v = test (s N) v) :
    ∃ N : ℕ, ∀ n ≥ N, s n = s N := by
  classical
  haveI : Fintype S := Fintype.ofFinite S
  by_cases hV : Nonempty V
  · obtain ⟨v0⟩ := hV
    have sep : ∀ p : S × S, ∃ v : V, p.1 ≠ p.2 → test p.1 v ≠ test p.2 v := by
      intro p
      by_cases hp : p.1 = p.2
      · exact ⟨v0, fun h' => absurd hp h'⟩
      · by_contra hcon
        push_neg at hcon
        exact hp (hsep p.1 p.2 (fun v => (hcon v).2))
    choose vv hvv using sep
    choose NN hNNv using fun p : S × S => h (vv p)
    refine ⟨Finset.univ.sup NN, fun n hn => ?_⟩
    by_contra hne
    have hle : NN (s n, s (Finset.univ.sup NN)) ≤ Finset.univ.sup NN :=
      Finset.le_sup (Finset.mem_univ _)
    have h1 := hNNv (s n, s (Finset.univ.sup NN)) n (le_trans hle hn)
    have h2 := hNNv (s n, s (Finset.univ.sup NN)) (Finset.univ.sup NN) hle
    exact hvv (s n, s (Finset.univ.sup NN)) hne (h1.trans h2.symm)
  · exact ⟨0, fun n _ => hsep _ _ (fun v => absurd ⟨v⟩ hV)⟩

end Lax765601Proofs.Transducers