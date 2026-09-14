/- Factors of a string between two optional bounds, and the transfer of a split along an equality of
`(k+1)`-types.  These are the combinatorial ingredients of Claim `claim:fo-composition-quantifier-rank`
(the compositionality claim inside the proof of Lemma `lem:k-types-fo-equivalence` of
*Transducers*, M. Bojańczyk).

A bound is an element of `Option ℕ`: `none` stands for the beginning of the
string (as a left bound) or for its end (as a right bound), and `some c` stands
for the position `c`, which is *excluded* from the factor.  With this
convention the four factors that occur in the proof — the whole string, a
prefix, a suffix and the open interval between two marked positions — are the
four instances of `segP`.
-/
import Lax916827Proofs.Source.PartC.KTypes
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

variable {A : Type}

/-! ## Factors between two bounds -/

/-- The first position of the factor delimited by the left bound. -/
def loB : Option ℕ → ℕ
  | none => 0
  | some c => c + 1

/-- The first position after the factor delimited by the right bound. -/
def hiB (w : List A) : Option ℕ → ℕ
  | none => w.length
  | some d => d

/-- The factor of `w` strictly between the bounds `l` and `r`. -/
def segP (w : List A) (l r : Option ℕ) : List A := (w.take (hiB w r)).drop (loB l)

@[simp] lemma segP_none_none (w : List A) : segP w none none = w := by
  simp [segP, loB, hiB]

@[simp] lemma segP_none_some (w : List A) (d : ℕ) : segP w none (some d) = w.take d := by
  simp [segP, loB, hiB]

@[simp] lemma segP_some_none (w : List A) (c : ℕ) : segP w (some c) none = w.drop (c + 1) := by
  simp [segP, loB, hiB]

@[simp] lemma segP_some_some (w : List A) (c d : ℕ) :
    segP w (some c) (some d) = (w.take d).drop (c + 1) := rfl

lemma hiB_le_length {w : List A} {r : Option ℕ} (hr : ∀ d ∈ r, d < w.length) :
    hiB w r ≤ w.length := by
  cases r with
  | none => exact le_rfl
  | some d => exact le_of_lt (hr d rfl)

lemma segP_length (w : List A) (l r : Option ℕ) (hr : hiB w r ≤ w.length) :
    (segP w l r).length = hiB w r - loB l := by
  simp [segP, Nat.min_eq_left hr]

@[simp] lemma segP_self (w : List A) (m : ℕ) : segP w (some m) (some m) = [] := by
  simp [segP, loB, hiB]

/-- Splitting a factor at a position inside it. -/
lemma segP_split {w : List A} {l r : Option ℕ} {m : ℕ} {a : A} (ha : w[m]? = some a)
    (hl : loB l ≤ m) (hr : m < hiB w r) :
    segP w l r = segP w l (some m) ++ a :: segP w (some m) r := by
  have hmw : m < w.length := by
    by_contra h
    rw [List.getElem?_eq_none (by omega)] at ha
    exact absurd ha (by simp)
  set H := hiB w r with hH
  set lo := loB l with hlo
  have hu : m < (w.take H).length := by
    rw [List.length_take]; omega
  have h1 : (w.take H).take m = w.take m := by
    rw [List.take_take, Nat.min_eq_left (le_of_lt hr)]
  have h2 : (w.take H)[m]? = some a := by
    rw [List.getElem?_take_of_lt hr]; exact ha
  have h3 : (w.take H).drop lo = ((w.take H).take m).drop lo ++ (w.take H).drop m := by
    conv_lhs => rw [← List.take_append_drop m (w.take H)]
    rw [List.drop_append]
    congr 1
    rw [List.length_take, Nat.min_eq_left (le_of_lt hu)]
    rw [Nat.sub_eq_zero_of_le hl, List.drop_zero]
  have h4 : (w.take H).drop m = a :: (w.take H).drop (m + 1) := by
    rw [List.drop_eq_getElem_cons hu]
    congr 1
    have := h2
    rw [List.getElem?_eq_getElem hu] at this
    exact Option.some.inj this
  show (w.take H).drop lo = ((w.take m).drop lo) ++ a :: ((w.take H).drop (m + 1))
  rw [h3, h4, h1]

/-- The letter at a position of a factor is the letter at the corresponding
position of the string. -/
lemma segP_getElem? (w : List A) (l r : Option ℕ) (q : ℕ) (hq : q < (segP w l r).length) :
    (segP w l r)[q]? = w[loB l + q]? := by
  have hlen : (segP w l r).length = min (hiB w r) w.length - loB l := by
    simp [segP]
  rw [hlen] at hq
  show ((w.take (hiB w r)).drop (loB l))[q]? = _
  rw [List.getElem?_drop, List.getElem?_take_of_lt (by omega)]

/-- The prefix of a factor is a factor. -/
lemma segP_take (w : List A) (l r : Option ℕ) (q : ℕ) (hq : q ≤ (segP w l r).length) :
    (segP w l r).take q = segP w l (some (loB l + q)) := by
  have hlen : (segP w l r).length = min (hiB w r) w.length - loB l := by
    simp [segP]
  rw [hlen] at hq
  show ((w.take (hiB w r)).drop (loB l)).take q = (w.take (loB l + q)).drop (loB l)
  rw [List.take_drop, List.take_take]
  rcases Nat.lt_or_ge (min (hiB w r) w.length) (loB l) with h | h
  · have hq0 : q = 0 := by omega
    subst hq0
    have h1 : (w.take (min (loB l + 0) (hiB w r))).drop (loB l) = [] := by
      apply List.drop_eq_nil_of_le
      rw [List.length_take]
      omega
    have h2 : (w.take (loB l + 0)).drop (loB l) = [] := by
      apply List.drop_eq_nil_of_le
      rw [List.length_take]
      omega
    rw [h1, h2]
  · rw [Nat.min_eq_left (by omega)]

/-- The suffix of a factor is a factor. -/
lemma segP_drop (w : List A) (l r : Option ℕ) (q : ℕ) :
    (segP w l r).drop (q + 1) = segP w (some (loB l + q)) r := by
  show ((w.take (hiB w r)).drop (loB l)).drop (q + 1) = (w.take (hiB w r)).drop (loB l + q + 1)
  rw [List.drop_drop, show loB l + (q + 1) = loB l + q + 1 from by omega]

/-! ## Transfer of a split -/

/-- If two strings have the same `(k+1)`-type, then every position of the first
one is matched by a position of the second one carrying the same letter and
splitting the string into two factors of the same `k`-types.  This is the
content of Definition `def:k-types` of the `(k+1)`-type as a set of triples. -/
lemma exists_split_of_tp_succ_eq (k : ℕ) (g g' : List A) (h : tp (k + 1) g = tp (k + 1) g')
    (p : ℕ) (hp : p < g.length) :
    ∃ q, q < g'.length ∧ g'[q]? = g[p]? ∧
      tp k (g.take p) = tp k (g'.take q) ∧ tp k (g.drop (p + 1)) = tp k (g'.drop (q + 1)) := by
  have hg : g = g.take p ++ g[p] :: g.drop (p + 1) := by
    conv_lhs => rw [← List.take_append_drop p g]
    rw [List.drop_eq_getElem_cons hp]
  have hmem : (tp k (g.take p), g[p], tp k (g.drop (p + 1))) ∈ tpSet k g :=
    ⟨g.take p, g[p], g.drop (p + 1), hg, rfl⟩
  rw [(tp_succ_eq_iff_tpSet k g g').mp h] at hmem
  obtain ⟨h₁, b, h₂, hg', heq⟩ := hmem
  simp only [Prod.mk.injEq] at heq
  obtain ⟨e1, e2, e3⟩ := heq
  refine ⟨h₁.length, ?_, ?_, ?_, ?_⟩
  · rw [hg']; simp
  · rw [hg', List.getElem?_append_right (le_refl _), Nat.sub_self,
      List.getElem?_eq_getElem hp]
    simp [← e2]
  · rw [hg', List.take_left]; exact e1
  · rw [hg']
    have : (h₁ ++ b :: h₂).drop (h₁.length + 1) = h₂ := by
      rw [← List.drop_drop, List.drop_left]
      simp
    rw [this]; exact e3

end Lax314295Proofs.Transducers
