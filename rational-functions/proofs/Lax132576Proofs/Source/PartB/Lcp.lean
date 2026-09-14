/-
Longest common prefixes of strings and the left distance (Definition `def:left-distance`).

These notions are the combinatorial core of the machine independent characterisation of
subsequential functions (Theorem `thm:subsequential-functions`): the transducer that we construct
outputs the longest common prefix of the outputs on the short extensions of the input read so far,
and the bounded variation property is an upper bound on the left distance. -/
import Lax765601Proofs.Source.Common.Basic
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

/-! ## The longest common prefix of two strings -/

/-- The longest common prefix of two strings. -/
noncomputable def lcp2 {B : Type} : List B → List B → List B
  | [], _ => []
  | _, [] => []
  | a :: x, b :: y => @ite _ (a = b) (Classical.propDecidable _) (a :: lcp2 x y) []

variable {B : Type}

@[simp] lemma lcp2_nil_left (y : List B) : lcp2 [] y = [] := by
  cases y <;> rfl

@[simp] lemma lcp2_nil_right (x : List B) : lcp2 x [] = [] := by
  cases x <;> rfl

lemma lcp2_cons_cons (a b : B) (x y : List B) :
    lcp2 (a :: x) (b :: y) = @ite _ (a = b) (Classical.propDecidable _) (a :: lcp2 x y) [] := rfl

lemma lcp2_cons_cons_pos {a b : B} (h : a = b) (x y : List B) :
    lcp2 (a :: x) (b :: y) = a :: lcp2 x y := by
  rw [lcp2_cons_cons, if_pos h]

lemma lcp2_cons_cons_neg {a b : B} (h : a ≠ b) (x y : List B) :
    lcp2 (a :: x) (b :: y) = [] := by
  rw [lcp2_cons_cons, if_neg h]

lemma lcp2_prefix_left (x y : List B) : lcp2 x y <+: x := by
  induction x generalizing y with
  | nil => simp
  | cons a x ih =>
      cases y with
      | nil => simp
      | cons b y =>
          by_cases h : a = b
          · rw [lcp2_cons_cons_pos h]
            exact List.cons_prefix_cons.2 ⟨rfl, ih y⟩
          · rw [lcp2_cons_cons_neg h]
            simp

lemma lcp2_prefix_right (x y : List B) : lcp2 x y <+: y := by
  induction x generalizing y with
  | nil => simp
  | cons a x ih =>
      cases y with
      | nil => simp
      | cons b y =>
          by_cases h : a = b
          · subst h
            rw [lcp2_cons_cons_pos rfl]
            exact List.cons_prefix_cons.2 ⟨rfl, ih y⟩
          · rw [lcp2_cons_cons_neg h]
            simp

/-- The universal property: a common prefix of `x` and `y` is a prefix of
`lcp2 x y`. -/
lemma prefix_lcp2 {p x y : List B} (hx : p <+: x) (hy : p <+: y) : p <+: lcp2 x y := by
  induction p generalizing x y with
  | nil => simp
  | cons a p ih =>
      obtain ⟨x', rfl⟩ := hx
      obtain ⟨y', rfl⟩ := hy
      rw [List.cons_append, List.cons_append, lcp2_cons_cons_pos rfl]
      exact List.cons_prefix_cons.2 ⟨rfl, ih ⟨x', rfl⟩ ⟨y', rfl⟩⟩

lemma lcp2_comm (x y : List B) : lcp2 x y = lcp2 y x :=
  List.IsPrefix.eq_of_length_le
    (prefix_lcp2 (lcp2_prefix_right x y) (lcp2_prefix_left x y))
    ((prefix_lcp2 (lcp2_prefix_right y x) (lcp2_prefix_left y x)).length_le)

lemma lcp2_length_le_left (x y : List B) : (lcp2 x y).length ≤ x.length :=
  (lcp2_prefix_left x y).length_le

lemma lcp2_length_le_right (x y : List B) : (lcp2 x y).length ≤ y.length :=
  (lcp2_prefix_right x y).length_le

/-- If `x` is a prefix of `y` then it is the longest common prefix. -/
lemma lcp2_eq_left_of_prefix {x y : List B} (h : x <+: y) : lcp2 x y = x :=
  (List.IsPrefix.eq_of_length_le (lcp2_prefix_left x y)
    (prefix_lcp2 (List.prefix_refl x) h).length_le)

/-- Two prefixes of a common string are comparable. -/
lemma prefix_or_prefix_of_prefix {x y z : List B} (hx : x <+: z) (hy : y <+: z) :
    x <+: y ∨ y <+: x :=
  (List.prefix_or_prefix_of_prefix hx hy)

/-- The first letter after the common prefix differs. -/
lemma lcp2_getElem_ne {x y : List B} {n : ℕ} (hn : n = (lcp2 x y).length)
    (hx : n < x.length) (hy : n < y.length) : x[n]? ≠ y[n]? := by
  induction x generalizing y n with
  | nil => simp at hx
  | cons a x ih =>
      cases y with
      | nil => simp at hy
      | cons b y =>
          by_cases hab : a = b
          · subst hab
            rw [lcp2_cons_cons, if_pos rfl] at hn
            simp only [List.length_cons] at hn
            obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨(lcp2 x y).length, by omega⟩
            have hm : m = (lcp2 x y).length := by omega
            have hx' : m < x.length := by simpa using hx
            have hy' : m < y.length := by simpa using hy
            have := ih hm hx' hy'
            simpa using this
          · rw [lcp2_cons_cons, if_neg hab] at hn
            simp only [List.length_nil] at hn
            subst hn
            simpa using hab

/-! ## The left distance -/

/-- The set whose infimum defines the left distance is nonempty. -/
lemma leftDist_set_nonempty (x y : List B) :
    {k : ℕ | ∃ v v₁ v₂ : List B,
      x = v ++ v₁ ∧ y = v ++ v₂ ∧ v₁.length ≤ k ∧ v₂.length ≤ k}.Nonempty :=
  ⟨max x.length y.length, [], x, y, by simp, by simp, by simp, by simp⟩

/-- An upper bound on the left distance, from an explicit decomposition. -/
lemma leftDist_le {x y : List B} {k : ℕ} {v v₁ v₂ : List B}
    (hx : x = v ++ v₁) (hy : y = v ++ v₂) (h₁ : v₁.length ≤ k) (h₂ : v₂.length ≤ k) :
    leftDist x y ≤ k :=
  Nat.sInf_le ⟨v, v₁, v₂, hx, hy, h₁, h₂⟩

/-- The left distance is realised by the longest common prefix. -/
lemma leftDist_eq (x y : List B) :
    leftDist x y = max (x.length - (lcp2 x y).length) (y.length - (lcp2 x y).length) := by
  obtain ⟨x', hx'⟩ := lcp2_prefix_left x y
  obtain ⟨y', hy'⟩ := lcp2_prefix_right x y
  have hxl : (lcp2 x y).length + x'.length = x.length := by
    have := congrArg List.length hx'; simpa using this
  have hyl : (lcp2 x y).length + y'.length = y.length := by
    have := congrArg List.length hy'; simpa using this
  apply le_antisymm
  · exact leftDist_le hx'.symm hy'.symm (by omega) (by omega)
  · have hmem : ∃ v v₁ v₂ : List B, x = v ++ v₁ ∧ y = v ++ v₂ ∧
        v₁.length ≤ leftDist x y ∧ v₂.length ≤ leftDist x y :=
      Nat.sInf_mem (leftDist_set_nonempty x y)
    obtain ⟨v, v₁, v₂, hx, hy, h₁, h₂⟩ := hmem
    have hv : v <+: lcp2 x y := prefix_lcp2 ⟨v₁, hx.symm⟩ ⟨v₂, hy.symm⟩
    have hvl : v.length ≤ (lcp2 x y).length := hv.length_le
    have hxlen : x.length = v.length + v₁.length := by
      have := congrArg List.length hx; simpa using this
    have hylen : y.length = v.length + v₂.length := by
      have := congrArg List.length hy; simpa using this
    omega

/-- From a bound on the left distance: the tails after the longest common prefix
are short. -/
lemma length_sub_lcp2_le_of_leftDist {x y : List B} {k : ℕ} (h : leftDist x y ≤ k) :
    x.length - (lcp2 x y).length ≤ k ∧ y.length - (lcp2 x y).length ≤ k := by
  rw [leftDist_eq] at h
  exact ⟨le_trans (le_max_left _ _) h, le_trans (le_max_right _ _) h⟩

/-- From a bound on the left distance: the lengths are close. -/
lemma length_sub_le_of_leftDist {x y : List B} {k : ℕ} (h : leftDist x y ≤ k) :
    x.length - y.length ≤ k := by
  obtain ⟨h₁, _⟩ := length_sub_lcp2_le_of_leftDist h
  have := lcp2_length_le_right x y
  omega

lemma leftDist_comm (x y : List B) : leftDist x y = leftDist y x := by
  rw [leftDist_eq, leftDist_eq, lcp2_comm]
  omega

/-- From a bound on the left distance: the strings agree on a long prefix. -/
lemma prefix_take_of_leftDist {x y : List B} {k n : ℕ} (h : leftDist x y ≤ k)
    (hn : n + k ≤ x.length) : x.take n <+: y := by
  obtain ⟨h₁, _⟩ := length_sub_lcp2_le_of_leftDist h
  have hle : n ≤ (lcp2 x y).length := by omega
  calc x.take n = (lcp2 x y).take n := by
        rw [List.prefix_iff_eq_take.1 (lcp2_prefix_left x y), List.take_take]
        congr 1
        omega
    _ <+: lcp2 x y := List.take_prefix _ _
    _ <+: y := lcp2_prefix_right x y

/-- All but the last `k` letters of `x` are a prefix of `y`. -/
lemma take_sub_prefix_of_leftDist {x y : List B} {k : ℕ} (h : leftDist x y ≤ k) :
    x.take (x.length - k) <+: y := by
  by_cases hk : x.length ≤ k
  · rw [show x.length - k = 0 by omega]
    simp
  · exact prefix_take_of_leftDist h (by omega)

/-- The value of a string at a position inside a prefix. -/
lemma getElem?_of_prefix {p x : List B} (h : p <+: x) {m : ℕ} (hm : m < p.length) :
    x[m]? = p[m]? := by
  obtain ⟨t, rfl⟩ := h
  rw [List.getElem?_append_left hm]

/-- **Transfer of a divergence.**  If `x` and `y` end with the strings `S` and
`S'`, which start with different letters (or one of which is empty), and the
parts before `S` and `S'` have the same length, then the longest common prefix
of `x` and `y` is no longer than that part. -/
lemma lcp2_length_le_of_diverge {S S' x y : List B} (hS : S <:+ x) (hS' : S' <:+ y)
    (hlen : x.length - S.length = y.length - S'.length)
    (hdiv : ∀ (c : B) (s : List B) (c' : B) (s' : List B), S = c :: s → S' = c' :: s' → c ≠ c') :
    (lcp2 x y).length ≤ x.length - S.length := by
  obtain ⟨p, hp⟩ := hS
  obtain ⟨p', hp'⟩ := hS'
  have hpl : p.length = x.length - S.length := by
    have := congrArg List.length hp
    simp only [List.length_append] at this
    omega
  have hp'l : p'.length = y.length - S'.length := by
    have := congrArg List.length hp'
    simp only [List.length_append] at this
    omega
  rcases S with _ | ⟨c, s⟩
  · have : (lcp2 x y).length ≤ x.length := lcp2_length_le_left x y
    simpa using this
  rcases S' with _ | ⟨c', s'⟩
  · have h1 : (lcp2 x y).length ≤ y.length := lcp2_length_le_right x y
    simp only [List.length_nil, Nat.sub_zero] at hlen hp'l
    omega
  · by_contra hcon
    push_neg at hcon
    have hcne : c ≠ c' := hdiv c s c' s' rfl rfl
    have hxm : x[p.length]? = some c := by
      rw [← hp, List.getElem?_append_right (by omega)]
      simp
    have hym : y[p'.length]? = some c' := by
      rw [← hp', List.getElem?_append_right (by omega)]
      simp
    have hm : p.length = p'.length := by omega
    have h1 : x[p.length]? = (lcp2 x y)[p.length]? :=
      getElem?_of_prefix (lcp2_prefix_left x y) (by omega)
    have h2 : y[p'.length]? = (lcp2 x y)[p'.length]? :=
      getElem?_of_prefix (lcp2_prefix_right x y) (by omega)
    rw [hxm] at h1
    rw [hym, ← hm] at h2
    rw [← h1] at h2
    exact hcne (Option.some_injective _ h2.symm)

/-! ## The left distance is a metric -/

/-- Two strings agree on any prefix of their longest common prefix. -/
lemma take_eq_take_of_le_lcp2 {x y : List B} {m : ℕ} (hm : m ≤ (lcp2 x y).length) :
    x.take m = y.take m := by
  obtain ⟨t, ht⟩ := lcp2_prefix_left x y
  obtain ⟨t', ht'⟩ := lcp2_prefix_right x y
  have hx : x.take m = (lcp2 x y).take m := by
    conv_lhs => rw [← ht]
    rw [List.take_append, Nat.sub_eq_zero_of_le hm]
    simp
  have hy : y.take m = (lcp2 x y).take m := by
    conv_lhs => rw [← ht']
    rw [List.take_append, Nat.sub_eq_zero_of_le hm]
    simp
  rw [hx, hy]

/-- The longest common prefix is an ultrametric-like operation. -/
lemma lcp2_length_min_le (x y z : List B) :
    min (lcp2 x y).length (lcp2 y z).length ≤ (lcp2 x z).length := by
  set m := min (lcp2 x y).length (lcp2 y z).length with hm
  have h1 : x.take m = y.take m := take_eq_take_of_le_lcp2 (by rw [hm]; exact min_le_left _ _)
  have h2 : y.take m = z.take m := take_eq_take_of_le_lcp2 (by rw [hm]; exact min_le_right _ _)
  have hpx : x.take m <+: x := List.take_prefix _ _
  have hpz : x.take m <+: z := by
    rw [h1, h2]
    exact List.take_prefix _ _
  have hle := (prefix_lcp2 hpx hpz).length_le
  have hmx : m ≤ x.length := le_trans (by rw [hm]; exact min_le_left _ _) (lcp2_length_le_left x y)
  simp only [List.length_take] at hle
  omega

/-- The triangle inequality for the left distance. -/
lemma leftDist_triangle (x y z : List B) : leftDist x z ≤ leftDist x y + leftDist y z := by
  rw [leftDist_eq, leftDist_eq, leftDist_eq]
  have hm := lcp2_length_min_le x y z
  have h1 := lcp2_length_le_left x y
  have h2 := lcp2_length_le_right x y
  have h3 := lcp2_length_le_left y z
  have h4 := lcp2_length_le_right y z
  have h5 := lcp2_length_le_left x z
  have h6 := lcp2_length_le_right x z
  omega

lemma leftDist_self (x : List B) : leftDist x x = 0 := by
  simpa using leftDist_le (x := x) (y := x) (k := 0) (v := x) (v₁ := []) (v₂ := [])
    (by simp) (by simp) (by simp) (by simp)

end Lax132576Proofs.Transducers
