import Lax185574Proofs.Chain.Damping
import Lax185574Proofs.Chain.Additive
import Lax185574.ChainTheorem

/-!
The chain of the companion paper's Theorem 4.4 (the proof of
`thm:main-ordering` with `q = ⌈n^{ε/2r}⌉`), as an explicit function of the
graph.

* `qOf n r ε` is the least `q ∈ [1, n+1]` with `q^{2r·den ε} ≥ n^{num ε}`,
  and `n + 1` if there is none.
* The ordering is the Welzl ordering of the graph.
* `S₀ = V` and `S_{i+1}` is the damping step applied to `S_i`, until the
  empty set is reached.
* `B_i = ⋃_{j ≥ i} S_j`.

Graphs with at most one vertex get the chain `[V, ∅]`.

Every graph gets a decreasing chain of length at most `2 + 2r/ε`. If the
growth ratio of atomic types is `γ₁`, the growth ratio of `(r+1)`-types
is `γ`, and the Welzl ordering has alternation `α`, then every radius-`r`
ball of the `B_{i+1}`-flip metric meets at most
`γ₁ · (2 + 2r/ε) · (200 (q+1)(α+1)K²)^r` atomic types over `B_i`, where
`K = max(γ, 4γ₁(log₂ n + 1), 1)`.
-/

set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]

section Defs

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- `q = ⌈n^{ε/2r}⌉`, capped at `n + 1`. -/
def qOf (n r : ℕ) (ε : ℚ) : ℕ :=
  (firstFrom (fun q => decide (n ^ ε.num.natAbs ≤ q ^ (2 * r * ε.den))) 1 (n + 1)).getD (n + 1)

/-- The Welzl ordering as positions. -/
def welzlVOrder : VOrder V := listOrder (welzlOrder G) welzlOrder_nodup mem_welzlOrder

/-- The damping sequence `A, damp A, damp (damp A), …` up to the first
empty set (excluded), with fuel `f`. -/
def dampSeq (r : ℕ) (o : VOrder V) (q : ℕ) : ℕ → Finset V → List (Finset V)
  | 0, _ => []
  | f + 1, A => if A = ∅ then [] else A :: dampSeq r o q f (damp G r o q A)

/-- The unions of the suffixes of a list. -/
def suffixUnions (L : List (Finset V)) : List (Finset V) :=
  (List.range L.length).map fun i => (Ico i L.length).biUnion fun j => L.getD j ∅

/-- The sets `S₀ = V, S₁, …, S_m = ∅`. -/
def chainSeq (r : ℕ) (ε : ℚ) : List (Finset V) :=
  dampSeq G r (welzlVOrder G) (qOf (Fintype.card V) r ε) (Fintype.card V + 1) univ ++ [∅]

/-- **The chain** `V = B₀ ⊇ B₁ ⊇ ⋯ ⊇ B_m = ∅`. -/
def chainAlg (r : ℕ) (ε : ℚ) : List (Finset V) :=
  if Fintype.card V ≤ 1 then [univ, ∅] else suffixUnions (chainSeq G r ε)

end Defs

/-! ### Suffix unions -/

section Suffix

theorem length_suffixUnions (L : List (Finset V)) : (suffixUnions L).length = L.length := by
  simp [suffixUnions]

theorem getElem_suffixUnions (L : List (Finset V)) (i : ℕ) (hi : i < (suffixUnions L).length) :
    (suffixUnions L)[i] = (Ico i L.length).biUnion fun j => L.getD j ∅ := by
  simp [suffixUnions]

end Suffix

/-! ### The damping sequence -/

section Seq

variable {G : SimpleGraph V} [DecidableRel G.Adj] {r : ℕ} {o : VOrder V} {q : ℕ}

/-- The damping sequence, followed by `∅`: it starts with `A`, its last
entry is `∅`, all others are nonempty, every entry is the damping step
applied to the previous one, and the `i`-th entry has at most `|A| / q^i`
elements. -/
theorem dampSeq_spec (hq : 2 ≤ q) : ∀ (f : ℕ) (A : Finset V), A.card < f →
    let L := dampSeq G r o q f A ++ [∅]
    L.head? = some A ∧
    (∀ i (h : i + 1 < L.length), L[i + 1] = damp G r o q L[i]) ∧
    (∀ i (h : i + 1 < L.length), L[i].Nonempty) ∧
    (∀ i (h : i < L.length), q ^ i * L[i].card ≤ A.card)
  | 0, A, h => by omega
  | f + 1, A, h => by
    by_cases hA : A = ∅
    · subst hA; simp [dampSeq]
    have hne : A.Nonempty := nonempty_iff_ne_empty.2 hA
    have hlt := damp_lt (G := G) r o hq hne
    obtain ⟨ih1, ih2, ih3, ih4⟩ := dampSeq_spec hq f (damp G r o q A) (by omega)
    simp only [dampSeq, if_neg hA, List.cons_append]
    refine ⟨rfl, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_⟩
    · rcases i with _ | i
      · simp only [List.getElem_cons_succ, List.getElem_cons_zero]
        have := List.head?_eq_getElem?
          (l := dampSeq G r o q f (damp G r o q A) ++ [∅])
        rw [ih1] at this
        exact (Option.some.inj (this.trans (List.getElem?_eq_getElem (by simp)))).symm
      · simp only [List.getElem_cons_succ]
        exact ih2 i (by simp at hi ⊢; omega)
    · rcases i with _ | i
      · simpa using hne
      · simp only [List.getElem_cons_succ]
        exact ih3 i (by simp at hi ⊢; omega)
    · rcases i with _ | i
      · simp
      · simp only [List.getElem_cons_succ]
        have := ih4 i (by simp at hi ⊢; omega)
        have hd := damp_card (G := G) r o q A
        calc q ^ (i + 1) * _ = q * (q ^ i * _) := by ring
          _ ≤ q * (damp G r o q A).card := Nat.mul_le_mul_left _ this
          _ ≤ A.card := hd

end Seq

/-! ### `q` -/

section Q

theorem firstFrom_lt {p : ℕ → Bool} : ∀ {k f a : ℕ}, firstFrom p k f = some a → a < k + f
  | _, 0, _, h => by simp [firstFrom] at h
  | k, f + 1, a, h => by
    unfold firstFrom at h
    split_ifs at h
    · cases h; omega
    · have := firstFrom_lt h; omega

theorem qOf_spec {n r : ℕ} {ε : ℚ} (hn : 2 ≤ n) (hε : 0 < ε) :
    2 ≤ qOf n r ε ∧ qOf n r ε ≤ n + 1 ∧
      (qOf n r ε - 1) ^ (2 * r * ε.den) ≤ n ^ ε.num.natAbs ∧
      (n ^ ε.num.natAbs ≤ qOf n r ε ^ (2 * r * ε.den) ∨ n < qOf n r ε) := by
  have ha : 1 ≤ ε.num.natAbs := by
    have := Rat.num_pos.2 hε; omega
  have hp1 : ¬ (n ^ ε.num.natAbs ≤ 1 ^ (2 * r * ε.den)) := by
    rw [one_pow, not_le]; exact Nat.one_lt_pow (by omega) (by omega)
  unfold qOf
  cases h : firstFrom (fun q => decide (n ^ ε.num.natAbs ≤ q ^ (2 * r * ε.den))) 1 (n + 1) with
  | none =>
    simp only [Option.getD_none]
    refine ⟨by omega, le_rfl, ?_, Or.inr (by omega)⟩
    by_contra hc; push Not at hc
    obtain ⟨a, ha⟩ := firstFrom_isSome (p := fun q => decide (n ^ ε.num.natAbs ≤
      q ^ (2 * r * ε.den))) (k := 1) (f := n + 1) (b := n) (by omega) (by omega)
      (by simp only [decide_eq_true_eq]; simp only [Nat.add_sub_cancel] at hc; exact hc.le)
    rw [h] at ha; cases ha
  | some q =>
    simp only [Option.getD_some]
    obtain ⟨hq, hq1, hmin⟩ := firstFrom_some h
    simp only [decide_eq_true_eq] at hq
    have hq2 : 2 ≤ q := by
      by_contra hc
      have : q = 1 := by omega
      subst this; exact hp1 hq
    have hqn : q ≤ n + 1 := by have := firstFrom_lt h; omega
    refine ⟨hq2, hqn, ?_, Or.inl hq⟩
    have := hmin (q - 1) (by omega) (by omega)
    simp only [decide_eq_false_iff_not, not_le] at this
    exact this.le

end Q

/-! ### The chain -/

section Main

variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem chainSeq_spec {r : ℕ} {ε : ℚ} (hn : 2 ≤ Fintype.card V) (hε : 0 < ε) :
    let L := chainSeq G r ε
    let q := qOf (Fintype.card V) r ε
    L.head? = some univ ∧
    (∀ i (h : i + 1 < L.length), L[i + 1] = damp G r (welzlVOrder G) q L[i]) ∧
    (∀ i (h : i + 1 < L.length), L[i].Nonempty) ∧
    (∀ i (h : i < L.length), q ^ i * L[i].card ≤ Fintype.card V) ∧
    L.getLast? = some ∅ := by
  have hq := (qOf_spec (r := r) hn hε).1
  obtain ⟨h1, h2, h3, h4⟩ := dampSeq_spec (G := G) (r := r) (o := welzlVOrder G) hq
    (Fintype.card V + 1) univ (by simp)
  refine ⟨h1, h2, h3, fun i hi => ?_, ?_⟩
  · have := h4 i hi; rwa [card_univ] at this
  simp [chainSeq]

theorem chainSeq_length_ge {r : ℕ} {ε : ℚ} (hn : 2 ≤ Fintype.card V) :
    2 ≤ (chainSeq G r ε).length := by
  have hne : (univ : Finset V) ≠ ∅ := by
    rw [← nonempty_iff_ne_empty, univ_nonempty_iff]; exact Fintype.card_pos_iff.1 (by omega)
  simp [chainSeq, dampSeq, hne]

/-- The chain is decreasing, from `V` to `∅`. -/
theorem chainAlg_isDecreasingChain (r : ℕ) {ε : ℚ} (hε : 0 < ε) :
    Lax185574.ChainTheorem.IsDecreasingChain (chainAlg G r ε) := by
  unfold chainAlg
  split_ifs with hn
  · exact ⟨by simp, by simp, by simp, fun t ht => by
      have : t = 0 := by simp at ht; omega
      subst this; simp⟩
  push Not at hn
  obtain ⟨h1, -, -, -, hlast⟩ := chainSeq_spec (G := G) (r := r) hn hε
  have hlen := chainSeq_length_ge (G := G) (r := r) (ε := ε) hn
  set L := chainSeq G r ε
  have hL : (suffixUnions L).length = L.length := length_suffixUnions L
  refine ⟨by rw [← List.length_pos_iff, hL]; omega, ?_, ?_, fun t ht => ?_⟩
  · rw [List.head_eq_getElem, getElem_suffixUnions]
    refine eq_univ_of_forall fun x => mem_biUnion.2 ⟨0, mem_Ico.2 ⟨le_rfl, by omega⟩, ?_⟩
    rw [List.getD_eq_getElem _ _ (by omega)]
    have : L[0]'(by omega) = univ := by
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at h1
      exact Option.some.inj h1
    rw [this]; exact mem_univ x
  · rw [List.getLast_eq_getElem, getElem_suffixUnions]
    rw [hL]
    have hN : (Ico (L.length - 1) L.length) = {L.length - 1} := by
      ext j; simp only [mem_Ico, mem_singleton]; omega
    rw [hN, singleton_biUnion, List.getD_eq_getElem _ _ (by omega)]
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
    exact Option.some.inj hlast
  · rw [getElem_suffixUnions, getElem_suffixUnions]
    exact biUnion_subset_biUnion_of_subset_left _ (Ico_subset_Ico (by omega) le_rfl)

/-- The chain has at most `2 + 2r/ε` sets. -/
theorem chainAlg_length {r : ℕ} {ε : ℚ} (hε : 0 < ε) :
    ((chainAlg G r ε).length : ℚ) ≤ 2 * r / ε + 2 := by
  have hpos : 0 ≤ 2 * (r : ℚ) / ε := by positivity
  unfold chainAlg
  split_ifs with hn
  · simp only [List.length_cons, List.length_nil]; norm_num; exact hpos
  push Not at hn
  rw [length_suffixUnions]
  obtain ⟨-, -, h3, h4, -⟩ := chainSeq_spec (G := G) (r := r) hn hε
  obtain ⟨hq2, -, -, hq4⟩ := qOf_spec (r := r) hn hε
  have hlen := chainSeq_length_ge (G := G) (r := r) (ε := ε) hn
  obtain ⟨k, hkL⟩ : ∃ k, (chainSeq G r ε).length = k + 2 :=
    ⟨(chainSeq G r ε).length - 2, by omega⟩
  -- `q^k ≤ n` for the last nonempty set
  have hqk : qOf (Fintype.card V) r ε ^ k ≤ Fintype.card V := by
    have hne := h3 k (by omega)
    have := h4 k (by omega)
    have : 1 ≤ ((chainSeq G r ε)[k]'(by omega)).card := card_pos.2 hne
    nlinarith
  set n := Fintype.card V
  set q := qOf n r ε
  have hk : (k : ℚ) ≤ 2 * r / ε := by
    rcases hq4 with h | h
    · set a := ε.num.natAbs
      set b := ε.den
      have hpow : n ^ (a * k) ≤ n ^ (2 * r * b) := by
        calc n ^ (a * k) = (n ^ a) ^ k := by ring
          _ ≤ (q ^ (2 * r * b)) ^ k := Nat.pow_le_pow_left h k
          _ = (q ^ k) ^ (2 * r * b) := by ring
          _ ≤ n ^ (2 * r * b) := Nat.pow_le_pow_left hqk _
      have hak : a * k ≤ 2 * r * b := (Nat.pow_le_pow_iff_right (by omega)).1 hpow
      have ha : (a : ℚ) = ε.num := by
        have := Rat.num_pos.2 hε
        simp only [a, Nat.cast_natAbs]; push_cast; exact abs_of_pos (by exact_mod_cast this)
      have hεab : ε = (a : ℚ) / b := by rw [ha]; exact (Rat.num_div_den ε).symm
      have hapos : (0 : ℚ) < a := by rw [ha]; exact_mod_cast Rat.num_pos.2 hε
      have hbpos : (0 : ℚ) < b := by exact_mod_cast ε.den_pos
      rw [hεab, div_div_eq_mul_div, le_div_iff₀ hapos]
      have : ((a * k : ℕ) : ℚ) ≤ ((2 * r * b : ℕ) : ℚ) := by exact_mod_cast hak
      push_cast at this; linarith
    · have : k = 0 := by
        by_contra hk0
        have : q ≤ q ^ k := Nat.le_self_pow hk0 q
        omega
      rw [this]; simpa using hpos
  rw [hkL]; push_cast; linarith

/-- The packing bound used for the chain: the smaller of `n` and
`4γ₁(log₂ n + 1)`. -/
theorem isPackingBound_min :
    IsPackingBound G (min (Fintype.card V)
      (4 * growth (fun B => tpRel G B 0) * (Nat.log 2 (Fintype.card V) + 1))) := by
  rcases min_choice (Fintype.card V)
      (4 * growth (fun B => tpRel G B 0) * (Nat.log 2 (Fintype.card V) + 1)) with h | h <;>
    rw [h]
  · exact isPackingBound_card
  · exact isPackingBound_of_growth fun Y hY => numCls_le_growth_mul (fun B => tpRel G B 0) hY

/-- **The width of the chain, for one graph.** Every radius-`r` ball of the
`B_{t+1}`-flip metric meets at most `γ₁ · m · (200 (q+1)(α+1)K²)^r`
atomic types over `B_t`. -/
theorem chainAlg_ball {r : ℕ} (hr : 1 ≤ r) {ε : ℚ} (hε : 0 < ε) (hn : 2 ≤ Fintype.card V)
    (t : ℕ) (ht : t + 1 < (chainAlg G r ε).length) (u : V) :
    Lax185574.Partitions.partCount
        (Lax185574.Partitions.atomicTypes G ((chainAlg G r ε)[t] : Set V))
        (Lax185574.Flips.flipBall G
          (Lax185574.Partitions.atomicTypes G ((chainAlg G r ε)[t + 1] : Set V)) r u) ≤
      growth (fun B => tpRel G B 0) * (chainAlg G r ε).length *
        (200 * (qOf (Fintype.card V) r ε + 1) * (alternation G (welzlOrder G) + 1) *
          (max (growth (fun B => tpRel G B r)) (max (min (Fintype.card V)
            (4 * growth (fun B => tpRel G B 0) * (Nat.log 2 (Fintype.card V) + 1))) 1)) ^ 2) ^ r := by
  classical
  have hn' : ¬ Fintype.card V ≤ 1 := by omega
  obtain ⟨-, h2, h3, -, hlast⟩ := chainSeq_spec (G := G) (r := r) hn hε
  have hlen := chainSeq_length_ge (G := G) (r := r) (ε := ε) hn
  have hq2 := (qOf_spec (r := r) hn hε).1
  set γ1 := growth (fun B => tpRel G B 0)
  set γr := growth (fun B => tpRel G B r)
  set β := min (Fintype.card V) (4 * γ1 * (Nat.log 2 (Fintype.card V) + 1))
  set α := alternation G (welzlOrder G)
  set q := qOf (Fintype.card V) r ε
  set M := (200 * (q + 1) * (α + 1) * (max γr (max β 1)) ^ 2) ^ r
  set L := chainSeq G r ε with hLdef
  set N := L.length
  have hB : chainAlg G r ε = suffixUnions L := by simp only [chainAlg, if_neg hn', L]
  have hBlen : (chainAlg G r ε).length = N := by rw [hB, length_suffixUnions]
  have ht' : t + 1 < N := hBlen ▸ ht
  have hBt : ∀ s (hs : s < (chainAlg G r ε).length),
      (chainAlg G r ε)[s] = (Ico s N).biUnion fun j => L.getD j ∅ := by
    intro s hs
    have : (chainAlg G r ε)[s] = (suffixUnions L)[s]'(by rw [length_suffixUnions]; omega) := by
      simp only [hB]
    rw [this, getElem_suffixUnions]
  -- the last set is empty, so `B_t` is the union of `L_j` for `t ≤ j < N - 1`
  have hlastE : L.getD (N - 1) ∅ = ∅ := by
    rw [List.getD_eq_getElem _ _ (by omega)]
    rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (by omega)] at hlast
    exact Option.some.inj hlast
  have hBt' : (chainAlg G r ε)[t] = (Ico t (N - 1)).biUnion fun j => L.getD j ∅ := by
    rw [hBt t (by omega)]
    ext x; simp only [mem_biUnion, mem_Ico]
    constructor
    · rintro ⟨j, ⟨h1, h2⟩, hx⟩
      refine ⟨j, ⟨h1, ?_⟩, hx⟩
      by_contra hj
      have : j = N - 1 := by omega
      rw [this, hlastE] at hx; simp at hx
    · rintro ⟨j, ⟨h1, h2⟩, hx⟩; exact ⟨j, ⟨h1, by omega⟩, hx⟩
  -- the flip ball as a finite set
  set X := Lax185574.Flips.flipBall G
    (Lax185574.Partitions.atomicTypes G ((chainAlg G r ε)[t + 1] : Set V)) r u
  set Xf := univ.filter fun v => v ∈ X
  have hXf : (Xf : Set V) = X := by ext; simp [Xf]
  -- one damping step per index
  have hstep : ∀ j ∈ Ico t (N - 1), numCls (tpRel G (L.getD j ∅) 0) Xf ≤ M := by
    intro j hj
    rw [mem_Ico] at hj
    have hjN : j + 1 < N := by omega
    rw [List.getD_eq_getElem _ _ (by omega)]
    have hA : (L[j]'(by omega)).Nonempty := h3 j hjN
    obtain ⟨H, hflip, hball⟩ := damp_spec (G := G) hr (o := welzlVOrder G) (q := q)
      (by omega) (γ := γr) (β := β) (α := α)
      (fun B hB => numCls_le_growth_mul (fun B => tpRel G B r) hB) (growth_le_card _)
      isPackingBound_min (min_le_left _ _)
      (isAltBound_listOrder G _ welzlOrder_nodup mem_welzlOrder) hA
    rw [← h2 j hjN] at hflip hball
    -- `L_{j+1} ⊆ B_{t+1}`
    have hsub : (L[j + 1] : Set V) ⊆ ((chainAlg G r ε)[t + 1] : Set V) := by
      intro x hx
      rw [hBt (t + 1) ht]
      exact mem_biUnion.2 ⟨j + 1, mem_Ico.2 ⟨by omega, hjN⟩,
        by rw [List.getD_eq_getElem _ _ hjN]; exact hx⟩
    have hflip' : Lax185574.Flips.IsFlip G
        (Lax185574.Partitions.atomicTypes G ((chainAlg G r ε)[t + 1] : Set V)) H :=
      Lax185574Proofs.FlipBasics.isFlip_mono
        (Lax185574Proofs.FlipBasics.atomicTypes_anti G hsub) hflip
    have hXball : Xf ⊆ ballF H r u := by
      intro v hv
      have : v ∈ X := (mem_filter.1 hv).2
      exact mem_filter.2 ⟨mem_univ _, this H hflip'⟩
    calc numCls (tpRel G L[j] 0) Xf ≤ numCls (tpRel G (L[j] ∪ L[j + 1]) 0) Xf :=
          numCls_le_of_le (tpRel_isEquiv _ 0) (tpRel_isEquiv _ 0)
            fun x _ y _ h => tpRel_anti subset_union_left 0 h
      _ ≤ numCls (tpRel G (L[j] ∪ L[j + 1]) 0) (ballF H r u) := numCls_mono _ hXball
      _ ≤ M := hball u
  have hγ1 : 1 ≤ γ1 := by
    obtain ⟨a⟩ : Nonempty V := Fintype.card_pos_iff.1 (by omega)
    have h := numCls_le_growth_mul (fun B => tpRel G B 0) (singleton_nonempty a)
    have : 1 ≤ numCls (tpRel G {a} 0) univ := card_pos.2 ⟨_, mem_image_of_mem _ (mem_univ a)⟩
    simp at h; omega
  have hpc : Lax185574.Partitions.partCount
      (Lax185574.Partitions.atomicTypes G ((chainAlg G r ε)[t] : Set V)) X =
      numCls (tpRel G (chainAlg G r ε)[t] 0) Xf := by
    rw [← hXf]; exact partCount_eq_numCls _ _ (fun x y => atomicTypes_iff_tpRel _ x y) Xf
  rw [hpc, hBt']
  have hI : (Ico t (N - 1)).Nonempty := ⟨t, mem_Ico.2 ⟨le_rfl, by omega⟩⟩
  calc numCls (tpRel G ((Ico t (N - 1)).biUnion fun j => L.getD j ∅) 0) Xf
      ≤ γ1 * ∑ j ∈ Ico t (N - 1), numCls (tpRel G (L.getD j ∅) 0) Xf :=
        numCls_biUnion_le (fun R hR => numCls_le_growth_mul (fun B => tpRel G B 0) hR) hγ1
          _ hI _ Xf
    _ ≤ γ1 * ∑ j ∈ Ico t (N - 1), M := Nat.mul_le_mul_left _ (sum_le_sum hstep)
    _ = γ1 * ((N - 1 - t) * M) := by simp
    _ ≤ γ1 * (N * M) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
    _ = γ1 * (chainAlg G r ε).length * M := by rw [hBlen]; ring

end Main

end Lax185574Proofs.Chain
