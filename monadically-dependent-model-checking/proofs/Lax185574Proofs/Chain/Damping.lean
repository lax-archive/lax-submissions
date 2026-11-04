import Lax185574Proofs.Chain.Predamping
import Lax185574Proofs.Chain.Welzl
import Lax185574Proofs.Chain.Flip

/-!
The Damping Theorem with explicit bounds (`thm:static-s-flip-explicit` of
the companion paper), for the partition selector of `(r+1)`-types.

The damping step `damp` returns `∅` when `|A| < 6(q+1)`. Otherwise it runs
the predamping procedure for `κ = 1, 2, …, n` and returns the first output
`S` with `q |S| ≤ |A|`, or `∅` if there is none. If `γ` bounds the growth
of the `(r+1)`-types, `β` the packing ratio and `α` the alternation of
the ordering, the search stops at some `κ ≤ max(γ, β, 1)`, and the flip
built from the output keeps every radius-`r` ball within
`(200 (q+1)(α+1) K²)^r` atomic types over `A ∪ S`, where
`K = max(γ, β, 1)`.
-/

set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain

open Finset

universe u

variable {V : Type u} [Fintype V] [DecidableEq V] [LinearOrder V]

/-! ### Vertex orderings from lists -/

section ListOrder

/-- The positions in a list without repetitions that contains every
vertex. -/
def listOrder (l : List V) (hl : l.Nodup) (hall : ∀ x, x ∈ l) : VOrder V where
  pos x := l.idxOf x
  inj x y h := (List.idxOf_inj (hall x)).1 h
  dense x i hi := by
    have hx : l.idxOf x < l.length := List.idxOf_lt_length_iff.2 (hall x)
    exact ⟨l[i], hl.idxOf_getElem i (by omega)⟩

theorem infix_of_idxOf : ∀ (l : List V), l.Nodup → ∀ a b, a ∈ l → b ∈ l →
    l.idxOf b = l.idxOf a + 1 → [a, b] <:+: l
  | [], _, a, _, ha, _, _ => by simp at ha
  | c :: m, hl, a, b, ha, hb, h => by
    rw [List.nodup_cons] at hl
    by_cases hac : a = c
    · subst hac
      rw [List.idxOf_cons_self] at h
      have hbc : b ≠ a := fun e => by rw [e, List.idxOf_cons_self] at h; omega
      rw [List.idxOf_cons_ne _ (Ne.symm hbc)] at h
      have hbm : b ∈ m := (List.mem_cons.1 hb).resolve_left hbc
      have h0 : m.idxOf b = 0 := by simpa using h
      cases m with
      | nil => simp at hbm
      | cons d m' =>
        have : d = b := by
          by_contra hdb
          rw [List.idxOf_cons_ne _ hdb] at h0; simp at h0
        subst this
        exact List.IsPrefix.isInfix (by simp)
    · have ham : a ∈ m := (List.mem_cons.1 ha).resolve_left hac
      have hbc : b ≠ c := fun e => by
        rw [e, List.idxOf_cons_self, List.idxOf_cons_ne _ (Ne.symm hac)] at h; omega
      have hbm : b ∈ m := (List.mem_cons.1 hb).resolve_left hbc
      rw [List.idxOf_cons_ne _ (Ne.symm hac), List.idxOf_cons_ne _ (Ne.symm hbc)] at h
      exact List.infix_cons (infix_of_idxOf m hl.2 a b ham hbm (by simpa using h))

theorem card_infix_le (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) :
    ∀ l : List V, (univ.filter fun a => ∃ b, [a, b] <:+: l ∧ x ∈ sdiff G a b).card ≤
      altCount G x l
  | [] => by simp [altCount]
  | [c] => by
    have : (univ.filter fun a => ∃ b, [a, b] <:+: [c] ∧ x ∈ sdiff G a b) = ∅ := by
      refine filter_false_of_mem fun a _ ⟨b, hb, _⟩ => ?_
      have := hb.length_le; simp at this
    rw [this]; simp
  | c :: d :: m => by
    have ih := card_infix_le G x (d :: m)
    have hsub : (univ.filter fun a => ∃ b, [a, b] <:+: c :: d :: m ∧ x ∈ sdiff G a b) ⊆
        (if x ∈ sdiff G c d then {c} else ∅) ∪
          (univ.filter fun a => ∃ b, [a, b] <:+: d :: m ∧ x ∈ sdiff G a b) := by
      intro a ha
      obtain ⟨b, hb, hx⟩ := (mem_filter.1 ha).2
      rw [List.infix_cons_iff] at hb
      rcases hb with hb | hb
      · rw [List.cons_prefix_cons] at hb
        obtain ⟨rfl, hb⟩ := hb
        rw [List.cons_prefix_cons] at hb
        obtain ⟨rfl, -⟩ := hb
        simp [hx]
      · exact mem_union_right _ (mem_filter.2 ⟨mem_univ _, b, hb, hx⟩)
    refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
    simp only [altCount]
    split_ifs <;> simp <;> omega

/-- The alternation of a list bounds that of its ordering. -/
theorem isAltBound_listOrder (G : SimpleGraph V) [DecidableRel G.Adj] (l : List V)
    (hl : l.Nodup) (hall : ∀ x, x ∈ l) :
    IsAltBound G (listOrder l hl hall) (alternation G l) := by
  intro x
  refine le_trans (card_le_card fun a ha => ?_) ((card_infix_le G x l).trans
    (le_sup (f := fun x => altCount G x l) (mem_univ x)))
  obtain ⟨b, hb, hx⟩ := (mem_filter.1 ha).2
  exact mem_filter.2 ⟨mem_univ _, b, infix_of_idxOf l hl a b (hall a) (hall b) hb, hx⟩

end ListOrder

/-! ### The damping step -/

section Damp

/-- The first `k ∈ [k₀, k₀ + f)` with `p k`. -/
def firstFrom (p : ℕ → Bool) : ℕ → ℕ → Option ℕ
  | _, 0 => none
  | k, f + 1 => if p k then some k else firstFrom p (k + 1) f

theorem firstFrom_some {p : ℕ → Bool} : ∀ {k f a : ℕ}, firstFrom p k f = some a →
    p a ∧ k ≤ a ∧ ∀ b, k ≤ b → b < a → p b = false
  | _, 0, _, h => by simp [firstFrom] at h
  | k, f + 1, a, h => by
    unfold firstFrom at h
    split_ifs at h with hk
    · cases h; exact ⟨hk, le_rfl, fun b h1 h2 => by omega⟩
    · obtain ⟨h1, h2, h3⟩ := firstFrom_some h
      refine ⟨h1, by omega, fun b hb1 hb2 => ?_⟩
      rcases eq_or_lt_of_le hb1 with rfl | hb1
      · simpa using hk
      · exact h3 b hb1 hb2

theorem firstFrom_isSome {p : ℕ → Bool} : ∀ {k f b : ℕ}, k ≤ b → b < k + f → p b →
    ∃ a, firstFrom p k f = some a
  | _, 0, _, h1, h2, _ => by omega
  | k, f + 1, b, h1, h2, hb => by
    unfold firstFrom
    split_ifs with hk
    · exact ⟨k, rfl⟩
    · have hkb : k ≠ b := fun e => hk (e ▸ hb)
      exact firstFrom_isSome (by omega) (by omega) hb

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The damping step for radius `r`, ordering `o` and parameter `q`. -/
def damp (r : ℕ) (o : VOrder V) (q : ℕ) (A : Finset V) : Finset V :=
  if A.card < 6 * (q + 1) then ∅ else
    match firstFrom (fun κ => decide (q * (predamp G (fun B => tpRel G B r) o A q κ).card ≤
        A.card)) 1 (Fintype.card V) with
    | some κ => predamp G (fun B => tpRel G B r) o A q κ
    | none => ∅

variable {G}

theorem isSelector_tp (r : ℕ) : IsSelector G (fun B => tpRel G B r) :=
  ⟨fun B => tpRel_isEquiv B r, fun h _ _ hxy => tpRel_anti h r hxy,
    fun _ _ _ h => tpRel_zero_of h⟩

/-- The damping step always shrinks by the factor `q`. -/
theorem damp_card (r : ℕ) (o : VOrder V) (q : ℕ) (A : Finset V) :
    q * (damp G r o q A).card ≤ A.card := by
  unfold damp
  split_ifs
  · simp
  · split
    · rename_i κ hκ
      simpa using (firstFrom_some hκ).1
    · simp

theorem damp_lt (r : ℕ) (o : VOrder V) {q : ℕ} (hq : 2 ≤ q) {A : Finset V} (hA : A.Nonempty) :
    (damp G r o q A).card < A.card := by
  have h1 := damp_card (G := G) r o q A
  have h2 := card_pos.2 hA
  nlinarith

/-- **Damping Theorem with explicit bounds.** -/
theorem damp_spec {r : ℕ} (hr : 1 ≤ r) {o : VOrder V} {q : ℕ} (hq : 1 ≤ q)
    {γ β α : ℕ} (hγ : ∀ B : Finset V, B.Nonempty → numCls (tpRel G B r) univ ≤ γ * B.card)
    (hγn : γ ≤ Fintype.card V) (hβ : IsPackingBound G β) (hβn : β ≤ Fintype.card V)
    (hα : IsAltBound G o α) {A : Finset V} (hA : A.Nonempty) :
    ∃ H : SimpleGraph V,
      Lax185574.Flips.IsFlip G (Lax185574.Partitions.atomicTypes G (damp G r o q A : Set V)) H ∧
      ∀ u, numCls (tpRel G (A ∪ damp G r o q A) 0) (ballF H r u) ≤
        (200 * (q + 1) * (α + 1) * (max γ (max β 1)) ^ 2) ^ r := by
  classical
  set K := max γ (max β 1)
  have hK1 : 1 ≤ K := le_max_of_le_right (le_max_right _ _)
  have hKn : K ≤ Fintype.card V := by
    obtain ⟨a, -⟩ := hA
    have : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 ⟨a⟩
    exact max_le hγn (max_le hβn this)
  have hselr := isSelector_tp (G := G) r
  unfold damp
  split_ifs with hsmall
  · -- small `A`: no damping is needed
    refine ⟨G, Lax185574Proofs.FlipBasics.isFlip_refl G _, fun u => ?_⟩
    rw [union_empty]
    calc numCls (tpRel G A 0) (ballF G r u) ≤ numCls (tpRel G A 0) univ :=
          numCls_mono _ (subset_univ _)
      _ ≤ numCls (tpRel G A r) univ :=
          numCls_le_of_le (tpRel_isEquiv A 0) (tpRel_isEquiv A r)
            fun x _ y _ h => tpRel_zero_of h
      _ ≤ γ * A.card := hγ A hA
      _ ≤ K * (6 * (q + 1)) := Nat.mul_le_mul (le_max_left _ _) (by omega)
      _ ≤ K ^ 2 * (200 * (q + 1) * (α + 1)) := by
          refine Nat.mul_le_mul (by nlinarith) ?_
          have : 1 ≤ α + 1 := by omega
          nlinarith
      _ = 200 * (q + 1) * (α + 1) * K ^ 2 := by ring
      _ ≤ (200 * (q + 1) * (α + 1) * K ^ 2) ^ r := by
          apply Nat.le_self_pow (by omega)
  · -- the search succeeds at `κ = K` at the latest
    have hp : q * (predamp G (fun B => tpRel G B r) o A q K).card ≤ A.card :=
      predamp_card hselr hK1 (fun B hB => (hγ B hB).trans
        (Nat.mul_le_mul_right _ (le_max_left _ _)))
        (hβ.mono (le_max_of_le_right (le_max_left _ _))) (by omega)
    obtain ⟨κ, hκ⟩ := firstFrom_isSome (p := fun κ => decide (q * (predamp G
        (fun B => tpRel G B r) o A q κ).card ≤ A.card)) (k := 1) (f := Fintype.card V)
      (b := K) hK1 (by omega) (by simpa using hp)
    rw [hκ]
    obtain ⟨-, hκ1, hκmin⟩ := firstFrom_some hκ
    have hκK : κ ≤ K := by
      by_contra h
      have := hκmin K hK1 (by omega)
      simp only [decide_eq_false_iff_not] at this
      exact this hp
    dsimp only
    set S := predamp G (fun B => tpRel G B r) o A q κ
    set B := A ∪ S
    set M2 := 5 * (3 * (q + 1)) * κ * κ
    set M3 := (4 * α + 3) * (2 * (3 * (q + 1)) * κ) + 2
    have hA2 : ∀ u, ∃ s ∈ S, numCls (tpRel G B r) (sdiff G u s) ≤ M2 := by
      intro u
      obtain ⟨s, hs, h⟩ := predamp_near (o := o) (A := A) (q := q) hselr hκ1 u
      exact ⟨s, hs, (ham_eq_numCls hselr B u s) ▸ h⟩
    have hA3 : ∀ u v, tpRel G S 0 u v → numCls (tpRel G B r) (sdiff G u v) ≤ M3 := by
      intro u v huv
      have := predamp_same_type (o := o) (A := A) (q := q) hselr hκ1 hα huv
      rw [ham_eq_numCls hselr] at this
      exact this
    obtain ⟨ρ, hρinv, hρ⟩ := exists_mismatch_asymmetric (G := G) hA2 hA3
    have hRQ : ∀ x y, tpRel G B r x y → tpRel G S 0 x y := fun x y h =>
      tpRel_anti subset_union_right 0 (tpRel_zero_of h)
    have hRp : IsRepSet (tpRel G B r) (reps (fun B => tpRel G B r) o B) :=
      ⟨fun x => exists_rep hselr B x, fun a ha b hb h => rep_unique hselr ha hb h⟩
    obtain ⟨σ, hσinv, hσsymm, hσ⟩ := exists_symmetric (tpRel_isEquiv S 0)
      (tpRel_isEquiv B r) hRQ hRp hρinv hρ
    refine ⟨flipOf G σ hσsymm, ?_, fun u => ?_⟩
    · rw [atomicTypes_eq_tpSetoid]; exact isFlip_flipOf hσsymm hσinv
    · have hflipB : Lax185574.Flips.IsFlip G (tpSetoid G B 0) (flipOf G σ hσsymm) :=
        Lax185574Proofs.FlipBasics.isFlip_mono
          (fun x y h => tpRel_anti subset_union_right 0 h) (isFlip_flipOf hσsymm hσinv)
      have hmis : ∀ x, numCls (tpRel G B r) (univ.filter ((flipOf G σ hσsymm).Adj x)) ≤
          3 * (M2 + M3) := fun x =>
        (numCls_mono _ (neighbors_flipOf_subset hσsymm x)).trans (hσ x)
      refine (numCls_ball_le hflipB hmis u).trans (Nat.pow_le_pow_left ?_ r)
      -- `3 (M₂ + M₃) + 1 ≤ 200 (q+1)(α+1) K²`
      have hκK2 : κ * κ ≤ K ^ 2 := by nlinarith
      have hκ' : κ ≤ K ^ 2 := by nlinarith
      have e1 : 3 * (M2 + M3) + 1 ≤ 45 * (q + 1) * (κ * κ) + 72 * (q + 1) * α * κ +
          54 * (q + 1) * κ + 7 := by
        simp only [M2, M3]; ring_nf; omega
      have h1 : 45 * (q + 1) * (κ * κ) ≤ 45 * (q + 1) * (α + 1) * K ^ 2 := by
        calc 45 * (q + 1) * (κ * κ) ≤ 45 * (q + 1) * K ^ 2 := Nat.mul_le_mul_left _ hκK2
          _ ≤ 45 * (q + 1) * (α + 1) * K ^ 2 := by
            rw [Nat.mul_assoc (45 * (q + 1)) (α + 1)]
            exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
      have h2 : 72 * (q + 1) * α * κ ≤ 72 * (q + 1) * (α + 1) * K ^ 2 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) hκ'
      have h3 : 54 * (q + 1) * κ ≤ 54 * (q + 1) * (α + 1) * K ^ 2 := by
        calc 54 * (q + 1) * κ ≤ 54 * (q + 1) * K ^ 2 := Nat.mul_le_mul_left _ hκ'
          _ ≤ 54 * (q + 1) * (α + 1) * K ^ 2 := by
            rw [Nat.mul_assoc (54 * (q + 1)) (α + 1)]
            exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
      have h4 : 7 ≤ 29 * (q + 1) * (α + 1) * K ^ 2 := by
        have : 1 ≤ (q + 1) * (α + 1) * K ^ 2 :=
          Nat.one_le_iff_ne_zero.2 (by positivity)
        nlinarith
      have : 200 * (q + 1) * (α + 1) * K ^ 2 = 45 * (q + 1) * (α + 1) * K ^ 2 +
          72 * (q + 1) * (α + 1) * K ^ 2 + 54 * (q + 1) * (α + 1) * K ^ 2 +
          29 * (q + 1) * (α + 1) * K ^ 2 := by ring
      omega

end Damp

end Lax185574Proofs.Chain
