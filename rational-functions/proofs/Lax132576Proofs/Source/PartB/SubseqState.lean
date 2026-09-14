/-
The Myhill-Nerode state of the transducer computing the non-branching part
(the second half of the proof of Theorem `thm:subsequential-functions`).

As in the proof of Theorem `thm:sequential-function-independent`, the state of the transducer after
reading `w` is the tuple of the left quotients at `w` of finitely many regular languages: the
domain, the languages of inputs whose output has a prescribed short suffix, and the languages of
inputs whose output has a prescribed length modulo a fixed modulus.  Continuity makes these
languages regular, so the state takes finitely many values.

The main results of this file say that the state determines the data used by the
transducer: the *branching part* (the piece of the output of a short extension
that comes after the non-branching part, `key_drop`), the increment of the
non-branching part caused by one more input letter (`incr_congr`) and the
end-of-input output (`endOut_congr`).
-/
import Lax132576Proofs.Source.PartB.SubseqAlpha
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace Subseq

variable {A B : Type} (D : Data A B)

/-! ## The languages used by the state -/

/-- The modulus used to compare the lengths of the outputs. -/
def Mod : ℕ := 2 * M0 D + 1

lemma Mod_pos : 0 < Mod D := by simp [Mod]

/-- The language of inputs whose output is defined and has `u` as a suffix. -/
def SufL (u : List B) : Language A := {w | ∃ x, D.f w = some x ∧ u <:+ x}

/-- The language of inputs whose output is defined and has length congruent to
`r` modulo `Mod D`. -/
def ModL (r : ℕ) : Language A := {w | ∃ x, D.f w = some x ∧ x.length % Mod D = r}

lemma sufL_isRegular [Finite A] [Finite B] (u : List B) : Language.IsRegular (SufL D u) := by
  have h := D.cont (suffixLang u) (suffixLang_isRegular u)
  convert h using 1

lemma modL_isRegular [Finite A] [Finite B] (r : ℕ) :
    Language.IsRegular (ModL D r) := by
  have h := D.cont (lengthModLang (Mod D) r)
    (lengthModLang_isRegular (Mod D) r (Mod_pos D))
  convert h using 1

/-! ## The state -/

/-- The state of the transducer after reading `w`. -/
noncomputable def state (w : List A) :
    Language A × ({u : List B // u.length ≤ M0 D} → Language A) × (Fin (Mod D) → Language A) :=
  ((Dom D.f).leftQuotient w,
    fun u => (SufL D u.val).leftQuotient w,
    fun r => (ModL D r.val).leftQuotient w)

lemma state_range_finite [Finite A] [Finite B] : (Set.range (state D)).Finite := by
  classical
  haveI : Finite {u : List B // u.length ≤ M0 D} := (List.finite_length_le B (M0 D)).to_subtype
  have h0 : (Set.range (Dom D.f).leftQuotient).Finite :=
    (dom_isRegular D.cont).finite_range_leftQuotient
  have h1 : ∀ u : {u : List B // u.length ≤ M0 D},
      (Set.range (SufL D u.val).leftQuotient).Finite :=
    fun u => (sufL_isRegular D u.val).finite_range_leftQuotient
  have h2 : ∀ r : Fin (Mod D), (Set.range (ModL D r.val).leftQuotient).Finite :=
    fun r => (modL_isRegular D r.val).finite_range_leftQuotient
  refine Set.Finite.subset
    (Set.Finite.prod h0 (Set.Finite.prod
      (Set.Finite.pi (t := fun u : {u : List B // u.length ≤ M0 D} =>
        Set.range (SufL D u.val).leftQuotient) h1)
      (Set.Finite.pi (t := fun r : Fin (Mod D) => Set.range (ModL D r.val).leftQuotient) h2)))
    ?_
  rintro s ⟨w, rfl⟩
  exact ⟨⟨w, rfl⟩, fun u _ => ⟨w, rfl⟩, fun r _ => ⟨w, rfl⟩⟩

lemma state_append (w v : List A) :
    state D (w ++ v) =
      ((state D w).1.leftQuotient v,
        fun u => ((state D w).2.1 u).leftQuotient v,
        fun r => ((state D w).2.2 r).leftQuotient v) := by
  simp [state, Language.leftQuotient_append]

lemma state_append_congr {w w' : List A} (h : state D w = state D w') (v : List A) :
    state D (w ++ v) = state D (w' ++ v) := by
  rw [state_append, state_append, h]

/-! ## What the state determines -/

lemma dom_congr {w w' : List A} (h : state D w = state D w') (v : List A) :
    (D.f (w ++ v)).isSome ↔ (D.f (w' ++ v)).isSome := by
  have h1 : (Dom D.f).leftQuotient w = (Dom D.f).leftQuotient w' := congrArg Prod.fst h
  constructor
  · intro hv
    have hin : v ∈ (Dom D.f).leftQuotient w := by rw [Language.mem_leftQuotient]; exact hv
    rw [h1, Language.mem_leftQuotient] at hin
    exact hin
  · intro hv
    have hin : v ∈ (Dom D.f).leftQuotient w' := by rw [Language.mem_leftQuotient]; exact hv
    rw [← h1, Language.mem_leftQuotient] at hin
    exact hin

lemma pre_congr {w w' : List A} (h : state D w = state D w') :
    w ∈ Pre D.f ↔ w' ∈ Pre D.f := by
  constructor
  · rintro ⟨v, hv⟩; exact ⟨v, (dom_congr D h v).1 hv⟩
  · rintro ⟨v, hv⟩; exact ⟨v, (dom_congr D h v).2 hv⟩

lemma suffix_congr {w w' : List A} (h : state D w = state D w') (v : List A) {u : List B}
    (hu : u.length ≤ M0 D) {x x' : List B} (hx : D.f (w ++ v) = some x)
    (hx' : D.f (w' ++ v) = some x') : u <:+ x ↔ u <:+ x' := by
  have h1 : (SufL D u).leftQuotient w = (SufL D u).leftQuotient w' :=
    congrFun (congrArg (fun s => s.2.1) h) ⟨u, hu⟩
  constructor
  · intro hsuf
    have hin : v ∈ (SufL D u).leftQuotient w := by
      rw [Language.mem_leftQuotient]; exact ⟨x, hx, hsuf⟩
    rw [h1, Language.mem_leftQuotient] at hin
    obtain ⟨y, hy, hsy⟩ := hin
    rw [hx'] at hy
    cases hy
    exact hsy
  · intro hsuf
    have hin : v ∈ (SufL D u).leftQuotient w' := by
      rw [Language.mem_leftQuotient]; exact ⟨x', hx', hsuf⟩
    rw [← h1, Language.mem_leftQuotient] at hin
    obtain ⟨y, hy, hsy⟩ := hin
    rw [hx] at hy
    cases hy
    exact hsy

lemma len_mod_congr {w w' : List A} (h : state D w = state D w') (v : List A)
    {x x' : List B} (hx : D.f (w ++ v) = some x) (hx' : D.f (w' ++ v) = some x') :
    x.length % Mod D = x'.length % Mod D := by
  set r : Fin (Mod D) := ⟨x.length % Mod D, Nat.mod_lt _ (Mod_pos D)⟩ with hr
  have h1 : (ModL D r.val).leftQuotient w = (ModL D r.val).leftQuotient w' :=
    congrFun (congrArg (fun s => s.2.2) h) r
  have hin : v ∈ (ModL D r.val).leftQuotient w := by
    rw [Language.mem_leftQuotient]; exact ⟨x, hx, rfl⟩
  rw [h1, Language.mem_leftQuotient] at hin
  obtain ⟨y, hy, hsy⟩ := hin
  rw [hx'] at hy
  cases hy
  exact hsy.symm

/-! ## The branching part is determined by the state -/

/-- One half of `key_drop`: the length of the branching part does not increase
when passing to a string with the same state. -/
lemma rho_le {w w' : List A} (h : state D w = state D w') {v : List A} (hv : v.length ≤ D.k + 1)
    {x x' : List B} (hx : D.f (w ++ v) = some x) (hx' : D.f (w' ++ v) = some x') :
    x.length - (alpha D w).length ≤ x'.length - (alpha D w').length := by
  obtain ⟨v₂, x₂, hv₂, hx₂, hlcp⟩ := alpha_achieved D hv hx
  set P := lcp2 x x₂ with hP
  set S := x.drop P.length with hS
  set S' := x₂.drop P.length with hS'
  have hPx : P <+: x := lcp2_prefix_left _ _
  have hPx₂ : P <+: x₂ := lcp2_prefix_right _ _
  have hSlen : S.length = x.length - (alpha D w).length := by
    simp [hS, hlcp]
  have hS'len : S'.length = x₂.length - (alpha D w).length := by
    simp [hS', hlcp]
  have hSM : S.length ≤ M0 D := by rw [hSlen]; exact delay_bound D hv hx
  have hS'M : S'.length ≤ M0 D := by rw [hS'len]; exact delay_bound D hv₂ hx₂
  -- the output of `v₂` at `w'`
  obtain ⟨x₂', hx₂'⟩ : ∃ y, D.f (w' ++ v₂) = some y := by
    have := (dom_congr D h v₂).1 (by rw [hx₂]; simp)
    exact Option.isSome_iff_exists.1 this
  -- transfer the two suffixes
  have hSx' : S <:+ x' := (suffix_congr D h v hSM hx hx').1 (by rw [hS]; exact List.drop_suffix _ _)
  have hS'x₂' : S' <:+ x₂' :=
    (suffix_congr D h v₂ hS'M hx₂ hx₂').1 (by rw [hS']; exact List.drop_suffix _ _)
  -- the lengths shift by the same amount
  have hd : (x'.length : ℤ) - x.length = (x₂'.length : ℤ) - x₂.length := by
    have hm1 : (Mod D : ℤ) ∣ (x'.length : ℤ) - x.length :=
      Nat.modEq_iff_dvd.1 (len_mod_congr D h v hx hx')
    have hm2 : (Mod D : ℤ) ∣ (x₂'.length : ℤ) - x₂.length :=
      Nat.modEq_iff_dvd.1 (len_mod_congr D h v₂ hx₂ hx₂')
    have hdvd : (Mod D : ℤ) ∣ ((x'.length : ℤ) - x.length) - ((x₂'.length : ℤ) - x₂.length) :=
      dvd_sub hm1 hm2
    have hbv : leftDist x x₂ ≤ D.K := D.bv w v v₂ x x₂ hv hv₂ hx hx₂
    have hbv' : leftDist x' x₂' ≤ D.K := D.bv w' v v₂ x' x₂' hv hv₂ hx' hx₂'
    have h1 : x.length - x₂.length ≤ D.K := length_sub_le_of_leftDist hbv
    have h2 : x₂.length - x.length ≤ D.K :=
      length_sub_le_of_leftDist (by rw [leftDist_comm]; exact hbv)
    have h3 : x'.length - x₂'.length ≤ D.K := length_sub_le_of_leftDist hbv'
    have h4 : x₂'.length - x'.length ≤ D.K :=
      length_sub_le_of_leftDist (by rw [leftDist_comm]; exact hbv')
    have habs : |((x'.length : ℤ) - x.length) - ((x₂'.length : ℤ) - x₂.length)| < (Mod D : ℤ) := by
      have hM : (Mod D : ℤ) = 2 * (2 * (D.K : ℤ)) + 1 := by
        unfold Mod M0; push_cast; ring
      rw [abs_lt, hM]
      omega
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    omega
  have hSx'le : S.length ≤ x'.length := hSx'.length_le
  have hS'x₂'le : S'.length ≤ x₂'.length := hS'x₂'.length_le
  have hlen : x'.length - S.length = x₂'.length - S'.length := by
    have hax : (alpha D w).length ≤ x.length := (alpha_prefix D hv hx).length_le
    have hax₂ : (alpha D w).length ≤ x₂.length := (alpha_prefix D hv₂ hx₂).length_le
    omega
  have hdiv : ∀ (c : B) (s : List B) (c' : B) (s' : List B), S = c :: s → S' = c' :: s' →
      c ≠ c' := by
    intro c s c' s' hc hc' hcc
    have hxs : x = P ++ c :: s := by
      have ht : x.take P.length ++ x.drop P.length = x := List.take_append_drop _ _
      rw [← List.prefix_iff_eq_take.1 hPx, ← hS, hc] at ht
      exact ht.symm
    have hx₂s : x₂ = P ++ c' :: s' := by
      have ht : x₂.take P.length ++ x₂.drop P.length = x₂ := List.take_append_drop _ _
      rw [← List.prefix_iff_eq_take.1 hPx₂, ← hS', hc'] at ht
      exact ht.symm
    have h1 : P ++ [c] <+: x := ⟨s, by rw [hxs]; simp⟩
    have h2 : P ++ [c] <+: x₂ := ⟨s', by rw [hx₂s, hcc]; simp⟩
    have := (prefix_lcp2 h1 h2).length_le
    simp only [List.length_append, List.length_singleton, ← hP] at this
    omega
  have hle := lcp2_length_le_of_diverge hSx' hS'x₂' hlen hdiv
  have hα' : (alpha D w').length ≤ (lcp2 x' x₂').length :=
    (prefix_lcp2 (alpha_prefix D hv hx') (alpha_prefix D hv₂ hx₂')).length_le
  omega

/-- **The branching part is determined by the state.**  If `w` and `w'` have the
same state, then for every short extension the part of the output that comes
after the non-branching part is the same. -/
lemma key_drop {w w' : List A} (h : state D w = state D w') {v : List A} (hv : v.length ≤ D.k + 1)
    {x x' : List B} (hx : D.f (w ++ v) = some x) (hx' : D.f (w' ++ v) = some x') :
    x.drop (alpha D w).length = x'.drop (alpha D w').length := by
  have h1 := rho_le D h hv hx hx'
  have h2 := rho_le D h.symm hv hx' hx
  have hax : (alpha D w).length ≤ x.length := (alpha_prefix D hv hx).length_le
  have hax' : (alpha D w').length ≤ x'.length := (alpha_prefix D hv hx').length_le
  have hSsuf : x.drop (alpha D w).length <:+ x := List.drop_suffix _ _
  have hSlen : (x.drop (alpha D w).length).length ≤ M0 D := by
    simpa using delay_bound D hv hx
  have hSx' : x.drop (alpha D w).length <:+ x' := (suffix_congr D h v hSlen hx hx').1 hSsuf
  have := List.suffix_iff_eq_drop.1 hSx'
  rw [this]
  congr 1
  simp only [List.length_drop]
  omega

/-! ## The increment of the non-branching part -/

/-- The increment of the non-branching part caused by reading one more letter:
the number of letters that have to be removed from `alpha D w`, and the string
that has to be appended afterwards. -/
noncomputable def incr (w : List A) (a : A) : ℕ × List B :=
  ((alpha D w).length - (lcp2 (alpha D w) (alpha D (w ++ [a]))).length,
    (alpha D (w ++ [a])).drop (lcp2 (alpha D w) (alpha D (w ++ [a]))).length)

/-- A short extension of `w ++ [a]`, whose output extends both non-branching
parts. -/
lemma exists_common {w : List A} {a : A} (hw : w ++ [a] ∈ Pre D.f) :
    ∃ (u : List A) (z : List B), u.length ≤ D.k ∧ D.f (w ++ [a] ++ u) = some z ∧
      alpha D w <+: z ∧ alpha D (w ++ [a]) <+: z := by
  obtain ⟨u, hu, hud⟩ := D.short (w ++ [a]) hw
  obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 hud
  refine ⟨u, z, hu, hz, ?_, alpha_prefix D (le_trans hu (Nat.le_succ _)) hz⟩
  have hz' : D.f (w ++ ([a] ++ u)) = some z := by rw [← List.append_assoc]; exact hz
  exact alpha_prefix D (by simpa using Nat.succ_le_succ hu) hz'

/-- The two non-branching parts are prefixes of a common string, hence
comparable. -/
lemma alpha_comparable {w : List A} {a : A} (hw : w ++ [a] ∈ Pre D.f) :
    alpha D w <+: alpha D (w ++ [a]) ∨ alpha D (w ++ [a]) <+: alpha D w := by
  obtain ⟨u, z, _, _, h1, h2⟩ := exists_common D hw
  exact prefix_or_prefix_of_prefix h1 h2

/-- The non-branching part after reading one more letter is obtained from the
previous one by removing `(incr D w a).1` letters and appending
`(incr D w a).2`. -/
lemma alpha_step (w : List A) (a : A) :
    alpha D (w ++ [a]) =
      (alpha D w).take ((alpha D w).length - (incr D w a).1) ++ (incr D w a).2 := by
  set L := lcp2 (alpha D w) (alpha D (w ++ [a])) with hL
  have hLw : L <+: alpha D w := lcp2_prefix_left _ _
  have hLwa : L <+: alpha D (w ++ [a]) := lcp2_prefix_right _ _
  have hle : L.length ≤ (alpha D w).length := hLw.length_le
  have h1 : (alpha D w).length - (incr D w a).1 = L.length := by
    simp only [incr, ← hL]
    omega
  rw [h1]
  have h2 : (alpha D w).take L.length = L := (List.prefix_iff_eq_take.1 hLw).symm
  rw [h2]
  have h3 : (alpha D (w ++ [a])).take L.length = L := (List.prefix_iff_eq_take.1 hLwa).symm
  show alpha D (w ++ [a]) = L ++ (alpha D (w ++ [a])).drop L.length
  conv_lhs => rw [← List.take_append_drop L.length (alpha D (w ++ [a]))]
  rw [h3]

lemma incr_fst_le_length (w : List A) (a : A) :
    (incr D w a).1 ≤ (alpha D w).length := by
  simp [incr]

/-- A closed formula for the increment in terms of the output of a short
extension. -/
lemma incr_eq {w : List A} {a : A} {u : List A} {z : List B} (hu : u.length ≤ D.k)
    (hz : D.f (w ++ [a] ++ u) = some z) :
    incr D w a = ((alpha D w).length - (alpha D (w ++ [a])).length,
      (z.drop (alpha D w).length).take ((alpha D (w ++ [a])).length - (alpha D w).length)) := by
  have hzwa : alpha D (w ++ [a]) <+: z := alpha_prefix D (le_trans hu (Nat.le_succ _)) hz
  have hzw : alpha D w <+: z := by
    have hz' : D.f (w ++ ([a] ++ u)) = some z := by rw [← List.append_assoc]; exact hz
    exact alpha_prefix D (by simpa using Nat.succ_le_succ hu) hz'
  rcases prefix_or_prefix_of_prefix hzw hzwa with hpre | hpre
  · have hLeq : lcp2 (alpha D w) (alpha D (w ++ [a])) = alpha D w :=
      lcp2_eq_left_of_prefix hpre
    have hlen : (alpha D w).length ≤ (alpha D (w ++ [a])).length := hpre.length_le
    obtain ⟨t, ht⟩ := hzwa
    have hdz : z.drop (alpha D w).length =
        (alpha D (w ++ [a])).drop (alpha D w).length ++ t := by
      rw [← ht, List.drop_append_of_le_length hlen]
    simp only [incr, hLeq, Prod.mk.injEq]
    refine ⟨by omega, ?_⟩
    rw [hdz, List.take_left']
    simp only [List.length_drop]
  · have hLeq : lcp2 (alpha D w) (alpha D (w ++ [a])) = alpha D (w ++ [a]) := by
      rw [lcp2_comm]; exact lcp2_eq_left_of_prefix hpre
    have hlen : (alpha D (w ++ [a])).length ≤ (alpha D w).length := hpre.length_le
    simp only [incr, hLeq, Prod.mk.injEq]
    refine ⟨trivial, ?_⟩
    rw [show (alpha D (w ++ [a])).length - (alpha D w).length = 0 by omega]
    simp

/-- Both components of the increment are bounded. -/
lemma incr_le {w : List A} {a : A} (hw : w ++ [a] ∈ Pre D.f) :
    (incr D w a).1 ≤ M0 D ∧ (incr D w a).2.length ≤ M0 D := by
  obtain ⟨u, z, hu, hz, hzw, hzwa⟩ := exists_common D hw
  have hd1 : z.length - (alpha D w).length ≤ M0 D := by
    have hz' : D.f (w ++ ([a] ++ u)) = some z := by rw [← List.append_assoc]; exact hz
    exact delay_bound D (by simpa using Nat.succ_le_succ hu) hz'
  have hd2 : z.length - (alpha D (w ++ [a])).length ≤ M0 D :=
    delay_bound D (le_trans hu (Nat.le_succ _)) hz
  have h1 : (alpha D w).length ≤ z.length := hzw.length_le
  have h2 : (alpha D (w ++ [a])).length ≤ z.length := hzwa.length_le
  rw [incr_eq D hu hz]
  constructor
  · simp only
    omega
  · simp only [List.length_take, List.length_drop]
    omega

/-- **The increment is determined by the state.** -/
lemma incr_congr {w w' : List A} (h : state D w = state D w') {a : A}
    (hw : w ++ [a] ∈ Pre D.f) : incr D w a = incr D w' a := by
  obtain ⟨u, z, hu, hz, hzw, hzwa⟩ := exists_common D hw
  have hz' : D.f (w ++ ([a] ++ u)) = some z := by rw [← List.append_assoc]; exact hz
  have hsa : state D (w ++ [a]) = state D (w' ++ [a]) := state_append_congr D h [a]
  obtain ⟨y, hy⟩ : ∃ y, D.f (w' ++ [a] ++ u) = some y := by
    have hdom := (dom_congr D hsa u).1 (by rw [hz]; simp)
    exact Option.isSome_iff_exists.1 hdom
  have hy' : D.f (w' ++ ([a] ++ u)) = some y := by rw [← List.append_assoc]; exact hy
  have hshort : ([a] ++ u).length ≤ D.k + 1 := by simpa using Nat.succ_le_succ hu
  have hk1 : z.drop (alpha D w).length = y.drop (alpha D w').length :=
    key_drop D h hshort hz' hy'
  have hk2 : z.drop (alpha D (w ++ [a])).length = y.drop (alpha D (w' ++ [a])).length :=
    key_drop D hsa (le_trans hu (Nat.le_succ _)) hz hy
  have hyw : alpha D w' <+: y := alpha_prefix D hshort hy'
  have hywa : alpha D (w' ++ [a]) <+: y := alpha_prefix D (le_trans hu (Nat.le_succ _)) hy
  have e1 : z.length - (alpha D w).length = y.length - (alpha D w').length := by
    have := congrArg List.length hk1
    simpa using this
  have e2 : z.length - (alpha D (w ++ [a])).length
      = y.length - (alpha D (w' ++ [a])).length := by
    have := congrArg List.length hk2
    simpa using this
  have l1 : (alpha D w).length ≤ z.length := hzw.length_le
  have l2 : (alpha D (w ++ [a])).length ≤ z.length := hzwa.length_le
  have l3 : (alpha D w').length ≤ y.length := hyw.length_le
  have l4 : (alpha D (w' ++ [a])).length ≤ y.length := hywa.length_le
  rw [incr_eq D hu hz, incr_eq D hu hy, hk1]
  have hfst : (alpha D w).length - (alpha D (w ++ [a])).length
      = (alpha D w').length - (alpha D (w' ++ [a])).length := by omega
  have hsnd : (alpha D (w ++ [a])).length - (alpha D w).length
      = (alpha D (w' ++ [a])).length - (alpha D w').length := by omega
  rw [hfst, hsnd]

/-! ## The end-of-input output -/

/-- The end-of-input output: the part of `f w` that comes after the
non-branching part. -/
noncomputable def endOut (w : List A) : Option (List B) :=
  (D.f w).map (fun x => x.drop (alpha D w).length)

lemma alpha_append_endOut {w : List A} {x : List B} (hx : D.f w = some x) :
    alpha D w ++ x.drop (alpha D w).length = x := by
  have hpre : alpha D w <+: x := alpha_prefix D (v := []) (by simp) (by simpa using hx)
  obtain ⟨t, ht⟩ := hpre
  rw [← ht]
  simp

lemma endOut_length {w : List A} {u : List B} (hu : endOut D w = some u) : u.length ≤ M0 D := by
  rw [endOut, Option.map_eq_some_iff] at hu
  obtain ⟨x, hx, rfl⟩ := hu
  have hx' : D.f (w ++ []) = some x := by simpa using hx
  simpa using delay_bound D (v := []) (by simp) hx'

/-- **The end-of-input output is determined by the state.** -/
lemma endOut_congr {w w' : List A} (h : state D w = state D w') : endOut D w = endOut D w' := by
  have hdom := dom_congr D h []
  simp only [List.append_nil] at hdom
  cases hx : D.f w with
  | none =>
    have : ¬ (D.f w').isSome := by
      intro hc
      have := hdom.2 hc
      rw [hx] at this
      simp at this
    cases hx' : D.f w' with
    | none => simp [endOut, hx, hx']
    | some y => rw [hx'] at this; simp at this
  | some x =>
    have hsome : (D.f w').isSome := hdom.1 (by rw [hx]; simp)
    obtain ⟨x', hx'⟩ := Option.isSome_iff_exists.1 hsome
    have hxa : D.f (w ++ []) = some x := by simpa using hx
    have hxa' : D.f (w' ++ []) = some x' := by simpa using hx'
    have := key_drop D h (v := []) (by simp) hxa hxa'
    simp [endOut, hx, hx', this]

end Subseq

end Lax132576Proofs.Transducers
