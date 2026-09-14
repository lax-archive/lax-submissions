/-
Atomisation of nondeterministic automata with output.

Every nfa with output is equivalent to one in which each transition reads at most one input letter
and writes at most one output letter.  This normal form is the basis of the constructions of Section
*Rational relations*: closure of rational relations under composition (Theorem
`thm:composition-rational-relations`) and their continuity (Theorem
`thm:continuity-rational-relations`).

The construction replaces a transition reading `a₁ ⋯ aₘ` and writing
`b₁ ⋯ bₙ` by a chain of `m + n` transitions, which first read the letters `aᵢ`
and then write the letters `bⱼ`.
-/
import Lax132576Proofs.Source.PartB.LabAut
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace Atomize

variable {A B Q : Type} (M : NFAO A B Q)

/-- The type of transitions of `M`. -/
abbrev Tr : Type := {t : Q × List A × List B × Q // t ∈ M.δ}

instance : Finite (Tr M) := M.δ_finite.to_subtype

/-- The source state of a transition. -/
def src (t : Tr M) : Q := t.val.1

/-- The input string of a transition. -/
def inp (t : Tr M) : List A := t.val.2.1

/-- The output string of a transition. -/
def outp (t : Tr M) : List B := t.val.2.2.1

/-- The target state of a transition. -/
def tgt (t : Tr M) : Q := t.val.2.2.2

/-- The number of atomic steps into which a transition is split. -/
def len (t : Tr M) : ℕ := (inp M t).length + (outp M t).length

lemma mem_delta (t : Tr M) : (src M t, inp M t, outp M t, tgt M t) ∈ M.δ := t.2

/-- The states of the atomised automaton: the old states, together with one
intermediate state for every step of every transition. -/
abbrev St : Type := Q ⊕ ((t : Tr M) × Fin (len M t))

/-- The input letter read by the `i`-th step of the transition `t`. -/
def stepIn (t : Tr M) (i : Fin (len M t)) : List A :=
  if h : (i : ℕ) < (inp M t).length then [(inp M t)[(i : ℕ)]] else []

/-- The output letter written by the `i`-th step of the transition `t`. -/
def stepOut (t : Tr M) (i : Fin (len M t)) : List B :=
  if h : (i : ℕ) < (inp M t).length then []
  else [(outp M t)[(i : ℕ) - (inp M t).length]'(by
    have hi := i.isLt
    simp only [len] at hi
    omega)]

/-- The state reached after the `i`-th step of the transition `t`. -/
def next (t : Tr M) (i : Fin (len M t)) : St M :=
  if h : (i : ℕ) + 1 < len M t then Sum.inr ⟨t, ⟨(i : ℕ) + 1, h⟩⟩ else Sum.inl (tgt M t)

/-- The state entered when the transition `t` is started. -/
def entry (t : Tr M) : St M :=
  if h : 0 < len M t then Sum.inr ⟨t, ⟨0, h⟩⟩ else Sum.inl (tgt M t)

/-- The transitions of the atomised automaton, presented as the range of a map
from a finite index type. -/
def gen : (Tr M) ⊕ ((t : Tr M) × Fin (len M t)) → (St M × List A × List B × St M)
  | Sum.inl t => (Sum.inl (src M t), [], [], entry M t)
  | Sum.inr ⟨t, i⟩ => (Sum.inr ⟨t, i⟩, stepIn M t i, stepOut M t i, next M t i)

/-- The atomised automaton. -/
def atom : NFAO A B (St M) where
  init := Sum.inl '' M.init
  final := Sum.inl '' M.final
  δ := Set.range (gen M)
  δ_finite := Set.finite_range _

@[simp] lemma mem_atom_delta (x : St M × List A × List B × St M) :
    x ∈ (atom M).δ ↔ ∃ y, gen M y = x := Iff.rfl

/-- Every transition of the atomised automaton reads at most one letter and
writes at most one letter. -/
lemma atom_atomic : ∀ t ∈ (atom M).δ, t.2.1.length ≤ 1 ∧ t.2.2.1.length ≤ 1 := by
  intro ⟨q, u, x, s⟩ h
  rw [mem_atom_delta] at h
  obtain ⟨y, hy⟩ := h
  cases y with
  | inl t =>
    simp [gen] at hy
    simp [hy]
  | inr p =>
    simp [gen] at hy
    rcases hy with ⟨rfl, rfl, rfl, rfl⟩
    simp [stepIn, stepOut]
    by_cases h : (p.2 : ℕ) < (inp M p.1).length <;> simp [h]

/-- The transitions leaving an intermediate state. -/
lemma atom_delta_inr {t : Tr M} {i : Fin (len M t)} {u : List A} {x : List B} {s : St M}
    (h : (Sum.inr ⟨t, i⟩, u, x, s) ∈ (atom M).δ) :
    u = stepIn M t i ∧ x = stepOut M t i ∧ s = next M t i := by
  rw [mem_atom_delta] at h
  obtain ⟨y, hy⟩ := h
  cases y with
  | inl t' => simp [gen] at hy
  | inr p => simp [gen] at hy; rcases hy with ⟨rfl, rfl, rfl, rfl⟩; trivial

/-- The transitions leaving an old state. -/
lemma atom_delta_inl {q : Q} {u : List A} {x : List B} {s : St M}
    (h : (Sum.inl q, u, x, s) ∈ (atom M).δ) :
    ∃ t : Tr M, src M t = q ∧ u = [] ∧ x = [] ∧ s = entry M t := by
  rw [mem_atom_delta] at h
  obtain ⟨y, hy⟩ := h
  cases y with
  | inl t =>
      simp only [gen, Prod.mk.injEq, Sum.inl.injEq] at hy
      exact ⟨t, hy.1, hy.2.1.symm, hy.2.2.1.symm, hy.2.2.2.symm⟩
  | inr p => simp [gen] at hy

/-- The input letters read by the `i`-th step and by the later steps of a
transition make up the input still to be read at step `i`. -/
lemma stepIn_append (t : Tr M) (i : Fin (len M t)) :
    stepIn M t i ++ (inp M t).drop ((i : ℕ) + 1) = (inp M t).drop (i : ℕ) := by
  unfold stepIn
  split_ifs with h
  · conv_rhs => rw [List.drop_eq_getElem_cons h]
    simp
  · push_neg at h
    rw [List.drop_eq_nil_iff.mpr h,
      List.drop_eq_nil_iff.mpr (by omega : (inp M t).length ≤ (i : ℕ) + 1)]
    simp

/-- The output analogue of `stepIn_append`. -/
lemma stepOut_append (t : Tr M) (i : Fin (len M t)) :
    stepOut M t i ++ (outp M t).drop ((i : ℕ) + 1 - (inp M t).length)
      = (outp M t).drop ((i : ℕ) - (inp M t).length) := by
  have hi := i.isLt
  simp only [len] at hi
  unfold stepOut
  split_ifs with h
  · have h1 : (i : ℕ) + 1 - (inp M t).length = 0 := by omega
    have h2 : (i : ℕ) - (inp M t).length = 0 := by omega
    rw [h1, h2]; simp
  · push_neg at h
    have h1 : (i : ℕ) + 1 - (inp M t).length = ((i : ℕ) - (inp M t).length) + 1 := by omega
    rw [h1]
    conv_rhs =>
      rw [List.drop_eq_getElem_cons
        (by omega : (i : ℕ) - (inp M t).length < (outp M t).length)]
    simp

/-! ### From `M` to its atomisation -/

lemma chain_aux (t : Tr M) (j : ℕ) : ∀ i : Fin (len M t), len M t - (i : ℕ) ≤ j →
    (atom M).relFrom (Sum.inr ⟨t, i⟩) ((inp M t).drop (i : ℕ))
      ((outp M t).drop ((i : ℕ) - (inp M t).length)) (Sum.inl (tgt M t)) := by
  intro i hi
  let L := len M t
  have hi_lt : (i : ℕ) < L := i.isLt
  -- We prove by strong induction on n = L - k that from any state Sum.inr ⟨t, k⟩ with
  -- L - k ≤ n, we can reach Sum.inl (tgt M t)
  have hsuff : ∀ n : ℕ, ∀ k : Fin L, L - (k : ℕ) = n →
      (atom M).relFrom (Sum.inr ⟨t, k⟩) ((inp M t).drop (k : ℕ))
        ((outp M t).drop ((k : ℕ) - (inp M t).length)) (Sum.inl (tgt M t)) := by
    intro n
    induction n with
    | zero => 
      intro k hk
      -- If L - k = 0 and k < L, contradiction
      omega
    | succ m ih => 
      intro k hk
      -- L - k = m + 1, so k.val = L - m - 1, and k.val + 1 = L - m
      have hk_val : (k : ℕ) + 1 = L - m := by omega
      have hk_lt : (k : ℕ) + 1 ≤ L := by omega
      -- Check if k is the last step
      by_cases hlast : (k : ℕ) + 1 = L
      · -- k is the last intermediate state, next state is the target
        -- The transition is in delta
        have hmem : (Sum.inr ⟨t, k⟩, stepIn M t k, stepOut M t k, next M t k) ∈ (atom M).δ := by
          simp [mem_atom_delta, gen]
        -- next M t k = Sum.inl (tgt M t)
        have hnext : next M t k = Sum.inl (tgt M t) := by
          simp only [next]
          split_ifs with h
          · omega
          · rfl
        -- Use relFrom_nil at target
        have hmem' : (Sum.inr ⟨t, k⟩, stepIn M t k, stepOut M t k, Sum.inl (tgt M t)) ∈ (atom M).δ := by
          rw [← hnext]; exact hmem
        have hreach := NFAO.relFrom_nil (atom M) (Sum.inl (tgt M t))
        -- Show input/output work out
        have hL : L = (inp M t).length + (outp M t).length := rfl
        have hk_eq : (k : ℕ) = (inp M t).length + (outp M t).length - 1 := by omega
        have hinp : stepIn M t k = (inp M t).drop (k : ℕ) := by
          simp [stepIn]
          by_cases hk_in : (k : ℕ) < (inp M t).length
          · -- k < inp.length, so outp.length = 0
            have houtp_zero : (outp M t).length = 0 := by omega
            simp [hk_in]
            -- k = inp.length - 1, so inp.drop k = [inp[k]]
            have hk_last : (k : ℕ) + 1 = (inp M t).length := by omega
            have hne : inp M t ≠ [] := by intro h; simp [h] at hk_last
            have hk_eq' : (k : ℕ) = (inp M t).length - 1 := by omega
            simp only [hk_eq']
            rw [List.drop_length_sub_one hne]
            congr 1
            have hget : ∀ (as : List A) (has : as ≠ []), as[as.length - 1]'(by
              have := List.length_pos_of_ne_nil has
              omega) = as.getLast has := by
              intro as has
              induction as with
              | nil => contradiction
              | cons a as ih =>
                cases as with
                | nil => simp [List.getLast]
                | cons b bs =>
                  simp only [List.length_cons, Nat.add_sub_cancel]
                  exact ih (by simp)
            exact hget _ hne
          · -- k ≥ inp.length, so drop k = []
            push_neg at hk_in
            simp [hk_in, List.drop_eq_nil_iff.mpr hk_in]
        have hout : stepOut M t k = (outp M t).drop ((k : ℕ) - (inp M t).length) := by
          simp [stepOut]
          by_cases hk_in : (k : ℕ) < (inp M t).length
          · -- k < inp.length means outp.length = 0
            have houtp_zero : (outp M t).length = 0 := by omega
            simp [hk_in, houtp_zero]
          · -- k ≥ inp.length
            push_neg at hk_in
            -- Need: [outp[k - inp.length]] = outp.drop (k - inp.length)
            -- k - inp.length = outp.length - 1
            have hk_sub : (k : ℕ) - (inp M t).length = (outp M t).length - 1 := by omega
            have hne : outp M t ≠ [] := by
              intro h
              simp [h] at hk_sub hk_eq hL
              omega
            have hget : ∀ (as : List B) (has : as ≠ []), as[as.length - 1]'(by
              have := List.length_pos_of_ne_nil has
              omega) = as.getLast has := by
              intro as has
              induction as with
              | nil => contradiction
              | cons a as ih =>
                cases as with
                | nil => simp [List.getLast]
                | cons b bs =>
                  simp only [List.length_cons, Nat.add_sub_cancel]
                  exact ih (by simp)
            simp only [hk_sub, hk_in, not_lt.mpr]
            simp
            rw [List.drop_length_sub_one hne]
            congr 1
            exact hget _ hne
        have hreach := NFAO.relFrom_nil (atom M) (Sum.inl (tgt M t))
        have := NFAO.relFrom_step hmem' hreach
        simp [hinp, hout] at this
        exact this
      · -- next state is another intermediate state
        have hk'_lt : (k : ℕ) + 1 < L := Nat.lt_of_le_of_ne hk_lt hlast
        let k' : Fin L := ⟨(k : ℕ) + 1, hk'_lt⟩
        have hk'_eq : L - (k' : ℕ) = m := by simp [k']; omega
        -- The transition is in delta
        have hmem : (Sum.inr ⟨t, k⟩, stepIn M t k, stepOut M t k, next M t k) ∈ (atom M).δ := by
          simp [mem_atom_delta, gen]
        -- next M t k = Sum.inr ⟨t, k'⟩
        have hnext : next M t k = Sum.inr ⟨t, k'⟩ := by
          simp only [next]
          split_ifs with h
          · rfl
          · omega
        -- Use IH for k'
        have hreach : (atom M).relFrom (Sum.inr ⟨t, k'⟩) ((inp M t).drop (k' : ℕ))
            ((outp M t).drop ((k' : ℕ) - (inp M t).length)) (Sum.inl (tgt M t)) := ih k' hk'_eq
        -- Show input/output combine correctly
        have hinp : stepIn M t k ++ (inp M t).drop (k' : ℕ) = (inp M t).drop (k : ℕ) := by
          simp [stepIn, k']
          by_cases hk_in : (k : ℕ) < (inp M t).length
          · simp [hk_in]
          · have hk'_out : (k' : ℕ) ≥ (inp M t).length := by simp [k']; omega
            simp [hk_in]
            omega
        have hout : stepOut M t k ++ (outp M t).drop ((k' : ℕ) - (inp M t).length) = 
                    (outp M t).drop ((k : ℕ) - (inp M t).length) := by
          simp [stepOut, k']
          by_cases hk_in : (k : ℕ) < (inp M t).length
          · -- k < inp length, so k - inp.length = 0
            simp [hk_in]
            have : (k : ℕ) - (inp M t).length = 0 := by omega
            simp [this]
          · -- k ≥ inp length
            simp [hk_in]
            -- Need: [outp[k - inp.length]] :: drop (k+1 - inp.length) outp = drop (k - inp.length) outp
            have h1 : (k : ℕ) + 1 - (inp M t).length = (k : ℕ) - (inp M t).length + 1 := by omega
            rw [h1]
            simp
        have hmem' : (Sum.inr ⟨t, k⟩, stepIn M t k, stepOut M t k, Sum.inr ⟨t, k'⟩) ∈ (atom M).δ := by
          rw [← hnext]; exact hmem
        obtain ⟨ts, hpath, hinput, houtput⟩ := NFAO.relFrom_step hmem' hreach
        exact ⟨ts, hpath, hinp ▸ hinput, hout ▸ houtput⟩
  exact hsuff (L - (i : ℕ)) i rfl

/-- The atomisation simulates a single transition of `M`. -/
lemma atom_of_transition (t : Tr M) :
    (atom M).relFrom (Sum.inl (src M t)) (inp M t) (outp M t) (Sum.inl (tgt M t)) := by
  have hmem : (Sum.inl (src M t), ([] : List A), ([] : List B), entry M t) ∈ (atom M).δ := by
    rw [mem_atom_delta]; exact ⟨Sum.inl t, rfl⟩
  have key : (atom M).relFrom (entry M t) (inp M t) (outp M t) (Sum.inl (tgt M t)) := by
    unfold entry
    split_ifs with h
    · simpa using chain_aux M t (len M t) ⟨0, h⟩ (by omega)
    · simp only [len, not_lt, Nat.le_zero] at h
      have h1 : inp M t = [] := List.eq_nil_of_length_eq_zero (by omega)
      have h2 : outp M t = [] := List.eq_nil_of_length_eq_zero (by omega)
      rw [h1, h2]
      exact NFAO.relFrom_nil _ _
  simpa using NFAO.relFrom_step hmem key

/-- The atomisation simulates `M`. -/
lemma atom_complete {q p : Q} {w : List A} {v : List B} (h : M.relFrom q w v p) :
    (atom M).relFrom (Sum.inl q) w v (Sum.inl p) := by
  refine NFAO.relFrom_induction (M := M)
    (motive := fun q w v => (atom M).relFrom (Sum.inl q) w v (Sum.inl p))
    (NFAO.relFrom_nil _ _) ?_ h
  intro q q' u x w v ht _ ih
  exact NFAO.relFrom_trans (atom_of_transition M ⟨(q, u, x, q'), ht⟩) ih

/-! ### From the atomisation back to `M` -/

/-- What remains to be done from a state of the atomisation: the state of `M` in
which the current transition ends, together with the input still to be read and
the output still to be written. -/
def expand : St M → Q × List A × List B
  | Sum.inl q => (q, [], [])
  | Sum.inr ⟨t, i⟩ =>
      (tgt M t, (inp M t).drop (i : ℕ), (outp M t).drop ((i : ℕ) - (inp M t).length))

/-- What remains to be done after the `i`-th step of a transition. -/
lemma expand_next (t : Tr M) (i : Fin (len M t)) :
    expand M (next M t i)
      = (tgt M t, (inp M t).drop ((i : ℕ) + 1),
          (outp M t).drop ((i : ℕ) + 1 - (inp M t).length)) := by
  have hi := i.isLt
  simp only [len] at hi
  unfold next
  split_ifs with h
  · rfl
  · simp only [len] at h
    have h1 : (inp M t).length ≤ (i : ℕ) + 1 := by omega
    have h2 : (outp M t).length ≤ (i : ℕ) + 1 - (inp M t).length := by omega
    simp [expand, List.drop_eq_nil_iff.mpr h1, List.drop_eq_nil_iff.mpr h2]

/-- What remains to be done when a transition is entered: the whole transition. -/
lemma expand_entry (t : Tr M) : expand M (entry M t) = (tgt M t, inp M t, outp M t) := by
  unfold entry
  split_ifs with h
  · simp [expand]
  · simp only [len, not_lt, Nat.le_zero] at h
    have h1 : inp M t = [] := List.eq_nil_of_length_eq_zero (by omega)
    have h2 : outp M t = [] := List.eq_nil_of_length_eq_zero (by omega)
    simp [expand, h1, h2]

lemma atom_sound_aux {p : Q} : ∀ {s : St M} {w : List A} {v : List B},
    (atom M).relFrom s w v (Sum.inl p) →
      ∃ w' v', w = (expand M s).2.1 ++ w' ∧ v = (expand M s).2.2 ++ v' ∧
        M.relFrom (expand M s).1 w' v' p := by
  intro s w v h
  refine NFAO.relFrom_induction (M := atom M)
    (motive := fun s w v => ∃ w' v', w = (expand M s).2.1 ++ w' ∧ v = (expand M s).2.2 ++ v' ∧
      M.relFrom (expand M s).1 w' v' p)
    ⟨[], [], by simp [expand], by simp [expand], NFAO.relFrom_nil _ _⟩ ?_ h
  rintro s s' u x w v ht _ ⟨w', v', hw, hv, hrel⟩
  match s with
  | Sum.inl q =>
      obtain ⟨t, hsrc, rfl, rfl, rfl⟩ := atom_delta_inl M ht
      rw [expand_entry] at hw hv hrel
      refine ⟨inp M t ++ w', outp M t ++ v', by simp [expand, hw], by simp [expand, hv], ?_⟩
      simp only [expand]
      exact NFAO.relFrom_step (M := M) (hsrc ▸ mem_delta M t) hrel
  | Sum.inr ⟨t, i⟩ =>
      obtain ⟨rfl, rfl, rfl⟩ := atom_delta_inr M ht
      rw [expand_next] at hw hv hrel
      refine ⟨w', v', ?_, ?_, hrel⟩
      · simp only [expand]
        rw [hw, ← List.append_assoc, stepIn_append]
      · simp only [expand]
        rw [hv, ← List.append_assoc, stepOut_append]

lemma atom_sound {q p : Q} {w : List A} {v : List B}
    (h : (atom M).relFrom (Sum.inl q) w v (Sum.inl p)) : M.relFrom q w v p := by
  obtain ⟨w', v', hw, hv, hrel⟩ := atom_sound_aux M h
  simp only [expand] at hw hv hrel
  simpa [hw, hv] using hrel

lemma atom_rel : (atom M).rel = M.rel := by
  funext w v
  simp only [eq_iff_iff, NFAO.rel_iff_relFrom]
  constructor
  · rintro ⟨s, hs, s', hs', hrel⟩
    obtain ⟨q, hq, rfl⟩ := hs
    obtain ⟨p, hp, rfl⟩ := hs'
    exact ⟨q, hq, p, hp, atom_sound M hrel⟩
  · rintro ⟨q, hq, p, hp, hrel⟩
    exact ⟨Sum.inl q, ⟨q, hq, rfl⟩, Sum.inl p, ⟨p, hp, rfl⟩, atom_complete M hrel⟩

end Atomize

/-- **Atomisation.**  Every rational relation is computed by an nfa with output
in which every transition reads at most one letter and writes at most one
letter. -/
theorem exists_atomic_nfao {A B : Type} {R : List A → List B → Prop} (hR : IsRationalRel R) :
    ∃ (Q : Type) (_ : Finite Q) (M : NFAO A B Q),
      (∀ t ∈ M.δ, t.2.1.length ≤ 1 ∧ t.2.2.1.length ≤ 1) ∧ ∀ w v, R w v ↔ M.rel w v := by
  obtain ⟨Q, hQ, M, hM⟩ := hR
  refine ⟨Atomize.St M, inferInstance, Atomize.atom M, Atomize.atom_atomic M, ?_⟩
  intro w v
  rw [hM w v, ← Atomize.atom_rel M]

end Lax132576Proofs.Transducers
