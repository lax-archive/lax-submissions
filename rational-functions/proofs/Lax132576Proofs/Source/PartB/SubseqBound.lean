/- The bound on the deletions in the non-branching part (Claim `claim:eliminating-negative-letters`
of the book).

Reading one more letter may *shorten* the non-branching part `alpha D w`; in the
book this is expressed by allowing the transducer to output negative letters,
i.e. elements of the free group.  The transducer can only produce genuine
output, so we have to know that the deletions are bounded: the letters that
`alpha D w` loses in the future are among its last `M` letters, for a constant
`M` depending only on `D`.

The proof is the pumping argument of the book.  The length of the non-branching
part changes by an amount `dl D w v` that depends only on the state of `w` and
on `v`; if a loop had a negative change, then iterating it would give a
non-branching part of negative length.  All loops therefore have a non-negative
change, and removing the loops from a run bounds the change from below by
`-M0 D` times the number of states.
-/
import Lax132576Proofs.Source.PartB.SubseqState
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace Subseq

variable {A B : Type} (D : Data A B)

/-- The change in the length of the non-branching part caused by extending the
input by `v`. -/
noncomputable def dl (w v : List A) : ℤ := ((alpha D (w ++ v)).length : ℤ) - (alpha D w).length

lemma dl_nil (w : List A) : dl D w [] = 0 := by simp [dl]

lemma dl_append (w v₁ v₂ : List A) : dl D w (v₁ ++ v₂) = dl D w v₁ + dl D (w ++ v₁) v₂ := by
  simp only [dl, ← List.append_assoc]
  ring

/-- The change of length caused by one letter is bounded. -/
lemma dl_step_bound {w : List A} {a : A} (hw : w ++ [a] ∈ Pre D.f) :
    -(M0 D : ℤ) ≤ dl D w [a] ∧ dl D w [a] ≤ M0 D := by
  obtain ⟨u, z, hu, hz, hzw, hzwa⟩ := exists_common D hw
  have hd1 : z.length - (alpha D w).length ≤ M0 D := by
    have hz' : D.f (w ++ ([a] ++ u)) = some z := by rw [← List.append_assoc]; exact hz
    exact delay_bound D (by simpa using Nat.succ_le_succ hu) hz'
  have hd2 : z.length - (alpha D (w ++ [a])).length ≤ M0 D :=
    delay_bound D (le_trans hu (Nat.le_succ _)) hz
  have h1 : (alpha D w).length ≤ z.length := hzw.length_le
  have h2 : (alpha D (w ++ [a])).length ≤ z.length := hzwa.length_le
  simp only [dl]
  omega

/-- The change of length caused by one letter depends only on the state. -/
lemma dl_step_congr {w w' : List A} (h : state D w = state D w') {a : A}
    (hw : w ++ [a] ∈ Pre D.f) : dl D w [a] = dl D w' [a] := by
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
  have e1 : z.length - (alpha D w).length = y.length - (alpha D w').length := by
    have := congrArg List.length hk1; simpa using this
  have e2 : z.length - (alpha D (w ++ [a])).length
      = y.length - (alpha D (w' ++ [a])).length := by
    have := congrArg List.length hk2; simpa using this
  have l1 : (alpha D w).length ≤ z.length := hzw.length_le
  have l2 : (alpha D (w ++ [a])).length ≤ z.length := hzwa.length_le
  have l3 : (alpha D w').length ≤ y.length := (alpha_prefix D hshort hy').length_le
  have l4 : (alpha D (w' ++ [a])).length ≤ y.length :=
    (alpha_prefix D (le_trans hu (Nat.le_succ _)) hy).length_le
  simp only [dl]
  omega

/-- The change of length depends only on the state. -/
lemma dl_congr {w w' : List A} (h : state D w = state D w') (v : List A)
    (hpre : w ++ v ∈ Pre D.f) : dl D w v = dl D w' v := by
  induction v using List.reverseRecOn with
  | nil => simp [dl_nil]
  | append_singleton v' a ih =>
    have hwv : (w ++ v') ++ [a] ∈ Pre D.f := by
      rw [List.append_assoc]; exact hpre
    have hpre' : w ++ v' ∈ Pre D.f := mem_pre_of_append hwv
    have hst : state D (w ++ v') = state D (w' ++ v') := state_append_congr D h v'
    rw [dl_append, dl_append, ih hpre', dl_step_congr D hst hwv]

/-- A crude bound: the length decreases by at most `M0 D` per letter. -/
lemma dl_ge_length (w v : List A) (hpre : w ++ v ∈ Pre D.f) :
    -((M0 D : ℤ) * v.length) ≤ dl D w v := by
  induction v using List.reverseRecOn with
  | nil => simp [dl_nil]
  | append_singleton v' a ih =>
    have hwv : (w ++ v') ++ [a] ∈ Pre D.f := by
      rw [List.append_assoc]; exact hpre
    have hpre' : w ++ v' ∈ Pre D.f := mem_pre_of_append hwv
    have h1 := ih hpre'
    have h2 := (dl_step_bound D hwv).1
    rw [dl_append]
    simp only [List.length_append, List.length_singleton]
    push_cast
    linarith

/-- **The loops do not decrease the length.**  If reading `v` leads back to the
same state, then it cannot shorten the non-branching part, since otherwise
iterating `v` would make its length negative. -/
lemma loop_iter {w v : List A} (hw : w ++ v ∈ Pre D.f) (h : state D (w ++ v) = state D w)
    (n : ℕ) : w ++ npow v n ∈ Pre D.f ∧ state D (w ++ npow v n) = state D w ∧
      dl D w (npow v n) = n * dl D w v := by
  induction n with
  | zero => refine ⟨?_, ?_, ?_⟩ <;> simp [mem_pre_of_append hw, dl_nil]
  | succ n ih =>
    obtain ⟨hp, hs, hd⟩ := ih
    have hnext : (w ++ npow v n) ++ v ∈ Pre D.f := by
      obtain ⟨u, hu⟩ := hw
      refine ⟨u, ?_⟩
      have h1 : (D.f (w ++ (v ++ u))).isSome := by rw [← List.append_assoc]; exact hu
      have h2 := (dom_congr D hs.symm (v ++ u)).1 h1
      rw [List.append_assoc]
      exact h2
    have hst : state D ((w ++ npow v n) ++ v) = state D w := by
      rw [state_append_congr D hs v]; exact h
    have hdl : dl D (w ++ npow v n) v = dl D w v := dl_congr D hs v hnext
    refine ⟨?_, ?_, ?_⟩
    · rw [npow_succ', ← List.append_assoc]; exact hnext
    · rw [npow_succ', ← List.append_assoc]; exact hst
    · rw [npow_succ', dl_append, hd, hdl]
      push_cast
      ring

lemma dl_loop_nonneg {w v : List A} (hw : w ++ v ∈ Pre D.f) (h : state D (w ++ v) = state D w) :
    0 ≤ dl D w v := by
  by_contra hcon
  push_neg at hcon
  have hd1 : dl D w v ≤ -1 := by omega
  set n := (alpha D w).length + 1 with hn
  obtain ⟨hp, hs, hd⟩ := loop_iter D hw h n
  have h0 : dl D w (npow v n)
      = ((alpha D (w ++ npow v n)).length : ℤ) - (alpha D w).length := rfl
  rw [h0] at hd
  have hlen : ((alpha D (w ++ npow v n)).length : ℤ)
      = (alpha D w).length + n * dl D w v := by linarith
  have hnn : (0 : ℤ) ≤ ((alpha D (w ++ npow v n)).length : ℤ) := Int.natCast_nonneg _
  have h3 : (n : ℤ) * dl D w v ≤ (n : ℤ) * (-1) :=
    mul_le_mul_of_nonneg_left hd1 (by positivity)
  have hncast : (n : ℤ) = ((alpha D w).length : ℤ) + 1 := by rw [hn]; push_cast; ring
  rw [hncast] at h3 hlen
  linarith

/-- **The deletion bound.**  There is a constant `M` such that extending the
input never shortens the non-branching part by more than `M` letters. -/
lemma exists_deletion_bound [Finite A] [Finite B] :
    ∃ M : ℕ, M0 D ≤ M ∧ ∀ w v : List A, w ++ v ∈ Pre D.f → -(M : ℤ) ≤ dl D w v := by
  classical
  haveI : Fintype (Set.range (state D)) := (state_range_finite D).fintype
  set N := Fintype.card (Set.range (state D)) with hN
  refine ⟨M0 D * (N + 1), Nat.le_mul_of_pos_right _ (Nat.succ_pos _), ?_⟩
  intro w v
  induction hm : v.length using Nat.strong_induction_on generalizing v w with
  | _ m ih =>
    subst hm
    intro hpre
    by_cases hsmall : v.length ≤ N
    · have h1 := dl_ge_length D w v hpre
      have h2 : (M0 D : ℤ) * v.length ≤ (M0 D : ℤ) * ((N : ℤ) + 1) := by
        have : ((v.length : ℤ)) ≤ (N : ℤ) + 1 := by exact_mod_cast by omega
        exact mul_le_mul_of_nonneg_left this (by positivity)
      push_cast
      push_cast at h1 h2
      linarith
    · push_neg at hsmall
      have hcard : Fintype.card (Set.range (state D)) < Fintype.card (Fin (N + 1)) := by
        simp [← hN]
      obtain ⟨i, j, hij, hst⟩ :=
        Fintype.exists_ne_map_eq_of_card_lt
          (fun i : Fin (N + 1) =>
            (⟨state D (w ++ v.take i.val), ⟨w ++ v.take i.val, rfl⟩⟩ : Set.range (state D)))
          hcard
      -- cut out a loop
      have hsplit : ∃ p q r : List A, p ++ q ++ r = v ∧ 0 < q.length ∧
          state D ((w ++ p) ++ q) = state D (w ++ p) := by
        have key : ∀ i j : Fin (N + 1), i.val < j.val →
            state D (w ++ v.take i.val) = state D (w ++ v.take j.val) →
            ∃ p q r : List A, p ++ q ++ r = v ∧ 0 < q.length ∧
              state D ((w ++ p) ++ q) = state D (w ++ p) := by
          intro i j hlt hstij
          have hj1 : j.val < N + 1 := j.isLt
          have hjv : j.val ≤ v.length := by omega
          have hti : (v.take j.val).take i.val = v.take i.val := by
            rw [List.take_take]
            congr 1
            omega
          have hpq : v.take i.val ++ (v.take j.val).drop i.val = v.take j.val := by
            conv_lhs => rw [← hti]
            exact List.take_append_drop _ _
          refine ⟨v.take i.val, (v.take j.val).drop i.val, v.drop j.val, ?_, ?_, ?_⟩
          · rw [hpq]; exact List.take_append_drop _ _
          · simp only [List.length_drop, List.length_take]
            omega
          · rw [List.append_assoc, hpq]
            exact hstij.symm
        rcases lt_or_gt_of_ne hij with hlt | hlt
        · exact key i j hlt (by simpa using congrArg Subtype.val hst)
        · exact key j i hlt (by simpa using congrArg Subtype.val hst.symm)
      obtain ⟨p, q, r, hv, hqlen, hloopSt⟩ := hsplit
      have hvw : ((w ++ p) ++ q) ++ r = w ++ v := by rw [← hv]; simp [List.append_assoc]
      have hloopPre : (w ++ p) ++ q ∈ Pre D.f := by
        refine mem_pre_of_append (v := r) ?_
        rw [hvw]; exact hpre
      have hloop : 0 ≤ dl D (w ++ p) q := dl_loop_nonneg D hloopPre hloopSt
      have hshortPre : w ++ (p ++ r) ∈ Pre D.f := by
        obtain ⟨u, hu⟩ := hpre
        have h1 : (D.f (((w ++ p) ++ q) ++ (r ++ u))).isSome := by
          have he : ((w ++ p) ++ q) ++ (r ++ u) = (w ++ v) ++ u := by
            rw [← hvw]; simp [List.append_assoc]
          rw [he]; exact hu
        have h2 := (dom_congr D hloopSt (r ++ u)).1 h1
        refine ⟨u, ?_⟩
        have he2 : (w ++ p) ++ (r ++ u) = (w ++ (p ++ r)) ++ u := by simp [List.append_assoc]
        rw [he2] at h2
        exact h2
      have hshortLen : (p ++ r).length < v.length := by
        have hvl := congrArg List.length hv
        simp only [List.length_append] at hvl ⊢
        omega
      have hih := ih (p ++ r).length hshortLen w (p ++ r) rfl hshortPre
      have hqrPre : ((w ++ p) ++ q) ++ r ∈ Pre D.f := by rw [hvw]; exact hpre
      have hrcongr : dl D ((w ++ p) ++ q) r = dl D (w ++ p) r :=
        dl_congr D hloopSt r hqrPre
      have E1 : dl D w ((p ++ q) ++ r) = dl D w (p ++ q) + dl D ((w ++ p) ++ q) r := by
        rw [dl_append]
        congr 2
        simp [List.append_assoc]
      have E2 : dl D w (p ++ q) = dl D w p + dl D (w ++ p) q := dl_append D w p q
      have E3 : dl D w (p ++ r) = dl D w p + dl D (w ++ p) r := dl_append D w p r
      have hdec : dl D w v = dl D w (p ++ r) + dl D (w ++ p) q := by
        rw [← hv, E1, E2, hrcongr, E3]
        ring
      rw [hdec]
      linarith

/-- **Stability of the non-branching part.**  All but the last `M` letters of
`alpha D w` are permanent: they are a prefix of every future non-branching
part. -/
lemma alpha_stable {M : ℕ} (hM : ∀ w v : List A, w ++ v ∈ Pre D.f → -(M : ℤ) ≤ dl D w v)
    (w v : List A) (hpre : w ++ v ∈ Pre D.f) :
    (alpha D w).take ((alpha D w).length - M) <+: alpha D (w ++ v) := by
  induction v using List.reverseRecOn with
  | nil => simpa using List.take_prefix _ _
  | append_singleton v' a ih =>
    have hwv : (w ++ v') ++ [a] ∈ Pre D.f := by rw [List.append_assoc]; exact hpre
    have hpre' : w ++ v' ∈ Pre D.f := mem_pre_of_append hwv
    have hih := ih hpre'
    have hlen : ((alpha D w).length : ℤ) - M ≤ (alpha D (w ++ (v' ++ [a]))).length := by
      have := hM w (v' ++ [a]) hpre
      simp only [dl] at this
      linarith
    rcases alpha_comparable D hwv with hc | hc
    · rw [← List.append_assoc]
      exact hih.trans hc
    · rw [← List.append_assoc]
      refine List.prefix_of_prefix_length_le hih hc ?_
      have : ((alpha D ((w ++ v') ++ [a])).length : ℤ) ≥ ((alpha D w).length : ℤ) - M := by
        rw [List.append_assoc]; exact hlen
      simp only [List.length_take]
      omega

end Subseq

end Lax132576Proofs.Transducers
