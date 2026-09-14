/-
# Moving the head along the tape

Generic lemmas describing the deterministic run of a tape machine: a single transition,
and a *walk*, in which the machine crosses a stretch of tape without changing state or
rewriting anything.  The walk lemmas describe every intermediate configuration, which is
what is needed both to compose the walks and to know that the machine does not accept in
the middle of one.
-/
import Lax251941Proofs.Source.Sim.Config

namespace Lax251941Proofs.PCP
namespace Sim

variable {M : TM}

lemma dstep_move_right (hdet : Det M) {L v : List ℕ} {q a r b : ℕ}
    (h : (q, a, r, b, true) ∈ M.trans) :
    dstep M ⟨L, q, a :: v⟩ = ⟨b :: L, r, v⟩ := by
  have hE : entry M (Cfg.mk L q (a :: v)).st (Cfg.mk L q (a :: v)).right.headI
      = some (r, b, true) := by
    simpa using (entry_eq_some_iff hdet).mpr h
  rw [dstep_right hE]
  rfl

lemma dstep_move_left (hdet : Det M) {L v : List ℕ} {y q a r b : ℕ}
    (h : (q, a, r, b, false) ∈ M.trans) :
    dstep M ⟨y :: L, q, a :: v⟩ = ⟨L, r, y :: b :: v⟩ := by
  have hE : entry M (Cfg.mk (y :: L) q (a :: v)).st (Cfg.mk (y :: L) q (a :: v)).right.headI
      = some (r, b, false) := by
    simpa using (entry_eq_some_iff hdet).mpr h
  rw [dstep_left hE (rfl : (Cfg.mk (y :: L) q (a :: v)).left = y :: L)]
  rfl

/-- Walking to the right across a stretch of tape, leaving it unchanged. -/
lemma walk_right (hdet : Det M) (q : ℕ) (v : List ℕ) (L w : List ℕ)
    (h : ∀ a ∈ v, (q, a, q, a, true) ∈ M.trans) :
    ∀ t ≤ v.length, (dstep M)^[t] ⟨L, q, v ++ w⟩
      = ⟨(v.take t).reverse ++ L, q, v.drop t ++ w⟩ := by
  induction v generalizing L with
  | nil =>
    intro t ht
    simp only [List.length_nil, Nat.le_zero] at ht
    subst ht
    simp
  | cons a v ih =>
    intro t ht
    cases t with
    | zero => simp
    | succ t =>
      rw [Function.iterate_succ_apply]
      have h1 : dstep M ⟨L, q, (a :: v) ++ w⟩ = ⟨a :: L, q, v ++ w⟩ := by
        have := dstep_move_right (v := v ++ w) (L := L) hdet (h a (by simp))
        simpa using this
      rw [h1, ih (a :: L) (fun x hx => h x (by simp [hx])) t (by simpa using ht)]
      simp

/-- Walking to the left across a stretch of tape, leaving it unchanged. -/
lemma walk_left (hdet : Det M) (q : ℕ) (v : List ℕ) (L w : List ℕ) (hw : w ≠ [])
    (h : ∀ a ∈ w.headI :: v, (q, a, q, a, false) ∈ M.trans) :
    ∀ t ≤ v.length, (dstep M)^[t] ⟨v ++ L, q, w⟩
      = ⟨v.drop t ++ L, q, (v.take t).reverse ++ w⟩ := by
  induction v generalizing L w with
  | nil =>
    intro t ht
    simp only [List.length_nil, Nat.le_zero] at ht
    subst ht
    simp
  | cons y v ih =>
    intro t ht
    cases t with
    | zero => simp
    | succ t =>
      rw [Function.iterate_succ_apply]
      obtain ⟨x, w', rfl⟩ : ∃ x w', w = x :: w' := by
        cases w with
        | nil => exact absurd rfl hw
        | cons x w' => exact ⟨x, w', rfl⟩
      have hx : (q, x, q, x, false) ∈ M.trans := h x (by simp)
      have h1 : dstep M ⟨(y :: v) ++ L, q, x :: w'⟩ = ⟨v ++ L, q, y :: x :: w'⟩ := by
        have := dstep_move_left (L := v ++ L) (v := w') (y := y) hdet hx
        simpa using this
      rw [h1, ih (L := L) (w := y :: x :: w') (by simp)
        (fun z hz => h z (by
          simp only [List.headI_cons, List.mem_cons] at hz ⊢
          rcases hz with rfl | hz
          · exact Or.inr (by simp)
          · exact Or.inr (by simp [hz])))
        t (by simpa using ht)]
      simp

end Sim
end Lax251941Proofs.PCP
