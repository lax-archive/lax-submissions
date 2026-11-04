import Lax185574Proofs.ResolveRam.Glue.LibSz
import Lax185574Proofs.ResolveRam.Glue.Disp
import Lax185574Proofs.ResolveRam.SizeGlue.Ent

/-!
The libraries of the cases of the glue program are small (`LibSm`).

Every word that a case adds to the state is empty, a word of the next
state, the real query of the next call, or one of the answers of the
compositions of the current item, which are words of the state and the
answer.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574Proofs.Words Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.ResolveRam

theorem tot_eq (ws : List (List ℕ)) : tot ws = total ws + ws.length := by
  have := length_toWord_ws' ws; rw [length_toWord_ws] at this; omega

theorem tot_infix {A B : List (List ℕ)} (h : A <:+: B) : tot A ≤ tot B := by
  obtain ⟨s, t, rfl⟩ := h
  rw [tot_append, tot_append]; omega

theorem mem_rng_plan {L : List (List ℕ)} {ps : List (ℕ × ℕ)} {p : ℕ × ℕ} (hp : p ∈ ps) :
    rng L p.1 p.2 <:+: planW L ps := by
  unfold planW
  induction ps with
  | nil => simp at hp
  | cons q ps ih =>
    rw [List.flatMap_cons]
    rcases List.mem_cons.1 hp with rfl | h
    · exact (List.prefix_append _ _).isInfix
    · exact (ih h).trans (List.suffix_append _ _).isInfix

theorem mem_plan {L : List (List ℕ)} {ps : List (ℕ × ℕ)} {j : ℕ} (hp : (j, 1) ∈ ps) (hj : j < L.length) :
    L[j] ∈ planW L ps := by
  have h := (mem_rng_plan (L := L) hp).subset
  apply h
  simp [rng, List.take_one, List.head?_drop, List.getElem?_eq_getElem hj]

/-- A library that adds at most three words of the size of the output. -/
theorem libSm_small {L ws N : List (List ℕ)} {b o : List ℕ} (hL : L = ws ++ N) (hN : N.length ≤ 3)
    (hw : ∀ w ∈ N, w.length ≤ o.length ∧ ∀ e ∈ w, e ≤ maxEntry o) : LibSm L ws b o := by
  refine libSm_of hL ?_ fun w h e he => by have := (hw w h).2 e he; omega
  have h1 := tot_le (B := o.length) fun w h => (hw w h).1
  rw [tot_eq] at h1
  have : N.length * (o.length + 1) ≤ 3 * (o.length + 1) := Nat.mul_le_mul_right _ hN
  omega

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The output of the round at the position before `c'`. -/
noncomputable def oOf (c' : Cur) : List ℕ := hdOf G P Q s k₀ q₀ c' ++ rQ G k₀ q₀ (callOf G P Q s k₀ q₀ c')

theorem oOf_ws {c' : Cur} {w : List ℕ} (hw : w ∈ (swAt G P Q s k₀ q₀ c').ws) :
    w.length ≤ (oOf G P Q s k₀ q₀ c').length ∧ ∀ e ∈ w, e ≤ maxEntry (oOf G P Q s k₀ q₀ c') := by
  obtain ⟨h1, h2⟩ := out_ws G P Q s k₀ q₀ (o := oOf G P Q s k₀ q₀ c') ⟨_, rfl⟩
  have := length_lt_tot hw; rw [tot_eq] at this
  exact ⟨by omega, h2 w hw⟩

theorem oOf_tot (c' : Cur) :
    tot (swAt G P Q s k₀ q₀ c').ws + 1 ≤ (oOf G P Q s k₀ q₀ c').length := by
  obtain ⟨h1, -⟩ := out_ws G P Q s k₀ q₀ (o := oOf G P Q s k₀ q₀ c') ⟨_, rfl⟩
  rw [tot_eq]; omega

theorem oOf_q {c' : Cur} (hne : callOf G P Q s k₀ q₀ c' ≠ .stp) :
    (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ c')).length ≤ (oOf G P Q s k₀ q₀ c').length ∧
      ∀ e ∈ realQ G k₀ q₀ (callOf G P Q s k₀ q₀ c'), e ≤ maxEntry (oOf G P Q s k₀ q₀ c') :=
  out_q G k₀ q₀ hne ⟨_, rfl⟩

theorem nil_ok {o : List ℕ} : ([] : List ℕ).length ≤ o.length ∧ ∀ e ∈ ([] : List ℕ), e ≤ maxEntry o :=
  ⟨by simp, by simp⟩

/-- A word that the plan copies to the next state. -/
theorem plan_ok {c' : Cur} {L : List (List ℕ)} {ps : List (ℕ × ℕ)} {j : ℕ}
    (hpl : planW L ps = (swAt G P Q s k₀ q₀ c').ws) (hp : (j, 1) ∈ ps) (hj : j < L.length) :
    L[j].length ≤ (oOf G P Q s k₀ q₀ c').length ∧ ∀ e ∈ L[j], e ≤ maxEntry (oOf G P Q s k₀ q₀ c') := by
  have := mem_plan hp hj; rw [hpl] at this; exact oOf_ws G P Q s k₀ q₀ this

/-- **A case that adds `[[], Y]` and copies `Y`.** -/
theorem libSm_two {c c' : Cur} {Y : List ℕ} {ps : List (ℕ × ℕ)}
    (hpl : planW ((swAt G P Q s k₀ q₀ c).ws ++ [[], Y]) ps = (swAt G P Q s k₀ q₀ c').ws)
    (hp : ((swAt G P Q s k₀ q₀ c).ws.length + 1, 1) ∈ ps) {b : List ℕ} :
    LibSm ((swAt G P Q s k₀ q₀ c).ws ++ [[], Y]) (swAt G P Q s k₀ q₀ c).ws b (oOf G P Q s k₀ q₀ c') := by
  refine libSm_small rfl (by simp) fun w hw => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact nil_ok
  · have := plan_ok G P Q s k₀ q₀ hpl hp (by simp)
    simpa using this

/-- **A case that adds `[[], Y, q]` and copies `Y`, with `q` the next query.** -/
theorem libSm_three {c c' : Cur} {Y : List ℕ} {ps : List (ℕ × ℕ)}
    (hpl : planW ((swAt G P Q s k₀ q₀ c).ws ++ [[], Y, realQ G k₀ q₀ (callOf G P Q s k₀ q₀ c')]) ps =
      (swAt G P Q s k₀ q₀ c').ws)
    (hp : ((swAt G P Q s k₀ q₀ c).ws.length + 1, 1) ∈ ps) (hne : callOf G P Q s k₀ q₀ c' ≠ .stp)
    {b : List ℕ} :
    LibSm ((swAt G P Q s k₀ q₀ c).ws ++ [[], Y, realQ G k₀ q₀ (callOf G P Q s k₀ q₀ c')])
      (swAt G P Q s k₀ q₀ c).ws b (oOf G P Q s k₀ q₀ c') := by
  refine libSm_small rfl (by simp) fun w hw => ?_
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · exact nil_ok
  · have := plan_ok G P Q s k₀ q₀ hpl hp (by simp)
    simpa using this
  · exact oOf_q G P Q s k₀ q₀ hne

/-- **The case after the far tree.** -/
theorem libSm_ft {c c' : Cur} {F : List (List ℕ)} {ps : List (ℕ × ℕ)}
    (hpl : planW ((swAt G P Q s k₀ q₀ c).ws ++ [] :: F) ps = (swAt G P Q s k₀ q₀ c').ws)
    (hp : ((swAt G P Q s k₀ q₀ c).ws.length + 1, F.length) ∈ ps) {b : List ℕ} :
    LibSm ((swAt G P Q s k₀ q₀ c).ws ++ [] :: F) (swAt G P Q s k₀ q₀ c).ws b (oOf G P Q s k₀ q₀ c') := by
  set ws := (swAt G P Q s k₀ q₀ c).ws
  have hr : rng (ws ++ [] :: F) (ws.length + 1) F.length = F := by
    have e : ws ++ [] :: F = (ws ++ [[]]) ++ F := by simp
    have hl : (ws ++ [[]]).length = ws.length + 1 := by simp
    rw [e, ← hl]
    simp [rng, List.drop_left]
  have hin := mem_rng_plan (L := ws ++ [] :: F) hp
  simp only [hr, hpl] at hin
  have ht := tot_infix hin
  have ho := oOf_tot G P Q s k₀ q₀ c'
  have := tot_eq (swAt G P Q s k₀ q₀ c').ws
  refine libSm_of rfl ?_ fun w hw e he => ?_
  · rw [tot_eq, tot_eq] at ht
    simp only [total_cons, List.length_cons, List.length_nil]
    omega
  · simp only [List.mem_cons] at hw
    rcases hw with rfl | hw
    · simp at he
    · have := (oOf_ws G P Q s k₀ q₀ (hin.subset hw)).2 e he; omega

/-- **The end of an item.** `coW` is the list of the answers of the
compositions, `E` the expansion and the library ends with the new lengths
and, on the way up, the next query. -/
theorem libSm_fin {c c' : Cur} {C E X : List (List ℕ)} {ps : List (ℕ × ℕ)} {b : List ℕ}
    (hpl : planW ((swAt G P Q s k₀ q₀ c).ws ++ [] :: C ++ E ++ X) ps = (swAt G P Q s k₀ q₀ c').ws)
    (hpE : ((swAt G P Q s k₀ q₀ c).ws.length + 1 + C.length, E.length) ∈ ps)
    (hC : tot C ≤ tot (swAt G P Q s k₀ q₀ c).ws + b.length + 1)
    (hCe : ∀ w ∈ C, ∀ e ∈ w, e ≤ maxEntry (toWord (swAt G P Q s k₀ q₀ c).ws) + maxEntry b)
    (hX : X.length ≤ 2) (hXw : ∀ w ∈ X, w.length ≤ (oOf G P Q s k₀ q₀ c').length ∧
      ∀ e ∈ w, e ≤ maxEntry (oOf G P Q s k₀ q₀ c')) :
    LibSm ((swAt G P Q s k₀ q₀ c).ws ++ [] :: C ++ E ++ X) (swAt G P Q s k₀ q₀ c).ws b
      (oOf G P Q s k₀ q₀ c') := by
  set ws := (swAt G P Q s k₀ q₀ c).ws
  have hr : rng (ws ++ [] :: C ++ E ++ X) (ws.length + 1 + C.length) E.length = E := by
    have e : ws ++ [] :: C ++ E ++ X = (ws ++ [] :: C) ++ (E ++ X) := by simp
    have hl : (ws ++ [] :: C).length = ws.length + 1 + C.length := by simp; omega
    rw [e, ← hl]
    simp [rng, List.drop_left]
  have hin := mem_rng_plan (L := ws ++ [] :: C ++ E ++ X) hpE
  simp only [hr, hpl] at hin
  have ht := tot_infix hin
  have ho := oOf_tot G P Q s k₀ q₀ c'
  have hXt := tot_le (B := (oOf G P Q s k₀ q₀ c').length) fun w h => (hXw w h).1
  have hX3 : X.length * ((oOf G P Q s k₀ q₀ c').length + 1) ≤ 2 * ((oOf G P Q s k₀ q₀ c').length + 1) :=
    Nat.mul_le_mul_right _ hX
  refine libSm_of (N := [] :: C ++ E ++ X) (by simp) ?_ fun w hw e he => ?_
  · have h1 : tot ([] :: C ++ E ++ X) = 1 + tot C + tot E + tot X := by
      simp only [List.cons_append, tot_cons, tot_append, List.length_nil]; omega
    rw [← tot_eq, h1]
    have := tot_eq ws
    omega
  · simp only [List.cons_append, List.mem_cons, List.mem_append] at hw
    rcases hw with rfl | (hw | hw) | hw
    · simp at he
    · have := hCe w hw e he; omega
    · have := (oOf_ws G P Q s k₀ q₀ (hin.subset hw)).2 e he; omega
    · have := (hXw w hw).2 e he; omega

end Lax185574Proofs.ResolveRam.Glue
