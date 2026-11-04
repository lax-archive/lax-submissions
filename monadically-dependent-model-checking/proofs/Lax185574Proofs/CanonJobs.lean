import Lax185574Proofs.Words.CanonGlue
import Lax185574Proofs.LoopGlue
import Lax185574.CanonicalForm
import Lax185574Proofs.Interface.Shim.CanonicalForm

/-!
The canonical form of a list of jobs on the word RAM, as a composite of
the program of the canonical form of one set (obs:canonical) with the
loop driver.

The glue program `canonGlue` asks for the jobs one after the other, and
the program of `Lax185574.CanonicalForm.exists_program_canonical` answers
each job. A job is a list of words, and the elements of the set are taken
as the words themselves (`RawWord`), so the answer is the sorted list of
the distinct words.
-/

namespace Lax185574Proofs.CanonJobs

open Lax808846.Ram Lax808846.RamComputes Lax185574.WordEncoding Lax185574.Computing
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax185574Proofs.Words Lax185574Proofs.Simulate Lax185574Proofs.RamSim

/-- A word as an element: its encoding is the word itself. -/
structure RawWord where
  /-- The word. -/
  w : List ℕ
  deriving DecidableEq

instance : WordEncoding RawWord := ⟨RawWord.w⟩

@[simp] theorem toWord_raw (a : RawWord) : toWord a = a.w := rfl

theorem map_toWord_raw (ws : List (List ℕ)) : (ws.map RawWord.mk).map toWord = ws := by
  induction ws with
  | nil => rfl
  | cons u ws ih => simp only [List.map_cons, toWord_raw, List.cons.injEq, true_and]; exact ih

/-- The set of the words of a list, in canonical form. -/
theorem toWord_canon (ws : List (List ℕ)) :
    toWord (finsetOf {x | x ∈ ws.map RawWord.mk}) = toWord (sortedDistinct ws) := by
  have hfin : ({x | x ∈ ws.map RawWord.mk} : Set RawWord).Finite := (ws.map RawWord.mk).finite_toSet
  have h1 : finsetOf {x | x ∈ ws.map RawWord.mk} = (ws.map RawWord.mk).toFinset := by
    unfold finsetOf; rw [dif_pos hfin]; ext a; simp
  show toWord (Finset.words _) = toWord (sortedDistinct ws)
  congr 1
  rw [h1]
  unfold Finset.words sortedDistinct
  congr 1
  ext u
  simp

/-! ### The rounds of the script -/

theorem lpU_zero (x : List ℕ) : lpU x (lpA0 x) [] = [0, x.length] ++ x ++ [0] := by
  simp [lpU, lpA0]

theorem glueOut_getD {js : List Job} {fin : List ℕ × List ℕ} {j : ℕ} (hj : j < js.length) :
    glueOut js fin j = [(toWord (js, fin)).length + 1, 3 + j + total ((allResults js).take j),
      (toWord (js, fin)).length, 0, jobPos js (j + 1)] ++ toWord ((allResults js).take j) ++
      toWord (jobQuery ((allResults js).take j) (js.getD j (0, []))) := by
  simp [glueOut, Nat.ne_of_lt hj]

theorem length_state {js : List Job} {j : ℕ} (hj : j < js.length) :
    (0 :: jobPos js (j + 1) :: toWord ((allResults js).take j)).length =
      3 + j + total ((allResults js).take j) := by
  have h1 := length_toWord_words ((allResults js).take j)
  have h2 : ((allResults js).take j).length = j := by
    rw [List.length_take, length_allResults]; omega
  simp only [List.length_cons]
  omega

theorem lpU_shape (x r q b : List ℕ) (T : ℕ) :
    lpU x ([T, (0 :: r).length, x.length] ++ (0 :: r) ++ q) b =
      [T, (0 :: r).length] ++ x ++ (0 :: r) ++ (b.length :: b) := by
  simp only [lpU, List.getD_eq_getElem?_getD]
  simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.getD_some, List.drop_zero, List.take_length, List.drop_succ_cons]
  have : List.take (0 :: r).length (0 :: (r ++ q)) = 0 :: r := by
    rw [← List.cons_append, List.take_left']; rfl
  rw [this]

theorem lpQ_shape (x r q : List ℕ) (T : ℕ) :
    lpQ ([T, (0 :: r).length, x.length] ++ (0 :: r) ++ q) = q := by
  simp only [lpQ, List.getD_eq_getElem?_getD]
  simp only [List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.getD_some]
  rw [show 3 + (0 :: r).length = ([T, (0 :: r).length, x.length] ++ (0 :: r)).length by simp; omega]
  rw [← List.cons_append, ← List.cons_append, ← List.cons_append]
  simp

theorem glueOut_shape {js : List Job} {fin : List ℕ × List ℕ} {j : ℕ} (hj : j < js.length) :
    glueOut js fin j = [(toWord (js, fin)).length + 1,
      (0 :: jobPos js (j + 1) :: toWord ((allResults js).take j)).length, (toWord (js, fin)).length] ++
      (0 :: jobPos js (j + 1) :: toWord ((allResults js).take j)) ++
      toWord (jobQuery ((allResults js).take j) (js.getD j (0, []))) := by
  rw [glueOut_getD hj, length_state hj]
  simp

theorem lpU_succ {js : List Job} {fin : List ℕ × List ℕ} {j : ℕ} (hj : j < js.length) :
    lpU (toWord (js, fin)) (glueOut js fin j) ((allResults js).getD j []) = glueIn js fin (j + 1) := by
  rw [glueOut_shape hj, lpU_shape, length_state hj]
  simp [glueIn]

theorem lpQ_glueOut {js : List Job} {fin : List ℕ × List ℕ} {j : ℕ} (hj : j < js.length) :
    lpQ (glueOut js fin j) = toWord (jobQuery ((allResults js).take j) (js.getD j (0, []))) := by
  rw [glueOut_shape hj, lpQ_shape]

theorem answer_eq {js : List Job} {j : ℕ} (hj : j < js.length) :
    toWord (sortedDistinct (jobQuery ((allResults js).take j) (js.getD j (0, [])))) =
      (allResults js).getD j [] := by
  have := allResults_getElem? js j hj
  simp only [List.getD_eq_getElem?_getD, this, List.getElem?_eq_getElem hj, Option.getD_some,
    jobAnswer]

/-! ### Sizes -/

theorem length_le_jobSize (js : List Job) (fin : List ℕ × List ℕ) :
    (toWord (js, fin)).length ≤ jobSize js fin := by
  unfold jobSize; omega

theorem jobsOut_length_le (js : List Job) (fin : List ℕ × List ℕ) :
    (jobsOut js fin).length ≤ jobSize js fin := by
  unfold jobSize; omega

theorem answer_length_le (js : List Job) (fin : List ℕ × List ℕ) (j : ℕ) :
    ((allResults js).getD j []).length ≤ jobSize js fin := by
  have h1 : ((allResults js).getD j []).length ≤ total (allResults js) := by
    rcases Nat.lt_or_ge j (allResults js).length with h | h
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]
      unfold total
      exact (List.sublist_flatten_of_mem (List.getElem_mem h)).length_le
    · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]; simp
  unfold jobSize; omega

theorem query_length_le (js : List Job) (fin : List ℕ × List ℕ) {j : ℕ} (hj : j < js.length) :
    (toWord (jobQuery ((allResults js).take j) (js.getD j (0, [])))).length ≤ jobSize js fin := by
  have h1 : (toWord (jobQuery ((allResults js).take j) (js.getD j (0, [])))).length ≤
      ((List.range js.length).map fun j =>
        (toWord (jobQuery ((allResults js).take j) (js.getD j (0, [])))).length).sum :=
    List.le_sum_of_mem (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)
  unfold jobSize; omega

theorem jobs_length_lt (js : List Job) (fin : List ℕ × List ℕ) :
    js.length < (toWord (js, fin)).length := by
  show js.length < (toWord js ++ toWord fin).length
  rw [List.length_append]
  have : (toWord js).length ≥ 1 := by show (js.length :: _).length ≥ 1; simp
  have h2 : js.length ≤ (toWord js).length - 1 + 0 := by
    show js.length ≤ (js.length :: (js.map toWord).flatten).length - 1 + 0
    simp only [List.length_cons, Nat.add_sub_cancel, Nat.add_zero]
    rw [List.length_flatten]
    have : ∀ a ∈ js, 1 ≤ (toWord a).length := by
      intro a _; show 1 ≤ (toWord a.1 ++ toWord a.2).length; simp [word_simps]
    calc js.length = (js.map fun _ => 1).sum := by simp
      _ ≤ (js.map fun a => (toWord a).length).sum := List.sum_le_sum (fun a ha => this a ha)
      _ = ((js.map toWord).map List.length).sum := by simp [List.map_map]; rfl
  have : (toWord fin).length ≥ 1 := by
    show (toWord fin.1 ++ toWord fin.2).length ≥ 1; simp [word_simps]
  omega

/-! ### The composite -/

/-- The size factor of the layout of the glue program. -/
def gsz : ℕ := glueLayout.temps + 2 + glueLayout.scalars.length + glueLayout.arrays.length + 1

/-- The answers of the callee, as a function of the round. -/
theorem callee_round {pc : Program} {ec cc ac : ℕ}
    (hc : ∀ (α : Type) [WordEncoding α] (l : List α),
      Computes pc ec cc (l.map toWord) (finsetOf {x | x ∈ l}) (fun m => cc * (m + 1) ^ ac))
    (ws : List (List ℕ)) (v : ℕ) (hadm : ∀ y ∈ toWord ws, cc * ((toWord ws).length + y + 1) ^ ec ≤ 2 ^ v)
    (hT : cc * ((toWord ws).length + 1) ^ ac ≤ 2 ^ v) :
    (∃ t ≤ cc * ((toWord ws).length + 1) ^ ac, RunsTo v pc (toWord ws) (toWord (sortedDistinct ws)) t) ∧
      ∀ r t, RunsTo v pc (toWord ws) r t → r = toWord (sortedDistinct ws) := by
  have h := hc RawWord (ws.map RawWord.mk) v
  rw [map_toWord_raw, toWord_canon] at h
  obtain ⟨h1, h2⟩ := h hadm
  refine ⟨?_, h1⟩
  obtain ⟨t, ht, hr⟩ := h2 hT (toWord ws) rfl
  exact ⟨t, ht, hr⟩

theorem pow_le_pow_of_le' {X a b : ℕ} (hX : 1 ≤ X) (h : a ≤ b) : X ^ a ≤ X ^ b :=
  Nat.pow_le_pow_right hX h

/-- The time of the script of the canonical form of a list of jobs. -/
theorem canon_time_arith {tG tP : ℕ → ℕ} {J S zl KL Lc gK cc ac E Q : ℕ} (hJ : J + 1 ≤ S + 1)
    (htG : ∀ i ≤ J, tG i ≤ Lc * (gK * (S + 1) ^ 2) + 1) (htP : ∀ i < J, tP i ≤ cc * (S + 1) ^ ac)
    (hzl : zl ≤ S) (hac : ac ≤ E) (hQt : KL * (Lc * gK + cc + 5) ≤ 5 * Q) :
    KL * (scriptTime tG tP J 0 + zl + 1) ≤ 2 ^ (E + 12) * Q * (S + 1) ^ (E + 4) := by
  set TG := Lc * (gK * (S + 1) ^ 2) + 1 with hTG
  set TP := cc * (S + 1) ^ ac with hTP
  set Y := S + 1 with hY
  have hY1 : 1 ≤ Y := by omega
  have h2E : 2 ^ (E + 12) = 2 ^ E * 4096 := by rw [pow_add]; norm_num
  have hE1 : 1 ≤ 2 ^ E := Nat.one_le_two_pow
  have hsum : scriptTime tG tP J 0 ≤ Y * (TG + TP + 3) := by
    simp only [scriptTime]
    have h1 : ∑ i ∈ Finset.Ico 0 J, (tG i + tP i + 2) ≤ ∑ _i ∈ Finset.Ico 0 J, (TG + TP + 2) :=
      Finset.sum_le_sum fun i hi => by
        have hi' := (Finset.mem_Ico.mp hi).2
        have := htG i hi'.le; have := htP i hi'; omega
    rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul] at h1
    have h2 := htG J le_rfl
    have h3 : (J - 0) * (TG + TP + 2) + (TG + 1) ≤ (J + 1) * (TG + TP + 3) := by
      rw [Nat.sub_zero, add_mul, one_mul]
      exact Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) (by omega)
    have : (J + 1) * (TG + TP + 3) ≤ Y * (TG + TP + 3) := Nat.mul_le_mul_right _ hJ
    omega
  have hTGb : TG ≤ Lc * gK * Y ^ 2 + 1 := by
    have : Lc * (gK * (S + 1) ^ 2) = Lc * gK * Y ^ 2 := by rw [hY]; ring
    rw [hTG]; omega
  have hP1 : Y ≤ Y ^ (E + 3) := by
    calc Y = Y ^ 1 := (pow_one _).symm
      _ ≤ Y ^ (E + 3) := Nat.pow_le_pow_right hY1 (by omega)
  have hPa : Y * Y ^ ac ≤ Y ^ (E + 3) := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right hY1 (by omega)
  have hP3 : Y * Y ^ 2 ≤ Y ^ (E + 3) := by
    rw [← pow_succ']; exact Nat.pow_le_pow_right hY1 (by omega)
  have hT1 : scriptTime tG tP J 0 + zl + 1 ≤ (Lc * gK + cc + 5) * Y ^ (E + 3) := by
    have e1 : Y * (TG + TP + 3) ≤ Lc * gK * (Y * Y ^ 2) + cc * (Y * Y ^ ac) + 4 * Y := by
      have : Y * (TG + TP + 3) ≤ Y * (Lc * gK * Y ^ 2 + 1 + cc * Y ^ ac + 3) :=
        Nat.mul_le_mul_left _ (by rw [hTP] at *; omega)
      have e : Y * (Lc * gK * Y ^ 2 + 1 + cc * Y ^ ac + 3) =
          Lc * gK * (Y * Y ^ 2) + cc * (Y * Y ^ ac) + 4 * Y := by ring
      omega
    have f1 := Nat.mul_le_mul_left (Lc * gK) hP3
    have f2 := Nat.mul_le_mul_left cc hPa
    have e : (Lc * gK + cc + 5) * Y ^ (E + 3) =
        Lc * gK * Y ^ (E + 3) + cc * Y ^ (E + 3) + 5 * Y ^ (E + 3) := by ring
    omega
  calc KL * (scriptTime tG tP J 0 + zl + 1)
      ≤ KL * ((Lc * gK + cc + 5) * Y ^ (E + 3)) := Nat.mul_le_mul_left _ hT1
    _ = KL * (Lc * gK + cc + 5) * Y ^ (E + 3) := by ring
    _ ≤ 5 * Q * Y ^ (E + 3) := Nat.mul_le_mul_right _ hQt
    _ ≤ 2 ^ (E + 12) * Q * Y ^ (E + 4) := by
      rw [h2E]
      have : 5 * Q * Y ^ (E + 3) ≤ (2 ^ E * 4096 * Q) * Y ^ (E + 3) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (le_trans (by norm_num) (Nat.mul_le_mul_right 4096 hE1)))
      exact le_trans this (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hY1 (by omega)))

/-- **Canonical form of a list of jobs.** One program computes the result
of a well-formed list of jobs, at every word length with room for a
fixed power of its size, within that power. The program runs the glue
program and the program of the canonical form of one set in the loop
driver. -/
theorem canonJobs_program :
    ∃ (p : Program) (K e : ℕ), ∀ (js : List Job) (fin : List ℕ × List ℕ), JobsWF js fin →
      ∀ w : ℕ, K * (jobSize js fin + maxEntry (toWord (js, fin)) + 1) ^ e ≤ 2 ^ w →
        (∀ y t, RunsTo w p (toWord (js, fin)) y t → y = jobsOut js fin) ∧
        ∃ t ≤ K * (jobSize js fin + 1) ^ e,
          RunsTo w p (toWord (js, fin)) (jobsOut js fin) t := by
  obtain ⟨pc, ec, cc, ac, hc⟩ := Lax185574Proofs.Shim.CanonicalForm.exists_program_canonical
  set Gp := compileProgram glueLayout canonGlue with hGp
  obtain ⟨p, KL, hL⟩ := loop_sound Gp pc
  set Lc := glueLayout.const with hLc
  set gC := glueC + 2 with hgC
  set E := ec + ac with hE
  set Q := (cc + 1) * (gsz + 1) * gC * (KL + 1) * (Lc * glueK + 1) with hQ
  set K := 2 ^ (E + 12) * Q with hK
  refine ⟨p, K, E + 4, fun js fin hwf w hadm => ?_⟩
  set x := toWord (js, fin) with hx
  set J := js.length with hJ
  set Rs := allResults js with hRs
  set S := jobSize js fin with hS
  set M := maxEntry x with hM
  set Xb := S + M + 1 with hXb
  have hX1 : 1 ≤ Xb := by omega
  have hxS : x.length ≤ S := length_le_jobSize js fin
  have hJx : J < x.length := jobs_length_lt js fin
  have hJX : J < Xb := by omega
  -- the constant
  have hQ1 : 1 ≤ Q := Nat.one_le_iff_ne_zero.mpr (by rw [hQ]; exact Nat.pos_iff_ne_zero.mp (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (by rw [hgC]; exact Nat.succ_pos _)) (Nat.succ_pos _)) (Nat.succ_pos _)))
  have hQg : gsz * gC ≤ Q := by
    have e : Q = ((gsz + 1) * gC) * ((cc + 1) * (KL + 1) * (Lc * glueK + 1)) := by rw [hQ]; ring
    rw [e]
    exact le_trans (Nat.mul_le_mul_right _ (by omega))
      (Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _)))
  have hQc : cc + 1 ≤ Q := by
    have e : Q = (cc + 1) * ((gsz + 1) * gC * (KL + 1) * (Lc * glueK + 1)) := by rw [hQ]; ring
    rw [e]; exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (by rw [hgC]; exact Nat.succ_pos _)) (Nat.succ_pos _)) (Nat.succ_pos _))
  have hQt : KL * (Lc * glueK + cc + 5) ≤ 5 * Q := by
    have h6 : Lc * glueK + cc + 5 ≤ 5 * ((cc + 1) * (Lc * glueK + 1)) := by
      have : (cc + 1) * (Lc * glueK + 1) = cc * (Lc * glueK) + cc + Lc * glueK + 1 := by ring
      omega
    have e : 5 * Q = (KL + 1) * (5 * ((cc + 1) * (Lc * glueK + 1))) * ((gsz + 1) * gC) := by
      rw [hQ]; ring
    rw [e]
    exact le_trans (Nat.mul_le_mul (by omega) h6)
      (Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.succ_pos _) (by rw [hgC]; exact Nat.succ_pos _)))
  have h2E : 2 ^ (E + 12) = 2 ^ E * 4096 := by rw [pow_add]; norm_num
  have hE1 : 1 ≤ 2 ^ E := Nat.one_le_two_pow
  have hK12 : 2 ^ 12 ≤ K := by
    rw [hK, h2E]
    calc 2 ^ 12 = 1 * 4096 * 1 := by norm_num
      _ ≤ 2 ^ E * 4096 * Q := Nat.mul_le_mul (Nat.mul_le_mul hE1 le_rfl) hQ1
  have hXe : Xb ≤ Xb ^ (E + 4) := by
    calc Xb = Xb ^ 1 := (pow_one _).symm
      _ ≤ Xb ^ (E + 4) := Nat.pow_le_pow_right hX1 (by omega)
  have hw12 : 12 ≤ w := by
    by_contra hlt
    have h1 : 2 ^ w < 2 ^ 12 := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ 12 ≤ K * Xb ^ (E + 4) :=
      le_trans hK12 (Nat.le_mul_of_pos_right _ (pow_pos (by omega) _))
    omega
  have hw8 : 8 ≤ w := by omega
  obtain ⟨hcap32, hcap⟩ := lpCap_bounds hw8
  have hKX : K * Xb ^ (E + 4) ≤ 8 * lpCap w := by rw [← hcap]; exact hadm
  have hxw : x.length < 2 ^ (w - 1) := by
    have h1 : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
    have : 2 * Xb ≤ K * Xb ^ (E + 4) := Nat.mul_le_mul (by omega) hXe
    omega
  -- room for the glue program
  set Bv := gC * Xb with hBv
  have hGroom : ∀ j ≤ J, lpSize w (2 * j) ≠ 0 ∧ gsz * Bv ≤ 2 ^ lpV w (2 * j) := by
    intro j hj
    have hBv0 : Bv ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
    have hroomG : (2 * j + 1) ^ 2 * ((gsz + 1) * Bv) ≤ lpCap w := by
      have h1 : (2 * j + 1) ^ 2 ≤ 4 * Xb ^ 2 := by
        have : 2 * j + 1 ≤ 2 * Xb := by omega
        calc (2 * j + 1) ^ 2 ≤ (2 * Xb) ^ 2 := Nat.pow_le_pow_left this 2
          _ = 4 * Xb ^ 2 := by ring
      set T := (gsz + 1) * gC * Xb ^ 3 with hT
      have h2 : 32 * T ≤ K * Xb ^ (E + 4) := by
        have hQg' : (gsz + 1) * gC ≤ Q := by
          have e : Q = ((gsz + 1) * gC) * ((cc + 1) * (KL + 1) * (Lc * glueK + 1)) := by rw [hQ]; ring
          rw [e]; exact Nat.le_mul_of_pos_right _ (Nat.mul_pos (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) (Nat.succ_pos _))
        calc 32 * T = 32 * ((gsz + 1) * gC) * Xb ^ 3 := by rw [hT]; ring
          _ ≤ 2 ^ E * 4096 * Q * Xb ^ (E + 4) :=
            Nat.mul_le_mul (Nat.mul_le_mul (by omega) hQg') (Nat.pow_le_pow_right hX1 (by omega))
          _ = K * Xb ^ (E + 4) := by rw [hK, h2E]
      calc (2 * j + 1) ^ 2 * ((gsz + 1) * Bv) ≤ 4 * Xb ^ 2 * ((gsz + 1) * (gC * Xb)) := Nat.mul_le_mul h1 le_rfl
        _ = 4 * T := by rw [hT]; ring
        _ ≤ lpCap w := by omega
    obtain ⟨hs, hv⟩ := lp_room (w := w) (i := 2 * j) (N := (gsz + 1) * Bv)
      (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) hBv0)) hroomG
    exact ⟨hs, le_trans (Nat.mul_le_mul_right _ (by omega)) hv⟩
  have h2Bv : 2 * Xb ≤ Bv := by rw [hBv, hgC]; exact Nat.mul_le_mul_right _ (by omega)
  have hBv1 : 1 < Bv := by omega
  have hBvC : glueC * (S + M + 1) ≤ Bv := by rw [hBv, hgC]; exact Nat.mul_le_mul_right _ (by omega)
  -- the runs of the glue program
  have hGrun : ∀ j, ∃ tg, j ≤ J → tg ≤ Lc * (glueK * (S + 1) ^ 2) + 1 ∧
      RunsTo (lpV w (2 * j)) Gp (glueIn js fin j) (glueOut js fin j) tg ∧
      ∀ o t, RunsTo (lpV w (2 * j)) Gp (glueIn js fin j) o t → o = glueOut js fin j := by
    intro j
    by_cases hj : j ≤ J
    · obtain ⟨ext, σ', hr, hout⟩ := canonGlue_run js fin hwf j hj Bv hBvC
      obtain ⟨⟨t, ht, hrun⟩, huniq⟩ := glue_runsTo canonGlue_ok (B := Bv) (v := lpV w (2 * j))
        (ext := ext) hBv1 (hGroom j hj).2
        (fun y hy => by
          have := glueIn_entry_le js fin j hj y hy
          simp only [← hx, ← hM, ← hS] at this
          omega) hr
      rw [hout] at hrun huniq
      exact ⟨t, fun _ => ⟨ht, hrun, huniq⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose tG htG using hGrun
  -- the runs of the callee
  set qw : ℕ → List (List ℕ) := fun j => jobQuery (Rs.take j) (js.getD j (0, [])) with hqw
  have hPrun : ∀ j, ∃ tp, j < J → lpSize w (2 * j + 1) ≠ 0 ∧ tp ≤ cc * (S + 1) ^ ac ∧
      RunsTo (lpV w (2 * j + 1)) pc (toWord (qw j)) (Rs.getD j []) tp ∧
      ∀ r t, RunsTo (lpV w (2 * j + 1)) pc (toWord (qw j)) r t → r = Rs.getD j [] := by
    intro j
    by_cases hj : j < J
    · have hql : (toWord (qw j)).length ≤ S := query_length_le js fin hj
      have hqv : ∀ y ∈ toWord (qw j), y ≤ M + S := jobQuery_entry_le js fin j hj
      set N := (cc + 1) * (2 * Xb) ^ E with hN
      have h2X : 1 ≤ 2 * Xb := by omega
      obtain ⟨hsz, hNv⟩ := lp_room (w := w) (i := 2 * j + 1) (N := N)
        (Nat.one_le_iff_ne_zero.mpr (by rw [hN]; exact Nat.mul_ne_zero (Nat.succ_ne_zero _) (pow_ne_zero _ (by omega)))) (by
          have h1 : (2 * j + 1 + 1) ^ 2 ≤ 4 * Xb ^ 2 := by
            have : 2 * j + 1 + 1 ≤ 2 * Xb := by omega
            calc (2 * j + 1 + 1) ^ 2 ≤ (2 * Xb) ^ 2 := Nat.pow_le_pow_left this 2
              _ = 4 * Xb ^ 2 := by ring
          set T := (cc + 1) * 2 ^ E * Xb ^ (E + 2) with hT
          have h3 : 32 * T ≤ K * Xb ^ (E + 4) := by
            calc 32 * T = 2 ^ E * 32 * (cc + 1) * Xb ^ (E + 2) := by rw [hT]; ring
              _ ≤ 2 ^ E * 4096 * Q * Xb ^ (E + 4) :=
                Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul le_rfl (by norm_num)) hQc)
                  (Nat.pow_le_pow_right hX1 (by omega))
              _ = K * Xb ^ (E + 4) := by rw [hK, h2E]
          have h5 : (2 * Xb) ^ E = 2 ^ E * Xb ^ E := mul_pow _ _ _
          calc (2 * j + 1 + 1) ^ 2 * N ≤ 4 * Xb ^ 2 * N := Nat.mul_le_mul h1 le_rfl
            _ = 4 * T := by rw [hN, h5, hT]; ring
            _ ≤ lpCap w := by omega)
      have hpow : ∀ a ≤ E, cc * (2 * Xb) ^ a ≤ N := fun a ha =>
        Nat.mul_le_mul (by omega) (Nat.pow_le_pow_right h2X ha)
      have hadmq : ∀ y ∈ toWord (qw j), cc * ((toWord (qw j)).length + y + 1) ^ ec ≤ 2 ^ lpV w (2 * j + 1) := by
        intro y hy
        have := hqv y hy
        exact le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
          (le_trans (hpow ec (by omega)) hNv)
      have hTq : cc * ((toWord (qw j)).length + 1) ^ ac ≤ 2 ^ lpV w (2 * j + 1) :=
        le_trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _))
          (le_trans (hpow ac (by omega)) hNv)
      obtain ⟨⟨t, ht, hr⟩, hu⟩ := callee_round hc (qw j) _ hadmq hTq
      rw [answer_eq hj] at hr hu
      refine ⟨t, fun _ => ⟨hsz, le_trans ht (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)),
        hr, hu⟩⟩
    · exact ⟨0, fun h => absurd h hj⟩
  choose tP htP using hPrun
  -- the script
  set A : ℕ → List ℕ := fun j => if j = 0 then lpA0 x else glueOut js fin (j - 1) with hA
  set Bs : ℕ → List ℕ := fun j => if j = 0 then [] else Rs.getD (j - 1) [] with hBs
  have hU : ∀ j ≤ J, lpU x (A j) (Bs j) = glueIn js fin j := by
    intro j hj
    cases j with
    | zero => simp [hA, hBs, lpU_zero, glueIn, hx]
    | succ j => simp only [hA, hBs, Nat.succ_ne_zero, if_false, Nat.add_sub_cancel]; exact lpU_succ (by omega)
  have hA1 : ∀ j, A (j + 1) = glueOut js fin j := fun j => by simp [hA]
  have hB1 : ∀ j, Bs (j + 1) = Rs.getD j [] := fun j => by simp [hBs]
  have hQ : ∀ j < J, lpQ (A (j + 1)) = toWord (qw j) := fun j hj => by rw [hA1, lpQ_glueOut hj]
  have hhead : ∀ j < J, (A (j + 1)).head? ≠ some 0 := fun j hj => by
    rw [hA1, glueOut_shape hj]; simp
  have hlast : glueOut js fin J = 0 :: jobsOut js fin := by simp [glueOut, hJ]
  have hcapL : 3 * S + 10 ≤ lpCap w := by
    have : 2 ^ 12 * Xb ≤ K * Xb ^ (E + 4) := Nat.mul_le_mul hK12 hXe
    omega
  have hCU : ∀ j < J, CallUniq w Gp pc x A Bs j := by
    intro j hj
    refine ⟨fun o t h => ?_, hhead j hj, fun r t h => ?_⟩
    · rw [hU j hj.le] at h; rw [hA1]; exact ((htG j hj.le).2.2) o t h
    · rw [hQ j hj] at h; rw [hB1]; exact ((htP j hj).2.2.2) r t h
  have hDU : ∀ o t, RunsTo (lpV w (2 * J)) Gp (lpU x (A J) (Bs J)) o t → o = 0 :: jobsOut js fin := by
    intro o t h
    rw [hU J le_rfl] at h; rw [← hlast]; exact ((htG J le_rfl).2.2) o t h
  refine ⟨fun y t h => loop_script_sound (fun w x hw hx => (hL w x hw hx).2) hw8 hxw (A := A) (B := Bs)
    (R := J) (by simp [hA]) (by simp [hBs]) hCU hDU y t h, ?_⟩
  have hCO : ∀ j < J, CallOK w Gp pc x A Bs tG tP j := by
    intro j hj
    obtain ⟨hg1, hg2, hg3⟩ := htG j hj.le
    obtain ⟨hp0, hp1, hp2, hp3⟩ := htP j hj
    refine ⟨(hGroom j hj.le).1, by rw [hU j hj.le, hA1]; exact hg2,
      fun o t h => by rw [hU j hj.le] at h; rw [hA1]; exact hg3 o t h, ?_, hhead j hj, ?_, hp0,
      by rw [hQ j hj, hB1]; exact hp2, fun r t h => by rw [hQ j hj] at h; rw [hB1]; exact hp3 r t h, ?_⟩
    · rw [hA1, glueOut_shape hj]; simp
    · rw [hA1]; have := glueOut_length_le js fin j hj.le
      simp only [← hS] at this; omega
    · rw [hB1]; have := answer_length_le js fin j
      simp only [← hS, ← hRs] at this; omega
  have hDO : DoneOK w Gp x A Bs tG J (jobsOut js fin) := by
    obtain ⟨hg1, hg2, hg3⟩ := htG J le_rfl
    refine ⟨(hGroom J le_rfl).1, by rw [hU J le_rfl, ← hlast]; exact hg2, hDU, ?_⟩
    have := jobsOut_length_le js fin
    simp only [← hS] at this; simp; omega
  obtain ⟨t, ht, hrun⟩ := loop_script_run (fun w x hw hx => (hL w x hw hx).1) hw8 hxw (A := A) (B := Bs)
    (tG := tG) (tP := tP) (R := J) (by simp [hA]) (by simp [hBs]) hCO hDO
  refine ⟨t, le_trans ht ?_, hrun⟩
  -- the time
  rw [hK]
  exact canon_time_arith (by omega) (fun i hi => (htG i hi).1) (fun i hi => (htP i hi).2.1)
    (by have := jobsOut_length_le js fin; simp only [← hS] at this; exact this) (by omega) hQt

end Lax185574Proofs.CanonJobs
