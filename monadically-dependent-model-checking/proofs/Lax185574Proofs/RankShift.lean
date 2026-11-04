import Lax185574Proofs.ShiftRam.Rounds
import Lax185574Proofs.LoopScriptOne
import Lax185574.RankShift
import Lax185574.Restriction
import Lax185574Proofs.Interface.Shim.Restriction
import Lax185574Proofs.Interface.Poly

/-!
The rank shift on the word RAM (lem:shift), as a composite of the
restriction program (lem:restrict) with the loop driver.
-/

namespace Lax185574Proofs.RankShift

open Lax808846.Ram Lax808846.RamComputes Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574Proofs.TreeAlgo
open Lax185574Proofs.Words Lax185574Proofs.Simulate Lax185574Proofs.RamSim Lax185574Proofs.ShiftRam

theorem pow_two_le {X e : ℕ} (hX : 1 ≤ X) : X ^ 2 ≤ X ^ (e + 2) :=
  Nat.pow_le_pow_right hX (by omega)

theorem pow_le_pow_add {X e : ℕ} (hX : 1 ≤ X) : X ^ e ≤ X ^ (e + 2) :=
  Nat.pow_le_pow_right hX (by omega)

theorem arith_room (cR A D C Pw Q W L : ℕ) (hA : A ≤ D) (hD : 1 ≤ D) (hP : 1 ≤ Pw) (hQ : 1 ≤ Q)
    (hC : 64 * (cR + 1) * D ≤ C) (hT : C * (Pw * Q) ≤ W) (hW : W = 8 * L) :
    4 * (cR * A * Pw + 1) ≤ L := by
  have h1 : cR * A * Pw ≤ cR * D * Pw := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hA)
  have h2 : 1 ≤ D * Pw := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h3 : 32 * (cR * D * Pw + 1) ≤ 64 * (cR + 1) * D * Pw := by
    have : cR * D * Pw + 1 ≤ (cR + 1) * (D * Pw) := by nlinarith
    calc 32 * (cR * D * Pw + 1) ≤ 32 * ((cR + 1) * (D * Pw)) := Nat.mul_le_mul_left _ this
      _ ≤ 64 * (cR + 1) * D * Pw := by nlinarith
  have h4 : 64 * (cR + 1) * D * Pw ≤ C * Pw := Nat.mul_le_mul_right _ hC
  have h5 : C * Pw ≤ C * (Pw * Q) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hQ)
  omega

theorem arith_time (KL cR k D C N Pw tP tm0 tm1 zl ℓ : ℕ) (hD : 1 ≤ D) (hP : 1 ≤ Pw)
    (hℓ : ℓ ≤ k) (htP : tP ≤ cR * D * Pw) (htm0 : tm0 ≤ 3100 * N + 200 * ℓ + 3001)
    (htm1 : tm1 ≤ 140 * zl + 301) (hzl : zl ≤ N)
    (hC : (KL + 1) * (4200 * (k + 1) + cR * D) ≤ C) :
    KL * (tm0 + tP + 2 + (tm1 + 1) + zl + 1) ≤ C * (Pw * (N + 1) ^ 2) := by
  have h1 : tm0 + 2 + (tm1 + 1) + zl + 1 ≤ 4200 * (k + 1) * (N + 1) := by nlinarith
  have h2 : tm0 + tP + 2 + (tm1 + 1) + zl + 1 ≤ (4200 * (k + 1) + cR * D) * (Pw * (N + 1) ^ 2) := by
    have h3 : 4200 * (k + 1) * (N + 1) ≤ 4200 * (k + 1) * (Pw * (N + 1) ^ 2) := by
      apply Nat.mul_le_mul_left
      exact le_trans (by nlinarith : N + 1 ≤ (N + 1) ^ 2) (Nat.le_mul_of_pos_left _ hP)
    have h4 : cR * D * Pw ≤ cR * D * (Pw * (N + 1) ^ 2) := by
      apply Nat.mul_le_mul_left
      exact Nat.le_mul_of_pos_right _ (by positivity)
    nlinarith
  calc KL * (tm0 + tP + 2 + (tm1 + 1) + zl + 1)
      ≤ KL * ((4200 * (k + 1) + cR * D) * (Pw * (N + 1) ^ 2)) := Nat.mul_le_mul_left _ h2
    _ = KL * (4200 * (k + 1) + cR * D) * (Pw * (N + 1) ^ 2) := by ring
    _ ≤ (KL + 1) * (4200 * (k + 1) + cR * D) * (Pw * (N + 1) ^ 2) := by gcongr; omega
    _ ≤ C * (Pw * (N + 1) ^ 2) := Nat.mul_le_mul_right _ hC

theorem arith_C (KL cR k D : ℕ) (hD : 1 ≤ D) :
    (KL + 1) * (4200 * (k + 1) + cR * D) ≤ 2 ^ 14 * 31 * (KL + 1) * (cR + 1) * (k + 1) * D := by
  have h1 : 4200 * (k + 1) ≤ 4200 * (k + 1) * D := Nat.le_mul_of_pos_right _ hD
  have h2 : cR * D ≤ cR * (k + 1) * D := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_left _ (by omega))
  have h3 : 4200 * (k + 1) + cR * D ≤ 2 ^ 14 * 31 * (cR + 1) * (k + 1) * D := by
    have : 4200 * (k + 1) * D + cR * (k + 1) * D = (4200 + cR) * ((k + 1) * D) := by ring
    have h4 : (4200 + cR) * ((k + 1) * D) ≤ 2 ^ 14 * 31 * (cR + 1) * ((k + 1) * D) :=
      Nat.mul_le_mul_right _ (by omega)
    have : 2 ^ 14 * 31 * (cR + 1) * ((k + 1) * D) = 2 ^ 14 * 31 * (cR + 1) * (k + 1) * D := by ring
    omega
  calc (KL + 1) * (4200 * (k + 1) + cR * D) ≤ (KL + 1) * (2 ^ 14 * 31 * (cR + 1) * (k + 1) * D) :=
        Nat.mul_le_mul_left _ h3
    _ = 2 ^ 14 * 31 * (KL + 1) * (cR + 1) * (k + 1) * D := by ring

/-- The constants of the rank shift. -/
theorem shift_const {KL cR k eR aR D C : ℕ} (hD : D = (k + 6) ^ (eR + aR))
    (hC : C = 2 ^ 14 * lsz * (KL + 1) * (cR + 1) * (k + 1) * D) :
    6 ^ eR ≤ D ∧ (k + 2) ^ aR ≤ D ∧ 1 ≤ D ∧ 507904 ≤ C ∧ 64 * (cR + 1) * D ≤ C ∧
      (KL + 1) * (4200 * (k + 1) + cR * D) ≤ C := by
  have hD6 : 6 ^ eR ≤ D := by
    rw [hD]; exact le_trans (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_right (by omega) (by omega))
  have hDk : (k + 2) ^ aR ≤ D := by
    rw [hD]; exact le_trans (Nat.pow_le_pow_left (by omega) _) (Nat.pow_le_pow_right (by omega) (by omega))
  have hDpos : 1 ≤ D := by rw [hD]; exact Nat.one_le_pow _ _ (by omega)
  rw [lsz_eq] at hC
  have hF : 1 ≤ (KL + 1) * (cR + 1) * (k + 1) * D :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_add_left 1 KL) (Nat.le_add_left 1 cR))
      (Nat.le_add_left 1 k)) hDpos
  have hG : 1 ≤ 256 * 31 * (KL + 1) * (k + 1) :=
    Nat.mul_le_mul (Nat.mul_le_mul (show 1 ≤ 256 * 31 by norm_num) (Nat.le_add_left 1 KL))
      (Nat.le_add_left 1 k)
  refine ⟨hD6, hDk, hDpos, ?_, ?_, ?_⟩
  · have e : C = 507904 * ((KL + 1) * (cR + 1) * (k + 1) * D) := by rw [hC]; ring
    rw [e]; exact Nat.le_mul_of_pos_right _ hF
  · have e : C = 64 * (cR + 1) * D * (256 * 31 * (KL + 1) * (k + 1)) := by rw [hC]; ring
    rw [e]; exact Nat.le_mul_of_pos_right _ hG
  · rw [hC]; exact arith_C KL cR k D hDpos

/-- The query is admissible at the word length of region `1`. -/
theorem query_adm {cR eR w X : ℕ} {Q : List ℕ} (hQ : ∀ y ∈ Q, Q.length + y + 1 ≤ 6 * X)
    (h : 4 * (cR * (6 * X) ^ eR + 1) ≤ lpCap w) : WordAdmissible eR cR (lpV w 1) Q := by
  intro y hy
  have h1 := (lp_room (w := w) (i := 1) (N := cR * (6 * X) ^ eR + 1) (by omega) (by norm_num; omega)).2
  have := Nat.mul_le_mul_left cR (Nat.pow_le_pow_left (hQ y hy) eR)
  omega

/-- **The first round of the rank shift.** The glue program finds an
extension with guard `0`, whose child is `node_{k+1,q}(ā b)`, and asks
for its restriction to the first `ℓ` positions. -/
theorem shift_round0 {n : ℕ} (G : PartialGraph (Fin n)) (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin n)
    (hℓ : 1 ≤ ℓ) {x : List ℕ} (hx : x = [k, q + 1, ℓ] ++ toWord (node G k (q + 1) u))
    {Xb : ℕ} (hXb : Xb = x.length + maxEntry x + 1) {v : ℕ} (hS : lsz * (64 * Xb ^ 2) ≤ 2 ^ v) :
    ∃ (b : Fin n) (o : List ℕ), o.getD 0 0 = 1 ∧ o.getD 1 0 = 0 ∧ o.getD 2 0 = 0 ∧
      o.head? ≠ some 0 ∧ o ≠ [] ∧ o.length ≤ x.length + ℓ + 4 ∧
      lpQ o = toWord (tree G (k + 1) q (Fin.snoc u b), initJ ℓ) ∧
      (lpQ o).length ≤ x.length + ℓ + 1 ∧ (∀ y ∈ lpQ o, y ≤ maxEntry x + 1) ∧
      (∃ tm ≤ 3100 * x.length + 200 * ℓ + 3001, RunsTo v glueProg (lpU x (lpA0 x) []) o tm) ∧
      (∀ o' tm, RunsTo v glueProg (lpU x (lpA0 x) []) o' tm → o' = o) ∧
      (toWord (tree G (k + 1) q u)).length ≤ x.length ∧
      ∀ y ∈ toWord (tree G (k + 1) q u), y < x.length + maxEntry x + 2 := by
  subst hx
  set t := node G k (q + 1) u with ht
  set x := [k, q + 1, ℓ] ++ toWord t with hxdef
  have hmem : ∀ y ∈ x, y ≤ maxEntry x := fun y hy => le_maxEntry hy
  have hkM : k ≤ maxEntry x := hmem k (by simp [hxdef])
  have hqM : q + 1 ≤ maxEntry x := hmem (q + 1) (by simp [hxdef])
  have hℓM : ℓ ≤ maxEntry x := hmem ℓ (by simp [hxdef])
  have htN : (toWord t).length + 3 = x.length := by simp [hxdef]
  have hXX : Xb ≤ Xb ^ 2 := Nat.le_self_pow (by norm_num) _
  obtain ⟨a, ha, -, ⟨tm0, htm0, hG0⟩, hU0⟩ := shift_g0 (v := v) k q ℓ t
    (exists_guard_zero G k q hℓ u) (64 * Xb ^ 2)
    (fun y hy => by have := hmem y hy; omega) (by omega) hS
  obtain ⟨b, hb⟩ := child_eq G k q u ha
  have hinf := child_infix ha
  have hcl : (toWord a.2).length ≤ (toWord t).length := hinf.length_le
  have hcv : ∀ y ∈ toWord a.2, y ≤ maxEntry x := fun y hy =>
    hmem y (List.mem_append_right _ (hinf.subset hy))
  set o := [1, 0, 0, k + 1, q, ℓ + 1] ++ toWord a.2 ++ (ℓ :: List.range ℓ) with ho
  have hq0e : lpQ o = [k + 1, q, ℓ + 1] ++ toWord a.2 ++ (ℓ :: List.range ℓ) := by
    show o.drop (3 + o.getD 1 0) = _
    rw [show o.getD 1 0 = 0 by simp [ho]]
    simp [ho]
  have hq0 : lpQ o = toWord (tree G (k + 1) q (Fin.snoc u b), initJ ℓ) := by
    rw [toWord_query, hq0e, hb]; rfl
  have hb2 : toWord (node G (k + 1) q (Fin.snoc u b)) = toWord a.2 := by rw [hb]
  obtain ⟨hzl, hzv⟩ := answer_bound G (k + 1) q u b (x.length + maxEntry x + 2)
    (fun y hy => by rw [hb2] at hy; have := hcv y hy; omega) (by rw [hb2]; omega) (by omega)
    (by omega) (by omega)
  rw [hb2] at hzl
  refine ⟨b, o, by simp [ho], by simp [ho], by simp [ho], by simp [ho], by simp [ho],
    by simp [ho]; omega, hq0, by rw [hq0e]; simp; omega, ?_, ⟨tm0, by omega, hG0⟩, hU0,
    by omega, hzv⟩
  intro y hy
  rw [hq0e] at hy
  rcases List.mem_append.mp hy with h | h
  · rcases List.mem_append.mp h with h | h
    · simp at h; omega
    · exact le_trans (hcv y h) (by omega)
  · simp at h; omega

/-- **Soundness of the rank shift.** Every halting run of the composite
on the word of `tree_{k,q+1}(ā)` outputs the word of `tree_{k+1,q}(ā)`. -/
theorem shift_sound {pR p : Program} {eR cR aR : ℕ}
    (hp : ∀ (w : ℕ) (x : List ℕ), 8 ≤ w → x.length < 2 ^ (w - 1) →
      ∀ z t, RunsTo w p x z t → ∃ T, LoopTrace w glueProg pR x 0 (lpA0 x) [] z T)
    {n : ℕ} (G : PartialGraph (Fin n)) (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin n) (hℓ : 1 ≤ ℓ)
    (hRk : ∀ u' : Fin (ℓ + 1) → Fin n, Computes pR eR cR (tree G (k + 1) q u', initJ ℓ)
      (tree G (k + 1) q (fun i => u' ((initJ ℓ).get i))) (fun m => cR * (m + 1) ^ aR))
    {x : List ℕ} (hx : x = [k, q + 1, ℓ] ++ toWord (node G k (q + 1) u))
    {Xb : ℕ} (hXb : Xb = x.length + maxEntry x + 1) {w : ℕ} (hw8 : 8 ≤ w)
    (hxw : x.length < 2 ^ (w - 1))
    (hG : ∀ i ≤ 2, lpSize w i ≠ 0 ∧ lsz * (64 * Xb ^ 2) ≤ 2 ^ lpV w i)
    (hroomP : 4 * (cR * (6 * Xb) ^ eR + 1) ≤ lpCap w) :
    ∀ y t, RunsTo w p x y t → y = toWord (tree G (k + 1) q u) := by
  obtain ⟨b, o, ho0, ho1, ho2, hh, -, -, hq0, hq0l, hq0v, -, hU0, hzl, hzv⟩ :=
    shift_round0 G k q u hℓ hx hXb (hG 0 (by omega)).2
  have hℓM : ℓ ≤ maxEntry x := le_maxEntry (by rw [hx]; simp)
  have hP := hRk (Fin.snoc u b)
  rw [restrict_answer] at hP
  have hadmP : WordAdmissible eR cR (lpV w 1) (toWord (tree G (k + 1) q (Fin.snoc u b), initJ ℓ)) := by
    rw [← hq0]; exact query_adm (X := Xb) (fun y hy => by have := hq0v y hy; omega) hroomP
  have hXX : Xb ≤ Xb ^ 2 := Nat.le_self_pow (by norm_num) _
  exact one_call_sound hp hw8 hxw hU0 hh
    (fun r tm h => by rw [hq0] at h; exact (hP (lpV w 1) hadmP).1 r tm h)
    (shift_g1 (v := lpV w 2) x o _ ho1 ho2 ho0 (64 * Xb ^ 2) (fun y hy => by have := hzv y hy; omega)
      (by omega) (hG 2 le_rfl).2).2

/-- **The time of the rank shift.** If the time bound fits into a word,
the composite halts with the word of `tree_{k+1,q}(ā)` within it. -/
theorem shift_time {pR p : Program} {eR cR aR KL : ℕ}
    (hp : ∀ (w : ℕ) (x : List ℕ), 8 ≤ w → x.length < 2 ^ (w - 1) →
      ∀ z T, LoopTrace w glueProg pR x 0 (lpA0 x) [] z T →
        ∃ t ≤ KL * (T + z.length + 1), RunsTo w p x z t)
    {n : ℕ} (G : PartialGraph (Fin n)) (k q : ℕ) {ℓ : ℕ} (u : Fin ℓ → Fin n) (hℓ : 1 ≤ ℓ)
    (hℓk : ℓ ≤ k)
    (hRk : ∀ u' : Fin (ℓ + 1) → Fin n, Computes pR eR cR (tree G (k + 1) q u', initJ ℓ)
      (tree G (k + 1) q (fun i => u' ((initJ ℓ).get i))) (fun m => cR * (m + 1) ^ aR))
    {x : List ℕ} (hx : x = [k, q + 1, ℓ] ++ toWord (node G k (q + 1) u))
    {Xb : ℕ} (hXb : Xb = x.length + maxEntry x + 1) {w : ℕ} (hw8 : 8 ≤ w)
    (hxw : x.length < 2 ^ (w - 1))
    (hG : ∀ i ≤ 2, lpSize w i ≠ 0 ∧ lsz * (64 * Xb ^ 2) ≤ 2 ^ lpV w i)
    (hroomP : 4 * (cR * (6 * Xb) ^ eR + 1) ≤ lpCap w) (hXcap : 8 * Xb ≤ lpCap w)
    {D C : ℕ} (hDk : (k + 2) ^ aR ≤ D) (hDpos : 1 ≤ D) (hC1 : 64 * (cR + 1) * D ≤ C)
    (hCK : (KL + 1) * (4200 * (k + 1) + cR * D) ≤ C)
    (hT : C * (x.length + 1) ^ (aR + 2) ≤ 2 ^ w) :
    ∃ t ≤ C * (x.length + 1) ^ (aR + 2), RunsTo w p x (toWord (tree G (k + 1) q u)) t := by
  obtain ⟨b, o, ho0, ho1, ho2, hh, hne, hol, hq0, hq0l, hq0v, ⟨tm0, htm0, hG0⟩, hU0, hzl, hzv⟩ :=
    shift_round0 G k q u hℓ hx hXb (hG 0 (by omega)).2
  have hℓM : ℓ ≤ maxEntry x := le_maxEntry (by rw [hx]; simp)
  have hP := hRk (Fin.snoc u b)
  rw [restrict_answer] at hP
  set z := toWord (tree G (k + 1) q u) with hz
  have hadmP : WordAdmissible eR cR (lpV w 1) (toWord (tree G (k + 1) q (Fin.snoc u b), initJ ℓ)) := by
    rw [← hq0]; exact query_adm (X := Xb) (fun y hy => by have := hq0v y hy; omega) hroomP
  have hXX : Xb ≤ Xb ^ 2 := Nat.le_self_pow (by norm_num) _
  obtain ⟨⟨tm1, htm1, hrun1⟩, hu1⟩ := shift_g1 (v := lpV w 2) x o z ho1 ho2 ho0 (64 * Xb ^ 2)
    (fun y hy => by have := hzv y hy; omega) (by omega) (hG 2 le_rfl).2
  obtain ⟨-, hcap⟩ := lpCap_bounds hw8
  -- the run of the restriction program
  obtain ⟨N, hN⟩ : ∃ N, N = x.length := ⟨_, rfl⟩
  rw [← hN] at hT ⊢
  have hql1 : (lpQ o).length + 1 ≤ (k + 2) * (N + 1) := by
    have : (k + 2) * (N + 1) = k * N + 2 * N + k + 2 := by ring
    omega
  obtain ⟨Pw, hPw⟩ : ∃ Pw, Pw = (N + 1) ^ aR := ⟨_, rfl⟩
  have hPw1 : 1 ≤ Pw := by rw [hPw]; exact Nat.one_le_pow _ _ (by omega)
  have hTP0 : cR * ((lpQ o).length + 1) ^ aR ≤ cR * (k + 2) ^ aR * Pw := by
    rw [Nat.mul_assoc, hPw, ← mul_pow]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hql1 _)
  have hQ : (N + 1) ^ (aR + 2) = Pw * (N + 1) ^ 2 := by rw [pow_add, hPw]
  have hN2 : 1 ≤ (N + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hroomT : 4 * (cR * (k + 2) ^ aR * Pw + 1) ≤ lpCap w :=
    arith_room cR _ D C Pw _ _ _ hDk hDpos hPw1 hN2 hC1 (by rw [← hQ]; exact hT) hcap
  obtain ⟨hsP, hTPv⟩ := lp_room (w := w) (i := 1) (N := cR * (k + 2) ^ aR * Pw + 1) (by omega)
    (by norm_num; omega)
  have hTP : cR * (wordLength (tree G (k + 1) q (Fin.snoc u b), initJ ℓ) + 1) ^ aR ≤
      2 ^ lpV w 1 := by
    simp only [wordLength]; rw [← hq0]; omega
  obtain ⟨tP, htP, hrP⟩ := (hP (lpV w 1) hadmP).2 hTP _ rfl
  rw [← hq0] at hrP
  beta_reduce at hrP
  rw [← hz] at hrP
  obtain ⟨tz, htz, hrun⟩ := one_call_run hp hw8 hxw (hG 0 (by omega)).1 hG0 hU0 hne hh
    (by omega) hsP hrP (fun r tm h => by rw [hq0] at h; exact (hP (lpV w 1) hadmP).1 r tm h)
    (by omega) (hG 2 le_rfl).1 hrun1 hu1 (by simp; omega)
  refine ⟨tz, le_trans htz ?_, hrun⟩
  rw [hQ]
  have htP2 : tP ≤ cR * ((lpQ o).length + 1) ^ aR := by
    have := htP; simp only [wordLength] at this; rw [← hq0] at this; exact this
  have htP' : tP ≤ cR * D * Pw := le_trans htP2 (le_trans hTP0
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hDk)))
  exact arith_time KL cR k D C N Pw tP tm0 tm1 z.length ℓ hDpos hPw1 hℓk htP'
    (by omega) htm1 (by omega) hCK

/-- The statement for the older notion `Lax185574.Computing.Computes`. -/
theorem exists_program_shift_old :
    ∃ (p : Program) (e : ℕ), ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n),
        1 ≤ ℓ → ℓ ≤ k →
        Computes p e c (tree G k (q + 1) u) (tree G (k + 1) q u)
          (fun m => c * (m + 1) ^ a) := by
  obtain ⟨pR, eR, hR⟩ := Lax185574Proofs.Shim.Restriction.exists_program_restrict
  obtain ⟨p, KL, hL⟩ := loop_sound glueProg pR
  refine ⟨p, eR + 2, fun k q => ?_⟩
  obtain ⟨cR, aR, hRk⟩ := hR (k + 1) q
  obtain ⟨D, hD⟩ : ∃ D, D = (k + 6) ^ (eR + aR) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = 2 ^ 14 * lsz * (KL + 1) * (cR + 1) * (k + 1) * D := ⟨_, rfl⟩
  obtain ⟨hD6, hDk, hDpos, hCbig, hC1, hCK⟩ := shift_const hD hC
  refine ⟨C, aR + 2, fun n G ℓ u hℓ hℓk => ?_⟩
  have hP := fun u' => hRk n G (ℓ + 1) u' (initJ ℓ) (by omega) (initJ_nodup ℓ)
  intro w hadm
  have hx : toWord (tree G k (q + 1) u) = [k, q + 1, ℓ] ++ toWord (node G k (q + 1) u) := rfl
  rw [hx] at hadm ⊢
  set x := [k, q + 1, ℓ] ++ toWord (node G k (q + 1) u) with hxdef
  obtain ⟨Xb, hXb⟩ : ∃ Xb, Xb = x.length + maxEntry x + 1 := ⟨_, rfl⟩
  have hadm' : C * Xb ^ (eR + 2) ≤ 2 ^ w := by
    rw [hXb]; exact hadm _ (maxEntry_mem (by simp [hxdef]))
  have hX1 : 1 ≤ Xb := by omega
  have hXX : Xb ≤ Xb ^ 2 := Nat.le_self_pow (by norm_num) _
  have hX2 : C * Xb ^ 2 ≤ 2 ^ w := le_trans (Nat.mul_le_mul_left _ (pow_two_le hX1)) hadm'
  have hCX : 507904 * Xb ^ 2 ≤ 2 ^ w := le_trans (Nat.mul_le_mul_right _ hCbig) hX2
  have hw8 : 8 ≤ w := by
    by_contra hlt
    have : 2 ^ w ≤ 128 := le_trans (Nat.pow_le_pow_right (by norm_num) (by omega : w ≤ 7)) (by norm_num)
    have : 1 ≤ Xb ^ 2 := Nat.one_le_pow _ _ hX1
    omega
  obtain ⟨-, hcap⟩ := lpCap_bounds hw8
  have hxw : x.length < 2 ^ (w - 1) := by
    have h1 : 2 ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
    omega
  -- the room of the regions for the glue program
  have hGroom : ∀ i ≤ 2, lpSize w i ≠ 0 ∧ lsz * (64 * Xb ^ 2) ≤ 2 ^ lpV w i := by
    intro i hi
    have h1 : 1 ≤ Xb ^ 2 := Nat.one_le_pow _ _ hX1
    refine lp_room ?_ ?_
    · rw [lsz_eq]; omega
    · have : (i + 1) ^ 2 ≤ 9 := by interval_cases i <;> norm_num
      have h9 := Nat.mul_le_mul_right (lsz * (64 * Xb ^ 2)) this
      rw [lsz_eq] at h9 ⊢; omega
  -- the room of the region of the restriction program
  have hroomP : 4 * (cR * (6 * Xb) ^ eR + 1) ≤ lpCap w := by
    have hY : 1 ≤ 6 ^ eR * Xb ^ eR :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (pow_ne_zero _ (by norm_num)) (pow_ne_zero _ (by omega)))
    have h3 : 64 * (cR + 1) * 6 ^ eR ≤ C := le_trans (Nat.mul_le_mul_left _ hD6) hC1
    have h2 : 64 * (cR + 1) * 6 ^ eR * Xb ^ eR ≤ C * Xb ^ (eR + 2) :=
      Nat.mul_le_mul h3 (pow_le_pow_add hX1)
    have e : 64 * (cR + 1) * 6 ^ eR * Xb ^ eR =
        64 * (cR * (6 ^ eR * Xb ^ eR)) + 64 * (6 ^ eR * Xb ^ eR) := by ring
    rw [mul_pow]; omega
  have hXcap : 8 * Xb ≤ lpCap w := by omega
  refine ⟨shift_sound (fun w x hw hx => (hL w x hw hx).2) G k q u hℓ hP hxdef hXb hw8 hxw hGroom
    hroomP, fun hT => ?_⟩
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact shift_time (fun w x hw hx => (hL w x hw hx).1) G k q u hℓ hℓk hP hxdef hXb hw8 hxw hGroom
    hroomP hXcap hDk hDpos hC1 hCK hT

open Lax185574.Encoding Lax185574.Algorithms Lax185574Proofs.Interface

/--
---
conclusion: Lax185574.RankShift.exists_program_shift
---
The program runs the glue program `ShiftRam.glue` and the restriction
program of the restriction lemma in the loop driver `loop_sound`. In its
first round the glue program reads the tree, finds the first extension
with guard `0`, which exists since `dist(a₁, a₁) = 0`, and asks for the
restriction of its child to the first `ℓ` positions. In its second round
it outputs the answer. The child is `tree_{k+1,q−1}(ā b)` for a vertex
`b`, so the answer is `tree_{k+1,q−1}(ā)`, as in the proof of the rank
shift lemma. Every run inside the driver is right at an admissible word
length: the runs of the glue program because their values are polynomial
in the input, the run of the restriction program because its query is
admissible at the word length of its region. The constant absorbs the
constant of the restriction program at rank `(k + 1, q)`, and the degree
is that of the restriction program plus two.

The proof is carried out for the notion `Lax185574.Computing.Computes`,
and transferred to `Lax185574.Algorithms.Algorithm.Computes`
through `Lax185574Proofs.Interface`.
-/
theorem exists_program_shift :
    ∃ A : Algorithm, ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n), 1 ≤ ℓ → ℓ ≤ k →
        A.Computes c (tree G k (q + 1) u) (tree G (k + 1) q u)
          (((encode (tree G k (q + 1) u)).length + 1) ^ a) := by
  obtain ⟨p, e, h⟩ := exists_program_shift_old
  refine ⟨⟨p, e⟩, fun k q => ?_⟩
  obtain ⟨c, a, h⟩ := h k q
  exact ⟨c, a, fun n G ℓ u h₁ h₂ => computes_of_poly rfl (h n G ℓ u h₁ h₂)⟩

end Lax185574Proofs.RankShift
