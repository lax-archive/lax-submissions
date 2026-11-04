import Lax185574Proofs.ResolveRam.SlotTime
import Lax185574Proofs.RamPipeFwd

/-!
The composite of lem:resolve-lift halts if all rounds fit.

`resolve_run`: let `Hb` bound the heads of the glue program and `Qb` the
sizes of the input, of the output and of the queries and answers of the
calls. Let `Bnd` bound the guard quantity of the time clause of the
glue program, twice the time bound of every call and the constants. If
every region of the loop driver up to the last round has room for `Bnd ·
2 ^ (2 D + 20)`, then the composite halts with the output within the
constant of the driver times the bound of the glue program, the times of
the switch and the length of the output. Adapted from the assembly of
thm:mc (`MC/Asm/Fit`).
-/

namespace Lax185574Proofs.ResolveRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ScatterTypes
open Lax185574.ResolveLift Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo
open Lax185574Proofs.Words Lax185574Proofs.Simulate Lax185574Proofs.RamSim Lax185574Proofs.RamCat
open Lax808846Proofs.Machine

/-! ### Sizes of words -/

theorem maxEntry_le_of {l : List ℕ} {B : ℕ} (h : ∀ e ∈ l, e ≤ B) : maxEntry l ≤ B := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    show max a (maxEntry l) ≤ B
    exact max_le (h a (by simp)) (ih fun e he => h e (by simp [he]))

theorem lt_ySz {l : List ℕ} {e : ℕ} (he : e ∈ l) : e < ySz l := by
  have := le_maxEntry he; unfold ySz; omega

theorem length_lt_ySz (l : List ℕ) : l.length < ySz l := by unfold ySz; omega

theorem ySz_append (a b : List ℕ) : ySz (a ++ b) ≤ ySz a + ySz b := by
  have h : maxEntry (a ++ b) ≤ maxEntry a + maxEntry b := maxEntry_le_of fun e he => by
    rcases List.mem_append.1 he with h | h
    · have := le_maxEntry h; omega
    · have := le_maxEntry h; omega
  unfold ySz; simp only [List.length_append]; omega

theorem ySz_cons (e : ℕ) (l : List ℕ) : ySz (e :: l) ≤ ySz l + e + 1 := by
  have h : maxEntry (e :: l) ≤ e + maxEntry l := maxEntry_le_of fun x hx => by
    rcases List.mem_cons.1 hx with rfl | h
    · omega
    · have := le_maxEntry h; omega
  unfold ySz; simp only [List.length_cons]; omega

theorem getD_le_maxEntry (l : List ℕ) (i : ℕ) : l.getD i 0 ≤ maxEntry l := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : l[i]? with _ | e
  · simp
  · exact le_maxEntry (List.mem_of_getElem? h)

theorem ySz_lpU (x a b : List ℕ) : ySz (lpU x a b) ≤ 2 * (ySz x + ySz a + ySz b) + 3 := by
  have hm : maxEntry (lpU x a b) ≤ maxEntry x + maxEntry a + b.length + maxEntry b :=
    maxEntry_le_of fun e he => by
      simp only [lpU, List.mem_append, List.mem_cons, List.mem_singleton] at he
      rcases he with ((((rfl | rfl | he) | he) | he) | rfl | he)
      · have := getD_le_maxEntry a 0; omega
      · have := getD_le_maxEntry a 1; omega
      · simp at he
      · have := le_maxEntry (List.mem_of_mem_drop (List.mem_of_mem_take he)); omega
      · have := le_maxEntry (List.mem_of_mem_drop (List.mem_of_mem_take he)); omega
      · omega
      · have := le_maxEntry he; omega
  have hl : (lpU x a b).length ≤ 3 + x.length + a.length + b.length := by
    simp only [lpU, List.length_append, List.length_cons, List.length_nil, List.length_take,
      List.length_drop]
    omega
  unfold ySz at *; omega

/-! ### Tools of the loop driver -/

theorem rle_catLim {B w E : ℕ} (hE : E ≤ w) (h : B + 1 ≤ 2 ^ (w - E)) : B ≤ catLim w E := by
  unfold catLim
  rw [Nat.le_div_iff_mul_le (by positivity)]
  have e : 2 ^ w = 2 ^ (w - E) * 2 ^ E := by rw [← pow_add]; congr 1; omega
  have h2 : (B + 1) * 2 ^ E ≤ 2 ^ (w - E) * 2 ^ E := Nat.mul_le_mul_right _ h
  have : 1 ≤ 2 ^ E := Nat.one_le_two_pow
  rw [add_mul, one_mul] at h2
  omega

theorem rlpSize_ne {w i : ℕ} (h : (i + 1) ^ 2 ≤ lpCap w) : lpSize w i ≠ 0 := by
  have h1 := lpSize_ge w i
  have : 1 ≤ lpCap w / (i + 1) ^ 2 := (Nat.one_le_div_iff (by positivity)).2 h
  omega

theorem rpow_lpV_le (w i : ℕ) : 2 ^ lpV w i ≤ lpCap w := two_pow_mono (by unfold lpV lpCap; omega)

/-- The sum over the rounds of a function of the calls. -/
theorem sum_range_calls {α : Type*} (f : α → ℕ) (cs : List α) :
    ∑ j ∈ Finset.range cs.length, (match cs[j]? with | some c => f c | none => 0) =
      (cs.map f).sum := by
  induction cs with
  | nil => simp
  | cons c cs ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons, ← ih]
    simp only [List.getElem?_cons_succ, List.getElem?_cons_zero]
    omega

variable {n : ℕ} (G : PartialGraph (Fin n)) (k₀ q₀ : ℕ)

/-- The exponent of the guard quantity of the time clause of the glue program. -/
noncomputable def eGl : ℕ := eSh + eFt + eCo + eCa + eSt + 2

theorem round_sz {x z : List ℕ} {cs : List RCall} {hd : ℕ → List ℕ} {Hb Qb : ℕ}
    (hHb : ∀ j < cs.length, ySz (hd j) ≤ Hb) (hQ : ∀ c ∈ cs, ySz (rQ G k₀ q₀ c) + ySz (rY G k₀ q₀ c) ≤ Qb)
    (hz : ySz z ≤ Qb) (hx : ySz x ≤ Qb) {j : ℕ} (hj : j ≤ cs.length) :
    ySz (gU G k₀ q₀ x cs hd z j) + ySz (gOut G k₀ q₀ cs hd z j) + ySz x ≤ 8 * (Hb + Qb) + 16 := by
  have hO : ∀ i ≤ cs.length, ySz (gOut G k₀ q₀ cs hd z i) ≤ Hb + Qb + 1 := by
    intro i hi
    unfold gOut
    rcases h : cs[i]? with _ | c
    · have := ySz_cons 0 z; simp only; omega
    · have hi' : i < cs.length := by
        by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; simp at h
      have := ySz_append (hd i) (rQ G k₀ q₀ c)
      have := hHb i hi'
      have := hQ c (List.mem_of_getElem? h)
      simp only; omega
  have hA : ySz (gA G k₀ q₀ x cs hd z j) ≤ Hb + Qb + 4 := by
    rcases j with _ | j
    · have : ySz (lpA0 x) ≤ x.length + 4 := by
        have hm : maxEntry (lpA0 x) ≤ x.length := maxEntry_le_of fun e he => by
          simp only [lpA0, List.mem_cons, List.not_mem_nil, or_false] at he
          rcases he with rfl | rfl | rfl <;> omega
        have hl : (lpA0 x).length = 3 := rfl
        unfold ySz; omega
      have := length_lt_ySz x
      simp only [gA]; omega
    · have := hO j (by omega); simp only [gA]; omega
  have hB : ySz (gB G k₀ q₀ cs j) ≤ Qb + 1 := by
    rcases j with _ | j
    · simp [gB, ySz, maxEntry]
    · simp only [gB]
      rcases h : cs[j]? with _ | c
      · simp [ySz, maxEntry]
      · have := hQ c (List.mem_of_getElem? h)
        simp only; omega
  have := ySz_lpU x (gA G k₀ q₀ x cs hd z j) (gB G k₀ q₀ cs j)
  have := hO j hj
  simp only [gU]; omega

/-- The time bound of the switch in a round. -/
noncomputable def swT (Ks : ℕ) (cs : List RCall) (j : ℕ) : ℕ :=
  match cs[j]? with
  | some c => Ks * (2 * realT G k₀ q₀ c + 8 * dFix + 1)
  | none => 0

set_option maxHeartbeats 2000000 in
/-- **The composite halts if all rounds fit.** -/
theorem resolve_run {Gp sw P0 : Program} {sI D Ks KL cG aG : ℕ}
    (hsw : Sw5Spec sw Ks D pSh pFt pCo pCa pSt) (hP0 : LoopSpec P0 Gp sw KL) (hD : sI + 4 ≤ D)
    {P Q : ℕ} {s : Bool} (hk : 1 ≤ k₀)
    (hgl : RGlueAt G k₀ q₀ Gp sI (2 * D + 20) eSh eFt eCo eCa eSt cG aG P Q s)
    {Qb Bnd : ℕ}
    (hQ : ∀ c ∈ rcalls G P Q s k₀ q₀, ySz (rQ G k₀ q₀ c) + ySz (rY G k₀ q₀ c) ≤ Qb)
    (hz : ySz (zOut G k₀ q₀ P Q s) ≤ Qb) (hx : ySz (xIn G k₀ q₀ P Q s) ≤ Qb)
    (hB1 : cG * (8 * (cG * (ySz (xIn G k₀ q₀ P Q s) + (n + 1) *
        (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ aG) + Qb) + 16) ^
          eGl + 8 * (cG * (ySz (xIn G k₀ q₀ P Q s) + (n + 1) *
        (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ aG) + Qb) + 16 ≤ Bnd)
    (hB2 : ∀ c ∈ rcalls G P Q s k₀ q₀, 2 * realT G k₀ q₀ c + 10 * dFix + 2 ≤ Bnd)
    (hB3 : bigAll k₀ q₀ Ks + dFix ≤ Bnd)
    {w : ℕ} (hreg : ∀ i ≤ 2 * (rcalls G P Q s k₀ q₀).length + 2,
      Bnd * 2 ^ (2 * D + 20) ≤ 2 ^ lpV w i)
    (hw : 8 ≤ w) (hxw : (xIn G k₀ q₀ P Q s).length < 2 ^ (w - 1))
    (hsz : (2 * (rcalls G P Q s k₀ q₀).length + 3) ^ 2 ≤ lpCap w) :
    ∃ t ≤ KL * (rBound G k₀ q₀ P Q s cG aG +
        ∑ j ∈ Finset.range (rcalls G P Q s k₀ q₀).length, swT G k₀ q₀ Ks (rcalls G P Q s k₀ q₀) j +
        2 * (rcalls G P Q s k₀ q₀).length + 1 + (zOut G k₀ q₀ P Q s).length + 1),
      RunsTo w P0 (xIn G k₀ q₀ P Q s) (zOut G k₀ q₀ P Q s) t := by
  obtain ⟨hd, tG, hhd, hsum, hhdB, hrd⟩ := hgl.rounds
  set x := xIn G k₀ q₀ P Q s with hxd
  set cs := rcalls G P Q s k₀ q₀ with hcsd
  set z := zOut G k₀ q₀ P Q s with hzd
  set R := cs.length with hRd
  set X := ySz x with hXd
  set Hb := cG * (X + (n + 1) *
    (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ aG) with hHb
  have hX1 : 1 ≤ X := by simp only [hXd, ySz]; omega
  have hBnd : 1 ≤ Bnd := by omega
  have hQB : Qb + 1 ≤ Bnd := by omega
  have hreg' : ∀ i ≤ 2 * R + 2, 2 * D + 20 ≤ lpV w i ∧ Bnd ≤ 2 ^ (lpV w i - (2 * D + 20)) :=
    fun i hi => le_pow_sub (hreg i hi) hBnd
  have hsize : ∀ i ≤ 2 * R + 2, lpSize w i ≠ 0 := fun i hi =>
    rlpSize_ne (le_trans (Nat.pow_le_pow_left (by omega) 2) hsz)
  have hcB : cBig k₀ q₀ ^ (eSum + 1) ≤ Bnd := by unfold bigAll at hB3; omega
  have hKs : Ks ≤ Bnd := by unfold bigAll at hB3; omega
  have hsz' := fun j hj => round_sz G k₀ q₀ (x := x) (z := z) (cs := cs) (hd := hd) (Hb := Hb)
    (Qb := Qb) hhdB hQ hz hx (j := j) hj
  have hE1 : 1 ≤ eGl := by unfold eGl; omega
  -- the runs of the glue program
  have hG : ∀ j, ∃ t, j ≤ R → t ≤ tG j ∧
      RunsTo (lpV w (2 * j)) Gp (gU G k₀ q₀ x cs hd z j) (gOut G k₀ q₀ cs hd z j) t ∧
      (∀ c, cs[j]? = some c →
        RGuard G k₀ q₀ eSh eFt eCo eCa eSt X (lpV w (2 * j)) (2 * D + 20) c) := by
    intro j
    by_cases hj : j ≤ R
    swap
    · exact ⟨0, fun h => absurd h hj⟩
    obtain ⟨hv, hBv⟩ := hreg' (2 * j) (by omega)
    have hs := hsz' j hj
    have hpow : cG * (ySz (gU G k₀ q₀ x cs hd z j) + ySz (gOut G k₀ q₀ cs hd z j) + X) ^ eGl ≤
        cG * (8 * (Hb + Qb) + 16) ^ eGl := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hs _)
    have p1 : 2 ^ (lpV w (2 * j) - (2 * D + 20)) ≤ 2 ^ (lpV w (2 * j) - sI) :=
      two_pow_mono (by omega)
    have hent : ∀ e ∈ gU G k₀ q₀ x cs hd z j, e < 2 ^ (lpV w (2 * j) - sI) := by
      intro e he
      have := lt_ySz he
      omega
    have hfit : cG * (ySz (gU G k₀ q₀ x cs hd z j) + ySz (gOut G k₀ q₀ cs hd z j) + X) ^ eGl ≤
        2 ^ (lpV w (2 * j) - (2 * D + 20)) := by omega
    obtain ⟨t, ht, hr⟩ := (hrd j hj _ (by omega) hent).2 hfit
    obtain ⟨-, -, hg⟩ := (hrd j hj _ (by omega) hent).1 _ _ hr
    exact ⟨t, fun _ => ⟨ht, hr, hg⟩⟩
  choose tG' htG using hG
  -- the runs of the switch
  have hP : ∀ j, ∃ t, j < R → t ≤ swT G k₀ q₀ Ks cs j ∧
      RunsTo (lpV w (2 * j + 1)) sw (lpQ (gA G k₀ q₀ x cs hd z (j + 1)))
        (gB G k₀ q₀ cs (j + 1)) t ∧ (gB G k₀ q₀ cs (j + 1)).length ≤ lpCap w := by
    intro j
    by_cases hj : j < R
    swap
    · exact ⟨0, fun h => absurd h hj⟩
    obtain ⟨c, hc⟩ : ∃ c, cs[j]? = some c := ⟨cs[j], List.getElem?_eq_getElem hj⟩
    have hcm : c ∈ cs := List.mem_of_getElem? hc
    have hgo : gOut G k₀ q₀ cs hd z j = hd j ++ rQ G k₀ q₀ c := by simp only [gOut, hc]
    have hA : gA G k₀ q₀ x cs hd z (j + 1) = hd j ++ rQ G k₀ q₀ c := by simp only [gA, hgo]
    have hB' : gB G k₀ q₀ cs (j + 1) = rY G k₀ q₀ c := by simp only [gB, hc]
    obtain ⟨-, -, hlen⟩ := hhd j hj
    rw [hA, lpQ_append hlen, hB']
    obtain ⟨-, -, hg⟩ := htG j hj.le
    have hg := hg c hc
    obtain ⟨hv1, hBv⟩ := hreg' (2 * j) (by omega)
    have hvv : lpV w (2 * j) - 2 ≤ lpV w (2 * j + 1) := lpV_succ_ge w (2 * j)
    set v := lpV w (2 * j) with hv
    set v' := lpV w (2 * j + 1) with hv'
    have h2 := hB2 c hcm
    have hQc := hQ c hcm
    obtain ⟨yA', yB', yC', yE', yF', tA, tB, tC, tE, tF, hrA, hrB, hrC, hrE, hrF, hy, ht⟩ :=
      slots_run hk hcm hg (wA := v' - 8 - 2 * D) (wB := v' - 10 - 2 * D) (wC := v' - 12 - 2 * D)
        (wE := v' - 6 - D) (wF := v' - 8 - D) (by omega) (by omega) (by omega) (by omega)
        (by omega) (Or.inr (le_trans hcB hBv)) (by omega) (by omega)
    have oA := runsTo_out_length hrA
    have oB := runsTo_out_length hrB
    have oC := runsTo_out_length hrC
    have oE := runsTo_out_length hrE
    have oF := runsTo_out_length hrF
    have pw : ∀ m, v - (2 * D + 20) ≤ m → 2 ^ (v - (2 * D + 20)) ≤ 2 ^ m := fun m h =>
      two_pow_mono h
    have cap : ∀ m, v - (2 * D + 20) ≤ m → realT G k₀ q₀ c + 4 * dFix + 1 ≤ 2 ^ m := fun m h => by
      have := pw m h; omega
    have cA : yA'.length ≤ catLim (v' - 8 - D) (D + 2) :=
      rle_catLim (by omega) (le_trans (by omega) (cap _ (by omega)))
    have cB : yB'.length ≤ catLim (v' - 10 - D) (D + 2) :=
      rle_catLim (by omega) (le_trans (by omega) (cap _ (by omega)))
    have cC : yC'.length ≤ catLim (v' - 12 - D) (D + 2) :=
      rle_catLim (by omega) (le_trans (by omega) (cap _ (by omega)))
    have cE : yE'.length ≤ catLim (v' - 6) (D + 2) :=
      rle_catLim (by omega) (le_trans (by omega) (cap _ (by omega)))
    have cF : yF'.length ≤ catLim (v' - 8) (D + 2) :=
      rle_catLim (by omega) (le_trans (by omega) (cap _ (by omega)))
    have hql : (sw5In (qA c) (qB G k₀ q₀ c) (qC c) (qE c) (qF G k₀ q₀ c)).length <
        2 ^ (v' - 14 - 2 * D) := by
      have h1 := length_lt_ySz (rQ G k₀ q₀ c)
      have := pw (v' - 14 - 2 * D) (by omega)
      unfold rQ at h1 hQc
      omega
    obtain ⟨t, ht', hr⟩ := (hsw v' _ _ _ _ _ (le_trans hKs (le_trans hBv (pw _ (by omega)))) hql
      (by omega)).1 yA' yB' yC' yE' yF' tA tB tC tE tF hrA hrB hrC hrE hrF cA cB cC cE cF
    rw [hy] at hr
    refine ⟨t, fun _ => ⟨?_, hr, ?_⟩⟩
    · simp only [swT, hc]
      refine le_trans ht' (Nat.mul_le_mul_left _ ?_)
      omega
    · have hy' : (rY G k₀ q₀ c).length ≤ 2 ^ v' := by
        rw [← hy]; simp only [List.length_append]
        have := cap v' (by omega)
        omega
      exact le_trans hy' (rpow_lpV_le w _)
  choose tP' htP using hP
  -- the calls of the script
  have hcall : ∀ j < R, CallOK w Gp sw x (gA G k₀ q₀ x cs hd z) (gB G k₀ q₀ cs) tG' tP' j := by
    intro j hj
    obtain ⟨hne, hh0, -⟩ := hhd j hj
    obtain ⟨c, hc⟩ : ∃ c, cs[j]? = some c := ⟨cs[j], List.getElem?_eq_getElem hj⟩
    have hgo : gOut G k₀ q₀ cs hd z j = hd j ++ rQ G k₀ q₀ c := by simp only [gOut, hc]
    have hA : gA G k₀ q₀ x cs hd z (j + 1) = gOut G k₀ q₀ cs hd z j := rfl
    obtain ⟨-, hrG, -⟩ := htG j hj.le
    obtain ⟨-, hrP, hcap⟩ := htP j hj
    obtain ⟨hv, hBv⟩ := hreg' (2 * j) (by omega)
    have hol : (gOut G k₀ q₀ cs hd z j).length ≤ lpCap w := by
      have := length_lt_ySz (gOut G k₀ q₀ cs hd z j)
      have := hsz' j hj.le
      have h1 : 2 ^ (lpV w (2 * j) - (2 * D + 20)) ≤ 2 ^ lpV w (2 * j) := two_pow_mono (by omega)
      exact le_trans (by omega) (rpow_lpV_le w (2 * j))
    refine ⟨hsize _ (by omega), hrG, fun o t h => (runsTo_unique h hrG).1, ?_, ?_, ?_,
      hsize _ (by omega), hrP, fun r t h => (runsTo_unique h hrP).1, hcap⟩
    · rw [hA, hgo]; simp [hne]
    · rw [hA, hgo]
      rcases hhj : hd j with _ | ⟨a, l⟩
      · exact absurd hhj hne
      · rw [hhj] at hh0; simpa using hh0
    · rw [hA]; exact hol
  -- the last round
  have hdone : DoneOK w Gp x (gA G k₀ q₀ x cs hd z) (gB G k₀ q₀ cs) tG' R z := by
    have hgo : gOut G k₀ q₀ cs hd z R = 0 :: z := by
      simp only [gOut, List.getElem?_eq_none (le_refl R)]
    obtain ⟨-, hrG, -⟩ := htG R le_rfl
    rw [hgo] at hrG
    obtain ⟨hv, hBv⟩ := hreg' (2 * R) (by omega)
    have hol : (0 :: z).length ≤ lpCap w := by
      have := length_lt_ySz (gOut G k₀ q₀ cs hd z R)
      have := hsz' R le_rfl
      rw [hgo] at *
      have h1 : 2 ^ (lpV w (2 * R) - (2 * D + 20)) ≤ 2 ^ lpV w (2 * R) := two_pow_mono (by omega)
      exact le_trans (by omega) (rpow_lpV_le w (2 * R))
    exact ⟨hsize _ (by omega), hrG, fun o t h => (runsTo_unique h hrG).1, hol⟩
  obtain ⟨t, ht, hr⟩ := loop_script_run (fun w x hw hx => (hP0 w x hw hx).1) hw hxw
    (A := gA G k₀ q₀ x cs hd z) (B := gB G k₀ q₀ cs) rfl rfl hcall hdone
  refine ⟨t, le_trans ht (Nat.mul_le_mul_left _ ?_), hr⟩
  have hsum' : scriptTime tG' tP' R 0 ≤ (∑ j ∈ Finset.range (R + 1), tG j) +
      ∑ j ∈ Finset.range R, swT G k₀ q₀ Ks cs j + 2 * R + 1 := by
    unfold scriptTime
    rw [← Finset.range_eq_Ico, Finset.sum_range_succ]
    have h1 : ∑ i ∈ Finset.range R, (tG' i + tP' i + 2) ≤
        ∑ i ∈ Finset.range R, (tG i + swT G k₀ q₀ Ks cs i + 2) := by
      apply Finset.sum_le_sum
      intro i hi
      have hi' := Finset.mem_range.1 hi
      have := (htG i hi'.le).1
      have := (htP i hi').1
      omega
    have h3 : ∑ i ∈ Finset.range R, (tG i + swT G k₀ q₀ Ks cs i + 2) =
        ∑ i ∈ Finset.range R, tG i + ∑ i ∈ Finset.range R, swT G k₀ q₀ Ks cs i + 2 * R := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
        smul_eq_mul]
      ring
    have := (htG R le_rfl).1
    omega
  omega

end Lax185574Proofs.ResolveRam
