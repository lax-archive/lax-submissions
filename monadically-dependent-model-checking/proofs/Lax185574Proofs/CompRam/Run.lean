import Lax185574Proofs.CompRam.Sound
import Lax185574Proofs.LoopScript

/-!
The composite of lem:compose halts within time.

`SizeOK m L M`: along the script, the inputs and outputs of the rounds up
to `m` have length at most `L` and entries at most `M + L`. If every
region of the driver up to round `m` has room for the constant `bigR`
of these sizes, the composite halts with the word of the far composition
within `KL ((m + 1) roundT + L + 1)` steps (`comp_run`), where `roundT`
bounds the cost of one round of the glue and one call of the switch.
-/

namespace Lax185574Proofs.CompRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574Proofs.Words Lax185574Proofs.TreeAlgo
open Lax185574.TypeTrees Lax185574.PartialGraphs Lax185574Proofs.Simulate Lax185574Proofs.RamSim
open Lax185574Proofs.MC (SwSpec LoopSpec two_pow_mono le_pow_sub)
open Lax185574Proofs.RamCat Lax185574Proofs.RamExec

/-- The sizes along the script up to round `m`. -/
structure SizeOK {n : ℕ} (G : PartialGraph (Fin n)) (k q : ℕ) {l1 l2 : ℕ} (u₁ : Fin l1 → Fin n)
    (u₂ : Fin l2 → Fin n) (m L M : ℕ) : Prop where
  inL : ∀ j ≤ m, (uT G k q u₁ u₂ j).length ≤ L
  outL : ∀ j ≤ m, (aT G k q u₁ u₂ (j + 1)).length ≤ L
  ent : ∀ j ≤ m, ∀ e ∈ uT G k q u₁ u₂ j ++ aT G k q u₁ u₂ (j + 1), e ≤ M + L

/-- The room that every region needs. -/
noncomputable def bigR (eR eS eC C A Ks sQ cG E L M : ℕ) : ℕ :=
  2 ^ (sQ + 20) * (cG * (3 * L + M + 1) ^ E + crunBig eR eS eC C A + C * (L + 1) ^ A + Ks + L + M + 1)

/-- The cost of one round. -/
noncomputable def roundT (eR eS eC C A Ks cG L : ℕ) : ℕ :=
  cG * (2 * L + 1) ^ 2 + Ks * (C * (L + 1) ^ A + crunBig eR eS eC C A + L + 1) + 2

theorem maxEntry_le_of {l : List ℕ} {B : ℕ} (h : ∀ x ∈ l, x ≤ B) : maxEntry l ≤ B := by
  induction l with
  | nil => simp [maxEntry]
  | cons a l ih =>
    simp only [maxEntry, List.foldr_cons] at ih ⊢
    exact max_le (h a (by simp)) (ih fun x hx => h x (by simp [hx]))

theorem catLim_ge {v E : ℕ} (h : E ≤ v) : 2 ^ (v - E) - 1 ≤ catLim v E := by
  unfold catLim
  have hv : 2 ^ v = 2 ^ (v - E) * 2 ^ E := by rw [← pow_add]; congr 1; omega
  rw [hv]
  have hE : 0 < 2 ^ E := by positivity
  have hq : 0 < 2 ^ (v - E) := by positivity
  generalize 2 ^ E = P at hE ⊢
  generalize 2 ^ (v - E) = Q at hq ⊢
  rw [Nat.le_div_iff_mul_le hE, Nat.sub_mul]
  have : P ≤ Q * P := Nat.le_mul_of_pos_left _ hq
  omega

theorem scriptTime_le {tG tP : ℕ → ℕ} {R Tg Tp : ℕ} (hG : ∀ j ≤ R, tG j ≤ Tg)
    (hP : ∀ j < R, tP j ≤ Tp) : scriptTime tG tP R 0 ≤ R * (Tg + Tp + 2) + Tg + 1 := by
  unfold scriptTime
  have h1 : (∑ i ∈ Finset.Ico 0 R, (tG i + tP i + 2)) ≤ ∑ _i ∈ Finset.Ico 0 R, (Tg + Tp + 2) :=
    Finset.sum_le_sum fun i hi => by
      have := (Finset.mem_Ico.1 hi).2
      have := hG i (by omega); have := hP i (by omega); omega
  rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul, Nat.sub_zero] at h1
  have := hG R le_rfl
  omega

/-- **The composite halts within time.** -/
theorem comp_run {pR pS pC Gp sw p : Program} {eR eS eC K C A Ks KL D sI sQ cG E : ℕ}
    (hR : CRun pR pS pC eR eS eC K C A) (hK1 : 1 ≤ K) (hsw : SwSpec sw Ks D pR pS pC)
    (hp : LoopSpec p Gp sw KL) (hG : GlueSpec Gp sI sQ eR eS eC cG E) (hD : sI + 4 ≤ D)
    (hQ : D + 20 ≤ sQ) {n : ℕ} {G : PartialGraph (Fin n)} {k q l1 l2 : ℕ}
    {u₁ : Fin l1 → Fin n} {u₂ : Fin l2 → Fin n} (hI : Inst G k q u₁ u₂) (hK : k + q + 1 ≤ K)
    {m : ℕ} {z : List ℕ} (hend : trT G k q u₁ u₂ m = .done z) (hreach : Reached G k q u₁ u₂ m)
    (hcall : ∀ j < m, ∃ g S q', trT G k q u₁ u₂ j = .call (g :: S) q' ∧
        Fits g.ph q' ∧ Ans G q' (ansOf G q') ∧ RankLe (k + q + 1) q')
    {L M : ℕ} (hsz : SizeOK G k q u₁ u₂ m L M)
    {w : ℕ} (hw : 8 ≤ w) (hx : (xT G k q u₁ u₂).length < 2 ^ (w - 1))
    (hroom : ∀ i ≤ 2 * m + 2, lpSize w i ≠ 0 ∧ bigR eR eS eC C A Ks sQ cG E L M ≤ 2 ^ lpV w i)
    (hcap : L ≤ lpCap w) :
    ∃ t ≤ KL * ((m + 1) * roundT eR eS eC C A Ks cG L + L + 1),
      RunsTo w p (xT G k q u₁ u₂) z t := by
  have hS := cSound_of_cRun hR hK1
  set Cb := crunBig eR eS eC C A with hCb
  set X := cG * (3 * L + M + 1) ^ E + Cb + C * (L + 1) ^ A + Ks + L + M + 1 with hXdef
  -- the facts about region `i`
  have hreg : ∀ i ≤ 2 * m + 2, sQ + 20 ≤ lpV w i ∧ X ≤ 2 ^ (lpV w i - (sQ + 20)) := by
    intro i hi
    have h := (hroom i hi).2
    simp only [bigR] at h
    rw [Nat.mul_comm] at h
    exact le_pow_sub h (by omega)
  -- the glue rounds
  have hround : ∀ j, j ≤ m → (sI ≤ lpV w (2 * j) ∧
      ∀ e ∈ uT G k q u₁ u₂ j, e < 2 ^ (lpV w (2 * j) - sI)) ∧
      ∃ t, t ≤ cG * (2 * L + 1) ^ 2 ∧
        RunsTo (lpV w (2 * j)) Gp (uT G k q u₁ u₂ j) (aT G k q u₁ u₂ (j + 1)) t := by
    intro j hj
    obtain ⟨hv, hX⟩ := hreg (2 * j) (by omega)
    set v := lpV w (2 * j)
    have hp1 : 2 ^ (v - (sQ + 20)) ≤ 2 ^ (v - sI) := two_pow_mono (by omega)
    have hp2 : 2 ^ (v - (sQ + 20)) ≤ 2 ^ (v - sQ) := two_pow_mono (by omega)
    have hent : ∀ e ∈ uT G k q u₁ u₂ j, e < 2 ^ (v - sI) := fun e he => by
      have := hsz.ent j hj e (List.mem_append_left _ he); omega
    refine ⟨⟨by omega, hent⟩, ?_⟩
    have hRj : Reached G k q u₁ u₂ j := fun i hi => hreach i (by omega)
    have h1 := hsz.inL j hj
    have h2 := hsz.outL j hj
    have hme := maxEntry_le_of (hsz.ent j hj)
    have hc : cG * ((uT G k q u₁ u₂ j).length + (aT G k q u₁ u₂ (j + 1)).length +
        maxEntry (uT G k q u₁ u₂ j ++ aT G k q u₁ u₂ (j + 1)) + 1) ^ E ≤ 2 ^ (v - sQ) := by
      have : cG * ((uT G k q u₁ u₂ j).length + (aT G k q u₁ u₂ (j + 1)).length +
          maxEntry (uT G k q u₁ u₂ j ++ aT G k q u₁ u₂ (j + 1)) + 1) ^ E ≤
          cG * (3 * L + M + 1) ^ E := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
      omega
    obtain ⟨t, ht, hr⟩ := hG.run n G k q l1 l2 u₁ u₂ hI j hRj v (by omega) hent hc
    refine ⟨t, le_trans ht (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)), hr⟩
  -- the calls
  have hcallee : ∀ j, j < m → ∃ t, t ≤ Ks * (C * (L + 1) ^ A + Cb + L + 1) ∧
      RunsTo (lpV w (2 * j + 1)) sw (lpQ (aT G k q u₁ u₂ (j + 1))) (bT G k q u₁ u₂ (j + 1)) t ∧
      ∀ r t', RunsTo (lpV w (2 * j + 1)) sw (lpQ (aT G k q u₁ u₂ (j + 1))) r t' →
        r = bT G k q u₁ u₂ (j + 1) := by
    intro j hj
    obtain ⟨⟨hsv, hent⟩, t0, -, hr0⟩ := hround j hj.le
    have hRj : Reached G k q u₁ u₂ j := fun i hi => hreach i (by omega)
    obtain ⟨-, -, -, hqg⟩ := hG.sound n G k q l1 l2 u₁ u₂ hI j hRj _ hsv hent _ t0 hr0
    obtain ⟨g, S, q', htr, -, hA, hRk⟩ := hcall j hj
    simp only [QGuard, htr] at hqg
    obtain ⟨hv, hX⟩ := hreg (2 * j) (by omega)
    obtain ⟨hv', hX'⟩ := hreg (2 * j + 1) (by omega)
    have hvv := lpV_succ_ge w (2 * j)
    set v := lpV w (2 * j) with hvdef
    set v' := lpV w (2 * j + 1) with hv'def
    have hp2 : 2 ^ (v - (sQ + 20)) ≤ 2 ^ (v - sQ) := two_pow_mono (by omega)
    have hp3 : 2 ^ (v' - (sQ + 20)) ≤ 2 ^ (v' - 10 - D) := two_pow_mono (by omega)
    have hp4 : 2 ^ (v' - 10 - D) ≤ 2 ^ (v' - 8 - D) := two_pow_mono (by omega)
    have hp5 : 2 ^ (v' - (sQ + 20)) ≤ 2 ^ (v' - 6 - D) := two_pow_mono (by omega)
    have hp6 : 2 ^ (v' - 6 - D) ≤ 2 ^ (v' - 4 - D) := two_pow_mono (by omega)
    have hp7 : 2 ^ (v' - 8 - D) ≤ 2 ^ (v' - 6 - D) := two_pow_mono (by omega)
    have hqa := lpQ_aT htr
    have hql : (qWord q').length ≤ L := by
      have := hsz.outL j hj.le
      rw [← hqa]
      exact le_trans (by simp [lpQ]) this
    have hrl : (realQ q').length ≤ (qWord q').length := by
      rw [qWord_parts, Lax185574Proofs.MC.swIn_length_le]
      cases q' <;> simp [qR, qS, qC, realQ] <;> omega
    have hbl : (bT G k q u₁ u₂ (j + 1)).length ≤ L := by
      have := hsz.inL (j + 1) hj
      refine le_trans ?_ this
      unfold uT
      rw [lpU_nowin (by rw [aT_succ, htr]; exact getD_two_outW _ _ _)]
      simp only [lpU, List.length_append, List.length_cons]; omega
    have hrT : realT C A q' ≤ C * (L + 1) ^ A :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    obtain ⟨y, z', u, tA, tB, tC, hy, hz, hu, hyzu, htt⟩ := callee_run hR hK1 hA
      (rankLe_mono hRk hK) hqg (v := v - sQ) (wR := v' - 4 - D) (wS := v' - 6 - D)
      (wC := v' - 8 - D) (by omega) (by omega) (by omega) (by omega)
    have hb : bT G k q u₁ u₂ (j + 1) = y ++ z' ++ u := by rw [bT_call htr, hyzu]
    have hyl : y.length ≤ L ∧ z'.length ≤ L ∧ u.length ≤ L ∧ y.length + z'.length + u.length ≤ L := by
      rw [hb] at hbl; simp only [List.length_append] at hbl; omega
    have l1 := catLim_ge (v := v' - 4) (E := D + 2) (by omega)
    have l2 := catLim_ge (v := v' - 6) (E := D + 2) (by omega)
    have l3 := catLim_ge (v := v' - 8) (E := D + 2) (by omega)
    rw [show v' - 4 - (D + 2) = v' - 6 - D by omega] at l1
    rw [show v' - 6 - (D + 2) = v' - 8 - D by omega] at l2
    rw [show v' - 8 - (D + 2) = v' - 10 - D by omega] at l3
    rw [hqa, qWord_parts]
    have hsl : (swIn (qR q') (qS q') (qC q')).length < 2 ^ (v' - 10 - D) := by
      rw [← qWord_parts]; omega
    obtain ⟨t, ht, hrun⟩ := (hsw v' _ _ _ (by omega) hsl (by omega)).1 y z' u tA tB tC hy hz hu
      (by omega) (by omega) (by omega)
    refine ⟨t, le_trans ht (Nat.mul_le_mul_left _ (by omega)), by rw [hb]; exact hrun, ?_⟩
    intro r t' hr
    rw [← qWord_parts] at hr
    rw [bT_call htr]
    exact switch_ans (p := sw) (fun w' qA qB qC h1 h2 h3 o T hr' => by
        obtain ⟨y, z, u, tA, tB, tC, hy, hz, hu, ho, -⟩ := (hsw w' qA qB qC h1 h2 h3).2 o T hr'
        exact ⟨y, z, u, tA, tB, tC, hy, hz, hu, ho⟩)
      hS hA (rankLe_mono hRk hK) hqg (v := v - sQ) (w := v') (by omega) (by omega) (by omega)
      (by rw [← qWord_parts] at hsl; omega) (by omega) r t' hr
  choose! tG htG using fun j hj => (hround j hj).2
  choose! tP htP using hcallee
  have hback : ∀ (w : ℕ) (x : List ℕ), 8 ≤ w → x.length < 2 ^ (w - 1) →
      ∀ z T, LoopTrace w Gp sw x 0 (lpA0 x) [] z T → ∃ t ≤ KL * (T + z.length + 1), RunsTo w p x z t :=
    fun w x hw hx => (hp w x hw hx).1
  have hzl : (0 :: z).length ≤ L := by rw [← aT_done hend]; exact hsz.outL m le_rfl
  have hC : ∀ j < m, CallOK w Gp sw (xT G k q u₁ u₂) (aT G k q u₁ u₂) (bT G k q u₁ u₂) tG tP j := by
    intro j hj
    obtain ⟨g, S, q', htr, -⟩ := hcall j hj
    obtain ⟨⟨hsv, hent⟩, -⟩ := hround j hj.le
    have hRj : Reached G k q u₁ u₂ j := fun i hi => hreach i (by omega)
    obtain ⟨hh, hne⟩ := head_aT htr
    exact ⟨(hroom (2 * j) (by omega)).1, (htG j hj.le).2,
      fun o t h => (hG.sound n G k q l1 l2 u₁ u₂ hI j hRj _ hsv hent o t h).1, hne, hh,
      le_trans (hsz.outL j hj.le) hcap, (hroom (2 * j + 1) (by omega)).1, (htP j hj).2.1,
      (htP j hj).2.2, le_trans (by
        have := hsz.inL (j + 1) hj
        refine le_trans ?_ this
        unfold uT
        rw [lpU_nowin (by rw [aT_succ, htr]; exact getD_two_outW _ _ _)]
        simp only [lpU, List.length_append, List.length_cons]; omega) hcap⟩
  have hDn : DoneOK w Gp (xT G k q u₁ u₂) (aT G k q u₁ u₂) (bT G k q u₁ u₂) tG m z := by
    obtain ⟨⟨hsv, hent⟩, -⟩ := hround m le_rfl
    refine ⟨(hroom (2 * m) (by omega)).1, ?_, fun o t h => ?_, le_trans hzl hcap⟩
    · have := (htG m le_rfl).2
      rw [aT_done hend] at this
      exact this
    · rw [(hG.sound n G k q l1 l2 u₁ u₂ hI m hreach _ hsv hent o t h).1, aT_done hend]
  obtain ⟨t, ht, hrun⟩ := loop_script_run hback hw hx (A := aT G k q u₁ u₂) (B := bT G k q u₁ u₂)
    (tG := tG) (tP := tP) (R := m) rfl rfl hC hDn
  refine ⟨t, le_trans ht (Nat.mul_le_mul_left _ ?_), hrun⟩
  have := scriptTime_le (tG := tG) (tP := tP) (R := m) (Tg := cG * (2 * L + 1) ^ 2)
    (Tp := Ks * (C * (L + 1) ^ A + Cb + L + 1)) (fun j hj => (htG j hj).1)
    (fun j hj => (htP j hj).1)
  have hz : z.length + 1 ≤ L := by simpa using hzl
  simp only [roundT]
  generalize cG * (2 * L + 1) ^ 2 = Tg at this ⊢
  generalize Ks * (C * (L + 1) ^ A + Cb + L + 1) = Tp at this ⊢
  have e : (m + 1) * (Tg + Tp + 2) = m * (Tg + Tp + 2) + (Tg + Tp + 2) := by ring
  omega

end Lax185574Proofs.CompRam
