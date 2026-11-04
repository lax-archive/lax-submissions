import Lax185574Proofs.ResolveRam.SlotAnswer
import Lax185574Proofs.ResolveRam.LoopTools

/-!
Soundness of the composite of lem:resolve-lift: the loop driver of a
glue program as in `RGlueAt` and the callee `switch5` of the five
callees.

The proof follows the calls with `inv_script_sound`. The invariant of
round `j` is that the input of the glue program has entries below
`2 ^ (v - sI)` at the word length `v` of the round. In a round with a
call, the guard of the call and the room of the regions give that the
query fits the switch and that the five runs of the slots give the
answer of the call (`slots_answer`). The room comes from one of two
cases (`hcase`): either the input is at least as large as the constants
`bigAll`, and the guard itself gives room, or every region of the
driver up to the last round has room for the constants.
-/

namespace Lax185574Proofs.ResolveRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ScatterTypes
open Lax185574.ResolveLift Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo
open Lax185574Proofs.Words Lax185574Proofs.Simulate Lax185574Proofs.RamSim Lax185574Proofs.RamCat
open Lax185574Proofs.RamExec

/-- The specification of the five-callee switch `p` with constant `K`,
as given by `switch5`. -/
def Sw5Spec (p : Program) (K D : ℕ) (A B C E F : Program) : Prop :=
  ∀ (w : ℕ) (qA qB qC qE qF : List ℕ), K ≤ 2 ^ (w - 12 - 2 * D) →
      (sw5In qA qB qC qE qF).length < 2 ^ (w - 14 - 2 * D) → 2 * D + 18 ≤ w →
      (∀ yA yB yC yE yF tA tB tC tE tF,
        RunsTo (w - 8 - 2 * D) A qA yA tA → RunsTo (w - 10 - 2 * D) B qB yB tB →
        RunsTo (w - 12 - 2 * D) C qC yC tC → RunsTo (w - 6 - D) E qE yE tE →
        RunsTo (w - 8 - D) F qF yF tF →
        yA.length ≤ catLim (w - 8 - D) (D + 2) → yB.length ≤ catLim (w - 10 - D) (D + 2) →
        yC.length ≤ catLim (w - 12 - D) (D + 2) → yE.length ≤ catLim (w - 6) (D + 2) →
        yF.length ≤ catLim (w - 8) (D + 2) →
        ∃ t ≤ K * (tA + tB + tC + tE + tF + yA.length + yB.length + yC.length + yE.length +
            yF.length + 1),
          RunsTo w p (sw5In qA qB qC qE qF) (yA ++ yB ++ yC ++ yE ++ yF) t) ∧
      (∀ o T, RunsTo w p (sw5In qA qB qC qE qF) o T →
        ∃ yA yB yC yE yF tA tB tC tE tF,
          RunsTo (w - 8 - 2 * D) A qA yA tA ∧ RunsTo (w - 10 - 2 * D) B qB yB tB ∧
          RunsTo (w - 12 - 2 * D) C qC yC tC ∧ RunsTo (w - 6 - D) E qE yE tE ∧
          RunsTo (w - 8 - D) F qF yF tF ∧ o = yA ++ yB ++ yC ++ yE ++ yF ∧
          yA.length ≤ catLim (w - 8 - D) (D + 2) ∧ yB.length ≤ catLim (w - 10 - D) (D + 2) ∧
          yC.length ≤ catLim (w - 12 - D) (D + 2) ∧ yE.length ≤ catLim (w - 6) (D + 2) ∧
          yF.length ≤ catLim (w - 8) (D + 2))

/-- The constants that the regions must exceed. -/
noncomputable def bigAll (k₀ q₀ Ks : ℕ) : ℕ :=
  cBig k₀ q₀ ^ (eSum + 1) + fixBig + Ks + qA0.length + qB0.length + qC0.length + qE0.length +
    qF0.length + 1

variable {n : ℕ} (G : PartialGraph (Fin n)) (k₀ q₀ : ℕ)

theorem rQ_length (Ks : ℕ) (c : RCall) :
    (rQ G k₀ q₀ c).length ≤ 6 + (realQ G k₀ q₀ c).length + bigAll k₀ q₀ Ks := by
  have hl : ∀ qA qB qC qE qF : List ℕ, (sw5In qA qB qC qE qF).length =
      6 + qA.length + qB.length + qC.length + qE.length + qF.length := by
    intro qA qB qC qE qF
    simp only [sw5In, swIn, List.length_append, List.length_cons, List.length_nil]; omega
  unfold bigAll
  cases c <;> simp only [rQ, hl, qA, qB, qC, qE, qF, realQ] <;> omega

theorem guard_base {u : List ℕ} {e X N : ℕ} (hX : 1 ≤ X)
    (h : (u.length + maxEntry u + 1 + X) ^ (e + 1) ≤ N) :
    u.length + maxEntry u + 1 + X ≤ N ∧ 2 ≤ N := by
  have : u.length + maxEntry u + 1 + X ≤ (u.length + maxEntry u + 1 + X) ^ (e + 1) :=
    Nat.le_self_pow (by omega) _
  omega

theorem two_le_pow {m : ℕ} (h : 2 ≤ 2 ^ m) : 1 ≤ m := by
  rcases m with _ | m
  · simp at h
  · omega

set_option maxHeartbeats 1000000 in
/-- **Soundness of the composite.** -/
theorem resolve_sound {Gp sw P0 : Program} {sI D Ks KL cG aG : ℕ}
    (hsw : Sw5Spec sw Ks D pSh pFt pCo pCa pSt) (hP0 : LoopSpec P0 Gp sw KL) (hD : sI + 4 ≤ D)
    {P Q : ℕ} {s : Bool} (hk : 1 ≤ k₀)
    (hgl : RGlueAt G k₀ q₀ Gp sI (2 * D + 20) eSh eFt eCo eCa eSt cG aG P Q s)
    {w : ℕ} (hw : 8 ≤ w) (hx : (xIn G k₀ q₀ P Q s).length < 2 ^ (w - 1))
    (h0 : ySz (xIn G k₀ q₀ P Q s) * 2 ^ (2 * D + 20) ≤ 2 ^ lpV w 0)
    (hcase : bigAll k₀ q₀ Ks ≤ ySz (xIn G k₀ q₀ P Q s) ∨
      ∀ i ≤ 2 * (rcalls G P Q s k₀ q₀).length + 2,
        bigAll k₀ q₀ Ks * 2 ^ (2 * D + 30) ≤ 2 ^ lpV w i ∧
          ySz (xIn G k₀ q₀ P Q s) * 2 ^ (2 * D + 20) ≤ 2 ^ lpV w i) :
    ∀ z t, RunsTo w P0 (xIn G k₀ q₀ P Q s) z t → z = zOut G k₀ q₀ P Q s := by
  have hback : ∀ (w : ℕ) (x : List ℕ), 8 ≤ w → x.length < 2 ^ (w - 1) →
      ∀ z t, RunsTo w P0 x z t → ∃ T, LoopTrace w Gp sw x 0 (lpA0 x) [] z T :=
    fun w x hw hx => (hP0 w x hw hx).2
  obtain ⟨hd, tG, hhd, -, -, hrd⟩ := hgl.rounds
  set x := xIn G k₀ q₀ P Q s with hxd
  set cs := rcalls G P Q s k₀ q₀ with hcsd
  set z := zOut G k₀ q₀ P Q s with hzd
  set R := cs.length with hRd
  set X := ySz x with hXd
  set Bg := bigAll k₀ q₀ Ks with hBg
  have hX1 : 1 ≤ X := by simp only [hXd, ySz]; omega
  have hxX : ∀ e ∈ x, e < X := fun e he => by
    have := le_maxEntry he; simp only [hXd, ySz]; omega
  have hBg1 : 1 ≤ Bg := by simp only [hBg, bigAll]; omega
  have hcB : cBig k₀ q₀ ^ (eSum + 1) ≤ Bg := by simp only [hBg, bigAll]; omega
  have hfB : fixBig ≤ Bg := by simp only [hBg, bigAll]; omega
  have hKB : Ks ≤ Bg := by simp only [hBg, bigAll]; omega
  -- a number below `X · 2^(2D+20) ≤ 2^v` is below `2^(v - sI)`
  have hfit : ∀ v, X * 2 ^ (2 * D + 20) ≤ 2 ^ v → sI ≤ v ∧ X ≤ 2 ^ (v - sI) := by
    intro v h
    obtain ⟨h1, h2⟩ := le_pow_sub h hX1
    exact ⟨by omega, le_trans h2 (two_pow_mono (by omega))⟩
  refine inv_script_sound hback hw hx (A := gA G k₀ q₀ x cs hd z) (B := gB G k₀ q₀ cs)
    (I := fun j => sI ≤ lpV w (2 * j) ∧
      ∀ e ∈ gU G k₀ q₀ x cs hd z j, e < 2 ^ (lpV w (2 * j) - sI)) (R := R)
    rfl rfl ?_ ?_ ?_
  · -- the first round
    obtain ⟨hs0, hX0⟩ := hfit _ h0
    refine ⟨hs0, ?_⟩
    show ∀ e ∈ lpU x (lpA0 x) [], e < 2 ^ (lpV w 0 - sI)
    refine lpU_lt (by positivity) (fun e he => lt_of_lt_of_le (hxX e he) hX0) (fun e he => ?_)
      (by simp) (by simpa using Nat.two_pow_pos _)
    simp only [lpA0, List.mem_cons, List.not_mem_nil, or_false] at he
    have : x.length < X := by simp only [hXd, ySz]; omega
    rcases he with rfl | rfl | rfl <;> omega
  · -- the rounds with a call
    intro j hj ⟨hsv, hI⟩ o t hrun
    have hvv := lpV_succ_ge w (2 * j)
    have hvv' : lpV w (2 * j + 1) - 2 ≤ lpV w (2 * j + 2) := lpV_succ_ge w (2 * j + 1)
    set v := lpV w (2 * j) with hv
    set v' := lpV w (2 * j + 1) with hv'
    set v'' := lpV w (2 * j + 2) with hv''
    obtain ⟨ho, hoe, hog⟩ := (hrd j hj.le v hsv hI).1 o t hrun
    obtain ⟨c, hc⟩ : ∃ c, cs[j]? = some c := ⟨cs[j], List.getElem?_eq_getElem hj⟩
    have hcm : c ∈ cs := List.mem_of_getElem? hc
    have hgo : gOut G k₀ q₀ cs hd z j = hd j ++ rQ G k₀ q₀ c := by simp only [gOut, hc]
    obtain ⟨hne, hh0, hlen⟩ := hhd j hj
    have hA : gA G k₀ q₀ x cs hd z (j + 1) = hd j ++ rQ G k₀ q₀ c := by simp only [gA, hgo]
    have hg := hog c hc
    obtain ⟨hgb, hg2⟩ := guard_base hX1 hg
    have hv1 := two_le_pow hg2
    -- the room of this round
    have hBv : Bg ≤ 2 ^ (v - (2 * D + 20)) := by
      rcases hcase with h | h
      · omega
      · obtain ⟨h1, -⟩ := h (2 * j) (by omega)
        obtain ⟨-, h2⟩ := le_pow_sub h1 hBg1
        exact le_trans h2 (two_pow_mono (by omega))
    have hxn : ∀ e ∈ x, e < 2 ^ (v'' - sI) := by
      rcases hcase with h | h
      · intro e he
        refine lt_of_lt_of_le (hxX e he) (le_trans (by omega : X ≤ 2 ^ (v - (2 * D + 20)))
          (two_pow_mono (by omega)))
      · obtain ⟨-, h2⟩ := h (2 * j + 2) (by omega)
        obtain ⟨-, h3⟩ := hfit _ h2
        exact fun e he => lt_of_lt_of_le (hxX e he) h3
    have hBO : BigOK k₀ q₀ X (v - (2 * D + 20)) := Or.inr (le_trans hcB hBv)
    refine ⟨ho, ?_, fun r t' hr => ?_⟩
    · rw [hA]
      rcases hhj : hd j with _ | ⟨a, l⟩
      · exact absurd hhj hne
      · rw [hhj] at hh0; simpa using hh0
    rw [ho, hgo, lpQ_append hlen] at hr
    -- the switch
    have hql := rQ_length G k₀ q₀ Ks c
    have e16 : 2 ^ (v - (2 * D + 20)) * 16 ≤ 2 ^ (v' - 14 - 2 * D) := by
      rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]; exact two_pow_mono (by omega)
    have eK : 2 ^ (v - (2 * D + 20)) ≤ 2 ^ (v' - 12 - 2 * D) := two_pow_mono (by omega)
    obtain ⟨yA', yB', yC', yE', yF', tA, tB, tC, tE, tF, hrA, hrB, hrC, hrE, hrF, hr', lA, lB, lC,
      lE, lF⟩ := (hsw v' _ _ _ _ _ (by omega) (lt_of_le_of_lt hql (by omega)) (by omega)).2 r t' hr
    have hY := slots_answer G hk hcm hg (by omega) (by omega) (by omega) (by omega) (by omega) hBO
      (le_trans hfB hBv) hrA hrB hrC hrE hrF
    have hB' : gB G k₀ q₀ cs (j + 1) = rY G k₀ q₀ c := by simp only [gB, hc]
    refine ⟨by rw [hB', hr', hY], by rw [show 2 * (j + 1) = 2 * j + 2 by ring]; omega, ?_⟩
    -- the invariant of the next round
    show ∀ e ∈ lpU x (gA G k₀ q₀ x cs hd z (j + 1)) (gB G k₀ q₀ cs (j + 1)), e < 2 ^ (v'' - sI)
    rw [show gA G k₀ q₀ x cs hd z (j + 1) = o by rw [ho]; rfl, hB', ← hY]
    obtain ⟨M, hM⟩ : ∃ M, M = 2 ^ (v' - 8 - D) := ⟨_, rfl⟩
    have k1 : 2 ^ (v - sI - 4) ≤ 2 ^ (v'' - sI) := two_pow_mono (by omega)
    have k8 : M * 8 ≤ 2 ^ (v'' - sI) := by
      rw [hM, show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_add]; exact two_pow_mono (by omega)
    have kA : 2 ^ (v' - 8 - 2 * D) ≤ M := by rw [hM]; exact two_pow_mono (by omega)
    have kB : 2 ^ (v' - 10 - 2 * D) ≤ M := by rw [hM]; exact two_pow_mono (by omega)
    have kC : 2 ^ (v' - 12 - 2 * D) ≤ M := by rw [hM]; exact two_pow_mono (by omega)
    have kE : 2 ^ (v' - 6 - D) ≤ M * 4 := by
      rw [hM, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; exact two_pow_mono (by omega)
    have kF : 2 ^ (v' - 8 - D) ≤ M := by rw [hM]
    have cA := le_trans lA (le_trans (catLim_le _ _) (two_pow_mono (show v' - 8 - D - (D + 2) ≤ v' - 8 - D by omega)))
    have cB := le_trans lB (le_trans (catLim_le _ _) (two_pow_mono (show v' - 10 - D - (D + 2) ≤ v' - 8 - D by omega)))
    have cC := le_trans lC (le_trans (catLim_le _ _) (two_pow_mono (show v' - 12 - D - (D + 2) ≤ v' - 8 - D by omega)))
    have cE := le_trans lE (le_trans (catLim_le _ _) (two_pow_mono (show v' - 6 - (D + 2) ≤ v' - 8 - D by omega)))
    have cF := le_trans lF (le_trans (catLim_le _ _) (two_pow_mono (show v' - 8 - (D + 2) ≤ v' - 8 - D by omega)))
    rw [← hM] at cA cB cC cE cF
    have oA := runsTo_out_lt hrA
    have oB := runsTo_out_lt hrB
    have oC := runsTo_out_lt hrC
    have oE := runsTo_out_lt hrE
    have oF := runsTo_out_lt hrF
    refine lpU_lt (by positivity) hxn (fun e he => lt_of_lt_of_le (hoe e he) k1) (fun e he => ?_) ?_
    · simp only [List.mem_append] at he
      rcases he with ((((he | he) | he) | he) | he)
      · have := oA e he; omega
      · have := oB e he; omega
      · have := oC e he; omega
      · have := oE e he; omega
      · have := oF e he; omega
    · simp only [List.length_append]; omega
  · -- the last round
    intro ⟨hsv, hI⟩ o t hrun
    obtain ⟨ho, -, -⟩ := (hrd R le_rfl _ hsv hI).1 o t hrun
    rw [ho]
    simp only [gOut, List.getElem?_eq_none (le_refl R)]

end Lax185574Proofs.ResolveRam
