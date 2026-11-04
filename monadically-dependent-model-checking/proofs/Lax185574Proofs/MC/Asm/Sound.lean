import Lax185574Proofs.MC.Asm.Callees
import Lax185574Proofs.MC.Asm.InvScript

/-!
Soundness of the pipeline thread of thm:mc.

The pipeline is the loop driver with the glue program `G` and the
callee `switch ML RL Ev D`. If the glue program follows the calls of
the algorithm (`GlueAt`), then at every word length at which all regions
of the driver are large enough, every halting run of the pipeline
outputs `1` and the answer of thm:mc. Without vertices the pipeline
never halts.

The proof follows the script of the calls with `inv_script_sound`. The
invariant of round `j` is that the input of the glue program has
entries below `2 ^ (v - sI)`, at the word length `v` of the round. It
holds for the first round because the entries of `x` are small, and for
the next round because the glue program writes entries below
`2 ^ (v - sI - 4)`, the callee runs at least `D ≥ sI + 4` levels lower,
and the word length drops by at most four from one round to the next.
-/

namespace Lax185574Proofs.MC

open Lax808846.Ram Lax185574Proofs.Words Lax185574Proofs.RamSim Lax185574Proofs.Simulate
open Lax185574Proofs.RamCat Lax185574Proofs.RamExec
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.ConstructionSequences

/-- The specification of the callee `switch A B C D` with constant `K`. -/
def SwSpec (p : Program) (K D : ℕ) (A B C : Program) : Prop :=
  ∀ (w : ℕ) (qA qB qC : List ℕ), K ≤ 2 ^ (w - 8 - D) →
      (swIn qA qB qC).length < 2 ^ (w - 10 - D) → D + 14 ≤ w →
      (∀ y z u tA tB tC, RunsTo (w - 4 - D) A qA y tA → RunsTo (w - 6 - D) B qB z tB →
        RunsTo (w - 8 - D) C qC u tC → y.length ≤ catLim (w - 4) (D + 2) →
        z.length ≤ catLim (w - 6) (D + 2) → u.length ≤ catLim (w - 8) (D + 2) →
        ∃ t ≤ K * (tA + tB + tC + y.length + z.length + u.length + 1),
          RunsTo w p (swIn qA qB qC) (y ++ z ++ u) t) ∧
      (∀ o T, RunsTo w p (swIn qA qB qC) o T →
        ∃ y z u tA tB tC, RunsTo (w - 4 - D) A qA y tA ∧ RunsTo (w - 6 - D) B qB z tB ∧
          RunsTo (w - 8 - D) C qC u tC ∧ o = y ++ z ++ u ∧
          y.length ≤ catLim (w - 4) (D + 2) ∧ z.length ≤ catLim (w - 6) (D + 2) ∧
          u.length ≤ catLim (w - 8) (D + 2))

/-- The specification of the loop driver `p` of `G` and `P` with
constant `K`. -/
def LoopSpec (p G P : Program) (K : ℕ) : Prop :=
  ∀ (w : ℕ) (x : List ℕ), 8 ≤ w → x.length < 2 ^ (w - 1) →
    (∀ z T, LoopTrace w G P x 0 (lpA0 x) [] z T →
      ∃ t ≤ K * (T + z.length + 1), RunsTo w p x z t) ∧
    (∀ z t, RunsTo w p x z t → ∃ T, LoopTrace w G P x 0 (lpA0 x) [] z T)

/-- The constant that the word lengths of the regions must exceed. -/
noncomputable def soundBig (eM eR eE cM cR cE dM dR dE Ks : ℕ) : ℕ :=
  calleeBig eM eR eE cM cR cE dM dR dE + Ks + qM0.length + qR0.length + qE0.length + 1

theorem le_pow_sub {B k v : ℕ} (h : B * 2 ^ k ≤ 2 ^ v) (hB : 1 ≤ B) : k ≤ v ∧ B ≤ 2 ^ (v - k) := by
  have hk : k ≤ v := by
    have : 2 ^ k ≤ 2 ^ v := le_trans (Nat.le_mul_of_pos_left _ hB) h
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 this
  refine ⟨hk, ?_⟩
  rw [show 2 ^ v = 2 ^ (v - k) * 2 ^ k by rw [← pow_add]; congr 1; omega] at h
  exact Nat.le_of_mul_le_mul_right h (by positivity)

theorem catLim_le (w E : ℕ) : catLim w E ≤ 2 ^ (w - E) := by
  unfold catLim
  rcases le_total E w with h | h
  · calc (2 ^ w - 1) / 2 ^ E ≤ 2 ^ w / 2 ^ E := Nat.div_le_div_right (Nat.sub_le _ _)
      _ = 2 ^ (w - E) := by rw [Nat.pow_div h (by norm_num)]
  · calc (2 ^ w - 1) / 2 ^ E ≤ 2 ^ w / 2 ^ E := Nat.div_le_div_right (Nat.sub_le _ _)
      _ ≤ 1 := by
        rcases Nat.lt_or_ge (2 ^ w) (2 ^ E) with h' | h'
        · rw [Nat.div_eq_of_lt h']; omega
        · have : 2 ^ w = 2 ^ E := le_antisymm (two_pow_mono h) h'
          rw [this, Nat.div_self (by positivity)]
      _ ≤ _ := Nat.one_le_two_pow

theorem lpU_lt {x a b : List ℕ} {N : ℕ} (hN : 0 < N) (hx : ∀ e ∈ x, e < N)
    (ha : ∀ e ∈ a, e < N) (hb : ∀ e ∈ b, e < N) (hbl : b.length < N) :
    ∀ e ∈ lpU x a b, e < N := by
  have hg : ∀ i, a.getD i 0 < N := by
    intro i
    rw [List.getD_eq_getElem?_getD]
    rcases h : a[i]? with _ | e
    · simpa using hN
    · exact ha e (List.mem_of_getElem? h)
  intro e he
  simp only [lpU, List.mem_append, List.mem_cons, List.mem_singleton] at he
  rcases he with ((((rfl | rfl | he) | he) | he) | rfl | he)
  · exact hg 0
  · exact hg 1
  · simp at he
  · exact hx e (List.mem_of_mem_drop (List.mem_of_mem_take he))
  · exact ha e (List.mem_of_mem_drop (List.mem_of_mem_take he))
  · exact hbl
  · exact hb e he

theorem lpQ_append {h u : List ℕ} (hh : h.getD 1 0 + 3 = h.length) : lpQ (h ++ u) = u := by
  have h1 : 1 < h.length := by omega
  have : (h ++ u).getD 1 0 = h.getD 1 0 := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h1]
  simp only [lpQ, this]
  rw [show 3 + h.getD 1 0 = h.length by omega, List.drop_left]

theorem swIn_length_le (qA qB qC : List ℕ) :
    (swIn qA qB qC).length = 3 + qA.length + qB.length + qC.length := by
  simp [swIn]; omega

theorem guard_length {u : List ℕ} {e N : ℕ} (h : (u.length + maxEntry u + 1) ^ (e + 1) ≤ N) :
    u.length < N := by
  have : u.length + maxEntry u + 1 ≤ (u.length + maxEntry u + 1) ^ (e + 1) :=
    Nat.le_self_pow (by omega) _
  omega

/-- The length of the query of a call under its guard. -/
theorem callQ_length {n : ℕ} {s : List (PartialGraph (Fin n))} {q : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {eM eR eE v sQ : ℕ} {c : PCall n}
    (hg : GuardOK s q φ eM eR eE v sQ c) :
    (callQ s q φ c).length < 3 + 2 ^ (v - sQ) + qM0.length + qR0.length + qE0.length := by
  rw [callQ, swIn_length_le]
  cases c with
  | merge t P Q =>
    simp only [GuardOK] at hg
    have := guard_length hg
    simp only [callQM, callQR, callQE] at this ⊢; omega
  | resolve t sg P Q =>
    simp only [GuardOK] at hg
    have := guard_length hg
    simp only [callQM, callQR, callQE] at this ⊢; omega
  | eval a =>
    simp only [GuardOK] at hg
    have := guard_length hg
    simp only [callQM, callQR, callQE] at this ⊢; omega

/-- **Soundness of the pipeline thread.** -/
theorem pipe_sound {pM pR pE G sw P0 : Program} {eM eR eE q cM cR cE dM dR dE Ks KL D sI cG : ℕ}
    (hS : CalleeSound pM pR pE eM eR eE q cM cR cE dM dR dE) (hsw : SwSpec sw Ks D pM pR pE)
    (hP0 : LoopSpec P0 G sw KL) (hD : sI + 4 ≤ D) {φ : Lax3.FirstOrder.FO 0}
    (hq : Lax3.FirstOrder.rank φ = q) {n : ℕ} {Gr : SimpleGraph (Fin n)}
    {s : List (PartialGraph (Fin n))} {x : List ℕ} {steps : List Step}
    (hcs : IsConstructionSequence Gr s) (hgl : GlueAt G sI (D + 16) eM eR eE cG φ x s steps)
    {w : ℕ} (hw : 8 ≤ w) (hx : x.length < 2 ^ (w - 1))
    (hbig : ∀ i ≤ 2 * (pcalls n steps).length + 2,
      soundBig eM eR eE cM cR cE dM dR dE Ks * 2 ^ (D + 20) ≤ 2 ^ lpV w i ∧
        (x.length + maxEntry x + 1) * 2 ^ sI ≤ 2 ^ lpV w i) :
    ∀ z t, RunsTo w P0 x z t → z = 1 :: mcAns Gr φ := by
  have hback : ∀ (w : ℕ) (x : List ℕ), 8 ≤ w → x.length < 2 ^ (w - 1) →
      ∀ z t, RunsTo w P0 x z t → ∃ T, LoopTrace w G sw x 0 (lpA0 x) [] z T :=
    fun w x hw hx => (hP0 w x hw hx).2
  set B := soundBig eM eR eE cM cR cE dM dR dE Ks with hBdef
  have hB1 : 1 ≤ B := by simp only [hBdef, soundBig]; omega
  -- the facts about region `i`
  have hreg : ∀ i ≤ 2 * (pcalls n steps).length + 2,
      D + 20 ≤ lpV w i ∧ B ≤ 2 ^ (lpV w i - (D + 20)) ∧ sI ≤ lpV w i ∧
        ∀ e ∈ lpA0 x ++ x, e < 2 ^ (lpV w i - sI) := by
    intro i hi
    obtain ⟨h1, h2⟩ := hbig i hi
    obtain ⟨k1, k2⟩ := le_pow_sub h1 hB1
    obtain ⟨-, k4⟩ := le_pow_sub h2 (by omega)
    refine ⟨k1, k2, by omega, fun e he => ?_⟩
    simp only [lpA0, List.mem_append, List.mem_cons] at he
    have : e ≤ x.length + maxEntry x := by
      rcases he with (rfl | rfl | rfl | he) | he
      · omega
      · omega
      · omega
      · simp at he
      · have := le_maxEntry he; omega
    omega
  -- the entries of the first input
  have hU0 : ∀ v, sI ≤ v → (∀ e ∈ lpA0 x ++ x, e < 2 ^ (v - sI)) →
      ∀ e ∈ lpU x (lpA0 x) [], e < 2 ^ (v - sI) := by
    intro v _ h
    exact lpU_lt (by positivity) (fun e he => h e (List.mem_append_right _ he))
      (fun e he => h e (List.mem_append_left _ he)) (by simp) (by simpa using Nat.two_pow_pos _)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- without vertices the pipeline never halts
    obtain ⟨-, -, hr0, -⟩ := hreg 0 (by omega)
    obtain ⟨-, -, -, hx0⟩ := hreg 0 (by omega)
    intro z t h
    exact absurd h (loop_never hback hw hx (fun o t => hgl.empty hn _ o t hr0
      (hU0 _ hr0 hx0)) z t)
  obtain ⟨hd, hhd, -, -, hrd⟩ := hgl.rounds hn
  simp only [hq] at hhd hrd
  set cs := pcalls n steps with hcsdef
  set R := cs.length with hRdef
  set ans := finAns s q φ
  refine inv_script_sound hback hw hx (A := pA x s q φ cs hd ans) (B := pB s q φ cs)
    (I := fun j => ∀ e ∈ pU x s q φ cs hd ans j, e < 2 ^ (lpV w (2 * j) - sI)) (R := R)
    rfl rfl ?_ ?_ ?_
  · -- the invariant of the first round
    obtain ⟨-, -, hr0, hx0⟩ := hreg 0 (by omega)
    exact hU0 _ hr0 hx0
  · -- the rounds with a call
    intro j hj hI o t hrun
    obtain ⟨hv1, hBv, hsv, -⟩ := hreg (2 * j) (by omega)
    obtain ⟨hv1', hBv', -, -⟩ := hreg (2 * j + 1) (by omega)
    obtain ⟨-, -, hsv'', hxv''⟩ := hreg (2 * j + 2) (by omega)
    have hvv := lpV_succ_ge w (2 * j)
    have hvv' := lpV_succ_ge w (2 * j + 1)
    set v := lpV w (2 * j)
    set v' := lpV w (2 * j + 1)
    set v'' := lpV w (2 * j + 2)
    obtain ⟨ho, hoe, hog⟩ := (hrd j hj.le v hsv hI).1 o t hrun
    obtain ⟨c, hc⟩ : ∃ c, cs[j]? = some c := ⟨cs[j], List.getElem?_eq_getElem hj⟩
    have hgo : glueOut s q φ cs hd ans j = hd j ++ callQ s q φ c := by
      simp only [glueOut, hc]
    obtain ⟨hne, hh0, hlen⟩ := hhd j hj
    have hA : pA x s q φ cs hd ans (j + 1) = hd j ++ callQ s q φ c := by
      simp only [pA, hgo]
    refine ⟨ho, ?_, fun r t' hr => ?_⟩
    · rw [hA]
      rcases hhj : hd j with _ | ⟨a, l⟩
      · exact absurd hhj hne
      · rw [hhj] at hh0; simpa using hh0
    rw [ho, hgo, lpQ_append hlen, callQ] at hr
    have hg := hog c hc
    have hql := callQ_length hg
    rw [callQ] at hql
    have h2 : 2 ^ (v - (D + 16)) ≤ 2 ^ (v' - 14 - D) := two_pow_mono (by omega)
    have h3 : 2 ^ (v' - (D + 20)) * 2 ^ 10 = 2 ^ (v' - 10 - D) := by
      rw [← pow_add]; congr 1; omega
    have h4 : 2 ^ (v' - 14 - D) * 2 ^ 4 = 2 ^ (v' - 10 - D) := by
      rw [← pow_add]; congr 1; omega
    have h5 : 2 ^ (v' - (D + 20)) * 2 ^ 12 = 2 ^ (v' - 8 - D) := by
      rw [← pow_add]; congr 1; omega
    have hBdef' := hBdef
    simp only [soundBig] at hBdef'
    obtain ⟨y, z, u, tA, tB, tC, hy, hz, hu, hr', hyl, hzl, hul⟩ :=
      (hsw v' _ _ _ (by omega) (by omega) (by omega)).2 r t' hr
    have hY := callee_answers hS hq (by omega : v ≤ v' + 2) hg
      (by simp only [calleeBig] at hBdef' ⊢; omega) hy hz hu
    have hB' : pB s q φ cs (j + 1) = callY s q φ c := by simp only [pB, hc]
    refine ⟨by rw [hB', hr', hY], ?_⟩
    -- the invariant of the next round
    show ∀ e ∈ lpU x (pA x s q φ cs hd ans (j + 1)) (pB s q φ cs (j + 1)), e < 2 ^ (v'' - sI)
    rw [show pA x s q φ cs hd ans (j + 1) = o by rw [ho]; rfl, hB', ← hY]
    have k1 : 2 ^ (v - sI - 4) ≤ 2 ^ (v'' - sI) := two_pow_mono (by omega)
    have k2 : 2 ^ (v' - 4 - D) ≤ 2 ^ (v'' - sI) := two_pow_mono (by omega)
    have k3 : 2 ^ (v' - 6 - D) ≤ 2 ^ (v' - 4 - D) := two_pow_mono (by omega)
    have k4 : 2 ^ (v' - 8 - D) ≤ 2 ^ (v' - 6 - D) := two_pow_mono (by omega)
    have k5 : 2 ^ (v' - 6 - D) * 2 ^ 2 = 2 ^ (v' - 4 - D) := by
      rw [← pow_add]; congr 1; omega
    have l1 := catLim_le (v' - 4) (D + 2)
    have l2 := catLim_le (v' - 6) (D + 2)
    have l3 := catLim_le (v' - 8) (D + 2)
    rw [show v' - 4 - (D + 2) = v' - 6 - D by omega] at l1
    rw [show v' - 6 - (D + 2) = v' - 8 - D by omega] at l2
    rw [show v' - 8 - (D + 2) = v' - 10 - D by omega] at l3
    have k6 : 2 ^ (v' - 10 - D) ≤ 2 ^ (v' - 8 - D) := two_pow_mono (by omega)
    have oy := runsTo_out_lt hy
    have oz := runsTo_out_lt hz
    have ou := runsTo_out_lt hu
    refine lpU_lt (by positivity) (fun e he => hxv'' e (List.mem_append_right _ he))
      (fun e he => lt_of_lt_of_le (hoe e he) k1) (fun e he => ?_) ?_
    · simp only [List.mem_append] at he
      rcases he with (he | he) | he
      · exact lt_of_lt_of_le (oy e he) k2
      · exact lt_of_lt_of_le (oz e he) (le_trans k3 k2)
      · exact lt_of_lt_of_le (ou e he) (le_trans k4 (le_trans k3 k2))
    · simp only [List.length_append]; omega
  · -- the last round
    intro hI o t hrun
    obtain ⟨-, -, hsv, -⟩ := hreg (2 * R) (by omega)
    obtain ⟨ho, -, -⟩ := (hrd R le_rfl _ hsv hI).1 o t hrun
    rw [ho]
    simp only [glueOut, List.getElem?_eq_none (le_refl R)]
    rw [← finAns_eq hn hcs φ, hq]

end Lax185574Proofs.MC
