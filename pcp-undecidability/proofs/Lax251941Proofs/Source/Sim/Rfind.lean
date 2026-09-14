/-
# Minimisation, and the compiler

This file completes the compiler of `RequestProject/Sim/Compile.lean` with the last of
the five clauses of `Nat.Partrec'`: unbounded search.

The program is an unbounded loop.  A *flag* register drives the loop of `loopDec`: the
body of the loop begins with the flag already decremented to zero, evaluates
`f (k ::ᵥ v)` for the current value `k` of the counter, and, if the value is nonzero,
increments the counter and sets the flag back to one, so that the loop goes round again.
If the value is zero the flag is left at zero and the loop stops with the counter holding
the least witness; if no witness exists the flag is set again at every turn and the
program diverges, which is exactly the behaviour of `Nat.rfind`.
-/
import Lax251941Proofs.Source.Sim.Compile

namespace Lax251941Proofs.PCP
namespace Sim

open List (Vector)

/-- The body of the unbounded search loop of `rfindProg`.  The registers `W, …, W+n-1`
hold the arguments, `W+n` the counter, `W+n+1` the flag and `W+n+2` a scratch register. -/
def rfindBody (n W : ℕ) (F : Prog) : Prog :=
  pseq (pcopy (W + n) 0 (W + n + 2))
    (pseq (pcopyBlock W 1 (W + n + 2) n)
      (pseq F
        (pseq (pifnz (n + 1) (pseq [Instr.inc (W + n + 1)] [Instr.inc (W + n)]))
          (pclearRange 0 (n + 1)))))

/-- The search program: save the arguments, set the flag, run the search loop, then
restore the arguments and deliver the counter. -/
def rfindProg (n W : ℕ) (F : Prog) : Prog :=
  pseq (pseq (pmoveBlock 0 W n) [Instr.inc (W + n + 1)])
    (pseq (loopDec (W + n + 1) (rfindBody n W F))
      (pseq (pmoveBlock W 0 n) (pmove (W + n) n)))

/-- **One turn of the search loop.**  Started with the flag at zero, the body computes
`f (k ::ᵥ v)`; it leaves the counter and the flag alone if that value is zero, and
otherwise increments the counter and sets the flag. -/
lemma runs_rfindBody {n bF W : ℕ} {f : List.Vector ℕ (n + 1) → ℕ} {F : Prog}
    (hF : Computes (n + 1) bF ((f : List.Vector ℕ (n + 1) → ℕ) : _ →. ℕ) F)
    (hWF : bF ≤ W) (hWn : n + 2 ≤ W) (a : Regs) (t : Regs) (k : ℕ)
    (hlo : ∀ i, i < W → t i = 0) (harg : ∀ j, j < n → t (W + j) = a j)
    (hk : t (W + n) = k) (hfl : t (W + n + 1) = 0) :
    ∃ t', Runs (rfindBody n W F) t t' ∧ (∀ i, i < W → t' i = 0) ∧
      (∀ j, j < n → t' (W + j) = a j) ∧ t' (W + n + 2) = 0 ∧
      (∀ i, W + n + 3 ≤ i → t' i = t i) ∧
      ((f (k ::ᵥ vargs n a) = 0 ∧ t' (W + n) = k ∧ t' (W + n + 1) = 0) ∨
        (f (k ::ᵥ vargs n a) ≠ 0 ∧ t' (W + n) = k + 1 ∧ t' (W + n + 1) = 1)) := by
  classical
  -- step 1: load the counter into the first argument position
  have hr1 := impl_pcopy (src := W + n) (dst := 0) (tmp := W + n + 2)
    (by omega) (by omega) (by omega) t
  set u1 : Regs := fun i => if i = 0 then t (W + n) else if i = W + n + 2 then 0 else t i
    with hu1def
  have hu1_0 : u1 0 = k := by
    rw [hu1def]
    beta_reduce
    rw [if_pos rfl, hk]
  have hu1_out : ∀ i, i ≠ 0 → i ≠ W + n + 2 → u1 i = t i := by
    intro i h1 h2
    rw [hu1def]
    beta_reduce
    rw [if_neg h1, if_neg h2]
  -- step 2: copy the saved arguments into the remaining argument positions
  obtain ⟨u2, hr2, hc1, hc2, hc3⟩ :=
    acts_pcopyBlock (src := W) (dst := 1) (tmp := W + n + 2) (m := n) (Or.inr (by omega))
      (fun j hj => by omega) (fun j hj => by omega) u1
  have hu2_0 : u2 0 = k := by
    rw [hc3 0 (by omega) (fun j hj => by omega), hu1_0]
  have hu2_arg : ∀ j, j < n → u2 (1 + j) = a j := by
    intro j hj
    rw [hc1 j hj, hu1_out _ (by omega) (by omega), harg j hj]
  have hu2_mid : ∀ i, n + 1 ≤ i → i < W → u2 i = 0 := by
    intro i h1 h2
    rw [hc3 i (by omega) (fun j hj => by omega), hu1_out i (by omega) (by omega)]
    exact hlo i h2
  have hu2_hi : ∀ i, W ≤ i → i ≠ W + n + 2 → u2 i = t i := by
    intro i h1 h2
    rw [hc3 i h2 (fun j hj => by omega), hu1_out i (by omega) h2]
  have hu2_va : vargs (n + 1) u2 = k ::ᵥ vargs n a := by
    rw [vargs_cons, hu2_0]
    congr 1
    refine vargs_congr (fun j hj => ?_)
    show u2 (j + 1) = a j
    rw [show j + 1 = 1 + j from by omega]
    exact hu2_arg j hj
  -- step 3: evaluate `f`
  obtain ⟨hFrun, -⟩ := hF.2 u2 (fun i h1 h2 => hu2_mid i h1 (by omega))
  have hr3 : Runs F u2 (Function.update u2 (n + 1) (f (k ::ᵥ vargs n a))) :=
    hFrun _ (by rw [hu2_va]; exact mem_lift_self f _)
  have hu3_out : ∀ i, i ≠ n + 1 → Function.update u2 (n + 1) (f (k ::ᵥ vargs n a)) i = u2 i :=
    fun i hi => Function.update_of_ne hi _ _
  -- step 4: the conditional
  have hB : Impl (pseq [Instr.inc (W + n + 1)] [Instr.inc (W + n)])
      (fun t => Function.update (Function.update t (W + n + 1) (t (W + n + 1) + 1)) (W + n)
        (Function.update t (W + n + 1) (t (W + n + 1) + 1) (W + n) + 1)) :=
    impl_seq (impl_inc _) (impl_inc _)
  have hr4 := impl_pifnz (n + 1) hB (fun t => by
    rw [Function.update_of_ne (show n + 1 ≠ W + n by omega),
      Function.update_of_ne (show n + 1 ≠ W + n + 1 by omega)])
    (Function.update u2 (n + 1) (f (k ::ᵥ vargs n a)))
  by_cases hY : f (k ::ᵥ vargs n a) = 0
  · -- the search stops
    beta_reduce at hr4
    rw [show (Function.update u2 (n + 1) (f (k ::ᵥ vargs n a))) (n + 1) = 0 from by
      rw [Function.update_self, hY], if_pos rfl] at hr4
    obtain ⟨u5, hr5, he1, he2⟩ :=
      acts_pclearRange 0 (n + 1) (Function.update u2 (n + 1) (f (k ::ᵥ vargs n a)))
    have hu3_all : ∀ i, Function.update u2 (n + 1) (f (k ::ᵥ vargs n a)) i = u2 i := by
      intro i
      by_cases hi : i = n + 1
      · rw [hi, Function.update_self, hY]
        exact (hu2_mid (n + 1) (by omega) (by omega)).symm
      · exact hu3_out i hi
    have hu5_out : ∀ i, n + 1 ≤ i → u5 i = u2 i := by
      intro i hi
      rw [he2 i (Or.inr (by omega)), hu3_all i]
    refine ⟨u5, runs_pseq hr1 (runs_pseq hr2 (runs_pseq hr3 (runs_pseq hr4 hr5))), ?_, ?_, ?_, ?_,
      Or.inl ⟨hY, ?_, ?_⟩⟩
    · intro i hi
      by_cases h : i < n + 1
      · exact he1 i (by omega) (by omega)
      · rw [hu5_out i (by omega)]
        exact hu2_mid i (by omega) hi
    · intro j hj
      rw [hu5_out _ (by omega), hu2_hi _ (by omega) (by omega)]
      exact harg j hj
    · rw [hu5_out _ (by omega)]
      exact hc2
    · intro i hi
      rw [hu5_out i (by omega), hu2_hi i (by omega) (by omega)]
    · rw [hu5_out _ (by omega), hu2_hi _ (by omega) (by omega)]
      exact hk
    · rw [hu5_out _ (by omega), hu2_hi _ (by omega) (by omega)]
      exact hfl
  · -- the search goes on
    beta_reduce at hr4
    rw [if_neg (show ¬ ((Function.update u2 (n + 1) (f (k ::ᵥ vargs n a))) (n + 1) = 0) from by
      rw [Function.update_self]; exact hY),
      Function.update_idem] at hr4
    set w : Regs := Function.update u2 (n + 1) 0 with hwdef
    have hw_fl : w (W + n + 1) = 0 := by
      rw [hwdef, Function.update_of_ne (by omega), hu2_hi _ (by omega) (by omega)]
      exact hfl
    have hw_k : w (W + n) = k := by
      rw [hwdef, Function.update_of_ne (by omega), hu2_hi _ (by omega) (by omega)]
      exact hk
    set u4 : Regs := Function.update (Function.update w (W + n + 1) (w (W + n + 1) + 1)) (W + n)
      (Function.update w (W + n + 1) (w (W + n + 1) + 1) (W + n) + 1) with hu4def
    have hu4_fl : u4 (W + n + 1) = 1 := by
      rw [hu4def, Function.update_of_ne (by omega), Function.update_self, hw_fl]
    have hu4_k : u4 (W + n) = k + 1 := by
      rw [hu4def, Function.update_self, Function.update_of_ne (show W + n ≠ W + n + 1 by omega),
        hw_k]
    have hu4_out : ∀ i, i ≠ W + n → i ≠ W + n + 1 → i ≠ n + 1 → u4 i = u2 i := by
      intro i h1 h2 h3
      rw [hu4def, Function.update_of_ne h1, Function.update_of_ne h2, hwdef,
        Function.update_of_ne h3]
    have hu4_low : u4 (n + 1) = 0 := by
      rw [hu4def, Function.update_of_ne (by omega), Function.update_of_ne (by omega), hwdef,
        Function.update_self]
    have hu4_out' : ∀ i, i ≠ W + n → i ≠ W + n + 1 → u4 i = u2 i := by
      intro i h1 h2
      by_cases h3 : i = n + 1
      · rw [h3, hu4_low, hu2_mid (n + 1) (by omega) (by omega)]
      · exact hu4_out i h1 h2 h3
    obtain ⟨u5, hr5, he1, he2⟩ := acts_pclearRange 0 (n + 1) u4
    have hu5_out : ∀ i, n + 1 ≤ i → u5 i = u4 i := fun i hi => he2 i (Or.inr (by omega))
    refine ⟨u5, runs_pseq hr1 (runs_pseq hr2 (runs_pseq hr3 (runs_pseq hr4 hr5))), ?_, ?_, ?_, ?_,
      Or.inr ⟨hY, ?_, ?_⟩⟩
    · intro i hi
      by_cases h : i < n + 1
      · exact he1 i (by omega) (by omega)
      · rw [hu5_out i (by omega), hu4_out' i (by omega) (by omega)]
        exact hu2_mid i (by omega) hi
    · intro j hj
      rw [hu5_out _ (by omega), hu4_out' _ (by omega) (by omega),
        hu2_hi _ (by omega) (by omega)]
      exact harg j hj
    · rw [hu5_out _ (by omega), hu4_out' _ (by omega) (by omega)]
      exact hc2
    · intro i hi
      rw [hu5_out i (by omega), hu4_out' i (by omega) (by omega),
        hu2_hi i (by omega) (by omega)]
    · rw [hu5_out _ (by omega), hu4_k]
    · rw [hu5_out _ (by omega), hu4_fl]

/-! ## Minimisation -/

lemma computes_rfind {n : ℕ} {f : List.Vector ℕ (n + 1) → ℕ} {bF : ℕ} {F : Prog}
    (hF : Computes (n + 1) bF ((f : List.Vector ℕ (n + 1) → ℕ) : _ →. ℕ) F) :
    ∃ b P, Computes n b (fun v => Nat.rfind fun k => Part.some (decide (f (k ::ᵥ v) = 0))) P := by
  classical
  obtain ⟨W, hWF, hWn⟩ : ∃ W, bF ≤ W ∧ n + 2 ≤ W :=
    ⟨max bF (n + 2), le_max_left _ _, le_max_right _ _⟩
  refine ⟨W + n + 3, rfindProg n W F, by omega, fun s hs => ?_⟩
  -- step 1: save the arguments
  obtain ⟨t1, hr1, ha1, ha2, ha3⟩ :=
    acts_pmoveBlock (src := 0) (dst := W) (m := n) (Or.inl (by omega)) s
  have ht1lo : ∀ i, i < W → t1 i = 0 := by
    intro i hi
    by_cases h : i < n
    · have := ha2 i h
      rwa [Nat.zero_add] at this
    · rw [ha3 i (fun j hj => by omega)]
      exact hs i (by omega) (by omega)
  have ht1arg : ∀ j, j < n → t1 (W + j) = s j := by
    intro j hj
    have := ha1 j hj
    rwa [Nat.zero_add] at this
  have ht1hi : ∀ i, W + n ≤ i → t1 i = s i := fun i hi => ha3 i (fun j hj => by omega)
  -- step 2: set the flag
  have hr2 := impl_inc (W + n + 1) t1
  set t2 : Regs := Function.update t1 (W + n + 1) (t1 (W + n + 1) + 1) with ht2def
  have ht1fl : t1 (W + n + 1) = 0 := by
    rw [ht1hi _ (by omega)]
    exact hs _ (by omega) (by omega)
  have ht2fl : t2 (W + n + 1) = 1 := by rw [ht2def, Function.update_self, ht1fl]
  have ht2out : ∀ i, i ≠ W + n + 1 → t2 i = t1 i := fun i hi => Function.update_of_ne hi _ _
  have ht2lo : ∀ i, i < W → t2 i = 0 := by
    intro i hi
    rw [ht2out i (by omega)]
    exact ht1lo i hi
  have ht2arg : ∀ j, j < n → t2 (W + j) = s j := by
    intro j hj
    rw [ht2out _ (by omega)]
    exact ht1arg j hj
  have ht2k : t2 (W + n) = 0 := by
    rw [ht2out _ (by omega), ht1hi _ (by omega)]
    exact hs _ (by omega) (by omega)
  have ht2tmp : t2 (W + n + 2) = 0 := by
    rw [ht2out _ (by omega), ht1hi _ (by omega)]
    exact hs _ (by omega) (by omega)
  have ht2hi : ∀ i, W + n + 3 ≤ i → t2 i = s i := by
    intro i hi
    rw [ht2out i (by omega), ht1hi i (by omega)]
  have hrPre : Runs (pseq (pmoveBlock 0 W n) [Instr.inc (W + n + 1)]) s t2 := runs_pseq hr1 hr2
  refine ⟨?_, ?_⟩
  · -- the search succeeds
    intro y hy
    have hy1 : f (y ::ᵥ vargs n s) = 0 := by
      have := Nat.rfind_spec hy
      simpa using this
    have hy2 : ∀ m, m < y → f (m ::ᵥ vargs n s) ≠ 0 := by
      intro m hm
      have := Nat.rfind_min hy hm
      simpa using this
    set I : Regs → Prop := fun t => ∃ k, t (W + n) = k ∧
      (∀ j, j < k → f (j ::ᵥ vargs n s) ≠ 0) ∧
      (t (W + n + 1) = 1 ∨ (t (W + n + 1) = 0 ∧ f (k ::ᵥ vargs n s) = 0)) ∧
      (∀ i, i < W → t i = 0) ∧ (∀ j, j < n → t (W + j) = s j) ∧ t (W + n + 2) = 0 ∧
      (∀ i, W + n + 3 ≤ i → t i = s i) with hIdef
    have hI2 : I t2 :=
      ⟨0, ht2k, fun j hj => absurd hj (by omega), Or.inl ht2fl, ht2lo, ht2arg, ht2tmp, ht2hi⟩
    have hstep : ∀ t, I t → t (W + n + 1) ≠ 0 →
        ∃ t', Runs (rfindBody n W F) (Function.update t (W + n + 1) (t (W + n + 1) - 1)) t' ∧
          I t' ∧ 2 * (y - t' (W + n)) + t' (W + n + 1)
            < 2 * (y - t (W + n)) + t (W + n + 1) := by
      intro t hIt hne
      obtain ⟨k, hk, hmin, hflag, hlo, harg, htmp, hhi⟩ := hIt
      have hfl1 : t (W + n + 1) = 1 := by
        rcases hflag with h | ⟨h, -⟩
        · exact h
        · exact absurd h hne
      have hu_fl : Function.update t (W + n + 1) (t (W + n + 1) - 1) (W + n + 1) = 0 := by
        rw [Function.update_self, hfl1]
      have hu_out : ∀ i, i ≠ W + n + 1 →
          Function.update t (W + n + 1) (t (W + n + 1) - 1) i = t i :=
        fun i hi => Function.update_of_ne hi _ _
      have hklt : k ≤ y := by
        by_contra hgt
        exact hmin y (by omega) hy1
      obtain ⟨t', hrun, hlo', harg', htmp', hhi', hcase⟩ :=
        runs_rfindBody hF hWF hWn s _ k
          (fun i hi => by rw [hu_out i (by omega)]; exact hlo i hi)
          (fun j hj => by rw [hu_out _ (by omega)]; exact harg j hj)
          (by rw [hu_out _ (by omega)]; exact hk) hu_fl
      have hhi'' : ∀ i, W + n + 3 ≤ i → t' i = s i := by
        intro i hi
        rw [hhi' i hi, hu_out i (by omega)]
        exact hhi i hi
      rcases hcase with ⟨hz, hk', hfl'⟩ | ⟨hnz, hk', hfl'⟩
      · exact ⟨t', hrun, ⟨k, hk', hmin, Or.inr ⟨hfl', hz⟩, hlo', harg', htmp', hhi''⟩,
          by rw [hk', hfl', hk, hfl1]; omega⟩
      · have hkly : k < y := by
          rcases Nat.lt_or_ge k y with h | h
          · exact h
          · exact absurd (by rw [show k = y from by omega]; exact hy1) hnz
        refine ⟨t', hrun, ⟨k + 1, hk', ?_, Or.inl hfl', hlo', harg', htmp', hhi''⟩, ?_⟩
        · intro j hj
          rcases Nat.lt_or_ge j k with h | h
          · exact hmin j h
          · rw [show j = k from by omega]
            exact hnz
        · rw [hk', hfl', hk, hfl1]
          omega
    obtain ⟨t7, hr7, hI7, hz7⟩ :=
      runs_loopDec_of_measure (mu := fun t => 2 * (y - t (W + n)) + t (W + n + 1)) hstep t2 hI2
    obtain ⟨kf, hkf, hminf, hflagf, hlof, hargf, htmpf, hhif⟩ := hI7
    have hkfy : kf = y := by
      rcases hflagf with h | ⟨-, hz⟩
      · rw [hz7] at h
        exact absurd h (by omega)
      · by_contra hne
        rcases Nat.lt_or_ge kf y with h1 | h1
        · exact hy2 kf h1 hz
        · exact hminf y (by omega) hy1
    -- restore the arguments and deliver the counter
    obtain ⟨t8, hr8, hb1, hb2, hb3⟩ :=
      acts_pmoveBlock (src := W) (dst := 0) (m := n) (Or.inr (by omega)) t7
    have hr9 := impl_pmove (src := W + n) (dst := n) (show W + n ≠ n by omega) t8
    refine Eq.mpr ?_ (runs_pseq hrPre (runs_pseq hr7 (runs_pseq hr8 hr9)))
    congr 1
    funext i
    by_cases hiK : i = W + n
    · rw [hiK]
      beta_reduce
      rw [if_pos rfl, Function.update_of_ne (show W + n ≠ n by omega)]
      exact hs _ (by omega) (by omega)
    · by_cases hin : i = n
      · rw [hin]
        beta_reduce
        rw [if_neg (show n ≠ W + n by omega), if_pos rfl, Function.update_self,
          hb3 (W + n) (fun j hj => by omega), hkf, hkfy]
      · beta_reduce
        rw [if_neg hiK, if_neg hin, Function.update_of_ne hin]
        by_cases hlt : i < n
        · have := hb1 i hlt
          rw [Nat.zero_add] at this
          rw [this, hargf i hlt]
        · by_cases hiW : i < W
          · rw [hb3 i (fun j hj => by omega), hlof i hiW]
            exact hs i (by omega) (by omega)
          · by_cases hblk : i < W + n
            · obtain ⟨j, hj⟩ : ∃ j, i = W + j := ⟨i - W, by omega⟩
              subst hj
              rw [hb2 j (by omega)]
              exact hs _ (by omega) (by omega)
            · rw [hb3 i (fun j hj => by omega)]
              by_cases hfl : i = W + n + 1
              · rw [hfl, hz7]
                exact hs _ (by omega) (by omega)
              · by_cases htm : i = W + n + 2
                · rw [htm, htmpf]
                  exact hs _ (by omega) (by omega)
                · rw [hhif i (by omega)]
  · -- the search diverges
    intro hnd
    have hall : ∀ k, f (k ::ᵥ vargs n s) ≠ 0 := by
      intro k hk0
      refine hnd ?_
      exact Nat.rfind_dom.mpr ⟨k, by simp [hk0], fun {_} _ => trivial⟩
    refine not_halts_pseq_right hrPre (not_halts_pseq_left ?_)
    refine not_halts_loopDec
      (I := fun t => t (W + n + 1) = 1 ∧ (∀ i, i < W → t i = 0) ∧
        (∀ j, j < n → t (W + j) = s j) ∧ t (W + n + 2) = 0)
      (fun t ht => by rw [ht.1]; omega) ?_ ⟨ht2fl, ht2lo, ht2arg, ht2tmp⟩
    rintro t ⟨hfl1, hlo, harg, htmp⟩
    have hu_fl : Function.update t (W + n + 1) (t (W + n + 1) - 1) (W + n + 1) = 0 := by
      rw [Function.update_self, hfl1]
    have hu_out : ∀ i, i ≠ W + n + 1 →
        Function.update t (W + n + 1) (t (W + n + 1) - 1) i = t i :=
      fun i hi => Function.update_of_ne hi _ _
    obtain ⟨t', hrun, hlo', harg', htmp', -, hcase⟩ :=
      runs_rfindBody hF hWF hWn s _ (t (W + n))
        (fun i hi => by rw [hu_out i (by omega)]; exact hlo i hi)
        (fun j hj => by rw [hu_out _ (by omega)]; exact harg j hj)
        (hu_out _ (by omega)) hu_fl
    rcases hcase with ⟨hz, -, -⟩ | ⟨-, -, hfl'⟩
    · exact absurd hz (hall _)
    · exact ⟨t', hrun, hfl', hlo', harg', htmp'⟩

/-! ## The compiler -/

theorem exists_prog_primrec {n : ℕ} {f : List.Vector ℕ n → ℕ} (hf : Nat.Primrec' f) :
    ∃ b P, Computes n b ((f : List.Vector ℕ n → ℕ) : _ →. ℕ) P := by
  induction hf with
  | zero => exact ⟨1, [], computes_zero⟩
  | succ => exact ⟨3, _, computes_succ⟩
  | get i => exact ⟨_, _, computes_get i⟩
  | @comp m k f g hf hg ihf ihg =>
    obtain ⟨bF, F, hF⟩ := ihf
    choose bG G hG using ihg
    obtain ⟨b, P, hP⟩ := computes_comp hF hG
    refine ⟨b, P, hP.congr fun v => ?_⟩
    simp
    exact Part.bind_some _ _
  | @prec n f g hf hg ihf ihg =>
    obtain ⟨bF, F, hF⟩ := ihf
    obtain ⟨bG, G, hG⟩ := ihg
    exact computes_prec hF hG

theorem exists_prog {n : ℕ} {f : List.Vector ℕ n →. ℕ} (hf : Nat.Partrec' f) :
    ∃ b P, Computes n b f P := by
  induction hf with
  | prim hf => exact exists_prog_primrec hf
  | @comp m k f g hf hg ihf ihg =>
    obtain ⟨bF, F, hF⟩ := ihf
    choose bG G hG using ihg
    exact computes_comp hF hG
  | @rfind n f hf ihf =>
    obtain ⟨bF, F, hF⟩ := ihf
    obtain ⟨b, P, hP⟩ := computes_rfind hF
    exact ⟨b, P, hP⟩

end Sim
end Lax251941Proofs.PCP
