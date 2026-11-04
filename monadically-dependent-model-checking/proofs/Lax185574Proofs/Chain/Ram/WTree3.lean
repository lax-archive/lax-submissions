import Lax185574Proofs.Chain.Ram.WTree2

/-!
The greedy procedure of the Welzl ordering as a program, third part:
facts about the greedy procedure itself, and the update of all weights
and values after a step.

Once at most one vertex is active the greedy step does nothing
(`welzlStep_of_card`), so the procedure may be run with more fuel than
needed (`welzlRun_of_card`). The steps only grow (`steps_welzlRun`), so
the number of steps crossed by a vertex never exceeds its final value,
and that is at most `Kw`, the largest final number over all vertices.

The weight exponent of `x` after `k` steps is `wExp G (wSt G k) x`, and the
value `ξ(u,v)` is the sum `xiP` of the weights of the vertices crossing
`u v` (`xi_eq_xiP`). After a step `(u, v)`, the command `xLoop` doubles
the weight of every vertex `x` crossing `u v`: it adds the old weight to
the values of all pairs crossed by `x` and then increments `wc[x]`
(`xLoop_run`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram Lax185574Proofs.Chain

/-! ### The greedy procedure with more fuel -/

section Fuel

variable {V : Type*} [Fintype V] [DecidableEq V] [LinearOrder V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

theorem welzlRun_add (a b : ℕ) (st : WState V) :
    welzlRun G (a + b) st = welzlRun G b (welzlRun G a st) := by
  induction a generalizing st with
  | zero => simp [welzlRun]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [welzlRun]
    exact ih _

theorem candPairs_eq_nil {A : Finset V} (h : A.card ≤ 1) : candPairs A = [] := by
  rw [List.eq_nil_iff_forall_not_mem]
  intro p hp
  simp only [candPairs, List.mem_flatMap, List.mem_filterMap, Option.ite_none_right_eq_some,
    Option.some.injEq] at hp
  obtain ⟨u, -, v, -, ⟨hvu, hu, hv⟩, rfl⟩ := hp
  have := Finset.one_lt_card.2 ⟨u, hu, v, hv, ne_of_gt hvu⟩
  omega

theorem welzlStep_of_card {st : WState V} (h : st.active.card ≤ 1) : welzlStep G st = st := by
  unfold welzlStep
  rw [candPairs_eq_nil h]
  rfl

theorem welzlRun_of_card (m : ℕ) {st : WState V} (h : st.active.card ≤ 1) :
    welzlRun G m st = st := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [welzlRun]; rw [welzlStep_of_card h]; exact ih

theorem steps_welzlStep (st : WState V) :
    ∃ l : List (V × V), (welzlStep G st).steps = l ++ st.steps ∧ l.length ≤ 1 := by
  unfold welzlStep
  split
  · exact ⟨[], rfl, by simp⟩
  · rename_i p _
    exact ⟨[p], rfl, by simp⟩

theorem steps_welzlRun (m : ℕ) (st : WState V) :
    ∃ l : List (V × V), (welzlRun G m st).steps = l ++ st.steps ∧ l.length ≤ m := by
  induction m generalizing st with
  | zero => exact ⟨[], rfl, by simp⟩
  | succ m ih =>
    simp only [welzlRun]
    obtain ⟨l1, h1, hl1⟩ := steps_welzlStep (G := G) st
    obtain ⟨l2, h2, hl2⟩ := ih (welzlStep G st)
    refine ⟨l2 ++ l1, by rw [h2, h1, List.append_assoc], by simp; omega⟩

theorem stepCross_append (x : V) (l s : List (V × V)) :
    stepCross G x (l ++ s) = stepCross G x l + stepCross G x s := by
  unfold stepCross; exact List.countP_append

theorem stepCross_le_length (x : V) (s : List (V × V)) : stepCross G x s ≤ s.length := by
  unfold stepCross; exact List.countP_le_length

end Fuel

/-! ### The states of the greedy procedure on `Fin n` -/

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

variable (G) in
/-- The state after `k` greedy steps. -/
noncomputable def wSt (k : ℕ) : WState (Fin n) := welzlRun G k ⟨univ, fun _ => 1, []⟩

variable (G) in
/-- The weight exponents of a state, on numbers. -/
noncomputable def wExp (st : WState (Fin n)) (x : ℕ) : ℕ :=
  if h : x < n then stepCross G ⟨x, h⟩ st.steps else 0

variable (G) in
/-- The largest number of steps crossed by one vertex. -/
noncomputable def Kw : ℕ := univ.sup fun x => stepCross G x (welzlTree G).steps

theorem welzlTree_eq : welzlTree G = wSt G n := by
  simp [welzlTree, wSt, Fintype.card_fin]

theorem wSt_succ (k : ℕ) : wSt G (k + 1) = welzlStep G (wSt G k) := by
  unfold wSt; rw [welzlRun_add]; rfl

theorem wSt_zero : wSt G 0 = ⟨univ, fun _ => 1, []⟩ := rfl

theorem wSt_inv (k : ℕ) : WInv (G := G) (wSt G k) := winv_run _ winv_init

theorem steps_length_wSt (k : ℕ) : (wSt G k).steps.length ≤ k := by
  obtain ⟨l, h, hl⟩ := steps_welzlRun (G := G) k ⟨univ, fun _ => 1, []⟩
  unfold wSt; rw [h]; simpa using hl

theorem wExp_le_final {k : ℕ} (hk : k ≤ n) (x : ℕ) : wExp G (wSt G k) x ≤ wExp G (wSt G n) x := by
  unfold wExp
  split
  · rename_i hx
    obtain ⟨l, h, -⟩ := steps_welzlRun (G := G) (n - k) (wSt G k)
    have e : wSt G n = welzlRun G (n - k) (wSt G k) := by
      unfold wSt; rw [← welzlRun_add]; congr 1; omega
    rw [e, h, stepCross_append]
    omega
  · exact le_rfl

theorem wExp_final_le (x : ℕ) : wExp G (wSt G n) x ≤ Kw G := by
  unfold wExp Kw
  split
  · rename_i hx
    rw [← welzlTree_eq]
    exact Finset.le_sup (f := fun x => stepCross G x (welzlTree G).steps) (mem_univ _)
  · exact Nat.zero_le _

theorem wExp_le_Kw {k : ℕ} (hk : k ≤ n) (x : ℕ) : wExp G (wSt G k) x ≤ Kw G :=
  (wExp_le_final hk x).trans (wExp_final_le x)

theorem Kw_le : Kw G ≤ n := by
  unfold Kw
  refine Finset.sup_le fun x _ => ?_
  rw [welzlTree_eq]
  exact (stepCross_le_length _ _).trans (steps_length_wSt n)

theorem wExp_zero (x : ℕ) : wExp G (wSt G 0) x = 0 := by
  unfold wExp; split <;> simp [wSt_zero, stepCross]

theorem ind_crN_fin (x u v : Fin n) :
    ind (crN G x u v) = if CrossesPair G x u v then 1 else 0 := by
  by_cases h : CrossesPair G x u v
  · simp [h, ind, (crN_fin x u v).2 h]
  · have : ¬ crN G x u v := fun h' => h ((crN_fin x u v).1 h')
    simp [h, ind, this]

/-- **The values as sums.** -/
theorem xi_eq_xiP {st : WState (Fin n)} (hw : ∀ x, st.w x = 2 ^ stepCross G x st.steps)
    {u v : ℕ} (hu : u < n) (hv : v < n) :
    xi G st.w ⟨u, hu⟩ ⟨v, hv⟩ = xiP G (wExp G st) n u v := by
  unfold xi xiP
  rw [sum_filter, ← Fin.sum_univ_eq_sum_range (fun x => ind (crN G x u v) * 2 ^ wExp G st x)]
  refine sum_congr rfl fun x _ => ?_
  have h1 : wExp G st x = stepCross G x st.steps := by simp [wExp, x.2]
  have h2 := ind_crN_fin (G := G) x ⟨u, hu⟩ ⟨v, hv⟩
  simp only at h2
  rw [h1, h2, hw x]
  split_ifs <;> simp

/-! ### Numeric bounds -/

theorem mul_two_pow_lt {K : ℕ} (hK : K ≤ n) : n * 2 ^ K < 2 ^ (2 * n + 2) := by
  have h1 : n < 2 ^ n := Nat.lt_two_pow_self
  have h2 : 2 ^ K ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hK
  calc n * 2 ^ K ≤ n * 2 ^ n := Nat.mul_le_mul_left _ h2
    _ < 2 ^ n * 2 ^ n := Nat.mul_lt_mul_of_pos_right h1 (by positivity)
    _ ≤ 2 ^ (2 * n + 2) := by rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-! ### Doubling the weights of the vertices crossing a step -/

/-- Double the weight of `wx` if it crosses the step `wbu wbv`. -/
def xBody : Com :=
  .ite (.eq (wCrossE "wx" "wbu" "wbv") (.lit 1))
    (.seq updX (.store "wc" (.var "wx") (.add (.get "wc" (.var "wx")) (.lit 1)))) .skip

/-- Double the weights of all vertices crossing the step `wbu wbv`. -/
def xLoop : Com := forUp "wx" (.var "n") xBody

/-- The scalars `xLoop` may change. -/
def xW : List String := ["wx", "wa", "wb", "bt", "bj", "bk"]

/-- The arrays `xLoop` may change. -/
def xA : List String := ["xb", "xt", "wc"]

/-- The exponents after the first `k` vertices of the loop. -/
noncomputable def ckE (c0 : ℕ → ℕ) (q : ℕ → Prop) (k : ℕ) (x : ℕ) : ℕ := c0 x + ind (x < k ∧ q x)

theorem ckE_eq (c0 : ℕ → ℕ) (q : ℕ → Prop) (k : ℕ) :
    ckE c0 q k = fun x => c0 x + ind (x < k ∧ q x) := rfl

theorem xBody_run {B K p1 p2 k : ℕ} {c0 : ℕ → ℕ} {τ : Env} (hB : WB n B) (hC : WCtx n G τ)
    (hK : K ≤ n) (hc0 : ∀ x < n, c0 x + ind (crN G x p1 p2) ≤ K)
    (hp1 : τ.vars "wbu" = p1) (hp2 : τ.vars "wbv" = p2) (hp1n : p1 < n) (hp2n : p2 < n)
    (hk : τ.vars "wx" = k) (hkn : k < n)
    (hwc : Vec τ "wc" n (ckE c0 (fun x => crN G x p1 p2) k))
    (hrep : XiRep n (xiP G (ckE c0 (fun x => crN G x p1 p2) k) n) τ) :
    ∃ τ', Run B xBody τ τ'
        (if crN G k p1 p2 then uxC n (20 * (K + Nat.log 2 n) + 30) + 42 else 37) ∧
      τ'.vars "wx" = k ∧ Vec τ' "wc" n (ckE c0 (fun x => crN G x p1 p2) (k + 1)) ∧
      XiRep n (xiP G (ckE c0 (fun x => crN G x p1 p2) (k + 1)) n) τ' ∧ Fr xW xA τ τ' := by
  have hs := hB.small
  have hnn : n ≤ n * n := Nat.le_mul_self n
  have hcond := evalB_condCross (B := B) hC.hn hC.hadj hk hp1 hp2 hkn hp1n hp2n (by omega)
  have hdbl := fun u v => xiP_double (G := G) c0 (fun x => crN G x p1 p2) hkn u v
  have hck : ckE c0 (fun x => crN G x p1 p2) k k = c0 k := by simp [ckE, ind]
  by_cases hcr : crN G k p1 p2
  · have hck1 := hc0 k hkn
    rw [ind_eq_one.2 hcr] at hck1
    have hjD : c0 k < 2 * n + 2 := by omega
    have hwk : (τ.arrs "wc")[k]? = some (c0 k) := by rw [hwc.get k hkn, hck]
    have hle : ∀ u v, xiP G (ckE c0 (fun x => crN G x p1 p2) (k + 1)) n u v ≤ n * 2 ^ K :=
      fun u v => xiP_le (fun x hx => by
        have := hc0 x hx
        have : ind (x < k + 1 ∧ crN G x p1 p2) ≤ ind (crN G x p1 p2) := by
          unfold ind; split_ifs <;> simp_all
        simp only [ckE]; omega) u v
    have hsum : ∀ u v, crN G k u v → xiP G (ckE c0 (fun x => crN G x p1 p2) k) n u v + 2 ^ c0 k =
        xiP G (ckE c0 (fun x => crN G x p1 p2) (k + 1)) n u v := fun u v h => by
      have := hdbl u v
      simp only [ckE_eq]
      rw [this, ind_eq_one.2 ⟨h, hcr⟩, one_mul]
    obtain ⟨τ1, hr1, hR1, hF1⟩ := updX_run (B := B) (G := G) (x := k) (j := c0 k)
      (P := 20 * (K + Nat.log 2 n) + 30) hB hC hk hkn hwk hjD hrep
      (fun u _ v _ h => by rw [hsum u v h]; exact (hle u v).trans_lt (mul_two_pow_lt hK))
      (fun u _ v _ h => by
        rw [hsum u v h]
        have := log_le_of_le (hle u v)
        omega)
    have hk1 : τ1.vars "wx" = k := by rw [hF1.vars _ (by decide), hk]
    have hwc1 : (τ1.arrs "wc") = τ.arrs "wc" := hF1.arrs _ (by decide)
    have hget : (Expr.get "wc" (.var "wx")).evalB B τ1 = some (c0 k) :=
      evalB_getVar hk1 (by omega) (by rw [hwc1]; exact hwk) (by omega)
    have hst := Run.store (B := B) (σ := τ1) (a := "wc") (i := .var "wx")
      (e := .add (.get "wc" (.var "wx")) (.lit 1)) (idx := k) (v := c0 k + 1)
      (by rw [evalB_var (by omega), hk1])
      (by have := evalB_bin (op := .add) hget (evalB_lit (n := 1) (B := B) (σ := τ1) (by omega))
            (by simp; omega)
          simpa using this)
      (by rw [hwc1, hwc.len]; exact hkn)
    have hrun : Run B xBody τ (τ1.setArr "wc" k (c0 k + 1))
        (uxC n (20 * (K + Nat.log 2 n) + 30) + 42) :=
      (Run.ite_true (by rw [hcond]; simp [hcr]) (Run.seq hr1 hst)).mono (by simp; omega)
    refine ⟨_, by rw [if_pos hcr]; exact hrun, by simp [hk1], ?_, ?_, ?_⟩
    · refine ⟨by simp [hwc1, hwc.len], fun x hx => ?_⟩
      simp only [arrs_setArr, if_true, hwc1]
      rw [List.getElem?_set]
      by_cases hxk : k = x
      · subst hxk
        simp [hwc.len, hkn, ckE, hcr, ind]
      · rw [if_neg hxk, hwc.get x hx]
        have : (x < k + 1 ∧ crN G x p1 p2) ↔ (x < k ∧ crN G x p1 p2) :=
          ⟨fun ⟨h1, h2⟩ => ⟨by omega, h2⟩, fun ⟨h1, h2⟩ => ⟨by omega, h2⟩⟩
        simp only [ckE, ind_eq_iff.2 this]
    · exact XiRep.mk' hR1 (by simp) (by simp) fun u _ v _ => by
        have := hdbl u v
        simp only [ckE_eq]
        rw [this, ind_eq_iff.2 (show crN G k u v ∧ crN G k p1 p2 ↔ crN G k u v from
          ⟨fun h => h.1, fun h => ⟨h, hcr⟩⟩)]
    · exact (hF1.mono (by simp [xW]) (by simp [xA])).setArr (by simp [xA]) _ _
  · have hrun : Run B xBody τ τ 37 :=
      (Run.ite_false (by rw [hcond]; simp [hcr]) Run.skip).mono (by simp)
    refine ⟨τ, by rw [if_neg hcr]; exact hrun, hk, ?_, ?_, Fr.refl _ _ τ⟩
    · refine hwc.congr fun x hx => ?_
      have : (x < k ∧ crN G x p1 p2) ↔ (x < k + 1 ∧ crN G x p1 p2) :=
        ⟨fun ⟨h1, h2⟩ => ⟨by omega, h2⟩, fun ⟨h1, h2⟩ => ⟨by
          rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | h
          · exact h
          · subst h; exact absurd h2 hcr, h2⟩⟩
      simp only [ckE, ind_eq_iff.2 this]
    · refine hrep.congr fun u _ v _ => ?_
      have := hdbl u v
      simp only [ckE_eq]
      rw [this]
      simp [ind, hcr]

/-- **Doubling the weights.** After the step `p1 p2`, the loop adds one
to the exponent of every vertex crossing `p1 p2` and updates all values. -/
theorem xLoop_run {B K p1 p2 : ℕ} {c0 : ℕ → ℕ} {σ : Env} (hB : WB n B) (hC : WCtx n G σ)
    (hK : K ≤ n) (hc0 : ∀ x < n, c0 x + ind (crN G x p1 p2) ≤ K)
    (hp1 : σ.vars "wbu" = p1) (hp2 : σ.vars "wbv" = p2) (hp1n : p1 < n) (hp2n : p2 < n)
    (hwc : Vec σ "wc" n c0) (hrep : XiRep n (xiP G c0 n) σ) :
    ∃ σ', Run B xLoop σ σ' (n * 45 + 6 + (∑ x ∈ range n, ind (crN G x p1 p2)) *
        (uxC n (20 * (K + Nat.log 2 n) + 30) + 5)) ∧
      Vec σ' "wc" n (fun x => c0 x + ind (crN G x p1 p2)) ∧
      XiRep n (xiP G (fun x => c0 x + ind (crN G x p1 p2)) n) σ' ∧ Fr xW xA σ σ' := by
  have hs := hB.small
  let q : ℕ → Prop := fun x => crN G x p1 p2
  let UX := uxC n (20 * (K + Nat.log 2 n) + 30)
  let c : ℕ → ℕ := fun k => if crN G k p1 p2 then UX + 42 else 37
  let I : ℕ → Env → Prop := fun k τ => Fr xW xA σ τ ∧ Vec τ "wc" n (ckE c0 q k) ∧
    XiRep n (xiP G (ckE c0 q k) n) τ
  have hCτ : ∀ τ, Fr xW xA σ τ → WCtx n G τ := fun τ hF => hC.fr hF (by decide) (by decide)
    (by decide)
  have h0 : ∀ x, ckE c0 q 0 x = c0 x := fun x => by simp [ckE, ind]
  obtain ⟨σ', hr, ⟨hF', hW', hR'⟩, -⟩ :=
    forUpV_run (B := B) (i := "wx") (e := .var "n") (body := xBody) (N := n) c I (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [(hCτ τ hI.1).hn]; omega), (hCτ τ hI.1).hn])
      (σ := σ) ⟨(Fr.refl xW xA σ).setVar (by simp [xW]) 0,
        Vec.of_eq (τ' := σ.setVar "wx" 0) (hwc.congr fun x _ => (h0 x).symm) rfl,
        XiRep.mk' hrep rfl rfl fun u _ v _ => xiP_congr (fun x _ => (h0 x).symm) u v⟩
      (by
        rintro k hk τ ⟨hFτ, hWτ, hRτ⟩ hwx
        obtain ⟨τ', hr', hk', hW', hR', hF'⟩ := xBody_run (B := B) (G := G) hB (hCτ τ hFτ) hK hc0
          (by rw [hFτ.vars _ (by decide), hp1]) (by rw [hFτ.vars _ (by decide), hp2]) hp1n hp2n
          hwx hk hWτ hRτ
        exact ⟨τ', hr', hk', (hFτ.trans hF').setVar (by simp [xW]) _, hW'.of_eq rfl,
          XiRep.mk' hR' rfl rfl fun _ _ _ _ => rfl⟩)
  have hfin : ∀ x < n, ckE c0 q n x = c0 x + ind (crN G x p1 p2) := fun x hx => by
    simp only [ckE, q]
    congr 1
    exact ind_eq_iff.2 ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
  refine ⟨σ', hr.mono ?_, hW'.congr hfin, XiRep.mk' hR' rfl rfl fun u _ v _ => xiP_congr hfin u v,
    hF'⟩
  have hc : ∀ k ∈ range n, c k + (Expr.var "n").size + 7 = 45 + ind (crN G k p1 p2) * (UX + 5) :=
    fun k _ => by
      simp only [c, size_var]
      by_cases h : crN G k p1 p2 <;> simp [h, ind]
      all_goals omega
  rw [sum_congr rfl hc, sum_add_distrib, ← sum_mul]
  simp only [sum_const, card_range, smul_eq_mul, size_var, UX]
  omega

end Lax185574Proofs.Chain.Ram
