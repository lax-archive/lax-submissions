import Lax185574Proofs.Chain.Ram.PdApp

/-!
The predamping procedure for one `A` and `κ`.

`PdSt` is the state of the procedure for the set `S` chosen so far,
listed in `Sl` in the order of choice. One application `pdApp` either
adds the vertex of `pdStep` or sets `stop` (`pdApp_run`). The loop
`pdLoop` runs applications until `stop` is set, and ends with `S`
equal to `predamp` (`pdLoop_run`). The cost of an application is
`appCost n r` plus the drop of the pointer potential `pdPot`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram Lax185574Proofs.Chain

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

/-- The state of the procedure after choosing `S`, listed by `sl`. -/
structure PdSt (n r : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (A : Finset (Fin n))
    (pf : ℕ → ℕ) (t1 t2 t3 : ℕ) (S : Finset (Fin n)) (sl : ℕ → ℕ) (τ : Env) : Prop where
  fix : PdFix n r G A pf t1 t2 t3 τ
  inS : Vec τ "inS" n (fun u => ind (inBN S u))
  slok : SlOK n S sl S.card
  sc : τ.vars "sc" = S.card
  hsl : ∀ j < S.card, (τ.arrs "Sl")[j]? = some (sl j)
  p2 : PtrOK n S.card (fun w s => t2 < hamN G (lbl n (tpN G (A ∪ S) r)) w s) sl
    (fun w => (τ.arrs "p2").getD w 0)
  p3 : PtrOK n S.card (fun w s => t3 ≤ betwN n pf (lbl n (tpN G (A ∪ S) r)) w s) sl
    (fun w => (τ.arrs "p3").getD w 0)
  ztab : Zero τ "tab"
  zcnt : Mat τ "cnt" n (fun _ _ => 0)
  zsz : Vec τ "sz" n (fun _ => 0)
  zmark : Vec τ "mark" n (fun _ => 0)

/-- Add the vertex found, or stop. -/
def addPhase : Com :=
  .ite (.lt (.var "fw") (.var "n"))
    (.seq (.store "inS" (.var "fw") (.lit 1))
      (.seq (.store "Sl" (.var "sc") (.var "fw")) (.assign "sc" (.add (.var "sc") (.lit 1)))))
    (.assign "stop" (.lit 1))

/-- One application of the rules. -/
def pdApp : Com := .seq prepCom (.seq r1Phase (.seq r23Phase addPhase))

/-- The cost of one application, besides the potential. -/
def appCost (n r : ℕ) : ℕ := prepCost n r + n * (n * 200 + 200) + 100 + r23Cost n + 40

variable {r : ℕ} {A : Finset (Fin n)} {pf : ℕ → ℕ} {t1 t2 t3 : ℕ}

theorem inBN_insert {S : Finset (Fin n)} {w : Fin n} {u : ℕ} :
    inBN (insert w S) u ↔ u = w ∨ inBN S u :=
  ⟨fun ⟨h, hm⟩ => (mem_insert.1 hm).elim (fun e => Or.inl (congrArg Fin.val e))
      (fun h' => Or.inr ⟨h, h'⟩),
    fun h => h.elim (fun e => ⟨e ▸ w.2, by simp [Fin.ext_iff, e]⟩)
      (fun ⟨h, hm⟩ => ⟨h, mem_insert_of_mem hm⟩)⟩

theorem pos_lt (o : VOrder (Fin n)) (x : Fin n) : o.pos x < n := by
  by_contra hc
  push Not at hc
  have hex : ∀ i : Fin (n + 1), ∃ y, o.pos y = i := fun i => by
    rcases Nat.lt_or_ge (i : ℕ) (o.pos x) with h | h
    · exact o.dense x i h
    · exact ⟨x, by have := i.2; omega⟩
  choose f hf using hex
  have hinj : Function.Injective f := fun i j h => by
    have := congrArg o.pos h; rw [hf, hf] at this; exact Fin.ext this
  have := Fintype.card_le_of_injective f hinj
  simp at this

theorem posN_lt (o : VOrder (Fin n)) {z : ℕ} (hz : z < n) : posN o z < n := by
  simp only [posN, dif_pos hz]; exact pos_lt o _

/-- **One application of the rules.** -/
theorem pdApp_run {B' : ℕ} (hB' : PdBound n B') (hrB : r < B') (ht1 : t1 < B') (ht2 : t2 < B')
    (ht3 : t3 < B') (o : VOrder (Fin n)) (hpfo : pf = posN o) (q κ : ℕ) (hκ : 1 ≤ κ)
    (e1 : t1 = 3 * (q + 1) * κ) (e2 : t2 = 5 * (3 * (q + 1)) * κ * κ)
    (e3 : t3 = 2 * (3 * (q + 1)) * κ)
    {S : Finset (Fin n)} {sl : ℕ → ℕ} {σ : Env} (hst : PdSt n r G A pf t1 t2 t3 S sl σ) :
    ∃ σ' K, Run B' pdApp σ σ' K ∧ K + pdPot n σ' ≤ appCost n r + pdPot n σ ∧
      (∀ x, x ∉ pdApp.wvars → σ'.vars x = σ.vars x) ∧
      (∀ a, a ∉ pdApp.warrs → σ'.arrs a = σ.arrs a) ∧
      ((∃ w, pdStep G (tpP G r) o A q κ S = some w ∧
          PdSt n r G A pf t1 t2 t3 (insert w S) (fun j => if j = S.card then w else sl j) σ' ∧
          σ'.vars "stop" = σ.vars "stop") ∨
        (pdStep G (tpP G r) o A q κ S = none ∧ PdSt n r G A pf t1 t2 t3 S sl σ' ∧
          σ'.vars "stop" = 1)) := by
  have hpf : ∀ z < n, pf z < n := fun z hz => by rw [hpfo]; exact posN_lt o hz
  have hB'' := hB'
  unfold PdBound at hB''
  obtain ⟨hF, hS, hslok, hsc, hsl, hP2, hP3, hz, hcnt, hsz, hmark⟩ := hst
  set L := lbl n (tpN G (A ∪ S) r) with hLdef
  have hL : IsLabels n L := isLabels_lbl (tpN_isEqv r)
  have hscn : S.card ≤ n := by
    have := card_le_univ S; simpa using this
  -- the first phase
  obtain ⟨σ1, hr1, hF1, ha1, hv1, hlab1, hcnt1, hsz1, hrep1, hz1⟩ :=
    prepCom_run (G := G) (A := A) (pf := pf) (t1 := t1) (t2 := t2) (t3 := t3) (S := S)
      (by unfold TpBound; omega) hrB hpf hF hS hz hcnt hsz
  rw [← hLdef] at hlab1 hcnt1 hsz1 hrep1
  -- rule (R1)
  obtain ⟨σ2, hr2, hF2, hfw2, ha2, hv2, hcnt2, hsz2⟩ :=
    r1Phase_run hB' ht1 hL hF1 hlab1 hcnt1 hsz1
  have hsc2 : σ2.vars "sc" = S.card := by
    rw [hv2 "sc" (by decide), hv1 "sc" (by decide), hsc]
  have hsl2 : ∀ j < S.card, (σ2.arrs "Sl")[j]? = some (sl j) := fun j hj => by
    rw [ha2 _ (by decide), ha1 _ (by decide)]; exact hsl j hj
  have hlab2 : Vec σ2 "lab" n L := hlab1.of_eq (ha2 _ (by decide))
  have hrep2 : Vec σ2 "rep" n (fun z => ind (isRepN n pf L z)) := hrep1.of_eq (ha2 _ (by decide))
  have hmark2 : Vec σ2 "mark" n (fun _ => 0) :=
    (hmark.of_eq (ha1 _ (by decide))).of_eq (ha2 _ (by decide))
  have hP22 : PtrOK n S.card (fun w s => t2 < hamN G L w s) sl
      (fun w => (σ2.arrs "p2").getD w 0) := by
    rw [ha2 _ (by decide), ha1 _ (by decide)]; exact hP2
  have hP32 : PtrOK n S.card (fun w s => t3 ≤ betwN n pf L w s) sl
      (fun w => (σ2.arrs "p3").getD w 0) := by
    rw [ha2 _ (by decide), ha1 _ (by decide)]; exact hP3
  -- rules (R2) and (R3)
  obtain ⟨σ3, K3, hr3, hF3, hfw3, hP23, hP33, hmark3, ha3, hsc3, hK3⟩ :=
    r23Phase_run hB' ht2 ht3 hL hpf hscn hslok.lt hF2 hlab2 hrep2 hsc2 hsl2 hmark2 hP22 hP32 hfw2
  -- the step of the procedure
  have hrules := rules_val (G := G) o r A q κ hslok
  rw [← e1, ← e2, ← e3, ← hLdef, ← hpfo] at hrules
  rw [← hrules] at hfw3
  have hpot : pdPot n σ2 = pdPot n σ := by
    apply pdPot_of_arrs <;> rw [ha2 _ (by decide), ha1 _ (by decide)]
  -- facts kept until the end of the rules
  have hS3 : Vec σ3 "inS" n (fun u => ind (inBN S u)) :=
    ((hS.of_eq (ha1 _ (by decide))).of_eq (ha2 _ (by decide))).of_eq (ha3 _ (by decide))
  have hsl3 : ∀ j < S.card, (σ3.arrs "Sl")[j]? = some (sl j) := fun j hj => by
    rw [ha3 _ (by decide)]; exact hsl2 j hj
  have hz3 : Zero σ3 "tab" := by
    intro t ht; rw [ha3 _ (by decide), ha2 _ (by decide)] at ht ⊢; exact hz1 t ht
  have hcnt3 : Mat σ3 "cnt" n (fun _ _ => 0) := hcnt2.of_eq (ha3 _ (by decide))
  have hsz3 : Vec σ3 "sz" n (fun _ => 0) := hsz2.of_eq (ha3 _ (by decide))
  have hstop3 : σ3.vars "stop" = σ.vars "stop" := by
    rw [hr3.frame_var "stop" (by decide), hv2 "stop" (by decide), hv1 "stop" (by decide)]
  have hrun3 : Run B' (.seq prepCom (.seq r1Phase r23Phase)) σ σ3
      (prepCost n r + (n * (n * 200 + 200) + 100 + K3)) := Run.seq hr1 (Run.seq hr2 hr3)
  have hfwev : (Cond.lt (.var "fw") (.var "n")).evalB B' σ3 =
      some (decide (σ3.vars "fw" < n)) := by
    have : σ3.vars "fw" ≤ n := by
      rw [hfw3]; cases h : pdStep G (tpP G r) o A q κ S with
      | none => simp
      | some w => simp
    rw [evalB_condLt (evalB_var (by omega)) (evalB_var (by rw [hF3.hn]; omega)), hF3.hn]
  cases hstep : pdStep G (tpP G r) o A q κ S with
  | some w =>
    rw [hstep] at hfw3
    simp only [Option.map_some, Option.getD_some] at hfw3
    have hwS : w ∉ S := pdStep_not_mem (tpP_selector G r) hκ hstep
    have hwn := w.2
    have hScn : S.card < n := by
      have := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2
        ⟨subset_univ S, fun h => hwS (h ▸ mem_univ w)⟩)
      simpa using this
    set σ4 := ((σ3.setArr "inS" w 1).setArr "Sl" S.card w).setVar "sc" (S.card + 1) with hσ4
    have hl3 : ∀ a ∈ ["inS", "Sl"], (σ3.arrs a).length = n := fun a ha => hF3.lvec a (by
      simp at ha ⊢; tauto)
    have hadd : Run B' addPhase σ3 σ4 24 :=
      (Run.ite_true (by rw [hfwev]; simp [hfw3])
        (Run.seq (Run.store (i := .var "fw") (e := .lit 1) (idx := w) (v := 1)
            (by simp [hfw3]; omega) (by simp; omega) (by rw [hl3 "inS" (by simp)]; exact hwn))
          (Run.seq (Run.store (i := .var "sc") (e := .var "fw") (idx := S.card) (v := w)
              (by simp [hsc3]; omega) (by simp [hfw3]; omega)
              (by simp; rw [hl3 "Sl" (by simp)]; omega))
            (Run.assign (by simp [hsc3]; omega))))).mono (by simp)
    have hrun : Run B' pdApp σ σ4 (prepCost n r + (n * (n * 200 + 200) + 100 + (K3 + 24))) :=
      Run.seq hr1 (Run.seq hr2 (Run.seq hr3 hadd))
    have hpot4 : pdPot n σ4 = pdPot n σ3 := pdPot_of_arrs (by simp [hσ4]) (by simp [hσ4])
    refine ⟨σ4, _, hrun, by rw [hpot4]; unfold appCost; omega,
      fun x hx => hrun.frame_var x hx, fun a ha => hrun.frame_arr a ha, Or.inl ⟨w, rfl, ?_, ?_⟩⟩
    · have hcard : (insert w S).card = S.card + 1 := card_insert_of_notMem hwS
      have hsub : A ∪ S ⊆ A ∪ insert w S := union_subset_union le_rfl (subset_insert _ _)
      have h4a : ∀ a, a ∉ ["inS", "Sl"] → σ4.arrs a = σ3.arrs a := fun a ha => by
        simp at ha
        simp only [hσ4, arrs_setVar, arrs_setArr, if_neg ha.1, if_neg ha.2]
      refine ⟨((hF3.setArr (by simp [fixArrs]) _ _).setArr (by simp [fixArrs]) _ _).setVar
          (by simp [fixVars]) _, ⟨by simp [hσ4, hS3.len], fun u hu => ?_⟩,
        by rw [hcard]; exact hslok.insert hwS, by rw [hcard]; simp [hσ4], fun j hj => ?_, ?_, ?_,
        fun t ht => by rw [h4a "tab" (by decide)] at ht ⊢; exact hz3 t ht,
        hcnt3.of_eq (h4a _ (by decide)), hsz3.of_eq (h4a _ (by decide)),
        hmark3.of_eq (h4a _ (by decide))⟩
      · simp only [hσ4, arrs_setVar, arrs_setArr, if_neg (show "inS" ≠ "Sl" by decide), if_true,
          List.getElem?_set]
        by_cases huw : (w : ℕ) = u
        · simp only [huw, if_true, hS3.len, hu]
          congr 1; symm; rw [ind_eq_one, inBN_insert]; exact Or.inl huw.symm
        · rw [if_neg huw, hS3.get u hu]
          congr 1; rw [ind_eq_iff, inBN_insert]
          exact ⟨fun h => Or.inr h, fun h => h.resolve_left (Ne.symm huw)⟩
      · rw [hcard] at hj
        simp only [hσ4, arrs_setVar, arrs_setArr, if_true, List.getElem?_set]
        have hlen : ((σ3.setArr "inS" (↑w) 1).arrs "Sl").length = n := by
          simp [hl3 "Sl" (by simp)]
        by_cases hjs : S.card = j
        · subst hjs; simp [hl3 "Sl" (by simp), hScn]
        · rw [if_neg hjs, if_neg (Ne.symm hjs)]
          simp only [arrs_setArr, if_neg (show "Sl" ≠ "inS" by decide)]
          exact hsl3 j (by omega)
      · rw [hcard]
        have := hP23.grow (F' := fun w' s => t2 < hamN G (lbl n (tpN G (A ∪ insert w S) r)) w' s)
          (fun w' s hw' hs h => lt_of_lt_of_le h (hamN_mono o hsub hw' hs)) hslok.lt w
        simpa [h4a "p2" (by decide)] using this
      · rw [hcard]
        have := hP33.grow
          (F' := fun w' s => t3 ≤ betwN n pf (lbl n (tpN G (A ∪ insert w S) r)) w' s)
          (fun w' s hw' hs h => by
            rw [hpfo] at h ⊢; exact le_trans h (betwN_mono o hsub hw' hs)) hslok.lt w
        simpa [h4a "p3" (by decide)] using this
    · simp only [hσ4, vars_setVar, if_neg (show "stop" ≠ "sc" by decide), vars_setArr, hstop3]
  | none =>
    rw [hstep] at hfw3
    simp only [Option.map_none, Option.getD_none] at hfw3
    have hadd : Run B' addPhase σ3 (σ3.setVar "stop" 1) 8 :=
      (Run.ite_false (by rw [hfwev]; simp [hfw3]) (Run.assign (by simp; omega))).mono (by simp)
    have hrun : Run B' pdApp σ (σ3.setVar "stop" 1)
        (prepCost n r + (n * (n * 200 + 200) + 100 + (K3 + 8))) :=
      Run.seq hr1 (Run.seq hr2 (Run.seq hr3 hadd))
    refine ⟨σ3.setVar "stop" 1, _, hrun, by rw [pdPot_setVar]; unfold appCost; omega,
      fun x hx => hrun.frame_var x hx, fun a ha => hrun.frame_arr a ha, Or.inr ⟨rfl, ?_, by simp⟩⟩
    exact ⟨hF3.setVar (by simp [fixVars]) _, hS3.of_eq rfl, hslok, by simp [hsc3],
      fun j hj => hsl3 j hj, hP23, hP33, fun t ht => hz3 t ht, hcnt3.of_eq rfl, hsz3.of_eq rfl,
      hmark3.of_eq rfl⟩

/-! ### The loop -/

/-- Apply the rules until none applies. -/
def pdLoop : Com := .seq (.assign "stop" (.lit 0)) (.while (.eq (.var "stop") (.lit 0)) pdApp)

/-- **The predamping procedure.** -/
theorem pdLoop_run {B' : ℕ} (hB' : PdBound n B') (hrB : r < B') (ht1 : t1 < B') (ht2 : t2 < B')
    (ht3 : t3 < B') (o : VOrder (Fin n)) (hpfo : pf = posN o) (q κ : ℕ) (hκ : 1 ≤ κ)
    (e1 : t1 = 3 * (q + 1) * κ) (e2 : t2 = 5 * (3 * (q + 1)) * κ * κ)
    (e3 : t3 = 2 * (3 * (q + 1)) * κ)
    {sl : ℕ → ℕ} {σ : Env} (hst : PdSt n r G A pf t1 t2 t3 ∅ sl σ) :
    ∃ σ' K sl', Run B' pdLoop σ σ' K ∧
      PdSt n r G A pf t1 t2 t3 (predamp G (tpP G r) o A q κ) sl' σ' ∧
      K + pdPot n σ' ≤ (n + 2) * (appCost n r + 20) + 10 + pdPot n σ ∧
      (∀ x, x ∉ pdLoop.wvars → σ'.vars x = σ.vars x) ∧
      (∀ a, a ∉ pdLoop.warrs → σ'.arrs a = σ.arrs a) := by
  have hB'' := hB'
  unfold PdBound at hB''
  let J : Env → Prop := fun τ => ∃ (S : Finset (Fin n)) (sl : ℕ → ℕ),
    PdSt n r G A pf t1 t2 t3 S sl τ ∧ S = pdRun G (tpP G r) o A q κ S.card ∅ ∧
    (τ.vars "stop" = 0 ∨ (τ.vars "stop" = 1 ∧ pdStep G (tpP G r) o A q κ S = none))
  let Ψ : Env → ℕ := fun τ => (appCost n r + 20) * (n + 2 - τ.vars "sc" - τ.vars "stop") +
    pdPot n τ
  have hJ0 : J (σ.setVar "stop" 0) := ⟨∅, sl, by
      obtain ⟨hF, hS, hslok, hsc, hsl, hP2, hP3, hz, hcnt, hsz, hmark⟩ := hst
      exact ⟨hF.setVar (by simp [fixVars]) _, hS.of_eq rfl, hslok, by simp [hsc], hsl, hP2, hP3,
        hz, hcnt.of_eq rfl, hsz.of_eq rfl, hmark.of_eq rfl⟩, by simp [pdRun], Or.inl (by simp)⟩
  obtain ⟨σ', K, hr, ⟨S, sl', hst', hSrun, hstop'⟩, hfalse, hK⟩ :=
    Run.while_potential (B := B') (b := .eq (.var "stop") (.lit 0)) (c := pdApp) J Ψ
      (fun τ ⟨S, sl, h, _, hs⟩ => ⟨_, eq_lit_evalB (by rcases hs with h' | h' <;> omega)
        (by omega)⟩)
      (by
        rintro τ ⟨S, sl, hst, hSrun, hs⟩ hc
        have hs0 : τ.vars "stop" = 0 := by
          rw [eq_lit_evalB (by rcases hs with h' | h' <;> omega) (by omega)] at hc
          simpa using hc
        have hcn : S.card ≤ n := by have := card_le_univ S; simpa using this
        have hscv := hst.sc
        obtain ⟨τ', K, hr, hK, hfv, hfa, hres⟩ :=
          pdApp_run hB' hrB ht1 ht2 ht3 o hpfo q κ hκ e1 e2 e3 hst
        rcases hres with ⟨w, hw, hst', hstop'⟩ | ⟨hnone, hst', hstop'⟩
        · have hwS : w ∉ S := pdStep_not_mem (tpP_selector G r) hκ hw
          have hcard : (insert w S).card = S.card + 1 := card_insert_of_notMem hwS
          have hcn' : S.card + 1 ≤ n := by
            have := card_le_univ (insert w S); simp at this; omega
          refine ⟨τ', K, hr, ⟨insert w S, _, hst', ?_, Or.inl (by rw [hstop', hs0])⟩, ?_⟩
          · rw [hcard]
            have := pdRun_succ_of_some (j := S.card) (A := A) (q := q) (κ := κ) (o := o)
              (G := G) (r := r) (w := w) (by rw [← hSrun]; exact hw)
            rw [this, ← hSrun]
          · simp only [Ψ, hst'.sc, hcard, hstop', hs0, hscv, Cond.size, Expr.size]
            have : n + 2 - S.card - 0 = (n + 2 - (S.card + 1) - 0) + 1 := by omega
            rw [this, Nat.mul_add, mul_one]
            omega
        · refine ⟨τ', K, hr, ⟨S, sl, hst', hSrun, Or.inr ⟨hstop', hnone⟩⟩, ?_⟩
          simp only [Ψ, hst'.sc, hstop', hs0, hscv, Cond.size, Expr.size]
          have : n + 2 - S.card - 0 = (n + 2 - S.card - 1) + 1 := by omega
          rw [this, Nat.mul_add, mul_one]
          omega)
      hJ0
  have hs1 : σ'.vars "stop" = 1 ∧ pdStep G (tpP G r) o A q κ S = none := by
    rcases hstop' with h | h
    · rw [eq_lit_evalB (by omega) (by omega)] at hfalse; simp [h] at hfalse
    · exact h
  have hcn : S.card ≤ n := by have := card_le_univ S; simpa using this
  have hpre : predamp G (tpP G r) o A q κ = S := by
    rw [predamp_eq (j := S.card) (by omega) (by rw [← hSrun]; exact hs1.2), ← hSrun]
  have hrun : Run B' pdLoop σ σ' (2 + K) := Run.seq (Run.assign (v := 0) (by simp; omega)) hr
  refine ⟨σ', 2 + K, sl', hrun, by rw [hpre]; exact hst', ?_, fun x hx => hrun.frame_var x hx,
    fun a ha => hrun.frame_arr a ha⟩
  have h0 : Ψ (σ.setVar "stop" 0) = (appCost n r + 20) * (n + 2) + pdPot n σ := by
    show (appCost n r + 20) * (n + 2 - (σ.setVar "stop" 0).vars "sc" -
      (σ.setVar "stop" 0).vars "stop") + pdPot n (σ.setVar "stop" 0) = _
    rw [pdPot_setVar]; simp [hst.sc]
  have h1 : pdPot n σ' ≤ Ψ σ' := Nat.le_add_left _ _
  rw [h0] at hK
  simp only [Cond.size, Expr.size] at hK
  have : (appCost n r + 20) * (n + 2) = (n + 2) * (appCost n r + 20) := Nat.mul_comm _ _
  omega

end Lax185574Proofs.Chain.Ram
