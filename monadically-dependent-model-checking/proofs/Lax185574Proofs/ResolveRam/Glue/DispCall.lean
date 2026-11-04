import Lax185574Proofs.ResolveRam.Glue.CaseKB

/-!
The dispatcher at a position that is followed by a call (`disp_call`).

At every valid position `c` other than the scatter type whose next
position carries a call, the dispatcher does what a case of a round must
do (`DCase`), with a plan that gives the next state (`DPlan`), a library
that is small relative to the state, the answer and the output
(`LibSm`), and a cost that is at most a constant times `(n + 1) Y^B`,
given the bounds `SzKit` with constants `C` and `A`.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574Proofs.Words Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.ResolveRam
open Lax185574Proofs.TypeTreeSizes Lax3.DistFO

/-- The sum of the constants of the pieces. -/
noncomputable def cPc {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV) : ℕ :=
  cFA + cEx + cUp hAt hAV + cAt hAt hAV + cKd

/-- The sum of the exponents of the pieces. -/
noncomputable def aPc {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV) : ℕ :=
  aFA + aEx + aUp hAt hAV + aAt hAt hAV + aKd

/-- The constant of the cost of a case. -/
noncomputable def kqOf {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV)
    (C k₀ q₀ : ℕ) : ℕ :=
  (cPc hAt hAV + 1) * czOf C k₀ q₀ * (czOf C k₀ q₀ + 1) ^ aPc hAt hAV + czOf C k₀ q₀ + C + 1

theorem one_le_cz (C k₀ q₀ : ℕ) : 1 ≤ czOf C k₀ q₀ := by unfold czOf; omega

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

section Unit

variable {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV) (C A : ℕ)

/-- The unit of the cost of a case. -/
noncomputable def vU : ℕ :=
  kqOf hAt hAV C k₀ q₀ * ((n + 1) * yQ G P Q s k₀ q₀ ^ (2 * A * (aPc hAt hAV + 1)))

theorem one_le_vU : 1 ≤ vU G P Q s k₀ q₀ hAt hAV C A := by
  have h1 := one_le_U (A := 2 * A * (aPc hAt hAV + 1)) (N := n + 1) (by omega) (one_le_yQ G P Q s k₀ q₀)
  have h2 : 1 ≤ kqOf hAt hAV C k₀ q₀ := by unfold kqOf; omega
  unfold vU
  simpa using Nat.mul_le_mul h2 h1

theorem U_ge : (n + 1) * yQ G P Q s k₀ q₀ ^ A ≤ (n + 1) * yQ G P Q s k₀ q₀ ^ (2 * A * (aPc hAt hAV + 1)) :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (one_le_yQ G P Q s k₀ q₀) (by nlinarith))

theorem le_vU {x : ℕ} (h : x ≤ C * ((n + 1) * yQ G P Q s k₀ q₀ ^ A)) : x ≤ vU G P Q s k₀ q₀ hAt hAV C A := by
  unfold vU
  exact le_trans h (Nat.mul_le_mul (by unfold kqOf; omega) (U_ge G P Q s k₀ q₀ hAt hAV A))

theorem le_vU_nf {x : ℕ} (h : x ≤ C * yQ G P Q s k₀ q₀ ^ A) : x ≤ vU G P Q s k₀ q₀ hAt hAV C A :=
  le_vU G P Q s k₀ q₀ hAt hAV C A (nf_lin (by omega) h)

theorem le_vU_cz {x : ℕ} (h : x ≤ czOf C k₀ q₀) : x ≤ vU G P Q s k₀ q₀ hAt hAV C A := by
  have := one_le_U (A := 2 * A * (aPc hAt hAV + 1)) (N := n + 1) (by omega) (one_le_yQ G P Q s k₀ q₀)
  unfold vU
  calc x ≤ kqOf hAt hAV C k₀ q₀ * 1 := by unfold kqOf; omega
    _ ≤ _ := Nat.mul_le_mul_left _ this

theorem le_vU_pc {x c : ℕ} (hc : c ≤ cPc hAt hAV)
    (h : x ≤ c * czOf C k₀ q₀ * (czOf C k₀ q₀ + 1) ^ aPc hAt hAV *
      ((n + 1) * yQ G P Q s k₀ q₀ ^ (2 * A * (aPc hAt hAV + 1)))) : x ≤ vU G P Q s k₀ q₀ hAt hAV C A := by
  unfold vU
  refine le_trans h (Nat.mul_le_mul_right _ ?_)
  unfold kqOf
  have : c * czOf C k₀ q₀ * (czOf C k₀ q₀ + 1) ^ aPc hAt hAV ≤
      (cPc hAt hAV + 1) * czOf C k₀ q₀ * (czOf C k₀ q₀ + 1) ^ aPc hAt hAV :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by omega))
  omega

theorem le_vU_y2 {x : ℕ} (h : x ≤ czOf C k₀ q₀ * yQ G P Q s k₀ q₀ ^ (2 * A)) :
    x ≤ vU G P Q s k₀ q₀ hAt hAV C A := by
  have hY := one_le_yQ G P Q s k₀ q₀
  have h1 : yQ G P Q s k₀ q₀ ^ (2 * A) ≤ (n + 1) * yQ G P Q s k₀ q₀ ^ (2 * A * (aPc hAt hAV + 1)) :=
    le_trans (Nat.pow_le_pow_right hY (by nlinarith)) (Nat.le_mul_of_pos_left _ (by omega))
  unfold vU
  exact le_trans h (Nat.mul_le_mul (by unfold kqOf; omega) h1)

end Unit

/-! ### The cases with their costs -/

/-- A case of the dispatcher at `c` with a small library and a cost of at most `8000 V`. -/
def DOk (atC bR1 : Com) (c : Cur) (V : ℕ) : Prop :=
  ∃ L ps KB, DCase G P Q s k₀ q₀ (disp atC bR1) c L ps KB ∧ DPlan G P Q s k₀ q₀ c L ps ∧
    LibSm L (swAt G P Q s k₀ q₀ c).ws (rY G k₀ q₀ (callOf G P Q s k₀ q₀ c))
      (oOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ c)) ∧ KB ≤ 8000 * V

/-- The sizes of a case: the answer, the state, the next state and the next query. -/
structure Atoms (c : Cur) (Z : ℕ) : Prop where
  b : (rY G k₀ q₀ (callOf G P Q s k₀ q₀ c)).length ≤ Z
  ws : tot (swAt G P Q s k₀ q₀ c).ws ≤ Z
  nws : tot (swAt G P Q s k₀ q₀ (next G P Q s k₀ q₀ c)).ws ≤ Z
  q : (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ c))).length ≤ Z

theorem total_le_tot (ws : List (List ℕ)) : total ws ≤ tot ws := by rw [tot_eq]; omega

/-- A word of the plan is a word of the next state. -/
theorem plan_tot {L : List (List ℕ)} {ps : List (ℕ × ℕ)} {ws : List (List ℕ)} {j : ℕ}
    (hpl : planW L ps = ws) (hp : (j, 1) ∈ ps) (hj : j < L.length) : L[j].length < tot ws := by
  have := mem_plan hp hj; rw [hpl] at this; exact length_lt_tot this

/-- A range of the plan is a part of the next state. -/
theorem plan_rng_tot {L : List (List ℕ)} {ps : List (ℕ × ℕ)} {ws : List (List ℕ)} {p : ℕ × ℕ}
    (hpl : planW L ps = ws) (hp : p ∈ ps) : tot (rng L p.1 p.2) ≤ tot ws := by
  have := mem_rng_plan (L := L) hp; rw [hpl] at this; exact tot_infix this

theorem LL_tot (c : Cur) : (swAt G P Q s k₀ q₀ c).LL.length < tot (swAt G P Q s k₀ q₀ c).ws :=
  length_lt_tot (by rw [SW.ws_eq]; simp)

theorem CO_tot (c : Cur) : tot (swAt G P Q s k₀ q₀ c).CO ≤ tot (swAt G P Q s k₀ q₀ c).ws := by
  rw [SW.ws_eq]; simp only [tot_cons, tot_append]; omega

section Cases

variable {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV) {C A : ℕ}
  (hK : SzKit G P Q s k₀ q₀ C A) (hk : 1 ≤ k₀)

include hK hk

theorem itm_mem {d i : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    itm G P Q s k₀ q₀ d i ∈ lvR G P Q s k₀ q₀ d := by
  rw [itm_eq G P Q s k₀ q₀ hi]; exact List.getElem_mem hi

/-- The cost of the end of an item. -/
theorem kFE_le {d i m : ℕ} {b : List ℕ} (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hb : b.length ≤ vU G P Q s k₀ q₀ hAt hAV C A)
    (hws : tot (swAt G P Q s k₀ q₀ (.dn d i m)).ws ≤ vU G P Q s k₀ q₀ hAt hAV C A)
    (hE : tot (exE G P Q s k₀ q₀ d i) ≤ vU G P Q s k₀ q₀ hAt hAV C A) :
    kFE G P Q s k₀ q₀ d i m b ≤ 1700 * vU G P Q s k₀ q₀ hAt hAV C A := by
  set V := vU G P Q s k₀ q₀ hAt hAV C A
  have hx := itm_mem G P Q s k₀ q₀ hK hk hi
  have hco := coW_le G P Q s k₀ q₀ hK hk hd hx
  have hco' : tot (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2) ≤ V := by
    rw [tot_eq]
    exact le_vU_y2 G P Q s k₀ q₀ hAt hAV C A (le_trans hco (Nat.mul_le_mul_right _ (by unfold czOf; nlinarith)))
  have hEx := le_vU_pc G P Q s k₀ q₀ hAt hAV C A (c := cEx) (by unfold cPc; omega)
    (kEx_le G P Q s k₀ q₀ hK hk hd hi (E := aPc hAt hAV) (by unfold aPc; omega))
  have hdV := le_vU_cz G P Q s k₀ q₀ hAt hAV C A (x := d) (by unfold czOf; omega)
  have t1 := total_le_tot ((swAt G P Q s k₀ q₀ (.dn d i m)).ws ++ [] :: coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2)
  rw [tot_append, tot_cons] at t1
  have t2 := total_le_tot (exE G P Q s k₀ q₀ d i)
  have t3 := length_le_tot (exE G P Q s k₀ q₀ d i)
  have hV := one_le_vU G P Q s k₀ q₀ hAt hAV C A
  unfold kFE kFinE
  simp only [List.length_nil] at t1
  omega

/-- The cost of the branch to the next position after an item. -/
theorem kBr_le {d i m : ℕ} {b : List ℕ} {c' : Cur} (hd : d < q₀)
    (hc' : ∀ d' j m', c' = .up d' j m' → d' ≤ q₀)
    (hb : b.length ≤ vU G P Q s k₀ q₀ hAt hAV C A)
    (hws : tot (swAt G P Q s k₀ q₀ (.dn d i m)).ws ≤ vU G P Q s k₀ q₀ hAt hAV C A)
    (hE : tot (exE G P Q s k₀ q₀ d i) ≤ vU G P Q s k₀ q₀ hAt hAV C A)
    (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hnws : tot (swAt G P Q s k₀ q₀ c').ws ≤ vU G P Q s k₀ q₀ hAt hAV C A)
    (hq : (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ c')).length ≤ vU G P Q s k₀ q₀ hAt hAV C A) :
    kBr G P Q s k₀ q₀ hAt hAV d i m b c' ≤ 2500 * vU G P Q s k₀ q₀ hAt hAV C A := by
  set V := vU G P Q s k₀ q₀ hAt hAV C A
  have hV := one_le_vU G P Q s k₀ q₀ hAt hAV C A
  have hqV := le_vU_cz G P Q s k₀ q₀ hAt hAV C A (x := q₀) (by unfold czOf; omega)
  cases c' with
  | up d' j m' =>
    have hd' := hc' d' j m' rfl
    have hx := itm_mem G P Q s k₀ q₀ hK hk hi
    have hco := coW_le G P Q s k₀ q₀ hK hk hd hx
    have hco' : tot (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2) ≤ V := by
      rw [tot_eq]
      exact le_vU_y2 G P Q s k₀ q₀ hAt hAV C A (le_trans hco (Nat.mul_le_mul_right _ (by unfold czOf; nlinarith)))
    have hU := le_vU_pc G P Q s k₀ q₀ hAt hAV C A (c := cUp hAt hAV) (by unfold cPc; omega)
      (kAtom_le G P Q s k₀ q₀ hK hk (d := d') (i := 0) (cA := cUp hAt hAV) (aA := aUp hAt hAV)
        (E := aPc hAt hAV) hd' (by unfold aPc; omega))
    have hLL := LL_tot G P Q s k₀ q₀ (.up d' j m')
    have t1 := total_le_tot (finL1 G P Q s k₀ q₀ d i m ++ [(swAt G P Q s k₀ q₀ (.up d' j m')).LL])
    have t2 : tot (finL1 G P Q s k₀ q₀ d i m ++ [(swAt G P Q s k₀ q₀ (.up d' j m')).LL]) =
        tot (swAt G P Q s k₀ q₀ (.dn d i m)).ws + 1 + tot (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2) +
          tot (exE G P Q s k₀ q₀ d i) + ((swAt G P Q s k₀ q₀ (.up d' j m')).LL.length + 1) := by
      simp only [finL1, tot_append, tot_cons, tot_nil, List.length_nil]; omega
    simp only [kBr, kUp, kAtT]
    omega
  | _ => simp only [kBr]; omega

end Cases

theorem rng_fin (ws C E X : List (List ℕ)) :
    rng (ws ++ [] :: C ++ E ++ X) (ws.length + 1 + C.length) E.length = E := by
  have e : ws ++ [] :: C ++ E ++ X = (ws ++ [] :: C) ++ (E ++ X) := by simp
  have hl : (ws ++ [] :: C).length = ws.length + 1 + C.length := by simp; omega
  rw [e, ← hl]
  simp [rng, List.drop_left]

theorem finNew_len (c : Cur) : (finNew G P Q s k₀ q₀ c).length ≤ 2 := by
  cases c <;> simp [finNew]

theorem finNew_ok (c' : Cur) (hne : ∀ d j m, c' = .up d j m → callOf G P Q s k₀ q₀ c' ≠ .stp) :
    ∀ w ∈ finNew G P Q s k₀ q₀ c', w.length ≤ (oOf G P Q s k₀ q₀ c').length ∧
      ∀ e ∈ w, e ≤ maxEntry (oOf G P Q s k₀ q₀ c') := by
  have hLL : (swAt G P Q s k₀ q₀ c').LL ∈ (swAt G P Q s k₀ q₀ c').ws := by rw [SW.ws_eq]; simp
  cases c' with
  | up d j m =>
    intro w hw
    simp only [finNew, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact oOf_ws G P Q s k₀ q₀ hLL
    · exact oOf_q G P Q s k₀ q₀ (hne d j m rfl)
  | stp => intro w hw; simp only [finNew, List.mem_singleton] at hw; subst hw; exact oOf_ws G P Q s k₀ q₀ hLL
  | dn d j m => intro w hw; simp only [finNew, List.mem_singleton] at hw; subst hw; exact oOf_ws G P Q s k₀ q₀ hLL
  | fin => intro w hw; simp only [finNew, List.mem_singleton] at hw; subst hw; exact oOf_ws G P Q s k₀ q₀ hLL

theorem up_le_of_next {c : Cur} (hv : Valid G P Q s k₀ q₀ c) :
    ∀ d' j m', next G P Q s k₀ q₀ c = .up d' j m' → d' ≤ q₀ := by
  intro d' j m' h
  rcases (rest_step G P Q s k₀ q₀ hv).2 with h1 | h1 <;> rw [h] at h1
  · exact h1.1
  · cases h1

theorem callOf_next_ne {c : Cur} (hv : Valid G P Q s k₀ q₀ c) (hnf : next G P Q s k₀ q₀ c ≠ .fin) :
    callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ c) ≠ .stp :=
  callOf_ne_stp G P Q s k₀ q₀ (((rest_step G P Q s k₀ q₀ hv).2).resolve_right hnf) (next_ne_stp G P Q s k₀ q₀ c)

/-- The answers of the compositions at the last composition of an item. -/
theorem coW_last {d i m : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) (hm2 : 2 ≤ m)
    (hm : m + 1 = nDn G P Q s k₀ q₀ d i) :
    coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2 =
      (swAt G P Q s k₀ q₀ (.dn d i m)).CO ++ [realY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i m))] := by
  have hnd := nDn_itm (G := G) (P := P) (Q := Q) (s := s) (k₀ := k₀) (q₀ := q₀) hi
  obtain ⟨hb0, hc0⟩ := callOf_dn_comp G P Q s k₀ q₀ hi hm2 (by omega)
  rw [hc0]
  have hCOw : (swAt G P Q s k₀ q₀ (.dn d i m)).CO = (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2).take (m - 2) := by
    simp [swAt]
  have hlen : (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2).length = m - 2 + 1 := by rw [length_coW]; omega
  have e1 : coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2 = (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2).take (m - 2 + 1) :=
    (List.take_of_length_le (by omega)).symm
  have : (swAt G P Q s k₀ q₀ (.dn d i m)).CO ++ [realY G k₀ q₀ (.compose (shOf G (itm G P Q s k₀ q₀ d i).2)
      (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2)[m - 2])] = coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2 := by
    rw [hCOw]
    conv_rhs => rw [e1, List.take_add_one, List.getElem?_eq_getElem (by omega)]
    simp [coW, realY]
  exact this.symm

/-- **The library at the end of an item.** -/
theorem fin_lib {d i m : ℕ} (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hm : m + 1 = nDn G P Q s k₀ q₀ d i) {b : List ℕ}
    (hC : tot (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2) ≤ tot (swAt G P Q s k₀ q₀ (.dn d i m)).ws + b.length + 1)
    (hCe : ∀ w ∈ coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2, ∀ e ∈ w,
      e ≤ maxEntry (toWord (swAt G P Q s k₀ q₀ (.dn d i m)).ws) + maxEntry b) :
    LibSm (finL1 G P Q s k₀ q₀ d i m ++ finNew G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m)))
      (swAt G P Q s k₀ q₀ (.dn d i m)).ws b (oOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m))) := by
  have hp := plan_fin G P Q s k₀ q₀ hd hi hm
  unfold DPlan at hp
  have hv : Valid G P Q s k₀ q₀ (.dn d i m) := ⟨hd, hi, by omega⟩
  have hne : ∀ d' j m', next G P Q s k₀ q₀ (.dn d i m) = .up d' j m' →
      callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m)) ≠ .stp := by
    intro d' j m' h
    exact callOf_next_ne G P Q s k₀ q₀ hv (by rw [h]; simp)
  exact libSm_fin G P Q s k₀ q₀ (C := coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2) (E := exE G P Q s k₀ q₀ d i)
    (X := finNew G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m))) hp.1 (by simp [finPs, psFin]) hC hCe
    (finNew_len G P Q s k₀ q₀ _) (finNew_ok G P Q s k₀ q₀ _ hne)

/-- The expansion of an item is a part of the next state. -/
theorem fin_exE {d i m : ℕ} (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hm : m + 1 = nDn G P Q s k₀ q₀ d i) :
    tot (exE G P Q s k₀ q₀ d i) ≤ tot (swAt G P Q s k₀ q₀ (next G P Q s k₀ q₀ (.dn d i m))).ws := by
  have hp := plan_fin G P Q s k₀ q₀ hd hi hm
  unfold DPlan at hp
  have := plan_rng_tot hp.1 (p := ((swAt G P Q s k₀ q₀ (.dn d i m)).ws.length + 1 +
    (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2).length, (exE G P Q s k₀ q₀ d i).length)) (by simp [finPs, psFin])
  simp only [finL1] at this
  rw [rng_fin] at this
  exact this

section Cases2

variable {atC : Com} {atV : List String} (hAt : AtSpec atC atV) (hAV : ∀ y ∈ atKeep, y ∉ atV) {C A : ℕ}
  (hK : SzKit G P Q s k₀ q₀ C A) (hk : 1 ≤ k₀)

include hK hk

theorem ok_shift {bR1 : Com} {d i : ℕ} (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hA : Atoms G P Q s k₀ q₀ (.dn d i 0) (C * ((n + 1) * yQ G P Q s k₀ q₀ ^ A))) :
    DOk G P Q s k₀ q₀ atC bR1 (.dn d i 0) (vU G P Q s k₀ q₀ hAt hAV C A) := by
  have hp := plan_dn0 G P Q s k₀ q₀ hi
  have hp' := hp
  unfold DPlan at hp'
  refine ⟨_, _, _, disp_dn0 G P Q s k₀ q₀ hi, hp, libSm_two G P Q s k₀ q₀ hp'.1 (by simp [psRep1]), ?_⟩
  have h1 := le_vU G P Q s k₀ q₀ hAt hAV C A hA.b
  have h2 := le_vU_cz G P Q s k₀ q₀ hAt hAV C A (x := d) (by unfold czOf; omega)
  have h3 := one_le_vU G P Q s k₀ q₀ hAt hAV C A
  unfold kShift; omega

theorem ok_comp {bR1 : Com} {d i m : ℕ} (hi : i < (lvR G P Q s k₀ q₀ d).length) (hm2 : 2 ≤ m)
    (hmn : m + 1 < nDn G P Q s k₀ q₀ d i)
    (hA : Atoms G P Q s k₀ q₀ (.dn d i m) (C * ((n + 1) * yQ G P Q s k₀ q₀ ^ A))) :
    DOk G P Q s k₀ q₀ atC bR1 (.dn d i m) (vU G P Q s k₀ q₀ hAt hAV C A) := by
  have hp := plan_comp G P Q s k₀ q₀ hi hm2 hmn
  have hp' := hp
  unfold DPlan at hp'
  refine ⟨_, _, _, disp_comp G P Q s k₀ q₀ hi hm2 hmn, hp, libSm_two G P Q s k₀ q₀ hp'.1 (by simp [psComp]), ?_⟩
  have h1 := le_vU G P Q s k₀ q₀ hAt hAV C A hA.b
  have h3 := one_le_vU G P Q s k₀ q₀ hAt hAV C A
  unfold kComp; omega

/-- The total length of the members of the far tree. -/
theorem faW_le {d i : ℕ} (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length) :
    total ((faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).map toWord) ≤ vU G P Q s k₀ q₀ hAt hAV C A ∧
      (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).length ≤ vU G P Q s k₀ q₀ hAt hAV C A := by
  have hx := itm_mem G P Q s k₀ q₀ hK hk hi
  have hFl := faP_le G P Q s k₀ q₀ hK hk hd hx
  have hFm : ∀ w ∈ (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).map toWord,
      w.length ≤ C * yQ G P Q s k₀ q₀ ^ A := by
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨ν, hν, rfl⟩ := hw
    exact hK.fa d hd _ hx ν (List.mem_filter.1 hν).1
  have hFt := total_le_mul hFm
  rw [List.length_map] at hFt
  refine ⟨le_vU_y2 G P Q s k₀ q₀ hAt hAV C A ?_, le_vU_nf G P Q s k₀ q₀ hAt hAV C A hFl⟩
  have e : yQ G P Q s k₀ q₀ ^ (2 * A) = yQ G P Q s k₀ q₀ ^ A * yQ G P Q s k₀ q₀ ^ A := by rw [two_mul, pow_add]
  rw [e]
  calc _ ≤ (C * yQ G P Q s k₀ q₀ ^ A) * (C * yQ G P Q s k₀ q₀ ^ A) := le_trans hFt (Nat.mul_le_mul_right _ hFl)
    _ = (C * C) * (yQ G P Q s k₀ q₀ ^ A * yQ G P Q s k₀ q₀ ^ A) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (by unfold czOf; nlinarith)

theorem ok_ft {bR1 : Com} {d i : ℕ} (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hF : 0 < (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).length)
    (hA : Atoms G P Q s k₀ q₀ (.dn d i 1) (C * ((n + 1) * yQ G P Q s k₀ q₀ ^ A))) :
    DOk G P Q s k₀ q₀ atC bR1 (.dn d i 1) (vU G P Q s k₀ q₀ hAt hAV C A) := by
  have hp := plan_dn1 G P Q s k₀ q₀ hi hF
  have hp' := hp
  unfold DPlan at hp'
  refine ⟨_, _, _, disp_dn1 G P Q s k₀ q₀ hk hd hi hF, hp, libSm_ft G P Q s k₀ q₀ hp'.1 (by simp [psFt]), ?_⟩
  have hFA := le_vU_pc G P Q s k₀ q₀ hAt hAV C A (c := cFA) (by unfold cPc; omega)
    (kFA_le G P Q s k₀ q₀ hK hk hd hi hA.b (E := aPc hAt hAV) (by unfold aPc; omega))
  obtain ⟨hF1, hF2⟩ := faW_le G P Q s k₀ q₀ hAt hAV hK hk hd hi
  have h1 := le_vU G P Q s k₀ q₀ hAt hAV C A hA.b
  have h2 := le_vU G P Q s k₀ q₀ hAt hAV C A hA.ws
  have h3 := total_le_tot (swAt G P Q s k₀ q₀ (.dn d i 1)).ws
  have h4 := one_le_vU G P Q s k₀ q₀ hAt hAV C A
  unfold kFt; rw [List.length_map]; omega

/-- The sizes of the end of an item. -/
theorem fin_atoms {d i m : ℕ} (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hm : m + 1 = nDn G P Q s k₀ q₀ d i)
    (hA : Atoms G P Q s k₀ q₀ (.dn d i m) (C * ((n + 1) * yQ G P Q s k₀ q₀ ^ A))) :
    kFE G P Q s k₀ q₀ d i m (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i m))) + 104 +
      kBr G P Q s k₀ q₀ hAt hAV d i m (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i m)))
        (next G P Q s k₀ q₀ (.dn d i m)) ≤ 4400 * vU G P Q s k₀ q₀ hAt hAV C A := by
  have hv : Valid G P Q s k₀ q₀ (.dn d i m) := ⟨hd, hi, by omega⟩
  have hE := le_trans (fin_exE G P Q s k₀ q₀ hd hi hm) hA.nws
  have hE' := le_vU G P Q s k₀ q₀ hAt hAV C A hE
  have h1 := le_vU G P Q s k₀ q₀ hAt hAV C A hA.b
  have h2 := le_vU G P Q s k₀ q₀ hAt hAV C A hA.ws
  have h3 := le_vU G P Q s k₀ q₀ hAt hAV C A hA.nws
  have h4 := le_vU G P Q s k₀ q₀ hAt hAV C A hA.q
  have k1 := kFE_le G P Q s k₀ q₀ hAt hAV hK hk (m := m) hd hi h1 h2 hE'
  have k2 := kBr_le G P Q s k₀ q₀ hAt hAV hK hk (m := m) hd (up_le_of_next G P Q s k₀ q₀ hv) h1 h2 hE' hi h3 h4
  have h5 := one_le_vU G P Q s k₀ q₀ hAt hAV C A
  omega

theorem ok_fin1 {bR1 : Com} {d i : ℕ} (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hF0 : (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).length = 0)
    (hA : Atoms G P Q s k₀ q₀ (.dn d i 1) (C * ((n + 1) * yQ G P Q s k₀ q₀ ^ A))) :
    DOk G P Q s k₀ q₀ atC bR1 (.dn d i 1) (vU G P Q s k₀ q₀ hAt hAV C A) := by
  have hm : 1 + 1 = nDn G P Q s k₀ q₀ d i := by rw [nDn_itm (G := G) (P := P) (Q := Q) (s := s) (k₀ := k₀) (q₀ := q₀) hi, hF0]
  have hco : coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2 = [] := by
    rw [← List.length_eq_zero_iff, length_coW, hF0]
  refine ⟨_, _, _, disp_dn1e G P Q s k₀ q₀ hAt hAV hk hd hi hF0, plan_fin G P Q s k₀ q₀ hd hi hm,
    fin_lib G P Q s k₀ q₀ hd hi hm (by rw [hco, tot_nil]; omega) (by rw [hco]; simp), ?_⟩
  have hFA := le_vU_pc G P Q s k₀ q₀ hAt hAV C A (c := cFA) (by unfold cPc; omega)
    (kFA_le G P Q s k₀ q₀ hK hk hd hi hA.b (E := aPc hAt hAV) (by unfold aPc; omega))
  obtain ⟨hF1, hF2⟩ := faW_le G P Q s k₀ q₀ hAt hAV hK hk hd hi
  have h0 := fin_atoms G P Q s k₀ q₀ hAt hAV hK hk hd hi hm hA
  have h1 := le_vU G P Q s k₀ q₀ hAt hAV C A hA.b
  have h2 := le_vU G P Q s k₀ q₀ hAt hAV C A hA.ws
  have h3 := total_le_tot (swAt G P Q s k₀ q₀ (.dn d i 1)).ws
  unfold kFt; rw [List.length_map]; omega

theorem ok_last {bR1 : Com} {d i m : ℕ} (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length) (hm2 : 2 ≤ m)
    (hm : m + 1 = nDn G P Q s k₀ q₀ d i)
    (hA : Atoms G P Q s k₀ q₀ (.dn d i m) (C * ((n + 1) * yQ G P Q s k₀ q₀ ^ A))) :
    DOk G P Q s k₀ q₀ atC bR1 (.dn d i m) (vU G P Q s k₀ q₀ hAt hAV C A) := by
  have hco := coW_last G P Q s k₀ q₀ hi hm2 hm
  have hC : tot (coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2) ≤
      tot (swAt G P Q s k₀ q₀ (.dn d i m)).ws + (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i m))).length + 1 := by
    rw [hco, tot_append, tot_cons, tot_nil]
    have := CO_tot G P Q s k₀ q₀ (.dn d i m)
    have := realY_len_le G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i m))
    omega
  have hCe : ∀ w ∈ coW G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2, ∀ e ∈ w,
      e ≤ maxEntry (toWord (swAt G P Q s k₀ q₀ (.dn d i m)).ws) +
        maxEntry (rY G k₀ q₀ (callOf G P Q s k₀ q₀ (.dn d i m))) := by
    intro w hw e he
    rw [hco, List.mem_append, List.mem_singleton] at hw
    rcases hw with hw | rfl
    · have : w ∈ (swAt G P Q s k₀ q₀ (.dn d i m)).ws := by rw [SW.ws_eq]; simp [hw]
      have := ent_toWord this he; omega
    · have := le_maxEntry (realY_sub G k₀ q₀ _ e he); omega
  refine ⟨_, _, _, disp_last G P Q s k₀ q₀ hAt hAV hk hd hi hm2 hm, plan_fin G P Q s k₀ q₀ hd hi hm,
    fin_lib G P Q s k₀ q₀ hd hi hm hC hCe, ?_⟩
  have h0 := fin_atoms G P Q s k₀ q₀ hAt hAV hK hk hd hi hm hA
  have h1 := le_vU G P Q s k₀ q₀ hAt hAV C A hA.b
  have h2 := le_vU G P Q s k₀ q₀ hAt hAV C A hA.ws
  have h3 := total_le_tot (swAt G P Q s k₀ q₀ (.dn d i m)).ws
  have h4 := length_le_tot (swAt G P Q s k₀ q₀ (.dn d i m)).ws
  unfold kLast; omega

theorem ok_upA {bR1 : Com} {d i : ℕ} (hd : d < q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hA : Atoms G P Q s k₀ q₀ (.up d i 0) (C * ((n + 1) * yQ G P Q s k₀ q₀ ^ A))) :
    DOk G P Q s k₀ q₀ atC bR1 (.up d i 0) (vU G P Q s k₀ q₀ hAt hAV C A) := by
  have hp := plan_upA G P Q s k₀ q₀ (i := i) hd
  have hp' := hp
  unfold DPlan at hp'
  have hn := next_up0 G P Q s k₀ q₀ (i := i) hd
  obtain ⟨hpl, -, -⟩ := hp'
  rw [hn] at hpl
  have hne : callOf G P Q s k₀ q₀ (.up d i 1) ≠ .stp :=
    callOf_ne_stp G P Q s k₀ q₀ (show Valid G P Q s k₀ q₀ (.up d i 1) from ⟨hd.le, hi, by simp [nUp, hd]⟩)
      (by simp)
  refine ⟨_, _, _, disp_upA G P Q s k₀ q₀ hk hd hi, hp, ?_, ?_⟩
  · rw [hn]; exact libSm_three G P Q s k₀ q₀ hpl (by simp [psRep2]) hne
  have hcw := plan_tot hpl (j := (swAt G P Q s k₀ q₀ (.up d i 0)).ws.length + 1) (by simp [psRep2]) (by simp)
  rw [List.getElem_append_right (by simp)] at hcw
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.add_sub_cancel_left,
    List.getElem_cons_succ, List.getElem_cons_zero] at hcw
  have hnws := hA.nws
  have hq := hA.q
  rw [hn] at hnws hq
  have hKd := le_vU_pc G P Q s k₀ q₀ hAt hAV C A (c := cKd) (by unfold cPc; omega)
    (kKid_le G P Q s k₀ q₀ hK (i := i) hd (E := aPc hAt hAV) (by unfold aPc; omega))
  have h1 := le_vU G P Q s k₀ q₀ hAt hAV C A hA.b
  have h2 := le_vU G P Q s k₀ q₀ hAt hAV C A hA.ws
  have h3 := le_vU G P Q s k₀ q₀ hAt hAV C A hnws
  have h4 := le_vU G P Q s k₀ q₀ hAt hAV C A hq
  have h5 := le_vU_cz G P Q s k₀ q₀ hAt hAV C A (x := d) (by unfold czOf; omega)
  have t1 := total_le_tot ((swAt G P Q s k₀ q₀ (.up d i 0)).ws ++
    [[], canonW (atomQ G P Q s k₀ q₀ (itm G P Q s k₀ q₀ d i).2)])
  simp only [tot_append, tot_cons, tot_nil, List.length_nil] at t1
  have h6 := one_le_vU G P Q s k₀ q₀ hAt hAV C A
  unfold kUpA kKdT; omega

theorem ok_upB {bR1 : Com} {d i m : ℕ} (hd : d ≤ q₀) (hi : i < (lvR G P Q s k₀ q₀ d).length)
    (hm : m + 1 = nUp q₀ d) (hnf : next G P Q s k₀ q₀ (.up d i m) ≠ .fin)
    (hA : Atoms G P Q s k₀ q₀ (.up d i m) (C * ((n + 1) * yQ G P Q s k₀ q₀ ^ A))) :
    DOk G P Q s k₀ q₀ atC bR1 (.up d i m) (vU G P Q s k₀ q₀ hAt hAV C A) := by
  have hp := plan_upB G P Q s k₀ q₀ hd hi hm hnf
  have hp' := hp
  unfold DPlan at hp'
  have hv : Valid G P Q s k₀ q₀ (.up d i m) := ⟨hd, hi, by omega⟩
  have hne := callOf_next_ne G P Q s k₀ q₀ hv hnf
  refine ⟨_, _, _, disp_upB G P Q s k₀ q₀ hAt hAV hk hd hi hm hnf, hp,
    libSm_three G P Q s k₀ q₀ hp'.1 (by simp [psUp]) hne, ?_⟩
  obtain ⟨hnd, hni⟩ := nx_valid G P Q s k₀ q₀ hd hi hm hnf
  have hAt' := le_vU_pc G P Q s k₀ q₀ hAt hAV C A (c := cAt hAt hAV) (by unfold cPc; omega)
    (kAtom_le G P Q s k₀ q₀ hK hk (d := nxD G P Q s k₀ q₀ d i) (i := nxI G P Q s k₀ q₀ d i)
      (cA := cAt hAt hAV) (aA := aAt hAt hAV) (E := aPc hAt hAV) hnd (by unfold aPc; omega))
  have hio : i < (outW G P Q s k₀ q₀ d).length := by rw [length_outW]; omega
  have ho := le_vU_nf G P Q s k₀ q₀ hAt hAV C A (hK.out d hd _ (List.getElem_mem hio))
  have h1 := le_vU G P Q s k₀ q₀ hAt hAV C A hA.b
  have h2 := le_vU G P Q s k₀ q₀ hAt hAV C A hA.ws
  have h4 := le_vU G P Q s k₀ q₀ hAt hAV C A hA.q
  have h5 := le_vU_cz G P Q s k₀ q₀ hAt hAV C A (x := d) (by unfold czOf; omega)
  have t1 := total_le_tot ((swAt G P Q s k₀ q₀ (.up d i m)).ws ++ [[], (outW G P Q s k₀ q₀ d)[i]'hio])
  simp only [tot_append, tot_cons, tot_nil, List.length_nil] at t1
  have t2 := total_le_tot (swAt G P Q s k₀ q₀ (.up d i m)).ws
  have h6 := one_le_vU G P Q s k₀ q₀ hAt hAV C A
  unfold kUpB kAtT; omega

/-- **The dispatcher at a position followed by a call.** -/
theorem disp_call {bR1 : Com} {c : Cur} (hv : Valid G P Q s k₀ q₀ c) (hc : c ≠ .stp)
    (hnf : next G P Q s k₀ q₀ c ≠ .fin)
    (hA : Atoms G P Q s k₀ q₀ c (C * ((n + 1) * yQ G P Q s k₀ q₀ ^ A))) :
    DOk G P Q s k₀ q₀ atC bR1 c (vU G P Q s k₀ q₀ hAt hAV C A) := by
  cases c with
  | stp => exact absurd rfl hc
  | fin => exact hv.elim
  | dn d i m =>
    obtain ⟨hd, hi, hm⟩ := hv
    have hnd := nDn_itm (G := G) (P := P) (Q := Q) (s := s) (k₀ := k₀) (q₀ := q₀) hi
    rcases (show m = 0 ∨ m = 1 ∨ 2 ≤ m by omega) with rfl | rfl | hm2
    · exact ok_shift G P Q s k₀ q₀ hAt hAV hK hk hd hi hA
    · by_cases hF : 0 < (faP G (dataOf G P Q s k₀ q₀) (itm G P Q s k₀ q₀ d i).2).length
      · exact ok_ft G P Q s k₀ q₀ hAt hAV hK hk hd hi hF hA
      · exact ok_fin1 G P Q s k₀ q₀ hAt hAV hK hk hd hi (by omega) hA
    · by_cases hml : m + 1 = nDn G P Q s k₀ q₀ d i
      · exact ok_last G P Q s k₀ q₀ hAt hAV hK hk hd hi hm2 hml hA
      · exact ok_comp G P Q s k₀ q₀ hAt hAV hK hk hi hm2 (by omega) hA
  | up d i m =>
    obtain ⟨hd, hi, hm⟩ := hv
    by_cases h0 : m = 0 ∧ d < q₀
    · obtain ⟨rfl, hdq⟩ := h0
      exact ok_upA G P Q s k₀ q₀ hAt hAV hK hk hdq hi hA
    · have hm' : m + 1 = nUp q₀ d := by
        unfold nUp at hm ⊢; split_ifs at hm ⊢ with h <;> omega
      exact ok_upB G P Q s k₀ q₀ hAt hAV hK hk hd hi hm' hnf hA

end Cases2

end Lax185574Proofs.ResolveRam.Glue
