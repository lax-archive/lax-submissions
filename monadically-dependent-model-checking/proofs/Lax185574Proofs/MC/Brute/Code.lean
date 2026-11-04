import Lax185574Proofs.MC.Brute.Step

/-!
Reading the code of the sentence, for the brute-force thread.

The code is a prefix code, so `rdFml` reads it without knowing its
length: it keeps the number `bfr` of subformulas still to be read, and
copies the code into `bfc`, with its length in `bfl`. Before every
opcode it checks that three more entries fit below `W - 3`, and
otherwise sets `ovf` and stops. `rdFml_run` gives the run.
-/

namespace Lax185574Proofs.MC.Brute

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax3.FirstOrder Lax185574.InstanceEncoding

/-- The codes of a list of formulas of any arities, one after the other. -/
def codesL : List (Σ k, FO k) → List ℕ
  | [] => []
  | ψ :: Ψ => code ψ.2 ++ codesL Ψ

/-- Read one opcode and its arguments. -/
def rdOp : Com :=
  .seq (.read "bfo") (.seq (.store "bfc" (.var "bfl") (.var "bfo")) (.seq (.assign "bfl" (.add (.var "bfl") (.lit 1)))
    (.ite (.lt (.var "bfo") (.lit 2))
      (.seq (.read "bfy") (.seq (.store "bfc" (.var "bfl") (.var "bfy")) (.seq (.assign "bfl" (.add (.var "bfl") (.lit 1)))
        (.seq (.read "bfy") (.seq (.store "bfc" (.var "bfl") (.var "bfy")) (.seq (.assign "bfl" (.add (.var "bfl") (.lit 1)))
          (.assign "bfr" (.sub (.var "bfr") (.lit 1)))))))))
      (.ite (.eq (.var "bfo") (.lit 3)) (.assign "bfr" (.add (.var "bfr") (.lit 1))) .skip))))

/-- One round: check the room, then read an opcode. -/
def rdBody : Com :=
  .ite (.lt (.sub (.var "W") (.var "bfl")) (.lit 6))
    (.seq (.assign "ovf" (.lit 1)) (.assign "bfr" (.lit 0))) rdOp

/-- Read the code of a formula into `bfc`. -/
def rdFml : Com :=
  .seq (.assign "bfl" (.lit 0)) (.seq (.assign "bfr" (.lit 1)) (.while (.lt (.lit 0) (.var "bfr")) rdBody))

theorem fill_step {arr cw : List ℕ} {p v : ℕ}
    (h : ∀ i, arr.getD i 0 = if i < p then cw.getD i 0 else 0) (hp : p < arr.length)
    (hv : cw.getD p 0 = v) : ∀ i, (arr.set p v).getD i 0 = if i < p + 1 then cw.getD i 0 else 0 := by
  intro i
  rw [List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases he : p = i
  · subst he; rw [if_pos rfl, if_pos hp, if_pos (by omega), ← hv]; rfl
  · rw [if_neg he, ← List.getD_eq_getElem?_getD, h i]
    by_cases hi : i < p
    · rw [if_pos hi, if_pos (by omega)]
    · rw [if_neg hi, if_neg (by omega)]

theorem getD_of_drop {cw d : List ℕ} {p v : ℕ} (h : cw.drop p = v :: d) :
    cw.getD p 0 = v ∧ cw.drop (p + 1) = d := by
  have h1 : cw[p]? = some v := by
    rw [← List.head?_drop, h]; rfl
  refine ⟨by rw [List.getD_eq_getElem?_getD, h1]; rfl, ?_⟩
  rw [← List.drop_drop, h]; rfl

/-- Collapse environment chains with reads. -/
macro "csimp" : tactic => `(tactic| simp only [vars_setVar, arrs_setVar, arrs_setArr, vars_setArr,
  inp_setVar, inp_setArr, out_setVar, out_setArr, length_arrs_setArr, List.length_set, ↓reduceIte,
  String.reduceEq] at *)

/-- The state of the reading loop. -/
def RdOK (B W : ℕ) (cw rest : List ℕ) (τ : Env) : Prop :=
  τ.vars "W" = W ∧ (τ.arrs "bfc").length = B ∧ τ.vars "bfl" ≤ cw.length ∧
  τ.vars "bfl" + 3 ≤ W ∧ τ.vars "bfr" ≤ τ.vars "bfl" + 1 ∧
  (∀ i, (τ.arrs "bfc").getD i 0 = if i < τ.vars "bfl" then cw.getD i 0 else 0) ∧
  ((τ.vars "ovf" = 0 ∧ ∃ Ψ : List (Σ k, FO k), τ.inp = codesL Ψ ++ rest ∧
      cw.drop (τ.vars "bfl") = codesL Ψ ∧ τ.vars "bfr" = Ψ.length) ∨
    (τ.vars "ovf" = 1 ∧ τ.vars "bfr" = 0 ∧ W < cw.length + 6))

theorem rd_atom {B W op a b : ℕ} (h6 : 6 < B) {t : List ℕ} {τ : Env} (hB : B = W + 1) (hW : τ.vars "W" = W)
    (hl : τ.vars "bfl" + 6 ≤ W) (hr : 1 ≤ τ.vars "bfr") (hrB : τ.vars "bfr" < B)
    (hinp : τ.inp = op :: a :: b :: t) (hop : op < 2) (haB : a < B) (hbB : b < B)
    (hlen : (τ.arrs "bfc").length = B) :
    ∃ τ', Run B rdBody τ τ' 60 ∧ τ'.inp = t ∧ τ'.vars "bfl" = τ.vars "bfl" + 3 ∧
      τ'.vars "bfr" = τ.vars "bfr" - 1 ∧ τ'.vars "ovf" = τ.vars "ovf" ∧ τ'.vars "W" = W ∧
      τ'.arrs "bfc" = (((τ.arrs "bfc").set (τ.vars "bfl") op).set (τ.vars "bfl" + 1) a).set
        (τ.vars "bfl" + 2) b := by
  unfold rdBody rdOp
  run_vcg
  all_goals first | bdead | (csimp; simp only [hinp, List.headD_cons, List.tail_cons] at *; omega) | skip
  all_goals (try csimp)
  all_goals simp only [hinp, List.headD_cons, List.tail_cons] at *
  all_goals first | bdead | skip
  all_goals (try simp only [true_and, and_true, and_self])
  all_goals first | exact hW | trivial | omega

theorem rd_un {B W op : ℕ} (h6 : 6 < B) {t : List ℕ} {τ : Env} (hB : B = W + 1) (hW : τ.vars "W" = W)
    (hl : τ.vars "bfl" + 6 ≤ W) (hrB : τ.vars "bfr" < B)
    (hinp : τ.inp = op :: t) (hop : op = 2 ∨ op = 4) (hlen : (τ.arrs "bfc").length = B) :
    ∃ τ', Run B rdBody τ τ' 60 ∧ τ'.inp = t ∧ τ'.vars "bfl" = τ.vars "bfl" + 1 ∧
      τ'.vars "bfr" = τ.vars "bfr" ∧ τ'.vars "ovf" = τ.vars "ovf" ∧ τ'.vars "W" = W ∧
      τ'.arrs "bfc" = (τ.arrs "bfc").set (τ.vars "bfl") op := by
  unfold rdBody rdOp
  run_vcg
  all_goals first | bdead | (csimp; simp only [hinp, List.headD_cons, List.tail_cons] at *; omega) | skip
  all_goals (try csimp)
  all_goals simp only [hinp, List.headD_cons, List.tail_cons] at *
  all_goals first | bdead | skip
  all_goals (try simp only [true_and, and_true, and_self])
  all_goals first | exact hW | trivial | omega

theorem rd_and {B W : ℕ} (h6 : 6 < B) {t : List ℕ} {τ : Env} (hB : B = W + 1) (hW : τ.vars "W" = W)
    (hl : τ.vars "bfl" + 6 ≤ W) (hrB : τ.vars "bfr" + 1 < B)
    (hinp : τ.inp = 3 :: t) (hlen : (τ.arrs "bfc").length = B) :
    ∃ τ', Run B rdBody τ τ' 60 ∧ τ'.inp = t ∧ τ'.vars "bfl" = τ.vars "bfl" + 1 ∧
      τ'.vars "bfr" = τ.vars "bfr" + 1 ∧ τ'.vars "ovf" = τ.vars "ovf" ∧ τ'.vars "W" = W ∧
      τ'.arrs "bfc" = (τ.arrs "bfc").set (τ.vars "bfl") 3 := by
  unfold rdBody rdOp
  run_vcg
  all_goals first | bdead | (csimp; simp only [hinp, List.headD_cons, List.tail_cons] at *; omega) | skip
  all_goals (try csimp)
  all_goals simp only [hinp, List.headD_cons, List.tail_cons] at *
  all_goals first | bdead | skip
  all_goals (try simp only [true_and, and_true, and_self])
  all_goals first | exact hW | trivial | omega

theorem rd_full {B W : ℕ} (h6 : 6 < B) {τ : Env} (hB : B = W + 1) (hW : τ.vars "W" = W)
    (hl : W < τ.vars "bfl" + 6) (hlB : τ.vars "bfl" < B) :
    ∃ τ', Run B rdBody τ τ' 20 ∧ τ'.inp = τ.inp ∧ τ'.vars "bfl" = τ.vars "bfl" ∧
      τ'.vars "bfr" = 0 ∧ τ'.vars "ovf" = 1 ∧ τ'.vars "W" = W ∧ τ'.arrs "bfc" = τ.arrs "bfc" := by
  unfold rdBody rdOp
  run_vcg
  all_goals first | bdead | (csimp; omega) | skip
  all_goals (try csimp)
  all_goals first | bdead | skip
  all_goals (try simp only [true_and, and_true, and_self])
  all_goals first | exact hW | trivial | omega

theorem codesL_cons_ne {Ψ : List (Σ k, FO k)} (h : Ψ ≠ []) : codesL Ψ ≠ [] := by
  obtain ⟨⟨k, ψ⟩, Ψ', rfl⟩ := List.exists_cons_of_ne_nil h
  cases ψ <;> simp [codesL, code]

/-- One round of the reading loop. -/
theorem rdBody_step {B W : ℕ} {cw rest : List ℕ} (h6 : 6 < B) (hB : B = W + 1) (hcw : ∀ v ∈ cw, v < B)
    {τ : Env} (hI : RdOK B W cw rest τ) (hr : 0 < τ.vars "bfr") :
    ∃ τ' K, Run B rdBody τ τ' K ∧ RdOK B W cw rest τ' ∧
      1 + 3 + K + (300 * (cw.length - τ'.vars "bfl") + 100 * τ'.vars "bfr") ≤
        300 * (cw.length - τ.vars "bfl") + 100 * τ.vars "bfr" := by
  obtain ⟨hW, hlen, hle, hlW, hrl1, hfill, hcase⟩ := hI
  rcases hcase with ⟨hov, Ψ, hinp, hdrop, hrl⟩ | ⟨-, hr0, -⟩
  swap
  · omega
  have hΨ : Ψ ≠ [] := by rintro rfl; simp at hrl; omega
  have hlt : τ.vars "bfl" < cw.length := by
    by_contra hc
    rw [List.drop_eq_nil_of_le (by omega)] at hdrop
    exact codesL_cons_ne hΨ hdrop.symm
  by_cases hroom : W < τ.vars "bfl" + 6
  · obtain ⟨τ', r, e1, e2, e3, e4, e5, e6⟩ := rd_full h6 hB hW hroom (by omega)
    refine ⟨τ', 20, r, ⟨e5, by rw [e6]; exact hlen, by omega, by omega, by omega,
      by rw [e6, e2]; exact hfill,
      Or.inr ⟨e4, e3, by omega⟩⟩, by rw [e2, e3]; omega⟩
  · simp only [not_lt] at hroom
    obtain ⟨⟨k, ψ⟩, Ψ', rfl⟩ := List.exists_cons_of_ne_nil hΨ
    simp only [codesL] at hinp hdrop
    simp only [List.length_cons] at hrl
    have hmem : ∀ v ∈ cw.drop (τ.vars "bfl"), v < B := fun v hv => hcw v (List.mem_of_mem_drop hv)
    cases ψ with
    | adj i j =>
      simp only [code, List.cons_append, List.nil_append] at hinp hdrop
      obtain ⟨g0, d0⟩ := getD_of_drop hdrop
      obtain ⟨g1, d1⟩ := getD_of_drop d0
      obtain ⟨g2, d2⟩ := getD_of_drop d1
      have hl3 := congrArg List.length hdrop
      simp only [List.length_drop, List.length_cons] at hl3
      rw [hdrop] at hmem
      obtain ⟨τ', r, e1, e2, e3, e4, e5, e6⟩ := rd_atom h6 (op := 0) (a := i) (b := j) hB hW hroom
        (by omega) (by omega) hinp (by omega) (hmem _ (by simp)) (hmem _ (by simp)) hlen
      refine ⟨τ', 60, r, ⟨e5, by rw [e6]; simp [hlen], by omega, by omega, by omega, ?_, Or.inl ⟨by rw [e4, hov],
        Ψ', by rw [e1], by rw [e2, show τ.vars "bfl" + 3 = τ.vars "bfl" + 1 + 1 + 1 by omega, d2],
        by rw [e3, hrl]; rfl⟩⟩, by rw [e2, e3]; omega⟩
      rw [e6, e2]
      have f1 := fill_step hfill (by omega) g0
      have f2 := fill_step f1 (by simp; omega) g1
      have f3 := fill_step f2 (by simp; omega) g2
      intro x; rw [f3 x]
    | eq i j =>
      simp only [code, List.cons_append, List.nil_append] at hinp hdrop
      obtain ⟨g0, d0⟩ := getD_of_drop hdrop
      obtain ⟨g1, d1⟩ := getD_of_drop d0
      obtain ⟨g2, d2⟩ := getD_of_drop d1
      have hl3 := congrArg List.length hdrop
      simp only [List.length_drop, List.length_cons] at hl3
      rw [hdrop] at hmem
      obtain ⟨τ', r, e1, e2, e3, e4, e5, e6⟩ := rd_atom h6 (op := 1) (a := i) (b := j) hB hW hroom
        (by omega) (by omega) hinp (by omega) (hmem _ (by simp)) (hmem _ (by simp)) hlen
      refine ⟨τ', 60, r, ⟨e5, by rw [e6]; simp [hlen], by omega, by omega, by omega, ?_, Or.inl ⟨by rw [e4, hov],
        Ψ', by rw [e1], by rw [e2, show τ.vars "bfl" + 3 = τ.vars "bfl" + 1 + 1 + 1 by omega, d2],
        by rw [e3, hrl]; rfl⟩⟩, by rw [e2, e3]; omega⟩
      rw [e6, e2]
      have f1 := fill_step hfill (by omega) g0
      have f2 := fill_step f1 (by simp; omega) g1
      have f3 := fill_step f2 (by simp; omega) g2
      intro x; rw [f3 x]
    | not ψ =>
      simp only [code, List.cons_append] at hinp hdrop
      obtain ⟨g0, d0⟩ := getD_of_drop hdrop
      obtain ⟨τ', r, e1, e2, e3, e4, e5, e6⟩ := rd_un h6 (op := 2) hB hW hroom (by omega) hinp
        (Or.inl rfl) hlen
      refine ⟨τ', 60, r, ⟨e5, by rw [e6]; simp [hlen], by omega, by omega, by omega, ?_, Or.inl ⟨by rw [e4, hov],
        ⟨k, ψ⟩ :: Ψ', by rw [e1]; simp [codesL], by rw [e2, d0]; simp [codesL],
        by rw [e3, hrl]; simp⟩⟩, by rw [e2, e3]; omega⟩
      rw [e6, e2]; exact fill_step hfill (by omega) g0
    | and ψ₁ ψ₂ =>
      simp only [code, List.cons_append, List.append_assoc] at hinp hdrop
      obtain ⟨g0, d0⟩ := getD_of_drop hdrop
      obtain ⟨τ', r, e1, e2, e3, e4, e5, e6⟩ := rd_and h6 hB hW hroom (by omega) hinp hlen
      refine ⟨τ', 60, r, ⟨e5, by rw [e6]; simp [hlen], by omega, by omega, by omega, ?_, Or.inl ⟨by rw [e4, hov],
        ⟨k, ψ₁⟩ :: ⟨k, ψ₂⟩ :: Ψ', by rw [e1]; simp [codesL], by rw [e2, d0]; simp [codesL],
        by rw [e3, hrl]; simp⟩⟩, by rw [e2, e3]; omega⟩
      rw [e6, e2]; exact fill_step hfill (by omega) g0
    | ex ψ =>
      simp only [code, List.cons_append] at hinp hdrop
      obtain ⟨g0, d0⟩ := getD_of_drop hdrop
      obtain ⟨τ', r, e1, e2, e3, e4, e5, e6⟩ := rd_un h6 (op := 4) hB hW hroom (by omega) hinp
        (Or.inr rfl) hlen
      refine ⟨τ', 60, r, ⟨e5, by rw [e6]; simp [hlen], by omega, by omega, by omega, ?_, Or.inl ⟨by rw [e4, hov],
        ⟨k + 1, ψ⟩ :: Ψ', by rw [e1]; simp [codesL], by rw [e2, d0]; simp [codesL],
        by rw [e3, hrl]; simp⟩⟩, by rw [e2, e3]; omega⟩
      rw [e6, e2]; exact fill_step hfill (by omega) g0

theorem condPos_eval {B : ℕ} {y : String} {ρ : Env} {b : Bool}
    (h : (Cond.lt (.lit 0) (.var y)).evalB B ρ = some b) : b = decide (0 < ρ.vars y) := by
  simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff] at h
  obtain ⟨_, _, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := h
  exact hr

/-- **Reading the code.** On input `code φ ++ rest`, `rdFml` either
copies the code into `bfc` and leaves its length in `bfl`, or sets
`ovf`, which happens only if `W < |code φ| + 6`. -/
theorem rdFml_run {B W : ℕ} (φ : FO 0) {rest : List ℕ} (hB : B = W + 1)
    (hcw : ∀ v ∈ code φ, v < B) {σ : Env} (hW : σ.vars "W" = W) (hov : σ.vars "ovf" = 0)
    (hinp : σ.inp = code φ ++ rest) (hlen : (σ.arrs "bfc").length = B)
    (hz : ∀ i, (σ.arrs "bfc").getD i 0 = 0) (h6 : 6 < B) :
    ∃ σ', Run B rdFml σ σ' (300 * (code φ).length + 120) ∧ σ'.vars "W" = W ∧
      (σ'.arrs "bfc").length = B ∧
      ((σ'.vars "ovf" = 0 ∧ σ'.inp = rest ∧ σ'.vars "bfl" = (code φ).length ∧
          ∀ i, (σ'.arrs "bfc").getD i 0 = (code φ).getD i 0) ∨
        (σ'.vars "ovf" = 1 ∧ W < (code φ).length + 6)) := by
  set cw := code φ with hcwd
  set σ0 := (σ.setVar "bfl" 0).setVar "bfr" 1
  have hI0 : RdOK B W cw rest σ0 := ⟨by simp [σ0, hW], by simp [σ0, hlen], by simp [σ0], by simp [σ0]; omega,
    by simp [σ0],
    fun i => by simp only [σ0, arrs_setVar, vars_setVar]; rw [hz i]; simp, Or.inl ⟨by simp [σ0, hov],
      [⟨0, φ⟩], by simp [σ0, hinp, codesL, hcwd], by simp [σ0, codesL, hcwd], by simp [σ0]⟩⟩
  have hdef : ∀ τ, RdOK B W cw rest τ → ∃ v, (Cond.lt (.lit 0) (.var "bfr")).evalB B τ = some v := by
    intro τ hI
    obtain ⟨-, -, -, hlW, hrl, -⟩ := hI
    have : τ.vars "bfr" < B := by omega
    exact ⟨_, evalB_condLt (evalB_lit (by omega)) (evalB_var this)⟩
  obtain ⟨σ', K, hrun, hI', hfalse, hK⟩ := Run.while_potential (B := B)
    (b := .lt (.lit 0) (.var "bfr")) (c := rdBody) (RdOK B W cw rest)
    (fun τ => 300 * (cw.length - τ.vars "bfl") + 100 * τ.vars "bfr") hdef
    (fun τ hI hb => rdBody_step h6 hB hcw hI (by have := condPos_eval hb; simpa using this.symm)) hI0
  have hr0 : σ'.vars "bfr" = 0 := by
    have := condPos_eval hfalse; simp at this; omega
  have hΦ0 : 300 * (cw.length - σ0.vars "bfl") + 100 * σ0.vars "bfr" = 300 * cw.length + 100 := by
    simp [σ0]
  obtain ⟨hW', hlen', hle', -, -, hfill', hcase'⟩ := hI'
  refine ⟨σ', ?_, hW', hlen', ?_⟩
  · unfold rdFml
    refine (Run.seq (Run.assign (v := 0) (by simp; omega)) (Run.seq (Run.assign (v := 1)
      (by simp; omega)) hrun)).mono ?_
    simp only [Expr.size, Cond.size] at hK ⊢
    rw [hΦ0] at hK
    omega
  · rcases hcase' with ⟨hov', Ψ, hinp', hdrop', hrl'⟩ | ⟨hov', -, hlt'⟩
    · left
      have hΨ : Ψ = [] := by rw [hr0] at hrl'; exact List.length_eq_zero_iff.mp hrl'.symm
      subst hΨ
      simp only [codesL, List.nil_append, List.drop_eq_nil_iff] at hinp' hdrop'
      refine ⟨hov', hinp', by omega, fun i => ?_⟩
      rw [hfill' i]
      split_ifs with h
      · rfl
      · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    · exact Or.inr ⟨hov', hlt'⟩

end Lax185574Proofs.MC.Brute
