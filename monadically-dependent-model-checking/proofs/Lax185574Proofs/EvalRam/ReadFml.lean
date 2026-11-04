import Lax185574Proofs.Words.TreeCopy
import Lax185574Proofs.Words.ForLoop
import Lax185574Proofs.EvalRam.Word

/-!
Reading the code of a formula off the input tape.

The code of a formula is a prefix code, so a program can read it without
knowing its length: it keeps the number `pd` of subformulas still to be
read. An opcode is followed by `nargs` arguments and starts `arity`
subformulas, so reading it changes `pd` by `arity − 1`. The command
`readFml` copies the code into the array `f` and leaves its length in
`fl`.
-/

namespace Lax185574Proofs.EvalRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574.WordEncoding Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO

/-- The codes of a list of formulas of any arities, one after the
other. -/
def codes : List (Σ ℓ, DistFO ℓ) → List ℕ
  | [] => []
  | φ :: Ψ => code φ.2 ++ codes Ψ

theorem codes_append (Φ Ψ : List (Σ ℓ, DistFO ℓ)) : codes (Φ ++ Ψ) = codes Φ ++ codes Ψ := by
  induction Φ with
  | nil => rfl
  | cons φ Φ ih => simp [codes, ih]

theorem length_le_codes : ∀ Ψ : List (Σ ℓ, DistFO ℓ), Ψ.length ≤ (codes Ψ).length
  | [] => le_rfl
  | φ :: Ψ => by
    have := length_le_codes Ψ
    have := Lax185574Proofs.TreeAlgo.one_le_code_length φ.2
    simp [codes]; omega

/-- The number of arguments after an opcode. -/
def nargs (op : ℕ) : ℕ := if op < 4 then 2 else if op < 6 then 3 else if op = 8 then 2 else 0

/-- The number of subformulas after an opcode. -/
def arity (op : ℕ) : ℕ := if op < 6 then 0 else if op = 7 then 2 else 1

/-- The code of a formula: the opcode, its arguments, and the codes of
its subformulas. -/
theorem code_split {ℓ : ℕ} (φ : DistFO ℓ) :
    ∃ (op : ℕ) (args : List ℕ) (ch : List (Σ ℓ, DistFO ℓ)),
      code φ = op :: (args ++ codes ch) ∧ args.length = nargs op ∧ ch.length = arity op ∧ op ≤ 8 := by
  cases φ with
  | eq i j => exact ⟨0, [i.val, j.val], [], by simp [code, codes], by simp [nargs], by simp [arity], by omega⟩
  | edge i j => exact ⟨1, [i.val, j.val], [], by simp [code, codes], by simp [nargs], by simp [arity], by omega⟩
  | nonEdge i j => exact ⟨2, [i.val, j.val], [], by simp [code, codes], by simp [nargs], by simp [arity], by omega⟩
  | color Y i => exact ⟨3, [Y, i.val], [], by simp [code, codes], by simp [nargs], by simp [arity], by omega⟩
  | distLe r i j => exact ⟨4, [r, i.val, j.val], [], by simp [code, codes], by simp [nargs], by simp [arity], by omega⟩
  | distColorLt r Y i => exact ⟨5, [r, Y, i.val], [], by simp [code, codes], by simp [nargs], by simp [arity], by omega⟩
  | not φ => exact ⟨6, [], [⟨_, φ⟩], by simp [code, codes], by simp [nargs], by simp [arity], by omega⟩
  | and φ ψ => exact ⟨7, [], [⟨_, φ⟩, ⟨_, ψ⟩], by simp [code, codes], by simp [nargs], by simp [arity], by omega⟩
  | exLocal i s φ =>
    exact ⟨8, [i.val, s], [⟨_, φ⟩], by simp [code, codes], by simp [nargs], by simp [arity], by omega⟩

/-! ### The commands -/

/-- Read one number and append it to `f`. -/
def rdOne : Com :=
  .seq (.read "w") (.seq (.store "f" (.var "fl") (.var "w")) (.assign "fl" (.add (.var "fl") (.lit 1))))

/-- The number of arguments of the opcode `op`. -/
def setNa : Com :=
  .ite (.lt (.var "op") (.lit 4)) (.assign "na" (.lit 2))
    (.ite (.lt (.var "op") (.lit 6)) (.assign "na" (.lit 3))
      (.ite (.eq (.var "op") (.lit 8)) (.assign "na" (.lit 2)) (.assign "na" (.lit 0))))

/-- Account for the subformulas of the opcode `op`. -/
def setPd : Com :=
  .ite (.lt (.var "op") (.lit 6)) (.assign "pd" (.sub (.var "pd") (.lit 1)))
    (.ite (.eq (.var "op") (.lit 7)) (.assign "pd" (.add (.var "pd") (.lit 1))) .skip)

/-- Read one opcode and its arguments. -/
def fmlBody : Com :=
  .seq rdOne (.seq (.assign "op" (.var "w")) (.seq setNa (.seq (forUp "rj" (.var "na") rdOne) setPd)))

/-- Read the code of a formula into `f`. -/
def readFml : Com :=
  .seq (.assign "fl" (.lit 0)) (.seq (.assign "pd" (.lit 1)) (.while (.lt (.lit 0) (.var "pd")) fmlBody))

/-! ### Specifications -/

/-- The first `m` numbers of `W` are in `f`, the rest of `W` is on the
tape. -/
def FAt (W O rest : List ℕ) (m : ℕ) (ρ : Env) : Prop :=
  ρ.vars "fl" = m ∧ ρ.arrs "f" = W.take m ++ O.drop m ∧ ρ.inp = W.drop m ++ rest

theorem FAt.setVar {W O rest : List ℕ} {m : ℕ} {ρ : Env} (h : FAt W O rest m ρ) {x : String}
    (hx : x ≠ "fl") (v : ℕ) : FAt W O rest m (ρ.setVar x v) := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨by simp [hx.symm, h1], by simp [h2], by simp [h3]⟩

theorem rdOne_spec (B : ℕ) (W O rest : List ℕ) (m : ℕ) (hm : m < W.length)
    (hO : W.length ≤ O.length) (hW : ∀ v ∈ W, v < B) (hB : W.length < B) :
    Spec B (FAt W O rest m) rdOne (fun _ ρ' => FAt W O rest (m + 1) ρ' ∧ ρ'.vars "w" = W[m]) 10 := by
  rintro ρ ⟨hfl, hf, hinp⟩
  have hinp' : ρ.inp = W[m] :: (W.drop (m + 1) ++ rest) := by
    rw [hinp, List.drop_eq_getElem_cons hm]; rfl
  have hlen : (W.take m).length = m := by simp; omega
  have hst : (ρ.arrs "f").set m W[m] = W.take (m + 1) ++ O.drop (m + 1) := by
    rw [hf, set_prefix' hlen (by omega), List.take_add_one, List.getElem?_eq_getElem hm]; rfl
  have hwB : W[m] < B := hW _ (List.getElem_mem hm)
  have hfl' : (ρ.arrs "f").length = O.length := by rw [hf]; simp; omega
  set ρ1 : Env := { ρ.setVar "w" W[m] with inp := W.drop (m + 1) ++ rest } with hρ1
  refine ⟨(ρ1.setArr "f" m W[m]).setVar "fl" (m + 1), ?_, ⟨by simp, ?_, by simp [hρ1]⟩, by simp [hρ1]⟩
  · unfold rdOne
    refine (Run.seq (Run.read hinp') (Run.seq (Run.store (idx := m) (v := W[m]) ?_ ?_ ?_)
      (Run.assign ?_))).mono (by simp)
    · simp [hρ1, hfl]; omega
    · simp [hρ1]; exact hwB
    · simp [hρ1, hfl']; omega
    · simp [hρ1, hfl]; omega
  · simp [hρ1, hst]

theorem setNa_spec (B : ℕ) (o : ℕ) (hB : 8 < B) (ho : o < B) :
    Spec B (fun ρ => ρ.vars "op" = o) setNa (fun _ ρ' => ρ'.vars "na" = nargs o) 20 := by
  rintro ρ hop
  subst hop
  unfold setNa
  run_vcg
  all_goals (simp only [nargs]; split_ifs <;> simp_all <;> omega)

theorem setPd_spec (B : ℕ) (o d : ℕ) (hB : 8 < B) (ho : o < B) (hd : d + 1 < B) :
    Spec B (fun ρ => ρ.vars "op" = o ∧ ρ.vars "pd" = d) setPd
      (fun _ ρ' => ρ'.vars "pd" = d + arity o - 1) 20 := by
  rintro ρ ⟨hop, hpd⟩
  subst hop hpd
  unfold setPd
  run_vcg
  all_goals (simp only [arity]; split_ifs <;> simp_all <;> omega)

theorem rdArgs_spec (B : ℕ) (W O rest : List ℕ) (m N : ℕ) (hm : m + N ≤ W.length)
    (hO : W.length ≤ O.length) (hW : ∀ v ∈ W, v < B) (hB : W.length + 4 < B) :
    Spec B (fun ρ => FAt W O rest m ρ ∧ ρ.vars "na" = N) (forUp "rj" (.var "na") rdOne)
      (fun _ ρ' => FAt W O rest (m + N) ρ') (N * 20 + 7) := by
  rintro ρ ⟨hF, hna⟩
  obtain ⟨ρ', hr, hI, -⟩ := forUp_run (B := B) (i := "rj") (e := .var "na") (body := rdOne) (N := N)
    (K := 10) (fun j τ => FAt W O rest (m + j) τ ∧ τ.vars "na" = N) (σ := ρ) (by omega)
    (fun j _ τ hI _ => by simp [hI.2]; omega) ⟨hF.setVar (by decide) 0, by simp [hna]⟩
    (fun j hj τ hI hrj => by
      obtain ⟨τ', hr', hF', -⟩ := rdOne_spec B W O rest (m + j) (by omega) hO hW (by omega) τ hI.1
      refine ⟨τ', hr', by rw [hr'.frame_var "rj" (by decide), hrj], ?_, ?_⟩
      · exact (show m + (j + 1) = m + j + 1 by omega) ▸ hF'.setVar (by decide) (j + 1)
      · simp [hr'.frame_var "na" (by decide), hI.2])
  exact ⟨ρ', hr.mono (by simp; omega), hI.1⟩

theorem pos_of_condLt_true {B : ℕ} {x : String} {ρ : Env}
    (h : (Cond.lt (.lit 0) (.var x)).evalB B ρ = some true) : 0 < ρ.vars x := by
  simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff] at h
  obtain ⟨a, b, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := h
  simpa using hr.symm

theorem zero_of_condLt_false {B : ℕ} {x : String} {ρ : Env}
    (h : (Cond.lt (.lit 0) (.var x)).evalB B ρ = some false) : ρ.vars x = 0 := by
  simp only [evalB_condLt_iff, evalB_lit_iff, evalB_var_iff] at h
  obtain ⟨a, b, ⟨rfl, -⟩, ⟨rfl, -⟩, hr⟩ := h
  have := hr.symm
  simp only [decide_eq_false_iff_not, not_lt] at this
  omega

/-- The invariant of the reading loop. -/
def RdInv (W O rest : List ℕ) (ρ : Env) : Prop :=
  ∃ (m : ℕ) (Ψ : List (Σ ℓ, DistFO ℓ)), FAt W O rest m ρ ∧ m ≤ W.length ∧
    W.drop m = codes Ψ ∧ ρ.vars "pd" = Ψ.length

theorem fmlBody_spec (B : ℕ) (W O rest : List ℕ) (hO : W.length ≤ O.length)
    (hW : ∀ v ∈ W, v < B) (hB : W.length + 10 < B) :
    Spec B (fun ρ => RdInv W O rest ρ ∧ 0 < ρ.vars "pd") fmlBody
      (fun ρ ρ' => RdInv W O rest ρ' ∧ ρ.vars "fl" < ρ'.vars "fl") 120 := by
  rintro ρ ⟨⟨m, Ψ, hF, hmW, hdrop, hpd⟩, hpos⟩
  obtain ⟨φ, Ψt, rfl⟩ : ∃ φ Ψt, Ψ = φ :: Ψt := by
    cases Ψ with
    | nil => simp at hpd; omega
    | cons φ Ψt => exact ⟨φ, Ψt, rfl⟩
  obtain ⟨op, args, ch, hc, hna, hch, hop8⟩ := code_split φ.2
  have hdrop' : W.drop m = op :: (args ++ codes (ch ++ Ψt)) := by
    rw [hdrop, codes, hc, codes_append]; simp
  have hm : m < W.length := by
    have := congrArg List.length hdrop'; simp at this; omega
  have hWm : W[m] = op := by
    have := congrArg (·[0]?) hdrop'
    simp [List.getElem?_drop, List.getElem?_eq_getElem hm] at this; exact this
  have hlenrest : m + 1 + args.length + (codes (ch ++ Ψt)).length = W.length := by
    have := congrArg List.length hdrop'; simp at this; omega
  have hdrop2 : W.drop (m + 1 + nargs op) = codes (ch ++ Ψt) := by
    rw [show m + 1 + nargs op = m + (op :: args).length by simp [hna]; omega]
    exact drop_add_of_drop (by rw [hdrop']; simp)
  have hpdB : Ψt.length + 1 + 1 < B := by
    have := length_le_codes Ψt
    have : (codes Ψt).length ≤ (codes (ch ++ Ψt)).length := by rw [codes_append]; simp
    omega
  -- the run
  obtain ⟨ρ1, hr1, hF1, hw1⟩ := rdOne_spec B W O rest m hm hO hW (by omega) ρ hF
  rw [hWm] at hw1
  have hpd1 : ρ1.vars "pd" = Ψt.length + 1 := by rw [hr1.frame_var "pd" (by decide), hpd]; simp
  set ρ2 := ρ1.setVar "op" op with hρ2
  have hr2 : Run B (.assign "op" (.var "w")) ρ1 ρ2 2 :=
    (Run.assign (v := op) (by simp [hw1]; omega)).mono (by simp)
  obtain ⟨ρ3, hr3, hna3⟩ := setNa_spec B op (by omega) (by omega) ρ2 (by simp [hρ2])
  have hF3 : FAt W O rest (m + 1) ρ3 := by
    obtain ⟨h1, h2, h3⟩ := hF1.setVar (x := "op") (by decide) op
    exact ⟨by rw [hr3.frame_var "fl" (by decide)]; exact h1,
      by rw [hr3.frame_arr "f" (by decide)]; exact h2, by rw [hr3.frame_inp (by decide)]; exact h3⟩
  obtain ⟨ρ4, hr4, hF4⟩ := rdArgs_spec B W O rest (m + 1) (nargs op) (by omega) hO hW (by omega) ρ3
    ⟨hF3, hna3⟩
  have hop4 : ρ4.vars "op" = op := by
    rw [hr4.frame_var "op" (by decide), hr3.frame_var "op" (by decide)]; simp [hρ2]
  have hpd4 : ρ4.vars "pd" = Ψt.length + 1 := by
    rw [hr4.frame_var "pd" (by decide), hr3.frame_var "pd" (by decide)]; simp [hρ2, hpd1]
  obtain ⟨ρ5, hr5, hpd5⟩ := setPd_spec B op (Ψt.length + 1) (by omega) (by omega) hpdB ρ4 ⟨hop4, hpd4⟩
  have hF5 : FAt W O rest (m + 1 + nargs op) ρ5 := by
    obtain ⟨h1, h2, h3⟩ := hF4
    exact ⟨by rw [hr5.frame_var "fl" (by decide)]; exact h1,
      by rw [hr5.frame_arr "f" (by decide)]; exact h2, by rw [hr5.frame_inp (by decide)]; exact h3⟩
  refine ⟨ρ5, ?_, ⟨m + 1 + nargs op, ch ++ Ψt, hF5, by omega, hdrop2, ?_⟩, ?_⟩
  · unfold fmlBody
    refine (Run.seq hr1 (Run.seq hr2 (Run.seq hr3 (Run.seq hr4 hr5)))).mono ?_
    have : nargs op ≤ 3 := by unfold nargs; split_ifs <;> omega
    omega
  · rw [hpd5, List.length_append, hch]; omega
  · rw [hF5.1, hF.1]; omega

/-- **Reading a formula.** `readFml` copies the code `W` of a formula from
the tape into `f` and leaves its length in `fl`. -/
theorem readFml_spec (B : ℕ) {ℓ : ℕ} (φ : DistFO ℓ) (O rest : List ℕ)
    (hO : (code φ).length ≤ O.length) (hW : ∀ v ∈ code φ, v < B) (hB : (code φ).length + 10 < B) :
    Spec B (fun ρ => ρ.inp = code φ ++ rest ∧ ρ.arrs "f" = O) readFml
      (fun _ ρ' => ρ'.vars "fl" = (code φ).length ∧ ρ'.arrs "f" = code φ ++ O.drop (code φ).length ∧
        ρ'.inp = rest) (124 * (code φ).length + 20) := by
  rintro ρ ⟨hinp, hf⟩
  set W := code φ with hWdef
  set ρ0 := (ρ.setVar "fl" 0).setVar "pd" 1 with hρ0
  have hI0 : RdInv W O rest ρ0 :=
    ⟨0, [⟨ℓ, φ⟩], ⟨by simp [hρ0], by simp [hρ0, hf], by simp [hρ0, hinp]⟩, by omega,
      by simp [codes, hWdef], by simp [hρ0]⟩
  have hpdB : ∀ σ, RdInv W O rest σ → σ.vars "pd" < B := by
    rintro σ ⟨m, Ψ, -, hm, hd, hp⟩
    have := length_le_codes Ψ
    have := congrArg List.length hd
    simp at this; omega
  obtain ⟨ρ', hr, hI', hfalse⟩ := (Spec.while_count (B := B) (b := .lt (.lit 0) (.var "pd"))
    (c := fmlBody) (P := fun σ => σ = ρ0) (K := 124 * W.length + 4) (RdInv W O rest)
    (fun σ => W.length - σ.vars "fl") 120
    (fun σ hI => ⟨_, evalB_condLt (evalB_lit (by omega)) (evalB_var (hpdB σ hI))⟩)
    ((fmlBody_spec B W O rest hO hW hB).conseq (fun σ ⟨hI, hc⟩ => ⟨hI, pos_of_condLt_true hc⟩)
      (fun σ σ' ⟨hI, _⟩ ⟨hI', hlt⟩ => ⟨hI', by
        obtain ⟨m, Ψ, hF, hm, -, -⟩ := hI'
        obtain ⟨m0, Ψ0, hF0, hm0, -, -⟩ := hI
        rw [hF.1] at hlt ⊢; rw [hF0.1] at hlt ⊢; omega⟩) le_rfl)
    (fun σ h => h ▸ hI0) (fun σ h => by subst h; simp [hρ0])).run rfl
  obtain ⟨m, Ψ, hF, hm, hd, hp⟩ := hI'
  have hΨ : Ψ = [] := List.eq_nil_of_length_eq_zero (by rw [← hp]; exact zero_of_condLt_false hfalse)
  subst hΨ
  have hmW : m = W.length := by
    have := congrArg List.length hd; simp [codes] at this; omega
  subst hmW
  obtain ⟨h1, h2, h3⟩ := hF
  refine ⟨ρ', ?_, h1, by rw [h2, List.take_length], by simp [h3]⟩
  unfold readFml
  exact (Run.seq (Run.assign (v := 0) (by simp; omega)) (Run.seq (Run.assign (v := 1) (by simp; omega))
    hr)).mono (by simp; omega)

end Lax185574Proofs.EvalRam
