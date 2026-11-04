import Lax185574Proofs.MC.Ram.Push
import Lax185574Proofs.MC.Localize
import Lax185574Proofs.Legacy


/-!
The rank and the localization of a sentence from its prefix code, for
the glue program of thm:mc.

The command `fLoop` walks the prefix code of a sentence in the array
`U` from position `fp`, with a stack `stk` of the numbers of free
variables of the pending subformulas. It keeps the largest such number
at an atom in `rk`, which is the quantifier rank at the end. In mode
`fm = 1` it also appends the code of the localization `loc q φ` to the
array `lo`, with the radii `rhoPlus (ℓ + 2) (q - ℓ - 1)` read from the
table `RP`.
-/

namespace Lax185574Proofs.MC.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC
open Lax3.FirstOrder
open Lax3.DistFO (rhoPlus)

/-! ### Pending subformulas -/

/-- A subformula with its number of free variables. -/
abbrev Pend := Σ ℓ : ℕ, FO ℓ

/-- The codes of the pending subformulas. -/
def pcode (ps : List Pend) : List ℕ := ps.flatMap fun p => Lax185574.InstanceEncoding.code p.2

/-- The codes of their localizations. -/
def ploc (q : ℕ) (ps : List Pend) : List ℕ :=
  ps.flatMap fun p => Lax185574.DistanceLogic.DistFO.code (loc q p.2)

/-- The largest rank of a pending subformula, plus its depth. -/
def prank (ps : List Pend) : ℕ := (ps.map fun p => p.1 + rank p.2).foldr max 0

/-- The depths, top of the stack last. -/
def pdeps (ps : List Pend) : List ℕ := (ps.map fun p => p.1).reverse

@[simp] theorem pcode_nil : pcode [] = [] := rfl
@[simp] theorem pcode_cons (p : Pend) (ps : List Pend) :
    pcode (p :: ps) = Lax185574.InstanceEncoding.code p.2 ++ pcode ps := by simp [pcode]
@[simp] theorem ploc_nil (q : ℕ) : ploc q [] = [] := rfl
@[simp] theorem ploc_cons (q : ℕ) (p : Pend) (ps : List Pend) :
    ploc q (p :: ps) = Lax185574.DistanceLogic.DistFO.code (loc q p.2) ++ ploc q ps := by
  simp [ploc]
@[simp] theorem prank_nil : prank [] = 0 := rfl
@[simp] theorem prank_cons (p : Pend) (ps : List Pend) :
    prank (p :: ps) = max (p.1 + rank p.2) (prank ps) := by simp [prank]
@[simp] theorem pdeps_cons (p : Pend) (ps : List Pend) :
    pdeps (p :: ps) = pdeps ps ++ [p.1] := by simp [pdeps]
@[simp] theorem length_pdeps (ps : List Pend) : (pdeps ps).length = ps.length := by
  simp [pdeps]

theorem code_ne_nil {ℓ : ℕ} (φ : FO ℓ) : Lax185574.InstanceEncoding.code φ ≠ [] := by
  cases φ <;> simp [Lax185574.InstanceEncoding.code]

theorem length_code_pos {ℓ : ℕ} (φ : FO ℓ) : 1 ≤ (Lax185574.InstanceEncoding.code φ).length :=
  List.length_pos_of_ne_nil (code_ne_nil φ)

theorem length_loc_le (q : ℕ) : ∀ {ℓ : ℕ} (φ : FO ℓ),
    (Lax185574.DistanceLogic.DistFO.code (loc q φ)).length ≤
      3 * (Lax185574.InstanceEncoding.code φ).length
  | _, .adj i j => by simp [loc, Lax185574.DistanceLogic.DistFO.code,
      Lax185574.InstanceEncoding.code]
  | _, .eq i j => by simp [loc, Lax185574.DistanceLogic.DistFO.code,
      Lax185574.InstanceEncoding.code]
  | _, .not φ => by
      have := length_loc_le q φ
      simp only [loc, Lax185574.DistanceLogic.DistFO.code, Lax185574.InstanceEncoding.code,
        List.length_cons]; omega
  | _, .and φ ψ => by
      have := length_loc_le q φ
      have := length_loc_le q ψ
      simp only [loc, Lax185574.DistanceLogic.DistFO.code, Lax185574.InstanceEncoding.code,
        List.length_cons, List.length_append]; omega
  | _, .ex φ => by
      have := length_loc_le q φ
      have := length_code_pos φ
      simp only [loc, Lax185574.DistanceLogic.DistFO.code, Lax185574.InstanceEncoding.code,
        List.length_cons]; omega

theorem length_ploc_le (q : ℕ) : ∀ ps : List Pend, (ploc q ps).length ≤ 3 * (pcode ps).length
  | [] => by simp
  | p :: ps => by
      have := length_loc_le q p.2
      have := length_ploc_le q ps
      simp only [ploc_cons, pcode_cons, List.length_append]; omega

theorem length_le_pcode : ∀ ps : List Pend, ps.length ≤ (pcode ps).length
  | [] => by simp
  | p :: ps => by
      have := length_code_pos p.2
      have := length_le_pcode ps
      simp only [pcode_cons, List.length_append, List.length_cons]; omega

theorem le_prank_of_mem {ps : List Pend} {p : Pend} (h : p ∈ ps) : p.1 + rank p.2 ≤ prank ps := by
  induction ps with
  | nil => simp at h
  | cons a ps ih =>
      rcases List.mem_cons.mp h with rfl | h
      · simp
      · simp only [prank_cons]; exact le_max_of_le_right (ih h)

/-! ### The command -/

/-- Pop the top depth into `fd` and read the opcode into `fo`. -/
def fPop : Com :=
  .seq (.assign "sp" (.sub (.var "sp") (.lit 1)))
    (.seq (.assign "fd" (.get "stk" (.var "sp"))) (.assign "fo" (.get "U" (.var "fp"))))

/-- Run `c` in mode `1` only. -/
def fEmit (c : Com) : Com := .ite (.eq (.var "fm") (.lit 1)) c .skip

/-- An atom: `adj i j` becomes `edge (i+1) (j+1)`, `eq i j` becomes `eq (i+1) (j+1)`. -/
def fAtom : Com :=
  .seq (.ite (.lt (.var "rk") (.var "fd")) (.assign "rk" (.var "fd")) .skip)
    (.seq (fEmit (pushL "lo" "lp" [.sub (.lit 1) (.var "fo"),
        .add (.get "U" (.add (.var "fp") (.lit 1))) (.lit 1),
        .add (.get "U" (.add (.var "fp") (.lit 2))) (.lit 1)]))
      (.assign "fp" (.add (.var "fp") (.lit 3))))

/-- A negation. -/
def fNot : Com :=
  .seq (fEmit (pushL "lo" "lp" [.lit 6]))
    (.seq (push1 "stk" "sp" (.var "fd")) (.assign "fp" (.add (.var "fp") (.lit 1))))

/-- A conjunction. -/
def fAnd : Com :=
  .seq (fEmit (pushL "lo" "lp" [.lit 7]))
    (.seq (push1 "stk" "sp" (.var "fd"))
      (.seq (push1 "stk" "sp" (.var "fd")) (.assign "fp" (.add (.var "fp") (.lit 1)))))

/-- A quantifier, guarded by the new variable `0` at radius `RP[fd]`. -/
def fEx : Com :=
  .seq (fEmit (pushL "lo" "lp" [.lit 8, .lit 0, .get "RP" (.var "fd")]))
    (.seq (push1 "stk" "sp" (.add (.var "fd") (.lit 1))) (.assign "fp" (.add (.var "fp") (.lit 1))))

/-- One symbol of the prefix code. -/
def fBody : Com :=
  .seq fPop (.ite (.lt (.var "fo") (.lit 2)) fAtom
    (.ite (.eq (.var "fo") (.lit 2)) fNot (.ite (.eq (.var "fo") (.lit 3)) fAnd fEx)))

/-- The walk over the code. -/
def fLoop : Com := .while (.lt (.lit 0) (.var "sp")) fBody


/-! ### Basic steps -/

local notation "fc" => Lax185574.InstanceEncoding.code
local notation "dc" => Lax185574.DistanceLogic.DistFO.code

theorem rank_le_code : ∀ {ℓ : ℕ} (φ : FO ℓ), rank φ ≤ (fc φ).length
  | _, .adj i j => by simp [rank]
  | _, .eq i j => by simp [rank]
  | _, .not φ => by
      have := rank_le_code φ
      simp only [rank, Lax185574.InstanceEncoding.code, List.length_cons]; omega
  | _, .and φ ψ => by
      have := rank_le_code φ
      have := rank_le_code ψ
      simp only [rank, Lax185574.InstanceEncoding.code, List.length_cons, List.length_append]
      omega
  | _, .ex φ => by
      have := rank_le_code φ
      simp only [rank, Lax185574.InstanceEncoding.code, List.length_cons]; omega

theorem filled_pop {a pv : String} {l : List ℕ} {d : ℕ} {τ : Env} (h : Filled a pv (l ++ [d]) τ) :
    Filled a pv l (τ.setVar pv l.length) ∧ (τ.arrs a)[l.length]? = some d := by
  refine ⟨⟨by simp, fun i hi => ?_⟩, ?_⟩
  · rw [arrs_setVar, h.get i (by simp; omega), List.getElem_append_left hi]
  · rw [h.get l.length (by simp)]; simp

theorem fPop_run {B : ℕ} {τ : Env} {ℓ : ℕ} {ψ : FO ℓ} {ps : List Pend} {R : List ℕ}
    (hs : Filled "stk" "sp" (pdeps (⟨ℓ, ψ⟩ :: ps)) τ)
    (hc : (τ.arrs "U").drop (τ.vars "fp") = pcode (⟨ℓ, ψ⟩ :: ps) ++ R)
    (hB : ps.length + 1 < B) (hℓ : ℓ < B) (hfp : τ.vars "fp" < B) (hop : (fc ψ).headD 0 < B) :
    Run B fPop τ (((τ.setVar "sp" ps.length).setVar "fd" ℓ).setVar "fo" ((fc ψ).headD 0)) 10 ∧
      Filled "stk" "sp" (pdeps ps)
        (((τ.setVar "sp" ps.length).setVar "fd" ℓ).setVar "fo" ((fc ψ).headD 0)) := by
  rw [pdeps_cons] at hs
  obtain ⟨hF, hg⟩ := filled_pop hs
  have hp := hs.pos
  simp only [List.length_append, length_pdeps, List.length_singleton] at hp
  have hu : (τ.arrs "U")[τ.vars "fp"]? = some ((fc ψ).headD 0) := by
    have h1 : (τ.arrs "U")[τ.vars "fp"]? = ((τ.arrs "U").drop (τ.vars "fp"))[0]? := by
      rw [List.getElem?_drop]; simp
    rw [h1, hc]
    obtain ⟨c, cs, hcs⟩ := List.exists_cons_of_ne_nil (code_ne_nil ψ)
    simp [hcs]
  refine ⟨(Run.seq (Run.assign ?_) (Run.seq (Run.assign ?_) (Run.assign ?_))).mono (by simp), ?_⟩
  · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
    exact ⟨_, _, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, by simp [Bop.apply, hp], by omega⟩
  · simp only [evalB_get_iff, evalB_var_iff, vars_setVar, arrs_setVar, if_true]
    refine ⟨ps.length, ⟨rfl, hB.trans' (by omega)⟩, ?_, hℓ⟩
    simpa using hg
  · simp only [evalB_get_iff, evalB_var_iff, vars_setVar, arrs_setVar]
    refine ⟨τ.vars "fp", ⟨by simp, by simpa using hfp⟩, by simpa using hu, hop⟩
  · have := (hF.setVar (y := "fd") (by decide) ℓ).setVar (y := "fo") (by decide) ((fc ψ).headD 0)
    simpa using this

/-- An emission in mode `1`, nothing in mode `0`. -/
theorem fEmit_pushL {B : ℕ} {es : List Expr} {vs : List ℕ} {l : List ℕ} {τ : Env}
    (hfm : τ.vars "fm" < B) (hB1 : 1 < B)
    (h : τ.vars "fm" = 1 → Filled "lo" "lp" l τ ∧ EvalsTo B "lo" "lp" τ es vs ∧
      l.length + vs.length ≤ (τ.arrs "lo").length ∧ l.length + vs.length < B) :
    ∃ τ', Run B (fEmit (pushL "lo" "lp" es)) τ τ' (5 + 7 * es.length + (es.map Expr.size).sum) ∧
      (∀ y, y ≠ "lp" → τ'.vars y = τ.vars y) ∧ (∀ b, b ≠ "lo" → τ'.arrs b = τ.arrs b) ∧
      (τ'.arrs "lo").length = (τ.arrs "lo").length ∧
      (τ.vars "fm" = 1 → Filled "lo" "lp" (l ++ vs) τ') := by
  by_cases h1 : τ.vars "fm" = 1
  · obtain ⟨hF, hev, hcap, hB⟩ := h h1
    obtain ⟨τ', r, F', fv, fa, fl, -, -⟩ := pushL_run hF hev hcap hB
    refine ⟨τ', (Run.ite_true ?_ r).mono (by simp; omega), fv, fa, fl, fun _ => F'⟩
    simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff]
    exact ⟨_, _, ⟨rfl, hfm⟩, ⟨rfl, by omega⟩, by simp [h1]⟩
  · refine ⟨τ, (Run.ite_false ?_ Run.skip).mono (by simp; omega), fun _ _ => rfl, fun _ _ => rfl, rfl,
      fun h => absurd h h1⟩
    simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff]
    refine ⟨_, 1, ⟨rfl, hfm⟩, ⟨rfl, by omega⟩, ?_⟩
    simp [h1]


/-! ### The invariant -/

/-- The context of the walk: room for the stack and, in mode `1`, for the
localization, the table of radii in mode `1`, and the bound. -/
structure FCtx (B q : ℕ) (φ : FO 0) (p0 : ℕ) (τ : Env) : Prop where
  stk : (fc φ).length + 1 ≤ (τ.arrs "stk").length
  lo : τ.vars "fm" = 1 → 3 * (fc φ).length ≤ (τ.arrs "lo").length
  rp : τ.vars "fm" = 1 → ∀ d < rank φ,
    (τ.arrs "RP")[d]? = some (rhoPlus (d + 2) (q - d - 1)) ∧ rhoPlus (d + 2) (q - d - 1) < B
  bnd : p0 + 3 * (fc φ).length + 5 < B
  fm : τ.vars "fm" < B

theorem FCtx.congr {B q : ℕ} {φ : FO 0} {p0 : ℕ} {τ τ' : Env} (h : FCtx B q φ p0 τ)
    (hs : (τ'.arrs "stk").length = (τ.arrs "stk").length)
    (hl : (τ'.arrs "lo").length = (τ.arrs "lo").length)
    (hr : τ'.arrs "RP" = τ.arrs "RP") (hm : τ'.vars "fm" = τ.vars "fm") : FCtx B q φ p0 τ' :=
  ⟨by rw [hs]; exact h.stk, by rw [hl, hm]; exact h.lo, by rw [hr, hm]; exact h.rp, h.bnd,
    by rw [hm]; exact h.fm⟩

/-- The invariant of the walk with the pending subformulas `ps`. -/
structure FInv (q : ℕ) (φ : FO 0) (R : List ℕ) (p0 : ℕ) (ps : List Pend) (τ : Env) : Prop where
  stk : Filled "stk" "sp" (pdeps ps) τ
  code : (τ.arrs "U").drop (τ.vars "fp") = pcode ps ++ R
  fp : τ.vars "fp" + (pcode ps).length = p0 + (fc φ).length
  len : ps.length + (pcode ps).length ≤ (fc φ).length + 1
  rk : max (τ.vars "rk") (prank ps) = rank φ
  lo : τ.vars "fm" = 1 → ∃ l, Filled "lo" "lp" l τ ∧ l ++ ploc q ps = dc (loc q φ)

/-- The state after popping the subformula `ψ` with `ℓ` free variables. -/
structure Popped (q : ℕ) (φ : FO 0) (R : List ℕ) (p0 : ℕ) (ℓ : ℕ) (ψ : FO ℓ) (ps : List Pend)
    (σ : Env) : Prop where
  stk : Filled "stk" "sp" (pdeps ps) σ
  fd : σ.vars "fd" = ℓ
  code : (σ.arrs "U").drop (σ.vars "fp") = fc ψ ++ (pcode ps ++ R)
  fp : σ.vars "fp" + (fc ψ).length + (pcode ps).length = p0 + (fc φ).length
  len : ps.length + 1 + (fc ψ).length + (pcode ps).length ≤ (fc φ).length + 1
  rk : max (σ.vars "rk") (max (ℓ + rank ψ) (prank ps)) = rank φ
  lo : σ.vars "fm" = 1 → ∃ l, Filled "lo" "lp" l σ ∧ l ++ (dc (loc q ψ) ++ ploc q ps) = dc (loc q φ)

theorem getElem_U {σ : Env} {c r : List ℕ} (h : (σ.arrs "U").drop (σ.vars "fp") = c ++ r) {k : ℕ}
    (hk : k < c.length) : (σ.arrs "U")[σ.vars "fp" + k]? = some c[k] := by
  have : (σ.arrs "U")[σ.vars "fp" + k]? = ((σ.arrs "U").drop (σ.vars "fp"))[k]? := by
    rw [List.getElem?_drop]
  rw [this, h, List.getElem?_append_left hk, List.getElem?_eq_getElem hk]

theorem drop_U {σ : Env} {c r : List ℕ} (h : (σ.arrs "U").drop (σ.vars "fp") = c ++ r) :
    (σ.arrs "U").drop (σ.vars "fp" + c.length) = r := by
  have := congrArg (List.drop c.length) h
  rw [List.drop_drop, List.drop_left] at this
  exact this

theorem rkMax_run {B : ℕ} {σ : Env} (hr : σ.vars "rk" < B) (hd : σ.vars "fd" < B) :
    ∃ σ₁, Run B (.ite (.lt (.var "rk") (.var "fd")) (.assign "rk" (.var "fd")) .skip) σ σ₁ 6 ∧
      σ₁.vars "rk" = max (σ.vars "rk") (σ.vars "fd") ∧ (∀ y, y ≠ "rk" → σ₁.vars y = σ.vars y) ∧
      σ₁.arrs = σ.arrs := by
  by_cases h : σ.vars "rk" < σ.vars "fd"
  · refine ⟨σ.setVar "rk" (σ.vars "fd"), (Run.ite_true ?_ (Run.assign ?_)).mono (by simp),
      by simp; omega, fun y hy => by simp [hy], by simp⟩
    · simp only [evalB_condLt_iff, evalB_var_iff]
      exact ⟨_, _, ⟨rfl, hr⟩, ⟨rfl, hd⟩, by simp [h]⟩
    · exact evalB_var hd
  · refine ⟨σ, (Run.ite_false ?_ Run.skip).mono (by simp), by omega, fun _ _ => rfl, rfl⟩
    simp only [evalB_condLt_iff, evalB_var_iff]
    exact ⟨_, _, ⟨rfl, hr⟩, ⟨rfl, hd⟩, by simp [h]⟩


theorem ev_var {B : ℕ} {x : String} {σ : Env} {v : ℕ} (h : σ.vars x = v) (hv : v < B) :
    (Expr.var x).evalB B σ = some v := by subst h; exact evalB_var hv

theorem ev_add {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ} (he : e.evalB B σ = some m)
    (hf : f.evalB B σ = some n) (h : m + n < B) : (Expr.add e f).evalB B σ = some (m + n) :=
  evalB_bin he hf h

theorem ev_sub {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ} (he : e.evalB B σ = some m)
    (hf : f.evalB B σ = some n) (h : m - n < B) : (Expr.sub e f).evalB B σ = some (m - n) :=
  evalB_bin he hf h

/-- The lo buffer before an emission, whatever the mode. -/
theorem exists_lo {q : ℕ} {φ : FO 0} {σ : Env} {r : List ℕ}
    (h : σ.vars "fm" = 1 → ∃ l, Filled "lo" "lp" l σ ∧ l ++ r = dc (loc q φ)) :
    ∃ l, σ.vars "fm" = 1 → Filled "lo" "lp" l σ ∧ l ++ r = dc (loc q φ) := by
  by_cases hm : σ.vars "fm" = 1
  · obtain ⟨l, h1, h2⟩ := h hm; exact ⟨l, fun _ => ⟨h1, h2⟩⟩
  · exact ⟨[], fun h' => absurd h' hm⟩

theorem length_lo_le {q : ℕ} {φ : FO 0} {l r : List ℕ} (h : l ++ r = dc (loc q φ)) :
    l.length + r.length ≤ 3 * (fc φ).length := by
  have := congrArg List.length h
  have := length_loc_le q φ
  simp only [List.length_append] at *; omega

theorem fAtom_case {B q : ℕ} {φ : FO 0} {R : List ℕ} {p0 ℓ : ℕ} {ψ : FO ℓ} {ps : List Pend}
    {σ : Env} (opc i j : ℕ) (hc : fc ψ = [opc, i, j]) (hl : dc (loc q ψ) = [1 - opc, i + 1, j + 1])
    (hrk : rank ψ = 0) (hi : i < ℓ) (hj : j < ℓ) (ho : σ.vars "fo" = opc) (hop : opc ≤ 1)
    (hC : FCtx B q φ p0 σ) (hP : Popped q φ R p0 ℓ ψ ps σ) :
    ∃ σ', Run B fAtom σ σ' 60 ∧ FCtx B q φ p0 σ' ∧ FInv q φ R p0 ps σ' ∧
      σ.vars "fp" < σ'.vars "fp" := by
  have hrkφ := rank_le_code φ
  have hrk1 := hP.rk
  have hfp := hP.fp
  have hbnd := hC.bnd
  rw [hc] at hfp
  simp only [List.length_cons, List.length_nil] at hfp
  have hℓ : ℓ ≤ rank φ := by rw [← hrk1, hrk]; omega
  have hrkσ : σ.vars "rk" ≤ rank φ := by rw [← hrk1]; omega
  obtain ⟨σ₁, r₁, hk₁, hv₁, ha₁⟩ := rkMax_run (B := B) (σ := σ) (by omega) (by rw [hP.fd]; omega)
  obtain ⟨l, hlo⟩ := exists_lo hP.lo
  have hU1 : (σ₁.arrs "U")[σ.vars "fp" + 1]? = some i := by
    rw [ha₁]
    simpa [hc] using getElem_U (k := 1) hP.code (by simp [hc])
  have hU2 : (σ₁.arrs "U")[σ.vars "fp" + 2]? = some j := by
    rw [ha₁]
    simpa [hc] using getElem_U (k := 2) hP.code (by simp [hc])
  have hfp1 : σ₁.vars "fp" = σ.vars "fp" := hv₁ _ (by decide)
  have hfpB : σ.vars "fp" + 3 < B := by omega
  obtain ⟨σ₂, r₂, hv₂, ha₂, hl₂, hF₂⟩ := fEmit_pushL (B := B) (τ := σ₁)
    (es := [.sub (.lit 1) (.var "fo"), .add (.get "U" (.add (.var "fp") (.lit 1))) (.lit 1),
      .add (.get "U" (.add (.var "fp") (.lit 2))) (.lit 1)]) (vs := [1 - opc, i + 1, j + 1]) (l := l)
    (by rw [hv₁ _ (by decide)]; exact hC.fm) (by omega) (by
      intro hm
      rw [hv₁ _ (by decide)] at hm
      obtain ⟨hF, heq⟩ := hlo hm
      have hlen := length_lo_le heq
      have hlo' := hC.lo hm
      simp only [List.length_append, hl, List.length_cons, List.length_nil] at hlen
      refine ⟨hF.congr (hv₁ _ (by decide)) (by rw [ha₁]), ?_, ?_, ?_⟩
      · intro τ' hv ha
        have hfo : τ'.vars "fo" = opc := by rw [hv _ (by decide), hv₁ _ (by decide), ho]
        have hfp' : τ'.vars "fp" = σ.vars "fp" := (hv _ (by decide)).trans hfp1
        have hU' : τ'.arrs "U" = σ₁.arrs "U" := ha _ (by decide)
        refine .cons ?_ (.cons ?_ (.cons ?_ .nil))
        · exact ev_sub (evalB_lit (by omega)) (ev_var hfo (by omega)) (by omega)
        · refine ev_add (evalB_get (ev_add (ev_var hfp' (by omega)) (evalB_lit (by omega))
            (by omega)) (by rw [hU']; exact hU1) (by omega)) (evalB_lit (by omega)) (by omega)
        · refine ev_add (evalB_get (ev_add (ev_var hfp' (by omega)) (evalB_lit (by omega))
            (by omega)) (by rw [hU']; exact hU2) (by omega)) (evalB_lit (by omega)) (by omega)
      · rw [ha₁]; simp only [List.length_cons, List.length_nil]; omega
      · simp only [List.length_cons, List.length_nil]; omega)
  have hfp2 : σ₂.vars "fp" = σ.vars "fp" := by rw [hv₂ _ (by decide), hfp1]
  refine ⟨σ₂.setVar "fp" (σ.vars "fp" + 3),
    (Run.seq r₁ (Run.seq r₂ (Run.assign (ev_add (ev_var hfp2 (by omega)) (evalB_lit (by omega))
      (by omega))))).mono (by simp), ?_, ?_, by simp⟩
  · refine hC.congr ?_ ?_ ?_ ?_
    · simp [ha₂ "stk" (by decide), ha₁]
    · simp [hl₂, ha₁]
    · simp [ha₂ "RP" (by decide), ha₁]
    · simp [hv₂ "fm" (by decide), hv₁ "fm" (by decide)]
  · refine ⟨hP.stk.congr ?_ ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hv₂ "sp" (by decide), hv₁ "sp" (by decide)]
    · simp [ha₂ "stk" (by decide), ha₁]
    · have := drop_U hP.code
      simp only [hc, List.length_cons, List.length_nil] at this
      simp [ha₂ "U" (by decide), ha₁, this]
    · simp; omega
    · have := hP.len; rw [hc] at this; simp at this; omega
    · simp only [vars_setVar, show ("rk" : String) ≠ "fp" by decide, if_false,
        hv₂ _ (by decide : ("rk" : String) ≠ "lp"), hk₁, hP.fd]
      rw [← hrk1, hrk]; omega
    · intro hm
      simp only [vars_setVar, show ("fm" : String) ≠ "fp" by decide, if_false,
        hv₂ _ (by decide : ("fm" : String) ≠ "lp")] at hm
      rw [hv₁ _ (by decide)] at hm
      refine ⟨l ++ [1 - opc, i + 1, j + 1], (hF₂ (by rw [hv₁ _ (by decide)]; exact hm)).setVar
        (by decide) _, ?_⟩
      rw [← (hlo hm).2, hl]; simp


/-- The invariant after a symbol that is not an atom. -/
theorem finv_of {q : ℕ} {φ : FO 0} {R : List ℕ} {p0 ℓ : ℕ} {ψ : FO ℓ} {ps ps' : List Pend}
    {σ σ' : Env} {l vs : List ℕ} {c0 : ℕ} (hP : Popped q φ R p0 ℓ ψ ps σ)
    (hc : fc ψ ++ pcode ps = c0 :: pcode ps') (hlv : dc (loc q ψ) ++ ploc q ps = vs ++ ploc q ps')
    (hlen : ps'.length ≤ ps.length + 2) (hrank : max (ℓ + rank ψ) (prank ps) = prank ps')
    (hstk : Filled "stk" "sp" (pdeps ps') σ') (hU : σ'.arrs "U" = σ.arrs "U")
    (hfp : σ'.vars "fp" = σ.vars "fp" + 1) (hrk : σ'.vars "rk" = σ.vars "rk")
    (hfm : σ'.vars "fm" = σ.vars "fm")
    (hlo : σ.vars "fm" = 1 → Filled "lo" "lp" l σ ∧ l ++ (dc (loc q ψ) ++ ploc q ps) = dc (loc q φ))
    (hlo' : σ.vars "fm" = 1 → Filled "lo" "lp" (l ++ vs) σ') : FInv q φ R p0 ps' σ' := by
  have hcl := congrArg List.length hc
  simp only [List.length_append, List.length_cons] at hcl
  have h1 : (σ.arrs "U").drop (σ.vars "fp") = [c0] ++ (pcode ps' ++ R) := by
    rw [hP.code, ← List.append_assoc, hc]; rfl
  refine ⟨hstk, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hU, hfp]; simpa using drop_U h1
  · have := hP.fp; rw [hfp]; omega
  · have := hP.len; omega
  · rw [hrk, ← hrank]; exact hP.rk
  · intro hm
    rw [hfm] at hm
    refine ⟨l ++ vs, hlo' hm, ?_⟩
    rw [List.append_assoc, ← hlv]; exact (hlo hm).2

theorem fNot_case {B q : ℕ} {φ : FO 0} {R : List ℕ} {p0 ℓ : ℕ} {ψ : FO ℓ} {ps : List Pend}
    {σ : Env} (hC : FCtx B q φ p0 σ) (hP : Popped q φ R p0 ℓ (.not ψ) ps σ) :
    ∃ σ', Run B fNot σ σ' 60 ∧ FCtx B q φ p0 σ' ∧ FInv q φ R p0 (⟨ℓ, ψ⟩ :: ps) σ' ∧
      σ.vars "fp" < σ'.vars "fp" := by
  have hrkφ := rank_le_code φ
  have hrk1 := hP.rk
  have hfp := hP.fp
  have hlen := hP.len
  have hbnd := hC.bnd
  have hcψ := length_code_pos ψ
  simp only [Lax185574.InstanceEncoding.code, List.length_cons, rank] at hfp hlen hrk1
  have hℓ : ℓ ≤ rank φ := by rw [← hrk1]; omega
  have hfpB : σ.vars "fp" + 3 < B := by omega
  obtain ⟨l, hlo⟩ := exists_lo hP.lo
  obtain ⟨σ₁, r₁, hv₁, ha₁, hl₁, hF₁⟩ := fEmit_pushL (B := B) (τ := σ) (es := [.lit 6]) (vs := [6])
    (l := l) hC.fm (by omega) (by
      intro hm
      obtain ⟨hF, heq⟩ := hlo hm
      have hlen' := length_lo_le heq
      have hlo' := hC.lo hm
      simp only [List.length_append, loc, Lax185574.DistanceLogic.DistFO.code,
        List.length_cons] at hlen'
      refine ⟨hF, fun τ' _ _ => .cons (evalB_lit (by omega)) .nil, ?_, ?_⟩ <;>
        simp only [List.length_cons, List.length_nil] <;> omega)
  have hs₁ : Filled "stk" "sp" (pdeps ps) σ₁ :=
    hP.stk.congr (hv₁ "sp" (by decide)) (ha₁ "stk" (by decide))
  have hlps := length_le_pcode ps
  obtain ⟨σ₂, r₂, hs₂, hv₂, ha₂, hl₂, -, -⟩ := push1_run (B := B) hs₁ (e := .var "fd") (v := ℓ)
    (ev_var (by rw [hv₁ "fd" (by decide), hP.fd]) (by omega))
    (by rw [ha₁ "stk" (by decide)]; have := hC.stk; simp only [length_pdeps]; omega)
    (by simp only [length_pdeps]; omega)
  have hfp2 : σ₂.vars "fp" = σ.vars "fp" := by rw [hv₂ _ (by decide), hv₁ _ (by decide)]
  refine ⟨σ₂.setVar "fp" (σ.vars "fp" + 1),
    (Run.seq r₁ (Run.seq r₂ (Run.assign (ev_add (ev_var hfp2 (by omega)) (evalB_lit (by omega))
      (by omega))))).mono (by simp), ?_, ?_, by simp⟩
  · refine hC.congr ?_ ?_ ?_ ?_
    · simp [hl₂, ha₁ "stk" (by decide)]
    · simp [ha₂ "lo" (by decide), hl₁]
    · simp [ha₂ "RP" (by decide), ha₁ "RP" (by decide)]
    · simp [hv₂ "fm" (by decide), hv₁ "fm" (by decide)]
  · refine finv_of (c0 := 2) (vs := [6]) (l := l) hP (by simp [Lax185574.InstanceEncoding.code])
      (by simp [loc, Lax185574.DistanceLogic.DistFO.code]) (by simp) (by simp [rank])
      (by simpa using hs₂.setVar (y := "fp") (by decide) (σ.vars "fp" + 1))
      (by simp [ha₂ "U" (by decide), ha₁ "U" (by decide)]) (by simp)
      (by simp [hv₂ "rk" (by decide), hv₁ "rk" (by decide)])
      (by simp [hv₂ "fm" (by decide), hv₁ "fm" (by decide)]) hlo (fun hm => ?_)
    exact ((hF₁ hm).congr (hv₂ "lp" (by decide)) (ha₂ "lo" (by decide))).setVar (by decide) _


theorem fAnd_case {B q : ℕ} {φ : FO 0} {R : List ℕ} {p0 ℓ : ℕ} {ψ χ : FO ℓ} {ps : List Pend}
    {σ : Env} (hC : FCtx B q φ p0 σ) (hP : Popped q φ R p0 ℓ (.and ψ χ) ps σ) :
    ∃ σ', Run B fAnd σ σ' 80 ∧ FCtx B q φ p0 σ' ∧ FInv q φ R p0 (⟨ℓ, ψ⟩ :: ⟨ℓ, χ⟩ :: ps) σ' ∧
      σ.vars "fp" < σ'.vars "fp" := by
  have hrkφ := rank_le_code φ
  have hrk1 := hP.rk
  have hfp := hP.fp
  have hlen := hP.len
  have hbnd := hC.bnd
  have hcψ := length_code_pos ψ
  have hcχ := length_code_pos χ
  simp only [Lax185574.InstanceEncoding.code, List.length_cons, List.length_append,
    rank] at hfp hlen hrk1
  have hℓ : ℓ ≤ rank φ := by rw [← hrk1]; omega
  have hfpB : σ.vars "fp" + 3 < B := by omega
  obtain ⟨l, hlo⟩ := exists_lo hP.lo
  obtain ⟨σ₁, r₁, hv₁, ha₁, hl₁, hF₁⟩ := fEmit_pushL (B := B) (τ := σ) (es := [.lit 7]) (vs := [7])
    (l := l) hC.fm (by omega) (by
      intro hm
      obtain ⟨hF, heq⟩ := hlo hm
      have hlen' := length_lo_le heq
      have hlo' := hC.lo hm
      simp only [List.length_append, loc, Lax185574.DistanceLogic.DistFO.code,
        List.length_cons] at hlen'
      refine ⟨hF, fun τ' _ _ => .cons (evalB_lit (by omega)) .nil, ?_, ?_⟩ <;>
        simp only [List.length_cons, List.length_nil] <;> omega)
  have hs₁ : Filled "stk" "sp" (pdeps ps) σ₁ :=
    hP.stk.congr (hv₁ "sp" (by decide)) (ha₁ "stk" (by decide))
  have hlps := length_le_pcode ps
  have hstkl := hC.stk
  obtain ⟨σ₂, r₂, hs₂, hv₂, ha₂, hl₂, -, -⟩ := push1_run (B := B) hs₁ (e := .var "fd") (v := ℓ)
    (ev_var (by rw [hv₁ "fd" (by decide), hP.fd]) (by omega))
    (by rw [ha₁ "stk" (by decide)]; simp only [length_pdeps]; omega)
    (by simp only [length_pdeps]; omega)
  obtain ⟨σ₃, r₃, hs₃, hv₃, ha₃, hl₃, -, -⟩ := push1_run (B := B) hs₂ (e := .var "fd") (v := ℓ)
    (ev_var (by rw [hv₂ "fd" (by decide), hv₁ "fd" (by decide), hP.fd]) (by omega))
    (by rw [hl₂, ha₁ "stk" (by decide)]; simp only [List.length_append, length_pdeps,
      List.length_singleton]; omega)
    (by simp only [List.length_append, length_pdeps, List.length_singleton]; omega)
  have hfp3 : σ₃.vars "fp" = σ.vars "fp" := by
    rw [hv₃ _ (by decide), hv₂ _ (by decide), hv₁ _ (by decide)]
  refine ⟨σ₃.setVar "fp" (σ.vars "fp" + 1),
    (Run.seq r₁ (Run.seq r₂ (Run.seq r₃ (Run.assign (ev_add (ev_var hfp3 (by omega))
      (evalB_lit (by omega)) (by omega)))))).mono (by simp), ?_, ?_, by simp⟩
  · refine hC.congr ?_ ?_ ?_ ?_
    · simp [hl₃, hl₂, ha₁ "stk" (by decide)]
    · simp [ha₃ "lo" (by decide), ha₂ "lo" (by decide), hl₁]
    · simp [ha₃ "RP" (by decide), ha₂ "RP" (by decide), ha₁ "RP" (by decide)]
    · simp [hv₃ "fm" (by decide), hv₂ "fm" (by decide), hv₁ "fm" (by decide)]
  · refine finv_of (c0 := 3) (vs := [7]) (l := l) hP (by simp [Lax185574.InstanceEncoding.code])
      (by simp [loc, Lax185574.DistanceLogic.DistFO.code]) (by simp)
      (by simp [rank]; omega)
      (by simpa using hs₃.setVar (y := "fp") (by decide) (σ.vars "fp" + 1))
      (by simp [ha₃ "U" (by decide), ha₂ "U" (by decide), ha₁ "U" (by decide)]) (by simp)
      (by simp [hv₃ "rk" (by decide), hv₂ "rk" (by decide), hv₁ "rk" (by decide)])
      (by simp [hv₃ "fm" (by decide), hv₂ "fm" (by decide), hv₁ "fm" (by decide)]) hlo
      (fun hm => ?_)
    exact (((hF₁ hm).congr (hv₂ "lp" (by decide)) (ha₂ "lo" (by decide))).congr
      (hv₃ "lp" (by decide)) (ha₃ "lo" (by decide))).setVar (by decide) _

theorem fEx_case {B q : ℕ} {φ : FO 0} {R : List ℕ} {p0 ℓ : ℕ} {ψ : FO (ℓ + 1)} {ps : List Pend}
    {σ : Env} (hC : FCtx B q φ p0 σ) (hP : Popped q φ R p0 ℓ (.ex ψ) ps σ) :
    ∃ σ', Run B fEx σ σ' 80 ∧ FCtx B q φ p0 σ' ∧ FInv q φ R p0 (⟨ℓ + 1, ψ⟩ :: ps) σ' ∧
      σ.vars "fp" < σ'.vars "fp" := by
  have hrkφ := rank_le_code φ
  have hrk1 := hP.rk
  have hfp := hP.fp
  have hlen := hP.len
  have hbnd := hC.bnd
  have hcψ := length_code_pos ψ
  simp only [Lax185574.InstanceEncoding.code, List.length_cons, rank] at hfp hlen hrk1
  have hℓ : ℓ < rank φ := by rw [← hrk1]; omega
  have hfpB : σ.vars "fp" + 3 < B := by omega
  obtain ⟨l, hlo⟩ := exists_lo hP.lo
  obtain ⟨σ₁, r₁, hv₁, ha₁, hl₁, hF₁⟩ := fEmit_pushL (B := B) (τ := σ)
    (es := [.lit 8, .lit 0, .get "RP" (.var "fd")]) (vs := [8, 0, rhoPlus (ℓ + 2) (q - ℓ - 1)])
    (l := l) hC.fm (by omega) (by
      intro hm
      obtain ⟨hF, heq⟩ := hlo hm
      have hlen' := length_lo_le heq
      have hlo' := hC.lo hm
      obtain ⟨hrp, hrpB⟩ := hC.rp hm ℓ hℓ
      simp only [List.length_append, loc, Lax185574.DistanceLogic.DistFO.code,
        List.length_cons] at hlen'
      refine ⟨hF, fun τ' hv ha => .cons (evalB_lit (by omega)) (.cons (evalB_lit (by omega))
        (.cons (evalB_get (ev_var (by rw [hv "fd" (by decide), hP.fd]) (by omega))
          (by rw [ha "RP" (by decide)]; exact hrp) hrpB) .nil)), ?_, ?_⟩ <;>
        simp only [List.length_cons, List.length_nil] <;> omega)
  have hs₁ : Filled "stk" "sp" (pdeps ps) σ₁ :=
    hP.stk.congr (hv₁ "sp" (by decide)) (ha₁ "stk" (by decide))
  have hlps := length_le_pcode ps
  obtain ⟨σ₂, r₂, hs₂, hv₂, ha₂, hl₂, -, -⟩ := push1_run (B := B) hs₁
    (e := .add (.var "fd") (.lit 1)) (v := ℓ + 1)
    (ev_add (ev_var (by rw [hv₁ "fd" (by decide), hP.fd]) (by omega)) (evalB_lit (by omega))
      (by omega))
    (by rw [ha₁ "stk" (by decide)]; have := hC.stk; simp only [length_pdeps]; omega)
    (by simp only [length_pdeps]; omega)
  have hfp2 : σ₂.vars "fp" = σ.vars "fp" := by rw [hv₂ _ (by decide), hv₁ _ (by decide)]
  refine ⟨σ₂.setVar "fp" (σ.vars "fp" + 1),
    (Run.seq r₁ (Run.seq r₂ (Run.assign (ev_add (ev_var hfp2 (by omega)) (evalB_lit (by omega))
      (by omega))))).mono (by simp), ?_, ?_, by simp⟩
  · refine hC.congr ?_ ?_ ?_ ?_
    · simp [hl₂, ha₁ "stk" (by decide)]
    · simp [ha₂ "lo" (by decide), hl₁]
    · simp [ha₂ "RP" (by decide), ha₁ "RP" (by decide)]
    · simp [hv₂ "fm" (by decide), hv₁ "fm" (by decide)]
  · refine finv_of (c0 := 4) (vs := [8, 0, rhoPlus (ℓ + 2) (q - ℓ - 1)]) (l := l) hP
      (by simp [Lax185574.InstanceEncoding.code])
      (by simp [loc, Lax185574.DistanceLogic.DistFO.code]) (by simp) (by simp [rank]; omega)
      (by simpa using hs₂.setVar (y := "fp") (by decide) (σ.vars "fp" + 1))
      (by simp [ha₂ "U" (by decide), ha₁ "U" (by decide)]) (by simp)
      (by simp [hv₂ "rk" (by decide), hv₁ "rk" (by decide)])
      (by simp [hv₂ "fm" (by decide), hv₁ "fm" (by decide)]) hlo (fun hm => ?_)
    exact ((hF₁ hm).congr (hv₂ "lp" (by decide)) (ha₂ "lo" (by decide))).setVar (by decide) _


/-! ### The loop -/

theorem fBody_step {B q : ℕ} {φ : FO 0} {R : List ℕ} {p0 : ℕ} {p : Pend} {ps : List Pend}
    {σ : Env} (hC : FCtx B q φ p0 σ) (hI : FInv q φ R p0 (p :: ps) σ) :
    ∃ σ' ps', Run B fBody σ σ' 120 ∧ FCtx B q φ p0 σ' ∧ FInv q φ R p0 ps' σ' ∧
      σ.vars "fp" < σ'.vars "fp" := by
  obtain ⟨ℓ, ψ⟩ := p
  have hrkφ := rank_le_code φ
  have hfp := hI.fp
  have hlen := hI.len
  have hrk := hI.rk
  have hbnd := hC.bnd
  have hcψ := length_code_pos ψ
  simp only [pcode_cons, List.length_append, List.length_cons, prank_cons] at hfp hlen hrk
  have hℓ : ℓ ≤ rank φ := by rw [← hrk]; omega
  have hop : (fc ψ).headD 0 ≤ 4 := by cases ψ <;> simp [Lax185574.InstanceEncoding.code]
  obtain ⟨rP, hsP⟩ := fPop_run (B := B) hI.stk hI.code (by omega) (by omega) (by omega) (by omega)
  set τ := ((σ.setVar "sp" ps.length).setVar "fd" ℓ).setVar "fo" ((fc ψ).headD 0) with hτ
  have hCτ : FCtx B q φ p0 τ := hC.congr (by simp [hτ]) (by simp [hτ]) (by simp [hτ])
    (by simp [hτ])
  have hPτ : Popped q φ R p0 ℓ ψ ps τ := by
    refine ⟨hsP, by simp [hτ], ?_, ?_, ?_, ?_, ?_⟩
    · have := hI.code; simp only [pcode_cons, List.append_assoc] at this; simpa [hτ] using this
    · simp [hτ]; omega
    · omega
    · simpa [hτ] using hrk
    · intro hm
      simp only [hτ, vars_setVar] at hm
      simp only [show ("fm" : String) ≠ "fo" by decide, show ("fm" : String) ≠ "fd" by decide,
        show ("fm" : String) ≠ "sp" by decide, if_false] at hm
      obtain ⟨l, hF, hl⟩ := hI.lo hm
      exact ⟨l, hF.congr (by simp [hτ]) (by simp [hτ]), by simpa using hl⟩
  have hfo : τ.vars "fo" = (fc ψ).headD 0 := by simp [hτ]
  have hfpτ : τ.vars "fp" = σ.vars "fp" := by simp [hτ]
  have c_lt (a : ℕ) (h : a < B) : ∀ b : Bool, decide ((fc ψ).headD 0 < a) = b →
      (Cond.lt (.var "fo") (.lit a)).evalB B τ = some b := by
    intro b hb; rw [← hb]; exact evalB_condLt (ev_var hfo (by omega)) (evalB_lit h)
  have c_eq (a : ℕ) (h : a < B) : ∀ b : Bool, ((fc ψ).headD 0 == a) = b →
      (Cond.eq (.var "fo") (.lit a)).evalB B τ = some b := by
    intro b hb; rw [← hb]; exact evalB_condEq (ev_var hfo (by omega)) (evalB_lit h)
  cases ψ with
  | adj i j =>
      obtain ⟨σ', r, hC', hI', hlt⟩ := fAtom_case 0 i j rfl (by simp [loc,
        Lax185574.DistanceLogic.DistFO.code]) rfl i.isLt j.isLt hfo (by omega) hCτ hPτ
      exact ⟨σ', ps, (Run.seq rP (Run.ite_true (c_lt 2 (by omega) true (by simp
        [Lax185574.InstanceEncoding.code])) r)).mono (by simp), hC', hI', by omega⟩
  | eq i j =>
      obtain ⟨σ', r, hC', hI', hlt⟩ := fAtom_case 1 i j rfl (by simp [loc,
        Lax185574.DistanceLogic.DistFO.code]) rfl i.isLt j.isLt hfo (by omega) hCτ hPτ
      exact ⟨σ', ps, (Run.seq rP (Run.ite_true (c_lt 2 (by omega) true (by simp
        [Lax185574.InstanceEncoding.code])) r)).mono (by simp), hC', hI', by omega⟩
  | not χ =>
      obtain ⟨σ', r, hC', hI', hlt⟩ := fNot_case hCτ hPτ
      exact ⟨σ', _, (Run.seq rP (Run.ite_false (c_lt 2 (by omega) false (by simp
        [Lax185574.InstanceEncoding.code])) (Run.ite_true (c_eq 2 (by omega) true (by simp
        [Lax185574.InstanceEncoding.code])) r))).mono (by simp), hC', hI', by omega⟩
  | and χ χ' =>
      obtain ⟨σ', r, hC', hI', hlt⟩ := fAnd_case hCτ hPτ
      exact ⟨σ', _, (Run.seq rP (Run.ite_false (c_lt 2 (by omega) false (by simp
        [Lax185574.InstanceEncoding.code])) (Run.ite_false (c_eq 2 (by omega) false (by simp
        [Lax185574.InstanceEncoding.code])) (Run.ite_true (c_eq 3 (by omega) true (by simp
        [Lax185574.InstanceEncoding.code])) r)))).mono (by simp), hC', hI', by omega⟩
  | ex χ =>
      obtain ⟨σ', r, hC', hI', hlt⟩ := fEx_case hCτ hPτ
      exact ⟨σ', _, (Run.seq rP (Run.ite_false (c_lt 2 (by omega) false (by simp
        [Lax185574.InstanceEncoding.code])) (Run.ite_false (c_eq 2 (by omega) false (by simp
        [Lax185574.InstanceEncoding.code])) (Run.ite_false (c_eq 3 (by omega) false (by simp
        [Lax185574.InstanceEncoding.code])) r)))).mono (by simp), hC', hI', by omega⟩

theorem fLoop_run {B q : ℕ} {φ : FO 0} {R : List ℕ} {p0 : ℕ} {ps : List Pend} {σ : Env}
    (hC : FCtx B q φ p0 σ) (hI : FInv q φ R p0 ps σ) :
    ∃ σ', Run B fLoop σ σ' (124 * (fc φ).length + 128) ∧ FCtx B q φ p0 σ' ∧
      FInv q φ R p0 [] σ' := by
  have hbnd := hC.bnd
  have hdef : ∀ τ, (FCtx B q φ p0 τ ∧ ∃ ps, FInv q φ R p0 ps τ) →
      τ.vars "sp" < B := by
    rintro τ ⟨-, ps, hI⟩
    have := hI.stk.pos; have := hI.len; simp only [length_pdeps] at *; omega
  obtain ⟨σ', r, ⟨hC', ps', hI'⟩, hf⟩ := Run.while_count (B := B) (b := .lt (.lit 0) (.var "sp"))
    (c := fBody) (fun τ => FCtx B q φ p0 τ ∧ ∃ ps, FInv q φ R p0 ps τ)
    (fun τ => p0 + (fc φ).length - τ.vars "fp") 120
    (fun τ h => ⟨_, evalB_condLt (evalB_lit (by omega)) (evalB_var (hdef τ h))⟩)
    (by
      rintro τ ⟨hCτ, ps, hIτ⟩ hc
      rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (hdef τ ⟨hCτ, ps, hIτ⟩))] at hc
      simp only [Option.some.injEq, decide_eq_true_eq] at hc
      cases ps with
      | nil => have := hIτ.stk.pos; simp at this; omega
      | cons p ps =>
          obtain ⟨τ', ps', r, hC', hI', hlt⟩ := fBody_step hCτ hIτ
          have := hI'.fp
          exact ⟨τ', r, ⟨hC', ps', hI'⟩, by omega⟩)
    ⟨hC, ps, hI⟩
  rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (hdef σ' ⟨hC', ps', hI'⟩))] at hf
  simp only [Option.some.injEq, decide_eq_false_iff_not, not_lt] at hf
  have hps : ps' = [] := by
    have := hI'.stk.pos; simp only [length_pdeps] at this
    exact List.eq_nil_of_length_eq_zero (by omega)
  subst hps
  refine ⟨σ', r.mono ?_, hC', hI'⟩
  simp only [Cond.size, Expr.size]
  have : p0 + (fc φ).length - σ.vars "fp" ≤ (fc φ).length + 1 := by
    have h1 := hI.fp; have h2 := hI.len; omega
  nlinarith


/-- The walk from the start: the stack holds the sentence at depth `0`. -/
def fWalk : Com :=
  .seq (.assign "sp" (.lit 0)) (.seq (push1 "stk" "sp" (.lit 0))
    (.seq (.assign "rk" (.lit 0)) (.seq (.assign "lp" (.lit 0)) fLoop)))

/-- **Rank and localization.** Started at the code of `φ` in `U`, the
walk sets `rk` to the rank of `φ`, moves `fp` behind the code, and in
mode `1` fills `lo` with the code of `loc q φ`. -/
theorem fWalk_run {B q : ℕ} {φ : FO 0} {R : List ℕ} {p0 : ℕ} {σ : Env}
    (hfp : σ.vars "fp" = p0) (hU : (σ.arrs "U").drop p0 = fc φ ++ R) (hC : FCtx B q φ p0 σ) :
    ∃ σ', Run B fWalk σ σ' (124 * (fc φ).length + 160) ∧ σ'.vars "rk" = rank φ ∧
      σ'.vars "fp" = p0 + (fc φ).length ∧
      (σ.vars "fm" = 1 → Filled "lo" "lp" (dc (loc q φ)) σ') := by
  have hbnd := hC.bnd
  have hcφ := length_code_pos φ
  have hF0 := Filled.empty "stk" "sp" σ
  obtain ⟨τ₁, r₁, hs₁, hv₁, ha₁, hl₁, -, -⟩ := push1_run (B := B) hF0 (e := .lit 0) (v := 0)
    (evalB_lit (by omega)) (by have := hC.stk; simp; omega) (by simp; omega)
  set τ₃ := (τ₁.setVar "rk" 0).setVar "lp" 0 with hτ₃
  have hC₃ : FCtx B q φ p0 τ₃ := hC.congr (by simp [hτ₃, hl₁]) (by simp [hτ₃, ha₁ "lo" (by decide)])
    (by simp [hτ₃, ha₁ "RP" (by decide)]) (by simp [hτ₃, hv₁ "fm" (by decide)])
  have hI₃ : FInv q φ R p0 [⟨0, φ⟩] τ₃ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := (hs₁.setVar (y := "rk") (by decide) 0).setVar (y := "lp") (by decide) 0
      simpa [pdeps] using this
    · simp [hτ₃, ha₁ "U" (by decide), hv₁ "fp" (by decide), hfp, hU, pcode]
    · simp [hτ₃, hv₁ "fp" (by decide), hfp, pcode]
    · simp [pcode]; omega
    · simp [hτ₃, prank]
    · intro _
      exact ⟨[], ⟨by simp [hτ₃], fun i h => absurd h (by simp)⟩, by simp [ploc]⟩
  obtain ⟨σ', r, hC', hI'⟩ := fLoop_run hC₃ hI₃
  have hfm : σ'.vars "fm" = σ.vars "fm" := by
    rw [r.frame_var "fm" (by decide)]; simp [hτ₃, hv₁ "fm" (by decide)]
  refine ⟨σ', (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq r₁ (Run.seq
    (Run.assign (evalB_lit (by omega))) (Run.seq (Run.assign (evalB_lit (by omega))) r)))).mono
    (by simp; omega), ?_, ?_, ?_⟩
  · have := hI'.rk; simp at this; exact this
  · have := hI'.fp; simpa using this
  · intro hm
    obtain ⟨l, hF, hl⟩ := hI'.lo (by rw [hfm]; exact hm)
    simp at hl; subst hl; exact hF

end Lax185574Proofs.MC.Glue
