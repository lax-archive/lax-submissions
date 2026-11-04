import Lax185574Proofs.MC.Glue.Call0

/-!
Two links for the glue program of thm:mc.

`BigStepB.vals_lt`, `Run.vals_lt`: a bounded run keeps every scalar,
every array entry and every input entry below the bound when they start
so. The arrays of `initEnv` are zero, so the words a round builds in its
arrays have entries below the bound.

`guardOK_of`: the guard that the writer checks on the query `realQ` of
a call, with the exponent `expOf` of its kind, is the guard `GuardOK` of
`GlueAt`.
-/

namespace Lax185574Proofs.MC.Glue

open Lax185574Proofs.MC Lax185574Proofs.Words Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.PartialGraphEncoding Lax185574.TypeTrees Lax185574.ConstructionModelChecking
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-! ### Bounded runs keep values below the bound -/

/-- All scalars, array entries and input entries of `σ` are below `B`. -/
def ValsLt (B : ℕ) (σ : Env) : Prop :=
  (∀ x, σ.vars x < B) ∧ (∀ a, ∀ v ∈ σ.arrs a, v < B) ∧ (∀ v ∈ σ.inp, v < B)

theorem ValsLt.setVar {B : ℕ} {σ : Env} (h : ValsLt B σ) (x : String) {v : ℕ} (hv : v < B) :
    ValsLt B (σ.setVar x v) := by
  refine ⟨fun y => ?_, h.2.1, h.2.2⟩
  simp only [vars_setVar]; split_ifs
  · exact hv
  · exact h.1 y

theorem ValsLt.setArr {B : ℕ} {σ : Env} (h : ValsLt B σ) (a : String) (k : ℕ) {v : ℕ}
    (hv : v < B) : ValsLt B (σ.setArr a k v) := by
  refine ⟨h.1, fun b u hu => ?_, h.2.2⟩
  simp only [arrs_setArr] at hu
  split_ifs at hu with hb
  · rcases List.mem_or_eq_of_mem_set hu with h' | h'
    · exact h.2.1 a u h'
    · rw [h']; exact hv
  · exact h.2.1 b u hu

theorem BigStepB.vals_lt {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ} (h : BigStepB B c σ σ' k) :
    ValsLt B σ → ValsLt B σ' := by
  induction h with
  | skip => exact id
  | assign he => exact fun hv => hv.setVar _ (Expr.eval_and_lt_of_evalB he).2
  | store _ he _ => exact fun hv => hv.setArr _ _ (Expr.eval_and_lt_of_evalB he).2
  | seq _ _ ih ih' => exact fun hv => ih' (ih hv)
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => exact fun hv => ih' (ih hv)
  | while_false _ => exact id
  | @read σ x v rest hi =>
    intro hv
    have hvB : v < B := hv.2.2 v (by rw [hi]; simp)
    refine ⟨fun y => ?_, hv.2.1, fun u hu => hv.2.2 u (by rw [hi]; exact List.mem_cons_of_mem _ hu)⟩
    show (σ.setVar x v).vars y < B
    simp only [vars_setVar]; split_ifs
    · exact hvB
    · exact hv.1 y
  | write _ => exact fun hv => hv

theorem Run.vals_lt {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K)
    (hv : ValsLt B σ) : ValsLt B σ' := by
  obtain ⟨k, -, hb⟩ := h
  exact BigStepB.vals_lt hb hv

theorem valsLt_init {B W : ℕ} (ext : String → ℕ) (x : List ℕ) (hW : W < B) (hx : ∀ v ∈ x, v < B) :
    ValsLt B ((initEnv ext x).setVar "W" W) := by
  refine ValsLt.setVar ⟨fun _ => ?_, fun a v hv => ?_, hx⟩ _ hW
  · show 0 < B; omega
  · simp only [initEnv, List.mem_replicate] at hv; omega

/-- The entries of a filled word are below the bound. -/
theorem Filled.lt_of_vals {B : ℕ} {a pv : String} {l : List ℕ} {τ : Env} (h : Filled a pv l τ)
    (hv : ValsLt B τ) : ∀ v ∈ l, v < B := by
  intro v hvl
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hvl
  exact hv.2.1 a _ (List.mem_of_getElem? (h.get i hi))

/-! ### The guard of a call -/

/-- The query of the callee that does the work in a call. -/
noncomputable def workQ {n : ℕ} (s : List (PartialGraph (Fin n))) (q : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    PCall n → List ℕ
  | c@(.merge ..) => callQM s q c
  | c@(.resolve ..) => callQR s q c
  | c@(.eval _) => callQE s q φ c

/-- The query of the working callee, by the kind of the call. -/
theorem realQ_call {n : ℕ} (s : List (PartialGraph (Fin n))) (q m : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (c : PCall n) :
    realQ (ckOf c) (cPOf c) (cQOf c) (csOf c) (gwOf s m c) (fwOf s q m c) (trOf s q c)
      (Lax185574.DistanceLogic.DistFO.code (loc q φ)) = workQ s q φ c := by
  cases c with
  | merge t P Q =>
    by_cases hPQ : P = Q
    · simp [realQ, ckOf, hPQ, callQM, workQ]
    · simp [realQ, ckOf, hPQ, callQM, workQ, trOf, toWord_mjobs]
  | resolve t sg P Q =>
    simp [realQ, ckOf, callQR, cPOf, cQOf, csOf, gwOf, fwOf, ctOf, workQ, List.append_assoc]
    simp only [Lax185574Proofs.Legacy.toWord_prod, Lax185574Proofs.Legacy.toWord_nat,
      Lax185574Proofs.Legacy.toWord_bool]
    rfl
  | eval a =>
    simp [realQ, ckOf, callQE, workQ, trOf]
    simp only [Lax185574Proofs.Legacy.toWord_prod, Lax185574Proofs.Legacy.toWord_distFO]

/-- **The guard of a call.** The guard on `realQ` with the exponent of
the kind of the call is `GuardOK`. -/
theorem guardOK_of {n : ℕ} {s : List (PartialGraph (Fin n))} {q m : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {eM eR eE v sQ : ℕ} (c : PCall n)
    (h : ((realQ (ckOf c) (cPOf c) (cQOf c) (csOf c) (gwOf s m c) (fwOf s q m c) (trOf s q c)
      (Lax185574.DistanceLogic.DistFO.code (loc q φ))).length +
      maxEntry (realQ (ckOf c) (cPOf c) (cQOf c) (csOf c) (gwOf s m c) (fwOf s q m c) (trOf s q c)
      (Lax185574.DistanceLogic.DistFO.code (loc q φ))) + 1) ^ (expOf eM eR eE (ckOf c) + 1) ≤
        2 ^ (v - sQ)) :
    GuardOK s q φ eM eR eE v sQ c := by
  rw [realQ_call s q m φ c] at h
  cases c with
  | merge t P Q =>
    have he : expOf eM eR eE (ckOf (PCall.merge (n := n) t P Q)) = eM := by
      simp only [expOf, ckOf]; split_ifs <;> simp_all
    rw [he] at h; exact h
  | resolve t sg P Q => simp only [GuardOK]; simpa [expOf, ckOf, workQ] using h
  | eval a => simp only [GuardOK]; simpa [expOf, ckOf, workQ] using h

end Lax185574Proofs.MC.Glue
