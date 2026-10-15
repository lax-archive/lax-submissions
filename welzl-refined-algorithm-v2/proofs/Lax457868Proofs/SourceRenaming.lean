import Lax457868Proofs.ReusedOriginal.Construction.WelzlProgram

/-! Alpha-renaming transport for the fixed IMP+ source language. -/

namespace Lax457868Proofs.SourceRenaming

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- A simultaneous bijective renaming of scalar and array identifiers. -/
structure Names where
  scalar : Equiv.Perm String
  array : Equiv.Perm String

def Names.identity : Names := ⟨Equiv.refl String, Equiv.refl String⟩

def renameExpr (ρ : Names) : Expr → Expr
  | .lit n => .lit n
  | .var x => .var (ρ.scalar x)
  | .get a i => .get (ρ.array a) (renameExpr ρ i)
  | .bin op e f => .bin op (renameExpr ρ e) (renameExpr ρ f)

def renameCond (ρ : Names) : Cond → Cond
  | .eq e f => .eq (renameExpr ρ e) (renameExpr ρ f)
  | .lt e f => .lt (renameExpr ρ e) (renameExpr ρ f)

def renameCom (ρ : Names) : Com → Com
  | .skip => .skip
  | .assign x e => .assign (ρ.scalar x) (renameExpr ρ e)
  | .store a i e => .store (ρ.array a) (renameExpr ρ i) (renameExpr ρ e)
  | .seq c d => .seq (renameCom ρ c) (renameCom ρ d)
  | .ite b c d => .ite (renameCond ρ b) (renameCom ρ c) (renameCom ρ d)
  | .while b c => .while (renameCond ρ b) (renameCom ρ c)
  | .read x => .read (ρ.scalar x)
  | .write e => .write (renameExpr ρ e)

/-- Rename the keys of an environment, leaving tapes unchanged. -/
def renameEnv (ρ : Names) (σ : Env) : Env :=
  { vars := fun x => σ.vars (ρ.scalar.symm x)
    arrs := fun a => σ.arrs (ρ.array.symm a)
    inp := σ.inp
    out := σ.out }

@[simp] lemma renameExpr_identity (e : Expr) :
    renameExpr Names.identity e = e := by
  induction e with
  | lit => rfl
  | var => simp [Names.identity, renameExpr]
  | get a i ih =>
      change Expr.get a (renameExpr Names.identity i) = Expr.get a i
      exact congrArg (Expr.get a) ih
  | bin op e f ih₁ ih₂ =>
      change Expr.bin op (renameExpr Names.identity e) (renameExpr Names.identity f) = _
      rw [ih₁, ih₂]

@[simp] lemma renameCond_identity (b : Cond) :
    renameCond Names.identity b = b := by
  cases b with
  | eq e f =>
      change Cond.eq (renameExpr Names.identity e) (renameExpr Names.identity f) = _
      rw [renameExpr_identity, renameExpr_identity]
  | lt e f =>
      change Cond.lt (renameExpr Names.identity e) (renameExpr Names.identity f) = _
      rw [renameExpr_identity, renameExpr_identity]

@[simp] lemma renameCom_identity (c : Com) :
    renameCom Names.identity c = c := by
  induction c with
  | skip => rfl
  | assign x e =>
      change Com.assign x (renameExpr Names.identity e) = Com.assign x e
      rw [renameExpr_identity]
  | store a i e =>
      change Com.store a (renameExpr Names.identity i) (renameExpr Names.identity e) = _
      rw [renameExpr_identity, renameExpr_identity]
  | seq c d ihc ihd =>
      change Com.seq (renameCom Names.identity c) (renameCom Names.identity d) = _
      rw [ihc, ihd]
  | ite b c d ihc ihd =>
      change Com.ite (renameCond Names.identity b) (renameCom Names.identity c)
        (renameCom Names.identity d) = _
      rw [renameCond_identity, ihc, ihd]
  | «while» b c ih =>
      change Com.while (renameCond Names.identity b) (renameCom Names.identity c) = _
      rw [renameCond_identity, ih]
  | read x => rfl
  | write e =>
      change Com.write (renameExpr Names.identity e) = _
      rw [renameExpr_identity]

@[simp] lemma renameEnv_identity (σ : Env) :
    renameEnv Names.identity σ = σ := by
  cases σ <;> rfl

def Names.inverse (ρ : Names) : Names :=
  ⟨ρ.scalar.symm, ρ.array.symm⟩

@[simp] lemma renameEnv_inverse_left (ρ : Names) (σ : Env) :
    renameEnv ρ (renameEnv ρ.inverse σ) = σ := by
  cases ρ with
  | mk scalar array =>
    cases σ with
    | mk vars arrs inp out =>
      change Env.mk (fun x => vars (scalar (scalar.symm x)))
          (fun a => arrs (array (array.symm a))) inp out = Env.mk vars arrs inp out
      congr 1 <;> funext x <;> simp [Equiv.apply_symm_apply]

@[simp] lemma renameEnv_inverse_right (ρ : Names) (σ : Env) :
    renameEnv ρ.inverse (renameEnv ρ σ) = σ := by
  cases ρ with
  | mk scalar array =>
    cases σ with
    | mk vars arrs inp out =>
      change Env.mk (fun x => vars (scalar.symm (scalar x)))
          (fun a => arrs (array.symm (array a))) inp out = Env.mk vars arrs inp out
      congr 1 <;> funext x <;> simp [Equiv.symm_apply_apply]

@[simp] lemma renameEnv_vars (ρ : Names) (σ : Env) (x : String) :
    (renameEnv ρ σ).vars (ρ.scalar x) = σ.vars x := by
  simp [renameEnv]

@[simp] lemma renameEnv_arrs (ρ : Names) (σ : Env) (a : String) :
    (renameEnv ρ σ).arrs (ρ.array a) = σ.arrs a := by
  simp [renameEnv]

@[simp] lemma renameEnv_setVar (ρ : Names) (σ : Env) (x : String) (v : ℕ) :
    renameEnv ρ (σ.setVar x v) = (renameEnv ρ σ).setVar (ρ.scalar x) v := by
  cases ρ with
  | mk scalar array =>
    cases σ with
    | mk vars arrs inp out =>
      change Env.mk (fun y => if scalar.symm y = x then v else vars (scalar.symm y))
          (fun y => arrs (array.symm y)) inp out =
        Env.mk (fun y => if y = scalar x then v else vars (scalar.symm y))
          (fun y => arrs (array.symm y)) inp out
      congr 1
      funext y
      by_cases h : scalar.symm y = x
      · have hy : y = scalar x := by simpa using congrArg scalar h
        simp [h, hy]
      · have hy : y ≠ scalar x := by
          intro hy
          apply h
          rw [hy]
          exact scalar.symm_apply_apply x
        simp [h, hy]

@[simp] lemma renameEnv_setArr (ρ : Names) (σ : Env) (a : String) (i v : ℕ) :
    renameEnv ρ (σ.setArr a i v) = (renameEnv ρ σ).setArr (ρ.array a) i v := by
  cases ρ with
  | mk scalar array =>
    cases σ with
    | mk vars arrs inp out =>
      change Env.mk (fun y => vars (scalar.symm y))
          (fun y => if array.symm y = a then (arrs a).set i v else arrs (array.symm y)) inp out =
        Env.mk (fun y => vars (scalar.symm y))
          (fun y => if y = array a then (arrs (array.symm (array a))).set i v else arrs (array.symm y)) inp out
      congr 1
      funext y
      by_cases h : array.symm y = a
      · have hy : y = array a := by simpa using congrArg array h
        simp [h, hy]
      · have hy : y ≠ array a := by
          intro hy
          apply h
          rw [hy]
          exact array.symm_apply_apply a
        simp [h, hy]

@[simp] lemma renameEnv_readResult (ρ : Names) (σ : Env) (x : String)
    (v : ℕ) (rest : List ℕ) :
    renameEnv ρ { σ.setVar x v with inp := rest } =
      { (renameEnv ρ σ).setVar (ρ.scalar x) v with inp := rest } := by
  calc
    renameEnv ρ { σ.setVar x v with inp := rest } =
        { renameEnv ρ (σ.setVar x v) with inp := rest } := by cases σ <;> rfl
    _ = { (renameEnv ρ σ).setVar (ρ.scalar x) v with inp := rest } := by
      rw [renameEnv_setVar]

@[simp] lemma renameEnv_writeResult (ρ : Names) (σ : Env) (v : ℕ) :
    renameEnv ρ { σ with out := σ.out ++ [v] } =
      { renameEnv ρ σ with out := σ.out ++ [v] } := by
  cases σ <;> rfl

@[simp] lemma renameExpr_size (ρ : Names) (e : Expr) :
    (renameExpr ρ e).size = e.size := by
  induction e with
  | lit => rfl
  | var => rfl
  | get a i ih => simp [renameExpr, ih]
  | bin op e f ih₁ ih₂ => simp [renameExpr, ih₁, ih₂]

@[simp] lemma renameCond_size (ρ : Names) (b : Cond) :
    (renameCond ρ b).size = b.size := by
  cases b <;> simp [renameCond]

lemma evalB_renameExpr (ρ : Names) (B : ℕ) (e : Expr) (σ : Env) :
    (renameExpr ρ e).evalB B (renameEnv ρ σ) = e.evalB B σ := by
  induction e with
  | lit n => rfl
  | var x => simp [Expr.evalB, renameExpr, renameEnv, Equiv.symm_apply_apply]
  | get a i ih => simp only [renameExpr, Expr.evalB, ih, renameEnv_arrs]
  | bin op e f ih₁ ih₂ =>
      simp [Expr.evalB, renameExpr, ih₁, ih₂]

lemma evalB_renameCond (ρ : Names) (B : ℕ) (b : Cond) (σ : Env) :
    (renameCond ρ b).evalB B (renameEnv ρ σ) = b.evalB B σ := by
  cases b <;> simp [Cond.evalB, renameCond, evalB_renameExpr]

lemma BigStepB.rename {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ}
    (ρ : Names) (h : BigStepB B c σ σ' k) :
    BigStepB B (renameCom ρ c) (renameEnv ρ σ) (renameEnv ρ σ') k := by
  induction h with
  | skip => exact .skip
  | @assign σ x e v he =>
      simpa [renameCom, renameExpr_size, renameEnv_setVar] using
        (BigStepB.assign (x := ρ.scalar x) (e := renameExpr ρ e)
          ((evalB_renameExpr ρ B e σ).trans he))
  | @store σ a i e k v hi he hk =>
      have hi' : (renameExpr ρ i).evalB B (renameEnv ρ σ) = some k :=
        (evalB_renameExpr ρ B i σ).trans hi
      have he' : (renameExpr ρ e).evalB B (renameEnv ρ σ) = some v :=
        (evalB_renameExpr ρ B e σ).trans he
      have hk' : k < ((renameEnv ρ σ).arrs (ρ.array a)).length := by
        simpa using hk
      simpa [renameCom, renameExpr, renameExpr_size, renameEnv_setArr] using
        (BigStepB.store hi' he' hk')
  | @seq c d σ σ' σ'' k k' hc hd ihc ihd =>
      simpa [renameCom] using BigStepB.seq ihc ihd
  | @ite_true b c d σ σ' k hb hc ih =>
      have hb' : (renameCond ρ b).evalB B (renameEnv ρ σ) = some true :=
        (evalB_renameCond ρ B b σ).symm ▸ hb
      simpa only [renameCom, renameCond_size] using BigStepB.ite_true hb' ih
  | @ite_false b c d σ σ' k hb hd ih =>
      have hb' : (renameCond ρ b).evalB B (renameEnv ρ σ) = some false :=
        (evalB_renameCond ρ B b σ).symm ▸ hb
      simpa only [renameCom, renameCond_size] using BigStepB.ite_false hb' ih
  | @while_true b c σ σ' σ'' k k' hb hc hw ihc ihw =>
      have hb' : (renameCond ρ b).evalB B (renameEnv ρ σ) = some true :=
        (evalB_renameCond ρ B b σ).symm ▸ hb
      simpa only [renameCom, renameCond_size] using BigStepB.while_true hb' ihc ihw
  | @while_false b c σ hb =>
      have hb' : (renameCond ρ b).evalB B (renameEnv ρ σ) = some false :=
        (evalB_renameCond ρ B b σ).symm ▸ hb
      simpa only [renameCom, renameCond_size] using BigStepB.while_false hb'
  | @read σ x v rest h =>
      have h' : (renameEnv ρ σ).inp = v :: rest := by simpa [renameEnv] using h
      simpa only [renameCom, renameEnv_readResult] using
        (BigStepB.read (B := B) (x := ρ.scalar x) (v := v) (rest := rest) h')
  | @write σ e v he =>
      simpa [renameCom, renameExpr_size, renameEnv] using
        (BigStepB.write (e := renameExpr ρ e) ((evalB_renameExpr ρ B e σ).trans he))

/-- Renaming a fixed source program preserves its exact cost bound. -/
lemma run_rename {B K : ℕ} {c : Com} {σ σ' : Env} (ρ : Names)
    (h : Run B c σ σ' K) :
    Run B (renameCom ρ c) (renameEnv ρ σ) (renameEnv ρ σ') K := by
  obtain ⟨k, hk, hrun⟩ := h
  exact ⟨k, hk, BigStepB.rename ρ hrun⟩

end Lax457868Proofs.SourceRenaming
