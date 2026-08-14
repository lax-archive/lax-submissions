import Lax3Proofs.Refine.OrderVirtualElimScan

/-!
# Row providers for the linear-space ordering engine

An augmented graph is not resident in memory.  The ordering engine asks a
provider to regenerate the row of the vertex in `w` into `vrow`, and then
consumes that row immediately.  This file fixes the executable contract at
that boundary.  In particular, a provider may use arbitrary private scratch,
but it must preserve the seven elimination arrays and the loop/bucket
scalars.  Its per-row charge is a function `κ`; later loops pay the sum of
those charges, rather than multiplying a worst row by the carrier.
-/

namespace Lax3Proofs.Refine.OrderVirtualProvider

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.Refine.OrderVirtualRowRep

/-- The resident part of one virtual elimination.  Every array here has
carrier-linear length; the bucket arena has the caller-selected linear extra
width `W`. -/
structure EngineArrays (n W : ℕ) (E D R ID BH BV BN : ℕ → ℕ)
    (σ : Env) : Prop where
  n_eq : σ.vars "n" = n
  elm_eq : σ.arrs "elm" = arrOf n E
  deg_eq : σ.arrs "deg" = arrOf n D
  rank_eq : σ.arrs "rnk" = arrOf n R
  idg_eq : σ.arrs "idg" = arrOf n ID
  head_eq : σ.arrs "bh" = arrOf (n + 1) BH
  val_eq : σ.arrs "bv" = arrOf (n + W + 1) BV
  next_eq : σ.arrs "bn" = arrOf (n + W + 1) BN

namespace EngineArrays

theorem deg_length {n W : ℕ} {E D R ID BH BV BN : ℕ → ℕ} {σ : Env}
    (h : EngineArrays n W E D R ID BH BV BN σ) :
    (σ.arrs "deg").length = n := by
  rw [h.deg_eq, length_arrOf]

/-- Scalar writes do not affect the resident elimination arrays. -/
theorem setVar {n W : ℕ} {E D R ID BH BV BN : ℕ → ℕ} {σ : Env}
    (h : EngineArrays n W E D R ID BH BV BN σ) (a : String) (x : ℕ)
    (ha : a ≠ "n") :
    EngineArrays n W E D R ID BH BV BN (σ.setVar a x) := by
  exact ⟨by rw [vars_setVar, if_neg (Ne.symm ha)]; exact h.n_eq,
    by simpa using h.elm_eq, by simpa using h.deg_eq,
    by simpa using h.rank_eq, by simpa using h.idg_eq,
    by simpa using h.head_eq, by simpa using h.val_eq,
    by simpa using h.next_eq⟩

/-- An array write outside the seven resident elimination arrays preserves
their exact representations.  The shared row buffer `vrow` is intentionally
allowed here: it is engine-owned syntactically but is not part of
`EngineArrays`. -/
theorem setArr_of_private {n W : ℕ} {E D R ID BH BV BN : ℕ → ℕ} {σ : Env}
    (h : EngineArrays n W E D R ID BH BV BN σ) {a : String}
    (helm : a ≠ "elm") (hdeg : a ≠ "deg") (hrnk : a ≠ "rnk")
    (hidg : a ≠ "idg") (hbh : a ≠ "bh") (hbv : a ≠ "bv")
    (hbn : a ≠ "bn") (p x : ℕ) :
    EngineArrays n W E D R ID BH BV BN (σ.setArr a p x) := by
  exact ⟨by simpa using h.n_eq,
    by rw [arrs_setArr, if_neg (Ne.symm helm)]; exact h.elm_eq,
    by rw [arrs_setArr, if_neg (Ne.symm hdeg)]; exact h.deg_eq,
    by rw [arrs_setArr, if_neg (Ne.symm hrnk)]; exact h.rank_eq,
    by rw [arrs_setArr, if_neg (Ne.symm hidg)]; exact h.idg_eq,
    by rw [arrs_setArr, if_neg (Ne.symm hbh)]; exact h.head_eq,
    by rw [arrs_setArr, if_neg (Ne.symm hbv)]; exact h.val_eq,
    by rw [arrs_setArr, if_neg (Ne.symm hbn)]; exact h.next_eq⟩

end EngineArrays

/-- Scalars whose meaning belongs to the elimination engine rather than to a
row provider. -/
structure ProviderStable (σ σ' : Env) : Prop where
  n_eq : σ'.vars "n" = σ.vars "n"
  w_eq : σ'.vars "w" = σ.vars "w"
  i_eq : σ'.vars "i" = σ.vars "i"
  sp_eq : σ'.vars "sp" = σ.vars "sp"
  ls_eq : σ'.vars "ls" = σ.vars "ls"
  cnt_eq : σ'.vars "cnt" = σ.vars "cnt"
  mind_eq : σ'.vars "mind" = σ.vars "mind"
  kmax_eq : σ'.vars "kmax" = σ.vars "kmax"

namespace ProviderStable

theorem refl (σ : Env) : ProviderStable σ σ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem trans {σ₀ σ₁ σ₂ : Env}
    (h₀₁ : ProviderStable σ₀ σ₁) (h₁₂ : ProviderStable σ₁ σ₂) :
    ProviderStable σ₀ σ₂ :=
  ⟨h₁₂.n_eq.trans h₀₁.n_eq, h₁₂.w_eq.trans h₀₁.w_eq,
    h₁₂.i_eq.trans h₀₁.i_eq, h₁₂.sp_eq.trans h₀₁.sp_eq,
    h₁₂.ls_eq.trans h₀₁.ls_eq, h₁₂.cnt_eq.trans h₀₁.cnt_eq,
    h₁₂.mind_eq.trans h₀₁.mind_eq, h₁₂.kmax_eq.trans h₀₁.kmax_eq⟩

/-- Array writes preserve every scalar in the provider-stability surface. -/
theorem setArr {σ₀ σ : Env} (h : ProviderStable σ₀ σ)
    (a : String) (p x : ℕ) : ProviderStable σ₀ (σ.setArr a p x) := by
  exact ⟨by simpa using h.n_eq, by simpa using h.w_eq,
    by simpa using h.i_eq, by simpa using h.sp_eq,
    by simpa using h.ls_eq, by simpa using h.cnt_eq,
    by simpa using h.mind_eq, by simpa using h.kmax_eq⟩

theorem i_eq_after_w {σ σ' : Env} {v : ℕ}
    (h : ProviderStable (σ.setVar "w" v) σ') :
    σ'.vars "i" = σ.vars "i" := by
  simpa using h.i_eq

end ProviderStable

/-- Names mutated by the generic elimination engine. -/
def engineVarNames : List String :=
  ["w", "i", "j", "u", "d", "p", "sp", "ls", "cnt", "mind", "kmax"]

/-- Arrays mutated by the generic elimination engine.  `vrow` is included
because a concrete provider and the consumer share that buffer. -/
def engineArrNames : List String :=
  ["vrow", "elm", "deg", "rnk", "idg", "bh", "bv", "bn"]

/-- A persistent provider predicate ignores every cell owned by the generic
engine.  Concrete providers discharge this from their disjoint input/rank
array names. -/
structure EngineClosed (P : Env → Prop) : Prop where
  setVar : ∀ {σ : Env} {a : String} {v : ℕ}, a ∈ engineVarNames →
    P σ → P (σ.setVar a v)
  setArr : ∀ {σ : Env} {a : String} {i v : ℕ}, a ∈ engineArrNames →
    P σ → P (σ.setArr a i v)

/-- Closure under a whole verified engine run.  This is the convenient form
for existing loop specifications such as bucket reconstruction; concrete
persistent memories prove it from the run's `frame_var`/`frame_arr` facts. -/
def EngineRunClosed (P : Env → Prop) : Prop :=
  ∀ {B K : ℕ} {c : Com} {σ σ' : Env},
    Run B c σ σ' K →
    (∀ a ∈ c.wvars, a ∈ engineVarNames) →
    (∀ a ∈ c.warrs, a ∈ engineArrNames) →
    P σ → P σ'

/-- `ProvidesRows` is the reusable executable interface.  `P` describes the
provider's persistent input (the compact input graph and earlier rank arrays).
It is deliberately separate from the engine arrays, which change during an
elimination. -/
def ProvidesRows (B n W : ℕ) (G : SimpleGraph (Fin n))
    (P : Env → Prop) (provide : Com) (κ : ℕ → ℕ) : Prop :=
  ∀ (w : Fin n) (E D R ID BH BV BN : ℕ → ℕ),
    Spec B
      (fun σ => P σ ∧ EngineArrays n W E D R ID BH BV BN σ ∧
        σ.vars "w" = (w : ℕ))
      provide
      (fun σ σ' => P σ' ∧ EngineArrays n W E D R ID BH BV BN σ' ∧
        ProviderStable σ σ' ∧
        ∃ tail A, RowRep G w tail A ∧
          σ'.vars "vtail" = tail ∧ σ'.arrs "vrow" = arrOf n A)
      (κ (w : ℕ))

/-- Running a provider exposes an exact carrier-sized row while retaining the
persistent state and engine frame. -/
theorem exists_provided_row {B n W : ℕ} {G : SimpleGraph (Fin n)}
    {P : Env → Prop} {provide : Com} {κ : ℕ → ℕ}
    (hp : ProvidesRows B n W G P provide κ) {w : Fin n}
    {E D R ID BH BV BN : ℕ → ℕ} {σ : Env}
    (hpre : P σ ∧ EngineArrays n W E D R ID BH BV BN σ ∧
      σ.vars "w" = (w : ℕ)) :
    ∃ σ' tail A,
      Run B provide σ σ' (κ (w : ℕ)) ∧ P σ' ∧
      EngineArrays n W E D R ID BH BV BN σ' ∧ ProviderStable σ σ' ∧
      RowRep G w tail A ∧ tail ≤ n ∧
      σ'.vars "vtail" = tail ∧ σ'.arrs "vrow" = arrOf n A := by
  obtain ⟨σ', hrun, hP, heng, hstable, tail, A, hrow, htail, hA⟩ :=
    (hp w E D R ID BH BV BN).run hpre
  exact ⟨σ', tail, A, hrun, hP, heng, hstable, hrow, hrow.tail_le, htail, hA⟩

end Lax3Proofs.Refine.OrderVirtualProvider
