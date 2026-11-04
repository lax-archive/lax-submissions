import Lax185574Proofs.Gaifman.NormalFormOps

/-!
Renaming operations for the locally bound variables of local formulas.  Anchor
renaming is intentionally absent: every local quantifier is centred at all of
the original anchors, so an arbitrary anchor map would change its semantics.

Adapted from lax-512892 (faghasemi/gaifman-theorem-lax, commit 7c2b896), file
`proofs/Lax512892Proofs/LocalSyntax.lean`.
-/

namespace Lax185574Proofs.Gaifman.LocalSyntax

open Lax185574Proofs.Gaifman.RelationalStructures Lax185574Proofs.Gaifman.Locality

/-- Lift a map of finite levels under one new last level. -/
def liftFin {m n : ℕ} (f : Fin m → Fin n) : Fin (m + 1) → Fin (n + 1) :=
  Fin.snoc (fun i => (f i).castSucc) (Fin.last n)

@[simp] theorem liftFin_castSucc {m n : ℕ} (f : Fin m → Fin n) (i : Fin m) :
    liftFin f i.castSucc = (f i).castSucc := by
  simp [liftFin]

@[simp] theorem liftFin_last {m n : ℕ} (f : Fin m → Fin n) :
    liftFin f (Fin.last m) = Fin.last n := by
  simp [liftFin]

namespace LocalTerm

/-- Rename locally bound variables, leaving anchors and constants fixed. -/
def renameBound {σ : Vocabulary} {k b b' : ℕ} (f : Fin b → Fin b') :
    Lax185574Proofs.Gaifman.Locality.LocalTerm σ k b →
      Lax185574Proofs.Gaifman.Locality.LocalTerm σ k b'
  | .anchor i => .anchor i
  | .bound i => .bound (f i)
  | .const c => .const c

@[simp] theorem eval_renameBound {σ : Vocabulary} {M : Type*} {k b b' : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (bound : Fin b' → M)
    (f : Fin b → Fin b') (t : Lax185574Proofs.Gaifman.Locality.LocalTerm σ k b) :
    (renameBound f t).eval A anchors bound =
      t.eval A anchors (bound ∘ f) := by
  cases t <;> rfl

/-- Weaken a local term by one new last bound variable. -/
def weakenBound {σ : Vocabulary} {k b : ℕ}
    (t : Lax185574Proofs.Gaifman.Locality.LocalTerm σ k b) :
    Lax185574Proofs.Gaifman.Locality.LocalTerm σ k (b + 1) :=
  renameBound Fin.castSucc t

@[simp] theorem eval_weakenBound {σ : Vocabulary} {M : Type*} {k b : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (bound : Fin b → M)
    (x : M) (t : Lax185574Proofs.Gaifman.Locality.LocalTerm σ k b) :
    (weakenBound t).eval A anchors (Fin.snoc bound x) =
      t.eval A anchors bound := by
  simp [weakenBound, eval_renameBound]

end LocalTerm

namespace LocalFormula

/-- Rename the currently in-scope locally bound variables.  Under a local
quantifier the map is lifted and the newly bound last variable stays last. -/
def renameBound {σ : Vocabulary} {k r b b' : ℕ} (f : Fin b → Fin b') :
    Lax185574Proofs.Gaifman.Locality.LocalFormula σ k r b →
      Lax185574Proofs.Gaifman.Locality.LocalFormula σ k r b'
  | .rel R args => .rel R (fun i => LocalTerm.renameBound f (args i))
  | .eq left right => .eq (LocalTerm.renameBound f left)
      (LocalTerm.renameBound f right)
  | .not φ => .not (renameBound f φ)
  | .or φ ψ => .or (renameBound f φ) (renameBound f ψ)
  | .ex φ => .ex (renameBound (liftFin f) φ)

/-- Renaming locally bound variables commutes with satisfaction. -/
theorem sat_renameBound {σ : Vocabulary} {M : Type*} {k r b b' : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (bound : Fin b' → M)
    (f : Fin b → Fin b')
    (φ : Lax185574Proofs.Gaifman.Locality.LocalFormula σ k r b) :
    (renameBound f φ).Sat A anchors bound ↔
      φ.Sat A anchors (bound ∘ f) := by
  induction φ generalizing b' with
  | rel R args =>
      simp only [renameBound, Lax185574Proofs.Gaifman.Locality.LocalFormula.Sat,
        LocalTerm.eval_renameBound]
  | eq left right =>
      simp only [renameBound, Lax185574Proofs.Gaifman.Locality.LocalFormula.Sat,
        LocalTerm.eval_renameBound]
  | not φ ih =>
      simp only [renameBound, Lax185574Proofs.Gaifman.Locality.LocalFormula.Sat]
      exact not_congr (ih bound f)
  | or φ ψ ihφ ihψ =>
      simp only [renameBound, Lax185574Proofs.Gaifman.Locality.LocalFormula.Sat]
      exact or_congr (ihφ bound f) (ihψ bound f)
  | ex φ ih =>
      simp only [renameBound, Lax185574Proofs.Gaifman.Locality.LocalFormula.Sat]
      apply exists_congr
      intro x
      apply and_congr_right
      intro _
      rw [ih (Fin.snoc bound x) (liftFin f)]
      have henv : Fin.snoc bound x ∘ liftFin f =
          Fin.snoc (bound ∘ f) x := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simp [liftFin]
        · simp [liftFin]
      rw [henv]

/-- Weaken every locally bound variable by one new last variable. -/
def weakenBound {σ : Vocabulary} {k r b : ℕ}
    (φ : Lax185574Proofs.Gaifman.Locality.LocalFormula σ k r b) :
    Lax185574Proofs.Gaifman.Locality.LocalFormula σ k r (b + 1) :=
  renameBound Fin.castSucc φ

@[simp] theorem sat_weakenBound {σ : Vocabulary} {M : Type*} {k r b : ℕ}
    (A : Structure σ M) (anchors : Fin k → M) (bound : Fin b → M)
    (x : M) (φ : Lax185574Proofs.Gaifman.Locality.LocalFormula σ k r b) :
    (weakenBound φ).Sat A anchors (Fin.snoc bound x) ↔
      φ.Sat A anchors bound := by
  rw [weakenBound, sat_renameBound]
  have henv : Fin.snoc bound x ∘ Fin.castSucc = bound := by
    funext i
    simp
  rw [henv]

end LocalFormula

end Lax185574Proofs.Gaifman.LocalSyntax
