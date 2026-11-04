import Lax185574Proofs.StpRam.Glue

/-!
The layout of the glue program of lem:compute-stp, and the check that
the compiler accepts the program.

`Com.okB` is a boolean version of `Com.Ok`, so that the check is a
computation.
-/

namespace Lax185574Proofs.StpRam

open Lax808846Proofs.Imp Lax808846Proofs.Compile

/-- The boolean version of `Expr.Ok`. -/
def exprOkB (L : Layout) : Expr → ℕ → Bool
  | .lit _, _ => true
  | .var x, _ => decide (x ∈ L.scalars)
  | .get a i, d => decide (a ∈ L.arrays) && exprOkB L i d && decide (d < L.temps)
  | .bin _ e f, d => exprOkB L f d && exprOkB L e (d + 1) && decide (d < L.temps)

theorem exprOkB_sound (L : Layout) : ∀ (e : Expr) (d : ℕ), exprOkB L e d = true → Expr.Ok L e d
  | .lit _, _, _ => trivial
  | .var x, _, h => by simpa [exprOkB, Expr.Ok] using h
  | .get a i, d, h => by
    simp only [exprOkB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, exprOkB_sound L i d h.1.2, h.2⟩
  | .bin _ e f, d, h => by
    simp only [exprOkB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨exprOkB_sound L f d h.1.1, exprOkB_sound L e (d + 1) h.1.2, h.2⟩

/-- The boolean version of `Com.Ok`. -/
def comOkB (L : Layout) : Com → Bool
  | .skip => true
  | .assign x e => decide (x ∈ L.scalars) && exprOkB L e 0
  | .store a i e => decide (a ∈ L.arrays) && exprOkB L i 0 && exprOkB L e 1 && decide (0 < L.temps)
  | .seq c d => comOkB L c && comOkB L d
  | .ite b c d => exprOkB L (condExpr b) 0 && comOkB L c && comOkB L d
  | .while b c => exprOkB L (condExpr b) 0 && comOkB L c
  | .read x => decide (x ∈ L.scalars)
  | .write e => exprOkB L e 0 && decide (0 < L.temps)

theorem comOkB_sound (L : Layout) : ∀ c : Com, comOkB L c = true → Com.Ok L c
  | .skip, _ => trivial
  | .assign x e, h => by
    simp only [comOkB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1, exprOkB_sound L e 0 h.2⟩
  | .store a i e, h => by
    simp only [comOkB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1.1, exprOkB_sound L i 0 h.1.1.2, exprOkB_sound L e 1 h.1.2, h.2⟩
  | .seq c d, h => by
    simp only [comOkB, Bool.and_eq_true] at h
    exact ⟨comOkB_sound L c h.1, comOkB_sound L d h.2⟩
  | .ite b c d, h => by
    simp only [comOkB, Bool.and_eq_true] at h
    exact ⟨exprOkB_sound L _ 0 h.1.1, comOkB_sound L c h.1.2, comOkB_sound L d h.2⟩
  | .while b c, h => by
    simp only [comOkB, Bool.and_eq_true] at h
    exact ⟨exprOkB_sound L _ 0 h.1, comOkB_sound L c h.2⟩
  | .read x, h => by simpa [comOkB, Com.Ok] using h
  | .write e, h => by
    simp only [comOkB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨exprOkB_sound L e 0 h.1, h.2⟩

/-- The scalars and arrays of the glue program. -/
def layout : Layout :=
  ⟨["tg", "sl", "cn", "ci2", "cx", "cp", "cv", "cd", "ck", "cy", "kk", "qq", "xp", "fn", "ti", "p0",
    "hk", "hq", "hl", "e1", "e2", "vv", "e3", "ev", "pa", "otg", "owin", "ws0", "wc", "i", "y", "fl2",
    "h0", "hn", "hk2", "hq2", "hj", "hg", "jn", "hc", "fc", "fi", "fl", "m", "p", "n", "j", "v", "ri",
    "re", "rp", "rj", "cap", "R1", "hp", "cnt", "fnd", "s", "ok", "ci", "cj", "pb", "la", "lb", "k", "c",
    "best", "prev", "tot", "er", "gr", "es", "gu", "gi", "b", "gc", "gv", "bu", "br", "bs", "bw", "bj",
    "be", "bv", "ep", "el", "ek", "dz", "du", "dv"],
    ["eo", "et", "no", "nt", "x", "st", "ln", "a", "rt", "ord", "bl", "dn", "dd"], 6⟩

theorem glue_okB : comOkB layout glue = true := by decide

theorem glue_ok : Com.Ok layout glue := comOkB_sound layout glue glue_okB

end Lax185574Proofs.StpRam
