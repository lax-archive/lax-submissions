import Lax185574Proofs.ResolveRam.Glue.OkCase
import Lax185574Proofs.ResolveRam.Glue.DispDef

/-!
The dispatcher of a later round of the glue program of lem:resolve-lift
compiles in `glueLay`, and so does the whole glue program (`glue_ok`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax185574Proofs.Words

set_option maxRecDepth 100000 in
theorem bUpB_okG : Com.Ok glueLay (bUpB atCmd) := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem dUpE_okG : Com.Ok glueLay (dUpE atCmd) := by
  simp +decide only [dUpE, asgs, Com.Ok, Cond.Ok, condExpr, Expr.Ok, eLL, bUpB_okG, and_true]

set_option maxRecDepth 100000 in
theorem disp_okG : Com.Ok glueLay (disp atCmd (bR1 atCmd)) := by
  simp +decide only [disp, Com.Ok, Cond.Ok, condExpr, Expr.Ok, bR1_okG, bShift_okG, bFt_okG, bComp_okG,
    bLast_okG, bUpA_okG, dUpE_okG, and_true]

/-- **The glue program of lem:resolve-lift compiles** in `glueLay`. -/
theorem glue_ok (K eT d eS eF eC eK dS dF dC dK : ℕ) :
    Com.Ok glueLay (glueTop K eT d (roundJ (disp atCmd (bR1 atCmd)) fECmd eS eF eC eK dS dF dC dK)) :=
  glue_ok_of disp_okG K eT d eS eF eC eK dS dF dC dK

end Lax185574Proofs.ResolveRam.Glue
