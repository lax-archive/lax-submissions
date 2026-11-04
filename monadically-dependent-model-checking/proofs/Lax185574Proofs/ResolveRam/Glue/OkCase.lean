import Lax185574Proofs.ResolveRam.Glue.OkTop
import Lax185574Proofs.ResolveRam.Glue.CR1
import Lax185574Proofs.ResolveRam.Glue.CFinL
import Lax185574Proofs.ResolveRam.Glue.CShift
import Lax185574Proofs.ResolveRam.Glue.CComp
import Lax185574Proofs.ResolveRam.Glue.CFtree
import Lax185574Proofs.ResolveRam.Glue.CUpA
import Lax185574Proofs.ResolveRam.Glue.CFE

/-!
The cases of a later round of the glue program of lem:resolve-lift, and
the end of the last round, compile in `glueLay`, with the piece of the
atom words `atCmd`. The cases have no parameters, so the check is a
computation. `glue_ok_of`: the glue program compiles around every body
that compiles.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax185574Proofs.Words

set_option maxRecDepth 100000 in
theorem bR1_okG : Com.Ok glueLay (bR1 atCmd) := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem bShift_okG : Com.Ok glueLay bShift := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem fE_okG : Com.Ok glueLay (fE atCmd) := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem bFt_okG : Com.Ok glueLay (bFt (fE atCmd)) := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem bComp_okG : Com.Ok glueLay bComp := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem bLast_okG : Com.Ok glueLay (bLast atCmd) := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem bUpA_okG : Com.Ok glueLay bUpA := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem fECmd_okG : Com.Ok glueLay fECmd := StpRam.comOkB_sound _ _ (by decide)

/-- **The glue program compiles** around every body of a later round that compiles. -/
theorem glue_ok_of {body : Com} (hb : Com.Ok glueLay body) (K eT d eS eF eC eK dS dF dC dK : ℕ) :
    Com.Ok glueLay (glueTop K eT d (roundJ body fECmd eS eF eC eK dS dF dC dK)) :=
  glueTop_okG (roundJ_okG hb fECmd_okG eS eF eC eK dS dF dC dK) K eT d

end Lax185574Proofs.ResolveRam.Glue
