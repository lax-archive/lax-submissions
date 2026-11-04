import Lax185574Proofs.ResolveRam.Glue.OkLay
import Lax185574Proofs.ResolveRam.Glue.Top0
import Lax185574Proofs.ResolveRam.Glue.RoundJ
import Lax185574Proofs.ResolveRam.Glue.TailRun
import Lax185574Proofs.StpRam.GlueOk

/-!
The frame of the glue program of lem:resolve-lift compiles in `glueLay`.

The commands without parameters are checked by computation
(`StpRam.comOkB_sound`). The commands that depend on a number or on a
list that is not given by its entries (`satLit`, `pushLits`, and the
commands around them) are checked by unfolding them down to those
pieces. `glueTop_okG` and `roundJ_okG` take the check of the parts they
run as hypotheses.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue

theorem satLit_okG {z : String} (hz : z ∈ glueLay.scalars) (N : ℕ) : Com.Ok glueLay (satLit z N) :=
  satLit_ok' hz glueLay_W (by decide) N

theorem pushLits_okG (l : List ℕ) : Com.Ok glueLay (pushLits l) :=
  pushLits_ok' (by decide) (by decide) (by decide) l

/-! ### Commands without parameters -/

set_option maxRecDepth 100000 in
theorem rdIn_okG : Com.Ok glueLay rdIn := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem rmR_okG : Com.Ok glueLay rmR := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem rmLs_okG : Com.Ok glueLay rmLs := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem wrHS_okG : Com.Ok glueLay wrHS := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem setQ_okG : Com.Ok glueLay setQ := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem slotA_okG : Com.Ok glueLay slotA := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem slotB_okG : Com.Ok glueLay slotB := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem slotC_okG : Com.Ok glueLay slotC := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem cpPart_oe_okG : Com.Ok glueLay (cpPart "oe" 0) := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem mxSeg_okG : Com.Ok glueLay (mxSeg "OB" "qa" "ql") := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem entChk_okG : Com.Ok glueLay entChk := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem wrAll_okG : Com.Ok glueLay wrAll := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem rdX_okG : Com.Ok glueLay rdX := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem locate_okG : Com.Ok glueLay locate := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem end0_okG : Com.Ok glueLay end0 := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem ld0_okG : Com.Ok glueLay ld0 := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem fill0Pre_okG : Com.Ok glueLay (pushL "OB" "po" (sc0.map Expr.var)) :=
  StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem cpSeg_x_okG : Com.Ok glueLay (cpSeg "x" "gz" "pp") := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem cpSeg_x2_okG : Com.Ok glueLay (cpSeg "x" "qs" "qn") := StpRam.comOkB_sound _ _ (by decide)

set_option maxRecDepth 100000 in
theorem cpSeg_x3_okG : Com.Ok glueLay (cpSeg "x" "pp" "dl") := StpRam.comOkB_sound _ _ (by decide)

/-! ### Commands with parameters -/

set_option maxRecDepth 100000 in
theorem guardChk_okG (e d : ℕ) : Com.Ok glueLay (guardChk e d) := by
  simp +decide only [guardChk, satAdd, satPow, satMul, forUp, Com.Ok, Cond.Ok, condExpr, Expr.Ok, mxSeg_okG,
    satLit_okG (z := "oe") (by decide), satLit_okG (z := "oc") (by decide), and_true]

set_option maxRecDepth 100000 in
theorem finCall_okG (e d : ℕ) : Com.Ok glueLay (finCall e d) := by
  simp +decide only [finCall, Com.Ok, Expr.Ok, guardChk_okG, entChk_okG, wrAll_okG, and_true]

set_option maxRecDepth 100000 in
theorem finCallM_okG (e d : ℕ) : Com.Ok glueLay (finCallM e d) := by
  simp +decide only [finCallM, Com.Ok, Expr.Ok, guardChk_okG, entChk_okG, wrAll_okG, and_true]

set_option maxRecDepth 100000 in
theorem fill0_okG : Com.Ok glueLay fill0 := by
  simp +decide only [fill0, Com.Ok, Expr.Ok, ld0_okG, fill0Pre_okG, pushLits_okG, cpSeg_x_okG, cpSeg_x2_okG,
    cpSeg_x3_okG, push1, pushL, and_true]

set_option maxRecDepth 100000 in
theorem round0_okG (e d : ℕ) : Com.Ok glueLay (round0 e d) := by
  simp +decide only [round0, Com.Ok, Cond.Ok, condExpr, Expr.Ok, rdX_okG, locate_okG, end0_okG, fill0_okG,
    finCall_okG, and_true]

set_option maxRecDepth 100000 in
theorem wrQ_okG : Com.Ok glueLay (wrQ sA sB sC sE) := by
  simp +decide only [wrQ, sA, sB, sC, sE, Com.Ok, Cond.Ok, condExpr, Expr.Ok, pushLits_okG, slotA_okG, slotB_okG,
    slotC_okG, cpPart_oe_okG, and_true]

set_option maxRecDepth 100000 in
theorem finSel_okG (eS eF eC eK dS dF dC dK : ℕ) :
    Com.Ok glueLay (finSel eS eF eC eK dS dF dC dK) := by
  simp +decide only [finSel, Com.Ok, Cond.Ok, condExpr, Expr.Ok, finCallM_okG, and_true]

set_option maxRecDepth 100000 in
theorem gate_okG {c : Com} (h : Com.Ok glueLay c) : Com.Ok glueLay (gate c) := by
  simp +decide only [gate, Com.Ok, Cond.Ok, condExpr, Expr.Ok, h, and_true]

theorem tailR_okG (eS eF eC eK dS dF dC dK : ℕ) :
    Com.Ok glueLay (tailR eS eF eC eK dS dF dC dK) :=
  ⟨rmLs_okG, gate_okG ⟨wrHS_okG, wrQ_okG, setQ_okG, finSel_okG eS eF eC eK dS dF dC dK⟩⟩

/-- **The start of a later round**, around a body that compiles. -/
theorem rdPre_okG {body : Com} (h : Com.Ok glueLay body) : Com.Ok glueLay (rdPre body) :=
  ⟨⟨rdIn_okG, rmR_okG, rmLs_okG⟩, gate_okG h⟩

/-- **A later round**, around a body and an end of the last round that compile. -/
theorem roundJ_okG {body fE : Com} (hb : Com.Ok glueLay body) (hf : Com.Ok glueLay fE)
    (eS eF eC eK dS dF dC dK : ℕ) : Com.Ok glueLay (roundJ body fE eS eF eC eK dS dF dC dK) := by
  refine rdPre_okG ⟨hb, gate_okG ?_⟩
  simp +decide only [Com.Ok, Cond.Ok, condExpr, Expr.Ok, hf, tailR_okG, and_true]

/-- **The glue program**, around a later round that compiles. -/
theorem glueTop_okG {rJ : Com} (h : Com.Ok glueLay rJ) (K e d : ℕ) :
    Com.Ok glueLay (glueTop K e d rJ) := by
  simp +decide only [glueTop, Com.Ok, Cond.Ok, condExpr, Expr.Ok, satLit_okG (z := "gk") (by decide),
    round0_okG, h, and_true]

end Lax185574Proofs.ResolveRam.Glue
