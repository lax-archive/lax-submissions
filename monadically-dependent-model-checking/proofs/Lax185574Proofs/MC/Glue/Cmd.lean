import Lax185574Proofs.MC.Glue.RoundJ

/-!
The glue program of thm:mc.

`glueCmd` reads the tag, checks that the word size admits the fixed
queries and answers (`dK < W / 8`), and runs round `0` and its first call
for the tag `0`, or a later round otherwise. `gLayout` lists its scalars
and arrays, and `glueCmd_ok` says that it compiles.
-/

namespace Lax185574Proofs.MC.Glue

open Lax185574Proofs.MC Lax185574Proofs.Words Lax185574Proofs.Simulate
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile

/-- The glue program, as a command. -/
noncomputable def glueCmd (eM eR eE d : ℕ) : Com :=
  .seq (.seq (.read "tg") (satLit "zk" dK)) (.ite (.lt (.var "zk") (.div (.var "W") (.lit 8)))
    (.ite (.eq (.var "tg") (.lit 0))
      (.seq round0 (.ite (.eq (.var "ovf") (.lit 0)) (r0Call eM eR eE d) .skip))
      (roundJ eM eR eE d))
    (.assign "ovf" (.lit 1)))

/-- The scalars and arrays of the glue program. -/
def gLayout : Layout :=
  ⟨["W", "ovf", "tg", "zk", "bA", "bl", "cA", "cP", "cQ", "ca", "ci", "ck", "cl", "cs", "ct", "cv",
    "dc", "e1", "e2", "e3", "e4", "e5", "fA", "fb", "fc", "fd", "fl", "fm", "fo", "fp", "gA", "gE",
    "gL", "gS", "gc", "gi", "gl", "gn", "iwK", "iwa", "iwc", "iwd", "iwe", "iwi", "iwj", "iwl", "iwn",
    "iwp", "iwq", "iwr", "iwrm", "iwrp", "j", "lA", "ll", "lp", "lst", "mx", "n", "o1", "oa", "ob",
    "oc", "oe", "off", "oi", "okk", "op", "otg", "oz", "p", "pf", "pg", "po", "qa", "ql", "qz", "rc",
    "rk", "s0", "sl", "sm", "sp", "tE", "tS", "ta", "tl", "v", "w0", "w1", "w2", "y", "zA", "zA2",
    "zAA", "zC", "zE", "zM", "zP", "zP1", "zT", "zc1", "zc20", "zc3", "zc9", "zd", "ze", "zi", "zx",
    "zy"],
    ["FW", "GW", "OB", "RP", "U", "lo", "stk", "ta", "tb", "x"], 8⟩

theorem gL_s : gLayout.scalars = ["W", "ovf", "tg", "zk", "bA", "bl", "cA", "cP", "cQ", "ca", "ci", "ck",
    "cl", "cs", "ct", "cv",
    "dc", "e1", "e2", "e3", "e4", "e5", "fA", "fb", "fc", "fd", "fl", "fm", "fo", "fp", "gA", "gE",
    "gL", "gS", "gc", "gi", "gl", "gn", "iwK", "iwa", "iwc", "iwd", "iwe", "iwi", "iwj", "iwl", "iwn",
    "iwp", "iwq", "iwr", "iwrm", "iwrp", "j", "lA", "ll", "lp", "lst", "mx", "n", "o1", "oa", "ob",
    "oc", "oe", "off", "oi", "okk", "op", "otg", "oz", "p", "pf", "pg", "po", "qa", "ql", "qz", "rc",
    "rk", "s0", "sl", "sm", "sp", "tE", "tS", "ta", "tl", "v", "w0", "w1", "w2", "y", "zA", "zA2",
    "zAA", "zC", "zE", "zM", "zP", "zP1", "zT", "zc1", "zc20", "zc3", "zc9", "zd", "ze", "zi", "zx",
    "zy"] := rfl
theorem gL_a : gLayout.arrays = ["FW", "GW", "OB", "RP", "U", "lo", "stk", "ta", "tb", "x"] := rfl
theorem gL_t : gLayout.temps = 8 := rfl

theorem satLit_ok {z : String} (hz : z ∈ gLayout.scalars) (hW : "W" ∈ gLayout.scalars) :
    ∀ N, Com.Ok gLayout (satLit z N) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    rw [satLit]
    split_ifs with h1 h2
    · simp [Com.Ok, Expr.Ok, hz]
    · refine ⟨ih _ (by omega), ?_, ?_⟩
      · simp [satAdd, Com.Ok, Cond.Ok, condExpr, Expr.Ok, gLayout] at hz ⊢; simp [hz]
      · simp [satInc, Com.Ok, Cond.Ok, condExpr, Expr.Ok, gLayout] at hz ⊢; simp [hz]
    · refine ⟨ih _ (by omega), ?_, trivial⟩
      simp [satAdd, Com.Ok, Cond.Ok, condExpr, Expr.Ok, gLayout] at hz ⊢; simp [hz]

theorem pushL_ok {a pv : String} (ha : a ∈ gLayout.arrays) (hpv : pv ∈ gLayout.scalars) :
    ∀ es : List Expr, (∀ e ∈ es, Expr.Ok gLayout e 1) → Com.Ok gLayout (pushL a pv es)
  | [], _ => trivial
  | e :: es, h => ⟨⟨⟨ha, hpv, h e (by simp), by decide⟩, hpv, trivial, hpv, by decide⟩,
      pushL_ok ha hpv es (fun e' he' => h e' (by simp [he']))⟩

theorem pushLits_ok (l : List ℕ) : Com.Ok gLayout (pushLits l) :=
  pushL_ok (by simp [gLayout]) (by simp [gLayout]) _ (fun e he => by
    simp only [List.mem_map] at he; obtain ⟨v, -, rfl⟩ := he; trivial)

theorem satLit_oz : ∀ N, Com.Ok gLayout (satLit "oz" N) := satLit_ok (by simp [gLayout]) (by simp [gLayout])
theorem satLit_oe : ∀ N, Com.Ok gLayout (satLit "oe" N) := satLit_ok (by simp [gLayout]) (by simp [gLayout])
theorem satLit_oc : ∀ N, Com.Ok gLayout (satLit "oc" N) := satLit_ok (by simp [gLayout]) (by simp [gLayout])

theorem outCmd_ok (eM eR eE d : ℕ) : Com.Ok gLayout (outCmd eM eR eE d) := by
  simp [outCmd, afterF, apAll, apJ, apOne, dmRow, dmInit, jbOne, apR, apS, buildInit, copyBack, copyTa, cpCol, cpGW, cpLo, cpSeg, cpTo, cpX, entChk, evEnd, fAnd, fAtom, fBody, fEmit, fEx, fLoop, fNot, fPop, fWalk, fwInit, fwTree, guardChk, guardSel, gwCols, gwInit, gwZeros, hdr1, issue, lastChk, ldL, ldSc, levelBody, locT, mBound, mInit, mxBody, mxSeg, nxF, outEnd, powers, push1, r0Chk2, r0Ev, r0Fields, r0Fill, r0Main, r0Step, rdIn, rdWin, read0, readInto, readOne, round0, roundJ, rpBody, rpTab, satAdd, satInc, satMul, satPow, setIf, sizeChk, skipG, skipL, skipLs, skipPG, skipT, stF, tLoc, tag1, tag2, tagSet, wAtoms, wCDist, wCol, wDist, wEq, wExts, wLevel, wq0, wq1, wq2, wq3, wrAll, wrHd, wrQ, forUp, ldNames, scN, cntE, cdistL, cdistRow, colL, distBlk, distL, distRow, eqL, eqRow, Com.Ok, Cond.Ok, condExpr, Expr.Ok, gL_s, gL_a, gL_t, pushL, scA, satLit_oz, satLit_oe, satLit_oc,
    pushLits_ok]

theorem round0_ok : Com.Ok gLayout round0 := by
  simp [pushL, gL_s, gL_a, gL_t, afterF, apAll, apJ, apOne, dmRow, dmInit, jbOne, apR, apS, buildInit, copyBack, copyTa, cpCol, cpGW, cpLo, cpSeg, cpTo, cpX, entChk, evEnd, fAnd, fAtom, fBody, fEmit, fEx, fLoop, fNot, fPop, fWalk, fwInit, fwTree, guardChk, guardSel, gwCols, gwInit, gwZeros, hdr1, issue, lastChk, ldL, ldSc, levelBody, locT, mBound, mInit, mxBody, mxSeg, nxF, outEnd, powers, push1, r0Chk2, r0Ev, r0Fields, r0Fill, r0Main, r0Step, rdIn, rdWin, read0, readInto, readOne, round0, roundJ, rpBody, rpTab, satAdd, satInc, satMul, satPow, setIf, sizeChk, skipG, skipL, skipLs, skipPG, skipT, stF, tLoc, tag1, tag2, tagSet, wAtoms, wCDist, wCol, wDist, wEq, wExts, wLevel, wq0, wq1, wq2, wq3, wrAll, wrHd, wrQ, forUp, ldNames, scN, cntE, cdistL, cdistRow, colL, distBlk, distL, distRow, eqL, eqRow, Com.Ok, Cond.Ok, condExpr, Expr.Ok, gLayout]

theorem r0Call_ok (eM eR eE d : ℕ) : Com.Ok gLayout (r0Call eM eR eE d) :=
  ⟨by simp [pushL, gL_s, gL_a, gL_t, afterF, apAll, apJ, apOne, dmRow, dmInit, jbOne, apR, apS, buildInit, copyBack, copyTa, cpCol, cpGW, cpLo, cpSeg, cpTo, cpX, entChk, evEnd, fAnd, fAtom, fBody, fEmit, fEx, fLoop, fNot, fPop, fWalk, fwInit, fwTree, guardChk, guardSel, gwCols, gwInit, gwZeros, hdr1, issue, lastChk, ldL, ldSc, levelBody, locT, mBound, mInit, mxBody, mxSeg, nxF, outEnd, powers, push1, r0Chk2, r0Ev, r0Fields, r0Fill, r0Main, r0Step, rdIn, rdWin, read0, readInto, readOne, round0, roundJ, rpBody, rpTab, satAdd, satInc, satMul, satPow, setIf, sizeChk, skipG, skipL, skipLs, skipPG, skipT, stF, tLoc, tag1, tag2, tagSet, wAtoms, wCDist, wCol, wDist, wEq, wExts, wLevel, wq0, wq1, wq2, wq3, wrAll, wrHd, wrQ, forUp, ldNames, scN, cntE, cdistL, cdistRow, colL, distBlk, distL, distRow, eqL, eqRow, Com.Ok, Cond.Ok, condExpr, Expr.Ok, gLayout], outCmd_ok eM eR eE d⟩

theorem roundJ_ok (eM eR eE d : ℕ) : Com.Ok gLayout (roundJ eM eR eE d) := by
  simp [pushL, gL_s, gL_a, gL_t, afterF, apAll, apJ, apOne, dmRow, dmInit, jbOne, apR, apS, buildInit, copyBack, copyTa, cpCol, cpGW, cpLo, cpSeg, cpTo, cpX, entChk, evEnd, fAnd, fAtom, fBody, fEmit, fEx, fLoop, fNot, fPop, fWalk, fwInit, fwTree, guardChk, guardSel, gwCols, gwInit, gwZeros, hdr1, issue, lastChk, ldL, ldSc, levelBody, locT, mBound, mInit, mxBody, mxSeg, nxF, outEnd, powers, push1, r0Chk2, r0Ev, r0Fields, r0Fill, r0Main, r0Step, rdIn, rdWin, read0, readInto, readOne, round0, roundJ, rpBody, rpTab, satAdd, satInc, satMul, satPow, setIf, sizeChk, skipG, skipL, skipLs, skipPG, skipT, stF, tLoc, tag1, tag2, tagSet, wAtoms, wCDist, wCol, wDist, wEq, wExts, wLevel, wq0, wq1, wq2, wq3, wrAll, wrHd, wrQ, forUp, ldNames, scN, cntE, cdistL, cdistRow, colL, distBlk, distL, distRow, eqL, eqRow, Com.Ok, Cond.Ok, condExpr, Expr.Ok, outCmd_ok]

theorem glueCmd_ok (eM eR eE d : ℕ) : Com.Ok gLayout (glueCmd eM eR eE d) :=
  ⟨⟨by simp [Com.Ok, gLayout], satLit_ok (by simp [gLayout]) (by simp [gLayout]) _⟩,
    by simp [Cond.Ok, condExpr, Expr.Ok, gLayout],
    ⟨by simp [Cond.Ok, condExpr, Expr.Ok, gLayout], ⟨round0_ok, by simp [Cond.Ok, condExpr, Expr.Ok,
      gLayout], r0Call_ok eM eR eE d, trivial⟩, roundJ_ok eM eR eE d⟩,
    by simp [Com.Ok, Expr.Ok, gLayout]⟩

end Lax185574Proofs.MC.Glue
