import Lax185574Proofs.ResolveRam.Glue.OkKit
import Lax185574Proofs.ResolveRam.Glue.PAt9
import Lax185574Proofs.ResolveRam.Glue.PFASpec
import Lax185574Proofs.ResolveRam.Glue.PEx7
import Lax185574Proofs.ResolveRam.Glue.PKid
import Lax185574Proofs.ResolveRam.Glue.PH3
import Lax185574Proofs.ResolveRam.Glue.PCT5
import Lax185574Proofs.ResolveRam.Glue.PLv2
import Lax185574Proofs.Words.Guarded

/-!
The layout of the glue program of lem:resolve-lift.

`glueLay` has every scalar and every array of the cases of the glue
program and of the pieces it runs, and `64` temporaries, as many as the
piece of the head needs. The pieces compile in it (`atCmd_okG` and the
like), by `com_ok_mono`. Its guard has `369` bits.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax185574Proofs.Words

/-- The scalars of the glue program. -/
def glS : List String :=
  ["W", "ovf", "NCO", "NFA", "NLV", "NSG", "Nd", "Ni", "Nm", "Nph", "Nt", "Nw", "a0", "b0", "bl",
    "c0", "ci", "ck", "cl", "cn", "cv", "dd", "e0", "e1", "e2", "f0", "fN", "fb", "fc", "fi", "fk",
    "flo", "fp", "gK", "gP", "gQ", "gS", "gX", "gc", "gk", "gn", "gq", "gz", "i", "iL", "ii", "j",
    "kl", "kn", "lD", "lL", "lN", "lS", "lo", "ls", "lt", "lvL", "lvN", "lvZ", "m", "m0", "mm",
    "mw", "mx", "n", "nCO", "nFA", "nLV", "nSG", "ne", "np", "nx", "o1", "oL", "oa", "ob", "oc",
    "oe", "of", "oi", "ol", "os", "ow", "ox", "p", "pc", "ph", "pk", "po", "pp", "pq", "pz", "q0",
    "q1", "qa", "qk", "ql", "qn", "qs", "qz", "r2", "r9", "rA", "rB", "rE", "rM", "rR", "rS", "rY",
    "rk", "sl", "sv", "tg", "v", "wa", "wl", "yo", "z0", "tb0", "tE", "tRp", "tpk", "tRm", "tL",
    "tp1", "tp2", "th", "tx", "tz", "tcn", "tcb", "tck", "tY", "tcP", "tcQ", "tP", "tQ", "tsg",
    "tnc", "tcb0", "tqi", "tqj", "tdL", "td0", "td1", "td2", "td3", "tmp", "tmL", "tm0", "tm1",
    "tm2", "tm3", "tmb", "tmf", "tmn", "tmj", "tF", "tA", "tB", "tC", "tD", "tG", "tH", "tqm",
    "tqY", "tqs", "ts", "ti1", "ti2", "tv", "ta", "tb", "tn", "tu", "tw", "tk", "tI", "tl", "tf",
    "tN", "tm", "tk1", "tqq", "tl1", "th0", "th1", "th2", "te", "tne", "tsS", "tsN", "tc", "tO1",
    "tO2", "tq", "tj", "tw0", "tpp", "tgg", "tw1", "tOl", "tsa", "tsl", "thn", "thcx", "thc0",
    "thx1", "thx", "thk", "thr", "thgp", "thgq", "thgs", "thb", "tha", "thd", "thw", "thv", "tkcd",
    "tkcx", "tkcy", "tkck", "tkcv", "tkcn", "tkcp", "tkok", "tkv", "tkgp", "tkgq", "tkbx", "tknc",
    "tkbz", "tkbe", "tkbv", "tkbj", "tkbw", "tkb", "tkbs", "tkn", "tkw", "tkfd", "tku", "tklo",
    "tkm", "tkcnt", "tkc", "tgc", "tcv",
    "tsb", "tsm", "tyl", "tys",
    "thdl", "thdv", "thdx", "thdu", "thdw", "thca", "thcb", "thcr", "thhp", "thhq", "thh1", "thh2",
    "thh3", "thh4", "tkdl", "tkdv", "tkdx", "tkdu", "tkdw", "tkca", "tkcb", "tkcr", "dl"]

/-- The arrays of the glue program. -/
def glA : List String :=
  ["OB", "PR", "a", "st", "ln", "x", "y", "Thco", "ThE", "ThN", "ThRm", "Tkco", "Tkeo", "Tket",
    "Tkno", "Tknt", "Tkcl", "Tkdm", "Tkdn", "Tkct", "Tkc1", "Tksy", "Tksu", "Thdd", "Thdp", "Thdq",
    "Tkdd"]

/-- The layout of the glue program. -/
def glueLay : Layout := ⟨glS, glA, 64⟩

theorem gl_s : glueLay.scalars = glS := rfl
theorem gl_a : glueLay.arrays = glA := rfl
theorem gl_t : glueLay.temps = 64 := rfl

theorem glueLay_W : "W" ∈ glueLay.scalars := by decide
theorem glueLay_ovf : "ovf" ∈ glueLay.scalars := by decide

set_option maxRecDepth 100000 in
theorem guardBits_glueLay : guardBits glueLay = 369 := rfl

set_option maxRecDepth 100000 in
theorem atCmd_okG : Com.Ok glueLay atCmd := com_ok_mono atCmd_ok (by decide) (by decide) (by decide)
theorem faCmd_okG : Com.Ok glueLay faCmd := com_ok_mono faCmd_ok (by decide) (by decide) (by decide)
set_option maxRecDepth 100000 in
theorem exCmd_okG : Com.Ok glueLay exCmd := com_ok_mono exCmd_ok (by decide) (by decide) (by decide)
theorem kidCmd_okG : Com.Ok glueLay kidCmd := com_ok_mono kidCmd_ok (by decide) (by decide) (by decide)
set_option maxRecDepth 100000 in
theorem hCmd_okG : Com.Ok glueLay hCmd := com_ok_mono hCmd_ok (by decide) (by decide) (by decide)
theorem ctCmd_okG : Com.Ok glueLay ctCmd := com_ok_mono ctCmd_ok (by decide) (by decide) (by decide)
theorem lv0Cmd_okG : Com.Ok glueLay lv0Cmd := com_ok_mono lv0Cmd_ok (by decide) (by decide) (by decide)

end Lax185574Proofs.ResolveRam.Glue
