import Lax185574Proofs.CompRam.GPow
import Lax185574Proofs.CompRam.FixedW
import Lax185574Proofs.MC.Glue.Out
import Lax185574Proofs.Words.TreeWord
import Lax185574Proofs.Words.GuardedSound

/-!
The command of the glue program of lem:compose.

The round copies its input, after the tag and the length of the state,
into the array `x`. In round `0` this is the input word
`[k, q, l1] ++ X ++ [k, q, l2] ++ Y` of the composite. In round `j ≥ 1`
it is the state `0 :: j :: toWord ws` followed by the frame `|o| :: o` of
the answer of the switch, where `ws` are the words of the stack. Then
`wp[i]` is the position of the frame of word `i` of the stack, for the
words of the two top frames.

The output is built in the buffer `OB` (filled up to `po`): the head
`[1, L, 0, 0, j + 1, count]`, the frames of the new top frames, the
unchanged rest of the stack as one segment of `x`, and the query of the
switch, or `0 :: z` for the final word. The fixed question `dSq` of the
rank shift is not put into the buffer: the buffer is written up to
`sp`, then `dSq` if `dq = 1`, then the rest of the buffer. Lengths that
are known only after a part is written are filled in afterwards.

A frame to be written is described by scalars (`emFr`): its six numbers
`gd gk g1 g2 gp gi`, the segments of `x` holding `A`, `B`, `SA`, `SB`,
`AT` (start `g?s`, length `g?l`), the segment of the word of `EX`, and,
if `gx = 1`, a new last word `gg :: R₁ ++ R₂` of `EX` with the segments
`R₁`, `R₂`. A new frame (`emFresh`) has its numbers in `cd ck c1 c2` and
its node words at `cAs`, `cBs`.

The checks: the round test `(2 j + 2)^4 ≤ 2^(v - sQ)` and the guard of
the query of the working callee (`guardChk`, kind `qk`: `0` restriction,
`1` rank shift, `2` canonical form, `3` none), and every written entry
below `Ob = W / 2^20 + 1` (`wChk`). If `W < 2^34` the round only sets
`ovf`.
-/

namespace Lax185574Proofs.CompRam

open Lax808846Proofs.Imp Lax808846Proofs.Compile Lax185574Proofs.Words Lax185574Proofs.MC Lax185574Proofs.MC.Glue

/-- The length of the fixed question of the rank shift. -/
def lDSq : ℕ := 37345

/-- A sequence of commands. -/
def seqs : List Com → Com
  | [] => .skip
  | [c] => c
  | c :: cs => .seq c (seqs cs)

/-- Assign a scalar. -/
abbrev asg (x : String) (e : Expr) : Com := .assign x e

/-- A scalar. -/
abbrev V (x : String) : Expr := .var x

/-- A literal. -/
abbrev N (n : ℕ) : Expr := .lit n

/-- An entry of `x`. -/
abbrev X (e : Expr) : Expr := .get "x" e

/-! ### Reading and moving through `x` -/

/-- Read one entry onto `x`. -/
def rdBody : Com := .seq (.read "rv") (push1 "x" "xp" (V "rv"))

/-- Read `n` entries onto `x`. -/
def rdN (n : String) : Com := forUp "ri" (V n) rdBody

/-- Move `y` past one frame. -/
def stepY : Com := asg "y" (.add (.add (V "y") (X (V "y"))) (N 1))

/-- Move `y` past `k` frames. -/
def skipK (k : String) : Com := forUp "sk" (V k) stepY

/-- Move `y` past a list of words. -/
def skipL : Com := seqs [asg "sn" (X (V "y")), asg "y" (.add (V "y") (N 1)), skipK "sn"]

/-- Move `y` past a node word of depth `dd`. -/
def skipNode : Com := .seq skipL (.ite (.eq (V "dd") (N 0)) .skip skipL)

/-- The positions of the frames of the first `nb` words of the stack. -/
def locW : Com :=
  .seq (asg "y" (N 3)) (forUp "wi" (V "nb") (.seq (.store "wp" (V "wi") (V "y")) stepY))

/-- The segment of word `w` of the stack. -/
def ldW (w : ℕ) (s l : String) : Com :=
  .seq (asg s (.add (.get "wp" (N w)) (N 1))) (asg l (X (.get "wp" (N w))))

/-- `y` at the list of extensions of the node word at `s`, `cnt` their number. -/
def extsAt (s cnt : String) : Com := seqs [asg "y" (V s), skipL, asg cnt (X (V "y"))]

/-- `y` from a list of words to its frame `k`. -/
def extFr (k : String) : Com := .seq (asg "y" (.add (V "y") (N 1))) (skipK k)

/-! ### Writing into the buffer -/

/-- Append a value. -/
def pv (e : Expr) : Com := push1 "OB" "po" e

/-- Append a segment of `x`. -/
def emSeg (s l : String) : Com := cpSeg "x" s l

/-- Append a word of `x` with its length. -/
def emW (s l : String) : Com := .seq (pv (V l)) (emSeg s l)

/-- Append scalars. -/
def pvs (xs : List String) : Com := pushL "OB" "po" (xs.map Expr.var)

/-- The word of `EX` of the frame, without its length. -/
def emEXc : Com :=
  .ite (.eq (V "gx") (N 0)) (emSeg "gEs" "gEl")
    (seqs [pv (.add (X (V "gEs")) (N 1)), asg "u1" (.add (V "gEs") (N 1)),
      asg "u2" (.sub (V "gEl") (N 1)), emSeg "u1" "u2", pv (.add (.add (N 1) (V "r1l")) (V "r2l")),
      pv (V "gg"), emSeg "r1s" "r1l", emSeg "r2s" "r2l"])

/-- The word of `EX` of the frame, with its length. -/
def emEXw : Com :=
  seqs [.ite (.eq (V "gx") (N 0)) (asg "gEL" (V "gEl"))
      (asg "gEL" (.add (.add (.add (V "gEl") (N 2)) (V "r1l")) (V "r2l"))),
    pv (V "gEL"), emEXc]

/-- The frame described by the scalars `g…`. -/
def emFr : Com :=
  seqs [pv (N 6), pvs ["gd", "gk", "g1", "g2", "gp", "gi"], emW "gAs" "gAl", emW "gBs" "gBl",
    emW "gSs" "gSl", emW "gTs" "gTl", emW "gUs" "gUl", emEXw]

/-- A new frame. -/
def emFresh : Com :=
  seqs [pv (N 6), pvs ["cd", "ck", "c1", "c2"], pushLits [0, 0], emW "cAs" "cAl", emW "cBs" "cBl",
    pushLits [0, 0, 0, 1, 0]]

/-- The head of the output of a call. -/
def emHd : Com := .seq (pushLits [1, 0, 0, 0]) (pvs ["j1", "cnt"])

/-- The rest of the stack. -/
def emRest : Com := emSeg "rS" "rL"

/-- Fill in the length of the state. -/
def patchL : Com := .store "OB" (N 1) (.sub (V "po") (N 3))

/-! ### The atoms of a new frame -/

/-- Set `fb` when entry `fk` of an atom code with opcode `ft` is a position. -/
def posCmd : Com :=
  .seq (asg "fb" (N 0))
  (.ite (.lt (V "ft") (N 3))
    (.ite (.eq (V "fk") (N 1)) (asg "fb" (N 1))
      (.ite (.eq (V "fk") (N 2)) (asg "fb" (N 1)) .skip))
  (.ite (.eq (V "ft") (N 3))
    (.ite (.eq (V "fk") (N 2)) (asg "fb" (N 1)) .skip)
  (.ite (.eq (V "ft") (N 4))
    (.ite (.eq (V "fk") (N 2)) (asg "fb" (N 1))
      (.ite (.eq (V "fk") (N 3)) (asg "fb" (N 1)) .skip))
  (.ite (.eq (V "ft") (N 5))
    (.ite (.eq (V "fk") (N 3)) (asg "fb" (N 1)) .skip) .skip))))

/-- Append entry `fk` of the atom code at `y`, moved by `c1` if it is a position. -/
def renEnt : Com :=
  .seq posCmd (pv (.add (X (.add (.add (V "y") (N 1)) (V "fk"))) (.mul (V "fb") (V "c1"))))

/-- Append the frame of the atom code at `y`, renamed, and move `y` past it. -/
def renFr : Com :=
  seqs [asg "fl" (X (V "y")), pv (V "fl"), asg "ft" (X (.add (V "y") (N 1))),
    forUp "fk" (V "fl") renEnt, stepY]

/-- The word of the atoms of the new frame. -/
def emAtoms : Com :=
  seqs [asg "y" (V "cAs"), skipL, asg "u1" (.add (V "cAs") (N 1)),
    asg "u2" (.sub (.sub (V "y") (V "cAs")) (N 1)), pv (.add (X (V "cAs")) (X (V "cBs"))),
    emSeg "u1" "u2", asg "nr" (X (V "cBs")), asg "y" (.add (V "cBs") (N 1)),
    forUp "rk" (V "nr") renFr]

/-! ### The queries -/

/-- The entry `J[fk]` of the positions of a restriction. -/
def jEnt : Com :=
  .ite (.lt (V "fk") (V "p1")) (pv (V "fk"))
    (.ite (.lt (V "fk") (.add (V "p1") (V "p2"))) (pv (.add (V "fk") (N 1))) (pv (V "p1")))

/-- The query of a restriction, with the parent in `pk pd p1 p2` and the
result in `R₁ ++ R₂`. -/
def emRe : Com :=
  seqs [pushLits [0, lDSq, 1], asg "qa" (V "po"), pv (.add (V "pk") (N 1)), pv (.sub (V "pd") (N 1)),
    pv (.add (.add (V "p1") (N 1)) (V "p2")), emSeg "r1s" "r1l", emSeg "r2s" "r2l",
    pv (.add (.add (V "p1") (V "p2")) (N 1)), forUp "fk" (.add (.add (V "p1") (V "p2")) (N 1)) jEnt,
    asg "ql" (.sub (V "po") (V "qa")), .store "OB" (.sub (V "qa") (N 3)) (V "ql"),
    asg "sp" (V "po"), pv (N 0), asg "dq" (N 1), asg "qk" (N 0)]

/-- The query of a rank shift of `[hk, hd, hl] ++ W` with `W` at `hs`, `hw`. -/
def emSh : Com :=
  seqs [pushLits [5, 0, 1, 0, 0, 0, 0, 0], asg "qa" (V "po"), pvs ["hk", "hd", "hl"], emSeg "hs" "hw",
    asg "ql" (.sub (V "po") (V "qa")), .store "OB" (.sub (V "qa") (N 7)) (V "ql"), pv (N 0),
    asg "sp" (V "po"), asg "dq" (N 0), asg "qk" (N 1)]

/-- The head of the query of a canonical form. -/
def emCaHd : Com :=
  seqs [pushLits [5, lDSq, 0, 0, 0, 0, 0, 0], asg "sp" (V "po"), asg "dq" (N 1), asg "qa" (V "po")]

/-- The end of the query of a canonical form. -/
def emCaEnd : Com :=
  seqs [asg "ql" (.sub (V "po") (V "qa")), .store "OB" (.sub (V "qa") (N 6)) (V "ql"), asg "qk" (N 2)]

/-- The final word `0 :: [hk, hd, hl] ++ R₁ ++ R₂`. -/
def emDone : Com :=
  seqs [pv (N 0), pvs ["hk", "hd", "hl"], emSeg "r1s" "r1l", emSeg "r2s" "r2l", asg "sp" (V "po"),
    asg "dq" (N 0), asg "qk" (N 3)]

/-! ### The rounds -/

/-- Load the frame with words from `w` on into the scalars `g…`. -/
def ldG (w : ℕ) : Com :=
  seqs [asg "gd" (X (.add (.get "wp" (N w)) (N 1))), asg "gk" (X (.add (.get "wp" (N w)) (N 2))),
    asg "g1" (X (.add (.get "wp" (N w)) (N 3))), asg "g2" (X (.add (.get "wp" (N w)) (N 4))),
    asg "gp" (X (.add (.get "wp" (N w)) (N 5))), asg "gi" (X (.add (.get "wp" (N w)) (N 6))),
    ldW (w + 1) "gAs" "gAl", ldW (w + 2) "gBs" "gBl", ldW (w + 3) "gSs" "gSl",
    ldW (w + 4) "gTs" "gTl", ldW (w + 5) "gUs" "gUl", ldW (w + 6) "gEs" "gEl", asg "gx" (N 0)]

/-- The rest of the stack below the first `c` frames. -/
def ldRest (c : ℕ) : Com :=
  seqs [asg "rS" (.add (.add (.get "wp" (N (7 * c - 1))) (X (.get "wp" (N (7 * c - 1))))) (N 1)),
    asg "rL" (.sub (V "L") (V "rS")), asg "cnt" (.sub (V "n") (N (7 * c)))]

/-- The child of the current extension of the frame `g…`. -/
def childCmd : Com :=
  seqs [asg "cd" (.sub (V "gd") (N 1)), asg "ck" (.add (V "gk") (N 1)),
    .ite (.lt (V "gi") (V "nA"))
      (seqs [asg "c1" (.add (V "g1") (N 1)), asg "c2" (V "g2"), asg "y" (V "yA"), extFr "gi",
        asg "cAs" (.add (V "y") (N 2)), asg "cAl" (.sub (X (V "y")) (N 1)), asg "cBs" (V "gTs"),
        asg "cBl" (V "gTl")])
      (seqs [asg "c1" (V "g1"), asg "c2" (.add (V "g2") (N 1)), asg "y" (V "yB"),
        asg "u" (.sub (V "gi") (V "nA")), extFr "u", asg "cAs" (V "gSs"), asg "cAl" (V "gSl"),
        asg "cBs" (.add (V "y") (N 2)), asg "cBl" (.sub (X (V "y")) (N 1))])]

/-- Advance the frame `g…` above the rest: open the child of its current
extension, or ask for the canonical form of its extensions. -/
def advCmd : Com :=
  seqs [extsAt "gAs" "nA", asg "yA" (V "y"), extsAt "gBs" "nB", asg "yB" (V "y"),
    .ite (.lt (V "gi") (.add (V "nA") (V "nB")))
      (seqs [childCmd, asg "gp" (N 3), asg "cnt" (.add (V "cnt") (N 14)), emHd, emFresh, emFr, emRest,
        patchL, emCaHd, emAtoms, emCaEnd])
      (seqs [asg "gp" (N 5), asg "cnt" (.add (V "cnt") (N 7)), emHd, emFr, emRest, patchL, emCaHd,
        emEXc, emCaEnd])]

/-- Hand the result `R₁ ++ R₂` of the top frame with the head
`[hk, hd, hl]` down: output it, ask for its restriction, or advance the
parent. -/
def retCmd : Com :=
  .ite (.eq (V "n") (N 7)) emDone
    (seqs [ldG 7, asg "pk" (V "gk"), asg "pd" (V "gd"), asg "p1" (V "g1"), asg "p2" (V "g2"),
      ldRest 2, extsAt "gAs" "nA",
      .ite (.lt (V "gi") (V "nA"))
        (seqs [asg "gp" (N 4), asg "cnt" (.add (V "cnt") (N 7)), emHd, emFr, emRest, patchL, emRe])
        (seqs [extsAt "gBs" "nB", asg "u" (.sub (V "gi") (V "nA")), extFr "u",
          asg "gg" (.add (V "g1") (X (.add (V "y") (N 1)))), asg "gx" (N 1),
          asg "gi" (.add (V "gi") (N 1)), advCmd])])

/-- Round `0`: the first frame and the canonical form of its atoms. -/
def round0 : Com :=
  seqs [asg "ck" (X (N 0)), asg "cd" (X (N 1)), asg "c1" (X (N 2)), asg "cAs" (N 3), asg "y" (N 3),
    asg "dd" (V "cd"), skipNode, asg "cAl" (.sub (V "y") (N 3)), asg "c2" (X (.add (V "y") (N 2))),
    asg "cBs" (.add (V "y") (N 3)), asg "y" (V "cBs"), skipNode, asg "cBl" (.sub (V "y") (V "cBs")),
    asg "jr" (N 0), asg "j1" (N 1), asg "cnt" (N 7), emHd, emFresh, patchL, emCaHd, emAtoms, emCaEnd]

/-- The part `b` of the answer of the switch that belongs to the phase `tp`. -/
def pickCmd : Com :=
  .ite (.eq (V "tp") (N 4))
    (.seq (asg "bs" (V "oS")) (asg "bl" (.sub (V "oL") (N 428))))
    (.ite (.eq (V "tp") (N 1))
      (.seq (asg "bs" (.add (V "oS") (N 4))) (asg "bl" (.sub (V "oL") (N 5))))
      (.ite (.eq (V "tp") (N 2))
        (.seq (asg "bs" (.add (V "oS") (N 4))) (asg "bl" (.sub (V "oL") (N 5))))
        (.seq (asg "bs" (.add (V "oS") (N 431))) (asg "bl" (.sub (V "oL") (N 431))))))

/-- Phase `0`. -/
def ph0Cmd : Com :=
  .ite (.eq (V "td") (N 0))
    (seqs [asg "hk" (V "gk"), asg "hd" (N 0), asg "hl" (.add (V "g1") (V "g2")), asg "r1s" (N 0),
      asg "r1l" (N 0), asg "r2s" (V "bs"), asg "r2l" (V "bl"), retCmd])
    (seqs [asg "gp" (N 1), asg "gUs" (V "bs"), asg "gUl" (V "bl"), asg "cnt" (.add (V "cnt") (N 7)),
      emHd, emFr, emRest, patchL, asg "hk" (V "gk"), asg "hd" (V "gd"), asg "hl" (V "g2"),
      asg "hs" (V "gBs"), asg "hw" (V "gBl"), emSh])

/-- Phase `1`. -/
def ph1Cmd : Com :=
  seqs [asg "gp" (N 2), asg "gTs" (.add (V "bs") (N 3)), asg "gTl" (.sub (V "bl") (N 3)),
    asg "cnt" (.add (V "cnt") (N 7)), emHd, emFr, emRest, patchL, asg "hk" (V "gk"), asg "hd" (V "gd"),
    asg "hl" (V "g1"), asg "hs" (V "gAs"), asg "hw" (V "gAl"), emSh]

/-- Phase `2`. -/
def ph2Cmd : Com :=
  seqs [asg "gSs" (.add (V "bs") (N 3)), asg "gSl" (.sub (V "bl") (N 3)), asg "gi" (N 0), advCmd]

/-- Phase `4`. -/
def ph4Cmd : Com :=
  seqs [extsAt "gAs" "nA", extFr "gi", asg "gg" (X (.add (V "y") (N 1))), asg "gx" (N 1),
    asg "r1s" (.add (V "bs") (N 3)), asg "r1l" (.sub (V "bl") (N 3)), asg "r2s" (N 0), asg "r2l" (N 0),
    asg "gi" (.add (V "gi") (N 1)), advCmd]

/-- Phase `5`. -/
def ph5Cmd : Com :=
  seqs [asg "hk" (V "gk"), asg "hd" (V "gd"), asg "hl" (.add (V "g1") (V "g2")), asg "r1s" (V "gUs"),
    asg "r1l" (V "gUl"), asg "r2s" (V "bs"), asg "r2l" (V "bl"), retCmd]

/-- Round `j ≥ 1` after reading: the step of the machine by the phase of the top frame. -/
def roundJ : Com :=
  seqs [asg "jr" (X (N 1)), asg "j1" (.add (V "jr") (N 1)), asg "n" (X (N 2)),
    .ite (.lt (V "n") (N 14)) (asg "nb" (V "n")) (asg "nb" (N 14)),
    locW, asg "oS" (.add (V "L") (N 1)), asg "oL" (X (V "L")), ldG 0, asg "tp" (V "gp"),
    asg "td" (V "gd"), pickCmd, ldRest 1,
    .ite (.eq (V "tp") (N 0)) ph0Cmd (.ite (.eq (V "tp") (N 1)) ph1Cmd
      (.ite (.eq (V "tp") (N 2)) ph2Cmd (.ite (.eq (V "tp") (N 4)) ph4Cmd ph5Cmd)))]

/-- Read the input and run the round. -/
def buildCmd : Com :=
  seqs [.read "tg", .read "L", asg "xp" (N 0), rdN "L", asg "po" (N 0),
    .ite (.eq (V "tg") (N 0)) round0
      (seqs [.read "ol", push1 "x" "xp" (V "ol"), rdN "ol", roundJ])]

/-- The round test `(2 jr + 2)^4 ≤ 2^(v - sQ)`, with `d = sQ - guardBits`,
on the cell just behind the buffer. -/
def roundTest (d : ℕ) : Com :=
  seqs [.store "OB" (V "po") (.mul (N 2) (V "jr")), asg "qa" (V "po"), asg "ql" (N 1), guardChk 3 d]

/-- The guard of the query of the working callee. -/
def guardQ (eR eS eC d : ℕ) : Com :=
  .ite (.eq (V "qk") (N 0)) (guardChk eR d)
    (.ite (.eq (V "qk") (N 1)) (guardChk eS d)
      (.ite (.eq (V "qk") (N 2)) (guardChk eC d) .skip))

/-- Write the buffer, with `dSq` after its first `sp` entries if `dq = 1`. -/
def wrOut : Com :=
  seqs [asg "Ob" (.add (.shiftr (V "W") (N 20)) (N 1)), forUp "ci" (V "sp") (wChk (.get "OB" (V "ci"))),
    .ite (.eq (V "dq") (N 1)) wDSq .skip, asg "sq" (.sub (V "po") (V "sp")),
    forUp "ci" (V "sq") (wChk (.get "OB" (.add (V "sp") (V "ci"))))]

/-- The command of the glue. -/
def glueCmd (eR eS eC d : ℕ) : Com :=
  .ite (.eq (.shiftr (V "W") (N 34)) (N 0)) (asg "ovf" (N 1))
    (seqs [buildCmd, guardQ eR eS eC d, roundTest d, wrOut])

/-! ### The layout -/

/-- The layout of the glue. -/
def gLayout : Layout :=
  ⟨["tg", "dd", "ol", "rv", "xp", "ri", "nb", "wi", "oS", "oL", "td", "hw", "hs", "tp", "bs", "bl", "hk",
    "hd", "hl", "L", "n", "pk", "pd", "p2", "p1", "nB", "yA", "yB", "nA", "u", "cd", "ck", "c2", "cAl",
    "cBl", "sn", "sk", "cAs", "cBs", "nr", "fl", "ft", "fb", "c1", "fk", "y", "rk", "j1", "cnt", "gd",
    "gk", "g1", "g2", "gp", "gi", "gAl", "gAs", "gBl", "gBs", "gSl", "gSs", "gTl", "gTs", "gUl", "gUs",
    "gEL", "rL", "rS", "gx", "gEs", "gEl", "u2", "u1", "gg", "r1l", "r1s", "r2l", "r2s", "qk", "jr", "qa",
    "ql", "mx", "o1", "oe", "ob", "oi", "oc", "oa", "dq", "fj", "fi", "fr", "po", "sq", "sp", "Ob", "ci",
    "W", "ovf"], ["wp", "x", "OB"], 8⟩

/-- A check of `Expr.Ok`. -/
def okE (L : Layout) : Expr → ℕ → Bool
  | .lit _, _ => true
  | .var x, _ => L.scalars.contains x
  | .get a i, d => L.arrays.contains a && okE L i d && decide (d < L.temps)
  | .bin _ e f, d => okE L f d && okE L e (d + 1) && decide (d < L.temps)

/-- A check of `Com.Ok`. -/
def okC (L : Layout) : Com → Bool
  | .skip => true
  | .assign x e => L.scalars.contains x && okE L e 0
  | .store a i e => L.arrays.contains a && okE L i 0 && okE L e 1 && decide (0 < L.temps)
  | .seq c d => okC L c && okC L d
  | .ite b c d => okE L (condExpr b) 0 && okC L c && okC L d
  | .while b c => okE L (condExpr b) 0 && okC L c
  | .read x => L.scalars.contains x
  | .write e => okE L e 0 && decide (0 < L.temps)

theorem okE_sound {L : Layout} : ∀ {e : Expr} {d : ℕ}, okE L e d = true → Expr.Ok L e d
  | .lit _, _, _ => trivial
  | .var x, _, h => by simpa [okE, Expr.Ok] using h
  | .get a i, d, h => by
    simp only [okE, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
    exact ⟨h.1.1, okE_sound h.1.2, h.2⟩
  | .bin _ e f, d, h => by
    simp only [okE, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨okE_sound h.1.1, okE_sound h.1.2, h.2⟩

theorem okC_sound {L : Layout} : ∀ {c : Com}, okC L c = true → Com.Ok L c
  | .skip, _ => trivial
  | .assign x e, h => by
    simp only [okC, Bool.and_eq_true, List.contains_iff_mem] at h; exact ⟨h.1, okE_sound h.2⟩
  | .store a i e, h => by
    simp only [okC, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
    exact ⟨h.1.1.1, okE_sound h.1.1.2, okE_sound h.1.2, h.2⟩
  | .seq c d, h => by
    simp only [okC, Bool.and_eq_true] at h; exact ⟨okC_sound h.1, okC_sound h.2⟩
  | .ite b c d, h => by
    simp only [okC, Bool.and_eq_true] at h; exact ⟨okE_sound h.1.1, okC_sound h.1.2, okC_sound h.2⟩
  | .while b c, h => by
    simp only [okC, Bool.and_eq_true] at h; exact ⟨okE_sound h.1, okC_sound h.2⟩
  | .read x, h => by simpa [okC, Com.Ok] using h
  | .write e, h => by
    simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at h; exact ⟨okE_sound h.1, h.2⟩

theorem satLit_okC (z : String) (hz : gLayout.scalars.contains z = true) :
    ∀ n, okC gLayout (satLit z n) = true := by
  have hz' : z ∈ gLayout.scalars := List.contains_iff_mem.mp hz
  have hW : "W" ∈ gLayout.scalars := by decide
  have ht : 0 < gLayout.temps := by decide
  have h1 : okC gLayout (satAdd z z z) = true := by simp [satAdd, okC, okE, condExpr, hz', hW, ht]
  have h2 : okC gLayout (satInc z) = true := by simp [satInc, okC, okE, condExpr, hz', hW, ht]
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [satLit]
    split_ifs with h3 h4
    · simp [okC, okE, hz']
    · simp only [okC, Bool.and_eq_true]; exact ⟨ih _ (by omega), h1, h2⟩
    · simp only [okC, Bool.and_eq_true]; exact ⟨ih _ (by omega), h1, trivial⟩

theorem guardChk_okC (e d : ℕ) : okC gLayout (guardChk e d) = true := by
  simp only [guardChk, okC, Bool.and_eq_true, satLit_okC "oe" (by decide), satLit_okC "oc" (by decide),
    true_and, and_true]
  decide

theorem glueCmd_ok (eR eS eC d : ℕ) : Com.Ok gLayout (glueCmd eR eS eC d) := by
  apply okC_sound
  simp only [glueCmd, seqs, guardQ, roundTest, okC, Bool.and_eq_true, guardChk_okC, true_and, and_true]
  decide

theorem guardBits_gLayout : guardBits gLayout = 113 := rfl

end Lax185574Proofs.CompRam
