import Lax808846Proofs.Frame

/-!
The concrete IMP+ implementation of Figure 1.  Randomness is read as bits
after the CSR word.  Eight `clog₂ n`-bit radix digits are attached to every
active ground vertex; in the collision-free case their lexicographic order
induces a uniform random ordering of the active set.
-/

namespace Lax235315Proofs.Construction.WelzlProgram

open Lax808846.Ram
open Lax808846Proofs.Imp
open Lax808846Proofs.Compile

/-- Right-associated sequencing, used only to keep the source readable. -/
def seqs : List Com → Com
  | [] => .skip
  | [c] => c
  | c :: d :: cs => .seq c (seqs (d :: cs))

def inc (x : String) : Com :=
  .assign x (.add (.var x) (.lit 1))

def clearArray (a lim : String) : Com :=
  seqs [
    .assign "i" (.lit 0),
    .while (.lt (.var "i") (.var lim)) <|
      seqs [.store a (.var "i") (.lit 0), inc "i"]]

/-- Read `lim` words into an array. -/
def readArray (a lim : String) : Com :=
  seqs [
    .assign "i" (.lit 0),
    .while (.lt (.var "i") (.var lim)) <|
      seqs [.read "tmp", .store a (.var "i") (.var "tmp"), inc "i"]]

/-- Read one `L`-bit, most-significant-bit-first key digit for vertex `v`. -/
def readKeyDigit (key : String) : Com :=
  seqs [
    .assign "digit" (.lit 0),
    .assign "j" (.lit 0),
    .while (.lt (.var "j") (.var "L")) <|
      seqs [
        .read "bit",
        .assign "digit" (.add (.mul (.var "digit") (.lit 2)) (.var "bit")),
        inc "j"],
    .store key (.var "v") (.var "digit")]

def keyNames : List String :=
  ["key0", "key1", "key2", "key3", "key4", "key5", "key6", "key7"]

def readAllKeyDigits : Com :=
  seqs (keyNames.map readKeyDigit)

/-- Collect the active vertices and read their eight key digits. -/
def readKeys : Com :=
  seqs [
    .assign "alen" (.lit 0),
    .assign "v" (.lit 0),
    .while (.lt (.var "v") (.var "n")) <|
      seqs [
        .ite (.eq (.get "activeA" (.var "v")) (.lit 1))
          (seqs [.store "ord" (.var "alen") (.var "v"),
            readAllKeyDigits, inc "alen"])
          .skip,
        inc "v"]]

/-- One stable counting-sort pass on a key digit. -/
def radixPass (key : String) : Com :=
  seqs [
    clearArray "count" "qpow",
    seqs [
      .assign "i" (.lit 0),
      .while (.lt (.var "i") (.var "alen")) <|
        seqs [
          .assign "v" (.get "ord" (.var "i")),
          .assign "digit" (.get key (.var "v")),
          .store "count" (.var "digit")
            (.add (.get "count" (.var "digit")) (.lit 1)),
          inc "i"]],
    seqs [
      .assign "sum" (.lit 0),
      .assign "digit" (.lit 0),
      .while (.lt (.var "digit") (.var "qpow")) <|
        seqs [
          .assign "tmp" (.get "count" (.var "digit")),
          .store "count" (.var "digit") (.var "sum"),
          .assign "sum" (.add (.var "sum") (.var "tmp")),
          inc "digit"]],
    seqs [
      .assign "i" (.lit 0),
      .while (.lt (.var "i") (.var "alen")) <|
        seqs [
          .assign "v" (.get "ord" (.var "i")),
          .assign "digit" (.get key (.var "v")),
          .assign "pos" (.get "count" (.var "digit")),
          .store "scratchOrder" (.var "pos") (.var "v"),
          .store "count" (.var "digit") (.add (.var "pos") (.lit 1)),
          inc "i"]],
    seqs [
      .assign "i" (.lit 0),
      .while (.lt (.var "i") (.var "alen")) <|
        seqs [
          .store "ord" (.var "i") (.get "scratchOrder" (.var "i")),
          inc "i"]]]

/-- Set `collision` when the two vertices currently named by `left` and
`right` have equal eight-digit keys. -/
def checkAllDigitsEqual : List String → Com
  | [] => .assign "collision" (.lit 1)
  | key :: keys =>
      .ite (.eq (.get key (.var "left")) (.get key (.var "right")))
        (checkAllDigitsEqual keys) .skip

def detectCollision : Com :=
  seqs [
    .assign "collision" (.lit 0),
    .assign "i" (.lit 1),
    .while (.lt (.var "i") (.var "alen")) <|
      seqs [
        .assign "left" (.get "ord" (.sub (.var "i") (.lit 1))),
        .assign "right" (.get "ord" (.var "i")),
        checkAllDigitsEqual keyNames,
        inc "i"]]

/-- Initialize one trace refinement with a single class.  The active side is
known to be nonempty whenever this routine is called. -/
def initPartition (active cls : String) : Com :=
  seqs [
    clearArray "classSize" "n",
    clearArray "markedCount" "n",
    clearArray "stamp" "n",
    .assign "v" (.lit 0),
    .assign "vcount" (.lit 0),
    .while (.lt (.var "v") (.var "n")) <|
      seqs [
        .ite (.eq (.get active (.var "v")) (.lit 1))
          (seqs [.store cls (.var "v") (.lit 0), inc "vcount"])
          .skip,
        inc "v"],
    .store "classSize" (.lit 0) (.var "vcount"),
    .assign "classCount" (.lit 1)]

/-- Refine all current classes by adjacency to the test vertex `t`.  Duplicate
CSR entries are discarded by `stamp`. -/
def refineMarkBody (active cls : String) : Com :=
  seqs [
    .assign "v" (.get "tgt" (.var "j")),
    .ite (.eq (.get active (.var "v")) (.lit 1))
      (.ite (.eq (.get "stamp" (.var "v")) (.var "token")) .skip
        (seqs [
          .store "stamp" (.var "v") (.var "token"),
          .store "marked" (.var "markedLen") (.var "v"),
          inc "markedLen",
          .assign "cl" (.get cls (.var "v")),
          .ite (.eq (.get "markedCount" (.var "cl")) (.lit 0))
            (seqs [.store "touched" (.var "touchedLen") (.var "cl"),
              inc "touchedLen"])
            .skip,
          .store "markedCount" (.var "cl")
            (.add (.get "markedCount" (.var "cl")) (.lit 1))]))
      .skip,
    inc "j"]

/-- Refine all current classes by adjacency to the test vertex `t`.  Duplicate
CSR entries are discarded by `stamp`. -/
def refineOne (active cls : String) : Com :=
  seqs [
    .assign "markedLen" (.lit 0),
    .assign "touchedLen" (.lit 0),
    .assign "j" (.get "off" (.var "t")),
    .assign "jend" (.get "off" (.add (.var "t") (.lit 1))),
    .while (.lt (.var "j") (.var "jend")) <|
      refineMarkBody active cls,
    .assign "i" (.lit 0),
    .while (.lt (.var "i") (.var "touchedLen")) <|
      seqs [
        .assign "cl" (.get "touched" (.var "i")),
        .ite (.lt (.get "markedCount" (.var "cl"))
            (.get "classSize" (.var "cl")))
          (seqs [
            .store "split" (.var "cl") (.var "classCount"),
            .store "classSize" (.var "classCount")
              (.get "markedCount" (.var "cl")),
            .store "classSize" (.var "cl")
              (.sub (.get "classSize" (.var "cl"))
                (.get "markedCount" (.var "cl"))),
            inc "classCount"])
          (.store "split" (.var "cl") (.var "cl")),
        inc "i"],
    .assign "i" (.lit 0),
    .while (.lt (.var "i") (.var "markedLen")) <|
      seqs [
        .assign "v" (.get "marked" (.var "i")),
        .assign "cl" (.get cls (.var "v")),
        .store cls (.var "v") (.get "split" (.var "cl")),
        inc "i"],
    .assign "i" (.lit 0),
    .while (.lt (.var "i") (.var "touchedLen")) <|
      seqs [
        .assign "cl" (.get "touched" (.var "i")),
        .store "markedCount" (.var "cl") (.lit 0),
        inc "i"]]

/-- Refine `active` using the first `testCount` entries of `tests`, select the
least vertex of every final class, and fill both the representative map and
the active representative side. -/
def partition (active tests testCount cls reps activeOut repOf outCount : String) : Com :=
  seqs [
    initPartition active cls,
    .assign "ti" (.lit 0),
    .while (.lt (.var "ti") (.var testCount)) <|
      seqs [
        .assign "token" (.add (.var "ti") (.lit 1)),
        .assign "t" (.get tests (.var "ti")),
        refineOne active cls,
        inc "ti"],
    clearArray activeOut "n",
    .assign "i" (.lit 0),
    .while (.lt (.var "i") (.var "n")) <|
      seqs [.store "repClass" (.var "i") (.var "n"), inc "i"],
    .assign outCount (.lit 0),
    .assign "v" (.lit 0),
    .while (.lt (.var "v") (.var "n")) <|
      seqs [
        .ite (.eq (.get active (.var "v")) (.lit 1))
          (seqs [
            .assign "cl" (.get cls (.var "v")),
            .ite (.eq (.get "repClass" (.var "cl")) (.var "n"))
              (seqs [
                .store "repClass" (.var "cl") (.var "v"),
                .store reps (.var outCount) (.var "v"),
                .store activeOut (.var "v") (.lit 1),
                inc outCount])
              .skip])
          .skip,
        inc "v"],
    .assign "v" (.lit 0),
    .while (.lt (.var "v") (.var "n")) <|
      seqs [
        .ite (.eq (.get active (.var "v")) (.lit 1))
          (seqs [
            .assign "cl" (.get cls (.var "v")),
            .store repOf (.var "v") (.get "repClass" (.var "cl"))])
          .skip,
        inc "v"]]

/-- One duplicate-tolerant CSR step of the batched near-twin verifier. -/
def collectNeighborBody : Com :=
  seqs [
    .assign "b" (.get "tgt" (.var "j")),
    .ite (.eq (.get "activeB" (.var "b")) (.lit 1))
      (.ite (.eq (.get "stamp" (.var "b")) (.var "token")) .skip
        (seqs [
          .store "stamp" (.var "b") (.var "token"),
          .store "neighbors" (.var "neighborLen") (.var "b"),
          inc "neighborLen"]))
      .skip,
    inc "j"]

/-- Account for one distinct active `B`-neighbor of the current `a`. -/
def accumulateNearBody : Com :=
  seqs [
    .assign "b" (.get "neighbors" (.var "i")),
    .store "degree" (.var "b")
      (.add (.get "degree" (.var "b")) (.lit 1)),
    .assign "r" (.get "repB" (.var "b")),
    .ite (.eq (.get "stamp" (.var "r")) (.var "token"))
      (.store "inter" (.var "b")
        (.add (.get "inter" (.var "b")) (.lit 1)))
      .skip,
    inc "i"]

/-- Check the completed symmetric-difference count for one `B` vertex. -/
def checkNearBody : Com :=
  seqs [
    .ite (.eq (.get "activeB" (.var "b")) (.lit 1))
      (seqs [
        .assign "r" (.get "repB" (.var "b")),
        .assign "diff"
          (.sub (.add (.get "degree" (.var "b"))
              (.get "degree" (.var "r")))
            (.mul (.lit 2) (.get "inter" (.var "b")))),
        .ite (.lt (.var "nearBound") (.var "diff"))
          (.assign "good" (.lit 0)) .skip])
      .skip,
    inc "b"]

/-- Process one active `A` vertex in the batched near-twin verifier. -/
def processActiveNearBody : Com :=
  seqs [
    .assign "token" (.add (.var "a") (.lit 1)),
    .assign "neighborLen" (.lit 0),
    .assign "j" (.get "off" (.var "a")),
    .assign "jend" (.get "off" (.add (.var "a") (.lit 1))),
    .while (.lt (.var "j") (.var "jend")) collectNeighborBody,
    .assign "i" (.lit 0),
    .while (.lt (.var "i") (.var "neighborLen")) accumulateNearBody]

/-- One iteration of the outer batched CSR sweep. -/
def sweepNearBody : Com :=
  seqs [
    .ite (.eq (.get "activeA" (.var "a")) (.lit 1))
      processActiveNearBody .skip,
    inc "a"]

/-- Clear the batched verifier counters and reset its outer sweep. -/
def prepareNearSweep : Com :=
  seqs [
    clearArray "degree" "n",
    clearArray "inter" "n",
    clearArray "stamp" "n",
    .assign "a" (.lit 0)]

/-- Scan the completed counters and clear `good` on a failed check. -/
def finishNearCheck : Com :=
  seqs [
    .assign "b" (.lit 0),
    .while (.lt (.var "b") (.var "n")) checkNearBody]

/-- Compute all distances on the current active ground set between vertices
of `B` and their chosen representatives in one batched CSR scan. -/
def verifyNear : Com :=
  seqs [
    prepareNearSweep,
    .while (.lt (.var "a") (.var "n")) sweepNearBody,
    finishNearCheck]

/-- Record, in increasing vertex order, the ground vertices removed by one
accepted reduction and their chosen representatives. -/
def recordRemoved : Com :=
  seqs [
    .store "roundStart" (.var "round") (.var "removedCount"),
    .assign "v" (.lit 0),
    .while (.lt (.var "v") (.var "n")) <|
      seqs [
        .ite (.eq (.get "activeA" (.var "v")) (.lit 1))
          (.ite (.eq (.get "nextA" (.var "v")) (.lit 0))
            (seqs [
              .store "removed" (.var "removedCount") (.var "v"),
              .store "removedRep" (.var "removedCount")
                (.get "repA" (.var "v")),
              inc "removedCount"])
            .skip)
          .skip,
        inc "v"]]

/-- Replace both active-side indicators by the representatives selected for
the next round. -/
def adoptNext : Com :=
  seqs [
    .assign "v" (.lit 0),
    .while (.lt (.var "v") (.var "n")) <|
      seqs [
        .store "activeA" (.var "v") (.get "nextA" (.var "v")),
        .store "activeB" (.var "v") (.get "nextB" (.var "v")),
        inc "v"]]

/-- Commit one accepted reduction and record the ground-side twin insertions
needed during reconstruction. -/
def commitReduction : Com :=
  seqs [
    recordRemoved,
    adoptNext,
    .store "roundEnd" (.var "round") (.var "removedCount"),
    .assign "acount" (.var "nextACount"),
    inc "round"]

/-- Compute the paper's ceiling sample size from the current active count. -/
def prepareSampleCount : Com :=
  seqs [
    .assign "denom" (.mul (.lit 2) (.var "csq")),
    .assign "sampleCount" (.div (.var "acount") (.var "denom")),
    .assign "rem" (.sub (.var "acount")
      (.mul (.var "sampleCount") (.var "denom"))),
    .ite (.eq (.var "rem") (.lit 0)) .skip (inc "sampleCount")]

/-- Build both trace partitions and verify the near-twin condition in a
collision-free reduction round. -/
def buildReductionCertificate : Com :=
  .seq
    (.seq prepareSampleCount
      (partition "activeB" "ord" "sampleCount" "classB"
        "repsB" "nextB" "repB" "nextBCount"))
    (.seq
      (partition "activeA" "repsB" "nextBCount" "classA"
        "repsA" "nextA" "repA" "nextACount")
      verifyNear)

/-- One random reduction round. -/
def reductionRound : Com :=
  seqs [
    readKeys,
    seqs ((keyNames.reverse).map radixPass),
    detectCollision,
    .ite (.eq (.var "collision") (.lit 0))
      (seqs [
        buildReductionCertificate,
        .ite (.eq (.var "good") (.lit 1)) commitReduction
          (.assign "acount" (.lit 0))])
      (seqs [.assign "good" (.lit 0), .assign "acount" (.lit 0)])]

def initActive : Com :=
  .seq
    (seqs [
      .assign "v" (.lit 0),
      .while (.lt (.var "v") (.var "n")) <|
        seqs [
          .store "activeA" (.var "v") (.lit 1),
          .store "activeB" (.var "v") (.lit 1),
          inc "v"]])
    (.assign "acount" (.var "n"))

def writeNaturalOrder : Com :=
  seqs [
    .assign "v" (.lit 0),
    .while (.lt (.var "v") (.var "n")) <|
      seqs [.write (.var "v"), inc "v"]]

/-- Compute `L = ⌈log₂ n⌉` and `qpow = 2^L`. -/
def computeLog : Com :=
  seqs [
    .assign "L" (.lit 0), .assign "qpow" (.lit 1),
    .while (.lt (.var "qpow") (.var "n")) <|
      seqs [.assign "qpow" (.mul (.var "qpow") (.lit 2)), inc "L"]]

/-- Build the base list and undo all accepted reductions using constant-time
linked-list insertions. -/
def reconstructAndWrite : Com :=
  seqs [
    .assign "head" (.var "n"),
    .assign "last" (.var "n"),
    .assign "v" (.lit 0),
    .while (.lt (.var "v") (.var "n")) <|
      seqs [
        .ite (.eq (.get "activeA" (.var "v")) (.lit 1))
          (.ite (.eq (.var "last") (.var "n"))
            (.assign "head" (.var "v"))
            (.store "nextVertex" (.var "last") (.var "v")))
          .skip,
        .ite (.eq (.get "activeA" (.var "v")) (.lit 1))
          (.assign "last" (.var "v")) .skip,
        inc "v"],
    .while (.lt (.lit 0) (.var "round")) <|
      seqs [
        .assign "round" (.sub (.var "round") (.lit 1)),
        .assign "i" (.get "roundStart" (.var "round")),
        .assign "iend" (.get "roundEnd" (.var "round")),
        .while (.lt (.var "i") (.var "iend")) <|
          seqs [
            .assign "v" (.get "removed" (.var "i")),
            .assign "r" (.get "removedRep" (.var "i")),
            .store "nextVertex" (.var "v") (.get "nextVertex" (.var "r")),
            .store "nextVertex" (.var "r") (.var "v"),
            inc "i"]],
    .assign "i" (.lit 0),
    .assign "v" (.var "head"),
    .while (.lt (.var "i") (.var "n")) <|
      seqs [
        .write (.var "v"),
        .assign "v" (.get "nextVertex" (.var "v")),
        inc "i"]]

/-- Read the deterministic parameter and CSR prefix. -/
def readGraph : Com :=
  seqs [
    .read "c", .read "n", .read "m",
    .assign "len" (.add (.var "n") (.lit 1)), readArray "off" "len",
    .assign "len" (.mul (.lit 2) (.var "m")), readArray "tgt" "len"]

/-- Initialize the logarithm, active sides, and reconstruction counters. -/
def initializeWelzl : Com :=
  seqs [computeLog, initActive,
    .assign "good" (.lit 1), .assign "round" (.lit 0),
    .assign "removedCount" (.lit 0)]

/-- Read the deterministic prefix and initialize the two active sides. -/
def setup : Com := seqs [readGraph, initializeWelzl]

/-- Guarded randomized phase.  The guards keep products involving `c²`
inside the linear word bound. -/
def reduceAll : Com :=
  .ite (.lt (.var "n") (.lit 2)) .skip
    (.ite (.eq (.var "c") (.lit 0)) (.assign "good" (.lit 0))
      (.ite (.lt (.div (.var "n") (.var "c")) (.var "c")) .skip
        (seqs [
          .assign "csq" (.mul (.var "c") (.var "c")),
          .ite (.lt (.div (.var "n") (.var "csq"))
              (.mul (.lit 12) (.var "L"))) .skip
            (seqs [
              .assign "threshold"
                (.mul (.mul (.lit 12) (.var "csq")) (.var "L")),
              .assign "nearBound" (.div (.var "threshold") (.lit 2)),
              .while (.lt (.var "threshold") (.var "acount"))
                reductionRound])])))

def finish : Com :=
  .ite (.eq (.var "good") (.lit 1)) reconstructAndWrite writeNaturalOrder

/-- Complete source program. Products involving `c²` are guarded before they
are evaluated, so every unbounded-semantics value remains linear in the CSR
word length. -/
def welzlCom : Com :=
  seqs [setup, reduceAll, finish]

def scalarNames : List String :=
  ["c", "n", "m", "len", "i", "iend", "j", "jend", "tmp", "v", "a", "b",
   "r", "t", "ti", "bit", "digit", "L", "qpow", "alen", "sum", "pos",
   "left", "right", "collision", "vcount", "classCount", "markedLen",
   "touchedLen", "token", "cl", "neighborLen", "diff", "good", "round",
   "removedCount", "acount", "nextACount", "nextBCount", "denom",
   "sampleCount", "rem", "csq", "threshold", "nearBound", "head", "last"]

def arrayNames : List String :=
  ["off", "tgt", "activeA", "activeB", "nextA", "nextB", "classA", "classB",
   "repsA", "repsB", "repA", "repB", "classSize", "markedCount", "stamp",
   "marked", "touched", "split", "repClass", "ord", "scratchOrder", "count",
   "degree", "inter", "neighbors", "roundStart", "roundEnd", "removed",
   "removedRep", "nextVertex"] ++ keyNames

/-- The deepest generated expression uses four compiler temporaries. -/
def layout : Layout := ⟨scalarNames, arrayNames, 4⟩

def welzlProgram : Program := compileProgram layout welzlCom

/-- Every variable and array used by the generated source is present in its
layout, and four temporary cells cover its deepest expression. -/
theorem welzlCom_ok : Com.Ok layout welzlCom := by
  simp [welzlCom, finish, reduceAll, setup, initializeWelzl, readGraph, computeLog,
    reductionRound, buildReductionCertificate, prepareSampleCount,
    reconstructAndWrite, writeNaturalOrder,
    initActive, commitReduction, recordRemoved, adoptNext, verifyNear,
    prepareNearSweep, finishNearCheck,
    sweepNearBody,
    processActiveNearBody, checkNearBody, accumulateNearBody,
    collectNeighborBody, partition, refineOne,
    initPartition, refineMarkBody, detectCollision, checkAllDigitsEqual, radixPass, readKeys,
    readAllKeyDigits, keyNames, readKeyDigit, readArray, clearArray, inc, seqs, layout,
    scalarNames, arrayNames, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

end Lax235315Proofs.Construction.WelzlProgram
