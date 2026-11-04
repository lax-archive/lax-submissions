import Lax185574Proofs.ResolveRam.Glue.CUpA
import Lax185574Proofs.ResolveRam.Glue.CUpO
import Lax185574Proofs.ResolveRam.Glue.CFinU
import Lax185574Proofs.ResolveRam.Glue.CFinL
import Lax185574Proofs.ResolveRam.Glue.CFinFt
import Lax185574Proofs.ResolveRam.Glue.CShift
import Lax185574Proofs.ResolveRam.Glue.CComp

/-!
The commands of the end of an item on the way up and of the dispatcher of
a later round of the glue program of lem:resolve-lift.

`bUpB atC` appends the output word of an item to the outputs and writes
the query of the atom words of the next item. `dUpE atC` ends the phase
(`Nph := 3`) after the last item and runs `bUpB atC` otherwise. The
dispatcher `disp atC bR1` reads the phase, the call number, the level and
the item of the current position from the head and runs the case of the
position.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam Lax185574Proofs.TreeAlgo

/-- The next item in the same level. -/
def nxA : List (String × Expr) :=
  [("Nd", .var "dd"), ("Ni", .add (.var "ii") (.lit 1)),
    ("ow", .add (.add (.add (.add (.lit 4) (.var "nSG")) (.var "oL")) (.var "ii")) (.lit 1)), ("e0", .lit 0)]

/-- The number of output words of the state. -/
def eOU : Expr := .sub (.sub (.sub (.var "m0") (.lit 4)) (.var "nSG")) (.var "nLV")

/-- The first item of the level above. -/
def nxB : List (String × Expr) :=
  [("Nd", .sub (.var "dd") (.lit 1)), ("Ni", .lit 0),
    ("ow", .sub (.add (.add (.lit 4) (.var "nSG")) (.var "oL")) (eLL (.sub (.var "dd") (.lit 1)))),
    ("e0", .sub eOU (.var "ii"))]

/-- The scalars of the new head after an item on the way up. -/
def hdB : List (String × Expr) :=
  [("Nt", .lit 1), ("Nw", .lit 0), ("Nph", .lit 2), ("Nm", .lit 0), ("NSG", .var "nSG"), ("NFA", .lit 0),
    ("NCO", .lit 0), ("NLV", .var "nLV"), ("qk", .lit 3), ("po", .lit 0)]

/-- The plan `psUp`. -/
def plUp : List (Expr × Expr) :=
  [(.lit 0, .lit 2), (.var "m0", .lit 1), (.lit 3, .sub (.sub (.var "m0") (.lit 3)) eOU),
    (.add (.sub (.var "m0") eOU) (.var "e0"), .sub eOU (.var "e0")), (.add (.var "m0") (.lit 1), .lit 1)]

/-- The case after the last call of an item on the way up. -/
noncomputable def bUpB (atC : Com) : Com :=
  .seq (.assign "m0" (.var "m")) (.seq apE (.seq sumLL
    (.seq (.assign "ow" (.add (.add (.add (.lit 4) (.var "nSG")) (.var "oL")) (.var "ii")))
    (.seq (ouC plK dlK)
    (.seq (.ite (.lt (.add (.var "ii") (.lit 1)) (eLL (.var "dd"))) (asgs nxA) (asgs nxB))
    (.seq (asgs hdB) (.seq (winC (.eq (.var "gq") (.lit 0)) (.eq (.add (.var "Ni") (.lit 1)) (eLL (.lit 0))))
    (.seq (atT atC) (stPlan plUp)))))))))

/-- The end of an item on the way up: the end of the phase after the
last item, `bUpB` otherwise. -/
noncomputable def dUpE (atC : Com) : Com :=
  .ite (.eq (.var "dd") (.lit 0))
    (.ite (.eq (.var "ii") (.sub (eLL (.lit 0)) (.lit 1))) (asgs [("Nph", .lit 3)]) (bUpB atC))
    (bUpB atC)

/-- The dispatcher. -/
noncomputable def disp (atC bR1 : Com) : Com :=
  .ite (.eq (.var "ph") (.lit 0)) bR1
    (.ite (.eq (.var "ph") (.lit 1))
      (.ite (.eq (.var "mm") (.lit 0)) bShift
        (.ite (.eq (.var "mm") (.lit 1)) (bFt (fE atC))
          (.ite (.lt (.sub (.var "mm") (.lit 1)) (.var "nFA")) bComp (bLast atC))))
      (.ite (.eq (.var "mm") (.lit 0))
        (.ite (.lt (.var "dd") (.var "gq")) bUpA (dUpE atC))
        (dUpE atC)))

end Lax185574Proofs.ResolveRam.Glue
