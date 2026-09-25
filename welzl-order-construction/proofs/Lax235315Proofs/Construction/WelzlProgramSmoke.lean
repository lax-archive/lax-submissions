import Lax235315Proofs.Construction.WelzlProgram
import Lax808846Proofs.Lib.Basic

/-! Executable smoke checks for the compiled program's deterministic branch. -/

namespace Lax235315Proofs.Construction.WelzlProgramSmoke

open Lax808846.Ram
open Lax235315Proofs.Construction.WelzlProgram

def test (x : List ℕ) : Option (List ℕ × ℕ) :=
  Lax808846Proofs.Reasoning.Lib.runOut 16 100000 welzlProgram (initState x) 0

#guard (test [1, 0, 0, 0]).map Prod.fst = some []
#guard (test [1, 1, 0, 0, 0]).map Prod.fst = some [0]
#guard (test [1, 2, 0, 0, 0, 0]).map Prod.fst = some [0, 1]

end Lax235315Proofs.Construction.WelzlProgramSmoke
