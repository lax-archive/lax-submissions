import Lax235315Proofs.Construction.WelzlProgram

/-! The compiled construction is a witness used by the proof package. -/

namespace Lax235315Proofs.ProofProgram

open Lax808846.Ram

/-- The fixed word-RAM witness obtained by compiling the readable source. -/
def program : Program :=
  Lax235315Proofs.Construction.WelzlProgram.welzlProgram

/-- The compiled address of the source program's success flag. -/
def successFlagCell : ℕ :=
  Lax235315Proofs.Construction.WelzlProgram.layout.varAddr "good"

end Lax235315Proofs.ProofProgram
