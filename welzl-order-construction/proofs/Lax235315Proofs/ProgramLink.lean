import Lax235315Proofs.ProofProgram
import Lax235315Proofs.Construction.WelzlProgram

namespace Lax235315Proofs.ProgramLink

set_option maxRecDepth 50000 in
set_option maxHeartbeats 2000000 in
/-- The proof-local program witness is exactly the compiled source. -/
lemma program_eq_compilation :
    Lax235315Proofs.ProofProgram.program =
      Lax235315Proofs.Construction.WelzlProgram.welzlProgram := by rfl

/-- The designated success cell is the source layout's actual `good` cell. -/
lemma successFlagCell_eq :
    Lax235315Proofs.ProofProgram.successFlagCell =
      Lax235315Proofs.Construction.WelzlProgram.layout.varAddr "good" := by rfl

end Lax235315Proofs.ProgramLink
