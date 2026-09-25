import Lax235315.ConstructionProgram
import Lax235315Proofs.Construction.WelzlProgram

namespace Lax235315Proofs.ProgramLink

set_option maxRecDepth 50000 in
set_option maxHeartbeats 2000000 in
/-- The reviewable fixed instruction sequence is exactly the compiled source. -/
theorem program_eq_compilation :
    Lax235315.ConstructionProgram.program =
      Lax235315Proofs.Construction.WelzlProgram.welzlProgram := by rfl

/-- The designated success cell is the source layout's actual `good` cell. -/
theorem successFlagCell_eq :
    Lax235315.ConstructionProgram.successFlagCell =
      Lax235315Proofs.Construction.WelzlProgram.layout.varAddr "good" := by rfl

end Lax235315Proofs.ProgramLink
