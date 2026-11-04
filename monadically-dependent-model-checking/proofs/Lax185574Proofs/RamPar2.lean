import Lax185574Proofs.RamParRun
import Lax185574Proofs.MC.Asm.Defs

/-!
The parallel combinator of `RamParRun` meets the interface `Par2Spec`
of the assembly of thm:mc.
-/

namespace Lax185574Proofs.MC

/-- **Two threads in parallel.** -/
theorem par2_spec : ∃ par K, Par2Spec par K :=
  ⟨Lax185574Proofs.RamPar.parProg Lax185574Proofs.RamPar.parK, Lax185574Proofs.RamPar.parK,
    fun P₀ P₁ w x hw hx => Lax185574Proofs.RamPar.par_spec P₀ P₁ w x hw hx⟩

end Lax185574Proofs.MC
