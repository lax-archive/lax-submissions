import Lax185574.ModelChecking
import Lax185574Proofs.Interface.Headline
import Lax185574Proofs.MainRam.Final
import Lax185574Proofs.MainRam.Unpair
import Lax185574Proofs.MainRam.Clip
import Lax185574Proofs.MainRam.Wrap
import Lax185574Proofs.MainRam.Validate

/-!
Proof of thm:main from thm:skel-few-types and thm:mc.
-/

namespace Lax185574Proofs.ModelChecking

open Lax185574Proofs.MainRam Lax185574Proofs.Interface
open Lax185574.Graphs Lax185574.FirstOrderLogic Lax185574.MonadicDependence
open Lax185574.Algorithms

/-- thm:main for programs reading a graph in compressed sparse row form.
The program dovetails over the threads `i ↦ (r, d, j)`. Thread `i` runs
the program of thm:skel-few-types with radius `r`, depth `d` and
`ε = 1/j` on the graph, clips and validates the computed word as a
construction script of the graph, runs the program of thm:mc on the
validated instance, and accepts with the answer when the validation
succeeded. For a class, a sentence and `ε`, the good thread uses the
`r, d` of thm:mc and a `j` with `a (b + 1) / j ≤ min ε 1`, where `a`
comes from thm:skel-few-types and `b` from thm:mc. It accepts within
`O(n^(3+ε) + |x|)` steps, and the dovetailer multiplies this by a
constant. The dovetailer answers with some accepting thread, which ran
within a polynomial of degree five in `|x|`. So its word length is large
enough for its run of thm:mc to be admissible, and its answer is right. -/
theorem exists_program_modelChecking_csr : OldHeadline :=
  modelChecking_of_glue unpairSpec clipSpec validSpec wrapSpec

/--
---
conclusion: Lax185574.ModelChecking.exists_program_modelChecking
---
The proof of the main theorem. The algorithm converts the word of the
graph into its compressed sparse row form and runs the program of
`exists_program_modelChecking_csr` on it. The conversion takes time
linear in the length of the input, which is `O(n²)`.
-/
theorem exists_program_modelChecking :
    ∃ A : Algorithm, ∀ C : GraphClass, MonadicallyDependent C →
      ∀ (φ : Sentence) (ε : ℝ), 0 < ε → ∃ c : ℕ,
        ∀ G ∈ C, A.Decides c (G, φ) (G ⊨ φ) ((G.n : ℝ) ^ (3 + ε)) :=
  modelChecking_of_old exists_program_modelChecking_csr

end Lax185574Proofs.ModelChecking
