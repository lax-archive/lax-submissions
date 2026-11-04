import Lax185574.CanonicalForm
import Lax185574Proofs.Interface.Poly

/-!
The statement of `Lax185574.CanonicalForm` for the older notion
`Lax185574.Computing.Computes`, derived from the concept.
-/

namespace Lax185574Proofs.Shim.CanonicalForm

open Lax808846.Ram Lax185574.Encoding Lax185574.Computing Lax185574.TypeTrees
open Lax185574Proofs.Interface

theorem exists_program_canonical :
    ∃ (p : Program) (e c a : ℕ),
      ∀ (α : Type) [Encode α] (l : List α),
        Computes p e c (l.map encode) (finsetOf {x | x ∈ l}) (fun m => c * (m + 1) ^ a) := by
  obtain ⟨A, c, a, h⟩ := Lax185574.CanonicalForm.exists_program_canonical
  refine ⟨A.program, 2 * A.wordExponent, c, a + 1, fun α _ l => ?_⟩
  classical
  rw [finsetOf_list]
  exact poly_of_computes rfl (List.cons_ne_nil _ _) (h α l)

end Lax185574Proofs.Shim.CanonicalForm
