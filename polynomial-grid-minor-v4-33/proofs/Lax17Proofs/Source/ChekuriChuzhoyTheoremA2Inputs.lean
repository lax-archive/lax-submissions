import Lax17Proofs.Source.RoutableSetFromNodeWellLinkedProducer
import Lax17Proofs.Source.CutWellLinkedCoreProducer
import Lax17Proofs.Source.ChekuriChuzhoyTheorem46
import Lax17Proofs.Source.ChekuriChuzhoyTheorem221

namespace Lax17Proofs

universe u v w

/-!
# Closed source inputs for Chekuri--Chuzhoy Theorem A.2

This module is the package-level endpoint for WP1.  It combines the proved
Lemma 2.17 route, the routed cut-matching construction, the accepted
`m^24` Section 4 strong-tree construction, and the source-faithful DFS proof
of Theorem 4.6.  The corresponding path threshold is `ell^50`.
-/

namespace SimpleGraph
namespace ChekuriChuzhoy


/-- All four proof-producing components of the expanded A.2 boundary. -/
theorem theoremA2LeafSourceInputs_proved :
    TheoremA2LeafSourceInputs.{u} :=
  ⟨exists_routableSetFromTreewidth_proved,
    exists_cutWellLinkedCoreFromRoutableSet_proved,
    exists_strongTreeOfSetsCoreFromNodeWellLinkedCore_proved,
    strongPathOfSetsFromLeafyStrongTreeOfSets_proved⟩

/-- WP1 acceptance endpoint: Chekuri--Chuzhoy A.2 source inputs with no
project axiom in their transitive closure. -/
theorem theoremA2SourceInputs_proved :
    TheoremA2SourceInputs.{u} :=
  theoremA2SourceInputs_of_leafSourceInputs
    theoremA2LeafSourceInputs_proved

end ChekuriChuzhoy
end SimpleGraph

end Lax17Proofs
