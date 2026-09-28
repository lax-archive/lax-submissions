import Mathlib.Combinatorics.Graph.Delete

namespace Lax303502Proofs

/-- The underlying multigraph type for the plane-topology development. -/
abbrev Graph (α β : Type*) := _root_.Graph α β

namespace Graph

abbrev deleteEdges {α β : Type*} (G : Graph α β) (F : Set β) : Graph α β :=
  _root_.Graph.deleteEdges G F

abbrev deleteVerts {α β : Type*} (G : Graph α β) (X : Set α) : Graph α β :=
  _root_.Graph.deleteVerts G X

end Graph
end Lax303502Proofs
