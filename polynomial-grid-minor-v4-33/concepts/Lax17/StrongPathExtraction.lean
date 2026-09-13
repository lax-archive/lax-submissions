import Lax17.PathOfSets
import Lax17.TreeOfSets

/-!
---
title: Strong path extraction
type: theorem
---
An ordered path in the meta-tree of a strong tree-of-sets system yields a
strong path-of-sets system on its internal clusters.
-/

namespace Lax17.StrongPathExtraction

universe u

/-- An ordered meta-tree path yields a strong path-of-sets system on its
internal clusters. -/
axiom strongPathExtraction :
  ∀ {V : Type u} [DecidableEq V] {G : SimpleGraph V}
    {m w ℓ : ℕ} (T : Lax17.TreeOfSets.StrongSystem G m w),
      0 < ℓ →
        Lax17.TreeOfSets.HasMetaPath T (ℓ + 2) →
          Nonempty (Lax17.PathOfSets.StrongSystem G ℓ w)

end Lax17.StrongPathExtraction
