import Lax17.Minor
import Lax17.Treewidth

/-!
---
title: Treewidth monotonicity under graph minors
type: theorem
---
Taking a graph minor cannot increase treewidth.
-/

namespace Lax17.TreewidthMinorMonotonicity

universe u

/-- Taking a graph minor cannot increase treewidth. -/
axiom treewidth_mono_minor :
  ∀ {V W : Type u} [Fintype V] [DecidableEq V]
    [Fintype W] [DecidableEq W]
    (G : SimpleGraph V) (H : SimpleGraph W),
      Lax17.Minor.IsMinor H G →
        Lax17.Treewidth.treewidth H ≤ Lax17.Treewidth.treewidth G

end Lax17.TreewidthMinorMonotonicity
