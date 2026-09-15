import Lax68.SeriesParallel
import Lax68.Planar

/-!
---
title: Series-parallel graphs are planar
type: opn
---
Every series-parallel graph is planar.

Open in this formalization: no proof is supplied yet.
-/

set_option autoImplicit false

namespace Lax68.SeriesParallelPlanar

/-- Every series-parallel graph is planar.

Open in this formalization: no proof is supplied yet. -/
axiom seriesParallel_planar {V : Type*} {G : SimpleGraph V} :
  Lax68.SeriesParallel.IsSeriesParallel G →
  Lax68.Planar.IsPlanar G

end Lax68.SeriesParallelPlanar
