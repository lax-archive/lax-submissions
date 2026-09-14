import Lax68.Ladders
import Lax68.SeriesParallel

/-!
---
title: Ladders are series-parallel
type: theorem
---
Every ladder graph is series-parallel.

Open in this formalization: no proof is supplied yet.
-/

set_option autoImplicit false

namespace Lax68.LadderSeriesParallel

/-- Every ladder graph is series-parallel.

Open in this formalization: no proof is supplied yet. -/
axiom ladder_seriesParallel {V : Type*} {G : SimpleGraph V} :
  Lax68.Ladders.IsLadder G →
  Lax68.SeriesParallel.IsSeriesParallel G

end Lax68.LadderSeriesParallel
