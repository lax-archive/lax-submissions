-- The locality theorem of arXiv:2606.23180 and its normal form.
import Lax3Proofs.WalkDistance
import Lax3Proofs.Horizon
import Lax3Proofs.SyntaxLemmas
import Lax3Proofs.SemLocal
import Lax3Proofs.Clusters
import Lax3Proofs.ScatterCore
import Lax3Proofs.Separation
import Lax3Proofs.FarQuant
import Lax3Proofs.BCAlgebra
import Lax3Proofs.ScatterFml
import Lax3Proofs.Assembly

-- Plain first-order logic as an input to the distance-logic engine.
import Lax3Proofs.Reduction

-- The isolation splitter game and Splitter's win on nowhere dense classes.
import Lax3Proofs.SplitterBasics
import Lax3Proofs.SplitterMono
import Lax3Proofs.SplitterWin
import Lax3Proofs.SplitterWinRec
import Lax3Proofs.UqwInstantiation
import Lax3Proofs.ReachedS

-- Sparse neighborhood covers and the augmentation chain behind their degree.
import Lax3Proofs.CoverConstruction
import Lax3Proofs.Augmentation
import Lax3Proofs.AugmentedDensity
import Lax3Proofs.OrderedCovers
import Lax3Proofs.CoverDegree
import Lax3Proofs.ClusterPaths
import Lax3Proofs.CoverCentres
import Lax3Proofs.CoverEdgeSum
import Lax3Proofs.CoverSpec

-- The two rewrites a step of the recursion performs, and the leaf case.
import Lax3Proofs.Relativize
import Lax3Proofs.Isolate
import Lax3Proofs.BotEval
import Lax3Proofs.Compaction
import Lax3Proofs.LocalityFun

-- Machine-independent arithmetic the redesign's cost argument amends rather
-- than re-derives: the sigma recursion over the game tree with its n^(1+eps)
-- close, and the adjacency-slot bound a cover implementation must size to.
import Lax3Proofs.CostRecurrence
import Lax3Proofs.TgtCoupling
import Lax3Proofs.RefineBfsProbe

-- The proofs package of submission Lax3.
--
-- What is here is the mathematical layer of the nowhere dense model
-- checking theorem: the locality engine of arXiv:2606.23180, the isolation
-- splitter game and Splitter's win on nowhere dense classes, the sparse
-- neighborhood covers of Grohe-Kreutzer-Siebertz section 6 with the
-- augmentation machinery behind their degree bound, and the two syntactic
-- rewrites (relativization to a cluster, isolation of a batch) that a
-- recursion descending the game tree performs on formulas.
--
-- What is not here, deliberately: the algorithm and its realization on
-- the word RAM. That layer was pruned on 2026-08-17 and is being redesigned
-- from first principles. See `plans/nowhere-dense-model-checking/`:
-- `pruned-algorithmic-layer.md` records what was removed and what it
-- taught, `algorithm-v2.md` is the design that replaces it. Nothing in
-- this package refers to the pruned layer, and the concept surface in
-- `../concepts` is unchanged by the prune.
--
-- Discharged here: `Lax3.Locality.locality` and `Lax3.NormalForm.normalForm`
-- (in `Assembly`). Still axioms on the concept surface:
-- `Lax3.ModelChecking.exists_almostLinearTime_program_modelChecking` (the
-- headline, which is what the redesign is for),
-- `Lax3.NowhereDenseSplitter.splitterWins_of_nowhereDense`, and
-- `Lax3.NeighborhoodCoverBound.exists_neighborhoodCover_degree_wcol`.
