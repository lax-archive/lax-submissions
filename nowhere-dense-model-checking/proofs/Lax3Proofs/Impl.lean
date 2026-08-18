import Lax3Proofs.ImplBfs
import Lax3Proofs.ImplScatter
import Lax3Proofs.ImplBot
import Lax3Proofs.ImplRestrict
import Lax3Proofs.ImplCover
import Lax3Proofs.ImplProfiles

/-!
# E12 — the `Arena` implementation and the routines (§8 step 6): head

The §4 operation table, §6's routines, delivered as programs against the
`Refine` tower where the tower carries them (`bfs`) and as concrete
functions with abstract cost statements where it does not — each with
the identity to the abstract layer the driver (`DriverArena`) consumes.

## Delivered in this family

* **`ImplBfs`** — `bfs` and `bfsSupports` (§4 rows 3–4).
  `bfsAlg_computes_ball_B0` consumes the tower's BFS at `B₀`, full mask,
  per E11's verdict (init is carrier-sized, expand is alive-summed —
  call it only post-`restrict`); `chargeB0_total` closes the account at
  exactly `2·‖B₀‖ + d + 2`. `descend`/`bfsSupports` materialize the
  `≤ d+1` walk-support names at every reached vertex from the distance
  array the tower's spec guarantees (`BallTable` — the seam, one
  hypothesis wide), with `descend_spec` (the list IS a witness walk's
  support, length exactly `D v`), and `supportsCharge_le`:
  `≤ (d+2)·ballNorm`, §4's `O(d·‖ball‖)`.

* **`ImplScatter`** — `greedyScatter` (§4 row 7, §6.5). The guarded
  early-stop sweep with the `t = 0` guard explicit;
  `greedyScatter_eq_min` (`= min t (greedySet).ncard`, §4's advertised
  value), `le_greedyScatter_iff` (decides the driver's atom
  `t ≤ greedyChoice.size` — the identity to
  `ScatterSentences.greedyChoice`/`greedySet`), and
  `greedyScatterCost_le : ≤ t·(n + W)` with
  `greedyScatterCost_zero : … = 0` — the `t = 0` guard as the cost
  statement it is.

* **`ImplBot`** — `BotTables` (§4 row 8, §6.4). `botEval`, the
  `Bool`-valued row evaluator; `botEval_eq_sat` (it computes `Sat ⊥`),
  `length_candidates_le` (the `k + 2^L` witness bound), and
  `tablesAux_bot_eq_botEval` — the identity to what `Driver.tablesAux`
  returns at its leaf, at every fuel.

The remainder landed as its own satellites (E12b/c/d):

* **`ImplRestrict`** — `restrict` + `isolate` (§6.1): local names by the
  driver's own enumeration (identities to `preG`/`childCol0` are `rfl`),
  the one-scratch-array-per-node sweep with the clean-restoration
  invariant load-bearing, `childCharge` with no carrier-sized term, and
  the children-aggregate closed to `2(c+1)·‖A‖^{1+δ}`.
* **`ImplCover`** — the peeling sweep (§6.2 ⟨B⟩): the peeled-ball =
  wreach-fibre identity at no side condition, the sweep and computed
  `sweepCtr` with identities to `Driver.cluster` and `CoverCentres.ctr`,
  and GKS's `(★)` accounting closed at `2·D·(n·D)` — under `1 ≤ r`,
  which GKS assume silently and which is false at `r = 0`.
* **`ImplProfiles`** — `recordProfiles` (§6.3): `(m+L)` single-source
  `BallTable`s assembled into exactly `Driver.childCol` (function
  equality), cumulative rows in `preG` before isolation; the honest
  iterated-call charge with the multi-source gap priced, not hidden.
-/

namespace Lax3Proofs.Impl

end Lax3Proofs.Impl
