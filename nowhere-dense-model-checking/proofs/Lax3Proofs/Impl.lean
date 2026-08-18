import Lax3Proofs.ImplBfs
import Lax3Proofs.ImplScatter
import Lax3Proofs.ImplBot

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

## Not yet in this family (E12's remainder)

`restrict` (§6.1, with the one-scratch-array-per-node amortization and
the `Σ_{s∈S} deg_A(s)`-shaped charge — NOT `O(‖A[S]‖ + |S|)`, which is
false), `isolate`, `recordProfiles` (§6.3), the `cover` ordering-to-
clusters sweep (§6.2 ⟨B⟩, GKS's own peeling routine with the `N_</N_>`
split and the `(★)` accounting), and the computed `ctr` read off that
sweep with the identity to `CoverCentres.ctr`. See the campaign record
for the split.
-/

namespace Lax3Proofs.Impl

end Lax3Proofs.Impl
