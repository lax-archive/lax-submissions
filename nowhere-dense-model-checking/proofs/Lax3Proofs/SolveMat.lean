import Lax3Proofs.ProgCodegen
import Lax3Proofs.SolveMatFrame
import Lax3Proofs.SolveMatArena
import Lax3Proofs.SolveMatTop

/-!
# F6b — the solve stage's bookends, and the budget reroute (head)

Three parts, each in its own file, all in service of discharging
`ProgCodegen.SolveSpec` (the campaign's one remaining machine
obligation) together with the concurrent driver-block leaf (F6c):

* **`SolveMatFrame`** — the NREST-layer reroute (F3c's finding 1):
  `frameProgMS`/`frameProgMS_le_spec`, the frame program with its
  profile stage re-specced at the multi-source seam
  (`Impl.ProfileTablesMS`, budget `profilesCMS`, rows by
  `recordProfilesMS_eq_childCol`) — the program whose advertised
  budget is `ProgCharge.frameChargeMS`, the vector the ledger
  comparison actually prices. Slot interfaces are `ProgFrame`'s
  verbatim, so a driver recursion consumes the MS budget end to end.
* **`SolveMatArena`** — bookend 1: `matCom`/`matCom_spec` take the
  parse's `CsrIn` to `MatIn` — the root `MArena`'s machine
  representation (`rootMArena`), with `RootCsr` the five pinned cells,
  `RootCsr.stable`/`spec_rootCsr_frame` the stability the driver
  blocks ride, and `RootCsr.adj_iff`/`up_getD` the reading. Cost
  `matK x = 11·|x| + 6`.
* **`SolveMatTop`** — bookend 2: `verdictCom`/`topCom` fold `top`'s
  boolean combination into `"verdict"` as one compile-time expression
  (`bcExpr`), local sentence atoms as literal bits (L1), scatter
  atoms as the block family's guard-bit reads (`scatterBit`, the named
  slot obligation `hav`). `topCom_spec` ends at `SolveSpec`'s exact
  postcondition through `le_greedyScatter_iff`.

`solveSpec_of_rest` below is the seam statement: `SolveSpec` holds of
`matCom ; restCom` as soon as the middle — F6c's blocks with the
verdict tail, e.g. `topCom` at their table state — carries the state
from `MatIn` to the verdict cell. It spends `matCom_spec` once, so the
block leaf never re-reads the parse.
-/

namespace Lax3Proofs.Prog

open Lax67Proofs.Imp Lax67Proofs.Reasoning
open Lax11.GraphEncoding
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)

open Classical in
/-- **The seam into `SolveSpec`**: the solve stage is the
materialization bookend followed by the rest — F6c's driver blocks and
the verdict tail. Given the rest's one obligation — from `MatIn` (the
root arena materialized, scratch fresh) to the verdict cell, within
`Kr x` — `SolveSpec` holds of the composite at `matK x + Kr x`.
The `ext` convention owed is `hextUp`, the parse's own
(`hextOff`/`hextTgt`) extended by the root renaming's length. -/
theorem solveSpec_of_rest (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ext : List ℕ → String → ℕ) (restCom : Com)
    (Kr : List ℕ → ℕ) (hq : 1 ≤ q)
    (hextUp : ∀ x ∈ mcD n G c w, ext x "up" = vertexCount x)
    (hrest : ∀ x ∈ mcD n G c w,
      Spec (mcB q x) (MatIn (ext x) x) restCom
        (fun _ σ' => σ'.vars "verdict" =
          if Unroll.unrolledMC (Headline.headlineSetup C hC φ) ord G
            (Impl.trivialColoring n) then 1 else 0)
        (Kr x)) :
    SolveSpec C hC φ ord G c w q ext (.seq matCom restCom)
      (fun x => matK x + Kr x) := by
  rintro x hx
  obtain ⟨henc, hside⟩ := hx
  exact Spec.seq
    (matCom_spec (mcB q x) (ext x) henc
      (length_add_one_lt_mcB (three_le_length henc) hq)
      (hextUp x ⟨henc, hside⟩))
    (hrest x ⟨henc, hside⟩)
    (fun _ _ _ h => h) (fun _ _ _ _ _ h => h)

end Lax3Proofs.Prog
