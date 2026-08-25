import Lax3Proofs.SolveChain
import Lax3Proofs.SolveMachPrepPins

/-!
# F7-a — `Adm` and `KB`, pinned

`SolveChain` carries the level chain with two abstract parameters that
the final assembly must instantiate: the admissibility predicate `Adm`
threaded through `BlockSpec`/`FrameStep`/`chainCom_blockSpec`/
`solveSpec_of_chain`, and the per-block budget family `KB`. This file
pins both, and proves the facts every consumer of them needs.

## §1–§3 `Adm := chainAdm`

`chainAdm S G₀ j A := prepAdm S j A ∧ (j ≤ S.depth → Inv S G₀ j A)`.

Both halves are needed, and the guard on the second is not decoration:

* `prepAdm` (`SolveMachPrepPins` §2) is the machine-level pin bundle
  the prep segment reads — the round count `A.hist.length = j` and the
  `≤ 2R+1` channel row bound. It is stated **unguarded** because
  `RoundPin` is (`SolveMachPrepPins`'s `PrepPins.round`), and it costs
  nothing to carry: `Inv`'s own first two clauses *are* `prepAdm`
  (`prepAdm_of_inv`).
* `Inv` (`DriverCorrect` §Inv) is the run invariant, and it is what
  supplies `BlockSpec`'s fuel-`0` edgeless guard through
  `eq_bot_of_inv_depth`. It is guarded by `j ≤ S.depth` because
  `inv_child` needs the width hypothesis `1 + j·(2R+1) ≤ S.width`,
  which `mkSetup_width_le` supplies only below the leaf level — and
  `SolveStep`'s `hAdmChild` asks for the child step at **every** `j`,
  with no `j < S.depth` side condition. Under the guard the step is
  provable at every `j`: at `j + 1 ≤ S.depth` the width hypothesis is
  available, and above the leaf level the conclusion is vacuous.

The three facts:

1. **root** — `chainAdm_root`, off `prepAdm_root` and `inv_root`;
2. **child** — `chainAdm_child` at the child the frame step actually
   forms, `childArena S A π u` for an arbitrary `π` and `u : Fin A.N`;
   `chainAdm_admChild` is `SolveStep.centreStep_of_prep_read`'s
   `hAdmChild` shape verbatim (`π := (ord A.N A.G).order`), and
   `chainAdm_leafChild` is its `hleafChild`;
3. **the edgeless guard** — `chainAdm_eq_bot` /
   `chainAdm_eq_bot_diag`: on the diagonal `j + k = S.depth` at `k = 0`,
   `Adm j A → A.G = ⊥`, which is exactly `BlockSpec`'s guard.

**Anti-vacuity.** `chainAdm_of_memTree` exhibits the predicate at
*every arena the driver's own run tree visits* on the campaign setup —
not merely at the root — off `Unroll.mkSetup_inv_of_memTree`.
`headlineSetup_chainAdm_root` is the root instance
`solveSpec_of_chain`'s `hAdmRoot` consumes.

`chainAdm_prepPins` records that the pinned `Adm` still satisfies
`SolveMachPrepPins.PrepPins` at the canonical `ℓp`/`hbf`/`htabF`, so
nothing the prep segment reads is lost by conjoining `Inv`.

## §4–§5 `KB := chainKB`

`chainKB` is a recursion on the **fuel** index `k` (structural — the
recursive occurrence sits under a lambda in the `nxK` slot, exactly as
`ProgCharge.driverChargeMS` does):

* `chainKB 0 j A := botComK A.N (S.pal j) Kq (levelFml S j)`;
* `chainKB (k+1) j A := 4 + max (botComK …) (frameElseK …)`.

`frameElseK` is `SolveChain.frameK`'s **else branch**, taken
unconditionally. That deviation from `frameK` is forced, and it is a
finding about `frameK`, not about the chain:

> `blockSpec_leaf_guard`'s `hKB` (`SolveChain:418`) asks for
> `4 + max (botComK A.N …) (KElse A) ≤ KB (k+1) j A` **at every `A`**,
> the edgeless ones included — the guarded command pays `Spec.ite`'s
> `max` before the test is evaluated. `frameK` returns exactly
> `botComK A.N …` on `A.G = ⊥`, which is smaller than
> `4 + max (botComK A.N …) (KElse A)` by at least `4`. So `frameK`
> **cannot** be `KB (k+1) j ·` for any instantiation of its
> parameters. `frameK_le_chainKB` records that the pinned family
> dominates the naming target everywhere, and
> `frameK_eq_frameElseK_of_ne_bot` records that the two agree on
> precisely the arenas the frame body ever runs on.

The two landed budget obligations are then definitional:
`chainKB_bot_hKB` is `botBlock_spec`'s `hKB` (`SolveChain:386`) and
`chainKB_guard_hKB` is `blockSpec_leaf_guard`'s (`SolveChain:418`), at
`KElse := frameElseK …`. `chainKB_botBlock_spec` runs the first through
`botBlock_spec` end to end, so the fit is a typechecked instantiation
and not a shape match.

## What is *not* here

`KsChargeBridge` (`SolveChain:705`) is a separate leaf. The
compatibility audit of this `KB` against it is in the report, not in
the file; the one part of it that is a Lean statement here is
`centreK_add_nxK` (the recursion slot enters `centreK` additively), the
step the node→root induction needs.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

variable {L n₀ : ℕ}

/-! ## §1 The concrete admissibility predicate -/

/-- **The chain's admissibility predicate, pinned.** The machine pins
(`prepAdm`, unguarded — `RoundPin` is) conjoined with the run
invariant below the leaf level (`Inv`, guarded — `inv_child`'s width
hypothesis is only available there, and `SolveStep`'s `hAdmChild` asks
for the child step at every `j`). -/
def chainAdm (S : Setup L) (G₀ : SimpleGraph (Fin n₀)) :
    (j : ℕ) → Arena (S.pal j) n₀ → Prop :=
  fun j A => prepAdm S j A ∧ (j ≤ S.depth → Inv S G₀ j A)

/-- The run invariant's first two clauses **are** the machine pins — so
conjoining `prepAdm` costs nothing wherever `Inv` is available. -/
theorem prepAdm_of_inv (S : Setup L) {G₀ : SimpleGraph (Fin n₀)} {j : ℕ}
    {A : Arena (S.pal j) n₀} (h : Inv S G₀ j A) : prepAdm S j A :=
  ⟨h.1, h.2.1⟩

theorem chainAdm_prepAdm (S : Setup L) {G₀ : SimpleGraph (Fin n₀)} {j : ℕ}
    {A : Arena (S.pal j) n₀} (h : chainAdm S G₀ j A) : prepAdm S j A := h.1

theorem chainAdm_inv (S : Setup L) {G₀ : SimpleGraph (Fin n₀)} {j : ℕ}
    {A : Arena (S.pal j) n₀} (h : chainAdm S G₀ j A) (hj : j ≤ S.depth) :
    Inv S G₀ j A := h.2 hj

/-- `chainAdm` is exactly `Inv` below the leaf level — the converse of
`chainAdm_inv`, which is what makes the predicate satisfiable wherever
the run invariant is (§3). -/
theorem chainAdm_of_inv (S : Setup L) {G₀ : SimpleGraph (Fin n₀)} {j : ℕ}
    {A : Arena (S.pal j) n₀} (h : Inv S G₀ j A) : chainAdm S G₀ j A :=
  ⟨prepAdm_of_inv S h, fun _ => h⟩

/-! ## §2 The three facts -/

/-- **Fact 1 — the root.** The arena `mkSetup`'s driver starts from is
admissible, at every graph and colouring. -/
theorem chainAdm_root (S : Setup L) {n : ℕ} (G : SimpleGraph (Fin n))
    (col : Coloring n L) : chainAdm S G 0 (rootArena G col) :=
  ⟨prepAdm_root S G col, fun _ => inv_root S G col⟩

/-- **Fact 2 — the child.** Admissibility is inherited by the child of
any centre of an edged arena, at whatever permutation the frame step
forms it with. The width hypothesis is `inv_child`'s, at `mkSetup` the
landed `mkSetup_width_le`. -/
theorem chainAdm_child (S : Setup L) {G₀ : SimpleGraph (Fin n₀)}
    (hwidth : ∀ i, i < S.depth → 1 + i * (2 * S.R + 1) ≤ S.width)
    (j : ℕ) (A : Arena (S.pal j) n₀) (h : chainAdm S G₀ j A) (hbot : ¬ A.G = ⊥)
    (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) :
    chainAdm S G₀ (j + 1) (childArena S A π u) := by
  refine ⟨prepAdm_child S j A π u h.1, fun hj1 => ?_⟩
  exact inv_child S π u (h.2 (by omega)) hbot (hwidth j (by omega))

/-- **Fact 3 — the edgeless guard**, at the leaf level: an admissible
arena at depth `S.depth` is edgeless. This is `BlockSpec`'s fuel-`0`
hypothesis, and the reason the `Inv` half is in `Adm` at all. -/
theorem chainAdm_eq_bot (S : Setup L) {G₀ : SimpleGraph (Fin n₀)}
    {N : ℕ → ℕ} {s : ℕ}
    (hQ : Lax3Proofs.UqwInstantiation.SplitterMargin G₀ N s S.R)
    (hd : S.depth = N (2 * s + 2)) {j : ℕ} {A : Arena (S.pal j) n₀}
    (hj : j = S.depth) (h : chainAdm S G₀ j A) : A.G = ⊥ := by
  subst hj
  exact eq_bot_of_inv_depth S hQ hd (h.2 le_rfl)

/-- **Fact 3, on the diagonal** — verbatim the shape `BlockSpec`'s
guard is consumed in: at `j + k = S.depth` with `k = 0`, admissibility
gives edgelessness. -/
theorem chainAdm_eq_bot_diag (S : Setup L) {G₀ : SimpleGraph (Fin n₀)}
    {N : ℕ → ℕ} {s : ℕ}
    (hQ : Lax3Proofs.UqwInstantiation.SplitterMargin G₀ N s S.R)
    (hd : S.depth = N (2 * s + 2)) {k j : ℕ} {A : Arena (S.pal j) n₀}
    (hdiag : j + k = S.depth) (h : chainAdm S G₀ j A) : k = 0 → A.G = ⊥ :=
  fun hk => chainAdm_eq_bot S hQ hd (by omega) h

/-! ## §3 The two shapes `SolveStep` consumes -/

/-- `centreStep_of_prep_read`'s `hAdmChild`, at the pinned `Adm`. -/
theorem chainAdm_admChild (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    {G₀ : SimpleGraph (Fin n₀)}
    (hwidth : ∀ i, i < S.depth → 1 + i * (2 * S.R + 1) ≤ S.width) :
    ∀ (j : ℕ) (A : Arena (S.pal j) n₀), chainAdm S G₀ j A → ¬ A.G = ⊥ →
      ∀ u : Fin A.N,
        chainAdm S G₀ (j + 1) (childArena S A ((ord A.N A.G).order) u) :=
  fun j A h hbot u => chainAdm_child S hwidth j A h hbot _ u

/-- `centreStep_of_prep_read`'s `hleafChild`, at the pinned `Adm`: the
child one level above the leaf is edgeless. -/
theorem chainAdm_leafChild (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    {G₀ : SimpleGraph (Fin n₀)} {N : ℕ → ℕ} {s : ℕ}
    (hQ : Lax3Proofs.UqwInstantiation.SplitterMargin G₀ N s S.R)
    (hd : S.depth = N (2 * s + 2))
    (hwidth : ∀ i, i < S.depth → 1 + i * (2 * S.R + 1) ≤ S.width) :
    ∀ (j : ℕ) (A : Arena (S.pal j) n₀), chainAdm S G₀ j A → ¬ A.G = ⊥ →
      j + 1 = S.depth → ∀ u : Fin A.N,
        (childArena S A ((ord A.N A.G).order) u).G = ⊥ :=
  fun j A h hbot hj u =>
    chainAdm_eq_bot S hQ hd hj (chainAdm_admChild S ord hwidth j A h hbot u)

/-! ## §4 Anti-vacuity: the predicate on the campaign's own run -/

/-- **The satisfiability witness.** Every arena the driver's run tree
visits, from the root of any input, is admissible — at the campaign
setup, on every graph and colouring, with no class-membership
hypothesis. The `Inv` half is `Unroll.mkSetup_inv_of_memTree`; the
`prepAdm` half falls out of it (`prepAdm_of_inv`). -/
theorem chainAdm_of_memTree (C : GraphClass) (hC : NowhereDense C) {q : ℕ}
    (φ : DistFO L 0) (hφ : DRank 0 q φ) (choice : ScatterChoice)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (col : Coloring n L)
    {j' : ℕ} {A' : Arena ((mkSetup C hC φ hφ choice).pal j') n}
    (h : Unroll.MemTree (mkSetup C hC φ hφ choice) n A'
      (Unroll.runTree (mkSetup C hC φ hφ choice) ord 0 (rootArena G col))) :
    chainAdm (mkSetup C hC φ hφ choice) G j' A' :=
  chainAdm_of_inv _ (Unroll.mkSetup_inv_of_memTree C hC φ hφ choice ord G col h)

/-- The same at a bottoming-out node — the leaves are admissible too
(`MemLeaf → MemTree`). -/
theorem chainAdm_of_memLeaf (C : GraphClass) (hC : NowhereDense C) {q : ℕ}
    (φ : DistFO L 0) (hφ : DRank 0 q φ) (choice : ScatterChoice)
    (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G : SimpleGraph (Fin n)) (col : Coloring n L)
    {j' : ℕ} {A' : Arena ((mkSetup C hC φ hφ choice).pal j') n}
    (h : Unroll.MemLeaf (mkSetup C hC φ hφ choice) n A'
      (Unroll.runTree (mkSetup C hC φ hφ choice) ord 0 (rootArena G col))) :
    chainAdm (mkSetup C hC φ hφ choice) G j' A' :=
  chainAdm_of_memTree C hC φ hφ choice ord G col (Unroll.memTree_of_memLeaf h)

/-! ### At the campaign setup: the three facts, hypothesis-free -/

section MkSetup

variable (C : GraphClass) (hC : NowhereDense C) {q : ℕ}
  (φ : DistFO L 0) (hφ : DRank 0 q φ) (choice : ScatterChoice)

/-- The width hypothesis, at `mkSetup`. -/
theorem mkSetup_widthAll :
    ∀ i, i < (mkSetup C hC φ hφ choice).depth →
      1 + i * (2 * (mkSetup C hC φ hφ choice).R + 1) ≤
        (mkSetup C hC φ hφ choice).width :=
  fun _ hi => mkSetup_width_le C hC φ hφ choice hi

/-- **Fact 2 at the campaign setup**, hypothesis-free in the width. -/
theorem mkSetup_chainAdm_admChild (ord : CoverSpec.OrderingRoutine)
    {G₀ : SimpleGraph (Fin n₀)} :
    ∀ (j : ℕ) (A : Arena ((mkSetup C hC φ hφ choice).pal j) n₀),
      chainAdm (mkSetup C hC φ hφ choice) G₀ j A → ¬ A.G = ⊥ →
      ∀ u : Fin A.N,
        chainAdm (mkSetup C hC φ hφ choice) G₀ (j + 1)
          (childArena (mkSetup C hC φ hφ choice) A ((ord A.N A.G).order) u) :=
  chainAdm_admChild _ ord (mkSetup_widthAll C hC φ hφ choice)

/-- **Fact 3 at the campaign setup**, on a member of the class — the
margin and the depth identity are the landed `mkSetup_margin` /
`mkSetup_depth`. -/
theorem mkSetup_chainAdm_eq_bot {G₀ : SimpleGraph (Fin n₀)} (hG₀ : C n₀ G₀)
    {j : ℕ} {A : Arena ((mkSetup C hC φ hφ choice).pal j) n₀}
    (hj : j = (mkSetup C hC φ hφ choice).depth)
    (h : chainAdm (mkSetup C hC φ hφ choice) G₀ j A) : A.G = ⊥ :=
  chainAdm_eq_bot _ (mkSetup_margin C hC φ hφ choice hG₀)
    (mkSetup_depth C hC φ hφ choice) hj h

/-- **Fact 3 on the diagonal**, at the campaign setup. -/
theorem mkSetup_chainAdm_eq_bot_diag {G₀ : SimpleGraph (Fin n₀)}
    (hG₀ : C n₀ G₀) {k j : ℕ}
    {A : Arena ((mkSetup C hC φ hφ choice).pal j) n₀}
    (hdiag : j + k = (mkSetup C hC φ hφ choice).depth)
    (h : chainAdm (mkSetup C hC φ hφ choice) G₀ j A) : k = 0 → A.G = ⊥ :=
  fun hk => mkSetup_chainAdm_eq_bot C hC φ hφ choice hG₀ (by omega) h

/-- `hleafChild` at the campaign setup. -/
theorem mkSetup_chainAdm_leafChild (ord : CoverSpec.OrderingRoutine)
    {G₀ : SimpleGraph (Fin n₀)} (hG₀ : C n₀ G₀) :
    ∀ (j : ℕ) (A : Arena ((mkSetup C hC φ hφ choice).pal j) n₀),
      chainAdm (mkSetup C hC φ hφ choice) G₀ j A → ¬ A.G = ⊥ →
      j + 1 = (mkSetup C hC φ hφ choice).depth → ∀ u : Fin A.N,
        (childArena (mkSetup C hC φ hφ choice) A ((ord A.N A.G).order) u).G
          = ⊥ :=
  chainAdm_leafChild _ ord (mkSetup_margin C hC φ hφ choice hG₀)
    (mkSetup_depth C hC φ hφ choice) (mkSetup_widthAll C hC φ hφ choice)

end MkSetup

/-! ### At `headlineSetup`: exactly what `solveSpec_of_chain` consumes -/

/-- **`solveSpec_of_chain`'s `hAdmRoot`, discharged.** -/
theorem headlineSetup_chainAdm_root (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) {n : ℕ} (G : SimpleGraph (Fin n)) :
    chainAdm (Headline.headlineSetup C hC φ) G 0
      (rootArena G (Impl.trivialColoring n)) :=
  chainAdm_root _ G (Impl.trivialColoring n)

/-- **`solveSpec_of_chain`'s `hdep0`, discharged** — at a degenerate
depth the input graph is already edgeless, on a member of the class.
(The root arena's graph *is* `G`, so this is Fact 3 at `j = 0`.) -/
theorem headlineSetup_chainAdm_dep0 (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) {n : ℕ} {G : SimpleGraph (Fin n)} (hG : C n G) :
    (Headline.headlineSetup C hC φ).depth = 0 → G = ⊥ := by
  intro h0
  exact mkSetup_chainAdm_eq_bot C hC _ _ _ hG h0.symm
    (headlineSetup_chainAdm_root C hC φ G)

/-- The child step at `headlineSetup`. -/
theorem headlineSetup_chainAdm_admChild (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (ord : CoverSpec.OrderingRoutine) {n : ℕ}
    (G₀ : SimpleGraph (Fin n)) :
    ∀ (j : ℕ) (A : Arena ((Headline.headlineSetup C hC φ).pal j) n),
      chainAdm (Headline.headlineSetup C hC φ) G₀ j A → ¬ A.G = ⊥ →
      ∀ u : Fin A.N,
        chainAdm (Headline.headlineSetup C hC φ) G₀ (j + 1)
          (childArena (Headline.headlineSetup C hC φ) A
            ((ord A.N A.G).order) u) :=
  mkSetup_chainAdm_admChild C hC _ _ _ ord

/-- The leaf child at `headlineSetup`, on a member of the class. -/
theorem headlineSetup_chainAdm_leafChild (C : GraphClass)
    (hC : NowhereDense C) (φ : FO 0) (ord : CoverSpec.OrderingRoutine)
    {n : ℕ} {G₀ : SimpleGraph (Fin n)} (hG₀ : C n G₀) :
    ∀ (j : ℕ) (A : Arena ((Headline.headlineSetup C hC φ).pal j) n),
      chainAdm (Headline.headlineSetup C hC φ) G₀ j A → ¬ A.G = ⊥ →
      j + 1 = (Headline.headlineSetup C hC φ).depth → ∀ u : Fin A.N,
        (childArena (Headline.headlineSetup C hC φ) A
          ((ord A.N A.G).order) u).G = ⊥ :=
  mkSetup_chainAdm_leafChild C hC _ _ _ ord hG₀

/-! ## §5 The machine pins survive the pin -/

theorem chainAdm_roundPin (S : Setup L) (G₀ : SimpleGraph (Fin n₀)) :
    RoundPin (n₀ := n₀) S (chainAdm S G₀) :=
  roundPin_mono S (fun _ _ h => h.1) (prepAdm_roundPin S)

theorem chainAdm_roomPin (S : Setup L) (G₀ : SimpleGraph (Fin n₀)) :
    RoomPin (n₀ := n₀) S (colCount S) (chainAdm S G₀) :=
  fun j A hj h => colCount_roomPin S j A hj h.1

theorem chainAdm_fitPin (S : Setup L) (G₀ : SimpleGraph (Fin n₀)) :
    FitPin (n₀ := n₀) S (colCount S) (chainAdm S G₀) :=
  fun j A hj h => colCount_fitPin S j A hj h.1

/-- **The five machine pins hold of the pinned `Adm`** — conjoining the
run invariant onto `prepAdm` loses nothing the prep segment reads
(`SolveMachPrepPins.stdPins` at `chainAdm` in place of `prepAdm`). -/
theorem chainAdm_prepPins (S : Setup L) (G₀ : SimpleGraph (Fin n₀)) :
    PrepPins (n₀ := n₀) S (colCount S) (chanTab S (colCount S))
      (chanBound S) (chainAdm S G₀) where
  chan := chanTab_chanPin S (colCount S)
  round := chainAdm_roundPin S G₀
  col := colCount_colPin S
  bound := chanBound_boundPin S
  room := chainAdm_roomPin S G₀
  fit := chainAdm_fitPin S G₀

/-! ## §6 The budget family -/

open Classical in
/-- **`frameK`'s else branch, unconditionally** — the frame body's own
advertised budget: the cover stage, the per-centre pipeline with the
inner block and the scatter calls, and the glue. Identical to
`SolveChain.frameK` on every arena the frame body runs on
(`frameK_eq_frameElseK_of_ne_bot`). -/
noncomputable def frameElseK (S : Setup L) (j : ℕ) (A : Arena (S.pal j) n₀)
    (ℓpj hbj : ℕ) (π : Equiv.Perm (Fin A.N)) (Kcov Kglue : ℕ)
    (nxK : Arena (S.pal (j + 1)) n₀ → ℕ) : ℕ :=
  Kcov + (((List.finRange A.N).map fun u =>
      centreK S A ℓpj hbj π u (nxK (childArena S A π u))
        + centreScatterK S j A π u).sum
    + Kglue)

open Classical in
theorem frameK_eq_frameElseK_of_ne_bot (S : Setup L) (j Kq : ℕ)
    (A : Arena (S.pal j) n₀) (ℓpj hbj : ℕ) (π : Equiv.Perm (Fin A.N))
    (Kcov Kglue : ℕ) (nxK : Arena (S.pal (j + 1)) n₀ → ℕ)
    (hbot : ¬ A.G = ⊥) :
    frameK S j Kq A ℓpj hbj π Kcov Kglue nxK
      = frameElseK S j A ℓpj hbj π Kcov Kglue nxK := by
  rw [frameK, if_neg hbot, frameElseK]

open Classical in
theorem frameK_le_max (S : Setup L) (j Kq : ℕ) (A : Arena (S.pal j) n₀)
    (ℓpj hbj : ℕ) (π : Equiv.Perm (Fin A.N)) (Kcov Kglue : ℕ)
    (nxK : Arena (S.pal (j + 1)) n₀ → ℕ) :
    frameK S j Kq A ℓpj hbj π Kcov Kglue nxK
      ≤ max (botComK A.N (S.pal j) Kq (levelFml S j))
          (frameElseK S j A ℓpj hbj π Kcov Kglue nxK) := by
  rw [frameK]
  split
  · exact le_max_left _ _
  · exact le_max_right _ _

open Classical in
/-- **The chain's budget family, pinned.** Recursion on the fuel index
only — the recursive occurrence sits under a lambda in `frameElseK`'s
`nxK` slot, structurally exactly as `ProgCharge.driverChargeMS`. The
`4 + max (botComK …) …` shape is the leaf guard's own arithmetic
(`blockSpec_leaf_guard`: `Spec.ite`'s `1 + 3` on top of the larger
branch), which the budget must carry at every arena. -/
noncomputable def chainKB (S : Setup L) (ord : CoverSpec.OrderingRoutine)
    (Kq : ℕ) (ℓp hbf : ℕ → ℕ)
    (Kcov : (j : ℕ) → Arena (S.pal j) n₀ → ℕ)
    (Kglue : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ) :
    (k j : ℕ) → Arena (S.pal j) n₀ → ℕ
  | 0, j, A => botComK A.N (S.pal j) Kq (levelFml S j)
  | k + 1, j, A =>
      4 + max (botComK A.N (S.pal j) Kq (levelFml S j))
        (frameElseK S j A (ℓp j) (hbf j) ((ord A.N A.G).order)
          (Kcov j A) (Kglue k j A)
          (fun A' => chainKB S ord Kq ℓp hbf Kcov Kglue k (j + 1) A'))

section KB

variable (S : Setup L) (ord : CoverSpec.OrderingRoutine) (Kq : ℕ)
  (ℓp hbf : ℕ → ℕ)
  (Kcov : (j : ℕ) → Arena (S.pal j) n₀ → ℕ)
  (Kglue : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ)

open Classical in
theorem chainKB_zero (j : ℕ) (A : Arena (S.pal j) n₀) :
    chainKB S ord Kq ℓp hbf Kcov Kglue 0 j A
      = botComK A.N (S.pal j) Kq (levelFml S j) := rfl

open Classical in
theorem chainKB_succ (k j : ℕ) (A : Arena (S.pal j) n₀) :
    chainKB S ord Kq ℓp hbf Kcov Kglue (k + 1) j A
      = 4 + max (botComK A.N (S.pal j) Kq (levelFml S j))
        (frameElseK S j A (ℓp j) (hbf j) ((ord A.N A.G).order)
          (Kcov j A) (Kglue k j A)
          (fun A' => chainKB S ord Kq ℓp hbf Kcov Kglue k (j + 1) A')) := rfl

open Classical in
/-- **`botBlock_spec`'s `hKB` (`SolveChain:386`), discharged** — at the
pinned family the leaf block's budget is the bottom block's budget on
the nose. -/
theorem chainKB_bot_hKB (j : ℕ) :
    ∀ A : Arena (S.pal j) n₀,
      botComK A.N (S.pal j) Kq (levelFml S j)
        ≤ chainKB S ord Kq ℓp hbf Kcov Kglue 0 j A :=
  fun _ => le_rfl

open Classical in
/-- **`blockSpec_leaf_guard`'s `hKB` (`SolveChain:418`), discharged** at
`KElse := frameElseK …` — the guard's `4 + max` is what the pinned
family is built out of. -/
theorem chainKB_guard_hKB (k j : ℕ) :
    ∀ A : Arena (S.pal j) n₀,
      4 + max (botComK A.N (S.pal j) Kq (levelFml S j))
          (frameElseK S j A (ℓp j) (hbf j) ((ord A.N A.G).order)
            (Kcov j A) (Kglue k j A)
            (fun A' => chainKB S ord Kq ℓp hbf Kcov Kglue k (j + 1) A'))
        ≤ chainKB S ord Kq ℓp hbf Kcov Kglue (k + 1) j A :=
  fun _ => le_rfl

open Classical in
/-- **The naming target is dominated.** `frameK` at the pinned
parameters never exceeds the pinned budget — so a `FrameStep`
discharger that prices its body at `frameK` (`SolveChain` §7's
intention) still fits, at every arena, edgeless or not. -/
theorem frameK_le_chainKB (k j : ℕ) (A : Arena (S.pal j) n₀) :
    frameK S j Kq A (ℓp j) (hbf j) ((ord A.N A.G).order)
        (Kcov j A) (Kglue k j A)
        (fun A' => chainKB S ord Kq ℓp hbf Kcov Kglue k (j + 1) A')
      ≤ chainKB S ord Kq ℓp hbf Kcov Kglue (k + 1) j A := by
  rw [chainKB_succ]
  exact le_trans (frameK_le_max S j Kq A (ℓp j) (hbf j) _ _ _ _) (by omega)

end KB

/-! ## §7 The pin, run through the landed block theorems

Not a shape match — the two theorems of `SolveChain` §5 that consume a
`KB` are instantiated at `chainAdm`/`chainKB` and typecheck. -/

section BotFit

variable (B : ℕ) (S : Setup L) (ord : CoverSpec.OrderingRoutine)
  (ℓp : ℕ → ℕ)
  (htabF : (j : ℕ) → (A : Arena (S.pal j) n₀) →
    Fin A.N → Fin (ℓp j) → List (Fin A.N))
  (hbf : ℕ → ℕ) (nmF : ℕ → ArenaNames)
  (G₀ : SimpleGraph (Fin n₀))
  (Kcov : (j : ℕ) → Arena (S.pal j) n₀ → ℕ)
  (Kglue : (k j : ℕ) → Arena (S.pal j) n₀ → ℕ)
  (Scr : ℕ → Env → Prop)
  (j Kq : ℕ) {na fa ea xa : String}

variable
  (hq : ∀ β ∈ levelFml S j, qdepth β ≤ Kq)
  (hn0B : n₀ < B) (hNLB : n₀ * S.pal j < B)
  (h2LB : 2 ^ S.pal j * (Kq + 1) < B)
  (hTB : n₀ * (levelFml S j).length < B)
  (hnd : [(nmF j).col, na, fa, ea, xa, (nmF j).tab].Nodup)
  (hoff : (nmF j).off ∉ [na, fa, ea, xa, (nmF j).tab])
  (htgt : (nmF j).tgt ∉ [na, fa, ea, xa, (nmF j).tab])
  (hup : (nmF j).up ∉ [na, fa, ea, xa, (nmF j).tab])
  (hhist : (nmF j).hist ∉ [na, fa, ea, xa, (nmF j).tab])
  (hnN : (nmF j).nN ∉ btScalars) (hnS : (nmF j).nS ∉ btScalars)
  (hnd5 : ([(nmF j).off, (nmF j).tgt, (nmF j).col, (nmF j).up,
    (nmF j).hist] : List String).Nodup)
  (hscr : ∀ σ, Scr j σ →
    (σ.arrs na).length = 2 ^ S.pal j ∧
    (σ.arrs fa).length = 2 ^ S.pal j * (Kq + 1) ∧
    (σ.arrs ea).length = Kq + 1 ∧ (σ.arrs xa).length = Kq + 1)

include hq hn0B hNLB h2LB hTB hnd hoff htgt hup hhist hnN hnS hnd5 hscr in
open Classical in
/-- **The bottom block at the pinned parameters** — `botBlock_spec`
(`SolveChain:385`) with `Adm := chainAdm` and `KB := chainKB`, its
budget hypothesis discharged by `chainKB_bot_hKB`. -/
theorem chainKB_botBlock_spec :
    BlockSpec B S ord ℓp htabF hbf nmF (chainAdm S G₀)
      (chainKB S ord Kq ℓp hbf Kcov Kglue) Scr 0 j
      (botCom (nmF j).nN (nmF j).col na fa ea xa (nmF j).tab (S.pal j) Kq
        (levelFml S j)) :=
  botBlock_spec B S ord ℓp htabF hbf nmF (chainAdm S G₀)
    (chainKB S ord Kq ℓp hbf Kcov Kglue) Scr j Kq hq hn0B hNLB h2LB hTB
    hnd hoff htgt hup hhist hnN hnS hnd5 hscr
    (chainKB_bot_hKB S ord Kq ℓp hbf Kcov Kglue j)

include hq hn0B hNLB h2LB hTB hnd hoff htgt hup hhist hnN hnS hnd5 hscr in
open Classical in
/-- **The guarded non-leaf block at the pinned parameters** —
`blockSpec_leaf_guard` (`SolveChain:410`) with `Adm := chainAdm`,
`KB := chainKB` and `KElse := frameElseK`: as soon as a frame body
meets `frameElseK`'s advertised budget on edged arenas, the guarded
block meets the pinned `KB`. Nothing about the body is assumed beyond
its own `Spec`. -/
theorem chainKB_blockSpec_leaf_guard (k : ℕ) (hn0B2 : n₀ * n₀ < B)
    (elseCom : Com)
    (helse : ∀ A : Arena (S.pal j) n₀, j + (k + 1) = S.depth →
      chainAdm S G₀ j A → ¬ A.G = ⊥ →
      Spec B (BlockPre S j (hbf j) A (htabF j A) (Scr j) (nmF j)) elseCom
        (fun _ σ' => BlockPost S ord (k + 1) j (hbf j) A (htabF j A) (nmF j) σ')
        (frameElseK S j A (ℓp j) (hbf j) ((ord A.N A.G).order)
          (Kcov j A) (Kglue k j A)
          (fun A' => chainKB S ord Kq ℓp hbf Kcov Kglue k (j + 1) A'))) :
    BlockSpec B S ord ℓp htabF hbf nmF (chainAdm S G₀)
      (chainKB S ord Kq ℓp hbf Kcov Kglue) Scr (k + 1) j
      (.ite (.eq (.var (nmF j).nS) (.lit 0))
        (botCom (nmF j).nN (nmF j).col na fa ea xa (nmF j).tab (S.pal j) Kq
          (levelFml S j))
        elseCom) :=
  blockSpec_leaf_guard B S ord ℓp htabF hbf nmF (chainAdm S G₀)
    (chainKB S ord Kq ℓp hbf Kcov Kglue) Scr j Kq hq hn0B hNLB h2LB hTB
    hnd hoff htgt hup hhist hnN hnS hnd5 hscr k hn0B2 elseCom _ helse
    (chainKB_guard_hKB S ord Kq ℓp hbf Kcov Kglue k j)

end BotFit

/-! ## §8 The recursion slot enters `centreK` additively

The one arithmetic fact the ledger comparison (`KsChargeBridge`, a
separate leaf) needs from this file: `centreK`'s `nxK` argument is a
plain summand, so the per-centre budget splits into "this node's five
stages" plus "the child's whole budget" — which is what lets the
node→root induction charge the five stages against
`centreChargeMS`'s five columns and hand the rest to the recursion. -/

open Classical in
theorem centreK_add_nxK (S : Setup L) {Λ : ℕ} (A : Arena Λ n₀)
    (ℓpj hbj : ℕ) (π : Equiv.Perm (Fin A.N)) (u : Fin A.N) (nxK : ℕ) :
    centreK S A ℓpj hbj π u nxK = centreK S A ℓpj hbj π u 0 + nxK := by
  simp only [centreK]
  omega

end Lax3Proofs.Prog
