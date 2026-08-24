import Lax3Proofs.SolveSweepBucket

/-!
# F6c13 (route 1) — the peel residual at a freed tie-break, and the
amortization a *canonical* peel needs

Wave 23 (`SolveSweepMdPeel`) discharges `CovMdPeelIn`
(`SolveSweepOrder.lean:451-480`) at

```
Kmp = fun _ A => 86 * A.N * A.N + 43 * A.N + 14
```

— a full carrier scan per round. §7 of the algorithm charges the whole
cover routine at `a·N^{1+2δ}`, so that `86·N²` breaks the headline at
the root. Wave 24 (`SolveSweepBucket`) declined to remove the `N²`
*from that residual*, and gave its reason: `CovMdPeelIn` pins the
pass's output to `mdPerm (mdChain A.G R).toGraph`, and `mdPerm` is
built from `minDegVert`, the minimum-degree vertex **of least index**,
which its three counterexample families price at `Θ(N²)` for every
constant-time bucket discipline they consider. That reason is prose in
a module docstring, not a theorem; what is formal there is
`eq_minDegVert_of_bucket` — the obligation such a pop would owe — and
the amortization (`peelLoop_linear`, `peelLoop_linear_cursor`), which
holds whichever way out is taken.

This file takes route 1 of wave 24's three ways out — **re-pin the
tie-break** — and lands its statement layer:

* **§2 `CovAugAdjSelIn` / §3 `CovSelPeelIn`** — the augmentation and
  peel residuals of `SolveSweepOrder` §3, restated at an arbitrary
  attaining selection `sel : ∀ m, MinDegSel m`: every clause
  unchanged, `mdChain`/`mdPerm` replaced by `selChain`/`selPerm`
  throughout. Nothing is weakened — §5 proves that at the pinned
  choice `sel = mdSel` these are the landed residuals *on the nose*,
  so wave 23's `covMdPeelIn_peelCom` discharges `CovSelPeelIn` at
  `mdSel` verbatim (`covSelPeelIn_peelCom_mdSel`).

* **§4 `covOrderIn_of_aug_selPeel`** — the glue, concluding
  `CovOrderIn … (selOrderingRoutine sel R) …` exactly as
  `covOrderIn_of_aug_mdPeel` concludes it at `mdOrderingRoutine R`.
  `covOrderIn_of_aug_mdPeel_of_sel` records that at `sel = mdSel` the
  new glue *is* the landed one, through `selOrderingRoutine_mdSel`.

Re-pinning is free upstream and this is already proved, not assumed:
`selOrderingRoutine_data` (wave 24 §5) gives the full six-clause
`AugChainData`, on every carrier and every graph, at **any** attaining
selection, because `selRankAux_props` uses only `MinDegSel.card_le` —
that the choice attains the minimum degree — and never `minDegVert`'s
`min'`. So the ordering routine loses nothing by the change, and
`isCoverOrdering_selOrderingRoutine` still leaves only the `time`
field owing.

## §1 — the amortization a canonical peel needs, and why it is a new one

Wave 24's `peelLoop_linear` / `peelLoop_linear_cursor` charge a round
`a + b·d` in the peeled vertex's **current** degree `d`, and pay for it
out of `livePot F S = ∑_{u ∈ S} |nbrsIn F S u|`. A round can charge the
current degree only if the row it walks lists exactly the live
neighbours — i.e. only if the peel *compacts* as it goes, which is what
`delAdjCom`'s swap-delete does and what scrambles the row order.

§1 adds the sibling potential for the other design, the one route 1
actually forces: `staticPot F S = ∑_{u ∈ S} |N_F(u)|`, the total
**original** degree of the live set. It falls by exactly `|N_F(v)|`
when `v` is peeled (`staticPot_erase` — no factor of two, unlike
`livePot_erase`), it starts at `slotCount F` (`staticPot_univ`), and
`peelLoop_linear_static` / `peelLoop_linear_static_cursor` are wave
24's two loop rules at it: a round costing `a + b·|N_F(v)|` (plus `e`
per rise of a cursor that falls by at most one) runs inside
`a·N + b·slotCount F + O(1)`, resp. `(a+e)·N + b·slotCount F + e·N + O(1)`.

Why the sibling is needed is the finding below: a canonical peel may
not compact its rows, so its round walks `v`'s *original* row and
`livePot` cannot pay for it, while `staticPot` can — at the same
linear total, since `staticPot F univ = slotCount F` either way.

## The finding — route 1 needs one more contract than it looks

Route 1 as scoped ("counting-sort the adjacency rows by index once,
which makes the bucket order a function of `G` alone; the selection is
that canonical run's pop") does **not** close on the landed contracts,
and this file does not pretend otherwise: `CovSelPeelIn` is stated
here and discharged here only at the *quadratic* `peelCom`, by
conservativity. The linear discharge is not landed. The obstruction is
sharper than wave 24's and worth recording exactly.

1. **The selection has to be named, and a bucket's pop is a function of
   the run, not of `(F, S)`.** `MinDegSel.pick` takes the graph and the
   live set and nothing else, so whatever the pass outputs must be
   *named* by a function of those two. A bucket queue's `O(1)` pop
   returns a member of the current minimum-degree bucket chosen by the
   structure's own order, which is a function of the machine's history.
   Two ways to close the gap, and only one of them is open here:
   **(a)** prove the pop equals a formula in `(F, S)` — wave 24 prices
   every candidate it examined (`min'` and the three families of its
   module docstring), and the cheapest known exact discipline for the
   least index of a bucket is a heap, i.e. route 2's `log`; or
   **(b)** *define* `pick` by replaying the run — legitimate, since the
   peel is deterministic and `S` determines the round index `n - |S|`
   and hence the state, but it makes the abstract selection a
   simulation of the machine rather than a formula, and it needs the
   run to be a function of `(F, S)` in the first place. That is what
   clause 2 is about.

2. **The history the replay must simulate includes the adjacency rows,
   which no landed contract pins.** The pushes a round makes into the
   buckets are its neighbours *in row order*. `DelAdjSt`
   (`SolveSweepAdj.lean:153`) deliberately leaves the row order free —
   it asks only that each live prefix list the current neighbours —
   and `CovAugAdjIn`'s postcondition is exactly a `DelAdjSt`, so the
   rows the peel receives are not a function of `G`. Counting-sorting
   them once repairs that at the *entry* to the peel. But wave 23's
   `delAdjCom` is a **swap-delete**: unlinking `v` from `u`'s row
   overwrites `v`'s slot with `u`'s last live entry
   (`adjCore_unlink`), so sortedness is destroyed in round one, and
   `AdjDeleteInW`'s postcondition — again just a `DelAdjSt` — does not
   say which permutation of the row survives. A replay-defined
   selection would therefore have to model the row array's whole
   evolution, which neither contract determines.

3. **The way out is to stop deleting.** A peel that never writes to
   the adjacency arrays keeps whatever row order it was handed, so one
   counting sort at entry makes the rows a function of `G` *for the
   whole run*, and the replay only has to model the buckets. The price
   is that a round then walks `v`'s original row, not its compacted
   one — which is precisely the charge `livePot` cannot carry and
   `staticPot` can. That is why §1 is here. What such a peel still
   owes, and what this leaf does not land, is: the counting-sort pass
   and its spec; the abstract bucket replay and its invariant (that
   bucket `d` holds exactly the live vertices of live-degree `d`, so
   its top attains the minimum); and the round program with its
   `O(1) + O(|N_F(v)|) + O(cursor rise)` spec. The cursor's own
   licence is landed (`minDeg_le_minDeg_erase_succ`), as is the loop
   rule it feeds (`peelLoop_linear_static_cursor`, §1).

Nothing in §0–§5 is conditional on that program: the residual, the
glue and the conservativity hold as stated, and a later leaf may
discharge `CovSelPeelIn` at any selection it can build. §0 is the two
lemmas such a leaf needs first: the constructor that turns a bucket
pop into a `MinDegSel`, and the countdown at a freed tie-break.
-/

/-! ## §0 The selection kit a bucket round needs

Three facts about `MinDegSel` that wave 24 left implicit and any peel
programmed against a freed tie-break needs on its first page: the
constructor from minimality (`MinDegSel.ofMin`), the countdown
convention (`selRankAux_peel_step`), and the identification of the
pick's degree with `minDeg` (`card_nbrsIn_pick_eq_minDeg`, stated in
`Lax3Proofs.Prog` below because `minDeg` lives there). -/

namespace Lax3Proofs.CoverRoutine

open Lax3Proofs.Augmentation (nbrsIn)

variable {n : ℕ}

/-- **A minimum-degree pop is an attaining selection.** What a bucket
round can actually prove of its answer is *minimality* — the popped
vertex is live and no live vertex has smaller degree (the shape of
`eq_minDegVert_of_bucket`'s first two hypotheses, without its third,
the least-index clause no constant-time pop provides). That is already
`MinDegSel.attains`: minimality and membership pin the `inf'` from both
sides. -/
def MinDegSel.ofMin
    (p : (F : SimpleGraph (Fin n)) → (S : Finset (Fin n)) → S.Nonempty → Fin n)
    (hmem : ∀ F S hS, p F S hS ∈ S)
    (hmin : ∀ (F : SimpleGraph (Fin n)) (S : Finset (Fin n)) (hS : S.Nonempty),
      ∀ u ∈ S, (nbrsIn F S (p F S hS)).card ≤ (nbrsIn F S u).card) :
    MinDegSel n where
  pick := p
  mem := hmem
  attains := fun F S hS =>
    le_antisymm
      (Finset.le_inf' hS (fun v => (nbrsIn F S v).card) (hmin F S hS))
      (Finset.inf'_le _ (hmem F S hS))

/-- **One round of the countdown at a freed tie-break** —
`mdRankAux_peel_step` (`SolveSweepMdPeel.lean:1235`) at an arbitrary
attaining selection: the round's vertex is `sel`'s pick of the live
set, its rank is the live count minus one — so the *first* vertex
peeled from a live set of `N` gets `N - 1` — and every still-live
vertex keeps the rank the whole peel gives it. The convention is not
optional: an off-by-one here produces a *different* permutation that
still typechecks against `RankArr`. -/
theorem selRankAux_peel_step (sel : MinDegSel n) (F : SimpleGraph (Fin n))
    {S : Finset (Fin n)} (hS : S.Nonempty) :
    selRankAux sel F S (sel.pick F S hS) = S.card - 1 ∧
      ∀ x ∈ S.erase (sel.pick F S hS),
        selRankAux sel F S x = selRankAux sel F (S.erase (sel.pick F S hS)) x := by
  refine ⟨by rw [selRankAux_of_nonempty sel F hS, if_pos rfl], ?_⟩
  intro x hx
  rw [selRankAux_of_nonempty sel F hS, if_neg (Finset.ne_of_mem_erase hx)]

end Lax3Proofs.CoverRoutine

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.Augmentation (nbrsIn)

/-- **An attaining selection stands at the live minimum degree.** So
wave 24 §4's cursor licence `minDeg_le_minDeg_erase_succ` applies to a
peel at *any* `sel`, not just at the pinned one: the bucket the round
pops from is `minDeg F S hS`, and that falls by at most one per round —
which is the hypothesis `peelLoop_linear_cursor` and
`peelLoop_linear_static_cursor` charge the cursor against. -/
theorem card_nbrsIn_pick_eq_minDeg {N : ℕ}
    (sel : Lax3Proofs.CoverRoutine.MinDegSel N) (F : SimpleGraph (Fin N))
    (S : Finset (Fin N)) (hS : S.Nonempty) :
    (nbrsIn F S (sel.pick F S hS)).card = minDeg F S hS :=
  sel.attains F S hS

/-! ## §1 The static-degree potential, and the two loop rules at it

Wave 24's `livePot` is the total *current* degree of the live set and
falls by twice the peeled vertex's current degree. `staticPot` is the
total *original* degree of the live set and falls by exactly the peeled
vertex's original degree. Both start at `slotCount F`; the second is
what a peel that does not compact its rows can afford to be charged
against. -/

/-- **The static-degree potential**: the total degree *in `F`* of the
live set `S`. Unlike `livePot` it does not shrink as neighbours are
peeled away — it is the cost of walking each live vertex's row as the
region was originally laid out. -/
noncomputable def staticPot {N : ℕ} (F : SimpleGraph (Fin N))
    (S : Finset (Fin N)) : ℕ :=
  ∑ u ∈ S, (F.neighborSet u).ncard

/-- **The static amortization, in one line.** Peeling `v` drops the
static potential by exactly `v`'s original degree — its own row and
nothing else, since no survivor's row is touched. A round charged
`b·|N_F(v)|` is therefore paid for out of the potential's own fall,
exactly (no factor of two, unlike `livePot_erase`). -/
theorem staticPot_erase {N : ℕ} (F : SimpleGraph (Fin N)) (S : Finset (Fin N))
    {v : Fin N} (hv : v ∈ S) :
    staticPot F S = (F.neighborSet v).ncard + staticPot F (S.erase v) :=
  (Finset.add_sum_erase S (fun u => (F.neighborSet u).ncard) hv).symm

/-- The static potential starts at the slot count — the same starting
value as `livePot` (`livePot_univ`), so the two rules give budgets in
the same `m`. -/
theorem staticPot_univ {N : ℕ} (F : SimpleGraph (Fin N)) :
    staticPot F Finset.univ = slotCount F := rfl

/-- **The peel loop at `a·N + b·m`, charged in the original degree.**
`peelLoop_linear` with `livePot` replaced by `staticPot`: a loop whose
every turn peels one vertex `v` out of the live set at a cost affine in
`v`'s degree *in `F`* runs inside `a·N + b·(slot count) + O(1)`. This
is the rule for a peel that reads rows without compacting them —
whose round cost is the original degree, which `livePot` cannot pay
for. -/
theorem peelLoop_linear_static {B N : ℕ} {F : SimpleGraph (Fin N)}
    {bc : Cond} {body : Com} (I : Env → Prop) (Sof : Env → Finset (Fin N)) (a b : ℕ)
    (hdef : ∀ σ, I σ → ∃ v, bc.evalB B σ = some v)
    (hstep : ∀ σ, I σ → bc.evalB B σ = some true →
      ∃ (v : Fin N) (σ' : Env) (K : ℕ), v ∈ Sof σ ∧ Run B body σ σ' K ∧ I σ' ∧
        Sof σ' = (Sof σ).erase v ∧
        1 + bc.size + K ≤ a + b * (F.neighborSet v).ncard) :
    Spec B (fun σ => I σ ∧ Sof σ = Finset.univ) (.while bc body)
      (fun _ σ' => I σ' ∧ bc.evalB B σ' = some false)
      (a * N + b * slotCount F + 1 + bc.size) := by
  classical
  refine Spec.while_potential I
    (fun σ => a * (Sof σ).card + b * staticPot F (Sof σ)) hdef ?_ (fun _ h => h.1) ?_
  · intro σ hI hv
    obtain ⟨v, σ', K, hvS, hrun, hI', hSof, hcost⟩ := hstep σ hI hv
    refine ⟨σ', K, hrun, hI', ?_⟩
    show 1 + bc.size + K + (a * (Sof σ').card + b * staticPot F (Sof σ'))
      ≤ a * (Sof σ).card + b * staticPot F (Sof σ)
    obtain ⟨c, hc⟩ : ∃ c, (Sof σ).card = c + 1 := by
      have := Finset.card_pos.mpr (⟨v, hvS⟩ : (Sof σ).Nonempty)
      exact ⟨(Sof σ).card - 1, by omega⟩
    have hcard : (Sof σ').card = c := by
      rw [hSof, Finset.card_erase_of_mem hvS, hc]
      omega
    have hpot : staticPot F (Sof σ)
        = (F.neighborSet v).ncard + staticPot F (Sof σ') := by
      rw [hSof]; exact staticPot_erase F (Sof σ) hvS
    have hdist : b * staticPot F (Sof σ)
        = b * (F.neighborSet v).ncard + b * staticPot F (Sof σ') := by
      rw [hpot]; ring
    have hac : a * (c + 1) = a * c + a := by ring
    rw [hcard, hc, hdist, hac]
    omega
  · rintro σ ⟨-, huniv⟩
    show a * (Sof σ).card + b * staticPot F (Sof σ) + 1 + bc.size
      ≤ a * N + b * slotCount F + 1 + bc.size
    have hcard : (Sof σ).card = N := by
      rw [huniv, Finset.card_univ, Fintype.card_fin]
    have hpot : staticPot F (Sof σ) = slotCount F := by rw [huniv, staticPot_univ]
    rw [hcard, hpot]

/-- **The static peel loop with a cursor.** `peelLoop_linear_cursor` at
`staticPot`: the round may in addition pay `e` per step of a cursor it
drives upward, provided the cursor falls by at most one per round — the
bucket cursor over degree levels, whose licence is
`minDeg_le_minDeg_erase_succ`. The cursor's total rise is `≤ 2N` and is
charged in the potential's `e·(N - cur)` term. -/
theorem peelLoop_linear_static_cursor {B N : ℕ} {F : SimpleGraph (Fin N)}
    {bc : Cond} {body : Com} (I : Env → Prop) (Sof : Env → Finset (Fin N))
    (cur : Env → ℕ) (a b e : ℕ)
    (hcurN : ∀ σ, I σ → cur σ ≤ N)
    (hdef : ∀ σ, I σ → ∃ v, bc.evalB B σ = some v)
    (hstep : ∀ σ, I σ → bc.evalB B σ = some true →
      ∃ (v : Fin N) (σ' : Env) (K : ℕ), v ∈ Sof σ ∧ Run B body σ σ' K ∧ I σ' ∧
        Sof σ' = (Sof σ).erase v ∧ cur σ ≤ cur σ' + 1 ∧
        1 + bc.size + K ≤ a + b * (F.neighborSet v).ncard
          + e * (cur σ' + 1 - cur σ)) :
    Spec B (fun σ => I σ ∧ Sof σ = Finset.univ) (.while bc body)
      (fun _ σ' => I σ' ∧ bc.evalB B σ' = some false)
      ((a + e) * N + b * slotCount F + e * N + 1 + bc.size) := by
  classical
  refine Spec.while_potential I
    (fun σ => (a + e) * (Sof σ).card + b * staticPot F (Sof σ) + e * (N - cur σ))
    hdef ?_ (fun _ h => h.1) ?_
  · intro σ hI hv
    obtain ⟨v, σ', K, hvS, hrun, hI', hSof, hcurdrop, hcost⟩ := hstep σ hI hv
    refine ⟨σ', K, hrun, hI', ?_⟩
    show 1 + bc.size + K
        + ((a + e) * (Sof σ').card + b * staticPot F (Sof σ') + e * (N - cur σ'))
      ≤ (a + e) * (Sof σ).card + b * staticPot F (Sof σ) + e * (N - cur σ)
    obtain ⟨c, hc⟩ : ∃ c, (Sof σ).card = c + 1 := by
      have := Finset.card_pos.mpr (⟨v, hvS⟩ : (Sof σ).Nonempty)
      exact ⟨(Sof σ).card - 1, by omega⟩
    have hcard : (Sof σ').card = c := by
      rw [hSof, Finset.card_erase_of_mem hvS, hc]
      omega
    have hpot : staticPot F (Sof σ)
        = (F.neighborSet v).ncard + staticPot F (Sof σ') := by
      rw [hSof]; exact staticPot_erase F (Sof σ) hvS
    have hdist : b * staticPot F (Sof σ)
        = b * (F.neighborSet v).ncard + b * staticPot F (Sof σ') := by
      rw [hpot]; ring
    have hac : (a + e) * (c + 1) = (a + e) * c + (a + e) := by ring
    have hkey : e * (cur σ' + 1 - cur σ) + e * (N - cur σ')
        ≤ e + e * (N - cur σ) := by
      have hx := hcurN σ hI
      have hy := hcurN σ' hI'
      have h1 : (cur σ' + 1 - cur σ) + (N - cur σ') ≤ 1 + (N - cur σ) := by omega
      calc e * (cur σ' + 1 - cur σ) + e * (N - cur σ')
          = e * ((cur σ' + 1 - cur σ) + (N - cur σ')) := by ring
        _ ≤ e * (1 + (N - cur σ)) := Nat.mul_le_mul_left e h1
        _ = e + e * (N - cur σ) := by ring
    rw [hcard, hc, hdist, hac]
    omega
  · rintro σ ⟨hI, huniv⟩
    show (a + e) * (Sof σ).card + b * staticPot F (Sof σ) + e * (N - cur σ) + 1 + bc.size
      ≤ (a + e) * N + b * slotCount F + e * N + 1 + bc.size
    have hcard : (Sof σ).card = N := by
      rw [huniv, Finset.card_univ, Fintype.card_fin]
    have hcur : e * (N - cur σ) ≤ e * N := Nat.mul_le_mul_left e (Nat.sub_le _ _)
    have hpot : staticPot F (Sof σ) = slotCount F := by rw [huniv, staticPot_univ]
    rw [hcard, hpot]
    omega

/-! ## §2–§5 The residuals at a freed tie-break -/

open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.CoverRoutine (MinDegSel mdSel mdChain mdPerm selChain selPerm
  selOrderingRoutine mdOrderingRoutine selChain_mdSel selPerm_mdSel
  selOrderingRoutine_mdSel)

/-! ### §2 The augmentation pass at a freed tie-break -/

/-- **Named residual (1a-i) at an arbitrary attaining selection** —
`CovAugAdjIn` (`SolveSweepOrder.lean:413`) with the deterministic chain
`mdChain` replaced by `selChain (sel A.N)`: from `CovOrderIn`'s exact
precondition, compute the `R` augmentation rounds along `sel`'s
elimination ranking and leave the augmented graph
`(selChain (sel A.N) A.G R).toGraph` as a deletable adjacency region,
preserving the arena, the allocations, and both scratch descriptors.
Every clause is `CovAugAdjIn`'s, verbatim, at the new chain. -/
def CovAugAdjSelIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (sel : ∀ m : ℕ, MinDegSel m)
    (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (aoO ajO dgO mtO : ℕ → String)
    (Sag Smp Ssw : ℕ → Env → Prop) (agC : ℕ → Com)
    (Kag : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ) :
    Prop :=
  ∀ x ∈ mcD n G c w,
    ∀ j, j < (Headline.headlineSetup C hC φ).depth →
    ∀ A : Arena ((Headline.headlineSetup C hC φ).pal j) n,
      Adm j A → ¬ A.G = ⊥ →
      Spec (mcB q x)
        (fun σ => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ ∧
          A.N ≤ (σ.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ.arrs (co j)).length ∧ Sag j σ ∧ Smp j σ ∧ Ssw j σ)
        (agC j)
        (fun _ σ' => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ' ∧
          DelAdjSt (aoO j) (ajO j) (dgO j) (mtO j)
            (selChain (sel A.N) A.G R).toGraph ∅ σ' ∧
          A.N ≤ (σ'.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ'.arrs (co j)).length ∧ Smp j σ' ∧ Ssw j σ')
        (Kag j A)

/-! ### §3 The peel pass at a freed tie-break -/

/-- **Named residual (1a-ii) at an arbitrary attaining selection** —
`CovMdPeelIn` (`SolveSweepOrder.lean:451`) with the permutation
`mdPerm (mdChain A.G R).toGraph` replaced by
`selPerm (sel A.N) (selChain (sel A.N) A.G R).toGraph`, and **nothing
else changed**: the same `DelAdjSt` precondition at the same augmented
graph, the same windowed `≤ length` allocations for `ca`/`co`, the same
arena preservation, the same scratch discipline (`Smp` consumed, `Ssw`
preserved), the same `mcB q x` word bound and the same budget shape
`Kmp j A`.

At `sel = mdSel` this *is* `CovMdPeelIn` (§5), so the freed tie-break
weakens nothing; what it buys is that the peel's output is no longer
pinned to `minDegVert`'s least-index choice, which wave 24 showed no
constant-time selection can produce. -/
def CovSelPeelIn (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (sel : ∀ m : ℕ, MinDegSel m)
    (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (ra : ℕ → String) (aoO ajO dgO mtO : ℕ → String)
    (Smp Ssw : ℕ → Env → Prop) (mpC : ℕ → Com)
    (Kmp : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ) :
    Prop :=
  ∀ x ∈ mcD n G c w,
    ∀ j, j < (Headline.headlineSetup C hC φ).depth →
    ∀ A : Arena ((Headline.headlineSetup C hC φ).pal j) n,
      Adm j A → ¬ A.G = ⊥ →
      Spec (mcB q x)
        (fun σ => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ ∧
          DelAdjSt (aoO j) (ajO j) (dgO j) (mtO j)
            (selChain (sel A.N) A.G R).toGraph ∅ σ ∧
          A.N ≤ (σ.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ.arrs (co j)).length ∧ Smp j σ ∧ Ssw j σ)
        (mpC j)
        (fun _ σ' => ArenaStW (arenaNames j) (hbf j)
            (Impl.ofArena A (htabF j A)) σ' ∧
          RankArr (ra j)
            (selPerm (sel A.N) (selChain (sel A.N) A.G R).toGraph) σ' ∧
          A.N ≤ (σ'.arrs (ca j)).length ∧
          A.N + 1 ≤ (σ'.arrs (co j)).length ∧ Ssw j σ')
        (Kmp j A)

/-! ### §4 The glue -/

open Classical in
/-- **Residual (1a) of the cover leaf at a freed tie-break**:
`CovOrderIn` holds — verbatim, at `ord := selOrderingRoutine sel R` —
of the sequenced program `agC j ; mpC j` at the summed budget, with the
ordering pass's scratch the conjunction of the two passes'. The rank
array the peel leaves *is* the routine's order:
`(selOrderingRoutine sel R A.N A.G).order` unfolds to
`selPerm (sel A.N) (selChain (sel A.N) A.G R).toGraph`, by `rfl`. The
proof is `covOrderIn_of_aug_mdPeel`'s, line for line. -/
theorem covOrderIn_of_aug_selPeel (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (sel : ∀ m : ℕ, MinDegSel m) (R : ℕ) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (ra : ℕ → String) (aoO ajO dgO mtO : ℕ → String)
    (Sag Smp Ssw : ℕ → Env → Prop) (agC mpC : ℕ → Com)
    (Kag Kmp : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (hag : CovAugAdjSelIn C hC φ sel R G c w q ℓp htabF hbf Adm ca co
      aoO ajO dgO mtO Sag Smp Ssw agC Kag)
    (hmp : CovSelPeelIn C hC φ sel R G c w q ℓp htabF hbf Adm ca co ra
      aoO ajO dgO mtO Smp Ssw mpC Kmp) :
    CovOrderIn C hC φ (selOrderingRoutine sel R) G c w q ℓp htabF hbf Adm ca co ra
      (fun j σ => Sag j σ ∧ Smp j σ) Ssw
      (fun j => .seq (agC j) (mpC j))
      (fun j A => Kag j A + Kmp j A) := by
  intro x hx j hj A hAdm hbot
  refine Spec.seq
    ((hag x hx j hj A hAdm hbot).pre ?_)
    (hmp x hx j hj A hAdm hbot) ?_ ?_
  · -- the ordering precondition is the augmentation pass's
    rintro σ ⟨hA, hca, hco, ⟨hSag, hSmp⟩, hSsw⟩
    exact ⟨hA, hca, hco, hSag, hSmp, hSsw⟩
  · -- the augmentation pass lands in the peel's precondition
    rintro σ σ' - ⟨hA', hadj', hca', hco', hSmp', hSsw'⟩
    exact ⟨hA', hadj', hca', hco', hSmp', hSsw'⟩
  · -- the peel's postcondition is the ordering's: the rank array is at
    -- the routine's order, definitionally
    rintro σ σ' σ'' - - ⟨hA'', hra'', hca'', hco'', hSsw''⟩
    exact ⟨hA'', hra'', hca'', hco'', hSsw''⟩

/-! ### §5 Conservativity: at the pinned choice, nothing has changed

The three statements above are the landed ones at `sel = mdSel`. So
freeing the tie-break costs nothing that was already proved, and wave
23's discharge of `CovMdPeelIn` transports to `CovSelPeelIn` on the
nose. -/

/-- The peel's target graph at the pinned selection is the landed one. -/
theorem selChain_toGraph_mdSel {m : ℕ} (G : SimpleGraph (Fin m)) (R : ℕ) :
    (selChain (mdSel m) G R).toGraph = (mdChain G R).toGraph := by
  rw [selChain_mdSel G R]

/-- The peel's target permutation at the pinned selection is the landed
one — the postcondition of `CovSelPeelIn` at `mdSel` is literally
`CovMdPeelIn`'s. -/
theorem selPerm_selChain_mdSel {m : ℕ} (G : SimpleGraph (Fin m)) (R : ℕ) :
    selPerm (mdSel m) (selChain (mdSel m) G R).toGraph
      = mdPerm (mdChain G R).toGraph := by
  rw [selChain_toGraph_mdSel G R, selPerm_mdSel]

/-- **The augmentation residual at the pinned selection is the landed
one.** -/
theorem covAugAdjSelIn_mdSel (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (aoO ajO dgO mtO : ℕ → String)
    (Sag Smp Ssw : ℕ → Env → Prop) (agC : ℕ → Com)
    (Kag : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ) :
    CovAugAdjSelIn C hC φ (fun m => mdSel m) R G c w q ℓp htabF hbf Adm ca co
        aoO ajO dgO mtO Sag Smp Ssw agC Kag ↔
      CovAugAdjIn C hC φ R G c w q ℓp htabF hbf Adm ca co
        aoO ajO dgO mtO Sag Smp Ssw agC Kag := by
  unfold CovAugAdjSelIn CovAugAdjIn
  simp only [selChain_toGraph_mdSel]

/-- **The peel residual at the pinned selection is the landed one.**
This is the precise sense in which `CovSelPeelIn` does not weaken
`CovMdPeelIn`: the two `Prop`s coincide at `sel = mdSel`, clause for
clause. -/
theorem covSelPeelIn_mdSel (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (ra : ℕ → String) (aoO ajO dgO mtO : ℕ → String)
    (Smp Ssw : ℕ → Env → Prop) (mpC : ℕ → Com)
    (Kmp : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ) :
    CovSelPeelIn C hC φ (fun m => mdSel m) R G c w q ℓp htabF hbf Adm ca co ra
        aoO ajO dgO mtO Smp Ssw mpC Kmp ↔
      CovMdPeelIn C hC φ R G c w q ℓp htabF hbf Adm ca co ra
        aoO ajO dgO mtO Smp Ssw mpC Kmp := by
  unfold CovSelPeelIn CovMdPeelIn
  simp only [selChain_toGraph_mdSel, selPerm_mdSel]

/-- **The freed residual is discharged at the pinned selection, by wave
23's program, verbatim.** `CovSelPeelIn` at `sel = mdSel` holds of
`peelCom` at `86·A.N² + 43·A.N + 14` — the quadratic budget, because
`peelCom` is the full-carrier scan. The *linear* budget is not landed
here; see the module docstring's finding for exactly what it still
owes. -/
theorem covSelPeelIn_peelCom_mdSel (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (ra : ℕ → String) (aoO ajO dgO mtO : ℕ → String)
    (Ssw : ℕ → Env → Prop) (hq : 1 ≤ q)
    (hnd : ∀ j, aoO j ≠ ajO j ∧ aoO j ≠ mtO j ∧ aoO j ≠ dgO j ∧
      ajO j ≠ mtO j ∧ ajO j ≠ dgO j ∧ mtO j ≠ dgO j ∧
      ra j ≠ aoO j ∧ ra j ≠ ajO j ∧ ra j ≠ dgO j ∧ ra j ≠ mtO j)
    (harn : ∀ (j : ℕ) (b : String), b = (arenaNames j).off ∨
      b = (arenaNames j).tgt ∨ b = (arenaNames j).col ∨
      b = (arenaNames j).up ∨ b = (arenaNames j).hist →
      b ≠ ra j ∧ b ≠ ajO j ∧ b ≠ dgO j ∧ b ≠ mtO j)
    (hSsw : ∀ (j : ℕ) (σ σ' : Env),
      (∀ b : String, b ≠ ra j → b ≠ ajO j → b ≠ dgO j → b ≠ mtO j →
        σ'.arrs b = σ.arrs b) →
      (∀ b : String, (σ'.arrs b).length = (σ.arrs b).length) →
      (∀ y : String, y ≠ "mp.n" → y ≠ "mp.u" → y ≠ "mp.b" → y ≠ "mp.k" →
        y ≠ "mp.r" → y ≠ "mp.v" → y ≠ "dl.i" → y ≠ "dl.w" → y ≠ "dl.p" →
        y ≠ "dl.l" → y ≠ "dl.u" → y ≠ "dl.q" → σ'.vars y = σ.vars y) →
      Ssw j σ → Ssw j σ') :
    CovSelPeelIn C hC φ (fun m => mdSel m) R G c w q ℓp htabF hbf Adm ca co ra
      aoO ajO dgO mtO (fun j σ => n ≤ (σ.arrs (ra j)).length) Ssw
      (fun j => peelCom (aoO j) (ajO j) (dgO j) (mtO j) (ra j) (arenaNames j).nN)
      (fun _ A => 86 * A.N * A.N + 43 * A.N + 14) :=
  (covSelPeelIn_mdSel C hC φ R G c w q ℓp htabF hbf Adm ca co ra
    aoO ajO dgO mtO _ Ssw _ _).mpr
    (covMdPeelIn_peelCom C hC φ R G c w q ℓp htabF hbf Adm ca co ra
      aoO ajO dgO mtO Ssw hq hnd harn hSsw)

/-- **At the pinned selection the new glue is the landed glue.** The
conclusion of `covOrderIn_of_aug_selPeel` at `sel = mdSel` is
`CovOrderIn … (mdOrderingRoutine R) …`, the conclusion of
`covOrderIn_of_aug_mdPeel`, because `selOrderingRoutine_mdSel` is an
equality of routines. So §4 subsumes the landed theorem rather than
sitting beside it. -/
theorem covOrderIn_of_aug_mdPeel_of_sel (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (R : ℕ) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String) (ra : ℕ → String) (aoO ajO dgO mtO : ℕ → String)
    (Sag Smp Ssw : ℕ → Env → Prop) (agC mpC : ℕ → Com)
    (Kag Kmp : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → ℕ)
    (hag : CovAugAdjIn C hC φ R G c w q ℓp htabF hbf Adm ca co
      aoO ajO dgO mtO Sag Smp Ssw agC Kag)
    (hmp : CovMdPeelIn C hC φ R G c w q ℓp htabF hbf Adm ca co ra
      aoO ajO dgO mtO Smp Ssw mpC Kmp) :
    CovOrderIn C hC φ (mdOrderingRoutine R) G c w q ℓp htabF hbf Adm ca co ra
      (fun j σ => Sag j σ ∧ Smp j σ) Ssw
      (fun j => .seq (agC j) (mpC j))
      (fun j A => Kag j A + Kmp j A) := by
  have h := covOrderIn_of_aug_selPeel C hC φ (fun m => mdSel m) R G c w q ℓp
    htabF hbf Adm ca co ra aoO ajO dgO mtO Sag Smp Ssw agC mpC Kag Kmp
    ((covAugAdjSelIn_mdSel C hC φ R G c w q ℓp htabF hbf Adm ca co
      aoO ajO dgO mtO Sag Smp Ssw agC Kag).mpr hag)
    ((covSelPeelIn_mdSel C hC φ R G c w q ℓp htabF hbf Adm ca co ra
      aoO ajO dgO mtO Smp Ssw mpC Kmp).mpr hmp)
  rwa [selOrderingRoutine_mdSel R] at h

end Lax3Proofs.Prog

