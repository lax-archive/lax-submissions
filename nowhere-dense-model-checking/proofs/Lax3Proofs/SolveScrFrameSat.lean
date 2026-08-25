import Lax3Proofs.SolveMachPrepSeam
import Lax3Proofs.SolveSegRead

/-!
# F6c12 (residual 1) — the scratch descriptor's new premises, satisfied

`SolveMachPrepSeam.rankScr_not_length_only` closed the length-only
transport `hscrLen` to any scratch descriptor that carries the
child-building pass's clean-scratch clause. `SolveChain` §3b replaced
it, at every site, by two premises a content-carrying descriptor can
meet — `ScrFrame` (agreement on the descriptor's read pool) and
`ScrStep` (level `j`'s own pool, framed, plus the level-`(j+1)`
descriptor the inner block restores).

**A replacement premise is only a fix if something can satisfy it.**
This file exhibits that something, concretely and at the canonical
names: the level-indexed tower

`RankScrTower D j σ := ∀ i ∈ [j, D], RankScr (rankScrName i)
(arenaNames i).nN σ`

over the canonical per-level rank scratch `rankScrName j = lv "sa.r" j`.
It is of exactly the shape the seam asks for — `rankScrTower_succ`
splits it as `RankScr (rankScrName j) (arenaNames j).nN σ ∧ …` — and:

* §2 it satisfies **`ScrFrame`** and **`ScrStep`** at the read pools
  `LV j = [(arenaNames j).nN]`, `LR j = [rankScrName j]`;
* §3 it satisfies the prep segment's descriptor tower `hscrDown`
  (`SolveMachPrepSeam.centrePrep_of_childLoadScr`'s hypothesis) and
  delivers `restrictCom_specW`'s content precondition at every level's
  own window (`rankScrTower_take`, through `ArenaStW.n_eq`);
* §4 it is **not vacuous**, and not vacuous *in the way that matters*:
  `rankScrEnv` is a concrete state at which it holds with a non-empty
  window and a scratch long enough to hold it — the exact configuration
  `rankScr_not_length_only` proves impossible. `rankScrTower_refutes_len`
  turns that around: this descriptor *provably* fails `hscrLen`, so the
  five sites could not have kept it;
* §5 the sites' remaining side conditions are discharged for this
  witness wherever the `lv` mechanism decides them
  (`hctrLV`, `hLVbt`, `hLRbot`), and `hfreshV` is shown to follow from
  the landed `hfreshS` — the level's carrier cell is already in
  `levelScalars`.

What this file does **not** claim: the two per-command conditions
`ScrFree LV LR j (covC j)` and `ScrFree LV LR j (readC j)` are about
programs the instantiator has not fixed yet, so they cannot be
discharged here. They are syntactic (`Com.wvars`/`Com.warrs`) and of
exactly the kind the campaign already takes from a discharger — the
same status as `hcovOwn`, `hprepOwn`, `hreadOwn`.

## Hazards honoured

No program, no budget, no stage. Nothing here is quantified over the
carrier, so no `N`-indexed term of any degree is introduced.
-/

set_option autoImplicit false

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver

/-! ## §1 The canonical rank scratch, and the descriptor over it -/

/-- **The level's rank scratch array**, at the canonical `lv` family —
the array `restrictCom_specW` ranks into and returns clean. A fresh
base of the length the `lv` mechanism requires, distinct from the
arena's five, the level table, the leaf's four and the loop counter. -/
def rankScrName (j : ℕ) : String := lv "sa.r" j

/-- **The witness descriptor**: the level's own clean rank scratch and
every deeper level's. The tower is what the prep segment's `hscrDown`
asks for; the level's own clause is what `restrictCom_specW` asks
for. -/
def RankScrTower (D : ℕ) (j : ℕ) (σ : Env) : Prop :=
  ∀ i, j ≤ i → i ≤ D → RankScr (rankScrName i) (arenaNames i).nN σ

/-- **The descriptor is of the seam's shape**: the level's own
clean-scratch clause, conjoined with the rest. -/
theorem rankScrTower_succ {D j : ℕ} {σ : Env} (hjD : j ≤ D) :
    RankScrTower D j σ ↔
      (RankScr (rankScrName j) (arenaNames j).nN σ ∧
        RankScrTower D (j + 1) σ) := by
  constructor
  · intro h
    exact ⟨h j le_rfl hjD, fun i hi hiD => h i (by omega) hiD⟩
  · rintro ⟨h0, h1⟩ i hi hiD
    rcases Nat.lt_or_ge j i with hlt | hge
    · exact h1 i hlt hiD
    · obtain rfl : i = j := le_antisymm hge hi
      exact h0

/-! ## §2 The two premises of `SolveChain` §3b, satisfied -/

/-- The descriptor's scalar read pool: the level's carrier cell. -/
def rankScrLV (j : ℕ) : List String := [(arenaNames j).nN]

/-- The descriptor's array read pool: the level's rank scratch. -/
def rankScrLR (j : ℕ) : List String := [rankScrName j]

/-- **`ScrFrame`, satisfied.** Each clause of the tower is a `RankScr`
at some level `i ≥ j`, and `ScrAgree` hands over exactly that level's
array and cell — which is what `rankScr_frame` consumes. No length
clause is used at all. -/
theorem rankScrTower_scrFrame (D : ℕ) :
    ScrFrame (RankScrTower D) rankScrLV rankScrLR := by
  rintro j σ σ' h ⟨hV, hA⟩ - i hi hiD
  exact rankScr_frame (h i hi hiD)
    (hA i hi _ (by simp [rankScrLR])) (hV i hi _ (by simp [rankScrLV]))

/-- **`ScrStep`, satisfied.** The level's own clause crosses by
`rankScr_frame` on level `j`'s pool; every deeper clause is the
level-`(j+1)` descriptor the block restores. This is precisely the
split the inner block forces: it rewrites the deeper scratch, so no
frame reaches it. -/
theorem rankScrTower_scrStep (D : ℕ) :
    ScrStep (RankScrTower D) rankScrLV rankScrLR := by
  intro j σ σ' h h1 hV hA _hlen i hi hiD
  rcases Nat.lt_or_ge j i with hlt | hge
  · exact h1 i hlt hiD
  · obtain rfl : i = j := le_antisymm hge hi
    exact rankScr_frame (h i le_rfl hiD)
      (hA _ (by simp [rankScrLR])) (hV _ (by simp [rankScrLV]))

/-! ## §3 The descriptor carries content -/

/-- **The prep segment's descriptor tower, satisfied** — verbatim
`centrePrep_of_childLoadScr`'s `hscrDown` (and
`centrePrepAll_of_partsScr_chanTab`'s), at any depth bound. -/
theorem rankScrTower_down (D : ℕ) (j : ℕ) (σ : Env)
    (h : RankScrTower D j σ) : RankScrTower D (j + 1) σ :=
  fun i hi hiD => h i (by omega) hiD

/-- **The content clause, at `restrictCom_specW`'s spelling.** Under
the level's windowed contract the descriptor delivers exactly the clean
window the child-building pass's restrict stage demands — the one
*content* clause `hscrLen` could never have carried. -/
theorem rankScrTower_take {D j : ℕ} (hjD : j ≤ D) {Λ n₀ ℓp hb : ℕ}
    {A : Impl.MArena Λ n₀ ℓp} {σ : Env}
    (hA : ArenaStW (arenaNames j) hb A σ) (h : RankScrTower D j σ) :
    (σ.arrs (rankScrName j)).take A.N = arrOf A.N (fun _ => 0) :=
  rankScr_take hA (h j le_rfl hjD)

/-! ## §4 The descriptor is inhabited — with a non-empty window -/

/-- A state at which the whole tower holds with the window of **every**
level equal to `m`: every cell reads `m`, every array is `m` zeros. -/
def rankScrEnv (m : ℕ) : Env where
  vars := fun _ => m
  arrs := fun _ => arrOf m (fun _ => 0)
  inp := []
  out := []

@[simp] theorem rankScrEnv_vars (m : ℕ) (y : String) :
    (rankScrEnv m).vars y = m := rfl

@[simp] theorem rankScrEnv_arrs (m : ℕ) (b : String) :
    (rankScrEnv m).arrs b = arrOf m (fun _ => 0) := rfl

/-- **The witness is inhabited**, at every window size. -/
theorem rankScrTower_rankScrEnv (D m : ℕ) (j : ℕ) :
    RankScrTower D j (rankScrEnv m) := by
  intro i _ _
  show ((rankScrEnv m).arrs (rankScrName i)).take
      ((rankScrEnv m).vars (arenaNames i).nN)
    = arrOf ((rankScrEnv m).vars (arenaNames i).nN) (fun _ => 0)
  simp only [rankScrEnv_vars, rankScrEnv_arrs]
  exact List.take_of_length_le (by simp)

/-- **The witness provably fails `hscrLen`.** Any transport of this
descriptor along array lengths alone is inconsistent — the descriptor
holds at `rankScrEnv (m+1)`, whose window is non-empty and whose
scratch is exactly long enough, and that is the configuration
`rankScr_not_length_only` refutes.

So the five sites did not merely *prefer* a different premise: keeping
`hscrLen` and instantiating `Scr` with anything implying `RankScr` at
the level's own window would have made the instantiation
unsatisfiable. -/
theorem rankScrTower_refutes_len {D j m : ℕ} (hjD : j ≤ D)
    (hscrLen : ∀ σ σ', RankScrTower D j σ →
      (∀ b, (σ'.arrs b).length = (σ.arrs b).length) → RankScrTower D j σ') :
    False :=
  rankScr_not_length_only (Scr := RankScrTower D) (j := j)
    (ra := rankScrName j) (nN := (arenaNames j).nN)
    hscrLen (fun _ h => h j le_rfl hjD)
    (rankScrTower_rankScrEnv D (m + 1) j) (by simp) (by simp)

/-! ## §5 The sites' side conditions, for this witness -/

/-- The rank scratch of any level misses the arena's five, the level
table and the leaf's four, at any pair of levels — the `lv` mechanism's
fact, and `hLRbot`'s content at `botBlock_specScr`,
`blockSpec_leaf_guardScr` and `solveSpec_closed_scr`. -/
theorem rankScrName_notMem_bot (i j : ℕ) :
    rankScrName i
      ∉ ([botNa j, botFa j, botEa j, botXa j, (arenaNames j).tab] :
        List String) := by
  show lv "sa.r" i
    ∉ (["sb.n", "sb.f", "sb.e", "sb.x", "sa.b"] : List String).map (lv · j)
  exact lv_notMem_map (m := 4) (by decide) (by decide) (by decide) i j

/-- `hLRbot`, for this witness. -/
theorem rankScrLR_notMem_bot (j i : ℕ) (_ : j ≤ i) :
    ∀ a ∈ rankScrLR i,
      a ∉ ([botNa j, botFa j, botEa j, botXa j, (arenaNames j).tab] :
        List String) := by
  intro a ha
  simp only [rankScrLR, List.mem_cons, List.not_mem_nil, or_false] at ha
  subst ha
  exact rankScrName_notMem_bot i j

/-- `hLVbt`, for this witness — the carrier cell is fresh against the
leaf stage's scratch scalars (`canon_nN`). -/
theorem rankScrLV_notMem_bt (i : ℕ) : ∀ y ∈ rankScrLV i, y ∉ btScalars := by
  intro y hy
  simp only [rankScrLV, List.mem_cons, List.not_mem_nil, or_false] at hy
  subst hy
  exact canon_nN i

/-- The loop counter is not the carrier cell of **any** level — the
`lv` mechanism's fact at two levels, `ctrName_ne_nN`'s generalisation. -/
theorem ctrName_ne_nN' (j i : ℕ) : ctrName j ≠ (arenaNames i).nN :=
  lv_ne_of_base_ne (by decide) (by decide) j i

/-- `hctrLV`, for this witness. -/
theorem rankScrLV_ne_ctr (j i : ℕ) (_ : j ≤ i) : ctrName j ∉ rankScrLV i := by
  intro hy
  simp only [rankScrLV, List.mem_cons, List.not_mem_nil, or_false] at hy
  exact ctrName_ne_nN' j i hy

/-! ## §6 The witness survives everything else the chain asks of `Scr`

`RankScrTower` alone is not the descriptor the chain will run with: the
chain also asks for the leaf's four region lengths (`hscr`), the
cover's two output allocations (`hscrCov`), the child table
(`htabLen`), and the batch width. Every one of those is a clause about
array *lengths*, and `ScrFrame`/`ScrStep` are closed under conjunction
with any such clause (`ScrFrame.and_lens`, `ScrStep.and_lens`). So the
§2 witness is a witness for the real descriptor too, whatever the
allocation clauses turn out to be. -/

/-- **The satisfiability claim, in full**: for *any* family of
allocation clauses `P` — read off the arrays' lengths, which is what
every remaining demand on `Scr` is — the descriptor

`fun j σ => RankScrTower D j σ ∧ P j (array lengths at σ)`

satisfies both premises the five sites now take, at the read pools
`rankScrLV`/`rankScrLR`. It carries content (§3), it is inhabited with
a non-empty window (§4), and it *refutes* the length-only transport it
replaces (`rankScrTower_refutes_len`). -/
theorem rankScrTower_and_lens_sat (D : ℕ) (P : ℕ → (String → ℕ) → Prop) :
    ScrFrame (fun j σ => RankScrTower D j σ ∧ P j (fun b => (σ.arrs b).length))
        rankScrLV rankScrLR ∧
      ScrStep (fun j σ => RankScrTower D j σ ∧ P j (fun b => (σ.arrs b).length))
        rankScrLV rankScrLR :=
  ⟨(rankScrTower_scrFrame D).and_lens P, (rankScrTower_scrStep D).and_lens P⟩

/-- The fattened descriptor still delivers the prep segment's tower. -/
theorem rankScrTower_and_lens_down (D : ℕ) (P : ℕ → (String → ℕ) → Prop)
    (hP : ∀ j f, P j f → P (j + 1) f) (j : ℕ) (σ : Env)
    (h : RankScrTower D j σ ∧ P j (fun b => (σ.arrs b).length)) :
    RankScrTower D (j + 1) σ ∧ P (j + 1) (fun b => (σ.arrs b).length) :=
  ⟨rankScrTower_down D j σ h.1, hP j _ h.2⟩

/-- `hfreshV` is **free**: the descriptor's only scalar is the level's
carrier cell, which is already in `levelScalars j`, so the landed
`hfreshS` covers it. Only `hfreshR` — the rank scratch against the
deeper array pools — is a genuinely new name-pool fact, and it is of
the same `lv` shape as `hfreshA`. -/
theorem rankScrLV_fresh_of_freshS {LS : ℕ → List String}
    (hfreshS : ∀ j i, j < i → ∀ y ∈ ctrName j :: levelScalars j, y ∉ LS i)
    (j i : ℕ) (hji : j < i) : ∀ y ∈ rankScrLV j, y ∉ LS i := by
  intro y hy
  simp only [rankScrLV, List.mem_cons, List.not_mem_nil, or_false] at hy
  subst hy
  exact hfreshS j i hji _ (by simp [levelScalars])

end Lax3Proofs.Prog
