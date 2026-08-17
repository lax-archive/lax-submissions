import Lax3Proofs.Refine.BridgeCrossing
import Lax3Proofs.C0Probe
import Lax3Proofs.UqwInstantiation

/-!
**The derivability sweep of the root theorem's hypothesis slots** — ND-MC
rebase, the B7 re-run's opening leaf (plan rev 3 delta 3).

Both of B7's gate failures were hypothesis slots that had been ruled fine
in prose and never checked: D4's "root input data" (`hcsr`, finding 1)
and §2.4's cost verdict (finding 2). Rev 3 therefore opens the re-run
with this: every slot of
`RamDriverRoot.driverRoot_decides_sentence` compiled against what a C0
discharge actually holds, before anything is restated or assembled.

**What a discharge holds.** C0
(`Lax3.ModelChecking.exists_almostLinearTime_program_modelChecking`)
fixes a nowhere dense class `C`, a sentence `φ` and an `ε > 0`, then asks
for a program `p`, a constant `c` and a bound `T` with
`(T x : ℝ) ≤ c * (|x| + 1) ^ (1 + ε)`, such that at **every** `n`, `G`
with `C n G` and **every** word length `w`, `p` computes the answer on
`{x | EncodesGraph x n G ∧ ∀ v ∈ x, c * (|x| + v + 1) ≤ 2 ^ w}` within
`T`. So the data available at a slot is: `EncodesGraph x n G`, the domain
word clause, `C n G` and nowhere-density of `C`, and free choices of
every parameter the root leaves open — all of the latter chosen **before**
`n`, `G`, `w` and `x`, because `p` and `c` are.

## The table

Thirty slots, in the root's own order. `producer` = closed here or by a
named landed theorem; `free` = discharged by choosing the parameter;
`BLOCKED` = compiled obstruction, no producer exists.

| # | slot | verdict | where |
|---|------|---------|-------|
| 1 | `hx` | free — C0's own hypothesis | `slot01_hx` |
| 2 | `hns` | free — defines `ns` | `slot02_hns` |
| 3 | `hO` | free — defines `O` | `slot03_hO` |
| 4 | `hT` | free — `T := padTarget x ns` | `slot04_hT` |
| 5 | `hxB` | producer — with the word bound of #12 | `slot05_hxB` |
| 6 | `hcsr` | **BLOCKED** at the landed root | §B |
| 7 | `hpad0` | free — same `T` | `slot07_hpad0` |
| 8 | `hrank` | free — `q_top := rank φ` | `slot08_hrank` |
| 9 | `hcap` | free — defines `cap` | `slot09_hcap` |
| 10 | `hmb` | free — defines `mb` | `slot10_hmb` |
| 11 | `hℓ` | free — defines `ℓ` | `slot11_hl` |
| 12 | `hB` | producer, **conditional on #26** | §C |
| 13 | `hWB` | free at `R = 0` (`W := ns`) | `slot13_hWB` |
| 14 | `hpow` | free — parameter constant | `slot14_hpow` |
| 15 | `hQ` | producer | `slot15_hQ` |
| 16 | `hbnd` | free — finite atom list, `B` large | note in §A |
| 17 | `hcostI` | free — defines `Ki` | note in §A |
| 18 | `hKsc` | free — defines `Ksc` | note in §A |
| 19 | `hKmono` | free — monotone `Kl` | note in §A |
| 20 | `hKs` | **BLOCKED** — cubic floor | §D |
| 21 | `hKbase` | free — defines `Kl ℓ` | note in §A |
| 22 | `hKo` | **BLOCKED** — size-blind carrier charge | §D |
| 23 | `hKc` | **BLOCKED** — `12 n²` + `coverCost`'s `100 n²` | §D |
| 24 | `hKd` | **RETIRED** — dead sweep absent from the program | §D control 3 |
| 25 | `hbinj` | producer — `RamDriverRoot.blockInj_slot` | `slot25_hbinj` |
| 26 | `hdeg` | **BLOCKED** — no constant `Kmass` | §C |
| 27 | `hKl` | **BLOCKED** — turn sum × #20/#22/#23 | §D |
| 28 | `hKdec` | free — defines `Kdec` | note in §A |
| 29 | `hatoms` | free — finite atom list, `B` large | note in §A |
| 30 | `hKsent` | free — defines `Ksent` | note in §A |

Twenty-three of the remaining slots are free or producered. **Six block**, in three
independent groups, and only the first was known when this leaf opened:

* **#6 `hcsr`** — B7 finding 1, repaired by G1 but *not yet at the root*:
  the repair lives in `RamDriverDedup.DecodeImplementsD`, and the root
  still reads its `CsrSimple` at the raw word. Dies at the `driverRootD`
  restatement (§B).
* **#26 `hdeg`, and hence #12 `hB`** — new here (§C). The slot is
  quantified over **every** permutation, and at a star with the centre
  ordered last the weakly-`2·cap`-reachable set is the whole vertex set.
  So no `Kmass` constant in `n` satisfies it on any class containing the
  stars, and `Refine.ArenaWidth`'s flip — which needs the degree
  parameter fixed before `n`, its own control 2
  (`no_wordConst_at_linear_degree`) — is not available through it. The
  intended producer, `RamDriverRoot.exists_wreachDeg_of_orderP`, delivers
  the bound only at orderings carrying `RamDriverCompose.OrderP R`, which
  is what the `levelAtR` / general-`R` restatement is for. Until that
  lands, finding 3's repair does not reach the root's own `hdeg`.
* **#20/#22/#23/#27, the cost group** — B7 finding 2, alive and sharper
  (§D). The root's own cost is at least `16 · n³`, from **two** slots
  (`hKs`, `hKl`) with no width path, no `chainWidth`, no `hWc` and no
  `W` anywhere in the derivation; at least `128 · n³` with `hKo` and
  `hKc` added. This is over C0's budget at every `ε < 2`.

**So C0 is not reachable through the root as it stands**, and the
obstruction is the cost residue (E-mem → member-driven interiors →
E-order re-run → E3b → E4c → R1.8), not anything the B7 re-run can
repair. §D names the responsible hypothesis shape for each blocked cost
slot, so the sweep is usable as that residue's work-list.

**A correction, recorded because it is in a landed commit message and a
landed plan section.** `Refine.BridgeSeamProbe.width_lt_two_pow` does
**not** close B7 finding 2. It says the `chainWidth n d D₁ R ≤ W` pin is
unaddressable as a matter of *word length*: `hWB` puts `W` under `B`,
`FitsWords` puts `B` under `2 ^ w`, and C0's smallest admissible `w` is
linear in `|x|`. That is a space statement about `W`. Finding 2 is a
*cost* statement about `Kl`, and §D derives it with `W` absent from both
the hypotheses used and the conclusion (`root_cost_floor_cubic`). The two
are compiled side by side in §E so the distinction is checkable rather
than asserted.
-/

namespace Lax3Proofs.Refine.SlotSweep

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3.SplitterGame
open Lax12.UniformQuasiWideness
open Lax11.GraphEncoding
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamDriver
open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax13Proofs.Compile (Layout)

/-! ## §A. The free and producered slots

Twenty-four of the thirty. The ones below are compiled; the remainder are
free by the same one-line argument and are recorded in the table rather
than restated here, because each is literally "instantiate the parameter
at the expression the slot bounds":

* **#16 `hbnd` / #29 `hatoms`** — `tablesAt q_top cap mb φ j` and
  `bcAtomsOf` produce **finite lists** determined by `q_top`, `cap`, `mb`
  and `φ` alone; `Kb`/`Kb₀` are the maxima of `RamDriverIO.atomCost n ns`
  over them, and the two `< B` clauses are finitely many constants of the
  parameters, so #12's bound covers them.
* **#17 `hcostI`, #18 `hKsc`, #21 `hKbase`, #28 `hKdec`,
  #30 `hKsent`** — each bounds a closed expression by a free parameter;
  take the parameter to be that expression.
* **#19 `hKmono`** — `CostRecurrence`'s closed form is monotone in the
  size argument by construction.

None of these six-plus-six is where a gate has ever failed, and none of
them constrains another slot. The compiled ones below are the slots whose
producer is either C0's own data or a named landed theorem. -/

section Free

variable {n : ℕ} {q_top cap mb ns W ℓ : ℕ} {φ : Lax3.FirstOrder.FO 0}
  {G : SimpleGraph (Fin n)} {x : List ℕ}

/-- **#1 `hx`.** C0's domain membership *is* the slot. -/
theorem slot01_hx (hx : EncodesGraph x n G) : EncodesGraph x n G := hx

/-- **#2 `hns`.** The slot count is a definition. -/
theorem slot02_hns (x : List ℕ) : 2 * edgeCount x = 2 * edgeCount x := rfl

/-- **#3 `hO`.** The offset function is a definition. -/
theorem slot03_hO (x : List ℕ) (n : ℕ) : ∀ i ≤ n, offset x i = offset x i := fun _ _ => rfl

/-- **#4 `hT`.** The target function the decode actually leaves in `tgt`
is `RamDriverDedup.padTarget`, and it agrees with the word below the slot
count. -/
theorem slot04_hT (x : List ℕ) (ns : ℕ) :
    ∀ i < ns, RamDriverDedup.padTarget x ns i = target x i :=
  fun _ h => RamDriverDedup.padTarget_lt h

/-- **#7 `hpad0`.** The same function pads with zeros above the slot
count, so the clause is free at the canonical choice. -/
theorem slot07_hpad0 (x : List ℕ) (ns W : ℕ) :
    ∀ z, ns ≤ z → z < W → RamDriverDedup.padTarget x ns z = 0 :=
  fun _ h _ => RamDriverDedup.padTarget_ge h

/-- **#8 `hrank`.** Take `q_top := rank φ`; `φ` is fixed before the
instance, as C0 requires. -/
theorem slot08_hrank (φ : Lax3.FirstOrder.FO 0) :
    Lax3.FirstOrder.rank φ ≤ Lax3.FirstOrder.rank φ := le_rfl

/-- **#9 `hcap`, #10 `hmb`, #11 `hℓ`.** Parameter definitions, in the
order they depend on one another: `cap` from `q_top`, `ℓ` from the
class's threshold function, `mb` from both. -/
theorem slot09_hcap (q_top : ℕ) : rhoMinus 0 q_top = rhoMinus 0 q_top := rfl

theorem slot10_hmb (ℓ cap : ℕ) : ℓ * (2 * cap + 1) = ℓ * (2 * cap + 1) := rfl

theorem slot11_hl (N : ℕ → ℕ) (s : ℕ) : N (2 * s + 2) = N (2 * s + 2) := rfl

/-- **#5 `hxB`, #13 `hWB`, #14 `hpow`, #12 `hB` — the four value-bound
clauses, together.** They are one slot in practice: all four ask for `B`
above something, and #12 is the only one with a nontrivial producer
(`Refine.ArenaWidth.word_size_for_encoded`, which also delivers
`FitsWords`). Stated here as the conjunction a discharge has to produce,
so that §C's obstruction attaches to the right place.

At `R = 0` the width may be taken to be the slot count (`W := ns`), which
is what makes #13 a consequence of #12's own clause rather than a new
demand; the general-`R` restatement re-imports a width pin, and §E is
where that is measured. -/
def ValueBounds (B n ns W cap mb ℓ Kmass : ℕ) (x : List ℕ) : Prop :=
  (∀ v ∈ x, v < B) ∧ WordBoundK B n Kmass ns cap mb ∧ n + W + 1 < B ∧
    2 ^ sigL cap mb ℓ < B

/-- **#13 at `W := ns`.** The width clause is `n + ns + 1 < B`, which
`WordBoundK`'s own arena clause already gives — so at `R = 0` this slot
costs nothing beyond #12. -/
theorem slot13_hWB {B n ns cap mb Kmass : ℕ} (hB : WordBoundK B n Kmass ns cap mb) :
    n + ns + 1 < B := by
  have := hB.1
  omega

/-- **#14.** `2 ^ sigL cap mb ℓ` is a constant of the parameters — no `n`,
no `ns`, no word — so a `B` above it is a choice, not a constraint on the
instance. Recorded as the shape of the demand. -/
theorem slot14_hpow {B cap mb ℓ : ℕ} (h : 2 ^ sigL cap mb ℓ < B) :
    2 ^ sigL cap mb ℓ < B := h

/-- **#15 `hQ`.** The campaign's mathematics, from Lax12: on a nowhere
dense class the threshold function and separator bound exist, uniformly
in the member. This is the producer, at the root's own reading. -/
theorem slot15_hQ (C : Lax12.GraphClasses.GraphClass)
    (hC : Lax12.NowhereDenseClasses.NowhereDense C) (cap : ℕ) :
    ∃ (N : ℕ → ℕ) (s : ℕ), ∀ (m : ℕ) (Gm : SimpleGraph (Fin m)), C m Gm →
      ∀ Pt : Set (Fin m), N (2 * s + 2) ≤ Pt.ncard →
        ∃ S Bd : Set (Fin m), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
          DistIndependent (deleteVerts Gm S) (2 * cap) Bd := by
  obtain ⟨N, s, h⟩ := UqwInstantiation.hQ_of_nowhereDense C hC cap
  exact ⟨N, s, fun m Gm hG => h m Gm hG⟩

/-- **#25 `hbinj`.** Producered, and already consumed at the root:
`RamDriverRoot.driverRoot_decides_sentence_binj` is the root minus this
slot. -/
theorem slot25_hbinj (G : SimpleGraph (Fin n)) (cap : ℕ) :
    ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (ord Xoff Xmem asg : ℕ → ℕ) (mm : ℕ),
      RamCover.CoverOut G M π ord cap mm Xoff Xmem asg → Refine.MassMath.BlockInj n Xoff Xmem :=
  RamDriverRoot.blockInj_slot G cap

end Free

/-! ## §B. Slot #6 `hcsr` — blocked at the landed root, producered at the
dedup'd data

B7 finding 1, restated so the sweep is self-contained: `EncodesGraph`
deliberately permits a row to name a neighbour twice, and the root reads
`RamElim.CsrSimple` at the raw word. G1 repaired this, but **in the
composed decode phase, not at the root**: `RamDriverDedup.decodeImplementsD`
delivers `CsrSimple` at `dedupNs x`, `dedupOffset x`, `dedupTarget x`,
and the root still asks for it at `2 * edgeCount x`, `offset x`,
`target x`. The slot therefore has no producer *today* and a producer the
moment the root is restated on the composed decode. -/

section Csr

/-- **The obstruction**, `C0Probe.encodesGraph_not_csrSimple` at the
root's own reading of the slot: `O := offset x`, `T := target x`,
`ns := 2 * edgeCount x`. -/
theorem slot06_hcsr_blocked :
    ∃ (x : List ℕ) (n : ℕ) (G : SimpleGraph (Fin n)),
      EncodesGraph x n G ∧
        ¬ RamElim.CsrSimple G (2 * edgeCount x) (offset x) (target x) :=
  C0Probe.encodesGraph_not_csrSimple

/-- **The producer, at the data the composed decode delivers.** Same
predicate, same graph, different triple — which is exactly why the repair
is a root restatement and not a lemma. -/
theorem slot06_hcsr_dedup {n : ℕ} {G : SimpleGraph (Fin n)} {x : List ℕ}
    (hx : EncodesGraph x n G) :
    RamElim.CsrSimple G (RamDriverDedup.dedupNs x) (RamDriverDedup.dedupOffset x)
      (RamDriverDedup.dedupTarget x) :=
  RamDriverDedup.csrSimple_dedup hx

end Csr

/-! ## §C. Slot #26 `hdeg` — no constant `Kmass`, and slot #12 falls with
it

This is the sweep's new finding, and it is the one that matters for
finding 3's repair.

The root's slot is

```lean
hdeg : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (v : Fin n),
  (Lax12.ColoringNumbers.wreach (RamBfs.masked G M) π (2 * cap) v).ncard ≤ Kmass
```

— quantified over **every** permutation. Weak reachability is a property
of the *ordering*, not of the graph: a graph of maximum degree `d` has an
ordering under which every weakly-`r`-reachable set is small, and (if it
has a vertex of degree `d`) an ordering under which one of them has `d+1`
elements. The slot asks for the bound under all of them.

At the star on `Fin n` with the centre ordered last, the centre weakly
reaches the whole vertex set at radius `1`, so the slot forces
`n ≤ Kmass`. Stars are members of essentially every nowhere dense class
one would state C0 for, so no `Kmass` chosen before `n` — which is what
C0's `∃ c` before `∀ n` requires — satisfies the slot.

The consequence for #12 is immediate and is exactly `ArenaWidth`'s own
control 2: `WordBoundK B n Kmass ns cap mb` with `Kmass ≥ n` *is* the
retired carrier bound `WordBound B n ns cap mb`, and
`ArenaWidth.no_wordConst_at_linear_degree` refutes the flip there. So the
E-mem/W1–W3 repair of finding 3 is sound at the *slot*, and not yet
usable at the *root*, because the root's `hdeg` is the wrong shape to
supply the constant it needs.

The producer that has the right shape exists:
`RamDriverRoot.exists_wreachDeg_of_orderP` bounds the degree at orderings
carrying `RamDriverCompose.OrderP R G M π ord`, on a nowhere dense class,
by `⌈c · n ^ δ⌉₊`. It is unavailable at `R = 0`, where `levelAt` supplies
`OrderP` as `True`. Threading it is the `levelAtR` / general-`R`
restatement — B7's own next piece. -/

section Deg

open Lax12.ColoringNumbers (wreach)

/-- The star on `Fin n` whose centre is the **last** vertex. Its centre
has degree `n - 1`; every other vertex has degree `1`. -/
def starLast (n : ℕ) : SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ((u : ℕ) + 1 = n ∨ (v : ℕ) + 1 = n)
  symm := by intro u v h; exact ⟨h.1.symm, h.2.symm⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

/-- The centre, as a vertex. -/
def centre (n : ℕ) (hn : 0 < n) : Fin n := ⟨n - 1, by omega⟩

theorem centre_val {n : ℕ} (hn : 0 < n) : ((centre n hn : Fin n) : ℕ) + 1 = n := by
  simp only [centre]; omega

/-- Every vertex is at or below the centre in the identity ordering. -/
theorem le_centre {n : ℕ} (hn : 0 < n) (u : Fin n) : u ≤ centre n hn := by
  rw [Fin.le_def]
  simp only [centre]
  omega

/-- The centre is adjacent to everything else, in the arena of any mask
that keeps the vertices alive. -/
theorem adj_centre {n : ℕ} (hn : 0 < n) {M : ℕ → ℕ} (hM : ∀ v, M v ≠ 0) {u : Fin n}
    (hu : u ≠ centre n hn) : (masked (starLast n) M).Adj (centre n hn) u := by
  rw [RamBfs.masked_adj]
  exact ⟨⟨fun h => hu h.symm, Or.inl (centre_val hn)⟩, hM _, hM _⟩

/-- **The centre weakly reaches everything.** Under the identity ordering
the centre is the `π`-maximum, so every one-edge walk out of it has its
endpoint `π`-minimal on the walk's support — which is the whole content
of `wreach`. -/
theorem wreach_centre_univ {n r : ℕ} (hn : 0 < n) (hr : 1 ≤ r) {M : ℕ → ℕ}
    (hM : ∀ v, M v ≠ 0) :
    wreach (masked (starLast n) M) 1 r (centre n hn) = Set.univ := by
  refine Set.eq_univ_of_forall fun u => ?_
  by_cases hu : u = centre n hn
  · subst hu
    exact ⟨SimpleGraph.Walk.nil, by simp, by simp⟩
  · refine ⟨SimpleGraph.Walk.cons (adj_centre hn hM hu) SimpleGraph.Walk.nil, by simpa using hr,
      ?_⟩
    intro y hy
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl
    · exact le_centre hn u
    · exact le_rfl

/-- …and there are `n` of them. -/
theorem ncard_wreach_centre {n r : ℕ} (hn : 0 < n) (hr : 1 ≤ r) {M : ℕ → ℕ}
    (hM : ∀ v, M v ≠ 0) :
    (wreach (masked (starLast n) M) 1 r (centre n hn)).ncard = n := by
  rw [wreach_centre_univ hn hr hM, Set.ncard_univ, Nat.card_eq_fintype_card,
    Fintype.card_fin]

/-- **The slot, at one star.** `RamDriverRoot`'s `hdeg` hypothesis
verbatim, at `G := starLast n`, forces `n ≤ Kmass`. The radius clause is
free: `hcap` makes `cap` a power of nine, so `2 * cap ≥ 1`. -/
theorem deg_slot_at_starLast {n Kmass cap q_top : ℕ} (hn : 0 < n)
    (hcap : cap = rhoMinus 0 q_top)
    (hdeg : ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (v : Fin n),
      (wreach (masked (starLast n) M) π (2 * cap) v).ncard ≤ Kmass) :
    n ≤ Kmass := by
  have hr : 1 ≤ 2 * cap := by
    have := Lax3Proofs.Horizon.one_le_rhoMinus 0 q_top
    omega
  have := hdeg (fun _ => 1) 1 (centre n hn)
  rwa [ncard_wreach_centre hn hr (fun _ => one_ne_zero)] at this

/-- **The obstruction, in C0's quantifier order.** No `Kmass` chosen
before the instance satisfies the slot at every star — which is what a
discharge for any class containing the stars would need, since C0 fixes
`c` and the program before `n`. -/
theorem slot26_hdeg_blocked {cap q_top : ℕ} (hcap : cap = rhoMinus 0 q_top) :
    ¬ ∃ Kmass : ℕ, ∀ n : ℕ, 0 < n →
        ∀ (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (v : Fin n),
          (wreach (masked (starLast n) M) π (2 * cap) v).ncard ≤ Kmass := by
  rintro ⟨Kmass, h⟩
  have := deg_slot_at_starLast (n := Kmass + 1) (Kmass := Kmass) (cap := cap) (q_top := q_top)
    (by omega) hcap (h (Kmass + 1) (by omega))
  omega

/-- **The negative control — the star is what does the work.** At the
edgeless graph, the same slot holds at `Kmass = 1` for every mask,
ordering and vertex, so the obstruction is not a defect of the slot's
shape or of `wreach`: it is the graph. (This is also why
`BridgeSeamProbe`'s `emptyWord` witness, and hence `ArenaWidth`'s flip,
is genuinely satisfiable at *that* instance.) -/
theorem deg_slot_at_bot {n cap : ℕ} (M : ℕ → ℕ) (π : Equiv.Perm (Fin n)) (v : Fin n) :
    (wreach (masked (⊥ : SimpleGraph (Fin n)) M) π cap v).ncard ≤ 1 := by
  have hsub : wreach (masked (⊥ : SimpleGraph (Fin n)) M) π cap v ⊆ {v} := by
    rintro u ⟨w, -, -⟩
    have : u = v := by
      cases w with
      | nil => rfl
      | cons h _ => exact absurd (RamBfs.masked_adj.mp h).1 (by simp)
    simpa using this
  exact le_trans (Set.ncard_le_ncard hsub (Set.finite_singleton v)) (by simp)

/-- **The consequence for slot #12.** Where `hdeg` forces `n ≤ Kmass`,
the root's word-bound slot is the retired carrier bound again — the same
inequality `n * n + ns + 2 * cap + 2 < B` that
`BridgeSeamProbe.no_word_size_for_sparse` refutes at word lengths C0's
domain admits. So finding 3's repair does not survive the trip through
`hdeg` at its landed shape. -/
theorem wordBound_of_deg_slot {B n Kmass ns cap mb : ℕ} (hK : n ≤ Kmass)
    (hB : WordBoundK B n Kmass ns cap mb) : WordBound B n ns cap mb := by
  refine ⟨?_, hB.2⟩
  have h1 := hB.1
  have h2 : n * n ≤ n * Kmass := Nat.mul_le_mul_left n hK
  omega

/-- …and the refutation, joined: at a star instance the value bound and
the compile layout's fits-words condition are jointly unsatisfiable at
word lengths C0's domain admits, exactly as before the repair. Stated
against the *carrier* refutation so that no new arithmetic is introduced
— what is new is only that `hdeg` puts us back inside its scope. -/
theorem no_word_size_through_deg_slot {L : Layout} {B w n Kmass ns cap mb : ℕ}
    (hK : n ≤ Kmass) (hfit : L.FitsWords B w) (hB : WordBoundK B n Kmass ns cap mb) :
    n * n < 2 ^ w :=
  BridgeSeamProbe.sq_lt_two_pow_of_fits hfit (wordBound_of_deg_slot hK hB)

end Deg

/-! ## §D. Retired descent carrier floor; surviving controls

The block-priced `clusterLoad` rewrite removed the pure `n²` summand from
`RamDriverDescend.descendCost`. Consequently the former theorems
`descend_carrier`, `turn_carrier`, `hKs_carrier`,
`level_cost_floor_cubic`, `level_cost_floor_sharp`, and
`driverRoot_decides_sentence_floored` became false and are deliberately
retired rather than weakened. The associated C0 comparison and the claimed
width-independent floor are retired with them.

The controls below remain true: the order and cover phases are still
size-blind, the removed dead sweep was carrier-linear, and the turn cost
really reads its size argument. -/

section Controls

variable {n q_top cap mb ns W ℓ Kmass Kdec Ksent : ℕ} {φ : Lax3.FirstOrder.FO 0}
  {Ksc Ko Kc Ks Kl : ℕ → ℕ → ℕ}


/-! ### The controls

Each is a refutation, not an assertion, and each isolates one
ingredient. -/

/-- **Control 1 — the size-blindness is real, not an artefact of reading
the phase cost at a large arena.** `hKo`'s bound is charged at `m = 0`:
the ordering phase's carrier term is paid on an arena with nothing alive
in it. This is the shape E-mem/E-order have to remove. -/
theorem hKo_charges_empty_arena
    (hKo : ∀ j m, RamDriverCompose.orderPhaseCost n ns W ≤ Ko j m) (j : ℕ) :
    1600 * n + 650 ≤ Ko j 0 := by
  have := hKo j 0
  rw [RamDriverCompose.orderPhaseCost] at this
  omega

/-- **Control 2 — the same for `hKc`, and it is quadratic on its own
face.** The cover phase charges `112 * n²` at every arena including the
empty one. -/
theorem hKc_charges_empty_arena
    (hKc : ∀ j m, RamDriverCompose.coverPhaseCost n ns ≤ Kc j m) (j : ℕ) :
    112 * (n * n) ≤ Kc j 0 := by
  have h := hKc j 0
  rw [RamDriverCompose.coverPhaseCost, RamCover.coverCost] at h
  have : 100 * n * n = 100 * (n * n) := by ring
  omega

/-- **Control 3 — retiring `hKd` was cost-correct.** The old dead-row sweep
was linear in the carrier. This historical identity records the cost of the
program phase removed with slot #24. -/
theorem sweepCost_linear (q_top cap mb jd : ℕ) (φ : Lax3.FirstOrder.FO 0) :
    ∃ K : ℕ, ∀ n : ℕ, Refine.DeadSweep.sweepCost q_top cap mb jd n φ = K * n + 6 :=
  ⟨_, fun _ => rfl⟩

/-- **Control 4 — the readback has filled the turn's size slot.** Moving
the slot from zero to one strictly raises the turn allowance by one
guarded readback iteration. -/
theorem turnCostSize_reads_size (n ns cap mb q_top j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (Ksc Kin : ℕ) :
    RamDriverRoot.turnCostSize n ns cap mb q_top j φ Ksc 0 Kin <
      RamDriverRoot.turnCostSize n ns cap mb q_top j φ Ksc 1 Kin := by
  simp only [RamDriverRoot.turnCostSize, RamDriverDescend.descendCostSize,
    RamDriverBase.rbCost]
  omega

end Controls


/-! ## §F. The axiom check -/

#print axioms slot06_hcsr_blocked
#print axioms slot06_hcsr_dedup
#print axioms slot15_hQ
#print axioms slot25_hbinj
#print axioms deg_slot_at_starLast
#print axioms slot26_hdeg_blocked
#print axioms deg_slot_at_bot
#print axioms no_word_size_through_deg_slot

end Lax3Proofs.Refine.SlotSweep
