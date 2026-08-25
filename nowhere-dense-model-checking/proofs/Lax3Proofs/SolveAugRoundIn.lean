import Lax3Proofs.SolveAugRoundSeams
import Lax3Proofs.SolveF7Adm

set_option autoImplicit false

/-!
# F6c12-5a-ii — `AugRoundIn`, discharged

`SolveAugRoundSeams` composed three of the round's four computational
stages into `augRdBody` and named four things that separated that from
`AugRoundIn`.  This file closes all four.

* **(a) the region.**  `SolveAugSymMerge`'s `augSymCsrIn_symComW` (this
  wave) restates the symmetrization at `augStInNW`, the region the base
  pass produces and the rounds can carry, so the three residuals of
  `covAugAdjSelIn_of_base_rounds_sym` finally speak one `AugSt`.
* **(b) the transitive matrix's re-zero** (§2): `ardClearCom`, the
  owner-advancing scan of the transitive CSR, at
  `ardClearK n T = 19·n + 23·T + 20`, discharging `TrClearAt` at the
  re-measured `trClearK`.
* **(c) the copy-back** (§3): `ardCopyCom`, two flat sweeps, at
  `ardCopyK n a = 12·n + 12·a + 32`, discharging `InCsrCopyAt` at the
  re-measured `inCsrCopyK`.
* **(d) the word bound** (§4): *not* discharged, and the reason is a
  result and not a gap — see below.

§5 assembles `rdC` and discharges `AugRoundIn`
(`augRoundIn_ardRoundCom`); §6 exhibits the names, the cells and the
descriptor, and proves the whole precondition inhabited.

## The verdict on (d): it is F7-c's choice of `q`, and here is the
## inequality

`augRdBody_spec` needs `n + n² + a + f + T < B` at `B = mcB q x`.  The
landed material gives `n` and `n²`.  For the three counts:

1. **`Adm` does supply the structural half.**  `chainAdm`'s `Inv`
   (`SolveF7Adm` §1, `DriverCorrect` §Inv) contains
   `ReachedS (2R) G₀ rounds (SimpleGraph.map A.up A.G)` on every arena
   with `A.G ≠ ⊥` — which is exactly the case `AugRoundIn` is stated
   in — and `reachedS_le` turns that into
   `SimpleGraph.map A.up A.G ≤ G₀`.  So `A.G ⊑ G₀`
   (`ardIsContained_of_inv`), which is precisely the hypothesis
   `exists_selChain_inDegLE_pow` consumes.  The earlier note that `Adm`
   "has no landed instantiation at all" is out of date.
2. **Nowhere-denseness then supplies the numbers**: at
   `d = (3·⌈c₀·m^δ'⌉₊ + 2) ^ 16^R` every round of the chain has
   `InDegLE d`, so `a ≤ n·d` and `f, T ≤ n·d²`.
3. **What is left is not a fact about the machine at all.**  It is
   `n + n² + n·d + 2·n·d² < q·(|x|+1)²`, an inequality between the
   class's density constant and the schedule's word-bound constant.
   `q` is fixed by F7's instantiation (`ProgCodegenLayout.lean:79-83`
   says so in as many words), the counts are not, and no choice of
   `Adm` can decide it.

`ardWordBound_of_inDegLE` is the sufficient condition, proved:

> if some `K` has `d² ≤ K·(m + 1)` at every carrier `m`, then **`q ≥
> 3·K + 2`** makes the round's word bound hold at every arena of every
> input.

That is the whole of (d).  The condition on `K` is a condition on the
*exponent*: `d ≈ C·m^(δ'·16^R)`, so `d² ≤ K·(m+1)` asks for
`δ'·16^R ≤ 1/2`, which F7 gets for free because
`exists_selChain_inDegLE_pow` is stated at **every** `δ' > 0` and
`R` is fixed before `δ'` is chosen.  Nothing here is tight: `3K + 2` is
generous by a factor of the `d ≤ d²` step.

`AugRoundIn` is therefore discharged **conditional on one named
hypothesis**, `ArdWord` (§4) — the round's own word bound, quantified
exactly as `AugRoundIn` quantifies — and `ardWordBound_of_inDegLE`
together with `ardIsContained_of_inv` reduces that hypothesis to the
inequality on `q` above.  The conclusion is not weakened anywhere else.

## The two programs, and why they are the shapes they are

**The re-zero** cannot be a flat sweep of the `n·n` window: that is
`Θ(n²)` per round and `R` rounds of it would put a term quadratic in
the carrier into `levelCharge`'s ledger, which §7's envelope has no
room for.  It walks the transitive CSR the pass left beside the matrix
instead — one store per emitted candidate — using `Lib.Csr`'s
`ownerScan_spec`: a single loop over the target array with the owning
row advanced beside it, `19` a row and `23` a slot.  `TransCsrAt`'s own
`markZero` says the cells the walk does *not* visit are already clear,
and its `complete` says the walk visits every cell that is set, so the
postcondition is the full window and not a prefix.

**The copy-back** is two flat sweeps because `TrInCsr` is almost
entirely a statement about the two abstract functions `off` and `tgt`:
only `offLen`, `tgtLen`, `offGet` and `tgtGet` mention the state at
all.  Copying the two arrays cell for cell therefore reproduces the
region at the *same* `off` and `tgt`, and the seven combinatorial
clauses come across untouched.

Neither pass re-zeroes anything it does not have to, and neither is
charged in a currency other than `n`, `arcCount`, `fratPairCount`,
`transPairCount`.

## The round, and its budget

    rdC j = frZero(ad) ; frZero(sd) ; frZero(dgE)
          ; augRdBody ; ardClearCom ; ardCopyCom

with the three carrier sweeps **first**, so that the round's descriptor
`Srd` does not have to carry them and a round restores every region the
next round reads: the fraternal mark window, the transitive mark
window, and the orientation pair.  The budget is `augRdRoundK`
(`SolveAugRoundSeams` §5, re-measured at the two new programs' real
figures) `= augRoundBudget 1025 455 588 305 287`, inside
`augChainCost_le_selChainCharge`'s gates at every `k ≥ 342` and so at
the `k = 475` the base and symmetrization passes already use.  Under
`D.InDegLE d` the whole round costs `n·(1025 + 455·d + 893·d²) + 287`:
the carrier enters linearly and never squared.

## One requirement this leaf pins rather than discharges

`Srd` is **one** predicate for all `R` rounds while the three counts
grow from round to round and an array's length cannot change, so every
allocation the round asks for has to be sized by the carrier alone —
`ardCap N = 2N³ + N² + N + 1` (§5), which dominates `arcCount ≤ N²` and
`fratPairCount, transPairCount ≤ N³` at every orientation of `Fin N`.
That is *space*, and space is free (`Imp.lean:20-44`); no time term is
quadratic in the carrier anywhere.  The one clause `exists_ardSrd`
cannot establish by allocating is the orientation pair's own
`ardCap`-sized allocation — reallocating `(io, it)` would destroy the
region the round reads — so it is a **hypothesis** there, and a real
requirement on whoever writes the orientation into that pair (the base
pass's `Sbd`).
-/

namespace Lax3Proofs.Prog

open scoped SimpleGraph
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax11.GraphEncoding
open Lax3.ColoredGraphs Lax3.DistFO Lax3.ScatterSentences Lax3.Locality
open Lax12.GraphClasses Lax12.NowhereDenseClasses
open Lax3.FirstOrder (FO)
open Lax3Proofs.Driver
open Lax3Proofs.Augmentation (Orientation fratGraph TransLink)
open Lax3Proofs.CoverRoutine (MinDegSel mdSel selRank selChain greedyStep)

/-! ## §0 Small helpers

The array and evaluation shapes the straight-line blocks are built
from; `SolveAugTrans` §5 has the same list, `private` there. -/

private theorem ard_getD_replicate (m k : ℕ) :
    (List.replicate m (0 : ℕ)).getD k 0 = 0 := by
  rcases Nat.lt_or_ge k m with h | h
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h)]
    simp
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using h)]
    rfl

private theorem ard_getD_set_self {l : List ℕ} {i c : ℕ} (h : i < l.length) :
    (l.set i c).getD i 0 = c := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_self h]
  rfl

private theorem ard_getElem?_of_lt (l : List ℕ) (i : ℕ) (h : i < l.length) :
    l[i]? = some (l.getD i 0) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

private theorem ard_evB_var {B : ℕ} {y : String} {σ : Env} {c : ℕ}
    (hy : σ.vars y = c) (hc : c < B) : (Expr.var y).evalB B σ = some c := by
  subst hy; exact evalB_var hc

private theorem ard_evB_add {B : ℕ} {e f : Expr} {σ : Env} {a b : ℕ}
    (he : e.evalB B σ = some a) (hf : f.evalB B σ = some b) (h : a + b < B) :
    (Expr.add e f).evalB B σ = some (a + b) := evalB_bin he hf (by simpa using h)

private theorem ard_evB_get {B : ℕ} {a : String} {i : Expr} {σ : Env} {p c : ℕ}
    (hi : i.evalB B σ = some p) (hp : p < (σ.arrs a).length)
    (hc : (σ.arrs a)[p]? = some c) (hcB : c < B) :
    (Expr.get a i).evalB B σ = some c := evalB_get hi hc hcB

private theorem ard_run_assign {B : ℕ} {x : String} {e : Expr} {σ : Env} {c K : ℕ}
    (h : e.evalB B σ = some c) (hK : 1 + e.size ≤ K) :
    Run B (.assign x e) σ (σ.setVar x c) K := (Run.assign h).mono hK

private theorem ard_run_store {B : ℕ} {a : String} {i e : Expr} {σ : Env} {p c K : ℕ}
    (hi : i.evalB B σ = some p) (he : e.evalB B σ = some c)
    (hp : p < (σ.arrs a).length) (hK : 1 + i.size + e.size ≤ K) :
    Run B (.store a i e) σ (σ.setArr a p c) K := (Run.store hi he hp).mono hK

/-- `TrInCsr` transports along its own two regions — `SolveAugRoundSeams`'s
`augRd_trInCsr_of_eq`, restated at a renaming of the regions, which is
what a copy needs: the *same* `off` and `tgt` at a *different* pair. -/
theorem ardTrInCsr_rename {o t o' t' : String} {m ns : ℕ} {D : Orientation m}
    {off tgt : ℕ → ℕ} {σ σ' : Env} (h : TrInCsr o t D ns off tgt σ)
    (hoL : m + 1 ≤ (σ'.arrs o').length) (htL : ns ≤ (σ'.arrs t').length)
    (hoG : ∀ i, i ≤ m → (σ'.arrs o')[i]? = some (off i))
    (htG : ∀ p, p < ns → (σ'.arrs t')[p]? = some (tgt p)) :
    TrInCsr o' t' D ns off tgt σ' where
  zero := h.zero
  step := h.step
  last := h.last
  offLen := hoL
  tgtLen := htL
  offGet := hoG
  tgtGet := htG
  tgtLt := h.tgtLt
  sound := h.sound
  complete := h.complete
  inj := h.inj

/-! ## §2 The transitive matrix's re-zero

`TransCsrIn`'s precondition asks for the `n·n` window clear on entry and
its postcondition leaves the marks *set* — they are the output — so
round `i + 1` cannot run until they are cleared again.  A flat sweep of
the window is `Θ(n²)` and `R` repetitions of it would put a term
quadratic in the carrier into the ledger; the pass therefore walks the
transitive CSR the enumeration left beside the matrix, one store per
emitted candidate.

It is `Lib.Csr`'s owner-advancing scan: one loop over the target array,
with the owning row `tz.u` and its row base `tz.b = u·n` carried
beside the slot pointer `tz.j`.  `TransCsrAt.complete` says every set
cell is visited; `TransCsrAt.markZero` says every unvisited cell was
already clear. -/

/-- The re-zero's five scratch scalars. -/
def ardTzScalars : List String := ["tz.j", "tz.u", "tz.b", "tz.m", "tz.w"]

private theorem ardTzScalars_ne {y : String} (h : y ∉ ardTzScalars) :
    y ≠ "tz.j" ∧ y ≠ "tz.u" ∧ y ≠ "tz.b" ∧ y ≠ "tz.m" ∧ y ≠ "tz.w" := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    · intro hc
      rw [hc] at h
      exact h (by simp [ardTzScalars])

private theorem ard_getD_set_of_ne {l : List ℕ} {i p c : ℕ} (h : i ≠ p) :
    (l.set i c).getD p 0 = l.getD p 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_set_ne h, List.getD_eq_getElem?_getD]

/-- Storing a zero keeps a cell clear, whichever cell is asked about. -/
private theorem ard_getD_set_zero {l : List ℕ} {i p : ℕ} (hi : i < l.length)
    (h : p = i ∨ l.getD p 0 = 0) : (l.set i 0).getD p 0 = 0 := by
  rcases h with rfl | h
  · exact ard_getD_set_self hi
  · rcases eq_or_ne p i with rfl | hp
    · exact ard_getD_set_self hi
    · rw [ard_getD_set_of_ne (Ne.symm hp)]; exact h

/-- **The row that owns a slot is unique.**  The offsets are monotone,
so two half-open blocks containing the same slot are the same block. -/
theorem ardTrOff_owner_unique {n : ℕ} (D : Orientation n) {u v p : ℕ}
    (h1 : trOff D u ≤ p) (h2 : p < trOff D (u + 1))
    (h3 : trOff D v ≤ p) (h4 : p < trOff D (v + 1)) : u = v := by
  by_contra hne
  rcases Nat.lt_or_ge u v with h | h
  · have := trOff_mono D (show u + 1 ≤ v from h)
    omega
  · have hlt : v < u := by omega
    have := trOff_mono D (show v + 1 ≤ u from hlt)
    omega

/-- **The turn.**  If the slot pointer is still inside the owner's row,
clear the owner's cell for that slot and advance the pointer; otherwise
advance the owner and its row base.  Exactly one pointer moves per
turn, which is what the amortization asks. -/
def ardClearAct (nN ro rt mk : String) : Com :=
  .ite (.lt (.var "tz.j") (.get ro (.add (.var "tz.u") (.lit 1))))
    (.seq (.assign "tz.w" (.get rt (.var "tz.j")))
      (.seq (.store mk (.add (.var "tz.b") (.var "tz.w")) (.lit 0))
        (.assign "tz.j" (.add (.var "tz.j") (.lit 1)))))
    (.seq (.assign "tz.u" (.add (.var "tz.u") (.lit 1)))
      (.assign "tz.b" (.add (.var "tz.b") (.var nN))))

/-- **The re-zero.**  Zero the three pointers, load the extent out of
the offsets array's last cell, and scan. -/
def ardClearCom (nN ro rt mk : String) : Com :=
  .seq (.assign "tz.j" (.lit 0))
    (.seq (.assign "tz.u" (.lit 0))
      (.seq (.assign "tz.b" (.lit 0))
        (.seq (.assign "tz.m" (.get ro (.var nN)))
          (Csr.scan "tz.j" "tz.m" (ardClearAct nN ro rt mk)))))

/-- The re-zero's budget: `19·n + 23·T + 20`, linear in the enumeration
it undoes and in nothing else. -/
def ardClearK (n T : ℕ) : ℕ := 19 * n + 23 * T + 20

/-- The array the re-zero can store into: its own one. -/
theorem ard_not_mem_warrs_clear {nN ro rt mk b : String} (h : b ≠ mk) :
    b ∉ (ardClearCom nN ro rt mk).warrs := by
  simp [ardClearCom, ardClearAct, Csr.scan, Com.warrs, h]

/-- The scalars the re-zero can assign to: its own five. -/
theorem ard_not_mem_wvars_clear {nN ro rt mk y : String} (h : y ∉ ardTzScalars) :
    y ∉ (ardClearCom nN ro rt mk).wvars := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := ardTzScalars_ne h
  simp [ardClearCom, ardClearAct, Csr.scan, Com.wvars, a1, a2, a3, a4, a5]

/-- **The re-zero, specified.**  From the transitive candidate region
the enumeration leaves, the whole `n·n` mark window is clear again, and
nothing but `mk` has been written.

The precondition asks for no allocation of its own — `TransCsrAt` names
all three — and the postcondition promises no length, so the
exact-length trap is not sprung in either direction. -/
theorem ardClear_spec {B : ℕ} {nN ro rt mk : String}
    (hmro : mk ≠ ro) (hmrt : mk ≠ rt) (hnN : nN ∉ ardTzScalars)
    {n : ℕ} (D : Orientation n) (ttF : ℕ → ℕ) :
    Spec B
      (fun σ => TransCsrAt ro rt mk D ttF σ ∧ σ.vars nN = n ∧
        n + n * n + transPairCount D < B)
      (ardClearCom nN ro rt mk)
      (fun σ σ' => (∀ i, i < n * n → (σ'.arrs mk).getD i 0 = 0) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ y, y ∉ ardTzScalars → σ'.vars y = σ.vars y) ∧
        (∀ b, b ≠ mk → σ'.arrs b = σ.arrs b))
      (ardClearK n (transPairCount D)) := by
  classical
  obtain ⟨c1, c2, c3, c4, c5⟩ := ardTzScalars_ne hnN
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hreg, hnv, hB⟩ := hσ
  obtain ⟨ns, hns⟩ : ∃ ns, trOff D n = ns := ⟨_, rfl⟩
  have hnsT : ns ≤ transPairCount D := by rw [← hns]; exact trOff_le_transPairCount D
  have hnsB : ns < B := by omega
  have hnB : n < B := by omega
  have hsqB : n * n < B := by omega
  -- the three pointer initialisations and the extent
  obtain ⟨τ1, hτ1⟩ : ∃ τ, τ = σ.setVar "tz.j" 0 := ⟨_, rfl⟩
  have r1 : Run B (.assign "tz.j" (.lit 0)) σ τ1 2 := by
    rw [hτ1]; exact ard_run_assign (evalB_lit (by omega)) (by simp)
  obtain ⟨τ2, hτ2⟩ : ∃ τ, τ = τ1.setVar "tz.u" 0 := ⟨_, rfl⟩
  have r2 : Run B (.assign "tz.u" (.lit 0)) τ1 τ2 2 := by
    rw [hτ2]; exact ard_run_assign (evalB_lit (by omega)) (by simp)
  obtain ⟨τ3, hτ3⟩ : ∃ τ, τ = τ2.setVar "tz.b" 0 := ⟨_, rfl⟩
  have r3 : Run B (.assign "tz.b" (.lit 0)) τ2 τ3 2 := by
    rw [hτ3]; exact ard_run_assign (evalB_lit (by omega)) (by simp)
  have hτ3arr : ∀ b, τ3.arrs b = σ.arrs b := by
    intro b; rw [hτ3, arrs_setVar, hτ2, arrs_setVar, hτ1, arrs_setVar]
  have hτ3nN : τ3.vars nN = n := by
    rw [hτ3, vars_setVar, if_neg c3, hτ2, vars_setVar, if_neg c2,
      hτ1, vars_setVar, if_neg c1]
    exact hnv
  have hroGet : (σ.arrs ro)[n]? = some ns := by rw [← hns]; exact hreg.toGet n le_rfl
  have hroLen : n < (σ.arrs ro).length := by have := hreg.toLen; omega
  obtain ⟨τ4, hτ4⟩ : ∃ τ, τ = τ3.setVar "tz.m" ns := ⟨_, rfl⟩
  have r4 : Run B (.assign "tz.m" (.get ro (.var nN))) τ3 τ4 3 := by
    rw [hτ4]
    refine ard_run_assign (ard_evB_get (ard_evB_var hτ3nN hnB) ?_ ?_ hnsB) (by simp)
    · rw [hτ3arr]; exact hroLen
    · rw [hτ3arr]; exact hroGet
  have hτ4arr : ∀ b, τ4.arrs b = σ.arrs b := by
    intro b; rw [hτ4, arrs_setVar]; exact hτ3arr b
  have hτ4nN : τ4.vars nN = n := by rw [hτ4, vars_setVar, if_neg c4]; exact hτ3nN
  have hτ4m : τ4.vars "tz.m" = ns := by rw [hτ4, vars_setVar, if_pos rfl]
  have hτ4j : τ4.vars "tz.j" = 0 := by
    rw [hτ4, vars_setVar, if_neg (by decide), hτ3, vars_setVar, if_neg (by decide),
      hτ2, vars_setVar, if_neg (by decide), hτ1, vars_setVar, if_pos rfl]
  have hτ4u : τ4.vars "tz.u" = 0 := by
    rw [hτ4, vars_setVar, if_neg (by decide), hτ3, vars_setVar, if_neg (by decide),
      hτ2, vars_setVar, if_pos rfl]
  have hτ4b : τ4.vars "tz.b" = 0 := by
    rw [hτ4, vars_setVar, if_neg (by decide), hτ3, vars_setVar, if_pos rfl]
  -- the scan's invariant
  obtain ⟨I, hI⟩ : ∃ I : Env → Prop, I = fun ρ =>
      ρ.vars nN = n ∧ ρ.vars "tz.m" = ns ∧ ρ.vars "tz.j" ≤ ns ∧
        ρ.vars "tz.u" ≤ n ∧ ρ.vars "tz.b" = ρ.vars "tz.u" * n ∧
        trOff D (ρ.vars "tz.u") ≤ ρ.vars "tz.j" ∧
        ρ.arrs ro = σ.arrs ro ∧ ρ.arrs rt = σ.arrs rt ∧
        n * n ≤ (ρ.arrs mk).length ∧
        (∀ v : Fin n, ∀ p, p < ρ.vars "tz.j" → trOff D (v : ℕ) ≤ p →
          p < trOff D ((v : ℕ) + 1) →
          (ρ.arrs mk).getD ((v : ℕ) * n + ttF p) 0 = 0) ∧
        (∀ v u : Fin n, ¬ TransLink D u v →
          (ρ.arrs mk).getD ((v : ℕ) * n + (u : ℕ)) 0 = 0) := ⟨_, rfl⟩
  have hIb : ∀ ρ, I ρ → ρ.vars "tz.m" = ns ∧ ρ.vars "tz.j" ≤ ns ∧ ρ.vars "tz.u" ≤ n := by
    intro ρ hρ; rw [hI] at hρ; exact ⟨hρ.2.1, hρ.2.2.1, hρ.2.2.2.1⟩
  have hstep : ∀ ρ, I ρ → ρ.vars "tz.j" < ns →
      ∃ ρ' K', Run B (ardClearAct nN ro rt mk) ρ ρ' K' ∧ I ρ' ∧
        ρ.vars "tz.j" ≤ ρ'.vars "tz.j" ∧ ρ.vars "tz.u" ≤ ρ'.vars "tz.u" ∧
        (ρ.vars "tz.j" < ρ'.vars "tz.j" ∨ ρ.vars "tz.u" < ρ'.vars "tz.u") ∧
        K' ≤ 19 * (ρ'.vars "tz.j" - ρ.vars "tz.j")
          + 15 * (ρ'.vars "tz.u" - ρ.vars "tz.u") := by
    intro ρ hρ hjlt
    rw [hI] at hρ
    obtain ⟨hnv', hm', hjle, hule, hb', hoff', hro', hrt', hmkL, hcl, hzr⟩ := hρ
    obtain ⟨j, hj⟩ : ∃ j, ρ.vars "tz.j" = j := ⟨_, rfl⟩
    obtain ⟨u, hu⟩ : ∃ u, ρ.vars "tz.u" = u := ⟨_, rfl⟩
    rw [hj] at hjlt hjle hoff' hcl
    rw [hu] at hule hb' hoff'
    -- the owner is a real row: `trOff D u ≤ j < trOff D n`
    have hun : u < n := by
      by_contra hc
      have : trOff D n ≤ trOff D u := trOff_mono D (by omega)
      omega
    have hu1 : u + 1 ≤ n := by omega
    have hE : (σ.arrs ro)[u + 1]? = some (trOff D (u + 1)) := hreg.toGet (u + 1) hu1
    have hEle : trOff D (u + 1) ≤ ns := by rw [← hns]; exact trOff_mono D hu1
    have hEidx : u + 1 < (ρ.arrs ro).length := by rw [hro']; have := hreg.toLen; omega
    have hcond : (Expr.get ro (.add (.var "tz.u") (.lit 1))).evalB B ρ
        = some (trOff D (u + 1)) :=
      ard_evB_get (ard_evB_add (ard_evB_var hu (by omega)) (evalB_lit (by omega))
        (by omega)) hEidx (by rw [hro']; exact hE) (by omega)
    rcases Nat.lt_or_ge j (trOff D (u + 1)) with hin | hout
    · -- the slot branch
      have hbtrue : (Cond.lt (.var "tz.j") (.get ro (.add (.var "tz.u") (.lit 1)))).evalB B ρ
          = some true := by
        rw [evalB_condLt (ard_evB_var hj (by omega)) hcond]
        simp [hin]
      have hwGet : (ρ.arrs rt)[j]? = some (ttF j) := by
        rw [hrt']; exact hreg.ttGet j (by omega)
      have hwLt : ttF j < n := hreg.ttLt j (by omega)
      have hrtIdx : j < (ρ.arrs rt).length := by rw [hrt']; have := hreg.ttLen; omega
      obtain ⟨ρ1, hρ1⟩ : ∃ r, r = ρ.setVar "tz.w" (ttF j) := ⟨_, rfl⟩
      have s1 : Run B (.assign "tz.w" (.get rt (.var "tz.j"))) ρ ρ1 3 := by
        rw [hρ1]
        exact ard_run_assign
          (ard_evB_get (ard_evB_var hj (by omega)) hrtIdx hwGet (by omega)) (by simp)
      have hcell : u * n + ttF j < n * n := by
        calc u * n + ttF j < u * n + n := by omega
          _ = (u + 1) * n := by ring
          _ ≤ n * n := Nat.mul_le_mul_right n hu1
      obtain ⟨ρ2, hρ2⟩ : ∃ r, r = ρ1.setArr mk (u * n + ttF j) 0 := ⟨_, rfl⟩
      have s2 : Run B (.store mk (.add (.var "tz.b") (.var "tz.w")) (.lit 0)) ρ1 ρ2 5 := by
        rw [hρ2]
        refine ard_run_store (ard_evB_add (ard_evB_var ?_ (by omega))
          (ard_evB_var ?_ (by omega)) (by omega)) (evalB_lit (by omega)) ?_ (by simp)
        · rw [hρ1, vars_setVar, if_neg (by decide)]; exact hb'
        · rw [hρ1, vars_setVar, if_pos rfl]
        · rw [hρ1, arrs_setVar]; omega
      obtain ⟨ρ3, hρ3⟩ : ∃ r, r = ρ2.setVar "tz.j" (j + 1) := ⟨_, rfl⟩
      have s3 : Run B (.assign "tz.j" (.add (.var "tz.j") (.lit 1))) ρ2 ρ3 4 := by
        rw [hρ3]
        refine ard_run_assign (ard_evB_add (ard_evB_var ?_ (by omega))
          (evalB_lit (by omega)) (by omega)) (by simp)
        rw [hρ2, vars_setArr, hρ1, vars_setVar, if_neg (by decide)]; exact hj
      have h3mk : ρ3.arrs mk = (ρ.arrs mk).set (u * n + ttF j) 0 := by
        rw [hρ3, arrs_setVar, hρ2, arrs_setArr, if_pos rfl, hρ1, arrs_setVar]
      have h3idx : u * n + ttF j < (ρ.arrs mk).length := by omega
      have h3j : ρ3.vars "tz.j" = j + 1 := by rw [hρ3, vars_setVar, if_pos rfl]
      have h3u : ρ3.vars "tz.u" = u := by
        rw [hρ3, vars_setVar, if_neg (by decide), hρ2, vars_setArr,
          hρ1, vars_setVar, if_neg (by decide)]
        exact hu
      have h3b : ρ3.vars "tz.b" = u * n := by
        rw [hρ3, vars_setVar, if_neg (by decide), hρ2, vars_setArr,
          hρ1, vars_setVar, if_neg (by decide)]
        exact hb'
      have hact : Run B (ardClearAct nN ro rt mk) ρ ρ3 19 := by
        have h12 : Run B (.seq (.assign "tz.w" (.get rt (.var "tz.j")))
            (.seq (.store mk (.add (.var "tz.b") (.var "tz.w")) (.lit 0))
              (.assign "tz.j" (.add (.var "tz.j") (.lit 1))))) ρ ρ3 12 :=
          (s1.seq (s2.seq s3)).mono (by omega)
        exact (Run.ite_true hbtrue h12).mono (by simp [Cond.size, Expr.size])
      refine ⟨ρ3, 19, hact, ?_, by omega, by omega, by omega, by omega⟩
      rw [hI]
      refine ⟨?_, ?_, by rw [h3j]; omega, by rw [h3u]; omega, by rw [h3b, h3u], ?_,
        ?_, ?_, ?_, ?_, ?_⟩
      · rw [hρ3, vars_setVar, if_neg c1, hρ2, vars_setArr, hρ1, vars_setVar, if_neg c5]
        exact hnv'
      · rw [hρ3, vars_setVar, if_neg (by decide), hρ2, vars_setArr,
          hρ1, vars_setVar, if_neg (by decide)]
        exact hm'
      · rw [h3u, h3j]; omega
      · rw [hρ3, arrs_setVar, hρ2, arrs_setArr, if_neg (Ne.symm hmro), hρ1, arrs_setVar]
        exact hro'
      · rw [hρ3, arrs_setVar, hρ2, arrs_setArr, if_neg (Ne.symm hmrt), hρ1, arrs_setVar]
        exact hrt'
      · rw [h3mk, List.length_set]; exact hmkL
      · intro v p hp hp1 hp2
        rw [h3j] at hp
        rw [h3mk]
        refine ard_getD_set_zero h3idx ?_
        rcases Nat.lt_or_ge p j with hlt | hge
        · exact Or.inr (hcl v p hlt hp1 hp2)
        · have hpj : p = j := by omega
          subst hpj
          exact Or.inl (by rw [ardTrOff_owner_unique D hp1 hp2 hoff' hin])
      · intro v y hvy
        rw [h3mk]
        exact ard_getD_set_zero h3idx (Or.inr (hzr v y hvy))
    · -- the owner branch
      have hbfalse : (Cond.lt (.var "tz.j") (.get ro (.add (.var "tz.u") (.lit 1)))).evalB B ρ
          = some false := by
        rw [evalB_condLt (ard_evB_var hj (by omega)) hcond]
        simp [Nat.not_lt.2 hout]
      have hu1' : u + 1 < n := by
        by_contra hc
        have : trOff D n ≤ trOff D (u + 1) := trOff_mono D (by omega)
        omega
      obtain ⟨ρ1, hρ1⟩ : ∃ r, r = ρ.setVar "tz.u" (u + 1) := ⟨_, rfl⟩
      have s1 : Run B (.assign "tz.u" (.add (.var "tz.u") (.lit 1))) ρ ρ1 4 := by
        rw [hρ1]
        exact ard_run_assign (ard_evB_add (ard_evB_var hu (by omega))
          (evalB_lit (by omega)) (by omega)) (by simp)
      have hbnew : u * n + n = (u + 1) * n := by ring
      have hbB : (u + 1) * n ≤ n * n := Nat.mul_le_mul_right n (by omega)
      obtain ⟨ρ2, hρ2⟩ : ∃ r, r = ρ1.setVar "tz.b" (u * n + n) := ⟨_, rfl⟩
      have s2 : Run B (.assign "tz.b" (.add (.var "tz.b") (.var nN))) ρ1 ρ2 4 := by
        rw [hρ2]
        refine ard_run_assign (ard_evB_add (ard_evB_var ?_ (by omega))
          (ard_evB_var ?_ (by omega)) (by omega)) (by simp)
        · rw [hρ1, vars_setVar, if_neg (by decide)]; exact hb'
        · rw [hρ1, vars_setVar, if_neg c2]; exact hnv'
      have h2u : ρ2.vars "tz.u" = u + 1 := by
        rw [hρ2, vars_setVar, if_neg (by decide), hρ1, vars_setVar, if_pos rfl]
      have h2j : ρ2.vars "tz.j" = j := by
        rw [hρ2, vars_setVar, if_neg (by decide), hρ1, vars_setVar, if_neg (by decide)]
        exact hj
      have h2arr : ∀ b, ρ2.arrs b = ρ.arrs b := by
        intro b; rw [hρ2, arrs_setVar, hρ1, arrs_setVar]
      have hact : Run B (ardClearAct nN ro rt mk) ρ ρ2 15 := by
        have h8 : Run B (.seq (.assign "tz.u" (.add (.var "tz.u") (.lit 1)))
            (.assign "tz.b" (.add (.var "tz.b") (.var nN)))) ρ ρ2 8 :=
          (s1.seq s2).mono (by omega)
        exact (Run.ite_false hbfalse h8).mono (by simp [Cond.size, Expr.size])
      refine ⟨ρ2, 15, hact, ?_, by omega, by omega, by omega, by omega⟩
      rw [hI]
      refine ⟨?_, ?_, by rw [h2j]; omega, by rw [h2u]; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hρ2, vars_setVar, if_neg c3, hρ1, vars_setVar, if_neg c2]; exact hnv'
      · rw [hρ2, vars_setVar, if_neg (by decide), hρ1, vars_setVar, if_neg (by decide)]
        exact hm'
      · rw [h2u, hρ2, vars_setVar, if_pos rfl]; ring
      · rw [h2u, h2j]; exact hout
      · rw [h2arr]; exact hro'
      · rw [h2arr]; exact hrt'
      · rw [h2arr]; exact hmkL
      · rw [h2arr, h2j]; exact hcl
      · rw [h2arr]; exact hzr
  obtain ⟨τ5, hrun5, hI5, hj5⟩ :=
    (Csr.ownerScan_spec B (23 * ns + 19 * n + 4) n ns 19 15 "tz.j" "tz.m" "tz.u"
      (ardClearAct nN ro rt mk) I hnsB hIb hstep (fun _ h => h)
      (fun ρ hρ => by
        have h := hIb ρ hρ
        have h1 : (19 + 4) * (ns - ρ.vars "tz.j") ≤ 23 * ns :=
          Nat.mul_le_mul_left 23 (by omega)
        have h2 : (15 + 4) * (n - ρ.vars "tz.u") ≤ 19 * n :=
          Nat.mul_le_mul_left 19 (by omega)
        omega)).run (σ := τ4) (by
      rw [hI]
      refine ⟨hτ4nN, hτ4m, by rw [hτ4j]; omega, by rw [hτ4u]; omega,
        by rw [hτ4b, hτ4u]; simp, ?_, hτ4arr ro, hτ4arr rt, ?_, ?_, ?_⟩
      · rw [hτ4u, hτ4j, trOff_zero]
      · rw [hτ4arr]; exact hreg.markLen
      · intro v p hp; rw [hτ4j] at hp; omega
      · rw [hτ4arr]; exact hreg.markZero)
  rw [hI] at hI5
  obtain ⟨-, -, -, -, -, -, -, -, hmkL5, hcl5, hzr5⟩ := hI5
  rw [hj5] at hcl5
  have hrun : Run B (ardClearCom nN ro rt mk) σ τ5
      (2 + (2 + (2 + (3 + (23 * ns + 19 * n + 4))))) :=
    r1.seq (r2.seq (r3.seq (r4.seq hrun5)))
  refine ⟨τ5, _, hrun, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [ardClearK]; omega
  · -- every cell of the window is clear
    intro i hi
    have hn0 : 0 < n := by
      rcases Nat.eq_zero_or_pos n with rfl | h
      · simp at hi
      · exact h
    have hq : i / n < n := Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hi)
    have hr : i % n < n := Nat.mod_lt _ hn0
    have hidx : (i / n) * n + i % n = i := by rw [Nat.div_add_mod' i n]
    by_cases hlink : TransLink D ⟨i % n, hr⟩ ⟨i / n, hq⟩
    · obtain ⟨p, hp1, hp2, hp3⟩ := hreg.complete ⟨i / n, hq⟩ ⟨i % n, hr⟩ hlink
      have hpns : p < ns := by
        have hle : trOff D (((⟨i / n, hq⟩ : Fin n) : ℕ) + 1) ≤ trOff D n :=
          trOff_mono D (by simp only [Fin.val_mk]; omega)
        omega
      have := hcl5 ⟨i / n, hq⟩ p hpns hp1 hp2
      rw [hp3] at this
      simpa [hidx] using this
    · have := hzr5 ⟨i / n, hq⟩ ⟨i % n, hr⟩ hlink
      simpa [hidx] using this
  · intro b; exact run_arrs_length_eq hrun b
  · intro y hy; exact hrun.frame_var y (ard_not_mem_wvars_clear hy)
  · intro b hb; exact hrun.frame_arr b (ard_not_mem_warrs_clear hb)

/-! ## §3 The copy-back

`StepEmitIn` reads the orientation from `(o, t)` and writes the next one
into `(o', t')`, and `rdC j` is one command for all `R` rounds, so the
round has to move it back.  Two flat sweeps: `n + 1` offsets and
`arcCount (greedyStep rk D)` targets, one store each, with the slot
count published in `nA`.

Both sweeps are `Spec.forRangeZero` — the counter is owned by the
combinator and the body is a store and a bump. -/

/-- The copy's three scratch scalars. -/
def ardCpScalars : List String := ["ac.e", "ac.i", "ac.p"]

/-- The two regions the copy reads and the two it writes, four distinct
arrays. -/
structure ArdCpNames (o' t' io it : String) : Prop where
  /-- The source offsets are not a written region. -/
  o'_io : o' ≠ io
  /-- … -/
  o'_it : o' ≠ it
  /-- The source targets are not a written region. -/
  t'_io : t' ≠ io
  /-- … -/
  t'_it : t' ≠ it
  /-- The two written regions are distinct. -/
  io_it : io ≠ it

/-- The copy's four cell conditions: its own three scratch scalars are
not the caller's three figure cells, and the destination count cell is
not the carrier cell. -/
structure ArdCpCells (nN nO nA : String) : Prop where
  /-- … -/
  nN_notMem : nN ∉ ardCpScalars
  /-- … -/
  nO_notMem : nO ∉ ardCpScalars
  /-- … -/
  nA_notMem : nA ∉ ardCpScalars
  /-- The destination count cell is not the carrier cell. -/
  nA_nN : nA ≠ nN
  /-- … nor the source count cell, which the second sweep reads. -/
  nA_nO : nA ≠ nO

private theorem ardCpScalars_ne {y : String} (h : y ∉ ardCpScalars) :
    y ≠ "ac.e" ∧ y ≠ "ac.i" ∧ y ≠ "ac.p" := by
  refine ⟨?_, ?_, ?_⟩ <;>
    · intro hc
      rw [hc] at h
      exact h (by simp [ardCpScalars])

/-- **The copy-back.**  Publish the count, then the offsets, then the
targets. -/
def ardCopyCom (nN nO nA o' t' io it : String) : Com :=
  .seq (.assign nA (.var nO))
    (.seq (.assign "ac.e" (.add (.var nN) (.lit 1)))
      (.seq
        (.seq (.assign "ac.i" (.lit 0))
          (.while (.lt (.var "ac.i") (.var "ac.e"))
            (.seq (.store io (.var "ac.i") (.get o' (.var "ac.i")))
              (.assign "ac.i" (.add (.var "ac.i") (.lit 1))))))
        (.seq (.assign "ac.p" (.lit 0))
          (.while (.lt (.var "ac.p") (.var nO))
            (.seq (.store it (.var "ac.p") (.get t' (.var "ac.p")))
              (.assign "ac.p" (.add (.var "ac.p") (.lit 1))))))))

/-- The copy's budget: `12·n + 12·a + 32`. -/
def ardCopyK (n a : ℕ) : ℕ := 12 * n + 12 * a + 32

/-- The arrays `ardCopyCom` can store into: its own two. -/
theorem ard_not_mem_warrs_copy {nN nO nA o' t' io it b : String}
    (h1 : b ≠ io) (h2 : b ≠ it) :
    b ∉ (ardCopyCom nN nO nA o' t' io it).warrs := by
  simp [ardCopyCom, Com.warrs, h1, h2]

/-- The scalars `ardCopyCom` can assign to: its own three, and `nA`. -/
theorem ard_not_mem_wvars_copy {nN nO nA o' t' io it y : String}
    (h1 : y ∉ ardCpScalars) (h2 : y ≠ nA) :
    y ∉ (ardCopyCom nN nO nA o' t' io it).wvars := by
  obtain ⟨a1, a2, a3⟩ := ardCpScalars_ne h1
  simp [ardCopyCom, Com.wvars, a1, a2, a3, h2]

/-- **The copy-back, specified.**  From a windowed in-neighbour CSR of
`D` in `(o', t')` with the slot count in `nO`, leave one in `(io, it)`
at the **same** `off` and `tgt`, with the count in `nA` and nothing
else written.

The destination allocations are asked for, not promised: `store` is
`List.set` and cannot lengthen an array, so an allocation clause in the
postcondition would be a hidden requirement on the caller. -/
theorem ardCopy_spec {B : ℕ} {nN nO nA o' t' io it : String}
    (hnm : ArdCpNames o' t' io it) (hcl : ArdCpCells nN nO nA)
    {n : ℕ} (D : Orientation n) (off tgt : ℕ → ℕ) :
    Spec B
      (fun σ => TrInCsr o' t' D (arcCount D) off tgt σ ∧
        σ.vars nN = n ∧ σ.vars nO = arcCount D ∧
        n + arcCount D + 1 < B ∧
        n + 1 ≤ (σ.arrs io).length ∧ arcCount D ≤ (σ.arrs it).length)
      (ardCopyCom nN nO nA o' t' io it)
      (fun σ σ' => TrInCsr io it D (arcCount D) off tgt σ' ∧
        σ'.vars nA = arcCount D ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ y, y ∉ ardCpScalars → y ≠ nA → σ'.vars y = σ.vars y) ∧
        (∀ b, b ≠ io → b ≠ it → σ'.arrs b = σ.arrs b))
      (ardCopyK n (arcCount D)) := by
  classical
  obtain ⟨e1, e2, e3⟩ := ardCpScalars_ne hcl.nN_notMem
  obtain ⟨f1, f2, f3⟩ := ardCpScalars_ne hcl.nO_notMem
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hcsr, hnv, hav, hB, hioL, hitL⟩ := hσ
  obtain ⟨a, ha⟩ : ∃ a, arcCount D = a := ⟨_, rfl⟩
  rw [ha] at hcsr hav hB hitL
  have hoffle : ∀ i, i ≤ n → off i ≤ a := by
    intro i hi
    have := hcsr.mono n le_rfl i hi
    rw [hcsr.last] at this
    exact this
  -- publish the count
  obtain ⟨τ0, hτ0⟩ : ∃ τ, τ = σ.setVar nA a := ⟨_, rfl⟩
  have r0 : Run B (.assign nA (.var nO)) σ τ0 2 := by
    rw [hτ0]; exact ard_run_assign (ard_evB_var hav (by omega)) (by simp)
  -- the offset bound cell
  obtain ⟨τ1, hτ1⟩ : ∃ τ, τ = τ0.setVar "ac.e" (n + 1) := ⟨_, rfl⟩
  have hτ0nN : τ0.vars nN = n := by rw [hτ0, vars_setVar, if_neg hcl.nA_nN.symm]; exact hnv
  have r1 : Run B (.assign "ac.e" (.add (.var nN) (.lit 1))) τ0 τ1 4 := by
    rw [hτ1]
    exact ard_run_assign
      (ard_evB_add (ard_evB_var hτ0nN (by omega)) (evalB_lit (by omega)) (by omega))
      (by simp)
  have hτ1arr : ∀ b, τ1.arrs b = σ.arrs b := by
    intro b; rw [hτ1, arrs_setVar, hτ0, arrs_setVar]
  have hτ1nN : τ1.vars nN = n := by
    rw [hτ1, vars_setVar, if_neg e1]; exact hτ0nN
  have hτ1nO : τ1.vars nO = a := by
    rw [hτ1, vars_setVar, if_neg f1, hτ0, vars_setVar, if_neg hcl.nA_nO.symm]; exact hav
  have hτ1e : τ1.vars "ac.e" = n + 1 := by rw [hτ1, vars_setVar, if_pos rfl]
  -- sweep 1: the offsets
  have hbody1 : Spec B
      (fun ρ => (TrInCsr o' t' D a off tgt ρ ∧ ρ.vars "ac.e" = n + 1 ∧
        ρ.vars nO = a ∧ ρ.vars "ac.i" ≤ n + 1 ∧
        n + 1 ≤ (ρ.arrs io).length ∧ a ≤ (ρ.arrs it).length ∧
        (∀ i, i < ρ.vars "ac.i" → (ρ.arrs io)[i]? = some (off i))) ∧
        ρ.vars "ac.i" < n + 1)
      (.seq (.store io (.var "ac.i") (.get o' (.var "ac.i")))
        (.assign "ac.i" (.add (.var "ac.i") (.lit 1))))
      (fun ρ ρ' => (TrInCsr o' t' D a off tgt ρ' ∧ ρ'.vars "ac.e" = n + 1 ∧
        ρ'.vars nO = a ∧ ρ'.vars "ac.i" ≤ n + 1 ∧
        n + 1 ≤ (ρ'.arrs io).length ∧ a ≤ (ρ'.arrs it).length ∧
        (∀ i, i < ρ'.vars "ac.i" → (ρ'.arrs io)[i]? = some (off i))) ∧
        ρ'.vars "ac.i" = ρ.vars "ac.i" + 1) 8 := by
    refine Spec.of_exists (fun ρ hρ => ?_)
    obtain ⟨⟨hc, he, hno, hile, hioL', hitL', hpre⟩, hilt⟩ := hρ
    obtain ⟨i, hi⟩ : ∃ i, ρ.vars "ac.i" = i := ⟨_, rfl⟩
    rw [hi] at hilt hile hpre
    have hiB : i < B := by omega
    have hiSrc : i < (ρ.arrs o').length := by have := hc.offLen; omega
    have hiDst : i < (ρ.arrs io).length := by omega
    have hval : (ρ.arrs o')[i]? = some (off i) := hc.offGet i (by omega)
    have hvalB : off i < B := by have := hoffle i (by omega); omega
    obtain ⟨ρ1, hρ1⟩ : ∃ r, r = ρ.setArr io i (off i) := ⟨_, rfl⟩
    have s1 : Run B (.store io (.var "ac.i") (.get o' (.var "ac.i"))) ρ ρ1 4 := by
      rw [hρ1]
      exact ard_run_store (ard_evB_var hi hiB)
        (ard_evB_get (ard_evB_var hi hiB) hiSrc hval hvalB) hiDst (by simp)
    obtain ⟨ρ2, hρ2⟩ : ∃ r, r = ρ1.setVar "ac.i" (i + 1) := ⟨_, rfl⟩
    have s2 : Run B (.assign "ac.i" (.add (.var "ac.i") (.lit 1))) ρ1 ρ2 4 := by
      rw [hρ2]
      refine ard_run_assign (ard_evB_add (ard_evB_var ?_ hiB)
        (evalB_lit (by omega)) (by omega)) (by simp)
      rw [hρ1, vars_setArr]; exact hi
    have h2io : ρ2.arrs io = (ρ.arrs io).set i (off i) := by
      rw [hρ2, arrs_setVar, hρ1, arrs_setArr, if_pos rfl]
    have h2i : ρ2.vars "ac.i" = i + 1 := by rw [hρ2, vars_setVar, if_pos rfl]
    have h2o' : ρ2.arrs o' = ρ.arrs o' := by
      rw [hρ2, arrs_setVar, hρ1, arrs_setArr, if_neg hnm.o'_io]
    have h2t' : ρ2.arrs t' = ρ.arrs t' := by
      rw [hρ2, arrs_setVar, hρ1, arrs_setArr, if_neg hnm.t'_io]
    have h2it : ρ2.arrs it = ρ.arrs it := by
      rw [hρ2, arrs_setVar, hρ1, arrs_setArr, if_neg (Ne.symm hnm.io_it)]
    refine ⟨ρ2, 8, (s1.seq s2).mono (by omega), le_rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      by rw [h2i, hi]⟩
    · exact ardTrInCsr_rename hc (by rw [h2o']; exact hc.offLen)
        (by rw [h2t']; exact hc.tgtLen) (by rw [h2o']; exact hc.offGet)
        (by rw [h2t']; exact hc.tgtGet)
    · rw [hρ2, vars_setVar, if_neg (by simp), hρ1, vars_setArr]; exact he
    · rw [hρ2, vars_setVar, if_neg f2, hρ1, vars_setArr]; exact hno
    · rw [h2i]; omega
    · rw [h2io, List.length_set]; exact hioL'
    · rw [h2it]; exact hitL'
    · intro k hk
      rw [h2i] at hk
      rw [h2io]
      rcases eq_or_ne k i with rfl | hki
      · rw [ard_getElem?_of_lt _ _ (by rw [List.length_set]; exact hiDst),
          ard_getD_set_self hiDst]
      · rw [List.getElem?_set_ne (Ne.symm hki)]
        exact hpre k (by omega)
  have hinit1 : ∀ b, ((τ1.setVar "ac.i" 0).arrs b) = σ.arrs b := by
    intro b; rw [arrs_setVar, hτ1arr]
  obtain ⟨τ2, hrun2, ⟨hc2, he2, hno2, -, hioL2, hitL2, hoff2⟩, hi2⟩ :=
    (Spec.forRangeZero (B := B) "ac.i" "ac.e"
      (fun ρ => TrInCsr o' t' D a off tgt ρ ∧ ρ.vars "ac.e" = n + 1 ∧
        ρ.vars nO = a ∧ ρ.vars "ac.i" ≤ n + 1 ∧
        n + 1 ≤ (ρ.arrs io).length ∧ a ≤ (ρ.arrs it).length ∧
        (∀ i, i < ρ.vars "ac.i" → (ρ.arrs io)[i]? = some (off i)))
      (n + 1) 8 (by omega) (fun _ hI => hI.2.2.2.1) (fun _ hI => hI.2.1)
      hbody1).run (σ := τ1)
      ⟨ardTrInCsr_rename hcsr (by rw [hinit1]; exact hcsr.offLen)
        (by rw [hinit1]; exact hcsr.tgtLen) (by rw [hinit1]; exact hcsr.offGet)
        (by rw [hinit1]; exact hcsr.tgtGet),
       by rw [vars_setVar, if_neg (by simp)]; exact hτ1e,
       by rw [vars_setVar, if_neg f2]; exact hτ1nO,
       by simp, by rw [hinit1]; exact hioL,
       by rw [hinit1]; exact hitL,
       by intro i hi'; simp at hi'⟩
  rw [hi2] at hoff2
  -- sweep 2: the targets
  have hbody2 : Spec B
      (fun ρ => (TrInCsr o' t' D a off tgt ρ ∧ ρ.vars nO = a ∧
        ρ.vars "ac.p" ≤ a ∧ a ≤ (ρ.arrs it).length ∧
        (∀ i, i ≤ n → (ρ.arrs io)[i]? = some (off i)) ∧
        n + 1 ≤ (ρ.arrs io).length ∧
        (∀ p, p < ρ.vars "ac.p" → (ρ.arrs it)[p]? = some (tgt p))) ∧
        ρ.vars "ac.p" < a)
      (.seq (.store it (.var "ac.p") (.get t' (.var "ac.p")))
        (.assign "ac.p" (.add (.var "ac.p") (.lit 1))))
      (fun ρ ρ' => (TrInCsr o' t' D a off tgt ρ' ∧ ρ'.vars nO = a ∧
        ρ'.vars "ac.p" ≤ a ∧ a ≤ (ρ'.arrs it).length ∧
        (∀ i, i ≤ n → (ρ'.arrs io)[i]? = some (off i)) ∧
        n + 1 ≤ (ρ'.arrs io).length ∧
        (∀ p, p < ρ'.vars "ac.p" → (ρ'.arrs it)[p]? = some (tgt p))) ∧
        ρ'.vars "ac.p" = ρ.vars "ac.p" + 1) 8 := by
    refine Spec.of_exists (fun ρ hρ => ?_)
    obtain ⟨⟨hc, hno, hple, hitL', hio', hioL', hpre⟩, hplt⟩ := hρ
    obtain ⟨p, hp⟩ : ∃ p, ρ.vars "ac.p" = p := ⟨_, rfl⟩
    rw [hp] at hplt hple hpre
    have hpB : p < B := by omega
    have hpSrc : p < (ρ.arrs t').length := by have := hc.tgtLen; omega
    have hpDst : p < (ρ.arrs it).length := by omega
    have hval : (ρ.arrs t')[p]? = some (tgt p) := hc.tgtGet p (by omega)
    have hvalB : tgt p < B := by have := hc.tgtLt p (by omega); omega
    obtain ⟨ρ1, hρ1⟩ : ∃ r, r = ρ.setArr it p (tgt p) := ⟨_, rfl⟩
    have s1 : Run B (.store it (.var "ac.p") (.get t' (.var "ac.p"))) ρ ρ1 4 := by
      rw [hρ1]
      exact ard_run_store (ard_evB_var hp hpB)
        (ard_evB_get (ard_evB_var hp hpB) hpSrc hval hvalB) hpDst (by simp)
    obtain ⟨ρ2, hρ2⟩ : ∃ r, r = ρ1.setVar "ac.p" (p + 1) := ⟨_, rfl⟩
    have s2 : Run B (.assign "ac.p" (.add (.var "ac.p") (.lit 1))) ρ1 ρ2 4 := by
      rw [hρ2]
      refine ard_run_assign (ard_evB_add (ard_evB_var ?_ hpB)
        (evalB_lit (by omega)) (by omega)) (by simp)
      rw [hρ1, vars_setArr]; exact hp
    have h2it : ρ2.arrs it = (ρ.arrs it).set p (tgt p) := by
      rw [hρ2, arrs_setVar, hρ1, arrs_setArr, if_pos rfl]
    have h2p : ρ2.vars "ac.p" = p + 1 := by rw [hρ2, vars_setVar, if_pos rfl]
    have h2o' : ρ2.arrs o' = ρ.arrs o' := by
      rw [hρ2, arrs_setVar, hρ1, arrs_setArr, if_neg hnm.o'_it]
    have h2t' : ρ2.arrs t' = ρ.arrs t' := by
      rw [hρ2, arrs_setVar, hρ1, arrs_setArr, if_neg hnm.t'_it]
    have h2io : ρ2.arrs io = ρ.arrs io := by
      rw [hρ2, arrs_setVar, hρ1, arrs_setArr, if_neg hnm.io_it]
    refine ⟨ρ2, 8, (s1.seq s2).mono (by omega), le_rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩,
      by rw [h2p, hp]⟩
    · exact ardTrInCsr_rename hc (by rw [h2o']; exact hc.offLen)
        (by rw [h2t']; exact hc.tgtLen) (by rw [h2o']; exact hc.offGet)
        (by rw [h2t']; exact hc.tgtGet)
    · rw [hρ2, vars_setVar, if_neg f3, hρ1, vars_setArr]; exact hno
    · rw [h2p]; omega
    · rw [h2it, List.length_set]; exact hitL'
    · rw [h2io]; exact hio'
    · rw [h2io]; exact hioL'
    · intro k hk
      rw [h2p] at hk
      rw [h2it]
      rcases eq_or_ne k p with rfl | hkp
      · rw [ard_getElem?_of_lt _ _ (by rw [List.length_set]; exact hpDst),
          ard_getD_set_self hpDst]
      · rw [List.getElem?_set_ne (Ne.symm hkp)]
        exact hpre k (by omega)
  have hinit2 : ∀ b, ((τ2.setVar "ac.p" 0).arrs b) = τ2.arrs b := by
    intro b; rw [arrs_setVar]
  obtain ⟨τ3, hrun3, ⟨hc3, hno3, -, hitL3, hio3, hioL3, htgt3⟩, hp3⟩ :=
    (Spec.forRangeZero (B := B) "ac.p" nO
      (fun ρ => TrInCsr o' t' D a off tgt ρ ∧ ρ.vars nO = a ∧
        ρ.vars "ac.p" ≤ a ∧ a ≤ (ρ.arrs it).length ∧
        (∀ i, i ≤ n → (ρ.arrs io)[i]? = some (off i)) ∧
        n + 1 ≤ (ρ.arrs io).length ∧
        (∀ p, p < ρ.vars "ac.p" → (ρ.arrs it)[p]? = some (tgt p)))
      a 8 (by omega) (fun _ hI => hI.2.2.1) (fun _ hI => hI.2.1) hbody2).run (σ := τ2)
      ⟨ardTrInCsr_rename hc2 (by rw [hinit2]; exact hc2.offLen)
        (by rw [hinit2]; exact hc2.tgtLen) (by rw [hinit2]; exact hc2.offGet)
        (by rw [hinit2]; exact hc2.tgtGet),
       by rw [vars_setVar, if_neg f3]; exact hno2,
       by simp, by rw [hinit2]; exact hitL2,
       by
         rw [hinit2]
         intro i hi'
         exact hoff2 i (by omega),
       by rw [hinit2]; exact hioL2,
       by intro p hp'; simp at hp'⟩
  rw [hp3] at htgt3
  -- the whole run, and its frame
  have hrun : Run B (ardCopyCom nN nO nA o' t' io it) σ τ3
      (2 + (4 + ((8 + 4) * (n + 1) + 6 + ((8 + 4) * a + 6)))) :=
    r0.seq (r1.seq (hrun2.seq hrun3))
  obtain ⟨b1, b2, b3⟩ := ardCpScalars_ne hcl.nA_notMem
  refine ⟨τ3, _, hrun, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ha]; simp only [ardCopyK]; omega
  · rw [ha]
    exact ardTrInCsr_rename hc3 hioL3 hitL3 hio3 htgt3
  · rw [ha]
    have hnaτ1 : τ1.vars nA = a := by
      rw [hτ1, vars_setVar, if_neg b1, hτ0, vars_setVar, if_pos rfl]
    -- `nA` is written only by the first line; the two sweeps do not
    -- touch it
    have h2 : τ2.vars nA = τ1.vars nA :=
      hrun2.frame_var nA (by simp [Com.wvars, b2])
    have h3 : τ3.vars nA = τ2.vars nA :=
      hrun3.frame_var nA (by simp [Com.wvars, b3])
    rw [h3, h2, hnaτ1]
  · intro b
    exact run_arrs_length_eq hrun b
  · intro y hy hy2
    exact hrun.frame_var y (ard_not_mem_wvars_copy hy hy2)
  · intro b h1 h2
    exact hrun.frame_arr b (ard_not_mem_warrs_copy h1 h2)

/-! ## §3b The two named contracts, discharged

`SolveAugRoundSeams` §2 and §3 stated the two missing passes as
`TrClearAt` and `InCsrCopyAt`.  Both are now programs. -/

private theorem ard_getD_of_ge {l : List ℕ} {i : ℕ} (h : l.length ≤ i) :
    l.getD i 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

/-- **`TrClearAt`, discharged** by `ardClearCom` at
`trClearK n T = 19·n + 23·T + 20`.  The contract's exact-length
precondition is what turns this file's "the window is clear" into the
contract's "every cell is clear": beyond `n·n` the array is not there,
and `List.getD` is the default. -/
theorem ardClearAt {B : ℕ} {nN ro rt mk : String}
    (hmro : mk ≠ ro) (hmrt : mk ≠ rt) (hnN : nN ∉ ardTzScalars) :
    TrClearAt B nN ro rt mk (ardClearCom nN ro rt mk) trClearK := by
  intro n D ttF
  refine ((ardClear_spec hmro hmrt hnN D ttF).pre (fun σ hσ => ⟨hσ.1, hσ.2.1,
    hσ.2.2.1⟩)).post (fun σ σ' hσ hQ => ⟨?_, hQ.2.2.2⟩)
  intro i
  rcases Nat.lt_or_ge i (n * n) with hi | hi
  · exact hQ.1 i hi
  · exact ard_getD_of_ge (by rw [hQ.2.1 mk, hσ.2.2.2]; exact hi)

/-- **`InCsrCopyAt`, discharged** by `ardCopyCom` at
`inCsrCopyK n a = 12·n + 12·a + 32`. -/
theorem ardCopyAt {B : ℕ} {nN nO nA o' t' io it : String}
    (hnm : ArdCpNames o' t' io it) (hcl : ArdCpCells nN nO nA) :
    InCsrCopyAt B nN nO nA o' t' io it (ardCopyCom nN nO nA o' t' io it)
      inCsrCopyK := by
  intro n D off tgt
  exact ((ardCopy_spec hnm hcl D off tgt).post
    (fun _ _ _ hQ => ⟨⟨off, tgt, hQ.1⟩, hQ.2.1, hQ.2.2.2.2⟩))

/-! ## §4 The word bound — the one thing that is F7-c's

`augRdBody_spec` asks for `n + n² + a + f + T < B`.  At `B = mcB q x`
the landed material supplies the first two terms and nothing about the
other three, and this section says exactly what supplies them.

`ArdWord` is the hypothesis, quantified exactly as `AugRoundIn` is, so
it can be discharged arena by arena and nothing about it is hidden
inside the round's proof. -/

/-- **The round's word bound**, as a named hypothesis: at every input,
every level, every admissible non-edgeless arena and every round, the
five figures the round computes with are words. -/
def ArdWord (C : GraphClass) (hC : NowhereDense C) (φ : FO 0)
    (sel : ∀ m : ℕ, MinDegSel m) (R : ℕ) {n : ℕ} (G : SimpleGraph (Fin n))
    (c w q : ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop) :
    Prop :=
  ∀ x ∈ mcD n G c w,
    ∀ j, j < (Headline.headlineSetup C hC φ).depth →
    ∀ A : Arena ((Headline.headlineSetup C hC φ).pal j) n,
      Adm j A → ¬ A.G = ⊥ → ∀ i, i < R →
      A.N + A.N * A.N + arcCount (selChain (sel A.N) A.G i)
        + fratPairCount (selChain (sel A.N) A.G i)
        + transPairCount (selChain (sel A.N) A.G i) + 1 < mcB q x

/-- **The inequality `q` must satisfy.**  Under an in-degree bound `d`
on the orientation, the round's five figures are words as soon as

* some `K` bounds `d²` by `K·(N + 1)` — a condition on the *exponent*
  of the density bound, and nothing else — and
* `q ≥ 3·K + 2`.

The proof is four steps and no estimate is wasted: `a ≤ N·d ≤ N·d²`,
`f, T ≤ N·d²`, `N·d² ≤ K·(N+1)²`, and `N + N² + 1 ≤ (N+1)²`, so the
whole is at most `(1 + 3K)·(N+1)² < q·(|x|+1)² = mcB q x`. -/
theorem ardWordBound_of_inDegLE {N K q d : ℕ} {x : List ℕ} {D : Orientation N}
    (hd : D.InDegLE d) (hK : d * d ≤ K * (N + 1)) (hNx : N ≤ x.length)
    (hq : 3 * K + 2 ≤ q) :
    N + N * N + arcCount D + fratPairCount D + transPairCount D + 1 < mcB q x := by
  have hdd : d ≤ d * d := by
    rcases Nat.eq_zero_or_pos d with rfl | h
    · simp
    · exact Nat.le_mul_of_pos_left d h
  have ha : arcCount D ≤ N * (d * d) :=
    le_trans (arcCount_le hd) (Nat.mul_le_mul_left N hdd)
  have hf : fratPairCount D ≤ N * (d * d) := fratPairCount_le hd
  have ht : transPairCount D ≤ N * (d * d) := transPairCount_le hd
  have hcell : N * (d * d) ≤ K * ((N + 1) * (N + 1)) := by
    calc N * (d * d) ≤ N * (K * (N + 1)) := Nat.mul_le_mul_left N hK
      _ = K * (N * (N + 1)) := by ring
      _ ≤ K * ((N + 1) * (N + 1)) :=
          Nat.mul_le_mul_left K (Nat.mul_le_mul_right _ (by omega))
  have hsq : N + N * N + 1 ≤ (N + 1) * (N + 1) := by nlinarith
  have hstep : N + N * N + arcCount D + fratPairCount D + transPairCount D + 1
      ≤ (1 + 3 * K) * ((N + 1) * (N + 1)) := by
    have : (1 + 3 * K) * ((N + 1) * (N + 1))
        = (N + 1) * (N + 1) + (K * ((N + 1) * (N + 1))
          + (K * ((N + 1) * (N + 1)) + K * ((N + 1) * (N + 1)))) := by ring
    omega
  have hmono : (N + 1) * (N + 1) ≤ (x.length + 1) * (x.length + 1) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hpos : 0 < (x.length + 1) * (x.length + 1) := Nat.mul_pos (by omega) (by omega)
  have hlast : (1 + 3 * K) * ((N + 1) * (N + 1))
      < q * ((x.length + 1) * (x.length + 1)) := by
    calc (1 + 3 * K) * ((N + 1) * (N + 1))
        ≤ (1 + 3 * K) * ((x.length + 1) * (x.length + 1)) :=
          Nat.mul_le_mul_left _ hmono
      _ < q * ((x.length + 1) * (x.length + 1)) :=
          Nat.mul_lt_mul_of_lt_of_le (by omega) le_rfl hpos
  rw [mcB, pow_two]
  omega

/-- Every arena's carrier is at most the root's — the embedding `up`
says so, with no state involved. -/
theorem ardArena_N_le {Λ n₀ : ℕ} (A : Arena Λ n₀) : A.N ≤ n₀ := by
  simpa using Fintype.card_le_of_embedding A.up

/-- **`ArdWord`, from an in-degree bound on the chain and a big enough
`q`.**  This is the whole of gap (d): the machine contributes nothing,
the class contributes `d`, and `q` is F7-c's. -/
theorem ardWord_of_inDegLE {C : GraphClass} {hC : NowhereDense C} {φ : FO 0}
    {sel : ∀ m : ℕ, MinDegSel m} {R : ℕ} {n : ℕ} {G : SimpleGraph (Fin n)}
    {c w q : ℕ}
    {Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop}
    (d : ℕ → ℕ) (K : ℕ)
    (hdeg : ∀ (j : ℕ) (A : Arena ((Headline.headlineSetup C hC φ).pal j) n),
      Adm j A → ¬ A.G = ⊥ → ∀ i, i < R →
      (selChain (sel A.N) A.G i).InDegLE (d A.N))
    (hK : ∀ m, d m * d m ≤ K * (m + 1)) (hq : 3 * K + 2 ≤ q) :
    ArdWord C hC φ sel R G c w q Adm := by
  intro x hx j hj A hAdm hbot i hi
  have henc : EncodesGraph x n G := hx.1
  have hlen := henc.length_eq
  exact ardWordBound_of_inDegLE (hdeg j A hAdm hbot i hi) (hK A.N)
    (le_trans (ardArena_N_le A) (by omega)) hq

/-! ### The structural half `Adm` *does* supply

`chainAdm`'s `Inv` half is not silent about the arena's graph: on every
arena with an edge it carries a `ReachedS` play whose position is
`SimpleGraph.map A.up A.G`, and a play only deletes edges
(`reachedS_le`).  So the arena's graph is a subgraph copy of the root's,
which is exactly the hypothesis `exists_selChain_inDegLE_pow` consumes
to produce the `d` above.  What is *not* derivable from any `Adm` is the
comparison between `d` and `q`. -/

/-- A graph is a copy of its own image under an embedding. -/
theorem ardIsContained_map {m n₀ : ℕ} (H : SimpleGraph (Fin m))
    (f : Fin m ↪ Fin n₀) : H ⊑ SimpleGraph.map f H := by
  refine ⟨⟨⟨fun a => f a, ?_⟩, ?_⟩⟩
  · intro a b hab
    exact SimpleGraph.map_adj_apply.2 hab
  · intro a b h
    exact f.injective h

/-- **`Inv` supplies the containment.**  On an arena with an edge the
run invariant's third clause is a `ReachedS` play at
`SimpleGraph.map A.up A.G`, and every reachable position is a subgraph
of the original. -/
theorem ardIsContained_of_inv {L n₀ : ℕ} {S : Setup L} {G₀ : SimpleGraph (Fin n₀)}
    {j : ℕ} {A : Arena (S.pal j) n₀} (h : Inv S G₀ j A) (hbot : ¬ A.G = ⊥) :
    A.G ⊑ G₀ := by
  obtain ⟨-, -, hb | ⟨rounds, -, -, hR, -⟩⟩ := h
  · exact absurd hb hbot
  · exact (ardIsContained_map A.G A.up).mono_right (ReachedS.reachedS_le hR)

/-- The same at the pinned `Adm` (`SolveF7Adm` §1): below the leaf level
`chainAdm` is `prepAdm` conjoined with `Inv`, so it delivers the
containment on every arena with an edge. -/
theorem ardIsContained_of_chainAdm {L n₀ : ℕ} {S : Setup L}
    {G₀ : SimpleGraph (Fin n₀)} {j : ℕ} {A : Arena (S.pal j) n₀}
    (hj : j ≤ S.depth) (h : chainAdm S G₀ j A) (hbot : ¬ A.G = ⊥) :
    A.G ⊑ G₀ := ardIsContained_of_inv (h.2 hj) hbot

/-! ## §5 The round, assembled

    rdC j = frZero(ad) ; frZero(sd) ; frZero(dgE)
          ; augRdBody ; ardClearCom ; ardCopyCom

The three carrier sweeps come **first**, so the round's descriptor does
not have to carry them and the round restores every region the *next*
round reads: the fraternal mark window (`augRdBody`), the transitive
mark window (`ardClearCom`), and the orientation pair (`ardCopyCom`). -/

/-- The union of the seven scratch pools the round's six passes own. -/
def ardScalars : List String :=
  frScalars ++ fpScalars ++ trScalars ++ emScalars ++ tpScalars ++
    ardTzScalars ++ ardCpScalars

theorem ard_notMem_pools {y : String} (h : y ∉ ardScalars) :
    y ∉ frScalars ∧ y ∉ fpScalars ∧ y ∉ trScalars ∧ y ∉ emScalars ∧
      y ∉ tpScalars ∧ y ∉ ardTzScalars ∧ y ∉ ardCpScalars := by
  simp only [ardScalars, List.mem_append, not_or] at h
  tauto

/-- The twenty-two working regions of a round, as a list: the twenty
`augRdAllocs` names and the orientation pair the round reads and writes
back. -/
def ardRegions (io it fo ft dgF ao aj dgP mt sg tp sk ro rt mkT o' t' qo qt
    ad sd dgE : ℕ → String) (j : ℕ) : List String :=
  io j :: it j :: augRdAllocs (fo j) (ft j) (dgF j) (ao j) (aj j) (dgP j)
    (mt j) (sg j) (tp j) (sk j) (ro j) (rt j) (mkT j) (o' j) (t' j) (qo j)
    (qt j) (ad j) (sd j) (dgE j)

/-- **The allocation the round's regions are sized at.**  It has to be a
figure of the *carrier alone*, because `Srd` is one predicate for all
`R` rounds while the three counts grow from round to round and an
array's length cannot: `arcCount D ≤ N²` and
`fratPairCount D, transPairCount D ≤ N³` at every orientation of `Fin
N`, so `2N³ + N² + N + 1` dominates every allocation any round asks
for.  This is *space*, not time — `Imp.lean:20-44`, memory starts zeroed
and an array of any length is there for free — and it is the only place
in the round where a figure of the carrier alone appears. -/
def ardCap (N : ℕ) : ℕ := 2 * (N * (N * N)) + N * N + N + 1

/-- Every orientation of `Fin N` has in-degree at most `N`. -/
theorem ardInDegLE_self {N : ℕ} (D : Orientation N) : D.InDegLE N := by
  intro v
  simpa using Finset.card_le_univ (D.inN v)

theorem ardArc_le {N : ℕ} (D : Orientation N) : arcCount D ≤ N * N := by
  have := two_mul_arcCount_le_sq_orient D
  omega

theorem ardFrat_le {N : ℕ} (D : Orientation N) :
    fratPairCount D ≤ N * (N * N) := fratPairCount_le (ardInDegLE_self D)

theorem ardTrans_le {N : ℕ} (D : Orientation N) :
    transPairCount D ≤ N * (N * N) := transPairCount_le (ardInDegLE_self D)

/-- Everything a round asks of an allocation is below `ardCap`. -/
theorem ardCap_bounds {N : ℕ} (D : Orientation N) :
    N + 1 ≤ ardCap N ∧ N * N ≤ ardCap N ∧ N * N + N ≤ ardCap N ∧
      arcCount D ≤ ardCap N ∧ fratPairCount D ≤ ardCap N ∧
      transPairCount D ≤ ardCap N ∧
      arcCount D + fratPairCount D + transPairCount D ≤ ardCap N := by
  have h1 := ardArc_le D
  have h2 := ardFrat_le D
  have h3 := ardTrans_le D
  simp only [ardCap]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- **The round's descriptor.**  Twenty-two regions at `ardCap` of the
carrier cell, the fraternal mark window at *exactly* `N·N` and clear,
and the transitive mark window clear on `[0, N·N)`.  Every clause is a
statement about `σ` alone, read against the arena's own carrier cell —
`Srd` can name neither the arena nor the orientation. -/
def ardSrd (mkF mkT : ℕ → String) (regs : ℕ → List String) (j : ℕ)
    (σ : Env) : Prop :=
  (∀ b ∈ regs j, ardCap (σ.vars (arenaNames j).nN) ≤ (σ.arrs b).length) ∧
    (σ.arrs (mkF j)).length
      = σ.vars (arenaNames j).nN * σ.vars (arenaNames j).nN ∧
    (∀ i, (σ.arrs (mkF j)).getD i 0 = 0) ∧
    (∀ i, i < σ.vars (arenaNames j).nN * σ.vars (arenaNames j).nN →
      (σ.arrs (mkT j)).getD i 0 = 0)

/-- **The round's region conditions**, at one level. -/
structure ArdNames (j : ℕ) (io it fo ft dgF mkF ao aj dgP mt sg tp sk
    ro rt mkT o' t' qo qt ad sd dgE : String) : Prop where
  /-- The fraternal half's own eleven-name condition. -/
  fh : AugRdFhNames (io) (it) (fo) (ft) (dgF) (mkF) (ao) (aj)
    (dgP) (mt) (sg) (tp) (sk)
  /-- The transitive pass's own five-name condition. -/
  tr : TrNames (io) (it) (ro) (rt) (mkT)
  /-- The emit's own fifteen-name condition. -/
  em : EmNames (io) (it) (ro) (rt) (mkT) (fo) (ft) (sg)
    (o') (t') (qo) (qt) (ad) (sd) (dgE)
  /-- The body's cross-stage separation. -/
  sep : AugRdSep (fo) (ft) (dgF) (mkF) (ao) (aj) (dgP) (mt)
    (sg) (tp) (sk) (ro) (rt) (mkT) (o') (t') (qo) (qt)
    (ad) (sd) (dgE)
  /-- The orientation pair is ordered — the windowing convention. -/
  it_io : it ≠ io
  /-- The copy-back's own four-name condition. -/
  cp : ArdCpNames (o') (t') (io) (it)
  /-- The fraternal mark window is none of the other twenty. -/
  mkF_alloc : mkF ∉ augRdAllocs (fo) (ft) (dgF) (ao) (aj) (dgP)
    (mt) (sg) (tp) (sk) (ro) (rt) (mkT) (o') (t') (qo)
    (qt) (ad) (sd) (dgE)
  /-- The orientation offsets are none of the twenty-one the body writes. -/
  io_wr : io ≠ mkF ∧ io ∉ augRdAllocs (fo) (ft) (dgF) (ao)
    (aj) (dgP) (mt) (sg) (tp) (sk) (ro) (rt) (mkT) (o')
    (t') (qo) (qt) (ad) (sd) (dgE)
  /-- … nor are the orientation targets. -/
  it_wr : it ≠ mkF ∧ it ∉ augRdAllocs (fo) (ft) (dgF) (ao)
    (aj) (dgP) (mt) (sg) (tp) (sk) (ro) (rt) (mkT) (o')
    (t') (qo) (qt) (ad) (sd) (dgE)
  /-- The arena's five arrays are none of the round's twenty-four. -/
  arn : ∀ b, b = (arenaNames j).off ∨ b = (arenaNames j).tgt ∨
    b = (arenaNames j).col ∨ b = (arenaNames j).up ∨ b = (arenaNames j).hist →
    b ≠ mkF ∧ b ∉ augRdAllocs (fo) (ft) (dgF) (ao) (aj) (dgP)
      (mt) (sg) (tp) (sk) (ro) (rt) (mkT) (o') (t') (qo)
      (qt) (ad) (sd) (dgE) ∧ b ≠ io ∧ b ≠ it

/-- **The round's cell conditions**: six named cells, outside all seven
scratch pools and pairwise distinct. -/
structure ArdCells (j : ℕ) (nF nT nO nA : String) : Prop where
  /-- … -/
  nN : (arenaNames j).nN ∉ ardScalars
  /-- … -/
  nS : (arenaNames j).nS ∉ ardScalars
  /-- … -/
  cF : nF ∉ ardScalars
  /-- … -/
  cT : nT ∉ ardScalars
  /-- … -/
  cO : nO ∉ ardScalars
  /-- … -/
  cA : nA ∉ ardScalars
  /-- … -/
  nodup : [(arenaNames j).nN, (arenaNames j).nS, nF, nT, nO, nA].Nodup

/-- **The round.**  Three carrier sweeps, the body, the re-zero, the
copy-back. -/
def ardRoundCom (nN nF nT nO nA io it fo ft dgF mkF ao aj dgP mt sg tp sk
    ro rt mkT o' t' qo qt ad sd dgE : String) : Com :=
  .seq (frZeroCom nN ad)
    (.seq (frZeroCom nN sd)
      (.seq (frZeroCom nN dgE)
        (.seq (augRdBody nN nF nT nO io it fo ft dgF mkF ao aj dgP mt sg tp sk
                ro rt mkT o' t' qo qt ad sd dgE)
          (.seq (ardClearCom nN ro rt mkT)
            (ardCopyCom nN nO nA o' t' io it)))))

theorem ard_not_mem_warrs_frZero {nN dg b : String} (h : b ≠ dg) :
    b ∉ (frZeroCom nN dg).warrs := by
  simp [frZeroCom, Csr.scan, Com.warrs, h]

theorem ard_not_mem_wvars_frZero {nN dg y : String} (h : y ∉ frScalars) :
    y ∉ (frZeroCom nN dg).wvars := by
  obtain ⟨-, -, -, -, -, -, -, -, hv, -, -, -⟩ := augRd_frScalars_ne h
  simp [frZeroCom, Csr.scan, Com.wvars, hv]

/-- The emit's three zeroed regions are pairwise distinct. -/
theorem ard_emWr_ne {o t ro rt mk fo ft sg o' t' qo qt ad sd dg : String}
    (h : EmNames o t ro rt mk fo ft sg o' t' qo qt ad sd dg) :
    ad ≠ sd ∧ ad ≠ dg ∧ sd ≠ dg := by
  have hnd := h.wrNd
  simp only [emWr, List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    not_or, List.nodup_nil, and_true] at hnd
  tauto


open Classical in
/-- **`AugRoundIn`, discharged.**  At the windowed orientation region
`augStInNW` (the one `augBaseOrientIn_orCom` produces and
`augSymCsrIn_symComW` consumes), the descriptor `ardSrd`, the program
`ardRoundCom` and the coefficients `1025, 455, 588, 305, 287`.

The selection is pinned to `bucketSel`, for the reason
`SolveAugRoundSeams`'s header gives: `fratPeelAt_fratPeelCom` delivers
`selRank (bucketSel n) (fratGraph D)` and `selRank` genuinely depends on
the tie-break.  `SolveAugBaseFrame` §2 pins `AugBasePeelIn` at the same
selection, and `covAugAdjSelIn_of_base_rounds_sym` is stated at an
arbitrary one, so the three residuals still compose.

The **one** hypothesis that is not a name condition or a frame is
`ArdWord` (§4): the round's five figures are words.  §4 reduces it to
`q ≥ 3·K + 2` for any `K` bounding the chain's squared in-degree by
`K·(N + 1)`, and that is F7-c's to choose. -/
theorem augRoundIn_ardRoundCom (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (R : ℕ) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String)
    (nF nT nO nA io it fo ft dgF mkF ao aj dgP mt sg tp sk
      ro rt mkT o' t' qo qt ad sd dgE : ℕ → String)
    (Smp Ssw : ℕ → Env → Prop)
    (hword : ArdWord C hC φ (fun m => bucketSel m) R G c w q Adm)
    (hnm : ∀ j, ArdNames j (io j) (it j) (fo j) (ft j) (dgF j) (mkF j) (ao j)
      (aj j) (dgP j) (mt j) (sg j) (tp j) (sk j) (ro j) (rt j) (mkT j) (o' j)
      (t' j) (qo j) (qt j) (ad j) (sd j) (dgE j))
    (hcell : ∀ j, ArdCells j (nF j) (nT j) (nO j) (nA j))
    (hSmp : ∀ (j : ℕ) (σ σ' : Env), Smp j σ →
      (∀ b, b ≠ mkF j →
        b ∉ augRdAllocs (fo j) (ft j) (dgF j) (ao j) (aj j) (dgP j) (mt j)
          (sg j) (tp j) (sk j) (ro j) (rt j) (mkT j) (o' j) (t' j) (qo j)
          (qt j) (ad j) (sd j) (dgE j) →
        b ≠ io j → b ≠ it j → σ'.arrs b = σ.arrs b) →
      (∀ y, y ∉ ardScalars → y ≠ nF j → y ≠ nT j → y ≠ nO j → y ≠ nA j →
        σ'.vars y = σ.vars y) → Smp j σ')
    (hSsw : ∀ (j : ℕ) (σ σ' : Env), Ssw j σ →
      (∀ b, b ≠ mkF j →
        b ∉ augRdAllocs (fo j) (ft j) (dgF j) (ao j) (aj j) (dgP j) (mt j)
          (sg j) (tp j) (sk j) (ro j) (rt j) (mkT j) (o' j) (t' j) (qo j)
          (qt j) (ad j) (sd j) (dgE j) →
        b ≠ io j → b ≠ it j → σ'.arrs b = σ.arrs b) →
      (∀ y, y ∉ ardScalars → y ≠ nF j → y ≠ nT j → y ≠ nO j → y ≠ nA j →
        σ'.vars y = σ.vars y) → Ssw j σ') :
    AugRoundIn C hC φ (fun m => bucketSel m) R G c w q ℓp htabF hbf Adm ca co
      (fun j A => augStInNW io it nA j A)
      (ardSrd mkF mkT (ardRegions io it fo ft dgF ao aj dgP mt sg tp sk
        ro rt mkT o' t' qo qt ad sd dgE))
      Smp Ssw
      (fun j => ardRoundCom (arenaNames j).nN (nF j) (nT j) (nO j) (nA j)
        (io j) (it j) (fo j) (ft j) (dgF j) (mkF j) (ao j) (aj j) (dgP j)
        (mt j) (sg j) (tp j) (sk j) (ro j) (rt j) (mkT j) (o' j) (t' j)
        (qo j) (qt j) (ad j) (sd j) (dgE j))
      1025 455 588 305 287 := by
  intro x hx j hj A hAdm hbot i hi
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hArena, hst, hSrdσ, hcaL, hcoL, hSm, hSw⟩ := hσ
  have nm := hnm j
  have cl := hcell j
  obtain ⟨p1, p2, p3, p4, p5, p6, p7⟩ := ard_notMem_pools cl.nN
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := ard_notMem_pools cl.nS
  obtain ⟨g1, g2, g3, g4, g5, g6, g7⟩ := ard_notMem_pools cl.cF
  obtain ⟨u1, u2, u3, u4, u5, u6, u7⟩ := ard_notMem_pools cl.cT
  obtain ⟨v1, v2, v3, v4, v5, v6, v7⟩ := ard_notMem_pools cl.cO
  obtain ⟨w1, w2, w3, w4, w5, w6, w7⟩ := ard_notMem_pools cl.cA
  have hnd := cl.nodup
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at hnd
  obtain ⟨⟨d1, d2, d3, d4, d5⟩, ⟨d6, d7, d8, d9⟩, ⟨d10, d11, d12⟩,
    ⟨d13, d14⟩, d15, -⟩ := hnd
  obtain ⟨e1, e2, e3⟩ := ard_emWr_ne nm.em
  obtain ⟨k1, k2⟩ := nm.io_wr
  obtain ⟨l1, l2⟩ := nm.it_wr
  simp only [augRdAllocs, List.mem_cons, List.not_mem_nil, or_false, not_or]
    at k2 l2
  obtain ⟨k21, k22, k23, k24, k25, k26, k27, k28, k29, k210, k211, k212, k213,
    k214, k215, k216, k217, k218, k219, k220⟩ := k2
  obtain ⟨l21, l22, l23, l24, l25, l26, l27, l28, l29, l210, l211, l212, l213,
    l214, l215, l216, l217, l218, l219, l220⟩ := l2
  have hmkFal := nm.mkF_alloc
  simp only [augRdAllocs, List.mem_cons, List.not_mem_nil, or_false, not_or]
    at hmkFal
  obtain ⟨m1, m2, m3, m4, m5, m6, m7, m8, m9, m10, m11, m12, m13, m14, m15,
    m16, m17, m18, m19, m20⟩ := hmkFal
  -- `mkT` against the three zeroed regions, off the emit's read/write split
  have hmkTad : ad j ≠ mkT j :=
    nm.em.wrRd (ad j) (by simp [emWr]) (mkT j) (by simp [emRd])
  have hmkTsd : sd j ≠ mkT j :=
    nm.em.wrRd (sd j) (by simp [emWr]) (mkT j) (by simp [emRd])
  have hmkTdg : dgE j ≠ mkT j :=
    nm.em.wrRd (dgE j) (by simp [emWr]) (mkT j) (by simp [emRd])
  have ho'mkT : o' j ≠ mkT j :=
    nm.em.wrRd (o' j) (by simp [emWr]) (mkT j) (by simp [emRd])
  have ht'mkT : t' j ≠ mkT j :=
    nm.em.wrRd (t' j) (by simp [emWr]) (mkT j) (by simp [emRd])
  -- the figures
  obtain ⟨D, hD⟩ : ∃ D, selChain (bucketSel A.N) A.G i = D := ⟨_, rfl⟩
  have hnv : σ.vars (arenaNames j).nN = A.N := hArena.n_eq
  obtain ⟨hTrE, -, hnAv⟩ := hst
  rw [hD] at hTrE hnAv
  obtain ⟨off, tgt, hcsr⟩ := hTrE
  have hB := hword x hx j hj A hAdm hbot i hi
  rw [hD] at hB
  obtain ⟨hregL, hmkFlen, hmkF0, hmkT0⟩ := hSrdσ
  rw [hnv] at hregL hmkFlen hmkT0
  have hcap := ardCap_bounds D
  have hAl : ∀ b ∈ ardRegions io it fo ft dgF ao aj dgP mt sg tp sk
      ro rt mkT o' t' qo qt ad sd dgE j, ardCap A.N ≤ (σ.arrs b).length := hregL
  have hNcap : A.N ≤ ardCap A.N := by simp only [ardCap]; omega
  have hNB : A.N < mcB q x := by omega
  have hadL : A.N ≤ (σ.arrs (ad j)).length :=
    le_trans hNcap (hAl (ad j) (by simp [ardRegions, augRdAllocs]))
  have hsdL : A.N ≤ (σ.arrs (sd j)).length :=
    le_trans hNcap (hAl (sd j) (by simp [ardRegions, augRdAllocs]))
  have hdgEL : A.N ≤ (σ.arrs (dgE j)).length :=
    le_trans hNcap (hAl (dgE j) (by simp [ardRegions, augRdAllocs]))
  have hioL : ardCap A.N ≤ (σ.arrs (io j)).length :=
    hAl (io j) (by simp [ardRegions])
  have hitL : ardCap A.N ≤ (σ.arrs (it j)).length :=
    hAl (it j) (by simp [ardRegions])
  -- ### phase 0: the three carrier sweeps
  obtain ⟨τ1, hr1, ⟨hnv1, -, hz1⟩, hfv1, hfa1, -, -⟩ :=
    ((frZero_spec (B := mcB q x) (nN := (arenaNames j).nN) (dg := ad j)
      (n := A.N) p1 hNB).frame).run
      ⟨hnv, hadL⟩
  have hlen1 := run_arrs_length_eq hr1
  have hfa1' : ∀ b, b ≠ ad j → τ1.arrs b = σ.arrs b :=
    fun b h => hfa1 b (ard_not_mem_warrs_frZero h)
  obtain ⟨τ2, hr2, ⟨hnv2, -, hz2⟩, hfv2, hfa2, -, -⟩ :=
    ((frZero_spec (B := mcB q x) (nN := (arenaNames j).nN) (dg := sd j)
      (n := A.N) p1 hNB).frame).run
      ⟨hnv1, by rw [hlen1 (sd j)]; exact hsdL⟩
  have hlen2 := run_arrs_length_eq hr2
  have hfa2' : ∀ b, b ≠ sd j → τ2.arrs b = τ1.arrs b :=
    fun b h => hfa2 b (ard_not_mem_warrs_frZero h)
  obtain ⟨τ3, hr3, ⟨hnv3, -, hz3⟩, hfv3, hfa3, -, -⟩ :=
    ((frZero_spec (B := mcB q x) (nN := (arenaNames j).nN) (dg := dgE j)
      (n := A.N) p1 hNB).frame).run
      ⟨hnv2, by rw [hlen2 (dgE j), hlen1 (dgE j)]; exact hdgEL⟩
  have hlen3 := run_arrs_length_eq hr3
  have hfa3' : ∀ b, b ≠ dgE j → τ3.arrs b = τ2.arrs b :=
    fun b h => hfa3 b (ard_not_mem_warrs_frZero h)
  have hlenZ : ∀ b, (τ3.arrs b).length = (σ.arrs b).length := by
    intro b; rw [hlen3 b, hlen2 b, hlen1 b]
  have hfaZ : ∀ b, b ≠ ad j → b ≠ sd j → b ≠ dgE j → τ3.arrs b = σ.arrs b := by
    intro b h1 h2 h3; rw [hfa3' b h3, hfa2' b h2, hfa1' b h1]
  have hfvZ : ∀ y, y ∉ frScalars → τ3.vars y = σ.vars y := by
    intro y hy
    rw [hfv3 y (ard_not_mem_wvars_frZero hy), hfv2 y (ard_not_mem_wvars_frZero hy),
      hfv1 y (ard_not_mem_wvars_frZero hy)]
  have hzad : ∀ k, k < A.N → (τ3.arrs (ad j)).getD k 0 = 0 := by
    rw [hfa3' (ad j) e2, hfa2' (ad j) e1]; exact hz1
  have hzsd : ∀ k, k < A.N → (τ3.arrs (sd j)).getD k 0 = 0 := by
    rw [hfa3' (sd j) e3]; exact hz2
  have hAlZ : ∀ b ∈ ardRegions io it fo ft dgF ao aj dgP mt sg tp sk
      ro rt mkT o' t' qo qt ad sd dgE j, ardCap A.N ≤ (τ3.arrs b).length := by
    intro b hb; rw [hlenZ b]; exact hAl b hb
  -- ### phase 1: the round's body
  obtain ⟨ρ, hrB, ⟨off', tgt', hcsr'⟩, hnO, hmkFl', hmkF0', ⟨ttF, htr'⟩, hnvB,
    hlenB, hfvB, hfaB⟩ :=
    (augRdBody_spec (B := mcB q x) nm.fh nm.tr nm.em nm.sep nm.it_io p1 g1
      (Ne.symm d2) ⟨p2, g2⟩ p3 g3 d3 d10 p4 p5 d4 D off tgt).run
      ⟨augRd_trInCsr_of_eq hcsr (hfaZ (io j) k218 k219 k220)
         (hfaZ (it j) l218 l219 l220),
       by rw [hfvZ _ p1]; exact hnv,
       by omega, by omega,
       le_trans (by simp only [ardCap]; omega)
         (hAlZ (fo j) (by simp [ardRegions, augRdAllocs])),
       le_trans hcap.2.2.2.2.1 (hAlZ (ft j) (by simp [ardRegions, augRdAllocs])),
       le_trans hNcap (hAlZ (dgF j) (by simp [ardRegions, augRdAllocs])),
       by rw [hfaZ (mkF j) m18 m19 m20]; exact hmkFlen,
       by rw [hfaZ (mkF j) m18 m19 m20]; exact hmkF0,
       le_trans (by simp only [ardCap]; omega)
         (hAlZ (ao j) (by simp [ardRegions, augRdAllocs])),
       le_trans hcap.2.2.2.2.1 (hAlZ (aj j) (by simp [ardRegions, augRdAllocs])),
       le_trans hNcap (hAlZ (dgP j) (by simp [ardRegions, augRdAllocs])),
       le_trans hcap.2.2.2.2.1 (hAlZ (mt j) (by simp [ardRegions, augRdAllocs])),
       le_trans hNcap (hAlZ (sg j) (by simp [ardRegions, augRdAllocs])),
       le_trans hNcap (hAlZ (tp j) (by simp [ardRegions, augRdAllocs])),
       le_trans hcap.2.2.1 (hAlZ (sk j) (by simp [ardRegions, augRdAllocs])),
       le_trans (by simp only [ardCap]; omega)
         (hAlZ (ro j) (by simp [ardRegions, augRdAllocs])),
       le_trans hcap.2.2.2.2.2.1
         (hAlZ (rt j) (by simp [ardRegions, augRdAllocs])),
       le_trans hcap.2.1 (hAlZ (mkT j) (by simp [ardRegions, augRdAllocs])),
       by rw [hfaZ (mkT j) (Ne.symm hmkTad) (Ne.symm hmkTsd) (Ne.symm hmkTdg)];
          exact hmkT0,
       le_trans (by simp only [ardCap]; omega)
         (hAlZ (o' j) (by simp [ardRegions, augRdAllocs])),
       le_trans hcap.2.2.2.2.2.2 (hAlZ (t' j) (by simp [ardRegions, augRdAllocs])),
       le_trans (by simp only [ardCap]; omega)
         (hAlZ (qo j) (by simp [ardRegions, augRdAllocs])),
       le_trans hcap.2.2.2.1 (hAlZ (qt j) (by simp [ardRegions, augRdAllocs])),
       le_trans hNcap (hAlZ (ad j) (by simp [ardRegions, augRdAllocs])),
       le_trans hNcap (hAlZ (sd j) (by simp [ardRegions, augRdAllocs])),
       le_trans hNcap (hAlZ (dgE j) (by simp [ardRegions, augRdAllocs])),
       hzad, hzsd, hz3⟩
  obtain ⟨DD, hDD⟩ :
      ∃ DD, greedyStep (selRank (bucketSel A.N) (fratGraph D)) D = DD := ⟨_, rfl⟩
  rw [hDD] at hcsr' hnO
  have hDDle : arcCount DD ≤ arcCount D + fratPairCount D + transPairCount D := by
    rw [← hDD]; exact arcCount_greedyStep_le D _
  have hioF : A.N + 1 ≤ (σ.arrs (io j)).length := by
    refine le_trans ?_ hioL; simp only [ardCap]; omega
  have hitF : arcCount DD ≤ (σ.arrs (it j)).length := by
    refine le_trans ?_ hitL
    have := hcap.2.2.2.2.2.2
    omega
  -- ### phase 2: the transitive matrix's re-zero
  obtain ⟨ρ2, hrC, hmkTz, hlenC, hfvC, hfaC⟩ :=
    (ardClear_spec (B := mcB q x) (Ne.symm nm.tr.ro_mk) (Ne.symm nm.tr.rt_mk) p6
      D ttF).run ⟨htr', hnvB, by omega⟩
  -- ### phase 3: the copy-back
  obtain ⟨σ', hrD, hcsrF, hnAF, hlenD, hfvD, hfaD⟩ :=
    (ardCopy_spec (B := mcB q x) nm.cp
      ⟨p7, v7, w7, Ne.symm d5, Ne.symm d15⟩ DD off' tgt').run
      ⟨augRd_trInCsr_of_eq hcsr' (hfaC (o' j) ho'mkT) (hfaC (t' j) ht'mkT),
       by rw [hfvC _ p6]; exact hnvB,
       by rw [hfvC _ v6]; exact hnO,
       by omega,
       by rw [hlenC (io j), hlenB (io j), hlenZ (io j)]; exact hioF,
       by rw [hlenC (it j), hlenB (it j), hlenZ (it j)]; exact hitF⟩
  -- ### the whole run, and its frames
  have hrun : Run (mcB q x)
      (ardRoundCom (arenaNames j).nN (nF j) (nT j) (nO j) (nA j) (io j) (it j)
        (fo j) (ft j) (dgF j) (mkF j) (ao j) (aj j) (dgP j) (mt j) (sg j)
        (tp j) (sk j) (ro j) (rt j) (mkT j) (o' j) (t' j) (qo j) (qt j)
        (ad j) (sd j) (dgE j)) σ σ' _ :=
    hr1.seq (hr2.seq (hr3.seq (hrB.seq (hrC.seq hrD))))
  have hlenF : ∀ b, (σ'.arrs b).length = (σ.arrs b).length := by
    intro b; rw [hlenD b, hlenC b, hlenB b, hlenZ b]
  have hvarF : ∀ y, y ∉ ardScalars → y ≠ nF j → y ≠ nT j → y ≠ nO j →
      y ≠ nA j → σ'.vars y = σ.vars y := by
    intro y hy y1 y2 y3 y4
    obtain ⟨q1, q2, q3, q4, q5, q6, q7⟩ := ard_notMem_pools hy
    rw [hfvD y q7 y4, hfvC y q6, hfvB y q1 q2 q3 q4 q5 y1 y2 y3, hfvZ y q1]
  have harrF : ∀ b, b ≠ mkF j →
      b ∉ augRdAllocs (fo j) (ft j) (dgF j) (ao j) (aj j) (dgP j) (mt j)
        (sg j) (tp j) (sk j) (ro j) (rt j) (mkT j) (o' j) (t' j) (qo j)
        (qt j) (ad j) (sd j) (dgE j) →
      b ≠ io j → b ≠ it j → σ'.arrs b = σ.arrs b := by
    intro b hb1 hb2 hb3 hb4
    have hb2' := hb2
    simp only [augRdAllocs, List.mem_cons, List.not_mem_nil, or_false, not_or]
      at hb2'
    rw [hfaD b hb3 hb4, hfaC b hb2'.2.2.2.2.2.2.2.2.2.2.2.2.1,
      hfaB b hb1 hb2, hfaZ b hb2'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        hb2'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
        hb2'.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2]
  -- the arena survives
  have hvN : σ'.vars (arenaNames j).nN = σ.vars (arenaNames j).nN :=
    hvarF _ cl.nN d2 d3 d4 d5
  have hvS : σ'.vars (arenaNames j).nS = σ.vars (arenaNames j).nS :=
    hvarF _ cl.nS d6 d7 d8 d9
  have harn : ∀ b, b = (arenaNames j).off ∨ b = (arenaNames j).tgt ∨
      b = (arenaNames j).col ∨ b = (arenaNames j).up ∨ b = (arenaNames j).hist →
      σ'.arrs b = σ.arrs b := by
    intro b hb
    obtain ⟨c1, c2, c3, c4⟩ := nm.arn b hb
    exact harrF b c1 c2 c3 c4
  -- the fraternal mark window survives the last two passes
  have hmkFF : σ'.arrs (mkF j) = ρ.arrs (mkF j) := by
    rw [hfaD (mkF j) (Ne.symm k1) (Ne.symm l1), hfaC (mkF j) m13]
  have hmkTF : σ'.arrs (mkT j) = ρ2.arrs (mkT j) :=
    hfaD (mkT j) (Ne.symm k213) (Ne.symm l213)
  refine ⟨σ', _, hrun, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- the budget: `augRdRoundK` term for term, with the copy's figure
    -- converted by `arcCount_greedyStep_le` and nothing else estimated
    rw [hD]
    simp only [augRdBodyK, augRdFratHalfK, fratKStd, fratK, fratPeelK, trK, emK,
      ardClearK, ardCopyK, augRoundBudget]
    omega
  · -- the arena
    exact arenaStW_of_eq hArena hvN hvS (harn _ (Or.inl rfl))
      (harn _ (Or.inr (Or.inl rfl))) (harn _ (Or.inr (Or.inr (Or.inl rfl))))
      (harn _ (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      (harn _ (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
  · -- the next orientation, in the round's own region
    show augStInNW io it nA j A _ σ'
    rw [hD, hDD]
    exact augStInNW_of_trInCsr nm.it_io hcsrF hnAF
  · -- the descriptor
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro b hb
      rw [hvN, hnv, hlenF b]
      exact hAl b hb
    · rw [hvN, hnv, hmkFF]; exact hmkFl'
    · rw [hmkFF]; exact hmkF0'
    · rw [hvN, hnv, hmkTF]; exact hmkTz
  · rw [hlenF (ca j)]; exact hcaL
  · rw [hlenF (co j)]; exact hcoL
  · exact hSmp j σ σ' hSm harrF hvarF
  · exact hSsw j σ σ' hSw harrF hvarF

/-! ## §6 Nothing above is vacuous

Three things are exhibited.

1. **The name and cell bundles are satisfiable** — twenty-three region
   names and four figure cells, at concrete strings, with every
   disequality the round's six passes ask for.  The arena's own
   `lv`-indexed names are kept apart from all of them by their first
   character (`ard_lv_ne_head`), which is what `lv_ne_fixed` cannot do
   for the emit's five-character `"em.v1"`.
2. **`ardSrd` is inhabited jointly with the rest of the precondition**
   (`exists_ardSrd`, `exists_ardRoundPre`): from any state carrying the
   arena and the orientation region, reallocating the twenty-one
   regions the round *writes* gives one satisfying `AugRoundIn`'s
   precondition entire.  The orientation pair is deliberately **not**
   reallocated — that would destroy the region — so its `ardCap`
   allocation is a hypothesis, and that is a real requirement on
   whoever writes the orientation (the base pass's `Sbd`), recorded
   here rather than hidden.
3. **`Smp` and `Ssw` need no witness of their own**: both hypotheses are
   frame-shaped, so `fun _ _ => True` satisfies them.
-/

/-- **A level-indexed name never equals a fixed one whose first letter
differs.**  `lv s j` is `s` with `j` copies of `'z'` pushed on, so its
first character is `s`'s; this is the only comparison lemma that
survives a length mismatch, which the emit's `"em.v1"` forces. -/
theorem ard_lv_ne_head {s b : String} {ch : Char} (hs : s.toList.head? = some ch)
    (hb : b.toList.head? ≠ some ch) (j : ℕ) : lv s j ≠ b := by
  intro hcon
  apply hb
  have hl : (lv s j).toList = b.toList := by rw [hcon]
  rw [lv_toList] at hl
  rw [← hl]
  cases hh : s.toList with
  | nil => rw [hh] at hs; simp at hs
  | cons a l =>
      rw [hh] at hs
      simp only [List.cons_append, List.head?_cons]
      simpa using hs

/-- The same against a whole list of fixed names. -/
theorem ard_lv_notMem {s : String} {ch : Char} (hs : s.toList.head? = some ch)
    {L : List String} (hL : ∀ b ∈ L, b.toList.head? ≠ some ch) (j : ℕ) :
    lv s j ∉ L := fun hmem => ard_lv_ne_head hs (hL _ hmem) j rfl

theorem ard_arenaNames_nN_head (j : ℕ) :
    (arenaNames j).nN = lv "sv.n" j := rfl

theorem ard_arenaNames_nS_head (j : ℕ) :
    (arenaNames j).nS = lv "sv.m" j := rfl

/-- **Every scratch scalar of every one of the round's six passes starts
with a letter other than `'s'`**, and the arena's two figure cells are
`lv "sv.n"` and `lv "sv.m"` — so neither is ever captured. -/
theorem ard_ardScalars_head : ∀ b ∈ ardScalars, b.toList.head? ≠ some 's' := by
  decide

theorem ard_nN_notMem_ardScalars (j : ℕ) : (arenaNames j).nN ∉ ardScalars :=
  ard_lv_notMem (s := "sv.n") rfl ard_ardScalars_head j

theorem ard_nS_notMem_ardScalars (j : ℕ) : (arenaNames j).nS ∉ ardScalars :=
  ard_lv_notMem (s := "sv.m") rfl ard_ardScalars_head j

/-! ### The concrete names

Twenty-seven fixed four-character strings on the base letter `'r'`, so
that every disequality among them is `decide` and every disequality
against the arena's `lv "s…"` names is `ard_lv_ne_head`. -/

/-- The orientation offsets. -/
abbrev ardIo : ℕ → String := fun _ => "ri.o"
/-- The orientation targets. -/
abbrev ardIt : ℕ → String := fun _ => "ri.t"
/-- The fraternity CSR's offsets. -/
abbrev ardFo : ℕ → String := fun _ => "rf.o"
/-- The fraternity CSR's targets. -/
abbrev ardFt : ℕ → String := fun _ => "rf.t"
/-- The fraternal CSR pass's degree region. -/
abbrev ardDgF : ℕ → String := fun _ => "rf.d"
/-- The fraternal mark matrix. -/
abbrev ardMkF : ℕ → String := fun _ => "rf.m"
/-- The peel's adjacency offsets. -/
abbrev ardAo : ℕ → String := fun _ => "rp.o"
/-- The peel's adjacency targets. -/
abbrev ardAj : ℕ → String := fun _ => "rp.j"
/-- The peel's degrees. -/
abbrev ardDgP : ℕ → String := fun _ => "rp.d"
/-- The peel's mates. -/
abbrev ardMt : ℕ → String := fun _ => "rp.m"
/-- The rank array. -/
abbrev ardSg : ℕ → String := fun _ => "rp.s"
/-- The peel's bucket heads. -/
abbrev ardTp : ℕ → String := fun _ => "rp.p"
/-- The peel's cell block. -/
abbrev ardSk : ℕ → String := fun _ => "rp.k"
/-- The transitive CSR's offsets. -/
abbrev ardRo : ℕ → String := fun _ => "rt.o"
/-- The transitive CSR's targets. -/
abbrev ardRt : ℕ → String := fun _ => "rt.t"
/-- The transitive mark matrix. -/
abbrev ardMkT : ℕ → String := fun _ => "rt.m"
/-- The emit's output offsets. -/
abbrev ardOo : ℕ → String := fun _ => "ro.o"
/-- The emit's output targets. -/
abbrev ardOt : ℕ → String := fun _ => "ro.t"
/-- The transpose's offsets. -/
abbrev ardQo : ℕ → String := fun _ => "rq.o"
/-- The transpose's targets. -/
abbrev ardQt : ℕ → String := fun _ => "rq.t"
/-- The emit's input stamp. -/
abbrev ardAd : ℕ → String := fun _ => "rz.a"
/-- The emit's fraternal stamp. -/
abbrev ardSd : ℕ → String := fun _ => "rz.s"
/-- The emit's transitive stamp. -/
abbrev ardDgE : ℕ → String := fun _ => "rz.d"
/-- The fraternity CSR's slot-count cell. -/
abbrev ardNF : ℕ → String := fun _ => "rc.f"
/-- The transitive enumeration's slot-count cell. -/
abbrev ardNT : ℕ → String := fun _ => "rc.t"
/-- The emit's output-count cell. -/
abbrev ardNO : ℕ → String := fun _ => "rc.o"
/-- The orientation region's arc-count cell. -/
abbrev ardNA : ℕ → String := fun _ => "rc.a"

/-- The twenty-three region names, as one list — the shape `arn` and
the inhabitation lemma consume. -/
abbrev ardAllocsStd : List String :=
  augRdAllocs "rf.o" "rf.t" "rf.d" "rp.o" "rp.j" "rp.d" "rp.m" "rp.s" "rp.p"
    "rp.k" "rt.o" "rt.t" "rt.m" "ro.o" "ro.t" "rq.o" "rq.t" "rz.a" "rz.s" "rz.d"

/-- Every one of the round's twenty-three regions starts with `'r'`, so
none is an arena array. -/
theorem ard_regions_head :
    ∀ b ∈ "rf.m" :: "ri.o" :: "ri.t" :: ardAllocsStd,
      b.toList.head? ≠ some 's' := by decide

/-- **The round's region conditions, at the concrete names.** -/
theorem ardNames_std (j : ℕ) :
    ArdNames j "ri.o" "ri.t" "rf.o" "rf.t" "rf.d" "rf.m" "rp.o" "rp.j" "rp.d"
      "rp.m" "rp.s" "rp.p" "rp.k" "rt.o" "rt.t" "rt.m" "ro.o" "ro.t" "rq.o"
      "rq.t" "rz.a" "rz.s" "rz.d" := by
  refine
    { fh := { fr := ⟨by decide, by decide, by decide, by decide, by decide,
                by decide, by decide, by decide, by decide, by decide,
                by decide, by decide, by decide, by decide⟩
              fp := ⟨by decide⟩
              o_wr := by decide
              t_wr := by decide
              mk_wr := by decide
              dgF_wr := by decide }
      tr := ⟨by decide, by decide, by decide, by decide, by decide, by decide,
             by decide, by decide, by decide⟩
      em := { wrRd := by decide, wrNd := by decide, fo_ft := by decide }
      sep := ⟨by decide⟩
      it_io := by decide
      cp := ⟨by decide, by decide, by decide, by decide, by decide⟩
      mkF_alloc := by decide
      io_wr := ⟨by decide, by decide⟩
      it_wr := ⟨by decide, by decide⟩
      arn := ?_ }
  rintro b (rfl | rfl | rfl | rfl | rfl) <;>
    refine ⟨ard_lv_ne_head rfl (by decide) j, ?_,
      ard_lv_ne_head rfl (by decide) j, ard_lv_ne_head rfl (by decide) j⟩ <;>
    exact ard_lv_notMem rfl
      (fun c hc => ard_regions_head c (by simp only [List.mem_cons]; tauto)) j

/-- The fraternal mark window's first letter, as a fixed fact. -/
theorem ard_mkF_head : ("rf.m" : String).toList.head? ≠ some 's' := by decide

/-- **The round's cell conditions, at the concrete names.** -/
theorem ardCells_std (j : ℕ) :
    ArdCells j "rc.f" "rc.t" "rc.o" "rc.a" where
  nN := ard_nN_notMem_ardScalars j
  nS := ard_nS_notMem_ardScalars j
  cF := by decide
  cT := by decide
  cO := by decide
  cA := by decide
  nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
      not_or, List.nodup_nil, and_true]
    refine ⟨⟨lv_ne_of_base_ne (by decide) (by decide) j j,
      ard_lv_ne_head rfl (by decide) j, ard_lv_ne_head rfl (by decide) j,
      ard_lv_ne_head rfl (by decide) j, ard_lv_ne_head rfl (by decide) j⟩,
      ⟨ard_lv_ne_head rfl (by decide) j, ard_lv_ne_head rfl (by decide) j,
       ard_lv_ne_head rfl (by decide) j, ard_lv_ne_head rfl (by decide) j⟩,
      ⟨by decide, by decide, by decide⟩, ⟨by decide, by decide⟩,
      by decide, by decide⟩

/-! ### The descriptor is inhabited jointly with the rest -/

/-- **`ardSrd` is established by allocating the twenty-one regions the
round writes, and nothing else.**  The orientation pair is deliberately
left alone — reallocating it would destroy the very region the round
consumes — so its `ardCap` allocation is a *hypothesis*, and that is a
requirement on whoever writes the orientation into it.

Memory starts zeroed (`Imp.lean:20-44`), so the fraternal window's
all-zero clause and the transitive window's clear-prefix clause come
free with the allocation. -/
theorem exists_ardSrd {io it fo ft dgF mkF ao aj dgP mt sg tp sk ro rt mkT
    o' t' qo qt ad sd dgE : ℕ → String} {j : ℕ}
    (hmk : mkF j ∉ augRdAllocs (fo j) (ft j) (dgF j) (ao j) (aj j) (dgP j) (mt j)
      (sg j) (tp j) (sk j) (ro j) (rt j) (mkT j) (o' j) (t' j) (qo j) (qt j)
      (ad j) (sd j) (dgE j))
    (hio : io j ≠ mkF j ∧ io j ∉ augRdAllocs (fo j) (ft j) (dgF j) (ao j) (aj j) (dgP j) (mt j)
      (sg j) (tp j) (sk j) (ro j) (rt j) (mkT j) (o' j) (t' j) (qo j) (qt j)
      (ad j) (sd j) (dgE j))
    (hit : it j ≠ mkF j ∧ it j ∉ augRdAllocs (fo j) (ft j) (dgF j) (ao j) (aj j) (dgP j) (mt j)
      (sg j) (tp j) (sk j) (ro j) (rt j) (mkT j) (o' j) (t' j) (qo j) (qt j)
      (ad j) (sd j) (dgE j))
    {NN : ℕ} {σ : Env} (hnv : σ.vars (arenaNames j).nN = NN)
    (hioL : ardCap NN ≤ (σ.arrs (io j)).length)
    (hitL : ardCap NN ≤ (σ.arrs (it j)).length) :
    ∃ σ' : Env, σ'.vars = σ.vars ∧
      (∀ b, b ≠ mkF j → b ∉ augRdAllocs (fo j) (ft j) (dgF j) (ao j) (aj j) (dgP j) (mt j)
      (sg j) (tp j) (sk j) (ro j) (rt j) (mkT j) (o' j) (t' j) (qo j) (qt j)
      (ad j) (sd j) (dgE j) → σ'.arrs b = σ.arrs b) ∧
      ardSrd mkF mkT (ardRegions io it fo ft dgF ao aj dgP mt sg tp sk ro rt mkT o' t' qo qt
      ad sd dgE) j σ' := by
  classical
  obtain ⟨L, hL⟩ : ∃ L : List String, L = augRdAllocs (fo j) (ft j) (dgF j) (ao j) (aj j) (dgP j) (mt j)
      (sg j) (tp j) (sk j) (ro j) (rt j) (mkT j) (o' j) (t' j) (qo j) (qt j)
      (ad j) (sd j) (dgE j) := ⟨_, rfl⟩
  rw [← hL] at hmk hio hit
  obtain ⟨F, hF⟩ : ∃ F : String → List ℕ, F = fun b =>
      if b = mkF j then List.replicate (NN * NN) 0
      else if b ∈ L then List.replicate (ardCap NN) 0
      else σ.arrs b := ⟨_, rfl⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : Env, τ = { σ with arrs := F } := ⟨_, rfl⟩
  have hFa : ∀ b, τ.arrs b = F b := fun b => by rw [hτ]
  have hFv : τ.vars = σ.vars := by rw [hτ]
  have hmkFτ : τ.arrs (mkF j) = List.replicate (NN * NN) 0 := by
    rw [hFa, hF]; simp
  have hmem : ∀ b, b ∈ L → τ.arrs b = List.replicate (ardCap NN) 0 := by
    intro b hb
    have hbm : b ≠ mkF j := fun h => hmk (h ▸ hb)
    rw [hFa, hF]; simp [hbm, hb]
  have hout : ∀ b, b ≠ mkF j → b ∉ L → τ.arrs b = σ.arrs b := by
    intro b h1 h2; rw [hFa, hF]; simp [h1, h2]
  have hnvτ : τ.vars (arenaNames j).nN = NN := by rw [hFv]; exact hnv
  refine ⟨τ, hFv, fun b h1 h2 => hout b h1 (by rw [hL]; exact h2), ?_, ?_, ?_, ?_⟩
  · intro b hb
    rw [hnvτ]
    simp only [ardRegions, List.mem_cons] at hb
    rcases hb with rfl | rfl | hb
    · rw [hout _ hio.1 hio.2]; exact hioL
    · rw [hout _ hit.1 hit.2]; exact hitL
    · rw [hmem _ (by rw [hL]; exact hb), List.length_replicate]
  · rw [hnvτ, hmkFτ, List.length_replicate]
  · intro k; rw [hmkFτ]; exact ard_getD_replicate _ _
  · intro k _
    rw [hmem (mkT j) (by rw [hL]; simp [augRdAllocs])]
    exact ard_getD_replicate _ _

/-- **`AugRoundIn`'s precondition is satisfiable in full.**  From any
state carrying the arena, the orientation region and the two spare
allocations, reallocating the round's twenty-one written regions gives
one satisfying every clause: the arena and the region survive because
neither the arena's five arrays nor the orientation pair is among the
twenty-one, and every scalar is the original's. -/
theorem exists_ardRoundPre {io it nA fo ft dgF mkF ao aj dgP mt sg tp sk ro rt
    mkT o' t' qo qt ad sd dgE ca co : ℕ → String} {j : ℕ}
    (hmk : mkF j ∉ augRdAllocs (fo j) (ft j) (dgF j) (ao j) (aj j) (dgP j) (mt j)
      (sg j) (tp j) (sk j) (ro j) (rt j) (mkT j) (o' j) (t' j) (qo j) (qt j)
      (ad j) (sd j) (dgE j))
    (hio : io j ≠ mkF j ∧ io j ∉ augRdAllocs (fo j) (ft j) (dgF j) (ao j) (aj j) (dgP j) (mt j)
      (sg j) (tp j) (sk j) (ro j) (rt j) (mkT j) (o' j) (t' j) (qo j) (qt j)
      (ad j) (sd j) (dgE j))
    (hit : it j ≠ mkF j ∧ it j ∉ augRdAllocs (fo j) (ft j) (dgF j) (ao j) (aj j) (dgP j) (mt j)
      (sg j) (tp j) (sk j) (ro j) (rt j) (mkT j) (o' j) (t' j) (qo j) (qt j)
      (ad j) (sd j) (dgE j))
    (hto : it j ≠ io j)
    (hkeep : ∀ b, b = (arenaNames j).off ∨ b = (arenaNames j).tgt ∨
      b = (arenaNames j).col ∨ b = (arenaNames j).up ∨
      b = (arenaNames j).hist ∨ b = ca j ∨ b = co j →
      b ≠ mkF j ∧ b ∉ augRdAllocs (fo j) (ft j) (dgF j) (ao j) (aj j) (dgP j) (mt j)
      (sg j) (tp j) (sk j) (ro j) (rt j) (mkT j) (o' j) (t' j) (qo j) (qt j)
      (ad j) (sd j) (dgE j))
    {Λ n₀ ℓ hb : ℕ} {A : Arena Λ n₀}
    {tab : Fin A.N → Fin ℓ → List (Fin A.N)} {D : Orientation A.N} {σ : Env}
    (hA : ArenaStW (arenaNames j) hb (Impl.ofArena A tab) σ)
    (hst : augStInNW io it nA j A D σ) (hnv : σ.vars (arenaNames j).nN = A.N)
    (hioL : ardCap A.N ≤ (σ.arrs (io j)).length)
    (hitL : ardCap A.N ≤ (σ.arrs (it j)).length)
    (hcaL : A.N ≤ (σ.arrs (ca j)).length)
    (hcoL : A.N + 1 ≤ (σ.arrs (co j)).length) :
    ∃ σ' : Env, ArenaStW (arenaNames j) hb (Impl.ofArena A tab) σ' ∧
      augStInNW io it nA j A D σ' ∧
      ardSrd mkF mkT (ardRegions io it fo ft dgF ao aj dgP mt sg tp sk ro rt mkT o' t' qo qt
      ad sd dgE) j σ' ∧
      A.N ≤ (σ'.arrs (ca j)).length ∧ A.N + 1 ≤ (σ'.arrs (co j)).length := by
  obtain ⟨σ', hvars, hframe, hsrd⟩ :=
    exists_ardSrd (mkT := mkT) hmk hio hit hnv hioL hitL
  obtain ⟨go1, go2⟩ := hkeep (arenaNames j).off (Or.inl rfl)
  obtain ⟨gt1, gt2⟩ := hkeep (arenaNames j).tgt (Or.inr (Or.inl rfl))
  obtain ⟨gc1, gc2⟩ := hkeep (arenaNames j).col (Or.inr (Or.inr (Or.inl rfl)))
  obtain ⟨gu1, gu2⟩ :=
    hkeep (arenaNames j).up (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  obtain ⟨gh1, gh2⟩ :=
    hkeep (arenaNames j).hist (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  obtain ⟨ga1, ga2⟩ :=
    hkeep (ca j) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  obtain ⟨gb1, gb2⟩ :=
    hkeep (co j) (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))))
  obtain ⟨⟨offD, tgtD, hTr⟩, -, hcell⟩ := hst
  refine ⟨σ', arenaStW_of_eq hA (by rw [hvars]) (by rw [hvars])
      (hframe _ go1 go2) (hframe _ gt1 gt2) (hframe _ gc1 gc2)
      (hframe _ gu1 gu2) (hframe _ gh1 gh2), ?_, hsrd, ?_, ?_⟩
  · refine augStInNW_of_trInCsr hto (augRd_trInCsr_of_eq hTr ?_ ?_) ?_
    · exact hframe _ hio.1 hio.2
    · exact hframe _ hit.1 hit.2
    · rw [hvars]; exact hcell
  · rw [hframe _ ga1 ga2]; exact hcaL
  · rw [hframe _ gb1 gb2]; exact hcoL

/-- **`AugRoundIn`, discharged at the concrete names**, with the two
transported descriptors at `True` — so nothing above is a statement
about an empty precondition.  The only hypothesis left is `ArdWord`. -/
theorem augRoundIn_ardRoundCom_std (C : GraphClass) (hC : NowhereDense C)
    (φ : FO 0) (R : ℕ) {n : ℕ}
    (G : SimpleGraph (Fin n)) (c w q : ℕ) (ℓp : ℕ → ℕ)
    (htabF : (j : ℕ) →
      (A : Arena ((Headline.headlineSetup C hC φ).pal j) n) →
      Fin A.N → Fin (ℓp j) → List (Fin A.N))
    (hbf : ℕ → ℕ)
    (Adm : (j : ℕ) → Arena ((Headline.headlineSetup C hC φ).pal j) n → Prop)
    (ca co : ℕ → String)
    (hword : ArdWord C hC φ (fun m => bucketSel m) R G c w q Adm) :
    AugRoundIn C hC φ (fun m => bucketSel m) R G c w q ℓp htabF hbf Adm ca co
      (fun j A => augStInNW ardIo ardIt ardNA j A)
      (ardSrd ardMkF ardMkT (ardRegions ardIo ardIt ardFo ardFt ardDgF ardAo
        ardAj ardDgP ardMt ardSg ardTp ardSk ardRo ardRt ardMkT ardOo ardOt
        ardQo ardQt ardAd ardSd ardDgE))
      (fun _ _ => True) (fun _ _ => True)
      (fun j => ardRoundCom (arenaNames j).nN (ardNF j) (ardNT j) (ardNO j)
        (ardNA j) (ardIo j) (ardIt j) (ardFo j) (ardFt j) (ardDgF j)
        (ardMkF j) (ardAo j) (ardAj j) (ardDgP j) (ardMt j) (ardSg j)
        (ardTp j) (ardSk j) (ardRo j) (ardRt j) (ardMkT j) (ardOo j)
        (ardOt j) (ardQo j) (ardQt j) (ardAd j) (ardSd j) (ardDgE j))
      1025 455 588 305 287 :=
  augRoundIn_ardRoundCom C hC φ R G c w q ℓp htabF hbf Adm ca co
    ardNF ardNT ardNO ardNA ardIo ardIt ardFo ardFt ardDgF ardMkF ardAo ardAj
    ardDgP ardMt ardSg ardTp ardSk ardRo ardRt ardMkT ardOo ardOt ardQo ardQt
    ardAd ardSd ardDgE _ _ hword ardNames_std ardCells_std
    (fun _ _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial)

/-- **The precondition of the concrete discharge is inhabited in full.**
Given a state with the arena, the orientation region and the two spare
allocations, the round's descriptor is one reallocation away — so
`augRoundIn_ardRoundCom_std` quantifies over a nonempty set of states
whenever an arena state carrying the orientation exists at all. -/
theorem exists_ardRoundPre_std {ca co : ℕ → String} {j : ℕ}
    (hca : ca j ≠ ardMkF j ∧ ca j ∉ augRdAllocs (ardFo j) (ardFt j) (ardDgF j)
      (ardAo j) (ardAj j) (ardDgP j) (ardMt j) (ardSg j) (ardTp j) (ardSk j)
      (ardRo j) (ardRt j) (ardMkT j) (ardOo j) (ardOt j) (ardQo j) (ardQt j)
      (ardAd j) (ardSd j) (ardDgE j))
    (hco : co j ≠ ardMkF j ∧ co j ∉ augRdAllocs (ardFo j) (ardFt j) (ardDgF j)
      (ardAo j) (ardAj j) (ardDgP j) (ardMt j) (ardSg j) (ardTp j) (ardSk j)
      (ardRo j) (ardRt j) (ardMkT j) (ardOo j) (ardOt j) (ardQo j) (ardQt j)
      (ardAd j) (ardSd j) (ardDgE j))
    {Λ n₀ ℓ hb : ℕ} {A : Arena Λ n₀}
    {tab : Fin A.N → Fin ℓ → List (Fin A.N)} {D : Orientation A.N} {σ : Env}
    (hA : ArenaStW (arenaNames j) hb (Impl.ofArena A tab) σ)
    (hst : augStInNW ardIo ardIt ardNA j A D σ)
    (hnv : σ.vars (arenaNames j).nN = A.N)
    (hioL : ardCap A.N ≤ (σ.arrs (ardIo j)).length)
    (hitL : ardCap A.N ≤ (σ.arrs (ardIt j)).length)
    (hcaL : A.N ≤ (σ.arrs (ca j)).length)
    (hcoL : A.N + 1 ≤ (σ.arrs (co j)).length) :
    ∃ σ' : Env, ArenaStW (arenaNames j) hb (Impl.ofArena A tab) σ' ∧
      augStInNW ardIo ardIt ardNA j A D σ' ∧
      ardSrd ardMkF ardMkT (ardRegions ardIo ardIt ardFo ardFt ardDgF ardAo
        ardAj ardDgP ardMt ardSg ardTp ardSk ardRo ardRt ardMkT ardOo ardOt
        ardQo ardQt ardAd ardSd ardDgE) j σ' ∧
      A.N ≤ (σ'.arrs (ca j)).length ∧ A.N + 1 ≤ (σ'.arrs (co j)).length := by
  refine exists_ardRoundPre (nA := ardNA) (ardNames_std j).mkF_alloc
    (ardNames_std j).io_wr (ardNames_std j).it_wr (ardNames_std j).it_io ?_
    hA hst hnv hioL hitL hcaL hcoL
  rintro b (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
  · exact ⟨ard_lv_ne_head rfl ard_mkF_head j, ard_lv_notMem rfl
      (fun z hz => ard_regions_head z (by simp only [List.mem_cons]; tauto)) j⟩
  · exact ⟨ard_lv_ne_head rfl ard_mkF_head j, ard_lv_notMem rfl
      (fun z hz => ard_regions_head z (by simp only [List.mem_cons]; tauto)) j⟩
  · exact ⟨ard_lv_ne_head rfl ard_mkF_head j, ard_lv_notMem rfl
      (fun z hz => ard_regions_head z (by simp only [List.mem_cons]; tauto)) j⟩
  · exact ⟨ard_lv_ne_head rfl ard_mkF_head j, ard_lv_notMem rfl
      (fun z hz => ard_regions_head z (by simp only [List.mem_cons]; tauto)) j⟩
  · exact ⟨ard_lv_ne_head rfl ard_mkF_head j, ard_lv_notMem rfl
      (fun z hz => ard_regions_head z (by simp only [List.mem_cons]; tauto)) j⟩
  · exact hca
  · exact hco

/-! ## §7 Axiom audit -/

#print axioms ardTrInCsr_rename
#print axioms ardTrOff_owner_unique
#print axioms ardClear_spec
#print axioms ardCopy_spec
#print axioms ardClearAt
#print axioms ardCopyAt
#print axioms ardWordBound_of_inDegLE
#print axioms ardArena_N_le
#print axioms ardWord_of_inDegLE
#print axioms ardIsContained_map
#print axioms ardIsContained_of_inv
#print axioms ardIsContained_of_chainAdm
#print axioms ardInDegLE_self
#print axioms ardCap_bounds
#print axioms augRoundIn_ardRoundCom
#print axioms ard_lv_ne_head
#print axioms ardNames_std
#print axioms ardCells_std
#print axioms exists_ardSrd
#print axioms exists_ardRoundPre
#print axioms augRoundIn_ardRoundCom_std
#print axioms exists_ardRoundPre_std

end Lax3Proofs.Prog
