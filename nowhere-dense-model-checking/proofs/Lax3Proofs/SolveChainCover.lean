import Lax3Proofs.SolveChainWin
import Lax3Proofs.ImplCover

/-!
# F6c6 (part 3) — the cover stage's machine interface, and its named obligation

The frame chain's cover stage must deliver, from the level's arena,
what every downstream consumer reads (the head file's item (b)):

* **the assignment** `ctr` — one array cell per vertex holding
  `Driver.centre S A π v`, the owner whose child answers for `v`
  (the readback's write-once discipline is definitional through it);
* **the clusters, grouped and ordered** — a CSR-shaped pair
  (`ClusterCsr`): offsets by centre in carrier order, and per centre
  the membership list of `Driver.cluster S A π u` **in ascending
  vertex order**. Ascending is now the enumeration order: after the
  `setEquiv` repin (`DriverArena`, F6c2's finding 1) the abstract
  local names are `Finset.orderIsoOfFin`'s, so the ascending member
  list is *verbatim* `Impl.restrictEmb`'s order — the row's entries
  are exactly what `ClusterList` (the restrict stage's precondition)
  demands, and a counting pass over a per-centre bit-vector emits
  them ascending for free. The cluster bit-vector itself is *not*
  part of the interface: `restrictCom`'s own `rankMark` rebuilds it
  per centre from the list in `O(|X_u|)`, on the one self-cleaning
  scratch array.

No `π`-rank array is delivered: no downstream stage reads `π` itself —
`cluster` and `centre` are the only two objects the ordering enters
through, and both are delivered evaluated.

**`CoverStageSpec` is a named obligation**, `ProgCodegen.SolveSpec`'s
move one layer down: the GKS peeling sweep (per centre one `bfsCom` on
the peeled graph at radius `2R`, plus peel) composes from the landed
`bfsCom_spec` and peel bookkeeping against the landed abstract
identities `Impl.sweepCluster_eq_cluster` / `Impl.sweepCtr_eq_centre`
(`ImplCover` §2–3, which close peeled balls into wreach fibres); its
budget target is `Impl.sweepCharge`'s GKS account
(`sweepCharge_le : ≤ 2·D²·N` under the cover-degree hypothesis).
That discharge did not fit this wave; the chain does not stall on it —
the frame-step obligation consumes this `Spec` shape and nothing else.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.Driver

/-! ## §1 The output regions -/

/-- **The assignment region**: entry `v` holds the centre whose child
answers for `v`. Windowed convention (a valid prefix of an allocation),
like every chain region. -/
def CtrArr (ca : String) {N : ℕ} (ctrF : Fin N → Fin N) (σ : Env) : Prop :=
  N ≤ (σ.arrs ca).length ∧
    ∀ v : Fin N, (σ.arrs ca).getD (v : ℕ) 0 = (ctrF v : ℕ)

/-- **The clusters, grouped and ordered**: offsets by centre (carrier
order) in `co`, memberships in `cm` — row `u` is the member list of
`Xf u` in **ascending vertex order**, which after the `setEquiv` repin
is exactly `Impl.restrictEmb`'s enumeration: entry `t` of row `u` is
the `t`-th local name's parent name, the very value the restrict
stage's `ClusterList` precondition reads. -/
def ClusterCsr (co cm : String) {N : ℕ} (Xf : Fin N → Set (Fin N))
    (σ : Env) : Prop :=
  ∃ offC : ℕ → ℕ,
    offC 0 = 0 ∧
    N + 1 ≤ (σ.arrs co).length ∧
    (∀ i, i ≤ N → (σ.arrs co).getD i 0 = offC i) ∧
    (∀ u : Fin N, offC ((u : ℕ) + 1) = offC (u : ℕ) + (Xf u).ncard) ∧
    offC N ≤ (σ.arrs cm).length ∧
    ∀ (u : Fin N) (t : ℕ), ∀ ht : t < (Xf u).ncard,
      (σ.arrs cm).getD (offC (u : ℕ) + t) 0
        = (Impl.restrictEmb (Xf u) ⟨t, ht⟩ : ℕ)

/-! ## §2 The named obligation -/

/-- **The cover stage's obligation** (F5's machine face, one arena):
from the level's windowed arena state and the two output allocations
(plus the stage's own scratch descriptor `Scv`, the discharger's
choice), the stage leaves the arena intact, the assignment region at
`Driver.centre`, and the cluster CSR at `Driver.cluster` — both at the
ordering the routine `ord` returns for this arena, the same ordering
`ProgDriver.CoverSlotSpec` pins for the NREST mirror. Budget `Kcov`,
the discharger's; the GKS account it should meet is
`Impl.sweepCharge`'s (`ImplCover` §4). -/
def CoverStageSpec (B : ℕ) {L Λ n₀ ℓp : ℕ} (S : Setup L)
    (ord : CoverSpec.OrderingRoutine) (hb : ℕ) (nm : ArenaNames)
    (A : Arena Λ n₀) (htab : Fin A.N → Fin ℓp → List (Fin A.N))
    (ca co cm : String) (Scv : Env → Prop) (coverCom : Com) (Kcov : ℕ) : Prop :=
  Spec B
    (fun σ => ArenaStW nm hb (Impl.ofArena A htab) σ ∧
      A.N ≤ (σ.arrs ca).length ∧ A.N + 1 ≤ (σ.arrs co).length ∧ Scv σ)
    coverCom
    (fun _ σ' => ArenaStW nm hb (Impl.ofArena A htab) σ' ∧
      CtrArr ca (centre S A ((ord A.N A.G).order)) σ' ∧
      ClusterCsr co cm (cluster S A ((ord A.N A.G).order)) σ')
    Kcov

/-! ## §3 What a row means to the restrict stage -/

/-- Reading one row of the cluster CSR *is* the restrict stage's
`ClusterList` semantics, relocated by the row's offset: entry
`offC u + t` holds `restrictEmb (cluster …) t` — so the frame block's
per-centre row copy into the `la` scratch (entry `t ← cm[offC u + t]`,
`|X_u|` cells) lands `ClusterList la (Xf u)` verbatim. Stated as the
membership fact the copy loop's invariant consumes. -/
theorem ClusterCsr.read_row {co cm : String} {N : ℕ}
    {Xf : Fin N → Set (Fin N)} {σ : Env} (h : ClusterCsr co cm Xf σ)
    (u : Fin N) :
    ∃ base : ℕ, base + (Xf u).ncard ≤ (σ.arrs cm).length ∧
      (σ.arrs co).getD (u : ℕ) 0 = base ∧
      ∀ t : ℕ, ∀ ht : t < (Xf u).ncard,
        (σ.arrs cm).getD (base + t) 0 = (Impl.restrictEmb (Xf u) ⟨t, ht⟩ : ℕ) := by
  obtain ⟨offC, h0, hcoL, hco, hstep, hcmL, hcm⟩ := h
  refine ⟨offC (u : ℕ), ?_, hco (u : ℕ) (le_of_lt u.2), fun t ht => hcm u t ht⟩
  -- the row ends at the next offset, and offsets are monotone up to `N`
  have hmono : ∀ j i : ℕ, i ≤ j → j ≤ N → offC i ≤ offC j := by
    intro j
    induction j with
    | zero =>
      intro i hij _
      obtain rfl : i = 0 := by omega
      exact le_rfl
    | succ j ih =>
      intro i hij hjN
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · have hstep' : offC (j + 1) = offC j + (Xf ⟨j, by omega⟩).ncard :=
          hstep ⟨j, by omega⟩
        have := ih i (by omega) (by omega)
        omega
      · obtain rfl : i = j + 1 := by omega
        exact le_rfl
  have hnext : offC ((u : ℕ) + 1) = offC (u : ℕ) + (Xf u).ncard := hstep u
  have hle : offC ((u : ℕ) + 1) ≤ offC N :=
    hmono N ((u : ℕ) + 1) (by have := u.2; omega) le_rfl
  omega

end Lax3Proofs.Prog
