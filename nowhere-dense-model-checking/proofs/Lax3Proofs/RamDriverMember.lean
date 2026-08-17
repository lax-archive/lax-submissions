import Lax3Proofs.RamCoverMember
import Lax3Proofs.RamDriverCluster

/-!
# Active-cover driver contracts

The landed driver stores a carrier-wide cover: there is one centre slot
for every carrier position and every carrier vertex has an assignment.
Nested arenas cannot afford either obligation.  This module gives the
parallel driver surface used by the member-driven ordering and cover
phases, without changing the existing carrier implementation.

`q` is the number of active centre positions.  `centre k` is the carrier
vertex at active position `k`; the machine keeps that list in the
depth's existing `ordName` allocation.  The cluster arena and the
compacted turn list are indexed by `[0,q)`, while vertices and table rows
remain in the original carrier numbering.
-/

namespace Lax3Proofs.RamDriverMember

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (CsrGraph masked)
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster
open Lax13Proofs.Imp Lax13Proofs.Reasoning

/-- The cover state retained by a member-driven level.  Physical arrays
keep their carrier allocations; only the live prefixes are meaningful. -/
structure CoverHeldAtA (B n q j : ℕ) (G : SimpleGraph (Fin n)) (M : ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (centre : ℕ → ℕ) (cap : ℕ)
    (Xoff Xmem asg : ℕ → ℕ) (m : ℕ) (σ : Env) : Prop where
  centre_arr : σ.arrs (ordName j) = arrOf n centre
  off_arr : σ.arrs (xofName j) = arrOf (n + 1) Xoff
  mem_arr : σ.arrs (xmmName j) = arrOf (n * n) Xmem
  asg_arr : σ.arrs (asgName j) = arrOf n asg
  pointer : σ.vars (xpName j) = m
  alloc : m ≤ n * n
  pointer_lt : m < B
  centre_lt : ∀ k < q, centre k < n
  cover : RamCover.CoverOutA G M π centre cap q m Xoff Xmem asg

/-- A carrier-wide retained cover restricts to the active consumer
surface at `q = n`. -/
theorem CoverHeldAtA.ofCarrier {B n j cap m : ℕ} {G : SimpleGraph (Fin n)}
    {M ord Xoff Xmem asg : ℕ → ℕ} {π : Equiv.Perm (Fin n)} {σ : Env}
    (hord : RamCover.OrdersBy n π ord)
    (h : CoverHeldAt B n j G M π ord cap Xoff Xmem asg m σ) :
    CoverHeldAtA B n n j G M π ord cap Xoff Xmem asg m σ :=
  { centre_arr := h.1
    off_arr := h.2.1
    mem_arr := h.2.2.1
    asg_arr := h.2.2.2.1
    pointer := h.2.2.2.2.1
    alloc := h.2.2.2.2.2.1
    pointer_lt := h.2.2.2.2.2.2.1
    centre_lt := h.2.2.2.2.2.2.2.1
    cover := h.2.2.2.2.2.2.2.2.toActive hord }

/-- Frame the five machine locations of an active retained cover. -/
theorem CoverHeldAtA.congr {B n q j cap m : ℕ} {G : SimpleGraph (Fin n)}
    {M centre Xoff Xmem asg : ℕ → ℕ} {π : Equiv.Perm (Fin n)} {σ σ' : Env}
    (h : CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg m σ)
    (hcentre : σ'.arrs (ordName j) = σ.arrs (ordName j))
    (hxoff : σ'.arrs (xofName j) = σ.arrs (xofName j))
    (hxmem : σ'.arrs (xmmName j) = σ.arrs (xmmName j))
    (hasg : σ'.arrs (asgName j) = σ.arrs (asgName j))
    (hxp : σ'.vars (xpName j) = σ.vars (xpName j)) :
    CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg m σ' :=
  { centre_arr := by rw [hcentre]; exact h.centre_arr
    off_arr := by rw [hxoff]; exact h.off_arr
    mem_arr := by rw [hxmem]; exact h.mem_arr
    asg_arr := by rw [hasg]; exact h.asg_arr
    pointer := by rw [hxp]; exact h.pointer
    alloc := h.alloc
    pointer_lt := h.pointer_lt
    centre_lt := h.centre_lt
    cover := h.cover }

/-- Everything a turn reads at one active cover. -/
structure TurnPreA (B n q cap mb ns Ws j : ℕ) (G : SimpleGraph (Fin n))
    (O T M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre Xoff Xmem asg : ℕ → ℕ) (m : ℕ) (σ : Env) : Prop where
  level : LevelPre B n cap mb ns Ws O T j M Gm C σ
  play : PlayRec B cap G j M Gm σ
  held : CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg m σ

/-- The ordering phase at the active interface.  Its executable answer
is the centre list.  `P` retains whatever mathematical witness relates
that list to the permutation used by the cover-degree argument. -/
def OrderImplementsA (B n W cap mb ns j : ℕ) (O T M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ)
    (P : (ℕ → ℕ) → ℕ → Equiv.Perm (Fin n) → (ℕ → ℕ) → Prop)
    (order : Com) (K : ℕ) : Prop :=
  Spec B (fun σ => LevelPre B n cap mb ns W O T j M Gm C σ)
    order
    (fun σ σ' => LevelPre B n cap mb ns W O T j M Gm C σ' ∧
      σ'.out = σ.out ∧
      (∀ a : ℕ, σ'.vars (ctrName a) = σ.vars (ctrName a)) ∧
      (∀ a : ℕ, σ'.arrs (resName a) = σ.arrs (resName a)) ∧
      (∀ a : ℕ, σ'.arrs (gamName a) = σ.arrs (gamName a)) ∧
      (∀ a : ℕ, σ'.arrs (parName a) = σ.arrs (parName a)) ∧
      ∃ (q : ℕ) (π : Equiv.Perm (Fin n)) (centre : ℕ → ℕ),
        q ≤ n ∧ σ'.arrs (ordName j) = arrOf n centre ∧
        (∀ k < q, centre k < n) ∧ P M q π centre) K

/-- The cover phase at the active interface.  It returns blocks indexed
by `[0,q)` and compacts exactly that prefix for the turn loop. -/
def CoverImplementsA (B n q cap mb ns W j : ℕ) (G : SimpleGraph (Fin n))
    (O T M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre : ℕ → ℕ) (coverPhaseA : Com) (K : ℕ) : Prop :=
  Spec B (fun σ => LevelPre B n cap mb ns W O T j M Gm C σ ∧
      σ.arrs (ordName j) = arrOf n centre ∧ ∀ k < q, centre k < n)
    coverPhaseA
    (fun σ σ' => LevelPre B n cap mb ns W O T j M Gm C σ' ∧ σ'.out = σ.out ∧
      (∀ a : ℕ, σ'.vars (ctrName a) = σ.vars (ctrName a)) ∧
      (∀ a : ℕ, σ'.arrs (resName a) = σ.arrs (resName a)) ∧
      (∀ a : ℕ, σ'.arrs (gamName a) = σ.arrs (gamName a)) ∧
      (∀ a : ℕ, σ'.arrs (parName a) = σ.arrs (parName a)) ∧
      ∃ (Xoff Xmem asg cps : ℕ → ℕ) (m cnum : ℕ),
        CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg m σ' ∧
        σ'.arrs (cpsName j) = arrOf n cps ∧ σ'.vars (cnumName j) = cnum ∧
        Compacted q cnum m M centre Xoff cps) K

/-- One active cluster turn.  This is the landed cluster obligation with
the carrier centre bound replaced by the active-prefix bound. -/
def ClusterStepImplementsA {n : ℕ} (B q_top cap mb ns W ℓ j : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (q : ℕ) (π : Equiv.Perm (Fin n))
    (centre Xoff Xmem asg : ℕ → ℕ) (m k : ℕ)
    (wA : (ℕ → ℕ) → ℕ) (inner : Com) (Kin : ℕ → ℕ) (K : ℕ) : Prop :=
  k < q → M (centre k) ≠ 0 →
  (∀ c < sigL cap mb j, ∀ v < n, C c v ≤ 1) →
  (∀ (M' Gm' : ℕ → ℕ) (C' : ℕ → ℕ → ℕ) (D' : Set (Fin n)),
      (∀ v : Fin n, v ∈ D' → M' (v : ℕ) = 0) →
      (∀ c < sigL cap mb (j + 1), ∀ v < n, C' c v ≤ 1) →
      Spec B (fun σ => LevelPre B n cap mb ns W O T (j + 1) M' Gm' C' σ ∧
          TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ℓ φ σ ∧
          PlayRec B cap G (j + 1) M' Gm' σ ∧
          TableInvOn q_top cap mb φ G (j + 1) M' C' D' σ) inner
        (fun σ σ' => LevelPostD B q_top cap mb φ G ns W O T (j + 1) M' Gm' C' D' σ σ' ∧
          σ'.out = σ.out) (Kin (wA M'))) →
  Spec B (fun σ => LevelPre B n cap mb ns W O T j M Gm C σ ∧
      TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ℓ φ σ ∧
      PlayRec B cap G j M Gm σ ∧
      CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg m σ ∧
      σ.vars (curName j) = k)
    (clusterCom q_top cap mb φ j inner)
    (fun σ σ' => LevelPre B n cap mb ns W O T j M Gm C σ' ∧
      TablesSized q_top cap mb φ n σ' ∧ BaseArrs B q_top cap mb ℓ φ σ' ∧
      PlayRec B cap G j M Gm σ' ∧ σ'.out = σ.out ∧
      σ'.vars (curName j) = σ.vars (curName j) ∧
      ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length), ∃ Tb : ℕ → ℕ,
        σ'.arrs (tabName j i) = arrOf n Tb ∧
        ∀ v : Fin n, M (v : ℕ) ≠ 0 → asg (v : ℕ) = σ.vars (curName j) →
          Tb (v : ℕ) ≤ 1 ∧
          (Tb (v : ℕ) ≠ 0 ↔
            Sat (masked G M) (colRead n C (sigL cap mb j)) (fun _ => v)
              (tablesAt q_top cap mb φ j)[i])) K

/-- The semantic frame of an active turn.  A depth-`j` row is unchanged
at every dead parent vertex, and at every live vertex assigned to a
different turn.  The explicit dead disjunct removes the old dependence
on an initialized assignment cell outside the active arena. -/
def ClusterFramesA {n : ℕ} (B q_top cap mb ns W ℓ j : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (q : ℕ) (π : Equiv.Perm (Fin n))
    (centre Xoff Xmem asg : ℕ → ℕ) (m k : ℕ)
    (wA : (ℕ → ℕ) → ℕ) (inner : Com) (Kin : ℕ → ℕ) (K : ℕ) : Prop :=
  k < q → M (centre k) ≠ 0 →
  (∀ (M' Gm' : ℕ → ℕ) (C' : ℕ → ℕ → ℕ) (D' : Set (Fin n)),
      (∀ v : Fin n, v ∈ D' → M' (v : ℕ) = 0) →
      (∀ c < sigL cap mb (j + 1), ∀ v < n, C' c v ≤ 1) →
      Spec B (fun σ => LevelPre B n cap mb ns W O T (j + 1) M' Gm' C' σ ∧
          TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ℓ φ σ ∧
          PlayRec B cap G (j + 1) M' Gm' σ ∧
          TableInvOn q_top cap mb φ G (j + 1) M' C' D' σ) inner
        (fun σ σ' => LevelPostD B q_top cap mb φ G ns W O T (j + 1) M' Gm' C' D' σ σ' ∧
          σ'.out = σ.out) (Kin (wA M'))) →
  Spec B (fun σ => LevelPre B n cap mb ns W O T j M Gm C σ ∧
      TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ℓ φ σ ∧
      PlayRec B cap G j M Gm σ ∧
      CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg m σ ∧
      σ.vars (curName j) = k)
    (clusterCom q_top cap mb φ j inner)
    (fun σ σ' => CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg m σ' ∧
      ∀ (i : ℕ), i < (tablesAt q_top cap mb φ j).length → ∀ Tb Tb₀ : ℕ → ℕ,
        σ'.arrs (tabName j i) = arrOf n Tb → σ.arrs (tabName j i) = arrOf n Tb₀ →
        ∀ v : Fin n, M (v : ℕ) = 0 ∨ asg (v : ℕ) ≠ σ.vars (curName j) →
          Tb (v : ℕ) = Tb₀ (v : ℕ)) K

/-- The active centre-loop invariant. -/
def LevelInvA {n : ℕ} (B q_top cap mb ns W ℓ j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
    (q : ℕ) (π : Equiv.Perm (Fin n)) (centre Xoff Xmem asg cps : ℕ → ℕ)
    (m cnum : ℕ) (D : Set (Fin n)) (outs : List ℕ) (σ : Env) : Prop :=
  LevelPre B n cap mb ns W O T j M Gm C σ ∧ TablesSized q_top cap mb φ n σ ∧
    BaseArrs B q_top cap mb ℓ φ σ ∧ PlayRec B cap G j M Gm σ ∧
    CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg m σ ∧
    σ.arrs (cpsName j) = arrOf n cps ∧ σ.vars (cnumName j) = cnum ∧
    σ.out = outs ∧ σ.vars (cixName j) ≤ cnum ∧
    ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length) (Tb : ℕ → ℕ),
      σ.arrs (tabName j i) = arrOf n Tb →
      ∀ v : Fin n, (v ∈ D ∨ (M (v : ℕ) ≠ 0 ∧
          ∃ k < σ.vars (cixName j), asg (v : ℕ) = cps k)) →
        Tb (v : ℕ) ≤ 1 ∧
        (Tb (v : ℕ) ≠ 0 ↔
          Sat (masked G M) (colRead n C (sigL cap mb j)) (fun _ => v)
            (tablesAt q_top cap mb φ j)[i])

/-! ## A driver text parameterized by its two carrier phases -/

open Classical in
/-- The recursion and cluster body are shared with the landed driver;
only ordering and cover construction are replaceable. -/
noncomputable def driverAuxA (q_top cap mb ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (orderPhase coverPhase : ℕ → Com) : ℕ → ℕ → Com
  | 0, j => baseCom q_top cap mb j φ
  | f + 1, j =>
      .seq (orderPhase j)
        (.seq (coverPhase j)
          (.seq (.assign (cixName j) (.lit 0))
            (.while (.lt (.var (cixName j)) (.var (cnumName j)))
              (.seq (.assign (curName j) (.get (cpsName j) (.var (cixName j))))
                (.seq (clusterCom q_top cap mb φ j
                    (driverAuxA q_top cap mb ℓ φ orderPhase coverPhase f (j + 1)))
                  (.assign (cixName j) (.add (.var (cixName j)) (.lit 1))))))))

open Classical in
/-- The active driver at depth `j`. -/
noncomputable def driverAtA (q_top cap mb ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (orderPhase coverPhase : ℕ → Com) (j : ℕ) : Com :=
  driverAuxA q_top cap mb ℓ φ orderPhase coverPhase (ℓ - j) j

theorem driverAtA_bot (q_top cap mb ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (orderPhase coverPhase : ℕ → Com) :
    driverAtA q_top cap mb ℓ φ orderPhase coverPhase ℓ = baseCom q_top cap mb ℓ φ := by
  rw [driverAtA, Nat.sub_self, driverAuxA]

theorem driverAtA_succ (q_top cap mb ℓ : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (orderPhase coverPhase : ℕ → Com) {j : ℕ} (hj : j < ℓ) :
    driverAtA q_top cap mb ℓ φ orderPhase coverPhase j =
      .seq (orderPhase j)
        (.seq (coverPhase j)
          (.seq (.assign (cixName j) (.lit 0))
            (.while (.lt (.var (cixName j)) (.var (cnumName j)))
              (.seq (.assign (curName j) (.get (cpsName j) (.var (cixName j))))
                (.seq (clusterCom q_top cap mb φ j
                    (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1)))
                  (.assign (cixName j) (.add (.var (cixName j)) (.lit 1)))))))) := by
  obtain ⟨f, hf⟩ : ∃ f, ℓ - j = f + 1 := ⟨ℓ - j - 1, by omega⟩
  rw [driverAtA, hf, driverAuxA, driverAtA, show ℓ - (j + 1) = f by omega]

/-- The domain-aware level contract for the parameterized active
driver.  Its semantic pre/postconditions are exactly the landed ones. -/
def LevelImplementsDA {n : ℕ} (B q_top cap mb ℓ W ns j : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (D : Set (Fin n)) (orderPhase coverPhase : ℕ → Com)
    (K : ℕ) : Prop :=
  (∀ v : Fin n, v ∈ D → M (v : ℕ) = 0) →
  (∀ c < sigL cap mb j, ∀ v < n, C c v ≤ 1) →
  Spec B (fun σ => LevelPre B n cap mb ns W O T j M Gm C σ ∧
      TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ℓ φ σ ∧
      PlayRec B cap G j M Gm σ ∧ TableInvOn q_top cap mb φ G j M C D σ)
    (driverAtA q_top cap mb ℓ φ orderPhase coverPhase j)
    (fun σ σ' => LevelPostD B q_top cap mb φ G ns W O T j M Gm C D σ σ' ∧
      σ'.out = σ.out) K

end Lax3Proofs.RamDriverMember
