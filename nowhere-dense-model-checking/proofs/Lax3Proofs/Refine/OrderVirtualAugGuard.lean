import Lax3Proofs.Refine.OrderVirtualBaseOrient
import Lax3Proofs.Refine.OrderVirtualBiUnion

/-!
# The rank-aware guard for virtual augmentation rows

Both rows of the next augmentation are obtained from the same local test.
An already adjacent vertex is rejected, an already emitted vertex is skipped,
and a vertex demanded in both directions is retained according to the saved
rank.  `RankDir` packages the only difference between incoming and outgoing
rows, so the executable proof below serves both recursive providers.
-/

namespace Lax3Proofs.Refine.OrderVirtualAugGuard

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.RamDriverAugment
  (Emits Guarded Marks stampCond emitBranch_run valSet mem_valSet mem_valSet_of valSet_union)
open Lax3Proofs.Refine.OrderVirtualBaseOrient
open Lax3Proofs.Refine.OrderVirtualBiUnion
open Lax3Proofs.Refine.OrderVirtualRows
open Lax3Proofs.Augmentation
open Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.RamAugment

/-- One rank-aware candidate test.  The three stamp arrays respectively
record old adjacency, demand in the opposite direction, and candidates
already emitted by either half of the desired demand union. -/
def virtualAugGuard (dir : RankDir) (rk : String) (act : Com) : Com :=
  .ite (.eq (.get "sta" (.var "u")) (.lit 0))
    (.ite (.eq (.get "ste" (.var "u")) (.lit 0))
      (.ite (.eq (.get "std" (.var "u")) (.lit 0))
        (.seq (.store "ste" (.var "u") (.lit 1)) act)
        (.ite (rankCond dir rk)
          (.seq (.store "ste" (.var "u") (.lit 1)) act) .skip))
      .skip)
    .skip

/-- Numeric contribution of one desired-demand candidate. -/
def virtualAugFe (dir : RankDir) (A Dm : Finset ℕ) (R : ℕ → ℕ)
    (root z : ℕ) : Finset ℕ :=
  if z ∈ A then ∅ else if z ∈ Dm ∧ ¬ dir.keep R root z then ∅ else {z}

/-! ## Direction-independent semantic names -/

noncomputable def demandSet (dir : RankDir) {n : ℕ} (D : Orientation n) (v : Fin n) :
    Finset (Fin n) :=
  match dir with
  | .incoming => demandIn D v
  | .outgoing => demandOut D v

noncomputable def oppositeDemandSet (dir : RankDir) {n : ℕ} (D : Orientation n) (v : Fin n) :
    Finset (Fin n) :=
  match dir with
  | .incoming => demandOut D v
  | .outgoing => demandIn D v

noncomputable def transSet (dir : RankDir) {n : ℕ} (D : Orientation n) (v : Fin n) :
    Finset (Fin n) :=
  match dir with
  | .incoming => transInSet D v
  | .outgoing => transOutSet D v

noncomputable def oppositeTransSet (dir : RankDir) {n : ℕ} (D : Orientation n) (v : Fin n) :
    Finset (Fin n) :=
  match dir with
  | .incoming => transOutSet D v
  | .outgoing => transInSet D v

noncomputable def augCandidateSet (dir : RankDir) {n : ℕ} (D : Orientation n)
    (rank : Fin n → ℕ) (v : Fin n) : Finset (Fin n) :=
  match dir with
  | .incoming => inCand D rank v
  | .outgoing => outCand D rank v

def oppositeOrientSet (dir : RankDir) {n : ℕ} (D : Orientation n)
    (v : Fin n) : Finset (Fin n) :=
  match dir with
  | .incoming => outSet D v
  | .outgoing => D.inN v

theorem adjSet_eq_direction_union {n : ℕ} (dir : RankDir)
    (D : Orientation n) (v : Fin n) :
    adjSet D v = orientSet dir D v ∪ oppositeOrientSet dir D v := by
  cases dir with
  | incoming => exact Lax3Proofs.RamDriverAugment.adjSet_eq D v
  | outgoing =>
      rw [orientSet, oppositeOrientSet,
        Lax3Proofs.RamDriverAugment.adjSet_eq, Finset.union_comm]

theorem orientSet_augOr_eq {n : ℕ} (dir : RankDir) (D : Orientation n)
    (rank : Fin n → ℕ) (v : Fin n) :
    orientSet dir (augOr D rank) v =
      orientSet dir D v ∪ augCandidateSet dir D rank v := by
  cases dir with
  | incoming => exact inSet_augOr_eq D rank v
  | outgoing => exact outSet_augOr_eq D rank v

/-- The two generated pieces are exactly the desired demand row with its
root erased.  A fraternity demand may contain that root; the eventual
orientation guard rejects it because the reverse demand is then present and
no strict rank can point from a vertex to itself. -/
theorem demandSet_erase_eq_union {n : ℕ} (dir : RankDir) (D : Orientation n)
    (v : Fin n) :
    (demandSet dir D v).erase v = transSet dir D v ∪ fratNbrs D v := by
  cases dir with
  | incoming =>
      exact demandIn_erase_eq D v
  | outgoing =>
      exact demandOut_erase_eq D v

theorem oppositeDemandSet_erase_eq_union {n : ℕ} (dir : RankDir)
    (D : Orientation n) (v : Fin n) :
    (oppositeDemandSet dir D v).erase v =
      oppositeTransSet dir D v ∪ fratNbrs D v := by
  cases dir with
  | incoming =>
      exact demandOut_erase_eq D v
  | outgoing =>
      exact demandIn_erase_eq D v

theorem root_not_mem_augCandidateSet {n : ℕ} (dir : RankDir)
    (D : Orientation n) (rank : Fin n → ℕ) (root : Fin n) :
    root ∉ augCandidateSet dir D rank root := by
  cases dir with
  | incoming =>
      rw [augCandidateSet, mem_inCand, newArc_in_iff]
      rintro ⟨-, hd, hkeep⟩
      have hback : root ∈ demandOut D root := by
        rw [Lax3Proofs.Refine.OrderVirtualRows.mem_demandIn] at hd
        rw [mem_demandOut]
        exact hd
      exact (Nat.lt_irrefl (rank root)) (hkeep hback)
  | outgoing =>
      rw [augCandidateSet, mem_outCand, newArc_out_iff]
      rintro ⟨-, hd, hkeep⟩
      have hback : root ∈ demandIn D root := by
        rw [mem_demandOut] at hd
        rw [Lax3Proofs.Refine.OrderVirtualRows.mem_demandIn]
        exact hd
      exact (Nat.lt_irrefl (rank root)) (hkeep hback)

/-- The numeric union produced by scanning the desired demand row under the
three-stamp guard is exactly the corresponding `NewArc` candidate set. -/
theorem virtualAugFe_demand_eq {n : ℕ} (dir : RankDir) (D : Orientation n)
    (rank : Fin n → ℕ) (R : ℕ → ℕ) (root : Fin n)
    (hrank : ∀ v : Fin n, rank v = R (v : ℕ)) :
    (valSet ((demandSet dir D root).erase root)).biUnion
        (virtualAugFe dir (valSet (adjSet D root))
          (valSet ((oppositeDemandSet dir D root).erase root)) R (root : ℕ)) =
      valSet (augCandidateSet dir D rank root) := by
  classical
  ext y
  cases dir with
  | incoming =>
      simp only [demandSet, oppositeDemandSet, augCandidateSet]
      rw [Finset.mem_biUnion, mem_valSet]
      constructor
      · rintro ⟨z, hzDnum, hy⟩
        obtain ⟨hzn, hzD⟩ := mem_valSet.1 hzDnum
        have hzroot : (⟨z, hzn⟩ : Fin n) ≠ root := (Finset.mem_erase.1 hzD).1
        have hzDemand : (⟨z, hzn⟩ : Fin n) ∈ demandIn D root :=
          (Finset.mem_erase.1 hzD).2
        have hAiff : z ∈ valSet (adjSet D root) ↔
            (⟨z, hzn⟩ : Fin n) ∈ adjSet D root := by
          rw [mem_valSet]
          constructor
          · rintro ⟨hz', hm⟩
            simpa using hm
          · exact fun hm => ⟨hzn, hm⟩
        have hOiff : z ∈ valSet ((demandOut D root).erase root) ↔
            (⟨z, hzn⟩ : Fin n) ∈ demandOut D root := by
          rw [mem_valSet]
          constructor
          · rintro ⟨hz', hm⟩
            exact (Finset.mem_erase.1 (by simpa using hm)).2
          · exact fun hm => ⟨hzn, Finset.mem_erase.2 ⟨hzroot, hm⟩⟩
        by_cases hzA : ⟨z, hzn⟩ ∈ adjSet D root
        · have hzAnum := hAiff.2 hzA
          unfold virtualAugFe at hy
          rw [if_pos hzAnum] at hy
          simp at hy
        by_cases hzO : ⟨z, hzn⟩ ∈ demandOut D root ∧
            ¬ R z < R (root : ℕ)
        · have hzOnum : z ∈ valSet ((demandOut D root).erase root) ∧
              ¬ R z < R (root : ℕ) := ⟨hOiff.2 hzO.1, hzO.2⟩
          have hzAnum : z ∉ valSet (adjSet D root) := fun h => hzA (hAiff.1 h)
          have hzOnum' : z ∈ valSet ((demandOut D root).erase root) ∧
              ¬ RankDir.incoming.keep R (root : ℕ) z := by
            simpa only [RankDir.keep] using hzOnum
          unfold virtualAugFe at hy
          rw [if_neg hzAnum, if_pos hzOnum'] at hy
          simp at hy
        have hzAnum : z ∉ valSet (adjSet D root) := fun h => hzA (hAiff.1 h)
        have hzOnum : ¬ (z ∈ valSet ((demandOut D root).erase root) ∧
            ¬ R z < R (root : ℕ)) := by
          rintro ⟨hm, hn⟩
          exact hzO ⟨hOiff.1 hm, hn⟩
        have hzOnum' : ¬ (z ∈ valSet ((demandOut D root).erase root) ∧
            ¬ RankDir.incoming.keep R (root : ℕ) z) := by
          simpa only [RankDir.keep] using hzOnum
        have hyz : y = z := by
          unfold virtualAugFe at hy
          rw [if_neg hzAnum, if_neg hzOnum'] at hy
          simpa using hy
        subst y
        refine ⟨hzn, ?_⟩
        rw [mem_inCand, newArc_in_iff]
        refine ⟨?_, hzDemand, ?_⟩
        · simpa using hzA
        · intro hzOut
          have hkeep : R z < R (root : ℕ) := by
            by_contra hn
            exact hzO ⟨hzOut, hn⟩
          simpa [hrank ⟨z, hzn⟩, hrank root] using hkeep
      · rintro ⟨hyn, hyCand⟩
        have hyCandMem : (⟨y, hyn⟩ : Fin n) ∈ inCand D rank root := hyCand
        have hyroot : (⟨y, hyn⟩ : Fin n) ≠ root := by
          intro heq
          apply root_not_mem_augCandidateSet .incoming D rank root
          simpa only [augCandidateSet, heq] using hyCandMem
        rw [mem_inCand, newArc_in_iff] at hyCand
        refine ⟨y, mem_valSet_of (Finset.mem_erase.2 ⟨hyroot, hyCand.2.1⟩), ?_⟩
        have hyA : y ∉ valSet (adjSet D root) := by
          intro hm
          obtain ⟨hy', hm'⟩ := mem_valSet.1 hm
          exact hyCand.1 (by simpa using hm')
        have hyO : ¬ (y ∈ valSet ((demandOut D root).erase root) ∧
            ¬ R y < R (root : ℕ)) := by
          rintro ⟨houtNum, hn⟩
          obtain ⟨hy', houtErase⟩ := mem_valSet.1 houtNum
          have hout := (Finset.mem_erase.1 houtErase).2
          apply hn
          have hout' : (⟨y, hyn⟩ : Fin n) ∈ demandOut D root := by simpa using hout
          simpa [hrank ⟨y, hyn⟩, hrank root] using hyCand.2.2 hout'
        have hyO' : ¬ (y ∈ valSet ((demandOut D root).erase root) ∧
            ¬ RankDir.incoming.keep R (root : ℕ) y) := by
          simpa only [RankDir.keep] using hyO
        unfold virtualAugFe
        rw [if_neg hyA, if_neg hyO']
        simp
  | outgoing =>
      simp only [demandSet, oppositeDemandSet, augCandidateSet]
      rw [Finset.mem_biUnion, mem_valSet]
      constructor
      · rintro ⟨z, hzDnum, hy⟩
        obtain ⟨hzn, hzD⟩ := mem_valSet.1 hzDnum
        have hzroot : (⟨z, hzn⟩ : Fin n) ≠ root := (Finset.mem_erase.1 hzD).1
        have hzDemand : (⟨z, hzn⟩ : Fin n) ∈ demandOut D root :=
          (Finset.mem_erase.1 hzD).2
        have hAiff : z ∈ valSet (adjSet D root) ↔
            (⟨z, hzn⟩ : Fin n) ∈ adjSet D root := by
          rw [mem_valSet]
          constructor
          · rintro ⟨hz', hm⟩
            simpa using hm
          · exact fun hm => ⟨hzn, hm⟩
        have hOiff : z ∈ valSet ((demandIn D root).erase root) ↔
            (⟨z, hzn⟩ : Fin n) ∈ demandIn D root := by
          rw [mem_valSet]
          constructor
          · rintro ⟨hz', hm⟩
            exact (Finset.mem_erase.1 (by simpa using hm)).2
          · exact fun hm => ⟨hzn, Finset.mem_erase.2 ⟨hzroot, hm⟩⟩
        by_cases hzA : ⟨z, hzn⟩ ∈ adjSet D root
        · have hzAnum := hAiff.2 hzA
          unfold virtualAugFe at hy
          rw [if_pos hzAnum] at hy
          simp at hy
        by_cases hzO : ⟨z, hzn⟩ ∈ demandIn D root ∧
            ¬ R (root : ℕ) < R z
        · have hzOnum : z ∈ valSet ((demandIn D root).erase root) ∧
              ¬ R (root : ℕ) < R z := ⟨hOiff.2 hzO.1, hzO.2⟩
          have hzAnum : z ∉ valSet (adjSet D root) := fun h => hzA (hAiff.1 h)
          have hzOnum' : z ∈ valSet ((demandIn D root).erase root) ∧
              ¬ RankDir.outgoing.keep R (root : ℕ) z := by
            simpa only [RankDir.keep] using hzOnum
          unfold virtualAugFe at hy
          rw [if_neg hzAnum, if_pos hzOnum'] at hy
          simp at hy
        have hzAnum : z ∉ valSet (adjSet D root) := fun h => hzA (hAiff.1 h)
        have hzOnum : ¬ (z ∈ valSet ((demandIn D root).erase root) ∧
            ¬ R (root : ℕ) < R z) := by
          rintro ⟨hm, hn⟩
          exact hzO ⟨hOiff.1 hm, hn⟩
        have hzOnum' : ¬ (z ∈ valSet ((demandIn D root).erase root) ∧
            ¬ RankDir.outgoing.keep R (root : ℕ) z) := by
          simpa only [RankDir.keep] using hzOnum
        have hyz : y = z := by
          unfold virtualAugFe at hy
          rw [if_neg hzAnum, if_neg hzOnum'] at hy
          simpa using hy
        subst y
        refine ⟨hzn, ?_⟩
        rw [mem_outCand, newArc_out_iff]
        refine ⟨?_, hzDemand, ?_⟩
        · simpa using hzA
        · intro hzIn
          have hkeep : R (root : ℕ) < R z := by
            by_contra hn
            exact hzO ⟨hzIn, hn⟩
          simpa [hrank ⟨z, hzn⟩, hrank root] using hkeep
      · rintro ⟨hyn, hyCand⟩
        have hyCandMem : (⟨y, hyn⟩ : Fin n) ∈ outCand D rank root := hyCand
        have hyroot : (⟨y, hyn⟩ : Fin n) ≠ root := by
          intro heq
          apply root_not_mem_augCandidateSet .outgoing D rank root
          simpa only [augCandidateSet, heq] using hyCandMem
        rw [mem_outCand, newArc_out_iff] at hyCand
        refine ⟨y, mem_valSet_of (Finset.mem_erase.2 ⟨hyroot, hyCand.2.1⟩), ?_⟩
        have hyA : y ∉ valSet (adjSet D root) := by
          intro hm
          obtain ⟨hy', hm'⟩ := mem_valSet.1 hm
          exact hyCand.1 (by simpa using hm')
        have hyO : ¬ (y ∈ valSet ((demandIn D root).erase root) ∧
            ¬ R (root : ℕ) < R y) := by
          rintro ⟨hinNum, hn⟩
          obtain ⟨hy', hinErase⟩ := mem_valSet.1 hinNum
          have hin := (Finset.mem_erase.1 hinErase).2
          apply hn
          have hin' : (⟨y, hyn⟩ : Fin n) ∈ demandIn D root := by simpa using hin
          simpa [hrank ⟨y, hyn⟩, hrank root] using hyCand.2.2 hin'
        have hyO' : ¬ (y ∈ valSet ((demandIn D root).erase root) ∧
            ¬ RankDir.outgoing.keep R (root : ℕ) y) := by
          simpa only [RankDir.keep] using hyO
        unfold virtualAugFe
        rw [if_neg hyA, if_neg hyO']
        simp

/-- The direction-parametric virtual guard implements exactly
`virtualAugFe`.  This is the reusable local proof needed by both halves of
every recursively generated augmented-orientation row. -/
theorem virtualAugGuard_of_emits {B n Ka root : ℕ} {dir : RankDir}
    {rk a₁ a₂ : String} {act : Com}
    {Acc : Finset ℕ → Env → Prop} {A Dm Base Cap : Finset ℕ} {R : ℕ → ℕ}
    (ha₁ : a₁ ≠ "ste") (ha₂ : a₂ ≠ "ste")
    (hb₁ : a₁ ≠ "sta") (hb₂ : a₂ ≠ "sta")
    (hc₁ : a₁ ≠ "std") (hc₂ : a₂ ≠ "std")
    (hd₁ : a₁ ≠ rk) (hd₂ : a₂ ≠ rk) (hds : rk ≠ "ste")
    (hB1 : 1 < B) (hnB : n < B) (hroot : root < n)
    (hR : ∀ v, v < n → R v < n) (hBA : Base ⊆ A)
    (hAccSt : ∀ S tau p x, Acc S tau → Acc S (tau.setArr "ste" p x))
    (hAccW : ∀ S tau, Acc S tau → tau.vars "w" = root)
    (hAcc : Emits B n Ka a₁ a₂ act Cap Acc) :
    Guarded B n (Ka + 24) (virtualAugGuard dir rk act)
      (virtualAugFe dir A Dm R root) Cap
      (fun S tau => Marks "ste" n 1 (Base ∪ S) (fun _ => 0) tau ∧
        Marks "sta" n 1 A (fun _ => 0) tau ∧
        Marks "std" n 1 Dm (fun _ => 0) tau ∧
        tau.arrs rk = arrOf n R ∧ Acc (Base ∪ S) tau) := by
  classical
  rintro S tau z ⟨hme, hma, hmd, hrnk, hA⟩ hu hzn hfe
  have ea := stampCond hma hu hzn hB1 hnB
  have ee := stampCond hme hu hzn hB1 hnB
  have ed := stampCond hmd hu hzn hB1 hnB
  have hw : tau.vars "w" = root := hAccW _ tau hA
  have elt : (rankCond dir rk).evalB B tau =
      some (decide (dir.keep R root z)) :=
    rankCond_eval hnB hroot hzn hR hrnk hw hu
  have hkeep : ∀ (tau' : Env),
      (∀ a, a ≠ a₁ → a ≠ a₂ → a ≠ "ste" → tau'.arrs a = tau.arrs a) →
      Marks "sta" n 1 A (fun _ => 0) tau' ∧
        Marks "std" n 1 Dm (fun _ => 0) tau' ∧
        tau'.arrs rk = arrOf n R := by
    intro tau' hfr
    obtain ⟨ga, hga, hgak⟩ := hma
    obtain ⟨gd, hgd, hgdk⟩ := hmd
    exact ⟨⟨ga, by
        rw [hfr "sta" (Ne.symm hb₁) (Ne.symm hb₂) (by decide)]
        exact hga, hgak⟩,
      ⟨gd, by
        rw [hfr "std" (Ne.symm hc₁) (Ne.symm hc₂) (by decide)]
        exact hgd, hgdk⟩,
      by
        rw [hfr rk (Ne.symm hd₁) (Ne.symm hd₂) hds]
        exact hrnk⟩
  by_cases hzA : z ∈ A
  · refine ⟨tau, _, Run.ite_false (by rw [ea]; simp [hzA]) Run.skip, ?_, ?_,
      fun _ _ => rfl⟩
    · simp only [virtualAugGuard, size_condEq, size_get, size_var, size_lit]
      omega
    · simp only [virtualAugFe, if_pos hzA, Finset.union_empty]
      exact ⟨hme, hma, hmd, hrnk, hA⟩
  · have hzB : z ∉ Base := fun hc => hzA (hBA hc)
    by_cases hzS : z ∈ S
    · refine ⟨tau, _, Run.ite_true (by rw [ea]; simp [hzA])
          (Run.ite_false (by rw [ee]; simp [hzB, hzS]) Run.skip), ?_, ?_, fun _ _ => rfl⟩
      · simp only [virtualAugGuard, size_condEq, size_get, size_var, size_lit]
        omega
      · have hset : S ∪ virtualAugFe dir A Dm R root z = S := by
          unfold virtualAugFe
          rw [if_neg hzA]
          split
          · exact Finset.union_empty _
          · rw [Finset.union_singleton, Finset.insert_eq_self.2 hzS]
        rw [hset]
        exact ⟨hme, hma, hmd, hrnk, hA⟩
    · have hzFresh : z ∉ Base ∪ S := by simp [hzB, hzS]
      have hemit : z ∈ Cap →
          ∃ tau' K,
            Run B (.seq (.store "ste" (.var "u") (.lit 1)) act) tau tau' K ∧
            K ≤ Ka + 3 ∧ Marks "ste" n 1 (Base ∪ insert z S) (fun _ => 0) tau' ∧
            Acc (Base ∪ insert z S) tau' ∧
            (∀ y, y ≠ "c" → tau'.vars y = tau.vars y) ∧
            Marks "sta" n 1 A (fun _ => 0) tau' ∧
            Marks "std" n 1 Dm (fun _ => 0) tau' ∧
            tau'.arrs rk = arrOf n R := by
        intro hzc
        obtain ⟨tau', K, hr, hK, hm', hA', hfv, hfr⟩ :=
          emitBranch_run (sd := "ste") (M := Base ∪ S) ha₁ ha₂ hB1 hnB hAccSt hAcc
            hme hA hu hzn hzFresh hzc
        obtain ⟨hma', hmd', hrnk'⟩ := hkeep tau' hfr
        have hset : insert z (Base ∪ S) = Base ∪ insert z S := by
          ext y
          simp only [Finset.mem_insert, Finset.mem_union]
          tauto
        exact ⟨tau', K, hr, hK, hm'.congr hset, by
          rw [← hset]
          exact hA', hfv, hma', hmd', hrnk'⟩
      by_cases hzD : z ∈ Dm
      · by_cases hlt : dir.keep R root z
        · have hnc : ¬ (z ∈ Dm ∧ ¬ dir.keep R root z) := by simp [hlt]
          obtain ⟨tau', K, hr, hK, hme', hA', hfv, hma', hmd', hrnk'⟩ :=
            hemit (hfe (by
              unfold virtualAugFe
              rw [if_neg hzA, if_neg hnc]
              exact Finset.mem_singleton_self z))
          refine ⟨tau', _, Run.ite_true (by rw [ea]; simp [hzA])
            (Run.ite_true (by rw [ee]; simp [hzB, hzS])
              (Run.ite_false (by rw [ed]; simp [hzD])
                (Run.ite_true (by rw [elt]; simp [hlt]) hr))), ?_, ?_, hfv⟩
          · cases dir <;>
              simp only [virtualAugGuard, rankCond, size_condEq, size_condLt,
                size_get, size_var, size_lit] <;> omega
          · unfold virtualAugFe
            rw [if_neg hzA, if_neg hnc, Finset.union_singleton]
            exact ⟨hme', hma', hmd', hrnk', hA'⟩
        · refine ⟨tau, _, Run.ite_true (by rw [ea]; simp [hzA])
            (Run.ite_true (by rw [ee]; simp [hzB, hzS])
              (Run.ite_false (by rw [ed]; simp [hzD])
                (Run.ite_false (by rw [elt]; simp [hlt]) Run.skip))), ?_, ?_,
            fun _ _ => rfl⟩
          · cases dir <;>
              simp only [virtualAugGuard, rankCond, size_condEq, size_condLt,
                size_get, size_var, size_lit] <;> omega
          · unfold virtualAugFe
            rw [if_neg hzA, if_pos (⟨hzD, hlt⟩ : z ∈ Dm ∧
              ¬ dir.keep R root z), Finset.union_empty]
            exact ⟨hme, hma, hmd, hrnk, hA⟩
      · have hnc : ¬ (z ∈ Dm ∧ ¬ dir.keep R root z) := by simp [hzD]
        obtain ⟨tau', K, hr, hK, hme', hA', hfv, hma', hmd', hrnk'⟩ :=
          hemit (hfe (by
            unfold virtualAugFe
            rw [if_neg hzA, if_neg hnc]
            exact Finset.mem_singleton_self z))
        refine ⟨tau', _, Run.ite_true (by rw [ea]; simp [hzA])
          (Run.ite_true (by rw [ee]; simp [hzB, hzS])
            (Run.ite_true (by rw [ed]; simp [hzD]) hr)), ?_, ?_, hfv⟩
        · simp only [virtualAugGuard, size_condEq, size_get, size_var, size_lit]
          omega
        · unfold virtualAugFe
          rw [if_neg hzA, if_neg hnc, Finset.union_singleton]
          exact ⟨hme', hma', hmd', hrnk', hA'⟩

#print axioms virtualAugGuard_of_emits

end Lax3Proofs.Refine.OrderVirtualAugGuard
