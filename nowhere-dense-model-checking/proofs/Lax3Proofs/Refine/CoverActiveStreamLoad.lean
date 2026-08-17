import Lax3Proofs.Refine.CoverActiveStreamSort
import Lax3Proofs.RamDriverDescend

/-!
# Loading one streamed row into the cluster interface

The historical cluster load first cleared the whole carrier and then read two
offsets into the materialised cover arena.  A streamed row is already the
current cluster and occupies `idx[0..tail)`.  This module marks precisely that
prefix and emits it directly as the next depth's member list.  The entering
cluster array is zero; the fused centre loop will establish that once at level
entry and restore it by clearing the row at turn exit.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamLoad

open Lax3.ColoredGraphs
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster
open Lax3Proofs.Refine.CoverActiveStreamSort
open Lax3Proofs.Refine.MassMath (clusterAt)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ## Prefix load -/

/-- Mark and emit one member of the resident streamed row. -/
def streamLoadSlot (idx : String) (j : ℕ) : Com :=
  .seq (.store (cluName j) (.get idx (.var "p")) (.lit 1))
    (.seq (.store (memName (j + 1)) (.var "p") (.get idx (.var "p")))
      (.assign "p" (.add (.var "p") (.lit 1))))

/-- Mark `idx[0..tail)` and copy the same sorted prefix to the child's member
array.  No offset array is read, and the emitted count is the row length. -/
def streamClusterLoadCom (idx : String) (j : ℕ) : Com :=
  .seq (.assign "p" (.lit 0))
    (.seq (.while (.lt (.var "p") (.var "tail")) (streamLoadSlot idx j))
      (.assign "bq" (.var "tail")))

/-- The prefix already copied and marked by `streamClusterLoadCom`. -/
def StreamLoadInv (n na tail j : ℕ) (idx : String) (Xmem : ℕ → ℕ)
    (σ : Env) : Prop :=
  σ.vars "tail" = tail ∧ σ.vars "p" ≤ tail ∧
    σ.arrs idx = arrOf na Xmem ∧
    (∃ Mm, σ.arrs (memName (j + 1)) = arrOf n Mm ∧
      ∀ k, k < σ.vars "p" → Mm k = Xmem k) ∧
    ∃ Xa, σ.arrs (cluName j) = arrOf n Xa ∧
      (∀ k, k < n → Xa k ≤ 1) ∧
      ∀ k, k < n → (Xa k ≠ 0 ↔ ∃ p, p < σ.vars "p" ∧ Xmem p = k)

/-- The streamed load costs one constant-sized body per row member. -/
def streamClusterLoadCost (tail : ℕ) : ℕ := 24 * tail + 8

/-- Loading a zero cluster array from a sorted streamed prefix produces its
exact indicator and the exact increasing child member enumeration.  Every
executed row address is below `tail ≤ n < B`. -/
theorem streamClusterLoadCom_spec {B n na tail j : ℕ} {Xmem : ℕ → ℕ}
    (idx : String) (hidxClu : idx ≠ cluName j)
    (hidxMem : idx ≠ memName (j + 1))
    (hcluMem : cluName j ≠ memName (j + 1))
    (hB : 1 < B) (hnB : n < B) (htail : tail ≤ n) (hfit : tail ≤ na)
    (hmem : ∀ p < tail, Xmem p < n)
    (hmono : ∀ p p', p < p' → p' < tail → Xmem p < Xmem p') :
    Spec B
      (fun σ => σ.vars "tail" = tail ∧ σ.arrs idx = arrOf na Xmem ∧
        σ.arrs (cluName j) = arrOf n (fun _ => 0) ∧
        ∃ Mm, σ.arrs (memName (j + 1)) = arrOf n Mm)
      (streamClusterLoadCom idx j)
      (fun _ σ' => ∃ Xa Mm,
        σ'.arrs (cluName j) = arrOf n Xa ∧
        (∀ k, k < n → Xa k ≤ 1) ∧
        markSet n Xa = {v : Fin n | ∃ p, p < tail ∧ Xmem p = (v : ℕ)} ∧
        σ'.arrs (memName (j + 1)) = arrOf n Mm ∧
        σ'.vars "bq" = tail ∧ MemEnum n tail Mm Xa)
      (streamClusterLoadCost tail) := by
  classical
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨htailVar, hidxArr, hcluArr, Mm₀, hmemArr⟩ := hσ
  have htailB : tail < B := lt_of_le_of_lt htail hnB
  let σ₀ := σ.setVar "p" 0
  have r₀ : Run B (.assign "p" (.lit 0)) σ σ₀ 2 :=
    Run.assign (evalB_lit (by omega))
  have hI₀ : StreamLoadInv n na tail j idx Xmem σ₀ := by
    refine ⟨by simp [σ₀, htailVar], by simp [σ₀], by simp [σ₀, hidxArr],
      ⟨Mm₀, by simp [σ₀, hmemArr], ?_⟩,
      fun _ => 0, by simp [σ₀, hcluArr], ?_, ?_⟩
    · intro k hk
      simp [σ₀] at hk
    · intro k hk
      simp
    · intro k hk
      simp [σ₀]
  have hstep : ∀ ρ : Env, StreamLoadInv n na tail j idx Xmem ρ →
      ρ.vars "p" < tail →
      ∃ ρ' K', Run B (streamLoadSlot idx j) ρ ρ' K' ∧
        StreamLoadInv n na tail j idx Xmem ρ' ∧
        ρ'.vars "p" = ρ.vars "p" + 1 ∧ K' ≤ 20 := by
    intro ρ hI hp
    obtain ⟨htailρ, hple, hidxρ, ⟨Mm, hMmArr, hMmVal⟩,
      Xa, hXaArr, hXaBit, hXaVal⟩ := hI
    have hpna : ρ.vars "p" < na := lt_of_lt_of_le hp hfit
    have hpn : ρ.vars "p" < n := lt_of_lt_of_le hp htail
    have hpB : ρ.vars "p" < B := lt_trans hpn hnB
    have hp1B : ρ.vars "p" + 1 < B := by omega
    have hXmN : Xmem (ρ.vars "p") < n := hmem _ hp
    have hXmB : Xmem (ρ.vars "p") < B := lt_trans hXmN hnB
    have hpEval : (Expr.var "p").evalB B ρ = some (ρ.vars "p") :=
      evalB_var hpB
    have hidxEval : (Expr.get idx (.var "p")).evalB B ρ =
        some (Xmem (ρ.vars "p")) :=
      evalB_get hpEval (by rw [hidxρ, getElem?_arrOf Xmem hpna]) hXmB
    have hcluLen : Xmem (ρ.vars "p") < (ρ.arrs (cluName j)).length := by
      rw [hXaArr, length_arrOf]
      exact hXmN
    set ρ₁ := ρ.setArr (cluName j) (Xmem (ρ.vars "p")) 1 with hρ₁
    have r₁ : Run B (.store (cluName j) (.get idx (.var "p")) (.lit 1)) ρ ρ₁ 5 :=
      (Run.store hidxEval (evalB_lit (by omega)) hcluLen).mono (by simp [Expr.size])
    have hp₁ : ρ₁.vars "p" = ρ.vars "p" := by simp [ρ₁]
    have hpEval₁ : (Expr.var "p").evalB B ρ₁ = some (ρ.vars "p") := by
      have h := evalB_var (B := B) (x := "p") (σ := ρ₁) (by rw [hp₁]; exact hpB)
      rwa [hp₁] at h
    have hidxEval₁ : (Expr.get idx (.var "p")).evalB B ρ₁ =
        some (Xmem (ρ.vars "p")) := by
      refine evalB_get hpEval₁ ?_ hXmB
      rw [hρ₁, arrs_setArr, if_neg hidxClu, hidxρ,
        getElem?_arrOf Xmem hpna]
    have hmemLen : ρ.vars "p" < (ρ₁.arrs (memName (j + 1))).length := by
      rw [hρ₁, arrs_setArr, if_neg (Ne.symm hcluMem), hMmArr, length_arrOf]
      exact hpn
    set ρ₂ := ρ₁.setArr (memName (j + 1)) (ρ.vars "p") (Xmem (ρ.vars "p")) with hρ₂
    have r₂ : Run B
        (.store (memName (j + 1)) (.var "p") (.get idx (.var "p"))) ρ₁ ρ₂ 5 :=
      (Run.store hpEval₁ hidxEval₁ hmemLen).mono (by simp [Expr.size])
    have hp₂ : ρ₂.vars "p" = ρ.vars "p" := by simp [ρ₂, hp₁]
    have hpEval₂ : (Expr.var "p").evalB B ρ₂ = some (ρ.vars "p") := by
      have h := evalB_var (B := B) (x := "p") (σ := ρ₂) (by rw [hp₂]; exact hpB)
      rwa [hp₂] at h
    have hpInc : (Expr.add (.var "p") (.lit 1)).evalB B ρ₂ =
        some (ρ.vars "p" + 1) :=
      evalB_bin hpEval₂ (evalB_lit (by omega)) (by simpa using hp1B)
    set ρ₃ := ρ₂.setVar "p" (ρ.vars "p" + 1) with hρ₃
    have r₃ : Run B (.assign "p" (.add (.var "p") (.lit 1))) ρ₂ ρ₃ 4 :=
      (Run.assign hpInc).mono (by simp [Expr.size])
    have hp₃ : ρ₃.vars "p" = ρ.vars "p" + 1 := by simp [ρ₃]
    have hrun : Run B (streamLoadSlot idx j) ρ ρ₃ 14 := by
      exact r₁.seq (r₂.seq r₃)
    refine ⟨ρ₃, 14, hrun, ?_, hp₃, by omega⟩
    refine ⟨?_, by rw [hp₃]; omega, ?_,
      ⟨upd Mm (ρ.vars "p") (Xmem (ρ.vars "p")), ?_, ?_⟩,
      upd Xa (Xmem (ρ.vars "p")) 1, ?_, ?_, ?_⟩
    · simp [hρ₃, hρ₂, hρ₁, htailρ]
    · rw [hρ₃, arrs_setVar, hρ₂, arrs_setArr,
        if_neg hidxMem, hρ₁, arrs_setArr,
        if_neg hidxClu]
      exact hidxρ
    · rw [hρ₃, arrs_setVar, hρ₂, arrs_setArr, if_pos rfl,
        hρ₁, arrs_setArr, if_neg (Ne.symm hcluMem), hMmArr,
        set_arrOf_eq_upd]
    · intro k hk
      rw [hp₃] at hk
      by_cases hkp : k = ρ.vars "p"
      · rw [hkp, upd_self]
      · rw [upd_of_ne _ hkp]
        exact hMmVal k (by omega)
    · rw [hρ₃, arrs_setVar, hρ₂, arrs_setArr, if_neg hcluMem,
        hρ₁, arrs_setArr, if_pos rfl, hXaArr, set_arrOf_eq_upd]
    · intro k hk
      by_cases hke : k = Xmem (ρ.vars "p")
      · rw [hke, upd_self]
      · rw [upd_of_ne _ hke]
        exact hXaBit k hk
    · intro k hk
      rw [hp₃]
      by_cases hke : k = Xmem (ρ.vars "p")
      · rw [hke, upd_self]
        exact ⟨fun _ => ⟨ρ.vars "p", by omega, rfl⟩, fun _ => one_ne_zero⟩
      · rw [upd_of_ne _ hke, hXaVal k hk]
        constructor
        · rintro ⟨p, hp' , hpv⟩
          exact ⟨p, by omega, hpv⟩
        · rintro ⟨p, hp', hpv⟩
          rcases Nat.lt_or_ge p (ρ.vars "p") with hlt | hge
          · exact ⟨p, hlt, hpv⟩
          · have hpeq : p = ρ.vars "p" := by omega
            exact absurd (by rw [← hpv, hpeq]) hke
  obtain ⟨σ₁, r₁, hI₁, hp₁⟩ :=
    (Csr.rowScan_spec
      (P := fun ρ => StreamLoadInv n na tail j idx Xmem ρ ∧ ρ.vars "p" = 0)
      B (24 * tail + 4) tail 20 "p" "tail"
      (streamLoadSlot idx j) (StreamLoadInv n na tail j idx Xmem) htailB
      (fun ρ hρ => ⟨hρ.1, hρ.2.1⟩) hstep
      (fun _ h => h.1) (fun _ h => by rw [h.2]; omega)).run ⟨hI₀, by simp [σ₀]⟩
  obtain ⟨htail₁, -, hidx₁, ⟨Mm, hMmArr, hMmVal⟩,
    Xa, hXaArr, hXaBit, hXaVal⟩ := hI₁
  rw [hp₁] at hMmVal hXaVal
  have tailEval : (Expr.var "tail").evalB B σ₁ = some tail := by
    have h := evalB_var (B := B) (x := "tail") (σ := σ₁) (by rw [htail₁]; exact htailB)
    rwa [htail₁] at h
  let σ₂ := σ₁.setVar "bq" tail
  have r₂ : Run B (.assign "bq" (.var "tail")) σ₁ σ₂ 2 :=
    Run.assign tailEval
  refine ⟨σ₂, 2 + ((24 * tail + 4) + 2), r₀.seq (r₁.seq r₂), ?_,
    Xa, Mm, ?_, hXaBit, ?_, ?_, ?_, ?_⟩
  · simp only [streamClusterLoadCost]
    omega
  · simpa [σ₂] using hXaArr
  · ext v
    rw [mem_markSet, Set.mem_setOf_eq, hXaVal (v : ℕ) v.isLt]
  · simpa [σ₂] using hMmArr
  · simp [σ₂]
  · refine ⟨?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [hMmVal k hk]
      exact hmem k hk
    · intro i k hik hk
      rw [hMmVal i (by omega), hMmVal k hk]
      exact hmono i k hik hk
    · intro k hk
      rw [hMmVal k hk, hXaVal (Xmem k) (hmem k hk)]
      exact ⟨k, hk, rfl⟩
    · intro a ha hXa
      obtain ⟨p, hp, hpv⟩ := (hXaVal a ha).mp hXa
      exact ⟨p, hp, (hMmVal p hp).trans hpv⟩

/-! ## Driver-facing streamed row -/

/-- The loaded row retains the sorted streamed state and supplies the exact
cluster indicator and child member enumeration used by descent.  Here `A₀`
is the ambient level arena stored at `alvName j`; `M` is the progressively
depleted cover-search mask stored in the streamed scratch array `"alv"`.
Keeping both arrays explicit prevents the descent from accidentally using
the already-depleted search mask as its arena. -/
structure StreamLoadOut {n : ℕ} (B ns nt na q cap j c tail bits : ℕ)
    (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre O T Xmem asg M Xa Mm : ℕ → ℕ) (σ : Env) : Prop where
  sorted : StreamSortedOut B ns nt na q cap c tail bits G A₀ π centre O T Xmem asg M σ
  ambient_arr : σ.arrs (alvName j) = arrOf n A₀
  ambient_bound : ∀ k, k < n → A₀ k < B
  cluster_arr : σ.arrs (cluName j) = arrOf n Xa
  cluster_bit : ∀ k, k < n → Xa k ≤ 1
  cluster_set : markSet n Xa = clusterAt G A₀ π centre cap c
  member_arr : σ.arrs (memName (j + 1)) = arrOf n Mm
  member_count : σ.vars "bq" = tail
  member_enum : MemEnum n tail Mm Xa

/-- The exact streamed row discharges the first executable operation of the
descent, without restoring either a carrier clear or an offset load. -/
theorem streamClusterLoadStep
    {B n ns nt na q cap j c tail bits : ℕ}
    {G : SimpleGraph (Fin n)} {A₀ O T centre Xmem asg M : ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} (hB : 1 < B) (hnB : n < B)
    (hA₀B : ∀ k, k < n → A₀ k < B) :
    Spec B
      (fun σ =>
        StreamSortedOut B ns nt na q cap c tail bits G A₀ π centre O T Xmem asg M σ ∧
        σ.arrs (alvName j) = arrOf n A₀ ∧
        σ.arrs (cluName j) = arrOf n (fun _ => 0) ∧
        ∃ Mm, σ.arrs (memName (j + 1)) = arrOf n Mm)
      (streamClusterLoadCom "xmem" j)
      (fun _ σ' => ∃ Xa Mm,
        StreamLoadOut B ns nt na q cap j c tail bits G A₀ π centre O T Xmem asg M Xa Mm σ')
      (streamClusterLoadCost tail) := by
  intro σ hσ
  obtain ⟨hsorted, hambient, hclu, hmemArr⟩ := hσ
  have hidxClu : "xmem" ≠ cluName j := by simp [cluName, String.ext_iff]
  have hidxMem : "xmem" ≠ memName (j + 1) := by simp [memName, String.ext_iff]
  have hcluMem : cluName j ≠ memName (j + 1) := by simp [cluName, memName, String.ext_iff]
  obtain ⟨σ', hr, ⟨Xa, Mm, hXa, hXabit, hXaset, hMm, hbq, henum⟩,
      hfv, hfa, -, -⟩ :=
    ((streamClusterLoadCom_spec "xmem" hidxClu hidxMem hcluMem
      hB hnB
      hsorted.row.tail_le (hsorted.row.tail_le.trans hsorted.row_fit)
      hsorted.row.mem_lt hsorted.row.block_mono).frame).run
      ⟨hsorted.tail_var, hsorted.row_arr, hclu, hmemArr⟩
  have hav : ∀ a : String, a ≠ cluName j → a ≠ memName (j + 1) →
      σ'.arrs a = σ.arrs a := by
    intro a hclu' hmem'
    apply hfa a
    simp [streamClusterLoadCom, streamLoadSlot, Com.warrs, hclu', hmem']
  have hvv : ∀ y : String, y ≠ "p" → y ≠ "bq" → σ'.vars y = σ.vars y := by
    intro y hp hbq'
    apply hfv y
    simp [streamClusterLoadCom, streamLoadSlot, Com.wvars, hp, hbq']
  have hsorted' :
      StreamSortedOut B ns nt na q cap c tail bits G A₀ π centre O T Xmem asg M σ' := by
    refine ⟨hsorted.row,
      (hvv "n" (by decide) (by decide)).trans hsorted.n_var,
      (hvv "qn" (by decide) (by decide)).trans hsorted.q_var,
      (hvv "c" (by decide) (by decide)).trans hsorted.centre_var,
      (hvv "xp" (by decide) (by decide)).trans hsorted.pointer_var,
      (hvv "tail" (by decide) (by decide)).trans hsorted.tail_var,
      (hvv "rsbits" (by decide) (by decide)).trans hsorted.bits_var,
      (hav "ord" (by simp [cluName, String.ext_iff])
        (by simp [memName, String.ext_iff])).trans hsorted.centre_arr,
      (hav "off" (by simp [cluName, String.ext_iff])
        (by simp [memName, String.ext_iff])).trans hsorted.off_arr,
      (hav "tgt" (by simp [cluName, String.ext_iff])
        (by simp [memName, String.ext_iff])).trans hsorted.target_arr,
      (hav "alv" (by simp [cluName, String.ext_iff])
        (by simp [memName, String.ext_iff])).trans hsorted.mask_arr,
      (hav "xmem" (by simp [cluName, String.ext_iff])
        (by simp [memName, String.ext_iff])).trans hsorted.row_arr,
      hsorted.row_fit,
      (hav "asg" (by simp [cluName, String.ext_iff])
        (by simp [memName, String.ext_iff])).trans hsorted.asg_arr, ?_, ?_, ?_,
      hsorted.mask_bound⟩
    · apply Lax3Proofs.Refine.CoverActiveTurn.distClean_of_arrs_eq hsorted.dist_clean
      exact hav "dist" (by simp [cluName, String.ext_iff])
        (by simp [memName, String.ext_iff])
    · obtain ⟨Q, hQ⟩ := hsorted.queue_arr
      exact ⟨Q, (hav "q" (by simp [cluName, String.ext_iff])
        (by simp [memName, String.ext_iff])).trans hQ⟩
    · obtain ⟨QD, hQD⟩ := hsorted.qdist_arr
      exact ⟨QD, (hav "qd" (by simp [cluName, String.ext_iff])
        (by simp [memName, String.ext_iff])).trans hQD⟩
  refine ⟨σ', hr, Xa, Mm, hsorted',
    (hav (alvName j) (by simp [alvName, cluName, String.ext_iff])
      (by simp [alvName, memName, String.ext_iff])).trans hambient,
    hA₀B, hXa, hXabit, ?_, hMm, hbq, henum⟩
  ext v
  rw [hXaset]
  exact hsorted.row.block (v : ℕ)

/-! ## Frames and audit -/

theorem noWrite_streamClusterLoadCom (idx : String) (j : ℕ) :
    (streamClusterLoadCom idx j).NoWrite := by
  simp [streamClusterLoadCom, streamLoadSlot, Com.NoWrite]

#print axioms streamClusterLoadCom_spec
#print axioms streamClusterLoadStep

end Lax3Proofs.Refine.CoverActiveStreamLoad
