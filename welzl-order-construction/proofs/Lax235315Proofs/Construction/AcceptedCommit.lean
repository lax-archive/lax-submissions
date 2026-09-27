import Lax235315Proofs.Construction.RoundInvariant
import Lax235315Proofs.Construction.CommitSource

/-! The literal accepted-round commit preserves the reduction frontier.
Its log allocation follows from cardinality conservation, and its round index
fits the workspace by the proved logarithmic shrinking bound. -/

namespace Lax235315Proofs.Construction.AcceptedCommit
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.DriverSetup
open Lax235315Proofs.Construction.SourceBounds
open Lax235315Proofs.Construction.BitArrays
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.RoundInvariant
open Lax235315Proofs.Construction.ActiveBookkeeping
open Lax235315Proofs.Construction.CommitSource
open Lax235315Proofs.Construction.RecordRemovedSource
open Lax235315Proofs.Construction.RadixEight

lemma view_bits {a : String} {σ : Env} (h : ArrayBits a σ) (i : ℕ) :
    view σ a i ≤ 1 := by
  by_cases hi : i < (σ.arrs a).length
  · apply h
    simp only [view, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]
    exact List.getElem_mem hi
  · have he : (σ.arrs a)[i]? = none := List.getElem?_eq_none (by omega)
    simp [view, List.getD_eq_getElem?_getD, he]

lemma active_of_array {n : ℕ} {a : String} {σ : Env} {f : ℕ → ℕ}
    (ha : σ.arrs a = arrOf n f) :
    activeVertices n (view σ a) = activeVertices n f := by
  ext i
  simp only [mem_activeVertices]
  exact ⟨fun ⟨hi, hv⟩ => ⟨hi, (view_of_array ha hi).symm.trans hv⟩,
    fun ⟨hi, hv⟩ => ⟨hi, (view_of_array ha hi).trans hv⟩⟩

lemma bits_of_array {n : ℕ} {a : String} {σ : Env} {f : ℕ → ℕ}
    (ha : σ.arrs a = arrOf n f) (hbits : ∀ i < n, f i ≤ 1) :
    ArrayBits a σ := by
  intro v hv
  rw [ha] at hv
  simp only [arrOf, List.mem_map, List.mem_range] at hv
  obtain ⟨i, hi, rfl⟩ := hv
  exact hbits i hi

lemma workspace_commit {B C c n : ℕ} {x : List ℕ} {σ σ' : Env}
    (h : Workspace B c n x σ) (hr : Run B commitReduction σ σ' C) :
    Workspace B c n x σ' := by
  refine ⟨SourceBounds.run_preserves hr h.bounded,
    (hr.frame_var "c" (by decide)).trans h.parameter,
    (hr.frame_var "n" (by decide)).trans h.vertices,
    (hr.frame_var "m" (by decide)).trans h.edges,
    (hr.frame_var "L" (by decide)).trans h.logarithm,
    (hr.frame_var "qpow" (by decide)).trans h.radixSize,
    (hr.frame_arr "off" (by decide)).trans h.offsets,
    (hr.frame_arr "tgt" (by decide)).trans h.targets,
    fun a => (run_array_length_eq hr a).trans (h.lengths a),
    inputBits_run hr h.randomInput, ?_⟩
  exact (hr.out_eq (by decide)).trans h.output

/-- Executing the accepted commit needs no separate capacity oracle: the
frontier itself supplies space for all deletions and the next round record. -/
lemma frontier_commit_run {B c n : ℕ} {x : List ℕ} {σ : Env}
    (h : Frontier B c n x σ) (hc : 1 ≤ c) (hn : 1 < n) (hnB : n < B)
    (hlarge : 12 * c ^ 2 * Nat.clog 2 n < σ.vars "acount")
    (hnextCount : σ.vars "nextACount" =
      (activeVertices n (view σ "nextA")).card)
    (hsub : activeVertices n (view σ "nextA") ⊆
      activeVertices n (view σ "activeA"))
    (hneA : (activeVertices n (view σ "nextA")).Nonempty)
    (hneB : (activeVertices n (view σ "nextB")).Nonempty)
    (hshrink : (activeVertices n (view σ "nextA")).card ≤
      σ.vars "acount" / 2 + c ^ 2) :
    ∃ σ', Run B commitReduction σ σ' (80 * (n + 1)) ∧
      Frontier B c n x σ' ∧
      σ'.vars "round" = σ.vars "round" + 1 ∧
      σ'.vars "acount" = σ.vars "nextACount" := by
  have hround := h.shrinking.rounds_succ_le_clog hc hn
  have hlog := clog_le_vertices n
  have hconserve := deleted_active_conservation
    (fun i _ => view_bits h.nextABits i) hsub
    (by rw [← h.activeCount]; exact h.conservation)
  have arr (a : String) (h₁ : a ≠ "off") (h₂ : a ≠ "tgt") (h₃ : a ≠ "count") :=
    h.workspace.vertex_array h₁ h₂ h₃
  obtain ⟨σ', rem, remRep, hr, ha, hb, hround', hacount, hremoved,
      hstart, hend, hrem, hrep, hprefix, hsuffix, hprefixRep, hsuffixRep⟩ :=
    commitReduction_run h.workspace.vertices rfl rfl
      (arr "activeA" (by decide) (by decide) (by decide))
      (arr "activeB" (by decide) (by decide) (by decide))
      (arr "nextA" (by decide) (by decide) (by decide))
      (arr "nextB" (by decide) (by decide) (by decide))
      (arr "repA" (by decide) (by decide) (by decide))
      (arr "removed" (by decide) (by decide) (by decide))
      (arr "removedRep" (by decide) (by decide) (by decide))
      (by rw [h.workspace.lengths]; change σ.vars "round" < n; omega)
      (by rw [h.workspace.lengths]; change σ.vars "round" < n; omega)
      hnB (by omega) h.workspace.bounded (by omega)
  have haSet := active_of_array ha
  have hbSet := active_of_array hb
  refine ⟨σ', hr, ?_, hround', hacount⟩
  refine ⟨workspace_commit h.workspace hr,
    (hr.frame_var "good" (by decide)).trans h.success,
    ?_, ?_, ?_, bits_of_array ha (fun i _ => view_bits h.nextABits i),
    bits_of_array hb (fun i _ => view_bits h.nextBBits i),
    BitArrays.run_preserves hr (by decide) h.nextABits,
    BitArrays.run_preserves hr (by decide) h.nextBBits, ?_, ?_⟩
  · rw [hacount, hnextCount, haSet]
  · intro _; rwa [haSet]
  · intro _; rwa [hbSet]
  · rw [hremoved, hacount, hnextCount]
    exact hconserve
  · rw [hround', hacount, hnextCount]
    exact h.shrinking.step hlarge hshrink

end Lax235315Proofs.Construction.AcceptedCommit
