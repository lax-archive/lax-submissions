import Lax3Proofs.Refine.CoverActiveStreamBatch

/-!
# Filtering the child members of one streamed cover row

The streamed cluster loader initially places the whole cluster in the child
member array.  Once the exact child and game masks have been written, this
module runs the verified stable member filter on that resident row.  The
result is the complete `BatchData` interface expected by the cluster
enumerator, while the batch remains supported on the row for its later
release.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamChild

open Lax3.ColoredGraphs
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster
open Lax3Proofs.RamDriverDescend
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.Refine.CoverActiveStreamSort
open Lax3Proofs.Refine.CoverActiveStreamLoad
open Lax3Proofs.Refine.CoverActiveStreamMask
open Lax3Proofs.Refine.CoverActiveStreamBatch
open Lax3Proofs.Refine.MassMath (clusterAt)
open Lax13Proofs.Imp Lax13Proofs.Reasoning

/-! ## Program and exported state -/

/-- Materialise the exact child/game masks, then stably filter the cluster's
resident member row by the child mask. -/
def streamChildFilterCom (j : ℕ) : Com :=
  .seq (streamChildGameCom j) (memFilterCom (j + 1))

/-- Two sparse mask passes followed by one stable pass over the same row. -/
def streamChildFilterCost (tail : ℕ) : ℕ :=
  streamChildGameCost tail + (23 * tail + 8)

theorem streamChildFilterCost_eq (tail : ℕ) :
    streamChildFilterCost tail = 66 * tail + 24 := by
  simp [streamChildFilterCost, streamChildGameCost]
  ring

/-- Driver-facing state after the streamed child masks and member filter.
`masks` retains the exact sparse arrays and their row support; `batch` is the
ordinary descent interface over the ambient arena `A₀`, now with an exact
child member enumeration.  The separate `M` parameter remains the
progressively depleted cover-search mask carried by `sorted`. -/
structure StreamChildOut {n : ℕ} (B ns nt na q cap j c tail bits : ℕ)
    (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre O T Xmem asg M Xa Mm Ra Wa Gm Alv Gam Mem : ℕ → ℕ)
    (mm : ℕ) (σ : Env) : Prop where
  sorted : StreamSortedOut B ns nt na q cap c tail bits G A₀ π centre O T
    Xmem asg M σ
  masks : StreamChildGameOut B na tail j G Xmem A₀ Xa Ra Wa Gm Alv Gam σ
  cluster_set : markSet n Xa = clusterAt G A₀ π centre cap c
  cluster_members : MemEnum n tail Mm Xa
  row_scan_count : σ.vars "bq" = tail
  child_member_arr : σ.arrs (memName (j + 1)) = arrOf n Mem
  child_member_count : σ.vars (mnumName (j + 1)) = mm
  child_member_enum : MemEnum n mm Mem Alv
  child_member_bound : ∀ z, z < mm → Mem z < B
  retained_graph : masked G Ra =
    Lax12.UniformQuasiWideness.deleteVerts (masked G A₀) (markSet n Xa)ᶜ
  batch : BatchData n j B G A₀ (markSet n Xa) (markSet n Wa) Alv Gam σ

/-! ## Small frame facts -/

theorem childGame_frame_arr {j : ℕ} {a : String}
    (ha : a ≠ alvName (j + 1)) (hg : a ≠ gamName (j + 1)) :
    a ∉ (streamChildGameCom j).warrs := by
  simp [streamChildGameCom, streamBlockSubCom, streamBlockAndSubCom,
    streamBlockMapCom, BlockLeaves.blockMapRangeCom, Com.warrs, ha, hg]

theorem childGame_frame_var {j : ℕ} {y : String}
    (hp : y ≠ "p") (he : y ≠ "pend") (hc : y ≠ "cw") :
    y ∉ (streamChildGameCom j).wvars := by
  simp [streamChildGameCom, streamBlockSubCom, streamBlockAndSubCom,
    streamBlockMapCom, BlockLeaves.blockMapRangeCom, Com.wvars, hp, he, hc]

/-! ## Exact composition -/

/-- **The streamed child interface.**  The loader's sorted cluster row is
filtered in place after the exact child/game maps.  Completeness of the
resulting member list follows because the child point equation implies that
every child vertex is a cluster vertex, and the loader enumerated every
cluster vertex.  The complete operation costs exactly `66·tail+24`; it has
no carrier scan, offset table, or allocation-width equality premise. -/
theorem streamChildFilterStep
    {B n ns nt na q cap j c tail bits : ℕ}
    {G : SimpleGraph (Fin n)}
    {A₀ O T centre Xmem asg M Xa Mm Ra Wa Gm : ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} (h1B : 1 < B) (hnB : n < B)
    (hWaB : ∀ v, v < n → Wa v < B) (hGmB : ∀ v, v < n → Gm v < B)
    (hWaSup : BlockSupported n 0 tail Xmem Wa) :
    Spec B
      (fun σ =>
        StreamRetainOut B ns nt na q cap j c tail bits G A₀ π centre O T
          Xmem asg M Xa Mm Ra σ ∧
        σ.arrs (batName j) = arrOf n Wa ∧
        σ.arrs (gamName j) = arrOf n Gm ∧
        σ.arrs (alvName (j + 1)) = arrOf n (fun _ => 0) ∧
        σ.arrs (gamName (j + 1)) = arrOf n (fun _ => 0))
      (streamChildFilterCom j)
      (fun _ σ' => ∃ Alv Gam Mem mm,
        StreamChildOut B ns nt na q cap j c tail bits G A₀ π centre O T
          Xmem asg M Xa Mm Ra Wa Gm Alv Gam Mem mm σ')
      (streamChildFilterCost tail) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hret, hbat, hgam, halv₀, hgam₀⟩ := hσ
  obtain ⟨σ₁, hr₁, ⟨Alv, Gam, hmasks₁⟩, hfv₁, hfa₁, -, -⟩ :=
    ((streamChildGameStep (G := G) h1B hnB hWaB hGmB hWaSup).frame).run
      (σ := σ) ⟨hret, hbat, hgam, halv₀, hgam₀⟩
  have hav₁ : ∀ a : String, a ≠ alvName (j + 1) →
      a ≠ gamName (j + 1) → σ₁.arrs a = σ.arrs a := by
    intro a ha hg
    exact hfa₁ a (childGame_frame_arr ha hg)
  have hvv₁ : ∀ y : String, y ≠ "p" → y ≠ "pend" → y ≠ "cw" →
      σ₁.vars y = σ.vars y := by
    intro y hp he hc
    exact hfv₁ y (childGame_frame_var hp he hc)
  have hmem₁ : σ₁.arrs (memName (j + 1)) = arrOf n Mm := by
    rw [hav₁ _ (by simp [memName, alvName, String.ext_iff])
      (by simp [memName, gamName, String.ext_iff])]
    exact hret.loaded.member_arr
  have hbq₁ : σ₁.vars "bq" = tail := by
    rw [hvv₁ "bq" (by decide) (by decide) (by decide)]
    exact hret.loaded.member_count
  have hAlvXa : ∀ a, a < n → Alv a ≠ 0 → Xa a ≠ 0 := by
    intro a ha hAa
    exact (hmasks₁.child_point ⟨a, ha⟩).mp hAa |>.2.1
  obtain ⟨σ₂, hr₂, ⟨Mem, mm, hmem₂, hmm₂, hMemE, hMemB⟩,
      hfv₂, hfa₂, -, -⟩ :=
    ((memFilter_spec (j := j + 1) (bs := tail) (Mm := Mm) (A := Alv)
      hnB hret.loaded.member_enum.card_le hret.loaded.member_enum.1
      hret.loaded.member_enum.2.1 hmasks₁.child_bound
      (fun a ha hAa => hret.loaded.member_enum.2.2.2 a ha
        (hAlvXa a ha hAa))).frame).run (σ := σ₁)
      ⟨hmem₁, hbq₁, hmasks₁.child_arr⟩
  have hav₂ : ∀ a : String, a ≠ memName (j + 1) →
      σ₂.arrs a = σ₁.arrs a := by
    intro a ha
    exact hfa₂ a (by rw [RamDriverFrames.warrs_memFilterCom]; simp [ha])
  have hvv₂ : ∀ y : String, y ≠ "mk" → y ≠ mnumName (j + 1) →
      y ≠ "mv" → σ₂.vars y = σ₁.vars y := by
    intro y hmk hmm hmv
    exact hfv₂ y (by
      rw [RamDriverFrames.wvars_memFilterCom]
      simp [hmk, hmm, hmv])
  have hmasks₂ :
      StreamChildGameOut B na tail j G Xmem A₀ Xa Ra Wa Gm Alv Gam σ₂ := by
    exact {
      tail_var := (hvv₂ "tail" (by decide)
        (by simp [mnumName, String.ext_iff]) (by decide)).trans hmasks₁.tail_var
      row_arr := (hav₂ "xmem" (by
        simp [memName, String.ext_iff])).trans hmasks₁.row_arr
      retained_arr := (hav₂ (resName j) (by
        simp [resName, memName, String.ext_iff])).trans hmasks₁.retained_arr
      cluster_arr := (hav₂ (cluName j) (by
        simp [cluName, memName, String.ext_iff])).trans hmasks₁.cluster_arr
      batch_arr := (hav₂ (batName j) (by
        simp [batName, memName, String.ext_iff])).trans hmasks₁.batch_arr
      batch_supported := hmasks₁.batch_supported
      parent_game_arr := (hav₂ (gamName j) (by
        simp [gamName, memName, String.ext_iff])).trans hmasks₁.parent_game_arr
      child_arr := (hav₂ (alvName (j + 1)) (by
        simp [alvName, memName, String.ext_iff])).trans hmasks₁.child_arr
      child_val := hmasks₁.child_val
      child_bound := hmasks₁.child_bound
      child_supported := hmasks₁.child_supported
      child_graph := hmasks₁.child_graph
      child_point := hmasks₁.child_point
      game_arr := (hav₂ (gamName (j + 1)) (by
        simp [gamName, memName, String.ext_iff])).trans hmasks₁.game_arr
      game_val := hmasks₁.game_val
      game_bound := hmasks₁.game_bound
      game_supported := hmasks₁.game_supported
      game_graph := hmasks₁.game_graph
    }
  have hrun : Run B (streamChildFilterCom j) σ σ₂
      (streamChildGameCost tail + (23 * tail + 8)) := hr₁.seq hr₂
  have hav : ∀ a : String, a ≠ alvName (j + 1) →
      a ≠ gamName (j + 1) → a ≠ memName (j + 1) →
      σ₂.arrs a = σ.arrs a := by
    intro a ha hg hm
    exact (hav₂ a hm).trans (hav₁ a ha hg)
  have hvv : ∀ y : String, y ≠ "p" → y ≠ "pend" → y ≠ "cw" →
      y ≠ "mk" → y ≠ mnumName (j + 1) → y ≠ "mv" →
      σ₂.vars y = σ.vars y := by
    intro y hp he hc hmk hmm hmv
    exact (hvv₂ y hmk hmm hmv).trans (hvv₁ y hp he hc)
  have hsorted₂ :
      StreamSortedOut B ns nt na q cap c tail bits G A₀ π centre O T Xmem asg M σ₂ := by
    refine ⟨hret.loaded.sorted.row,
      (hvv "n" (by decide) (by decide) (by decide) (by decide)
        (by simp [mnumName, String.ext_iff]) (by decide)).trans
          hret.loaded.sorted.n_var,
      (hvv "qn" (by decide) (by decide) (by decide) (by decide)
        (by simp [mnumName, String.ext_iff]) (by decide)).trans
          hret.loaded.sorted.q_var,
      (hvv "c" (by decide) (by decide) (by decide) (by decide)
        (by simp [mnumName, String.ext_iff]) (by decide)).trans
          hret.loaded.sorted.centre_var,
      (hvv "xp" (by decide) (by decide) (by decide) (by decide)
        (by simp [mnumName, String.ext_iff]) (by decide)).trans
          hret.loaded.sorted.pointer_var,
      hmasks₂.tail_var,
      (hvv "rsbits" (by decide) (by decide) (by decide) (by decide)
        (by simp [mnumName, String.ext_iff]) (by decide)).trans
          hret.loaded.sorted.bits_var,
      (hav "ord" (by simp [alvName, String.ext_iff])
        (by simp [gamName, String.ext_iff])
        (by simp [memName, String.ext_iff])).trans hret.loaded.sorted.centre_arr,
      (hav "off" (by simp [alvName, String.ext_iff])
        (by simp [gamName, String.ext_iff])
        (by simp [memName, String.ext_iff])).trans hret.loaded.sorted.off_arr,
      (hav "tgt" (by simp [alvName, String.ext_iff])
        (by simp [gamName, String.ext_iff])
        (by simp [memName, String.ext_iff])).trans hret.loaded.sorted.target_arr,
      (hav "alv" (by simp [alvName, String.ext_iff])
        (by simp [gamName, String.ext_iff])
        (by simp [memName, String.ext_iff])).trans hret.loaded.sorted.mask_arr,
      hmasks₂.row_arr, hret.loaded.sorted.row_fit,
      (hav "asg" (by simp [alvName, String.ext_iff])
        (by simp [gamName, String.ext_iff])
        (by simp [memName, String.ext_iff])).trans hret.loaded.sorted.asg_arr,
      ?_, ?_, ?_, hret.loaded.sorted.mask_bound⟩
    · apply Lax3Proofs.Refine.CoverActiveTurn.distClean_of_arrs_eq
        hret.loaded.sorted.dist_clean
      exact hav "dist" (by simp [alvName, String.ext_iff])
        (by simp [gamName, String.ext_iff])
        (by simp [memName, String.ext_iff])
    · obtain ⟨Q, hQ⟩ := hret.loaded.sorted.queue_arr
      exact ⟨Q, (hav "q" (by simp [alvName, String.ext_iff])
        (by simp [gamName, String.ext_iff])
        (by simp [memName, String.ext_iff])).trans hQ⟩
    · obtain ⟨QD, hQD⟩ := hret.loaded.sorted.qdist_arr
      exact ⟨QD, (hav "qd" (by simp [alvName, String.ext_iff])
        (by simp [gamName, String.ext_iff])
        (by simp [memName, String.ext_iff])).trans hQD⟩
  have hbq₂ : σ₂.vars "bq" = tail := by
    rw [hvv₂ "bq" (by decide) (by
      simp [mnumName, String.ext_iff]) (by decide)]
    exact hbq₁
  have hResEq : masked G Ra =
      Lax12.UniformQuasiWideness.deleteVerts (masked G A₀) (markSet n Xa)ᶜ := by
    rw [masked_congr hret.retained_val]
    exact masked_mul A₀ Xa (fun _ => Iff.rfl)
  have hbatch₂ :
      BatchData n j B G A₀ (markSet n Xa) (markSet n Wa) Alv Gam σ₂ := by
    exact ⟨⟨Xa, hmasks₂.cluster_arr, rfl, hret.loaded.cluster_bit⟩,
      ⟨Wa, hmasks₂.batch_arr, rfl, hWaB⟩,
      ⟨Ra, hmasks₂.retained_arr, hResEq, hret.retained_bound⟩,
      hmasks₂.child_arr, hmasks₂.child_bound, hmasks₂.child_graph,
      hmasks₂.child_point, hmasks₂.game_arr, hmasks₂.game_bound,
      Mem, mm, hmem₂, hmm₂, hMemE, hMemB⟩
  refine ⟨σ₂, streamChildFilterCost tail, hrun, ?_,
    Alv, Gam, Mem, mm, hsorted₂, hmasks₂, hret.loaded.cluster_set,
    hret.loaded.member_enum, hbq₂, hmem₂, hmm₂, hMemE, hMemB,
    hResEq, hbatch₂⟩
  exact le_rfl

#print axioms streamChildFilterStep

end Lax3Proofs.Refine.CoverActiveStreamChild
