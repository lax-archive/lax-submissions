import Lax3Proofs.Refine.CoverActiveStreamTurn
import Lax3Proofs.Refine.CoverActiveRadixPass

/-!
# Sorting one streamed active-cover row

The streamed BFS row is duplicate-free but arrives in discovery order.  This
module runs the existing verified radix block on the reusable prefix
`xmem[0..tail)`, proves exact membership preservation, and upgrades the row to
strict numeric order without an offset table or a larger allocation.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamSort

open Lax3.ColoredGraphs
open Lax3Proofs.Refine.CoverActiveRadixMath
open Lax3Proofs.Refine.CoverActiveRadixPass
open Lax3Proofs.Refine.CoverActiveStream
open Lax3Proofs.Refine.CoverActiveStreamTurn
open Lax3Proofs.Refine.CoverActiveTurn (distClean_of_arrs_eq)
open Lax13Proofs.Imp Lax13Proofs.Reasoning

/-! ## Program and state -/

/-- Sort the reusable prefix selected by the streamed turn. -/
def activeStreamSortCom : Com :=
  .seq (.assign "rslo" (.lit 0))
    (.seq (.assign "rsn" (.var "tail")) radixBlockCom)

def activeStreamSortK (bits tail : ℕ) : ℕ := radixBlockCost bits tail + 4

/-- The row after sorting, with all persistent cover and graph state framed. -/
structure StreamSortedOut {n : ℕ} (B ns nt na q r c tail bits : ℕ)
    (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre O T Xmem asg M : ℕ → ℕ) (σ : Env) : Prop where
  row : StreamRowA G A₀ π centre q r c tail Xmem asg M
  n_var : σ.vars "n" = n
  q_var : σ.vars "qn" = q
  centre_var : σ.vars "c" = c
  pointer_var : σ.vars "xp" = tail
  tail_var : σ.vars "tail" = tail
  bits_var : σ.vars "rsbits" = bits
  centre_arr : σ.arrs "ord" = arrOf n centre
  off_arr : σ.arrs "off" = arrOf (n + 1) O
  target_arr : σ.arrs "tgt" = arrOf nt T
  mask_arr : σ.arrs "alv" = arrOf n M
  row_arr : σ.arrs "xmem" = arrOf na Xmem
  row_fit : n ≤ na
  asg_arr : σ.arrs "asg" = arrOf n asg
  dist_clean : Lax3Proofs.Refine.BfsBlockMask.DistClean n (2 * r) M σ
  queue_arr : ∃ Q, σ.arrs "q" = arrOf n Q
  qdist_arr : ∃ QD, σ.arrs "qd" = arrOf n QD
  mask_bound : ∀ z < n, M z < B

variable {B n ns nt na q r c tail bits : ℕ} {G : SimpleGraph (Fin n)}
variable {A₀ centre O T Xmem asg M : ℕ → ℕ}
variable {π : Equiv.Perm (Fin n)}

/-! ## Mathematical row bridge -/

theorem rawRow_segment_nodup
    (h : RawStreamRowA G A₀ π centre q r c tail Xmem asg M) :
    (CoverActiveRadixPass.segment 0 tail Xmem).Nodup := by
  rw [CoverActiveRadixPass.segment, List.nodup_ofFn]
  intro i j hij
  apply Fin.ext
  exact h.block_inj (i : ℕ) (j : ℕ) i.isLt j.isLt (by simpa using hij)

/-- The executable radix result is a sorted streamed row. -/
theorem RawStreamRowA.of_radix
    (h : RawStreamRowA G A₀ π centre q r c tail Xmem asg M)
    {Xmem' : ℕ → ℕ}
    (hpow : n ≤ 2 ^ bits)
    (hseg : CoverActiveRadixPass.segment 0 tail Xmem' =
      radixRounds bits (CoverActiveRadixPass.segment 0 tail Xmem)) :
    StreamRowA G A₀ π centre q r c tail Xmem' asg M := by
  have hmem : ∀ p < tail, Xmem' p < n := by
    intro p hp
    have hx : Xmem' p ∈ CoverActiveRadixPass.segment 0 tail Xmem' :=
      mem_segment_iff.mpr ⟨p, hp, by simp⟩
    rw [hseg] at hx
    have hx' : Xmem' p ∈ CoverActiveRadixPass.segment 0 tail Xmem :=
      mem_radixRounds_iff.mp hx
    obtain ⟨i, hi, heq⟩ := mem_segment_iff.mp hx'
    rw [show 0 + i = i by omega] at heq
    rw [← heq]
    exact h.mem_lt i hi
  have hblock : ∀ w, (∃ p, p < tail ∧ Xmem' p = w) ↔
      (∃ p, p < tail ∧ Xmem p = w) := by
    intro w
    have hw : w ∈ CoverActiveRadixPass.segment 0 tail Xmem' ↔
        w ∈ CoverActiveRadixPass.segment 0 tail Xmem := by
      rw [hseg]
      exact mem_radixRounds_iff
    simpa only [mem_segment_iff, Nat.zero_add] using hw
  have hpw : (CoverActiveRadixPass.segment 0 tail Xmem').Pairwise
      (fun x y => x < y) := by
    rw [hseg]
    apply radixRounds_strict hpow
    · intro x hx
      obtain ⟨i, hi, heq⟩ := mem_segment_iff.mp hx
      rw [show 0 + i = i by omega] at heq
      rw [← heq]
      exact h.mem_lt i hi
    · exact rawRow_segment_nodup h
  have hmono : ∀ p p', p < p' → p' < tail → Xmem' p < Xmem' p' := by
    rw [pairwise_segment_iff] at hpw
    intro p p' hpp hp'
    simpa using hpw p p' hpp hp'
  exact h.sorted hmem hblock hmono

/-! ## Executable sort -/

/-- Sorting one streamed row requires only `tail < B` and an `n`-covering
radix width.  All other active-cover state is framed. -/
theorem activeStreamSort_spec
    (hB : 1 < B) (hnB : n < B) (hbitsB : bits < B) (hpow : n ≤ 2 ^ bits) :
    Spec B
      (fun σ => StreamTurnOut B ns nt na q r c tail G A₀ π centre O T Xmem asg M σ ∧
        σ.vars "rsbits" = bits)
      activeStreamSortCom
      (fun _ σ' => ∃ Xmem',
        StreamSortedOut B ns nt na q r c tail bits G A₀ π centre O T Xmem' asg M σ')
      (activeStreamSortK bits tail) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hout, hbits⟩ := hσ
  obtain ⟨Q₀, hq₀⟩ := hout.queue_arr
  have htailB : tail < B := lt_of_le_of_lt hout.row.tail_le hnB
  let σ₀ := σ.setVar "rslo" 0
  have r₀ : Run B (.assign "rslo" (.lit 0)) σ σ₀ 2 :=
    Run.assign (evalB_lit (by omega))
  have etail : (Expr.var "tail").evalB B σ₀ = some tail := by
    have ht : σ₀.vars "tail" = tail := by simp [σ₀, hout.tail_var]
    simpa only [ht] using (evalB_var (B := B) (x := "tail") (σ := σ₀)
      (by rw [ht]; exact htailB))
  let σ₁ := σ₀.setVar "rsn" tail
  have r₁ : Run B (.assign "rsn" (.var "tail")) σ₀ σ₁ 2 :=
    Run.assign etail
  have hpre : σ₁.vars "rslo" = 0 ∧ σ₁.vars "rsn" = tail ∧
      σ₁.vars "rsbits" = bits ∧ σ₁.arrs "xmem" = arrOf na Xmem ∧
      σ₁.arrs "q" = arrOf n Q₀ := by
    refine ⟨by simp [σ₁, σ₀], by simp [σ₁], ?_, ?_, ?_⟩
    · simp [σ₁, σ₀, hbits]
    · simp [σ₁, σ₀, hout.row_arr]
    · simp [σ₁, σ₀, hq₀]
  obtain ⟨σ₂, r₂, hb⟩ :=
    (radixBlockCom_spec (X := Xmem) (Q₀ := Q₀) hB hnB hout.row.tail_le hbitsB
      (by simpa using hout.row.tail_le.trans hout.row_fit) (by simpa using htailB)
      (fun i hi => lt_trans (by simpa using hout.row.mem_lt i hi) hnB)).run
        (σ := σ₁) hpre
  obtain ⟨hlo, hlen, hbits₂, -, Xmem', Q', hxmem', hq', hseg, houtside⟩ := hb
  have hrow' : StreamRowA G A₀ π centre q r c tail Xmem' asg M :=
    Lax3Proofs.Refine.CoverActiveStreamSort.RawStreamRowA.of_radix
      hout.row hpow (by simpa using hseg)
  have framev : ∀ y : String, y ∉ radixBlockCom.wvars →
      σ₂.vars y = σ₁.vars y := fun y hy => r₂.frame_var y hy
  have framea : ∀ a : String, a ∉ radixBlockCom.warrs →
      σ₂.arrs a = σ₁.arrs a := fun a ha => r₂.frame_arr a ha
  have hn₂ : σ₂.vars "n" = n := by
    rw [framev "n" (by
      simp [radixBlockCom, radixRoundCom, radixPassCom, stableScatterCom,
        selectDigitCom, selectDigitSlot, copyBackCom, copyBackSlot, Com.wvars])]
    simp [σ₁, σ₀, hout.n_var]
  have hqn₂ : σ₂.vars "qn" = q := by
    rw [framev "qn" (by
      simp [radixBlockCom, radixRoundCom, radixPassCom, stableScatterCom,
        selectDigitCom, selectDigitSlot, copyBackCom, copyBackSlot, Com.wvars])]
    simp [σ₁, σ₀, hout.q_var]
  have hc₂ : σ₂.vars "c" = c := by
    rw [framev "c" (by
      simp [radixBlockCom, radixRoundCom, radixPassCom, stableScatterCom,
        selectDigitCom, selectDigitSlot, copyBackCom, copyBackSlot, Com.wvars])]
    simp [σ₁, σ₀, hout.centre_var]
  have hxp₂ : σ₂.vars "xp" = tail := by
    rw [framev "xp" (by
      simp [radixBlockCom, radixRoundCom, radixPassCom, stableScatterCom,
        selectDigitCom, selectDigitSlot, copyBackCom, copyBackSlot, Com.wvars])]
    simp [σ₁, σ₀, hout.pointer_var]
  have htail₂ : σ₂.vars "tail" = tail := by
    rw [framev "tail" (by
      simp [radixBlockCom, radixRoundCom, radixPassCom, stableScatterCom,
        selectDigitCom, selectDigitSlot, copyBackCom, copyBackSlot, Com.wvars])]
    simp [σ₁, σ₀, hout.tail_var]
  have hord₂ : σ₂.arrs "ord" = arrOf n centre := by
    rw [framea "ord" (by
      simp [radixBlockCom, radixRoundCom, radixPassCom, stableScatterCom,
        selectDigitCom, selectDigitSlot, copyBackCom, copyBackSlot, Com.warrs])]
    simp [σ₁, σ₀, hout.centre_arr]
  have hoff₂ : σ₂.arrs "off" = arrOf (n + 1) O := by
    rw [framea "off" (by
      simp [radixBlockCom, radixRoundCom, radixPassCom, stableScatterCom,
        selectDigitCom, selectDigitSlot, copyBackCom, copyBackSlot, Com.warrs])]
    simp [σ₁, σ₀, hout.off_arr]
  have htgt₂ : σ₂.arrs "tgt" = arrOf nt T := by
    rw [framea "tgt" (by
      simp [radixBlockCom, radixRoundCom, radixPassCom, stableScatterCom,
        selectDigitCom, selectDigitSlot, copyBackCom, copyBackSlot, Com.warrs])]
    simp [σ₁, σ₀, hout.target_arr]
  have halv₂ : σ₂.arrs "alv" = arrOf n M := by
    rw [framea "alv" (by
      simp [radixBlockCom, radixRoundCom, radixPassCom, stableScatterCom,
        selectDigitCom, selectDigitSlot, copyBackCom, copyBackSlot, Com.warrs])]
    simp [σ₁, σ₀, hout.mask_arr]
  have hasg₂ : σ₂.arrs "asg" = arrOf n asg := by
    rw [framea "asg" (by
      simp [radixBlockCom, radixRoundCom, radixPassCom, stableScatterCom,
        selectDigitCom, selectDigitSlot, copyBackCom, copyBackSlot, Com.warrs])]
    simp [σ₁, σ₀, hout.asg_arr]
  have hqd₂ : σ₂.arrs "qd" = σ.arrs "qd" := by
    rw [framea "qd" (by
      simp [radixBlockCom, radixRoundCom, radixPassCom, stableScatterCom,
        selectDigitCom, selectDigitSlot, copyBackCom, copyBackSlot, Com.warrs])]
    simp [σ₁, σ₀]
  have hdist₂ : Lax3Proofs.Refine.BfsBlockMask.DistClean n (2 * r) M σ₂ := by
    apply distClean_of_arrs_eq hout.dist_clean
    rw [framea "dist" (by
      simp [radixBlockCom, radixRoundCom, radixPassCom, stableScatterCom,
        selectDigitCom, selectDigitSlot, copyBackCom, copyBackSlot, Com.warrs])]
    simp [σ₁, σ₀]
  have hsorted :
      StreamSortedOut B ns nt na q r c tail bits G A₀ π centre O T Xmem' asg M σ₂ := by
    refine ⟨hrow', hn₂, hqn₂, hc₂, hxp₂, htail₂, hbits₂, hord₂, hoff₂,
      htgt₂, halv₂, hxmem', hout.row_fit, hasg₂, hdist₂, ⟨Q', hq'⟩, ?_,
      hout.mask_bound⟩
    obtain ⟨QD, hQD⟩ := hout.qdist_arr
    exact ⟨QD, hqd₂.trans hQD⟩
  refine ⟨σ₂, _, r₀.seq (r₁.seq r₂), ?_, Xmem', hsorted⟩
  simp only [activeStreamSortK]
  omega

/-! ## Axiom audit -/

#print axioms RawStreamRowA.of_radix
#print axioms activeStreamSort_spec

end Lax3Proofs.Refine.CoverActiveStreamSort
