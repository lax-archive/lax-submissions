import Lax3Proofs.Refine.CoverActiveStream
import Lax3Proofs.Refine.CoverActiveTurn

/-!
# One linear-resident streamed active-cover turn

This is the executable counterpart of `CoverActiveStream`.  Every centre
resets `xp` to zero, emits its touched BFS queue into `xmem[0..tail)`, updates
the stable first-catcher assignment, and deletes the centre from the
progressive mask.  The command neither forms an accumulated `n * D` pointer
nor reads or writes an offset table.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamTurn

open Lax3.ColoredGraphs
open Lax11.GraphEncoding
open Lax3Proofs.RamBfs (CsrGraph WD)
open Lax3Proofs.RamCoverActive
open Lax3Proofs.Refine.BfsBlock
open Lax3Proofs.Refine.BfsBlockMask
open Lax3Proofs.Refine.CoverActiveBlock
open Lax3Proofs.Refine.CoverActiveStream
open Lax3Proofs.Refine.CoverActiveTurn
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ## Program and charge -/

/-- Search and emit one centre into a reusable carrier-sized row.  The centre
counter is deliberately left unchanged so the cluster body can consume the
row under its original assignment index; the enclosing fused loop advances it
after that body returns. -/
def activeStreamTurnCom (r : ℕ) : Com :=
  .seq (.assign "src" (.get "ord" (.var "c")))
    (.seq (bfsBlockCom (2 * r))
      (.seq (.assign "xp" (.lit 0))
        (.seq (emitQueueCom r)
          (.store "alv" (.var "src") (.lit 0)))))

/-- Search, one-row emission, and constant-time book-keeping. -/
def activeStreamTurnK (bw nb : ℕ) : ℕ := bfsBlockK bw nb + 34 * nb + 14

theorem activeStreamTurnK_le_weight (bw nb : ℕ) :
    activeStreamTurnK bw nb ≤ 150 * (bw + nb + 1) := by
  simp only [activeStreamTurnK, bfsBlockK]
  omega

/-! ## Machine boundaries -/

/-- State before searching centre `c`.  Only the semantic prefix persists;
`xmem` is a reusable array of length `n`, with no entering-content contract. -/
structure StreamTurnState {n : ℕ} (B ns nt q r c : ℕ)
    (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre O T Xmem asg M : ℕ → ℕ) (σ : Env) : Prop where
  state : CoverPrefixA G A₀ π centre q r c asg M
  n_var : σ.vars "n" = n
  q_var : σ.vars "qn" = q
  centre_var : σ.vars "c" = c
  centre_arr : σ.arrs "ord" = arrOf n centre
  off_arr : σ.arrs "off" = arrOf (n + 1) O
  target_arr : σ.arrs "tgt" = arrOf nt T
  mask_arr : σ.arrs "alv" = arrOf n M
  row_arr : σ.arrs "xmem" = arrOf n Xmem
  asg_arr : σ.arrs "asg" = arrOf n asg
  dist_clean : DistClean n (2 * r) M σ
  queue_arr : ∃ Q, σ.arrs "q" = arrOf n Q
  qdist_arr : ∃ QD, σ.arrs "qd" = arrOf n QD
  mask_bound : ∀ z < n, M z < B

/-- State after searching centre `c`, before sorting and consuming its row.
The scalar `c` still names that row while `row.state` has already advanced to
the persistent prefix `c+1`. -/
structure StreamTurnOut {n : ℕ} (B ns nt q r c tail : ℕ)
    (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre O T Xmem asg M : ℕ → ℕ) (σ : Env) : Prop where
  row : RawStreamRowA G A₀ π centre q r c tail Xmem asg M
  n_var : σ.vars "n" = n
  q_var : σ.vars "qn" = q
  centre_var : σ.vars "c" = c
  pointer_var : σ.vars "xp" = tail
  tail_var : σ.vars "tail" = tail
  centre_arr : σ.arrs "ord" = arrOf n centre
  off_arr : σ.arrs "off" = arrOf (n + 1) O
  target_arr : σ.arrs "tgt" = arrOf nt T
  mask_arr : σ.arrs "alv" = arrOf n M
  row_arr : σ.arrs "xmem" = arrOf n Xmem
  asg_arr : σ.arrs "asg" = arrOf n asg
  dist_clean : DistClean n (2 * r) M σ
  queue_arr : ∃ Q, σ.arrs "q" = arrOf n Q
  qdist_arr : ∃ QD, σ.arrs "qd" = arrOf n QD
  mask_bound : ∀ z < n, M z < B

variable {B n ns nt q r c bw nb : ℕ} {G : SimpleGraph (Fin n)}
variable {A₀ centre O T Xmem asg M : ℕ → ℕ}
variable {π : Equiv.Perm (Fin n)} {A : Finset ℕ}

/-- A streamed active-cover turn needs only carrier-sized row indices.  In
particular, there is no `xp + n < B` or `n * n < B` premise. -/
theorem activeStreamTurn_spec
    (hcentres : CentresBy n q A₀ π centre)
    (hcsr : CsrGraph G ns O T)
    (hnB : n < B) (hnsB : ns < B) (hnt : ns ≤ nt)
    (hqB : q < B) (hrB : 2 * r + 1 < B)
    (hA : ∀ v, v < n → M v ≠ 0 → WD G M (2 * r) (centre c) v → v ∈ A)
    (hbw : ∑ v ∈ A, Csr.rowLen O v ≤ bw)
    (hnb : A.card ≤ nb) :
    Spec B
      (fun σ => StreamTurnState B ns nt q r c G A₀ π centre O T Xmem asg M σ ∧
        c < q)
      (activeStreamTurnCom r)
      (fun _ σ' => ∃ tail Q QD Xmem', tail ≤ nb ∧
        StreamTurnOut B ns nt q r c tail G A₀ π centre O T Xmem'
          (queueCell asg q c r tail Q QD) (upd M (centre c) 0) σ')
      (activeStreamTurnK bw nb) := by
  classical
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hS, hc⟩ := hσ
  obtain ⟨hstate, hn, hqn, hcvar, hord, hoff, htgt, halv, hxmem,
    hasg, hdist, ⟨Q₀, hq₀⟩, ⟨QD₀, hqd₀⟩, hMB⟩ := hS
  have hcN : c < n := lt_of_lt_of_le hc hcentres.count_le
  have hcB : c < B := lt_trans hcN hnB
  have hsN : centre c < n := hcentres.centre_lt c hc
  have hsB : centre c < B := lt_trans hsN hnB
  have hzeroB : 0 < B := by omega
  have hrB' : r + 1 < B := by omega
  -- Load the current live centre.
  have esrc : (Expr.get "ord" (.var "c")).evalB B σ = some (centre c) := by
    apply evalB_get
    · apply evalB_var
      rw [hcvar]
      exact hcB
    · rw [hord, hcvar, getElem?_arrOf centre hcN]
    · exact hsB
  let σ₁ := σ.setVar "src" (centre c)
  have run₁ : Run B (.assign "src" (.get "ord" (.var "c"))) σ σ₁ 3 := by
    exact (Run.assign esrc).mono (by simp [Expr.size])
  have hpreBfs :
      σ₁.vars "n" = n ∧ σ₁.vars "src" = centre c ∧
        σ₁.arrs "off" = arrOf (n + 1) O ∧ σ₁.arrs "tgt" = arrOf nt T ∧
        σ₁.arrs "alv" = arrOf n M ∧ DistClean n (2 * r) M σ₁ ∧
        (∃ g, σ₁.arrs "q" = arrOf n g) ∧ (∃ g, σ₁.arrs "qd" = arrOf n g) := by
    refine ⟨by simp [σ₁, hn], by simp [σ₁], by simpa [σ₁] using hoff,
      by simpa [σ₁] using htgt, by simpa [σ₁] using halv, ?_,
      ⟨Q₀, by simpa [σ₁] using hq₀⟩, ⟨QD₀, by simpa [σ₁] using hqd₀⟩⟩
    simpa [σ₁] using hdist
  obtain ⟨σ₂, run₂, hdist₂, Q, QD, hq₂, hqd₂, htailn, htailnb,
      hQn, hseg, hQinj, hQD⟩ :=
    (bfsBlockM_specW (d := 2 * r) (s := centre c) hcsr hsN hnB hnsB hnt hrB hMB
      hA hbw hnb).run (σ := σ₁) hpreBfs
  let tail := σ₂.vars "tail"
  have htailn' : tail ≤ n := by simpa [tail] using htailn
  have htailnb' : tail ≤ nb := by simpa [tail] using htailnb
  have htailB : tail < B := lt_of_le_of_lt htailn' hnB
  -- The BFS leaves the persistent cover state untouched.
  have hn₂ : σ₂.vars "n" = n := by
    rw [run₂.frame_var "n" (notMem_bfsTurn_wvars r "n" (by simp))]
    simpa [σ₁] using hn
  have hqn₂ : σ₂.vars "qn" = q := by
    rw [run₂.frame_var "qn" (notMem_bfsTurn_wvars r "qn" (by simp))]
    simpa [σ₁] using hqn
  have hc₂ : σ₂.vars "c" = c := by
    rw [run₂.frame_var "c" (notMem_bfsTurn_wvars r "c" (by simp))]
    simpa [σ₁] using hcvar
  have hsrc₂ : σ₂.vars "src" = centre c := by
    rw [run₂.frame_var "src" (notMem_bfsTurn_wvars r "src" (by simp))]
    simp [σ₁]
  have hoff₂ : σ₂.arrs "off" = arrOf (n + 1) O := by
    rw [run₂.frame_arr "off" (notMem_bfsTurn_warrs r "off" (by simp))]
    simpa [σ₁] using hoff
  have htgt₂ : σ₂.arrs "tgt" = arrOf nt T := by
    rw [run₂.frame_arr "tgt" (notMem_bfsTurn_warrs r "tgt" (by simp))]
    simpa [σ₁] using htgt
  have halv₂ : σ₂.arrs "alv" = arrOf n M := by
    rw [run₂.frame_arr "alv" (notMem_bfsTurn_warrs r "alv" (by simp))]
    simpa [σ₁] using halv
  have hord₂ : σ₂.arrs "ord" = arrOf n centre := by
    rw [run₂.frame_arr "ord" (notMem_bfsTurn_warrs r "ord" (by simp))]
    simpa [σ₁] using hord
  have hxmem₂ : σ₂.arrs "xmem" = arrOf n Xmem := by
    rw [run₂.frame_arr "xmem" (notMem_bfsTurn_warrs r "xmem" (by simp))]
    simpa [σ₁] using hxmem
  have hasg₂ : σ₂.arrs "asg" = arrOf n asg := by
    rw [run₂.frame_arr "asg" (notMem_bfsTurn_warrs r "asg" (by simp))]
    simpa [σ₁] using hasg
  -- Reuse the row from index zero.
  let σx := σ₂.setVar "xp" 0
  have runx : Run B (.assign "xp" (.lit 0)) σ₂ σx 2 :=
    Run.assign (evalB_lit hzeroB)
  have hQDB : ∀ i < tail, QD i < B := by
    intro i hi
    have hqi : Q i < n := hQn i (by simpa [tail] using hi)
    have hwd : WD G M (2 * r) (centre c) (Q i) :=
      ((hseg (Q i) hqi).mp ⟨i, by simpa [tail] using hi, rfl⟩).2
    have hle := (hQD i (by simpa [tail] using hi) (2 * r) le_rfl).mpr hwd
    omega
  have hasgB : ∀ i < tail, asg (Q i) < B := by
    intro i hi
    have hqi : Q i < n := hQn i (by simpa [tail] using hi)
    have hm : M (Q i) ≠ 0 :=
      ((hseg (Q i) hqi).mp ⟨i, by simpa [tail] using hi, rfl⟩).1
    have ha : A₀ (Q i) ≠ 0 := by
      intro ha0
      exact hm ((hstate.mask (Q i) hqi).mpr (Or.inl ha0))
    exact lt_of_le_of_lt (hstate.asg_le (Q i) hqi ha) hqB
  have hpreEmit :
      QueueEmitInv n n tail q c r 0 Q QD Xmem asg (σx.setVar "cvk" 0) := by
    refine ⟨Xmem, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [σx, tail]
    · simpa [σx] using hqn₂
    · simpa [σx] using hc₂
    · simpa [σx] using hq₂
    · simpa [σx] using hqd₂
    · simpa [σx] using hxmem₂
    · simpa [σx, queueCell_zero] using hasg₂
    · simp
    · simp [σx]
    · intro p hp
      omega
    · intro i hi
      simp at hi
  obtain ⟨σ₃, run₃,
      ⟨⟨Xmem', htail₃, hqn₃, hc₃, hq₃, hqd₃, hxmem₃, hasg₃,
        hcvkle₃, hxp₃, hkeep₃, hwrite₃⟩, hcvk₃⟩⟩ :=
    (emitQueueCom_spec (n := n) (na := n) (tail := tail) (q := q) (c := c)
      (r := r) (xp₀ := 0) (Q := Q) (QD := QD) (Xm₀ := Xmem) (asg₀ := asg)
      hnB htailB htailn' hqB hc hrB' (by simpa using htailn') (by simpa using htailB)
      (fun i hi => hQn i (by simpa [tail] using hi)) hQDB hasgB).run
      (σ := σx) hpreEmit
  have hxp₃' : σ₃.vars "xp" = tail := by rw [hxp₃, hcvk₃]; omega
  have hasg₃' : σ₃.arrs "asg" = arrOf n (queueCell asg q c r tail Q QD) := by
    rw [hasg₃, hcvk₃]
  have hwrite₃' : ∀ i < tail, Xmem' i = Q i := by
    intro i hi
    simpa using hwrite₃ i (by simpa [hcvk₃] using hi)
  have hn₃ : σ₃.vars "n" = n := by
    rw [run₃.frame_var "n" (notMem_emitQueue_wvars r "n" (by simp))]
    simpa [σx] using hn₂
  have hsrc₃ : σ₃.vars "src" = centre c := by
    rw [run₃.frame_var "src" (notMem_emitQueue_wvars r "src" (by simp))]
    simpa [σx] using hsrc₂
  have hoff₃ : σ₃.arrs "off" = arrOf (n + 1) O := by
    rw [run₃.frame_arr "off" (notMem_emitQueue_warrs r "off" (by simp))]
    simpa [σx] using hoff₂
  have htgt₃ : σ₃.arrs "tgt" = arrOf nt T := by
    rw [run₃.frame_arr "tgt" (notMem_emitQueue_warrs r "tgt" (by simp))]
    simpa [σx] using htgt₂
  have halv₃ : σ₃.arrs "alv" = arrOf n M := by
    rw [run₃.frame_arr "alv" (notMem_emitQueue_warrs r "alv" (by simp))]
    simpa [σx] using halv₂
  have hord₃ : σ₃.arrs "ord" = arrOf n centre := by
    rw [run₃.frame_arr "ord" (notMem_emitQueue_warrs r "ord" (by simp))]
    simpa [σx] using hord₂
  have hdistArr₃ : σ₃.arrs "dist" = σ₂.arrs "dist" := by
    rw [run₃.frame_arr "dist" (notMem_emitQueue_warrs r "dist" (by simp))]
    simp [σx]
  -- Delete the centre, but leave scalar `c` for the immediate row consumer.
  let σ₄ := σ₃.setArr "alv" (centre c) 0
  have run₄ : Run B (.store "alv" (.var "src") (.lit 0)) σ₃ σ₄ 3 := by
    have h := Run.store (B := B) (σ := σ₃) (a := "alv") (i := .var "src")
      (e := .lit 0) (evalB_var (by rw [hsrc₃]; exact hsB)) (evalB_lit hzeroB)
      (by rw [hsrc₃, halv₃, length_arrOf]; exact hsN)
    rw [hsrc₃] at h
    exact h.mono (by simp [Expr.size])
  have hrow : RawStreamRowA G A₀ π centre q r c tail Xmem'
      (queueCell asg q c r tail Q QD) (upd M (centre c) 0) := by
    apply RawStreamRowA.stepQueue hcentres hstate hc htailn'
      (fun i hi => hQn i (by simpa [tail] using hi))
      (fun v hv => by simpa [tail] using hseg v hv)
      (fun i hi j hj hqij => hQinj i (by simpa [tail] using hi) j
        (by simpa [tail] using hj) hqij)
      (fun i hi k hk => hQD i (by simpa [tail] using hi) k hk)
    · exact hwrite₃'
    · intro w hw ha
      by_cases hset : asg w < q
      · simp [queueCell, hset]
      · have heq : asg w = q := by
          have := hstate.asg_le w hw ha
          omega
        simp [queueCell, caughtBefore, hset, heq]
    · intro u hu
      by_cases hus : u = centre c
      · simp [hus]
      · simp [hus]
  have hdist₄ : DistClean n (2 * r) (upd M (centre c) 0) σ₄ := by
    obtain ⟨D, hDarr, hclean⟩ := hdist₂
    refine ⟨D, ?_, cleanOn_upd_zero hclean⟩
    calc
      σ₄.arrs "dist" = σ₃.arrs "dist" := by simp [σ₄]
      _ = σ₂.arrs "dist" := hdistArr₃
      _ = arrOf n D := hDarr
  have hout : StreamTurnOut B ns nt q r c tail G A₀ π centre O T Xmem'
      (queueCell asg q c r tail Q QD) (upd M (centre c) 0) σ₄ := by
    refine ⟨hrow, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hdist₄,
      ⟨Q, ?_⟩, ⟨QD, ?_⟩, ?_⟩
    · simp [σ₄, hn₃]
    · simp [σ₄, hqn₃]
    · simp [σ₄, hc₃]
    · simp [σ₄, hxp₃']
    · simp [σ₄, htail₃]
    · simp [σ₄, hord₃]
    · simp [σ₄, hoff₃]
    · simp [σ₄, htgt₃]
    · simp [σ₄, halv₃, set_arrOf_eq_upd]
    · simpa [σ₄] using hxmem₃
    · simpa [σ₄] using hasg₃'
    · simpa [σ₄] using hq₃
    · simpa [σ₄] using hqd₃
    · intro z hz
      by_cases hzs : z = centre c
      · simpa [hzs] using hzeroB
      · simpa [hzs] using hMB z hz
  refine ⟨σ₄, _, run₁.seq (run₂.seq (runx.seq (run₃.seq run₄))), ?_,
    tail, Q, QD, Xmem', htailnb', hout⟩
  simp only [activeStreamTurnK]
  omega

/-! ## Axiom audit -/

#print axioms activeStreamTurnK_le_weight
#print axioms activeStreamTurn_spec

end Lax3Proofs.Refine.CoverActiveStreamTurn
