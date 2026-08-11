import Lax3Proofs.Refine.CoverActiveBlock

/-!
# One block-priced active-cover turn

This file composes the mask-scoped block BFS with the queue emitter.  The
turn loads one live centre, searches only its current masked ball, copies
exactly the returned queue, kills the centre, and records the new arena
offset.  Its cost is a function of the ball's row slots and vertices; the
carrier occurs only in physical array lengths and word bounds.
-/

namespace Lax3Proofs.Refine.CoverActiveTurn

open Lax3.ColoredGraphs
open Lax11.GraphEncoding
open Lax3Proofs.RamBfs (CsrGraph WD)
open Lax3Proofs.RamCoverActive
open Lax3Proofs.Refine.BfsBlock
open Lax3Proofs.Refine.BfsBlockMask
open Lax3Proofs.Refine.CoverActiveBlock
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ## Program and charge -/

/-- One complete active centre turn. -/
def activeTurnCom (r : ℕ) : Com :=
  .seq (.assign "src" (.get "ord" (.var "c")))
    (.seq (bfsBlockCom (2 * r))
      (.seq (emitQueueCom r)
        (.seq (.store "alv" (.var "src") (.lit 0))
          (.seq (.assign "c" (.add (.var "c") (.lit 1)))
            (.store "xoff" (.var "c") (.var "xp"))))))

/-- Search, queue emission, and the four constant-time book-keeping
instructions. -/
def activeTurnK (bw nb : ℕ) : ℕ := bfsBlockK bw nb + 34 * nb + 19

/-- The historical cover coefficient `150` pays the strengthened turn. -/
theorem activeTurnK_le_weight (bw nb : ℕ) :
    activeTurnK bw nb ≤ 150 * (bw + nb + 1) := by
  simp only [activeTurnK, bfsBlockK]
  omega

/-! ## Machine invariant -/

/-- The state shared by consecutive active turns.  In particular, distance
is clean only on the progressive mask, and assignment values are constrained
only semantically on the original live arena. -/
structure RawTurnState {n : ℕ} (B ns nt q r c xp : ℕ)
    (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre O T Xoff Xmem asg M : ℕ → ℕ) (σ : Env) : Prop where
  raw : RawCoverInvA G A₀ π centre q r c xp Xoff Xmem asg M
  n_var : σ.vars "n" = n
  q_var : σ.vars "qn" = q
  centre_var : σ.vars "c" = c
  pointer_var : σ.vars "xp" = xp
  centre_arr : σ.arrs "ord" = arrOf n centre
  off_arr : σ.arrs "off" = arrOf (n + 1) O
  target_arr : σ.arrs "tgt" = arrOf nt T
  mask_arr : σ.arrs "alv" = arrOf n M
  xoff_arr : σ.arrs "xoff" = arrOf (n + 1) Xoff
  xmem_arr : σ.arrs "xmem" = arrOf (n * n) Xmem
  asg_arr : σ.arrs "asg" = arrOf n asg
  dist_clean : DistClean n (2 * r) M σ
  queue_arr : ∃ Q, σ.arrs "q" = arrOf n Q
  qdist_arr : ∃ QD, σ.arrs "qd" = arrOf n QD
  mask_bound : ∀ z < n, M z < B

/-! ## Small frame and support lemmas -/

theorem notMem_bfsTurn_wvars (r : ℕ) (y : String)
    (hy : y ∈ ["n", "qn", "c", "xp", "src"]) : y ∉ (bfsBlockCom (2 * r)).wvars := by
  fin_cases hy <;>
    simp [bfsBlockCom, unwind, unwindSlot, Lax3Proofs.RamBfs.seedSrc,
      Lax3Proofs.RamBfs.bfsDrain, Lax3Proofs.RamBfs.expandRow,
      Lax3Proofs.RamBfs.scanSlot, Fill.put, Csr.loadRow, Csr.scan,
      Queue.drain, Com.wvars]

theorem notMem_bfsTurn_warrs (r : ℕ) (a : String)
    (ha : a ∈ ["off", "tgt", "alv", "ord", "xoff", "xmem", "asg"]) :
    a ∉ (bfsBlockCom (2 * r)).warrs := by
  fin_cases ha <;>
    simp [bfsBlockCom, unwind, unwindSlot, Lax3Proofs.RamBfs.seedSrc,
      Lax3Proofs.RamBfs.bfsDrain, Lax3Proofs.RamBfs.expandRow,
      Lax3Proofs.RamBfs.scanSlot, Fill.put, Csr.loadRow, Csr.scan,
      Queue.drain, Com.warrs]

theorem notMem_emitQueue_wvars (r : ℕ) (y : String)
    (hy : y ∈ ["n", "qn", "c", "src"]) : y ∉ (emitQueueCom r).wvars := by
  fin_cases hy <;> simp [emitQueueCom, emitQueueSlot, Com.wvars]

theorem notMem_emitQueue_warrs (r : ℕ) (a : String)
    (ha : a ∈ ["off", "tgt", "alv", "ord", "xoff", "dist"]) :
    a ∉ (emitQueueCom r).warrs := by
  fin_cases ha <;> simp [emitQueueCom, emitQueueSlot, Com.warrs]

theorem distClean_of_arrs_eq {n d : ℕ} {M : ℕ → ℕ} {σ σ' : Env}
    (h : DistClean n d M σ) (he : σ'.arrs "dist" = σ.arrs "dist") :
    DistClean n d M σ' := by
  obtain ⟨D₀, hD, hc⟩ := h
  exact ⟨D₀, he.trans hD, hc⟩

theorem cleanOn_upd_zero {n d s : ℕ} {M D : ℕ → ℕ}
    (h : CleanOn n d M D) : CleanOn n d (upd M s 0) D := by
  intro z hz hmz
  apply h z hz
  intro hm
  by_cases hzs : z = s
  · subst z
    simpa using hmz
  · rw [upd_of_ne _ hzs, hm] at hmz
    exact hmz rfl

@[simp] theorem queueCell_zero (asg : ℕ → ℕ) (q c r : ℕ) (Q QD : ℕ → ℕ) :
    queueCell asg q c r 0 Q QD = asg := by
  funext w
  simp [queueCell, caughtBefore]

/-! ## The composed turn -/

variable {B n ns nt q r c xp bw nb : ℕ} {G : SimpleGraph (Fin n)}
variable {A₀ centre O T Xoff Xmem asg M : ℕ → ℕ}
variable {π : Equiv.Perm (Fin n)} {A : Finset ℕ}

/-- A block BFS followed by the touched queue emitter advances the raw cover
invariant at a charge depending only on this ball. -/
theorem activeTurn_spec
    (hcentres : CentresBy n q A₀ π centre)
    (hcsr : CsrGraph G ns O T)
    (hnB : n < B) (hnsB : ns < B) (hnt : ns ≤ nt) (hnnB : n * n < B)
    (hqB : q < B) (hrB : 2 * r + 1 < B)
    (hA : ∀ v, v < n → M v ≠ 0 → WD G M (2 * r) (centre c) v → v ∈ A)
    (hbw : ∑ v ∈ A, Csr.rowLen O v ≤ bw)
    (hnb : A.card ≤ nb) :
    Spec B
      (fun σ => RawTurnState B ns nt q r c xp G A₀ π centre O T Xoff Xmem asg M σ ∧ c < q)
      (activeTurnCom r)
      (fun _ σ' => ∃ tail Q QD Xmem', tail ≤ nb ∧
        RawTurnState B ns nt q r (c + 1) (xp + tail) G A₀ π centre O T
          (upd Xoff (c + 1) (xp + tail)) Xmem'
          (queueCell asg q c r tail Q QD) (upd M (centre c) 0) σ')
      (activeTurnK bw nb) := by
  classical
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hS, hc⟩ := hσ
  obtain ⟨hraw, hn, hqn, hcvar, hxp, hord, hoff, htgt, halv, hxoff, hxmem,
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
  have htail : σ₂.vars "tail" = tail := rfl
  have htailn' : tail ≤ n := by simpa [tail] using htailn
  have htailnb' : tail ≤ nb := by simpa [tail] using htailnb
  have htailB : tail < B := lt_of_le_of_lt htailn' hnB
  -- The BFS leaves all cover state untouched except its private scratch.
  have hn₂ : σ₂.vars "n" = n := by
    rw [run₂.frame_var "n" (notMem_bfsTurn_wvars r "n" (by simp))]
    simpa [σ₁] using hn
  have hqn₂ : σ₂.vars "qn" = q := by
    rw [run₂.frame_var "qn" (notMem_bfsTurn_wvars r "qn" (by simp))]
    simpa [σ₁] using hqn
  have hc₂ : σ₂.vars "c" = c := by
    rw [run₂.frame_var "c" (notMem_bfsTurn_wvars r "c" (by simp))]
    simpa [σ₁] using hcvar
  have hxp₂ : σ₂.vars "xp" = xp := by
    rw [run₂.frame_var "xp" (notMem_bfsTurn_wvars r "xp" (by simp))]
    simpa [σ₁] using hxp
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
  have hxoff₂ : σ₂.arrs "xoff" = arrOf (n + 1) Xoff := by
    rw [run₂.frame_arr "xoff" (notMem_bfsTurn_warrs r "xoff" (by simp))]
    simpa [σ₁] using hxoff
  have hxmem₂ : σ₂.arrs "xmem" = arrOf (n * n) Xmem := by
    rw [run₂.frame_arr "xmem" (notMem_bfsTurn_warrs r "xmem" (by simp))]
    simpa [σ₁] using hxmem
  have hasg₂ : σ₂.arrs "asg" = arrOf n asg := by
    rw [run₂.frame_arr "asg" (notMem_bfsTurn_warrs r "asg" (by simp))]
    simpa [σ₁] using hasg
  -- The raw arena has room for this touched queue prefix.
  have hc1n : c + 1 ≤ n := by omega
  have hmul : (c + 1) * n ≤ n * n := Nat.mul_le_mul_right n hc1n
  have hroom : xp + tail ≤ n * n := by
    calc
      xp + tail ≤ c * n + n := Nat.add_le_add hraw.ptr_le htailn'
      _ = (c + 1) * n := by simp [Nat.add_mul]
      _ ≤ n * n := hmul
  have hroomB : xp + tail < B := lt_of_le_of_lt hroom hnnB
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
      exact hm ((hraw.mask (Q i) hqi).mpr (Or.inl ha0))
    exact lt_of_le_of_lt (hraw.asg_le (Q i) hqi ha) hqB
  have hpreEmit :
      QueueEmitInv n (n * n) tail q c r xp Q QD Xmem asg (σ₂.setVar "cvk" 0) := by
    refine ⟨Xmem, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [tail]
    · simpa using hqn₂
    · simpa using hc₂
    · simpa using hq₂
    · simpa using hqd₂
    · simpa using hxmem₂
    · simpa [queueCell_zero] using hasg₂
    · simp
    · simpa using hxp₂
    · intro p hp
      rfl
    · intro i hi
      simp at hi
  obtain ⟨σ₃, run₃,
      ⟨⟨Xmem', htail₃, hqn₃, hc₃, hq₃, hqd₃, hxmem₃, hasg₃,
        hcvkle₃, hxp₃, hkeep₃, hwrite₃⟩, hcvk₃⟩⟩ :=
    (emitQueueCom_spec (n := n) (na := n * n) (tail := tail) (q := q) (c := c)
      (r := r) (xp₀ := xp) (Q := Q) (QD := QD) (Xm₀ := Xmem) (asg₀ := asg)
      hnB htailB htailn' hqB hc hrB' hroom hroomB
      (fun i hi => hQn i (by simpa [tail] using hi)) hQDB hasgB).run
      (σ := σ₂) hpreEmit
  have hxp₃' : σ₃.vars "xp" = xp + tail := by rw [hxp₃, hcvk₃]
  have hasg₃' : σ₃.arrs "asg" = arrOf n (queueCell asg q c r tail Q QD) := by
    rw [hasg₃, hcvk₃]
  have hwrite₃' : ∀ i < tail, Xmem' (xp + i) = Q i := by
    intro i hi
    exact hwrite₃ i (by simpa [hcvk₃] using hi)
  have hn₃ : σ₃.vars "n" = n := by
    rw [run₃.frame_var "n" (notMem_emitQueue_wvars r "n" (by simp))]
    exact hn₂
  have hsrc₃ : σ₃.vars "src" = centre c := by
    rw [run₃.frame_var "src" (notMem_emitQueue_wvars r "src" (by simp))]
    exact hsrc₂
  have hoff₃ : σ₃.arrs "off" = arrOf (n + 1) O := by
    rw [run₃.frame_arr "off" (notMem_emitQueue_warrs r "off" (by simp))]
    exact hoff₂
  have htgt₃ : σ₃.arrs "tgt" = arrOf nt T := by
    rw [run₃.frame_arr "tgt" (notMem_emitQueue_warrs r "tgt" (by simp))]
    exact htgt₂
  have halv₃ : σ₃.arrs "alv" = arrOf n M := by
    rw [run₃.frame_arr "alv" (notMem_emitQueue_warrs r "alv" (by simp))]
    exact halv₂
  have hord₃ : σ₃.arrs "ord" = arrOf n centre := by
    rw [run₃.frame_arr "ord" (notMem_emitQueue_warrs r "ord" (by simp))]
    exact hord₂
  have hxoff₃ : σ₃.arrs "xoff" = arrOf (n + 1) Xoff := by
    rw [run₃.frame_arr "xoff" (notMem_emitQueue_warrs r "xoff" (by simp))]
    exact hxoff₂
  have hdistArr₃ : σ₃.arrs "dist" = σ₂.arrs "dist" :=
    run₃.frame_arr "dist" (notMem_emitQueue_warrs r "dist" (by simp))
  -- Kill the centre, advance the centre counter, and close the new offset.
  let σ₄ := σ₃.setArr "alv" (centre c) 0
  have run₄ : Run B (.store "alv" (.var "src") (.lit 0)) σ₃ σ₄ 3 := by
    have h := Run.store (B := B) (σ := σ₃) (a := "alv") (i := .var "src")
      (e := .lit 0) (evalB_var (by rw [hsrc₃]; exact hsB)) (evalB_lit hzeroB)
      (by rw [hsrc₃, halv₃, length_arrOf]; exact hsN)
    rw [hsrc₃] at h
    exact h.mono (by simp [Expr.size])
  have hc₄ : σ₄.vars "c" = c := by simp [σ₄, hc₃]
  let σ₅ := σ₄.setVar "c" (c + 1)
  have ecnext : (Expr.add (.var "c") (.lit 1)).evalB B σ₄ = some (c + 1) := by
    have h := evalB_bin (evalB_var (by rw [hc₄]; exact hcB)) (evalB_lit (by omega))
      (show Bop.add.apply (σ₄.vars "c") 1 < B by rw [Bop.apply_add, hc₄]; omega)
    rw [Bop.apply_add, hc₄] at h
    exact h
  have run₅ : Run B (.assign "c" (.add (.var "c") (.lit 1))) σ₄ σ₅ 4 := by
    exact (Run.assign ecnext).mono (by simp [σ₅, Expr.size])
  have hc₅ : σ₅.vars "c" = c + 1 := by simp [σ₅]
  have hxp₅ : σ₅.vars "xp" = xp + tail := by simp [σ₅, σ₄, hxp₃']
  have hcnextB : c + 1 < B := by omega
  have hxoff₅ : σ₅.arrs "xoff" = arrOf (n + 1) Xoff := by
    simp [σ₅, σ₄, hxoff₃]
  let σ₆ := σ₅.setArr "xoff" (c + 1) (xp + tail)
  have run₆ : Run B (.store "xoff" (.var "c") (.var "xp")) σ₅ σ₆ 3 := by
    have h := Run.store (B := B) (σ := σ₅) (a := "xoff") (i := .var "c")
      (e := .var "xp") (evalB_var (by rw [hc₅]; exact hcnextB))
      (evalB_var (by rw [hxp₅]; exact hroomB))
      (by rw [hc₅, hxoff₅, length_arrOf]; omega)
    rw [hc₅, hxp₅] at h
    exact h.mono (by simp [Expr.size])
  have hraw₆ : RawCoverInvA G A₀ π centre q r (c + 1) (xp + tail)
      (upd Xoff (c + 1) (xp + tail)) Xmem'
      (queueCell asg q c r tail Q QD) (upd M (centre c) 0) := by
    apply Lax3Proofs.Refine.CoverActiveBlock.RawCoverInvA.stepQueue
      hcentres hraw hc htailn'
      (fun i hi => hQn i (by simpa [tail] using hi))
      (fun v hv => by simpa [tail] using hseg v hv)
      (fun i hi j hj hqij => hQinj i (by simpa [tail] using hi) j
        (by simpa [tail] using hj) hqij)
      (fun i hi k hk => hQD i (by simpa [tail] using hi) k hk)
    · intro k hk
      rw [upd_of_ne _ (by omega)]
    · rw [upd_self]
    · exact hkeep₃
    · exact hwrite₃'
    · intro w hw ha
      by_cases hset : asg w < q
      · simp [queueCell, hset]
      · have heq : asg w = q := by
          have := hraw.asg_le w hw ha
          omega
        simp [queueCell, caughtBefore, hset, heq]
    · intro u hu
      by_cases hus : u = centre c
      · simp [hus]
      · simp [hus]
  have hdist₆ : DistClean n (2 * r) (upd M (centre c) 0) σ₆ := by
    obtain ⟨D, hDarr, hclean⟩ := hdist₂
    refine ⟨D, ?_, cleanOn_upd_zero hclean⟩
    calc
      σ₆.arrs "dist" = σ₃.arrs "dist" := by simp [σ₆, σ₅, σ₄]
      _ = σ₂.arrs "dist" := hdistArr₃
      _ = arrOf n D := hDarr
  have hstate₆ : RawTurnState B ns nt q r (c + 1) (xp + tail) G A₀ π centre O T
      (upd Xoff (c + 1) (xp + tail)) Xmem'
      (queueCell asg q c r tail Q QD) (upd M (centre c) 0) σ₆ := by
    refine ⟨hraw₆, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hdist₆,
      ⟨Q, ?_⟩, ⟨QD, ?_⟩, ?_⟩
    · simp [σ₆, σ₅, σ₄, hn₃]
    · simp [σ₆, σ₅, σ₄, hqn₃]
    · simp [σ₆, σ₅]
    · simp [σ₆, hxp₅]
    · simp [σ₆, σ₅, σ₄, hord₃]
    · simp [σ₆, σ₅, σ₄, hoff₃]
    · simp [σ₆, σ₅, σ₄, htgt₃]
    · simp [σ₆, σ₅, σ₄, halv₃, set_arrOf_eq_upd]
    · simp [σ₆, σ₅, σ₄, hxoff₃, set_arrOf_eq_upd]
    · simpa [σ₆, σ₅, σ₄] using hxmem₃
    · simpa [σ₆, σ₅, σ₄] using hasg₃'
    · simpa [σ₆, σ₅, σ₄] using hq₃
    · simpa [σ₆, σ₅, σ₄] using hqd₃
    · intro z hz
      by_cases hzs : z = centre c
      · simpa [hzs] using hzeroB
      · simpa [hzs] using hMB z hz
  refine ⟨σ₆, _, run₁.seq (run₂.seq (run₃.seq (run₄.seq (run₅.seq run₆)))), ?_,
    tail, Q, QD, Xmem', htailnb', hstate₆⟩
  simp only [activeTurnK]
  omega

/-! ## Axiom audit -/

#print axioms activeTurnK_le_weight
#print axioms activeTurn_spec

end Lax3Proofs.Refine.CoverActiveTurn
