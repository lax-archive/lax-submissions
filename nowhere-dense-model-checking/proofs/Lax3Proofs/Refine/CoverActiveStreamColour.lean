import Lax3Proofs.Refine.CoverActiveStreamPlay

namespace Lax3Proofs.Refine.CoverActiveStreamColour

open Lax3.ColoredGraphs
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (CsrGraph masked)
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster
open Lax3Proofs.RamDriverDescend
open Lax3Proofs.Refine.CoverActiveStreamChild
open Lax3Proofs.Refine.CoverActiveStreamChildEnum
open Lax3Proofs.Refine.CoverActiveStreamEnum
open Lax3Proofs.Refine.CoverActiveStreamMask
open Lax3Proofs.Refine.CoverActiveStreamPlay
open Lax3Proofs.Refine.CoverActiveStreamSort
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! Carrier-free expansion, colouring, and palette-lifecycle proofs for the
streamed cover driver. -/

def streamExpandCom (idx msk src dst : String) : Com :=
  .seq (.assign "p" (.lit 0))
    (.seq (.assign "pend" (.var "tail"))
      (expandBlockLoop idx msk src dst))

def streamExpandCost (tail rowMass : ℕ) : ℕ :=
  51 * tail + 24 * rowMass + 8

theorem streamExpandCom_supported_spec
    {B n ns nt na tail : ℕ} {G : SimpleGraph (Fin n)}
    {O T Idx Msk Src A₀ : ℕ → ℕ} {idx msk src dst : String}
    (hcsr : CsrGraph G ns O T)
    (h1B : 1 < B) (hnB : n < B) (hnsB : ns < B)
    (htail : tail ≤ n) (hfit : tail ≤ na)
    (hIdx : ∀ q, q < tail → Idx q < n)
    (hMB : ∀ k, k < n → Msk k < B) (hSB : ∀ k, k < n → Src k < B)
    (hdi : dst ≠ idx) (hdm : dst ≠ msk) (hds : dst ≠ src)
    (hdo : dst ≠ "off") (hdt : dst ≠ "tgt") :
    Spec B
      (fun σ => σ.vars "tail" = tail ∧ σ.vars "n" = n ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧ ns ≤ nt ∧
        σ.arrs idx = arrOf na Idx ∧ σ.arrs msk = arrOf n Msk ∧
        σ.arrs src = arrOf n Src ∧ σ.arrs dst = arrOf n A₀ ∧
        BlockSupported n 0 tail Idx Msk ∧ BlockSupported n 0 tail Idx Src ∧
        BlockSupported n 0 tail Idx A₀)
      (streamExpandCom idx msk src dst)
      (fun _ σ' =>
        (∃ A, σ'.arrs dst = arrOf n A ∧
          (∀ v, v < n → A v = expandVal G Msk Src v) ∧
          BlockSupported n 0 tail Idx A) ∧
        σ'.vars "tail" = tail ∧ σ'.vars "n" = n ∧
        σ'.arrs "off" = arrOf (n + 1) O ∧ σ'.arrs "tgt" = arrOf nt T ∧ ns ≤ nt ∧
        σ'.arrs idx = arrOf na Idx ∧ σ'.arrs msk = arrOf n Msk ∧
        σ'.arrs src = arrOf n Src)
      (streamExpandCost tail (expandRowSum O Idx 0 tail)) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨htailVar, hn, hoff, htgt, hnt, hidx, hmsk, hsrc, hdst,
    hM, hS, hA₀⟩ := hσ
  have htailB : tail < B := lt_of_le_of_lt htail hnB
  set σ₁ := σ.setVar "p" 0 with hσ₁
  have r₁ : Run B (.assign "p" (.lit 0)) σ σ₁ 2 :=
    Run.assign (evalB_lit (by omega))
  have htail₁ : σ₁.vars "tail" = tail := by
    rw [hσ₁, vars_setVar, if_neg (by decide)]
    exact htailVar
  have etail : (Expr.var "tail").evalB B σ₁ = some tail := by
    have h := evalB_var (B := B) (x := "tail") (σ := σ₁) (by rw [htail₁]; exact htailB)
    rwa [htail₁] at h
  set σ₂ := σ₁.setVar "pend" tail with hσ₂
  have r₂ : Run B (.assign "pend" (.var "tail")) σ₁ σ₂ 2 :=
    Run.assign etail
  have hp₂ : σ₂.vars "p" = 0 := by
    rw [hσ₂, vars_setVar, if_neg (by decide), hσ₁, vars_setVar, if_pos rfl]
  have hpend₂ : σ₂.vars "pend" = tail := by simp [hσ₂]
  have htail₂ : σ₂.vars "tail" = tail := by
    rw [hσ₂, vars_setVar, if_neg (by decide)]
    exact htail₁
  have hn₂ : σ₂.vars "n" = n := by simp [hσ₂, hσ₁, hn]
  have hoff₂ : σ₂.arrs "off" = arrOf (n + 1) O := by simp [hσ₂, hσ₁, hoff]
  have htgt₂ : σ₂.arrs "tgt" = arrOf nt T := by simp [hσ₂, hσ₁, htgt]
  have hidx₂ : σ₂.arrs idx = arrOf na Idx := by simp [hσ₂, hσ₁, hidx]
  have hmsk₂ : σ₂.arrs msk = arrOf n Msk := by simp [hσ₂, hσ₁, hmsk]
  have hsrc₂ : σ₂.arrs src = arrOf n Src := by simp [hσ₂, hσ₁, hsrc]
  have hdst₂ : σ₂.arrs dst = arrOf n A₀ := by simp [hσ₂, hσ₁, hdst]
  have hI₂ : ExpandBlockInv n ns nt na 0 tail G O T Idx Msk Src A₀
      idx msk src dst σ₂ := by
    exact ⟨hpend₂, by omega, by omega, hn₂, hoff₂, htgt₂, hnt,
      hmsk₂, hsrc₂, hidx₂, A₀, hdst₂, by omega, by simp⟩
  obtain ⟨σ₃, r₃, hI₃, hp₃⟩ :=
    (expandBlockLoop_spec (A₀ := A₀) hcsr htailB hfit h1B hnB hnsB
      (fun q _ hq => hIdx q hq) hMB hSB hdi hdm hds hdo hdt).run
      ⟨hI₂, hp₂⟩
  obtain ⟨A, hA, hval, hsup⟩ := hI₃.done_eq hp₃ hA₀ hM hS
  obtain ⟨-, -, -, hn₃, hoff₃, htgt₃, -, hmsk₃, hsrc₃, hidx₃, -⟩ := hI₃
  have htail₃ : σ₃.vars "tail" = tail := by
    rw [r₃.frame_var "tail" (by
      simp [expandBlockLoop, expandStep, expandSlot, Csr.loadRow, Csr.scan, Com.wvars])]
    exact htail₂
  refine ⟨σ₃, 2 + (2 + (51 * (tail - 0) + 24 * expandRowSum O Idx 0 tail + 4)),
    r₁.seq (r₂.seq r₃), ?_, ⟨A, hA, hval, hsup⟩,
    htail₃, hn₃, hoff₃, htgt₃, hnt, hidx₃, hmsk₃, hsrc₃⟩
  simp only [Nat.sub_zero, streamExpandCost]
  omega

#print axioms streamExpandCom_supported_spec

theorem mem_warrs_streamExpandCom {idx msk src dst a : String}
    (h : a ∈ (streamExpandCom idx msk src dst).warrs) : a = dst := by
  simpa [streamExpandCom, expandBlockLoop, expandStep, expandSlot,
    Csr.loadRow, Csr.scan, Com.warrs] using h

def streamChainCom (idx msk : String) (nm : ℕ → String) (r : ℕ) : Com :=
  foldRange (fun a => streamExpandCom idx msk (nm a) (nm (a + 1))) r

theorem streamChainCom_zero (idx msk : String) (nm : ℕ → String) :
    streamChainCom idx msk nm 0 = .skip := rfl

theorem streamChainCom_succ (idx msk : String) (nm : ℕ → String) (r : ℕ) :
    streamChainCom idx msk nm (r + 1) =
      .seq (streamExpandCom idx msk (nm 0) (nm 1))
        (streamChainCom idx msk (fun a => nm (a + 1)) r) := by
  simp [streamChainCom, foldRange_succ]

theorem mem_warrs_streamChainCom {idx msk : String} {nm : ℕ → String}
    {r : ℕ} {a : String} (h : a ∈ (streamChainCom idx msk nm r).warrs) :
    ∃ b, b < r ∧ a = nm (b + 1) := by
  obtain ⟨b, hb, hm⟩ := RamDriverFrames.mem_warrs_foldRange
    (fun b => streamExpandCom idx msk (nm b) (nm (b + 1))) r h
  exact ⟨b, hb, mem_warrs_streamExpandCom hm⟩

/-- Every radius stage of a streamed prefix chain, with the exact same
whole-carrier semantics as the flat chain but a row-local charge. -/
theorem streamChainCom_stages
    {B n ns nt na tail : ℕ} {G : SimpleGraph (Fin n)}
    {O T Idx Msk : ℕ → ℕ} {idx msk : String}
    (hcsr : CsrGraph G ns O T)
    (h1B : 1 < B) (hnB : n < B) (hnsB : ns < B)
    (htail : tail ≤ n) (hfit : tail ≤ na)
    (hIdx : ∀ q, q < tail → Idx q < n)
    (hMB : ∀ k, k < n → Msk k < B)
    (hM : BlockSupported n 0 tail Idx Msk) :
    ∀ (r : ℕ) (nm : ℕ → String) (Sr : ℕ → ℕ),
      (∀ a b, a ≤ r → b ≤ r → a ≠ b → nm a ≠ nm b) →
      (∀ a, a ≤ r → nm a ≠ idx) →
      (∀ a, a ≤ r → nm a ≠ msk) →
      (∀ a, a ≤ r → nm a ≠ "off") →
      (∀ a, a ≤ r → nm a ≠ "tgt") →
      (∀ k, k < n → Sr k ≤ 1) →
      BlockSupported n 0 tail Idx Sr →
      Spec B
        (fun σ => σ.vars "tail" = tail ∧ σ.vars "n" = n ∧
          σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧ ns ≤ nt ∧
          σ.arrs idx = arrOf na Idx ∧ σ.arrs msk = arrOf n Msk ∧
          σ.arrs (nm 0) = arrOf n Sr ∧
          ∀ a, 0 < a → a ≤ r → ∃ F, σ.arrs (nm a) = arrOf n F ∧
            BlockSupported n 0 tail Idx F)
        (streamChainCom idx msk nm r)
        (fun _ σ' =>
          (∀ a, a ≤ r → ∃ F, σ'.arrs (nm a) = arrOf n F ∧
            (∀ k, k < n → F k ≤ 1) ∧
            markSet n F = ballOf (masked G Msk) a (markSet n Sr) ∧
            BlockSupported n 0 tail Idx F) ∧
          σ'.vars "tail" = tail ∧ σ'.vars "n" = n ∧
          σ'.arrs "off" = arrOf (n + 1) O ∧ σ'.arrs "tgt" = arrOf nt T ∧ ns ≤ nt ∧
          σ'.arrs idx = arrOf na Idx ∧ σ'.arrs msk = arrOf n Msk)
        (streamExpandCost tail (expandRowSum O Idx 0 tail) * r + 1) := by
  intro r
  induction r with
  | zero =>
      intro nm Sr _ _ _ _ _ hSB hS
      refine Spec.of_exists fun σ hσ => ⟨σ, 1, ?_, le_rfl, ?_⟩
      · rw [streamChainCom_zero]
        exact Run.skip
      · refine ⟨?_, hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2.1,
          hσ.2.2.2.2.1, hσ.2.2.2.2.2.1, hσ.2.2.2.2.2.2.1⟩
        intro a ha
        have ha0 : a = 0 := by omega
        subst a
        exact ⟨Sr, hσ.2.2.2.2.2.2.2.1, hSB, by rw [ballOf_zero], hS⟩
  | succ r ih =>
      intro nm Sr hne hni hnm hno hntg hSB hS
      refine Spec.of_exists fun σ hσ => ?_
      obtain ⟨A₁, hA₁, hA₁sup⟩ := hσ.2.2.2.2.2.2.2.2 1 (by omega) (by omega)
      have hSrB : ∀ k, k < n → Sr k < B :=
        fun k hk => lt_of_le_of_lt (hSB k hk) h1B
      obtain ⟨σ₁, hr₁, ⟨F, hF, hFval, hFsup⟩,
          htail₁, hn₁, hoff₁, htgt₁, hnt₁, hidx₁, hmsk₁, hsrc₁⟩ :=
        (streamExpandCom_supported_spec (A₀ := A₁) hcsr h1B hnB hnsB
          htail hfit hIdx hMB hSrB
          (hni 1 (by omega)) (hnm 1 (by omega))
          (hne 1 0 (by omega) (by omega) (by omega))
          (hno 1 (by omega)) (hntg 1 (by omega))).run
          ⟨hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2.1, hσ.2.2.2.2.1,
            hσ.2.2.2.2.2.1, hσ.2.2.2.2.2.2.1, hσ.2.2.2.2.2.2.2.1,
            hA₁, hM, hS, hA₁sup⟩
      have hFbit : ∀ k, k < n → F k ≤ 1 := by
        intro k hk
        rw [hFval k hk]
        rcases expandVal_eq_or G Msk Sr k with h | h
        · rw [h]
        · rw [h]
          exact hSB k hk
      have hfuture : ∀ a, 0 < a → a ≤ r →
          ∃ A, σ₁.arrs (nm (a + 1)) = arrOf n A ∧ BlockSupported n 0 tail Idx A := by
        intro a ha har
        apply exists_blockSupported_run hr₁
        · intro hc
          have heq := mem_warrs_streamExpandCom hc
          exact hne (a + 1) 1 (by omega) (by omega) (by omega) heq
        · exact hσ.2.2.2.2.2.2.2.2 (a + 1) (by omega) (by omega)
      obtain ⟨σ₂, hr₂, hstage₂, htail₂, hn₂, hoff₂, htgt₂,
          hnt₂, hidx₂, hmsk₂⟩ :=
        (ih (fun a => nm (a + 1)) F
          (fun a b ha hb hab => hne (a + 1) (b + 1) (by omega) (by omega) (by omega))
          (fun a ha => hni (a + 1) (by omega))
          (fun a ha => hnm (a + 1) (by omega))
          (fun a ha => hno (a + 1) (by omega))
          (fun a ha => hntg (a + 1) (by omega)) hFbit hFsup).run
          ⟨htail₁, hn₁, hoff₁, htgt₁, hnt₁, hidx₁, hmsk₁,
            hF, hfuture⟩
      have hzero : σ₂.arrs (nm 0) = arrOf n Sr := by
        rw [hr₂.frame_arr (nm 0) (by
          intro hc
          obtain ⟨b, hb, hbe⟩ := mem_warrs_streamChainCom hc
          exact hne 0 (b + 2) (by omega) (by omega) (by omega) hbe), hsrc₁]
      have hrun : Run B (streamChainCom idx msk nm (r + 1)) σ σ₂
          (streamExpandCost tail (expandRowSum O Idx 0 tail) +
            (streamExpandCost tail (expandRowSum O Idx 0 tail) * r + 1)) := by
        rw [streamChainCom_succ]
        exact hr₁.seq hr₂
      refine ⟨σ₂, _, hrun, ?_, ?_, htail₂, hn₂, hoff₂, htgt₂,
        hnt₂, hidx₂, hmsk₂⟩
      · ring_nf
        exact le_rfl
      · intro a ha
        match a with
        | 0 => exact ⟨Sr, hzero, hSB, by rw [ballOf_zero], hS⟩
        | a + 1 =>
          obtain ⟨F', hF', hF'bit, hF'mark, hF'sup⟩ := hstage₂ a (by omega)
          refine ⟨F', hF', hF'bit, ?_, hF'sup⟩
          rw [hF'mark, markSet_congr hFval, markSet_expandVal, ballOf_nbhd]

#print axioms streamChainCom_stages

/-! The shared memory invariant of streamed colouring.  Every destination
slot is already row-supported; the fused level will establish that lifecycle
once, and every sparse colour pass preserves it. -/

structure StreamColPre (n ns nt na tail cap mb j : ℕ)
    (O T : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
    (Xmem Xa Ra Wf : ℕ → ℕ) (σ : Env) : Prop where
  tail_var : σ.vars "tail" = tail
  n_var : σ.vars "n" = n
  off_arr : σ.arrs "off" = arrOf (n + 1) O
  target_arr : σ.arrs "tgt" = arrOf nt T
  target_fit : ns ≤ nt
  row_arr : σ.arrs "xmem" = arrOf na Xmem
  cluster_arr : σ.arrs (cluName j) = arrOf n Xa
  retained_arr : σ.arrs (resName j) = arrOf n Ra
  old_colours : ∀ c, c < sigL cap mb j → σ.arrs (colName j c) = arrOf n (C c)
  batch_arr : σ.arrs "wa" = arrOf mb Wf
  next_slots : ∀ s, s < sigL cap mb (j + 1) →
    ∃ F, σ.arrs (colName (j + 1) s) = arrOf n F ∧
      BlockSupported n 0 tail Xmem F

/-- Sparse support certificates that must survive the recursive centre body
so that all depth-local buffers can be released on the same resident row.
They are semantic facts about the produced functions, independent of the
machine state that subsequently stores them. -/
structure StreamReuseSupports (n tail : ℕ)
    (Xmem Xa Ra Wa Alv Gam : ℕ → ℕ) : Prop where
  cluster : BlockSupported n 0 tail Xmem Xa
  retained : BlockSupported n 0 tail Xmem Ra
  batch : BlockSupported n 0 tail Xmem Wa
  child : BlockSupported n 0 tail Xmem Alv
  game : BlockSupported n 0 tail Xmem Gam

theorem StreamColPre.run_supported
    {B K n ns nt na tail cap mb j : ℕ}
    {O T : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {Xmem Xa Ra Wf : ℕ → ℕ} {σ σ' : Env} {cmd : Com}
    (h : StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ)
    (hr : Run B cmd σ σ' K)
    (htail : σ'.vars "tail" = σ.vars "tail")
    (hn : σ'.vars "n" = σ.vars "n")
    (hw : ∀ a ∈ cmd.warrs, ∃ s, s < sigL cap mb (j + 1) ∧
      a = colName (j + 1) s)
    (hout : ∀ s, s < sigL cap mb (j + 1) →
      colName (j + 1) s ∈ cmd.warrs →
      ∃ F, σ'.arrs (colName (j + 1) s) = arrOf n F ∧
        BlockSupported n 0 tail Xmem F) :
    StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ' := by
  have frame (a : String) (ha : ∀ s, s < sigL cap mb (j + 1) →
      a ≠ colName (j + 1) s) : σ'.arrs a = σ.arrs a := by
    exact hr.frame_arr a (fun hc => by
      obtain ⟨s, hs, he⟩ := hw a hc
      exact ha s hs he)
  refine {
    tail_var := by rw [htail]; exact h.tail_var
    n_var := by rw [hn]; exact h.n_var
    off_arr := by
      rw [frame "off" (fun s _ => Ne.symm (colName_ne_lit (by decide)))]
      exact h.off_arr
    target_arr := by
      rw [frame "tgt" (fun s _ => Ne.symm (colName_ne_lit (by decide)))]
      exact h.target_arr
    target_fit := h.target_fit
    row_arr := by
      rw [frame "xmem" (fun s _ => Ne.symm (colName_ne_lit (by decide)))]
      exact h.row_arr
    cluster_arr := by
      rw [frame (cluName j) (fun s _ => Ne.symm (colName_ne_cluName _ _ _))]
      exact h.cluster_arr
    retained_arr := by
      rw [frame (resName j) (fun s _ => Ne.symm (colName_ne_resName _ _ _))]
      exact h.retained_arr
    old_colours := fun c hc => by
      rw [frame (colName j c) (fun s _ => colName_ne_depth (by omega))]
      exact h.old_colours c hc
    batch_arr := by
      rw [frame "wa" (fun s _ => Ne.symm (colName_ne_lit (by decide)))]
      exact h.batch_arr
    next_slots := fun s hs => by
      by_cases hsc : colName (j + 1) s ∈ cmd.warrs
      · exact hout s hs hsc
      · obtain ⟨F, hF, hFsup⟩ := h.next_slots s hs
        exact ⟨F, by rw [hr.frame_arr _ hsc]; exact hF, hFsup⟩ }

#print axioms StreamColPre.run_supported

theorem mem_warrs_streamBlockMapCom {idx dst : String} {x : Expr} {a : String}
    (h : a ∈ (streamBlockMapCom idx dst x).warrs) : a = dst := by
  simpa [streamBlockMapCom, BlockLeaves.blockMapRangeCom, Com.warrs] using h

theorem streamOldBody_spec
    {B n ns nt na tail cap mb j c : ℕ}
    {O T : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {Xmem Xa Ra Wf : ℕ → ℕ}
    (h1B : 1 < B) (hnB : n < B) (htail : tail ≤ n) (hfit : tail ≤ na)
    (hIdx : ∀ q, q < tail → Xmem q < n)
    (hCB : ∀ k, k < n → C c k < B) (hXB : ∀ k, k < n → Xa k < B)
    (hCbit : ∀ k, k < n → C c k ≤ 1) (hXbit : ∀ k, k < n → Xa k ≤ 1)
    (hXsup : BlockSupported n 0 tail Xmem Xa)
    (hc : c < sigL cap mb j) :
    Spec B
      (StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf)
      (streamBlockAndCom "xmem" (colName j c) (cluName j)
        (colName (j + 1) (oldIdx cap mb j c)))
      (fun _ σ' =>
        StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ' ∧
        ∃ F, σ'.arrs (colName (j + 1) (oldIdx cap mb j c)) = arrOf n F ∧
          (∀ k, k < n → F k ≤ 1) ∧
          markSet n F = markSet n (C c) ∩ markSet n Xa ∧
          BlockSupported n 0 tail Xmem F)
      (streamBlockAndCost tail) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨g₀, hg₀, hg₀sup⟩ := hσ.next_slots (oldIdx cap mb j c) (oldIdx_lt_sigL c)
  have hprodSup : BlockSupported n 0 tail Xmem (fun v => C c v * Xa v) :=
    blockSupported_mul_right hXsup
  have hprodB : ∀ q, q < tail → C c (Xmem q) * Xa (Xmem q) < B := by
    intro q hq
    have hqN := hIdx q hq
    have h1 := hCbit (Xmem q) hqN
    have h2 := hXbit (Xmem q) hqN
    calc
      C c (Xmem q) * Xa (Xmem q) ≤ 1 * 1 := Nat.mul_le_mul h1 h2
      _ = 1 := by omega
      _ < B := h1B
  obtain ⟨σ', hr, ⟨⟨F, hF, hFval, hFsup⟩, htail', hrow', hcol', hclu'⟩,
      hfv, -, -, -⟩ :=
    ((streamBlockAndCom_supported_spec (idx := "xmem")
      (a := colName j c) (b := cluName j)
      (dst := colName (j + 1) (oldIdx cap mb j c))
      h1B hnB htail hfit hIdx hCB hXB hprodB
      (colName_ne_lit (q := "xmem") (by decide))
      (colName_ne_depth (by omega))
      (colName_ne_cluName _ _ _)).frame).run
      ⟨hσ.tail_var, hσ.row_arr, hg₀,
        ⟨hσ.old_colours c hc, hσ.cluster_arr⟩, hprodSup, hg₀sup⟩
  have hn' : σ'.vars "n" = σ.vars "n" := hfv "n" (by
    simp [streamBlockAndCom, streamBlockMapCom, BlockLeaves.blockMapRangeCom, Com.wvars])
  have hpre' : StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ' :=
    hσ.run_supported hr (by rw [htail', hσ.tail_var]) hn'
      (fun a ha => ⟨oldIdx cap mb j c, oldIdx_lt_sigL c,
        mem_warrs_streamBlockMapCom ha⟩)
      (fun s hs hsw => by
        have he := mem_warrs_streamBlockMapCom hsw
        have hsc : s = oldIdx cap mb j c := (colName_inj he).2
        subst s
        exact ⟨F, hF, hFsup⟩)
  refine ⟨σ', streamBlockAndCost tail, hr, le_rfl, hpre', F, hF, ?_, ?_, hFsup⟩
  · intro k hk
    rw [hFval k hk]
    exact (Nat.mul_le_mul (hCbit k hk) (hXbit k hk)).trans (by omega)
  · rw [markSet_congr hFval, markSet_mul]

#print axioms streamOldBody_spec

theorem streamOldLast_spec
    {B n ns nt na tail cap mb j : ℕ}
    {O T : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {Xmem Xa Ra Wf : ℕ → ℕ}
    (h1B : 1 < B) (hnB : n < B) (htail : tail ≤ n) (hfit : tail ≤ na)
    (hIdx : ∀ q, q < tail → Xmem q < n)
    (hXB : ∀ k, k < n → Xa k < B) (hXbit : ∀ k, k < n → Xa k ≤ 1)
    (hXsup : BlockSupported n 0 tail Xmem Xa) :
    Spec B
      (StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf)
      (streamBlockAndCom "xmem" (cluName j) (cluName j)
        (colName (j + 1) (oldIdx cap mb j (sigL cap mb j))))
      (fun _ σ' =>
        StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ' ∧
        ∃ F, σ'.arrs (colName (j + 1) (oldIdx cap mb j (sigL cap mb j))) =
            arrOf n F ∧
          (∀ k, k < n → F k ≤ 1) ∧ markSet n F = markSet n Xa ∧
          BlockSupported n 0 tail Xmem F)
      (streamBlockAndCost tail) := by
  refine Spec.of_exists fun σ hσ => ?_
  let s₀ := oldIdx cap mb j (sigL cap mb j)
  obtain ⟨g₀, hg₀, hg₀sup⟩ := hσ.next_slots s₀ (oldIdx_lt_sigL _)
  have hprodSup : BlockSupported n 0 tail Xmem (fun v => Xa v * Xa v) :=
    blockSupported_mul_left hXsup
  have hprodB : ∀ q, q < tail → Xa (Xmem q) * Xa (Xmem q) < B := by
    intro q hq
    have hqN := hIdx q hq
    calc
      Xa (Xmem q) * Xa (Xmem q) ≤ 1 * 1 :=
        Nat.mul_le_mul (hXbit _ hqN) (hXbit _ hqN)
      _ = 1 := by omega
      _ < B := h1B
  obtain ⟨σ', hr, ⟨⟨F, hF, hFval, hFsup⟩, htail', -, -, -⟩,
      hfv, -, -, -⟩ :=
    ((streamBlockAndCom_supported_spec (idx := "xmem")
      (a := cluName j) (b := cluName j) (dst := colName (j + 1) s₀)
      h1B hnB htail hfit hIdx hXB hXB hprodB
      (colName_ne_lit (q := "xmem") (by decide))
      (colName_ne_cluName _ _ _) (colName_ne_cluName _ _ _)).frame).run
      ⟨hσ.tail_var, hσ.row_arr, hg₀, ⟨hσ.cluster_arr, hσ.cluster_arr⟩,
        hprodSup, hg₀sup⟩
  have hn' : σ'.vars "n" = σ.vars "n" := hfv "n" (by
    simp [streamBlockAndCom, streamBlockMapCom, BlockLeaves.blockMapRangeCom, Com.wvars])
  have hpre' : StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ' :=
    hσ.run_supported hr (by rw [htail', hσ.tail_var]) hn'
      (fun a ha => ⟨s₀, oldIdx_lt_sigL _, mem_warrs_streamBlockMapCom ha⟩)
      (fun s hs hsw => by
        have he := mem_warrs_streamBlockMapCom hsw
        have hsc : s = s₀ := (colName_inj he).2
        subst s
        exact ⟨F, hF, hFsup⟩)
  have hFxa : ∀ k, k < n → F k = Xa k := by
    intro k hk
    rw [hFval k hk]
    have hx := hXbit k hk
    rcases Nat.eq_zero_or_pos (Xa k) with hz | hp
    · simp [hz]
    · have ho : Xa k = 1 := by omega
      simp [ho]
  refine ⟨σ', streamBlockAndCost tail, hr, le_rfl, hpre', F, hF, ?_, ?_, hFsup⟩
  · intro k hk
    rw [hFxa k hk]
    exact hXbit k hk
  · exact markSet_congr hFxa

#print axioms streamOldLast_spec

def streamOldCom (cap mb j : ℕ) : Com :=
  .seq (foldRange (fun c =>
      streamBlockAndCom "xmem" (colName j c) (cluName j)
        (colName (j + 1) (oldIdx cap mb j c))) (sigL cap mb j))
    (streamBlockAndCom "xmem" (cluName j) (cluName j)
      (colName (j + 1) (oldIdx cap mb j (sigL cap mb j))))

def streamOldCost (tail L : ℕ) : ℕ :=
  streamBlockAndCost tail * L + 1 + streamBlockAndCost tail

theorem streamOldCom_spec
    {B n ns nt na tail cap mb j : ℕ}
    {O T : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {Xmem Xa Ra Wf : ℕ → ℕ}
    (h1B : 1 < B) (hnB : n < B) (htail : tail ≤ n) (hfit : tail ≤ na)
    (hIdx : ∀ q, q < tail → Xmem q < n)
    (hCbit : ∀ c, c < sigL cap mb j → ∀ k, k < n → C c k ≤ 1)
    (hXbit : ∀ k, k < n → Xa k ≤ 1)
    (hXsup : BlockSupported n 0 tail Xmem Xa) :
    Spec B
      (StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf)
      (streamOldCom cap mb j)
      (fun _ σ' =>
        StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ' ∧
        ∀ c : Fin (sigL cap mb j + 1), ∃ F,
          σ'.arrs (colName (j + 1) (oldIdx cap mb j (c : ℕ))) = arrOf n F ∧
          (∀ k, k < n → F k ≤ 1) ∧
          markSet n F =
            Evaluator.relColoring (colRead n C (sigL cap mb j)) (markSet n Xa) c ∧
          BlockSupported n 0 tail Xmem F)
      (streamOldCost tail (sigL cap mb j)) := by
  have hCB : ∀ c, c < sigL cap mb j → ∀ k, k < n → C c k < B :=
    fun c hc k hk => lt_of_le_of_lt (hCbit c hc k hk) h1B
  have hXB : ∀ k, k < n → Xa k < B :=
    fun k hk => lt_of_le_of_lt (hXbit k hk) h1B
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨σ₁, hr₁, ⟨hpre₁, hR₁⟩, -, -, -, -⟩ :=
    ((foldr_family_spec
      (body := fun c => streamBlockAndCom "xmem" (colName j c) (cluName j)
        (colName (j + 1) (oldIdx cap mb j c)))
      (I := StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf)
      (R := fun c ρ => ∃ F,
        ρ.arrs (colName (j + 1) (oldIdx cap mb j c)) = arrOf n F ∧
        (∀ k, k < n → F k ≤ 1) ∧
        markSet n F = markSet n (C c) ∩ markSet n Xa ∧
        BlockSupported n 0 tail Xmem F)
      (Wr := fun c a => a = colName (j + 1) (oldIdx cap mb j c))
      (Kb := streamBlockAndCost tail)
      (fun _ a ha => mem_warrs_streamBlockMapCom ha)
      (fun _ _ _ hR hfr => by
        obtain ⟨F, hF, hFbit, hFmark, hFsup⟩ := hR
        exact ⟨F, by rw [hfr _ rfl]; exact hF, hFbit, hFmark, hFsup⟩)
      (List.range (sigL cap mb j)) (List.nodup_range)
      (fun c hc => streamOldBody_spec h1B hnB htail hfit hIdx
        (hCB c (List.mem_range.mp hc)) hXB (hCbit c (List.mem_range.mp hc))
        hXbit hXsup (List.mem_range.mp hc))
      (fun x hx y hy hxy a hax hay => hxy (oldIdx_inj
        (le_of_lt (List.mem_range.mp hx)) (le_of_lt (List.mem_range.mp hy))
        (colName_inj (hax ▸ hay : colName (j + 1) (oldIdx cap mb j x) =
          colName (j + 1) (oldIdx cap mb j y))).2))).frame).run hσ
  obtain ⟨σ₂, hr₂, ⟨hpre₂, hlast⟩, -, hfa₂, -, -⟩ :=
    ((streamOldLast_spec h1B hnB htail hfit hIdx hXB hXbit hXsup).frame).run hpre₁
  have hR₂ : ∀ c ∈ List.range (sigL cap mb j), ∃ F,
      σ₂.arrs (colName (j + 1) (oldIdx cap mb j c)) = arrOf n F ∧
      (∀ k, k < n → F k ≤ 1) ∧
      markSet n F = markSet n (C c) ∩ markSet n Xa ∧
      BlockSupported n 0 tail Xmem F := by
    intro c hc
    have hclt : c < sigL cap mb j := List.mem_range.mp hc
    obtain ⟨F, hF, hFbit, hFmark, hFsup⟩ := hR₁ c hc
    refine ⟨F, ?_, hFbit, hFmark, hFsup⟩
    rw [hfa₂ _ (by
      intro hw
      have he := mem_warrs_streamBlockMapCom hw
      have heq := (colName_inj he).2
      have hcL : c = sigL cap mb j := oldIdx_inj (le_of_lt hclt) le_rfl heq
      exact (Nat.ne_of_lt hclt) hcL), hF]
  refine ⟨σ₂, _, by rw [streamOldCom]; exact hr₁.seq hr₂, ?_, hpre₂, ?_⟩
  · simp only [streamOldCost, List.length_range]
    omega
  · intro c
    refine Fin.lastCases ?_ ?_ c
    · obtain ⟨F, hF, hFbit, hFmark, hFsup⟩ := hlast
      exact ⟨F, hF, hFbit, by rw [hFmark, Evaluator.relColoring_last], hFsup⟩
    · intro c₀
      obtain ⟨F, hF, hFbit, hFmark, hFsup⟩ :=
        hR₂ (c₀ : ℕ) (List.mem_range.mpr c₀.isLt)
      exact ⟨F, hF, hFbit,
        by rw [hFmark, Evaluator.relColoring_castSucc]; rfl, hFsup⟩

#print axioms streamOldCom_spec

def streamPdBodyCom (cap mb j : ℕ) (i : Fin mb) : Com :=
  .seq (streamBlockClearCom "xmem" (colName (j + 1) (pdIdx cap mb j i 0)))
    (.seq (.store (colName (j + 1) (pdIdx cap mb j i 0))
        (.get "wa" (.lit (i : ℕ))) (.lit 1))
      (streamChainCom "xmem" (resName j)
        (fun a => colName (j + 1) (pdIdx cap mb j i a)) cap))

def streamPdBodyCost (tail rowMass cap : ℕ) : ℕ :=
  streamBlockClearCost tail + 4 + (streamExpandCost tail rowMass * cap + 1)

theorem streamPdBody_spec
    {B n ns nt na tail cap mb j : ℕ} {G : SimpleGraph (Fin n)}
    {O T : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {Xmem Xa Ra Wf : ℕ → ℕ} {w : Fin mb → Fin n}
    (hcsr : CsrGraph G ns O T)
    (h1B : 1 < B) (hnB : n < B) (hnsB : ns < B) (hmbB : mb < B)
    (htail : tail ≤ n) (hfit : tail ≤ na)
    (hIdx : ∀ q, q < tail → Xmem q < n)
    (hRaB : ∀ k, k < n → Ra k < B) (hRsup : BlockSupported n 0 tail Xmem Ra)
    (hWf : ∀ i : Fin mb, Wf (i : ℕ) = (w i : ℕ))
    (hWrow : ∀ i : Fin mb, ∃ q, q < tail ∧ Xmem q = (w i : ℕ))
    (i : Fin mb) :
    Spec B
      (StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf)
      (streamPdBodyCom cap mb j i)
      (fun _ σ' =>
        StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ' ∧
        ∀ a, a ≤ cap → ∃ F,
          σ'.arrs (colName (j + 1) (pdIdx cap mb j i a)) = arrOf n F ∧
          (∀ k, k < n → F k ≤ 1) ∧
          markSet n F = ballOf (masked G Ra) a {w i} ∧
          BlockSupported n 0 tail Xmem F)
      (streamPdBodyCost tail (expandRowSum O Xmem 0 tail) cap) := by
  refine Spec.of_exists fun σ hσ => ?_
  let nm : ℕ → String := fun a => colName (j + 1) (pdIdx cap mb j i a)
  obtain ⟨g₀, hg₀, hg₀sup⟩ := hσ.next_slots (pdIdx cap mb j i 0) (pdIdx_lt_sigL i 0)
  obtain ⟨σ₁, hr₁, ⟨⟨g₁, hg₁, hg₁val, hg₁sup⟩, htail₁, hrow₁⟩,
      hfv₁, -, -, -⟩ :=
    ((streamBlockClearCom_supported_spec (idx := "xmem")
      (dst := nm 0) h1B hnB htail hfit hIdx
      (colName_ne_lit (q := "xmem") (by decide))).frame).run
      ⟨hσ.tail_var, hσ.row_arr, hg₀, hg₀sup⟩
  have hn₁eq : σ₁.vars "n" = σ.vars "n" := hfv₁ "n" (by
    simp [streamBlockClearCom, streamBlockMapCom, BlockLeaves.blockMapRangeCom, Com.wvars])
  have hpre₁ : StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ₁ :=
    hσ.run_supported hr₁ (by rw [htail₁, hσ.tail_var]) hn₁eq
      (fun a ha => ⟨pdIdx cap mb j i 0, pdIdx_lt_sigL i 0,
        mem_warrs_streamBlockMapCom ha⟩)
      (fun s hs hsw => by
        have he := mem_warrs_streamBlockMapCom hsw
        have hse : s = pdIdx cap mb j i 0 := (colName_inj he).2
        subst s
        exact ⟨g₁, hg₁, hg₁sup⟩)
  have hwi : Wf (i : ℕ) < n := by rw [hWf i]; exact (w i).isLt
  have hwiB : Wf (i : ℕ) < B := lt_trans hwi hnB
  have ewa : (Expr.get "wa" (.lit (i : ℕ))).evalB B σ₁ = some (Wf (i : ℕ)) :=
    evalB_get (evalB_lit (lt_trans i.isLt hmbB))
      (by rw [hpre₁.batch_arr, getElem?_arrOf Wf i.isLt]) hwiB
  have hlen : Wf (i : ℕ) < (σ₁.arrs (nm 0)).length := by
    rw [hg₁, length_arrOf]
    exact hwi
  set σ₂ := σ₁.setArr (nm 0) (Wf (i : ℕ)) 1 with hσ₂
  have hr₂ : Run B (.store (nm 0) (.get "wa" (.lit (i : ℕ))) (.lit 1))
      σ₁ σ₂ 4 :=
    (Run.store ewa (evalB_lit h1B) hlen).mono (by simp [Expr.size])
  let S := upd g₁ (Wf (i : ℕ)) 1
  have hSarr : σ₂.arrs (nm 0) = arrOf n S := by
    simp [hσ₂, hg₁, S, set_arrOf_eq_upd]
  have hSsup : BlockSupported n 0 tail Xmem S := by
    intro v hv hout
    have hvw : v ≠ Wf (i : ℕ) := by
      intro he
      obtain ⟨q, hq, hqw⟩ := hWrow i
      exact (hout q (by omega) hq) (calc
        Xmem q = (w i : ℕ) := hqw
        _ = Wf (i : ℕ) := (hWf i).symm
        _ = v := he.symm)
    change upd g₁ (Wf (i : ℕ)) 1 v = 0
    rw [upd_of_ne _ hvw, hg₁val v hv]
  have hSbit : ∀ k, k < n → S k ≤ 1 := by
    intro k hk
    by_cases hki : k = Wf (i : ℕ)
    · change upd g₁ (Wf (i : ℕ)) 1 k ≤ 1
      simp [hki]
    · change upd g₁ (Wf (i : ℕ)) 1 k ≤ 1
      rw [upd_of_ne _ hki, hg₁val k hk]
      omega
  have hSmark : markSet n S = {w i} := by
    ext v
    rw [mem_markSet, Set.mem_singleton_iff]
    constructor
    · intro hv
      by_cases hve : (v : ℕ) = Wf (i : ℕ)
      · exact Fin.ext (by rw [hve, hWf i])
      · exact absurd (by
          change upd g₁ (Wf (i : ℕ)) 1 (v : ℕ) = 0
          rw [upd_of_ne _ hve, hg₁val (v : ℕ) v.isLt]) hv
    · rintro rfl
      rw [show ((w i : Fin n) : ℕ) = Wf (i : ℕ) from (hWf i).symm]
      change upd g₁ (Wf (i : ℕ)) 1 (Wf (i : ℕ)) ≠ 0
      rw [upd_self]
      omega
  have hpre₂ : StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ₂ :=
    hpre₁.run_supported hr₂ (by simp [hσ₂]) (by simp [hσ₂])
      (fun a ha => by
        simp only [Com.warrs, List.mem_singleton] at ha
        exact ⟨pdIdx cap mb j i 0, pdIdx_lt_sigL i 0, ha⟩)
      (fun s hs hsw => by
        simp only [Com.warrs, List.mem_singleton] at hsw
        have hse : s = pdIdx cap mb j i 0 := (colName_inj hsw).2
        subst s
        exact ⟨S, hSarr, hSsup⟩)
  obtain ⟨σ₃, hr₃, hstage, htail₃, hn₃, hoff₃, htgt₃, hnt₃,
      hrow₃, hres₃⟩ :=
    (streamChainCom_stages (idx := "xmem") (msk := resName j)
      hcsr h1B hnB hnsB htail hfit hIdx hRaB hRsup cap nm S
      (fun a b ha hb hab he => hab (pdIdx_inj ha hb (colName_inj he).2).2)
      (fun a _ => colName_ne_lit (q := "xmem") (by decide))
      (fun a _ => colName_ne_resName _ _ _)
      (fun a _ => colName_ne_lit (q := "off") (by decide))
      (fun a _ => colName_ne_lit (q := "tgt") (by decide))
      hSbit hSsup).run
      ⟨hpre₂.tail_var, hpre₂.n_var, hpre₂.off_arr, hpre₂.target_arr,
        hpre₂.target_fit, hpre₂.row_arr, hpre₂.retained_arr, hSarr,
        fun a ha hac => by
          obtain ⟨A, hA, hAsup⟩ := hpre₂.next_slots (pdIdx cap mb j i a)
            (pdIdx_lt_sigL i a)
          exact ⟨A, hA, hAsup⟩⟩
  have hpre₃ : StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ₃ :=
    hpre₂.run_supported hr₃ (by rw [htail₃, hpre₂.tail_var])
      (by rw [hn₃, hpre₂.n_var])
      (fun a ha => by
        obtain ⟨b, hb, hbe⟩ := mem_warrs_streamChainCom ha
        exact ⟨pdIdx cap mb j i (b + 1), pdIdx_lt_sigL i (b + 1), hbe⟩)
      (fun s hs hsw => by
        obtain ⟨b, hb, hbe⟩ := mem_warrs_streamChainCom hsw
        have hse : s = pdIdx cap mb j i (b + 1) := (colName_inj hbe).2
        subst s
        obtain ⟨F, hF, -, -, hFsup⟩ := hstage (b + 1) (by omega)
        exact ⟨F, hF, hFsup⟩)
  have hrun : Run B (streamPdBodyCom cap mb j i) σ σ₃
      (streamBlockClearCost tail + (4 +
        (streamExpandCost tail (expandRowSum O Xmem 0 tail) * cap + 1))) := by
    rw [streamPdBodyCom]
    exact hr₁.seq (hr₂.seq hr₃)
  refine ⟨σ₃, _, hrun, ?_, hpre₃, ?_⟩
  · simp only [streamPdBodyCost]
    omega
  · intro a ha
    obtain ⟨F, hF, hFbit, hFmark, hFsup⟩ := hstage a ha
    exact ⟨F, hF, hFbit, by rw [hFmark, hSmark], hFsup⟩

#print axioms streamPdBody_spec

def streamPdCom (cap mb j : ℕ) : Com :=
  (List.finRange mb).foldr (fun i cmd => .seq (streamPdBodyCom cap mb j i) cmd) .skip

def streamPdCost (tail rowMass cap mb : ℕ) : ℕ :=
  streamPdBodyCost tail rowMass cap * mb + 1

theorem mem_warrs_streamPdBodyCom {cap mb j : ℕ} {i : Fin mb} {a : String}
    (h : a ∈ (streamPdBodyCom cap mb j i).warrs) :
    ∃ b, b ≤ cap ∧ a = colName (j + 1) (pdIdx cap mb j i b) := by
  simp only [streamPdBodyCom, Com.warrs, List.mem_append] at h
  rcases h with h | h | h
  · exact ⟨0, by omega, mem_warrs_streamBlockMapCom h⟩
  · simp only [List.mem_singleton] at h
    exact ⟨0, by omega, h⟩
  · obtain ⟨b, hb, hbe⟩ := mem_warrs_streamChainCom h
    exact ⟨b + 1, by omega, hbe⟩

theorem streamPdCom_spec
    {B n ns nt na tail cap mb j : ℕ} {G : SimpleGraph (Fin n)}
    {O T : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {Xmem Xa Ra Wf : ℕ → ℕ} {w : Fin mb → Fin n}
    (hcsr : CsrGraph G ns O T)
    (h1B : 1 < B) (hnB : n < B) (hnsB : ns < B) (hmbB : mb < B)
    (htail : tail ≤ n) (hfit : tail ≤ na)
    (hIdx : ∀ q, q < tail → Xmem q < n)
    (hRaB : ∀ k, k < n → Ra k < B) (hRsup : BlockSupported n 0 tail Xmem Ra)
    (hWf : ∀ i : Fin mb, Wf (i : ℕ) = (w i : ℕ))
    (hWrow : ∀ i : Fin mb, ∃ q, q < tail ∧ Xmem q = (w i : ℕ)) :
    Spec B
      (StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf)
      (streamPdCom cap mb j)
      (fun _ σ' =>
        StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ' ∧
        ∀ (i : Fin mb) a, a ≤ cap → ∃ F,
          σ'.arrs (colName (j + 1) (pdIdx cap mb j i a)) = arrOf n F ∧
          (∀ k, k < n → F k ≤ 1) ∧
          markSet n F = ballOf (masked G Ra) a {w i} ∧
          BlockSupported n 0 tail Xmem F)
      (streamPdCost tail (expandRowSum O Xmem 0 tail) cap mb) := by
  have h := foldr_family_spec
    (body := fun i : Fin mb => streamPdBodyCom cap mb j i)
    (I := StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf)
    (R := fun i ρ => ∀ a, a ≤ cap → ∃ F,
      ρ.arrs (colName (j + 1) (pdIdx cap mb j i a)) = arrOf n F ∧
      (∀ k, k < n → F k ≤ 1) ∧
      markSet n F = ballOf (masked G Ra) a {w i} ∧
      BlockSupported n 0 tail Xmem F)
    (Wr := fun i a => ∃ b, b ≤ cap ∧
      a = colName (j + 1) (pdIdx cap mb j i b))
    (Kb := streamPdBodyCost tail (expandRowSum O Xmem 0 tail) cap)
    (fun i a ha => mem_warrs_streamPdBodyCom ha)
    (fun i ρ ρ' hR hfr a ha => by
      obtain ⟨F, hF, hFbit, hFmark, hFsup⟩ := hR a ha
      exact ⟨F, by rw [hfr _ ⟨a, ha, rfl⟩]; exact hF, hFbit, hFmark, hFsup⟩)
    (List.finRange mb) (List.nodup_finRange mb)
    (fun i _ => streamPdBody_spec hcsr h1B hnB hnsB hmbB htail hfit hIdx
      hRaB hRsup hWf hWrow i)
    (fun x _ y _ hxy a hax hay => by
      obtain ⟨b, hb, hbe⟩ := hax
      obtain ⟨b', hb', hbe'⟩ := hay
      exact hxy (pdIdx_inj hb hb' (colName_inj (hbe ▸ hbe')).2).1)
  rw [List.length_finRange] at h
  simpa [streamPdCom, streamPdCost] using
    h.post (fun _ _ _ hq => ⟨hq.1, fun i a ha => hq.2 i (List.mem_finRange i) a ha⟩)

#print axioms streamPdCom_spec

def StreamOldHeld (n cap mb j : ℕ) (Vo : ℕ → Set (Fin n))
    (Xmem : ℕ → ℕ) (tail : ℕ) (σ : Env) : Prop :=
  ∀ c, c < sigL cap mb j + 1 → ∃ F,
    σ.arrs (colName (j + 1) (oldIdx cap mb j c)) = arrOf n F ∧
    (∀ k, k < n → F k ≤ 1) ∧ markSet n F = Vo c ∧
    BlockSupported n 0 tail Xmem F

theorem StreamOldHeld.run_pu
    {B K n cap mb j tail : ℕ} {Vo : ℕ → Set (Fin n)}
    {Xmem : ℕ → ℕ} {σ σ' : Env} {cmd : Com}
    (h : StreamOldHeld n cap mb j Vo Xmem tail σ) (hr : Run B cmd σ σ' K)
    (hw : ∀ a ∈ cmd.warrs, ∃ c b,
      a = colName (j + 1) (puIdx cap mb j c b)) :
    StreamOldHeld n cap mb j Vo Xmem tail σ' := by
  intro c hc
  obtain ⟨F, hF, hFbit, hFmark, hFsup⟩ := h c hc
  refine ⟨F, ?_, hFbit, hFmark, hFsup⟩
  rw [hr.frame_arr _ (by
    intro ha
    obtain ⟨s, b, he⟩ := hw _ ha
    exact oldIdx_ne_puIdx c s b (colName_inj he).2), hF]

def streamPuBodyCom (cap mb j c : ℕ) : Com :=
  .seq (streamBlockAndCom "xmem"
      (colName (j + 1) (oldIdx cap mb j c))
      (colName (j + 1) (oldIdx cap mb j c))
      (colName (j + 1) (puIdx cap mb j c 0)))
    (streamChainCom "xmem" (resName j)
      (fun b => colName (j + 1) (puIdx cap mb j c b)) cap)

def streamPuBodyCost (tail rowMass cap : ℕ) : ℕ :=
  streamBlockAndCost tail + (streamExpandCost tail rowMass * cap + 1)

theorem mem_warrs_streamPuBodyCom {cap mb j c : ℕ} {a : String}
    (h : a ∈ (streamPuBodyCom cap mb j c).warrs) :
    ∃ b, b ≤ cap ∧ a = colName (j + 1) (puIdx cap mb j c b) := by
  simp only [streamPuBodyCom, Com.warrs, List.mem_append] at h
  rcases h with h | h
  · exact ⟨0, by omega, mem_warrs_streamBlockMapCom h⟩
  · obtain ⟨b, hb, hbe⟩ := mem_warrs_streamChainCom h
    exact ⟨b + 1, by omega, hbe⟩

theorem streamPuBody_spec
    {B n ns nt na tail cap mb j c : ℕ} {G : SimpleGraph (Fin n)}
    {O T : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {Xmem Xa Ra Wf : ℕ → ℕ} {Vo : ℕ → Set (Fin n)}
    (hcsr : CsrGraph G ns O T)
    (h1B : 1 < B) (hnB : n < B) (hnsB : ns < B)
    (htail : tail ≤ n) (hfit : tail ≤ na)
    (hIdx : ∀ q, q < tail → Xmem q < n)
    (hRaB : ∀ k, k < n → Ra k < B) (hRsup : BlockSupported n 0 tail Xmem Ra)
    (hc : c < sigL cap mb j + 1) :
    Spec B
      (fun σ => StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ ∧
        StreamOldHeld n cap mb j Vo Xmem tail σ)
      (streamPuBodyCom cap mb j c)
      (fun _ σ' =>
        (StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ' ∧
          StreamOldHeld n cap mb j Vo Xmem tail σ') ∧
        ∀ b, b ≤ cap → ∃ F,
          σ'.arrs (colName (j + 1) (puIdx cap mb j c b)) = arrOf n F ∧
          (∀ k, k < n → F k ≤ 1) ∧
          markSet n F = ballOf (masked G Ra) b (Vo c) ∧
          BlockSupported n 0 tail Xmem F)
      (streamPuBodyCost tail (expandRowSum O Xmem 0 tail) cap) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hpre, hold⟩ := hσ
  obtain ⟨S₀, hS₀, hS₀bit, hS₀mark, hS₀sup⟩ := hold c hc
  obtain ⟨g₀, hg₀, hg₀sup⟩ := hpre.next_slots (puIdx cap mb j c 0) (puIdx_lt_sigL c 0)
  have hS₀B : ∀ k, k < n → S₀ k < B :=
    fun k hk => lt_of_le_of_lt (hS₀bit k hk) h1B
  have hprodSup : BlockSupported n 0 tail Xmem (fun v => S₀ v * S₀ v) :=
    blockSupported_mul_left hS₀sup
  have hprodB : ∀ q, q < tail → S₀ (Xmem q) * S₀ (Xmem q) < B := by
    intro q hq
    have hqN := hIdx q hq
    calc
      S₀ (Xmem q) * S₀ (Xmem q) ≤ 1 * 1 :=
        Nat.mul_le_mul (hS₀bit _ hqN) (hS₀bit _ hqN)
      _ = 1 := by omega
      _ < B := h1B
  obtain ⟨σ₁, hr₁, ⟨⟨S, hS, hSval, hSsup⟩, htail₁, -, -, -⟩,
      hfv₁, -, -, -⟩ :=
    ((streamBlockAndCom_supported_spec (idx := "xmem")
      (a := colName (j + 1) (oldIdx cap mb j c))
      (b := colName (j + 1) (oldIdx cap mb j c))
      (dst := colName (j + 1) (puIdx cap mb j c 0))
      h1B hnB htail hfit hIdx hS₀B hS₀B hprodB
      (colName_ne_lit (q := "xmem") (by decide))
      (colName_ne_slot (Ne.symm (oldIdx_ne_puIdx c c 0)))
      (colName_ne_slot (Ne.symm (oldIdx_ne_puIdx c c 0)))).frame).run
      ⟨hpre.tail_var, hpre.row_arr, hg₀, ⟨hS₀, hS₀⟩, hprodSup, hg₀sup⟩
  have hSeq : ∀ k, k < n → S k = S₀ k := by
    intro k hk
    rw [hSval k hk]
    rcases Nat.eq_zero_or_pos (S₀ k) with hz | hp
    · simp [hz]
    · have ho : S₀ k = 1 := by have := hS₀bit k hk; omega
      simp [ho]
  have hSbit : ∀ k, k < n → S k ≤ 1 := by
    intro k hk
    rw [hSeq k hk]
    exact hS₀bit k hk
  have hSmark : markSet n S = Vo c := by
    rw [markSet_congr hSeq, hS₀mark]
  have hn₁eq : σ₁.vars "n" = σ.vars "n" := hfv₁ "n" (by
    simp [streamBlockAndCom, streamBlockMapCom, BlockLeaves.blockMapRangeCom, Com.wvars])
  have hpre₁ : StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ₁ :=
    hpre.run_supported hr₁ (by rw [htail₁, hpre.tail_var]) hn₁eq
      (fun a ha => ⟨puIdx cap mb j c 0, puIdx_lt_sigL c 0,
        mem_warrs_streamBlockMapCom ha⟩)
      (fun s hs hsw => by
        have he := mem_warrs_streamBlockMapCom hsw
        have hse : s = puIdx cap mb j c 0 := (colName_inj he).2
        subst s
        exact ⟨S, hS, hSsup⟩)
  have hold₁ : StreamOldHeld n cap mb j Vo Xmem tail σ₁ :=
    hold.run_pu hr₁ (fun a ha =>
      ⟨c, 0, mem_warrs_streamBlockMapCom ha⟩)
  let nm : ℕ → String := fun b => colName (j + 1) (puIdx cap mb j c b)
  obtain ⟨σ₂, hr₂, hstage, htail₂, hn₂, -, -, -, -, -⟩ :=
    (streamChainCom_stages (idx := "xmem") (msk := resName j)
      hcsr h1B hnB hnsB htail hfit hIdx hRaB hRsup cap nm S
      (fun a b ha hb hab he => hab (puIdx_inj (by omega) (by omega) ha hb
        (colName_inj he).2).2)
      (fun a _ => colName_ne_lit (q := "xmem") (by decide))
      (fun a _ => colName_ne_resName _ _ _)
      (fun a _ => colName_ne_lit (q := "off") (by decide))
      (fun a _ => colName_ne_lit (q := "tgt") (by decide))
      hSbit hSsup).run
      ⟨hpre₁.tail_var, hpre₁.n_var, hpre₁.off_arr, hpre₁.target_arr,
        hpre₁.target_fit, hpre₁.row_arr, hpre₁.retained_arr, hS,
        fun b hb hbc => by
          obtain ⟨A, hA, hAsup⟩ := hpre₁.next_slots (puIdx cap mb j c b)
            (puIdx_lt_sigL c b)
          exact ⟨A, hA, hAsup⟩⟩
  have hpre₂ : StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ₂ :=
    hpre₁.run_supported hr₂ (by rw [htail₂, hpre₁.tail_var])
      (by rw [hn₂, hpre₁.n_var])
      (fun a ha => by
        obtain ⟨b, hb, hbe⟩ := mem_warrs_streamChainCom ha
        exact ⟨puIdx cap mb j c (b + 1), puIdx_lt_sigL c (b + 1), hbe⟩)
      (fun s hs hsw => by
        obtain ⟨b, hb, hbe⟩ := mem_warrs_streamChainCom hsw
        have hse : s = puIdx cap mb j c (b + 1) := (colName_inj hbe).2
        subst s
        obtain ⟨F, hF, -, -, hFsup⟩ := hstage (b + 1) (by omega)
        exact ⟨F, hF, hFsup⟩)
  have hold₂ : StreamOldHeld n cap mb j Vo Xmem tail σ₂ :=
    hold₁.run_pu hr₂ (fun a ha => by
      obtain ⟨b, -, hbe⟩ := mem_warrs_streamChainCom ha
      exact ⟨c, b + 1, hbe⟩)
  have hrun : Run B (streamPuBodyCom cap mb j c) σ σ₂
      (streamBlockAndCost tail +
        (streamExpandCost tail (expandRowSum O Xmem 0 tail) * cap + 1)) := by
    rw [streamPuBodyCom]
    exact hr₁.seq hr₂
  refine ⟨σ₂, _, hrun, ?_, ⟨hpre₂, hold₂⟩, ?_⟩
  · simp [streamPuBodyCost]
  · intro b hb
    obtain ⟨F, hF, hFbit, hFmark, hFsup⟩ := hstage b hb
    exact ⟨F, hF, hFbit, by rw [hFmark, hSmark], hFsup⟩

#print axioms streamPuBody_spec

def streamPuCom (cap mb j : ℕ) : Com :=
  foldRange (fun c => streamPuBodyCom cap mb j c) (sigL cap mb j + 1)

def streamPuCost (tail rowMass cap L : ℕ) : ℕ :=
  streamPuBodyCost tail rowMass cap * (L + 1) + 1

theorem streamPuCom_spec
    {B n ns nt na tail cap mb j : ℕ} {G : SimpleGraph (Fin n)}
    {O T : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {Xmem Xa Ra Wf : ℕ → ℕ} {Vo : ℕ → Set (Fin n)}
    (hcsr : CsrGraph G ns O T)
    (h1B : 1 < B) (hnB : n < B) (hnsB : ns < B)
    (htail : tail ≤ n) (hfit : tail ≤ na)
    (hIdx : ∀ q, q < tail → Xmem q < n)
    (hRaB : ∀ k, k < n → Ra k < B) (hRsup : BlockSupported n 0 tail Xmem Ra) :
    Spec B
      (fun σ => StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ ∧
        StreamOldHeld n cap mb j Vo Xmem tail σ)
      (streamPuCom cap mb j)
      (fun _ σ' =>
        (StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ' ∧
          StreamOldHeld n cap mb j Vo Xmem tail σ') ∧
        ∀ c, c < sigL cap mb j + 1 → ∀ b, b ≤ cap → ∃ F,
          σ'.arrs (colName (j + 1) (puIdx cap mb j c b)) = arrOf n F ∧
          (∀ k, k < n → F k ≤ 1) ∧
          markSet n F = ballOf (masked G Ra) b (Vo c) ∧
          BlockSupported n 0 tail Xmem F)
      (streamPuCost tail (expandRowSum O Xmem 0 tail) cap (sigL cap mb j)) := by
  have h := foldr_family_spec
    (body := fun c => streamPuBodyCom cap mb j c)
    (I := fun σ => StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ ∧
      StreamOldHeld n cap mb j Vo Xmem tail σ)
    (R := fun c ρ => ∀ b, b ≤ cap → ∃ F,
      ρ.arrs (colName (j + 1) (puIdx cap mb j c b)) = arrOf n F ∧
      (∀ k, k < n → F k ≤ 1) ∧
      markSet n F = ballOf (masked G Ra) b (Vo c) ∧
      BlockSupported n 0 tail Xmem F)
    (Wr := fun c a => ∃ b, b ≤ cap ∧
      a = colName (j + 1) (puIdx cap mb j c b))
    (Kb := streamPuBodyCost tail (expandRowSum O Xmem 0 tail) cap)
    (fun c a ha => mem_warrs_streamPuBodyCom ha)
    (fun c ρ ρ' hR hfr b hb => by
      obtain ⟨F, hF, hFbit, hFmark, hFsup⟩ := hR b hb
      exact ⟨F, by rw [hfr _ ⟨b, hb, rfl⟩]; exact hF, hFbit, hFmark, hFsup⟩)
    (List.range (sigL cap mb j + 1)) (List.nodup_range)
    (fun c hc => streamPuBody_spec hcsr h1B hnB hnsB htail hfit hIdx
      hRaB hRsup (List.mem_range.mp hc))
    (fun x hx y hy hxy a hax hay => by
      obtain ⟨b, hb, hbe⟩ := hax
      obtain ⟨b', hb', hbe'⟩ := hay
      exact hxy (puIdx_inj (by have := List.mem_range.mp hx; omega)
        (by have := List.mem_range.mp hy; omega) hb hb'
        (colName_inj (hbe ▸ hbe')).2).1)
  rw [List.length_range] at h
  simpa [streamPuCom, streamPuCost] using
    h.post (fun _ _ _ hq => ⟨hq.1, fun c hc b hb =>
      hq.2 c (List.mem_range.mpr (by omega)) b hb⟩)

#print axioms streamPuCom_spec

theorem mem_warrs_streamPdCom {cap mb j : ℕ} {a : String}
    (h : a ∈ (streamPdCom cap mb j).warrs) :
    ∃ (i : Fin mb) (b : ℕ), b ≤ cap ∧
      a = colName (j + 1) (pdIdx cap mb j i b) := by
  obtain ⟨i, -, hi⟩ := RamDriverFrames.mem_warrs_foldr
    (fun i : Fin mb => streamPdBodyCom cap mb j i) (List.finRange mb) h
  obtain ⟨b, hb, hbe⟩ := mem_warrs_streamPdBodyCom hi
  exact ⟨i, b, hb, hbe⟩

theorem mem_warrs_streamPuCom {cap mb j : ℕ} {a : String}
    (h : a ∈ (streamPuCom cap mb j).warrs) :
    ∃ c b, c < sigL cap mb j + 1 ∧ b ≤ cap ∧
      a = colName (j + 1) (puIdx cap mb j c b) := by
  obtain ⟨c, hc, hcm⟩ := RamDriverFrames.mem_warrs_foldRange
    (fun c => streamPuBodyCom cap mb j c) (sigL cap mb j + 1) h
  obtain ⟨b, hb, hbe⟩ := mem_warrs_streamPuBodyCom hcm
  exact ⟨c, b, hc, hb, hbe⟩

def streamColourCom (cap mb j : ℕ) : Com :=
  .seq (streamOldCom cap mb j)
    (.seq (streamPdCom cap mb j) (streamPuCom cap mb j))

def streamColourCost (tail rowMass cap mb L : ℕ) : ℕ :=
  streamOldCost tail L +
    (streamPdCost tail rowMass cap mb + streamPuCost tail rowMass cap L)

/-! The complete sparse colouring phase writes only successor palette
slots and the eight private loop counters listed below.  Keeping these
facts beside the new command avoids appealing to the carrier-scanning
colour phase merely for its frame theorem. -/

theorem mem_warrs_streamOldCom {cap mb j : ℕ} {a : String}
    (h : a ∈ (streamOldCom cap mb j).warrs) :
    ∃ s, s < sigL cap mb (j + 1) ∧ a = colName (j + 1) s := by
  simp only [streamOldCom, Com.warrs, List.mem_append] at h
  rcases h with h | h
  · obtain ⟨c, hc, hm⟩ := RamDriverFrames.mem_warrs_foldRange _ _ h
    exact ⟨oldIdx cap mb j c, oldIdx_lt_sigL c,
      mem_warrs_streamBlockMapCom hm⟩
  · exact ⟨oldIdx cap mb j (sigL cap mb j), oldIdx_lt_sigL _,
      mem_warrs_streamBlockMapCom h⟩

theorem mem_warrs_streamColourCom {cap mb j : ℕ} {a : String}
    (h : a ∈ (streamColourCom cap mb j).warrs) :
    ∃ s, s < sigL cap mb (j + 1) ∧ a = colName (j + 1) s := by
  simp only [streamColourCom, Com.warrs, List.mem_append] at h
  rcases h with h | h | h
  · exact mem_warrs_streamOldCom h
  · obtain ⟨i, b, hb, he⟩ := mem_warrs_streamPdCom h
    exact ⟨pdIdx cap mb j i b, pdIdx_lt_sigL i b, he⟩
  · obtain ⟨c, b, -, hb, he⟩ := mem_warrs_streamPuCom h
    exact ⟨puIdx cap mb j c b, puIdx_lt_sigL c b, he⟩

theorem mem_wvars_streamBlockMapCom {idx dst : String} {x : Expr} {y : String}
    (h : y ∈ (streamBlockMapCom idx dst x).wvars) :
    y ∈ (["p", "pend", "cw"] : List String) := by
  simp only [streamBlockMapCom, BlockLeaves.blockMapRangeCom, Com.wvars,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
  tauto

theorem mem_wvars_streamExpandCom {idx msk src dst y : String}
    (h : y ∈ (streamExpandCom idx msk src dst).wvars) :
    y ∈ (["p", "pend", "z", "hit", "w", "j", "jend"] : List String) := by
  simp only [streamExpandCom, expandBlockLoop, expandStep, expandSlot,
    Csr.loadRow, Csr.scan, Com.wvars, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false] at h ⊢
  tauto

theorem mem_wvars_streamChainCom {idx msk y : String} {nm : ℕ → String} {r : ℕ}
    (h : y ∈ (streamChainCom idx msk nm r).wvars) :
    y ∈ (["p", "pend", "z", "hit", "w", "j", "jend"] : List String) := by
  obtain ⟨a, -, ha⟩ := Lax3Proofs.RamDriverDescend.mem_wvars_foldRange _ _ h
  exact mem_wvars_streamExpandCom ha

theorem mem_wvars_streamColourCom {cap mb j : ℕ} {y : String}
    (h : y ∈ (streamColourCom cap mb j).wvars) :
    y ∈ (["p", "pend", "cw", "z", "hit", "w", "j", "jend"] : List String) := by
  have hmap : ∀ {idx dst : String} {x : Expr} {y : String},
      y ∈ (streamBlockMapCom idx dst x).wvars →
      y ∈ (["p", "pend", "cw", "z", "hit", "w", "j", "jend"] : List String) := by
    intro idx dst x y hy
    have := mem_wvars_streamBlockMapCom hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    tauto
  have hchain : ∀ {idx msk : String} {nm : ℕ → String} {r : ℕ} {y : String},
      y ∈ (streamChainCom idx msk nm r).wvars →
      y ∈ (["p", "pend", "cw", "z", "hit", "w", "j", "jend"] : List String) := by
    intro idx msk nm r y hy
    have := mem_wvars_streamChainCom hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at this ⊢
    tauto
  simp only [streamColourCom, Com.wvars, List.mem_append] at h
  rcases h with hold | hpd | hpu
  · simp only [streamOldCom, Com.wvars, List.mem_append] at hold
    rcases hold with hold | hold
    · obtain ⟨c, -, hc⟩ := Lax3Proofs.RamDriverDescend.mem_wvars_foldRange _ _ hold
      exact hmap hc
    · exact hmap hold
  · obtain ⟨i, -, hi⟩ := Lax3Proofs.RamDriverDescend.mem_wvars_foldr
      (fun i : Fin mb => streamPdBodyCom cap mb j i) (List.finRange mb) hpd
    simp only [streamPdBodyCom, Com.wvars, List.mem_append,
      List.not_mem_nil, false_or] at hi
    rcases hi with hi | hi
    · exact hmap hi
    · exact hchain hi
  · obtain ⟨c, -, hc⟩ := Lax3Proofs.RamDriverDescend.mem_wvars_foldRange _ _ hpu
    simp only [streamPuBodyCom, Com.wvars, List.mem_append] at hc
    rcases hc with hc | hc
    · exact hmap hc
    · exact hchain hc

theorem noWrite_streamExpandCom (idx msk src dst : String) :
    (streamExpandCom idx msk src dst).NoWrite := by
  simp [streamExpandCom, expandBlockLoop, expandStep, expandSlot,
    Csr.loadRow, Csr.scan, Com.NoWrite]

theorem noWrite_streamChainCom (idx msk : String) (nm : ℕ → String) (r : ℕ) :
    (streamChainCom idx msk nm r).NoWrite :=
  Lax3Proofs.RamDriverBot.noWrite_foldRange _
    (fun _ => noWrite_streamExpandCom _ _ _ _) _

theorem noWrite_streamColourCom (cap mb j : ℕ) :
    (streamColourCom cap mb j).NoWrite := by
  have hmap : ∀ (idx dst : String) (x : Expr),
      (streamBlockMapCom idx dst x).NoWrite := fun idx dst x => by
    simp [streamBlockMapCom, BlockLeaves.blockMapRangeCom, Com.NoWrite]
  have hold : (streamOldCom cap mb j).NoWrite := by
    exact ⟨Lax3Proofs.RamDriverBot.noWrite_foldRange _
        (fun _ => hmap _ _ _) _, hmap _ _ _⟩
  have hpdBody : ∀ i : Fin mb, (streamPdBodyCom cap mb j i).NoWrite := by
    intro i
    exact ⟨hmap _ _ _, ⟨trivial, noWrite_streamChainCom _ _ _ _⟩⟩
  have hpd : (streamPdCom cap mb j).NoWrite :=
    Lax3Proofs.RamDriverDescend.noWrite_foldr hpdBody _
  have hpuBody : ∀ c, (streamPuBodyCom cap mb j c).NoWrite := by
    intro c
    exact ⟨hmap _ _ _, noWrite_streamChainCom _ _ _ _⟩
  have hpu : (streamPuCom cap mb j).NoWrite :=
    Lax3Proofs.RamDriverBot.noWrite_foldRange _ hpuBody _
  exact ⟨hold, hpd, hpu⟩

theorem streamColourCom_spec
    {B n ns nt na tail cap mb j : ℕ} {G : SimpleGraph (Fin n)}
    {O T : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {Xmem Xa Ra Wf : ℕ → ℕ} {w : Fin mb → Fin n}
    (hcsr : CsrGraph G ns O T)
    (h1B : 1 < B) (hnB : n < B) (hnsB : ns < B) (hmbB : mb < B)
    (htail : tail ≤ n) (hfit : tail ≤ na)
    (hIdx : ∀ q, q < tail → Xmem q < n)
    (hRaB : ∀ k, k < n → Ra k < B) (hRsup : BlockSupported n 0 tail Xmem Ra)
    (hCbit : ∀ c, c < sigL cap mb j → ∀ k, k < n → C c k ≤ 1)
    (hXbit : ∀ k, k < n → Xa k ≤ 1) (hXsup : BlockSupported n 0 tail Xmem Xa)
    (hWf : ∀ i : Fin mb, Wf (i : ℕ) = (w i : ℕ))
    (hWrow : ∀ i : Fin mb, ∃ q, q < tail ∧ Xmem q = (w i : ℕ)) :
    Spec B
      (StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf)
      (streamColourCom cap mb j)
      (fun _ σ' =>
        StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ' ∧
        (∀ s, s < sigL cap mb (j + 1) → ∀ v, v < n →
          cellsOf σ' (colName (j + 1) s) v ≤ 1) ∧
        colRead n (fun s => cellsOf σ' (colName (j + 1) s))
            (sigL cap mb (j + 1)) =
          Evaluator.isoColoring (cap := cap) (masked G Ra)
            (Evaluator.relColoring (colRead n C (sigL cap mb j)) (markSet n Xa)) w)
      (streamColourCost tail (expandRowSum O Xmem 0 tail) cap mb (sigL cap mb j)) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨σ₁, hr₁, hpre₁, hold₁⟩ :=
    (streamOldCom_spec h1B hnB htail hfit hIdx hCbit hXbit hXsup).run hσ
  let Vo := relSlot n cap mb j C (markSet n Xa)
  have hOld₁ : StreamOldHeld n cap mb j Vo Xmem tail σ₁ := by
    intro c hc
    obtain ⟨F, hF, hFbit, hFmark, hFsup⟩ := hold₁ ⟨c, hc⟩
    exact ⟨F, hF, hFbit, by
      simpa only [Vo] using hFmark.trans (relSlot_val ⟨c, hc⟩).symm, hFsup⟩
  obtain ⟨σ₂, hr₂, ⟨hpre₂, hpd₂⟩, -, hfa₂, -, -⟩ :=
    ((streamPdCom_spec hcsr h1B hnB hnsB hmbB htail hfit hIdx
      hRaB hRsup hWf hWrow).frame).run hpre₁
  have hOld₂ : StreamOldHeld n cap mb j Vo Xmem tail σ₂ := by
    intro c hc
    obtain ⟨F, hF, hFbit, hFmark, hFsup⟩ := hOld₁ c hc
    refine ⟨F, ?_, hFbit, hFmark, hFsup⟩
    rw [hfa₂ _ (by
      intro hw
      obtain ⟨i, b, hb, he⟩ := mem_warrs_streamPdCom hw
      exact oldIdx_ne_pdIdx c i b (colName_inj he).2), hF]
  obtain ⟨σ₃, hr₃, ⟨⟨hpre₃, hOld₃⟩, hpu₃⟩, -, hfa₃, -, -⟩ :=
    ((streamPuCom_spec hcsr h1B hnB hnsB htail hfit hIdx hRaB hRsup).frame).run
      ⟨hpre₂, hOld₂⟩
  have hpd₃ : ∀ (i : Fin mb) a, a ≤ cap → ∃ F,
      σ₃.arrs (colName (j + 1) (pdIdx cap mb j i a)) = arrOf n F ∧
      (∀ k, k < n → F k ≤ 1) ∧
      markSet n F = ballOf (masked G Ra) a {w i} ∧
      BlockSupported n 0 tail Xmem F := by
    intro i a ha
    obtain ⟨F, hF, hFbit, hFmark, hFsup⟩ := hpd₂ i a ha
    refine ⟨F, ?_, hFbit, hFmark, hFsup⟩
    rw [hfa₃ _ (by
      intro hw
      obtain ⟨c, b, -, -, he⟩ := mem_warrs_streamPuCom hw
      exact pdIdx_ne_puIdx i a c b (colName_inj he).2), hF]
  have key : ∀ s : Fin (sigL cap mb (j + 1)), ∃ F,
      σ₃.arrs (colName (j + 1) (s : ℕ)) = arrOf n F ∧
      (∀ v, v < n → F v ≤ 1) ∧
      markSet n F = Evaluator.isoColoring (cap := cap) (masked G Ra)
        (Evaluator.relColoring (colRead n C (sigL cap mb j)) (markSet n Xa)) w s := by
    intro s
    rcases slot_cases (L' := sigL cap mb j + 1) (m' := mb) (cp := cap) s with
      ⟨d, rfl⟩ | ⟨i, a, rfl⟩ | ⟨d, b, rfl⟩
    · obtain ⟨F, hF, hFbit, hFmark, -⟩ := hOld₃ (d : ℕ) d.isLt
      refine ⟨F, ?_, hFbit, ?_⟩
      · rw [show ((Evaluator.slotOld d : Fin (sigL cap mb (j + 1))) : ℕ) =
          oldIdx cap mb j (d : ℕ) from val_slotOld d]
        exact hF
      · have hv : Vo (d : ℕ) =
            Evaluator.relColoring (colRead n C (sigL cap mb j)) (markSet n Xa) d := by
            simpa only [Vo] using relSlot_val (C := C) (X := markSet n Xa) d
        rw [hFmark, hv, Evaluator.isoColoring_slotOld]
    · obtain ⟨F, hF, hFbit, hFmark, -⟩ :=
        hpd₃ i (a : ℕ) (Nat.lt_succ_iff.mp a.isLt)
      refine ⟨F, ?_, hFbit, ?_⟩
      · rw [show ((Evaluator.slotPd i a : Fin (sigL cap mb (j + 1))) : ℕ) =
          pdIdx cap mb j i (a : ℕ) from val_slotPd i a]
        exact hF
      · rw [hFmark, Evaluator.isoColoring_slotPd, ballOf_singleton]
    · obtain ⟨F, hF, hFbit, hFmark, -⟩ :=
        hpu₃ (d : ℕ) d.isLt (b : ℕ) (Nat.lt_succ_iff.mp b.isLt)
      refine ⟨F, ?_, hFbit, ?_⟩
      · rw [show ((Evaluator.slotPu d b : Fin (sigL cap mb (j + 1))) : ℕ) =
          puIdx cap mb j (d : ℕ) (b : ℕ) from val_slotPu d b]
        exact hF
      · have hv : Vo (d : ℕ) =
            Evaluator.relColoring (colRead n C (sigL cap mb j)) (markSet n Xa) d := by
            simpa only [Vo] using relSlot_val (C := C) (X := markSet n Xa) d
        rw [hFmark, hv, Evaluator.isoColoring_slotPu]
        rfl
  have hrun : Run B (streamColourCom cap mb j) σ σ₃
      (streamOldCost tail (sigL cap mb j) +
        (streamPdCost tail (expandRowSum O Xmem 0 tail) cap mb +
          streamPuCost tail (expandRowSum O Xmem 0 tail) cap (sigL cap mb j))) := by
    rw [streamColourCom]
    exact hr₁.seq (hr₂.seq hr₃)
  refine ⟨σ₃, _, hrun, ?_, hpre₃, ?_, ?_⟩
  · simp [streamColourCost]
  · intro s hs v hv
    obtain ⟨F, hF, hFbit, -⟩ := key ⟨s, hs⟩
    rw [cellsOf_eq hF hv]
    exact hFbit v hv
  · funext s
    obtain ⟨F, hF, -, hFmark⟩ := key s
    rw [← hFmark]
    exact markSet_congr (fun k hk => cellsOf_eq hF hk)

#print axioms streamColourCom_spec

/-! ## Enumeration-to-colouring adapter -/

/-- Enumerate the resident batch and immediately build its successor
palette, without re-materialising the cover or scanning the carrier. -/
def streamEnumColourCom (cap mb j : ℕ) : Com :=
  .seq (enumStreamCom "xmem" (batName j) (cluName j) mb)
    (streamColourCom cap mb j)

def streamEnumColourCost (tail rowMass cap mb L : ℕ) : ℕ :=
  enumStreamCost tail mb + streamColourCost tail rowMass cap mb L

/-- **A played streamed row reaches the ordinary mathematical colour
step.**  The padded enumeration is obtained from the row, every sparse
colour write remains supported on that row, and the retained-mask graph
equation converts the exact sparse result to `stepColoringP`.  The recursion
record and cluster data are framed for the following kill/recursive phase. -/
theorem streamEnumColourStep
    {B n ns nt na q cap mb j c tail bits d mm : ℕ}
    {G : SimpleGraph (Fin n)}
    {A₀ O T centre Xmem asg M Xa Mm Ra Wa Gm Alv Gam Mem : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    (hcsr : CsrGraph G ns O T) (hnt : ns ≤ nt)
    (hB : WordBoundK B n d ns cap mb)
    (hCbit : ∀ s, s < sigL cap mb j → ∀ v, v < n → C s v ≤ 1) :
    Spec B
      (fun σ =>
        StreamPlayOut B ns nt na q cap mb j c tail bits G A₀ π centre O T
            Xmem asg M Xa Mm Ra Wa Gm Alv Gam Mem mm σ ∧
        (∀ s, s < sigL cap mb j →
          σ.arrs (colName j s) = arrOf n (C s)) ∧
        ∀ s, s < sigL cap mb (j + 1) →
          σ.arrs (colName (j + 1) s) = arrOf n (fun _ => 0))
      (streamEnumColourCom cap mb j)
      (fun σ σ' => ∃ (w : Fin mb → Fin n) (C' : ℕ → ℕ → ℕ),
        StreamSortedOut B ns nt na q cap c tail bits G A₀ π centre O T
            Xmem asg M σ' ∧
        markSet n Xa =
          Lax3Proofs.Refine.MassMath.clusterAt G A₀ π centre cap c ∧
        ClusterData n mb j B G A₀ (markSet n Xa) (markSet n Wa) w
            Alv Gam σ' ∧
        ClusterWa mb w σ' ∧
        PlayRec B cap G (j + 1) Alv Gam σ' ∧
        PlayRec B cap G j A₀ Gm σ' ∧
        StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra
          (fun k => if h : k < mb then (w ⟨k, h⟩ : ℕ) else 0) σ' ∧
        σ'.arrs (alvName j) = arrOf n A₀ ∧
        (∀ v, v < n → A₀ v < B) ∧
        σ'.out = σ.out ∧
        (∀ s, s < sigL cap mb (j + 1) →
          σ'.arrs (colName (j + 1) s) = arrOf n (C' s)) ∧
        (∀ s, s < sigL cap mb (j + 1) → ∀ v, v < n → C' s v ≤ 1) ∧
        colRead n C' (sigL cap mb (j + 1)) =
          stepColoringP cap (masked G A₀) (colRead n C (sigL cap mb j))
            (markSet n Xa) w ∧
        StreamReuseSupports n tail Xmem Xa Ra Wa Alv Gam ∧
        σ'.arrs (batName j) = arrOf n Wa)
      (streamEnumColourCost tail (expandRowSum O Xmem 0 tail) cap mb
        (sigL cap mb j)) := by
  classical
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hplayed, hold, hnext⟩ := hσ
  obtain ⟨σ₁, hr₁, hq₁, hframe₁⟩ :=
    ((streamChildEnumStep (G := G) hB).frame).run (σ := σ)
      ⟨hplayed.child, hplayed.play, hplayed.batch_nonempty,
        hplayed.batch_card, hplayed.wa_alloc⟩
  obtain ⟨hsorted₁, hplay₁, hout₁, w, hdata₁, hwa₁⟩ := hq₁
  obtain ⟨hfv₁, hfa₁, -, -⟩ := hframe₁
  have hav₁ : ∀ a : String, a ≠ "wa" → σ₁.arrs a = σ.arrs a := by
    intro a ha
    exact hfa₁ a (not_mem_warrs_enumStreamCom ha)
  let Wf : ℕ → ℕ :=
    fun k => if h : k < mb then (w ⟨k, h⟩ : ℕ) else 0
  have hpre₁ : StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ₁ := by
    refine {
      tail_var := hsorted₁.tail_var
      n_var := hsorted₁.n_var
      off_arr := hsorted₁.off_arr
      target_arr := hsorted₁.target_arr
      target_fit := hnt
      row_arr := hsorted₁.row_arr
      cluster_arr := (hav₁ _ (by simp [cluName, String.ext_iff])).trans
        hplayed.child.masks.cluster_arr
      retained_arr := (hav₁ _ (by simp [resName, String.ext_iff])).trans
        hplayed.child.masks.retained_arr
      old_colours := fun s hs =>
        (hav₁ _ (colName_ne_lit (by decide))).trans (hold s hs)
      batch_arr := hwa₁
      next_slots := fun s hs => ⟨fun _ => 0,
        (hav₁ _ (colName_ne_lit (by decide))).trans (hnext s hs),
        blockSupported_zero n 0 tail Xmem⟩ }
  have hWf : ∀ i : Fin mb, Wf (i : ℕ) = (w i : ℕ) := by
    intro i
    simp [Wf]
  have hWrow : ∀ i : Fin mb, ∃ p, p < tail ∧ Xmem p = (w i : ℕ) := by
    intro i
    apply (hsorted₁.row.block (w i : ℕ)).mpr
    have hi := hdata₁.mem_cluster i
    rw [hplayed.child.cluster_set] at hi
    exact hi
  obtain ⟨σ₂, hr₂, ⟨hpre₂, hbit₂, heq₂⟩,
      hfv₂, hfa₂, -, hout₂⟩ :=
    ((streamColourCom_spec hcsr hB.one_lt hB.n_lt hB.ns_lt hB.mb_lt
      hsorted₁.row.tail_le (hsorted₁.row.tail_le.trans hsorted₁.row_fit)
      hsorted₁.row.mem_lt hplayed.child.retained_bound
      hplayed.child.retained_supported hCbit hplayed.child.cluster_bit
      hplayed.child.cluster_supported hWf hWrow).frame).run hpre₁
  have hav₂ : ∀ a : String,
      (∀ s, s < sigL cap mb (j + 1) → a ≠ colName (j + 1) s) →
      σ₂.arrs a = σ₁.arrs a := by
    intro a ha
    exact hfa₂ a (by
      intro hw
      obtain ⟨s, hs, he⟩ := mem_warrs_streamColourCom hw
      exact ha s hs he)
  have hvv₂ : ∀ y : String,
      y ∉ (["p", "pend", "cw", "z", "hit", "w", "j", "jend"] : List String) →
      σ₂.vars y = σ₁.vars y := by
    intro y hy
    exact hfv₂ y (fun hw => hy (mem_wvars_streamColourCom hw))
  have hsorted₂ :
      StreamSortedOut B ns nt na q cap c tail bits G A₀ π centre O T
        Xmem asg M σ₂ := by
    refine ⟨hsorted₁.row,
      (hvv₂ "n" (by decide)).trans hsorted₁.n_var,
      (hvv₂ "qn" (by decide)).trans hsorted₁.q_var,
      (hvv₂ "c" (by decide)).trans hsorted₁.centre_var,
      (hvv₂ "xp" (by decide)).trans hsorted₁.pointer_var,
      (hvv₂ "tail" (by decide)).trans hsorted₁.tail_var,
      (hvv₂ "rsbits" (by decide)).trans hsorted₁.bits_var,
      (hav₂ "ord" (fun s _ => Ne.symm (colName_ne_lit (by decide)))).trans
        hsorted₁.centre_arr,
      (hav₂ "off" (fun s _ => Ne.symm (colName_ne_lit (by decide)))).trans
        hsorted₁.off_arr,
      (hav₂ "tgt" (fun s _ => Ne.symm (colName_ne_lit (by decide)))).trans
        hsorted₁.target_arr,
      (hav₂ "alv" (fun s _ => Ne.symm (colName_ne_lit (by decide)))).trans
        hsorted₁.mask_arr,
      (hav₂ "xmem" (fun s _ => Ne.symm (colName_ne_lit (by decide)))).trans
        hsorted₁.row_arr, hsorted₁.row_fit,
      (hav₂ "asg" (fun s _ => Ne.symm (colName_ne_lit (by decide)))).trans
        hsorted₁.asg_arr, ?_, ?_, ?_, hsorted₁.mask_bound⟩
    · apply Lax3Proofs.Refine.CoverActiveTurn.distClean_of_arrs_eq
        hsorted₁.dist_clean
      exact hav₂ "dist" (fun s _ => Ne.symm (colName_ne_lit (by decide)))
    · obtain ⟨Q, hQ⟩ := hsorted₁.queue_arr
      exact ⟨Q, (hav₂ "q" (fun s _ =>
        Ne.symm (colName_ne_lit (by decide)))).trans hQ⟩
    · obtain ⟨QD, hQD⟩ := hsorted₁.qdist_arr
      exact ⟨QD, (hav₂ "qd" (fun s _ =>
        Ne.symm (colName_ne_lit (by decide)))).trans hQD⟩
  have hdata₂ :
      ClusterData n mb j B G A₀ (markSet n Xa) (markSet n Wa) w
        Alv Gam σ₂ := by
    refine ⟨RamDriverDescend.batchData_congr hdata₁.1
      (hav₂ _ (fun s _ => Ne.symm (colName_ne_cluName _ _ _)))
      (hav₂ _ (fun s _ => Ne.symm (colName_ne_batName _ _ _)))
      (hav₂ _ (fun s _ => Ne.symm (colName_ne_resName _ _ _)))
      (hav₂ _ (fun s _ => Ne.symm (colName_ne_alvName _ _ _)))
      (hav₂ _ (fun s _ => Ne.symm (colName_ne_gamName _ _ _)))
      (hav₂ _ (fun s _ => Ne.symm (colName_ne_memName _ _ _)))
      (hvv₂ _ (by simp [mnumName, String.ext_iff])), hdata₁.2⟩
  have hplay₂ : PlayRec B cap G (j + 1) Alv Gam σ₂ :=
    hplay₁.congr
      (fun a _ => hvv₂ (ctrName a) (by simp [ctrName, String.ext_iff]))
      (fun a _ => hav₂ (resName a)
        (fun s _ => Ne.symm (colName_ne_resName _ _ _)))
      (fun a _ => hav₂ (gamName a)
        (fun s _ => Ne.symm (colName_ne_gamName _ _ _)))
      (fun a _ => hav₂ (parName a) (fun s _ => Ne.symm (by
        simpa [parName] using colName_ne_balName (j + 1) s a)))
  have hparent₁ : PlayRec B cap G j A₀ Gm σ₁ :=
    Lax3Proofs.RamDriver.PlayRec.congr hplayed.parent_play
      (fun a _ => hfv₁ _ (not_mem_wvars_enumStreamCom
        (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff])))
      (fun a _ => hav₁ _ (by simp [resName, String.ext_iff]))
      (fun a _ => hav₁ _ (by simp [gamName, String.ext_iff]))
      (fun a _ => hav₁ _ (by simp [parName, balName, String.ext_iff]))
  have hparent₂ : PlayRec B cap G j A₀ Gm σ₂ :=
    Lax3Proofs.RamDriver.PlayRec.congr hparent₁
      (fun a _ => hvv₂ (ctrName a) (by simp [ctrName, String.ext_iff]))
      (fun a _ => hav₂ (resName a)
        (fun s _ => Ne.symm (colName_ne_resName _ _ _)))
      (fun a _ => hav₂ (gamName a)
        (fun s _ => Ne.symm (colName_ne_gamName _ _ _)))
      (fun a _ => hav₂ (parName a) (fun s _ => Ne.symm (by
        simpa [parName] using colName_ne_balName (j + 1) s a)))
  let C' : ℕ → ℕ → ℕ := fun s => cellsOf σ₂ (colName (j + 1) s)
  refine ⟨σ₂, _, hr₁.seq hr₂, ?_, w, C', hsorted₂,
    hplayed.child.cluster_set, hdata₂,
    hpre₂.batch_arr, hplay₂, hparent₂, hpre₂, ?_, hplayed.child.ambient_bound,
    ?_, ?_, ?_, ?_⟩
  · simp [streamEnumColourCom, streamEnumColourCost]
  · exact (hav₂ _ (fun s _ => Ne.symm (colName_ne_alvName _ _ _))).trans
      ((hav₁ _ (by simp [alvName, String.ext_iff])).trans
        hplayed.child.ambient_arr)
  · exact (hout₂ (noWrite_streamColourCom cap mb j)).trans hout₁
  · intro s hs
    obtain ⟨F, hF, -⟩ := hpre₂.next_slots s hs
    exact arrOf_cellsOf hF
  · exact hbit₂
  · constructor
    · rw [heq₂, stepColoringP, hplayed.child.retained_graph]
    · constructor
      · exact {
          cluster := hplayed.child.cluster_supported
          retained := hplayed.child.retained_supported
          batch := hplayed.child.masks.batch_supported
          child := hplayed.child.masks.child_supported
          game := hplayed.child.masks.game_supported }
      · exact (hav₂ _ (fun s _ => Ne.symm (colName_ne_batName _ _ _))).trans
          ((hav₁ _ (by simp [batName, String.ext_iff])).trans
            hplayed.child.masks.batch_arr)

#print axioms streamEnumColourStep

def streamPaletteClearCom (cap mb j : ℕ) : Com :=
  foldRange (fun s => streamBlockClearCom "xmem" (colName (j + 1) s))
    (sigL cap mb (j + 1))

def streamPaletteClearCost (tail slots : ℕ) : ℕ :=
  streamBlockClearCost tail * slots + 1

theorem streamSlotClear_spec
    {B n ns nt na tail cap mb j s : ℕ}
    {O T : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {Xmem Xa Ra Wf : ℕ → ℕ}
    (h1B : 1 < B) (hnB : n < B) (htail : tail ≤ n) (hfit : tail ≤ na)
    (hIdx : ∀ q, q < tail → Xmem q < n) (hs : s < sigL cap mb (j + 1)) :
    Spec B
      (StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf)
      (streamBlockClearCom "xmem" (colName (j + 1) s))
      (fun _ σ' =>
        StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ' ∧
        σ'.arrs (colName (j + 1) s) = arrOf n (fun _ => 0))
      (streamBlockClearCost tail) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨g₀, hg₀, hg₀sup⟩ := hσ.next_slots s hs
  obtain ⟨σ', hr, ⟨⟨F, hF, hFval, hFsup⟩, htail', -⟩,
      hfv, -, -, -⟩ :=
    ((streamBlockClearCom_supported_spec (idx := "xmem")
      (dst := colName (j + 1) s) h1B hnB htail hfit hIdx
      (colName_ne_lit (q := "xmem") (by decide))).frame).run
      ⟨hσ.tail_var, hσ.row_arr, hg₀, hg₀sup⟩
  have hn' : σ'.vars "n" = σ.vars "n" := hfv "n" (by
    simp [streamBlockClearCom, streamBlockMapCom, BlockLeaves.blockMapRangeCom, Com.wvars])
  have hpre' : StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ' :=
    hσ.run_supported hr (by rw [htail', hσ.tail_var]) hn'
      (fun a ha => ⟨s, hs, mem_warrs_streamBlockMapCom ha⟩)
      (fun s' hs' hsw => by
        have he := mem_warrs_streamBlockMapCom hsw
        have hse : s' = s := (colName_inj he).2
        subst s'
        exact ⟨F, hF, hFsup⟩)
  have hzero : σ'.arrs (colName (j + 1) s) = arrOf n (fun _ => 0) := by
    rw [hF]
    exact arrOf_congr hFval
  exact ⟨σ', streamBlockClearCost tail, hr, le_rfl, hpre', hzero⟩

theorem streamPaletteClearCom_spec
    {B n ns nt na tail cap mb j : ℕ}
    {O T : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {Xmem Xa Ra Wf : ℕ → ℕ}
    (h1B : 1 < B) (hnB : n < B) (htail : tail ≤ n) (hfit : tail ≤ na)
    (hIdx : ∀ q, q < tail → Xmem q < n) :
    Spec B
      (StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf)
      (streamPaletteClearCom cap mb j)
      (fun _ σ' =>
        StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf σ' ∧
        ∀ s, s < sigL cap mb (j + 1) →
          σ'.arrs (colName (j + 1) s) = arrOf n (fun _ => 0))
      (streamPaletteClearCost tail (sigL cap mb (j + 1))) := by
  have h := foldr_family_spec
    (body := fun s => streamBlockClearCom "xmem" (colName (j + 1) s))
    (I := StreamColPre n ns nt na tail cap mb j O T C Xmem Xa Ra Wf)
    (R := fun s ρ => ρ.arrs (colName (j + 1) s) = arrOf n (fun _ => 0))
    (Wr := fun s a => a = colName (j + 1) s)
    (Kb := streamBlockClearCost tail)
    (fun s a ha => mem_warrs_streamBlockMapCom ha)
    (fun s ρ ρ' hR hfr => by
      change ρ'.arrs (colName (j + 1) s) = arrOf n (fun _ => 0)
      rw [hfr _ rfl]
      exact hR)
    (List.range (sigL cap mb (j + 1))) (List.nodup_range)
    (fun s hs => streamSlotClear_spec h1B hnB htail hfit hIdx (List.mem_range.mp hs))
    (fun x _ y _ hxy a hax hay => hxy (colName_inj (hax ▸ hay)).2)
  rw [List.length_range] at h
  simpa [streamPaletteClearCom, streamPaletteClearCost] using
    h.post (fun _ _ _ hq => ⟨hq.1, fun s hs => hq.2 s (List.mem_range.mpr hs)⟩)

#print axioms streamPaletteClearCom_spec

end Lax3Proofs.Refine.CoverActiveStreamColour
