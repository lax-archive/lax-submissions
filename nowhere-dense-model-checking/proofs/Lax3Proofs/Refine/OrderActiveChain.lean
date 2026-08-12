import Lax3Proofs.Refine.OrderActiveRound

/-!
# The compact active augmentation chain

This file composes the resident compact augmentation engine with the live
relink.  Its invariant keeps the mathematical augmentation chain and the
physical array lengths in one place, so each round can be invoked without
reintroducing a carrier-sized pass.
-/

namespace Lax3Proofs.Refine.OrderActiveChain

open Lax13Proofs.Imp Lax13Proofs.Reasoning
open Lax3Proofs.Augmentation (Orientation IsAugChain GreedyFratRound
  AugmentedDepthOneDensity budget)
open Lax3Proofs.RamDriver (Sized exists_arrOf foldRange)
open Lax3Proofs.RamElim (InCsr)
open Lax3Proofs.Refine.ScatterBlock (MemList renEnv renEnv_arrs renEnv_vars)
open Lax3Proofs.Refine.AugCompact (AugEntryC AugArrsC AugMemPost augCompactCost
  augCompactCost_eq augWidthE)
open Lax3Proofs.Refine.OrderActiveWork (engineWorkSwap AugWorkEntryC
  augCompactWorkCom augCompactWork_specLive)
open Lax3Proofs.Refine.OrderActiveRound
open Lax3Proofs.Refine.OrderActiveTail

/-- Every array used by a compact round, at its physical resident length.
The level graph itself stays in `off`/`tgt`; the engine's conceptual graph
is redirected to `gof`/`gtg`. -/
def activeOrderLayout (n W : ℕ) : List (String × ℕ) :=
  [("mem", n), ("ork", n),
   ("ioff", n + 1), ("itg", W), ("doff", n + 1), ("dtg", W),
   ("ooff", n + 1), ("otg", W), ("ofl", n), ("gof", n + 1),
   ("gtg", W), ("ffl", n), ("alv", n), ("deg", n), ("elm", n),
   ("rnk", n), ("idg", n), ("bh", n + 1), ("bv", n + W + 1),
   ("bn", n + W + 1), ("ifl", n), ("noff", n + 1), ("nfl", n),
   ("ntg", W), ("stf", n), ("sta", n), ("std", n), ("ste", n)]

def ActiveOrderSized (n W : ℕ) (σ : Env) : Prop := Sized (activeOrderLayout n W) σ

/-- The resident length invariant plus the two live CSR prefixes is exactly
the entry surface of the compact augmentation wrapper. -/
theorem augWorkEntry_of_sized {n mm W kd : ℕ} {IO IT : ℕ → ℕ} {σ : Env}
    (hn : σ.vars "n" = n) (hmm : σ.vars "mm" = mm) (hkd : σ.vars "kd" = kd)
    (hmn : mm ≤ n) (hkdW : kd ≤ W) (hsz : ActiveOrderSized n W σ)
    (hio : ∀ i, i ≤ mm → (σ.arrs "ioff").getD i 0 = IO i)
    (hit : ∀ z, z < kd → (σ.arrs "itg").getD z 0 = IT z) :
    AugWorkEntryC n mm W W kd IO IT σ := by
  classical
  have get (a : String) (k : ℕ) (h : (a, k) ∈ activeOrderLayout n W) :
      ∃ g, σ.arrs a = arrOf k g := hsz.get h
  obtain ⟨iog, hiog⟩ := get "ioff" (n + 1) (by simp [activeOrderLayout])
  obtain ⟨itg, hitg⟩ := get "itg" W (by simp [activeOrderLayout])
  obtain ⟨dog, hdog⟩ := get "doff" (n + 1) (by simp [activeOrderLayout])
  obtain ⟨dtg, hdtg⟩ := get "dtg" W (by simp [activeOrderLayout])
  obtain ⟨oog, hoog⟩ := get "ooff" (n + 1) (by simp [activeOrderLayout])
  obtain ⟨otg, hotg⟩ := get "otg" W (by simp [activeOrderLayout])
  obtain ⟨ofg, hofg⟩ := get "ofl" n (by simp [activeOrderLayout])
  obtain ⟨gof, hgof⟩ := get "gof" (n + 1) (by simp [activeOrderLayout])
  obtain ⟨gtg, hgtg⟩ := get "gtg" W (by simp [activeOrderLayout])
  obtain ⟨ffg, hffg⟩ := get "ffl" n (by simp [activeOrderLayout])
  obtain ⟨alg, halg⟩ := get "alv" n (by simp [activeOrderLayout])
  obtain ⟨deg, hdeg⟩ := get "deg" n (by simp [activeOrderLayout])
  obtain ⟨elg, helg⟩ := get "elm" n (by simp [activeOrderLayout])
  obtain ⟨rkg, hrkg⟩ := get "rnk" n (by simp [activeOrderLayout])
  obtain ⟨idg, hidg⟩ := get "idg" n (by simp [activeOrderLayout])
  obtain ⟨bhg, hbhg⟩ := get "bh" (n + 1) (by simp [activeOrderLayout])
  obtain ⟨bvg, hbvg⟩ := get "bv" (n + W + 1) (by simp [activeOrderLayout])
  obtain ⟨bng, hbng⟩ := get "bn" (n + W + 1) (by simp [activeOrderLayout])
  obtain ⟨ifg, hifg⟩ := get "ifl" n (by simp [activeOrderLayout])
  obtain ⟨nog, hnog⟩ := get "noff" (n + 1) (by simp [activeOrderLayout])
  obtain ⟨nfg, hnfg⟩ := get "nfl" n (by simp [activeOrderLayout])
  obtain ⟨ntg, hntg⟩ := get "ntg" W (by simp [activeOrderLayout])
  obtain ⟨sfg, hsfg⟩ := get "stf" n (by simp [activeOrderLayout])
  obtain ⟨sag, hsag⟩ := get "sta" n (by simp [activeOrderLayout])
  obtain ⟨sdg, hsdg⟩ := get "std" n (by simp [activeOrderLayout])
  obtain ⟨seg, hseg⟩ := get "ste" n (by simp [activeOrderLayout])
  obtain ⟨okg, hokg⟩ := get "ork" n (by simp [activeOrderLayout])
  have hioP : ∀ i ≤ mm, iog i = IO i := by
    intro i hi
    have h := hio i hi
    rwa [hiog, getD_arrOf iog (by omega)] at h
  have hitP : ∀ z < kd, itg z = IT z := by
    intro z hz
    have h := hit z hz
    rwa [hitg, getD_arrOf itg (lt_of_lt_of_le hz hkdW)] at h
  rw [AugWorkEntryC, AugEntryC]
  refine ⟨?_, ?_, ?_, hmn, hkdW, ?_⟩
  · simpa only [renEnv_vars] using hn
  · simpa only [renEnv_vars] using hmm
  · simpa only [renEnv_vars] using hkd
  refine ⟨⟨iog, ?_, hioP⟩, ⟨itg, ?_, hitP⟩, ⟨dog, ?_⟩, ⟨dtg, ?_⟩,
    ⟨oog, ?_⟩, ⟨otg, ?_⟩, ⟨ofg, ?_⟩, ⟨gof, ?_⟩, ⟨gtg, ?_⟩,
    ⟨ffg, ?_⟩, ⟨alg, ?_⟩, ⟨deg, ?_⟩, ⟨elg, ?_⟩, ⟨rkg, ?_⟩,
    ⟨idg, ?_⟩, ⟨bhg, ?_⟩, ⟨bvg, ?_⟩, ⟨bng, ?_⟩, ⟨ifg, ?_⟩,
    ⟨nog, ?_⟩, ⟨nfg, ?_⟩, ⟨ntg, ?_⟩, ⟨sfg, ?_⟩, ⟨sag, ?_⟩,
    ⟨sdg, ?_⟩, ⟨seg, ?_⟩, ⟨okg, ?_⟩⟩
  · simpa [renEnv_arrs, engineWorkSwap] using hiog
  · simpa [renEnv_arrs, engineWorkSwap] using hitg
  · simpa [renEnv_arrs, engineWorkSwap] using hdog
  · simpa [renEnv_arrs, engineWorkSwap] using hdtg
  · simpa [renEnv_arrs, engineWorkSwap] using hoog
  · simpa [renEnv_arrs, engineWorkSwap] using hotg
  · simpa [renEnv_arrs, engineWorkSwap] using hofg
  · simpa [renEnv_arrs, engineWorkSwap] using hgof
  · simpa [renEnv_arrs, engineWorkSwap] using hgtg
  · simpa [renEnv_arrs, engineWorkSwap] using hffg
  · simpa [renEnv_arrs, engineWorkSwap] using halg
  · simpa [renEnv_arrs, engineWorkSwap] using hdeg
  · simpa [renEnv_arrs, engineWorkSwap] using helg
  · simpa [renEnv_arrs, engineWorkSwap] using hrkg
  · simpa [renEnv_arrs, engineWorkSwap] using hidg
  · simpa [renEnv_arrs, engineWorkSwap] using hbhg
  · simpa [renEnv_arrs, engineWorkSwap] using hbvg
  · simpa [renEnv_arrs, engineWorkSwap] using hbng
  · simpa [renEnv_arrs, engineWorkSwap] using hifg
  · simpa [renEnv_arrs, engineWorkSwap] using hnog
  · simpa [renEnv_arrs, engineWorkSwap] using hnfg
  · simpa [renEnv_arrs, engineWorkSwap] using hntg
  · simpa [renEnv_arrs, engineWorkSwap] using hsfg
  · simpa [renEnv_arrs, engineWorkSwap] using hsag
  · simpa [renEnv_arrs, engineWorkSwap] using hsdg
  · simpa [renEnv_arrs, engineWorkSwap] using hseg
  · simpa [renEnv_arrs, engineWorkSwap] using hokg

/-! ## The chain invariant and its honest resident width -/

/-- Room for the round's temporary augmentation graph, the current
orientation, and the original compact graph.  The extra
`mm · budget ... R` term is load-bearing: an augmented orientation may
contain more arcs than the input graph, so the input slot count alone cannot
serve as the second summand of `augWidthE` after the first round. -/
def activeChainWidthE (mm cs d D₁ R : ℕ) : ℕ :=
  mm * (budget d D₁ R + 1) ^ 2 + mm * budget d D₁ R + cs + 1

/-- One compact augmentation followed by the resident live-prefix relink. -/
def activeRoundCom : Com := .seq augCompactWorkCom roundRelinkCom

/-- A uniform round charge at the live width.  Actual input and output slot
counts are both at most `w`. -/
def activeRoundCost (mm w : ℕ) : ℕ :=
  augCompactCost mm w w + 2 + roundRelinkCost mm w

/-- Between rounds, the arrays contain the final orientation of the
chain-so-far in `ioff`/`itg`, and `kd` is its actual slot count. -/
def ActiveFoldInv (n mm W w d₀ : ℕ) (H : SimpleGraph (Fin mm))
    (Mem : ℕ → ℕ) (i : ℕ) (σ : Env) : Prop :=
  σ.vars "n" = n ∧ σ.vars "mm" = mm ∧ σ.arrs "mem" = arrOf n Mem ∧
  ActiveOrderSized n W σ ∧
  ∃ (D : ℕ → Orientation mm) (m : ℕ) (IO IT : ℕ → ℕ),
    IsAugChain H D i ∧
    (∀ l < i, GreedyFratRound (D l) (D (l + 1))) ∧
    (D 0).InDegLE d₀ ∧ InCsr (D i) m IO IT ∧ m ≤ w ∧
    σ.vars "kd" = m ∧
    (∀ z, z ≤ mm → (σ.arrs "ioff").getD z 0 = IO z) ∧
    (∀ z, z < m → (σ.arrs "itg").getD z 0 = IT z)

/-- One compact resident round grows the augmentation chain and preserves
the full machine invariant. -/
theorem activeFold_step {B n mm cs W w d D₁ d₀ R : ℕ}
    {H : SimpleGraph (Fin mm)} {Mem : ℕ → ℕ} {X : Set (Fin n)}
    (hml : MemList n mm Mem X) (hmn : mm ≤ n) (hwW : w ≤ W)
    (hB : mm + w + 1 < B) (hnB : n < B) (hd₀d : d₀ ≤ d)
    (hdens : ∀ (D : ℕ → Orientation mm) (i : ℕ), i ≤ R →
      IsAugChain H D i →
      (∀ l < i, GreedyFratRound (D l) (D (l + 1))) →
      AugmentedDepthOneDensity D i D₁)
    (hcap : activeChainWidthE mm cs d D₁ R ≤ w) :
    ∀ i σ, i < R → ActiveFoldInv n mm W w d₀ H Mem i σ →
      ∃ σ', Run B activeRoundCom σ σ' (activeRoundCost mm w) ∧
        ActiveFoldInv n mm W w d₀ H Mem (i + 1) σ' ∧
        ActiveZeroTail mm σ σ' := by
  classical
  intro i σ hiR hI
  obtain ⟨hn, hmm, hmem, hsz, D, m, IO, IT, hchain, hgreedy, hD₀, hin, hmw,
    hkd, hio, hit⟩ := hI
  set bi := budget d D₁ i with hbiDef
  have hbi : (D i).InDegLE bi :=
    Lax3Proofs.Augmentation.greedy_chain_inDegLE hchain
      (hdens D i (by omega) hchain hgreedy) hgreedy
      (fun v => (hD₀ v).trans hd₀d) i le_rfl
  have hbiR : bi ≤ budget d D₁ R := by
    exact Lax3Proofs.TgtCoupling.budget_mono d D₁ (le_of_lt hiR)
  have hnextR : budget d D₁ (i + 1) ≤ budget d D₁ R := by
    exact Lax3Proofs.TgtCoupling.budget_mono d D₁ (by omega)
  have hmArc : m ≤ mm * bi :=
    Lax3Proofs.Refine.AugCompact.arcs_le_compact hin hbi
  have hpow : mm * (budget d D₁ (i + 1) + 1) ^ 2 ≤
      mm * (budget d D₁ R + 1) ^ 2 :=
    Nat.mul_le_mul_left mm (Nat.pow_le_pow_left (by omega) 2)
  have hmLast : m ≤ mm * budget d D₁ R :=
    hmArc.trans (Nat.mul_le_mul_left mm hbiR)
  have hwidth : augWidthE mm m (budget d D₁ (i + 1)) ≤ w := by
    have hc := hcap
    simp only [augWidthE, activeChainWidthE] at hc ⊢
    omega
  have hsq : mm * (bi * bi) ≤ mm * (budget d D₁ R + 1) ^ 2 :=
    Nat.mul_le_mul_left mm (by nlinarith)
  have hfrat : Lax3Proofs.RamAugment.fratSlots (D i) ≤ W := by
    have h₁ := Lax3Proofs.RamAugment.fratSlots_le hbi
    have hc := hcap
    simp only [activeChainWidthE] at hc
    exact (h₁.trans (hsq.trans (by omega))).trans hwW
  have hdb : 2 * (bi * bi) + bi ≤ budget d D₁ (i + 1) := by
    simpa only [hbiDef] using Lax3Proofs.TgtCoupling.two_sq_add_le_budget_succ d D₁ i
  have hmB : m < B := lt_of_le_of_lt hmw (by omega)
  have hmmB : mm < B := by omega
  obtain ⟨hIOB, hITB⟩ :=
    Lax3Proofs.Refine.SymCompact.prep_bounds_of_inCsr hin hmB hmmB
  have hent : AugWorkEntryC n mm W W m IO IT σ :=
    augWorkEntry_of_sized hn hmm hkd hmn (hmw.trans hwW) hsz hio hit
  obtain ⟨σa, ra, hpost, -, htailA, hna, -, -⟩ :=
    augCompactWork_specLive hml hin hbi le_rfl hmw hwW hfrat hdb hwidth hB hnB
      hIOB hITB hmem hent
  obtain ⟨Rk, NO, NT, k, m', D', hork, hk, hnoff, hntg, hmn', hm'W,
    hstep, hin', hlow, hgreedy', hdegree, harcs⟩ := hpost
  let Dnew : ℕ → Orientation mm := fun l => if l = i + 1 then D' else D l
  have hchainN : IsAugChain H Dnew (i + 1) := by
    refine ⟨by simp only [Dnew, if_neg (show 0 ≠ i + 1 by omega)]; exact hchain.1,
      fun l hl => ?_⟩
    rcases Nat.lt_or_ge l i with hli | hli
    · simp only [Dnew, if_neg (show l ≠ i + 1 by omega),
        if_neg (show l + 1 ≠ i + 1 by omega)]
      exact hchain.2 l hli
    · have : l = i := by omega
      subst l
      simp only [Dnew, if_neg (show i ≠ i + 1 by omega), if_pos rfl]
      exact hstep
  have hgreedyN : ∀ l < i + 1, GreedyFratRound (Dnew l) (Dnew (l + 1)) := by
    intro l hl
    rcases Nat.lt_or_ge l i with hli | hli
    · simp only [Dnew, if_neg (show l ≠ i + 1 by omega),
        if_neg (show l + 1 ≠ i + 1 by omega)]
      exact hgreedy l hli
    · have : l = i := by omega
      subst l
      simp only [Dnew, if_neg (show i ≠ i + 1 by omega), if_pos rfl]
      exact hgreedy'
  have hD₀N : (Dnew 0).InDegLE d₀ := by
    simpa only [Dnew, if_neg (show 0 ≠ i + 1 by omega)] using hD₀
  have hbN : (Dnew (i + 1)).InDegLE (budget d D₁ (i + 1)) :=
    Lax3Proofs.Augmentation.greedy_chain_inDegLE hchainN
      (hdens Dnew (i + 1) (by omega) hchainN hgreedyN) hgreedyN
      (fun v => (hD₀N v).trans hd₀d) (i + 1) le_rfl
  have hbD' : D'.InDegLE (budget d D₁ (i + 1)) := by
    simpa only [Dnew, if_pos rfl] using hbN
  have hm'w : m' ≤ w := by
    have h₁ : m' ≤ mm * budget d D₁ (i + 1) := harcs _ hbD'
    have h₂ : mm * budget d D₁ (i + 1) ≤ mm * budget d D₁ R :=
      Nat.mul_le_mul_left mm hnextR
    have hc := hcap
    simp only [activeChainWidthE] at hc
    omega
  have hsza : ActiveOrderSized n W σa := hsz.run ra
  obtain ⟨NOg, hNOg⟩ := hsza.get (p := ("noff", n + 1)) (by simp [activeOrderLayout])
  have hNO : ∀ z, z ≤ mm → NOg z = NO z := by
    intro z hz
    have h := hnoff z hz
    rwa [hNOg, getD_arrOf NOg (by omega)] at h
  have hm'B : m' < B := lt_of_le_of_lt hm'w (by omega)
  obtain ⟨hNOB, hNTB⟩ :=
    Lax3Proofs.Refine.SymCompact.prep_bounds_of_inCsr hin' hm'B hmmB
  have hmma : σa.vars "mm" = mm := by
    rw [ra.frame_var "mm" (by decide)]
    exact hmm
  obtain ⟨hioffE, hitgE⟩ :
      (∃ g, σa.arrs "ioff" = arrOf (n + 1) g) ∧
      (∃ g, σa.arrs "itg" = arrOf W g) :=
    ⟨hsza.get (p := ("ioff", n + 1)) (by simp [activeOrderLayout]),
      hsza.get (p := ("itg", W)) (by simp [activeOrderLayout])⟩
  obtain ⟨σb, rb, hioB, hitB, hkdB, hmmBv, -, hframeB⟩ :=
    roundRelink_spec (n := n) (NO := NO) (hmmB := by omega) hm'B hmn
      (hm'w.trans hwW) hmma hmn' hNOg hNO hntg hNOB hNTB hioffE hitgE
  have hszaB : ActiveOrderSized n W σb := hsza.run rb
  have hnb : σb.vars "n" = n := by
    rw [rb.frame_var "n" (by decide)]
    exact hna
  have hmemb : σb.arrs "mem" = arrOf n Mem := by
    rw [hframeB "mem" (by decide) (by decide), ra.frame_arr "mem" (by decide)]
    exact hmem
  obtain ⟨IOg, hIOg, hIOgP⟩ := hioB
  obtain ⟨ITg, hITg, hITgP⟩ := hitB
  have hioB' : ∀ z, z ≤ mm → (σb.arrs "ioff").getD z 0 = NO z := by
    intro z hz
    rw [hIOg, getD_arrOf IOg (by omega), hIOgP z hz]
  have hitB' : ∀ z, z < m' → (σb.arrs "itg").getD z 0 = NT z := by
    intro z hz
    rw [hITg, getD_arrOf ITg (lt_of_lt_of_le hz (hm'w.trans hwW)), hITgP z hz]
  have htailB : ActiveZeroTail mm σa σb := by
    apply ActiveZeroTail.of_frame
    intro a ha
    apply hframeB a
    · intro h
      subst a
      simpa [activeZeroNames] using ha
    · intro h
      subst a
      simpa [activeZeroNames] using ha
  have htailAll : ActiveZeroTail mm σ σb := ActiveZeroTail.trans htailA htailB
  refine ⟨σb, (ra.seq rb).mono ?_, ?_, htailAll⟩
  · simp only [activeRoundCost, augCompactCost_eq, roundRelinkCost]
    omega
  · exact ⟨hnb, hmmBv, hmemb, hszaB, Dnew, m', NO, NT, hchainN, hgreedyN,
      hD₀N, (by simpa only [Dnew, if_pos rfl] using hin'), hm'w, hkdB, hioB', hitB'⟩

/-- The complete compact augmentation loop.  The command is syntactically
constant across rounds; the stage index lives only in `ActiveFoldInv`. -/
def activeRoundsCom (R : ℕ) : Com :=
  foldRange (fun _ => activeRoundCom) R

/-- Iterate the resident compact round through the requested augmentation
depth, retaining the final chain witness and the live CSR in place. -/
theorem activeFold_run {B n mm cs W w d D₁ d₀ R : ℕ}
    {H : SimpleGraph (Fin mm)} {Mem : ℕ → ℕ} {X : Set (Fin n)}
    (hml : MemList n mm Mem X) (hmn : mm ≤ n) (hwW : w ≤ W)
    (hB : mm + w + 1 < B) (hnB : n < B) (hd₀d : d₀ ≤ d)
    (hdens : ∀ (D : ℕ → Orientation mm) (i : ℕ), i ≤ R →
      IsAugChain H D i →
      (∀ l < i, GreedyFratRound (D l) (D (l + 1))) →
      AugmentedDepthOneDensity D i D₁)
    (hcap : activeChainWidthE mm cs d D₁ R ≤ w)
    { σ : Env } (hI : ActiveFoldInv n mm W w d₀ H Mem 0 σ) :
    ∃ σ', Run B (activeRoundsCom R) σ σ'
        (R * activeRoundCost mm w + 1) ∧
      ActiveFoldInv n mm W w d₀ H Mem R σ' ∧
      ActiveZeroTail mm σ σ' := by
  let I : ℕ → Env → Prop := fun i τ =>
    ActiveFoldInv n mm W w d₀ H Mem i τ ∧ ActiveZeroTail mm σ τ
  have hstep : ∀ i τ, i < R → I i τ →
      ∃ τ', Run B activeRoundCom τ τ' (activeRoundCost mm w) ∧ I (i + 1) τ' := by
    intro i τ hi hIτ
    obtain ⟨τ', hr, hnext, htail⟩ :=
      activeFold_step hml hmn hwW hB hnB hd₀d hdens hcap i τ hi hIτ.1
    exact ⟨τ', hr, hnext, ActiveZeroTail.trans hIτ.2 htail⟩
  obtain ⟨σ', hr, hIR, htail⟩ :=
    Lax3Proofs.RamDriverCompose.fold_run_aux hstep R 0 (by omega) σ
      ⟨hI, ActiveZeroTail.refl mm σ⟩
  exact ⟨σ', by simpa only [activeRoundsCom, Nat.zero_add] using hr,
    by simpa only [Nat.zero_add] using hIR, htail⟩

/-! ## Axioms -/

#print axioms augWorkEntry_of_sized
#print axioms activeFold_step
#print axioms activeFold_run

end Lax3Proofs.Refine.OrderActiveChain
