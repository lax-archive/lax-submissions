import Lax3Proofs.Refine.CoverActiveStreamSort
import Lax3Proofs.Refine.ActiveEnum

/-!
# Enumerating one streamed active-cover row

The materialised active driver loads a row through two offsets.  A streamed
row already occupies the prefix `[0, tail)`.  This module reuses the verified
collector and padding loops on that prefix, so the immediate cluster consumer
gets exactly the same padded `W ∩ X` enumeration without an offset-table read
or a carrier scan.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamEnum

open Lax3.ColoredGraphs
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster
open Lax3Proofs.RamDriverDescend
open Lax3Proofs.RamDriverMember
open Lax3Proofs.Refine.ActiveEnum
open Lax3Proofs.Refine.CoverActiveStreamSort
open Lax3Proofs.Refine.MassMath (clusterAt)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ## Prefix collector -/

/-- Enumerate the marked vertices in `idx[0..tail)` and pad the result to
`mb`.  Unlike `enumBlockCom`, this command does not read an offset table. -/
def enumStreamCom (idx bat clu : String) (mb : ℕ) : Com :=
  .seq (.assign "bc" (.lit 0))
    (.seq (.assign "p" (.lit 0))
      (.seq (.assign "pend" (.var "tail"))
        (.seq (.while (.lt (.var "p") (.var "pend"))
            (enumBlockBody idx bat clu))
          (.seq (.assign "k" (.var "bc"))
            (.while (.lt (.var "k") (.lit mb))
              (.seq (.store "wa" (.var "k") (.get "wa" (.lit 0)))
                (.assign "k" (.add (.var "k") (.lit 1)))))))))

/-- Affine charge of prefix collection and formula-sized padding. -/
def enumStreamCost (tail mb : ℕ) : ℕ := 30 * tail + 12 * mb + 40

/-- Enumerating the streamed prefix produces exactly its marked vertices,
padded to `mb`.  The resident array may be larger than the prefix, but only
indices below `tail ≤ n < B` are executed. -/
theorem enumStreamCom_spec {B n na tail mb : ℕ} {Xmem Wa Xa : ℕ → ℕ}
    (idx bat clu : String) (hidx : idx ≠ "wa") (hbat : bat ≠ "wa")
    (hclu : clu ≠ "wa") (hB : 1 < B) (hnB : n < B) (htail : tail ≤ n)
    (hfit : tail ≤ na) (hmbB : mb < B)
    (hmem : ∀ p < tail, Xmem p < n)
    (hinj : ∀ p p', p < tail → p' < tail → Xmem p = Xmem p' → p = p')
    (hcard : (markSet n (fun v => Wa v * Xa v)).ncard ≤ mb)
    (hne : ∃ q, q < tail ∧ Wa (Xmem q) * Xa (Xmem q) ≠ 0)
    (hWB : ∀ v, v < n → Wa v < B) (hX1 : ∀ v, v < n → Xa v ≤ 1) :
    Spec B
      (fun σ => σ.arrs idx = arrOf na Xmem ∧
        σ.arrs bat = arrOf n Wa ∧ σ.arrs clu = arrOf n Xa ∧
        σ.vars "tail" = tail ∧ ∃ g, σ.arrs "wa" = arrOf mb g)
      (enumStreamCom idx bat clu mb)
      (fun _ σ' => ∃ E : ℕ → ℕ, σ'.arrs "wa" = arrOf mb E ∧
        (∀ i, i < mb → E i < n ∧ Wa (E i) * Xa (E i) ≠ 0) ∧
        (∀ q, q < tail → Wa (Xmem q) * Xa (Xmem q) ≠ 0 →
          ∃ i, i < mb ∧ E i = Xmem q))
      (enumStreamCost tail mb) := by
  classical
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hxmem, hbatArr, hcluArr, htailVar, g₀, hwa⟩ := hσ
  have htailB : tail < B := lt_of_le_of_lt htail hnB
  have hcardRow :
      (markSet tail (blockMarker 0 Xmem Wa Xa)).ncard ≤ mb := by
    refine (blockMarker_ncard_le (n := n) (m := tail) (e := tail) (p₀ := 0)
      le_rfl hmem ?_).trans hcard
    intro p p' _ hp _ hp' heq
    exact hinj p p' hp hp' heq
  let σ₀ := σ.setVar "bc" 0
  have r₀ : Run B (.assign "bc" (.lit 0)) σ σ₀ 2 :=
    Run.assign (evalB_lit (by omega))
  let σp := σ₀.setVar "p" 0
  have rp : Run B (.assign "p" (.lit 0)) σ₀ σp 2 :=
    Run.assign (evalB_lit (by omega))
  have etail : (Expr.var "tail").evalB B σp = some tail := by
    have ht : σp.vars "tail" = tail := by simp [σp, σ₀, htailVar]
    simpa only [ht] using (evalB_var (B := B) (x := "tail") (σ := σp)
      (by rw [ht]; exact htailB))
  let σ₁ := σp.setVar "pend" tail
  have r₁ : Run B (.assign "pend" (.var "tail")) σp σ₁ 2 :=
    Run.assign etail
  have hI₁ : BlockCollectInv n na tail 0 mb Xmem Wa Xa idx bat clu σ₁ := by
    refine ⟨by simp [σ₁, σp], by simp [σ₁, σp], by simp [σ₁],
      ?_, ?_, ?_, ?_, g₀, ?_, ?_, ?_⟩
    · simpa [σ₁, σp, σ₀] using hxmem
    · simpa [σ₁, σp, σ₀] using hbatArr
    · simpa [σ₁, σp, σ₀] using hcluArr
    · have hbc : σ₁.vars "bc" = 0 := by simp [σ₁, σp, σ₀]
      have hp : σ₁.vars "p" = 0 := by simp [σ₁, σp]
      rw [hbc, hp, ncard_markedBelow_blockMarker_start]
    · simpa [σ₁, σp, σ₀] using hwa
    · intro i hi
      simp [σ₁, σp, σ₀] at hi
    · intro q _ hq _
      simp [σ₁, σp] at hq
  obtain ⟨σ₂, r₂, hI₂, hp₂⟩ :=
    (enumBlockLoop_spec B n na tail 0 mb Xmem Wa Xa idx bat clu hidx hbat hclu
      hfit htailB hB hnB hmbB (fun q _ hq => hmem q hq) hcardRow hWB hX1).run hI₁
  obtain ⟨-, -, -, -, -, -, hbc₂, E₂, hwa₂, hlt₂, hcov₂⟩ := hI₂
  obtain ⟨q₀, hq₀, hq₀m⟩ := hne
  obtain ⟨i₀, hi₀, -⟩ := hcov₂ q₀ (by omega) (by simpa [hp₂] using hq₀) hq₀m
  have hbcpos : 1 ≤ σ₂.vars "bc" := by omega
  have hbcmb : σ₂.vars "bc" ≤ mb :=
    le_trans hbc₂ (le_trans
      (Set.ncard_le_ncard (markedBelow_subset tail _ _) (Set.toFinite _)) hcardRow)
  let σ₃ := σ₂.setVar "k" (σ₂.vars "bc")
  have r₃ : Run B (.assign "k" (.var "bc")) σ₂ σ₃ 2 :=
    (Run.assign (evalB_var (by omega))).mono (by simp)
  have hk₃ : σ₃.vars "k" = σ₂.vars "bc" := by simp [σ₃]
  have hP₃ : BlockPadInv n mb (σ₂.vars "bc") (E₂ 0) 0 tail Xmem
      (fun v => Wa v * Xa v) σ₃ := by
    refine ⟨by rw [hk₃], by rw [hk₃]; exact hbcmb, E₂,
      by simpa [σ₃] using hwa₂, rfl, ?_, ?_⟩
    · intro i hi
      rw [hk₃] at hi
      exact hlt₂ i hi
    · intro q hq₀ hqt hqm
      obtain ⟨i, hi, hEi⟩ := hcov₂ q hq₀ (by simpa [hp₂] using hqt) hqm
      exact ⟨i, hi, hEi⟩
  obtain ⟨σ₄, r₄, hP₄, hk₄⟩ :=
    (enumBlockPadLoop_spec B n mb (σ₂.vars "bc") (E₂ 0) 0 tail Xmem
      (fun v => Wa v * Xa v) hB hnB hmbB hbcpos).run hP₃
  obtain ⟨-, -, E₄, hwa₄, -, hlt₄, hcov₄⟩ := hP₄
  rw [hk₄] at hlt₄
  refine ⟨σ₄,
    2 + (2 + (2 + ((30 * tail + 4) + (2 + (12 * mb + 4))))),
    r₀.seq (rp.seq (r₁.seq (r₂.seq (r₃.seq r₄)))), ?_, E₄, hwa₄, hlt₄, ?_⟩
  · simp only [enumStreamCost]
    omega
  · intro q hqt hqm
    obtain ⟨i, hi, hEi⟩ := hcov₄ q (by omega) hqt hqm
    exact ⟨i, by omega, hEi⟩

/-! ## Frames -/

theorem not_mem_wvars_enumStreamCom {idx bat clu : String} {mb : ℕ} {y : String}
    (hbc : y ≠ "bc") (hp : y ≠ "p") (he : y ≠ "pend")
    (hz : y ≠ "z") (hk : y ≠ "k") :
    y ∉ (enumStreamCom idx bat clu mb).wvars := by
  simp [enumStreamCom, enumBlockBody, Com.wvars, hbc, hp, he, hz, hk]

theorem not_mem_warrs_enumStreamCom {idx bat clu : String} {mb : ℕ} {a : String}
    (h : a ≠ "wa") : a ∉ (enumStreamCom idx bat clu mb).warrs := by
  simp [enumStreamCom, enumBlockBody, Com.warrs, h]

theorem noWrite_enumStreamCom (idx bat clu : String) (mb : ℕ) :
    (enumStreamCom idx bat clu mb).NoWrite := by
  simp [enumStreamCom, enumBlockBody, Com.NoWrite]

/-! ## Cluster-turn adapter -/

/-- Driver-facing contract for the immediate consumer of a sorted streamed
row.  It retains the progressive cover state and returns the exact padded
batch interface expected by the colour phase. -/
def EnumStreamStepA {n : ℕ} (B ns nt na q cap mb j c tail bits : ℕ)
    (G : SimpleGraph (Fin n)) (A₀ O T : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre Xmem asg M : ℕ → ℕ) (X W : Set (Fin n))
    (Alv' Gam' : ℕ → ℕ) (K : ℕ) : Prop :=
  Spec B (fun σ =>
      StreamSortedOut B ns nt na q cap c tail bits G A₀ π centre O T Xmem asg M σ ∧
      BatchData n j B G A₀ X W Alv' Gam' σ ∧
      PlayRec B cap G (j + 1) Alv' Gam' σ ∧ (W ∩ X).Nonempty ∧
      W.ncard ≤ mb ∧
      (∀ v : Fin n, v ∈ X → v ∈ clusterAt G A₀ π centre cap c) ∧
      ∃ g, σ.arrs "wa" = arrOf mb g)
    (enumStreamCom "xmem" (batName j) (cluName j) mb)
    (fun σ σ' =>
      StreamSortedOut B ns nt na q cap c tail bits G A₀ π centre O T Xmem asg M σ' ∧
      PlayRec B cap G (j + 1) Alv' Gam' σ' ∧ σ'.out = σ.out ∧
      ∃ w : Fin mb → Fin n,
        ClusterData n mb j B G A₀ X W w Alv' Gam' σ' ∧ ClusterWa mb w σ') K

/-- The sorted streamed row discharges the cluster enumerator without an
offset table or a full-cover contract. -/
theorem enumStreamStepA {n B ns nt na q cap mb j c tail bits K d : ℕ}
    {G : SimpleGraph (Fin n)} {A₀ O T : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre Xmem asg M : ℕ → ℕ} {X W : Set (Fin n)} {Alv' Gam' : ℕ → ℕ}
    (hB : WordBoundK B n d ns cap mb) (hK : enumStreamCost tail mb ≤ K) :
    EnumStreamStepA B ns nt na q cap mb j c tail bits G A₀ O T π centre Xmem
      asg M X W Alv' Gam' K := by
  intro σ hσ
  obtain ⟨hsorted, hbatch, hplay, hne, hcard, hXcl, ⟨gwa, hwa⟩⟩ := hσ
  obtain ⟨Xa, hXaarr, hXs, hXa1⟩ := hbatch.1
  obtain ⟨Wa, hWaarr, hWs, hWaB⟩ := hbatch.2.1
  have hbatwa : batName j ≠ "wa" := by simp [batName, String.ext_iff]
  have hcluwa : cluName j ≠ "wa" := by simp [cluName, String.ext_iff]
  have hprod : markSet n (fun v => Wa v * Xa v) = W ∩ X := by
    ext v
    show Wa (v : ℕ) * Xa (v : ℕ) ≠ 0 ↔ _
    rw [← hWs, ← hXs]
    exact ⟨fun h => ⟨fun hc => h (by rw [hc]; ring),
        fun hc => h (by rw [hc]; ring)⟩,
      fun h => Nat.mul_ne_zero h.1 h.2⟩
  have hprodCard : (markSet n (fun v => Wa v * Xa v)).ncard ≤ mb := by
    rw [hprod]
    exact (Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)).trans hcard
  have hrowne : ∃ p, p < tail ∧ Wa (Xmem p) * Xa (Xmem p) ≠ 0 := by
    obtain ⟨v, hvW, hvX⟩ := hne
    have hvprod : Wa (v : ℕ) * Xa (v : ℕ) ≠ 0 := by
      apply Nat.mul_ne_zero
      · change v ∈ markSet n Wa
        rw [hWs]
        exact hvW
      · change v ∈ markSet n Xa
        rw [hXs]
        exact hvX
    obtain ⟨p, hp, hpv⟩ := (hsorted.row.block (v : ℕ)).mpr (hXcl v hvX)
    exact ⟨p, hp, by simpa [hpv] using hvprod⟩
  obtain ⟨σ', hr, ⟨E, hwa', hltE, hcovE⟩, hfv, hfa, -, hout⟩ :=
    ((enumStreamCom_spec "xmem" (batName j) (cluName j) (by decide) hbatwa hcluwa
      hB.one_lt hB.n_lt hsorted.row.tail_le
      (hsorted.row.tail_le.trans hsorted.row_fit) hB.mb_lt hsorted.row.mem_lt
      hsorted.row.block_inj hprodCard hrowne hWaB hXa1).frame).run
      ⟨hsorted.row_arr, hWaarr, hXaarr, hsorted.tail_var, gwa, hwa⟩
  have hav : ∀ a : String, a ≠ "wa" → σ'.arrs a = σ.arrs a :=
    fun a ha => hfa a (not_mem_warrs_enumStreamCom ha)
  have hvv : ∀ y : String, y ≠ "bc" → y ≠ "p" → y ≠ "pend" →
      y ≠ "z" → y ≠ "k" → σ'.vars y = σ.vars y :=
    fun y hbc hp he hz hk =>
      hfv y (not_mem_wvars_enumStreamCom hbc hp he hz hk)
  have hsorted' :
      StreamSortedOut B ns nt na q cap c tail bits G A₀ π centre O T Xmem asg M σ' := by
    refine ⟨hsorted.row,
      (hvv "n" (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        hsorted.n_var,
      (hvv "qn" (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        hsorted.q_var,
      (hvv "c" (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        hsorted.centre_var,
      (hvv "xp" (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        hsorted.pointer_var,
      (hvv "tail" (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        hsorted.tail_var,
      (hvv "rsbits" (by decide) (by decide) (by decide) (by decide) (by decide)).trans
        hsorted.bits_var,
      (hav "ord" (by decide)).trans hsorted.centre_arr,
      (hav "off" (by decide)).trans hsorted.off_arr,
      (hav "tgt" (by decide)).trans hsorted.target_arr,
      (hav "alv" (by decide)).trans hsorted.mask_arr,
      (hav "xmem" (by decide)).trans hsorted.row_arr, hsorted.row_fit,
      (hav "asg" (by decide)).trans hsorted.asg_arr, ?_, ?_, ?_, hsorted.mask_bound⟩
    · apply Lax3Proofs.Refine.CoverActiveTurn.distClean_of_arrs_eq hsorted.dist_clean
      exact hav "dist" (by decide)
    · obtain ⟨Q, hQ⟩ := hsorted.queue_arr
      exact ⟨Q, (hav "q" (by decide)).trans hQ⟩
    · obtain ⟨QD, hQD⟩ := hsorted.qdist_arr
      exact ⟨QD, (hav "qd" (by decide)).trans hQD⟩
  have hbatch' : BatchData n j B G A₀ X W Alv' Gam' σ' :=
    RamDriverDescend.batchData_congr hbatch
      (hav _ (by simp [cluName, String.ext_iff])) (hav _ hbatwa)
      (hav _ (by simp [resName, String.ext_iff]))
      (hav _ (by simp [alvName, String.ext_iff]))
      (hav _ (by simp [gamName, String.ext_iff]))
      (hav _ (by simp [memName, String.ext_iff]))
      (hvv _ (by simp [mnumName, String.ext_iff])
        (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff])
        (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff]))
  have hplay' : PlayRec B cap G (j + 1) Alv' Gam' σ' :=
    hplay.congr
      (fun a _ => hvv (ctrName a) (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff]))
      (fun a _ => hav (resName a) (by simp [resName, String.ext_iff]))
      (fun a _ => hav (gamName a) (by simp [gamName, String.ext_iff]))
      (fun a _ => hav (parName a) (by simp [parName, balName, String.ext_iff]))
  refine ⟨σ', hr.mono hK, hsorted', hplay',
    hout (noWrite_enumStreamCom "xmem" (batName j) (cluName j) mb),
    fun i => ⟨E (i : ℕ), (hltE (i : ℕ) i.isLt).1⟩, ⟨?_, ?_⟩, ?_⟩
  · exact hbatch'
  · apply Set.eq_of_subset_of_subset
    · rintro v ⟨i, rfl⟩
      rw [← hprod]
      exact (hltE (i : ℕ) i.isLt).2
    · intro v hv
      have hvX : v ∈ X := hv.2
      obtain ⟨p, hp, hpv⟩ := (hsorted.row.block (v : ℕ)).mpr (hXcl v hvX)
      have hvprod : Wa (v : ℕ) * Xa (v : ℕ) ≠ 0 := by
        apply Nat.mul_ne_zero
        · change v ∈ markSet n Wa
          rw [hWs]
          exact hv.1
        · change v ∈ markSet n Xa
          rw [hXs]
          exact hv.2
      obtain ⟨i, hi, hEi⟩ := hcovE p hp (by simpa [hpv] using hvprod)
      refine ⟨⟨i, hi⟩, Fin.ext ?_⟩
      change E i = (v : ℕ)
      exact hEi.trans hpv
  · rw [ClusterWa, hwa']
    exact arrOf_congr (fun i hi => by rw [dif_pos hi])

/-! ## Axiom audit -/

#print axioms enumStreamCom_spec
#print axioms enumStreamStepA

end Lax3Proofs.Refine.CoverActiveStreamEnum
