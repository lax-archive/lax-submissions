import Lax3Proofs.RamDriver
import Lax3Proofs.RamDriverCluster
import Lax3Proofs.Refine.BfsBlockParMask

/-!
Driver-facing adapters for the per-depth parent-tree cache.

The search proof uses the fixed arrays `"alv"`, `"dist"`, and `"par"`.
`RamDriver.cacheSwap` transports it, without a copy, to `resName j`,
`pdsName j`, and `parName j`.  The second half of this file verifies the
fixed-count parent walk that consumes such a retained tree.
-/

namespace Lax3Proofs.Refine.DriverCache

open Lax3.ColoredGraphs Lax11.GraphEncoding
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.WalkDistance Lax3Proofs.RamBfs Lax3Proofs.RamBfsPaths
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster
open Lax3Proofs.Refine.BfsBlockMask Lax3Proofs.Refine.BfsBlockPar
open Lax3Proofs.Refine.BfsBlockParMask Lax3Proofs.Refine.ScatterBlock

variable {n ns nt d s : ℕ} {G : SimpleGraph (Fin n)} {M O T : ℕ → ℕ}

/-! ### Renaming the cache engine -/

/-- The three pairwise swaps used by the cache are their own inverse. -/
theorem cacheSwap_invol (j : ℕ) (z : String) : cacheSwap j (cacheSwap j z) = z := by
  by_cases h₁ : z = "alv"
  · subst h₁
    simp [cacheSwap, resName, pdsName, parName, balName, balAltName, String.ext_iff]
  · by_cases h₂ : z = resName j
    · subst h₂
      simp [cacheSwap, resName, pdsName, parName, balName, balAltName, String.ext_iff]
    · by_cases h₃ : z = "dist"
      · subst h₃
        simp [cacheSwap, resName, pdsName, parName, balName, balAltName, String.ext_iff]
      · by_cases h₄ : z = pdsName j
        · subst h₄
          simp [cacheSwap, resName, pdsName, parName, balName, balAltName, String.ext_iff]
        · by_cases h₅ : z = "par"
          · subst h₅
            simp [cacheSwap, resName, pdsName, parName, balName, balAltName, String.ext_iff]
          · by_cases h₆ : z = parName j
            · subst h₆
              simp [cacheSwap, resName, pdsName, parName, balName, balAltName,
                String.ext_iff]
            · simp [cacheSwap, h₁, h₂, h₃, h₄, h₅, h₆]

@[simp] theorem cacheSwap_alv (j : ℕ) : cacheSwap j "alv" = resName j := by
  simp [cacheSwap]

@[simp] theorem cacheSwap_dist (j : ℕ) : cacheSwap j "dist" = pdsName j := by
  simp [cacheSwap, resName, pdsName, parName, balName, balAltName, String.ext_iff]

@[simp] theorem cacheSwap_par (j : ℕ) : cacheSwap j "par" = parName j := by
  simp [cacheSwap, resName, pdsName, parName, balName, balAltName, String.ext_iff]

@[simp] theorem cacheSwap_off (j : ℕ) : cacheSwap j "off" = "off" := by
  simp [cacheSwap, resName, pdsName, parName, balName, balAltName, String.ext_iff]

@[simp] theorem cacheSwap_tgt (j : ℕ) : cacheSwap j "tgt" = "tgt" := by
  simp [cacheSwap, resName, pdsName, parName, balName, balAltName, String.ext_iff]

@[simp] theorem cacheSwap_q (j : ℕ) : cacheSwap j "q" = "q" := by
  simp [cacheSwap, resName, pdsName, parName, balName, balAltName, String.ext_iff]

@[simp] theorem cacheSwap_qd (j : ℕ) : cacheSwap j "qd" = "qd" := by
  simp [cacheSwap, resName, pdsName, parName, balName, balAltName, String.ext_iff]

/-- A mask-scoped clean-distance clause at an arbitrary array name. -/
def DistCleanAt (a : String) (n d : ℕ) (M : ℕ → ℕ) (σ : Env) : Prop :=
  ∃ D₀, σ.arrs a = arrOf n D₀ ∧ CleanOn n d M D₀

/-- The mask-scoped parent engine transported directly onto one depth's
retained arrays. -/
theorem cacheBfsCom_specW {B cap j : ℕ} (hcsr : CsrGraph G ns O T) (hs : s < n)
    (hms : M s ≠ 0) (hnB : n < B) (hnsB : ns < B) (hnt : ns ≤ nt)
    (hdB : 2 * cap + 1 < B) (hMB : ∀ z < n, M z < B)
    {A : Finset ℕ}
    (hA : ∀ v, v < n → M v ≠ 0 → WD G M (2 * cap) s v → v ∈ A)
    {bw nb : ℕ} (hbw : ∑ v ∈ A, Csr.rowLen O v ≤ bw) (hnb : A.card ≤ nb) :
    Spec B
      (fun σ => σ.vars "n" = n ∧ σ.vars "src" = s ∧
        σ.arrs "off" = arrOf (n + 1) O ∧ σ.arrs "tgt" = arrOf nt T ∧
        σ.arrs (resName j) = arrOf n M ∧ DistCleanAt (pdsName j) n (2 * cap) M σ ∧
        (∃ g, σ.arrs "q" = arrOf n g) ∧ (∃ g, σ.arrs "qd" = arrOf n g) ∧
        (∃ g, σ.arrs (parName j) = arrOf n g))
      (cacheBfsCom cap j)
      (fun _ σ' => DistCleanAt (pdsName j) n (2 * cap) M σ' ∧
        ∃ D P, σ'.arrs (parName j) = arrOf n P ∧ ParTree G M (2 * cap) s D P)
      (bfsBlockParK bw nb) := by
  have h := bfsBlockParM_specW hcsr hs hms hnB hnsB hnt hdB hMB hA hbw hnb
  have hr := renCom_spec (cacheSwap_invol j) h
  simpa [cacheBfsCom, DistCleanAt, DistClean, renEnv] using hr

/-! ### Walking a retained parent tree -/

/-- The vertices visited in the first `i` iterations of the fixed parent
walk. -/
def parentBelow (n i t : ℕ) (P : ℕ → ℕ) : Set (Fin n) :=
  {z : Fin n | ∃ k < i, (z : ℕ) = parIter P t k}

theorem parentBelow_zero (n t : ℕ) (P : ℕ → ℕ) : parentBelow n 0 t P = ∅ := by
  ext z
  simp [parentBelow]

/-- One more parent iteration adds precisely its current vertex. -/
theorem parentBelow_succ {n i t : ℕ} (P : ℕ → ℕ)
    (hi : parIter P t i < n) :
    parentBelow n (i + 1) t P =
      parentBelow n i t P ∪ {(⟨parIter P t i, hi⟩ : Fin n)} := by
  ext z
  simp only [parentBelow, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨k, hk, hz⟩
    rcases Nat.lt_or_ge k i with hki | hki
    · exact Or.inl ⟨k, hki, hz⟩
    · exact Or.inr (Fin.ext (by rw [hz, show k = i by omega]))
  · rintro (⟨k, hk, hz⟩ | rfl)
    · exact ⟨k, by omega, hz⟩
    · exact ⟨i, by omega, rfl⟩

/-- At the fixed-count exit, `parentBelow` is the ordinary parent buffer
set of radius `d`. -/
theorem parentBelow_succ_eq (n d t : ℕ) (P : ℕ → ℕ) :
    parentBelow n (d + 1) t P = bufSet n d (parIter P t) := by
  ext z
  simp only [parentBelow, Set.mem_setOf_eq, mem_bufSet]
  exact ⟨fun ⟨i, hi, hz⟩ => ⟨i, by omega, hz⟩,
    fun ⟨i, hi, hz⟩ => ⟨i, by omega, hz⟩⟩

/-- Writing one into a mask adds exactly the addressed vertex. -/
theorem markSet_upd_one {n : ℕ} (f : ℕ → ℕ) {k : ℕ} (hk : k < n) :
    markSet n (upd f k 1) = markSet n f ∪ {(⟨k, hk⟩ : Fin n)} := by
  ext z
  simp only [mem_markSet, Set.mem_union, Set.mem_singleton_iff]
  by_cases hz : (z : ℕ) = k
  · rw [hz, upd_self]
    exact ⟨fun _ => Or.inr (Fin.ext hz), fun _ => one_ne_zero⟩
  · rw [upd_of_ne _ hz]
    exact ⟨Or.inl, fun h => h.elim id (fun hc => absurd (by rw [hc]) hz)⟩

/-- Once the distance-many parents have reached the root, all further
iterations stay there because a parent tree roots itself. -/
theorem parIter_after_dist {D P : ℕ → ℕ}
    (hT : ParTree G M d s D P) {t : ℕ} (ht : t < n) (hdt : D t ≤ d) (k : ℕ) :
    parIter P t (D t + k) = s := by
  induction k with
  | zero => simpa using hT.chain_last ht hdt
  | succ k ih =>
      rw [show D t + (k + 1) = (D t + k) + 1 by omega, parIter_succ, ih, hT.self]

/-- Every cell read by the fixed `d + 1` parent walk is a vertex, including
the repetitions of the root after a shorter path has ended. -/
theorem parIter_lt_cap {D P : ℕ → ℕ}
    (hT : ParTree G M d s D P) {t : ℕ} (ht : t < n) (hdt : D t ≤ d) :
    ∀ i ≤ d + 1, parIter P t i < n := by
  have hs : s < n := by
    have h := (hT.chain ht hdt (D t) le_rfl).1
    rwa [hT.chain_last ht hdt] at h
  intro i hi
  by_cases hid : i ≤ D t
  · exact (hT.chain ht hdt i hid).1
  · have hie : i = D t + (i - D t) := by omega
    rw [hie, parIter_after_dist hT ht hdt]
    exact hs

/-- Extending a parent buffer beyond the target's distance adds only
repetitions of the root, which was already its last cell. -/
theorem bufSet_cap_eq {D P : ℕ → ℕ}
    (hT : ParTree G M d s D P) {t : ℕ} (ht : t < n) (hdt : D t ≤ d) :
    bufSet n d (parIter P t) = bufSet n (D t) (parIter P t) := by
  ext z
  simp only [mem_bufSet]
  constructor
  · rintro ⟨i, hi, hz⟩
    by_cases hid : i ≤ D t
    · exact ⟨i, hid, hz⟩
    · have hie : i = D t + (i - D t) := by omega
      have hit : parIter P t i = s := by
        rw [hie, parIter_after_dist hT ht hdt]
      exact ⟨D t, le_rfl, by rw [hz, hit, hT.chain_last ht hdt]⟩
  · rintro ⟨i, hi, hz⟩
    exact ⟨i, by omega, hz⟩

/-- The loop invariant for consuming a retained tree. -/
def ParentMarkInv (n d t j a : ℕ) (P Wa : ℕ → ℕ) (sigma : Env) : Prop :=
  sigma.arrs (parName a) = arrOf n P ∧ sigma.vars "plen" = d + 1 ∧
    sigma.vars "pi" ≤ d + 1 ∧ sigma.vars "pc" = parIter P t (sigma.vars "pi") ∧
    ∃ Wa' : ℕ → ℕ, sigma.arrs (batName j) = arrOf n Wa' ∧
      (∀ k, k < n → Wa' k ≤ 1) ∧
      markSet n Wa' = markSet n Wa ∪ parentBelow n (sigma.vars "pi") t P

/-- One fixed parent step preserves the cached tree and adds its current
vertex to the batch indicator. -/
theorem markParentStep_spec {B n d s t j a : ℕ} {G : SimpleGraph (Fin n)}
    {M D P Wa : ℕ → ℕ} (hT : ParTree G M d s D P) (ht : t < n)
    (hdt : D t ≤ d) (hnB : n < B) (hdB : d + 1 < B) (h1B : 1 < B) :
    Spec B (fun sigma => ParentMarkInv n d t j a P Wa sigma ∧ sigma.vars "pi" < d + 1)
      (markParentStep j a)
      (fun sigma sigma' => ParentMarkInv n d t j a P Wa sigma' ∧
        sigma'.vars "pi" = sigma.vars "pi" + 1) 12 := by
  refine Spec.of_exists (fun sigma hsigma => ?_)
  obtain ⟨⟨hpar, hplen, hpile, hpc, Wa', hbat, hbit, hmark⟩, hpilt⟩ := hsigma
  have hanc : parIter P t (sigma.vars "pi") < n :=
    parIter_lt_cap hT ht hdt _ (by omega)
  have hpcn : sigma.vars "pc" < n := by rw [hpc]; exact hanc
  have hstep : P (sigma.vars "pc") = parIter P t (sigma.vars "pi" + 1) := by
    rw [parIter_succ, hpc]
  have hnextn : P (sigma.vars "pc") < n := by
    rw [hstep]
    exact parIter_lt_cap hT ht hdt _ (by omega)
  have hbatlen : sigma.vars "pc" < (sigma.arrs (batName j)).length := by
    rw [hbat, length_arrOf]
    exact hpcn
  have hparlen : sigma.vars "pc" < (sigma.arrs (parName a)).length := by
    rw [hpar, length_arrOf]
    exact hpcn
  have hparv : (sigma.arrs (parName a)).getD (sigma.vars "pc") 0 = P (sigma.vars "pc") := by
    rw [hpar, getD_arrOf P hpcn]
  have hparv' : (sigma.arrs (parName a))[sigma.vars "pc"]?.getD 0 = P (sigma.vars "pc") := by
    rw [← List.getD_eq_getElem?_getD]
    exact hparv
  have hparB : (sigma.arrs (parName a))[sigma.vars "pc"]?.getD 0 < B := by
    rw [hparv']
    omega
  have hpcB : sigma.vars "pc" < B := by omega
  have hpiB : sigma.vars "pi" + 1 < B := by omega
  have hnames : batName j ≠ parName a := by
    simp [batName, parName, balName, String.ext_iff]
  have hnames' : parName a ≠ batName j := Ne.symm hnames
  have hparlen' :
      (sigma.setArr (batName j) (sigma.vars "pc") 1).vars "pc" <
        ((sigma.setArr (batName j) (sigma.vars "pc") 1).arrs (parName a)).length := by
    simpa [hnames'] using hparlen
  have hparB' :
      ((sigma.setArr (batName j) (sigma.vars "pc") 1).arrs (parName a)).getD
          ((sigma.setArr (batName j) (sigma.vars "pc") 1).vars "pc") 0 < B := by
    simpa [hnames'] using (show (sigma.arrs (parName a)).getD (sigma.vars "pc") 0 < B by
      rw [hparv]
      omega)
  run_vcg
  refine ⟨⟨by simp [hpar, hnames'], by simp [hplen], by simp; omega,
    by simp [hnames', hparv', hstep], upd Wa' (sigma.vars "pc") 1,
    by simp [hbat, set_arrOf_eq_upd], ?_, ?_⟩, by simp⟩
  · intro k hk
    by_cases hke : k = sigma.vars "pc"
    · rw [hke, upd_self]
    · rw [upd_of_ne _ hke]
      exact hbit k hk
  · simp only [vars_setVar, vars_setArr, String.reduceEq, ↓reduceIte]
    have hfin : (⟨sigma.vars "pc", hpcn⟩ : Fin n) =
        ⟨parIter P t (sigma.vars "pi"), hanc⟩ := Fin.ext hpc
    rw [markSet_upd_one Wa' hpcn, hmark, parentBelow_succ P hanc,
      hfin, Set.union_assoc]

/-- Cost of consuming one retained tree. -/
def markParentsK (cap : ℕ) : ℕ := 32 * cap + 30

/-- **A retained parent tree supplies one earlier round's path.** The
fixed-count loop marks its entire capped parent chain; repetitions after
the root do not enlarge the set, so it has the support and size of the
tree's actual source-to-target walk. -/
theorem markParentsCom_spec {B n cap s t j a : ℕ} {G : SimpleGraph (Fin n)}
    {M D P Wa : ℕ → ℕ} (hT : ParTree G M (2 * cap) s D P) (hs : s < n)
    (ht : t < n) (hdt : D t ≤ 2 * cap) (hnB : n < B)
    (hdB : 2 * cap + 1 < B) (h1B : 1 < B) (hbit : ∀ k, k < n → Wa k ≤ 1) :
    Spec B (fun sigma => sigma.vars (ctrName j) = t ∧
        sigma.arrs (parName a) = arrOf n P ∧
        sigma.arrs (batName j) = arrOf n Wa)
      (markParentsCom cap j a)
      (fun _ sigma' => ∃ Wa' : ℕ → ℕ,
        sigma'.arrs (batName j) = arrOf n Wa' ∧ (∀ k, k < n → Wa' k ≤ 1) ∧
        markSet n Wa' = markSet n Wa ∪ bufSet n (2 * cap) (parIter P t) ∧
        (bufSet n (2 * cap) (parIter P t)).ncard ≤ 2 * cap + 1 ∧
        ∃ p : (masked G M).Walk ⟨s, hs⟩ ⟨t, ht⟩, p.length ≤ 2 * cap ∧
          {z : Fin n | z ∈ p.support} = bufSet n (2 * cap) (parIter P t))
      (markParentsK cap) := by
  have hloop := Spec.forRangeZero (B := B) "pi" "plen"
    (ParentMarkInv n (2 * cap) t j a P Wa) (2 * cap + 1) 12 hdB
    (fun sigma h => h.2.2.1) (fun sigma h => h.2.1)
    (markParentStep_spec hT ht hdt hnB hdB h1B)
  refine Spec.of_exists (fun sigma hsigma => ?_)
  obtain ⟨hctr, hpar, hbat⟩ := hsigma
  have hctrB : sigma.vars (ctrName j) < B := by rw [hctr]; omega
  unfold markParentsK
  run_vcg [hloop]
  · obtain ⟨⟨hpar', hplen', hpile', hpc', Wa', hbat', hbit', hmark'⟩, hpi'⟩ :=
      ‹ParentMarkInv n (2 * cap) t j a P Wa _ ∧ _›
    obtain ⟨p, hplenp, hpsup⟩ := hT.walk hs (D t) hdt ⟨t, ht⟩ rfl
    refine ⟨Wa', hbat', hbit', ?_, ?_, p, by omega, ?_⟩
    · rw [hmark', hpi', parentBelow_succ_eq]
    · rw [bufSet_cap_eq hT ht hdt, ← hpsup]
      exact ncard_support_le p (by omega)
    · rw [bufSet_cap_eq hT ht hdt, ← hpsup]
  · refine ⟨by simp [hpar], by simp, by simp, by simp [hctr], Wa, by simp [hbat], hbit, ?_⟩
    simp only [vars_setVar, ↓reduceIte]
    rw [parentBelow_zero, Set.union_empty]

end Lax3Proofs.Refine.DriverCache
