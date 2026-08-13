import Lax3Proofs.Refine.CoverActiveStreamMask

/-!
# Cached batches on one streamed cover row

The carrier implementation of `batchCachedCom` first marks complete cached
parent chains and then cuts their union back to the current cluster with a
carrier-wide pass.  On a reusable streamed row that cut is too late: cells of
the parent chains outside the row would remain resident.

This module moves the cut into the parent walk.  Each visited parent cell is
assigned the current cluster bit, so the batch is supported by
`xmem[0..tail)` throughout its lifetime.  The opening batch array is zero and
the row-local release pass restores that state after the cluster consumer is
finished.  The child and game masks are consequently exact sparse writes over
the same row.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamBatch

open Lax3.ColoredGraphs
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster
open Lax3Proofs.RamDriverDescend
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamBfsPaths
open Lax3Proofs.Refine.DriverCache
open Lax3Proofs.Refine.CoverActiveStreamLoad
open Lax3Proofs.Refine.CoverActiveStreamMask
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ## Cutting a cached parent chain while it is walked -/

/-- One cached-parent step writes the cluster bit rather than the constant
one.  Parent traversal is unchanged; only the batch write is cut eagerly. -/
def streamMarkParentStep (j a : ℕ) : Com :=
  .seq (.store (batName j) (.var "pc") (.get (cluName j) (.var "pc")))
    (.seq (.assign "pc" (.get (parName a) (.var "pc")))
      (.assign "pi" (.add (.var "pi") (.lit 1))))

/-- Walk one retained parent tree for its fixed capped length, cutting every
marked vertex to the resident streamed cluster as it is visited. -/
def streamMarkParentsCom (cap j a : ℕ) : Com :=
  .seq (.assign "pc" (.var (ctrName j)))
    (.seq (.assign "plen" (.lit (2 * cap + 1)))
      (.seq (.assign "pi" (.lit 0))
        (.while (.lt (.var "pi") (.var "plen"))
          (streamMarkParentStep j a))))

/-- Updating one indicator cell by another indicator adds precisely the
addressed singleton when the second indicator marks it. -/
theorem markSet_upd_indicator {n : ℕ} (f X : ℕ → ℕ) {k : ℕ} (hk : k < n)
    (hsub : markSet n f ⊆ markSet n X) :
    markSet n (upd f k (X k)) =
      markSet n f ∪ ({(⟨k, hk⟩ : Fin n)} ∩ markSet n X) := by
  ext z
  simp only [mem_markSet, Set.mem_union, Set.mem_inter_iff, Set.mem_singleton_iff]
  by_cases hzk : (z : ℕ) = k
  · have hzfin : z = ⟨k, hk⟩ := Fin.ext hzk
    subst z
    rw [upd_self]
    constructor
    · intro hX
      exact Or.inr ⟨rfl, hX⟩
    · rintro (hf | ⟨-, hX⟩)
      · exact hsub hf
      · exact hX
  · rw [upd_of_ne _ hzk]
    constructor
    · exact Or.inl
    · rintro (hf | ⟨hz, -⟩)
      · exact hf
      · exact absurd (congrArg Fin.val hz) hzk

/-- The cut parent walk retains the ordinary parent iterator and records the
part of its visited prefix lying in the streamed cluster. -/
def StreamParentMarkInv (n d t j a : ℕ) (P Xa Wa : ℕ → ℕ)
    (sigma : Env) : Prop :=
  sigma.arrs (parName a) = arrOf n P ∧
    sigma.arrs (cluName j) = arrOf n Xa ∧
    sigma.vars "plen" = d + 1 ∧ sigma.vars "pi" ≤ d + 1 ∧
    sigma.vars "pc" = parIter P t (sigma.vars "pi") ∧
    ∃ Wa' : ℕ → ℕ, sigma.arrs (batName j) = arrOf n Wa' ∧
      (∀ k, k < n → Wa' k ≤ 1) ∧
      markSet n Wa' ⊆ markSet n Xa ∧
      markSet n Wa' = markSet n Wa ∪
        (parentBelow n (sigma.vars "pi") t P ∩ markSet n Xa)

/-- One eagerly-cut parent step preserves the cached tree and adds exactly
the current parent vertex when that vertex belongs to the streamed row. -/
theorem streamMarkParentStep_spec
    {B n d s t j a : ℕ} {G : SimpleGraph (Fin n)}
    {M D P Xa Wa : ℕ → ℕ}
    (hT : ParTree G M d s D P) (ht : t < n) (hdt : D t ≤ d)
    (hnB : n < B) (hdB : d + 1 < B) (h1B : 1 < B)
    (hXbit : ∀ k, k < n → Xa k ≤ 1) :
    Spec B
      (fun sigma => StreamParentMarkInv n d t j a P Xa Wa sigma ∧
        sigma.vars "pi" < d + 1)
      (streamMarkParentStep j a)
      (fun sigma sigma' => StreamParentMarkInv n d t j a P Xa Wa sigma' ∧
        sigma'.vars "pi" = sigma.vars "pi" + 1)
      14 := by
  refine Spec.of_exists (fun sigma hsigma => ?_)
  obtain ⟨⟨hpar, hclu, hplen, hpile, hpc, Wa', hbat, hbit, hsub, hmark⟩,
    hpilt⟩ := hsigma
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
  have hclulen : sigma.vars "pc" < (sigma.arrs (cluName j)).length := by
    rw [hclu, length_arrOf]
    exact hpcn
  have hparv : (sigma.arrs (parName a)).getD (sigma.vars "pc") 0 =
      P (sigma.vars "pc") := by
    rw [hpar, getD_arrOf P hpcn]
  have hparv' : (sigma.arrs (parName a))[sigma.vars "pc"]?.getD 0 =
      P (sigma.vars "pc") := by
    rw [← List.getD_eq_getElem?_getD]
    exact hparv
  have hcluv : (sigma.arrs (cluName j)).getD (sigma.vars "pc") 0 =
      Xa (sigma.vars "pc") := by
    rw [hclu, getD_arrOf Xa hpcn]
  have hcluv' : (sigma.arrs (cluName j))[sigma.vars "pc"]?.getD 0 =
      Xa (sigma.vars "pc") := by
    rw [← List.getD_eq_getElem?_getD]
    exact hcluv
  have hparB : (sigma.arrs (parName a))[sigma.vars "pc"]?.getD 0 < B := by
    rw [hparv']
    omega
  have hcluB : (sigma.arrs (cluName j))[sigma.vars "pc"]?.getD 0 < B := by
    rw [hcluv']
    exact lt_of_le_of_lt (hXbit _ hpcn) h1B
  have hpcB : sigma.vars "pc" < B := by omega
  have hpiB : sigma.vars "pi" + 1 < B := by omega
  have hbatpar : batName j ≠ parName a := by
    simp [batName, parName, balName, String.ext_iff]
  have hbatclu : batName j ≠ cluName j := by
    simp [batName, cluName, String.ext_iff]
  have hparbat : parName a ≠ batName j := Ne.symm hbatpar
  have hclubat : cluName j ≠ batName j := Ne.symm hbatclu
  have hparlen' :
      (sigma.setArr (batName j) (sigma.vars "pc") (Xa (sigma.vars "pc"))).vars "pc" <
        ((sigma.setArr (batName j) (sigma.vars "pc")
          (Xa (sigma.vars "pc"))).arrs (parName a)).length := by
    simpa [hparbat] using hparlen
  have hparB' :
      ((sigma.setArr (batName j) (sigma.vars "pc")
          (Xa (sigma.vars "pc"))).arrs (parName a)).getD
          ((sigma.setArr (batName j) (sigma.vars "pc")
            (Xa (sigma.vars "pc"))).vars "pc") 0 < B := by
    simpa [hparbat] using
      (show (sigma.arrs (parName a)).getD (sigma.vars "pc") 0 < B by
        rw [hparv]
        omega)
  have hcluArr' :
      (sigma.setArr (batName j) (sigma.vars "pc")
        (Xa (sigma.vars "pc"))).arrs (cluName j) = arrOf n Xa := by
    simp [hclubat, hclu]
  have hparlenRun :
      (sigma.setArr (batName j) (sigma.vars "pc")
        ((sigma.arrs (cluName j)).getD (sigma.vars "pc") 0)).vars "pc" <
        ((sigma.setArr (batName j) (sigma.vars "pc")
          ((sigma.arrs (cluName j)).getD (sigma.vars "pc") 0)).arrs
          (parName a)).length := by
    simpa [hcluv] using hparlen'
  have hparBRun :
      ((sigma.setArr (batName j) (sigma.vars "pc")
          ((sigma.arrs (cluName j)).getD (sigma.vars "pc") 0)).arrs
          (parName a)).getD
          ((sigma.setArr (batName j) (sigma.vars "pc")
            ((sigma.arrs (cluName j)).getD (sigma.vars "pc") 0)).vars "pc") 0 < B := by
    simpa [hcluv] using hparB'
  run_vcg
  refine ⟨⟨by simp [hpar, hparbat], by simp [hclu, hclubat], by simp [hplen],
    by simp; omega, by simp [hparbat, hparv', hstep],
    upd Wa' (sigma.vars "pc") (Xa (sigma.vars "pc")),
    by simp [hbat, hcluv', set_arrOf_eq_upd], ?_, ?_, ?_⟩, by simp⟩
  · intro k hk
    by_cases hke : k = sigma.vars "pc"
    · rw [hke, upd_self]
      exact hXbit _ hpcn
    · rw [upd_of_ne _ hke]
      exact hbit k hk
  · rw [markSet_upd_indicator Wa' Xa hpcn hsub]
    exact Set.union_subset hsub Set.inter_subset_right
  · simp only [vars_setVar, vars_setArr, String.reduceEq, ↓reduceIte]
    rw [markSet_upd_indicator Wa' Xa hpcn hsub, hmark,
      parentBelow_succ P hanc]
    have hfin : (⟨sigma.vars "pc", hpcn⟩ : Fin n) =
        ⟨parIter P t (sigma.vars "pi"), hanc⟩ := Fin.ext hpc
    rw [hfin]
    ext z
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_singleton_iff]
    tauto

/-- Cost of one eagerly-cut retained parent walk. -/
def streamMarkParentsK (cap : ℕ) : ℕ := 36 * cap + 32

/-- A retained parent tree contributes exactly the part of its capped parent
chain inside the streamed cluster. -/
theorem streamMarkParentsCom_spec
    {B n cap s t j a : ℕ} {G : SimpleGraph (Fin n)}
    {M D P Xa Wa : ℕ → ℕ}
    (hT : ParTree G M (2 * cap) s D P) (hs : s < n) (ht : t < n)
    (hdt : D t ≤ 2 * cap) (hnB : n < B) (hdB : 2 * cap + 1 < B)
    (h1B : 1 < B) (hbit : ∀ k, k < n → Wa k ≤ 1)
    (hWsub : markSet n Wa ⊆ markSet n Xa)
    (hXbit : ∀ k, k < n → Xa k ≤ 1) :
    Spec B
      (fun sigma => sigma.vars (ctrName j) = t ∧
        sigma.arrs (parName a) = arrOf n P ∧
        sigma.arrs (cluName j) = arrOf n Xa ∧
        sigma.arrs (batName j) = arrOf n Wa)
      (streamMarkParentsCom cap j a)
      (fun _ sigma' => ∃ Wa' : ℕ → ℕ,
        sigma'.arrs (batName j) = arrOf n Wa' ∧
        (∀ k, k < n → Wa' k ≤ 1) ∧
        markSet n Wa' ⊆ markSet n Xa ∧
        markSet n Wa' = markSet n Wa ∪
          (bufSet n (2 * cap) (parIter P t) ∩ markSet n Xa) ∧
        (bufSet n (2 * cap) (parIter P t)).ncard ≤ 2 * cap + 1 ∧
        ∃ p : (masked G M).Walk ⟨s, hs⟩ ⟨t, ht⟩,
          p.length ≤ 2 * cap ∧
          {z : Fin n | z ∈ p.support} =
            bufSet n (2 * cap) (parIter P t))
      (streamMarkParentsK cap) := by
  have hloop := Spec.forRangeZero (B := B) "pi" "plen"
    (StreamParentMarkInv n (2 * cap) t j a P Xa Wa) (2 * cap + 1) 14 hdB
    (fun sigma h => h.2.2.2.1) (fun sigma h => h.2.2.1)
    (streamMarkParentStep_spec hT ht hdt hnB hdB h1B hXbit)
  refine Spec.of_exists (fun sigma hsigma => ?_)
  obtain ⟨hctr, hpar, hclu, hbat⟩ := hsigma
  have hctrB : sigma.vars (ctrName j) < B := by rw [hctr]; omega
  unfold streamMarkParentsK
  run_vcg [hloop]
  · obtain ⟨⟨hpar', hclu', hplen', hpile', hpc', Wa', hbat', hbit', hsub', hmark'⟩,
      hpi'⟩ := ‹StreamParentMarkInv n (2 * cap) t j a P Xa Wa _ ∧ _›
    obtain ⟨p, hplenp, hpsup⟩ := hT.walk hs (D t) hdt ⟨t, ht⟩ rfl
    refine ⟨Wa', hbat', hbit', hsub', ?_, ?_, p, by omega, ?_⟩
    · rw [hmark', hpi', parentBelow_succ_eq]
    · rw [bufSet_cap_eq hT ht hdt, ← hpsup]
      exact ncard_support_le p (by omega)
    · rw [bufSet_cap_eq hT ht hdt, ← hpsup]
  · refine ⟨by simp [hpar], by simp [hclu], by simp, by simp, by simp [hctr], Wa,
      by simp [hbat], hbit, hWsub, ?_⟩
    simp only [vars_setVar, ↓reduceIte]
    rw [parentBelow_zero, Set.empty_inter, Set.union_empty]

/-! ## A cached batch that is supported throughout -/

theorem warrs_streamMarkParentsCom (cap j a : ℕ) :
    (streamMarkParentsCom cap j a).warrs = [batName j] := rfl

theorem wvars_streamMarkParentsCom (cap j a : ℕ) :
    (streamMarkParentsCom cap j a).wvars =
      (markParentsCom cap j a).wvars := rfl

theorem mem_wvars_streamMarkParentsCom {cap j a : ℕ} {y : String}
    (h : y ∈ (streamMarkParentsCom cap j a).wvars) :
    y ∈ descendScalars := by
  rw [wvars_streamMarkParentsCom] at h
  exact mem_wvars_markParentsCom h

/-- The batch accumulated after `s` retained parent walks.  In addition to
the executable game clauses of `BatchMark`, every intermediate indicator is
already contained in the streamed cluster. -/
def StreamBatchMark {n : ℕ} (cap j : ℕ) (G : SimpleGraph (Fin n))
    (U : ℕ → Fin n) (Gam : ℕ → ℕ → ℕ) (v : Fin n)
    (X : Set (Fin n)) (s : ℕ) (sigma : Env) : Prop :=
  ∃ Wa : ℕ → ℕ, sigma.arrs (batName j) = arrOf n Wa ∧
    (∀ k, k < n → Wa k ≤ 1) ∧ markSet n Wa ⊆ X ∧
    v ∈ markSet n Wa ∧ (markSet n Wa).ncard ≤ 1 + s * (2 * cap + 1) ∧
    ∀ a, a < s → WithinDist (masked G (Gam a)) (2 * cap) (U a) v →
      ∃ p : (masked G (Gam a)).Walk (U a) v, p.length ≤ 2 * cap ∧
        {z : Fin n | z ∈ p.support} ∩ X ⊆ markSet n Wa

/-- The eagerly-cut cached fold has the same actual parent-chain work as the
old cached fold, plus one cluster read per visited parent cell. -/
theorem streamBatchCachedFold_spec
    {B n ns nt cap mb j : ℕ} {d : ℕ} {G : SimpleGraph (Fin n)}
    {O T : ℕ → ℕ}
    (hB : WordBoundK B n d ns cap mb) {U : ℕ → Fin n}
    {Gam : ℕ → ℕ → ℕ} {M Xa : ℕ → ℕ} {v : Fin n}
    (hMv : M (v : ℕ) ≠ 0) (hXbit : ∀ k, k < n → Xa k ≤ 1) :
    ∀ (r s : ℕ), s + r ≤ j →
      Spec B
        (fun sigma => BatchEnv cap nt j O T U Gam v sigma ∧
          CachedRounds cap G j M sigma ∧
          sigma.arrs (cluName j) = arrOf n Xa ∧
          StreamBatchMark cap j G U Gam v (markSet n Xa) s sigma)
        (foldRange (fun b => streamMarkParentsCom cap j (s + b)) r)
        (fun _ sigma' => BatchEnv cap nt j O T U Gam v sigma' ∧
          CachedRounds cap G j M sigma' ∧
          sigma'.arrs (cluName j) = arrOf n Xa ∧
          StreamBatchMark cap j G U Gam v (markSet n Xa) (s + r) sigma')
        (streamMarkParentsK cap * r + 1) := by
  have hnB := hB.n_lt
  have h1B := hB.one_lt
  have hdB : 2 * cap + 1 < B := by have := hB.1; omega
  intro r
  induction r with
  | zero =>
      intro s _
      exact Spec.of_exists (fun sigma h =>
        ⟨sigma, 1, Run.skip, by omega, h.1, h.2.1, h.2.2.1, h.2.2.2⟩)
  | succ r ih =>
      intro s hsr
      have hsj : s < j := by omega
      refine Spec.of_exists (fun sigma hsigma => ?_)
      rcases hsigma with ⟨hEnv, hCache, hClu, hMark⟩
      rcases hMark with ⟨Wa, hbat, hbit, hWsub, hvW, hcard, hwalk⟩
      obtain ⟨hn, hoff, htgt, halv, hdist, hq, hpar, hpath, hctrj, hctr, hgam⟩ := hEnv
      obtain ⟨u, R, Ga, D, P, hctra, hresa, hgama, hpara, hT, hRG, hdt⟩ :=
        hCache.target hsj v.isLt hMv
      have hu : u = U s := by
        apply Fin.ext
        rw [← hctra, hctr s hsj]
      subst u
      have hGaEq : ∀ z, z < n → Ga z = Gam s z := by
        intro z hz
        apply eq_of_arrOf_eq (N := n) (by rw [← hgama, ← hgam s hsj]) hz
      have hGaMask : masked G Ga = masked G (Gam s) := masked_congr hGaEq
      have hle : masked G R ≤ masked G (Gam s) := by
        rw [← hGaMask]
        exact hRG
      obtain ⟨sigma₁, hr₁, Wa', hbat₁, hbit₁, hsub₁, hmark₁, hcard₁,
          p, hp, hpsup⟩ :=
        (streamMarkParentsCom_spec (j := j) (a := s) hT (U s).isLt v.isLt hdt
          hnB hdB h1B hbit hWsub hXbit).run (σ := sigma)
          ⟨hctrj, hpara, hClu, hbat⟩
      have henv₁ : BatchEnv cap nt j O T U Gam v sigma₁ :=
        batchEnv_run
          ⟨hn, hoff, htgt, halv, hdist, hq, hpar, hpath, hctrj, hctr, hgam⟩ hr₁
          (fun _ hy => mem_wvars_streamMarkParentsCom hy)
          (fun b hb => Or.inl (by
            rw [warrs_streamMarkParentsCom] at hb
            exact List.eq_of_mem_singleton hb))
      have hcache₁ : CachedRounds cap G j M sigma₁ :=
        cachedRounds_batch_run hCache hr₁
          (fun _ hy => mem_wvars_streamMarkParentsCom hy)
          (fun b hb => by
            rw [warrs_streamMarkParentsCom] at hb
            exact List.eq_of_mem_singleton hb)
      have hclu₁ : sigma₁.arrs (cluName j) = arrOf n Xa := by
        rw [hr₁.frame_arr (cluName j) (by
          rw [warrs_streamMarkParentsCom]
          simp [cluName, batName, String.ext_iff])]
        exact hClu
      let p' : (masked G (Gam s)).Walk (U s) v := p.mapLe hle
      have hp' : p'.length ≤ 2 * cap :=
        (SimpleGraph.Walk.length_map _ p).le.trans hp
      have hpsup' : {z : Fin n | z ∈ p'.support} =
          bufSet n (2 * cap) (parIter P (v : ℕ)) := by
        rw [show p' = p.mapLe hle by rfl,
          SimpleGraph.Walk.support_mapLe_eq_support hle p, hpsup]
      have hmono : markSet n Wa ⊆ markSet n Wa' := by
        rw [hmark₁]
        exact Set.subset_union_left
      have hmk₁ : StreamBatchMark cap j G U Gam v (markSet n Xa) (s + 1) sigma₁ := by
        refine ⟨Wa', hbat₁, hbit₁, hsub₁, hmono hvW, ?_, ?_⟩
        · rw [hmark₁]
          calc
            (markSet n Wa ∪
                (bufSet n (2 * cap) (parIter P (v : ℕ)) ∩ markSet n Xa)).ncard ≤
                (markSet n Wa).ncard +
                  (bufSet n (2 * cap) (parIter P (v : ℕ)) ∩
                    markSet n Xa).ncard := Set.ncard_union_le _ _
            _ ≤ (1 + s * (2 * cap + 1)) + (2 * cap + 1) := by
              apply Nat.add_le_add hcard
              exact le_trans
                (Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)) hcard₁
            _ = 1 + (s + 1) * (2 * cap + 1) := by ring
        · intro b hb hwd
          rcases Nat.lt_or_ge b s with hbs | hbs
          · obtain ⟨q, hq', hqs⟩ := hwalk b hbs hwd
            exact ⟨q, hq', subset_trans hqs hmono⟩
          · have hbe : b = s := by omega
            subst hbe
            exact ⟨p', hp', by
              rw [hmark₁, hpsup']
              exact Set.subset_union_right⟩
      have hshift :
          (fun b => streamMarkParentsCom cap j (s + (b + 1))) =
            (fun b => streamMarkParentsCom cap j (s + 1 + b)) := by
        funext b
        congr 1
        omega
      obtain ⟨sigma₂, hr₂, henv₂, hcache₂, hclu₂, hmk₂⟩ :=
        (ih (s + 1) (by omega)).run (σ := sigma₁)
          ⟨henv₁, hcache₁, hclu₁, hmk₁⟩
      have hr₂' :
          Run B (foldRange (fun b => streamMarkParentsCom cap j (s + (b + 1))) r)
            sigma₁ sigma₂ (streamMarkParentsK cap * r + 1) := by
        rw [hshift]
        exact hr₂
      have hrun :
          Run B (foldRange (fun b => streamMarkParentsCom cap j (s + b)) (r + 1))
            sigma sigma₂
            (streamMarkParentsK cap + (streamMarkParentsK cap * r + 1)) := by
        rw [foldRange_succ]
        exact hr₁.seq hr₂'
      refine ⟨sigma₂, _, hrun, by ring_nf; omega, henv₂, hcache₂,
        hclu₂, ?_⟩
      have hre : s + 1 + r = s + (r + 1) := by omega
      rwa [hre] at hmk₂

/-- Opening a streamed batch writes only its connector and then performs the
eagerly-cut cached parent fold.  The zero precondition is the reusable-array
lifecycle boundary; no carrier fill and no post-fold carrier cut occur. -/
def streamBatchCachedCom (cap j : ℕ) : Com :=
  .seq (.store (batName j) (.var (ctrName j))
      (.get (cluName j) (.var (ctrName j))))
    (foldRange (fun a => streamMarkParentsCom cap j a) j)

def streamBatchCachedCost (cap j : ℕ) : ℕ :=
  streamMarkParentsK cap * j + 5

/-- Set containment in a row-supported indicator is the pointwise support
premise needed by the exact sparse-map adapters. -/
theorem blockSupported_of_markSet_subset
    {n p₀ e : ℕ} {Idx F X : ℕ → ℕ}
    (hsub : markSet n F ⊆ markSet n X)
    (hX : BlockSupported n p₀ e Idx X) :
    BlockSupported n p₀ e Idx F := by
  intro z hz hout
  by_contra hF
  have hzF : (⟨z, hz⟩ : Fin n) ∈ markSet n F := hF
  have hzX := hsub hzF
  exact hzX (hX z hz hout)

/-- **The streamed cached batch.** Its exact mathematical batch is the same
cluster-cut connector-and-walk union as `batchCachedCom_spec`, but the batch
never leaves the row and the cost contains only actual cached-parent work. -/
theorem streamBatchCachedCom_spec
    {B n ns nt cap mb j tail : ℕ} {d : ℕ}
    {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}
    (hB : WordBoundK B n d ns cap mb) {U : ℕ → Fin n}
    {Gam : ℕ → ℕ → ℕ} {M Xa Xmem : ℕ → ℕ} {v : Fin n}
    (hMv : M (v : ℕ) ≠ 0) (hXbit : ∀ k, k < n → Xa k ≤ 1)
    (hvX : Xa (v : ℕ) ≠ 0) (hXsup : BlockSupported n 0 tail Xmem Xa) :
    Spec B
      (fun sigma => BatchEnv cap nt j O T U Gam v sigma ∧
        CachedRounds cap G j M sigma ∧
        sigma.arrs (cluName j) = arrOf n Xa ∧
        sigma.arrs (batName j) = arrOf n (fun _ => 0))
      (streamBatchCachedCom cap j)
      (fun _ sigma' => BatchEnv cap nt j O T U Gam v sigma' ∧
        CachedRounds cap G j M sigma' ∧
        sigma'.arrs (cluName j) = arrOf n Xa ∧
        ∃ Wa : ℕ → ℕ, sigma'.arrs (batName j) = arrOf n Wa ∧
          (∀ k, k < n → Wa k < B) ∧
          markSet n Wa ⊆ markSet n Xa ∧ v ∈ markSet n Wa ∧
          (markSet n Wa).ncard ≤ 1 + j * (2 * cap + 1) ∧
          (∀ a, a < j → WithinDist (masked G (Gam a)) (2 * cap) (U a) v →
            ∃ p : (masked G (Gam a)).Walk (U a) v, p.length ≤ 2 * cap ∧
              {z : Fin n | z ∈ p.support} ∩ markSet n Xa ⊆ markSet n Wa) ∧
          BlockSupported n 0 tail Xmem Wa)
      (streamBatchCachedCost cap j) := by
  have hnB := hB.n_lt
  have h1B := hB.one_lt
  refine Spec.of_exists (fun sigma hsigma => ?_)
  obtain ⟨henv, hcache, hclu, hbat₀⟩ := hsigma
  have hctr : sigma.vars (ctrName j) = (v : ℕ) :=
    henv.2.2.2.2.2.2.2.2.1
  have hvn : (v : ℕ) < n := v.isLt
  have hidxB : sigma.vars (ctrName j) < B := by rw [hctr]; omega
  have hidxLen : sigma.vars (ctrName j) < (sigma.arrs (batName j)).length := by
    rw [hbat₀, length_arrOf, hctr]
    exact hvn
  have hcluLen : sigma.vars (ctrName j) < (sigma.arrs (cluName j)).length := by
    rw [hclu, length_arrOf, hctr]
    exact hvn
  have ectr : (Expr.var (ctrName j)).evalB B sigma = some (v : ℕ) := by
    have h := evalB_var (B := B) (x := ctrName j) (σ := sigma) hidxB
    rwa [hctr] at h
  have eclu : (Expr.get (cluName j) (.var (ctrName j))).evalB B sigma =
      some (Xa (v : ℕ)) :=
    evalB_get ectr (by rw [hclu, getElem?_arrOf Xa hvn])
      (lt_of_le_of_lt (hXbit _ hvn) h1B)
  set sigma₁ := sigma.setArr (batName j) (v : ℕ) (Xa (v : ℕ)) with hsigma₁
  have hr₁ : Run B
      (.store (batName j) (.var (ctrName j))
        (.get (cluName j) (.var (ctrName j)))) sigma sigma₁ 4 :=
    (Run.store ectr eclu (by simpa [hctr] using hidxLen)).mono (by simp [Expr.size])
  let W₁ := upd (fun _ => 0) (v : ℕ) (Xa (v : ℕ))
  have hbat₁ : sigma₁.arrs (batName j) = arrOf n W₁ := by
    simp [hsigma₁, hbat₀, W₁, set_arrOf_eq_upd]
  have hzero : markSet n (fun _ => 0) = ∅ := by
    ext z
    simp only [mem_markSet, Set.mem_empty_iff_false, iff_false, not_not]
  have hW₁set : markSet n W₁ = {v} := by
    rw [show W₁ = upd (fun _ => 0) (v : ℕ) (Xa (v : ℕ)) by rfl,
      markSet_upd_indicator (fun _ => 0) Xa hvn (by
        intro z hz
        change (0 : ℕ) ≠ 0 at hz
        exact (hz rfl).elim), hzero, Set.empty_union]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hz, -⟩
      exact hz
    · intro hz
      subst z
      exact ⟨rfl, hvX⟩
  have hW₁bit : ∀ k, k < n → W₁ k ≤ 1 := by
    intro k hk
    by_cases hkv : k = (v : ℕ)
    · simpa [W₁, hkv] using hXbit (v : ℕ) hvn
    · simp [W₁, hkv]
  have henv₁ : BatchEnv cap nt j O T U Gam v sigma₁ :=
    batchEnv_run henv hr₁
      (fun _ hy => by simp only [Com.wvars] at hy; exact absurd hy (by simp))
      (fun b hb => Or.inl (by
        simp only [Com.warrs] at hb
        exact List.eq_of_mem_singleton hb))
  have hcache₁ : CachedRounds cap G j M sigma₁ :=
    cachedRounds_batch_run hcache hr₁
      (fun _ hy => by simp only [Com.wvars] at hy; exact absurd hy (by simp))
      (fun b hb => by
        simp only [Com.warrs] at hb
        exact List.eq_of_mem_singleton hb)
  have hclu₁ : sigma₁.arrs (cluName j) = arrOf n Xa := by
    rw [hsigma₁, arrs_setArr, if_neg (by
      simp [cluName, batName, String.ext_iff])]
    exact hclu
  have hmk₁ : StreamBatchMark cap j G U Gam v (markSet n Xa) 0 sigma₁ := by
    refine ⟨W₁, hbat₁, hW₁bit, ?_, ?_, ?_, fun a ha => absurd ha (by omega)⟩
    · rw [hW₁set]
      intro z hz
      subst z
      exact hvX
    · rw [hW₁set]
      exact Set.mem_singleton v
    · rw [hW₁set, Set.ncard_singleton]
      omega
  obtain ⟨sigma₂, hr₂, henv₂, hcache₂, hclu₂,
      Wa, hbat₂, hbit₂, hsub₂, hvW, hcard, hwalk⟩ :=
    (streamBatchCachedFold_spec hB hMv hXbit j 0 (by omega)).run
      (σ := sigma₁) ⟨henv₁, hcache₁, hclu₁, hmk₁⟩
  rw [Nat.zero_add] at hcard hwalk
  have hfold :
      (foldRange (fun b => streamMarkParentsCom cap j (0 + b)) j) =
        foldRange (fun a => streamMarkParentsCom cap j a) j := by
    congr 1
    funext b
    congr 1
    omega
  rw [hfold] at hr₂
  have hrun : Run B (streamBatchCachedCom cap j) sigma sigma₂
      (4 + (streamMarkParentsK cap * j + 1)) := hr₁.seq hr₂
  refine ⟨sigma₂, _, hrun, ?_, henv₂, hcache₂, hclu₂, Wa,
    hbat₂, ?_, hsub₂, hvW, hcard, hwalk, ?_⟩
  · simp only [streamBatchCachedCost]
    omega
  · intro k hk
    exact lt_of_le_of_lt (hbit₂ k hk) h1B
  · exact blockSupported_of_markSet_subset hsub₂ hXsup

/-! ## Child and retained-game masks on the same row -/

/-- In one sparse pass, retain the current game in the cluster and remove the
current batch.  Combining the two arithmetic operations is important here:
an in-place second sparse pass would otherwise need the intermediate mask to
be zero away from the row before its first execution. -/
def streamBlockAndSubCom (idx a b cut dst : String) : Com :=
  streamBlockMapCom idx dst
    (.mul (.mul (.get a (.var "cw")) (.get b (.var "cw")))
      (.sub (.lit 1) (.get cut (.var "cw"))))

def streamBlockAndSubCost (tail : ℕ) : ℕ := 23 * tail + 8

/-- Exact whole-carrier adapter for the fused conjunction/subtraction map.
As with the other streamed maps, `na` is only the resident allocation width;
all executed addresses lie in `idx[0..tail)`. -/
theorem streamBlockAndSubCom_supported_spec
    {B n na tail : ℕ} {idx a b cut dst : String}
    {Idx A C D g₀ : ℕ → ℕ}
    (h1B : 1 < B) (hnB : n < B) (htail : tail ≤ n) (hfit : tail ≤ na)
    (hIdx : ∀ q, q < tail → Idx q < n)
    (hAB : ∀ v, v < n → A v < B) (hCB : ∀ v, v < n → C v < B)
    (hDB : ∀ v, v < n → D v < B)
    (hACB : ∀ q, q < tail → A (Idx q) * C (Idx q) < B)
    (hACDB : ∀ q, q < tail →
      A (Idx q) * C (Idx q) * (1 - D (Idx q)) < B)
    (hdi : dst ≠ idx) (hda : dst ≠ a) (hdb : dst ≠ b)
    (hdc : dst ≠ cut) :
    Spec B
      (fun sigma => sigma.vars "tail" = tail ∧ sigma.arrs idx = arrOf na Idx ∧
        sigma.arrs dst = arrOf n g₀ ∧
        (sigma.arrs a = arrOf n A ∧ sigma.arrs b = arrOf n C ∧
          sigma.arrs cut = arrOf n D) ∧
        BlockSupported n 0 tail Idx
          (fun v => A v * C v * (1 - D v)) ∧
        BlockSupported n 0 tail Idx g₀)
      (streamBlockAndSubCom idx a b cut dst)
      (fun _ sigma' =>
        (∃ g, sigma'.arrs dst = arrOf n g ∧
          (∀ v, v < n → g v = A v * C v * (1 - D v)) ∧
          BlockSupported n 0 tail Idx g) ∧
        sigma'.vars "tail" = tail ∧ sigma'.arrs idx = arrOf na Idx ∧
        sigma'.arrs a = arrOf n A ∧ sigma'.arrs b = arrOf n C ∧
        sigma'.arrs cut = arrOf n D)
      (streamBlockAndSubCost tail) := by
  have h := streamBlockMapCom_supported_spec (B := B) (n := n) (na := na)
    (tail := tail) (idx := idx) (dst := dst)
    (x := .mul (.mul (.get a (.var "cw")) (.get b (.var "cw")))
      (.sub (.lit 1) (.get cut (.var "cw"))))
    (Idx := Idx) (F := fun v => A v * C v * (1 - D v)) (g₀ := g₀)
    (l := [(a, n, A), (b, n, C), (cut, n, D)]) h1B hnB htail hfit hIdx hdi
    (by
      rintro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl
      · exact Ne.symm hda
      · exact Ne.symm hdb
      · exact Ne.symm hdc)
    (by
      intro sigma q hq _ hcw hI
      obtain ⟨-, -, -, -, hfr, -⟩ := hI
      have ha := hfr (a, n, A) (by simp)
      have hb := hfr (b, n, C) (by simp)
      have hc := hfr (cut, n, D) (by simp)
      have hqN := hIdx q hq
      have ecw : (Expr.var "cw").evalB B sigma = some (Idx q) := by
        have he := evalB_var (B := B) (x := "cw") (σ := sigma) (by
          rw [hcw]
          exact lt_trans hqN hnB)
        rwa [hcw] at he
      exact evalB_bin
        (evalB_bin
          (evalB_get ecw (by rw [ha, getElem?_arrOf A hqN]) (hAB _ hqN))
          (evalB_get ecw (by rw [hb, getElem?_arrOf C hqN]) (hCB _ hqN))
          (hACB q hq))
        (evalB_bin (evalB_lit h1B)
          (evalB_get ecw (by rw [hc, getElem?_arrOf D hqN]) (hDB _ hqN))
          (by change 1 - D (Idx q) < B; omega))
        (hACDB q hq))
  simpa [streamBlockAndSubCom, streamBlockAndSubCost, streamBlockMapCost,
    BlockLeaves.BlockFrozen, Expr.size] using h

/-- Materialise the child's mask and the next-depth game mask by two passes
over the current resident row. -/
def streamChildGameCom (j : ℕ) : Com :=
  .seq (streamBlockSubCom "xmem" (resName j) (batName j) (alvName (j + 1)))
    (streamBlockAndSubCom "xmem" (gamName j) (cluName j) (batName j)
      (gamName (j + 1)))

def streamChildGameCost (tail : ℕ) : ℕ := 43 * tail + 16

/-- The data exported immediately after the two streamed post-batch masks.
Both value clauses are carrier-wide, rather than merely equations at the row
positions; support is retained explicitly for subsequent sparse consumers. -/
structure StreamChildGameOut {n : ℕ} (B na tail j : ℕ)
    (G : SimpleGraph (Fin n))
    (Xmem M Xa Ra Wa Gm Alv Gam : ℕ → ℕ) (sigma : Env) : Prop where
  tail_var : sigma.vars "tail" = tail
  row_arr : sigma.arrs "xmem" = arrOf na Xmem
  retained_arr : sigma.arrs (resName j) = arrOf n Ra
  cluster_arr : sigma.arrs (cluName j) = arrOf n Xa
  batch_arr : sigma.arrs (batName j) = arrOf n Wa
  batch_supported : BlockSupported n 0 tail Xmem Wa
  parent_game_arr : sigma.arrs (gamName j) = arrOf n Gm
  child_arr : sigma.arrs (alvName (j + 1)) = arrOf n Alv
  child_val : ∀ v, v < n → Alv v = Ra v * (1 - Wa v)
  child_bound : ∀ v, v < n → Alv v < B
  child_supported : BlockSupported n 0 tail Xmem Alv
  child_graph : masked G Alv =
    Lax12.UniformQuasiWideness.deleteVerts
      (Lax12.UniformQuasiWideness.deleteVerts (masked G M) (markSet n Xa)ᶜ)
      (markSet n Wa)
  child_point : ∀ v : Fin n, Alv (v : ℕ) ≠ 0 ↔
    (M (v : ℕ) ≠ 0 ∧ v ∈ markSet n Xa ∧ v ∉ markSet n Wa)
  game_arr : sigma.arrs (gamName (j + 1)) = arrOf n Gam
  game_val : ∀ v, v < n → Gam v = Gm v * Xa v * (1 - Wa v)
  game_bound : ∀ v, v < n → Gam v < B
  game_supported : BlockSupported n 0 tail Xmem Gam
  game_graph : masked G Gam =
    Lax12.UniformQuasiWideness.deleteVerts
      (Lax12.UniformQuasiWideness.deleteVerts (masked G Gm) (markSet n Xa)ᶜ)
      (markSet n Wa)

/-- Exact post-batch masks in `43·tail+16` steps.  The retained-value premise
is precisely the carrier equation exported by `streamRetainStep`; no equality
between the resident allocation `na` and the carrier `n` is used. -/
theorem streamChildGameCom_spec
    {B n na tail j : ℕ} {G : SimpleGraph (Fin n)}
    {Xmem M Xa Ra Wa Gm : ℕ → ℕ}
    (h1B : 1 < B) (hnB : n < B) (htail : tail ≤ n) (hfit : tail ≤ na)
    (hIdx : ∀ q, q < tail → Xmem q < n)
    (hRaval : ∀ v, v < n → Ra v = M v * Xa v)
    (hRaB : ∀ v, v < n → Ra v < B)
    (hXbit : ∀ v, v < n → Xa v ≤ 1)
    (hWaB : ∀ v, v < n → Wa v < B)
    (hGmB : ∀ v, v < n → Gm v < B)
    (hRaSup : BlockSupported n 0 tail Xmem Ra)
    (hXaSup : BlockSupported n 0 tail Xmem Xa)
    (hWaSup : BlockSupported n 0 tail Xmem Wa) :
    Spec B
      (fun sigma => sigma.vars "tail" = tail ∧
        sigma.arrs "xmem" = arrOf na Xmem ∧
        sigma.arrs (resName j) = arrOf n Ra ∧
        sigma.arrs (cluName j) = arrOf n Xa ∧
        sigma.arrs (batName j) = arrOf n Wa ∧
        sigma.arrs (gamName j) = arrOf n Gm ∧
        sigma.arrs (alvName (j + 1)) = arrOf n (fun _ => 0) ∧
        sigma.arrs (gamName (j + 1)) = arrOf n (fun _ => 0))
      (streamChildGameCom j)
      (fun _ sigma' => ∃ Alv Gam,
        StreamChildGameOut B na tail j G Xmem M Xa Ra Wa Gm Alv Gam sigma')
      (streamChildGameCost tail) := by
  have hXaB : ∀ v, v < n → Xa v < B := by
    intro v hv
    exact lt_of_le_of_lt (hXbit v hv) h1B
  have hchildB : ∀ q, q < tail →
      Ra (Xmem q) * (1 - Wa (Xmem q)) < B := by
    intro q hq
    have hqN := hIdx q hq
    calc
      Ra (Xmem q) * (1 - Wa (Xmem q)) ≤ Ra (Xmem q) * 1 :=
        Nat.mul_le_mul_left _ (by omega)
      _ = Ra (Xmem q) := by ring
      _ < B := hRaB _ hqN
  have hGX : ∀ q, q < tail → Gm (Xmem q) * Xa (Xmem q) < B := by
    intro q hq
    have hqN := hIdx q hq
    calc
      Gm (Xmem q) * Xa (Xmem q) ≤ Gm (Xmem q) * 1 :=
        Nat.mul_le_mul_left _ (hXbit _ hqN)
      _ = Gm (Xmem q) := by ring
      _ < B := hGmB _ hqN
  have hgameB : ∀ q, q < tail →
      Gm (Xmem q) * Xa (Xmem q) * (1 - Wa (Xmem q)) < B := by
    intro q hq
    calc
      Gm (Xmem q) * Xa (Xmem q) * (1 - Wa (Xmem q)) ≤
          Gm (Xmem q) * Xa (Xmem q) * 1 :=
        Nat.mul_le_mul_left _ (by omega)
      _ = Gm (Xmem q) * Xa (Xmem q) := by ring
      _ < B := hGX q hq
  have hchildSup : BlockSupported n 0 tail Xmem
      (fun v => Ra v * (1 - Wa v)) := blockSupported_sub_left hRaSup
  have hgameSup : BlockSupported n 0 tail Xmem
      (fun v => Gm v * Xa v * (1 - Wa v)) :=
    blockSupported_sub_left (blockSupported_mul_right hXaSup)
  refine Spec.of_exists fun sigma hsigma => ?_
  obtain ⟨htailVar, hrow, hres, hclu, hbat, hgam, halv₀, hgam₀⟩ := hsigma
  obtain ⟨sigma₁, hr₁,
      ⟨⟨Alv, halv₁, hAlvval, hAlvsup⟩, htail₁, hrow₁, hres₁, hbat₁⟩,
      -, hfa₁, -, -⟩ :=
    ((streamBlockSubCom_supported_spec (B := B) (n := n) (na := na)
      (tail := tail) (idx := "xmem") (a := resName j) (b := batName j)
      (dst := alvName (j + 1)) (Idx := Xmem) (A := Ra) (C := Wa)
      (g₀ := fun _ => 0) h1B hnB htail hfit hIdx hRaB hWaB hchildB
      (by simp [alvName, String.ext_iff])
      (by simp [alvName, resName, String.ext_iff])
      (by simp [alvName, batName, String.ext_iff])).frame).run
      ⟨htailVar, hrow, halv₀, ⟨hres, hbat⟩, hchildSup,
        blockSupported_zero n 0 tail Xmem⟩
  have hclu₁ : sigma₁.arrs (cluName j) = arrOf n Xa := by
    rw [hfa₁ _ (by
      simp [streamBlockSubCom, streamBlockMapCom,
        BlockLeaves.blockMapRangeCom, Com.warrs, cluName, alvName,
        String.ext_iff])]
    exact hclu
  have hgam₁ : sigma₁.arrs (gamName j) = arrOf n Gm := by
    rw [hfa₁ _ (by
      simp [streamBlockSubCom, streamBlockMapCom,
        BlockLeaves.blockMapRangeCom, Com.warrs, gamName, alvName,
        String.ext_iff])]
    exact hgam
  have hgam₀₁ : sigma₁.arrs (gamName (j + 1)) = arrOf n (fun _ => 0) := by
    rw [hfa₁ _ (by
      simp [streamBlockSubCom, streamBlockMapCom,
        BlockLeaves.blockMapRangeCom, Com.warrs, gamName, alvName,
        String.ext_iff])]
    exact hgam₀
  obtain ⟨sigma₂, hr₂,
      ⟨⟨Gam, hgam₂, hGamval, hGamsup⟩, htail₂, hrow₂,
        hgamParent₂, hclu₂, hbat₂⟩, -, hfa₂, -, -⟩ :=
    ((streamBlockAndSubCom_supported_spec (B := B) (n := n) (na := na)
      (tail := tail) (idx := "xmem") (a := gamName j) (b := cluName j)
      (cut := batName j) (dst := gamName (j + 1))
      (Idx := Xmem) (A := Gm) (C := Xa) (D := Wa) (g₀ := fun _ => 0)
      h1B hnB htail hfit hIdx hGmB hXaB hWaB hGX hgameB
      (by simp [gamName, String.ext_iff])
      (Ne.symm (gamName_ne_succ (le_refl j)))
      (by simp [gamName, cluName, String.ext_iff])
      (by simp [gamName, batName, String.ext_iff])).frame).run
      ⟨htail₁, hrow₁, hgam₀₁, ⟨hgam₁, hclu₁, hbat₁⟩,
        hgameSup, blockSupported_zero n 0 tail Xmem⟩
  have halv₂ : sigma₂.arrs (alvName (j + 1)) = arrOf n Alv := by
    rw [hfa₂ _ (by
      simp [streamBlockAndSubCom, streamBlockMapCom,
        BlockLeaves.blockMapRangeCom, Com.warrs, alvName, gamName,
        String.ext_iff])]
    exact halv₁
  have hres₂ : sigma₂.arrs (resName j) = arrOf n Ra := by
    rw [hfa₂ _ (by
      simp [streamBlockAndSubCom, streamBlockMapCom,
        BlockLeaves.blockMapRangeCom, Com.warrs, resName, gamName,
        String.ext_iff])]
    exact hres₁
  have hAlvB : ∀ v, v < n → Alv v < B := by
    intro v hv
    rw [hAlvval v hv]
    calc
      Ra v * (1 - Wa v) ≤ Ra v * 1 := Nat.mul_le_mul_left _ (by omega)
      _ = Ra v := by ring
      _ < B := hRaB v hv
  have hGamB : ∀ v, v < n → Gam v < B := by
    intro v hv
    rw [hGamval v hv]
    calc
      Gm v * Xa v * (1 - Wa v) ≤ Gm v * Xa v * 1 :=
        Nat.mul_le_mul_left _ (by omega)
      _ = Gm v * Xa v := by ring
      _ ≤ Gm v * 1 := Nat.mul_le_mul_left _ (hXbit v hv)
      _ = Gm v := by ring
      _ < B := hGmB v hv
  have hAlvEq : masked G Alv =
      Lax12.UniformQuasiWideness.deleteVerts
        (Lax12.UniformQuasiWideness.deleteVerts (masked G M) (markSet n Xa)ᶜ)
        (markSet n Wa) := by
    rw [masked_congr (M := Alv)
      (M' := fun a => M a * Xa a * (1 - Wa a))
      (fun v hv => by rw [hAlvval v hv, hRaval v hv])]
    exact masked_step M Xa Wa (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have hAlvPt : ∀ v : Fin n, Alv (v : ℕ) ≠ 0 ↔
      (M (v : ℕ) ≠ 0 ∧ v ∈ markSet n Xa ∧ v ∉ markSet n Wa) := by
    intro v
    rw [hAlvval (v : ℕ) v.isLt, hRaval (v : ℕ) v.isLt,
      mask_cell_ne_zero M Xa Wa (v : ℕ)]
    constructor
    · rintro ⟨hM, hX, hW⟩
      exact ⟨hM, hX, fun hc => hc hW⟩
    · rintro ⟨hM, hX, hW⟩
      exact ⟨hM, hX, by by_contra hc; exact hW hc⟩
  have hGamEq : masked G Gam =
      Lax12.UniformQuasiWideness.deleteVerts
        (Lax12.UniformQuasiWideness.deleteVerts (masked G Gm) (markSet n Xa)ᶜ)
        (markSet n Wa) := by
    rw [masked_congr (M := Gam)
      (M' := fun a => Gm a * Xa a * (1 - Wa a)) hGamval]
    exact masked_step Gm Xa Wa (fun _ => Iff.rfl) (fun _ => Iff.rfl)
  have hrun : Run B (streamChildGameCom j) sigma sigma₂
      (streamBlockSubCost tail + streamBlockAndSubCost tail) := hr₁.seq hr₂
  refine ⟨sigma₂, _, hrun, ?_, Alv, Gam, htail₂, hrow₂, hres₂,
    hclu₂, hbat₂, hWaSup, hgamParent₂, halv₂, hAlvval, hAlvB, hAlvsup,
    hAlvEq, hAlvPt, hgam₂, hGamval, hGamB, hGamsup, hGamEq⟩
  simp only [streamChildGameCost, streamBlockSubCost, streamBlockAndSubCost]
  omega

/-- Driver-facing splice from the preceding retained-mask leaf.  This theorem
consumes `StreamRetainOut` directly, so the row bounds, exact retained value,
and both support facts needed by the sparse maps cannot be replaced by an
implicit `na = n` assumption at composition time. -/
theorem streamChildGameStep
    {B n ns nt na q cap j c tail bits : ℕ}
    {G : SimpleGraph (Fin n)} {A₀ O T centre Xmem asg M Xa Mm Ra Wa Gm : ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} (h1B : 1 < B) (hnB : n < B)
    (hWaB : ∀ v, v < n → Wa v < B) (hGmB : ∀ v, v < n → Gm v < B)
    (hWaSup : BlockSupported n 0 tail Xmem Wa) :
    Spec B
      (fun sigma =>
        StreamRetainOut B ns nt na q cap j c tail bits G A₀ π centre O T
          Xmem asg M Xa Mm Ra sigma ∧
        sigma.arrs (batName j) = arrOf n Wa ∧
        sigma.arrs (gamName j) = arrOf n Gm ∧
        sigma.arrs (alvName (j + 1)) = arrOf n (fun _ => 0) ∧
        sigma.arrs (gamName (j + 1)) = arrOf n (fun _ => 0))
      (streamChildGameCom j)
      (fun _ sigma' => ∃ Alv Gam,
        StreamChildGameOut B na tail j G Xmem M Xa Ra Wa Gm Alv Gam sigma')
      (streamChildGameCost tail) := by
  refine Spec.of_exists fun sigma hsigma => ?_
  obtain ⟨hret, hbat, hgam, halv, hgam'⟩ := hsigma
  obtain ⟨sigma', hr, hout⟩ :=
    (streamChildGameCom_spec (G := G) h1B hnB hret.loaded.sorted.row.tail_le
      (hret.loaded.sorted.row.tail_le.trans hret.loaded.sorted.row_fit)
      hret.loaded.sorted.row.mem_lt hret.retained_val hret.retained_bound
      hret.loaded.cluster_bit hWaB hGmB hret.retained_supported
      (Lax3Proofs.Refine.CoverActiveStreamMask.StreamLoadOut.cluster_supported
        hret.loaded) hWaSup).run
      ⟨hret.loaded.sorted.tail_var, hret.loaded.sorted.row_arr,
        hret.retained_arr, hret.loaded.cluster_arr, hbat, hgam, halv, hgam'⟩
  exact ⟨sigma', streamChildGameCost tail, hr, le_rfl, hout⟩

/-! ## Reusable batch-array lifecycle -/

/-- Release precisely the row cells occupied by a completed streamed batch.
The batch's support premise upgrades that prefix clear to an exact zero array,
ready for the next cluster. -/
def streamBatchReleaseCom (j : ℕ) : Com :=
  streamBlockClearCom "xmem" (batName j)

def streamBatchReleaseCost (tail : ℕ) : ℕ := 14 * tail + 8

/-- The open-batch and post-mask phases together charge one fixed cached
parent walk per earlier round plus two passes over the actual row. -/
def streamBatchMasksCost (cap j tail : ℕ) : ℕ :=
  streamBatchCachedCost cap j + streamChildGameCost tail

theorem streamBatchMasksCost_eq (cap j tail : ℕ) :
    streamBatchMasksCost cap j tail =
      (36 * cap + 32) * j + 43 * tail + 21 := by
  simp [streamBatchMasksCost, streamBatchCachedCost, streamMarkParentsK,
    streamChildGameCost]
  ring

/-- Including the row-local release that restores the zero precondition for
the next cluster still has no carrier-width term. -/
def streamBatchLifecycleCost (cap j tail : ℕ) : ℕ :=
  streamBatchMasksCost cap j tail + streamBatchReleaseCost tail

theorem streamBatchLifecycleCost_eq (cap j tail : ℕ) :
    streamBatchLifecycleCost cap j tail =
      (36 * cap + 32) * j + 57 * tail + 29 := by
  simp [streamBatchLifecycleCost, streamBatchMasksCost_eq,
    streamBatchReleaseCost]
  ring

theorem streamBatchReleaseCom_spec
    {B n na tail j : ℕ} {Xmem Wa : ℕ → ℕ}
    (h1B : 1 < B) (hnB : n < B) (htail : tail ≤ n) (hfit : tail ≤ na)
    (hIdx : ∀ q, q < tail → Xmem q < n)
    (hWaSup : BlockSupported n 0 tail Xmem Wa) :
    Spec B
      (fun sigma => sigma.vars "tail" = tail ∧
        sigma.arrs "xmem" = arrOf na Xmem ∧
        sigma.arrs (batName j) = arrOf n Wa)
      (streamBatchReleaseCom j)
      (fun _ sigma' => sigma'.vars "tail" = tail ∧
        sigma'.arrs "xmem" = arrOf na Xmem ∧
        sigma'.arrs (batName j) = arrOf n (fun _ => 0))
      (streamBatchReleaseCost tail) := by
  have h := streamBlockClearCom_supported_spec (B := B) (n := n) (na := na)
    (tail := tail) (idx := "xmem") (dst := batName j)
    (Idx := Xmem) (g₀ := Wa) h1B hnB htail hfit hIdx
    (by simp [batName, String.ext_iff])
  refine h.pre ?_ |>.post ?_
  · rintro sigma ⟨ht, hx, hw⟩
    exact ⟨ht, hx, hw, hWaSup⟩
  · rintro _ sigma' - ⟨⟨W', hw', hzero, -⟩, ht, hx⟩
    refine ⟨ht, hx, ?_⟩
    rw [hw']
    apply arrOf_congr
    intro v hv
    exact hzero v hv

theorem noWrite_streamBlockAndSubCom (idx a b cut dst : String) :
    (streamBlockAndSubCom idx a b cut dst).NoWrite :=
  noWrite_streamBlockMapCom _ _ _

#print axioms streamMarkParentsCom_spec
#print axioms streamBatchCachedCom_spec
#print axioms streamBlockAndSubCom_supported_spec
#print axioms streamChildGameCom_spec
#print axioms streamChildGameStep
#print axioms streamBatchReleaseCom_spec

end Lax3Proofs.Refine.CoverActiveStreamBatch
