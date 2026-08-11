import Lax3Proofs.Refine.CoverActiveBudget
import Lax3Proofs.RamDriverCompose

/-!
# The active-cover phase at the recursive-driver interface

This module composes the direct active-cover core with identity-prefix
compaction.  The only level scratch array the core changes is `elm`; the
core restores it to zero, so the level frame is recovered semantically at
the phase boundary.
-/

namespace Lax3Proofs.Refine.CoverActiveDriver

open Lax3.ColoredGraphs
open Lax12.ColoringNumbers (wreach)
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamCoverActive
open Lax3Proofs.RamCoverActiveMass
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCompose
open Lax3Proofs.RamDriverMember
open Lax3Proofs.Refine.CoverActiveBudget
open Lax3Proofs.Refine.CoverActiveCompact
open Lax3Proofs.Refine.CoverActiveCore
open Lax3Proofs.Refine.CoverActiveInit
open Lax3Proofs.Refine.CoverActiveLoop
open Lax3Proofs.Refine.ScatterBlock
open Lax3Proofs.Refine.MassWeight (arenaWeight)
open Lax13Proofs.Imp Lax13Proofs.Reasoning

/-- Active cover construction followed by its active-prefix compaction. -/
def activeCoverPhase (j r : ℕ) : Com :=
  .seq (activeCoreAtCom j r) (activeCompactCom j)

theorem warrs_activeCoverPhase (j r : ℕ) : (activeCoverPhase j r).warrs =
    [xofName j, "elm", "dist", asgName j, "dist", "q", "dist", "q", "qd",
      "dist", "dist", xmmName j, asgName j, "elm", xofName j, "q", "q",
      xmmName j, cpsName j] := by
  rfl

theorem wvars_activeCoverPhase_eraseDups (j r : ℕ) :
    (activeCoverPhase j r).wvars.eraseDups =
      ["qn", "xp", "aci", "acs", "acv", "c", "src", "tail", "head", "sc",
        "v", "dv", "dn", "j", "jend", "w", "ri", "u", "du", "cvk", "cvu",
        "cvd", "rsbits", "rspow", "rsc", "rslo", "rsnext", "rsn", "rsb",
        "rsw", "rsi", "rsv", "rsd", "i", xpName j, cnumName j] := by
  rfl

theorem n_notMem_activeCoverPhase (j r : ℕ) :
    "n" ∉ (activeCoverPhase j r).wvars := by
  rw [← List.mem_eraseDups]
  rw [wvars_activeCoverPhase_eraseDups]
  simp [xpName, cnumName, String.ext_iff]

theorem m_notMem_activeCoverPhase (j r : ℕ) :
    "m" ∉ (activeCoverPhase j r).wvars := by
  rw [← List.mem_eraseDups, wvars_activeCoverPhase_eraseDups]
  simp [xpName, cnumName, String.ext_iff]

theorem lw_notMem_activeCoverPhase (j r : ℕ) :
    "lw" ∉ (activeCoverPhase j r).wvars := by
  rw [← List.mem_eraseDups, wvars_activeCoverPhase_eraseDups]
  simp [xpName, cnumName, String.ext_iff]

theorem mnumName_notMem_activeCoverPhase (j r : ℕ) :
    mnumName j ∉ (activeCoverPhase j r).wvars := by
  rw [← List.mem_eraseDups, wvars_activeCoverPhase_eraseDups]
  simp [mnumName, xpName, cnumName, String.ext_iff]

theorem ctrName_notMem_activeCoverPhase (j r a : ℕ) :
    ctrName a ∉ (activeCoverPhase j r).wvars := by
  rw [← List.mem_eraseDups, wvars_activeCoverPhase_eraseDups]
  simp [ctrName, xpName, cnumName, String.ext_iff]

theorem off_notMem_activeCoverPhase (j r : ℕ) :
    "off" ∉ (activeCoverPhase j r).warrs := by
  rw [warrs_activeCoverPhase]
  simp [xofName, xmmName, asgName, cpsName, String.ext_iff]

theorem tgt_notMem_activeCoverPhase (j r : ℕ) :
    "tgt" ∉ (activeCoverPhase j r).warrs := by
  rw [warrs_activeCoverPhase]
  simp [xofName, xmmName, asgName, cpsName, String.ext_iff]

theorem alvName_notMem_activeCoverPhase (j r a : ℕ) :
    alvName a ∉ (activeCoverPhase j r).warrs := by
  rw [warrs_activeCoverPhase]
  simp [alvName, xofName, xmmName, asgName, cpsName, String.ext_iff]

theorem gamName_notMem_activeCoverPhase (j r a : ℕ) :
    gamName a ∉ (activeCoverPhase j r).warrs := by
  rw [warrs_activeCoverPhase]
  simp [gamName, xofName, xmmName, asgName, cpsName, String.ext_iff]

theorem colName_notMem_activeCoverPhase (j r a c : ℕ) :
    colName a c ∉ (activeCoverPhase j r).warrs := by
  rw [warrs_activeCoverPhase]
  simp [colName, xofName, xmmName, asgName, cpsName, String.ext_iff]

theorem memName_notMem_activeCoverPhase (j r a : ℕ) :
    memName a ∉ (activeCoverPhase j r).warrs := by
  rw [warrs_activeCoverPhase]
  simp [memName, xofName, xmmName, asgName, cpsName, String.ext_iff]

theorem resName_notMem_activeCoverPhase (j r a : ℕ) :
    resName a ∉ (activeCoverPhase j r).warrs := by
  rw [warrs_activeCoverPhase]
  simp [resName, xofName, xmmName, asgName, cpsName, String.ext_iff]

theorem parName_notMem_activeCoverPhase (j r a : ℕ) :
    parName a ∉ (activeCoverPhase j r).warrs := by
  rw [warrs_activeCoverPhase]
  simp [parName, balName, xofName, xmmName, asgName, cpsName, String.ext_iff]

theorem zero_notMem_activeCoverPhase (j r : ℕ) :
    ∀ a ∈ zeroArrs, a ≠ "elm" → a ∉ (activeCoverPhase j r).warrs := by
  rw [warrs_activeCoverPhase]
  intro a ha haelm
  simp only [zeroArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (haelm rfl).elim
  all_goals simp [xofName, xmmName, asgName, cpsName, String.ext_iff]

theorem activeCoverPhase_noWrite (j r : ℕ) :
    (activeCoverPhase j r).NoWrite := by
  exact of_decide_eq_true rfl

/-! ## The restored level frame -/

/-- `OrderMem` survives a run that may use `elm`, provided the phase
returns that array zeroed and frames the other seven zero arrays. -/
theorem orderMem_run_restoreElm {B n ns W : ℕ} {c : Com} {σ σ' : Env} {K : ℕ}
    (h : OrderMem B n ns W σ) (hr : Run B c σ σ' K)
    (helm : σ'.arrs "elm" = arrOf n (fun _ => 0))
    (hlw : "lw" ∉ c.wvars)
    (hz : ∀ a ∈ zeroArrs, a ≠ "elm" → a ∉ c.warrs) :
    OrderMem B n ns W σ' := by
  obtain ⟨hle, hlwv, hsz, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  refine ⟨hle, by rw [hr.frame_var "lw" hlw]; exact hlwv, hsz.run hr,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    run_mem_arrs_lt hr "itg" h9, run_mem_arrs_lt hr "ntg" h10⟩
  · rw [helm]
    exact eq_zero_of_mem_arrOf fun _ _ => rfl
  · rw [hr.frame_arr "bh" (hz "bh" (by simp [zeroArrs]) (by decide))]
    exact h2
  · rw [hr.frame_arr "ooff" (hz "ooff" (by simp [zeroArrs]) (by decide))]
    exact h3
  · rw [hr.frame_arr "noff" (hz "noff" (by simp [zeroArrs]) (by decide))]
    exact h4
  · rw [hr.frame_arr "stf" (hz "stf" (by simp [zeroArrs]) (by decide))]
    exact h5
  · rw [hr.frame_arr "sta" (hz "sta" (by simp [zeroArrs]) (by decide))]
    exact h6
  · rw [hr.frame_arr "std" (hz "std" (by simp [zeroArrs]) (by decide))]
    exact h7
  · rw [hr.frame_arr "ste" (hz "ste" (by simp [zeroArrs]) (by decide))]
    exact h8

/-- Variant of `levelPre_run` for a phase that borrows and restores
`elm`. -/
theorem levelPre_run_restoreElm
    {B n cap mb ns W j : ℕ} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {c : Com} {σ σ' : Env} {K : ℕ}
    (h : LevelPre B n cap mb ns W O T j M Gm C σ)
    (hr : Run B c σ σ' K)
    (helm : σ'.arrs "elm" = arrOf n (fun _ => 0))
    (hn : "n" ∉ c.wvars) (hm : "m" ∉ c.wvars) (hlw : "lw" ∉ c.wvars)
    (hoff : "off" ∉ c.warrs) (htgt : "tgt" ∉ c.warrs)
    (halv : alvName j ∉ c.warrs) (hgam : gamName j ∉ c.warrs)
    (hcol : ∀ q : ℕ, colName j q ∉ c.warrs)
    (hz : ∀ a ∈ zeroArrs, a ≠ "elm" → a ∉ c.warrs)
    (hmemA : memName j ∉ c.warrs) (hmmv : mnumName j ∉ c.wvars) :
    LevelPre B n cap mb ns W O T j M Gm C σ' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14,
    h15, Mem, mmj, hm1, hm2, hm3, hm4⟩ := h
  exact ⟨by rw [hr.frame_var "n" hn]; exact h1,
    by rw [hr.frame_arr "off" hoff]; exact h2,
    by rw [hr.frame_arr "tgt" htgt]; exact h3,
    by rw [hr.frame_arr _ halv]; exact h4,
    by rw [hr.frame_arr _ hgam]; exact h5,
    fun q hq => by rw [hr.frame_arr _ (hcol q)]; exact h6 q hq,
    h7, h8, h9, levelMem_run hr h10, h11.run hr,
    by rw [hr.frame_var "m" hm]; exact h12,
    orderMem_run_restoreElm h13 hr helm hlw hz, h14, h15,
    Mem, mmj, by rw [hr.frame_arr _ hmemA]; exact hm1,
    by rw [hr.frame_var _ hmmv]; exact hm2, hm3, hm4⟩

/-! ## Driver contract -/

/-- The direct active core and its identity-prefix compaction implement the
member-driven cover interface, at a charge linear in the current arena
weight (up to the fixed weak-reachability degree and radix width). -/
theorem activeCoverPhase_spec {n B q cap mb ns W j d : ℕ}
    {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)} {centre : ℕ → ℕ}
    (hB : WordBoundK B n d ns cap mb)
    (hcsr : Lax3Proofs.RamElim.CsrSimple G ns O T)
    (horder : ActiveOrderP G cap d M q π centre) :
    CoverImplementsA B n q cap mb ns W j G O T M Gm C π centre
      (activeCoverPhase j cap) (activeCoverCost n d (arenaWeight n G M)) := by
  intro σ hpre
  obtain ⟨hlevel, hcentre, _hcentre_lt⟩ := hpre
  have hlevel₀ := hlevel
  obtain ⟨hn, hoff, htgt, halv, hgam, hcol, hMb, hGmb, hCb, hLM, hDM,
    hm, hOM, hpad, hTB, Mem, mmj, hmem, hmm, hMemEnum, hMemB⟩ := hlevel
  have hqmm : q = mmj := horder.count_eq_memEnum hMemEnum
  have helmLen : (σ.arrs "elm").length = n :=
    hOM.2.2.1.length (p := ("elm", n)) (by simp)
  obtain ⟨elm, helm, helm0⟩ := zeroed_of_mem helmLen hOM.2.2.2.1
  have helmExact : σ.arrs "elm" = arrOf n (fun _ => 0) :=
    helm.trans (RamDriverOrder.arrOf_congr helm0)
  have hnB : n < B := hB.n_lt
  have hnsB : ns < B := hB.ns_lt
  have hnt : ns ≤ W := hOM.1
  have hqB : q < B := lt_of_le_of_lt horder.centres.count_le hnB
  have hrB : 2 * cap + 1 < B := by
    have := hB.arena
    omega
  have harenaB : n * d + n < B := by
    have := hB.arena
    omega
  have hdouble : ∀ p < n, p + p < B := by
    intro p hp
    let v : Fin n := ⟨p, hp⟩
    have hwpos : 0 < (wreach (masked G M) π (2 * cap) v).ncard :=
      (Set.ncard_pos (Set.toFinite _)).mpr
        ⟨v, RamCover.self_mem_wreach (masked G M) π (2 * cap) v⟩
    have hd : 1 ≤ d := by
      have := horder.degree v
      omega
    have hnle : n ≤ n * d := Nat.le_mul_of_pos_right n hd
    have := hB.arena
    omega
  have hcorePre : ActiveCoreAtPre B n ns W q cap j M centre O T σ := by
    change ActiveInitPre B n ns W q cap j M centre O T
      (renEnv (activeOutputSwap j) σ)
    refine
      { n_var := by simpa using hn
        count_var := by simpa [hqmm] using hmm
        centre_arr := by
          simpa [activeOutputSwap, ordName, xofName, xmmName, asgName,
            String.ext_iff] using hcentre
        ambient_arr := by
          simpa [activeOutputSwap, alvName, xofName, xmmName, asgName,
            String.ext_iff] using halv
        off_arr := by
          simpa [activeOutputSwap, xofName, xmmName, asgName,
            String.ext_iff] using hoff
        target_arr := by
          simpa [activeOutputSwap, xofName, xmmName, asgName,
            String.ext_iff] using htgt
        zero_mask := by
          simpa [activeOutputSwap, xofName, xmmName, asgName,
            String.ext_iff] using helmExact
        dist_arr := by
          simpa [activeOutputSwap, xofName, xmmName, asgName,
            String.ext_iff] using hLM.1.get (p := ("dist", n)) (by simp)
        queue_arr := by
          simpa [activeOutputSwap, xofName, xmmName, asgName,
            String.ext_iff] using hLM.1.get (p := ("q", n)) (by simp)
        qdist_arr := by
          simpa [activeOutputSwap, xofName, xmmName, asgName,
            String.ext_iff] using hLM.qdArr
        xoff_arr := by
          simpa using hDM.get j (p := (xofName j, n + 1)) (by simp)
        xmem_arr := by
          simpa using hDM.get j (p := (xmmName j, n * n)) (by simp)
        asg_arr := by
          simpa using hDM.get j (p := (asgName j, n)) (by simp)
        ambient_bound := hMb }
  obtain ⟨σ₁, rcore, hcore⟩ :=
    (activeCoreAtK_spec horder.centres hcsr.csr hnB hnsB hnt hqB hrB
      harenaB hdouble (activeBallBudget horder.centres) horder.degree
      (fun _xp _Xoff _Xmem _asg hraw hxp =>
        activeCoverCoreCost_le horder hcsr hraw hxp)).run hcorePre
  have hDM₁ : DepthMem n cap mb σ₁ := hDM.run rcore
  have hcps₁ : ∃ cps₀, σ₁.arrs (cpsName j) = arrOf n cps₀ :=
    hDM₁.get j (p := (cpsName j, n)) (by simp)
  obtain ⟨σ₂, rcompact, hn₂, hqn₂, helm₂,
      Xoff, Xmem, asg, cps, m, hheld, hcps₂, hcnum₂, hcompact⟩ :=
    (activeCompact_spec horder.centres hqB).run ⟨hcore, hcps₁⟩
  have hrRaw : Run B (activeCoverPhase j cap) σ σ₂
      (activeCoverCoreCost n d (arenaWeight n G M) + activeCompactCost q) := by
    simpa [activeCoverPhase] using rcore.seq rcompact
  have hr : Run B (activeCoverPhase j cap) σ σ₂
      (activeCoverCost n d (arenaWeight n G M)) :=
    hrRaw.mono (by
      rw [activeCoverCost]
      exact Nat.add_le_add_left (activeCompactCost_le horder.centres) _)
  refine ⟨σ₂, hr, ?_⟩
  refine ⟨levelPre_run_restoreElm hlevel₀ hr helm₂
      (n_notMem_activeCoverPhase j cap) (m_notMem_activeCoverPhase j cap)
      (lw_notMem_activeCoverPhase j cap) (off_notMem_activeCoverPhase j cap)
      (tgt_notMem_activeCoverPhase j cap) (alvName_notMem_activeCoverPhase j cap j)
      (gamName_notMem_activeCoverPhase j cap j)
      (fun c => colName_notMem_activeCoverPhase j cap j c)
      (zero_notMem_activeCoverPhase j cap)
      (memName_notMem_activeCoverPhase j cap j)
      (mnumName_notMem_activeCoverPhase j cap),
    hr.out_eq (activeCoverPhase_noWrite j cap),
    fun a => hr.frame_var _ (ctrName_notMem_activeCoverPhase j cap a),
    fun a => hr.frame_arr _ (resName_notMem_activeCoverPhase j cap a),
    fun a => hr.frame_arr _ (gamName_notMem_activeCoverPhase j cap a),
    fun a => hr.frame_arr _ (parName_notMem_activeCoverPhase j cap a),
    Xoff, Xmem, asg, cps, m, q, hheld, hcps₂, hcnum₂, hcompact⟩

/-! ## Axiom audit -/

#print axioms activeCoverPhase_noWrite
#print axioms activeCoverPhase_spec

end Lax3Proofs.Refine.CoverActiveDriver
