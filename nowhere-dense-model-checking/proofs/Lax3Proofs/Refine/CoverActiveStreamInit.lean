import Lax3Proofs.Refine.CoverActiveInit
import Lax3Proofs.Refine.CoverActiveStreamLoop

/-!
# Initialisation of the streamed active-cover loop

The historical active-cover initializer already walks only the live member
prefix.  This file transports that walk to the streamed depth-owned arrays.
In particular, the progressive mask lives in `cpsName j`, the reusable row in
`xmmName j`, and the assignment and distance arrays in `asgName j` and
`pdsName j`.  No carrier-sized clear is introduced.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamInit

open Lax3.ColoredGraphs
open Lax3.DistFO
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster
open Lax3Proofs.RamCoverActive
open Lax3Proofs.Refine.BfsBlockMask
open Lax3Proofs.Refine.CoverActiveInit
open Lax3Proofs.Refine.CoverActiveLoop
open Lax3Proofs.Refine.CoverActiveStream
open Lax3Proofs.Refine.CoverActiveStreamDepth
open Lax3Proofs.Refine.CoverActiveStreamLoop
open Lax3Proofs.Refine.CoverActiveStreamScratch
open Lax3Proofs.Refine.CoverActiveStreamTurn
open Lax3Proofs.Refine.CoverActiveNamed
open Lax3Proofs.Refine.CoverActiveTurn
open Lax3Proofs.Refine.ScatterBlock
open Lax13Proofs.Imp Lax13Proofs.Reasoning

/-! ## Transport to depth-owned storage -/

/-- Exchange the four fixed arrays used by `activeInitCom` with the
depth-owned streamed arrays.  The ordering and ambient mask already have
their final names and are therefore fixed. -/
def streamInitSwap (j : ℕ) (a : String) : String :=
  if a = "elm" then cpsName j
  else if a = cpsName j then "elm"
  else if a = "dist" then pdsName j
  else if a = pdsName j then "dist"
  else if a = "xmem" then xmmName j
  else if a = xmmName j then "xmem"
  else if a = "asg" then asgName j
  else if a = asgName j then "asg"
  else a

@[simp] theorem streamInitSwap_elm (j : ℕ) :
    streamInitSwap j "elm" = cpsName j := by
  simp [streamInitSwap]

@[simp] theorem streamInitSwap_cpsName (j : ℕ) :
    streamInitSwap j (cpsName j) = "elm" := by
  simp [streamInitSwap, cpsName, pdsName, balAltName, xmmName, asgName,
    String.ext_iff]

@[simp] theorem streamInitSwap_dist (j : ℕ) :
    streamInitSwap j "dist" = pdsName j := by
  simp [streamInitSwap, cpsName, String.ext_iff]

@[simp] theorem streamInitSwap_pdsName (j : ℕ) :
    streamInitSwap j (pdsName j) = "dist" := by
  simp [streamInitSwap, cpsName, pdsName, balAltName, xmmName, asgName,
    String.ext_iff]

@[simp] theorem streamInitSwap_xmem (j : ℕ) :
    streamInitSwap j "xmem" = xmmName j := by
  simp [streamInitSwap, cpsName, pdsName, balAltName, String.ext_iff]

@[simp] theorem streamInitSwap_xmmName (j : ℕ) :
    streamInitSwap j (xmmName j) = "xmem" := by
  simp [streamInitSwap, cpsName, pdsName, balAltName, xmmName, asgName,
    String.ext_iff]

@[simp] theorem streamInitSwap_asg (j : ℕ) :
    streamInitSwap j "asg" = asgName j := by
  simp [streamInitSwap, cpsName, pdsName, balAltName, xmmName, String.ext_iff]

@[simp] theorem streamInitSwap_asgName (j : ℕ) :
    streamInitSwap j (asgName j) = "asg" := by
  simp [streamInitSwap, cpsName, pdsName, balAltName, xmmName, asgName,
    String.ext_iff]

theorem streamInitSwap_of_ne (j : ℕ) (a : String)
    (he : a ≠ "elm") (hej : a ≠ cpsName j)
    (hd : a ≠ "dist") (hdj : a ≠ pdsName j)
    (hx : a ≠ "xmem") (hxj : a ≠ xmmName j)
    (ha : a ≠ "asg") (haj : a ≠ asgName j) :
    streamInitSwap j a = a := by
  simp [streamInitSwap, he, hej, hd, hdj, hx, hxj, ha, haj]

theorem streamInitSwap_invol (j : ℕ) :
    ∀ a, streamInitSwap j (streamInitSwap j a) = a := by
  intro a
  by_cases he : a = "elm"
  · subst a; simp
  by_cases hej : a = cpsName j
  · subst a; simp
  by_cases hd : a = "dist"
  · subst a; simp
  by_cases hdj : a = pdsName j
  · subst a; simp
  by_cases hx : a = "xmem"
  · subst a; simp
  by_cases hxj : a = xmmName j
  · subst a; simp
  by_cases ha : a = "asg"
  · subst a; simp
  by_cases haj : a = asgName j
  · subst a; simp
  rw [streamInitSwap_of_ne j a he hej hd hdj hx hxj ha haj]
  exact streamInitSwap_of_ne j a he hej hd hdj hx hxj ha haj

/-- The live-prefix initializer at the physical arrays of depth `j`. -/
def streamInitAtDepthCom (j r : ℕ) : Com :=
  renCom (streamInitSwap j) (activeInitCom j r)

/-- The transported initializer writes exactly its four current-depth
arrays.  This frame is the bridge used by the recursive driver: every table,
play record, and deeper scratch row crosses initialization unchanged. -/
theorem notMem_warrs_streamInitAtDepthCom
    {j r : ℕ} {a : String}
    (hxoff : a ≠ "xoff") (hcps : a ≠ cpsName j)
    (hpds : a ≠ pdsName j) (hasg : a ≠ asgName j) :
    a ∉ (streamInitAtDepthCom j r).warrs := by
  intro ha
  have hpull := Lax3Proofs.Refine.ScatterBlock.mem_renCom_warrs
    (streamInitSwap_invol j) (activeInitCom j r) ha
  simp [activeInitCom, activeInitTurn,
    Lax3Proofs.Refine.CoverBlock.centreLoopCom, Com.warrs] at hpull
  rcases hpull with hpull | hpull | hpull | hpull
  · have heq := congrArg (streamInitSwap j) hpull
    rw [streamInitSwap_invol j] at heq
    exact hxoff (by simpa [streamInitSwap] using heq)
  · have heq := congrArg (streamInitSwap j) hpull
    rw [streamInitSwap_invol j] at heq
    exact hcps (by simpa using heq)
  · have heq := congrArg (streamInitSwap j) hpull
    rw [streamInitSwap_invol j] at heq
    exact hpds (by simpa using heq)
  · have heq := congrArg (streamInitSwap j) hpull
    rw [streamInitSwap_invol j] at heq
    exact hasg (by simpa using heq)

/-- The initializer's scalar writes are fixed, unindexed temporaries. -/
theorem notMem_wvars_streamInitAtDepthCom
    {j r : ℕ} {x : String}
    (hqn : x ≠ "qn") (hxp : x ≠ "xp") (haci : x ≠ "aci")
    (hacs : x ≠ "acs") (hacv : x ≠ "acv") :
    x ∉ (streamInitAtDepthCom j r).wvars := by
  simpa [streamInitAtDepthCom, activeInitCom, activeInitTurn,
    Lax3Proofs.Refine.CoverBlock.centreLoopCom,
    Lax3Proofs.Refine.ScatterBlock.renCom_wvars, Com.wvars]
    using And.intro hqn
      (And.intro hxp (And.intro haci (And.intro hacs (And.intro hacv haci))))

/-- The transported initializer writes no array owned by a shallower
recursive level. -/
theorem belowArr_notMem_warrs_streamInitAtDepthCom
    {j r : ℕ} {a : String}
    (h : Lax3Proofs.RamDriverWrites.BelowArr j a) :
    a ∉ (streamInitAtDepthCom j r).warrs := by
  have hd := Lax3Proofs.RamDriverWrites.hasDigit_of_belowArr h
  apply notMem_warrs_streamInitAtDepthCom
  · exact fun hq =>
      (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit "xoff") (hq ▸ hd)
  · exact Lax3Proofs.RamDriverWrites.belowArr_ne h le_rfl (by tauto)
  · exact Lax3Proofs.RamDriverWrites.belowArr_ne h le_rfl (by tauto)
  · exact Lax3Proofs.RamDriverWrites.belowArr_ne h le_rfl (by tauto)

/-- The scalar half of the shallower-level frame for the initializer. -/
theorem belowVar_notMem_wvars_streamInitAtDepthCom
    {j r : ℕ} {x : String}
    (h : Lax3Proofs.RamDriverWrites.BelowVar j x) :
    x ∉ (streamInitAtDepthCom j r).wvars := by
  have hd := Lax3Proofs.RamDriverWrites.hasDigit_of_belowVar h
  apply notMem_wvars_streamInitAtDepthCom <;>
    intro hq <;> subst x <;>
      exact (by decide : ¬ Lax3Proofs.RamDriverWrites.HasDigit _) hd

theorem noWrite_streamInitAtDepthCom (j r : ℕ) :
    (streamInitAtDepthCom j r).NoWrite := by
  apply Lax3Proofs.Refine.ScatterBlock.renCom_noWrite
  simp [activeInitCom, activeInitTurn,
    Lax3Proofs.Refine.CoverBlock.centreLoopCom, Com.NoWrite]

/-! ## Initial streamed turn -/

structure StreamInitPre
    (B n cap mb ns nt q j bits ell : ℕ)
    (A₀ centre O T Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (σ : Env) : Prop where
  level : LevelPre B n cap mb ns nt O T j A₀ Gm C σ
  count_var : σ.vars (mnumName j) = q
  centre_arr : σ.arrs (ordName j) = arrOf n centre
  mask_zero : σ.arrs (cpsName j) = arrOf n (fun _ => 0)
  bits_var : σ.vars "rsbits" = bits

private theorem levelMem_renEnv_streamDepthSwap
    {B n cap mb j : ℕ} {σ : Env}
    (hl : LevelMem B n cap mb σ) (hd : DepthMem n cap mb σ)
    (hpds : ∀ v ∈ σ.arrs (pdsName j), v < B) :
    LevelMem B n cap mb (renEnv (streamDepthSwap j) σ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
    · simpa only [renEnv_arrs, streamDepthSwap_alv] using
        hd.get j (p := (cpsName j, n)) (by simp)
    · simpa [renEnv_arrs, streamDepthSwap, ordName, cpsName, xmmName,
        asgName, pdsName, balAltName, String.ext_iff] using
        hl.1.get (p := ("tab", n)) (by simp)
    · simpa only [renEnv_arrs, streamDepthSwap_dist] using
        hd.get j (p := (pdsName j, n)) (by simp [pdsName])
    · simpa [renEnv_arrs, streamDepthSwap, ordName, cpsName, xmmName,
        asgName, pdsName, balAltName, String.ext_iff] using
        hl.1.get (p := ("q", n)) (by simp)
    · simpa [renEnv_arrs, streamDepthSwap, ordName, cpsName, xmmName,
        asgName, pdsName, balAltName, String.ext_iff] using
        hl.1.get (p := ("exc", n)) (by simp)
    · simpa only [renEnv_arrs, streamDepthSwap_asg] using
        hd.get j (p := (asgName j, n)) (by simp)
    · simpa only [renEnv_arrs, streamDepthSwap_ord] using
        hd.get j (p := (ordName j, n)) (by simp)
    · simpa [renEnv_arrs, streamDepthSwap, ordName, cpsName, xmmName,
        asgName, pdsName, balAltName, String.ext_iff] using
        hl.1.get (p := ("xoff", n + 1)) (by simp)
    · simpa only [renEnv_arrs, streamDepthSwap_xmem] using
        hd.get j (p := (xmmName j, n * n)) (by simp)
    · simpa [renEnv_arrs, streamDepthSwap, ordName, cpsName, xmmName,
        asgName, pdsName, balAltName, String.ext_iff] using
        hl.1.get (p := ("par", n)) (by simp)
    · simpa [renEnv_arrs, streamDepthSwap, ordName, cpsName, xmmName,
        asgName, pdsName, balAltName, String.ext_iff] using
        hl.1.get (p := ("path", 2 * cap + 1)) (by simp)
    · simpa [renEnv_arrs, streamDepthSwap, ordName, cpsName, xmmName,
        asgName, pdsName, balAltName, String.ext_iff] using
        hl.1.get (p := ("wa", mb)) (by simp)
    · simpa [renEnv_arrs, streamDepthSwap, ordName, cpsName, xmmName,
        asgName, pdsName, balAltName, String.ext_iff] using
        hl.1.get (p := ("mem", n)) (by simp)
    · simpa [renEnv_arrs, streamDepthSwap, ordName, cpsName, xmmName,
        asgName, pdsName, balAltName, String.ext_iff] using
        hl.1.get (p := ("qd", n)) (by simp)
  · simpa only [renEnv_arrs, streamDepthSwap_dist] using hpds
  · simpa [renEnv_arrs, streamDepthSwap, ordName, cpsName, xmmName,
      asgName, pdsName, balAltName, String.ext_iff] using hl.2.2

private theorem depthMem_renEnv_streamDepthSwap
    {B n cap mb j : ℕ} {σ : Env}
    (hl : LevelMem B n cap mb σ) (hd : DepthMem n cap mb σ) :
    DepthMem n cap mb (renEnv (streamDepthSwap j) σ) := by
  intro d
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl
    · simpa only [renEnv_arrs, streamDepthSwap_alvName] using
        hd.get d (p := (alvName d, n)) (by simp)
    · simpa only [renEnv_arrs, streamDepthSwap_gamName] using
        hd.get d (p := (gamName d, n)) (by simp)
    · simpa only [renEnv_arrs, streamDepthSwap_cluName] using
        hd.get d (p := (cluName d, n)) (by simp)
    · simpa only [renEnv_arrs, streamDepthSwap_resName] using
        hd.get d (p := (resName d, n)) (by simp)
    · simpa [renEnv_arrs, streamDepthSwap, balName, ordName, cpsName,
        xmmName, asgName, pdsName, balAltName, String.ext_iff] using
        hd.get d (p := (balName d, n)) (by simp)
    · by_cases hdj : d = j
      · subst d
        change ∃ g, σ.arrs (streamDepthSwap j (pdsName j)) = arrOf n g
        simpa only [streamDepthSwap_pdsName] using
          hl.1.get (p := ("dist", n)) (by simp)
      · change ∃ g, σ.arrs (streamDepthSwap j (pdsName d)) = arrOf n g
        rw [streamDepthSwap_pdsName_of_ne hdj]
        exact hd.get d (p := (pdsName d, n)) (by simp [pdsName])
    · simpa only [renEnv_arrs, streamDepthSwap_batName] using
        hd.get d (p := (batName d, n)) (by simp)
    · by_cases hdj : d = j
      · subst d
        simpa only [renEnv_arrs, streamDepthSwap_ordName] using
          hl.1.get (p := ("ord", n)) (by simp)
      · rw [renEnv_arrs, streamDepthSwap_ordName_of_ne hdj]
        exact hd.get d (p := (ordName d, n)) (by simp)
    · simpa [renEnv_arrs, streamDepthSwap, xofName, ordName, cpsName,
        xmmName, asgName, pdsName, balAltName, String.ext_iff] using
        hd.get d (p := (xofName d, n + 1)) (by simp)
    · by_cases hdj : d = j
      · subst d
        simpa only [renEnv_arrs, streamDepthSwap_xmmName] using
          hl.1.get (p := ("xmem", n * n)) (by simp)
      · rw [renEnv_arrs, streamDepthSwap_xmmName_of_ne hdj]
        exact hd.get d (p := (xmmName d, n * n)) (by simp)
    · by_cases hdj : d = j
      · subst d
        simpa only [renEnv_arrs, streamDepthSwap_asgName] using
          hl.1.get (p := ("asg", n)) (by simp)
      · rw [renEnv_arrs, streamDepthSwap_asgName_of_ne hdj]
        exact hd.get d (p := (asgName d, n)) (by simp)
    · by_cases hdj : d = j
      · subst d
        simpa only [renEnv_arrs, streamDepthSwap_cpsName] using
          hl.1.get (p := ("alv", n)) (by simp)
      · rw [renEnv_arrs, streamDepthSwap_cpsName_of_ne hdj]
        exact hd.get d (p := (cpsName d, n)) (by simp)
    · simpa only [renEnv_arrs, streamDepthSwap_memName] using
        hd.get d (p := (memName d, n)) (by simp)
    · simpa only [renEnv_arrs, streamDepthSwap_klName] using
        hd.get d (p := (klName d, mb)) (by simp)
  · intro c hc
    obtain ⟨g, hg⟩ := hd.col hc
    exact ⟨g, by simpa only [renEnv_arrs, streamDepthSwap_colName] using hg⟩

/-- A physical level and the word-valued depth-owned distance row induce the
same level interface in the pulled-back streamed view. -/
theorem levelPre_renEnv_streamDepthSwap
    {B n cap mb ns nt j : ℕ} {O T A₀ Gm : ℕ → ℕ}
    {C : ℕ → ℕ → ℕ} {σ : Env}
    (h : LevelPre B n cap mb ns nt O T j A₀ Gm C σ)
    (hpds : ∀ v ∈ σ.arrs (pdsName j), v < B) :
    LevelPre B n cap mb ns nt O T j A₀ Gm C
      (renEnv (streamDepthSwap j) σ) := by
  obtain ⟨hn, hoff, htgt, halv, hgam, hcol, hAB, hGB, hCbit, hl, hd,
    hm, ho, hpad, htB, Mem, mm, hmem, hmm, henum, hMemB⟩ := h
  refine ⟨by simpa using hn, ?_, ?_, ?_, ?_, ?_, hAB, hGB, hCbit,
    levelMem_renEnv_streamDepthSwap hl hd hpds,
    depthMem_renEnv_streamDepthSwap hl hd, by simpa using hm, ?_, hpad, htB,
    Mem, mm, ?_, by simpa using hmm, henum, hMemB⟩
  · simpa [renEnv_arrs, streamDepthSwap, ordName, cpsName, xmmName,
      asgName, pdsName, balAltName, String.ext_iff] using hoff
  · simpa [renEnv_arrs, streamDepthSwap, ordName, cpsName, xmmName,
      asgName, pdsName, balAltName, String.ext_iff] using htgt
  · simpa only [renEnv_arrs, streamDepthSwap_alvName] using halv
  · simpa only [renEnv_arrs, streamDepthSwap_gamName] using hgam
  · intro c hc
    simpa only [renEnv_arrs, streamDepthSwap_colName] using hcol c hc
  · simpa [OrderMem, Sized, renEnv_arrs, renEnv_vars, streamDepthSwap,
      ordName, cpsName, xmmName, asgName, pdsName, balAltName,
      String.ext_iff] using ho
  · simpa only [renEnv_arrs, streamDepthSwap_memName] using hmem

private theorem streamDepthSwap_of_ext_bb
    {j : ℕ} {a : String} (h : Lax3Proofs.RamDriverBot.Ext "bb" a) :
    streamDepthSwap j a = a := by
  have hfix (p : String) (hlen : 2 ≤ p.toList.length)
      (hp : ¬("bb".toList <+: p.toList)) :
      ¬Lax3Proofs.RamDriverBot.Ext "bb" p := by
    simpa using Lax3Proofs.RamDriverWrites.not_ext_bb_append hlen hp ""
  apply streamDepthSwap_of_ne
  · intro ha
    subst a
    exact hfix "ord" (by decide) (by decide) h
  · intro ha
    subst a
    rw [ordName] at h
    exact Lax3Proofs.RamDriverWrites.not_ext_bb_append
      (p := "od") (by decide) (by decide) (toString j) h
  · intro ha
    subst a
    exact hfix "alv" (by decide) (by decide) h
  · intro ha
    subst a
    rw [cpsName] at h
    exact Lax3Proofs.RamDriverWrites.not_ext_bb_append
      (p := "cs") (by decide) (by decide) (toString j) h
  · intro ha
    subst a
    exact hfix "xmem" (by decide) (by decide) h
  · intro ha
    subst a
    rw [xmmName] at h
    exact Lax3Proofs.RamDriverWrites.not_ext_bb_append
      (p := "xm") (by decide) (by decide) (toString j) h
  · intro ha
    subst a
    exact hfix "asg" (by decide) (by decide) h
  · intro ha
    subst a
    rw [asgName] at h
    exact Lax3Proofs.RamDriverWrites.not_ext_bb_append
      (p := "ag") (by decide) (by decide) (toString j) h
  · intro ha
    subst a
    exact hfix "dist" (by decide) (by decide) h
  · intro ha
    subst a
    rw [pdsName, balAltName] at h
    exact Lax3Proofs.RamDriverWrites.not_ext_bb_append
      (p := "blt") (by decide) (by decide) (toString j) h

private theorem botMem_renEnv_streamDepthSwap
    {B L k j : ℕ} {ψ : DistFO L k} {out : String} {σ : Env}
    (hout : Lax3Proofs.RamDriverBot.Ext "bb" out)
    (h : BotMem B ψ out σ) :
    BotMem B ψ out (renEnv (streamDepthSwap j) σ) := by
  induction ψ generalizing out with
  | adj => trivial
  | eq => trivial
  | color => trivial
  | distLe => trivial
  | distColorLt => trivial
  | not ψ ih =>
      exact ih (hout.trans (Lax3Proofs.RamDriverBot.ext_append out "a")) h
  | and ψ χ ihψ ihχ =>
      exact ⟨ihψ (hout.trans (Lax3Proofs.RamDriverBot.ext_append out "a")) h.1,
        ihχ (hout.trans (Lax3Proofs.RamDriverBot.ext_append out "b")) h.2⟩
  | exU => trivial
  | exL r g ψ ih =>
      refine ⟨h.1, ?_, ih (hout.trans
        (Lax3Proofs.RamDriverBot.ext_append out "a")) h.2.2⟩
      simpa only [renEnv_arrs, streamDepthSwap_of_ext_bb
        (hout.trans (Lax3Proofs.RamDriverBot.ext_append out "g"))] using h.2.1

theorem tablesSized_renEnv_streamDepthSwap
    {q_top cap mb n j : ℕ} {φ : Lax3.FirstOrder.FO 0} {σ : Env}
    (h : TablesSized q_top cap mb φ n σ) :
    TablesSized q_top cap mb φ n (renEnv (streamDepthSwap j) σ) := by
  intro d p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hp
  obtain ⟨g, hg⟩ := h d _ (List.mem_map.2 ⟨i, hi, rfl⟩)
  exact ⟨g, by simpa only [renEnv_arrs, streamDepthSwap_tabName] using hg⟩

theorem baseArrs_renEnv_streamDepthSwap
    {B q_top cap mb ell j : ℕ} {φ : Lax3.FirstOrder.FO 0} {σ : Env}
    (h : BaseArrs B q_top cap mb ell φ σ) :
    BaseArrs B q_top cap mb ell φ (renEnv (streamDepthSwap j) σ) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    simp only [List.mem_singleton] at hp
    subst p
    obtain ⟨g, hg⟩ := h.1.get (p := ("rep", 2 ^ sigL cap mb ell)) (by simp)
    exact ⟨g, by simpa [renEnv_arrs, streamDepthSwap, ordName, cpsName,
      xmmName, asgName, pdsName, balAltName, String.ext_iff] using hg⟩
  · intro d i hi
    exact botMem_renEnv_streamDepthSwap (Lax3Proofs.RamDriverBot.ext_refl "bb")
      (h.2 d i hi)

variable {B n cap mb ns nt q r j bits ell : ℕ}
variable {A₀ centre O T Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
variable {π : Equiv.Perm (Fin n)} {G : SimpleGraph (Fin n)}

private theorem init_old_pre {σ : Env}
    (hpre : StreamInitPre B n cap mb ns nt q j bits ell A₀ centre O T Gm C σ) :
    ActiveInitPre B n ns nt q r j A₀ centre O T
      (renEnv (streamInitSwap j) σ) := by
  obtain ⟨hn, hoff, htgt, halv, -, -, hAB, -, -, hLM, hDM, -⟩ := hpre.level
  refine
    { n_var := by simpa using hn
      count_var := by simpa using hpre.count_var
      centre_arr := by
        simpa [renEnv_arrs, streamInitSwap, ordName, cpsName, pdsName,
          balAltName, xmmName, asgName, String.ext_iff] using hpre.centre_arr
      ambient_arr := by
        simpa [renEnv_arrs, streamInitSwap, alvName, cpsName, pdsName,
          balAltName, xmmName, asgName, String.ext_iff] using halv
      off_arr := by
        simpa [renEnv_arrs, streamInitSwap, cpsName, pdsName, balAltName,
          xmmName, asgName, String.ext_iff] using hoff
      target_arr := by
        simpa [renEnv_arrs, streamInitSwap, cpsName, pdsName, balAltName,
          xmmName, asgName, String.ext_iff] using htgt
      zero_mask := by simpa [renEnv_arrs] using hpre.mask_zero
      dist_arr := by
        simpa [renEnv_arrs, pdsName] using
          hDM.get j (p := (balAltName j, n)) (by simp)
      queue_arr := by
        simpa [renEnv_arrs, streamInitSwap, cpsName, pdsName, balAltName,
          xmmName, asgName, String.ext_iff] using
          hLM.1.get (p := ("q", n)) (by simp)
      qdist_arr := by
        simpa [renEnv_arrs, streamInitSwap, cpsName, pdsName, balAltName,
          xmmName, asgName, String.ext_iff] using hLM.qdArr
      xoff_arr := by
        simpa [renEnv_arrs, streamInitSwap, cpsName, pdsName, balAltName,
          xmmName, asgName, String.ext_iff] using
          hLM.1.get (p := ("xoff", n + 1)) (by simp)
      xmem_arr := by
        simpa [renEnv_arrs] using hDM.get j (p := (xmmName j, n * n)) (by simp)
      asg_arr := by
        simpa [renEnv_arrs] using hDM.get j (p := (asgName j, n)) (by simp)
      ambient_bound := hAB }

private theorem n_le_square (n : ℕ) : n ≤ n * n := by
  rcases n with _ | n
  · simp
  · exact Nat.le_mul_of_pos_right _ (Nat.succ_pos _)

/-- The transported member walk establishes exactly the streamed state at
centre zero. -/
theorem streamInitTurn_spec
    (hcentres : CentresBy n q A₀ π centre)
    (hnB : n < B) (hqB : q < B) (hrB : 2 * r + 1 < B) :
    Spec B
      (StreamInitPre B n cap mb ns nt q j bits ell A₀ centre O T Gm C)
      (streamInitAtDepthCom j r)
      (fun _ σ' => ∃ Xmem asg M : ℕ → ℕ,
        StreamTurnState B ns nt (n * n) q r 0 G A₀ π centre O T
          Xmem asg M ((renEnv (streamDepthSwap j) σ').setVar "c" 0))
      (activeInitCost q) := by
  intro σ hpre
  obtain ⟨σ', hr, hraw⟩ :=
    (renCom_spec (streamInitSwap_invol j)
      (activeInit_spec (G := G) hcentres hnB hqB hrB)).run (init_old_pre hpre)
  obtain ⟨c, xp, Xoff, Xmem, asg, M, hstate⟩ := hraw
  have hc : c = 0 := by simpa using hstate.centre_var.symm
  subst c
  refine ⟨σ', ?_, Xmem, asg, M, ?_⟩
  · simpa [streamInitAtDepthCom] using hr
  refine
    { state := CoverPrefixA.of_raw hstate.raw
      n_var := by simpa [renEnv_vars] using hstate.n_var
      q_var := by simpa [renEnv_vars] using hstate.q_var
      centre_var := by simp
      centre_arr := by
        simpa [renEnv_arrs, activeCoverSwap, streamInitSwap, streamDepthSwap,
          ordName, cpsName, pdsName, balAltName, xmmName, asgName,
          String.ext_iff] using hstate.centre_arr
      off_arr := by
        simpa [renEnv_arrs, activeCoverSwap, streamInitSwap, streamDepthSwap,
          ordName, cpsName, pdsName, balAltName, xmmName, asgName,
          String.ext_iff] using hstate.off_arr
      target_arr := by
        simpa [renEnv_arrs, activeCoverSwap, streamInitSwap, streamDepthSwap,
          ordName, cpsName, pdsName, balAltName, xmmName, asgName,
          String.ext_iff] using hstate.target_arr
      mask_arr := by
        simpa [renEnv_arrs, activeCoverSwap, streamInitSwap, streamDepthSwap,
          ordName, cpsName, pdsName, balAltName, xmmName, asgName,
          String.ext_iff] using hstate.mask_arr
      row_arr := by
        simpa [renEnv_arrs, activeCoverSwap, streamInitSwap, streamDepthSwap,
          ordName, cpsName, pdsName, balAltName, xmmName, asgName,
          String.ext_iff] using hstate.xmem_arr
      row_fit := n_le_square n
      asg_arr := by
        simpa [renEnv_arrs, activeCoverSwap, streamInitSwap, streamDepthSwap,
          ordName, cpsName, pdsName, balAltName, xmmName, asgName,
          String.ext_iff] using hstate.asg_arr
      dist_clean := by
        obtain ⟨D, hD, hclean⟩ := hstate.dist_clean
        exact ⟨D, by
          simpa [renEnv_arrs, activeCoverSwap, streamInitSwap, streamDepthSwap,
            ordName, cpsName, pdsName, balAltName, xmmName, asgName,
            String.ext_iff] using hD, hclean⟩
      queue_arr := by
        obtain ⟨Q, hQ⟩ := hstate.queue_arr
        exact ⟨Q, by
          simpa [renEnv_arrs, activeCoverSwap, streamInitSwap, streamDepthSwap,
            ordName, cpsName, pdsName, balAltName, xmmName, asgName,
            String.ext_iff] using hQ⟩
      qdist_arr := by
        obtain ⟨QD, hQD⟩ := hstate.qdist_arr
        exact ⟨QD, by
          simpa [renEnv_arrs, activeCoverSwap, streamInitSwap, streamDepthSwap,
            ordName, cpsName, pdsName, balAltName, xmmName, asgName,
            String.ext_iff] using hQD⟩
      mask_bound := hstate.mask_bound }

/-! ## Stable loop entry -/

/-- Everything that crosses the live-prefix initializer into the fused centre
loop.  The current scratch head is split from the deeper suffix because the
initializer deliberately consumes its mask and distance components. -/
structure StreamInitStablePre
    (B n q_top cap mb ns nt q j bits ell : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (G : SimpleGraph (Fin n))
    (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre O T Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
    (D : Set (Fin n)) (σ : Env) : Prop where
  init : StreamInitPre B n cap mb ns nt q j bits ell A₀ centre O T Gm C σ
  tables : TablesSized q_top cap mb φ n σ
  base_arrs : BaseArrs B q_top cap mb ell φ σ
  play : PlayRec B cap G j A₀ Gm σ
  table_inv : TableInvOn q_top cap mb φ G j A₀ C D σ
  head : StreamScratchHead B n cap mb j σ
  scratch : StreamScratchFrom B n cap mb ell (j + 1) σ

open Classical in
/-- The member-priced initializer establishes the exact stable state expected
by `streamCentreLoopStep`, while framing the already-correct domain and every
deeper reusable row. -/
theorem streamInitStableStep
    {B n q_top cap mb ns nt q j bits ell : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {A₀ : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre O T Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {D : Set (Fin n)}
    (hcentres : CentresBy n q A₀ π centre)
    (hnB : n < B) (hqB : q < B) (hrB : 2 * cap + 1 < B) :
    Spec B
      (StreamInitStablePre B n q_top cap mb ns nt q j bits ell φ G A₀ π
        centre O T Gm C D)
      (streamInitAtDepthCom j cap)
      (fun σ σ' => ∃ Xmem asg M : ℕ → ℕ,
        StreamStableState B n q_top cap mb ns nt q j 0 bits ell φ G A₀ π
          centre O T Xmem asg M Gm C (σ'.setVar "c" 0) ∧
        TableInvOn q_top cap mb φ G j A₀ C D (σ'.setVar "c" 0) ∧
        σ'.out = σ.out)
      (activeInitCost q) := by
  refine Spec.of_exists fun σ hpre => ?_
  have hlogical₀ : LevelPre B n cap mb ns nt O T j A₀ Gm C
      (renEnv (streamDepthSwap j) σ) :=
    levelPre_renEnv_streamDepthSwap hpre.init.level hpre.head.dist_words
  have hlogicalTables₀ : TablesSized q_top cap mb φ n
      (renEnv (streamDepthSwap j) σ) :=
    tablesSized_renEnv_streamDepthSwap hpre.tables
  have hlogicalBase₀ : BaseArrs B q_top cap mb ell φ
      (renEnv (streamDepthSwap j) σ) :=
    baseArrs_renEnv_streamDepthSwap hpre.base_arrs
  obtain ⟨σ', hr, Xmem, asg, M, hturn⟩ :=
    (streamInitTurn_spec (G := G) hcentres hnB hqB hrB).run hpre.init
  have hlevel : LevelPre B n cap mb ns nt O T j A₀ Gm C σ' := by
    apply Lax3Proofs.RamDriverCompose.levelPre_run hpre.init.level hr
    · apply notMem_wvars_streamInitAtDepthCom <;>
        simp [mnumName, String.ext_iff]
    · apply notMem_wvars_streamInitAtDepthCom <;>
        simp [mnumName, String.ext_iff]
    · apply notMem_wvars_streamInitAtDepthCom <;>
        simp [mnumName, String.ext_iff]
    · apply notMem_warrs_streamInitAtDepthCom <;>
        simp [cpsName, pdsName, balAltName, asgName, String.ext_iff]
    · apply notMem_warrs_streamInitAtDepthCom <;>
        simp [cpsName, pdsName, balAltName, asgName, String.ext_iff]
    · apply notMem_warrs_streamInitAtDepthCom <;>
        simp [alvName, cpsName, pdsName, balAltName, asgName, String.ext_iff]
    · apply notMem_warrs_streamInitAtDepthCom <;>
        simp [gamName, cpsName, pdsName, balAltName, asgName, String.ext_iff]
    · intro s
      apply notMem_warrs_streamInitAtDepthCom <;>
        simp [colName, cpsName, pdsName, balAltName, asgName, String.ext_iff]
    · intro a ha
      simp only [Lax3Proofs.RamDriverCompose.zeroArrs, List.mem_cons,
        List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        apply notMem_warrs_streamInitAtDepthCom <;>
          simp [cpsName, pdsName, balAltName, asgName, String.ext_iff]
    · apply notMem_warrs_streamInitAtDepthCom <;>
        simp [memName, cpsName, pdsName, balAltName, asgName, String.ext_iff]
    · apply notMem_wvars_streamInitAtDepthCom <;>
        simp [mnumName, String.ext_iff]
  have hplay : PlayRec B cap G j A₀ Gm σ' := by
    apply hpre.play.congr
    · intro a ha
      exact hr.frame_var _ (by
        apply notMem_wvars_streamInitAtDepthCom <;>
          simp [ctrName, String.ext_iff])
    · intro a ha
      exact hr.frame_arr _ (by
        apply notMem_warrs_streamInitAtDepthCom <;>
          simp [resName, cpsName, pdsName, balAltName, asgName, String.ext_iff])
    · intro a ha
      exact hr.frame_arr _ (by
        apply notMem_warrs_streamInitAtDepthCom <;>
          simp [gamName, cpsName, pdsName, balAltName, asgName, String.ext_iff])
    · intro a ha
      exact hr.frame_arr _ (by
        apply notMem_warrs_streamInitAtDepthCom <;>
          simp [parName, balName, cpsName, pdsName, balAltName, asgName,
            String.ext_iff])
  have hscratch : StreamScratchFrom B n cap mb ell (j + 1) σ' := by
    apply hpre.scratch.run hr
    · intro d hd _
      apply notMem_warrs_streamInitAtDepthCom
      · simp [cpsName, String.ext_iff]
      · intro he
        exact (by omega : d ≠ j) (Lax3Proofs.RamDriverWrites.cpsName_inj he)
      · simp [cpsName, pdsName, balAltName, String.ext_iff]
      · simp [cpsName, asgName, String.ext_iff]
    · intro d hd _
      apply notMem_warrs_streamInitAtDepthCom <;>
        simp [cluName, cpsName, pdsName, balAltName, asgName, String.ext_iff]
    · intro d hd _
      apply notMem_warrs_streamInitAtDepthCom <;>
        simp [resName, cpsName, pdsName, balAltName, asgName, String.ext_iff]
    · intro d hd _
      apply notMem_warrs_streamInitAtDepthCom <;>
        simp [batName, cpsName, pdsName, balAltName, asgName, String.ext_iff]
    · intro d hd _
      apply notMem_warrs_streamInitAtDepthCom <;>
        simp [alvName, cpsName, pdsName, balAltName, asgName, String.ext_iff]
    · intro d hd _
      apply notMem_warrs_streamInitAtDepthCom <;>
        simp [gamName, cpsName, pdsName, balAltName, asgName, String.ext_iff]
    · intro d hd _ s hs
      apply notMem_warrs_streamInitAtDepthCom <;>
        simp [colName, cpsName, pdsName, balAltName, asgName, String.ext_iff]
  have htable : TableInvOn q_top cap mb φ G j A₀ C D σ' := by
    intro i hi
    obtain ⟨Tb, hTb, hbit, hval⟩ := hpre.table_inv i hi
    refine ⟨Tb, ?_, hbit, hval⟩
    rw [hr.frame_arr _ (by
      apply notMem_warrs_streamInitAtDepthCom <;>
        simp [tabName, cpsName, pdsName, balAltName, asgName, String.ext_iff])]
    exact hTb
  let σ₀ := σ'.setVar "c" 0
  have hlevel₀ : LevelPre B n cap mb ns nt O T j A₀ Gm C σ₀ := by
    exact levelPre_setVar hlevel "c" (by decide) (by decide) (by decide)
      (by simp [mnumName, String.ext_iff]) 0
  have hlogicalPost : LevelPre B n cap mb ns nt O T j A₀ Gm C
      (renEnv (streamDepthSwap j) σ') :=
    Lax3Proofs.Refine.CoverActiveStreamLoop.levelPre_renEnv_streamDepthSwap_after_run
      hlogical₀ hlevel hr
  have hlogical₀' : LevelPre B n cap mb ns nt O T j A₀ Gm C
      (renEnv (streamDepthSwap j) σ₀) := by
    have hset := levelPre_setVar hlogicalPost "c" (by decide) (by decide)
      (by decide) (by simp [mnumName, String.ext_iff]) 0
    simpa [σ₀, renEnv] using hset
  have hplay₀ : PlayRec B cap G j A₀ Gm σ₀ := by
    apply hplay.congr <;> intro a ha
    · simp [σ₀, ctrName, String.ext_iff]
    · simp [σ₀]
    · simp [σ₀]
    · simp [σ₀]
  have hscratch₀ : StreamScratchFrom B n cap mb ell (j + 1) σ₀ := by
    exact hscratch.congr (fun a => by simp [σ₀])
  have htable₀ : TableInvOn q_top cap mb φ G j A₀ C D σ₀ := by
    simpa only [σ₀, TableInvOn, arrs_setVar] using htable
  refine ⟨σ', activeInitCost q, hr, le_rfl, Xmem, asg, M, ?_, htable₀,
    hr.out_eq (noWrite_streamInitAtDepthCom j cap)⟩
  refine {
    turn := by simpa [σ₀, renEnv] using hturn
    bits_var := ?_
    level := hlevel₀
    logical_level := hlogical₀'
    play := hplay₀
    logical_tables := by
      simpa [σ₀, renEnv] using
        (Lax3Proofs.Refine.CoverActiveStreamLoop.tablesSized_renEnv_run
          hlogicalTables₀ hr)
    tables := by simpa [σ₀] using hpre.tables.run hr
    logical_base := by
      have hbase :=
        Lax3Proofs.Refine.CoverActiveStreamLoop.baseArrs_renEnv_run
          hlogicalBase₀ hr
      simpa [σ₀, renEnv] using baseArrs_setVar_c hbase "c" 0
    base_arrs := by
      exact baseArrs_setVar_c (hpre.base_arrs.run hr) "c" 0
    cluster_zero := ?_
    retained_zero := ?_
    batch_zero := ?_
    child_zero := ?_
    game_zero := ?_
    colours_zero := ?_
    scratch := hscratch₀ }
  · simpa [σ₀, renEnv] using (hr.frame_var "rsbits"
      (by apply notMem_wvars_streamInitAtDepthCom <;>
        simp [String.ext_iff])).trans hpre.init.bits_var
  · change σ'.arrs (cluName j) = arrOf n (fun _ => 0)
    rw [hr.frame_arr (cluName j) (by
      apply notMem_warrs_streamInitAtDepthCom <;>
        simp [cluName, cpsName, pdsName, balAltName, asgName, String.ext_iff])]
    exact hpre.head.cluster_zero
  · change σ'.arrs (resName j) = arrOf n (fun _ => 0)
    rw [hr.frame_arr (resName j) (by
      apply notMem_warrs_streamInitAtDepthCom <;>
        simp [resName, cpsName, pdsName, balAltName, asgName, String.ext_iff])]
    exact hpre.head.retained_zero
  · change σ'.arrs (batName j) = arrOf n (fun _ => 0)
    rw [hr.frame_arr (batName j) (by
      apply notMem_warrs_streamInitAtDepthCom <;>
        simp [batName, cpsName, pdsName, balAltName, asgName, String.ext_iff])]
    exact hpre.head.batch_zero
  · change σ'.arrs (alvName (j + 1)) = arrOf n (fun _ => 0)
    rw [hr.frame_arr (alvName (j + 1)) (by
      apply notMem_warrs_streamInitAtDepthCom <;>
        simp [alvName, cpsName, pdsName, balAltName, asgName, String.ext_iff])]
    exact hpre.head.child_zero
  · change σ'.arrs (gamName (j + 1)) = arrOf n (fun _ => 0)
    rw [hr.frame_arr (gamName (j + 1)) (by
      apply notMem_warrs_streamInitAtDepthCom <;>
        simp [gamName, cpsName, pdsName, balAltName, asgName, String.ext_iff])]
    exact hpre.head.game_zero
  · intro s hs
    change σ'.arrs (colName (j + 1) s) = arrOf n (fun _ => 0)
    rw [hr.frame_arr (colName (j + 1) s) (by
      apply notMem_warrs_streamInitAtDepthCom <;>
        simp [colName, cpsName, pdsName, balAltName, asgName, String.ext_iff])]
    exact hpre.head.colours_zero s hs

/-! ## Axiom audit -/

#print axioms streamInitSwap_invol
#print axioms streamInitTurn_spec
#print axioms streamInitStableStep

end Lax3Proofs.Refine.CoverActiveStreamInit
