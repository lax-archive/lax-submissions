import Lax3Proofs.RamDriverClusterMember
import Lax3Proofs.RamDriverDescend
import Lax3Proofs.RamDriverWrites
import Lax3Proofs.Refine.KillListWalk
import Lax3Proofs.Refine.ScatterDeadTurn

/-!
# Executable adapters for active-cover driver phases

The low-level walks already operate on the carrier arrays they actually
touch.  This file replays their surface proofs with `TurnPreA`, so a
nested arena carries only its live cover prefix and never has to
initialise dead assignment cells.
-/

namespace Lax3Proofs.RamDriverMemberPhases

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (masked CsrGraph)
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverBot
open Lax3Proofs.RamDriverCluster
open Lax3Proofs.RamDriverMember
open Lax3Proofs.RamDriverClusterMember
open Lax3Proofs.RamDriverDescend
open Lax3Proofs.RamDriverFrames
open Lax3Proofs.Refine
open Lax3Proofs.Refine.KillPass
open Lax3Proofs.Refine.ScatterDeadTurn
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

variable {n : ℕ}

/-! ## Batch padding -/

/-- The active padding contract with the word clause used by the walk. -/
def EnumStepAW (B q cap mb ns Ws j : ℕ) (G : SimpleGraph (Fin n))
    (O T M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre Xoff Xmem asg : ℕ → ℕ) (m : ℕ) (X W : Set (Fin n))
    (Alv' Gam' : ℕ → ℕ) (K : ℕ) : Prop :=
  Spec B (fun σ => TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
      Xoff Xmem asg m σ ∧ BatchData n j B G M X W Alv' Gam' σ ∧
      PlayRec B cap G (j + 1) Alv' Gam' σ ∧ (W ∩ X).Nonempty ∧
      W.ncard ≤ mb ∧ (∃ g, σ.arrs "wa" = arrOf mb g) ∧
      MaskWords B (batName j) σ)
    (enumBatch (batName j) (cluName j) mb)
    (fun σ σ' => TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
        Xoff Xmem asg m σ' ∧ PlayRec B cap G (j + 1) Alv' Gam' σ' ∧
      σ'.out = σ.out ∧ σ'.vars (curName j) = σ.vars (curName j) ∧
      ∃ w : Fin mb → Fin n, ClusterData n mb j B G M X W w Alv' Gam' σ' ∧
        ClusterWa mb w σ') K

/-- The existing padding walk discharges the active contract unchanged. -/
theorem enumStepAW {B q cap mb ns Ws j K : ℕ} {G : SimpleGraph (Fin n)}
    {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre Xoff Xmem asg : ℕ → ℕ} {m : ℕ} {X W : Set (Fin n)}
    {Alv' Gam' : ℕ → ℕ} {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hK : 23 * n + 12 * mb + 30 ≤ K) :
    EnumStepAW B q cap mb ns Ws j G O T M Gm C π centre Xoff Xmem asg m
      X W Alv' Gam' K := by
  have hmbB : mb < B := hB.mb_lt
  intro σ hσ
  obtain ⟨⟨hlev, hplayrec, hheld⟩, hbat, hplay', hne, hcard, ⟨gwa, hwa⟩,
      hmw⟩ := hσ
  obtain ⟨Xa, hXaarr, hXs, hXa1⟩ := hbat.1
  obtain ⟨Wa, hWaarr, hWs, -⟩ := hbat.2.1
  have hbatwa : batName j ≠ "wa" := by simp [batName, String.ext_iff]
  have hcluwa : cluName j ≠ "wa" := by simp [cluName, String.ext_iff]
  have hprod : markSet n (fun k => Wa k * Xa k) = W ∩ X := by
    ext v
    show Wa (v : ℕ) * Xa (v : ℕ) ≠ 0 ↔ _
    rw [← hWs, ← hXs]
    exact ⟨fun h => ⟨fun hc => h (by rw [hc]; ring), fun hc => h (by rw [hc]; ring)⟩,
      fun h => Nat.mul_ne_zero h.1 h.2⟩
  obtain ⟨σ', hr, ⟨E, hwa', hltE, hcovE⟩, hfv, hfa, -, hout⟩ :=
    ((enumBatch_spec B n mb Wa Xa (batName j) (cluName j) hbatwa hcluwa
      hB.one_lt hB.n_lt hmbB
      (by rw [hprod]; exact le_trans (Set.ncard_le_ncard Set.inter_subset_left
        (Set.toFinite _)) hcard)
      (by rw [hprod]; exact hne) (fun k hk => hmw.get hWaarr hk) hXa1).frame).run
      ⟨hlev.1, hWaarr, hXaarr, gwa, hwa⟩
  have hav : ∀ a : String, a ≠ "wa" → σ'.arrs a = σ.arrs a :=
    fun a ha => hfa a (not_mem_warrs_enumBatch ha)
  have hvv : ∀ y : String, y ≠ "bc" → y ≠ "z" → y ≠ "k" →
      σ'.vars y = σ.vars y :=
    fun y h1 h2 h3 => hfv y (not_mem_wvars_enumBatch h1 h2 h3)
  refine ⟨σ', hr.mono (by omega),
    ⟨levelPre_congr hlev hr
        (hvv "n" (by decide) (by decide) (by decide))
        (hvv "m" (by decide) (by decide) (by decide))
        (hvv "lw" (by decide) (by decide) (by decide))
        (hav "off" (by decide)) (hav "tgt" (by decide))
        (hav _ (by simp [alvName, String.ext_iff]))
        (hav _ (by simp [gamName, String.ext_iff]))
        (fun c' _ => hav _ (by simp [colName, String.ext_iff]))
        (fun a ha => hav a (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
        (hav _ (by simp [memName, String.ext_iff]))
        (hvv _ (by simp [mnumName, String.ext_iff])
          (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff])),
      hplayrec.congr
        (fun a _ => hvv (ctrName a) (by simp [ctrName, String.ext_iff])
          (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff]))
        (fun a _ => hav (resName a) (by simp [resName, String.ext_iff]))
        (fun a _ => hav (gamName a) (by simp [gamName, String.ext_iff]))
        (fun a _ => hav (parName a) (by simp [parName, balName, String.ext_iff])),
      hheld.congr (hav _ (by simp [ordName, String.ext_iff]))
        (hav _ (by simp [xofName, String.ext_iff]))
        (hav _ (by simp [xmmName, String.ext_iff]))
        (hav _ (by simp [asgName, String.ext_iff]))
        (hvv _ (by simp [xpName, String.ext_iff])
          (by simp [xpName, String.ext_iff]) (by simp [xpName, String.ext_iff]))⟩,
    hplay'.congr
      (fun a _ => hvv (ctrName a) (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff]))
      (fun a _ => hav (resName a) (by simp [resName, String.ext_iff]))
      (fun a _ => hav (gamName a) (by simp [gamName, String.ext_iff]))
      (fun a _ => hav (parName a) (by simp [parName, balName, String.ext_iff])),
    hout (noWrite_enumBatch _ _ _),
    hvv _ (by simp [curName, String.ext_iff]) (by simp [curName, String.ext_iff])
      (by simp [curName, String.ext_iff]),
    fun i => ⟨E (i : ℕ), (hltE (i : ℕ) i.isLt).1⟩, ⟨?_, ?_⟩, ?_⟩
  · exact RamDriverDescend.batchData_congr hbat
      (hav _ (by simp [cluName, String.ext_iff])) (hav _ hbatwa)
      (hav _ (by simp [resName, String.ext_iff]))
      (hav _ (by simp [alvName, String.ext_iff]))
      (hav _ (by simp [gamName, String.ext_iff]))
      (hav _ (by simp [memName, String.ext_iff]))
      (hvv _ (by simp [mnumName, String.ext_iff])
        (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff]))
  · apply Set.eq_of_subset_of_subset
    · rintro v ⟨i, rfl⟩
      rw [← hprod]
      exact (hltE (i : ℕ) i.isLt).2
    · intro v hv
      rw [← hprod] at hv
      obtain ⟨i, hi, hEi⟩ := hcovE (v : ℕ) v.isLt hv
      exact ⟨⟨i, hi⟩, Fin.ext hEi⟩
  · rw [ClusterWa, hwa']
    exact arrOf_congr (fun i hi => by rw [dif_pos hi])

/-- The word clause follows from `BatchData`, exactly as in the carrier proof. -/
theorem enumStepA {B q cap mb ns Ws j K : ℕ} {G : SimpleGraph (Fin n)}
    {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre Xoff Xmem asg : ℕ → ℕ} {m : ℕ} {X W : Set (Fin n)}
    {Alv' Gam' : ℕ → ℕ} {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hK : 23 * n + 12 * mb + 30 ≤ K) :
    EnumStepA B q cap mb ns Ws j G O T M Gm C π centre Xoff Xmem asg m
      X W Alv' Gam' K :=
  (enumStepAW hB hK).pre (fun _ hσ => by
    obtain ⟨hturn, hbat, hplay, hne, hcard, hwa⟩ := hσ
    obtain ⟨Wa, hWaarr, -, hWaB⟩ := hbat.2.1
    refine ⟨hturn, hbat, hplay, hne, hcard, hwa, fun v hv => ?_⟩
    rw [hWaarr] at hv
    obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hv
    exact hWaB k (List.mem_range.1 hk))

/-! ## Child colouring -/

/-- The landed colouring walk, with the active cover merely framed. -/
theorem colourStepA
    {B q cap mb ns Ws j K : ℕ} {G : SimpleGraph (Fin n)}
    {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre Xoff Xmem asg : ℕ → ℕ} {m : ℕ} {X W : Set (Fin n)}
    {w : Fin mb → Fin n} {Alv' Gam' : ℕ → ℕ}
    (hK : colourCost n ns cap mb (sigL cap mb j) ≤ K) :
    ColourStepA B q cap mb ns Ws j G O T M Gm C π centre Xoff Xmem asg m
      X W w Alv' Gam' K := by
  intro hcsr d hB σ hσ
  obtain ⟨⟨hlev, hplayj, hheld⟩, ⟨hbat, hrange⟩, hwa, hplay1⟩ := hσ
  obtain ⟨Xa, hXaarr, hXs, hXbit⟩ := hbat.1
  obtain ⟨Ra, hRaarr, hRam, hRaB⟩ := hbat.2.2.1
  have hdep := hlev.2.2.2.2.2.2.2.2.2.2.1
  have hCbit : ∀ c, c < sigL cap mb j → ∀ v, v < n → C c v ≤ 1 :=
    hlev.2.2.2.2.2.2.2.2.1
  have hWf : ∀ i : Fin mb,
      (fun k => if h : k < mb then ((w ⟨k, h⟩ : Fin n) : ℕ) else 0) (i : ℕ) =
        (w i : ℕ) := by
    intro i
    simp only [dif_pos i.isLt, Fin.eta]
  have hpre : ColPre n cap mb Ws j O T C Xa Ra
      (fun k => if h : k < mb then ((w ⟨k, h⟩ : Fin n) : ℕ) else 0) σ :=
    ⟨hlev.1, hlev.2.1, hlev.2.2.1, hXaarr, hRaarr, hlev.2.2.2.2.2.1, hwa,
      fun s hs => hdep.col hs⟩
  obtain ⟨σ', hr, ⟨hpre', hbit', heq'⟩, hfv, hfa, -, hout⟩ :=
    ((colourCom_spec (nt := Ws) hcsr hB
      hlev.2.2.2.2.2.2.2.2.2.2.2.2.1.1 hRaB hCbit hXbit hWf).frame).run hpre
  have hav : ∀ a : String, (∀ s, a ≠ colName (j + 1) s) →
      σ'.arrs a = σ.arrs a := by
    intro a ha
    refine hfa a (fun hc => ?_)
    obtain ⟨s, hs⟩ := RamDriverFrames.mem_warrs_colourCom cap mb j hc
    exact ha s hs
  have hvv : ∀ y : String, y ∉ (["i", "z", "hit", "w", "j", "jend"] : List String) →
      σ'.vars y = σ.vars y :=
    fun y hy => hfv y (fun hc => hy (mem_wvars_colourCom hc))
  have hctr : ∀ a : ℕ, σ'.vars (ctrName a) = σ.vars (ctrName a) := fun a =>
    hvv _ (RamDriverIO.notMem_of_append (p := "ctr") (s := toString a) (by decide))
  have hgama : ∀ a : ℕ, σ'.arrs (gamName a) = σ.arrs (gamName a) := fun a =>
    hav _ (fun s => Ne.symm (colName_ne_gamName _ _ _))
  have hresa : ∀ a : ℕ, σ'.arrs (resName a) = σ.arrs (resName a) := fun a =>
    hav _ (fun s => Ne.symm (colName_ne_resName _ _ _))
  have hpara : ∀ a : ℕ, σ'.arrs (parName a) = σ.arrs (parName a) := fun a =>
    hav _ (fun s => Ne.symm (by simpa [parName] using colName_ne_balName (j + 1) s a))
  have hturn' : TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
      Xoff Xmem asg m σ' := by
    refine ⟨levelPre_congr hlev hr (hvv "n" (by decide)) (hvv "m" (by decide))
        (hvv "lw" (by decide))
        (hav "off" (fun s => Ne.symm (colName_ne_lit (by decide))))
        (hav "tgt" (fun s => Ne.symm (colName_ne_lit (by decide))))
        (hav _ (fun s => Ne.symm (colName_ne_alvName _ _ _))) (hgama j)
        (fun c' _ => hav _ (fun s => colName_ne_depth (by omega)))
        (fun a ha => hav a ?_)
        (hav _ (fun s => Ne.symm (colName_ne_memName _ _ _)))
        (hvv _ (RamDriverIO.notMem_of_append (p := "mm") (s := toString j) (by decide))),
      hplayj.congr (fun a _ => hctr a) (fun a _ => hresa a)
        (fun a _ => hgama a) (fun a _ => hpara a),
      hheld.congr (hav _ (fun s => Ne.symm (colName_ne_ordName _ _ _)))
        (hav _ (fun s => Ne.symm (colName_ne_xofName _ _ _)))
        (hav _ (fun s => Ne.symm (colName_ne_xmmName _ _ _)))
        (hav _ (fun s => Ne.symm (colName_ne_asgName _ _ _)))
        (hvv _ (RamDriverIO.notMem_of_append (p := "xq") (s := toString j) (by decide)))⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      exact fun s => Ne.symm (colName_ne_lit (by decide))
  refine ⟨σ', hr.mono hK, hturn',
    ⟨RamDriverDescend.batchData_congr hbat
        (hav _ (fun s => Ne.symm (colName_ne_cluName _ _ _)))
        (hav _ (fun s => Ne.symm (colName_ne_batName _ _ _)))
        (hav _ (fun s => Ne.symm (colName_ne_resName _ _ _)))
        (hav _ (fun s => Ne.symm (colName_ne_alvName _ _ _)))
        (hav _ (fun s => Ne.symm (colName_ne_gamName _ _ _)))
        (hav _ (fun s => Ne.symm (colName_ne_memName _ _ _)))
        (hvv _ (RamDriverIO.notMem_of_append (p := "mm")
          (s := toString (j + 1)) (by decide))), hrange⟩,
    hplay1.congr (fun a _ => hctr a) (fun a _ => hresa a)
      (fun a _ => hgama a) (fun a _ => hpara a),
    hout (noWrite_colourCom cap mb j),
    hvv _ (RamDriverIO.notMem_of_append (p := "cu") (s := toString j) (by decide)),
    fun s => cellsOf σ' (colName (j + 1) s), fun c hc => ?_, hbit', ?_⟩
  · obtain ⟨g, hg⟩ := hpre'.2.2.2.2.2.2.2 c hc
    exact arrOf_cellsOf hg
  · rw [heq', stepColoringP, hRam, hXs]

/-! ## Kill-list enumeration -/

/-- The landed kill-list walk, with the active cover merely framed. -/
theorem killListStepA
    {B q q_top cap mb ns Ws j : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} {centre Xoff Xmem asg : ℕ → ℕ} {m : ℕ}
    {X W : Set (Fin n)} {w : Fin mb → Fin n} {Alv' Gam' : ℕ → ℕ}
    {C' : ℕ → ℕ → ℕ} :
    KillListStepA B q q_top cap mb ns Ws j φ G O T M Gm C π centre Xoff Xmem asg m
      X W w Alv' Gam' C' (Refine.KillListPass.killListCost mb) := by
  intro d hB
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hturn, hdat, hwa, hcolarr, hplay, htsz, hkrows⟩ := hσ
  obtain ⟨Xa, hXa, hXaS, hXaB⟩ := hdat.1.1
  have hdep : DepthMem n cap mb σ :=
    hturn.level.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨σ', hrun, hlist⟩ :=
    (Refine.KillListPass.killListCom_spec (M := M) (Xa := Xa) (w := w) (j := j)
        hB.one_lt hB.n_lt hB.mb_lt
        (fun z hz => hturn.level.2.2.2.2.2.2.1 z hz) hXaB).run (σ := σ)
      ⟨Refine.KillPass.clusterWa_eq hwa, hturn.level.2.2.2.1, hXa, hdep.kl j⟩
  have harr : ∀ a : String, a ≠ klName j → σ'.arrs a = σ.arrs a :=
    fun a ha => hrun.frame_arr a (RamDriverWrites.notMem_warrs_killListCom ha)
  have hvar : ∀ y : String, y ≠ kkName j → y ≠ "kk" → y ≠ "kv" → y ≠ "kf" →
      y ≠ "kt" → σ'.vars y = σ.vars y :=
    fun y h1 h2 h3 h4 h5 =>
      hrun.frame_var y (RamDriverWrites.notMem_wvars_killListCom h1 h2 h3 h4 h5)
  have harrDepth : ∀ b : ℕ, σ'.arrs (alvName b) = σ.arrs (alvName b) := fun b =>
    harr _ (by simp [alvName, klName, String.ext_iff])
  have harrGam : ∀ b : ℕ, σ'.arrs (gamName b) = σ.arrs (gamName b) := fun b =>
    harr _ (by simp [gamName, klName, String.ext_iff])
  have harrRes : ∀ b : ℕ, σ'.arrs (resName b) = σ.arrs (resName b) := fun b =>
    harr _ (by simp [resName, klName, String.ext_iff])
  have harrPar : ∀ b : ℕ, σ'.arrs (parName b) = σ.arrs (parName b) := fun b =>
    harr _ (by simp [parName, balName, klName, String.ext_iff])
  have harrCol : ∀ b c : ℕ, σ'.arrs (colName b c) = σ.arrs (colName b c) := fun b c =>
    harr _ (by simp [colName, klName, String.ext_iff])
  have harrMem : ∀ b : ℕ, σ'.arrs (memName b) = σ.arrs (memName b) := fun b =>
    harr _ (by simp [memName, klName, String.ext_iff])
  have hvarMm : ∀ b : ℕ, σ'.vars (mnumName b) = σ.vars (mnumName b) := fun b =>
    hvar _ (by simp [mnumName, kkName, String.ext_iff])
      (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff])
      (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff])
  have hlev' : LevelPre B n cap mb ns Ws O T j M Gm C σ' :=
    RamDriverCompose.levelPre_run hturn.level hrun
      (RamDriverWrites.notMem_wvars_killListCom (by simp [kkName, String.ext_iff])
        (by decide) (by decide) (by decide) (by decide))
      (RamDriverWrites.notMem_wvars_killListCom (by simp [kkName, String.ext_iff])
        (by decide) (by decide) (by decide) (by decide))
      (RamDriverWrites.notMem_wvars_killListCom (by simp [kkName, String.ext_iff])
        (by decide) (by decide) (by decide) (by decide))
      (RamDriverWrites.notMem_warrs_killListCom (by simp [klName, String.ext_iff]))
      (RamDriverWrites.notMem_warrs_killListCom (by simp [klName, String.ext_iff]))
      (RamDriverWrites.notMem_warrs_killListCom
        (by simp [alvName, klName, String.ext_iff]))
      (RamDriverWrites.notMem_warrs_killListCom
        (by simp [gamName, klName, String.ext_iff]))
      (fun _ => RamDriverWrites.notMem_warrs_killListCom
        (by simp [colName, klName, String.ext_iff]))
      (fun a ha => by
        simp only [RamDriverCompose.zeroArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact RamDriverWrites.notMem_warrs_killListCom
            (by simp [klName, String.ext_iff]))
      (RamDriverWrites.notMem_warrs_killListCom
        (by simp [memName, klName, String.ext_iff]))
      (RamDriverWrites.notMem_wvars_killListCom
        (by simp [mnumName, kkName, String.ext_iff])
        (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff])
        (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff]))
  refine ⟨σ', _, hrun, le_rfl, ⟨hlev', ?_, ?_⟩, ⟨?_, hdat.2⟩, fun c hc => ?_,
    ?_, ?_, ?_, ?_, ?_⟩
  · exact hturn.play.congr
      (fun a _ => hvar (ctrName a) (by simp [ctrName, kkName, String.ext_iff])
        (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff]))
      (fun a _ => harrRes a) (fun a _ => harrGam a) (fun a _ => harrPar a)
  · exact hturn.held.congr
      (harr (ordName j) (by simp [ordName, klName, String.ext_iff]))
      (harr (xofName j) (by simp [xofName, klName, String.ext_iff]))
      (harr (xmmName j) (by simp [xmmName, klName, String.ext_iff]))
      (harr (asgName j) (by simp [asgName, klName, String.ext_iff]))
      (hvar (xpName j) (by simp [xpName, kkName, String.ext_iff])
        (by simp [xpName, String.ext_iff]) (by simp [xpName, String.ext_iff])
        (by simp [xpName, String.ext_iff]) (by simp [xpName, String.ext_iff]))
  · exact Refine.KillPass.batchData_congr hdat.1
      (harr (cluName j) (by simp [cluName, klName, String.ext_iff]))
      (harr (batName j) (by simp [batName, klName, String.ext_iff]))
      (harr (resName j) (by simp [resName, klName, String.ext_iff]))
      (harrDepth (j + 1)) (harrGam (j + 1)) (harrMem (j + 1)) (hvarMm (j + 1))
  · rw [harrCol (j + 1) c]
    exact hcolarr c hc
  · exact hplay.congr
      (fun a _ => hvar (ctrName a) (by simp [ctrName, kkName, String.ext_iff])
        (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff]))
      (fun a _ => harrRes a) (fun a _ => harrGam a) (fun a _ => harrPar a)
  · exact hrun.out_eq (RamDriverWrites.noWrite_killListCom mb j)
  · exact hvar (curName j) (by simp [curName, kkName, String.ext_iff])
      (by simp [curName, String.ext_iff]) (by simp [curName, String.ext_iff])
      (by simp [curName, String.ext_iff]) (by simp [curName, String.ext_iff])
  · intro i hi Tb hTb
    exact hkrows i hi Tb (by rw [← harr (tabName (j + 1) i)
      (by simp [tabName, klName, String.ext_iff])]; exact hTb)
  · obtain ⟨kl, kq, hkl, hkq, hqle, hkln, hinj, hsound, hcomp⟩ := hlist
    refine ⟨kl, kq, hkl, hkq, hqle, hkln, hinj, fun e he => ?_, fun v hMv hvX hvW => ?_⟩
    · obtain ⟨hM, hXv, p, hp⟩ := hsound e he
      refine ⟨w p, hp, by rw [hp]; exact hM, ?_, ?_⟩
      · rw [← hXaS]
        show Xa (w p : ℕ) ≠ 0
        rw [hp]
        exact hXv
      · exact hdat.mem_batch p
    · obtain ⟨p, hp⟩ : ∃ p : Fin mb, w p = v := by
        have : v ∈ Set.range w := by
          rw [hdat.2]
          exact ⟨hvW, hvX⟩
        exact this
      obtain ⟨e, he, hee⟩ := hcomp p (by rw [hp]; exact hMv)
        (by rw [hp]; rw [← hXaS] at hvX; exact hvX)
      exact ⟨e, he, by rw [hee, hp]⟩

/-! ## Killed child rows -/

set_option maxHeartbeats 1000000 in
open Classical in
/-- The landed kill-row walk, with the active cover merely framed. -/
theorem killStepA
    {B q q_top cap mb ns Ws ℓ j : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} {centre Xoff Xmem asg : ℕ → ℕ} {m : ℕ}
    {X W : Set (Fin n)} {w : Fin mb → Fin n} {Alv' Gam' : ℕ → ℕ}
    {C' : ℕ → ℕ → ℕ} :
    KillStepA B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π centre Xoff Xmem asg m
      X W w Alv' Gam' C' (killCost q_top cap mb (j + 1) φ) := by
  intro d hB
  have hlocal : ∀ β ∈ tablesAt q_top cap mb φ (j + 1), IsLocal β :=
    fun β hβ => (tableRank_of_mem_tablesAt (j + 1) β hβ).1
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hturn, hdat, hwa, hcolarr, hcolbit, hcolread, hplay, htsz, hbarr⟩ := hσ
  obtain ⟨Xa, hXa, hXaS, hXaB⟩ := hdat.1.1
  obtain ⟨σ', hrun, hrows⟩ :=
    (killCom_spec (M := M) (Xa := Xa) (w := w) hB.one_lt hB.n_lt hB.mb_lt
      hcolbit hlocal (fun z hz => hturn.level.2.2.2.2.2.2.1 z hz) hXaB).run
      (σ := σ) ⟨⟨hturn.level.1, fun c hc => hcolarr c hc, hbarr.2 (j + 1)⟩,
        clusterWa_eq hwa, hturn.level.2.2.2.1, hXa,
        fun i hi => htsz.get (j + 1) hi⟩
  have harr : ∀ (a : String), (∀ i, a ≠ tabName (j + 1) i) → ¬ Ext "bb" a →
      σ'.arrs a = σ.arrs a :=
    fun a htb hext => hrun.frame_arr a (notMem_warrs_killCom hlocal htb hext)
  have hvar : ∀ (y : String), y ≠ "kk" → y ≠ "kv" → (∀ i, y ≠ envName i) →
      ¬ Ext "bb" y → σ'.vars y = σ.vars y :=
    fun y hkk hkv hev hext =>
      hrun.frame_var y (notMem_wvars_killCom hlocal hkk hkv hev hext)
  have hnev : ∀ (p : String) (c : Char), (∃ t, p.toList = c :: t) → c ≠ 'e' →
      ∀ i, p ≠ envName i :=
    fun p c hp hc i => ne_of_head_ne hp (head_envName i) hc
  have harrDepth : ∀ b : ℕ, σ'.arrs (alvName b) = σ.arrs (alvName b) := fun b =>
    harr (alvName b) (fun i => alvName_ne_tabName b (j + 1) i)
      (fun h => not_ext_b_alvName b (RamDriverCompose.ext_b_of_ext_bb h))
  have harrGam : ∀ b : ℕ, σ'.arrs (gamName b) = σ.arrs (gamName b) := fun b =>
    harr (gamName b) (fun i => gamName_ne_tabName b (j + 1) i)
      (fun h => not_ext_b_gamName b (RamDriverCompose.ext_b_of_ext_bb h))
  have harrRes : ∀ b : ℕ, σ'.arrs (resName b) = σ.arrs (resName b) := fun b =>
    harr (resName b) (fun i => by simp [resName, tabName, String.ext_iff])
      (by rw [resName]; exact DeadSweep.not_ext_bb_append (p := "res") rfl (by decide) _)
  have harrPar : ∀ b : ℕ, σ'.arrs (parName b) = σ.arrs (parName b) := fun b =>
    harr (parName b) (fun i => by simp [parName, balName, tabName, String.ext_iff])
      (by rw [parName, balName]
          exact RamDriverWrites.not_ext_bb_append (p := "bal") (by decide) (by decide) _)
  have harrCol : ∀ b c : ℕ, σ'.arrs (colName b c) = σ.arrs (colName b c) := fun b c =>
    harr (colName b c) (fun i => colName_ne_tabName b c (j + 1) i)
      (fun h => not_ext_b_colName b c (RamDriverCompose.ext_b_of_ext_bb h))
  have harrMem : ∀ b : ℕ, σ'.arrs (memName b) = σ.arrs (memName b) := fun b =>
    harr (memName b)
      (fun i => ne_of_head_ne (RamDriverCompose.head_memName b)
        (head_tabName (j + 1) i) (by decide))
      (RamDriverCompose.not_ext_bb_memName b)
  have hvarMm : ∀ b : ℕ, σ'.vars (mnumName b) = σ.vars (mnumName b) := fun b =>
    hvar (mnumName b) (by simp [mnumName, String.ext_iff])
      (by simp [mnumName, String.ext_iff])
      (hnev (mnumName b) 'm' ⟨_, by rw [mnumName, String.toList_append]; rfl⟩ (by decide))
      (RamDriverCompose.not_ext_bb_mnumName b)
  have hlev' : LevelPre B n cap mb ns Ws O T j M Gm C σ' :=
    RamDriverCompose.levelPre_run hturn.level hrun
      (notMem_wvars_killCom hlocal (by decide) (by decide)
        (fun i => lit_ne_envName ⟨_, rfl⟩ (by decide) i)
        (not_ext_of_not_prefix (by decide)))
      (notMem_wvars_killCom hlocal (by decide) (by decide)
        (fun i => lit_ne_envName ⟨_, rfl⟩ (by decide) i)
        (not_ext_of_not_prefix (by decide)))
      (notMem_wvars_killCom hlocal (by decide) (by decide)
        (fun i => lit_ne_envName ⟨_, rfl⟩ (by decide) i)
        (not_ext_of_not_prefix (by decide)))
      (notMem_warrs_killCom hlocal
        (fun i => RamDriverBase.lit_ne_tabName (by decide) (j + 1) i)
        (not_ext_of_not_prefix (by decide)))
      (notMem_warrs_killCom hlocal
        (fun i => RamDriverBase.lit_ne_tabName (by decide) (j + 1) i)
        (not_ext_of_not_prefix (by decide)))
      (notMem_warrs_killCom hlocal (fun i => alvName_ne_tabName j (j + 1) i)
        (fun h => not_ext_b_alvName j (RamDriverCompose.ext_b_of_ext_bb h)))
      (notMem_warrs_killCom hlocal (fun i => gamName_ne_tabName j (j + 1) i)
        (fun h => not_ext_b_gamName j (RamDriverCompose.ext_b_of_ext_bb h)))
      (fun c => notMem_warrs_killCom hlocal
        (fun i => colName_ne_tabName j c (j + 1) i)
        (fun h => not_ext_b_colName j c (RamDriverCompose.ext_b_of_ext_bb h)))
      (fun a ha => by
        simp only [RamDriverCompose.zeroArrs, List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact notMem_warrs_killCom hlocal
            (fun i => RamDriverBase.lit_ne_tabName (by decide) (j + 1) i)
            (not_ext_of_not_prefix (by decide)))
      (notMem_warrs_killCom hlocal
        (fun i => ne_of_head_ne (RamDriverCompose.head_memName j)
          (head_tabName (j + 1) i) (by decide))
        (RamDriverCompose.not_ext_bb_memName j))
      (notMem_wvars_killCom hlocal (by simp [mnumName, String.ext_iff])
        (by simp [mnumName, String.ext_iff])
        (hnev _ 'm' ⟨_, by rw [mnumName, String.toList_append]; rfl⟩ (by decide))
        (RamDriverCompose.not_ext_bb_mnumName j))
  refine ⟨σ', _, hrun, le_rfl, ⟨hlev', ?_, ?_⟩, ⟨?_, hdat.2⟩, fun c hc => ?_,
    ?_, ?_, ?_, fun i hi Tb harrTb v hMv hvX hvW => ?_⟩
  · exact hturn.play.congr
      (fun a _ => hvar (ctrName a) (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff])
        (hnev (ctrName a) 'c' ⟨_, by rw [ctrName, String.toList_append]; rfl⟩ (by decide))
        (DeadSweep.not_ext_bb_ctrName a))
      (fun a _ => harrRes a) (fun a _ => harrGam a) (fun a _ => harrPar a)
  · exact hturn.held.congr
      (harr (ordName j) (fun i => by simp [ordName, tabName, String.ext_iff])
        (DeadSweep.not_ext_bb_ordName j))
      (harr (xofName j) (fun i => by simp [xofName, tabName, String.ext_iff])
        (DeadSweep.not_ext_bb_xofName j))
      (harr (xmmName j) (fun i => by simp [xmmName, tabName, String.ext_iff])
        (DeadSweep.not_ext_bb_xmmName j))
      (harr (asgName j) (fun i => by simp [asgName, tabName, String.ext_iff])
        (DeadSweep.not_ext_bb_asgName j))
      (hvar (xpName j) (by simp [xpName, String.ext_iff])
        (by simp [xpName, String.ext_iff])
        (hnev (xpName j) 'x' ⟨_, by rw [xpName, String.toList_append]; rfl⟩ (by decide))
        (DeadSweep.not_ext_bb_xpName j))
  · exact KillPass.batchData_congr hdat.1
      (harr (cluName j) (fun i => by simp [cluName, tabName, String.ext_iff])
        (by rw [cluName]; exact DeadSweep.not_ext_bb_append (p := "clu") rfl (by decide) _))
      (harr (batName j) (fun i => by simp [batName, tabName, String.ext_iff])
        (not_ext_bb_of_cons₂ (y := batName j)
          (by rw [batName, String.toList_append]; rfl) (by decide)))
      (harr (resName j) (fun i => by simp [resName, tabName, String.ext_iff])
        (by rw [resName]; exact DeadSweep.not_ext_bb_append (p := "res") rfl (by decide) _))
      (harrDepth (j + 1)) (harrGam (j + 1)) (harrMem (j + 1)) (hvarMm (j + 1))
  · rw [harrCol (j + 1) c]
    exact hcolarr c hc
  · exact hplay.congr
      (fun a _ => hvar (ctrName a) (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff])
        (hnev (ctrName a) 'c' ⟨_, by rw [ctrName, String.toList_append]; rfl⟩ (by decide))
        (DeadSweep.not_ext_bb_ctrName a))
      (fun a _ => harrRes a) (fun a _ => harrGam a) (fun a _ => harrPar a)
  · exact hrun.out_eq (RamDriverWrites.noWrite_killCom q_top cap mb j φ)
  · exact hvar (curName j) (by simp [curName, String.ext_iff])
      (by simp [curName, String.ext_iff])
      (hnev (curName j) 'c' ⟨_, by rw [curName, String.toList_append]; rfl⟩ (by decide))
      (by rw [curName]; exact DeadSweep.not_ext_bb_append (p := "cu") rfl (by decide) _)
  · obtain ⟨p, hp⟩ : ∃ p : Fin mb, w p = v := by
      have : v ∈ Set.range w := by
        rw [hdat.2]
        exact ⟨hvW, hvX⟩
      exact this
    obtain ⟨Tb', hTb', hval'⟩ := hrows i hi
    have hcell : Tb (v : ℕ) = Tb' (v : ℕ) :=
      eq_of_arrOf_eq (harrTb.symm.trans hTb') v.isLt
    have hXav : Xa (v : ℕ) ≠ 0 := by
      rw [← hXaS] at hvX
      exact hvX
    obtain ⟨hb1, hbiff⟩ := hval' p (by rw [hp]; exact hMv)
      (by rw [hp]; exact hXav)
    rw [hp] at hb1 hbiff
    have hdead : Alv' (v : ℕ) = 0 := by
      by_contra hc
      exact absurd ((hdat.1.2.2.2.2.2.2.1 v).mp hc).2.2 (by simp [hvW])
    refine ⟨by rw [hcell]; exact hb1, ?_⟩
    rw [hcell, hbiff]
    exact (DeadRow.sat_bot_of_dead₁ (G := G) hdead
      (hlocal _ (List.getElem_mem hi))).symm

/-! ## Dead-aware scatter fold -/

/-- The state read by the scatter engine, retaining only an active cover. -/
def ScatPreA (B q q_top cap mb ns Ws j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    {n : ℕ} (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre Xoff Xmem asg : ℕ → ℕ) (m : ℕ) (X W : Set (Fin n))
    (w : Fin mb → Fin n) (Alv' Gam' : ℕ → ℕ) (C' : ℕ → ℕ → ℕ)
    (σ : Env) : Prop :=
  TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre Xoff Xmem asg m σ ∧
    ClusterData n mb j B G M X W w Alv' Gam' σ ∧
    (∀ c < sigL cap mb (j + 1), σ.arrs (colName (j + 1) c) = arrOf n (C' c)) ∧
    (∀ c < sigL cap mb (j + 1), ∀ v < n, C' c v ≤ 1) ∧
    colRead n C' (sigL cap mb (j + 1)) =
      stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w ∧
    TableInvOn q_top cap mb φ G (j + 1) Alv' C' (rowDom M Alv' X W) σ

variable {B q q_top cap mb ns Ws ℓ j : ℕ} {φ : Lax3.FirstOrder.FO 0}
  {G : SimpleGraph (Fin n)} {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
  {π : Equiv.Perm (Fin n)} {centre Xoff Xmem asg : ℕ → ℕ} {m : ℕ}
  {X W : Set (Fin n)} {w : Fin mb → Fin n} {Alv' Gam' : ℕ → ℕ}
  {C' : ℕ → ℕ → ℕ} {σ : Env}

theorem ScatPreA.n_eq
    (h : ScatPreA (n := n) B q q_top cap mb ns Ws j φ G O T M Gm C π centre Xoff Xmem asg m
      X W w Alv' Gam' C' σ) : σ.vars "n" = n := h.1.level.1

theorem ScatPreA.off
    (h : ScatPreA (n := n) B q q_top cap mb ns Ws j φ G O T M Gm C π centre Xoff Xmem asg m
      X W w Alv' Gam' C' σ) : σ.arrs "off" = arrOf (n + 1) O := h.1.level.2.1

theorem ScatPreA.tgt
    (h : ScatPreA (n := n) B q q_top cap mb ns Ws j φ G O T M Gm C π centre Xoff Xmem asg m
      X W w Alv' Gam' C' σ) : σ.arrs "tgt" = arrOf Ws T := h.1.level.2.2.1

theorem ScatPreA.mem
    (h : ScatPreA (n := n) B q q_top cap mb ns Ws j φ G O T M Gm C π centre Xoff Xmem asg m
      X W w Alv' Gam' C' σ) : LevelMem B n cap mb σ :=
  h.1.level.2.2.2.2.2.2.2.2.2.1

theorem ScatPreA.nsW
    (h : ScatPreA (n := n) B q q_top cap mb ns Ws j φ G O T M Gm C π centre Xoff Xmem asg m
      X W w Alv' Gam' C' σ) : ns ≤ Ws :=
  h.1.level.2.2.2.2.2.2.2.2.2.2.2.2.1.1

theorem ScatPreA.data
    (h : ScatPreA (n := n) B q q_top cap mb ns Ws j φ G O T M Gm C π centre Xoff Xmem asg m
      X W w Alv' Gam' C' σ) : ClusterData n mb j B G M X W w Alv' Gam' σ := h.2.1

/-- The active scatter state survives every engine call. -/
theorem ScatPreA.run {c : Com} {σ σ' : Env} {K : ℕ}
    (h : ScatPreA (n := n) B q q_top cap mb ns Ws j φ G O T M Gm C π centre Xoff Xmem asg m
      X W w Alv' Gam' C' σ)
    (hrun : Run B c σ σ' K)
    (hA : ∀ a ∈ c.warrs, a ∈ scratchArrs ∨ BbExt a)
    (hV : ∀ y ∈ ["n", "m", "lw"], y ∉ c.wvars)
    (hVctr : ∀ a : ℕ, ctrName a ∉ c.wvars) (hVxp : xpName j ∉ c.wvars)
    (hVmm : ∀ a : ℕ, mnumName a ∉ c.wvars) :
    ScatPreA (n := n) B q q_top cap mb ns Ws j φ G O T M Gm C π centre Xoff Xmem asg m
      X W w Alv' Gam' C' σ' := by
  have hfa : ∀ a : String, a ∉ scratchArrs → ¬ BbExt a →
      σ'.arrs a = σ.arrs a :=
    fun a ha hb => hrun.frame_arr a (fun hm => (hA a hm).elim ha hb)
  have hfv : ∀ y : String, y ∉ c.wvars → σ'.vars y = σ.vars y :=
    fun y hy => hrun.frame_var y hy
  obtain ⟨hturn, hdata, hcolarr, hcolbit, hcolread, htab⟩ := h
  have hlev' : LevelPre B n cap mb ns Ws O T j M Gm C σ' :=
    levelPre_congr hturn.level hrun
      (hfv "n" (hV "n" (by simp))) (hfv "m" (hV "m" (by simp)))
      (hfv "lw" (hV "lw" (by simp)))
      (hfa "off" (by decide) not_bbExt_off) (hfa "tgt" (by decide) not_bbExt_tgt)
      (hfa _ (alvName_notMem_scratchArrs j) (not_bbExt_alvName j))
      (hfa _ (gamName_notMem_scratchArrs j) (not_bbExt_gamName j))
      (fun c hc => hfa _ (colName_notMem_scratchArrs j c) (not_bbExt_colName j c))
      (fun a ha => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact hfa _ (by decide) not_bbExt_elm
        · exact hfa _ (by decide) not_bbExt_bh
        · exact hfa _ (by decide) not_bbExt_ooff
        · exact hfa _ (by decide) not_bbExt_noff
        · exact hfa _ (by decide) not_bbExt_stf
        · exact hfa _ (by decide) not_bbExt_sta
        · exact hfa _ (by decide) not_bbExt_std
        · exact hfa _ (by decide) not_bbExt_ste)
      (hfa _ (memName_notMem_scratchArrs j) (not_bbExt_memName j))
      (hfv _ (hVmm j))
  have hturn' : TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre Xoff Xmem asg m
      σ' :=
    { level := hlev'
      play := hturn.play.congr (fun a _ => hfv _ (hVctr a))
        (fun a _ => hfa _ (resName_notMem_scratchArrs a) (not_bbExt_resName a))
        (fun a _ => hfa _ (gamName_notMem_scratchArrs a) (not_bbExt_gamName a))
        (fun a _ => hfa _ (parName_notMem_scratchArrs a) (not_bbExt_parName a))
      held := hturn.held.congr
        (hfa _ (by simp [ordName, scratchArrs, String.ext_iff]) (not_bbExt_ordName j))
        (hfa _ (by simp [xofName, scratchArrs, String.ext_iff]) (not_bbExt_xofName j))
        (hfa _ (by simp [xmmName, scratchArrs, String.ext_iff]) (not_bbExt_xmmName j))
        (hfa _ (by simp [asgName, scratchArrs, String.ext_iff]) (not_bbExt_asgName j))
        (hfv _ hVxp) }
  refine ⟨hturn', ⟨?_, hdata.2⟩, ?_, hcolbit, hcolread, ?_⟩
  · exact RamDriverDescend.batchData_congr hdata.1
      (hfa _ (cluName_notMem_scratchArrs j) (not_bbExt_cluName j))
      (hfa _ (batName_notMem_scratchArrs j) (not_bbExt_batName j))
      (hfa _ (resName_notMem_scratchArrs j) (not_bbExt_resName j))
      (hfa _ (alvName_notMem_scratchArrs (j + 1)) (not_bbExt_alvName (j + 1)))
      (hfa _ (gamName_notMem_scratchArrs (j + 1)) (not_bbExt_gamName (j + 1)))
      (hfa _ (memName_notMem_scratchArrs (j + 1)) (not_bbExt_memName (j + 1)))
      (hfv _ (hVmm (j + 1)))
  · intro c hc
    rw [hfa _ (colName_notMem_scratchArrs (j + 1) c)
      (not_bbExt_colName (j + 1) c)]
    exact hcolarr c hc
  · intro i hi
    obtain ⟨Tb, hTb, hTb1, hTbS⟩ := htab i hi
    exact ⟨Tb, by rw [hfa _ (tabName_notMem_scratchArrs (j + 1) i)
      (not_bbExt_tabName (j + 1) i)]; exact hTb, hTb1, hTbS⟩

/-- The active dead-aware phase precondition. -/
def DeadPreA (B q q_top cap mb ns Ws ℓ j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    {n : ℕ} (G : SimpleGraph (Fin n)) (O T M Gm : ℕ → ℕ)
    (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre Xoff Xmem asg : ℕ → ℕ) (m : ℕ) (X W : Set (Fin n))
    (w : Fin mb → Fin n) (Alv' Gam' : ℕ → ℕ) (C' : ℕ → ℕ → ℕ)
    (σ : Env) : Prop :=
  ScatPreA (n := n) B q q_top cap mb ns Ws j φ G O T M Gm C π centre Xoff Xmem asg m
      X W w Alv' Gam' C' σ ∧
    KillListAt mb j M X W σ ∧ BaseArrs B q_top cap mb ℓ φ σ

theorem DeadPreA.run {c : Com} {σ σ' : Env} {K : ℕ}
    (h : DeadPreA (n := n) B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π centre Xoff Xmem asg m
      X W w Alv' Gam' C' σ)
    (hrun : Run B c σ σ' K)
    (hA : ∀ a ∈ c.warrs, a ∈ scratchArrs ∨ BbExt a)
    (hkl : klName j ∉ c.warrs)
    (hV : ∀ y ∈ ["n", "m", "lw"], y ∉ c.wvars)
    (hVctr : ∀ a : ℕ, ctrName a ∉ c.wvars) (hVxp : xpName j ∉ c.wvars)
    (hVmm : ∀ a : ℕ, mnumName a ∉ c.wvars) (hVkk : kkName j ∉ c.wvars) :
    DeadPreA (n := n) B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π centre Xoff Xmem asg m
      X W w Alv' Gam' C' σ' := by
  obtain ⟨hpre, ⟨kl, kq, hklA, hkkV, hkqmb, hkllt, hklinj, hklsnd, hklcmp⟩,
    hbarr⟩ := h
  exact ⟨hpre.run hrun hA hV hVctr hVxp hVmm,
    ⟨kl, kq, by rw [hrun.frame_arr _ hkl]; exact hklA,
      by rw [hrun.frame_var _ hVkk]; exact hkkV, hkqmb, hkllt, hklinj, hklsnd,
      hklcmp⟩, hbarr.run hrun⟩

theorem DeadPreA.run_scatDead {L ti : ℕ} {β : DistFO L 1} {r t : ℕ}
    {σ σ' : Env} {K : ℕ}
    (h : DeadPreA (n := n) B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π centre Xoff Xmem asg m
      X W w Alv' Gam' C' σ)
    (hloc : IsLocal β) (hrun : Run B (scatDeadCom j ti β r t) σ σ' K) :
    DeadPreA (n := n) B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π centre Xoff Xmem asg m
      X W w Alv' Gam' C' σ' := by
  refine h.run hrun (fun a ha => ?_) (fun ha => ?_) (fun y hy => ?_)
    (fun a => ?_) ?_ (fun a => ?_) ?_
  · rcases RamDriverWrites.warrs_scatDeadCom j ti β r t hloc ha with hm | hm
    · refine Or.inl ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [scratchArrs]
    · exact Or.inr hm
  · rcases RamDriverWrites.warrs_scatDeadCom j ti β r t hloc ha with hm | hm
    · revert hm
      simp [klName, String.ext_iff]
    · exact not_ext_bb_klName j hm
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl
    · exact notMem_wvars_scatDeadCom_lit hloc (by decide) (by decide)
        (not_ext_bb_short (by decide)) (fun k => by simp [envName, String.ext_iff])
    · exact notMem_wvars_scatDeadCom_lit hloc (by decide) (by decide)
        (not_ext_bb_short (by decide)) (fun k => by simp [envName, String.ext_iff])
    · exact notMem_wvars_scatDeadCom_lit hloc (by decide) (by decide)
        (not_ext_bb_of_cons rfl (by decide)) (fun k => by simp [envName, String.ext_iff])
  · exact notMem_wvars_scatDeadCom_lit hloc
      (RamDriverIO.notMem_of_append (p := "ctr") (s := toString a) (by decide))
      (RamDriverIO.notMem_of_append (p := "ctr") (s := toString a) (by decide))
      (not_ext_bb_ctrName a) (fun k => by simp [ctrName, envName, String.ext_iff])
  · exact notMem_wvars_scatDeadCom_lit hloc
      (RamDriverIO.notMem_of_append (p := "xq") (s := toString j) (by decide))
      (RamDriverIO.notMem_of_append (p := "xq") (s := toString j) (by decide))
      (not_ext_bb_xpName j) (fun k => by simp [xpName, envName, String.ext_iff])
  · exact notMem_wvars_scatDeadCom_lit hloc (by simp [mnumName, String.ext_iff])
      (by simp [mnumName, String.ext_iff]) (ScatterDeadTurn.not_ext_bb_mnumName a)
      (fun k => by simp [mnumName, envName, String.ext_iff])
  · exact notMem_wvars_scatDeadCom_lit hloc
      (RamDriverIO.notMem_of_append (p := "kq") (s := toString j) (by decide))
      (RamDriverIO.notMem_of_append (p := "kq") (s := toString j) (by decide))
      (not_ext_bb_kkName j) (fun k => by simp [kkName, envName, String.ext_iff])

theorem DeadPreA.run_flag {i k : ℕ} {σ σ' : Env} {K : ℕ}
    (h : DeadPreA (n := n) B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π centre Xoff Xmem asg m
      X W w Alv' Gam' C' σ)
    (hrun : Run B (.assign (flgName j i k) (.var "flag")) σ σ' K) :
    DeadPreA (n := n) B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π centre Xoff Xmem asg m
      X W w Alv' Gam' C' σ' := by
  have hne : ∀ {p : String}, '_' ∉ p.toList → ∀ a : ℕ,
      p ++ toString a ∉ (Com.assign (flgName j i k) (.var "flag")).wvars := by
    intro p hp a hm
    simp only [Com.wvars, List.mem_cons, List.not_mem_nil, or_false] at hm
    exact underscore_notMem_prefixed hp a (hm ▸ underscore_mem_flgName j i k)
  refine h.run hrun (fun a ha => absurd ha (by simp [Com.warrs]))
    (by simp [Com.warrs]) (fun y hy => ?_) (fun a => hne (by decide) a)
    (hne (by decide) j) (fun a => hne (by decide) a) (hne (by decide) j)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
  simp only [Com.wvars, List.mem_cons, List.not_mem_nil, or_false]
  rcases hy with rfl | rfl | rfl <;>
    exact flgName_ne_lit j i k (by decide) ∘ Eq.symm

/-- The active precondition exposes the same cover-independent view. -/
theorem DeadPreA.view
    (h : DeadPreA (n := n) B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π centre Xoff Xmem asg m
      X W w Alv' Gam' C' σ) :
    DeadView B q_top cap mb ns Ws ℓ j φ G O T M C X W w Alv' Gam' C' σ := by
  obtain ⟨hpre, hklist, hbarr⟩ := h
  exact
    { n_eq := hpre.n_eq
      off := hpre.off
      tgt := hpre.tgt
      mem := hpre.mem
      nsW := hpre.nsW
      data := hpre.data
      col_arr := hpre.2.2.1
      col_bit := hpre.2.2.2.1
      col_read := hpre.2.2.2.2.1
      table := hpre.2.2.2.2.2
      kill_list := hklist
      base_arrs := hbarr }

open Classical in
/-- One dead-aware scatter atom on the active-cover precondition. -/
theorem scatDeadSpecA {bw nb : ℕ}
    (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hXalive : ∀ v : Fin n, v ∈ X → M (v : ℕ) ≠ 0)
    (hbud : ∀ r : ℕ, ScatterBlock.BallBudget n r G Alv' O bw nb)
    {σs : ScatterSentence (sigL cap mb (j + 1))}
    (hβ : σs.β ∈ tablesAt q_top cap mb φ (j + 1)) (hloc : IsLocal σs.β)
    (hrB : σs.r + 1 < B) (htB : σs.t + n + mb < B)
    {Kb : ℕ} (hKb : ScatterDeadPass.scatDeadKX σs.β n X.ncard mb bw nb σs.t ≤ Kb) :
    Spec B (DeadPreA (n := n) B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π centre
        Xoff Xmem asg m X W w Alv' Gam' C')
      (scatDeadCom j (posOf σs.β (tablesAt q_top cap mb φ (j + 1))) σs.β σs.r σs.t)
      (fun σ σ' => DeadPreA (n := n) B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π
          centre Xoff Xmem asg m X W w Alv' Gam' C' σ' ∧ σ'.out = σ.out ∧
        σ'.vars (curName j) = σ.vars (curName j) ∧
        (∀ i' k', σ'.vars (flgName j i' k') = σ.vars (flgName j i' k')) ∧
        σ'.vars "flag" ≤ 1 ∧
        (σ'.vars "flag" ≠ 0 ↔ ScatVal (stepArenaP (masked G M) X w)
          (stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w) σs))
      Kb := by
  refine scatDead_specCore hcsr hB hXalive hbud hβ hloc hrB htB hKb
    (fun h => h.view) ?_
  intro σ σ' K h hr
  exact h.run_scatDead hloc hr

open Classical in
/-- One active-cover scatter atom and its stored flag. -/
theorem atomDeadSpecA {bw nb : ℕ}
    (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hXalive : ∀ v : Fin n, v ∈ X → M (v : ℕ) ≠ 0)
    (hbud : ∀ r : ℕ, ScatterBlock.BallBudget n r G Alv' O bw nb)
    (i k : ℕ) {σs : ScatterSentence (sigL cap mb (j + 1))}
    (hβ : σs.β ∈ tablesAt q_top cap mb φ (j + 1)) (hloc : IsLocal σs.β)
    (hrB : σs.r + 1 < B) (htB : σs.t + n + mb < B)
    {Kb : ℕ} (hKb : deadAtomKX σs.β n X.ncard mb bw nb σs.t ≤ Kb) :
    Spec B (DeadPreA (n := n) B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π centre
        Xoff Xmem asg m X W w Alv' Gam' C')
      (.seq (scatDeadCom j (posOf σs.β (tablesAt q_top cap mb φ (j + 1)))
          σs.β σs.r σs.t)
        (.assign (flgName j i k) (.var "flag")))
      (fun σ σ' => DeadPreA (n := n) B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π
          centre Xoff Xmem asg m X W w Alv' Gam' C' σ' ∧ σ'.out = σ.out ∧
        σ'.vars (curName j) = σ.vars (curName j) ∧
        (∀ i' k', ¬ (i' = i ∧ k' = k) →
          σ'.vars (flgName j i' k') = σ.vars (flgName j i' k')) ∧
        σ'.vars (flgName j i k) ≤ 1 ∧
        (σ'.vars (flgName j i k) ≠ 0 ↔ ScatVal (stepArenaP (masked G M) X w)
          (stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w) σs))
      Kb := by
  classical
  have hcur : curName j ≠ flgName j i k := fun h =>
    underscore_notMem_prefixed (p := "cu") (by decide) j
      (h ▸ (underscore_mem_flgName j i k : '_' ∈ (flgName j i k).toList) :
        '_' ∈ (curName j).toList)
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨τ, hrτ, hdead, hout, hcurτ, hflgfr, hfl1, hfliff⟩ :=
    (scatDeadSpecA hcsr hB hXalive hbud hβ hloc hrB htB (le_refl _)).run hσ
  have hflagB : τ.vars "flag" < B := lt_of_le_of_lt hfl1 hB.one_lt
  have r2 : Run B (.assign (flgName j i k) (.var "flag")) τ
      (τ.setVar (flgName j i k) (τ.vars "flag")) (1 + (Expr.var "flag").size) :=
    Run.assign (evalB_var hflagB)
  refine ⟨_, _, hrτ.seq r2, ?_, hdead.run_flag r2, ?_, ?_, ?_, ?_, ?_⟩
  · refine le_trans ?_ hKb
    rw [deadAtomKX]
    simp only [Expr.size]
    omega
  · rw [out_setVar]
    exact hout
  · rw [vars_setVar, if_neg hcur]
    exact hcurτ
  · intro i' k' hik
    rw [vars_setVar, if_neg (fun hc => hik (by
      obtain ⟨-, hi, hk⟩ := flgName_inj hc
      exact ⟨hi, hk⟩))]
    exact hflgfr i' k'
  · rw [vars_setVar, if_pos rfl]
    exact hfl1
  · rw [vars_setVar, if_pos rfl]
    exact hfliff

open Classical in
/-- The active-cover scatter atoms of one tabled formula. -/
theorem atomsDeadSpecA {bw nb : ℕ}
    (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hXalive : ∀ v : Fin n, v ∈ X → M (v : ℕ) ≠ 0)
    (hbud : ∀ r : ℕ, ScatterBlock.BallBudget n r G Alv' O bw nb)
    (i : ℕ) {Kb : ℕ} :
    ∀ (l : List (ScatterSentence (sigL cap mb (j + 1)))) (k0 : ℕ),
      (∀ σs ∈ l, σs.β ∈ tablesAt q_top cap mb φ (j + 1) ∧ σs.r + 1 < B ∧
        σs.t + n + mb < B ∧ deadAtomKX σs.β n X.ncard mb bw nb σs.t ≤ Kb) →
      Spec B (DeadPreA (n := n) B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π centre
          Xoff Xmem asg m X W w Alv' Gam' C')
        (foldIdx (fun k σs =>
            Com.seq (scatDeadCom j (posOf σs.β (tablesAt q_top cap mb φ (j + 1)))
              σs.β σs.r σs.t) (.assign (flgName j i k) (.var "flag"))) k0 l)
        (fun σ σ' => DeadPreA (n := n) B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π
            centre Xoff Xmem asg m X W w Alv' Gam' C' σ' ∧ σ'.out = σ.out ∧
          σ'.vars (curName j) = σ.vars (curName j) ∧
          (∀ i' k', (i' ≠ i ∨ ∀ p < l.length, k' ≠ k0 + p) →
            σ'.vars (flgName j i' k') = σ.vars (flgName j i' k')) ∧
          ∀ p, ∀ _ : p < l.length,
            σ'.vars (flgName j i (k0 + p)) ≤ 1 ∧
            (σ'.vars (flgName j i (k0 + p)) ≠ 0 ↔
              ScatVal (stepArenaP (masked G M) X w)
                (stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w) l[p]))
        (Kb * l.length + 1) := by
  intro l
  induction l with
  | nil =>
      intro k0 _
      refine (Spec.skip (B := B) (P := DeadPreA (n := n) B q q_top cap mb ns Ws ℓ j φ G
        O T M Gm C π centre Xoff Xmem asg m X W w Alv' Gam' C')).post ?_ |>.mono (by simp)
      rintro σ σ' hσ rfl
      exact ⟨hσ, rfl, rfl, fun _ _ _ => rfl, fun p hp => absurd hp (by simp)⟩
  | cons x xs ih =>
      intro k0 hall
      obtain ⟨hxβ, hxr, hxt, hxK⟩ := hall x (by simp)
      refine ((atomDeadSpecA hcsr hB hXalive hbud i k0 hxβ
        (tableRank_of_mem_tablesAt (j + 1) _ hxβ).1 hxr hxt hxK).seq
        (ih (k0 + 1) (fun s hs => hall s (by simp [hs]))) (fun _ _ _ hq => hq.1) ?_).mono
        (by simp [Nat.mul_succ]; omega)
      rintro σ σ' σ'' - ⟨-, hout', hc', hfl', hle', hval'⟩
        ⟨hpre'', hout'', hc'', hfl'', hval''⟩
      refine ⟨hpre'', by rw [hout'', hout'], by rw [hc'', hc'], ?_, ?_⟩
      · intro i' k' hik
        rw [hfl'' i' k' ?_, hfl' i' k' ?_]
        · rcases hik with h | h
          · exact fun hc => h hc.1
          · exact fun hc => h 0 (by simp) (by omega)
        · rcases hik with h | h
          · exact _root_.Or.inl h
          · exact _root_.Or.inr fun p hp => by
              have := h (p + 1) (by simp only [List.length_cons]; omega)
              omega
      · intro p hp
        match p with
        | 0 =>
            rw [Nat.add_zero, hfl'' i k0 (_root_.Or.inr fun p _ => by omega)]
            exact ⟨hle', hval'⟩
        | r + 1 =>
            rw [show k0 + (r + 1) = k0 + 1 + r from by omega]
            simpa using hval'' r (by simpa using hp)

set_option maxHeartbeats 1000000 in
open Classical in
/-- The complete active-cover scatter fold over a depth's table. -/
theorem blocksDeadSpecA {bw nb : ℕ}
    (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hXalive : ∀ v : Fin n, v ∈ X → M (v : ℕ) ≠ 0)
    (hbud : ∀ r : ℕ, ScatterBlock.BallBudget n r G Alv' O bw nb)
    {Kb Ki : ℕ} :
    ∀ (l : List (DistFO (sigL cap mb j) 1)) (i0 : ℕ),
      (∀ β ∈ l, β ∈ tablesAt q_top cap mb φ j) →
      (∀ β ∈ l, ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t + n + mb < B ∧
          deadAtomKX σs.β n X.ncard mb bw nb σs.t ≤ Kb) →
      (∀ β ∈ l, Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki) →
      Spec B (DeadPreA (n := n) B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π centre
          Xoff Xmem asg m X W w Alv' Gam' C')
        (foldIdx (fun i β => scatterDeadCom q_top cap mb φ j i β) i0 l)
        (fun σ σ' => DeadPreA (n := n) B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π
            centre Xoff Xmem asg m X W w Alv' Gam' C' σ' ∧ σ'.out = σ.out ∧
          σ'.vars (curName j) = σ.vars (curName j) ∧
          (∀ i' k', (∀ p < l.length, i' ≠ i0 + p) →
            σ'.vars (flgName j i' k') = σ.vars (flgName j i' k')) ∧
          ∀ p, ∀ hp : p < l.length,
            ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j l[p])).2,
              σ'.vars (flgName j (i0 + p)
                  (posOf σs (bcAtomsOf q_top (stepFml cap mb j l[p])).2)) ≤ 1 ∧
              (σ'.vars (flgName j (i0 + p)
                  (posOf σs (bcAtomsOf q_top (stepFml cap mb j l[p])).2)) ≠ 0 ↔
                ScatVal (stepArenaP (masked G M) X w)
                  (stepColoringP cap (masked G M) (colRead n C (sigL cap mb j)) X w) σs))
        (Ki * l.length + 1) := by
  intro l
  induction l with
  | nil =>
      intro i0 _ _ _
      refine (Spec.skip (B := B) (P := DeadPreA (n := n) B q q_top cap mb ns Ws ℓ j φ G
        O T M Gm C π centre Xoff Xmem asg m X W w Alv' Gam' C')).post ?_ |>.mono (by simp)
      rintro σ σ' hσ rfl
      exact ⟨hσ, rfl, rfl, fun _ _ _ => rfl, fun p hp => absurd hp (by simp)⟩
  | cons x xs ih =>
      intro i0 hmem hbnd hcost
      have hx : x ∈ tablesAt q_top cap mb φ j := hmem x (by simp)
      refine (((atomsDeadSpecA hcsr hB hXalive hbud i0
          (bcAtomsOf q_top (stepFml cap mb j x)).2 0
          (fun s hs => ⟨mem_tablesAt_succ_of_mem_bcAtomsOf_right hx hs,
            (hbnd x (by simp) s hs).1, (hbnd x (by simp) s hs).2.1,
            (hbnd x (by simp) s hs).2.2⟩)).mono (hcost x (by simp))).seq
        (ih (i0 + 1) (fun β hβ => hmem β (by simp [hβ]))
          (fun β hβ => hbnd β (by simp [hβ])) (fun β hβ => hcost β (by simp [hβ])))
        (fun _ _ _ hq => hq.1) ?_).mono (by simp [Nat.mul_succ]; omega)
      rintro σ σ' σ'' - ⟨-, hout', hc', hfl', hval'⟩
        ⟨hpre'', hout'', hc'', hfl'', hval''⟩
      refine ⟨hpre'', by rw [hout'', hout'], by rw [hc'', hc'], ?_, ?_⟩
      · intro i' k' hik
        rw [hfl'' i' k' (fun p hp => by
            have := hik (p + 1) (by simp only [List.length_cons]; omega)
            omega),
          hfl' i' k' (_root_.Or.inl (by have := hik 0 (by simp); omega))]
      · intro p hp
        match p with
        | 0 =>
            intro σs hσs
            simp only [List.getElem_cons_zero] at hσs ⊢
            obtain ⟨hlt, hget⟩ := getElem_posOf hσs
            have hb := hval' (posOf σs (bcAtomsOf q_top (stepFml cap mb j x)).2) hlt
            rw [Nat.zero_add, hget] at hb
            rw [Nat.add_zero, hfl'' i0 _ (fun p _ => by omega)]
            exact hb
        | r + 1 =>
            intro σs hσs
            rw [show i0 + (r + 1) = i0 + 1 + r from by omega]
            exact hval'' r (by simpa using hp) σs (by simpa using hσs)

open Classical in
/-- The complete landed dead-aware scatter phase at the active interface. -/
theorem scatterStepA {bw nb Kb Ki K : ℕ}
    (hcsr : CsrGraph G ns O T) {d : ℕ} (hB : WordBoundK B n d ns cap mb)
    (hbnd : ∀ β ∈ tablesAt q_top cap mb φ j,
      ∀ σs ∈ (bcAtomsOf q_top (stepFml cap mb j β)).2,
        σs.r + 1 < B ∧ σs.t + n + mb < B ∧
          deadAtomKX σs.β n X.ncard mb bw nb σs.t ≤ Kb)
    (hcost : ∀ β ∈ tablesAt q_top cap mb φ j,
      Kb * (bcAtomsOf q_top (stepFml cap mb j β)).2.length + 1 ≤ Ki)
    (hK : Ki * (tablesAt q_top cap mb φ j).length + 1 ≤ K) :
    ScatterStepA B q q_top cap mb ns Ws ℓ j φ G O T M Gm C π centre Xoff Xmem asg m
      X W w Alv' Gam' C' bw nb K := by
  intro hXalive hbud
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hturn, hdata, hcolarr, hcolbit, hcolread, htab, hklist, hbarr⟩ := hσ
  obtain ⟨σ', hrun, hpre', hout, hc, -, hval⟩ :=
    (blocksDeadSpecA hcsr hB hXalive hbud (tablesAt q_top cap mb φ j) 0
      (fun _ hβ => hβ) hbnd hcost).run
      ⟨⟨hturn, hdata, hcolarr, hcolbit, hcolread, htab⟩, hklist, hbarr⟩
  exact ⟨σ', _, hrun, hK, hpre'.1.1, hpre'.1.2.1, hpre'.1.2.2.1,
    hpre'.1.2.2.2.2.2, hout, hc,
    fun i hi σs hσs => by simpa using hval i hi σs hσs⟩

end Lax3Proofs.RamDriverMemberPhases
