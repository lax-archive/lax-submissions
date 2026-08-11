import Lax3Proofs.RamDriverMember

/-!
# The active-cover level induction

This is the level composition for `RamDriverMember.driverAtA`.  It is
separate from the landed carrier proof so that the member-driven order
and cover phases can be developed and reviewed without destabilising
that regression path.
-/

namespace Lax3Proofs.RamDriverClusterMember

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3.SplitterGame
open Lax12.UniformQuasiWideness
open Lax3Proofs.FormulaTables Lax3Proofs.WalkDistance
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster
open Lax3Proofs.RamDriverMember
open Lax13Proofs.Imp Lax13Proofs.Reasoning

variable {B n q cap mb ns W j : ℕ} {G : SimpleGraph (Fin n)}
variable {O T M Gm centre Xoff Xmem asg : ℕ → ℕ} {π : Equiv.Perm (Fin n)}
variable {C : ℕ → ℕ → ℕ} {m : ℕ} {σ : Env}

/-- Updating an unrelated scalar preserves the active cover. -/
theorem coverHeld_setVar
    (h : CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg m σ)
    (x : String) (hx : x ≠ xpName j) (k : ℕ) :
    CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg m (σ.setVar x k) :=
  { centre_arr := by simpa using h.centre_arr
    off_arr := by simpa using h.off_arr
    mem_arr := by simpa using h.mem_arr
    asg_arr := by simpa using h.asg_arr
    pointer := by rw [vars_setVar, if_neg (Ne.symm hx)]; exact h.pointer
    alloc := h.alloc
    pointer_lt := h.pointer_lt
    centre_lt := h.centre_lt
    cover := h.cover }

theorem coverHeld_setVar_c
    (h : CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg m σ) (k : ℕ) :
    CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg m
      (σ.setVar (curName j) k) :=
  coverHeld_setVar h _ (curName_ne_xpName j j) k

theorem coverHeld_setVar_ci
    (h : CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg m σ) (k : ℕ) :
    CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg m
      (σ.setVar (cixName j) k) :=
  coverHeld_setVar h _ (cixName_ne_xpName j j) k

open Classical in
/-- One active-cover level, discharged from its two phase contracts and
its cluster-turn contracts. -/
theorem levelImplementsA
    {B q_top cap mb ℓ W ns : ℕ} {N : ℕ → ℕ} {s : ℕ}
    {φ : Lax3.FirstOrder.FO 0}
    {G : SimpleGraph (Fin n)} {O T : ℕ → ℕ}
    {orderPhase coverPhase : ℕ → Com}
    {P : ℕ → Equiv.Perm (Fin n) → (ℕ → ℕ) → Prop}
    {wA : (ℕ → ℕ) → ℕ} {wB : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ}
    {Ko Kc Ks Ksf Kl : ℕ → ℕ → ℕ} {Kmass : ℕ}
    (hnB : n < B)
    (hQ : ∀ Pt : Set (Fin n), N (2 * s + 2) ≤ Pt.ncard →
      ∃ S Bd : Set (Fin n), S.ncard ≤ s ∧ Bd ⊆ Pt \ S ∧ 2 * s + 2 ≤ Bd.ncard ∧
        DistIndependent (deleteVerts G S) (2 * cap) Bd)
    (hℓ : ℓ = N (2 * s + 2))
    (hbase : ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (D : Set (Fin n)),
      masked G M = ⊥ →
      LevelImplementsDA B q_top cap mb ℓ W ns ℓ φ G O T M Gm C D
        orderPhase coverPhase (Kl ℓ (wA M)))
    (horder : ∀ (j : ℕ), j < ℓ → ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ),
      OrderImplementsA B n W cap mb ns j O T M Gm C P (orderPhase j) (Ko j (wA M)))
    (hcover : ∀ (j : ℕ), j < ℓ → ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
        (q : ℕ) (π : Equiv.Perm (Fin n)) (centre : ℕ → ℕ),
      CoverImplementsA B n q cap mb ns W j G O T M Gm C π centre (coverPhase j)
        (Kc j (wA M)))
    (hstep : ∀ (j : ℕ), j < ℓ → ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
        (q : ℕ) (π : Equiv.Perm (Fin n)) (centre Xoff Xmem asg : ℕ → ℕ)
        (mm k : ℕ),
      ClusterStepImplementsA B q_top cap mb ns W ℓ j φ G O T M Gm C q π centre
        Xoff Xmem asg mm k wA
        (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1)) (Kl (j + 1))
        (Ks j (wB Xoff Xmem k)))
    (hframe : ∀ (j : ℕ), j < ℓ → ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
        (q : ℕ) (π : Equiv.Perm (Fin n)) (centre Xoff Xmem asg : ℕ → ℕ)
        (mm k : ℕ),
      ClusterFramesA B q_top cap mb ns W ℓ j φ G O T M Gm C q π centre
        Xoff Xmem asg mm k wA
        (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1)) (Kl (j + 1))
        (Ksf j (wB Xoff Xmem k)))
    (hloopfr : ∀ (j : ℕ), j < ℓ →
      cpsName j ∉ (clusterCom q_top cap mb φ j
          (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1))).warrs ∧
        cnumName j ∉ (clusterCom q_top cap mb φ j
          (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1))).wvars ∧
        cixName j ∉ (clusterCom q_top cap mb φ j
          (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1))).wvars)
    (hphfr : ∀ (jd i : ℕ), tabName jd i ∉ (orderPhase jd).warrs ∧
      tabName jd i ∉ (coverPhase jd).warrs)
    (hmass : ∀ (M : ℕ → ℕ) (q : ℕ) (π : Equiv.Perm (Fin n))
        (centre Xoff Xmem asg cps : ℕ → ℕ) (mm cnum : ℕ),
      P q π centre → RamCover.CoverOutA G M π centre cap q mm Xoff Xmem asg →
      Compacted q cnum mm M centre Xoff cps →
      cnum ≤ wA M ∧
        (∑ k ∈ Finset.range cnum, wB Xoff Xmem (cps k)) ≤ Kmass * (wA M + 1))
    (hK : ∀ (j : ℕ), j < ℓ → ∀ m t : ℕ, t ≤ m → ∀ bs : ℕ → ℕ,
      (∑ c ∈ Finset.range t, bs c) ≤ Kmass * (m + 1) →
      Ko j m + (Kc j m + ((∑ c ∈ Finset.range t, (Ks j (bs c) + 11)) + 6))
        ≤ Kl j m) :
    ∀ (j : ℕ), j ≤ ℓ → ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (D : Set (Fin n)),
      LevelImplementsDA B q_top cap mb ℓ W ns j φ G O T M Gm C D
        orderPhase coverPhase (Kl j (wA M)) := by
  classical
  have key : ∀ (f j : ℕ), ℓ - j = f → j ≤ ℓ →
      ∀ (M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (D : Set (Fin n)),
      LevelImplementsDA B q_top cap mb ℓ W ns j φ G O T M Gm C D
        orderPhase coverPhase (Kl j (wA M)) := by
    intro f
    induction f with
    | zero =>
      intro j hf hj M Gm C D hDdead hbit
      have hje : j = ℓ := by omega
      subst hje
      intro σ hσ
      have hbot : masked G M = ⊥ :=
        eq_bot_of_playOk_full hQ
          (by rw [← hℓ]; exact playOk_of_playRec hσ.2.2.2.1)
      exact hbase M Gm C D hbot hDdead hbit σ hσ
    | succ f ih =>
      intro j hf hj M Gm C D hDdead hbit
      have hjl : j < ℓ := by omega
      have hinner : ∀ (M' Gm' : ℕ → ℕ) (C' : ℕ → ℕ → ℕ) (D' : Set (Fin n)),
          (∀ v : Fin n, v ∈ D' → M' (v : ℕ) = 0) →
          (∀ c < sigL cap mb (j + 1), ∀ v < n, C' c v ≤ 1) →
          Spec B (fun σ => LevelPre B n cap mb ns W O T (j + 1) M' Gm' C' σ ∧
              TablesSized q_top cap mb φ n σ ∧ BaseArrs B q_top cap mb ℓ φ σ ∧
              PlayRec B cap G (j + 1) M' Gm' σ ∧
              TableInvOn q_top cap mb φ G (j + 1) M' C' D' σ)
            (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1))
            (fun σ σ' => LevelPostD B q_top cap mb φ G ns W O T (j + 1) M' Gm' C' D'
                σ σ' ∧ σ'.out = σ.out)
            (Kl (j + 1) (wA M')) :=
        fun M' Gm' C' D' hD' hb' => ih (j + 1) (by omega) (by omega)
          M' Gm' C' D' hD' hb'
      refine Spec.of_exists fun σ hσ => ?_
      rw [driverAtA_succ q_top cap mb ℓ φ orderPhase coverPhase hjl]
      obtain ⟨σ₁, hr₁, hlev₁, hout₁, hctr₁, hres₁, hgam₁, hpar₁, q, π, centre,
          hqn, hcentre₁, hcentrelt, hP⟩ := (horder j hjl M Gm C).run hσ.1
      have htsz₁ : TablesSized q_top cap mb φ n σ₁ := hσ.2.1.run hr₁
      have hbarr₁ : BaseArrs B q_top cap mb ℓ φ σ₁ := hσ.2.2.1.run hr₁
      have hplay₁ : PlayRec B cap G j M Gm σ₁ :=
        hσ.2.2.2.1.congr (fun a _ => hctr₁ a)
          (fun a _ => hres₁ a)
          (fun a _ => hgam₁ a)
          (fun a _ => hpar₁ a)
      obtain ⟨σ₂, hr₂, hlev₂, hout₂, hctr₂, hres₂, hgam₂, hpar₂,
          Xoff, Xmem, asg, cps, mm, cnum,
          hheld₂, hcps₂, hcnum₂, hcomp₂⟩ :=
        (hcover j hjl M Gm C q π centre).run ⟨hlev₁, hcentre₁, hcentrelt⟩
      have htsz₂ : TablesSized q_top cap mb φ n σ₂ := htsz₁.run hr₂
      have hbarr₂ : BaseArrs B q_top cap mb ℓ φ σ₂ := hbarr₁.run hr₂
      have hplay₂ : PlayRec B cap G j M Gm σ₂ :=
        hplay₁.congr (fun a _ => hctr₂ a)
          (fun a _ => hres₂ a)
          (fun a _ => hgam₂ a)
          (fun a _ => hpar₂ a)
      have hcnB : cnum < B :=
        lt_of_le_of_lt (hcomp₂.le_carrier.trans hheld₂.cover.count_le) hnB
      have hdead₂ : ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length)
          (Tb : ℕ → ℕ), σ₂.arrs (tabName j i) = arrOf n Tb →
          ∀ v : Fin n, v ∈ D →
            Tb (v : ℕ) ≤ 1 ∧
            (Tb (v : ℕ) ≠ 0 ↔ Sat (masked G M) (colRead n C (sigL cap mb j))
              (fun _ => v) (tablesAt q_top cap mb φ j)[i]) := by
        intro i hi Tb harr v hv
        obtain ⟨Tb₀, harr₀, hbit₀, hval₀⟩ := hσ.2.2.2.2 i hi
        have hfr : σ₂.arrs (tabName j i) = σ.arrs (tabName j i) := by
          rw [hr₂.frame_arr _ (hphfr j i).2, hr₁.frame_arr _ (hphfr j i).1]
        have heq := eq_of_arrOf_eq ((harr.symm.trans hfr).trans harr₀) v.isLt
        rw [heq]
        exact ⟨hbit₀ v hv, hval₀ v hv⟩
      have hasgcps : ∀ v < n, M v ≠ 0 → ∃ k < cnum, asg v = cps k := by
        intro v hv hal
        have hlt : asg v < q := hheld₂.cover.asg_lt v hv hal
        have hself : RamCover.InCluster (masked G M) π cap (centre (asg v)) v :=
          hheld₂.cover.asg_cover v hv hal (mem_ball_self _ _ _)
        obtain ⟨p, hp₁, hp₂, -⟩ := (hheld₂.cover.block (asg v) hlt v).mpr hself
        obtain ⟨k, hk, hkc⟩ := hcomp₂.covers (asg v) hlt (by omega)
          ((Refine.MassAlive.inCluster_alive_iff hself).mp hal)
        exact ⟨k, hk, hkc.symm⟩
      obtain ⟨hfrA, hfrQ, hfrI⟩ := hloopfr j hjl
      have hbody : ∀ kk : ℕ, kk < cnum → Spec B
          (fun τ => LevelInvA B q_top cap mb ns W ℓ j φ G O T M Gm C q π centre
              Xoff Xmem asg cps mm cnum D σ₂.out τ ∧ τ.vars (cixName j) = kk)
          (.seq (.assign (curName j) (.get (cpsName j) (.var (cixName j))))
            (.seq (clusterCom q_top cap mb φ j
                (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1)))
              (.assign (cixName j) (.add (.var (cixName j)) (.lit 1)))))
          (fun _ τ' => LevelInvA B q_top cap mb ns W ℓ j φ G O T M Gm C q π centre
              Xoff Xmem asg cps mm cnum D σ₂.out τ' ∧
            τ'.vars (cixName j) = kk + 1)
          (Ks j (wB Xoff Xmem (cps kk)) + 7) := by
        intro kk hkk
        have hpos : cps kk < q := hcomp₂.lt _ hkk
        have hcl : Spec B (fun τ => LevelPre B n cap mb ns W O T j M Gm C τ ∧
              TablesSized q_top cap mb φ n τ ∧ BaseArrs B q_top cap mb ℓ φ τ ∧
              PlayRec B cap G j M Gm τ ∧
              CoverHeldAtA B n q j G M π centre cap Xoff Xmem asg mm τ ∧
              τ.vars (curName j) = cps kk)
            (clusterCom q_top cap mb φ j
              (driverAtA q_top cap mb ℓ φ orderPhase coverPhase (j + 1))) _
            (Ks j (wB Xoff Xmem (cps kk))) :=
          spec_conj
            (hstep j hjl M Gm C q π centre Xoff Xmem asg mm (cps kk) hpos
              (hcomp₂.alive kk hkk) hbit hinner)
            (hframe j hjl M Gm C q π centre Xoff Xmem asg mm (cps kk) hpos
              (hcomp₂.alive kk hkk) hinner)
        refine Spec.of_exists fun τ hτ => ?_
        obtain ⟨⟨hlevτ, htszτ, hbarrτ, hplayτ, hheldτ, hcpsτ, hcnumτ, houtτ, -, htabτ⟩,
          hcix⟩ := hτ
        have hcixlt : τ.vars (cixName j) < cnum := by rw [hcix]; exact hkk
        have hcixB : τ.vars (cixName j) < B := by omega
        have hposτ : cps (τ.vars (cixName j)) < q := by rw [hcix]; exact hpos
        have hread : Run B (.assign (curName j) (.get (cpsName j) (.var (cixName j)))) τ
            (τ.setVar (curName j) (cps (τ.vars (cixName j)))) 3 := by
          have h := Run.assign (B := B) (σ := τ) (x := curName j)
            (e := .get (cpsName j) (.var (cixName j)))
            (evalB_get (evalB_var hcixB)
              (by
                rw [hcpsτ]
                exact getElem?_arrOf cps
                  (lt_of_lt_of_le hcixlt (hcomp₂.le_carrier.trans hqn)))
              (lt_trans hposτ (lt_of_le_of_lt hqn hnB)))
          simpa using h
        set τ₁ := τ.setVar (curName j) (cps (τ.vars (cixName j))) with hτ₁
        have hcur₁ : τ₁.vars (curName j) = cps (τ.vars (cixName j)) := by
          rw [hτ₁, vars_setVar, if_pos rfl]
        obtain ⟨τ₂, hr, ⟨⟨hlev', htsz', hbarr', hplay', hout', hc', htab'⟩,
            hheld', hfr'⟩, hfv, hfa, -, -⟩ :=
          (hcl.frame).run (σ := τ₁)
            ⟨levelPre_setVar_c hlevτ _, tablesSized_setVar_c htszτ _ _,
              baseArrs_setVar_c hbarrτ _ _, playRec_setVar_c hplayτ _,
              coverHeld_setVar_c hheldτ _, by rw [hcur₁, hcix]⟩
        have hcix₂ : τ₂.vars (cixName j) = τ.vars (cixName j) := by
          rw [hfv _ hfrI, hτ₁, vars_setVar, if_neg (cixName_ne_curName j j)]
        have hbump : Run B (.assign (cixName j) (.add (.var (cixName j)) (.lit 1))) τ₂
            (τ₂.setVar (cixName j) (τ.vars (cixName j) + 1)) 4 := by
          have h := Run.assign (B := B) (σ := τ₂) (x := cixName j)
            (e := .add (.var (cixName j)) (.lit 1))
            (evalB_bin (evalB_var (by rw [hcix₂]; exact hcixB)) (evalB_lit (by omega))
              (by simp only [Bop.apply_add, hcix₂]; omega))
          rw [Bop.apply_add, hcix₂] at h
          simpa using h
        refine ⟨τ₂.setVar (cixName j) (τ.vars (cixName j) + 1), _,
          hread.seq (hr.seq hbump), by omega, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
        · exact levelPre_setVar_ci hlev' _
        · exact tablesSized_setVar_c htsz' _ _
        · exact baseArrs_setVar_c hbarr' _ _
        · exact playRec_setVar_ci hplay' _
        · exact coverHeld_setVar_ci hheld' _
        · rw [arrs_setVar, hfa _ hfrA, hτ₁, arrs_setVar]; exact hcpsτ
        · rw [vars_setVar, if_neg (Ne.symm (cixName_ne_cnumName j j)), hfv _ hfrQ, hτ₁,
            vars_setVar, if_neg (cnumName_ne_curName j j)]
          exact hcnumτ
        · rw [out_setVar, hout', hτ₁, out_setVar]; exact houtτ
        · rw [vars_setVar, if_pos rfl]; omega
        · intro i hi Tb harr v hv
          rw [vars_setVar, if_pos rfl] at hv
          rw [arrs_setVar] at harr
          obtain ⟨Tb', harr', hcorr'⟩ := htab' i hi
          have hTb : Tb (v : ℕ) = Tb' (v : ℕ) :=
            eq_of_arrOf_eq (harr.symm.trans harr') v.isLt
          rcases hv with hdv | ⟨k, hk, hkv⟩
          · obtain ⟨Tb₀, harr₀⟩ := htszτ.get j hi
            have hdead : M (v : ℕ) = 0 := hDdead v hdv
            have hsame := hfr' i hi Tb' Tb₀ harr'
              (by rw [hτ₁, arrs_setVar]; exact harr₀) v (Or.inl hdead)
            rw [hTb, hsame]
            exact htabτ i hi Tb₀ harr₀ v (Or.inl hdv)
          · rcases Nat.lt_or_ge k (τ.vars (cixName j)) with hlt | hge
            · obtain ⟨Tb₀, harr₀⟩ := htszτ.get j hi
              have hne : asg (v : ℕ) ≠ τ₁.vars (curName j) := by
                rw [hcur₁, hkv]
                exact fun he => absurd (hcomp₂.inj (by omega) hcixlt he) (by omega)
              have hsame := hfr' i hi Tb' Tb₀ harr'
                (by rw [hτ₁, arrs_setVar]; exact harr₀) v (Or.inr hne)
              rw [hTb, hsame]
              exact htabτ i hi Tb₀ harr₀ v (Or.inr ⟨k, hlt, hkv⟩)
            · have hkeq : k = τ.vars (cixName j) := by omega
              rw [hTb]
              exact hcorr' v (by rw [hcur₁, hkv, hkeq])
        · rw [vars_setVar, if_pos rfl]; omega
      obtain ⟨σ₄, hr₄, hI₄, hcn₄⟩ :=
        (Refine.SigmaLoop.forRangeZeroSum (cixName j) (cnumName j)
          (LevelInvA B q_top cap mb ns W ℓ j φ G O T M Gm C q π centre Xoff Xmem
            asg cps mm cnum D σ₂.out) cnum
          (fun kk => Ks j (wB Xoff Xmem (cps kk)) + 7) hcnB
          (fun _ hτ => hτ.2.2.2.2.2.2.2.2.1) (fun _ hτ => hτ.2.2.2.2.2.2.1)
          hbody).run (σ := σ₂)
          ⟨levelPre_setVar_ci hlev₂ 0, tablesSized_setVar_c htsz₂ _ 0,
            baseArrs_setVar_c hbarr₂ _ 0, playRec_setVar_ci hplay₂ 0,
            coverHeld_setVar_ci hheld₂ 0, by simpa using hcps₂,
            by rw [vars_setVar, if_neg (Ne.symm (cixName_ne_cnumName j j))]; exact hcnum₂,
            by simp, by simp, by
              intro i hi Tb harr v hv
              rw [arrs_setVar] at harr
              rcases hv with hdv | ⟨k, hk, -⟩
              · exact hdead₂ i hi Tb harr v hdv
              · rw [vars_setVar, if_pos rfl] at hk; omega⟩
      have htabinv : TableInvOn q_top cap mb φ G j M C
          ({v : Fin n | M (v : ℕ) ≠ 0} ∪ D) σ₄ := by
        intro i hi
        obtain ⟨Tb, harr⟩ := hI₄.2.1.get j hi
        have hrow : ∀ v : Fin n, v ∈ ({v : Fin n | M (v : ℕ) ≠ 0} ∪ D) →
            Tb (v : ℕ) ≤ 1 ∧
            (Tb (v : ℕ) ≠ 0 ↔ Sat (masked G M) (colRead n C (sigL cap mb j))
              (fun _ => v) (tablesAt q_top cap mb φ j)[i]) := by
          rintro v (hal | hdv)
          · obtain ⟨k, hk, hkv⟩ := hasgcps (v : ℕ) v.isLt hal
            exact hI₄.2.2.2.2.2.2.2.2.2 i hi Tb harr v
              (Or.inr ⟨k, by rw [hcn₄]; exact hk, hkv⟩)
          · exact hI₄.2.2.2.2.2.2.2.2.2 i hi Tb harr v (Or.inl hdv)
        exact ⟨Tb, harr, fun v hv => (hrow v hv).1, fun v hv => (hrow v hv).2⟩
      obtain ⟨hturns, hbs⟩ := hmass M q π centre Xoff Xmem asg cps mm cnum
        hP hheld₂.cover hcomp₂
      have hsum : (∑ kk ∈ Finset.range cnum,
          (Ks j (wB Xoff Xmem (cps kk)) + 7 + 4)) =
          ∑ kk ∈ Finset.range cnum, (Ks j (wB Xoff Xmem (cps kk)) + 11) :=
        Finset.sum_congr rfl fun _ _ => by omega
      have hcost : Ko j (wA M) + (Kc j (wA M) +
            ((∑ kk ∈ Finset.range cnum, (Ks j (wB Xoff Xmem (cps kk)) + 11)) + 6))
          ≤ Kl j (wA M) :=
        hK j hjl (wA M) cnum hturns (fun c => wB Xoff Xmem (cps c)) hbs
      refine ⟨σ₄, _, hr₁.seq (hr₂.seq hr₄), ?_,
        ⟨hI₄.1, hI₄.2.1, htabinv⟩,
        by rw [hI₄.2.2.2.2.2.2.2.1, hout₂, hout₁]⟩
      rw [hsum]
      omega
  exact fun j hj => key (ℓ - j) j rfl hj

end Lax3Proofs.RamDriverClusterMember
