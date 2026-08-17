import Lax3Proofs.Refine.CoverActiveNamed

/-!
# Member-priced initialization of the active cover

The active cover must not clear or copy a carrier-wide scratch array at
every recursive level.  `OrderMem` already hands a level the all-zero
`elm` array.  This walk visits the active ordering prefix only and, at
each live centre, installs the ambient mask value, the clean distance
sentinel, and the active assignment sentinel.  The cover loop consumes
all of those entries and leaves `elm` zero again.
-/

namespace Lax3Proofs.Refine.CoverActiveInit

open Lax3.ColoredGraphs
open Lax3Proofs.RamDriver (alvName mnumName ordName)
open Lax3Proofs.RamCoverActive
open Lax3Proofs.Refine.BfsBlockMask (CleanOn DistClean)
open Lax3Proofs.Refine.CoverActiveNamed
open Lax3Proofs.Refine.CoverActiveLoop
open Lax3Proofs.Refine.CoverActiveTurn
open Lax3Proofs.Refine.CoverBlock
open Lax3Proofs.Refine.ScatterBlock (renEnv)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ## Program and cost -/

/-- The mask represented by the first `i` active centres. -/
def prefixMask (A₀ centre : ℕ → ℕ) (i : ℕ) : ℕ → ℕ := fun z =>
  if ∃ k < i, centre k = z then A₀ z else 0

@[simp] theorem prefixMask_zero (A₀ centre : ℕ → ℕ) :
    prefixMask A₀ centre 0 = fun _ => 0 := by
  funext z
  simp [prefixMask]

theorem prefixMask_succ (A₀ centre : ℕ → ℕ) (i : ℕ) :
    upd (prefixMask A₀ centre i) (centre i) (A₀ (centre i)) =
      prefixMask A₀ centre (i + 1) := by
  funext z
  by_cases hz : z = centre i
  · subst z
    rw [upd_self, prefixMask, if_pos]
    exact ⟨i, by omega, rfl⟩
  · rw [upd_of_ne _ hz]
    simp only [prefixMask]
    by_cases hpre : ∃ k < i, centre k = z
    · rw [if_pos hpre, if_pos]
      exact ⟨hpre.choose, by omega, hpre.choose_spec.2⟩
    · rw [if_neg hpre, if_neg]
      rintro ⟨k, hk, hcentre⟩
      have hki : k = i ∨ k < i := by omega
      rcases hki with rfl | hki
      · exact hz hcentre.symm
      · exact hpre ⟨k, hki, hcentre⟩

/-- Initialize one live centre. -/
def activeInitTurn (j r : ℕ) : Com :=
  .seq (.assign "acs" (.get (ordName j) (.var "aci")))
    (.seq (.assign "acv" (.get (alvName j) (.var "acs")))
      (.seq (.store "elm" (.var "acs") (.var "acv"))
        (.seq (.store "dist" (.var "acs") (.lit (2 * r + 1)))
          (.seq (.store "asg" (.var "acs") (.var "qn"))
            (.assign "aci" (.add (.var "aci") (.lit 1)))))))

/-- Install the runtime active count, zero the cover pointer and first
offset, then initialize exactly the live prefix. -/
def activeInitCom (j r : ℕ) : Com :=
  .seq (.assign "qn" (.var (mnumName j)))
    (.seq (.assign "xp" (.lit 0))
      (.seq (.store "xoff" (.lit 0) (.lit 0))
        (centreLoopCom "aci" "qn" (activeInitTurn j r))))

def activeInitCost (q : ℕ) : ℕ :=
  7 + coverLoopK 25 q (fun _ => 0)

/-! ## Entry and loop invariant -/

structure ActiveInitPre (B n ns nt q r j : ℕ) (A₀ centre O T : ℕ → ℕ)
    (σ : Env) : Prop where
  n_var : σ.vars "n" = n
  count_var : σ.vars (mnumName j) = q
  centre_arr : σ.arrs (ordName j) = arrOf n centre
  ambient_arr : σ.arrs (alvName j) = arrOf n A₀
  off_arr : σ.arrs "off" = arrOf (n + 1) O
  target_arr : σ.arrs "tgt" = arrOf nt T
  zero_mask : σ.arrs "elm" = arrOf n (fun _ => 0)
  dist_arr : ∃ D, σ.arrs "dist" = arrOf n D
  queue_arr : ∃ Q, σ.arrs "q" = arrOf n Q
  qdist_arr : ∃ QD, σ.arrs "qd" = arrOf n QD
  xoff_arr : ∃ Xoff, σ.arrs "xoff" = arrOf (n + 1) Xoff
  xmem_arr : ∃ Xmem, σ.arrs "xmem" = arrOf (n * n) Xmem
  asg_arr : ∃ asg, σ.arrs "asg" = arrOf n asg
  ambient_bound : ∀ z < n, A₀ z < B

structure ActiveInitInv (B n ns nt q r j : ℕ) (A₀ centre O T : ℕ → ℕ)
    (σ : Env) : Prop where
  counter_le : σ.vars "aci" ≤ q
  n_var : σ.vars "n" = n
  q_var : σ.vars "qn" = q
  centre_arr : σ.arrs (ordName j) = arrOf n centre
  ambient_arr : σ.arrs (alvName j) = arrOf n A₀
  off_arr : σ.arrs "off" = arrOf (n + 1) O
  target_arr : σ.arrs "tgt" = arrOf nt T
  mask_arr : σ.arrs "elm" = arrOf n (prefixMask A₀ centre (σ.vars "aci"))
  dist_arr : ∃ D, σ.arrs "dist" = arrOf n D ∧
    ∀ k < σ.vars "aci", D (centre k) = 2 * r + 1
  asg_arr : ∃ asg, σ.arrs "asg" = arrOf n asg ∧
    ∀ k < σ.vars "aci", asg (centre k) = q
  xoff_arr : ∃ Xoff, σ.arrs "xoff" = arrOf (n + 1) Xoff ∧ Xoff 0 = 0
  xmem_arr : ∃ Xmem, σ.arrs "xmem" = arrOf (n * n) Xmem
  pointer_var : σ.vars "xp" = 0
  queue_arr : ∃ Q, σ.arrs "q" = arrOf n Q
  qdist_arr : ∃ QD, σ.arrs "qd" = arrOf n QD
  ambient_bound : ∀ z < n, A₀ z < B

/-! ## One initialization turn -/

variable {B n ns nt q r j k : ℕ}
variable {A₀ centre O T : ℕ → ℕ}
variable {π : Equiv.Perm (Fin n)}
variable {G : SimpleGraph (Fin n)}

theorem activeInitTurn_spec
    (hcentres : CentresBy n q A₀ π centre)
    (hnB : n < B) (hqB : q < B) (hrB : 2 * r + 1 < B)
    (hk : k < q) :
    Spec B
      (fun σ => ActiveInitInv B n ns nt q r j A₀ centre O T σ ∧
        σ.vars "aci" = k)
      (activeInitTurn j r)
      (fun _ σ' => ActiveInitInv B n ns nt q r j A₀ centre O T σ' ∧
        σ'.vars "aci" = k + 1)
      (centreK 25 0) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hI, haci⟩ := hσ
  obtain ⟨D, hdist, hdist_pre⟩ := hI.dist_arr
  obtain ⟨asg, hasg, hasg_pre⟩ := hI.asg_arr
  obtain ⟨Xoff, hxoff, hxoff0⟩ := hI.xoff_arr
  obtain ⟨Xmem, hxmem⟩ := hI.xmem_arr
  obtain ⟨Q, hQ⟩ := hI.queue_arr
  obtain ⟨QD, hQD⟩ := hI.qdist_arr
  have hkn : k < n := lt_of_lt_of_le hk hcentres.count_le
  have hkB : k < B := lt_trans hkn hnB
  have hcn : centre k < n := hcentres.centre_lt k hk
  have hcB : centre k < B := lt_trans hcn hnB
  have hAB : A₀ (centre k) < B := hI.ambient_bound _ hcn
  have hk1B : k + 1 < B := by omega
  let σ₁ := σ.setVar "acs" (centre k)
  have r₁ : Run B (.assign "acs" (.get (ordName j) (.var "aci"))) σ σ₁ 3 := by
    apply Run.assign
    apply evalB_get (k := k)
    · simpa [haci] using (evalB_var (B := B) (σ := σ) (x := "aci") (by
        rw [haci]
        exact hkB))
    · rw [hI.centre_arr, getElem?_arrOf centre hkn]
    · exact hcB
  let σ₂ := σ₁.setVar "acv" (A₀ (centre k))
  have r₂ : Run B (.assign "acv" (.get (alvName j) (.var "acs"))) σ₁ σ₂ 3 := by
    apply Run.assign
    apply evalB_get
    · exact evalB_var (by simp [σ₁, hcB])
    · simp [σ₁, hI.ambient_arr, getElem?_arrOf A₀ hcn]
    · exact hAB
  let σ₃ := σ₂.setArr "elm" (centre k) (A₀ (centre k))
  have r₃ : Run B (.store "elm" (.var "acs") (.var "acv")) σ₂ σ₃ 3 := by
    exact Run.store (evalB_var (by simp [σ₂, σ₁, hcB]))
      (evalB_var (by simp [σ₂, hAB])) (by
        simp [σ₂, σ₁, hI.mask_arr, length_arrOf, hcn])
  let σ₄ := σ₃.setArr "dist" (centre k) (2 * r + 1)
  have r₄ : Run B (.store "dist" (.var "acs") (.lit (2 * r + 1))) σ₃ σ₄ 3 := by
    exact Run.store (evalB_var (by simp [σ₃, σ₂, σ₁, hcB])) (evalB_lit hrB) (by
      simp [σ₃, σ₂, σ₁, hdist, length_arrOf, hcn])
  let σ₅ := σ₄.setArr "asg" (centre k) q
  have r₅ : Run B (.store "asg" (.var "acs") (.var "qn")) σ₄ σ₅ 3 := by
    exact Run.store (evalB_var (by simp [σ₄, σ₃, σ₂, σ₁, hcB]))
      (by
        have h := evalB_var (B := B) (σ := σ₄) (x := "qn") (by
          simpa [σ₄, σ₃, σ₂, σ₁, hI.q_var] using hqB)
        simpa [σ₄, σ₃, σ₂, σ₁, hI.q_var] using h) (by
        simp [σ₄, σ₃, σ₂, σ₁, hasg, length_arrOf, hcn])
  let σ₆ := σ₅.setVar "aci" (k + 1)
  have r₆ : Run B (.assign "aci" (.add (.var "aci") (.lit 1))) σ₅ σ₆ 4 := by
    apply Run.assign
    have haci₅ : σ₅.vars "aci" = k := by
      simp [σ₅, σ₄, σ₃, σ₂, σ₁, haci]
    have he := evalB_bin (B := B) (σ := σ₅) (op := .add) (m := k) (n := 1)
      (e := .var "aci") (f := .lit 1)
      (by simpa [haci₅] using
        (evalB_var (B := B) (σ := σ₅) (x := "aci") (by rw [haci₅]; exact hkB)))
      (evalB_lit (B := B) (σ := σ₅) (n := 1) (by omega))
      (by simpa only [Lax13Proofs.Imp.Bop.apply_add] using hk1B)
    simpa using he
  have hrun : Run B (activeInitTurn j r) σ σ₆ 19 :=
    r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq r₆))))
  have hordElm : ordName j ≠ "elm" := by simp [ordName, String.ext_iff]
  have hordDist : ordName j ≠ "dist" := by simp [ordName, String.ext_iff]
  have hordAsg : ordName j ≠ "asg" := by simp [ordName, String.ext_iff]
  have halvElm : alvName j ≠ "elm" := by simp [alvName, String.ext_iff]
  have halvDist : alvName j ≠ "dist" := by simp [alvName, String.ext_iff]
  have halvAsg : alvName j ≠ "asg" := by simp [alvName, String.ext_iff]
  refine ⟨σ₆, 19, hrun, by simp [centreK], ?_, by simp [σ₆]⟩
  refine
    { counter_le := by simp [σ₆]; omega
      n_var := by simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hI.n_var]
      q_var := by simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hI.q_var]
      centre_arr := by
        simpa [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hordElm, hordDist, hordAsg] using
          hI.centre_arr
      ambient_arr := by
        simpa [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, halvElm, halvDist, halvAsg] using
          hI.ambient_arr
      off_arr := by simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hI.off_arr]
      target_arr := by simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hI.target_arr]
      mask_arr := by
        simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hI.mask_arr, haci,
          set_arrOf_eq_upd, prefixMask_succ]
      dist_arr := ⟨upd D (centre k) (2 * r + 1), by
        simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hdist, set_arrOf_eq_upd], by
        intro i hi
        simp only [σ₆, vars_setVar, if_pos] at hi
        by_cases hik : i = k
        · subst i
          simp
        · have hik' : i < k := by omega
          have hne : centre i ≠ centre k := fun heq =>
            hik (hcentres.injective (lt_trans hik' hk) hk heq)
          rw [upd_of_ne _ hne]
          exact hdist_pre i (by rw [haci]; exact hik')⟩
      asg_arr := ⟨upd asg (centre k) q, by
        simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hasg, set_arrOf_eq_upd], by
        intro i hi
        simp only [σ₆, vars_setVar, if_pos] at hi
        by_cases hik : i = k
        · subst i
          simp
        · have hik' : i < k := by omega
          have hne : centre i ≠ centre k := fun heq =>
            hik (hcentres.injective (lt_trans hik' hk) hk heq)
          rw [upd_of_ne _ hne]
          exact hasg_pre i (by rw [haci]; exact hik')⟩
      xoff_arr := ⟨Xoff, by
        simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hxoff], hxoff0⟩
      xmem_arr := ⟨Xmem, by simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hxmem]⟩
      pointer_var := by simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hI.pointer_var]
      queue_arr := ⟨Q, by simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hQ]⟩
      qdist_arr := ⟨QD, by simp [σ₆, σ₅, σ₄, σ₃, σ₂, σ₁, hQD]⟩
      ambient_bound := hI.ambient_bound }

/-! ## Complete initializer -/

theorem activeInit_spec
    (hcentres : CentresBy n q A₀ π centre)
    (hnB : n < B) (hqB : q < B) (hrB : 2 * r + 1 < B) :
    Spec B
      (ActiveInitPre B n ns nt q r j A₀ centre O T)
      (activeInitCom j r)
      (fun _ σ' => RawLoopState B ns nt q r G
        A₀ π centre O T ((renEnv (activeCoverSwap j) σ').setVar "c" 0))
      (activeInitCost q) := by
  intro σ hpre
  have hzeroB : 0 < B := by omega
  let σ₁ := σ.setVar "qn" q
  have r₁ : Run B (.assign "qn" (.var (mnumName j))) σ σ₁ 2 := by
    have h := Run.assign (B := B) (σ := σ) (x := "qn")
      (e := .var (mnumName j))
      (evalB_var (by rw [hpre.count_var]; exact hqB))
    simpa [σ₁, hpre.count_var] using h
  let σ₂ := σ₁.setVar "xp" 0
  have r₂ : Run B (.assign "xp" (.lit 0)) σ₁ σ₂ 2 :=
    Run.assign (evalB_lit hzeroB)
  obtain ⟨Xoff₀, hxoff₀⟩ := hpre.xoff_arr
  let Xoff := upd Xoff₀ 0 0
  let σ₃ := σ₂.setArr "xoff" 0 0
  have r₃ : Run B (.store "xoff" (.lit 0) (.lit 0)) σ₂ σ₃ 3 := by
    exact Run.store (evalB_lit hzeroB) (evalB_lit hzeroB) (by
      simp [σ₂, σ₁, hxoff₀, length_arrOf])
  obtain ⟨D₀, hD₀⟩ := hpre.dist_arr
  obtain ⟨Q₀, hQ₀⟩ := hpre.queue_arr
  obtain ⟨QD₀, hQD₀⟩ := hpre.qdist_arr
  obtain ⟨Xmem₀, hXmem₀⟩ := hpre.xmem_arr
  obtain ⟨asg₀, hasg₀⟩ := hpre.asg_arr
  let I := ActiveInitInv B n ns nt q r j A₀ centre O T
  have hordXoff : ordName j ≠ "xoff" := by simp [ordName, String.ext_iff]
  have halvXoff : alvName j ≠ "xoff" := by simp [alvName, String.ext_iff]
  have hI₀ : I (σ₃.setVar "aci" 0) :=
    { counter_le := by simp
      n_var := by simp [σ₃, σ₂, σ₁, hpre.n_var]
      q_var := by simp [σ₃, σ₂, σ₁]
      centre_arr := by
        simpa [σ₃, σ₂, σ₁, hordXoff] using hpre.centre_arr
      ambient_arr := by
        simpa [σ₃, σ₂, σ₁, halvXoff] using hpre.ambient_arr
      off_arr := by simp [σ₃, σ₂, σ₁, hpre.off_arr]
      target_arr := by simp [σ₃, σ₂, σ₁, hpre.target_arr]
      mask_arr := by simp [σ₃, σ₂, σ₁, hpre.zero_mask]
      dist_arr := ⟨D₀, by simp [σ₃, σ₂, σ₁, hD₀], by simp⟩
      asg_arr := ⟨asg₀, by simp [σ₃, σ₂, σ₁, hasg₀], by simp⟩
      xoff_arr := ⟨Xoff, by
        simp [σ₃, σ₂, σ₁, Xoff, hxoff₀, set_arrOf_eq_upd], by
        simp [Xoff]⟩
      xmem_arr := ⟨Xmem₀, by simp [σ₃, σ₂, σ₁, hXmem₀]⟩
      pointer_var := by simp [σ₃, σ₂]
      queue_arr := ⟨Q₀, by simp [σ₃, σ₂, σ₁, hQ₀]⟩
      qdist_arr := ⟨QD₀, by simp [σ₃, σ₂, σ₁, hQD₀]⟩
      ambient_bound := hpre.ambient_bound }
  have hbody : CentreImplementsB B "aci" (activeInitTurn j r) I q 25 (fun _ => 0) := by
    intro i hi
    exact activeInitTurn_spec hcentres hnB hqB hrB hi
  have hloop := centreLoop_spec "aci" "qn" q 25 (fun _ => 0) hqB
    (fun _ h => h.counter_le) (fun _ h => h.q_var) hbody
  obtain ⟨σ₄, rloop, hI₄, haci₄⟩ := hloop.run hI₀
  obtain ⟨D, hD, hDpre⟩ := hI₄.dist_arr
  obtain ⟨asg, hasg, hasgpre⟩ := hI₄.asg_arr
  obtain ⟨Xoff', hXoff', hXoff0⟩ := hI₄.xoff_arr
  obtain ⟨Xmem, hXmem⟩ := hI₄.xmem_arr
  obtain ⟨Q, hQ⟩ := hI₄.queue_arr
  obtain ⟨QD, hQD⟩ := hI₄.qdist_arr
  have hmaskPoint : ∀ z < n, prefixMask A₀ centre q z = A₀ z := by
    intro z hz
    by_cases hAz : A₀ z = 0
    · simp [prefixMask, hAz]
    · obtain ⟨i, hi, hic⟩ := hcentres.complete z hz hAz
      rw [prefixMask, if_pos ⟨i, hi, hic⟩]
  have hmask : σ₄.arrs "elm" = arrOf n A₀ := by
    rw [hI₄.mask_arr, haci₄]
    exact arrOf_congr hmaskPoint
  have hclean : CleanOn n (2 * r) A₀ D := by
    intro z hz hAz
    obtain ⟨i, hi, hic⟩ := hcentres.complete z hz hAz
    rw [← hic]
    exact hDpre i (by rw [haci₄]; exact hi)
  have hasgSent : ∀ z < n, A₀ z ≠ 0 → asg z = q := by
    intro z hz hAz
    obtain ⟨i, hi, hic⟩ := hcentres.complete z hz hAz
    rw [← hic]
    exact hasgpre i (by rw [haci₄]; exact hi)
  have hraw : RawCoverInvA G A₀ π centre q r 0 0
      Xoff' Xmem asg A₀ :=
    RawCoverInvA.init (fun _ _ => rfl) hXoff0 hasgSent
  have hstate : RawTurnState B ns nt q r 0 0 G A₀ π
      centre O T Xoff' Xmem asg A₀
      ((renEnv (activeCoverSwap j) σ₄).setVar "c" 0) := by
    refine ⟨hraw, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ⟨D, ?_, hclean⟩, ⟨Q, ?_⟩, ⟨QD, ?_⟩, hI₄.ambient_bound⟩
    · simpa using hI₄.n_var
    · simpa using hI₄.q_var
    · simp
    · simpa using hI₄.pointer_var
    · simpa [renEnv] using hI₄.centre_arr
    · simpa [activeCoverSwap, ordName, String.ext_iff] using hI₄.off_arr
    · simpa [activeCoverSwap, ordName, String.ext_iff] using hI₄.target_arr
    · simpa [renEnv] using hmask
    · simpa [activeCoverSwap, ordName, String.ext_iff] using hXoff'
    · simpa [activeCoverSwap, ordName, String.ext_iff] using hXmem
    · simpa [activeCoverSwap, ordName, String.ext_iff] using hasg
    · simpa [activeCoverSwap, ordName, String.ext_iff] using hD
    · simpa [activeCoverSwap, ordName, String.ext_iff] using hQ
    · simpa [activeCoverSwap, ordName, String.ext_iff] using hQD
  refine ⟨σ₄, ?_, ⟨0, 0, Xoff', Xmem, asg, A₀, hstate⟩⟩
  have hrun := r₁.seq (r₂.seq (r₃.seq rloop))
  convert hrun using 1 <;> simp [activeInitCom, activeInitCost] <;> omega

/-! ## Axiom audit -/

#print axioms activeInitTurn_spec
#print axioms activeInit_spec

end Lax3Proofs.Refine.CoverActiveInit
