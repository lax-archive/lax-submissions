import Lax3Proofs.Refine.OrderVirtualFrat
import Lax3Proofs.Refine.OrderVirtualRows

/-!
# A compositional erased-biunion row provider

The next virtual orientation is regenerated from transitive and fraternal
walks through the previous orientation.  Both transitive halves are nested
finite-set unions.  This file factors the corresponding executable provider
out of the fraternity proof: an outer row is scanned, an inner row is
generated for every outer entry, and a carrier-sized stamp emits the union
without duplicates.  The requested root is pre-stamped, so the public result
is the nested union with that root erased.
-/

namespace Lax3Proofs.Refine.OrderVirtualBiUnion

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.RamDriverAugment
  (Marks valSet mem_valSet mem_valSet_of valSet_lt)
open Lax3Proofs.Refine.OrderVirtualProvider
open Lax3Proofs.Refine.OrderVirtualSetRow
open Lax3Proofs.Refine.OrderVirtualBaseFrat (fratFe)
open Lax3Proofs.Refine.OrderVirtualFrat
open Lax3Proofs.Augmentation
open Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.RamAugment

variable {n : ℕ}

/-! ## The two transitive row families -/

/-- Incoming two-path predecessors of a vertex.  Erasing the root is
extensionally harmless because an orientation has no directed two-cycle. -/
noncomputable def transInSet (D : Orientation n) (v : Fin n) : Finset (Fin n) :=
  ((D.inN v).biUnion D.inN).erase v

/-- Outgoing two-path successors of a vertex. -/
noncomputable def transOutSet (D : Orientation n) (v : Fin n) : Finset (Fin n) :=
  ((outSet D v).biUnion (outSet D)).erase v

theorem mem_transInSet {D : Orientation n} {u v : Fin n} :
    u ∈ transInSet D v ↔ TransLink D u v := by
  rw [transInSet, Finset.mem_erase, Finset.mem_biUnion]
  constructor
  · rintro ⟨-, w, hwv, huw⟩
    exact ⟨w, huw, hwv⟩
  · intro h
    obtain ⟨w, huw, hwv⟩ := h
    refine ⟨?_, w, hwv, huw⟩
    intro huv
    subst u
    exact not_transLink_self D v ⟨w, huw, hwv⟩

theorem mem_transOutSet {D : Orientation n} {u v : Fin n} :
    u ∈ transOutSet D v ↔ TransLink D v u := by
  rw [transOutSet, Finset.mem_erase, Finset.mem_biUnion]
  constructor
  · rintro ⟨-, w, hvw, hwu⟩
    exact ⟨w, mem_outSet.1 hvw, mem_outSet.1 hwu⟩
  · intro h
    obtain ⟨w, hvw, hwu⟩ := h
    refine ⟨?_, w, mem_outSet.2 hvw, mem_outSet.2 hwu⟩
    intro huv
    subst u
    exact not_transLink_self D v ⟨w, hvw, hwu⟩

/-- Reverse demands, with the irrelevant self-demand erased, are the union
of the incoming two-path row and the fraternity row. -/
theorem demandIn_erase_eq (D : Orientation n) (v : Fin n) :
    (Lax3Proofs.Refine.OrderVirtualRows.demandIn D v).erase v =
      transInSet D v ∪ fratNbrs D v := by
  classical
  ext u
  rw [Finset.mem_erase, Finset.mem_union, mem_transInSet, mem_fratNbrs,
    Lax3Proofs.Refine.OrderVirtualRows.mem_demandIn,
    Lax3Proofs.Augmentation.fratGraph_adj]
  constructor
  · rintro ⟨hne, htrans | hfrat⟩
    · exact Or.inl htrans
    · exact Or.inr ⟨hne, hfrat⟩
  · rintro (htrans | ⟨hne, hfrat⟩)
    · refine ⟨?_, Or.inl htrans⟩
      intro huv
      subst u
      exact not_transLink_self D v htrans
    · exact ⟨hne, Or.inr hfrat⟩

/-- Forward demands have the symmetric decomposition. -/
theorem demandOut_erase_eq (D : Orientation n) (v : Fin n) :
    (demandOut D v).erase v = transOutSet D v ∪ fratNbrs D v := by
  classical
  ext u
  rw [Finset.mem_erase, Finset.mem_union, mem_transOutSet, mem_fratNbrs,
    mem_demandOut, Lax3Proofs.Augmentation.fratGraph_adj]
  constructor
  · rintro ⟨hne, htrans | hfrat⟩
    · exact Or.inl htrans
    · exact Or.inr ⟨hne, hfrat.symm⟩
  · rintro (htrans | ⟨hne, hfrat⟩)
    · refine ⟨?_, Or.inl htrans⟩
      intro huv
      subst u
      exact not_transLink_self D v htrans
    · exact ⟨hne, Or.inr hfrat.symm⟩

/-- Numeric image of a totalized inner row. -/
noncomputable def innerValSet (Inner : Fin n → Finset (Fin n))
    (z : ℕ) : Finset ℕ :=
  if hz : z < n then valSet (Inner ⟨z, hz⟩) else ∅

@[simp] theorem innerValSet_of_lt (Inner : Fin n → Finset (Fin n))
    {z : ℕ} (hz : z < n) :
    innerValSet Inner z = valSet (Inner ⟨z, hz⟩) := by
  simp [innerValSet, hz]

/-- Contribution of one outer entry, with the requested root suppressed. -/
noncomputable def eraseBiStep (Inner : Fin n → Finset (Fin n))
    (root z : ℕ) : Finset ℕ :=
  (innerValSet Inner z).biUnion (fratFe root)

/-- Numeric set enumerated by the complete nested walk. -/
noncomputable def eraseBiNum
    (Outer Inner : Fin n → Finset (Fin n)) (root : Fin n) : Finset ℕ :=
  (valSet (Outer root)).biUnion (eraseBiStep Inner (root : ℕ))

/-- The numeric nested walk is exactly the image of the erased finset
biunion. -/
theorem eraseBiNum_eq
    (Outer Inner : Fin n → Finset (Fin n)) (root : Fin n) :
    eraseBiNum Outer Inner root =
      valSet (((Outer root).biUnion Inner).erase root) := by
  classical
  ext y
  rw [eraseBiNum, Finset.mem_biUnion, mem_valSet]
  constructor
  · rintro ⟨z, hzOuter, hyStep⟩
    obtain ⟨hzn, hzOuter'⟩ := mem_valSet.1 hzOuter
    rw [eraseBiStep, innerValSet_of_lt Inner hzn,
      Finset.mem_biUnion] at hyStep
    obtain ⟨u, huInner, hy⟩ := hyStep
    obtain ⟨hun, huInner'⟩ := mem_valSet.1 huInner
    rw [fratFe] at hy
    by_cases hur : u = (root : ℕ)
    · simp [hur] at hy
    · have hyu : y = u := by simpa [hur] using hy
      subst y
      refine ⟨hun, ?_⟩
      rw [Finset.mem_erase, Finset.mem_biUnion]
      exact ⟨fun h => hur (congrArg Fin.val h),
        ⟨z, hzn⟩, hzOuter', huInner'⟩
  · rintro ⟨hyn, hyUnion⟩
    rw [Finset.mem_erase, Finset.mem_biUnion] at hyUnion
    obtain ⟨hyr, z, hzOuter, hyInner⟩ := hyUnion
    refine ⟨(z : ℕ), mem_valSet_of hzOuter, ?_⟩
    rw [eraseBiStep, innerValSet_of_lt Inner z.isLt,
      Finset.mem_biUnion]
    refine ⟨y, mem_valSet_of hyInner, ?_⟩
    have hyr' : y ≠ (root : ℕ) := fun h => hyr (Fin.ext h)
    simp [fratFe, hyr']

/-! ## Generic nested-scan invariant -/

/-- State carried while the outer row of an erased biunion is scanned. -/
structure EraseBiOuterAcc (n W : ℕ) (P : Env → Prop)
    (root : Fin n) (Cap : Finset ℕ) (step : ℕ → Finset ℕ)
    (outTail : ℕ) (Aout : ℕ → ℕ) (p : ℕ)
    (E Deg ER ID BH BV BN : ℕ → ℕ) (tau : Env) : Prop where
  marks : Marks "stf" n 1
    ({(root : ℕ)} ∪ bufferAcc p Aout step) (fun _ => 0) tau
  fill : RowFillAcc "vrow" n Cap (bufferAcc p Aout step) tau
  persistent : P tau
  engine : EngineArrays n W E Deg ER ID BH BV BN tau
  out_eq : tau.arrs "vout" = arrOf n Aout
  vin_length : (tau.arrs "vin").length = n
  save_length : (tau.arrs "vsave").length = 4
  root_eq : tau.vars "froot" = (root : ℕ)
  end_eq : tau.vars "fend" = outTail

namespace EraseBiOuterAcc

theorem setVarPrivate {n W : ℕ} {P : Env → Prop}
    {root : Fin n} {Cap : Finset ℕ} {step : ℕ → Finset ℕ}
    {outTail : ℕ} {Aout : ℕ → ℕ} {p : ℕ}
    {E Deg ER ID BH BV BN : ℕ → ℕ} {tau : Env}
    (hclose : FratScratchClosed P)
    (h : EraseBiOuterAcc n W P root Cap step outTail Aout p
      E Deg ER ID BH BV BN tau)
    {y : String} (hyn : y ≠ "n") (hyr : y ≠ "froot")
    (hye : y ≠ "fend") (hyc : y ≠ "c") (x : ℕ) :
    EraseBiOuterAcc n W P root Cap step outTail Aout p
      E Deg ER ID BH BV BN (tau.setVar y x) := by
  refine ⟨h.marks.setVar y x, h.fill.setVar hyc x,
    hclose.setVar hyn h.persistent, ?_, by simpa using h.out_eq,
    by simpa using h.vin_length, by simpa using h.save_length, ?_, ?_⟩
  · exact ⟨by rw [vars_setVar, if_neg (Ne.symm hyn)]; exact h.engine.n_eq,
      by simpa using h.engine.elm_eq, by simpa using h.engine.deg_eq,
      by simpa using h.engine.rank_eq, by simpa using h.engine.idg_eq,
      by simpa using h.engine.head_eq, by simpa using h.engine.val_eq,
      by simpa using h.engine.next_eq⟩
  · rw [vars_setVar, if_neg (Ne.symm hyr)]
    exact h.root_eq
  · rw [vars_setVar, if_neg (Ne.symm hye)]
    exact h.end_eq

end EraseBiOuterAcc

/-- Run the guarded generated inner row and identify its contribution with
one step of the erased biunion. -/
theorem eraseBiInnerBuffer_run {B n W : ℕ} {P : Env → Prop}
    {Inner : Fin n → Finset (Fin n)} {root : Fin n} {z : ℕ} (hz : z < n)
    {Cap S : Finset ℕ} {outTail outerPos inTail : ℕ}
    {Aout Ain : ℕ → ℕ} {E Deg ER ID BH BV BN : ℕ → ℕ} {tau : Env}
    (hclose : FratScratchClosed P)
    (hB1 : 1 < B) (hnB : n < B) (hCap : Cap ⊆ Finset.range n)
    (hrow : SetRowRep (Inner ⟨z, hz⟩) inTail Ain)
    (hfeCap : ∀ p, p < inTail → fratFe (root : ℕ) (Ain p) ⊆ Cap)
    (hmarks : Marks "stf" n 1 ({(root : ℕ)} ∪ S) (fun _ => 0) tau)
    (hacc : VirtualInnerAcc n W P root Cap outTail outerPos Aout Ain inTail
      E Deg ER ID BH BV BN S tau) :
    ∃ tau' K,
      Run B (bufferScan "vin" "fk" "vtail" "u"
        (Lax3Proofs.RamDriverAugment.fratGuard (rowFillAct "vrow"))) tau tau' K ∧
      K ≤ inTail * 26 + 6 ∧
      Marks "stf" n 1
        ({(root : ℕ)} ∪ (S ∪ eraseBiStep Inner (root : ℕ) z))
        (fun _ => 0) tau' ∧
      VirtualInnerAcc n W P root Cap outTail outerPos Aout Ain inTail
        E Deg ER ID BH BV BN (S ∪ eraseBiStep Inner (root : ℕ) z) tau' := by
  let J : Finset ℕ → Env → Prop := fun U sigma =>
    Marks "stf" n 1 ({(root : ℕ)} ∪ U) (fun _ => 0) sigma ∧
      VirtualInnerAcc n W P root Cap outTail outerPos Aout Ain inTail
        E Deg ER ID BH BV BN U sigma
  obtain ⟨tau', K, hr, hK, hJ⟩ :=
    emitBuffer_run (B := B) (n := n) (tail := inTail) (Kg := 15)
      (src := "vin") (j := "fk") (jend := "vtail")
      (grd := Lax3Proofs.RamDriverAugment.fratGuard (rowFillAct "vrow"))
      (S := Inner ⟨z, hz⟩) (A := Ain) (fe := fratFe (root : ℕ))
      (J := J) (E0 := S) (Cap := Cap) (sigma := tau)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hB1 hnB hrow hacc.in_tail_eq hacc.in_eq
      (fun _ _ h => h.2.in_eq)
      (by
        intro U sigma y x hy hJ
        refine ⟨hJ.1.setVar y x, ?_⟩
        rcases hy with rfl | rfl
        · exact hJ.2.setVarPrivate hclose (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) x
        · exact hJ.2.setVarPrivate hclose (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) x)
      hfeCap (virtualInnerAcc_guarded hclose hB1 hnB hCap) ⟨hmarks, hacc⟩
  have hstep : bufferAcc inTail Ain (fratFe (root : ℕ)) =
      eraseBiStep Inner (root : ℕ) z := by
    rw [bufferAcc_eq_biUnion_valSet hrow, eraseBiStep,
      innerValSet_of_lt Inner hz]
  rw [hstep] at hJ
  exact ⟨tau', K, hr, by omega, hJ.1, hJ.2⟩

/-! ## One outer slot -/

/-- Save the outer state, invoke the inner provider at the selected outer
entry, restore the caller, and feed the generated row through the duplicate
stamp. -/
theorem eraseBiInner_run {B n W : ℕ} {P : Env → Prop}
    {Outer Inner : Fin n → Finset (Fin n)}
    {provideIn : Com} {kin : ℕ → ℕ}
    {root : Fin n} {outTail p : ℕ}
    {Aout : ℕ → ℕ} {E Deg ER ID BH BV BN : ℕ → ℕ} {tau : Env}
    (hclose : FratScratchClosed P) (hframes : FratIncomingFrames provideIn)
    (hB4 : 3 < B) (hnB : n < B)
    (hpin : ProvidesSetRows B n W Inner P "vin" provideIn kin)
    (hout : SetRowRep (Outer root) outTail Aout)
    (hp : p < outTail) (hfj : tau.vars "fj" = p)
    (houter : EraseBiOuterAcc n W P root (eraseBiNum Outer Inner root)
      (eraseBiStep Inner (root : ℕ)) outTail Aout p
      E Deg ER ID BH BV BN tau) :
    ∃ tau' K,
      Run B (virtualFratInner provideIn) (tau.setVar "u" (Aout p)) tau' K ∧
      K ≤ kin (Aout p) +
        26 * (Inner ⟨Aout p, hout.value_lt p hp⟩).card + 32 ∧
      tau'.vars "fj" = p ∧
      EraseBiOuterAcc n W P root (eraseBiNum Outer Inner root)
        (eraseBiStep Inner (root : ℕ)) outTail Aout (p + 1)
        E Deg ER ID BH BV BN tau' := by
  classical
  let z := Aout p
  have hz : z < n := hout.value_lt p hp
  let S := bufferAcc p Aout (eraseBiStep Inner (root : ℕ))
  have hCap : eraseBiNum Outer Inner root ⊆ Finset.range n := by
    rw [eraseBiNum_eq]
    intro y hy
    exact Finset.mem_range.2 (valSet_lt hy)
  obtain ⟨hSsub, Acur, hAcur, hc, hnd, hmem⟩ := houter.fill
  change S ⊆ eraseBiNum Outer Inner root at hSsub
  have hScard : S.card < B := by
    have hle := Finset.card_le_card (hSsub.trans hCap)
    rw [Finset.card_range] at hle
    omega
  have hrootB : (root : ℕ) < B := lt_trans root.isLt hnB
  have houtTailB : outTail < B := lt_of_le_of_lt hout.tail_le hnB
  have hpB : p < B := lt_trans hp houtTailB
  let sigma0 := tau.setVar "u" z
  have hP0 : P sigma0 := hclose.setVar (by decide) houter.persistent
  have heng0 : EngineArrays n W E Deg ER ID BH BV BN sigma0 := by
    refine ⟨by simpa [sigma0] using houter.engine.n_eq,
      by simpa [sigma0] using houter.engine.elm_eq,
      by simpa [sigma0] using houter.engine.deg_eq,
      by simpa [sigma0] using houter.engine.rank_eq,
      by simpa [sigma0] using houter.engine.idg_eq,
      by simpa [sigma0] using houter.engine.head_eq,
      by simpa [sigma0] using houter.engine.val_eq,
      by simpa [sigma0] using houter.engine.next_eq⟩
  have hsaveLen0 : (sigma0.arrs "vsave").length = 4 := by
    simpa [sigma0] using houter.save_length
  have hc0 : sigma0.vars "c" = S.card := by
    simpa [sigma0] using hc
  have hroot0 : sigma0.vars "froot" = (root : ℕ) := by
    simpa [sigma0] using houter.root_eq
  have hend0 : sigma0.vars "fend" = outTail := by
    simpa [sigma0] using houter.end_eq
  have hfj0 : sigma0.vars "fj" = p := by
    simpa [sigma0] using hfj
  obtain ⟨sigma1, r1, hP1, heng1, hsave1⟩ :=
    fratSaveState_run hclose hP0 heng0 hsaveLen0 hc0 hroot0 hend0 hfj0
      hB4 hScard hrootB houtTailB hpB
  have hu1 : sigma1.vars "u" = z := by
    rw [r1.frame_var "u" (by decide)]
    simp [sigma0]
  have eu1 : (Expr.var "u").evalB B sigma1 = some z := by
    have h := evalB_var (B := B) (x := "u") (σ := sigma1)
      (by rw [hu1]; exact lt_trans hz hnB)
    rwa [hu1] at h
  let sigma2 := sigma1.setVar "w" z
  have r2 : Run B (.assign "w" (.var "u")) sigma1 sigma2 2 := Run.assign eu1
  have hP2 : P sigma2 := hclose.setVar (by decide) hP1
  have heng2 : EngineArrays n W E Deg ER ID BH BV BN sigma2 := by
    refine ⟨by simpa [sigma2] using heng1.n_eq,
      by simpa [sigma2] using heng1.elm_eq,
      by simpa [sigma2] using heng1.deg_eq,
      by simpa [sigma2] using heng1.rank_eq,
      by simpa [sigma2] using heng1.idg_eq,
      by simpa [sigma2] using heng1.head_eq,
      by simpa [sigma2] using heng1.val_eq,
      by simpa [sigma2] using heng1.next_eq⟩
  have hw2 : sigma2.vars "w" = z := by simp [sigma2]
  obtain ⟨sigma3, r3, hP3, heng3, -, inTail, Ain, hrowIn, htail3, hAin3⟩ :=
    (hpin ⟨z, hz⟩ E Deg ER ID BH BV BN).run ⟨hP2, heng2, hw2⟩
  have hsave3 : sigma3.arrs "vsave" =
      arrOf 4 (fratSavedValues S.card (root : ℕ) outTail p) := by
    rw [r3.frame_arr "vsave" hframes.save]
    simpa [sigma2] using hsave1
  obtain ⟨sigma4, r4, hP4, heng4, hc4, hroot4, hend4, hfj4⟩ :=
    fratRestoreState_run hclose hP3 heng3 hsave3 hB4
      hScard hrootB houtTailB hpB
  have hvrow4 : sigma4.arrs "vrow" = tau.arrs "vrow" := by
    rw [r4.frame_arr "vrow" (by decide), r3.frame_arr "vrow" hframes.vrow,
      r2.frame_arr "vrow" (by decide), r1.frame_arr "vrow" (by decide)]
    rfl
  have hvout4 : sigma4.arrs "vout" = tau.arrs "vout" := by
    rw [r4.frame_arr "vout" (by decide), r3.frame_arr "vout" hframes.vout,
      r2.frame_arr "vout" (by decide), r1.frame_arr "vout" (by decide)]
    rfl
  have hstf4 : sigma4.arrs "stf" = tau.arrs "stf" := by
    rw [r4.frame_arr "stf" (by decide), r3.frame_arr "stf" hframes.stamp,
      r2.frame_arr "stf" (by decide), r1.frame_arr "stf" (by decide)]
    rfl
  have hvin4 : sigma4.arrs "vin" = arrOf n Ain := by
    rw [r4.frame_arr "vin" (by decide)]
    exact hAin3
  have htail4 : sigma4.vars "vtail" = inTail := by
    rw [r4.frame_var "vtail" (by decide)]
    exact htail3
  have hsaveLen4 : (sigma4.arrs "vsave").length = 4 := by
    rw [r4.frame_arr "vsave" (by decide), hsave3, length_arrOf]
  have hfill4 : RowFillAcc "vrow" n (eraseBiNum Outer Inner root) S sigma4 :=
    ⟨hSsub, Acur, hvrow4.trans hAcur, hc4, hnd, hmem⟩
  have hmarks4 : Marks "stf" n 1 ({(root : ℕ)} ∪ S) (fun _ => 0) sigma4 :=
    houter.marks.of_eq hstf4
  have hinner4 : VirtualInnerAcc n W P root (eraseBiNum Outer Inner root)
      outTail p Aout Ain inTail E Deg ER ID BH BV BN S sigma4 :=
    ⟨hfill4, hP4, heng4, hvout4.trans houter.out_eq, hvin4,
      hsaveLen4, htail4, hroot4, hend4, hfj4⟩
  have hfeCap : ∀ q, q < inTail →
      fratFe (root : ℕ) (Ain q) ⊆ eraseBiNum Outer Inner root := by
    intro q hq y hy
    rw [eraseBiNum, Finset.mem_biUnion]
    refine ⟨z, (hout.mem_valSet_iff z).2 ⟨p, hp, rfl⟩, ?_⟩
    rw [eraseBiStep, innerValSet_of_lt Inner hz, Finset.mem_biUnion]
    exact ⟨Ain q, (hrowIn.mem_valSet_iff (Ain q)).2 ⟨q, hq, rfl⟩, hy⟩
  obtain ⟨sigma5, K5, r5, hK5, hmarks5, hacc5⟩ :=
    eraseBiInnerBuffer_run (Inner := Inner) (root := root) (z := z) hz
      hclose (by omega) hnB hCap hrowIn hfeCap hmarks4 hinner4
  have houter5 : EraseBiOuterAcc n W P root (eraseBiNum Outer Inner root)
      (eraseBiStep Inner (root : ℕ)) outTail Aout (p + 1)
      E Deg ER ID BH BV BN sigma5 := by
    refine ⟨?_, ?_, hacc5.persistent, hacc5.engine, hacc5.out_eq,
      by rw [hacc5.in_eq, length_arrOf], hacc5.save_length,
      hacc5.root_eq, hacc5.end_eq⟩
    · simpa only [S, z, bufferAcc_succ] using hmarks5
    · simpa only [S, z, bufferAcc_succ] using hacc5.fill
  refine ⟨sigma5, 12 + (2 + (kin z + (12 + K5))), ?_, ?_, hacc5.outer_eq,
    houter5⟩
  · simpa only [virtualFratInner, sigma0, z] using
      r1.seq (r2.seq (r3.seq (r4.seq r5)))
  · have htailCard : inTail = (Inner ⟨Aout p, hout.value_lt p hp⟩).card := by
      simpa [z] using hrowIn.tail_eq
    rw [htailCard] at hK5
    dsimp [z]
    omega

/-! ## The complete generic outer scan -/

/-- Totalized cost of one generated inner row and its guarded scan. -/
noncomputable def eraseBiRawBudget {n : ℕ} (kin : ℕ → ℕ)
    (Inner : Fin n → Finset (Fin n)) (z : ℕ) : ℕ :=
  if hz : z < n then kin z + 26 * (Inner ⟨z, hz⟩).card + 32 else 0

@[simp] theorem eraseBiRawBudget_of_lt {n : ℕ} (kin : ℕ → ℕ)
    (Inner : Fin n → Finset (Fin n)) {z : ℕ} (hz : z < n) :
    eraseBiRawBudget kin Inner z =
      kin z + 26 * (Inner ⟨z, hz⟩).card + 32 := by
  simp [eraseBiRawBudget, hz]

/-- Per-outer-slot cost, including the reusable-buffer scanner. -/
noncomputable def eraseBiSlotBudget {n : ℕ} (kin : ℕ → ℕ)
    (Inner : Fin n → Finset (Fin n)) (z : ℕ) : ℕ :=
  eraseBiRawBudget kin Inner z + 11

@[simp] theorem eraseBiSlotBudget_of_lt {n : ℕ} (kin : ℕ → ℕ)
    (Inner : Fin n → Finset (Fin n)) {z : ℕ} (hz : z < n) :
    eraseBiSlotBudget kin Inner z =
      kin z + 26 * (Inner ⟨z, hz⟩).card + 43 := by
  rw [eraseBiSlotBudget, eraseBiRawBudget_of_lt kin Inner hz]

/-- Lift the checked nested call through the exact outer row. -/
theorem eraseBiOuter_run {B n W : ℕ} {P : Env → Prop}
    {Outer Inner : Fin n → Finset (Fin n)}
    {provideIn : Com} {kin : ℕ → ℕ}
    {root : Fin n} {outTail : ℕ}
    {Aout : ℕ → ℕ} {E Deg ER ID BH BV BN : ℕ → ℕ} {sigma : Env}
    (hclose : FratScratchClosed P) (hframes : FratIncomingFrames provideIn)
    (hB4 : 3 < B) (hnB : n < B)
    (hpin : ProvidesSetRows B n W Inner P "vin" provideIn kin)
    (hout : SetRowRep (Outer root) outTail Aout)
    (houter0 : EraseBiOuterAcc n W P root (eraseBiNum Outer Inner root)
      (eraseBiStep Inner (root : ℕ)) outTail Aout 0
      E Deg ER ID BH BV BN sigma) :
    ∃ sigma' K,
      Run B (bufferScan "vout" "fj" "fend" "u"
        (virtualFratInner provideIn)) sigma sigma' K ∧
      K ≤ (∑ z ∈ valSet (Outer root), eraseBiSlotBudget kin Inner z) + 6 ∧
      EraseBiOuterAcc n W P root (eraseBiNum Outer Inner root)
        (eraseBiStep Inner (root : ℕ)) outTail Aout outTail
        E Deg ER ID BH BV BN sigma' := by
  let costs : ℕ → ℕ := fun p => eraseBiRawBudget kin Inner (Aout p)
  let I : ℕ → Env → Prop := fun p tau =>
    EraseBiOuterAcc n W P root (eraseBiNum Outer Inner root)
      (eraseBiStep Inner (root : ℕ)) outTail Aout p
      E Deg ER ID BH BV BN tau ∧
      tau.vars "fend" = outTail ∧ tau.vars "fj" = p ∧ p ≤ outTail
  have hstart : I 0 (sigma.setVar "fj" 0) := by
    refine ⟨houter0.setVarPrivate hclose (by decide) (by decide) (by decide)
      (by decide) 0, ?_, by simp, by omega⟩
    simpa using houter0.end_eq
  obtain ⟨sigma', K, hr, hK, hI⟩ :=
    bufferScanC_run (B := B) (len := n) (hi := outTail)
      (src := "vout") (j := "fj") (jend := "fend") (u := "u")
      (body := virtualFratInner provideIn)
      (costs := costs) (A := Aout) (I := I) (sigma := sigma)
      (by decide) (lt_of_le_of_lt hout.tail_le hnB) (by omega) hout.tail_le
      houter0.end_eq
      (fun _ _ h => h.1.out_eq)
      (fun p hp => lt_trans (hout.value_lt p hp) hnB)
      (fun _ _ h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩)
      (by
        intro p tau hIp hp
        obtain ⟨tau', K', hr', hK', hfj', houter'⟩ :=
          eraseBiInner_run hclose hframes hB4 hnB hpin hout hp
            hIp.2.2.1 hIp.1
        refine ⟨tau', K', hr', ?_, hfj', ?_⟩
        · simpa only [costs, eraseBiRawBudget_of_lt kin Inner
            (hout.value_lt p hp)] using hK'
        refine ⟨houter'.setVarPrivate hclose (by decide) (by decide) (by decide)
          (by decide) (p + 1), ?_, by simp, by omega⟩
        rw [vars_setVar, if_neg (by decide)]
        exact houter'.end_eq)
      hstart
  have hsum := hout.sum_slots (eraseBiSlotBudget kin Inner)
  have hcostEq : (∑ p ∈ Finset.range outTail, (costs p + 11)) =
      ∑ z ∈ valSet (Outer root), eraseBiSlotBudget kin Inner z := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [costs, eraseBiSlotBudget]
  rw [hcostEq] at hK
  exact ⟨sigma', K, hr, hK, hI.1⟩

/-! ## Complete compositional provider -/

/-- Total cost of one erased-biunion row. -/
noncomputable def eraseBiCost {n : ℕ} (kout kin : ℕ → ℕ)
    (Outer Inner : Fin n → Finset (Fin n)) (w : ℕ) : ℕ :=
  if hw : w < n then
    kout w +
      (∑ z ∈ valSet (Outer ⟨w, hw⟩), eraseBiSlotBudget kin Inner z) +
      14 * (((Outer ⟨w, hw⟩).biUnion Inner).erase ⟨w, hw⟩).card + 30
  else 0

@[simp] theorem eraseBiCost_of_lt {n : ℕ} (kout kin : ℕ → ℕ)
    (Outer Inner : Fin n → Finset (Fin n)) {w : ℕ} (hw : w < n) :
    eraseBiCost kout kin Outer Inner w =
      kout w +
        (∑ z ∈ valSet (Outer ⟨w, hw⟩), eraseBiSlotBudget kin Inner z) +
        14 * (((Outer ⟨w, hw⟩).biUnion Inner).erase ⟨w, hw⟩).card + 30 := by
  simp [eraseBiCost, hw]

/-! ## Complete provider theorem -/

/-- Two exact row providers compose to the erased nested union of their row
families.  This is the executable transitive-walk combinator used by the
recursive orientation provider. -/
theorem virtualEraseBiUnionProvidesSetRows {B n W : ℕ} {P : Env → Prop}
    {Outer Inner : Fin n → Finset (Fin n)}
    {provideOut provideIn : Com} {kout kin : ℕ → ℕ}
    (hclose : FratScratchClosed P)
    (hfin : FratIncomingFrames provideIn)
    (hfout : FratOutgoingFrames provideOut)
    (hB4 : 3 < B) (hnB : n < B)
    (hpin : ProvidesSetRows B n W Inner P "vin" provideIn kin)
    (hpout : ProvidesSetRows B n W Outer P "vout" provideOut kout) :
    ProvidesSetRows B n W
      (fun root => ((Outer root).biUnion Inner).erase root)
      (FratWorkspace n P) "vrow"
      (virtualFratProvide provideOut provideIn)
      (eraseBiCost kout kin Outer Inner) := by
  classical
  intro root E Deg ER ID BH BV BN
  refine Spec.of_exists fun sigma hpre => ?_
  obtain ⟨hmem, heng, hw⟩ := hpre
  have hrootB : (root : ℕ) < B := lt_trans root.isLt hnB
  obtain ⟨sigma1, r1, hP1, heng1, hstable1,
      outTail, Aout, hrowOut, htail1, hAout1⟩ :=
    (hpout root E Deg ER ID BH BV BN).run ⟨hmem.persistent, heng, hw⟩
  have hw1 : sigma1.vars "w" = (root : ℕ) := by
    rw [hstable1.w_eq, hw]
  have ew1 : (Expr.var "w").evalB B sigma1 = some (root : ℕ) := by
    have h := evalB_var (B := B) (x := "w") (σ := sigma1)
      (by rw [hw1]; exact hrootB)
    rwa [hw1] at h
  let sigma2 := sigma1.setVar "froot" (root : ℕ)
  have r2 : Run B (.assign "froot" (.var "w")) sigma1 sigma2 2 := Run.assign ew1
  have houtTailB : outTail < B := lt_of_le_of_lt hrowOut.tail_le hnB
  have evtail2 : (Expr.var "vtail").evalB B sigma2 = some outTail := by
    have htail2 : sigma2.vars "vtail" = outTail := by simpa [sigma2] using htail1
    have h := evalB_var (B := B) (x := "vtail") (σ := sigma2)
      (by rw [htail2]; exact houtTailB)
    rwa [htail2] at h
  let sigma3 := sigma2.setVar "fend" outTail
  have r3 : Run B (.assign "fend" (.var "vtail")) sigma2 sigma3 2 :=
    Run.assign evtail2
  let sigma4 := sigma3.setVar "c" 0
  have r4 : Run B (.assign "c" (.lit 0)) sigma3 sigma4 2 :=
    Run.assign (evalB_lit (by omega))
  have ew4 : (Expr.var "w").evalB B sigma4 = some (root : ℕ) := by
    simpa [sigma4, sigma3, sigma2] using ew1
  have hstf1 : sigma1.arrs "stf" = arrOf n (fun _ => 0) := by
    rw [r1.frame_arr "stf" hfout.stamp]
    exact hmem.stamp_zero
  have hstf4 : sigma4.arrs "stf" = arrOf n (fun _ => 0) := by
    simpa [sigma4, sigma3, sigma2] using hstf1
  have hrootSlot : (root : ℕ) < (sigma4.arrs "stf").length := by
    rw [hstf4, length_arrOf]
    exact root.isLt
  let sigma5 := sigma4.setArr "stf" (root : ℕ) 1
  have r5 : Run B (.store "stf" (.var "w") (.lit 1)) sigma4 sigma5 3 :=
    Run.store ew4 (evalB_lit (by omega)) hrootSlot
  have hstf5 : sigma5.arrs "stf" =
      arrOf n (fun k => if k = (root : ℕ) then 1 else 0) := by
    simp [sigma5, hstf4, set_arrOf]
  have hmarks5 : Marks "stf" n 1
      ({(root : ℕ)} ∪ bufferAcc 0 Aout
        (eraseBiStep Inner (root : ℕ)))
      (fun _ => 0) sigma5 := by
    refine ⟨fun k => if k = (root : ℕ) then 1 else 0, hstf5, ?_⟩
    intro k hk
    simp
  have hvrow1 : (sigma1.arrs "vrow").length = n := by
    rw [r1.frame_arr "vrow" hfout.vrow]
    exact hmem.vrow_length
  have hvrow5 : (sigma5.arrs "vrow").length = n := by
    simpa [sigma5, sigma4, sigma3, sigma2] using hvrow1
  obtain ⟨A0, hA0⟩ := Lax3Proofs.RamDriver.exists_arrOf hvrow5
  have hfill5 : RowFillAcc "vrow" n (eraseBiNum Outer Inner root)
      (bufferAcc 0 Aout (eraseBiStep Inner (root : ℕ))) sigma5 := by
    refine ⟨by simp, A0, hA0, by simp [sigma5, sigma4], ?_, ?_⟩
    · simp [Lax3Proofs.Refine.OrderVirtualRowRep.rowList]
    · intro z
      simp [Lax3Proofs.Refine.OrderVirtualRowRep.rowList]
  have hvin1 : (sigma1.arrs "vin").length = n := by
    rw [r1.frame_arr "vin" hfout.vin]
    exact hmem.vin_length
  have hvin5 : (sigma5.arrs "vin").length = n := by
    simpa [sigma5, sigma4, sigma3, sigma2] using hvin1
  have hsave1 : (sigma1.arrs "vsave").length = 4 := by
    rw [r1.frame_arr "vsave" hfout.save]
    exact hmem.save_length
  have hsave5 : (sigma5.arrs "vsave").length = 4 := by
    simpa [sigma5, sigma4, sigma3, sigma2] using hsave1
  have hP5 : P sigma5 :=
    hclose.setStamp
      (hclose.setVar (by decide)
        (hclose.setVar (by decide) (hclose.setVar (by decide) hP1)))
  have heng5 : EngineArrays n W E Deg ER ID BH BV BN sigma5 := by
    refine ⟨by simpa [sigma5, sigma4, sigma3, sigma2] using heng1.n_eq,
      by simpa [sigma5, sigma4, sigma3, sigma2] using heng1.elm_eq,
      by simpa [sigma5, sigma4, sigma3, sigma2] using heng1.deg_eq,
      by simpa [sigma5, sigma4, sigma3, sigma2] using heng1.rank_eq,
      by simpa [sigma5, sigma4, sigma3, sigma2] using heng1.idg_eq,
      by simpa [sigma5, sigma4, sigma3, sigma2] using heng1.head_eq,
      by simpa [sigma5, sigma4, sigma3, sigma2] using heng1.val_eq,
      by simpa [sigma5, sigma4, sigma3, sigma2] using heng1.next_eq⟩
  have hout5 : sigma5.arrs "vout" = arrOf n Aout := by
    simpa [sigma5, sigma4, sigma3, sigma2] using hAout1
  have houter5 : EraseBiOuterAcc n W P root (eraseBiNum Outer Inner root)
      (eraseBiStep Inner (root : ℕ)) outTail Aout 0
      E Deg ER ID BH BV BN sigma5 := by
    refine ⟨hmarks5, hfill5, hP5, heng5, hout5, hvin5, hsave5, ?_, ?_⟩
    · simp [sigma5, sigma4, sigma3, sigma2]
    · simp [sigma5, sigma4, sigma3]
  obtain ⟨sigma6, K6, r6, hK6, houter6⟩ :=
    eraseBiOuter_run hclose hfin hB4 hnB hpin hrowOut houter5
  have hfull : bufferAcc outTail Aout (eraseBiStep Inner (root : ℕ)) =
      eraseBiNum Outer Inner root := by
    simpa only [eraseBiNum] using
      bufferAcc_eq_biUnion_valSet hrowOut (eraseBiStep Inner (root : ℕ))
  have hmarks6 := houter6.marks
  have hfill6 := houter6.fill
  rw [hfull, eraseBiNum_eq Outer Inner root] at hmarks6 hfill6
  obtain ⟨Arow, hArow6, hc6, hrow⟩ := hfill6.toSetRowRep
  obtain ⟨g, hstf6, hg⟩ := hmarks6
  let target := ((Outer root).biUnion Inner).erase root
  obtain ⟨sigma7, K7, r7, hK7, hclear7⟩ :=
    stampBuffer_run (B := B) (n := n) (tail := target.card)
      (b := 0) (src := "vrow") (j := "fc") (jend := "c")
      (u := "u") (s := "stf") (S := target) (A := Arow)
      (g := g) (sigma := sigma6) (by decide) (by decide) (by decide)
      (by decide) (by omega) hnB (by omega) hrow hc6 hArow6 hstf6
  have hP7 : P sigma7 := by
    apply hclose.run r7
    · intro a ha
      intro han
      subst a
      simpa [bufferScan, Lax3Proofs.RamDriverAugment.scanBody, Csr.scan,
        Com.wvars] using ha
    · intro a ha
      simp [bufferScan, Lax3Proofs.RamDriverAugment.scanBody, Csr.scan,
        Com.warrs] at ha
      exact Or.inr (Or.inl ha)
    · decide
    · decide
    · exact houter6.persistent
  obtain ⟨g7, hstf7, hg7⟩ := hclear7
  have hg7root : ∀ k < n,
      g7 k = if k = (root : ℕ) then 1 else 0 := by
    intro k hk
    rw [hg7 k hk, hg k hk]
    by_cases hkS : k ∈ valSet target
    · have hkr : k ≠ (root : ℕ) := by
        intro hkr
        subst k
        obtain ⟨hkn, hm⟩ := mem_valSet.1 hkS
        exact (Finset.mem_erase.1 hm).1 (Fin.ext rfl)
      dsimp [target] at hkS ⊢
      simp [hkS, hkr]
    · dsimp [target] at hkS ⊢
      simp [hkS]
  have hstf7root : sigma7.arrs "stf" =
      arrOf n (fun k => if k = (root : ℕ) then 1 else 0) :=
    hstf7.trans (arrOf_congr hg7root)
  have hfroot7 : sigma7.vars "froot" = (root : ℕ) := by
    rw [r7.frame_var "froot" (by decide)]
    exact houter6.root_eq
  have efroot7 : (Expr.var "froot").evalB B sigma7 = some (root : ℕ) := by
    have h := evalB_var (B := B) (x := "froot") (σ := sigma7)
      (by rw [hfroot7]; exact hrootB)
    rwa [hfroot7] at h
  let sigma8 := sigma7.setVar "u" (root : ℕ)
  have r8 : Run B (.assign "u" (.var "froot")) sigma7 sigma8 2 :=
    Run.assign efroot7
  have hP8 : P sigma8 := hclose.setVar (by decide) hP7
  have eu8 : (Expr.var "u").evalB B sigma8 = some (root : ℕ) := by
    have h := evalB_var (B := B) (x := "u") (σ := sigma8)
      (by simp [sigma8, hrootB])
    simpa [sigma8] using h
  have hrootSlot8 : (root : ℕ) < (sigma8.arrs "stf").length := by
    rw [arrs_setVar, hstf7root, length_arrOf]
    exact root.isLt
  let sigma9 := sigma8.setArr "stf" (root : ℕ) 0
  have r9 : Run B (.store "stf" (.var "u") (.lit 0)) sigma8 sigma9 3 :=
    Run.store eu8 (evalB_lit (by omega)) hrootSlot8
  have hP9 : P sigma9 := hclose.setStamp hP8
  have hstf9 : sigma9.arrs "stf" = arrOf n (fun _ => 0) := by
    change (sigma8.setArr "stf" (root : ℕ) 0).arrs "stf" =
      arrOf n (fun _ => 0)
    rw [arrs_setArr, if_pos rfl, arrs_setVar, hstf7root, set_arrOf]
    apply arrOf_congr
    intro k hk
    by_cases hkr : k = (root : ℕ) <;> simp [hkr]
  have hfroot9 : sigma9.vars "froot" = (root : ℕ) := by
    simp [sigma9, sigma8, hfroot7]
  have efroot9 : (Expr.var "froot").evalB B sigma9 = some (root : ℕ) := by
    have h := evalB_var (B := B) (x := "froot") (σ := sigma9)
      (by rw [hfroot9]; exact hrootB)
    rwa [hfroot9] at h
  let sigma10 := sigma9.setVar "w" (root : ℕ)
  have r10 : Run B (.assign "w" (.var "froot")) sigma9 sigma10 2 :=
    Run.assign efroot9
  have hP10 : P sigma10 := hclose.setVar (by decide) hP9
  have hc7 : sigma7.vars "c" = target.card := by
    rw [r7.frame_var "c" (by decide)]
    exact hc6
  have hc10 : sigma10.vars "c" = target.card := by
    simpa [sigma10, sigma9, sigma8] using hc7
  have hcardB : target.card < B := lt_of_le_of_lt hrow.tail_le hnB
  have ec10 : (Expr.var "c").evalB B sigma10 = some target.card := by
    have h := evalB_var (B := B) (x := "c") (σ := sigma10)
      (by rw [hc10]; exact hcardB)
    rwa [hc10] at h
  let sigma11 := sigma10.setVar "vtail" target.card
  have r11 : Run B (.assign "vtail" (.var "c")) sigma10 sigma11 2 :=
    Run.assign ec10
  have hP11 : P sigma11 := hclose.setVar (by decide) hP10
  have rAll : Run B (virtualFratProvide provideOut provideIn) sigma sigma11
      (kout (root : ℕ) +
        (2 + (2 + (2 + (3 + (K6 + (K7 + (2 + (3 + (2 + 2)))))))))) := by
    simpa only [virtualFratProvide] using
      r1.seq (r2.seq (r3.seq (r4.seq (r5.seq
        (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq r11)))))))))
  have hcost : kout (root : ℕ) +
        (2 + (2 + (2 + (3 + (K6 + (K7 + (2 + (3 + (2 + 2))))))))) ≤
      eraseBiCost kout kin Outer Inner (root : ℕ) := by
    rw [eraseBiCost_of_lt kout kin Outer Inner root.isLt]
    have hroot : (⟨(root : ℕ), root.isLt⟩ : Fin n) = root := Fin.ext rfl
    rw [hroot]
    dsimp [target] at hK7 ⊢
    omega
  have heng7 : EngineArrays n W E Deg ER ID BH BV BN sigma7 := by
    refine ⟨by rw [r7.frame_var "n" (by decide)]; exact houter6.engine.n_eq,
      by rw [r7.frame_arr "elm" (by decide)]; exact houter6.engine.elm_eq,
      by rw [r7.frame_arr "deg" (by decide)]; exact houter6.engine.deg_eq,
      by rw [r7.frame_arr "rnk" (by decide)]; exact houter6.engine.rank_eq,
      by rw [r7.frame_arr "idg" (by decide)]; exact houter6.engine.idg_eq,
      by rw [r7.frame_arr "bh" (by decide)]; exact houter6.engine.head_eq,
      by rw [r7.frame_arr "bv" (by decide)]; exact houter6.engine.val_eq,
      by rw [r7.frame_arr "bn" (by decide)]; exact houter6.engine.next_eq⟩
  have heng11 : EngineArrays n W E Deg ER ID BH BV BN sigma11 := by
    refine ⟨by simpa [sigma11, sigma10, sigma9, sigma8] using heng7.n_eq,
      by simpa [sigma11, sigma10, sigma9, sigma8] using heng7.elm_eq,
      by simpa [sigma11, sigma10, sigma9, sigma8] using heng7.deg_eq,
      by simpa [sigma11, sigma10, sigma9, sigma8] using heng7.rank_eq,
      by simpa [sigma11, sigma10, sigma9, sigma8] using heng7.idg_eq,
      by simpa [sigma11, sigma10, sigma9, sigma8] using heng7.head_eq,
      by simpa [sigma11, sigma10, sigma9, sigma8] using heng7.val_eq,
      by simpa [sigma11, sigma10, sigma9, sigma8] using heng7.next_eq⟩
  have hvout7 : sigma7.arrs "vout" = arrOf n Aout := by
    rw [r7.frame_arr "vout" (by decide)]
    exact houter6.out_eq
  have hvin7 : (sigma7.arrs "vin").length = n := by
    rw [congrArg List.length (r7.frame_arr "vin" (by decide))]
    exact houter6.vin_length
  have hvrow7 : sigma7.arrs "vrow" = arrOf n Arow := by
    rw [r7.frame_arr "vrow" (by decide)]
    exact hArow6
  have hsave7 : (sigma7.arrs "vsave").length = 4 := by
    rw [congrArg List.length (r7.frame_arr "vsave" (by decide))]
    exact houter6.save_length
  have hmem11 : FratWorkspace n P sigma11 := by
    refine ⟨hP11, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [sigma11, sigma10, sigma9, sigma8] using
        congrArg List.length hvout7
    · simpa [sigma11, sigma10, sigma9, sigma8] using hvin7
    · simpa [sigma11, sigma10, sigma9, sigma8] using
        congrArg List.length hvrow7
    · simpa [sigma11, sigma10, sigma9, sigma8] using hsave7
    · simpa [sigma11, sigma10] using hstf9
  have hstable11 : ProviderStable sigma sigma11 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply rAll.frame_var "n"
      simp [virtualFratProvide, virtualFratInner, fratSaveState,
        fratRestoreState, fratSave, fratRestore, bufferScan,
        Lax3Proofs.RamDriverAugment.fratGuard, rowFillAct,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.wvars,
        hfout.stable.n, hfin.stable.n]
    · calc
        sigma11.vars "w" = (root : ℕ) := by simp [sigma11, sigma10]
        _ = sigma.vars "w" := hw.symm
    · apply rAll.frame_var "i"
      simp [virtualFratProvide, virtualFratInner, fratSaveState,
        fratRestoreState, fratSave, fratRestore, bufferScan,
        Lax3Proofs.RamDriverAugment.fratGuard, rowFillAct,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.wvars,
        hfout.stable.i, hfin.stable.i]
    · apply rAll.frame_var "sp"
      simp [virtualFratProvide, virtualFratInner, fratSaveState,
        fratRestoreState, fratSave, fratRestore, bufferScan,
        Lax3Proofs.RamDriverAugment.fratGuard, rowFillAct,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.wvars,
        hfout.stable.sp, hfin.stable.sp]
    · apply rAll.frame_var "ls"
      simp [virtualFratProvide, virtualFratInner, fratSaveState,
        fratRestoreState, fratSave, fratRestore, bufferScan,
        Lax3Proofs.RamDriverAugment.fratGuard, rowFillAct,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.wvars,
        hfout.stable.ls, hfin.stable.ls]
    · apply rAll.frame_var "cnt"
      simp [virtualFratProvide, virtualFratInner, fratSaveState,
        fratRestoreState, fratSave, fratRestore, bufferScan,
        Lax3Proofs.RamDriverAugment.fratGuard, rowFillAct,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.wvars,
        hfout.stable.cnt, hfin.stable.cnt]
    · apply rAll.frame_var "mind"
      simp [virtualFratProvide, virtualFratInner, fratSaveState,
        fratRestoreState, fratSave, fratRestore, bufferScan,
        Lax3Proofs.RamDriverAugment.fratGuard, rowFillAct,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.wvars,
        hfout.stable.mind, hfin.stable.mind]
    · apply rAll.frame_var "kmax"
      simp [virtualFratProvide, virtualFratInner, fratSaveState,
        fratRestoreState, fratSave, fratRestore, bufferScan,
        Lax3Proofs.RamDriverAugment.fratGuard, rowFillAct,
        Lax3Proofs.RamDriverAugment.scanBody, Csr.scan, Com.wvars,
        hfout.stable.kmax, hfin.stable.kmax]
  refine ⟨sigma11,
    kout (root : ℕ) +
      (2 + (2 + (2 + (3 + (K6 + (K7 + (2 + (3 + (2 + 2))))))))),
    rAll, hcost, hmem11, heng11, hstable11,
    target.card, Arow, ?_, ?_, ?_⟩
  · simpa only [target] using hrow
  · simp [sigma11]
  · simpa [sigma11, sigma10, sigma9, sigma8] using hvrow7

/-- Executable incoming two-path rows from two independently named copies of
the previous incoming-row provider. -/
theorem virtualTransInProvidesSetRows {B n W : ℕ} {P : Env → Prop}
    {D : Orientation n} {provideOuter provideInner : Com}
    {kouter kinner : ℕ → ℕ}
    (hclose : FratScratchClosed P)
    (hinnerFrames : FratIncomingFrames provideInner)
    (houterFrames : FratOutgoingFrames provideOuter)
    (hB4 : 3 < B) (hnB : n < B)
    (hinner : ProvidesSetRows B n W (fun w => D.inN w)
      P "vin" provideInner kinner)
    (houter : ProvidesSetRows B n W (fun w => D.inN w)
      P "vout" provideOuter kouter) :
    ProvidesSetRows B n W (transInSet D) (FratWorkspace n P) "vrow"
      (virtualFratProvide provideOuter provideInner)
      (eraseBiCost kouter kinner (fun w => D.inN w) (fun w => D.inN w)) := by
  simpa only [transInSet] using
    virtualEraseBiUnionProvidesSetRows hclose hinnerFrames houterFrames
      hB4 hnB hinner houter

/-- Executable outgoing two-path rows from two independently named copies of
the previous outgoing-row provider. -/
theorem virtualTransOutProvidesSetRows {B n W : ℕ} {P : Env → Prop}
    {D : Orientation n} {provideOuter provideInner : Com}
    {kouter kinner : ℕ → ℕ}
    (hclose : FratScratchClosed P)
    (hinnerFrames : FratIncomingFrames provideInner)
    (houterFrames : FratOutgoingFrames provideOuter)
    (hB4 : 3 < B) (hnB : n < B)
    (hinner : ProvidesSetRows B n W (outSet D)
      P "vin" provideInner kinner)
    (houter : ProvidesSetRows B n W (outSet D)
      P "vout" provideOuter kouter) :
    ProvidesSetRows B n W (transOutSet D) (FratWorkspace n P) "vrow"
      (virtualFratProvide provideOuter provideInner)
      (eraseBiCost kouter kinner (outSet D) (outSet D)) := by
  simpa only [transOutSet] using
    virtualEraseBiUnionProvidesSetRows hclose hinnerFrames houterFrames
      hB4 hnB hinner houter

/-! ## Axiom audit -/

#print axioms eraseBiNum_eq
#print axioms eraseBiInner_run
#print axioms eraseBiOuter_run
#print axioms virtualEraseBiUnionProvidesSetRows
#print axioms virtualTransInProvidesSetRows
#print axioms virtualTransOutProvidesSetRows

end Lax3Proofs.Refine.OrderVirtualBiUnion
