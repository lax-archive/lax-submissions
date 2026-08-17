import Lax3Proofs.Refine.OrderVirtualBaseOrient

/-!
# Virtual fraternity rows of the base orientation

The base orientation remains implicit: an outgoing row is generated into one
carrier-sized buffer, and for each of its entries an incoming row is generated
into a second buffer.  A stamp removes repeated witnesses and the requested
vertex itself.  No oriented edge array or fraternity graph is materialized.
-/

namespace Lax3Proofs.Refine.OrderVirtualBaseFrat

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.Augmentation
open Lax3Proofs.Augmentation.Orientation
open Lax3Proofs.RamElim (CsrSimple ElimCert)
open Lax3Proofs.RamAugment (outSet fratNbrs mem_outSet mem_fratNbrs)
open Lax3Proofs.RamDriverAugment
open Lax3Proofs.Refine.OrderVirtualProvider
open Lax3Proofs.Refine.OrderVirtualSetRow
open Lax3Proofs.Refine.OrderVirtualBaseOrient
open Lax3Proofs.Refine.OrderVirtualBucket (bucketExtra)
open Lax3Proofs.Refine.OrderVirtualLoop (VirtualElimResult)
open Lax3Proofs.Refine.OrderVirtualDriver (virtualElim virtualElimCost)

variable {n : ℕ}

/-! ## The numeric set enumerated by the nested buffers -/

/-- The fraternity guard contributes a singleton except at the requested
root, where it contributes nothing. -/
def fratFe (root z : ℕ) : Finset ℕ := if z = root then ∅ else {z}

/-- Numeric incoming row, totalized away from the carrier. -/
noncomputable def inValSet (D : Orientation n) (z : ℕ) : Finset ℕ :=
  if hz : z < n then valSet (D.inN ⟨z, hz⟩) else ∅

/-- Contribution of one outgoing neighbour: its incoming row with the root
removed. -/
noncomputable def fratStep (D : Orientation n) (root z : ℕ) : Finset ℕ :=
  (inValSet D z).biUnion (fratFe root)

/-- Complete numeric result of the nested outgoing/incoming walk. -/
noncomputable def fratNum (D : Orientation n) (root : Fin n) : Finset ℕ :=
  (valSet (outSet D root)).biUnion (fratStep D (root : ℕ))

@[simp] theorem inValSet_of_lt (D : Orientation n) {z : ℕ} (hz : z < n) :
    inValSet D z = valSet (D.inN ⟨z, hz⟩) := by
  simp [inValSet, hz]

theorem mem_fratStep {D : Orientation n} {root : Fin n} {z y : ℕ}
    (hz : z < n) :
    y ∈ fratStep D (root : ℕ) z ↔
      ∃ hy : y < n, (⟨y, hy⟩ : Fin n) ∈ D.inN ⟨z, hz⟩ ∧ y ≠ (root : ℕ) := by
  simp only [fratStep, inValSet_of_lt D hz, Finset.mem_biUnion, mem_valSet]
  constructor
  · rintro ⟨u, ⟨hu, huD⟩, hy⟩
    rw [fratFe] at hy
    by_cases hur : u = (root : ℕ)
    · simp [hur] at hy
    · have hyu : y = u := by simpa [hur] using hy
      subst y
      exact ⟨hu, huD, hur⟩
  · rintro ⟨hy, hyD, hyr⟩
    refine ⟨y, ⟨hy, hyD⟩, ?_⟩
    simp [fratFe, hyr]

/-- The nested numeric walk is exactly the numeric image of the fraternity
row. -/
theorem fratNum_eq (D : Orientation n) (root : Fin n) :
    fratNum D root = valSet (fratNbrs D root) := by
  classical
  ext y
  rw [fratNum, Finset.mem_biUnion, mem_valSet]
  constructor
  · rintro ⟨z, hzOut, hyStep⟩
    obtain ⟨hzn, hzOutD⟩ := mem_valSet.1 hzOut
    obtain ⟨hyn, hyIn, hyr⟩ := (mem_fratStep hzn).1 hyStep
    refine ⟨hyn, ?_⟩
    rw [Lax3Proofs.RamAugment.fratNbrs_eq, Finset.mem_erase,
      Finset.mem_biUnion]
    exact ⟨fun h => hyr (congrArg Fin.val h),
      ⟨z, hzn⟩, hzOutD, hyIn⟩
  · rintro ⟨hyn, hyFrat⟩
    rw [Lax3Proofs.RamAugment.fratNbrs_eq, Finset.mem_erase,
      Finset.mem_biUnion] at hyFrat
    obtain ⟨hyr, z, hzOut, hyIn⟩ := hyFrat
    refine ⟨(z : ℕ), mem_valSet_of hzOut, ?_⟩
    apply (mem_fratStep z.isLt).2
    exact ⟨hyn, hyIn, fun h => hyr (Fin.ext h)⟩

/-! ## Executable command -/

/-- One outgoing-buffer slot: preserve the output count, generate the
candidate's incoming row, restore the count, and feed that row to the
fraternity guard. -/
def baseFratInner (o t rk vin dst : String) : Com :=
  .seq (.assign "fcount" (.var "c"))
    (.seq (.assign "w" (.var "u"))
      (.seq (baseOrientProvide .incoming o t rk vin)
        (.seq (.assign "c" (.var "fcount"))
          (bufferScan vin "fk" "vtail" "u"
            (fratGuard (rowFillAct dst))))))

/-- Generate one exact fraternity row and return the stamp array to zero. -/
def baseFratProvide (o t rk vout vin dst : String) : Com :=
  .seq (.assign "froot" (.var "w"))
    (.seq (baseOrientProvide .outgoing o t rk vout)
      (.seq (.assign "fend" (.var "vtail"))
        (.seq (.assign "c" (.lit 0))
          (.seq (.store "stf" (.var "w") (.lit 1))
            (.seq (bufferScan vout "fj" "fend" "u"
                (baseFratInner o t rk vin dst))
              (.seq (bufferScan dst "fc" "c" "u"
                  (.store "stf" (.var "u") (.lit 0)))
                (.seq (.assign "u" (.var "froot"))
                  (.seq (.store "stf" (.var "u") (.lit 0))
                    (.seq (.assign "w" (.var "froot"))
                      (.assign "vtail" (.var "c")))))))))))

/-! ## Fixed workspace and loop invariants -/

/-- Persistent memory used by the base fraternity provider.  The literal
names keep the proof obligations decidable and are the names used by the
campaign driver. -/
structure BaseFratMem (n nt : ℕ) (O T R : ℕ → ℕ) (sigma : Env) : Prop where
  input : BaseOrientInput n nt "off" "tgt" "vr0" O T R sigma
  vout_length : (sigma.arrs "vout").length = n
  vin_length : (sigma.arrs "vin").length = n
  vrow_length : (sigma.arrs "vrow").length = n
  stamp_zero : sigma.arrs "stf" = arrOf n (fun _ => 0)

/-- The virtual engine may mutate its own scalars and arrays while the base
fraternity input and private buffers remain available. -/
theorem baseFratMem_engineClosed {n nt : ℕ} {O T R : ℕ → ℕ} :
    EngineClosed (BaseFratMem n nt O T R) := by
  constructor
  · intro sigma a v ha hP
    exact ⟨hP.input.setVar a v, by simpa using hP.vout_length,
      by simpa using hP.vin_length, by simpa using hP.vrow_length,
      by simpa using hP.stamp_zero⟩
  · intro sigma a i v ha hP
    have hao : a ≠ "off" := by
      intro h
      subst a
      simpa [engineArrNames] using ha
    have hat : a ≠ "tgt" := by
      intro h
      subst a
      simpa [engineArrNames] using ha
    have har : a ≠ "vr0" := by
      intro h
      subst a
      simpa [engineArrNames] using ha
    have havout : a ≠ "vout" := by
      intro h
      subst a
      simpa [engineArrNames] using ha
    have havin : a ≠ "vin" := by
      intro h
      subst a
      simpa [engineArrNames] using ha
    have hastf : a ≠ "stf" := by
      intro h
      subst a
      simpa [engineArrNames] using ha
    refine ⟨⟨by rw [arrs_setArr, if_neg (Ne.symm hao)]; exact hP.input.off_eq,
      by rw [arrs_setArr, if_neg (Ne.symm hat)]; exact hP.input.tgt_eq,
      by rw [arrs_setArr, if_neg (Ne.symm har)]; exact hP.input.rank_eq⟩,
      by rw [arrs_setArr, if_neg (Ne.symm havout)]; exact hP.vout_length,
      by rw [arrs_setArr, if_neg (Ne.symm havin)]; exact hP.vin_length,
      ?_, by rw [arrs_setArr, if_neg (Ne.symm hastf)]; exact hP.stamp_zero⟩
    rw [arrs_setArr]
    by_cases havrow : "vrow" = a
    · subst a
      simp [hP.vrow_length]
    · rw [if_neg havrow]
      exact hP.vrow_length

theorem baseFratMem_engineRunClosed {n nt : ℕ} {O T R : ℕ → ℕ} :
    EngineRunClosed (BaseFratMem n nt O T R) := by
  intro B K c sigma sigma' hrun hwv hwa hP
  have frame (a : String) (ha : a ∉ engineArrNames) :
      sigma'.arrs a = sigma.arrs a := by
    apply hrun.frame_arr a
    intro hac
    exact ha (hwa a hac)
  refine ⟨⟨by rw [frame "off" (by decide)]; exact hP.input.off_eq,
      by rw [frame "tgt" (by decide)]; exact hP.input.tgt_eq,
      by rw [frame "vr0" (by decide)]; exact hP.input.rank_eq⟩,
    by rw [frame "vout" (by decide)]; exact hP.vout_length,
    by rw [frame "vin" (by decide)]; exact hP.vin_length, ?_,
    by rw [frame "stf" (by decide)]; exact hP.stamp_zero⟩
  rw [Lax3Proofs.RamDriver.run_length_arrs hrun "vrow", hP.vrow_length]

/-- State carried by the outer scan after `p` outgoing-buffer slots. -/
structure OuterAcc (n nt W : ℕ) (O T R : ℕ → ℕ)
    (D : Orientation n) (root : Fin n) (Cap : Finset ℕ)
    (outTail : ℕ) (Aout : ℕ → ℕ) (p : ℕ)
    (E Deg ER ID BH BV BN : ℕ → ℕ) (tau : Env) : Prop where
  marks : Marks "stf" n 1
    ({(root : ℕ)} ∪ bufferAcc p Aout (fratStep D (root : ℕ))) (fun _ => 0) tau
  fill : RowFillAcc "vrow" n Cap
    (bufferAcc p Aout (fratStep D (root : ℕ))) tau
  input : BaseOrientInput n nt "off" "tgt" "vr0" O T R tau
  engine : EngineArrays n W E Deg ER ID BH BV BN tau
  out_eq : tau.arrs "vout" = arrOf n Aout
  vin_length : (tau.arrs "vin").length = n
  root_eq : tau.vars "froot" = (root : ℕ)
  end_eq : tau.vars "fend" = outTail

namespace OuterAcc

theorem setVarPrivate {n nt W : ℕ} {O T R : ℕ → ℕ}
    {D : Orientation n} {root : Fin n} {Cap : Finset ℕ}
    {outTail : ℕ} {Aout : ℕ → ℕ} {p : ℕ}
    {E Deg ER ID BH BV BN : ℕ → ℕ} {tau : Env}
    (h : OuterAcc n nt W O T R D root Cap outTail Aout p
      E Deg ER ID BH BV BN tau)
    {y : String} (hyn : y ≠ "n") (hyr : y ≠ "froot")
    (hye : y ≠ "fend") (hyc : y ≠ "c") (x : ℕ) :
    OuterAcc n nt W O T R D root Cap outTail Aout p
      E Deg ER ID BH BV BN (tau.setVar y x) := by
  refine ⟨h.marks.setVar y x, h.fill.setVar hyc x, h.input.setVar y x, ?_,
    by simpa using h.out_eq, by simpa using h.vin_length, ?_, ?_⟩
  · exact ⟨by rw [vars_setVar, if_neg (Ne.symm hyn)]; exact h.engine.n_eq,
      by simpa using h.engine.elm_eq, by simpa using h.engine.deg_eq,
      by simpa using h.engine.rank_eq, by simpa using h.engine.idg_eq,
      by simpa using h.engine.head_eq, by simpa using h.engine.val_eq,
      by simpa using h.engine.next_eq⟩
  · rw [vars_setVar, if_neg (Ne.symm hyr)]; exact h.root_eq
  · rw [vars_setVar, if_neg (Ne.symm hye)]; exact h.end_eq

end OuterAcc

/-- Accounting carried by the inner guarded scan. -/
structure InnerAcc (n nt W : ℕ) (O T R : ℕ → ℕ)
    (root : Fin n) (Cap : Finset ℕ) (outTail outerPos : ℕ)
    (Aout Ain : ℕ → ℕ) (inTail : ℕ)
    (E Deg ER ID BH BV BN : ℕ → ℕ) (S : Finset ℕ) (tau : Env) : Prop where
  fill : RowFillAcc "vrow" n Cap S tau
  input : BaseOrientInput n nt "off" "tgt" "vr0" O T R tau
  engine : EngineArrays n W E Deg ER ID BH BV BN tau
  out_eq : tau.arrs "vout" = arrOf n Aout
  in_eq : tau.arrs "vin" = arrOf n Ain
  in_tail_eq : tau.vars "vtail" = inTail
  root_eq : tau.vars "froot" = (root : ℕ)
  end_eq : tau.vars "fend" = outTail
  outer_eq : tau.vars "fj" = outerPos

namespace InnerAcc

theorem setVarPrivate {n nt W : ℕ} {O T R : ℕ → ℕ}
    {root : Fin n} {Cap : Finset ℕ} {outTail outerPos : ℕ}
    {Aout Ain : ℕ → ℕ} {inTail : ℕ} {E Deg ER ID BH BV BN : ℕ → ℕ}
    {S : Finset ℕ} {tau : Env}
    (h : InnerAcc n nt W O T R root Cap outTail outerPos Aout Ain inTail
      E Deg ER ID BH BV BN S tau)
    {y : String} (hyc : y ≠ "c") (hyn : y ≠ "n")
    (hyvt : y ≠ "vtail") (hyr : y ≠ "froot") (hye : y ≠ "fend")
    (hyo : y ≠ "fj") (x : ℕ) :
    InnerAcc n nt W O T R root Cap outTail outerPos Aout Ain inTail
      E Deg ER ID BH BV BN S (tau.setVar y x) := by
  refine ⟨h.fill.setVar hyc x, h.input.setVar y x, ?_, by simpa using h.out_eq,
    by simpa using h.in_eq, ?_, ?_, ?_, ?_⟩
  · exact ⟨by rw [vars_setVar, if_neg (Ne.symm hyn)]; exact h.engine.n_eq,
      by simpa using h.engine.elm_eq, by simpa using h.engine.deg_eq,
      by simpa using h.engine.rank_eq, by simpa using h.engine.idg_eq,
      by simpa using h.engine.head_eq, by simpa using h.engine.val_eq,
      by simpa using h.engine.next_eq⟩
  · rw [vars_setVar, if_neg (Ne.symm hyvt)]; exact h.in_tail_eq
  · rw [vars_setVar, if_neg (Ne.symm hyr)]; exact h.root_eq
  · rw [vars_setVar, if_neg (Ne.symm hye)]; exact h.end_eq
  · rw [vars_setVar, if_neg (Ne.symm hyo)]; exact h.outer_eq

theorem setStamp {n nt W : ℕ} {O T R : ℕ → ℕ}
    {root : Fin n} {Cap : Finset ℕ} {outTail outerPos : ℕ}
    {Aout Ain : ℕ → ℕ} {inTail : ℕ} {E Deg ER ID BH BV BN : ℕ → ℕ}
    {S : Finset ℕ} {tau : Env}
    (h : InnerAcc n nt W O T R root Cap outTail outerPos Aout Ain inTail
      E Deg ER ID BH BV BN S tau) (p x : ℕ) :
    InnerAcc n nt W O T R root Cap outTail outerPos Aout Ain inTail
      E Deg ER ID BH BV BN S (tau.setArr "stf" p x) := by
  refine ⟨h.fill.setArr_of_ne (by decide) p x, ?_, ?_, ?_, ?_, by simpa using h.in_tail_eq,
    by simpa using h.root_eq, by simpa using h.end_eq, by simpa using h.outer_eq⟩
  · exact ⟨by simpa using h.input.off_eq, by simpa using h.input.tgt_eq,
      by simpa using h.input.rank_eq⟩
  · exact ⟨by simpa using h.engine.n_eq, by simpa using h.engine.elm_eq,
      by simpa using h.engine.deg_eq, by simpa using h.engine.rank_eq,
      by simpa using h.engine.idg_eq, by simpa using h.engine.head_eq,
      by simpa using h.engine.val_eq, by simpa using h.engine.next_eq⟩
  · simpa using h.out_eq
  · simpa using h.in_eq

end InnerAcc

/-- Extending the exact output accumulator preserves all fixed inner-scan
state. -/
theorem innerAcc_emits {B n nt W : ℕ} {O T R : ℕ → ℕ}
    {root : Fin n} {Cap : Finset ℕ} {outTail outerPos : ℕ}
    {Aout Ain : ℕ → ℕ} {inTail : ℕ} {E Deg ER ID BH BV BN : ℕ → ℕ}
    (hnB : n < B) (hCap : Cap ⊆ Finset.range n) :
    Emits B n 7 "vrow" "@" (rowFillAct "vrow") Cap
      (InnerAcc n nt W O T R root Cap outTail outerPos Aout Ain inTail
        E Deg ER ID BH BV BN) := by
  rintro S tau z hA hu hzn hzS hzCap
  obtain ⟨tau', K, hr, hK, hfill, hfv, hfa⟩ :=
    rowFillAcc_emits (dst := "vrow") hnB hCap S tau z hA.fill hu hzn hzS hzCap
  refine ⟨tau', K, hr, hK, ?_, hfv, hfa⟩
  refine ⟨hfill, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hA.input.of_emit_frame (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) hfa
  · exact ⟨by rw [hfv "n" (by decide)]; exact hA.engine.n_eq,
      by rw [hfa "elm" (by decide) (by decide)]; exact hA.engine.elm_eq,
      by rw [hfa "deg" (by decide) (by decide)]; exact hA.engine.deg_eq,
      by rw [hfa "rnk" (by decide) (by decide)]; exact hA.engine.rank_eq,
      by rw [hfa "idg" (by decide) (by decide)]; exact hA.engine.idg_eq,
      by rw [hfa "bh" (by decide) (by decide)]; exact hA.engine.head_eq,
      by rw [hfa "bv" (by decide) (by decide)]; exact hA.engine.val_eq,
      by rw [hfa "bn" (by decide) (by decide)]; exact hA.engine.next_eq⟩
  · rw [hfa "vout" (by decide) (by decide)]; exact hA.out_eq
  · rw [hfa "vin" (by decide) (by decide)]; exact hA.in_eq
  · rw [hfv "vtail" (by decide)]; exact hA.in_tail_eq
  · rw [hfv "froot" (by decide)]; exact hA.root_eq
  · rw [hfv "fend" (by decide)]; exact hA.end_eq
  · rw [hfv "fj" (by decide)]; exact hA.outer_eq

/-- The standard fraternity stamp guard, specialized to the exact output
accumulator and the fixed virtual workspace. -/
theorem innerAcc_guarded {B n nt W : ℕ} {O T R : ℕ → ℕ}
    {root : Fin n} {Cap : Finset ℕ} {outTail outerPos : ℕ}
    {Aout Ain : ℕ → ℕ} {inTail : ℕ} {E Deg ER ID BH BV BN : ℕ → ℕ}
    (hB1 : 1 < B) (hnB : n < B) (hCap : Cap ⊆ Finset.range n) :
    Guarded B n 15 (fratGuard (rowFillAct "vrow"))
      (fratFe (root : ℕ)) Cap
      (fun S tau => Marks "stf" n 1 ({(root : ℕ)} ∪ S) (fun _ => 0) tau ∧
        InnerAcc n nt W O T R root Cap outTail outerPos Aout Ain inTail
          E Deg ER ID BH BV BN S tau) := by
  have he := innerAcc_emits (B := B) (n := n) (nt := nt) (W := W)
    (O := O) (T := T) (R := R) (root := root) (Cap := Cap)
    (outTail := outTail) (outerPos := outerPos) (Aout := Aout) (Ain := Ain)
    (inTail := inTail) (E := E) (Deg := Deg) (ER := ER) (ID := ID)
    (BH := BH) (BV := BV) (BN := BN) hnB hCap
  have hg := guardFrat_of_emits (B := B) (n := n) (Ka := 7)
    (i := (root : ℕ)) (a₁ := "vrow") (a₂ := "@")
    (act := rowFillAct "vrow") (Cap := Cap)
    (ha₁ := by decide) (ha₂ := by decide) hB1 hnB
    (fun _ _ p x h => h.setStamp p x) he
  simpa only [fratGuard, fratFe, Nat.reduceAdd] using hg

/-- Run the guarded inner scan once an incoming row has been generated. -/
theorem innerBuffer_run {B n nt W : ℕ} {O T R : ℕ → ℕ}
    {D : Orientation n} {root : Fin n} {z : ℕ} (hz : z < n)
    {Cap S : Finset ℕ} {outTail outerPos inTail : ℕ}
    {Aout Ain : ℕ → ℕ} {E Deg ER ID BH BV BN : ℕ → ℕ} {tau : Env}
    (hB1 : 1 < B) (hnB : n < B) (hCap : Cap ⊆ Finset.range n)
    (hrow : SetRowRep (D.inN ⟨z, hz⟩) inTail Ain)
    (hfeCap : ∀ p, p < inTail → fratFe (root : ℕ) (Ain p) ⊆ Cap)
    (hmarks : Marks "stf" n 1 ({(root : ℕ)} ∪ S) (fun _ => 0) tau)
    (hacc : InnerAcc n nt W O T R root Cap outTail outerPos Aout Ain inTail
      E Deg ER ID BH BV BN S tau) :
    ∃ tau' K,
      Run B (bufferScan "vin" "fk" "vtail" "u"
        (fratGuard (rowFillAct "vrow"))) tau tau' K ∧
      K ≤ inTail * 26 + 6 ∧
      Marks "stf" n 1 ({(root : ℕ)} ∪ (S ∪ fratStep D (root : ℕ) z))
        (fun _ => 0) tau' ∧
      InnerAcc n nt W O T R root Cap outTail outerPos Aout Ain inTail
        E Deg ER ID BH BV BN (S ∪ fratStep D (root : ℕ) z) tau' := by
  let J : Finset ℕ → Env → Prop := fun U sigma =>
    Marks "stf" n 1 ({(root : ℕ)} ∪ U) (fun _ => 0) sigma ∧
      InnerAcc n nt W O T R root Cap outTail outerPos Aout Ain inTail
        E Deg ER ID BH BV BN U sigma
  obtain ⟨tau', K, hr, hK, hJ⟩ :=
    emitBuffer_run (B := B) (n := n) (tail := inTail) (Kg := 15)
      (src := "vin") (j := "fk") (jend := "vtail")
      (grd := fratGuard (rowFillAct "vrow"))
      (S := D.inN ⟨z, hz⟩) (A := Ain) (fe := fratFe (root : ℕ))
      (J := J) (E0 := S) (Cap := Cap) (sigma := tau)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      hB1 hnB hrow hacc.in_tail_eq hacc.in_eq
      (fun _ _ h => h.2.in_eq)
      (by
        intro U sigma y x hy hJ
        refine ⟨hJ.1.setVar y x, ?_⟩
        rcases hy with rfl | rfl
        · exact hJ.2.setVarPrivate (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) x
        · exact hJ.2.setVarPrivate (by decide) (by decide) (by decide)
            (by decide) (by decide) (by decide) x)
      hfeCap (innerAcc_guarded hB1 hnB hCap) ⟨hmarks, hacc⟩
  have hstep : bufferAcc inTail Ain (fratFe (root : ℕ)) =
      fratStep D (root : ℕ) z := by
    rw [bufferAcc_eq_biUnion_valSet hrow, fratStep, inValSet_of_lt D hz]
  rw [hstep] at hJ
  exact ⟨tau', K, hr, by omega, hJ.1, hJ.2⟩

/-! ## One outer slot -/

/-- One complete turn of the outer buffer scan. -/
theorem baseFratInner_run {B n nt W : ℕ} {O T R : ℕ → ℕ}
    {D : Orientation n} {root : Fin n} {outTail p : ℕ}
    {Aout : ℕ → ℕ} {E Deg ER ID BH BV BN : ℕ → ℕ} {tau : Env}
    (hB1 : 1 < B) (hnB : n < B)
    (hpin : ProvidesSetRows B n W (fun w => D.inN w)
      (BaseOrientMem n nt "off" "tgt" "vr0" "vin" O T R) "vin"
      (baseOrientProvide .incoming "off" "tgt" "vr0" "vin")
      (baseOrientCost O))
    (hout : SetRowRep (outSet D root) outTail Aout)
    (hp : p < outTail) (hfj : tau.vars "fj" = p)
    (houter : OuterAcc n nt W O T R D root (fratNum D root)
      outTail Aout p E Deg ER ID BH BV BN tau) :
    ∃ tau' K,
      Run B (baseFratInner "off" "tgt" "vr0" "vin" "vrow")
        (tau.setVar "u" (Aout p)) tau' K ∧
      K ≤ baseOrientCost O (Aout p) +
        26 * (D.inN ⟨Aout p, hout.value_lt p hp⟩).card + 12 ∧
      tau'.vars "fj" = p ∧
      OuterAcc n nt W O T R D root (fratNum D root)
        outTail Aout (p + 1) E Deg ER ID BH BV BN tau' := by
  classical
  let z := Aout p
  have hz : z < n := hout.value_lt p hp
  let S := bufferAcc p Aout (fratStep D (root : ℕ))
  have hCap : fratNum D root ⊆ Finset.range n := by
    rw [fratNum_eq]
    intro y hy
    exact Finset.mem_range.2 (valSet_lt hy)
  obtain ⟨hSsub, Acur, hAcur, hc, hnd, hmem⟩ := houter.fill
  change S ⊆ fratNum D root at hSsub
  have hScard : S.card < B := by
    have hle := Finset.card_le_card (hSsub.trans hCap)
    rw [Finset.card_range] at hle
    omega
  let sigma0 := tau.setVar "u" z
  have hc0 : sigma0.vars "c" = S.card := by simpa [sigma0] using hc
  have ec : (Expr.var "c").evalB B sigma0 = some S.card := by
    have h := evalB_var (B := B) (x := "c") (σ := sigma0) (by rw [hc0]; exact hScard)
    rwa [hc0] at h
  let sigma1 := sigma0.setVar "fcount" S.card
  have r1 : Run B (.assign "fcount" (.var "c")) sigma0 sigma1 2 :=
    Run.assign ec
  have hu1 : sigma1.vars "u" = z := by simp [sigma1, sigma0]
  have eu : (Expr.var "u").evalB B sigma1 = some z := by
    have h := evalB_var (B := B) (x := "u") (σ := sigma1) (by rw [hu1]; omega)
    rwa [hu1] at h
  let sigma2 := sigma1.setVar "w" z
  have r2 : Run B (.assign "w" (.var "u")) sigma1 sigma2 2 := Run.assign eu
  have hinput2 : BaseOrientInput n nt "off" "tgt" "vr0" O T R sigma2 :=
    (houter.input.setVar "u" z).setVar "fcount" S.card |>.setVar "w" z
  have hvinlen2 : (sigma2.arrs "vin").length = n := by
    simpa [sigma2, sigma1, sigma0] using houter.vin_length
  have heng2 : EngineArrays n W E Deg ER ID BH BV BN sigma2 :=
    ⟨by simpa [sigma2, sigma1, sigma0] using houter.engine.n_eq,
      by simpa [sigma2, sigma1, sigma0] using houter.engine.elm_eq,
      by simpa [sigma2, sigma1, sigma0] using houter.engine.deg_eq,
      by simpa [sigma2, sigma1, sigma0] using houter.engine.rank_eq,
      by simpa [sigma2, sigma1, sigma0] using houter.engine.idg_eq,
      by simpa [sigma2, sigma1, sigma0] using houter.engine.head_eq,
      by simpa [sigma2, sigma1, sigma0] using houter.engine.val_eq,
      by simpa [sigma2, sigma1, sigma0] using houter.engine.next_eq⟩
  have hw2 : sigma2.vars "w" = z := by simp [sigma2]
  obtain ⟨sigma3, r3, hmem3, heng3, -, inTail, Ain, hrowIn, htail3, hAin3⟩ :=
    (hpin ⟨z, hz⟩ E Deg ER ID BH BV BN).run
      ⟨⟨hinput2, hvinlen2⟩, heng2, hw2⟩
  have hfcount3 : sigma3.vars "fcount" = S.card := by
    rw [r3.frame_var "fcount" (by decide)]
    simp [sigma2, sigma1]
  have efcount : (Expr.var "fcount").evalB B sigma3 = some S.card := by
    have h := evalB_var (B := B) (x := "fcount") (σ := sigma3)
      (by rw [hfcount3]; exact hScard)
    rwa [hfcount3] at h
  let sigma4 := sigma3.setVar "c" S.card
  have r4 : Run B (.assign "c" (.var "fcount")) sigma3 sigma4 2 :=
    Run.assign efcount
  have frame3 (a : String) (ha : a ∉
      (baseOrientProvide .incoming "off" "tgt" "vr0" "vin").warrs) :
      sigma3.arrs a = sigma2.arrs a := r3.frame_arr a ha
  have hfill4 : RowFillAcc "vrow" n (fratNum D root) S sigma4 := by
    refine ⟨hSsub, Acur, ?_, by simp [sigma4, hc], hnd, hmem⟩
    rw [arrs_setVar, frame3 "vrow" (by decide)]
    simpa [sigma2, sigma1, sigma0] using hAcur
  have hmarks4 : Marks "stf" n 1 ({(root : ℕ)} ∪ S) (fun _ => 0) sigma4 := by
    apply houter.marks.of_eq
    rw [arrs_setVar, frame3 "stf" (by decide)]
    simp [sigma2, sigma1, sigma0]
  have heng4 : EngineArrays n W E Deg ER ID BH BV BN sigma4 :=
    ⟨by simpa [sigma4] using heng3.n_eq, by simpa [sigma4] using heng3.elm_eq,
      by simpa [sigma4] using heng3.deg_eq, by simpa [sigma4] using heng3.rank_eq,
      by simpa [sigma4] using heng3.idg_eq, by simpa [sigma4] using heng3.head_eq,
      by simpa [sigma4] using heng3.val_eq, by simpa [sigma4] using heng3.next_eq⟩
  have hout4 : sigma4.arrs "vout" = arrOf n Aout := by
    rw [arrs_setVar, frame3 "vout" (by decide)]
    simpa [sigma2, sigma1, sigma0] using houter.out_eq
  have hinner4 : InnerAcc n nt W O T R root (fratNum D root)
      outTail p Aout Ain inTail E Deg ER ID BH BV BN S sigma4 := by
    refine ⟨hfill4, hmem3.input.setVar "c" S.card, heng4, hout4,
      by simpa [sigma4] using hAin3, by simpa [sigma4] using htail3, ?_, ?_, ?_⟩
    · rw [vars_setVar, if_neg (by decide),
          r3.frame_var "froot" (by decide)]
      simpa [sigma2, sigma1, sigma0] using houter.root_eq
    · rw [vars_setVar, if_neg (by decide),
          r3.frame_var "fend" (by decide)]
      simpa [sigma2, sigma1, sigma0] using houter.end_eq
    · rw [vars_setVar, if_neg (by decide),
          r3.frame_var "fj" (by decide)]
      simpa [sigma2, sigma1, sigma0] using hfj
  have hfeCap : ∀ q, q < inTail → fratFe (root : ℕ) (Ain q) ⊆ fratNum D root := by
    intro q hq y hy
    rw [fratNum, Finset.mem_biUnion]
    refine ⟨z, (hout.mem_valSet_iff z).2 ⟨p, hp, rfl⟩, ?_⟩
    rw [fratStep, inValSet_of_lt D hz, Finset.mem_biUnion]
    exact ⟨Ain q, (hrowIn.mem_valSet_iff (Ain q)).2 ⟨q, hq, rfl⟩, hy⟩
  obtain ⟨sigma5, K5, r5, hK5, hmarks5, hacc5⟩ :=
    innerBuffer_run (D := D) (root := root) (z := z) hz hB1 hnB hCap
      hrowIn hfeCap hmarks4 hinner4
  have houter5 : OuterAcc n nt W O T R D root (fratNum D root)
      outTail Aout (p + 1) E Deg ER ID BH BV BN sigma5 := by
    refine ⟨?_, ?_, hacc5.input, hacc5.engine, hacc5.out_eq,
      by rw [hacc5.in_eq, length_arrOf], hacc5.root_eq, hacc5.end_eq⟩
    · simpa only [S, z, bufferAcc_succ] using hmarks5
    · simpa only [S, z, bufferAcc_succ] using hacc5.fill
  refine ⟨sigma5, 2 + (2 + (baseOrientCost O z + (2 + K5))), ?_, ?_,
    hacc5.outer_eq, houter5⟩
  · simpa [baseFratInner, sigma0, z] using
      r1.seq (r2.seq (r3.seq (r4.seq r5)))
  · have htailCard : inTail =
        (D.inN ⟨Aout p, hout.value_lt p hp⟩).card := by
      simpa [z] using hrowIn.tail_eq
    rw [htailCard] at hK5
    dsimp [z]
    omega

/-! ## The complete outer scan -/

/-- Cost of the inner turn at a numeric vertex.  Totalizing here keeps the
cost function passed to `bufferScanC_run` independent of its slot proof. -/
noncomputable def baseFratRawBudget {n : ℕ} (O : ℕ → ℕ)
    (D : Orientation n) (z : ℕ) : ℕ :=
  if hz : z < n then baseOrientCost O z + 26 * (D.inN ⟨z, hz⟩).card + 12 else 0

@[simp] theorem baseFratRawBudget_of_lt {n : ℕ} (O : ℕ → ℕ)
    (D : Orientation n) {z : ℕ} (hz : z < n) :
    baseFratRawBudget O D z =
      baseOrientCost O z + 26 * (D.inN ⟨z, hz⟩).card + 12 := by
  simp [baseFratRawBudget, hz]

/-- Per-outgoing-neighbour budget.  The last `11` is the outer buffer
scanner's own slot charge. -/
noncomputable def baseFratSlotBudget {n : ℕ} (O : ℕ → ℕ)
    (D : Orientation n) (z : ℕ) : ℕ :=
  baseFratRawBudget O D z + 11

@[simp] theorem baseFratSlotBudget_of_lt {n : ℕ} (O : ℕ → ℕ)
    (D : Orientation n) {z : ℕ} (hz : z < n) :
  baseFratSlotBudget O D z =
      baseOrientCost O z + 26 * (D.inN ⟨z, hz⟩).card + 23 := by
  rw [baseFratSlotBudget, baseFratRawBudget_of_lt O D hz]

/-- Lift the checked one-slot turn through the exact outgoing buffer. -/
theorem baseFratOuter_run {B n nt W : ℕ} {O T R : ℕ → ℕ}
    {D : Orientation n} {root : Fin n} {outTail : ℕ}
    {Aout : ℕ → ℕ} {E Deg ER ID BH BV BN : ℕ → ℕ} {sigma : Env}
    (hB1 : 1 < B) (hnB : n < B)
    (hpin : ProvidesSetRows B n W (fun w => D.inN w)
      (BaseOrientMem n nt "off" "tgt" "vr0" "vin" O T R) "vin"
      (baseOrientProvide .incoming "off" "tgt" "vr0" "vin")
      (baseOrientCost O))
    (hout : SetRowRep (outSet D root) outTail Aout)
    (houter0 : OuterAcc n nt W O T R D root (fratNum D root)
      outTail Aout 0 E Deg ER ID BH BV BN sigma) :
    ∃ sigma' K,
      Run B (bufferScan "vout" "fj" "fend" "u"
        (baseFratInner "off" "tgt" "vr0" "vin" "vrow")) sigma sigma' K ∧
      K ≤ (∑ z ∈ valSet (outSet D root), baseFratSlotBudget O D z) + 6 ∧
      OuterAcc n nt W O T R D root (fratNum D root)
        outTail Aout outTail E Deg ER ID BH BV BN sigma' := by
  let costs : ℕ → ℕ := fun p => baseFratRawBudget O D (Aout p)
  let I : ℕ → Env → Prop := fun p tau =>
    OuterAcc n nt W O T R D root (fratNum D root)
      outTail Aout p E Deg ER ID BH BV BN tau ∧
      tau.vars "fend" = outTail ∧ tau.vars "fj" = p ∧ p ≤ outTail
  have hstart : I 0 (sigma.setVar "fj" 0) := by
    refine ⟨houter0.setVarPrivate (by decide) (by decide) (by decide)
      (by decide) 0, ?_, by simp, by omega⟩
    simpa using houter0.end_eq
  obtain ⟨sigma', K, hr, hK, hI⟩ :=
    bufferScanC_run (B := B) (len := n) (hi := outTail)
      (src := "vout") (j := "fj") (jend := "fend") (u := "u")
      (body := baseFratInner "off" "tgt" "vr0" "vin" "vrow")
      (costs := costs) (A := Aout) (I := I) (sigma := sigma)
      (by decide) (lt_of_le_of_lt hout.tail_le hnB) hB1 hout.tail_le
      houter0.end_eq
      (fun _ _ h => h.1.out_eq)
      (fun p hp => lt_trans (hout.value_lt p hp) hnB)
      (fun _ _ h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩)
      (by
        intro p tau hIp hp
        obtain ⟨tau', K', hr', hK', hfj', houter'⟩ :=
          baseFratInner_run hB1 hnB hpin hout hp hIp.2.2.1 hIp.1
        refine ⟨tau', K', hr', ?_, hfj', ?_⟩
        · simpa only [costs, baseFratRawBudget_of_lt O D
            (hout.value_lt p hp)] using hK'
        refine ⟨houter'.setVarPrivate (by decide) (by decide) (by decide)
          (by decide) (p + 1), ?_, by simp, by omega⟩
        rw [vars_setVar, if_neg (by decide)]
        exact houter'.end_eq)
      hstart
  have hsum := hout.sum_slots (baseFratSlotBudget O D)
  have hcostEq : (∑ p ∈ Finset.range outTail, (costs p + 11)) =
      ∑ z ∈ valSet (outSet D root), baseFratSlotBudget O D z := by
    rw [← hsum]
    apply Finset.sum_congr rfl
    intro p hp
    simp only [costs, baseFratSlotBudget]
  rw [hcostEq] at hK
  exact ⟨sigma', K, hr, hK, hI.1⟩

/-! ## Complete row provider -/

/-- Total per-row budget for the implicit base fraternity graph. -/
noncomputable def baseFratCost {n : ℕ} (O : ℕ → ℕ)
    (D : Orientation n) (w : ℕ) : ℕ :=
  if hw : w < n then
    baseOrientCost O w +
      (∑ z ∈ valSet (outSet D ⟨w, hw⟩), baseFratSlotBudget O D z) +
      14 * (fratNbrs D ⟨w, hw⟩).card + 30
  else 0

@[simp] theorem baseFratCost_of_lt {n : ℕ} (O : ℕ → ℕ)
    (D : Orientation n) {w : ℕ} (hw : w < n) :
    baseFratCost O D w =
      baseOrientCost O w +
        (∑ z ∈ valSet (outSet D ⟨w, hw⟩), baseFratSlotBudget O D z) +
        14 * (fratNbrs D ⟨w, hw⟩).card + 30 := by
  simp [baseFratCost, hw]

theorem root_not_mem_fratVal {D : Orientation n} (root : Fin n) :
    (root : ℕ) ∉ valSet (fratNbrs D root) := by
  intro h
  obtain ⟨hr, hm⟩ := mem_valSet.1 h
  have he : (⟨(root : ℕ), hr⟩ : Fin n) = root := Fin.ext rfl
  rw [he, Lax3Proofs.RamAugment.fratNbrs_eq] at hm
  simpa using hm

/-- The nested implicit walk is a reusable exact-set provider.  This
composition theorem is independent of how the two orientation-row providers
are implemented; the concrete CSR instance follows below. -/
theorem baseFratProvidesSetRows_of_orientation {B n nt W : ℕ}
    {O T R : ℕ → ℕ} {D : Orientation n}
    (hB1 : 1 < B) (hnB : n < B)
    (hpin : ProvidesSetRows B n W (fun w => D.inN w)
      (BaseOrientMem n nt "off" "tgt" "vr0" "vin" O T R) "vin"
      (baseOrientProvide .incoming "off" "tgt" "vr0" "vin")
      (baseOrientCost O))
    (hpout : ProvidesSetRows B n W (fun w => outSet D w)
      (BaseOrientMem n nt "off" "tgt" "vr0" "vout" O T R) "vout"
      (baseOrientProvide .outgoing "off" "tgt" "vr0" "vout")
      (baseOrientCost O)) :
    ProvidesSetRows B n W (fratNbrs D)
      (BaseFratMem n nt O T R) "vrow"
      (baseFratProvide "off" "tgt" "vr0" "vout" "vin" "vrow")
      (baseFratCost O D) := by
  classical
  intro root E Deg ER ID BH BV BN
  refine Spec.of_exists fun sigma hpre => ?_
  obtain ⟨hmem, heng, hw⟩ := hpre
  have hrootB : (root : ℕ) < B := lt_trans root.isLt hnB
  have ew : (Expr.var "w").evalB B sigma = some (root : ℕ) := by
    have h := evalB_var (B := B) (x := "w") (σ := sigma) (by rw [hw]; exact hrootB)
    rwa [hw] at h
  let sigma1 := sigma.setVar "froot" (root : ℕ)
  have r1 : Run B (.assign "froot" (.var "w")) sigma sigma1 2 := Run.assign ew
  have houtMem1 : BaseOrientMem n nt "off" "tgt" "vr0" "vout" O T R sigma1 :=
    ⟨hmem.input.setVar "froot" (root : ℕ), by simpa [sigma1] using hmem.vout_length⟩
  have heng1 : EngineArrays n W E Deg ER ID BH BV BN sigma1 :=
    ⟨by simpa [sigma1] using heng.n_eq, by simpa [sigma1] using heng.elm_eq,
      by simpa [sigma1] using heng.deg_eq, by simpa [sigma1] using heng.rank_eq,
      by simpa [sigma1] using heng.idg_eq, by simpa [sigma1] using heng.head_eq,
      by simpa [sigma1] using heng.val_eq, by simpa [sigma1] using heng.next_eq⟩
  have hw1 : sigma1.vars "w" = (root : ℕ) := by simpa [sigma1] using hw
  obtain ⟨sigma2, r2, houtMem2, heng2, hstable2,
      outTail, Aout, hrowOut, htail2, hAout2⟩ :=
    (hpout root E Deg ER ID BH BV BN).run ⟨houtMem1, heng1, hw1⟩
  have houtTailB : outTail < B := lt_of_le_of_lt hrowOut.tail_le hnB
  have evtail : (Expr.var "vtail").evalB B sigma2 = some outTail := by
    have h := evalB_var (B := B) (x := "vtail") (σ := sigma2)
      (by rw [htail2]; exact houtTailB)
    rwa [htail2] at h
  let sigma3 := sigma2.setVar "fend" outTail
  have r3 : Run B (.assign "fend" (.var "vtail")) sigma2 sigma3 2 :=
    Run.assign evtail
  let sigma4 := sigma3.setVar "c" 0
  have r4 : Run B (.assign "c" (.lit 0)) sigma3 sigma4 2 :=
    Run.assign (evalB_lit (by omega))
  have hw2 : sigma2.vars "w" = (root : ℕ) := by
    rw [hstable2.w_eq]
    exact hw1
  have hw4 : sigma4.vars "w" = (root : ℕ) := by simpa [sigma4, sigma3] using hw2
  have ew4 : (Expr.var "w").evalB B sigma4 = some (root : ℕ) := by
    have h := evalB_var (B := B) (x := "w") (σ := sigma4)
      (by rw [hw4]; exact hrootB)
    rwa [hw4] at h
  have hstf2 : sigma2.arrs "stf" = arrOf n (fun _ => 0) := by
    rw [r2.frame_arr "stf" (by decide)]
    simpa [sigma1] using hmem.stamp_zero
  have hstf4 : sigma4.arrs "stf" = arrOf n (fun _ => 0) := by
    simpa [sigma4, sigma3] using hstf2
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
      ({(root : ℕ)} ∪ bufferAcc 0 Aout (fratStep D (root : ℕ)))
      (fun _ => 0) sigma5 := by
    refine ⟨fun k => if k = (root : ℕ) then 1 else 0, hstf5, ?_⟩
    intro k hk
    simp
  have hinput5 : BaseOrientInput n nt "off" "tgt" "vr0" O T R sigma5 :=
    ⟨by simpa [sigma5, sigma4, sigma3] using houtMem2.input.off_eq,
      by simpa [sigma5, sigma4, sigma3] using houtMem2.input.tgt_eq,
      by simpa [sigma5, sigma4, sigma3] using houtMem2.input.rank_eq⟩
  have heng5 : EngineArrays n W E Deg ER ID BH BV BN sigma5 :=
    ⟨by simpa [sigma5, sigma4, sigma3] using heng2.n_eq,
      by simpa [sigma5, sigma4, sigma3] using heng2.elm_eq,
      by simpa [sigma5, sigma4, sigma3] using heng2.deg_eq,
      by simpa [sigma5, sigma4, sigma3] using heng2.rank_eq,
      by simpa [sigma5, sigma4, sigma3] using heng2.idg_eq,
      by simpa [sigma5, sigma4, sigma3] using heng2.head_eq,
      by simpa [sigma5, sigma4, sigma3] using heng2.val_eq,
      by simpa [sigma5, sigma4, sigma3] using heng2.next_eq⟩
  have hvrow2 : (sigma2.arrs "vrow").length = n := by
    rw [r2.frame_arr "vrow" (by decide)]
    simpa [sigma1] using hmem.vrow_length
  have hvrow5 : (sigma5.arrs "vrow").length = n := by
    simpa [sigma5, sigma4, sigma3] using hvrow2
  obtain ⟨A0, hA0⟩ := Lax3Proofs.RamDriver.exists_arrOf hvrow5
  have hfill5 : RowFillAcc "vrow" n (fratNum D root)
      (bufferAcc 0 Aout (fratStep D (root : ℕ))) sigma5 := by
    refine ⟨by simp, A0, hA0, by simp [sigma5, sigma4], ?_, ?_⟩
    · simp [Lax3Proofs.Refine.OrderVirtualRowRep.rowList]
    · intro z
      simp [Lax3Proofs.Refine.OrderVirtualRowRep.rowList]
  have hvout5 : sigma5.arrs "vout" = arrOf n Aout := by
    simpa [sigma5, sigma4, sigma3] using hAout2
  have hvin2 : (sigma2.arrs "vin").length = n := by
    rw [r2.frame_arr "vin" (by decide)]
    simpa [sigma1] using hmem.vin_length
  have hvin5 : (sigma5.arrs "vin").length = n := by
    simpa [sigma5, sigma4, sigma3] using hvin2
  have hfroot2 : sigma2.vars "froot" = (root : ℕ) := by
    rw [r2.frame_var "froot" (by decide)]
    simp [sigma1]
  have houter5 : OuterAcc n nt W O T R D root (fratNum D root)
      outTail Aout 0 E Deg ER ID BH BV BN sigma5 := by
    refine ⟨hmarks5, hfill5, hinput5, heng5, hvout5, hvin5, ?_, ?_⟩
    · simpa [sigma5, sigma4, sigma3] using hfroot2
    · simp [sigma5, sigma4, sigma3]
  obtain ⟨sigma6, K6, r6, hK6, houter6⟩ :=
    baseFratOuter_run hB1 hnB hpin hrowOut houter5
  have hfull : bufferAcc outTail Aout (fratStep D (root : ℕ)) =
      fratNum D root := by
    simpa only [fratNum] using
      bufferAcc_eq_biUnion_valSet hrowOut (fratStep D (root : ℕ))
  have hmarks6 := houter6.marks
  have hfill6 := houter6.fill
  rw [hfull, fratNum_eq D root] at hmarks6 hfill6
  obtain ⟨Arow, hArow6, hc6, hrow⟩ := hfill6.toSetRowRep
  obtain ⟨g, hstf6, hg⟩ := hmarks6
  obtain ⟨sigma7, K7, r7, hK7, hclear7⟩ :=
    stampBuffer_run (B := B) (n := n) (tail := (fratNbrs D root).card)
      (b := 0) (src := "vrow") (j := "fc") (jend := "c")
      (u := "u") (s := "stf") (S := fratNbrs D root) (A := Arow)
      (g := g) (sigma := sigma6) (by decide) (by decide) (by decide)
      (by decide) hB1 hnB (by omega) hrow hc6 hArow6 hstf6
  obtain ⟨g7, hstf7, hg7⟩ := hclear7
  have hg7root : ∀ k < n,
      g7 k = if k = (root : ℕ) then 1 else 0 := by
    intro k hk
    rw [hg7 k hk, hg k hk]
    by_cases hkS : k ∈ valSet (fratNbrs D root)
    · have hkr : k ≠ (root : ℕ) := by
        intro hkr
        apply root_not_mem_fratVal root
        simpa [hkr] using hkS
      simp [hkS, hkr]
    · simp [hkS]
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
  have hc7 : sigma7.vars "c" = (fratNbrs D root).card := by
    rw [r7.frame_var "c" (by decide)]
    exact hc6
  have hc10 : sigma10.vars "c" = (fratNbrs D root).card := by
    simpa [sigma10, sigma9, sigma8] using hc7
  have hcardB : (fratNbrs D root).card < B := by
    exact lt_of_le_of_lt hrow.tail_le hnB
  have ec10 : (Expr.var "c").evalB B sigma10 =
      some (fratNbrs D root).card := by
    have h := evalB_var (B := B) (x := "c") (σ := sigma10)
      (by rw [hc10]; exact hcardB)
    rwa [hc10] at h
  let sigma11 := sigma10.setVar "vtail" (fratNbrs D root).card
  have r11 : Run B (.assign "vtail" (.var "c")) sigma10 sigma11 2 :=
    Run.assign ec10
  have rAll : Run B
      (baseFratProvide "off" "tgt" "vr0" "vout" "vin" "vrow")
      sigma sigma11
      (2 + (baseOrientCost O (root : ℕ) +
        (2 + (2 + (3 + (K6 + (K7 + (2 + (3 + (2 + 2)))))))))) := by
    simpa only [baseFratProvide] using
      r1.seq (r2.seq (r3.seq (r4.seq (r5.seq
        (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq r11)))))))))
  have hcost :
      2 + (baseOrientCost O (root : ℕ) +
        (2 + (2 + (3 + (K6 + (K7 + (2 + (3 + (2 + 2))))))))) ≤
        baseFratCost O D (root : ℕ) := by
    rw [baseFratCost_of_lt O D root.isLt]
    change 2 + (baseOrientCost O (root : ℕ) +
        (2 + (2 + (3 + (K6 + (K7 + (2 + (3 + (2 + 2))))))))) ≤
      baseOrientCost O (root : ℕ) +
        (∑ z ∈ valSet (outSet D root), baseFratSlotBudget O D z) +
        14 * (fratNbrs D root).card + 30
    omega
  have hinput11 : BaseOrientInput n nt "off" "tgt" "vr0" O T R sigma11 :=
    ⟨by rw [rAll.frame_arr "off" (by decide)]; exact hmem.input.off_eq,
      by rw [rAll.frame_arr "tgt" (by decide)]; exact hmem.input.tgt_eq,
      by rw [rAll.frame_arr "vr0" (by decide)]; exact hmem.input.rank_eq⟩
  have hvout7 : sigma7.arrs "vout" = arrOf n Aout := by
    rw [r7.frame_arr "vout" (by decide)]
    exact houter6.out_eq
  have hvin7 : (sigma7.arrs "vin").length = n := by
    rw [r7.frame_arr "vin" (by decide)]
    exact houter6.vin_length
  have hvrow7 : sigma7.arrs "vrow" = arrOf n Arow := by
    rw [r7.frame_arr "vrow" (by decide)]
    exact hArow6
  have hmem11 : BaseFratMem n nt O T R sigma11 := by
    refine ⟨hinput11, ?_, ?_, ?_, ?_⟩
    · simpa [sigma11, sigma10, sigma9, sigma8] using
        congrArg List.length hvout7
    · simpa [sigma11, sigma10, sigma9, sigma8] using hvin7
    · simpa [sigma11, sigma10, sigma9, sigma8] using
        congrArg List.length hvrow7
    · simpa [sigma11, sigma10] using hstf9
  have heng11 : EngineArrays n W E Deg ER ID BH BV BN sigma11 :=
    ⟨by rw [rAll.frame_var "n" (by decide)]; exact heng.n_eq,
      by rw [rAll.frame_arr "elm" (by decide)]; exact heng.elm_eq,
      by rw [rAll.frame_arr "deg" (by decide)]; exact heng.deg_eq,
      by rw [rAll.frame_arr "rnk" (by decide)]; exact heng.rank_eq,
      by rw [rAll.frame_arr "idg" (by decide)]; exact heng.idg_eq,
      by rw [rAll.frame_arr "bh" (by decide)]; exact heng.head_eq,
      by rw [rAll.frame_arr "bv" (by decide)]; exact heng.val_eq,
      by rw [rAll.frame_arr "bn" (by decide)]; exact heng.next_eq⟩
  have hstable11 : ProviderStable sigma sigma11 :=
    ⟨by rw [rAll.frame_var "n" (by decide)],
      by simp [sigma11, sigma10, hw],
      by rw [rAll.frame_var "i" (by decide)],
      by rw [rAll.frame_var "sp" (by decide)],
      by rw [rAll.frame_var "ls" (by decide)],
      by rw [rAll.frame_var "cnt" (by decide)],
      by rw [rAll.frame_var "mind" (by decide)],
      by rw [rAll.frame_var "kmax" (by decide)]⟩
  refine ⟨sigma11,
    2 + (baseOrientCost O (root : ℕ) +
      (2 + (2 + (3 + (K6 + (K7 + (2 + (3 + (2 + 2))))))))),
    rAll, hcost, hmem11, heng11, hstable11,
    (fratNbrs D root).card, Arow, hrow, ?_, ?_⟩
  · simp [sigma11]
  · simpa [sigma11, sigma10, sigma9, sigma8] using hvrow7

/-- Concrete base-CSR instance of the fraternity set provider. -/
theorem baseFratProvidesSetRows {B n ns nt W : ℕ}
    {G : SimpleGraph (Fin n)} {O T R : ℕ → ℕ} {rho : Fin n → ℕ}
    (hcsr : CsrSimple G ns O T) (hnsnt : ns ≤ nt)
    (hrho : ∀ v : Fin n, rho v = R (v : ℕ))
    (hR : ∀ v, v < n → R v < n)
    (hB1 : 1 < B) (hnB : n < B) (hnsB : ns < B) :
    ProvidesSetRows B n W
      (fratNbrs (ElimCert.elimOr G rho))
      (BaseFratMem n nt O T R) "vrow"
      (baseFratProvide "off" "tgt" "vr0" "vout" "vin" "vrow")
      (baseFratCost O (ElimCert.elimOr G rho)) := by
  have hpin := baseOrientProvidesSetRows
    (B := B) (n := n) (ns := ns) (nt := nt) (W := W)
    (G := G) (O := O) (T := T) (R := R) (rho := rho)
    (o := "off") (t := "tgt") (rk := "vr0") (dst := "vin")
    .incoming hcsr hnsnt hrho hR hnB hnsB
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have hpout := baseOrientProvidesSetRows
    (B := B) (n := n) (ns := ns) (nt := nt) (W := W)
    (G := G) (O := O) (T := T) (R := R) (rho := rho)
    (o := "off") (t := "tgt") (rk := "vr0") (dst := "vout")
    .outgoing hcsr hnsnt hrho hR hnB hnsB
    (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  exact baseFratProvidesSetRows_of_orientation hB1 hnB hpin hpout

/-- The same executable row generator, exposed at the graph-row interface
consumed by virtual elimination. -/
theorem baseFratProvidesRows {B n ns nt W : ℕ}
    {G : SimpleGraph (Fin n)} {O T R : ℕ → ℕ} {rho : Fin n → ℕ}
    (hcsr : CsrSimple G ns O T) (hnsnt : ns ≤ nt)
    (hrho : ∀ v : Fin n, rho v = R (v : ℕ))
    (hR : ∀ v, v < n → R v < n)
    (hB1 : 1 < B) (hnB : n < B) (hnsB : ns < B) :
    ProvidesRows B n W (fratGraph (ElimCert.elimOr G rho))
      (BaseFratMem n nt O T R)
      (baseFratProvide "off" "tgt" "vr0" "vout" "vin" "vrow")
      (baseFratCost O (ElimCert.elimOr G rho)) := by
  apply providesRows_of_setRows
    (baseFratProvidesSetRows hcsr hnsnt hrho hR hB1 hnB hnsB)
  intro w
  ext u
  rw [mem_fratNbrs, Lax3Proofs.Augmentation.mem_nbrsIn]
  simp

/-- The first implicit augmentation rank: eliminate the fraternity graph of
the base elimination orientation without materializing that graph. -/
theorem baseFratVirtualElim_spec {B n ns nt : ℕ}
    {G : SimpleGraph (Fin n)} {O T R : ℕ → ℕ} {rho : Fin n → ℕ}
    (hcsr : CsrSimple G ns O T) (hnsnt : ns ≤ nt)
    (hrho : ∀ v : Fin n, rho v = R (v : ℕ))
    (hR : ∀ v, v < n → R v < n)
    (hB : 3 * n + 3 < B) (hnsB : ns < B) :
    Spec B
      (fun sigma => BaseFratMem n nt O T R sigma ∧
        ∃ E D ER ID BH BV BN,
          EngineArrays n (bucketExtra n) E D ER ID BH BV BN sigma ∧
          ∀ u < n, E u = 0)
      (virtualElim
        (baseFratProvide "off" "tgt" "vr0" "vout" "vin" "vrow"))
      (fun _ sigma' =>
        VirtualElimResult (fratGraph (ElimCert.elimOr G rho)) sigma')
      (virtualElimCost (fratGraph (ElimCert.elimOr G rho))
        (baseFratCost O (ElimCert.elimOr G rho))) := by
  apply Lax3Proofs.Refine.OrderVirtualDriver.virtualElim_spec
  · exact baseFratProvidesRows hcsr hnsnt hrho hR (by omega) (by omega) hnsB
  · exact baseFratMem_engineClosed
  · exact baseFratMem_engineRunClosed
  · exact hB

/-! ## Axiom audit -/

#print axioms fratNum_eq
#print axioms baseFratProvidesSetRows_of_orientation
#print axioms baseFratProvidesSetRows
#print axioms baseFratProvidesRows
#print axioms baseFratVirtualElim_spec

end Lax3Proofs.Refine.OrderVirtualBaseFrat
