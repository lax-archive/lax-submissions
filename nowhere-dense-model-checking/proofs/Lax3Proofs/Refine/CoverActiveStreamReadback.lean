import Lax3Proofs.Refine.CoverActiveStreamScatter

/-!
# Readback from one streamed active-cover row

The landed readback walks a CSR-style interval selected by two consecutive
cells of `xofName j`.  A streamed row already occupies `xmmName j[0..tail)`,
so it needs no materialized cover: two stores present that prefix as the
virtual interval `[0, tail)`, after which the verified readback is reused
unchanged.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamReadback

open Lax3.ColoredGraphs Lax3.DistFO Lax3.Locality Lax3.ScatterSentences
open Lax3Proofs.FormulaTables
open Lax3Proofs.RamBfs (masked)
open Lax3Proofs.RamCover Lax3Proofs.RamCoverActive
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverBase
open Lax3Proofs.RamDriverCluster
open Lax3Proofs.Refine.CoverActiveStream
open Lax3Proofs.Refine.CoverActiveStreamScatter
open Lax3Proofs.Refine.ScatterDeadTurn
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

variable {n : ℕ}

/-! ## The two-cell virtual offset row -/

/-- Present the reusable prefix as the current centre's block. -/
def streamOffsetCom (j : ℕ) : Com :=
  .seq (.store (xofName j) (.var (curName j)) (.lit 0))
    (.store (xofName j) (.add (.var (curName j)) (.lit 1)) (.var "tail"))

/-- The exact environment produced by `streamOffsetCom`. -/
def streamOffsetEnv (j c tail : ℕ) (σ : Env) : Env :=
  (σ.setArr (xofName j) c 0).setArr (xofName j) (c + 1) tail

/-- The offset function represented after the two stores. -/
def virtualOffset (Xoff : ℕ → ℕ) (c tail : ℕ) : ℕ → ℕ :=
  upd (upd Xoff c 0) (c + 1) tail

@[simp] theorem virtualOffset_current (Xoff : ℕ → ℕ) (c tail : ℕ) :
    virtualOffset Xoff c tail c = 0 := by
  simp [virtualOffset]

@[simp] theorem virtualOffset_next (Xoff : ℕ → ℕ) (c tail : ℕ) :
    virtualOffset Xoff c tail (c + 1) = tail := by
  simp [virtualOffset]

/-- The two stores cost eight instructions exactly. -/
theorem streamOffsetCom_run {B n j c tail : ℕ} {Xoff : ℕ → ℕ} {σ : Env}
    (hB : n < B) (hc : c < n) (htail : tail < B)
    (hcur : σ.vars (curName j) = c) (ht : σ.vars "tail" = tail)
    (hxoff : σ.arrs (xofName j) = arrOf (n + 1) Xoff) :
    Run B (streamOffsetCom j) σ (streamOffsetEnv j c tail σ) 8 := by
  let σ₁ := σ.setArr (xofName j) c 0
  have r₁ : Run B (.store (xofName j) (.var (curName j)) (.lit 0)) σ σ₁ 3 := by
    have hi : (Expr.var (curName j)).evalB B σ = some c := by
      simpa [hcur] using evalB_var (B := B) (σ := σ) (x := curName j)
        (show σ.vars (curName j) < B by omega)
    have hz : (Expr.lit 0).evalB B σ = some 0 := evalB_lit (by omega)
    simpa [σ₁, Expr.size] using
      (Run.store hi hz (by rw [hxoff, length_arrOf]; omega))
  have hcur₁ : σ₁.vars (curName j) = c := by simp [σ₁, hcur]
  have ht₁ : σ₁.vars "tail" = tail := by simp [σ₁, ht]
  have hc₁eval : (Expr.var (curName j)).evalB B σ₁ = some c := by
    rw [evalB_var (B := B) (σ := σ₁) (x := curName j) (by rw [hcur₁]; omega), hcur₁]
  have hOne₁eval : (Expr.lit 1).evalB B σ₁ = some 1 := evalB_lit (by omega)
  have hi₁ : (Expr.add (.var (curName j)) (.lit 1)).evalB B σ₁ = some (c + 1) := by
    simpa [Bop.apply_add] using
      (evalB_bin (op := Bop.add) (m := c) (n := 1) hc₁eval hOne₁eval
        (show Bop.add.apply c 1 < B by simp; omega))
  have hv₁ : (Expr.var "tail").evalB B σ₁ = some tail := by
    simpa [ht₁] using evalB_var (B := B) (σ := σ₁) (x := "tail")
      (show σ₁.vars "tail" < B by omega)
  have r₂ : Run B
      (.store (xofName j) (.add (.var (curName j)) (.lit 1)) (.var "tail")) σ₁
      (σ₁.setArr (xofName j) (c + 1) tail) 5 := by
    simpa [Expr.size] using
      (Run.store hi₁ hv₁ (by
        rw [length_arrs_setArr, hxoff, length_arrOf]
        omega))
  simpa [streamOffsetCom, streamOffsetEnv, σ₁] using r₁.seq r₂

theorem streamOffsetEnv_xof {n j c tail : ℕ} {Xoff : ℕ → ℕ} {σ : Env}
    (hxoff : σ.arrs (xofName j) = arrOf (n + 1) Xoff) :
    (streamOffsetEnv j c tail σ).arrs (xofName j) =
      arrOf (n + 1) (virtualOffset Xoff c tail) := by
  simp [streamOffsetEnv, hxoff, virtualOffset, set_arrOf_eq_upd]

theorem streamOffsetEnv_arr {j c tail : ℕ} {σ : Env} {a : String}
    (ha : a ≠ xofName j) :
    (streamOffsetEnv j c tail σ).arrs a = σ.arrs a := by
  simp [streamOffsetEnv, ha]

@[simp] theorem streamOffsetEnv_vars {j c tail : ℕ} {σ : Env} {x : String} :
    (streamOffsetEnv j c tail σ).vars x = σ.vars x := by
  simp [streamOffsetEnv]

@[simp] theorem streamOffsetEnv_out {j c tail : ℕ} {σ : Env} :
    (streamOffsetEnv j c tail σ).out = σ.out := by
  simp [streamOffsetEnv]

/-! ## The operational readback adapter -/

/-- Two offset stores followed by the existing verified readback. -/
noncomputable def streamReadbackCom
    (q_top cap mb : ℕ) (φ : Lax3.FirstOrder.FO 0) (j : ℕ) : Com :=
  .seq (streamOffsetCom j) (readbackCom q_top cap mb φ j)

/-- Atom expressions never inspect the private offset row. -/
theorem evalB_atomExpr_streamOffset {B q_top cap mb j i c tail : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {β : DistFO (sigL cap mb j) 1}
    (a : StepAtom cap mb j) (σ : Env) (v : ℕ) :
    (atomExpr q_top cap mb φ j i β a).evalB B
        ((streamOffsetEnv j c tail σ).setVar "rv" v) =
      (atomExpr q_top cap mb φ j i β a).evalB B (σ.setVar "rv" v) := by
  cases a with
  | inl γ =>
      simp [atomExpr, Expr.evalB, streamOffsetEnv, tabName, xofName, String.ext_iff]
  | inr s => simp [atomExpr, Expr.evalB, streamOffsetEnv]

/-! The next predicate is deliberately the operational seam rather than a
second semantic cover interface.  Its allocation is still the driver's
reserved `n * n` row array, but every value and cost premise below is only on
the live prefix `tail`. -/

structure StreamRbCore
    (B q_top cap mb ns Ws j : ℕ) (φ : Lax3.FirstOrder.FO 0)
    (O T M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
    (Xoff Xmem asg : ℕ → ℕ) (c tail : ℕ) (ou : List ℕ)
    (val : Fin n → ℕ → StepAtom cap mb j → Prop)
    (T₀ : ℕ → ℕ → ℕ) (σ : Env) : Prop where
  level : LevelPre B n cap mb ns Ws O T j M Gm C σ
  tables : TablesSized q_top cap mb φ n σ
  offset_arr : σ.arrs (xofName j) = arrOf (n + 1) Xoff
  row_arr : σ.arrs (xmmName j) = arrOf (n * n) Xmem
  asg_arr : σ.arrs (asgName j) = arrOf n asg
  current_var : σ.vars (curName j) = c
  tail_var : σ.vars "tail" = tail
  out_eq : σ.out = ou
  current_lt : c < n
  tail_le : tail ≤ n
  mem_lt : ∀ p < tail, Xmem p < n
  asg_lt : ∀ p < tail, asg (Xmem p) < B
  table_arr : ∀ i, i < (tablesAt q_top cap mb φ j).length →
    σ.arrs (tabName j i) = arrOf n (T₀ i)
  atoms : ∀ p, p < tail → ∀ hp : Xmem p < n, asg (Xmem p) = c →
    ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length)
      (h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧
        DRank 1 q' (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])),
      ∀ a ∈ (bcOf q_top (stepFml cap mb j
          (tablesAt q_top cap mb φ j)[i]) h).atoms,
        ∃ u ≤ 1,
          (atomExpr q_top cap mb φ j i
            (tablesAt q_top cap mb φ j)[i] a).evalB B
              (σ.setVar "rv" (Xmem p)) = some u ∧
          (u ≠ 0 ↔ val ⟨Xmem p, hp⟩ i a)

open Classical in
/-- **Operational streamed readback.**  The existing readback proof runs on
the virtual interval `[0,tail)`.  In particular, its logical arena size is
`tail`, not `n*n`, so only `tail < B` is needed. -/
theorem streamReadbackCore_spec
    {B q_top cap mb ns Ws j : ℕ} {φ : Lax3.FirstOrder.FO 0}
    {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {Xoff Xmem asg : ℕ → ℕ} {c tail : ℕ} {ou : List ℕ}
    {val : Fin n → ℕ → StepAtom cap mb j → Prop}
    {T₀ : ℕ → ℕ → ℕ}
    (hB : 1 < B) (hn : n < B) :
    Spec B
      (StreamRbCore B q_top cap mb ns Ws j φ O T M Gm C Xoff Xmem asg
        c tail ou val T₀)
      (streamReadbackCom q_top cap mb φ j)
      (fun _ σ' =>
        RbBase B q_top cap mb ns Ws j φ O T M Gm C
            (virtualOffset Xoff c tail) Xmem asg c ou val σ' ∧
          ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length),
            TabOk q_top cap mb j (virtualOffset Xoff c tail) Xmem asg c
              (fun v => val v i) (tablesAt q_top cap mb φ j)[i]
              (tabName j i) (T₀ i) σ' tail)
      (8 + rbCost q_top cap mb φ j tail) := by
  refine Spec.of_exists fun σ hσ => ?_
  let τ := streamOffsetEnv j c tail σ
  have htailB : tail < B := lt_of_le_of_lt hσ.tail_le hn
  have hoff : Run B (streamOffsetCom j) σ τ 8 :=
    streamOffsetCom_run hn hσ.current_lt htailB hσ.current_var hσ.tail_var hσ.offset_arr
  have hlevel : LevelPre B n cap mb ns Ws O T j M Gm C τ := by
    apply Lax3Proofs.RamDriverCompose.levelPre_run hσ.level hoff
    all_goals
      simp [streamOffsetCom, Com.wvars, Com.warrs, xofName, alvName, gamName, colName, memName,
        Lax3Proofs.RamDriverCompose.zeroArrs, String.ext_iff]
    intro a ha
    rcases ha with h | h | h | h | h | h | h | h <;> simp_all
  have htables : TablesSized q_top cap mb φ n τ := hσ.tables.run hoff
  have hxoff : τ.arrs (xofName j) =
      arrOf (n + 1) (virtualOffset Xoff c tail) :=
    streamOffsetEnv_xof hσ.offset_arr
  have hxmem : τ.arrs (xmmName j) = arrOf (n * n) Xmem := by
    rw [streamOffsetEnv_arr (by simp [xmmName, xofName, String.ext_iff])]
    exact hσ.row_arr
  have hasg : τ.arrs (asgName j) = arrOf n asg := by
    rw [streamOffsetEnv_arr (by simp [asgName, xofName, String.ext_iff])]
    exact hσ.asg_arr
  have hcur : τ.vars (curName j) = c := by simpa [τ] using hσ.current_var
  have hout : τ.out = ou := by simpa [τ] using hσ.out_eq
  have hsz : ∀ i, i < (tablesAt q_top cap mb φ j).length →
      τ.arrs (tabName j i) = arrOf n (T₀ i) := by
    intro i hi
    rw [streamOffsetEnv_arr (by simp [tabName, xofName, String.ext_iff])]
    exact hσ.table_arr i hi
  have hatom : ∀ p, virtualOffset Xoff c tail c ≤ p →
      p < virtualOffset Xoff c tail (c + 1) → ∀ hp : Xmem p < n,
      asg (Xmem p) = c → ∀ (i : ℕ)
      (hi : i < (tablesAt q_top cap mb φ j).length)
      (h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧
        DRank 1 q' (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])),
      ∀ a ∈ (bcOf q_top (stepFml cap mb j
        (tablesAt q_top cap mb φ j)[i]) h).atoms,
        ∃ u ≤ 1,
          (atomExpr q_top cap mb φ j i
            (tablesAt q_top cap mb φ j)[i] a).evalB B
              (τ.setVar "rv" (Xmem p)) = some u ∧
          (u ≠ 0 ↔ val ⟨Xmem p, hp⟩ i a) := by
    intro p _ hp hp_n hp_asg i hi h a ha
    obtain ⟨u, hu, heval, hval⟩ := hσ.atoms p (by simpa using hp) hp_n hp_asg i hi h a ha
    refine ⟨u, hu, ?_, hval⟩
    rw [evalB_atomExpr_streamOffset]
    exact heval
  have hm : tail ≤ n * n := by
    exact hσ.tail_le.trans (le_mul_self n)
  obtain ⟨σ', hr, hpost⟩ :=
    (readback_specCore (ns := ns) (O := O) (T := T) (M := M) (Gm := Gm)
      (C := C) (Xoff := virtualOffset Xoff c tail) (Xmem := Xmem) (asg := asg)
      (cc := c) (ou := ou) (val := val) (T₀ := T₀) (m := tail)
      hB hn hσ.current_lt (by simp) (by simp) hm htailB hσ.mem_lt
      (fun p _ hp => hσ.asg_lt p (by simpa using hp))).run (σ := τ)
      ⟨⟨hlevel, hxoff, hxmem, hasg, hcur, lt_trans hσ.current_lt hn,
        hout, hatom⟩, hsz⟩
  refine ⟨σ', 8 + rbCost q_top cap mb φ j tail, ?_, le_rfl, ?_⟩
  · simpa [streamReadbackCom] using hoff.seq hr
  · simpa using hpost

/-! ## Semantic streamed readback -/

/-- Everything the semantic adapter needs after the scatter fold.  Unlike
`RamDriverCluster.ReadbackStepA`, this contains one reusable row rather than
a materialized active cover. -/
structure StreamReadbackPre
    (B q_top cap mb ns Ws ell j q c tail : ℕ)
    (φ : Lax3.FirstOrder.FO 0) (G : SimpleGraph (Fin n))
    (O T A₀ Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ)
    (π : Equiv.Perm (Fin n)) (centre Xmem asg SearchM : ℕ → ℕ)
    (X W : Set (Fin n)) (w : Fin mb → Fin n) (Alv Gam : ℕ → ℕ)
    (C' : ℕ → ℕ → ℕ) (σ : Env) : Prop where
  level : LevelPre B n cap mb ns Ws O T j A₀ Gm C σ
  tables : TablesSized q_top cap mb φ n σ
  dead : DeadView B q_top cap mb ns Ws ell j φ G O T A₀ C X W w Alv Gam C' σ
  row : StreamRowA G A₀ π centre q cap c tail Xmem asg SearchM
  row_arr : σ.arrs (xmmName j) = arrOf (n * n) Xmem
  asg_arr : σ.arrs (asgName j) = arrOf n asg
  current_var : σ.vars (curName j) = c
  tail_var : σ.vars "tail" = tail
  flags : ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length),
    ∀ s ∈ (bcAtomsOf q_top (stepFml cap mb j
        (tablesAt q_top cap mb φ j)[i])).2,
      σ.vars (flgName j i (posOf s (bcAtomsOf q_top
        (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])).2)) ≤ 1 ∧
      (σ.vars (flgName j i (posOf s (bcAtomsOf q_top
        (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])).2)) ≠ 0 ↔
        ScatVal (stepArenaP (masked G A₀) X w)
          (stepColoringP cap (masked G A₀)
            (colRead n C (sigL cap mb j)) X w) s)

open Classical in
/-- **One streamed row is read back correctly.**  Cells assigned to another
centre are retained; live cells assigned to this centre become the semantic
depth-`j` table row. -/
theorem streamReadbackViewStep
    {B q_top cap mb ns Ws ell j q c tail d : ℕ}
    {φ : Lax3.FirstOrder.FO 0} {G : SimpleGraph (Fin n)}
    {O T A₀ Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} {centre Xmem asg SearchM : ℕ → ℕ}
    {X W : Set (Fin n)} {w : Fin mb → Fin n} {Alv Gam : ℕ → ℕ}
    {C' : ℕ → ℕ → ℕ}
    (hcap : cap = rhoMinus 0 q_top)
    (hB : WordBoundK B n d ns cap mb)
    (hcentres : CentresBy n q A₀ π centre)
    (hX : ∀ v : Fin n, v ∈ X ↔
      InCluster (masked G A₀) π cap (centre c) (v : ℕ)) :
    Spec B
      (StreamReadbackPre B q_top cap mb ns Ws ell j q c tail φ G O T A₀ Gm C
        π centre Xmem asg SearchM X W w Alv Gam C')
      (streamReadbackCom q_top cap mb φ j)
      (fun σ σ' =>
        LevelPre B n cap mb ns Ws O T j A₀ Gm C σ' ∧
        TablesSized q_top cap mb φ n σ' ∧
        σ'.out = σ.out ∧ σ'.vars (curName j) = σ.vars (curName j) ∧
        σ'.arrs (xmmName j) = arrOf (n * n) Xmem ∧
        σ'.arrs (asgName j) = arrOf n asg ∧
        ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length),
          ∃ Tb Tb₀ : ℕ → ℕ,
            σ'.arrs (tabName j i) = arrOf n Tb ∧
            σ.arrs (tabName j i) = arrOf n Tb₀ ∧
            (∀ v : Fin n, A₀ (v : ℕ) = 0 ∨ asg (v : ℕ) ≠ c →
              Tb (v : ℕ) = Tb₀ (v : ℕ)) ∧
            ∀ v : Fin n, A₀ (v : ℕ) ≠ 0 → asg (v : ℕ) = c →
              Tb (v : ℕ) ≤ 1 ∧
              (Tb (v : ℕ) ≠ 0 ↔
                Sat (masked G A₀) (colRead n C (sigL cap mb j)) (fun _ => v)
                  (tablesAt q_top cap mb φ j)[i]))
      (8 + rbCost q_top cap mb φ j tail) := by
  refine Spec.of_exists fun σ hσ => ?_
  have hcq : c < q := by exact hσ.row.state.pos_le
  have hcn : c < n := lt_of_lt_of_le hcq hcentres.count_le
  have hnB : n < B := hB.n_lt
  have hqB : q < B := lt_of_le_of_lt hcentres.count_le hnB
  have hcentreAlive : A₀ (centre c) ≠ 0 := hcentres.alive c hcq
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hdepth, -, -, -, -, -⟩ := hσ.level
  obtain ⟨Xoff, hxoff⟩ :=
    hdepth.get j (p := (xofName j, n + 1)) (by simp)
  set T₀ : ℕ → ℕ → ℕ := fun i v => (σ.arrs (tabName j i)).getD v 0 with hT₀
  have hsz : ∀ i, i < (tablesAt q_top cap mb φ j).length →
      σ.arrs (tabName j i) = arrOf n (T₀ i) := by
    intro i hi
    obtain ⟨g, hg⟩ := hσ.tables.get j hi
    rw [hg]
    refine arrOf_congr fun v hv => ?_
    rw [hT₀]
    simp only [hg, getD_arrOf _ hv]
  have hrowAlive : ∀ p < tail, A₀ (Xmem p) ≠ 0 := by
    intro p hp
    have hcl : InCluster (masked G A₀) π cap (centre c) (Xmem p) :=
      (hσ.row.block _).mp ⟨p, hp, rfl⟩
    exact (Lax3Proofs.Refine.MassAlive.inCluster_alive_iff hcl).mpr hcentreAlive
  have hrowX : ∀ (p : ℕ) (hp : p < tail),
      (⟨Xmem p, hσ.row.mem_lt p hp⟩ : Fin n) ∈ X := by
    intro p hp
    apply (hX _).mpr
    exact (hσ.row.block _).mp ⟨p, hp, rfl⟩
  have hrowDom : ∀ (p : ℕ) (hp : p < tail),
      (⟨Xmem p, hσ.row.mem_lt p hp⟩ : Fin n) ∈ rowDom A₀ Alv X W := by
    intro p hp
    let v : Fin n := ⟨Xmem p, hσ.row.mem_lt p hp⟩
    by_cases hal : Alv (v : ℕ) = 0
    · refine Or.inr ⟨hrowAlive p hp, hrowX p hp, ?_⟩
      by_contra hWv
      exact absurd hal ((hσ.dead.data.1.2.2.2.2.2.2.1 v).2
        ⟨hrowAlive p hp, hrowX p hp, hWv⟩)
    · exact Or.inl hal
  have hatom : ∀ p, p < tail → ∀ hp : Xmem p < n, asg (Xmem p) = c →
      ∀ (i : ℕ) (hi : i < (tablesAt q_top cap mb φ j).length)
      (h : ∃ q' : ℕ, q' + 1 ≤ q_top ∧
        DRank 1 q' (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])),
      ∀ a ∈ (bcOf q_top (stepFml cap mb j
        (tablesAt q_top cap mb φ j)[i]) h).atoms,
        ∃ u ≤ 1,
          (atomExpr q_top cap mb φ j i
            (tablesAt q_top cap mb φ j)[i] a).evalB B
              (σ.setVar "rv" (Xmem p)) = some u ∧
          (u ≠ 0 ↔ atomVal (stepArenaP (masked G A₀) X w)
            (stepColoringP cap (masked G A₀)
              (colRead n C (sigL cap mb j)) X w) ⟨Xmem p, hp⟩ a) := by
    intro p hp hp_n hp_asg i hi h a ha
    have hrv : (σ.setVar "rv" (Xmem p)).vars "rv" = Xmem p := by simp
    cases a with
    | inl γ =>
        have hmemγ : γ ∈ tablesAt q_top cap mb φ (j + 1) :=
          bcLocals_subset_tablesAt_succ (List.getElem_mem hi)
            ((mem_bcAtomsOf_left h).mpr ha)
        obtain ⟨hlt, heq⟩ := getElem_posOf hmemγ
        obtain ⟨Tc, hTc, hTc1, hTcval⟩ := hσ.dead.table _ hlt
        let v : Fin n := ⟨Xmem p, hp_n⟩
        have hvd : v ∈ rowDom A₀ Alv X W := by simpa [v] using hrowDom p hp
        refine ⟨Tc (Xmem p), hTc1 v hvd, ?_, ?_⟩
        · show (Expr.get (tabName (j + 1) (posOf γ
              (tablesAt q_top cap mb φ (j + 1)))) (.var "rv")).evalB B _ = _
          refine evalB_get (k := Xmem p) ?_ ?_ (lt_of_le_of_lt (hTc1 v hvd) hB.one_lt)
          · simpa [hrv] using evalB_var (B := B) (σ := σ.setVar "rv" (Xmem p))
              (x := "rv") (by rw [hrv]; omega)
          · rw [arrs_setVar, hTc]
            exact getElem?_arrOf _ hp_n
        · rw [hTcval v hvd, heq, masked_alv_eq hσ.dead.data, hσ.dead.col_read]
          exact Iff.rfl
    | inr s =>
        have hmem : s ∈ (bcAtomsOf q_top (stepFml cap mb j
            (tablesAt q_top cap mb φ j)[i])).2 := (mem_bcAtomsOf_right h).mpr ha
        obtain ⟨hf1, hfiff⟩ := hσ.flags i hi s hmem
        refine ⟨σ.vars (flgName j i (posOf s (bcAtomsOf q_top
          (stepFml cap mb j (tablesAt q_top cap mb φ j)[i])).2)), hf1, ?_, hfiff⟩
        show (Expr.var (flgName j i _)).evalB B _ = _
        rw [evalB_var (by rw [vars_setVar, if_neg (flgName_ne_rv _ _ _)]; omega),
          vars_setVar, if_neg (flgName_ne_rv _ _ _)]
  have hasgB : ∀ p < tail, asg (Xmem p) < B := by
    intro p hp
    exact lt_of_le_of_lt (hσ.row.state.asg_le _ (hσ.row.mem_lt p hp) (hrowAlive p hp)) hqB
  have hcore : StreamRbCore B q_top cap mb ns Ws j φ O T A₀ Gm C Xoff Xmem asg
      c tail σ.out
      (fun v _ a => atomVal (stepArenaP (masked G A₀) X w)
        (stepColoringP cap (masked G A₀) (colRead n C (sigL cap mb j)) X w) v a)
      T₀ σ :=
    { level := hσ.level
      tables := hσ.tables
      offset_arr := hxoff
      row_arr := hσ.row_arr
      asg_arr := hσ.asg_arr
      current_var := hσ.current_var
      tail_var := hσ.tail_var
      out_eq := rfl
      current_lt := hcn
      tail_le := hσ.row.tail_le
      mem_lt := hσ.row.mem_lt
      asg_lt := hasgB
      table_arr := hsz
      atoms := hatom }
  obtain ⟨σ', hr, hbase, htab⟩ :=
    (streamReadbackCore_spec (n := n) hB.one_lt hnB).run hcore
  obtain ⟨hlevel', -, hxmem', hasg', hcur', -, hout', -⟩ := hbase
  refine ⟨σ', 8 + rbCost q_top cap mb φ j tail, hr, le_rfl, ?_⟩
  refine ⟨hlevel', hσ.tables.run hr, hout', ?_, hxmem', hasg', ?_⟩
  · rw [hcur', hσ.current_var]
  · intro i hi
    obtain ⟨Tb, hTb, hTb₀, hTbval⟩ := htab i hi
    refine ⟨Tb, T₀ i, hTb, hsz i hi, ?_, ?_⟩
    · intro v hframe
      rcases hframe with hdead | hne
      · apply hTb₀ v (Or.inr ?_)
        intro p _ hp hpv
        have halive := hrowAlive p (by simpa using hp)
        exact halive (by simpa [hpv] using hdead)
      · exact hTb₀ v (Or.inl hne)
    · intro v hAv hasgv
      have hset : asg (v : ℕ) < q := by rw [hasgv]; exact hcq
      have hballCluster := CoverPrefixA.assigned_cover hcentres hσ.row.state
        (v : ℕ) v.isLt hAv hset
      have hcl : InCluster (masked G A₀) π cap (centre c) (v : ℕ) := by
        have := hballCluster (WalkDistance.mem_ball_self _ _ _)
        simpa [hasgv] using this
      obtain ⟨p, hp, hpv⟩ := (hσ.row.block (v : ℕ)).mpr hcl
      obtain ⟨hp_n, hcell⟩ := hTbval p (by simp) (by simpa using hp)
      obtain ⟨hbit, hval⟩ := hcell (by rwa [hpv])
      have hpvFin : (⟨Xmem p, hp_n⟩ : Fin n) = v := Fin.ext hpv
      refine ⟨by simpa [hpv] using hbit, ?_⟩
      have hβ : TableRank q_top (tablesAt q_top cap mb φ j)[i] :=
        tableRank_of_mem_tablesAt j _ (List.getElem_mem hi)
      have hballX : ball (masked G A₀) cap v ⊆ X := by
        intro z hz
        apply (hX z).mpr
        have hz' := hballCluster hz
        simpa [hasgv] using hz'
      have hglue := sat_iff_eval_step (mb := mb) (j := j) hcap
        (A := masked G A₀) (col := colRead n C (sigL cap mb j)) w v hβ hballX
      rw [show (v : ℕ) = Xmem p from hpv.symm, hval]
      constructor
      · rintro ⟨hh, hev⟩
        apply hglue.mpr
        simpa [atomVal, ScatVal, hpvFin] using hev
      · intro hs
        refine ⟨hasRank_stepFml hβ, ?_⟩
        simpa [atomVal, ScatVal, hpvFin] using hglue.mp hs

end Lax3Proofs.Refine.CoverActiveStreamReadback
