import Lax185574Proofs.Chain.Ram.Counts

/-!
Computing the partition `tpRel G B r` as labels.

The command `tpCom` leaves in `lab` the least-vertex labelling of
`tpRel G B r`, for the set `B` given by the 0/1 array `inB`, the
adjacency matrix `adj` and `r` in the scalar `tr`. It first computes the
atomic types by `n + 1` refinements (`tp0`), then runs `r` rounds
(`tpRound`), each of which counts neighbors per class and refines by one
key per vertex. The arrays `tab`, `cnt` and `sz` are zero before and
after. The cost is `O((r + 1) n²)`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram Lax185574Proofs.Chain

/-! ### Equality as a number -/

/-- `1` if the two values are equal, else `0`. -/
def eqX (e f : Expr) : Expr := .sub (.lit 1) (.add (.sub e f) (.sub f e))

theorem evalB_eqX {B : ℕ} {σ : Env} {e f : Expr} {a b : ℕ} (he : e.evalB B σ = some a)
    (hf : f.evalB B σ = some b) (ha : a < B) (hb : b < B) (hB : 1 < B) :
    (eqX e f).evalB B σ = some (ind (a = b)) := by
  have h1 := evalB_bin (op := .sub) he hf (by simp; omega)
  have h2 := evalB_bin (op := .sub) hf he (by simp; omega)
  have h3 := evalB_bin (op := .add) h1 h2 (by simp; omega)
  have h4 := evalB_bin (op := .sub) (evalB_lit (n := 1) (σ := σ) hB) h3 (by simp; omega)
  unfold eqX
  rw [h4]
  unfold ind
  by_cases h : a = b
  · simp [h]
  · simp [h]; omega

@[simp] theorem size_eqX (e f : Expr) : (eqX e f).size = 2 * e.size + 2 * f.size + 5 := by
  simp [eqX]; ring

/-! ### The context -/

/-- The scalars the types phase writes. -/
def tpVars : List String := ["b", "a", "ty", "tk", "cu", "cz", "ru", "rt"]

/-- The arrays the types phase writes. -/
def tpArrs : List String := ["lab", "key", "lab2", "tab", "labk", "cnt", "sz"]

/-- What the types phase reads, and the lengths of its arrays. -/
structure TBase (n r : ℕ) (G : SimpleGraph (Fin n)) (B : Finset (Fin n)) (τ : Env) : Prop where
  hn : τ.vars "n" = n
  hM : τ.vars "M" = n + 4
  htr : τ.vars "tr" = r
  hadj : Mat τ "adj" n (fun u v => ind (gA G u v))
  hinB : Vec τ "inB" n (fun u => ind (inBN B u))
  llab : (τ.arrs "lab").length = n
  lkey : (τ.arrs "key").length = n
  llab2 : (τ.arrs "lab2").length = n
  llabk : (τ.arrs "labk").length = n
  ltab : n * (n + 4) ≤ (τ.arrs "tab").length
  lcnt : (τ.arrs "cnt").length = n * n
  lsz : (τ.arrs "sz").length = n

variable {n r : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {B : Finset (Fin n)}

theorem TBase.setVar {τ : Env} (h : TBase n r G B τ) {x : String} (hx : x ∈ tpVars) (v : ℕ) :
    TBase n r G B (τ.setVar x v) := by
  have h1 : x ≠ "n" := by intro e; subst e; simp [tpVars] at hx
  have h2 : x ≠ "M" := by intro e; subst e; simp [tpVars] at hx
  have h3 : x ≠ "tr" := by intro e; subst e; simp [tpVars] at hx
  exact ⟨by simp [Ne.symm h1, h.hn], by simp [Ne.symm h2, h.hM], by simp [Ne.symm h3, h.htr],
    h.hadj.of_eq rfl, h.hinB.of_eq rfl, by simp [h.llab], by simp [h.lkey], by simp [h.llab2],
    by simp [h.llabk], by simpa using h.ltab, by simp [h.lcnt], by simp [h.lsz]⟩

theorem TBase.setArr {τ : Env} (h : TBase n r G B τ) {a : String} (ha : a ∈ tpArrs) (i v : ℕ) :
    TBase n r G B (τ.setArr a i v) := by
  have h1 : a ≠ "adj" := by intro e; subst e; simp [tpArrs] at ha
  have h2 : a ≠ "inB" := by intro e; subst e; simp [tpArrs] at ha
  refine ⟨by simp [h.hn], by simp [h.hM], by simp [h.htr], h.hadj.of_eq (by simp [Ne.symm h1]),
    h.hinB.of_eq (by simp [Ne.symm h2]), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [length_arrs_setArr] <;>
    first | exact h.llab | exact h.lkey | exact h.llab2 | exact h.llabk | exact h.ltab |
      exact h.lcnt | exact h.lsz

theorem inBN_lt {B : Finset (Fin n)} {y : ℕ} (h : inBN B y) : y < n := h.1

/-! ### Atomic types -/

/-- The first key of the atomic types. -/
def key0E : Expr := .mul (.get "inB" (.var "b")) (.add (.var "b") (.lit 1))

/-- The key of the atomic types for the vertex `ty`. -/
def keyAE : Expr := .mul (.get "inB" (.var "ty")) (.get "adj" (rm "b" "ty"))

/-- One refinement of the atomic types. -/
def tp0Step : Com := .seq (rowFill "key" (.var "b") keyAE) refine

/-- The atomic types. -/
def tp0 : Com :=
  .seq (rowFill "lab" (.var "b") (.lit 0))
    (.seq (rowFill "key" (.var "b") key0E) (.seq refine (forUp "ty" (.var "n") tp0Step)))

/-- The context a generic lemma of this file is run in: the caller's
facts `Ctx`, which must survive the scalars and arrays of the phase. -/
structure TpHyp (n r : ℕ) (G : SimpleGraph (Fin n)) (B : Finset (Fin n)) (Ctx : Env → Prop) :
    Prop where
  base : ∀ τ, Ctx τ → TBase n r G B τ
  cv : ∀ τ x v, Ctx τ → x ∈ tpVars → Ctx (τ.setVar x v)
  ca : ∀ τ a i v, Ctx τ → a ∈ tpArrs → Ctx (τ.setArr a i v)

/-- A generic refinement inside the types phase: the key array holds
`κ`, the labels are those of `E`. -/
theorem refine_tp {B' : ℕ} {Ctx : Env → Prop} (hH : TpHyp n r G B Ctx)
    {E : ℕ → ℕ → Prop} (hE : IsEqv n E) {κ : ℕ → ℕ} (hκ : ∀ u < n, κ u < n + 4)
    (hB' : n * (n + 4) + 3 * n + 10 < B')
    (P : Env → Prop) (hPv : ∀ τ x v, P τ → x ∈ ["ru", "rt"] → P (τ.setVar x v))
    (hPa : ∀ τ a i v, P τ → a ∈ ["lab", "lab2", "tab"] → P (τ.setArr a i v))
    {σ : Env} (hσ : Ctx σ) (hP : P σ) (hk : Vec σ "key" n κ) (hlab : Vec σ "lab" n (lbl n E))
    (hz : Zero σ "tab") :
    ∃ σ', Run B' refine σ σ' (n * 100 + 40) ∧ Ctx σ' ∧ P σ' ∧
      Vec σ' "lab" n (lbl n (fun v u => E v u ∧ κ v = κ u)) ∧ Zero σ' "tab" ∧
      σ'.arrs "key" = σ.arrs "key" := by
  have hb := hH.base σ hσ
  obtain ⟨σ', hr, ⟨hC', hP', hk'⟩, hlab', hz', -, -⟩ :=
    refine_run (B := B') (n := n) (M := n + 4) (L := lbl n E) (κ := κ)
      (fun τ => Ctx τ ∧ P τ ∧ τ.arrs "key" = σ.arrs "key")
      (fun u hu => lbl_lt hE hu) hκ (by omega) (by omega)
      (fun τ h => (hH.base τ h.1).hn) (fun τ h => (hH.base τ h.1).hM)
      (fun τ h => hk.of_eq h.2.2)
      (fun τ v h => ⟨hH.cv _ _ _ h.1 (by simp [tpVars]), hPv _ _ _ h.2.1 (by simp),
        by simp [h.2.2]⟩)
      (fun τ v h => ⟨hH.cv _ _ _ h.1 (by simp [tpVars]), hPv _ _ _ h.2.1 (by simp),
        by simp [h.2.2]⟩)
      (fun τ a i v h ha => by
        have ha' : a ≠ "key" := by
          intro e; subst e; simp at ha
        refine ⟨hH.ca _ _ _ _ h.1 (by simp [tpArrs] at ha ⊢; tauto), hPa _ _ _ _ h.2.1 ha, ?_⟩
        simp [Ne.symm ha', h.2.2])
      ⟨hσ, hP, rfl⟩ hlab hz hb.ltab hb.llab2
  exact ⟨σ', hr, hC', hP', hlab'.congr fun u hu => refine_lbl hE κ hu, hz', hk'⟩

/-- Filling the key array inside the types phase. -/
theorem fillKey_tp {B' : ℕ} {Ctx : Env → Prop} (hH : TpHyp n r G B Ctx) {e : Expr}
    {κ : ℕ → ℕ} (hnB : n < B') (P : Env → Prop)
    (hPv : ∀ τ v, P τ → P (τ.setVar "b" v))
    (hPa : ∀ τ i v, P τ → P (τ.setArr "key" i v))
    (he : ∀ τ k, Ctx τ → P τ → τ.vars "b" = k → k < n → e.evalB B' τ = some (κ k))
    {σ : Env} (hσ : Ctx σ) (hP : P σ) :
    ∃ σ', Run B' (rowFill "key" (.var "b") e) σ σ' (n * (e.size + 10) + 6) ∧ Ctx σ' ∧ P σ' ∧
      Vec σ' "key" n κ ∧ ∀ a, a ≠ "key" → σ'.arrs a = σ.arrs a := by
  have hb := hH.base σ hσ
  obtain ⟨σ', hr, ⟨hC', hP', hfr⟩, hl', hg'⟩ :=
    rowFill_run (B := B') (n := n) (base := 0) (K := e.size + 2) (arr := "key") (ie := .var "b")
      (e := e) (fun τ => Ctx τ ∧ P τ ∧ ∀ a, a ≠ "key" → τ.arrs a = σ.arrs a) κ hnB
      (fun τ h => (hH.base τ h.1).hn)
      (fun τ x h => ⟨hH.cv _ _ _ h.1 (by simp [tpVars]), hPv _ _ h.2.1,
        by simpa using h.2.2⟩)
      (fun τ i x h => ⟨hH.ca _ _ _ _ h.1 (by simp [tpArrs]), hPa _ _ _ h.2.1,
        fun a ha => by rw [arrs_setArr, if_neg ha]; exact h.2.2 a ha⟩)
      (fun τ k h hb hk => by simp [hb]; omega)
      (fun τ k h hb hk => he τ k h.1 h.2.1 hb hk) (by simp; omega) ⟨hσ, hP, fun _ _ => rfl⟩
      (by rw [hb.lkey]; omega)
  refine ⟨σ', hr.mono (by ring_nf; omega), hC', hP', ⟨by rw [hl', hb.lkey], fun u hu => ?_⟩, hfr⟩
  rw [hg' u]; simp [hu]

theorem isEqv_true : IsEqv n (fun _ _ => True) := ⟨fun _ _ => trivial, fun _ _ _ => trivial,
  fun _ _ _ _ _ => trivial⟩

theorem lbl_true {u : ℕ} (hu : u < n) : lbl n (fun _ _ => True) u = 0 := by
  obtain ⟨-, -, h⟩ := lbl_spec (isEqv_true (n := n)) hu
  by_contra hc; exact h 0 (by omega) trivial

theorem IsEqv.conjAll {E : ℕ → ℕ → Prop} (hE : IsEqv n E) (F : ℕ → ℕ → ℕ) (j : ℕ) :
    IsEqv n (fun v u => E v u ∧ ∀ y < j, F y v = F y u) :=
  ⟨fun u hu => ⟨hE.refl u hu, fun _ _ => rfl⟩,
    fun u v h => ⟨hE.symm _ _ h.1, fun y hy => (h.2 y hy).symm⟩,
    fun u v w h h' => ⟨hE.trans _ _ _ h.1 h'.1, fun y hy => (h.2 y hy).trans (h'.2 y hy)⟩⟩

theorem conjAll_succ {E : ℕ → ℕ → Prop} (F : ℕ → ℕ → ℕ) (j : ℕ) (u v : ℕ) :
    ((E v u ∧ ∀ y < j, F y v = F y u) ∧ F j v = F j u) ↔
      (E v u ∧ ∀ y < j + 1, F y v = F y u) := by
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, fun y hy => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hy with hy | rfl
    · exact h2 y hy
    · exact h3
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, fun y hy => h2 y (by omega)⟩, h2 j (by omega)⟩

/-- The bound on values of the types phase. -/
def TpBound (n B' : ℕ) : Prop := n * (n + 4) + 3 * n + 10 < B'

/-- **The atomic types.** -/
theorem tp0_run {B' : ℕ} {Ctx : Env → Prop} (hH : TpHyp n r G B Ctx) (hB' : TpBound n B')
    {σ : Env} (hσ : Ctx σ) (hz : Zero σ "tab") :
    ∃ σ', Run B' tp0 σ σ' (n * (n * 300 + 400) + 300) ∧ Ctx σ' ∧
      Vec σ' "lab" n (lbl n (tpN G B 0)) ∧ Zero σ' "tab" := by
  unfold TpBound at hB'
  have hb := hH.base σ hσ
  -- labels zero
  obtain ⟨σ1, hr1, hC1, hl1, hg1⟩ :=
    rowFill_run (B := B') (n := n) (base := 0) (K := 3) (arr := "lab") (ie := .var "b")
      (e := .lit 0) (fun τ => Ctx τ ∧ τ.arrs "tab" = σ.arrs "tab") (fun _ => 0) (by omega)
      (fun τ h => (hH.base τ h.1).hn)
      (fun τ x h => ⟨hH.cv _ _ _ h.1 (by simp [tpVars]), by simp [h.2]⟩)
      (fun τ i x h => ⟨hH.ca _ _ _ _ h.1 (by simp [tpArrs]), by simp [h.2]⟩)
      (fun τ k h hb hk => by simp [hb]; omega) (fun τ k h hb hk => by simp; omega) (by simp)
      ⟨hσ, rfl⟩ (by rw [hb.llab]; omega)
  have hv1 : Vec σ1 "lab" n (lbl n (fun _ _ => True)) :=
    ⟨by rw [hl1, hb.llab], fun u hu => by rw [hg1 u, lbl_true hu]; simp [hu]⟩
  have hz1 : Zero σ1 "tab" := by
    intro t ht; rw [hC1.2] at ht ⊢; exact hz t ht
  -- the first key
  obtain ⟨σ2, hr2, hC2, hP2, hk2, hfr2⟩ :=
    fillKey_tp (B' := B') hH (e := key0E) (κ := key0 B) (by omega) (fun _ => True)
      (fun _ _ _ => trivial) (fun _ _ _ _ => trivial)
      (fun τ k h _ hbk hk => by
        have hb := hH.base τ h
        have e1 := hb.hinB.evalB (B := B') hbk hk (by omega)
          (by have := ind_le_one (inBN B k); omega)
        have := ind_le_one (inBN B k)
        have hkey : ind (inBN B k) * (k + 1) ≤ n := by nlinarith
        have e2 := evalB_bin (op := .mul) e1 (evalB_bin (op := .add)
          (evalB_var (x := "b") (σ := τ) (B := B') (by omega)) (evalB_lit (n := 1) (by omega))
          (by simp [hbk]; omega)) (by simp [hbk]; omega)
        simpa [key0E, key0, hbk] using e2) hC1.1 trivial
  have hv2 : Vec σ2 "lab" n (lbl n (fun _ _ => True)) := hv1.of_eq (hfr2 _ (by decide))
  have hz2 : Zero σ2 "tab" := by
    intro t ht; rw [hfr2 _ (by decide)] at ht ⊢; exact hz1 t ht
  obtain ⟨σ3, hr3, hC3, -, hv3, hz3, -⟩ :=
    refine_tp (B' := B') hH isEqv_true (κ := key0 B)
      (fun u hu => by have := key0_lt (B := B) (u := u); omega) (by omega) (fun _ => True)
      (fun _ _ _ _ _ => trivial) (fun _ _ _ _ _ _ => trivial) hC2 trivial hk2 hv2 hz2
  -- the keys of the vertices
  set E0 : ℕ → ℕ → Prop := fun v u => True ∧ key0 B v = key0 B u with hE0
  have hE0e : IsEqv n E0 := isEqv_true.conj _
  let I : ℕ → Env → Prop := fun j τ => Ctx τ ∧
    Vec τ "lab" n (lbl n (fun v u => E0 v u ∧ ∀ y < j, keyA G B y v = keyA G B y u)) ∧
    Zero τ "tab"
  obtain ⟨σ4, hr4, ⟨hC4, hv4, hz4⟩, -⟩ :=
    forUp_run (B := B') (i := "ty") (e := .var "n") (body := tp0Step) (N := n)
      (K := n * 200 + 100) I (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [(hH.base τ hI.1).hn]; omega),
        (hH.base τ hI.1).hn])
      (σ := σ3) ⟨hH.cv _ _ _ hC3 (by simp [tpVars]),
        (hv3.of_eq (by simp)).congr fun u hu => lbl_congr (fun u _ v _ => by simp) hu,
        fun t ht => by simpa using hz3 t (by simpa using ht)⟩
      (by
        rintro j hj τ ⟨hCτ, hvτ, hzτ⟩ hty
        obtain ⟨τ1, hrk, hCk, htyk, hkk, hfrk⟩ :=
          fillKey_tp (B' := B') hH (e := keyAE) (κ := keyA G B j) (by omega)
            (fun ρ => ρ.vars "ty" = j) (fun ρ v h => by simp [h]) (fun ρ i v h => by simp [h])
            (fun ρ k h hP hbk hk => by
              have hb := hH.base ρ h
              have e1 := hb.hinB.evalB (B := B') hP hj (by omega)
                (by have := ind_le_one (inBN B j); omega)
              have e2 := hb.hadj.evalB (B := B') hb.hn hbk hP hk hj (by nlinarith) (by omega)
                (by have := ind_le_one (gA G k j); omega)
              have := ind_le_one (inBN B j)
              have := ind_le_one (gA G k j)
              have e3 := evalB_bin (op := .mul) e1 e2 (by simp; nlinarith)
              simpa [keyAE, keyA] using e3) hCτ hty
        have hvk := hvτ.of_eq (hfrk _ (by decide))
        have hzk : Zero τ1 "tab" := by
          intro t ht; rw [hfrk _ (by decide)] at ht ⊢; exact hzτ t ht
        obtain ⟨τ2, hrr, hCr, htyr, hvr, hzr, -⟩ :=
          refine_tp (B' := B') hH (hE0e.conjAll (keyA G B) j) (κ := keyA G B j)
            (fun u hu => by have := keyA_le (G := G) (B := B) (y := j) (u := u); omega) (by omega)
            (fun ρ => ρ.vars "ty" = j)
            (fun ρ x v h hx => by
              simp at hx; rcases hx with rfl | rfl <;> simp [h])
            (fun ρ a i v h _ => by simp [h]) hCk htyk hkk hvk hzk
        refine ⟨τ2, (Run.seq hrk hrr).mono (by simp [keyAE, rm]; nlinarith), htyr,
          hH.cv _ _ _ hCr (by simp [tpVars]), ?_, fun t ht => by simpa using hzr t (by simpa using ht)⟩
        exact (hvr.of_eq (by simp)).congr fun u hu =>
          lbl_congr (fun u _ v _ => conjAll_succ (keyA G B) j u v) hu)
  refine ⟨σ4, (Run.seq hr1 (Run.seq hr2 (Run.seq hr3 hr4))).mono ?_, hC4,
    hv4.congr fun u hu => lbl_congr (fun u hu v hv => (tpN_zero_iff hu hv).symm) hu, hz4⟩
  simp [key0E]
  nlinarith

/-! ### One round -/

/-- The label of the class of `ty`. -/
def cE : Expr := .get "labk" (.var "ty")
/-- The number of neighbors of `b` in the class of `ty`. -/
def cntE : Expr := .get "cnt" (.add (.mul (.var "b") (.var "n")) cE)
/-- The size of the class of `ty` minus `b`. -/
def sE : Expr := .sub (.get "sz" cE) (eqX (.get "labk" (.var "b")) cE)
/-- The key of `b` for the class of `ty`. -/
def keySE : Expr := .add (.mul (.lit 2) (eqX cntE sE)) (eqX cntE (.lit 0))

/-- The arrays `labk`, `cnt` and `sz` are those of `σ`. -/
def QSnap (σ τ : Env) : Prop :=
  τ.arrs "labk" = σ.arrs "labk" ∧ τ.arrs "cnt" = σ.arrs "cnt" ∧ τ.arrs "sz" = σ.arrs "sz"

theorem QSnap.setArr {σ τ : Env} (h : QSnap σ τ) (a : String) (ha : a ∉ ["labk", "cnt", "sz"])
    (i v : ℕ) : QSnap σ (τ.setArr a i v) := by
  simp at ha
  obtain ⟨h1, h2, h3⟩ := ha
  exact ⟨by simp [Ne.symm h1, h.1], by simp [Ne.symm h2, h.2.1], by simp [Ne.symm h3, h.2.2]⟩

/-- One refinement of a round. -/
def tpKeyStep : Com := .seq (rowFill "key" (.var "b") keySE) refine

/-- One round of the types. -/
def tpRound : Com :=
  .seq (rowFill "labk" (.var "b") (.get "lab" (.var "b")))
    (.seq cntPhase (.seq szPhase (.seq (forUp "ty" (.var "n") tpKeyStep)
      (.seq (matFill "cnt" (.lit 0)) (rowFill "sz" (.var "b") (.lit 0))))))

theorem szN_le (L : ℕ → ℕ) (c : ℕ) : szN n L c ≤ n := by
  classical
  unfold szN; exact card_filter_range_le _ _

theorem cntN_le (L : ℕ → ℕ) (u c : ℕ) : cntN G L u c ≤ n := by
  classical
  unfold cntN; exact card_filter_range_le _ _

theorem evalB_keySE {B' : ℕ} {τ : Env} {L : ℕ → ℕ} (hL : ∀ u < n, L u < n)
    (hB' : n * (n + 4) + 3 * n + 10 < B') (hn : τ.vars "n" = n)
    (hlabk : Vec τ "labk" n L) (hcnt : Mat τ "cnt" n (fun u c => cntN G L u c))
    (hsz : Vec τ "sz" n (fun c => szN n L c)) {j k : ℕ} (hty : τ.vars "ty" = j)
    (hb : τ.vars "b" = k) (hj : j < n) (hk : k < n) :
    keySE.evalB B' τ = some (keyS G L j k) := by
  have hLj := hL j hj
  have hLk := hL k hk
  have e1 : cE.evalB B' τ = some (L j) := hlabk.evalB hty hj (by omega) (by omega)
  have hidx := rowMajor_lt hk hLj
  have hnn : k * n ≤ k * n + L j := Nat.le_add_right _ _
  have e2 : (Expr.add (.mul (.var "b") (.var "n")) cE).evalB B' τ = some (k * n + L j) := by
    have := evalB_bin (op := .add) (evalB_bin (op := .mul) (evalB_var (x := "b") (σ := τ)
      (B := B') (by omega)) (evalB_var (x := "n") (by omega)) (by simp [hb, hn]; nlinarith)) e1
      (by simp [hb, hn]; nlinarith)
    simpa [hb, hn] using this
  have hc := cntN_le (G := G) L k (L j)
  have hs := szN_le (n := n) L (L j)
  have e3 : cntE.evalB B' τ = some (cntN G L k (L j)) :=
    evalB_get e2 (hcnt.get k hk (L j) hLj) (by omega)
  have e4 : (Expr.get "labk" (.var "b")).evalB B' τ = some (L k) :=
    hlabk.evalB hb hk (by omega) (by omega)
  have e5 := evalB_eqX e4 e1 (by omega) (by omega) (by omega)
  have hi := ind_le_one (L k = L j)
  have e6 : sE.evalB B' τ = some (szN n L (L j) - ind (L k = L j)) :=
    evalB_bin (op := .sub) (evalB_get e1 (hsz.get _ hLj) (by omega)) e5 (by simp; omega)
  have e7 := evalB_eqX e3 e6 (by omega) (by omega) (by omega)
  have e8 := evalB_eqX e3 (evalB_lit (n := 0) (σ := τ) (B := B') (by omega)) (by omega)
    (by omega) (by omega)
  have i1 := ind_le_one (cntN G L k (L j) = szN n L (L j) - ind (L k = L j))
  have i2 := ind_le_one (cntN G L k (L j) = 0)
  have e9 := evalB_bin (op := .add) (evalB_bin (op := .mul) (evalB_lit (n := 2) (σ := τ)
    (B := B') (by omega)) e7 (by simp; omega)) e8 (by simp; omega)
  simpa [keySE, keyS] using e9

/-- **One round of the types.** -/
theorem tpRound_run {B' : ℕ} {Ctx : Env → Prop} (hH : TpHyp n r G B Ctx) (hB' : TpBound n B')
    {k : ℕ} {σ : Env} (hσ : Ctx σ) (hlab : Vec σ "lab" n (lbl n (tpN G B k)))
    (hz : Zero σ "tab") (hcnt : Mat σ "cnt" n (fun _ _ => 0)) (hsz : Vec σ "sz" n (fun _ => 0)) :
    ∃ σ', Run B' tpRound σ σ' (n * (n * 1000 + 1000) + 1000) ∧ Ctx σ' ∧
      Vec σ' "lab" n (lbl n (tpN G B (k + 1))) ∧ Zero σ' "tab" ∧
      Mat σ' "cnt" n (fun _ _ => 0) ∧ Vec σ' "sz" n (fun _ => 0) := by
  unfold TpBound at hB'
  have hb := hH.base σ hσ
  set L := lbl n (tpN G B k) with hLdef
  have hE := tpN_isEqv (G := G) (B := B) k
  have hL : ∀ u < n, L u < n := fun u hu => lbl_lt hE hu
  -- copy the labels
  obtain ⟨σ1, hr1, ⟨hC1, ha1⟩, hl1, hg1⟩ :=
    rowFill_run (B := B') (n := n) (base := 0) (K := 4) (arr := "labk") (ie := .var "b")
      (e := .get "lab" (.var "b"))
      (fun τ => Ctx τ ∧ ∀ a, a ≠ "labk" → τ.arrs a = σ.arrs a) L (by omega)
      (fun τ h => (hH.base τ h.1).hn)
      (fun τ x h => ⟨hH.cv _ _ _ h.1 (by simp [tpVars]), by simpa using h.2⟩)
      (fun τ i x h => ⟨hH.ca _ _ _ _ h.1 (by simp [tpArrs]),
        fun a ha => by rw [arrs_setArr, if_neg ha]; exact h.2 a ha⟩)
      (fun τ k h hb hk => by simp [hb]; omega)
      (fun τ u h hbu hu => (hlab.of_eq (h.2 _ (by decide))).evalB hbu hu (by omega)
        (by have := hL u hu; omega)) (by simp)
      ⟨hσ, fun _ _ => rfl⟩ (by rw [hb.llabk]; omega)
  have hk1 : Vec σ1 "labk" n L := ⟨by rw [hl1, hb.llabk], fun u hu => by rw [hg1 u]; simp [hu]⟩
  -- counts
  obtain ⟨σ2, hr2, ⟨hC2, ha2⟩, hm2⟩ :=
    cntPhase_run (B := B') (G := G) (L := L) (fun τ => Ctx τ ∧ ∀ a, a ≠ "cnt" → τ.arrs a = σ1.arrs a) hL
      (by have : n * (n + 4) = n * n + 4 * n := by ring
          omega)
      (fun τ h => ⟨(hH.base τ h.1).hn, (hH.base τ h.1).hadj, hk1.of_eq (h.2 _ (by decide))⟩)
      (fun τ v h => ⟨hH.cv _ _ _ h.1 (by simp [tpVars]), by simpa using h.2⟩)
      (fun τ v h => ⟨hH.cv _ _ _ h.1 (by simp [tpVars]), by simpa using h.2⟩)
      (fun τ i v h => ⟨hH.ca _ _ _ _ h.1 (by simp [tpArrs]),
        fun a ha => by rw [arrs_setArr, if_neg ha]; exact h.2 a ha⟩)
      ⟨hC1, fun _ _ => rfl⟩ (hcnt.of_eq (ha1 _ (by decide)))
  have hk2 : Vec σ2 "labk" n L := hk1.of_eq (ha2 _ (by decide))
  obtain ⟨σ3, hr3, ⟨hC3, ha3⟩, hs3⟩ :=
    szPhase_run (B := B') (G := G) (L := L) (fun τ => Ctx τ ∧ ∀ a, a ≠ "sz" → τ.arrs a = σ2.arrs a) hL
      (by omega)
      (fun τ h => ⟨(hH.base τ h.1).hn, (hH.base τ h.1).hadj, hk2.of_eq (h.2 _ (by decide))⟩)
      (fun τ v h => ⟨hH.cv _ _ _ h.1 (by simp [tpVars]), by simpa using h.2⟩)
      (fun τ i v h => ⟨hH.ca _ _ _ _ h.1 (by simp [tpArrs]),
        fun a ha => by rw [arrs_setArr, if_neg ha]; exact h.2 a ha⟩)
      ⟨hC2, fun _ _ => rfl⟩ ((hsz.of_eq (ha1 _ (by decide))).of_eq (ha2 _ (by decide)))
  have hk3 : Vec σ3 "labk" n L := hk2.of_eq (ha3 _ (by decide))
  have hm3 : Mat σ3 "cnt" n (fun u c => cntN G L u c) := hm2.of_eq (ha3 _ (by decide))
  have hv3 : Vec σ3 "lab" n L := ((hlab.of_eq (ha1 _ (by decide))).of_eq
    (ha2 _ (by decide))).of_eq (ha3 _ (by decide))
  have hz3 : Zero σ3 "tab" := by
    intro t ht
    rw [ha3 _ (by decide), ha2 _ (by decide), ha1 _ (by decide)] at ht ⊢; exact hz t ht
  -- the refinements
  let Q : Env → Prop := QSnap σ3
  let I : ℕ → Env → Prop := fun j τ => Ctx τ ∧ Q τ ∧
    Vec τ "lab" n (lbl n (fun v u => tpN G B k v u ∧ ∀ y < j, keyS G L y v = keyS G L y u)) ∧
    Zero τ "tab"
  obtain ⟨σ4, hr4, ⟨hC4, hQ4, hv4, hz4⟩, -⟩ :=
    forUp_run (B := B') (i := "ty") (e := .var "n") (body := tpKeyStep) (N := n)
      (K := n * 300 + 100) I (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [(hH.base τ hI.1).hn]; omega),
        (hH.base τ hI.1).hn])
      (σ := σ3) ⟨hH.cv _ _ _ hC3 (by simp [tpVars]), ⟨rfl, rfl, rfl⟩,
        (hv3.of_eq (by simp)).congr fun u hu => lbl_congr (fun u _ v _ => by simp) hu,
        fun t ht => by simpa using hz3 t (by simpa using ht)⟩
      (by
        rintro j hj τ ⟨hCτ, hQ, hvτ, hzτ⟩ hty
        obtain ⟨τ1, hrk, hCk, ⟨htyk, hQk⟩, hkk, hfrk⟩ :=
          fillKey_tp (B' := B') hH (e := keySE) (κ := keyS G L j) (by omega)
            (fun ρ => ρ.vars "ty" = j ∧ Q ρ) (fun ρ v h => ⟨by simpa using h.1, h.2⟩)
            (fun ρ i v h => ⟨by simpa using h.1, h.2.setArr "key" (by decide) i v⟩)
            (fun ρ u h hP hbu hu => evalB_keySE hL hB' (hH.base ρ h).hn
              (hk3.of_eq hP.2.1) (hm3.of_eq hP.2.2.1) (hs3.of_eq hP.2.2.2) hP.1 hbu hj hu)
            hCτ ⟨hty, hQ⟩
        have hvk := hvτ.of_eq (hfrk _ (by decide))
        have hzk : Zero τ1 "tab" := by
          intro t ht; rw [hfrk _ (by decide)] at ht ⊢; exact hzτ t ht
        obtain ⟨τ2, hrr, hCr, ⟨htyr, hQr⟩, hvr, hzr, -⟩ :=
          refine_tp (B' := B') hH (hE.conjAll (keyS G L) j) (κ := keyS G L j)
            (fun u hu => by have := keyS_le (G := G) (L := L) (y := j) (u := u); omega) (by omega)
            (fun ρ => ρ.vars "ty" = j ∧ Q ρ)
            (fun ρ x v h hx => by
              simp at hx; rcases hx with rfl | rfl <;> exact ⟨by simpa using h.1, h.2⟩)
            (fun ρ a i v h ha => ⟨by simpa using h.1, h.2.setArr a (by
              simp at ha ⊢; rcases ha with rfl | rfl | rfl <;> simp) i v⟩)
            hCk ⟨htyk, hQk⟩ hkk hvk hzk
        refine ⟨τ2, (Run.seq hrk hrr).mono (by simp [keySE, cntE, sE, cE]; nlinarith), htyr,
          hH.cv _ _ _ hCr (by simp [tpVars]), hQr, ?_,
          fun t ht => by simpa using hzr t (by simpa using ht)⟩
        exact (hvr.of_eq (by simp)).congr fun u hu =>
          lbl_congr (fun u _ v _ => conjAll_succ (keyS G L) j u v) hu)
  have hv4' : Vec σ4 "lab" n (lbl n (tpN G B (k + 1))) :=
    hv4.congr fun u hu => lbl_congr (fun u hu v hv => (tpN_succ_iff hu hv).symm) hu
  -- clearing
  obtain ⟨σ5, hr5, ⟨hC5, ha5⟩, hm5⟩ :=
    matFill_run (B := B') (n := n) (K := 7) (arr := "cnt") (e := .lit 0)
      (fun τ => Ctx τ ∧ ∀ a, a ≠ "cnt" → τ.arrs a = σ4.arrs a) (fun _ _ => 0) (by nlinarith)
      (fun τ h => (hH.base τ h.1).hn)
      (fun τ x h => ⟨hH.cv _ _ _ h.1 (by simp [tpVars]), by simpa using h.2⟩)
      (fun τ x h => ⟨hH.cv _ _ _ h.1 (by simp [tpVars]), by simpa using h.2⟩)
      (fun τ i x h => ⟨hH.ca _ _ _ _ h.1 (by simp [tpArrs]),
        fun a ha => by rw [arrs_setArr, if_neg ha]; exact h.2 a ha⟩)
      (fun τ i j h _ _ _ _ => by simp; omega) (by simp) ⟨hC4, fun _ _ => rfl⟩
      ((hH.base σ4 hC4).lcnt)
  obtain ⟨σ6, hr6, ⟨hC6, ha6⟩, hl6, hg6⟩ :=
    rowFill_run (B := B') (n := n) (base := 0) (K := 3) (arr := "sz") (ie := .var "b")
      (e := .lit 0) (fun τ => Ctx τ ∧ ∀ a, a ≠ "sz" → τ.arrs a = σ5.arrs a) (fun _ => 0) (by omega)
      (fun τ h => (hH.base τ h.1).hn)
      (fun τ x h => ⟨hH.cv _ _ _ h.1 (by simp [tpVars]), by simpa using h.2⟩)
      (fun τ i x h => ⟨hH.ca _ _ _ _ h.1 (by simp [tpArrs]),
        fun a ha => by rw [arrs_setArr, if_neg ha]; exact h.2 a ha⟩)
      (fun τ k h hb hk => by simp [hb]; omega) (fun τ k h hb hk => by simp; omega) (by simp)
      ⟨hC5, fun _ _ => rfl⟩ (by rw [(hH.base σ5 hC5).lsz]; omega)
  refine ⟨σ6, (Run.seq hr1 (Run.seq hr2 (Run.seq hr3 (Run.seq hr4 (Run.seq hr5 hr6))))).mono ?_,
    hC6, (hv4'.of_eq (ha5 _ (by decide))).of_eq (ha6 _ (by decide)), ?_,
    hm5.of_eq (ha6 _ (by decide)),
    ⟨by rw [hl6, (hH.base σ5 hC5).lsz], fun u hu => by rw [hg6 u]; simp [hu]⟩⟩
  · simp
    nlinarith
  · intro t ht
    rw [ha6 _ (by decide), ha5 _ (by decide)] at ht ⊢; exact hz4 t ht

/-! ### All rounds -/

/-- **The types**: `lab` becomes the labelling of `tpRel G B r`. -/
def tpCom : Com := .seq tp0 (forUp "tk" (.var "tr") tpRound)

/-- The cost of the types phase. -/
def tpCost (n r : ℕ) : ℕ := (r + 1) * (n * (n * 1000 + 1000) + 1100)

theorem tpCom_run {B' : ℕ} {Ctx : Env → Prop} (hH : TpHyp n r G B Ctx) (hB' : TpBound n B')
    (hrB : r < B') {σ : Env} (hσ : Ctx σ) (hz : Zero σ "tab")
    (hcnt : Mat σ "cnt" n (fun _ _ => 0)) (hsz : Vec σ "sz" n (fun _ => 0)) :
    ∃ σ', Run B' tpCom σ σ' (tpCost n r) ∧ Ctx σ' ∧
      Vec σ' "lab" n (lbl n (tpN G B r)) ∧ Zero σ' "tab" ∧
      Mat σ' "cnt" n (fun _ _ => 0) ∧ Vec σ' "sz" n (fun _ => 0) := by
  obtain ⟨σ1, hr1, hC1, hv1, hz1⟩ := tp0_run (B' := B') hH hB' hσ hz
  have hc1 : Mat σ1 "cnt" n (fun _ _ => 0) := hcnt.of_eq (hr1.frame_arr "cnt" (by decide))
  have hs1 : Vec σ1 "sz" n (fun _ => 0) := hsz.of_eq (hr1.frame_arr "sz" (by decide))
  let I : ℕ → Env → Prop := fun k τ => Ctx τ ∧ Vec τ "lab" n (lbl n (tpN G B k)) ∧
    Zero τ "tab" ∧ Mat τ "cnt" n (fun _ _ => 0) ∧ Vec τ "sz" n (fun _ => 0)
  obtain ⟨σ2, hr2, ⟨hC2, hv2, hz2, hc2, hs2⟩, -⟩ :=
    forUp_run (B := B') (i := "tk") (e := .var "tr") (body := tpRound) (N := r)
      (K := n * (n * 1000 + 1000) + 1000) I hrB
      (fun k _ τ hI _ => by rw [evalB_var (by rw [(hH.base τ hI.1).htr]; omega),
        (hH.base τ hI.1).htr])
      (σ := σ1) ⟨hH.cv _ _ _ hC1 (by simp [tpVars]), hv1.of_eq rfl,
        fun t ht => by simpa using hz1 t (by simpa using ht), hc1.of_eq rfl, hs1.of_eq rfl⟩
      (by
        rintro k hk τ ⟨hCτ, hvτ, hzτ, hcτ, hsτ⟩ htk
        obtain ⟨τ', hr, hC', hv', hz', hc', hs'⟩ := tpRound_run (B' := B') hH hB' hCτ hvτ hzτ hcτ hsτ
        refine ⟨τ', hr, by rw [hr.frame_var "tk" (by decide), htk], hH.cv _ _ _ hC' (by simp [tpVars]),
          hv'.of_eq rfl, fun t ht => by simpa using hz' t (by simpa using ht), hc'.of_eq rfl,
          hs'.of_eq rfl⟩)
  refine ⟨σ2, (Run.seq hr1 hr2).mono ?_, hC2, hv2, hz2, hc2, hs2⟩
  unfold tpCost
  simp
  nlinarith

end Lax185574Proofs.Chain.Ram
