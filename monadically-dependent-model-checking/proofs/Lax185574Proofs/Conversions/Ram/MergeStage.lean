import Lax185574Proofs.Conversions.Ram.MergeOut

/-!
One stage of the program of lem:better-mw.

For the chain set `X = S_t`, the stage computes the labels of the
partition `𝒫` into atomic types over `X`, the labels of its split `𝒬`
along the least vertices of the parts, the walks of length five between
parts in both polarities, and the pair relation `R(G, 𝒫)`, and writes
the words of `𝒬` and of `R`.
-/

namespace Lax185574Proofs.Conversions.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574.Partitions Lax185574.TypeSplitting Lax185574.SplittingMonotone
open Lax185574.PairRelation Lax185574.WordEncoding

variable {n : ℕ}

/-- The arrays every phase relies on: the graph, the chain, and the
sizes of the work arrays. -/
structure Base (n m : ℕ) (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))) (τ : Env) :
    Prop where
  hn : τ.vars "n" = n
  hm : τ.vars "m" = m
  hadj : Mat τ "adj" n fun u z => ind (gA G u z)
  hinS : ∀ t < m, ∀ z < n, (τ.arrs "inS")[t * n + z]? = some (ind (z ∈ sortedVals (S.getD t ∅)))
  hlab : (τ.arrs "lab").length = n
  hqlab : (τ.arrs "qlab").length = n
  hE : (τ.arrs "E").length = n * n
  hLm : (τ.arrs "Lm").length = n * n
  hDp : (τ.arrs "Dp").length = n * n
  hDm : (τ.arrs "Dm").length = n * n
  hRm : (τ.arrs "Rm").length = n * n
  hR1 : (τ.arrs "R1").length = n
  hR3 : (τ.arrs "R3").length = n
  hR5 : (τ.arrs "R5").length = n

section Base

variable {m : ℕ} {G : SimpleGraph (Fin n)} {S : List (Finset (Fin n))}

theorem Base.of_run {B K : ℕ} {c : Com} {τ τ' : Env} (h : Base n m G S τ) (hr : Run B c τ τ' K)
    (hn : "n" ∉ c.wvars) (hm : "m" ∉ c.wvars) (ha : "adj" ∉ c.warrs) (hs : "inS" ∉ c.warrs) :
    Base n m G S τ' where
  hn := by rw [hr.frame_var "n" hn, h.hn]
  hm := by rw [hr.frame_var "m" hm, h.hm]
  hadj := h.hadj.of_eq (hr.frame_arr "adj" ha)
  hinS := by rw [hr.frame_arr "inS" hs]; exact h.hinS
  hlab := by rw [run_length_arrs hr, h.hlab]
  hqlab := by rw [run_length_arrs hr, h.hqlab]
  hE := by rw [run_length_arrs hr, h.hE]
  hLm := by rw [run_length_arrs hr, h.hLm]
  hDp := by rw [run_length_arrs hr, h.hDp]
  hDm := by rw [run_length_arrs hr, h.hDm]
  hRm := by rw [run_length_arrs hr, h.hRm]
  hR1 := by rw [run_length_arrs hr, h.hR1]
  hR3 := by rw [run_length_arrs hr, h.hR3]
  hR5 := by rw [run_length_arrs hr, h.hR5]

theorem Base.setVar {τ : Env} (h : Base n m G S τ) (x : String) (hxn : x ≠ "n") (hxm : x ≠ "m")
    (v : ℕ) : Base n m G S (τ.setVar x v) where
  hn := by simp [Ne.symm hxn, h.hn]
  hm := by simp [Ne.symm hxm, h.hm]
  hadj := h.hadj.of_eq (by simp)
  hinS := by simpa using h.hinS
  hlab := by simpa using h.hlab
  hqlab := by simpa using h.hqlab
  hE := by simpa using h.hE
  hLm := by simpa using h.hLm
  hDp := by simpa using h.hDp
  hDm := by simpa using h.hDm
  hRm := by simpa using h.hRm
  hR1 := by simpa using h.hR1
  hR3 := by simpa using h.hR3
  hR5 := by simpa using h.hR5

theorem Base.setArr {τ : Env} (h : Base n m G S τ) (a : String) (ha : a ≠ "adj") (hs : a ≠ "inS")
    (i v : ℕ) : Base n m G S (τ.setArr a i v) where
  hn := by simp [h.hn]
  hm := by simp [h.hm]
  hadj := h.hadj.of_eq (by simp [Ne.symm ha])
  hinS := by simpa [Ne.symm hs] using h.hinS
  hlab := by rw [length_arrs_setArr, h.hlab]
  hqlab := by rw [length_arrs_setArr, h.hqlab]
  hE := by rw [length_arrs_setArr, h.hE]
  hLm := by rw [length_arrs_setArr, h.hLm]
  hDp := by rw [length_arrs_setArr, h.hDp]
  hDm := by rw [length_arrs_setArr, h.hDm]
  hRm := by rw [length_arrs_setArr, h.hRm]
  hR1 := by rw [length_arrs_setArr, h.hR1]
  hR3 := by rw [length_arrs_setArr, h.hR3]
  hR5 := by rw [length_arrs_setArr, h.hR5]

theorem Base.matCtx {τ : Env} (h : Base n m G S τ) {t : ℕ} (ht : τ.vars "t" = t) (htm : t < m) :
    MatCtx n t (· ∈ sortedVals (S.getD t ∅)) (gA G) τ :=
  ⟨h.hn, ht, h.hinS t htm, h.hadj.get⟩

/-- The partition into atomic types over chain set `t`. -/
noncomputable def P (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))) (t : ℕ) : Setoid (Fin n) :=
  atomicTypes G ((S.getD t ∅ : Finset (Fin n)) : Set (Fin n))

/-- **Phase 1: the labels of the atomic types.** -/
theorem phaseLab {B t : ℕ} {τ : Env} (hb : Base n m G S τ) (ht : τ.vars "t" = t) (htm : t < m)
    (hB1 : t * n + n < B) (hB2 : n * n < B) (hnB : n + 1 < B) :
    ∃ τ', Run B (classify "lab" eqA) τ τ' (n * (n * (40 * n + 40 + 20) + 17) + 6) ∧
      Base n m G S τ' ∧ τ'.vars "t" = t ∧ LabAt n (repN (P G S t)) τ' := by
  obtain ⟨τ', hr, ⟨hb', ht'⟩, -, hl⟩ := classify_run (B := B) (arr := "lab") (eqc := eqA)
    (fun ρ => Base n m G S ρ ∧ ρ.vars "t" = t) (RAtom n (· ∈ sortedVals (S.getD t ∅)) (gA G))
    hnB (fun ρ h => h.1.hn)
    (fun ρ x h => ⟨h.1.setVar "u" (by decide) (by decide) x, by simp [h.2]⟩)
    (fun ρ x h => ⟨h.1.setVar "v" (by decide) (by decide) x, by simp [h.2]⟩)
    (fun ρ i x h => ⟨h.1.setArr "lab" (by decide) (by decide) i x, by simp [h.2]⟩)
    (fun ρ h hu hv => by
      obtain ⟨ρ', hr', hok⟩ := eqA_run (h.1.matCtx h.2 htm) hu hv hB1 hB2 hnB
      refine ⟨ρ', hr', ⟨h.1.of_run hr' (by decide) (by decide) (by decide) (by decide),
        by rw [hr'.frame_var "t" (by decide), h.2]⟩, hok, hr'.frame_var "u" (by decide),
        hr'.frame_var "v" (by decide), hr'.frame_arr "lab" (by decide)⟩)
    ⟨hb, ht⟩ hb.hlab
  refine ⟨τ', hr, hb', ht', fun v hv => ?_⟩
  rw [hl v hv, leastBelow_eq_repN (P G S t) _ (fun u w hu hw => (atomic_iff G _ ⟨u, hu⟩ ⟨w, hw⟩).symm) hv]

/-- The split of `P` along its least vertices: the partition of the stage. -/
noncomputable def Q (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))) (t : ℕ) : Setoid (Fin n) :=
  split G (P G S t) (minimalVertices (P G S t))

/-- **Phase 2: the labels of the split.** -/
theorem phaseQlab {B t : ℕ} {τ : Env} (hb : Base n m G S τ) (ht : τ.vars "t" = t) (htm : t < m)
    (hl : LabAt n (repN (P G S t)) τ) (hB2 : n * n < B) (hnB : n + 1 < B) :
    ∃ τ', Run B (classify "qlab" eqQ) τ τ' (n * (n * (50 * n + 40 + 20) + 17) + 6) ∧
      Base n m G S τ' ∧ LabAt n (repN (P G S t)) τ' ∧ Vec τ' "qlab" n (repN (Q G S t)) := by
  obtain ⟨τ', hr, ⟨hb', ht', hl'⟩, hlen, hq⟩ := classify_run (B := B) (arr := "qlab") (eqc := eqQ)
    (fun ρ => Base n m G S ρ ∧ ρ.vars "t" = t ∧ LabAt n (repN (P G S t)) ρ)
    (RSplit n (repN (P G S t)) (gA G))
    hnB (fun ρ h => h.1.hn)
    (fun ρ x h => ⟨h.1.setVar "u" (by decide) (by decide) x, by simp [h.2.1], by
      simpa [LabAt] using h.2.2⟩)
    (fun ρ x h => ⟨h.1.setVar "v" (by decide) (by decide) x, by simp [h.2.1], by
      simpa [LabAt] using h.2.2⟩)
    (fun ρ i x h => ⟨h.1.setArr "qlab" (by decide) (by decide) i x, by simp [h.2.1], by
      simpa [LabAt] using h.2.2⟩)
    (fun ρ h hu hv => by
      obtain ⟨ρ', hr', hok⟩ := eqQ_run (h.1.matCtx h.2.1 htm) h.2.2
        (fun z hz => le_of_lt (repN_lt _ hz)) hu hv hB2 hnB
      refine ⟨ρ', hr', ⟨h.1.of_run hr' (by decide) (by decide) (by decide) (by decide),
        by rw [hr'.frame_var "t" (by decide), h.2.1], by
          unfold LabAt; rw [hr'.frame_arr "lab" (by decide)]; exact h.2.2⟩, hok,
        hr'.frame_var "u" (by decide), hr'.frame_var "v" (by decide),
        hr'.frame_arr "qlab" (by decide)⟩)
    ⟨hb, ht, hl⟩ hb.hqlab
  refine ⟨τ', hr, hb', hl', hlen, fun v hv => ?_⟩
  rw [hq v hv, leastBelow_eq_repN (Q G S t) _ (fun u w hu hw => (split_iff' G _ ⟨u, hu⟩ ⟨w, hw⟩).symm) hv]

/-- The entry `adj[a, b]`. -/
def adjE : Expr := .get "adj" (rm "a" "b")

/-- The edges of polarity `pol` at `(a, b)`. -/
def eExpr (pol : Bool) : Expr := .or (if pol then adjE else .sub (.lit 1) adjE) (eqE "a" "b")

theorem evalB_eExpr {B : ℕ} {τ : Env} (hb : Base n m G S τ) (pol : Bool) {i j : ℕ}
    (ha : τ.vars "a" = i) (hbv : τ.vars "b" = j) (hi : i < n) (hj : j < n)
    (hB2 : n * n < B) (hnB : n + 1 < B) :
    (eExpr pol).evalB B τ = some (ind (EPol G pol i j)) := by
  have hadj : adjE.evalB B τ = some (ind (gA G i j)) :=
    hb.hadj.evalB hb.hn ha hbv hi hj hB2 (by omega) (by have := ind_le_one (gA G i j); omega)
  have heq := evalB_eqE (B := B) (σ := τ) (x := "a") (y := "b") (by omega) (by omega) (by omega)
  rw [ha, hbv] at heq
  cases pol
  · have h1 : (Expr.sub (.lit 1) adjE).evalB B τ = some (ind (¬ gA G i j)) := by
      rw [← one_sub_ind]
      exact evalB_bin (evalB_lit (by omega)) hadj (by simp; omega)
    have := evalB_bin (op := .or) h1 heq (by
      simp only [Bop.apply_or, lor_ind]; have := ind_le_one (¬ gA G i j ∨ i = j); omega)
    simp only [eExpr, Bool.false_eq_true, if_false]
    rw [this, Bop.apply_or, lor_ind]
    congr 1
    exact ind_eq_iff.mpr (by simp [EPol]; tauto)
  · have := evalB_bin (op := .or) hadj heq (by
      simp only [Bop.apply_or, lor_ind]; have := ind_le_one (gA G i j ∨ i = j); omega)
    simp only [eExpr, if_true]
    rw [this, Bop.apply_or, lor_ind]
    congr 1
    exact ind_eq_iff.mpr (by simp [EPol]; tauto)

/-- **Phase 3: the edges of one polarity.** `Keep` is whatever the
caller needs to survive the phase. -/
theorem phaseE {B : ℕ} {τ : Env} (pol : Bool) (Keep : Env → Prop)
    (hKa : ∀ ρ x, Keep ρ → Keep (ρ.setVar "a" x)) (hKb : ∀ ρ x, Keep ρ → Keep (ρ.setVar "b" x))
    (hKs : ∀ ρ i x, Keep ρ → Keep (ρ.setArr "E" i x))
    (hb : Base n m G S τ) (hk : Keep τ) (hB : n * n + n + 1 < B) :
    ∃ τ', Run B (matFill "E" (eExpr pol)) τ τ' (n * (n * (30 + 8) + 14) + 6) ∧
      Base n m G S τ' ∧ Keep τ' ∧ Mat τ' "E" n (fun a b => ind (EPol G pol a b)) := by
  obtain ⟨τ', hr, ⟨hb', hk'⟩, hm⟩ := matFill_run (B := B) (K := 30) (arr := "E") (e := eExpr pol)
    (fun ρ => Base n m G S ρ ∧ Keep ρ) (fun a b => ind (EPol G pol a b)) hB
    (fun ρ h => h.1.hn) (fun ρ x h => ⟨h.1.setVar "a" (by decide) (by decide) x, hKa _ _ h.2⟩)
    (fun ρ x h => ⟨h.1.setVar "b" (by decide) (by decide) x, hKb _ _ h.2⟩)
    (fun ρ i x h => ⟨h.1.setArr "E" (by decide) (by decide) i x, hKs _ _ _ h.2⟩)
    (fun ρ i j h ha hbv hi hj => evalB_eExpr h.1 pol ha hbv hi hj (by omega) (by omega))
    (by cases pol <;> simp [eExpr, adjE]) ⟨hb, hk⟩ hb.hE
  exact ⟨τ', hr, hb', hk', hm⟩

theorem Base.bfsCtx {τ : Env} (hb : Base n m G S τ) {L : ℕ → ℕ} {E : ℕ → ℕ → Prop} (D : String)
    (hl : LabAt n L τ) (hE : Mat τ "E" n fun a b => ind (E a b))
    (hD : (τ.arrs D).length = n * n) : BfsCtx n L E D τ :=
  ⟨hb.hn, hl, hE, hb.hR1, hb.hR3, hb.hR5, hb.hLm, hD⟩

/-- The pair relation at `(a, b)` from the matrices `Dp` and `Dm`. -/
def rExpr : Expr :=
  .and (.sub (.lit 1) (eqE "a" "b"))
    (.or (.and (.get "Dp" (rm "a" "b")) (.get "Dm" (rm "a" "b")))
      (.and (.get "Dp" (rm "b" "a")) (.get "Dm" (rm "b" "a"))))

/-- The pair relation of the stage. -/
noncomputable def R (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))) (t : ℕ) :
    SimpleGraph (Fin n) := pairRelation G (P G S t)

theorem evalB_rExpr {B t : ℕ} {τ : Env} (hn : τ.vars "n" = n)
    (hp : Mat τ "Dp" n fun u v => ind (Reach5 n (repN (P G S t)) (EPol G true) u v))
    (hm : Mat τ "Dm" n fun u v => ind (Reach5 n (repN (P G S t)) (EPol G false) u v))
    {i j : ℕ} (ha : τ.vars "a" = i) (hbv : τ.vars "b" = j) (hi : i < n) (hj : j < n)
    (hB2 : n * n < B) (hnB : n + 1 < B) :
    rExpr.evalB B τ = some (ind (gA (R G S t) i j)) := by
  set L := repN (P G S t)
  have hle : ∀ p : Prop, ind p < B := fun p => by have := ind_le_one p; omega
  have hpij := hp.evalB (B := B) hn ha hbv hi hj hB2 (by omega) (hle _)
  have hmij := hm.evalB (B := B) hn ha hbv hi hj hB2 (by omega) (hle _)
  have hpji := hp.evalB (B := B) hn hbv ha hj hi hB2 (by omega) (hle _)
  have hmji := hm.evalB (B := B) hn hbv ha hj hi hB2 (by omega) (hle _)
  have heq := evalB_eqE (B := B) (σ := τ) (x := "a") (y := "b") (by omega) (by omega) (by omega)
  rw [ha, hbv] at heq
  have hne : (Expr.sub (.lit 1) (eqE "a" "b")).evalB B τ = some (ind (¬ i = j)) := by
    rw [← one_sub_ind]; exact evalB_bin (evalB_lit (by omega)) heq (by simp; omega)
  have h1 := evalB_bin (op := .and) hpij hmij (by simp only [Bop.apply_and, land_ind]; exact hle _)
  have h2 := evalB_bin (op := .and) hpji hmji (by simp only [Bop.apply_and, land_ind]; exact hle _)
  simp only [Bop.apply_and, land_ind] at h1 h2
  have h3 := evalB_bin (op := .or) h1 h2 (by simp only [Bop.apply_or, lor_ind]; exact hle _)
  simp only [Bop.apply_or, lor_ind] at h3
  have h4 := evalB_bin (op := .and) hne h3 (by simp only [Bop.apply_and, land_ind]; exact hle _)
  simp only [Bop.apply_and, land_ind] at h4
  simp only [rExpr]
  rw [h4]
  congr 1
  refine ind_eq_iff.mpr ?_
  rw [show gA (R G S t) i j ↔ (R G S t).Adj ⟨i, hi⟩ ⟨j, hj⟩ from
    ⟨fun ⟨_, _, h⟩ => h, fun h => ⟨hi, hj, h⟩⟩, R, pairRelation_iff]
  simp only [ne_eq, Fin.mk.injEq]
  rfl

/-- One stage: the chain set `t = m - 1 - s`, then the phases. -/
def stageC : Com :=
  .seq (.assign "t" (.sub (.sub (.var "m") (.lit 1)) (.var "s")))
  (.seq (classify "lab" eqA)
  (.seq (classify "qlab" eqQ)
  (.seq (matFill "E" (eExpr true))
  (.seq (bfs "Dp")
  (.seq (matFill "E" (eExpr false))
  (.seq (bfs "Dm")
  (.seq writeParts
  (.seq (matFill "Rm" rExpr) writeGraph))))))))

theorem vec_of_arr {τ τ' : Env} {a : String} {f : ℕ → ℕ} (h : Vec τ a n f)
    (he : τ'.arrs a = τ.arrs a) : Vec τ' a n f := h.of_eq he

theorem labAt_of_arr {τ τ' : Env} {L : ℕ → ℕ} (h : LabAt n L τ)
    (he : τ'.arrs "lab" = τ.arrs "lab") : LabAt n L τ' := by
  unfold LabAt; rw [he]; exact h

/-- **One stage.** It writes the words of the partition and of the pair
relation of chain set `m - 1 - s`. -/
theorem stage_run {B s : ℕ} {τ : Env} (hb : Base n m G S τ) (hs : τ.vars "s" = s) (hsm : s < m)
    (hB : m * n + n * n + 2 * n + 3 < B) (hmB : m < B) :
    ∃ τ', Run B stageC τ τ' (2000 * (n + 1) ^ 3) ∧ Base n m G S τ' ∧ τ'.vars "s" = s ∧
      τ'.out = τ.out ++ (toWord (Q G S (m - 1 - s)) ++ toWord (R G S (m - 1 - s))) := by
  set t := m - 1 - s with ht
  have htm : t < m := by omega
  have hnn : n ≤ n * n := Nat.le_mul_self n
  have htn : t * n + n ≤ m * n := by
    have := Nat.mul_le_mul_right n (show t + 1 ≤ m by omega); rw [Nat.add_mul] at this; omega
  -- phase 0
  set τ0 := τ.setVar "t" t with hτ0
  have hr0 : Run B (.assign "t" (.sub (.sub (.var "m") (.lit 1)) (.var "s"))) τ τ0 6 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff, Bop.apply_sub, hb.hm, hs]
    exact ⟨m - 1, s, ⟨m, 1, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩, ⟨rfl, by omega⟩, rfl,
      by omega⟩
  have hb0 : Base n m G S τ0 := hb.setVar "t" (by decide) (by decide) t
  -- phase 1
  obtain ⟨τ1, hr1, hb1, ht1, hl1⟩ := phaseLab (B := B) hb0 (by simp [hτ0]) htm (by omega)
    (by omega) (by omega)
  -- phase 2
  obtain ⟨τ2, hr2, hb2, hl2, hq2⟩ := phaseQlab (B := B) hb1 ht1 htm hl1 (by omega) (by omega)
  -- phase 3
  obtain ⟨τ3, hr3, hb3, ⟨hl3, hq3⟩, hE3⟩ := phaseE (B := B) true
    (fun ρ => LabAt n (repN (P G S t)) ρ ∧ Vec ρ "qlab" n (repN (Q G S t)))
    (fun ρ x h => ⟨by simpa [LabAt] using h.1, h.2.of_eq (by simp)⟩)
    (fun ρ x h => ⟨by simpa [LabAt] using h.1, h.2.of_eq (by simp)⟩)
    (fun ρ i x h => ⟨by simpa [LabAt] using h.1, h.2.of_eq (by simp)⟩) hb2 ⟨hl2, hq2⟩ (by omega)
  -- phase 4
  obtain ⟨τ4, hr4, -, hDp4⟩ := bfs_run (B := B) (D := "Dp") (by decide)
    (hb3.bfsCtx "Dp" hl3 hE3 hb3.hDp) (fun z hz => repN_lt _ hz) (by omega)
  have hb4 := hb3.of_run hr4 (by decide) (by decide) (by decide) (by decide)
  have hl4 := labAt_of_arr hl3 (hr4.frame_arr "lab" (by decide))
  have hq4 := vec_of_arr hq3 (hr4.frame_arr "qlab" (by decide))
  -- phase 5
  obtain ⟨τ5, hr5, hb5, ⟨hl5, hq5, hDp5⟩, hE5⟩ := phaseE (B := B) false
    (fun ρ => LabAt n (repN (P G S t)) ρ ∧ Vec ρ "qlab" n (repN (Q G S t)) ∧
      Mat ρ "Dp" n fun u v => ind (Reach5 n (repN (P G S t)) (EPol G true) u v))
    (fun ρ x h => ⟨by simpa [LabAt] using h.1, h.2.1.of_eq (by simp), h.2.2.of_eq (by simp)⟩)
    (fun ρ x h => ⟨by simpa [LabAt] using h.1, h.2.1.of_eq (by simp), h.2.2.of_eq (by simp)⟩)
    (fun ρ i x h => ⟨by simpa [LabAt] using h.1, h.2.1.of_eq (by simp), h.2.2.of_eq (by simp)⟩)
    hb4 ⟨hl4, hq4, hDp4⟩ (by omega)
  -- phase 6
  obtain ⟨τ6, hr6, -, hDm6⟩ := bfs_run (B := B) (D := "Dm") (by decide)
    (hb5.bfsCtx "Dm" hl5 hE5 hb5.hDm) (fun z hz => repN_lt _ hz) (by omega)
  have hb6 := hb5.of_run hr6 (by decide) (by decide) (by decide) (by decide)
  have hq6 := vec_of_arr hq5 (hr6.frame_arr "qlab" (by decide))
  have hDp6 : Mat τ6 "Dp" n _ := hDp5.of_eq (hr6.frame_arr "Dp" (by decide))
  -- phase 7
  obtain ⟨τ7, hr7, -, ho7⟩ := writeParts_run (B := B) (q := repN (Q G S t)) ⟨hb6.hn, hq6⟩
    (fun z hz => repN_lt _ hz) (by omega)
  have hb7 := hb6.of_run hr7 (by decide) (by decide) (by decide) (by decide)
  have hDp7 : Mat τ7 "Dp" n _ := hDp6.of_eq (hr7.frame_arr "Dp" (by decide))
  have hDm7 : Mat τ7 "Dm" n _ := hDm6.of_eq (hr7.frame_arr "Dm" (by decide))
  -- phase 8
  obtain ⟨τ8, hr8, ⟨hb8, -, -⟩, hRm8⟩ := matFill_run (B := B) (K := 60) (arr := "Rm") (e := rExpr)
    (fun ρ => Base n m G S ρ ∧
      (Mat ρ "Dp" n fun u v => ind (Reach5 n (repN (P G S t)) (EPol G true) u v)) ∧
      (Mat ρ "Dm" n fun u v => ind (Reach5 n (repN (P G S t)) (EPol G false) u v)))
    (fun a b => ind (gA (R G S t) a b)) (by omega) (fun ρ h => h.1.hn)
    (fun ρ x h => ⟨h.1.setVar "a" (by decide) (by decide) x, h.2.1.of_eq (by simp),
      h.2.2.of_eq (by simp)⟩)
    (fun ρ x h => ⟨h.1.setVar "b" (by decide) (by decide) x, h.2.1.of_eq (by simp),
      h.2.2.of_eq (by simp)⟩)
    (fun ρ i x h => ⟨h.1.setArr "Rm" (by decide) (by decide) i x, h.2.1.of_eq (by simp),
      h.2.2.of_eq (by simp)⟩)
    (fun ρ i j h ha hbv hi hj => evalB_rExpr h.1.hn h.2.1 h.2.2 ha hbv hi hj (by omega) (by omega))
    (by simp [rExpr]) ⟨hb7, hDp7, hDm7⟩ hb7.hRm
  -- phase 9
  obtain ⟨τ9, hr9, -, ho9⟩ := writeGraph_run (B := B) (N := gA (R G S t)) ⟨hb8.hn, hRm8⟩ (by omega)
  have hb9 := hb8.of_run hr9 (by decide) (by decide) (by decide) (by decide)
  refine ⟨τ9, (Run.seq hr0 (Run.seq hr1 (Run.seq hr2 (Run.seq hr3 (Run.seq hr4 (Run.seq hr5
    (Run.seq hr6 (Run.seq hr7 (Run.seq hr8 hr9))))))))).mono ?_, hb9, ?_, ?_⟩
  · ring_nf
    nlinarith [Nat.zero_le n, Nat.zero_le (n * n), Nat.zero_le (n * n * n)]
  · rw [hr9.frame_var "s" (by decide), hr8.frame_var "s" (by decide), hr7.frame_var "s" (by decide),
      hr6.frame_var "s" (by decide), hr5.frame_var "s" (by decide), hr4.frame_var "s" (by decide),
      hr3.frame_var "s" (by decide), hr2.frame_var "s" (by decide), hr1.frame_var "s" (by decide)]
    simp [hτ0, hs]
  · rw [ho9, hr8.out_eq (by decide), ho7, hr6.out_eq (by decide), hr5.out_eq (by decide),
      hr4.out_eq (by decide), hr3.out_eq (by decide), hr2.out_eq (by decide),
      hr1.out_eq (by decide), toWord_setoid, toWord_graph]
    simp [hτ0]

end Base

end Lax185574Proofs.Conversions.Ram
