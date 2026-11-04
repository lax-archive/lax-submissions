import Lax185574Proofs.ResolveRam.Glue.PH1
import Lax185574Proofs.ResolveRam.Glue.DistRd
import Lax185574Proofs.ResolveRam.Glue.PCT4

/-!
Writing the distance matrix of the resolved graph in a tape program.

From the codes `dp[u]` and `dq[u]` of the distances from `u` to the
classes of `P` and `Q` (`dtLoop`), the flags `hp`, `hq` that tell whether
these classes have a vertex (`flgLoop`), and the matrix of `G` in `dd`,
`dhW` writes the word of the matrix whose entry `(u, w)` is `dhCode`, the
code of the distance of eq:resolve-dist (`dhW_run`). By
`distMatrix_resolveBy` this is the word of the distance matrix of the
resolved graph (`dhWord_eq`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.MC Lax185574Proofs.MC.Glue
open Lax185574Proofs.Words Lax185574.PartialGraphs Lax185574.WordEncoding Lax185574.ResolveLift
open Lax185574.DistanceMatrix Lax185574Proofs.DistMatrix

/-! ### The code of a sum as an expression -/

/-- `0` for `0` and `1` otherwise. -/
def sgnX (e : Expr) : Expr := .sub e (.sub e (.lit 1))

/-- The expression of `cadd a c b`, for `c ≥ 1`. -/
def caddX (e f : Expr) (c : ℕ) : Expr := .mul (.mul (sgnX e) (sgnX f)) (.add (.add e f) (.lit (c - 1)))

theorem sgnX_evalB {B a : ℕ} {e : Expr} {σ : Env} (he : e.evalB B σ = some a) (hB : 1 < B) :
    (sgnX e).evalB B σ = some (if a = 0 then 0 else 1) := by
  have ha := Expr.lt_of_evalB he
  have := ev_sub he (ev_sub he (evalB_lit (n := 1) hB) (by omega)) (by omega)
  unfold sgnX; rw [this]; congr 1; split_ifs <;> omega

theorem caddX_evalB {B a b c : ℕ} {e f : Expr} {σ : Env} (he : e.evalB B σ = some a)
    (hf : f.evalB B σ = some b) (hc : 1 ≤ c) (hB : a + b + c < B) :
    (caddX e f c).evalB B σ = some (cadd a c b) := by
  have h1 := ev_mul (sgnX_evalB he (by omega)) (sgnX_evalB hf (by omega))
    (show (if a = 0 then 0 else 1) * (if b = 0 then 0 else 1) < B by split_ifs <;> omega)
  have h2 := ev_add (ev_add he hf (by omega)) (evalB_lit (n := c - 1) (by omega)) (by omega)
  have := ev_mul h1 h2 (show (if a = 0 then 0 else 1) * (if b = 0 then 0 else 1) * (a + b + (c - 1)) < B by
    split_ifs <;> simp <;> omega)
  rw [show caddX e f c = .mul (.mul (sgnX e) (sgnX f)) (.add (.add e f) (.lit (c - 1))) from rfl, this]
  congr 1
  unfold cadd
  split_ifs <;> simp_all <;> omega

/-! ### One entry -/

/-- The code of the entry `(u, w)` of the matrix of the resolved graph. -/
def dhCode (dd : ℕ → ℕ → ℕ) (tp tq : ℕ → ℕ) (hp hq u w : ℕ) : ℕ :=
  cmin (dd u w) (cmin (cadd (tp u) 1 (tq w)) (cmin (cadd (tq u) 1 (tp w))
    (cmin (cadd (tp u) 2 (tp w) * hq) (cadd (tq u) 2 (tq w) * hp))))

/-- The scalars that the entry writes. -/
def dhVs : List String := ["ca", "cb", "cr", "h1", "h2", "h3", "h4"]

/-- `cr := cmin a b`. -/
def cminE (a b : Expr) : Com := .seq (.assign "ca" a) (.seq (.assign "cb" b) cminC)

/-- **The entry `(du, dw)` into `cr`.** -/
def dhEnt : Com :=
  .seq (.assign "h1" (caddX (.get "dp" (.var "du")) (.get "dq" (.var "dw")) 1))
  (.seq (.assign "h2" (caddX (.get "dq" (.var "du")) (.get "dp" (.var "dw")) 1))
  (.seq (.assign "h3" (.mul (caddX (.get "dp" (.var "du")) (.get "dp" (.var "dw")) 2) (.var "hq")))
  (.seq (.assign "h4" (.mul (caddX (.get "dq" (.var "du")) (.get "dq" (.var "dw")) 2) (.var "hp")))
  (.seq (cminE (.var "h3") (.var "h4")) (.seq (cminE (.var "h2") (.var "cr"))
  (.seq (cminE (.var "h1") (.var "cr")) (cminE (.get "dd" ddE) (.var "cr"))))))))

/-- The data that the entries read. -/
structure DhCtx (n : ℕ) (tp tq : ℕ → ℕ) (hp hq : ℕ) (D : List ℕ) (τ : Env) : Prop where
  vn : τ.vars "n" = n
  vp : τ.vars "hp" = hp
  vq : τ.vars "hq" = hq
  adp : τ.arrs "dp" = arrOf n tp
  adq : τ.arrs "dq" = arrOf n tq
  add : τ.arrs "dd" = D

theorem DhCtx.setVar {n hp hq : ℕ} {tp tq : ℕ → ℕ} {D : List ℕ} {τ : Env}
    (h : DhCtx n tp tq hp hq D τ) {y : String} (hy : y ∈ dhVs ++ ["du", "dw"]) (v : ℕ) :
    DhCtx n tp tq hp hq D (τ.setVar y v) := by
  have h1 : y ≠ "n" := by intro e; subst e; simp [dhVs] at hy
  have h2 : y ≠ "hp" := by intro e; subst e; simp [dhVs] at hy
  have h3 : y ≠ "hq" := by intro e; subst e; simp [dhVs] at hy
  exact ⟨by simp [Ne.symm h1, h.vn], by simp [Ne.symm h2, h.vp], by simp [Ne.symm h3, h.vq],
    by simp [h.adp], by simp [h.adq], by simp [h.add]⟩

theorem cminE_run {B a b : ℕ} {ea eb : Expr} {τ : Env} (ha : ea.evalB B τ = some a)
    (hb : ∀ ρ : Env, ρ.vars "cr" = τ.vars "cr" → (∀ y, y ≠ "ca" → ρ.vars y = τ.vars y) →
      ρ.arrs = τ.arrs → eb.evalB B ρ = some b) :
    Run B (cminE ea eb) τ (((τ.setVar "ca" a).setVar "cb" b).setVar "cr" (cmin a b))
      (2 + ea.size + eb.size + 20) := by
  have haB := Expr.lt_of_evalB ha
  have r1 : Run B (.assign "ca" ea) τ (τ.setVar "ca" a) (1 + ea.size) := Run.assign ha
  have hb' := hb (τ.setVar "ca" a) (by simp) (fun y hy => by simp [hy]) (by simp)
  have hbB := Expr.lt_of_evalB hb'
  have r2 : Run B (.assign "cb" eb) (τ.setVar "ca" a) ((τ.setVar "ca" a).setVar "cb" b) (1 + eb.size) :=
    Run.assign hb'
  have r3 := cminC_run (B := B) (τ := (τ.setVar "ca" a).setVar "cb" b) (a := a) (b := b) (by simp)
    (by simp) haB hbB
  exact (Run.seq r1 (Run.seq r2 r3)).mono (by omega)

theorem dhEnt_run {B n hp hq u w : ℕ} {tp tq : ℕ → ℕ} {D : List ℕ} {f : ℕ → ℕ → ℕ} {τ : Env}
    (hC : DhCtx n tp tq hp hq D τ) (hD : ∀ u < n, ∀ x < n, D[2 + u * (n + 1) + x]? = some (f u x))
    (hfB : ∀ u < n, ∀ x < n, f u x ≤ n) (htp : ∀ v < n, tp v ≤ n) (htq : ∀ v < n, tq v ≤ n)
    (hp1 : hp ≤ 1) (hq1 : hq ≤ 1) (hDB : D.length < B) (hnB : 3 * n + 3 < B)
    (hu : τ.vars "du" = u) (hw : τ.vars "dw" = w) (hun : u < n) (hwn : w < n) :
    ∃ τ', Run B dhEnt τ τ' 400 ∧ DhCtx n tp tq hp hq D τ' ∧ τ'.vars "du" = u ∧ τ'.vars "dw" = w ∧
      τ'.vars "cr" = dhCode f tp tq hp hq u w ∧ τ'.arrs = τ.arrs ∧
      (∀ y, y ∉ dhVs → τ'.vars y = τ.vars y) := by
  -- the values
  have gp : ∀ ρ : Env, ρ.arrs = τ.arrs → ∀ (x : String) (v : ℕ), ρ.vars x = v → v < n →
      (Expr.get "dp" (.var x)).evalB B ρ = some (tp v) := fun ρ ha x v hx hv =>
    evalB_get (ev_var hx (by omega)) (by rw [ha, hC.adp, getElem?_arrOf _ hv]) (by have := htp v hv; omega)
  have gq : ∀ ρ : Env, ρ.arrs = τ.arrs → ∀ (x : String) (v : ℕ), ρ.vars x = v → v < n →
      (Expr.get "dq" (.var x)).evalB B ρ = some (tq v) := fun ρ ha x v hx hv =>
    evalB_get (ev_var hx (by omega)) (by rw [ha, hC.adq, getElem?_arrOf _ hv]) (by have := htq v hv; omega)
  have tpu := htp u hun
  have tpw := htp w hwn
  have tqu := htq u hun
  have tqw := htq w hwn
  have cl : ∀ a b c, a ≤ n → b ≤ n → cadd a c b ≤ a + b + c := fun a b c _ _ => by
    unfold cadd; split_ifs <;> omega
  -- h1 .. h4
  set v1 := cadd (tp u) 1 (tq w)
  set v2 := cadd (tq u) 1 (tp w)
  set v3 := cadd (tp u) 2 (tp w) * hq
  set v4 := cadd (tq u) 2 (tq w) * hp
  set τ1 := τ.setVar "h1" v1
  have r1 : Run B (.assign "h1" (caddX (.get "dp" (.var "du")) (.get "dq" (.var "dw")) 1)) τ τ1
      (1 + (caddX (.get "dp" (.var "du")) (.get "dq" (.var "dw")) 1).size) :=
    Run.assign (caddX_evalB (gp τ rfl _ _ hu hun) (gq τ rfl _ _ hw hwn) le_rfl (by omega))
  set τ2 := τ1.setVar "h2" v2
  have r2 : Run B (.assign "h2" (caddX (.get "dq" (.var "du")) (.get "dp" (.var "dw")) 1)) τ1 τ2
      (1 + (caddX (.get "dq" (.var "du")) (.get "dp" (.var "dw")) 1).size) :=
    Run.assign (caddX_evalB (gq τ1 (by simp [τ1]) _ _ (by simp [τ1, hu]) hun)
      (gp τ1 (by simp [τ1]) _ _ (by simp [τ1, hw]) hwn) le_rfl (by omega))
  set τ3 := τ2.setVar "h3" v3
  have r3 : Run B (.assign "h3" (.mul (caddX (.get "dp" (.var "du")) (.get "dp" (.var "dw")) 2) (.var "hq")))
      τ2 τ3 (1 + (Expr.mul (caddX (.get "dp" (.var "du")) (.get "dp" (.var "dw")) 2) (.var "hq")).size) := by
    have hc := cl (tp u) (tp w) 2 tpu tpw
    refine Run.assign (ev_mul (caddX_evalB (gp τ2 (by simp [τ2, τ1]) _ _ (by simp [τ2, τ1, hu]) hun)
      (gp τ2 (by simp [τ2, τ1]) _ _ (by simp [τ2, τ1, hw]) hwn) (by omega) (by omega))
      (ev_var (by simp [τ2, τ1, hC.vq]) (by omega)) ?_)
    have : cadd (tp u) 2 (tp w) * hq ≤ cadd (tp u) 2 (tp w) := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hq1 with h | h <;> simp [h]
    omega
  set τ4 := τ3.setVar "h4" v4
  have r4 : Run B (.assign "h4" (.mul (caddX (.get "dq" (.var "du")) (.get "dq" (.var "dw")) 2) (.var "hp")))
      τ3 τ4 (1 + (Expr.mul (caddX (.get "dq" (.var "du")) (.get "dq" (.var "dw")) 2) (.var "hp")).size) := by
    have hc := cl (tq u) (tq w) 2 tqu tqw
    refine Run.assign (ev_mul (caddX_evalB (gq τ3 (by simp [τ3, τ2, τ1]) _ _ (by simp [τ3, τ2, τ1, hu]) hun)
      (gq τ3 (by simp [τ3, τ2, τ1]) _ _ (by simp [τ3, τ2, τ1, hw]) hwn) (by omega) (by omega))
      (ev_var (by simp [τ3, τ2, τ1, hC.vp]) (by omega)) ?_)
    have : cadd (tq u) 2 (tq w) * hp ≤ cadd (tq u) 2 (tq w) := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hp1 with h | h <;> simp [h]
    omega
  have b1 : v1 ≤ 2 * n + 1 := by have := cl (tp u) (tq w) 1 tpu tqw; omega
  have b2 : v2 ≤ 2 * n + 1 := by have := cl (tq u) (tp w) 1 tqu tpw; omega
  have b3 : v3 ≤ 2 * n + 2 := by
    have := cl (tp u) (tp w) 2 tpu tpw
    have : v3 ≤ cadd (tp u) 2 (tp w) := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hq1 with h | h <;> simp [v3, h]
    omega
  have b4 : v4 ≤ 2 * n + 2 := by
    have := cl (tq u) (tq w) 2 tqu tqw
    have : v4 ≤ cadd (tq u) 2 (tq w) := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hp1 with h | h <;> simp [v4, h]
    omega
  have cmB : ∀ a b, cmin a b ≤ max a b := cmin_le_max
  -- the minima
  set m1 := cmin v3 v4
  have r5 := cminE_run (B := B) (a := v3) (b := v4) (ea := .var "h3") (eb := .var "h4") (τ := τ4)
    (ev_var (by simp [τ4, τ3]) (by omega))
    (fun ρ _ hv _ => ev_var (by rw [hv _ (by decide)]; simp [τ4]) (by omega))
  set τ5 := ((τ4.setVar "ca" v3).setVar "cb" v4).setVar "cr" m1
  have bm1 : m1 ≤ 2 * n + 2 := le_trans (cmB _ _) (max_le b3 b4)
  set m2 := cmin v2 m1
  have r6 := cminE_run (B := B) (a := v2) (b := m1) (ea := .var "h2") (eb := .var "cr") (τ := τ5)
    (ev_var (by simp [τ5, τ4, τ3, τ2]) (by omega)) (fun ρ hcr _ _ => ev_var (by rw [hcr]; simp [τ5]) (by omega))
  set τ6 := ((τ5.setVar "ca" v2).setVar "cb" m1).setVar "cr" m2
  have bm2 : m2 ≤ 2 * n + 2 := le_trans (cmB _ _) (max_le (by omega) bm1)
  set m3 := cmin v1 m2
  have r7 := cminE_run (B := B) (a := v1) (b := m2) (ea := .var "h1") (eb := .var "cr") (τ := τ6)
    (ev_var (by simp [τ6, τ5, τ4, τ3, τ2, τ1]) (by omega))
    (fun ρ hcr _ _ => ev_var (by rw [hcr]; simp [τ6]) (by omega))
  set τ7 := ((τ6.setVar "ca" v1).setVar "cb" m2).setVar "cr" m3
  have bm3 : m3 ≤ 2 * n + 2 := le_trans (cmB _ _) (max_le (by omega) bm2)
  have hτ7 : ∀ y, y ∉ dhVs → τ7.vars y = τ.vars y := fun y hy => by
    simp only [dhVs, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    simp [τ7, τ6, τ5, τ4, τ3, τ2, τ1, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2.1,
      hy.2.2.2.2.2.2]
  have ha7 : τ7.arrs = τ.arrs := by simp [τ7, τ6, τ5, τ4, τ3, τ2, τ1]
  have hpos := hD u hun w hwn
  have hlt : 2 + u * (n + 1) + w < D.length := by
    by_contra h; rw [List.getElem?_eq_none (by omega)] at hpos; exact absurd hpos (by simp)
  have hfuw := hfB u hun w hwn
  set m4 := cmin (f u w) m3
  have r8 := cminE_run (B := B) (a := f u w) (b := m3) (ea := .get "dd" ddE) (eb := .var "cr") (τ := τ7)
    (evalB_get (ddE_evalB (by rw [hτ7 _ (by decide), hC.vn]) (by rw [hτ7 _ (by decide), hu])
      (by rw [hτ7 _ (by decide), hw]) (by omega) (by omega)) (by rw [ha7, hC.add]; exact hpos) (by omega))
    (fun ρ hcr _ _ => ev_var (by rw [hcr]; simp [τ7]) (by omega))
  set τ8 := ((τ7.setVar "ca" (f u w)).setVar "cb" m3).setVar "cr" m4
  have hτ8 : ∀ y, y ∉ dhVs → τ8.vars y = τ.vars y := fun y hy => by
    have h1 : y ≠ "ca" := by intro e; subst e; simp [dhVs] at hy
    have h2 : y ≠ "cb" := by intro e; subst e; simp [dhVs] at hy
    have h3 : y ≠ "cr" := by intro e; subst e; simp [dhVs] at hy
    simp only [τ8, vars_setVar, if_neg h1, if_neg h2, if_neg h3]
    exact hτ7 y hy
  have ha8 : τ8.arrs = τ.arrs := by simp [τ8, ha7]
  refine ⟨τ8, ?_, ⟨by rw [hτ8 _ (by decide), hC.vn], by rw [hτ8 _ (by decide), hC.vp],
      by rw [hτ8 _ (by decide), hC.vq], by rw [ha8, hC.adp], by rw [ha8, hC.adq], by rw [ha8, hC.add]⟩,
    by rw [hτ8 _ (by decide), hu], by rw [hτ8 _ (by decide), hw], by simp [τ8, m4, m3, m2, m1, v1, v2, v3, v4, dhCode],
    ha8, hτ8⟩
  unfold dhEnt
  exact (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7 r8))))))).mono
    (by simp [Expr.size, caddX, sgnX, ddE])

/-! ### The matrix -/

/-- The entries of one row. -/
def dhRow : Com := .seq (.write (.var "n")) (forUp "dw" (.var "n") (.seq dhEnt (.write (.var "cr"))))

/-- **The word of the matrix of the resolved graph.** -/
def dhW : Com := .seq (.write (.var "n")) (forUp "du" (.var "n") dhRow)

/-- The word that `dhW` writes, for entries `F`. -/
def dhWord (n : ℕ) (F : ℕ → ℕ → ℕ) : List ℕ :=
  n :: (List.range n).flatMap fun u => n :: (List.range n).map (F u)

theorem dhRow_run {B n hp hq u : ℕ} {tp tq : ℕ → ℕ} {D : List ℕ} {f : ℕ → ℕ → ℕ} {τ : Env}
    (hC : DhCtx n tp tq hp hq D τ) (hD : ∀ u < n, ∀ x < n, D[2 + u * (n + 1) + x]? = some (f u x))
    (hfB : ∀ u < n, ∀ x < n, f u x ≤ n) (htp : ∀ v < n, tp v ≤ n) (htq : ∀ v < n, tq v ≤ n)
    (hp1 : hp ≤ 1) (hq1 : hq ≤ 1) (hDB : D.length < B) (hnB : 3 * n + 3 < B)
    (hu : τ.vars "du" = u) (hun : u < n) :
    ∃ τ', Run B dhRow τ τ' (n * 410 + 8) ∧ DhCtx n tp tq hp hq D τ' ∧ τ'.vars "du" = u ∧
      τ'.out = τ.out ++ (n :: (List.range n).map (dhCode f tp tq hp hq u)) ∧ τ'.arrs = τ.arrs := by
  set τ0 : Env := { τ with out := τ.out ++ [n] }
  have r0 : Run B (.write (.var "n")) τ τ0 2 := (Run.write (ev_var hC.vn (by omega))).mono (by simp)
  have hC0 : DhCtx n tp tq hp hq D τ0 := ⟨hC.vn, hC.vp, hC.vq, hC.adp, hC.adq, hC.add⟩
  let I : ℕ → Env → Prop := fun j ρ => DhCtx n tp tq hp hq D ρ ∧ ρ.vars "du" = u ∧
    ρ.out = τ.out ++ (n :: (List.range j).map (dhCode f tp tq hp hq u)) ∧ ρ.arrs = τ.arrs
  obtain ⟨τ', r1, ⟨hC', hu', ho', ha'⟩, -⟩ := forUp_run (B := B) (i := "dw") (e := .var "n")
    (body := .seq dhEnt (.write (.var "cr"))) (N := n) (K := 402) I (σ := τ0) (by omega)
    (fun k _ ρ hI _ => by rw [evalB_var_iff, hI.1.vn]; omega)
    ⟨hC0.setVar (by simp) 0, by simp [τ0, hu], by simp [τ0], by simp [τ0]⟩
    (by
      rintro j hj ρ ⟨hCρ, huρ, hoρ, haρ⟩ hwj
      obtain ⟨ρ1, r1, hC1, hu1, hw1, hcr, ha1, -⟩ := dhEnt_run hCρ hD hfB htp htq hp1 hq1 hDB hnB huρ hwj
        hun hj
      have hval : dhCode f tp tq hp hq u j < B := by
        have := hfB u hun j hj
        have : dhCode f tp tq hp hq u j ≤ max (f u j) (2 * n + 2) := by
          unfold dhCode
          refine le_trans (cmin_le_max _ _) (max_le_max le_rfl ?_)
          refine le_trans (cmin_le_max _ _) (max_le ?_ ?_)
          · unfold cadd; split_ifs <;> have := htp u hun <;> have := htq j hj <;> omega
          refine le_trans (cmin_le_max _ _) (max_le ?_ ?_)
          · unfold cadd; split_ifs <;> have := htq u hun <;> have := htp j hj <;> omega
          refine le_trans (cmin_le_max _ _) (max_le ?_ ?_)
          · have : cadd (tp u) 2 (tp j) ≤ 2 * n + 2 := by
              unfold cadd; split_ifs <;> have := htp u hun <;> have := htp j hj <;> omega
            rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hq1 with h | h <;> simp [h] <;> omega
          · have : cadd (tq u) 2 (tq j) ≤ 2 * n + 2 := by
              unfold cadd; split_ifs <;> have := htq u hun <;> have := htq j hj <;> omega
            rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hp1 with h | h <;> simp [h] <;> omega
        omega
      have r2 : Run B (.write (.var "cr")) ρ1 { ρ1 with out := ρ1.out ++ [dhCode f tp tq hp hq u j] } 2 :=
        (Run.write (ev_var hcr hval)).mono (by simp)
      have ho1 : ρ1.out = ρ.out := r1.out_eq (by simp [dhEnt, cminE, cminC, Com.NoWrite])
      refine ⟨_, (Run.seq r1 r2).mono (by omega), hw1, (show DhCtx n tp tq hp hq D
          { ρ1 with out := ρ1.out ++ [dhCode f tp tq hp hq u j] } from
            ⟨hC1.vn, hC1.vp, hC1.vq, hC1.adp, hC1.adq, hC1.add⟩).setVar (by simp) _,
        by simp [hu1], ?_, by simp [ha1, haρ]⟩
      simp only [out_setVar, ho1, hoρ, List.range_succ, List.map_append, List.map_cons, List.map_nil]
      simp)
  refine ⟨τ', (Run.seq r0 r1).mono (by simp only [Expr.size]; omega), hC', hu', ho', ?_⟩
  rw [ha']

theorem dhW_run {B n hp hq : ℕ} {tp tq : ℕ → ℕ} {D : List ℕ} {f : ℕ → ℕ → ℕ} {σ : Env}
    (hC : DhCtx n tp tq hp hq D σ) (hD : ∀ u < n, ∀ x < n, D[2 + u * (n + 1) + x]? = some (f u x))
    (hfB : ∀ u < n, ∀ x < n, f u x ≤ n) (htp : ∀ v < n, tp v ≤ n) (htq : ∀ v < n, tq v ≤ n)
    (hp1 : hp ≤ 1) (hq1 : hq ≤ 1) (hDB : D.length < B) (hnB : 3 * n + 3 < B) :
    ∃ σ', Run B dhW σ σ' (n * (n * 410 + 16) + 8) ∧
      σ'.out = σ.out ++ dhWord n (dhCode f tp tq hp hq) ∧ σ'.arrs = σ.arrs := by
  set σ0 : Env := { σ with out := σ.out ++ [n] }
  have r0 : Run B (.write (.var "n")) σ σ0 2 := (Run.write (ev_var hC.vn (by omega))).mono (by simp)
  have hC0 : DhCtx n tp tq hp hq D σ0 := ⟨hC.vn, hC.vp, hC.vq, hC.adp, hC.adq, hC.add⟩
  let I : ℕ → Env → Prop := fun k ρ => DhCtx n tp tq hp hq D ρ ∧
    ρ.out = σ.out ++ (n :: (List.range k).flatMap fun u => n :: (List.range n).map (dhCode f tp tq hp hq u)) ∧
    ρ.arrs = σ.arrs
  obtain ⟨σ', r1, ⟨-, ho', ha'⟩, -⟩ := forUp_run (B := B) (i := "du") (e := .var "n")
    (body := dhRow) (N := n) (K := n * 410 + 8) I (σ := σ0) (by omega)
    (fun k _ ρ hI _ => by rw [evalB_var_iff, hI.1.vn]; omega)
    ⟨hC0.setVar (by simp) 0, by simp [σ0], by simp [σ0]⟩
    (by
      rintro k hk ρ ⟨hCρ, hoρ, haρ⟩ huk
      obtain ⟨ρ1, r, hC1, hu1, ho1, ha1⟩ := dhRow_run hCρ hD hfB htp htq hp1 hq1 hDB hnB huk hk
      refine ⟨ρ1, r, hu1, hC1.setVar (by simp) _, ?_, by simp [ha1, haρ]⟩
      simp only [out_setVar, ho1, hoρ, List.range_succ, List.flatMap_append, List.flatMap_cons,
        List.flatMap_nil]
      simp)
  refine ⟨σ', (Run.seq r0 r1).mono (Nat.le_of_eq (by simp only [Expr.size]; ring)), ?_, ?_⟩
  · rw [ho']; rfl
  · rw [ha']

/-! ### The link to the distance matrix of the resolved graph -/

/-- `1` if a vertex has color `X`, and `0` otherwise. -/
noncomputable def flg {n : ℕ} (G : PartialGraph (Fin n)) (X : ℕ) : ℕ :=
  open Classical in if ∃ y < n, colN G y = X then 1 else 0

theorem flg_iff {n : ℕ} (G : PartialGraph (Fin n)) (X : ℕ) :
    (∃ y < n, colN G y = X) ↔ ∃ x : Fin n, G.color x = X := by
  constructor
  · rintro ⟨y, hy, h⟩; exact ⟨⟨y, hy⟩, by simpa [colN, hy] using h⟩
  · rintro ⟨x, h⟩; exact ⟨x.val, x.isLt, by simpa [colN] using h⟩

theorem dcode_occ {n : ℕ} (G : PartialGraph (Fin n)) (a : ℕ∞) (X : ℕ) :
    dcode (a + occ G X) = dcode a * flg G X := by
  classical
  unfold flg
  by_cases h : ∃ x : Fin n, G.color x = X
  · rw [occ_eq_zero G h, add_zero, if_pos ((flg_iff G X).2 h), mul_one]
  · rw [occ_eq_top G h, add_top, dcode_top, if_neg (fun h' => h ((flg_iff G X).1 h')), mul_zero]

theorem flg_le {n : ℕ} (G : PartialGraph (Fin n)) (X : ℕ) : flg G X ≤ 1 := by
  unfold flg; split_ifs <;> omega

/-- **The entries are the codes of the distances after the resolve.** -/
theorem dhCode_eq {n : ℕ} (G : PartialGraph (Fin n)) (s : Bool) (P Q : ℕ) {u v : ℕ} (hu : u < n)
    (hv : v < n) :
    dhCode (dF G) (dtVal (colN G) (dF G) n P) (dtVal (colN G) (dF G) n Q) (flg G P) (flg G Q) u v =
      dcode (distMatrix (resolveBy G s P Q) ⟨u, hu⟩ ⟨v, hv⟩) := by
  rw [distMatrix_resolveBy]
  have e1 : (1 : ℕ∞) = ((1 : ℕ) : ℕ∞) := Nat.cast_one.symm
  have e2 : (2 : ℕ∞) = ((2 : ℕ) : ℕ∞) := Nat.cast_ofNat.symm
  rw [e1, e2]
  simp only [dcode_min, dcode_occ, dcode_add, dtVal_eq G _ hu, dtVal_eq G _ hv, dhCode]
  congr 1
  simp [dF, hu, hv]

/-- `dhWord` is the word of a matrix with the same entries. -/
theorem dhWord_matWord (n : ℕ) (F : ℕ → ℕ → ℕ) (g : Fin n → Fin n → ℕ)
    (h : ∀ u v : Fin n, g u v = F u v) : dhWord n F = matWord n g := by
  have row : ∀ u : Fin n, (List.ofFn fun v : Fin n => g u v) = (List.range n).map (F u) := fun u => by
    apply List.ext_getElem <;> simp [h]
  have e1 : (List.ofFn fun u : Fin n => n :: List.ofFn fun v : Fin n => g u v) =
      (List.range n).map (fun u => n :: (List.range n).map (F u)) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
      rw [row]
  rw [dhWord, matWord, e1, List.flatMap]

/-- **The word of `dhW` is the word of the distance matrix of the resolved graph.** -/
theorem dhWord_eq {n : ℕ} (G : PartialGraph (Fin n)) (s : Bool) (P Q : ℕ) :
    dhWord n (dhCode (dF G) (dtVal (colN G) (dF G) n P) (dtVal (colN G) (dF G) n Q) (flg G P)
      (flg G Q)) = toWord (distMatrix (resolveBy G s P Q)) := by
  rw [toWord_distMatrix]
  exact dhWord_matWord n _ _ fun u v => (dhCode_eq G s P Q u.isLt v.isLt).symm

end Lax185574Proofs.ResolveRam.Glue
