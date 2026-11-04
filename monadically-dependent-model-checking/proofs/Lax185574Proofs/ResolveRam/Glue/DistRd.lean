import Lax185574Proofs.ResolveRam.Glue.DistCode
import Lax185574Proofs.ResolveRam.Glue.R0

/-!
Tape commands on the distance matrix, shared by the pieces of the color
table and of the resolved graph.

* `rdD` reads the word of the distance matrix into the array `dd`, so the
  code of the entry `(u, v)` is at position `2 + u (n + 1) + v`.
* `cminC` and `caddC` compute `cmin` and `cadd` of two codes.
* `dtLoop dst X` writes to `dst[u]` the code of the distance from `u` to
  the color class of the scalar `X`, as the fold `cmPre` over the
  vertices of that class.
* `flgLoop dst X` sets `dst` to `1` if the class of `X` has a vertex and
  to `0` otherwise.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.MC Lax185574Proofs.MC.Glue
open Lax185574Proofs.Words

/-! ### Reading the matrix -/

/-- The length `n (n + 1) + 1` of the word of the matrix. -/
def dlE : Expr := .add (.mul (.var "n") (.add (.var "n") (.lit 1))) (.lit 1)

/-- Read the word of the distance matrix into `dd`. -/
def rdD : Com :=
  .seq (.assign "dl" dlE) (forUp "dv" (.var "dl") (.seq (.read "dx") (.store "dd" (.var "dv") (.var "dx"))))

theorem dlE_evalB {B n : ℕ} {σ : Env} (hn : σ.vars "n" = n) (hB : n * (n + 1) + 1 < B) :
    dlE.evalB B σ = some (n * (n + 1) + 1) := by
  have h1 : n + 1 ≤ n * (n + 1) + 1 := by nlinarith
  exact ev_add (ev_mul (ev_var hn (by omega)) (ev_add (ev_var hn (by omega)) (evalB_lit (by omega))
    (by omega)) (by omega)) (evalB_lit (by omega)) hB

theorem rdD_run {B n : ℕ} {L rest : List ℕ} {σ : Env} (hinp : σ.inp = L ++ rest)
    (hn : σ.vars "n" = n) (hL : L.length = n * (n + 1) + 1) (hdd : (σ.arrs "dd").length = L.length)
    (hLB : L.length < B) (hvB : ∀ v ∈ L, v < B) :
    ∃ σ', Run B rdD σ σ' (L.length * 17 + 30) ∧ σ'.inp = rest ∧ σ'.arrs "dd" = L ∧
      (∀ x, x ∉ ["dl", "dv", "dx"] → σ'.vars x = σ.vars x) ∧
      (∀ a, a ≠ "dd" → σ'.arrs a = σ.arrs a) ∧ σ'.out = σ.out := by
  set N := L.length with hN
  set σ0 := σ.setVar "dl" N
  have r0 : Run B (.assign "dl" dlE) σ σ0 (1 + dlE.size) := Run.assign (by
    rw [hL]; exact dlE_evalB hn (by omega))
  let I : ℕ → Env → Prop := fun k τ => τ.inp = L.drop k ++ rest ∧ τ.vars "dl" = N ∧
    (τ.arrs "dd").length = N ∧ (∀ j < k, (τ.arrs "dd")[j]? = L[j]?) ∧
    (∀ x, x ∉ ["dl", "dv", "dx"] → τ.vars x = σ.vars x) ∧ (∀ a, a ≠ "dd" → τ.arrs a = σ.arrs a) ∧
    τ.out = σ.out
  obtain ⟨σ', r, ⟨h1, -, h2, h3, h4, h5, h6⟩, -⟩ := forUp_run (B := B) (i := "dv") (e := .var "dl")
    (body := .seq (.read "dx") (.store "dd" (.var "dv") (.var "dx"))) (N := N) (K := 9) I (σ := σ0) hLB
    (fun k _ τ hI _ => by rw [evalB_var_iff, hI.2.1]; omega)
    ⟨by simp [σ0, hinp], by simp [σ0], by simp [σ0, hdd], fun j hj => absurd hj (Nat.not_lt_zero _),
      fun x hx => by simp at hx; simp [σ0, hx.1, hx.2.1], fun a _ => by simp [σ0], by simp [σ0]⟩
    (by
      rintro k hk τ ⟨hin, hdl, hl, hg, hv, ha, ho⟩ hvk
      have hd : L.drop k = L[k] :: L.drop (k + 1) := List.drop_eq_getElem_cons hk
      set τ1 : Env := { τ.setVar "dx" L[k] with inp := L.drop (k + 1) ++ rest }
      have r1 : Run B (.read "dx") τ τ1 1 := Run.read (by rw [hin, hd]; rfl)
      have r2 : Run B (.store "dd" (.var "dv") (.var "dx")) τ1 (τ1.setArr "dd" k L[k]) 3 :=
        (Run.store (by simp [τ1, hvk]; omega) (by simp [τ1]; exact hvB _ (List.getElem_mem hk))
          (by simp [τ1, hl, hk])).mono (by simp)
      refine ⟨_, (Run.seq r1 r2).mono (by omega), by simp [τ1, hvk], by simp [τ1], by simp [τ1, hdl],
        by simp [τ1, hl], fun j hj => ?_, fun x hx => ?_, fun a ha' => by simp [τ1, ha', ha a ha'],
        by simp [τ1, ho]⟩
      · simp only [arrs_setVar, arrs_setArr, if_true, τ1]
        rw [List.getElem?_set]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
        · simp [show k ≠ j by omega, hg j h]
        · simp [hl, hk]
      · simp at hx; simp [τ1, hx.1, hx.2.1, hx.2.2, hv x (by simp [hx.1, hx.2.1, hx.2.2])])
  refine ⟨σ', (Run.seq r0 r).mono (by simp only [dlE, Expr.size]; omega),
    by rw [h1]; try simp [N], ?_, h4, fun a ha => by rw [h5 a ha],
    by rw [h6]⟩
  refine List.ext_getElem? fun j => ?_
  by_cases hj : j < N
  · exact h3 j hj
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-! ### Arithmetic on codes -/

/-- `cr := cmin ca cb`. -/
def cminC : Com :=
  .ite (.eq (.var "ca") (.lit 0)) (.assign "cr" (.var "cb"))
    (.ite (.eq (.var "cb") (.lit 0)) (.assign "cr" (.var "ca"))
      (.ite (.lt (.var "ca") (.var "cb")) (.assign "cr" (.var "ca")) (.assign "cr" (.var "cb"))))

theorem cminC_run {B a b : ℕ} {τ : Env} (ha : τ.vars "ca" = a) (hb : τ.vars "cb" = b) (haB : a < B)
    (hbB : b < B) : Run B cminC τ (τ.setVar "cr" (cmin a b)) 20 := by
  have hB : 0 < B := by omega
  have ea := ev_var (B := B) ha haB
  have eb := ev_var (B := B) hb hbB
  have e0 : (Expr.lit 0).evalB B τ = some 0 := evalB_lit hB
  unfold cminC cmin
  by_cases h1 : a = 0
  · have c1 := evalB_condEq ea e0
    rw [show (a == 0) = true by simp [h1]] at c1
    rw [if_pos h1]
    exact (Run.ite_true c1 (Run.assign eb)).mono (by simp [Cond.size, Expr.size])
  · have c1 := evalB_condEq ea e0
    rw [show (a == 0) = false by simp [h1]] at c1
    rw [if_neg h1]
    by_cases h2 : b = 0
    · have c2 := evalB_condEq eb e0
      rw [show (b == 0) = true by simp [h2]] at c2
      rw [if_pos h2]
      exact (Run.ite_false c1 (Run.ite_true c2 (Run.assign ea))).mono (by simp [Cond.size, Expr.size])
    · have c2 := evalB_condEq eb e0
      rw [show (b == 0) = false by simp [h2]] at c2
      rw [if_neg h2]
      have c3 := evalB_condLt ea eb
      by_cases h3 : a < b
      · rw [show decide (a < b) = true by simp [h3]] at c3
        rw [min_eq_left (by omega)]
        exact (Run.ite_false c1 (Run.ite_false c2 (Run.ite_true c3 (Run.assign ea)))).mono
          (by simp [Cond.size, Expr.size])
      · rw [show decide (a < b) = false by simp [h3]] at c3
        rw [min_eq_right (by omega)]
        exact (Run.ite_false c1 (Run.ite_false c2 (Run.ite_false c3 (Run.assign eb)))).mono
          (by simp [Cond.size, Expr.size])

/-- `cr := cadd ca c cb`, for `c ≥ 1`. -/
def caddC (c : ℕ) : Com :=
  .ite (.eq (.var "ca") (.lit 0)) (.assign "cr" (.lit 0))
    (.ite (.eq (.var "cb") (.lit 0)) (.assign "cr" (.lit 0))
      (.assign "cr" (.add (.add (.var "ca") (.var "cb")) (.lit (c - 1)))))

theorem caddC_run {B a b c : ℕ} {τ : Env} (hc : 1 ≤ c) (ha : τ.vars "ca" = a) (hb : τ.vars "cb" = b)
    (hB : a + b + c < B) : Run B (caddC c) τ (τ.setVar "cr" (cadd a c b)) 20 := by
  have ea := ev_var (B := B) ha (by omega)
  have eb := ev_var (B := B) hb (by omega)
  have e0 : (Expr.lit 0).evalB B τ = some 0 := evalB_lit (by omega)
  unfold caddC cadd
  by_cases h1 : a = 0
  · have c1 := evalB_condEq ea e0
    rw [show (a == 0) = true by simp [h1]] at c1
    rw [if_pos (Or.inl h1)]
    exact (Run.ite_true c1 (Run.assign e0)).mono (by simp [Cond.size, Expr.size])
  · have c1 := evalB_condEq ea e0
    rw [show (a == 0) = false by simp [h1]] at c1
    by_cases h2 : b = 0
    · have c2 := evalB_condEq eb e0
      rw [show (b == 0) = true by simp [h2]] at c2
      rw [if_pos (Or.inr h2)]
      exact (Run.ite_false c1 (Run.ite_true c2 (Run.assign e0))).mono (by simp [Cond.size, Expr.size])
    · have c2 := evalB_condEq eb e0
      rw [show (b == 0) = false by simp [h2]] at c2
      rw [if_neg (by omega), show a + c + b - 1 = a + b + (c - 1) by omega]
      exact (Run.ite_false c1 (Run.ite_false c2 (Run.assign (ev_add (ev_add ea eb (by omega))
        (evalB_lit (by omega)) (by omega))))).mono (by simp [Cond.size, Expr.size])

/-! ### Distances to a color class -/

/-- The position of the entry `(du, dw)` in `dd`. -/
def ddE : Expr := .add (.add (.lit 2) (.mul (.var "du") (.add (.var "n") (.lit 1)))) (.var "dw")

theorem ddE_evalB {B n u w : ℕ} {τ : Env} (hn : τ.vars "n" = n) (hu : τ.vars "du" = u)
    (hw : τ.vars "dw" = w) (hnB : n + 1 < B) (hB : 2 + u * (n + 1) + w < B) :
    ddE.evalB B τ = some (2 + u * (n + 1) + w) := by
  have hu' : u < B := by
    have : u ≤ u * (n + 1) := Nat.le_mul_of_pos_right _ (by omega)
    omega
  exact ev_add (ev_add (evalB_lit (by omega)) (ev_mul (ev_var hu hu') (ev_add (ev_var hn (by omega))
    (evalB_lit (by omega)) hnB) (by omega)) (by omega)) (ev_var hw (by omega)) hB

/-- The scalars of `dtLoop`. -/
def dtVs : List String := ["du", "dw", "ca", "cb", "cr"]

/-- One vertex `dw` of the distances from `du` to the class of `X`. -/
def dtStep (dst X : String) : Com :=
  .ite (.eq (.get "co" (.var "dw")) (.var X))
    (.seq (.assign "ca" (.get dst (.var "du"))) (.seq (.assign "cb" (.get "dd" ddE))
      (.seq cminC (.store dst (.var "du") (.var "cr"))))) .skip

/-- The distances from the vertex `du` to the class of `X`. -/
def dtRow (dst X : String) : Com :=
  .seq (.store dst (.var "du") (.lit 0)) (forUp "dw" (.var "n") (dtStep dst X))

/-- **The distances from all vertices to the class of `X`.** -/
def dtLoop (dst X : String) : Com := forUp "du" (.var "n") (dtRow dst X)

/-- The code of the distance from `u` to the class `X`, from the codes
`f u x` of the entries of the matrix. -/
def dtVal (col : ℕ → ℕ) (f : ℕ → ℕ → ℕ) (n X u : ℕ) : ℕ :=
  cmPre (fun x => if col x = X then f u x else 0) n

/-- The data that `dtLoop` reads. -/
structure DtCtx (Xv : String) (n X : ℕ) (col : ℕ → ℕ) (D : List ℕ) (τ : Env) : Prop where
  vn : τ.vars "n" = n
  vx : τ.vars Xv = X
  aco : τ.arrs "co" = arrOf n col
  add : τ.arrs "dd" = D

theorem DtCtx.setVar {Xv : String} {n X : ℕ} {col : ℕ → ℕ} {D : List ℕ} {τ : Env}
    (h : DtCtx Xv n X col D τ) (hXv : Xv ∉ dtVs) {y : String} (hy : y ∈ dtVs) (v : ℕ) :
    DtCtx Xv n X col D (τ.setVar y v) := by
  have hyn : y ≠ "n" := by intro e; subst e; simp [dtVs] at hy
  have hyX : y ≠ Xv := by intro e; subst e; exact hXv hy
  exact ⟨by simp [hyn.symm, h.vn], by simp [hyX.symm, h.vx], by simp [h.aco], by simp [h.add]⟩

theorem DtCtx.setArr {Xv dst : String} {n X : ℕ} {col : ℕ → ℕ} {D : List ℕ} {τ : Env}
    (h : DtCtx Xv n X col D τ) (hd : dst ≠ "co" ∧ dst ≠ "dd") (i v : ℕ) :
    DtCtx Xv n X col D (τ.setArr dst i v) :=
  ⟨by simp [h.vn], by simp [h.vx], by simp [Ne.symm hd.1, h.aco], by simp [Ne.symm hd.2, h.add]⟩

theorem dtStep_run {B n X u w c : ℕ} {col : ℕ → ℕ} {f : ℕ → ℕ → ℕ} {D : List ℕ} {dst Xv : String}
    {τ : Env} (hd : dst ≠ "co" ∧ dst ≠ "dd") (hXv : Xv ∉ dtVs) (hC : DtCtx Xv n X col D τ)
    (hD : ∀ u < n, ∀ x < n, D[2 + u * (n + 1) + x]? = some (f u x))
    (hfB : ∀ u < n, ∀ x < n, f u x < B) (hcolB : ∀ v < n, col v < B) (hXB : X < B)
    (hDB : D.length < B) (hnB : n + 1 < B)
    (hu : τ.vars "du" = u) (hw : τ.vars "dw" = w) (hun : u < n) (hwn : w < n)
    (hc : (τ.arrs dst)[u]? = some c) (hcB : c < B) :
    ∃ τ', Run B (dtStep dst Xv) τ τ' 80 ∧ DtCtx Xv n X col D τ' ∧ τ'.vars "du" = u ∧
      τ'.vars "dw" = w ∧
      τ'.arrs dst = (τ.arrs dst).set u (cmin c (if col w = X then f u w else 0)) := by
  have hwB : w < B := by omega
  have ec : (Cond.eq (.get "co" (.var "dw")) (.var Xv)).evalB B τ = some (col w == X) :=
    evalB_condEq (evalB_get (ev_var hw hwB) (by rw [hC.aco, getElem?_arrOf _ hwn]) (hcolB w hwn))
      (ev_var hC.vx hXB)
  by_cases hwX : col w = X
  · rw [show (col w == X) = true by simp [hwX]] at ec
    rw [if_pos hwX]
    have hpos := hD u hun w hwn
    have hlt : 2 + u * (n + 1) + w < D.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hpos; exact absurd hpos (by simp)
    set τ1 := τ.setVar "ca" c
    have r1 : Run B (.assign "ca" (.get dst (.var "du"))) τ τ1 (1 + (Expr.get dst (.var "du")).size) :=
      Run.assign (evalB_get (ev_var hu (by omega)) hc hcB)
    have hC1 : DtCtx Xv n X col D τ1 := hC.setVar hXv (by simp [dtVs]) c
    set τ2 := τ1.setVar "cb" (f u w)
    have r2 : Run B (.assign "cb" (.get "dd" ddE)) τ1 τ2 (1 + (Expr.get "dd" ddE).size) :=
      Run.assign (evalB_get (ddE_evalB (u := u) (w := w) hC1.vn (by simp [τ1, hu]) (by simp [τ1, hw]) hnB
        (by omega))
        (by rw [hC1.add]; exact hpos) (hfB u hun w hwn))
    have hC2 : DtCtx Xv n X col D τ2 := hC1.setVar hXv (by simp [dtVs]) _
    have r3 := cminC_run (B := B) (τ := τ2) (a := c) (b := f u w) (by simp [τ2, τ1]) (by simp [τ2])
      hcB (hfB u hun w hwn)
    set τ3 := τ2.setVar "cr" (cmin c (f u w))
    have hC3 : DtCtx Xv n X col D τ3 := hC2.setVar hXv (by simp [dtVs]) _
    have hmB : cmin c (f u w) < B := lt_of_le_of_lt (cmin_le_max _ _) (max_lt hcB (hfB u hun w hwn))
    have hl : u < (τ3.arrs dst).length := by
      simp only [τ3, τ2, τ1, arrs_setVar]
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hc; exact absurd hc (by simp)
    have r4 : Run B (.store dst (.var "du") (.var "cr")) τ3 (τ3.setArr dst u (cmin c (f u w))) 3 :=
      (Run.store (ev_var (by simp [τ3, τ2, τ1, hu]) (by omega)) (ev_var (by simp [τ3]) hmB) hl).mono
        (by simp)
    refine ⟨_, (Run.ite_true ec (Run.seq r1 (Run.seq r2 (Run.seq r3 r4)))).mono
      (by simp [Cond.size, Expr.size, ddE]), hC3.setArr hd _ _, by simp [τ3, τ2, τ1, hu],
      by simp [τ3, τ2, τ1, hw], by simp [τ3, τ2, τ1]⟩
  · rw [show (col w == X) = false by simp [hwX]] at ec
    rw [if_neg hwX, cmin_zero_right]
    refine ⟨τ, (Run.ite_false ec Run.skip).mono (by simp [Cond.size, Expr.size]), hC, hu, hw, ?_⟩
    obtain ⟨hl, he⟩ := List.getElem?_eq_some_iff.1 hc
    rw [← he, List.set_getElem_self]

theorem dtVal_lt {B n X : ℕ} {col : ℕ → ℕ} {f : ℕ → ℕ → ℕ} {u : ℕ} (hun : u < n)
    (hfB : ∀ u < n, ∀ x < n, f u x < B) (j : ℕ) (hj : j ≤ n) :
    cmPre (fun x => if col x = X then f u x else 0) j < B := by
  have hB : 0 < B := lt_of_le_of_lt (Nat.zero_le _) (hfB u hun u hun)
  have := cmPre_le (f := fun x => if col x = X then f u x else 0) (k := j) (m := B - 1) (fun x hx => by
    split_ifs
    · have := hfB u hun x (by omega); omega
    · omega)
  omega

theorem dtRow_run {B n X u : ℕ} {col : ℕ → ℕ} {f : ℕ → ℕ → ℕ} {D : List ℕ} {dst Xv : String}
    {τ : Env} (hd : dst ≠ "co" ∧ dst ≠ "dd") (hXv : Xv ∉ dtVs) (hC : DtCtx Xv n X col D τ)
    (hD : ∀ u < n, ∀ x < n, D[2 + u * (n + 1) + x]? = some (f u x))
    (hfB : ∀ u < n, ∀ x < n, f u x < B) (hcolB : ∀ v < n, col v < B) (hXB : X < B)
    (hDB : D.length < B) (hnB : n + 1 < B)
    (hu : τ.vars "du" = u) (hun : u < n) (hl : (τ.arrs dst).length = n) :
    ∃ τ', Run B (dtRow dst Xv) τ τ' (n * 88 + 9) ∧ DtCtx Xv n X col D τ' ∧ τ'.vars "du" = u ∧
      τ'.arrs dst = (τ.arrs dst).set u (dtVal col f n X u) := by
  set g : ℕ → ℕ := fun x => if col x = X then f u x else 0
  have r0 : Run B (.store dst (.var "du") (.lit 0)) τ (τ.setArr dst u 0) 3 :=
    (Run.store (ev_var hu (by omega)) (evalB_lit (by omega)) (by omega)).mono (by simp)
  set A := τ.arrs dst
  let I : ℕ → Env → Prop := fun j ρ => DtCtx Xv n X col D ρ ∧ ρ.vars "du" = u ∧
    ρ.arrs dst = A.set u (cmPre g j)
  obtain ⟨τ', r1, ⟨hC', hu', ha'⟩, -⟩ := forUp_run (B := B) (i := "dw") (e := .var "n")
    (body := dtStep dst Xv) (N := n) (K := 80) I (σ := τ.setArr dst u 0) (by omega)
    (fun k _ ρ hI _ => by rw [evalB_var_iff, hI.1.vn]; omega)
    ⟨(hC.setArr hd u 0).setVar hXv (by simp [dtVs]) 0, by simp [hu], by simp [A, cmPre]⟩
    (by
      rintro j hj ρ ⟨hCρ, huρ, haρ⟩ hwj
      have hc : (ρ.arrs dst)[u]? = some (cmPre g j) := by
        rw [haρ, List.getElem?_set_self (by simp [A, hl, hun])]
      obtain ⟨ρ', r, hC', hu', hw', ha'⟩ := dtStep_run (c := cmPre g j) hd hXv hCρ hD hfB hcolB hXB hDB
        hnB huρ hwj hun hj hc (dtVal_lt hun hfB j (by omega))
      refine ⟨ρ', r, hw', hC'.setVar hXv (by simp [dtVs]) _, by simp [hu'], ?_⟩
      simp only [arrs_setVar]
      rw [ha', haρ, List.set_set]
      rfl)
  refine ⟨τ', (Run.seq r0 r1).mono (by simp only [Expr.size]; omega), hC', hu', ?_⟩
  rw [ha']
  rfl

/-- **The run of `dtLoop`.** -/
theorem dtLoop_run {B n X : ℕ} {col : ℕ → ℕ} {f : ℕ → ℕ → ℕ} {D : List ℕ} {dst Xv : String}
    {σ : Env} (hd : dst ≠ "co" ∧ dst ≠ "dd") (hXv : Xv ∉ dtVs) (hC : DtCtx Xv n X col D σ)
    (hD : ∀ u < n, ∀ x < n, D[2 + u * (n + 1) + x]? = some (f u x))
    (hfB : ∀ u < n, ∀ x < n, f u x < B) (hcolB : ∀ v < n, col v < B) (hXB : X < B)
    (hDB : D.length < B) (hnB : n + 1 < B) (hl : (σ.arrs dst).length = n) :
    ∃ σ', Run B (dtLoop dst Xv) σ σ' (n * (n * 88 + 17) + 6) ∧ DtCtx Xv n X col D σ' ∧
      σ'.arrs dst = arrOf n (dtVal col f n X) := by
  let I : ℕ → Env → Prop := fun k ρ => DtCtx Xv n X col D ρ ∧ (ρ.arrs dst).length = n ∧
    ∀ u < k, (ρ.arrs dst)[u]? = some (dtVal col f n X u)
  obtain ⟨σ', r, ⟨hC', hl', hv'⟩, -⟩ := forUp_run (B := B) (i := "du") (e := .var "n")
    (body := dtRow dst Xv) (N := n) (K := n * 88 + 9) I (σ := σ) (by omega)
    (fun k _ ρ hI _ => by rw [evalB_var_iff, hI.1.vn]; omega)
    ⟨hC.setVar hXv (by simp [dtVs]) 0, by simp [hl], fun u hu => absurd hu (Nat.not_lt_zero _)⟩
    (by
      rintro k hk ρ ⟨hCρ, hlρ, hvρ⟩ huk
      obtain ⟨ρ', r, hC', hu', ha'⟩ := dtRow_run (u := k) hd hXv hCρ hD hfB hcolB hXB hDB hnB huk hk hlρ
      refine ⟨ρ', r, hu', hC'.setVar hXv (by simp [dtVs]) _, by simp [ha', hlρ], fun u hu => ?_⟩
      simp only [arrs_setVar, ha']
      rcases Nat.lt_succ_iff_lt_or_eq.1 hu with h | rfl
      · rw [List.getElem?_set_ne (by omega)]; exact hvρ u h
      · rw [List.getElem?_set_self (by omega)])
  refine ⟨σ', r.mono (by simp only [Expr.size]; try (ring_nf; omega)), hC', ?_⟩
  refine List.ext_getElem? fun u => ?_
  by_cases hu : u < n
  · rw [hv' u hu, getElem?_arrOf _ hu]
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

/-! ### Whether a color class has a vertex -/

/-- Set the scalar `dst` to `1` if a vertex has the color of `X`, and to
`0` otherwise. -/
def flgLoop (dst X : String) : Com :=
  .seq (.assign dst (.lit 0)) (forUp "dw" (.var "n")
    (.ite (.eq (.get "co" (.var "dw")) (.var X)) (.assign dst (.lit 1)) .skip))

open Classical in
theorem flgLoop_run {B n X : ℕ} {col : ℕ → ℕ} {dst Xv : String} {σ : Env}
    (hdst : dst ∉ ["n", "dw"]) (hXv : Xv ∉ ["dw", dst]) (hn : σ.vars "n" = n) (hX : σ.vars Xv = X)
    (hco : σ.arrs "co" = arrOf n col) (hcolB : ∀ v < n, col v < B) (hXB : X < B) (hnB : n + 1 < B) :
    ∃ σ', Run B (flgLoop dst Xv) σ σ' (n * 30 + 10) ∧
      σ'.vars dst = (if ∃ x < n, col x = X then 1 else 0) ∧
      (∀ y, y ∉ [dst, "dw"] → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧
      σ'.inp = σ.inp := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hdst hXv
  set σ0 := σ.setVar dst 0
  have r0 : Run B (.assign dst (.lit 0)) σ σ0 2 := (Run.assign (evalB_lit (by omega))).mono (by simp)
  let I : ℕ → Env → Prop := fun k ρ => ρ.vars dst = (if ∃ x < k, col x = X then 1 else 0) ∧
    (∀ y, y ∉ [dst, "dw"] → ρ.vars y = σ.vars y) ∧ ρ.arrs = σ.arrs ∧ ρ.out = σ.out ∧ ρ.inp = σ.inp
  obtain ⟨σ', r, hI, -⟩ := forUp_run (B := B) (i := "dw") (e := .var "n")
    (body := .ite (.eq (.get "co" (.var "dw")) (.var Xv)) (.assign dst (.lit 1)) .skip) (N := n)
    (K := 20) I (σ := σ0) (by omega)
    (fun k _ ρ hI _ => by
      rw [evalB_var_iff, hI.2.1 "n" (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
        exact ⟨fun h => hdst.1 h.symm, by decide⟩), hn]; omega)
    ⟨by simp [σ0, hdst.2], fun y hy => by simp at hy; simp [σ0, hy.1, hy.2],
      by simp [σ0], by simp [σ0], by simp [σ0]⟩
    (by
      rintro k hk ρ ⟨hd, hv, ha, ho, hi⟩ hwk
      have ec : (Cond.eq (.get "co" (.var "dw")) (.var Xv)).evalB B ρ = some (col k == X) :=
        evalB_condEq (evalB_get (ev_var hwk (by omega)) (by rw [ha, hco, getElem?_arrOf _ hk])
          (hcolB k hk)) (ev_var (by rw [hv Xv (by simp; exact ⟨hXv.2, hXv.1⟩), hX]) hXB)
      by_cases hkX : col k = X
      · rw [show (col k == X) = true by simp [hkX]] at ec
        refine ⟨_, (Run.ite_true ec (Run.assign (evalB_lit (by omega)))).mono
          (by simp [Cond.size, Expr.size]), by simp [Ne.symm hdst.2, hwk], ?_, fun y hy => ?_,
          by simp [ha], by simp [ho], by simp [hi]⟩
        · simp only [vars_setVar, if_true, show dst ≠ "dw" from hdst.2, if_false]
          rw [if_pos ⟨k, by omega, hkX⟩]
        · simp at hy
          simp [hy.1, hy.2, hv y (by simp; exact hy)]
      · rw [show (col k == X) = false by simp [hkX]] at ec
        refine ⟨_, (Run.ite_false ec Run.skip).mono (by simp [Cond.size, Expr.size]), hwk, ?_,
          fun y hy => ?_, by simp [ha], by simp [ho], by simp [hi]⟩
        · simp only [vars_setVar, show dst ≠ "dw" from hdst.2, if_false, hd]
          congr 1
          apply propext
          constructor
          · rintro ⟨x, hx, h⟩; exact ⟨x, by omega, h⟩
          · rintro ⟨x, hx, h⟩
            refine ⟨x, ?_, h⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hx with h' | rfl
            · exact h'
            · exact absurd h hkX
        · simp at hy
          simp [hy.2, hv y (by simp; exact hy)])
  obtain ⟨hd, hv, ha, ho, hi⟩ := hI
  exact ⟨σ', (Run.seq r0 r).mono (by simp only [Expr.size]; omega), hd, hv, ha, ho, hi⟩

/-! ### The least code over each class -/

/-- Clear the first `n` entries of `dst`. -/
def clrA (dst : String) : Com := forUp "bz" (.var "n") (.store dst (.var "bz") (.lit 0))

theorem clrA_run {B n : ℕ} {dst : String} {σ : Env} (C : Env → Prop)
    (hC : ∀ τ x, C τ → C (τ.setVar "bz" x)) (hCa : ∀ τ i x, C τ → C (τ.setArr dst i x))
    (hCn : ∀ τ, C τ → τ.vars "n" = n) (hσ : C σ) (hl : (σ.arrs dst).length = n) (hnB : n < B) :
    ∃ σ', Run B (clrA dst) σ σ' (n * 12 + 6) ∧ C σ' ∧ σ'.arrs dst = arrOf n (fun _ => 0) := by
  let fk : ℕ → ℕ → ℕ := fun k v => if v < k then 0 else (σ.arrs dst).getD v 0
  let I : ℕ → Env → Prop := fun k τ => C τ ∧ τ.arrs dst = arrOf n (fk k)
  have h0 : σ.arrs dst = arrOf n (fk 0) := by
    refine List.ext_getElem (by simp [hl]) fun v h1 h2 => ?_
    simp [fk, arrOf, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1]
  obtain ⟨σ', hr, ⟨hC', h'⟩, -⟩ := forUp_run (B := B) (i := "bz") (e := .var "n")
    (body := .store dst (.var "bz") (.lit 0)) (N := n) (K := 4) I hnB
    (fun k _ τ hI _ => by
      simp only [evalB_var_iff]; exact ⟨(hCn τ hI.1).symm, by rw [hCn τ hI.1]; exact hnB⟩)
    ⟨hC σ 0 hσ, by rw [arrs_setVar]; exact h0⟩
    (by
      rintro k hk τ ⟨hCτ, hτ⟩ hbz
      refine ⟨τ.setArr dst k 0, (Run.store (by simp [hbz]; omega) (by simp; omega)
        (by rw [hτ]; simp; omega)).mono (by simp [Expr.size]), by simp [hbz],
        hC _ _ (hCa _ _ _ hCτ), ?_⟩
      rw [arrs_setVar, arrs_setArr, if_pos rfl, hτ, set_arrOf]
      congr 1; funext v
      by_cases hv : v = k
      · subst hv; simp [fk]
      · simp only [hv, if_false, fk]
        by_cases hvk : v < k
        · simp [hvk, show v < k + 1 by omega]
        · simp [hvk, show ¬ v < k + 1 by omega])
  refine ⟨σ', hr.mono (by simp [Expr.size]), hC', ?_⟩
  rw [h']; simp only [arrOf]
  exact List.map_congr_left fun v hv => by simp [fk, List.mem_range.1 hv]

/-- One vertex `bz` of the least codes over the classes. -/
def clsBody (dst : String) : Com :=
  .seq (.assign "ca" (.get dst (.get "cl" (.var "bz")))) (.seq (.assign "cb" (.get "dm" (.var "bz")))
    (.seq cminC (.store dst (.get "cl" (.var "bz")) (.var "cr"))))

/-- **The least code over each class.** For the class index `c`,
`dst[c]` folds the values `dm[y]` of the vertices `y` with `cl[y] = c`. -/
def clsLoop (dst : String) : Com := .seq (clrA dst) (forUp "bz" (.var "n") (clsBody dst))

/-- The value of `clsLoop` at the class index `c`. -/
def clsVal (cl t : ℕ → ℕ) (n c : ℕ) : ℕ := cmPre (fun y => if cl y = c then t y else 0) n

theorem clsLoop_run {B n : ℕ} {cl t : ℕ → ℕ} {dst : String} {σ : Env} (hd : dst ≠ "cl" ∧ dst ≠ "dm")
    (hn : σ.vars "n" = n) (hcl : σ.arrs "cl" = arrOf n cl) (hdm : σ.arrs "dm" = arrOf n t)
    (hclc : ∀ v < n, cl v < n) (htB : ∀ v < n, t v < B) (hnB : n + 1 < B)
    (hl : (σ.arrs dst).length = n) :
    ∃ σ', Run B (clsLoop dst) σ σ' (n * 60 + 20) ∧ σ'.arrs dst = arrOf n (clsVal cl t n) ∧
      σ'.vars "n" = n ∧ σ'.arrs "cl" = σ.arrs "cl" ∧ σ'.arrs "dm" = σ.arrs "dm" := by
  have hB0 : 0 < B := by omega
  let C : Env → Prop := fun τ => τ.vars "n" = n ∧ τ.arrs "cl" = arrOf n cl ∧ τ.arrs "dm" = arrOf n t
  have hCv : ∀ τ (y : String) x, C τ → y ≠ "n" → C (τ.setVar y x) := fun τ y x h hy =>
    ⟨by simp [Ne.symm hy, h.1], by simp [h.2.1], by simp [h.2.2]⟩
  have hCa : ∀ τ i x, C τ → C (τ.setArr dst i x) := fun τ i x h =>
    ⟨by simp [h.1], by simp [Ne.symm hd.1, h.2.1], by simp [Ne.symm hd.2, h.2.2]⟩
  obtain ⟨σ1, r1, hC1, h1⟩ := clrA_run (B := B) (dst := dst) C (fun τ x h => hCv τ "bz" x h (by decide))
    hCa (fun τ h => h.1) ⟨hn, hcl, hdm⟩ hl (by omega)
  have hval : ∀ c, ∀ k ≤ n, cmPre (fun y => if cl y = c then t y else 0) k ≤ B - 1 := fun c k hk =>
    cmPre_le fun y hy => by
      split_ifs
      · have := htB y (by omega); omega
      · omega
  let I : ℕ → Env → Prop := fun k ρ => C ρ ∧
    ρ.arrs dst = arrOf n (fun c => cmPre (fun y => if cl y = c then t y else 0) k)
  obtain ⟨σ', r2, ⟨hC', h'⟩, -⟩ := forUp_run (B := B) (i := "bz") (e := .var "n")
    (body := clsBody dst) (N := n) (K := 40) I (σ := σ1) (by omega)
    (fun k _ ρ hI _ => by rw [evalB_var_iff, hI.1.1]; omega)
    ⟨hCv _ _ _ hC1 (by decide), by simp only [arrs_setVar, h1]; rfl⟩
    (by
      rintro k hk ρ ⟨hCρ, hρ⟩ hbz
      have hck := hclc k hk
      set c0 := cl k
      set v0 := cmPre (fun y => if cl y = c0 then t y else 0) k
      have ecl : (Expr.get "cl" (.var "bz")).evalB B ρ = some c0 :=
        evalB_get (ev_var hbz (by omega)) (by rw [hCρ.2.1, getElem?_arrOf _ hk]) (by omega)
      set ρ1 := ρ.setVar "ca" v0
      have r1 : Run B (.assign "ca" (.get dst (.get "cl" (.var "bz")))) ρ ρ1
          (1 + (Expr.get dst (.get "cl" (.var "bz"))).size) :=
        Run.assign (evalB_get ecl (by rw [hρ, getElem?_arrOf _ hck]) (by have := hval c0 k (by omega); omega))
      set ρ2 := ρ1.setVar "cb" (t k)
      have r2 : Run B (.assign "cb" (.get "dm" (.var "bz"))) ρ1 ρ2 (1 + (Expr.get "dm" (.var "bz")).size) :=
        Run.assign (evalB_get (ev_var (v := k) (by simp [ρ1, hbz]) (by omega))
          (by simp only [ρ1, arrs_setVar]; rw [hCρ.2.2, getElem?_arrOf _ hk]) (htB k hk))
      have r3 := cminC_run (B := B) (τ := ρ2) (a := v0) (b := t k) (by simp [ρ2, ρ1]) (by simp [ρ2])
        (by have := hval c0 k (by omega); omega) (htB k hk)
      set ρ3 := ρ2.setVar "cr" (cmin v0 (t k))
      have hmB : cmin v0 (t k) < B :=
        lt_of_le_of_lt (cmin_le_max _ _) (max_lt (by have := hval c0 k (by omega); omega) (htB k hk))
      have ecl3 : (Expr.get "cl" (.var "bz")).evalB B ρ3 = some c0 :=
        evalB_get (ev_var (v := k) (by simp [ρ3, ρ2, ρ1, hbz]) (by omega))
          (by simp only [ρ3, ρ2, ρ1, arrs_setVar]; rw [hCρ.2.1, getElem?_arrOf _ hk]) (by omega)
      have r4 : Run B (.store dst (.get "cl" (.var "bz")) (.var "cr")) ρ3 (ρ3.setArr dst c0 (cmin v0 (t k)))
          (1 + (Expr.get "cl" (.var "bz")).size + (Expr.var "cr").size) :=
        Run.store ecl3 (ev_var (by simp [ρ3]) hmB) (by simp [ρ3, ρ2, ρ1, hρ, hck])
      refine ⟨_, (Run.seq r1 (Run.seq r2 (Run.seq r3 r4))).mono (by simp [Expr.size]), by simp [ρ3, ρ2, ρ1, hbz],
        hCv _ _ _ (hCa _ _ _ (hCv _ _ _ (hCv _ _ _ (hCv _ _ _ hCρ (by decide)) (by decide)) (by decide)))
          (by decide), ?_⟩
      simp only [arrs_setVar, arrs_setArr, if_true, ρ3, ρ2, ρ1, hρ, set_arrOf]
      congr 1; funext c
      by_cases hc : c = c0
      · subst hc; simp only [if_true, cmPre, v0, c0]
      · rw [if_neg hc, cmPre, if_neg (Ne.symm hc), cmin_zero_right])
  refine ⟨σ', (Run.seq r1 r2).mono (by simp only [Expr.size]; omega), by rw [h']; rfl, hC'.1,
    by rw [hC'.2.1, hcl], by rw [hC'.2.2, hdm]⟩

end Lax185574Proofs.ResolveRam.Glue
