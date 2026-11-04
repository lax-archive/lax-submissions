import Lax185574Proofs.ResolveRam.Glue.PieceSpec

/-!
Running a tape program inside a piece.

The pieces that read the input of the composite get it in the array `x`
and write to the buffer `OB`. Many programs that read graphs and write
words exist in the tape form, with scalars and arrays of exact lengths.
`trC r c` runs such a program `c` in a piece: the scalars and arrays of
`c` are renamed by `r`, a read takes the entry of `x` at the pointer `tq`
and advances the pointer, and a write appends to `OB` at `po` (`push1`).

The link is the relation `Sim p σ τ` between an environment `σ` of the
tape program and an environment `τ` of the piece: the renamed scalars
agree, every renamed array is the array of `σ` followed by a fixed tail,
the input of `σ` is the part of `x` from the pointer on (up to a bound),
and the buffer holds a fixed prefix followed by the output of `σ`. Every
run of `c` from `σ` gives a run of `trC r c` from `τ`, at most eight
times as costly, that keeps the relation (`trC_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.MC

/-- A renaming of the scalars and of the arrays. -/
structure Ren where
  v : String → String
  a : String → String

/-- The renaming by prefixes. -/
def preRen (pv pa : String) : Ren := ⟨(pv ++ ·), (pa ++ ·)⟩

/-- The renamed expression. -/
def rnE (r : Ren) : Expr → Expr
  | .lit n => .lit n
  | .var x => .var (r.v x)
  | .get a i => .get (r.a a) (rnE r i)
  | .bin op e f => .bin op (rnE r e) (rnE r f)

/-- The renamed condition. -/
def rnB (r : Ren) : Cond → Cond
  | .eq e f => .eq (rnE r e) (rnE r f)
  | .lt e f => .lt (rnE r e) (rnE r f)

/-- **The tape program in a piece.** -/
def trC (r : Ren) : Com → Com
  | .skip => .skip
  | .assign x e => .assign (r.v x) (rnE r e)
  | .store a i e => .store (r.a a) (rnE r i) (rnE r e)
  | .seq c d => .seq (trC r c) (trC r d)
  | .ite b c d => .ite (rnB r b) (trC r c) (trC r d)
  | .while b c => .while (rnB r b) (trC r c)
  | .read x => .seq (.assign (r.v x) (.get "x" (.var "tq"))) (.assign "tq" (.add (.var "tq") (.lit 1)))
  | .write e => push1 "OB" "po" (rnE r e)

/-- The expression uses only the scalars `Vs` and the arrays `As`. -/
def okE (Vs As : List String) : Expr → Bool
  | .lit _ => true
  | .var x => decide (x ∈ Vs)
  | .get a i => decide (a ∈ As) && okE Vs As i
  | .bin _ e f => okE Vs As e && okE Vs As f

/-- The condition uses only the scalars `Vs` and the arrays `As`. -/
def okB (Vs As : List String) : Cond → Bool
  | .eq e f => okE Vs As e && okE Vs As f
  | .lt e f => okE Vs As e && okE Vs As f

/-- The command uses only the scalars `Vs` and the arrays `As`. -/
def okC (Vs As : List String) : Com → Bool
  | .skip => true
  | .assign x e => decide (x ∈ Vs) && okE Vs As e
  | .store a i e => decide (a ∈ As) && okE Vs As i && okE Vs As e
  | .seq c d => okC Vs As c && okC Vs As d
  | .ite b c d => okB Vs As b && okC Vs As c && okC Vs As d
  | .while b c => okB Vs As b && okC Vs As c
  | .read x => decide (x ∈ Vs)
  | .write e => okE Vs As e

theorem size_rnE (r : Ren) : ∀ e : Expr, (rnE r e).size = e.size
  | .lit _ => rfl
  | .var _ => rfl
  | .get _ i => by simp [rnE, size_rnE r i]
  | .bin _ e f => by simp [rnE, size_rnE r e, size_rnE r f]

theorem size_rnB (r : Ren) : ∀ b : Cond, (rnB r b).size = b.size
  | .eq e f => by simp [rnB, Cond.size, size_rnE]
  | .lt e f => by simp [rnB, Cond.size, size_rnE]

/-- The data of a translation. -/
structure TrP where
  r : Ren
  Vs : List String
  As : List String
  pad : String → List ℕ
  X : List ℕ
  L : ℕ
  pre : List ℕ
  NOB : ℕ

/-- The names of a translation are apart. -/
def TrP.names (p : TrP) : Bool :=
  (p.Vs.map p.r.v).Nodup && (p.As.map p.r.a).Nodup && p.Vs.all (fun x => p.r.v x ≠ "tq" && p.r.v x ≠ "po") &&
    p.As.all (fun a => p.r.a a ≠ "x" && p.r.a a ≠ "OB")

/-- The conditions of a translation. -/
structure TrP.OK (p : TrP) (B : ℕ) : Prop where
  names : p.names = true
  hL : p.L < B
  hX : ∀ u ∈ p.X.take p.L, u < B

/-- **The relation of the two environments.** -/
structure Sim (p : TrP) (σ τ : Env) : Prop where
  vars : ∀ x ∈ p.Vs, τ.vars (p.r.v x) = σ.vars x
  arrs : ∀ a ∈ p.As, τ.arrs (p.r.a a) = σ.arrs a ++ p.pad a
  xa : τ.arrs "x" = p.X
  inp : σ.inp = (p.X.take p.L).drop (τ.vars "tq")
  outF : Filled "OB" "po" (p.pre ++ σ.out) τ
  obl : (τ.arrs "OB").length = p.NOB

section names

variable {p : TrP} {B : ℕ} (hp : p.OK B)
include hp

theorem TrP.OK.injv : ∀ x ∈ p.Vs, ∀ y ∈ p.Vs, p.r.v x = p.r.v y → x = y := by
  have h := hp.names
  simp only [TrP.names, Bool.and_eq_true, decide_eq_true_eq] at h
  exact fun x hx y hy => List.inj_on_of_nodup_map h.1.1.1 hx hy

theorem TrP.OK.inja : ∀ a ∈ p.As, ∀ b ∈ p.As, p.r.a a = p.r.a b → a = b := by
  have h := hp.names
  simp only [TrP.names, Bool.and_eq_true, decide_eq_true_eq] at h
  exact fun x hx y hy => List.inj_on_of_nodup_map h.1.1.2 hx hy

theorem TrP.OK.vtq : ∀ x ∈ p.Vs, p.r.v x ≠ "tq" ∧ p.r.v x ≠ "po" := by
  have h := hp.names
  simp only [TrP.names, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  intro x hx
  have := h.1.2 x hx
  simpa using this

theorem TrP.OK.ax : ∀ a ∈ p.As, p.r.a a ≠ "x" ∧ p.r.a a ≠ "OB" := by
  have h := hp.names
  simp only [TrP.names, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  intro a ha
  have := h.2 a ha
  simpa using this

end names

theorem rnE_evalB {B : ℕ} {r : Ren} {Vs As : List String} {pad : String → List ℕ} {σ τ : Env}
    (hv : ∀ x ∈ Vs, τ.vars (r.v x) = σ.vars x) (ha : ∀ a ∈ As, τ.arrs (r.a a) = σ.arrs a ++ pad a) :
    ∀ (e : Expr), okE Vs As e = true → ∀ {v : ℕ}, e.evalB B σ = some v → (rnE r e).evalB B τ = some v
  | .lit n, _, v, h => by simpa [rnE, Expr.evalB] using h
  | .var x, hx, v, h => by
    simp only [okE, decide_eq_true_eq] at hx
    simp only [rnE, Expr.evalB, hv x hx]; exact h
  | .get a i, hai, v, h => by
    simp only [okE, Bool.and_eq_true, decide_eq_true_eq] at hai
    rw [rnE, evalB_get_iff]
    rw [evalB_get_iff] at h
    obtain ⟨k, hk, hu, hf⟩ := h
    refine ⟨k, rnE_evalB hv ha i hai.2 hk, ?_, hf⟩
    rw [ha a hai.1, List.getElem?_append_left (List.getElem?_eq_some_iff.1 hu).1]
    exact hu
  | .bin op e f, hef, v, h => by
    simp only [okE, Bool.and_eq_true] at hef
    rw [rnE, evalB_bin_iff]
    rw [evalB_bin_iff] at h
    obtain ⟨m, n, hm, hn, hf⟩ := h
    exact ⟨m, n, rnE_evalB hv ha e hef.1 hm, rnE_evalB hv ha f hef.2 hn, hf⟩

theorem rnB_evalB {B : ℕ} {r : Ren} {Vs As : List String} {pad : String → List ℕ} {σ τ : Env}
    (hv : ∀ x ∈ Vs, τ.vars (r.v x) = σ.vars x) (ha : ∀ a ∈ As, τ.arrs (r.a a) = σ.arrs a ++ pad a)
    (b : Cond) (hb : okB Vs As b = true) {t : Bool} (h : b.evalB B σ = some t) :
    (rnB r b).evalB B τ = some t := by
  cases b with
  | eq e f =>
    simp only [okB, Bool.and_eq_true] at hb
    rw [rnB, evalB_condEq_iff]
    rw [evalB_condEq_iff] at h
    obtain ⟨m, n, hm, hn, hf⟩ := h
    exact ⟨m, n, rnE_evalB hv ha e hb.1 hm, rnE_evalB hv ha f hb.2 hn, hf⟩
  | lt e f =>
    simp only [okB, Bool.and_eq_true] at hb
    rw [rnB, evalB_condLt_iff]
    rw [evalB_condLt_iff] at h
    obtain ⟨m, n, hm, hn, hf⟩ := h
    exact ⟨m, n, rnE_evalB hv ha e hb.1 hm, rnE_evalB hv ha f hb.2 hn, hf⟩

/-- The output of a run extends the output before it. -/
theorem bs_out_prefix {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ} (h : BigStepB B c σ σ' k) :
    σ.out <+: σ'.out := by
  induction h with
  | skip => exact List.prefix_refl _
  | assign _ => exact List.prefix_refl _
  | store _ _ _ => exact List.prefix_refl _
  | seq _ _ ih ih' => exact ih.trans ih'
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => exact ih.trans ih'
  | while_false _ => exact List.prefix_refl _
  | read _ => exact List.prefix_refl _
  | write _ => exact List.prefix_append _ _

/-- A run keeps the lengths of all arrays. -/
theorem bs_len_eq {B : ℕ} {c : Com} {σ σ' : Env} {k : ℕ} (h : BigStepB B c σ σ' k) (b : String) :
    (σ'.arrs b).length = (σ.arrs b).length := by
  induction h with
  | skip => rfl
  | assign _ => rfl
  | store _ _ _ => simp only [arrs_setArr]; split <;> simp_all
  | seq _ _ ih ih' => rw [ih', ih]
  | ite_true _ _ ih => exact ih
  | ite_false _ _ ih => exact ih
  | while_true _ _ _ ih ih' => rw [ih', ih]
  | while_false _ => rfl
  | read _ => rfl
  | write _ => rfl

theorem run_len_eq {B : ℕ} {c : Com} {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K) (b : String) :
    (σ'.arrs b).length = (σ.arrs b).length := by
  obtain ⟨_, _, h⟩ := h; exact bs_len_eq h b

/-- **One run of the translation.** -/
theorem trC_bigStep {p : TrP} {B : ℕ} (hp : p.OK B) {c : Com} {σ σ' : Env} {k : ℕ}
    (h : BigStepB B c σ σ' k) :
    okC p.Vs p.As c = true → ∀ τ, Sim p σ τ → (p.pre ++ σ'.out).length ≤ p.NOB →
      (p.pre ++ σ'.out).length < B →
      ∃ τ' k', k' ≤ 8 * k ∧ BigStepB B (trC p.r c) τ τ' k' ∧ Sim p σ' τ' := by
  induction h with
  | skip =>
    intro _ τ hs _ _
    exact ⟨τ, 1, by omega, .skip, hs⟩
  | @assign σ x e v he =>
    intro hc τ hs _ _
    simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hv := hp.vtq x hc.1
    refine ⟨τ.setVar (p.r.v x) v, 1 + e.size, by omega, ?_, ?_⟩
    · have := BigStepB.assign (B := B) (x := p.r.v x) (rnE_evalB hs.vars hs.arrs e hc.2 he)
      rwa [size_rnE] at this
    · refine ⟨fun y hy => ?_, fun a ha => by simp [hs.arrs a ha], by simp [hs.xa], ?_,
        hs.outF.setVar hv.2 _, by simp [hs.obl]⟩
      · simp only [vars_setVar]
        by_cases hyx : y = x
        · subst hyx; simp
        · have : p.r.v y ≠ p.r.v x := fun h' => hyx (hp.injv y hy x hc.1 h')
          simp [this, hyx, hs.vars y hy]
      · simp [Ne.symm hv.1, hs.inp]
  | @store σ a i e kk v hi he hk =>
    intro hc τ hs _ _
    simp only [okC, Bool.and_eq_true, decide_eq_true_eq] at hc
    have hax := hp.ax a hc.1.1
    have hk' : kk < (τ.arrs (p.r.a a)).length := by rw [hs.arrs a hc.1.1]; simp; omega
    refine ⟨τ.setArr (p.r.a a) kk v, 1 + i.size + e.size, by omega, ?_, ?_⟩
    · have := BigStepB.store (B := B) (a := p.r.a a) (rnE_evalB hs.vars hs.arrs i hc.1.2 hi)
        (rnE_evalB hs.vars hs.arrs e hc.2 he) hk'
      rwa [size_rnE, size_rnE] at this
    · refine ⟨fun y hy => by simp [hs.vars y hy], fun b hb => ?_, by simp [Ne.symm hax.1, hs.xa],
        by simp [hs.inp], hs.outF.congr (by simp) (by simp [Ne.symm hax.2]), by simp [Ne.symm hax.2, hs.obl]⟩
      simp only [arrs_setArr]
      by_cases hba : b = a
      · subst hba; simp [hs.arrs b hb, List.set_append_left _ _ hk]
      · have : p.r.a b ≠ p.r.a a := fun h' => hba (hp.inja b hb a hc.1.1 h')
        simp [this, hba, hs.arrs b hb]
  | @seq c d σ₁ σ₂ σ₃ k₁ k₂ h₁ h₂ ih₁ ih₂ =>
    intro hc τ hs hO1 hO2
    simp only [okC, Bool.and_eq_true] at hc
    have hpr := bs_out_prefix h₂
    have hl : (p.pre ++ σ₂.out).length ≤ (p.pre ++ σ₃.out).length := by
      simp only [List.length_append]; have := hpr.length_le; omega
    obtain ⟨τ₁, k₁', hk₁, r₁, hs₁⟩ := ih₁ hc.1 τ hs (by omega) (by omega)
    obtain ⟨τ₂, k₂', hk₂, r₂, hs₂⟩ := ih₂ hc.2 τ₁ hs₁ hO1 hO2
    exact ⟨τ₂, k₁' + k₂', by omega, .seq r₁ r₂, hs₂⟩
  | @ite_true b c d σ₁ σ₂ k₁ hb h₁ ih =>
    intro hc τ hs hO1 hO2
    simp only [okC, Bool.and_eq_true] at hc
    obtain ⟨τ₁, k₁', hk₁, r₁, hs₁⟩ := ih hc.1.2 τ hs hO1 hO2
    refine ⟨τ₁, 1 + b.size + k₁', by omega, ?_, hs₁⟩
    have := BigStepB.ite_true (d := trC p.r d) (rnB_evalB hs.vars hs.arrs b hc.1.1 hb) r₁
    rwa [size_rnB] at this
  | @ite_false b c d σ₁ σ₂ k₁ hb h₁ ih =>
    intro hc τ hs hO1 hO2
    simp only [okC, Bool.and_eq_true] at hc
    obtain ⟨τ₁, k₁', hk₁, r₁, hs₁⟩ := ih hc.2 τ hs hO1 hO2
    refine ⟨τ₁, 1 + b.size + k₁', by omega, ?_, hs₁⟩
    have := BigStepB.ite_false (c := trC p.r c) (rnB_evalB hs.vars hs.arrs b hc.1.1 hb) r₁
    rwa [size_rnB] at this
  | @while_true b c σ₁ σ₂ σ₃ k₁ k₂ hb h₁ h₂ ih₁ ih₂ =>
    intro hc τ hs hO1 hO2
    have hc' := hc
    simp only [okC, Bool.and_eq_true] at hc'
    have hpr := bs_out_prefix h₂
    have hl : (p.pre ++ σ₂.out).length ≤ (p.pre ++ σ₃.out).length := by
      simp only [List.length_append]; have := hpr.length_le; omega
    obtain ⟨τ₁, k₁', hk₁, r₁, hs₁⟩ := ih₁ hc'.2 τ hs (by omega) (by omega)
    obtain ⟨τ₂, k₂', hk₂, r₂, hs₂⟩ := ih₂ hc τ₁ hs₁ hO1 hO2
    refine ⟨τ₂, 1 + b.size + k₁' + k₂', by omega, ?_, hs₂⟩
    have := BigStepB.while_true (rnB_evalB hs.vars hs.arrs b hc'.1 hb) r₁ r₂
    rwa [size_rnB] at this
  | @while_false b c σ₁ hb =>
    intro hc τ hs _ _
    simp only [okC, Bool.and_eq_true] at hc
    refine ⟨τ, 1 + b.size, by omega, ?_, hs⟩
    have := BigStepB.while_false (c := trC p.r c) (rnB_evalB hs.vars hs.arrs b hc.1 hb)
    rwa [size_rnB] at this
  | @read σ x v rest hin =>
    intro hc τ hs _ _
    simp only [okC, decide_eq_true_eq] at hc
    have hv := hp.vtq x hc
    set t := τ.vars "tq" with ht
    have hd : (p.X.take p.L).drop t = v :: rest := by rw [← hs.inp, hin]
    have h0 : (p.X.take p.L)[t]? = some v := by
      have := congrArg (·[0]?) hd
      simpa using this
    have htL : t < (p.X.take p.L).length := (List.getElem?_eq_some_iff.1 h0).1
    have htL' : t < p.L := by simp at htL; omega
    have hvB : v < B := hp.hX v (List.mem_of_getElem? h0)
    have hxv : (τ.arrs "x")[t]? = some v := by
      rw [hs.xa]; rw [List.getElem?_take] at h0; simpa [htL'] using h0
    have hLB := hp.hL
    set τ₁ := τ.setVar (p.r.v x) v with hτ₁
    have e1 : (Expr.get "x" (.var "tq")).evalB B τ = some v :=
      evalB_get (B := B) (evalB_var (B := B) (σ := τ) (x := "tq") (by omega)) hxv hvB
    have ht1 : τ₁.vars "tq" = t := by simp [hτ₁, Ne.symm hv.1, ht]
    have e2 : (Expr.add (.var "tq") (.lit 1)).evalB B τ₁ = some (t + 1) := by
      simp only [Expr.add_def, evalB_bin_iff, evalB_var_iff, evalB_lit_iff, ht1]
      exact ⟨t, 1, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩
    refine ⟨τ₁.setVar "tq" (t + 1), _, ?_, .seq (.assign (x := p.r.v x) e1) (.assign e2), ?_⟩
    · simp
    refine ⟨fun y hy => ?_, fun a ha => by simp [hτ₁, hs.arrs a ha], by simp [hτ₁, hs.xa], ?_,
      ?_, by simp [hτ₁, hs.obl]⟩
    · have hy' := hp.vtq y hy
      simp only [vars_setVar, if_neg hy'.1, hτ₁]
      by_cases hyx : y = x
      · subst hyx; simp
      · have : p.r.v y ≠ p.r.v x := fun h' => hyx (hp.injv y hy x hc h')
        simp [this, hyx, hs.vars y hy]
    · simp only [vars_setVar, if_true]
      rw [← List.drop_drop, hd]; rfl
    · exact (hs.outF.setVar hv.2 _).setVar (by decide) _
  | @write σ e v he =>
    intro hc τ hs hO1 hO2
    simp only [okC] at hc
    have he' := rnE_evalB hs.vars hs.arrs e hc he
    obtain ⟨τ', r', F', fv, fa, fl, fo, fi⟩ := push1_run hs.outF he'
      (by rw [hs.obl]; simp at hO1 ⊢; omega) (by simp at hO2 ⊢; omega)
    obtain ⟨k', hk', r''⟩ := r'
    refine ⟨τ', k', by rw [size_rnE] at hk'; omega, r'', ⟨fun y hy => ?_, fun a ha => ?_, ?_, ?_, ?_, ?_⟩⟩
    · rw [fv _ (hp.vtq y hy).2]; exact hs.vars y hy
    · rw [fa _ (hp.ax a ha).2]; exact hs.arrs a ha
    · rw [fa _ (by decide)]; exact hs.xa
    · rw [fv _ (by decide)]; exact hs.inp
    · simpa [List.append_assoc] using F'
    · rw [fl, hs.obl]

/-- **The tape program in a piece.** -/
theorem trC_run {p : TrP} {B : ℕ} (hp : p.OK B) {c : Com} (hc : okC p.Vs p.As c = true)
    {σ σ' : Env} {K : ℕ} (h : Run B c σ σ' K) {τ : Env} (hs : Sim p σ τ)
    (hO1 : (p.pre ++ σ'.out).length ≤ p.NOB) (hO2 : (p.pre ++ σ'.out).length < B) :
    ∃ τ', Run B (trC p.r c) τ τ' (8 * K) ∧ Sim p σ' τ' := by
  obtain ⟨k, hk, hb⟩ := h
  obtain ⟨τ', k', hk', hb', hs'⟩ := trC_bigStep hp hb hc τ hs hO1 hO2
  exact ⟨τ', ⟨k', by omega, hb'⟩, hs'⟩

theorem trC_noWrite (r : Ren) (c : Com) : (trC r c).NoWrite := by
  induction c <;> simp_all [trC, Com.NoWrite, push1]

theorem trC_noRead (r : Ren) (c : Com) : ¬ (trC r c).reads := by
  induction c <;> simp_all [trC, Com.reads, push1]

/-- The environment of the tape program for a piece environment `τ`:
the scalars are read through the renaming, array `a` is cut to length
`lens a`, the input is `x` from the pointer on, up to `L`. -/
def simEnv (r : Ren) (lens : String → ℕ) (X : List ℕ) (L : ℕ) (τ : Env) : Env :=
  ⟨fun x => τ.vars (r.v x), fun a => (τ.arrs (r.a a)).take (lens a), (X.take L).drop (τ.vars "tq"), []⟩

/-- The tails for `simEnv`. -/
def simPad (r : Ren) (lens : String → ℕ) (τ : Env) (a : String) : List ℕ := (τ.arrs (r.a a)).drop (lens a)

theorem sim_simEnv {r : Ren} {Vs As : List String} {lens : String → ℕ} {L : ℕ} {pre : List ℕ}
    {τ : Env} (hF : Filled "OB" "po" pre τ) :
    Sim ⟨r, Vs, As, simPad r lens τ, τ.arrs "x", L, pre, (τ.arrs "OB").length⟩
      (simEnv r lens (τ.arrs "x") L τ) τ :=
  ⟨fun _ _ => rfl, fun a _ => by simp [simEnv, simPad], rfl, rfl, by simpa [simEnv] using hF, rfl⟩

end Lax185574Proofs.ResolveRam.Glue
