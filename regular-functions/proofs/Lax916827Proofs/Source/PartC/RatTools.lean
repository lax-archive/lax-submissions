/- Tools for building rational functions, used in the proofs of Lemma
`lem:regular-closure-properties` and Claim `claim:conditional` of *Transducers* (M. Bojańczyk).

Three tools are provided.

* `isRationalFun_comp`: rational functions are closed under composition (a
  special case of Theorem `thm:composition-rational-relations`).
* `ctxEval`: a *contextual rewriting*.  The input string is scanned once; at
  every gap an output block is produced, which may depend on the letters
  surrounding the gap and on a "mode", the state reached by a deterministic
  automaton on the whole input string.  Such a function is rational.  Most of
  the rational functions used in Section *Two-way transducers* are of this form: they insert,
  delete or recolour letters, in a way that depends on the global shape of the
  input.
* `isRationalFun_ite`: rational functions are closed under case distinction over
  a regular language.
-/
import Lax916827Proofs.Source.PartC.RatBuild
import Lax132576Proofs.Source.PartB.RationalStatements
import Lax132576Proofs.Source.PartB.RatBimach
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-! ## Composition -/

lemma IsRationalRel.congr {A B : Type} {R R' : List A → List B → Prop}
    (hR : IsRationalRel R) (h : ∀ w v, R w v ↔ R' w v) : IsRationalRel R' := by
  obtain ⟨Q, hQ, M, hM⟩ := hR
  exact ⟨Q, hQ, M, fun w v => ((h w v).symm.trans (hM w v))⟩

/-- Rational functions are closed under composition. -/
theorem isRationalFun_comp {A B C : Type} {f : List A → List B} {g : List B → List C}
    (hf : IsRationalFun f) (hg : IsRationalFun g) : IsRationalFun (fun w => g (f w)) := by
  refine IsRationalRel.congr (rationalRel_comp hf hg) (fun w v => ?_)
  constructor
  · rintro ⟨u, rfl, rfl⟩; rfl
  · rintro rfl; exact ⟨f w, rfl, rfl⟩

/-! ## Contextual rewritings -/

section Ctx

variable {A B Mo : Type}

/-- The output of a contextual rewriting with mode-dependence already resolved:
`ψ prev next` is the block produced at a gap whose left neighbour is `prev` and
whose right neighbour is `next`. -/
def ctxAux (ψ : Option A → Option A → List B) : Option A → List A → List B
  | prev, [] => ψ prev none
  | prev, a :: w => ψ prev (some a) ++ ctxAux ψ (some a) w

@[simp] lemma ctxAux_nil (ψ : Option A → Option A → List B) (prev : Option A) :
    ctxAux ψ prev [] = ψ prev none := rfl

@[simp] lemma ctxAux_cons (ψ : Option A → Option A → List B) (prev : Option A)
    (a : A) (w : List A) :
    ctxAux ψ prev (a :: w) = ψ prev (some a) ++ ctxAux ψ (some a) w := rfl

/-- A contextual rewriting: the mode is the state reached by the deterministic
automaton `(Mo, μ, m₀)` on the whole input string, and at every gap the block
`ψ mode prev next` is produced. -/
def ctxEval (μ : Mo → A → Mo) (m₀ : Mo) (ψ : Mo → Option A → Option A → List B)
    (w : List A) : List B :=
  ctxAux (ψ (strTrans μ w m₀)) none w

/-- The bimachine computing a contextual rewriting. -/
def ctxBim (μ : Mo → A → Mo) (m₀ : Mo) (ψ : Mo → Option A → Option A → List B) :
    Bimachine A B (Option A × Mo) (Option A × (Mo → Mo)) where
  prefixInit := (none, m₀)
  prefixStep := fun p a => (some a, μ p.2 a)
  suffixInit := (none, id)
  suffixStep := fun s a => (some a, fun m => s.2 (μ m a))
  out := fun p s => ψ (s.2 p.2) p.1 s.1

lemma ctxBim_sfx (μ : Mo → A → Mo) (m₀ : Mo) (ψ : Mo → Option A → Option A → List B)
    (w : List A) :
    bmSfx (ctxBim μ m₀ ψ) w = (w.head?, fun m => strTrans μ w m) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [bmSfx_cons, ih]
      simp only [ctxBim]
      refine Prod.ext rfl ?_
      funext m
      simp [strTrans]

lemma ctxBim_evalFrom (μ : Mo → A → Mo) (m₀ : Mo) (ψ : Mo → Option A → Option A → List B)
    (prev : Option A) (m : Mo) (w : List A) :
    (ctxBim μ m₀ ψ).evalFrom (prev, m) w = ctxAux (ψ (strTrans μ w m)) prev w := by
  induction w generalizing prev m with
  | nil => simp [ctxBim, strTrans]
  | cons a w ih =>
      rw [Bimachine.evalFrom_cons', ctxBim_sfx]
      rw [show (ctxBim μ m₀ ψ).prefixStep (prev, m) a = (some a, μ m a) from rfl]
      rw [ih]
      rw [show (ctxBim μ m₀ ψ).out (prev, m)
          ((a :: w).head?, fun m' => strTrans μ (a :: w) m')
          = ψ (strTrans μ (a :: w) m) prev (some a) from rfl]
      have hs : strTrans μ w (μ m a) = strTrans μ (a :: w) m := by simp [strTrans]
      rw [hs, ctxAux_cons]

lemma ctxBim_eval (μ : Mo → A → Mo) (m₀ : Mo) (ψ : Mo → Option A → Option A → List B)
    (w : List A) : (ctxBim μ m₀ ψ).eval w = ctxEval μ m₀ ψ w := by
  rw [Bimachine.eval_eq_evalFrom]
  exact ctxBim_evalFrom μ m₀ ψ none m₀ w

/-- A contextual rewriting is a rational function. -/
theorem isRationalFun_ctxEval [Finite A] [Finite B] [Finite Mo]
    (μ : Mo → A → Mo) (m₀ : Mo) (ψ : Mo → Option A → Option A → List B) :
    IsRationalFun (ctxEval μ m₀ ψ) :=
  isRationalFun_of_bimachine (ctxBim μ m₀ ψ) (ctxBim_eval μ m₀ ψ)

end Ctx

/-! ## Case distinction over a regular language -/

section Ite

variable {A B σ Pf Sf Pg Sg : Type}

/-- The bimachine that runs the bimachine `Mf` or the bimachine `Mg`, according
to the state reached by the deterministic automaton `(σ, μ, ·)` on the whole
input string. -/
def iteBim (μ : σ → A → σ) (s₀ : σ) (acc : σ → Prop) [DecidablePred acc]
    (Mf : Bimachine A B Pf Sf) (Mg : Bimachine A B Pg Sg) :
    Bimachine A B (Pf × Pg × σ) (Sf × Sg × (σ → σ)) where
  prefixInit := (Mf.prefixInit, Mg.prefixInit, s₀)
  prefixStep := fun p a => (Mf.prefixStep p.1 a, Mg.prefixStep p.2.1 a, μ p.2.2 a)
  suffixInit := (Mf.suffixInit, Mg.suffixInit, id)
  suffixStep := fun s a => (Mf.suffixStep s.1 a, Mg.suffixStep s.2.1 a, fun q => s.2.2 (μ q a))
  out := fun p s => if acc (s.2.2 p.2.2) then Mf.out p.1 s.1 else Mg.out p.2.1 s.2.1

lemma iteBim_sfx (μ : σ → A → σ) (s₀ : σ) (acc : σ → Prop) [DecidablePred acc]
    (Mf : Bimachine A B Pf Sf) (Mg : Bimachine A B Pg Sg) (w : List A) :
    bmSfx (iteBim μ s₀ acc Mf Mg) w = (bmSfx Mf w, bmSfx Mg w, fun q => strTrans μ w q) := by
  induction w with
  | nil => rfl
  | cons a w ih =>
      rw [bmSfx_cons, ih, bmSfx_cons, bmSfx_cons]
      simp only [iteBim]
      refine Prod.ext rfl (Prod.ext rfl ?_)
      funext q
      simp [strTrans]

lemma iteBim_evalFrom (μ : σ → A → σ) (s₀ : σ) (acc : σ → Prop) [DecidablePred acc]
    (Mf : Bimachine A B Pf Sf) (Mg : Bimachine A B Pg Sg)
    (p : Pf) (q : Pg) (s : σ) (w : List A) :
    (iteBim μ s₀ acc Mf Mg).evalFrom (p, q, s) w =
      if acc (strTrans μ w s) then Mf.evalFrom p w else Mg.evalFrom q w := by
  induction w generalizing p q s with
  | nil => simp [iteBim, strTrans]
  | cons a w ih =>
      rw [Bimachine.evalFrom_cons', iteBim_sfx]
      rw [show (iteBim μ s₀ acc Mf Mg).prefixStep (p, q, s) a
          = (Mf.prefixStep p a, Mg.prefixStep q a, μ s a) from rfl]
      rw [ih]
      rw [show (iteBim μ s₀ acc Mf Mg).out (p, q, s)
            (bmSfx Mf (a :: w), bmSfx Mg (a :: w), fun q' => strTrans μ (a :: w) q')
          = (if acc (strTrans μ (a :: w) s) then Mf.out p (bmSfx Mf (a :: w))
              else Mg.out q (bmSfx Mg (a :: w))) from rfl]
      rw [Bimachine.evalFrom_cons' Mf, Bimachine.evalFrom_cons' Mg]
      have hs : strTrans μ w (μ s a) = strTrans μ (a :: w) s := by simp [strTrans]
      rw [hs]
      by_cases h : acc (strTrans μ (a :: w) s) <;> simp [h]

/-- Rational functions are closed under case distinction over a language
recognised by a deterministic automaton. -/
theorem isRationalFun_ite [Finite A] [Finite B] [Finite σ]
    (μ : σ → A → σ) (s₀ : σ) (acc : σ → Prop) [DecidablePred acc]
    {f g : List A → List B} (hf : IsRationalFun f) (hg : IsRationalFun g) :
    IsRationalFun (fun w => if acc (strTrans μ w s₀) then f w else g w) := by
  obtain ⟨Pf, Sf, hPf, hSf, Mf, hMf⟩ := isBimachine_of_rationalFun hf
  obtain ⟨Pg, Sg, hPg, hSg, Mg, hMg⟩ := isBimachine_of_rationalFun hg
  haveI := hPf; haveI := hSf; haveI := hPg; haveI := hSg
  refine isRationalFun_of_bimachine (iteBim μ s₀ acc Mf Mg) (fun w => ?_)
  rw [Bimachine.eval_eq_evalFrom]
  have h := iteBim_evalFrom μ s₀ acc Mf Mg Mf.prefixInit Mg.prefixInit s₀ w
  rw [show ((iteBim μ s₀ acc Mf Mg).prefixInit) = (Mf.prefixInit, Mg.prefixInit, s₀) from rfl, h,
    ← Bimachine.eval_eq_evalFrom, ← Bimachine.eval_eq_evalFrom, hMf, hMg]

/-- Rational functions are closed under case distinction over a regular
language. -/
theorem isRationalFun_ite_lang [Finite A] [Finite B] {L : Language A} (hL : L.IsRegular)
    {f g : List A → List B} (hf : IsRationalFun f) (hg : IsRationalFun g)
    [DecidablePred (· ∈ L)] :
    IsRationalFun (fun w => if w ∈ L then f w else g w) := by
  classical
  obtain ⟨σ, hσ, D, hD⟩ := hL
  haveI : Finite σ := hσ.finite
  have key : IsRationalFun (fun w => if D.evalFrom D.start w ∈ D.accept then f w else g w) :=
    isRationalFun_ite D.step D.start (fun s => s ∈ D.accept) hf hg
  refine IsRationalRel.congr key (fun w v => ?_)
  have hmem : ∀ w : List A, (w ∈ L) = (D.evalFrom D.start w ∈ D.accept) := by
    intro w
    rw [← hD]
    rfl
  simp only [hmem]

end Ite

/-! ## Two rational functions built with `ctxEval` -/

section Small

variable {A B : Type}

/-- A constant function is rational. -/
theorem isRationalFun_const [Finite A] [Finite B] (c : List B) :
    IsRationalFun (fun _ : List A => c) := by
  have hzero : ∀ (w : List A) (a : A),
      ctxAux (fun (prev : Option A) (_ : Option A) =>
        match prev with | none => c | some _ => ([] : List B)) (some a) w = [] := by
    intro w
    induction w with
    | nil => intro a; rfl
    | cons b w ih => intro a; simpa using ih b
  have h : (fun _ : List A => c) = ctxEval (fun (_ : Unit) (_ : A) => ()) ()
      (fun _ prev _ => match prev with | none => c | some _ => ([] : List B)) := by
    funext w
    rw [ctxEval]
    cases w with
    | nil => simp
    | cons a w => simp [hzero w a]
  rw [h]
  exact isRationalFun_ctxEval _ _ _

/-- Prepending a fixed letter is a rational function. -/
theorem isRationalFun_cons [Finite B] (c : B) :
    IsRationalFun (fun w : List B => c :: w) := by
  set ψ : Unit → Option B → Option B → List B := fun _ prev next =>
    (match prev with | none => [c] | some _ => []) ++
      (match next with | none => [] | some b => [b]) with hψ
  have hid : ∀ (w : List B) (x : B), ctxAux (ψ ()) (some x) w = w := by
    intro w
    induction w with
    | nil => intro x; simp [hψ]
    | cons b w ih => intro x; simpa [hψ] using ih b
  have h : ∀ w : List B, ctxEval (fun (_ : Unit) (_ : B) => ()) () ψ w = c :: w := by
    intro w
    cases w with
    | nil => simp [ctxEval, hψ]
    | cons b w =>
        have hstep : ctxEval (fun (_ : Unit) (_ : B) => ()) () ψ (b :: w)
            = ψ () none (some b) ++ ctxAux (ψ ()) (some b) w := rfl
        rw [hstep, hid w b]
        simp [hψ]
  rw [show (fun w : List B => c :: w) = ctxEval (fun (_ : Unit) (_ : B) => ()) () ψ from
    funext (fun w => (h w).symm)]
  exact isRationalFun_ctxEval _ _ _

end Small

end Lax916827Proofs.Transducers
