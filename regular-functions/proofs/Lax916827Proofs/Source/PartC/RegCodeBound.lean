/- The equivalence bound for codes of two-way transducers (Theorem
`thm:decidable-equivalence-regular` of *Transducers*, M. Bojańczyk).

This file proves the *mathematical* content of the hypothesis
`Transducers.EffectiveTwoWayBound` of `RequestProject/PartC/EffectiveReg.lean`:
for every pair of codes describing total two-way transducers there is a length
bound `n` such that agreeing on all inputs of length at most `n` forces the two
coded transducers to compute the same relation
(`Transducers.exists_twoWayCode_bound`).  Only the *computability* of a bound as
a function of the two codes is left as a hypothesis there.

The proof is the book's: a coded two-way transducer computes a regular function (Theorem
`thm:2dfa-decomposition-into-primes`, here in the form `Transducers.isRegularFun_of_isTwoWay`), and
two regular functions over finite alphabets agree everywhere as soon as they agree on the short
inputs (`Transducers.regularFun_eq_of_short`, the conclusion of the reduction to weighted automata
over `ℚ` in `RequestProject/PartC/WeightedRegClosure.lean`).

The work in between is bookkeeping on codes.  A code describes a transducer over the *infinite*
alphabet `ℕ` with the *infinite* state set `ℕ`, whereas Theorem `thm:2dfa-decomposition-into-primes`
speaks about finite alphabets and finitely many states; but a code is a finite table, so only
finitely many letters, output letters and states occur in it, and everything outside is inert.
`finAut` is the transducer of a code read over a finite alphabet `L` of input letters, a finite
alphabet `O` of output letters and the finite set of states occurring in the code, and `decCfg`
decodes its configurations back to configurations of the coded transducer; the two runs correspond
step by step. -/
import Lax916827Proofs.Source.PartC.RegCodeSan
import Lax916827Proofs.Source.PartC.SnakeReg
import Lax916827Proofs.Source.PartC.WeightedRegClosure
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

variable {A B Q : Type}

/-- A run that stops where no step is possible is unique: a two-way transducer
is deterministic. -/
lemma reaches_unique {M : TwoWay A B Q} {x z z' : Cfg A Q} {o o' : List B}
    (h : M.Reaches x o z) (h' : M.Reaches x o' z') (hz : M.stepCfg z = none)
    (hz' : M.stepCfg z' = none) : o = o' ∧ z = z' := by
  induction h generalizing o' z' with
  | refl x =>
      cases h' with
      | refl _ => exact ⟨rfl, rfl⟩
      | step hstep _ => rw [hz] at hstep; exact absurd hstep (by simp)
  | @step x x₁ x₂ o₁ o₂ hstep _ ih =>
      cases h' with
      | refl _ => rw [hz'] at hstep; exact absurd hstep (by simp)
      | @step _ x₁' x₂' o₁' o₂' hstep' hrest' =>
          rw [hstep] at hstep'
          obtain ⟨heq₁, heq₂⟩ : o₁ = o₁' ∧ x₁ = x₁' := by
            simpa [Prod.ext_iff] using Option.some.inj hstep'
          subst heq₁; subst heq₂
          obtain ⟨h1, h2⟩ := ih hrest' hz hz'
          exact ⟨by rw [h1], h2⟩

/-- The output of a two-way transducer on an input is unique. -/
lemma computes_unique {M : TwoWay A B Q} {w : List A} {v v' : List B}
    (h : M.Computes w v) (h' : M.Computes w v') : v = v' :=
  (reaches_unique h h' (by simp [stepCfg]) (by simp [stepCfg])).1

end TwoWay

namespace RegDec

/-! ## The letters, output letters and states of a code -/

/-- The output letters occurring in the transition table of a code, together
with `0`. -/
def outAlph (c : TwoWayCode) : List ℕ :=
  0 :: c.flatMap (fun t => Sum.elim id (fun z : ℕ × List ℕ × Bool => z.2.1) t.2)

/-- The states occurring in the transition table of a code, together with the
initial state `0`. -/
def stAlph (c : TwoWayCode) : List ℕ :=
  0 :: c.flatMap (fun t => t.1.2.1 :: Sum.elim (fun _ : List ℕ => []) (fun z : ℕ × List ℕ × Bool =>
    [z.1]) t.2)

@[simp] lemma zero_mem_outAlph (c : TwoWayCode) : 0 ∈ outAlph c := List.mem_cons_self

@[simp] lemma zero_mem_stAlph (c : TwoWayCode) : 0 ∈ stAlph c := List.mem_cons_self

lemma mem_of_lookup {c : TwoWayCode} {k} {x} (h : c.lookup k = some x) : (k, x) ∈ c := by
  obtain ⟨l₁, l₂, hc, -⟩ := List.lookup_eq_some_iff.1 h
  rw [hc]
  simp

lemma out_mem_outAlph_inl {c : TwoWayCode} {k} {o : List ℕ}
    (h : c.lookup k = some (Sum.inl o)) {y : ℕ} (hy : y ∈ o) : y ∈ outAlph c := by
  refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨(k, Sum.inl o), mem_of_lookup h, ?_⟩)
  simpa using hy

lemma out_mem_outAlph_inr {c : TwoWayCode} {k} {q : ℕ} {o : List ℕ} {d : Bool}
    (h : c.lookup k = some (Sum.inr (q, o, d))) {y : ℕ} (hy : y ∈ o) : y ∈ outAlph c := by
  refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨(k, Sum.inr (q, o, d)), mem_of_lookup h, ?_⟩)
  simpa using hy

lemma state_mem_stAlph {c : TwoWayCode} {k} {q : ℕ} {o : List ℕ} {d : Bool}
    (h : c.lookup k = some (Sum.inr (q, o, d))) : q ∈ stAlph c := by
  refine List.mem_cons_of_mem _ (List.mem_flatMap.2 ⟨(k, Sum.inr (q, o, d)), mem_of_lookup h, ?_⟩)
  simp

/-! ## The coded transducer over finite alphabets -/

/-- The states of the coded transducer that are actually used. -/
abbrev StT (c : TwoWayCode) := {q : ℕ // q ∈ stAlph c}

/-- A letter of a finite alphabet given as a list. -/
abbrev Ltr (L : List ℕ) := {x : ℕ // x ∈ L}

/-- The encoding of a state occurring in the code. -/
def encSt (c : TwoWayCode) (q : ℕ) : StT c :=
  if h : q ∈ stAlph c then ⟨q, h⟩ else ⟨0, zero_mem_stAlph c⟩

/-- The encoding of an output letter of the code. -/
def encOut (O : List ℕ) (hO : 0 ∈ O) (y : ℕ) : Ltr O :=
  if h : y ∈ O then ⟨y, h⟩ else ⟨0, hO⟩

@[simp] lemma encSt_val {c : TwoWayCode} {q : ℕ} (h : q ∈ stAlph c) : (encSt c q).val = q := by
  simp [encSt, h]

@[simp] lemma encOut_val {O : List ℕ} {hO : 0 ∈ O} {y : ℕ} (h : y ∈ O) :
    (encOut O hO y).val = y := by
  simp [encOut, h]

lemma map_encOut_val {O : List ℕ} {hO : 0 ∈ O} {o : List ℕ} (h : ∀ y ∈ o, y ∈ O) :
    (o.map (encOut O hO)).map Subtype.val = o := by
  induction o with
  | nil => rfl
  | cons y t ih =>
      simp only [List.map_cons, List.cons.injEq]
      exact ⟨encOut_val (h y (by simp)), ih (fun z hz => h z (by simp [hz]))⟩

/-- The transducer described by the code `c`, read over the input alphabet `L`
and the output alphabet `O`, with the states occurring in `c`. -/
def finAut (c : TwoWayCode) (L O : List ℕ) (hO : 0 ∈ O) : TwoWay (Ltr L) (Ltr O) (StT c) where
  init := encSt c 0
  step := fun l q r =>
    match c.lookup (l.map Subtype.val, q.val, r.map Subtype.val) with
    | some (Sum.inl o) => Sum.inl (o.map (encOut O hO))
    | some (Sum.inr (q', o, d)) => Sum.inr (encSt c q', o.map (encOut O hO), d)
    | none => Sum.inl []

/-- The decoding of a configuration of `finAut` into a configuration of the
coded transducer. -/
def decCfg (c : TwoWayCode) (L : List ℕ) : Cfg (Ltr L) (StT c) → Cfg ℕ ℕ
  | Cfg.conf u q v => Cfg.conf (u.map Subtype.val) q.val (v.map Subtype.val)
  | Cfg.halt => Cfg.halt

@[simp] lemma decCfg_halt (c : TwoWayCode) (L : List ℕ) : decCfg c L Cfg.halt = Cfg.halt := rfl

lemma eq_halt_of_decCfg_eq_halt {c : TwoWayCode} {L : List ℕ} {x : Cfg (Ltr L) (StT c)}
    (h : decCfg c L x = Cfg.halt) : x = Cfg.halt := by
  cases x with
  | halt => rfl
  | conf u q v => simp [decCfg] at h

/-- The transitions of `finAut c L O` decode to the transitions of the coded
transducer. -/
lemma step_finAut {c : TwoWayCode} {L O : List ℕ} (hO : 0 ∈ O)
    (hsub : ∀ y ∈ outAlph c, y ∈ O) (l r : Option (Ltr L)) (q : StT c) :
    (twoWayCodeAut c).step (l.map Subtype.val) q.val (r.map Subtype.val) =
      Sum.elim (fun o : List (Ltr O) => Sum.inl (o.map Subtype.val))
        (fun z : StT c × List (Ltr O) × Bool =>
          Sum.inr (z.1.val, z.2.1.map Subtype.val, z.2.2))
        ((finAut c L O hO).step l q r) := by
  rcases hlk : c.lookup (l.map Subtype.val, q.val, r.map Subtype.val) with _ | x
  · simp only [twoWayCodeAut, finAut, hlk, Sum.elim_inl, List.map_nil]
  · cases x with
    | inl o =>
        have ho : ∀ y ∈ o, y ∈ O := fun y hy => hsub y (out_mem_outAlph_inl hlk hy)
        simp only [twoWayCodeAut, finAut, hlk, Sum.elim_inl, map_encOut_val ho]
    | inr z =>
        obtain ⟨q', o, d⟩ := z
        have ho : ∀ y ∈ o, y ∈ O := fun y hy => hsub y (out_mem_outAlph_inr hlk hy)
        simp only [twoWayCodeAut, finAut, hlk, Sum.elim_inr, map_encOut_val ho,
          encSt_val (state_mem_stAlph hlk)]

/-- One step of `finAut c L O` is one step of the coded transducer. -/
lemma stepCfg_decCfg {c : TwoWayCode} {L O : List ℕ} (hO : 0 ∈ O)
    (hsub : ∀ y ∈ outAlph c, y ∈ O) (x : Cfg (Ltr L) (StT c)) :
    (twoWayCodeAut c).stepCfg (decCfg c L x) =
      (((finAut c L O hO).stepCfg x).map
        (fun p => (p.1.map Subtype.val, decCfg c L p.2))) := by
  cases x with
  | halt => simp [decCfg, TwoWay.stepCfg]
  | conf u q v =>
      have hu : (u.map Subtype.val).getLast? = u.getLast?.map Subtype.val := List.getLast?_map ..
      have hv : (v.map Subtype.val).head? = v.head?.map Subtype.val := List.head?_map ..
      simp only [decCfg, TwoWay.stepCfg, hu, hv, step_finAut hO hsub]
      rcases hstep : (finAut c L O hO).step u.getLast? q v.head? with o | ⟨q', o, dir⟩
      · simp
      · cases dir with
        | true =>
            cases v with
            | nil => simp
            | cons a v' => simp
        | false =>
            cases hgl : u.getLast? with
            | none => simp
            | some a =>
                simp only [List.map_cons, Sum.elim_inr, Option.map_some]
                rw [List.map_dropLast]

lemma reaches_decCfg_of_reaches {c : TwoWayCode} {L O : List ℕ} (hO : 0 ∈ O)
    (hsub : ∀ y ∈ outAlph c, y ∈ O) {x y : Cfg (Ltr L) (StT c)} {o : List (Ltr O)}
    (h : (finAut c L O hO).Reaches x o y) :
    (twoWayCodeAut c).Reaches (decCfg c L x) (o.map Subtype.val) (decCfg c L y) := by
  induction h with
  | refl x => exact TwoWay.Reaches.refl _
  | @step x x₁ x₂ o₁ o₂ hstep _ ih =>
      rw [List.map_append]
      refine TwoWay.Reaches.step ?_ ih
      rw [stepCfg_decCfg hO hsub, hstep]
      rfl

lemma reaches_of_reaches_decCfg {c : TwoWayCode} {L O : List ℕ} (hO : 0 ∈ O)
    (hsub : ∀ y ∈ outAlph c, y ∈ O) {x : Cfg (Ltr L) (StT c)} {z : Cfg ℕ ℕ} {o : List ℕ}
    (h : (twoWayCodeAut c).Reaches (decCfg c L x) o z) :
    ∃ (y : Cfg (Ltr L) (StT c)) (o' : List (Ltr O)),
      z = decCfg c L y ∧ o = o'.map Subtype.val ∧ (finAut c L O hO).Reaches x o' y := by
  generalize hx : decCfg c L x = x₀ at h
  induction h generalizing x with
  | refl x₀ => exact ⟨x, [], hx.symm, rfl, TwoWay.Reaches.refl _⟩
  | @step z₀ z₁ z₂ o₁ o₂ hstep _ ih =>
      subst hx
      rw [stepCfg_decCfg hO hsub] at hstep
      rcases hx' : (finAut c L O hO).stepCfg x with _ | ⟨o', x'⟩
      · rw [hx'] at hstep; simp at hstep
      · rw [hx'] at hstep
        simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hstep
        obtain ⟨ho, hz⟩ := hstep
        obtain ⟨y, o'', hy, ho2, hreach⟩ := ih (x := x') hz
        exact ⟨y, o' ++ o'', hy, by rw [← ho, ho2, List.map_append],
          TwoWay.Reaches.step hx' hreach⟩

/-- The initial configuration of `finAut c L O` decodes to the initial
configuration of the coded transducer. -/
lemma decCfg_init (c : TwoWayCode) (L O : List ℕ) (hO : 0 ∈ O) (w : List (Ltr L)) :
    decCfg c L (Cfg.conf [] (finAut c L O hO).init w) =
      Cfg.conf [] (twoWayCodeAut c).init (w.map Subtype.val) := by
  simp [decCfg, finAut, twoWayCodeAut, encSt]

/-- The coded transducer computes, on the strings over `L` with outputs over
`O`, exactly what `finAut c L O` computes. -/
theorem computes_finAut_iff {c : TwoWayCode} {L O : List ℕ} (hO : 0 ∈ O)
    (hsub : ∀ y ∈ outAlph c, y ∈ O) (w : List (Ltr L)) (v : List (Ltr O)) :
    (finAut c L O hO).Computes w v ↔
      twoWayCodeRel c (w.map Subtype.val) (v.map Subtype.val) := by
  constructor
  · intro h
    have hr := reaches_decCfg_of_reaches hO hsub h
    rw [decCfg_init] at hr
    exact hr
  · intro h
    have h' : (twoWayCodeAut c).Reaches (decCfg c L (Cfg.conf [] (finAut c L O hO).init w))
        (v.map Subtype.val) Cfg.halt := by rw [decCfg_init]; exact h
    obtain ⟨y, o', hy, ho, hreach⟩ := reaches_of_reaches_decCfg hO hsub h'
    have hyh : y = Cfg.halt := eq_halt_of_decCfg_eq_halt hy.symm
    subst hyh
    have hov : o' = v := List.map_injective_iff.2 Subtype.val_injective ho.symm
    subst hov
    exact hreach

/-! ## The function computed by a coded transducer over a finite alphabet -/

lemma exists_computes_finAut {c : TwoWayCode} {L O : List ℕ} (hO : 0 ∈ O)
    (hsub : ∀ y ∈ outAlph c, y ∈ O) (hc : TwoWayCodeTotal c) (w : List (Ltr L)) :
    ∃ v : List (Ltr O), (finAut c L O hO).Computes w v := by
  obtain ⟨v, hv⟩ := hc (w.map Subtype.val)
  have h' : (twoWayCodeAut c).Reaches (decCfg c L (Cfg.conf [] (finAut c L O hO).init w))
      v Cfg.halt := by rw [decCfg_init]; exact hv
  obtain ⟨y, o', hy, -, hreach⟩ := reaches_of_reaches_decCfg hO hsub h'
  have hyh : y = Cfg.halt := eq_halt_of_decCfg_eq_halt hy.symm
  subst hyh
  exact ⟨o', hreach⟩

open Classical in
/-- The function computed by a coded transducer, read over the alphabets `L`
and `O`. -/
noncomputable def finFun (c : TwoWayCode) (L O : List ℕ) (hO : 0 ∈ O)
    (hsub : ∀ y ∈ outAlph c, y ∈ O) (hc : TwoWayCodeTotal c) :
    List (Ltr L) → List (Ltr O) :=
  fun w => (exists_computes_finAut hO hsub hc w).choose

lemma finFun_computes {c : TwoWayCode} {L O : List ℕ} (hO : 0 ∈ O)
    (hsub : ∀ y ∈ outAlph c, y ∈ O) (hc : TwoWayCodeTotal c) (w : List (Ltr L)) :
    (finAut c L O hO).Computes w (finFun c L O hO hsub hc w) :=
  (exists_computes_finAut hO hsub hc w).choose_spec

lemma isRegularFun_finFun {c : TwoWayCode} {L O : List ℕ} (hO : 0 ∈ O)
    (hsub : ∀ y ∈ outAlph c, y ∈ O) (hc : TwoWayCodeTotal c) :
    IsRegularFun (finFun c L O hO hsub hc) :=
  isRegularFun_of_isTwoWay
    ⟨StT c, inferInstance, finAut c L O hO, finFun_computes hO hsub hc⟩

/-! ## The bound -/

/-- **The equivalence bound of Theorem `thm:decidable-equivalence-regular` exists.**  For two codes
describing total two-way transducers there is a length `n` such that the two
codes describe the same relation as soon as they describe the same relation on
the inputs of length at most `n`.

This is the mathematical content of the hypothesis
`Transducers.EffectiveTwoWayBound`; only the computability of `n` as a function
of the two codes is assumed there. -/
theorem exists_bound (c₁ c₂ : TwoWayCode) (h₁ : TwoWayCodeTotal c₁)
    (h₂ : TwoWayCodeTotal c₂) :
    ∃ n : ℕ, (∀ w : List ℕ, w.length ≤ n → twoWayCodeRel c₁ w = twoWayCodeRel c₂ w) →
      twoWayCodeRel c₁ = twoWayCodeRel c₂ := by
  classical
  set L := testAlphabet (c₁, c₂) with hLdef
  set O := outAlph c₁ ++ outAlph c₂ with hOdef
  have hO : 0 ∈ O := List.mem_append.2 (Or.inl (zero_mem_outAlph c₁))
  have hs₁ : ∀ y ∈ outAlph c₁, y ∈ O := fun y hy => List.mem_append.2 (Or.inl hy)
  have hs₂ : ∀ y ∈ outAlph c₂, y ∈ O := fun y hy => List.mem_append.2 (Or.inr hy)
  obtain ⟨n, hn⟩ := regularFun_eq_of_short (isRegularFun_finFun (L := L) hO hs₁ h₁)
    (isRegularFun_finFun (L := L) hO hs₂ h₂)
  refine ⟨n, fun hshort => ?_⟩
  -- the two coded transducers compute the same function over the finite alphabets
  have hf : finFun c₁ L O hO hs₁ h₁ = finFun c₂ L O hO hs₂ h₂ := by
    refine hn (fun w hw => ?_)
    have hlen : (w.map Subtype.val).length ≤ n := by simpa using hw
    have heq := hshort (w.map Subtype.val) hlen
    have hc1 : twoWayCodeRel c₁ (w.map Subtype.val)
        ((finFun c₁ L O hO hs₁ h₁ w).map Subtype.val) :=
      (computes_finAut_iff hO hs₁ w _).1 (finFun_computes hO hs₁ h₁ w)
    have hc2 : twoWayCodeRel c₂ (w.map Subtype.val)
        ((finFun c₁ L O hO hs₁ h₁ w).map Subtype.val) := heq ▸ hc1
    exact TwoWay.computes_unique ((computes_finAut_iff hO hs₂ w _).2 hc2)
      (finFun_computes hO hs₂ h₂ w)
  -- hence they compute the same relation on the strings over `L` ...
  have key : ∀ (w : List (Ltr L)) (v : List ℕ),
      twoWayCodeRel c₁ (w.map Subtype.val) v ↔ twoWayCodeRel c₂ (w.map Subtype.val) v := by
    intro w v
    have hc1 : twoWayCodeRel c₁ (w.map Subtype.val)
        ((finFun c₁ L O hO hs₁ h₁ w).map Subtype.val) :=
      (computes_finAut_iff hO hs₁ w _).1 (finFun_computes hO hs₁ h₁ w)
    have hc2 : twoWayCodeRel c₂ (w.map Subtype.val)
        ((finFun c₁ L O hO hs₁ h₁ w).map Subtype.val) := by
      rw [hf]
      exact (computes_finAut_iff hO hs₂ w _).1 (finFun_computes hO hs₂ h₂ w)
    constructor
    · intro h
      have : v = (finFun c₁ L O hO hs₁ h₁ w).map Subtype.val :=
        TwoWay.computes_unique h hc1
      rw [this]
      exact hc2
    · intro h
      have : v = (finFun c₁ L O hO hs₁ h₁ w).map Subtype.val :=
        TwoWay.computes_unique h hc2
      rw [this]
      exact hc1
  -- ... and therefore, by blindness to the letters outside the two codes, everywhere
  funext w v
  have hmem : ∀ x ∈ w.map (sanLetter (c₁, c₂)), x ∈ L := by
    intro x hx
    obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx
    exact sanLetter_mem_testAlphabet (c₁, c₂) y
  set w' : List (Ltr L) := (w.map (sanLetter (c₁, c₂))).attachWith (· ∈ L) hmem with hw'
  have hval : w'.map Subtype.val = w.map (sanLetter (c₁, c₂)) := by simp [hw']
  have e₁ := twoWayCodeRel_map (blind_sanLetter_left (c₁, c₂)) w v
  have e₂ := twoWayCodeRel_map (blind_sanLetter_right (c₁, c₂)) w v
  have hkey := key w' v
  rw [hval] at hkey
  simp only [eq_iff_iff]
  rw [← e₁, ← e₂]
  exact hkey

end RegDec

/-- **The equivalence bound of Theorem `thm:decidable-equivalence-regular` exists** (see
`Transducers.RegDec.exists_bound`). -/
theorem exists_twoWayCode_bound (c₁ c₂ : TwoWayCode) (h₁ : TwoWayCodeTotal c₁)
    (h₂ : TwoWayCodeTotal c₂) :
    ∃ n : ℕ, (∀ w : List ℕ, w.length ≤ n → twoWayCodeRel c₁ w = twoWayCodeRel c₂ w) →
      twoWayCodeRel c₁ = twoWayCodeRel c₂ :=
  RegDec.exists_bound c₁ c₂ h₁ h₂

end Lax916827Proofs.Transducers
