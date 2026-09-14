/-
The rational function described by a code, over the finite alphabets that the
code can see.

The decidability statements of Part B speak about codes, whose alphabet is the infinite set `ℕ`,
while the machine independent characterisations of Section *Machine independent characterisations*
are about functions over *finite* alphabets.  This file bridges the two.  A code has finitely many
transitions, so it reads only the letters of `codeAlphabet c` and writes only the letters of
`codeOutAlphabet c`; the corresponding subtypes `InA c` and `OutA c` of `ℕ` are finite (a spurious
letter `0` is added to the output alphabet so that it is nonempty, which is convenient when a
machine over `ℕ` has to be turned into a machine over `OutA c`).  Under the promise that the code
describes a total function on the strings over its alphabet, that function is `codeFun c : List (InA
c) → List (OutA c)`; it is rational, and it is computed by a Mealy machine exactly when the property
appearing in Theorem `thm:decide-if-mealy` holds. -/
import Lax132576Proofs.Source.PartB.PrefixCodes
import Lax132576Proofs.Source.PartB.RationalStatements
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers
namespace CodeRat

open LabAut

/-! ## The finite alphabets and the finite state space of a code -/

/-- The letters that the code can read. -/
def InA (c : RelCode) : Type := {x : ℕ // x ∈ codeAlphabet c}

/-- The letters that the code can write, together with the letter `0`. -/
def OutA (c : RelCode) : Type := {x : ℕ // x ∈ (0 : ℕ) :: codeOutAlphabet c}

/-- The states occurring in the code. -/
def stAll (c : RelCode) : List ℕ :=
  c.2.1 ++ c.2.2 ++ c.1.map (fun t => t.1) ++ c.1.map (fun t => t.2.2.2)

/-- The states of the code. -/
def StQ (c : RelCode) : Type := {q : ℕ // q ∈ stAll c}

instance instFiniteInA (c : RelCode) : Finite (InA c) := by
  show Finite {x : ℕ // x ∈ codeAlphabet c}
  infer_instance

instance instFiniteOutA (c : RelCode) : Finite (OutA c) := by
  show Finite {x : ℕ // x ∈ (0 : ℕ) :: codeOutAlphabet c}
  infer_instance

instance instFiniteStQ (c : RelCode) : Finite (StQ c) := by
  show Finite {q : ℕ // q ∈ stAll c}
  infer_instance

/-! ### Lifting strings over `ℕ` to strings over a subtype -/

/-- A string all of whose letters occur in a list `s` is the image of a string
over the subtype of the letters of `s`. -/
lemma exists_lift {s : List ℕ} : ∀ {l : List ℕ}, (∀ x ∈ l, x ∈ s) →
    ∃ l' : List {x : ℕ // x ∈ s}, l = l'.map Subtype.val := by
  intro l
  induction l with
  | nil => exact fun _ => ⟨[], rfl⟩
  | cons a l ih =>
      intro h
      obtain ⟨l', hl'⟩ := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
      exact ⟨⟨a, h a (List.mem_cons_self ..)⟩ :: l', by simp [hl']⟩

lemma map_val_injective {s : List ℕ} :
    Function.Injective (fun l : List {x : ℕ // x ∈ s} => l.map Subtype.val) :=
  List.map_injective_iff.2 Subtype.val_injective

/-- A prefix that survives an injective map was already a prefix. -/
lemma prefix_of_map_prefix {α β : Type} {f : α → β} (hf : Function.Injective f)
    {l₁ l₂ : List α} (h : l₁.map f <+: l₂.map f) : l₁ <+: l₂ := by
  have h1 : l₁.map f = (l₂.map f).take (l₁.map f).length := List.prefix_iff_eq_take.1 h
  rw [List.length_map, ← List.map_take] at h1
  have h2 : l₁ = l₂.take l₁.length := List.map_injective_iff.2 hf h1
  exact h2 ▸ List.take_prefix _ _

/-! ### The states occurring in a code -/

lemma init_mem_stAll {c : RelCode} {q : ℕ} (h : q ∈ c.2.1) : q ∈ stAll c := by
  simp only [stAll, List.mem_append]
  exact Or.inl (Or.inl (Or.inl h))

lemma final_mem_stAll {c : RelCode} {p : ℕ} (h : p ∈ c.2.2) : p ∈ stAll c := by
  simp only [stAll, List.mem_append]
  exact Or.inl (Or.inl (Or.inr h))

lemma src_mem_stAll {c : RelCode} {t : ℕ × List ℕ × List ℕ × ℕ} (h : t ∈ c.1) :
    t.1 ∈ stAll c := by
  simp only [stAll, List.mem_append]
  exact Or.inl (Or.inr (List.mem_map.2 ⟨t, h, rfl⟩))

lemma tgt_mem_stAll {c : RelCode} {t : ℕ × List ℕ × List ℕ × ℕ} (h : t ∈ c.1) :
    t.2.2.2 ∈ stAll c := by
  simp only [stAll, List.mem_append]
  exact Or.inr (List.mem_map.2 ⟨t, h, rfl⟩)

lemma trans_input_mem {c : RelCode} {t : ℕ × List ℕ × List ℕ × ℕ} (h : t ∈ c.1) {x : ℕ}
    (hx : x ∈ t.2.1) : x ∈ codeAlphabet c :=
  List.mem_flatMap.2 ⟨t, h, hx⟩

lemma trans_output_mem {c : RelCode} {t : ℕ × List ℕ × List ℕ × ℕ} (h : t ∈ c.1) {x : ℕ}
    (hx : x ∈ t.2.2.1) : x ∈ codeOutAlphabet c :=
  List.mem_flatMap.2 ⟨t, h, hx⟩

/-! ## The automaton described by a code, over its own alphabets -/

/-- The nfa with output described by a code, over the finite alphabets and the
finite state space of the code. -/
def codeNFAO (c : RelCode) : NFAO (InA c) (OutA c) (StQ c) where
  init := {q | q.val ∈ c.2.1}
  final := {q | q.val ∈ c.2.2}
  δ := {t | (t.1.val, t.2.1.map Subtype.val, t.2.2.1.map Subtype.val, t.2.2.2.val) ∈ c.1}
  δ_finite := by
    have hinj : Function.Injective
        (fun t : StQ c × List (InA c) × List (OutA c) × StQ c =>
          (t.1.val, t.2.1.map Subtype.val, t.2.2.1.map Subtype.val, t.2.2.2.val)) := by
      rintro ⟨q, w, v, p⟩ ⟨q', w', v', p'⟩ h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2, h3, h4⟩ := h
      have e1 : q = q' := Subtype.ext h1
      have e2 : w = w' := List.map_injective_iff.2 Subtype.val_injective h2
      have e3 : v = v' := List.map_injective_iff.2 Subtype.val_injective h3
      have e4 : p = p' := Subtype.ext h4
      simp [e1, e2, e3, e4]
    exact Set.Finite.preimage hinj.injOn c.1.finite_toSet

lemma mem_codeNFAO_delta {c : RelCode} {t : StQ c × List (InA c) × List (OutA c) × StQ c} :
    t ∈ (codeNFAO c).δ ↔
      (t.1.val, t.2.1.map Subtype.val, t.2.2.1.map Subtype.val, t.2.2.2.val) ∈ c.1 :=
  Iff.rfl

/-- A path of the automaton over the alphabets of the code projects to a path of
the automaton described by the code. -/
lemma codeNFAO_sound {c : RelCode} {q p : StQ c} {w : List (InA c)} {v : List (OutA c)}
    (h : (codeNFAO c).relFrom q w v p) :
    (codeAut c).relFrom q.val (w.map Subtype.val) (v.map Subtype.val) p.val := by
  refine NFAO.relFrom_induction
    (motive := fun (q : StQ c) (w : List (InA c)) (v : List (OutA c)) =>
      (codeAut c).relFrom q.val (w.map Subtype.val) (v.map Subtype.val) p.val)
    ?_ ?_ h
  · exact NFAO.relFrom_nil _ _
  · intro q q' u x w v ht _ ih
    have ht' : (q.val, u.map Subtype.val, x.map Subtype.val, q'.val) ∈ (codeAut c).δ :=
      mem_codeNFAO_delta.1 ht
    have := NFAO.relFrom_step ht' ih
    erw [List.map_append, List.map_append]
    exact this

/-- A path of the automaton described by a code lifts to a path of the automaton
over the alphabets of the code. -/
lemma codeNFAO_complete {c : RelCode} {p : ℕ} :
    ∀ {q : ℕ} {w v : List ℕ}, (codeAut c).relFrom q w v p → ∀ hq : q ∈ stAll c,
      ∃ (w' : List (InA c)) (v' : List (OutA c)) (p' : StQ c),
        p'.val = p ∧ w = w'.map Subtype.val ∧ v = v'.map Subtype.val ∧
          (codeNFAO c).relFrom ⟨q, hq⟩ w' v' p' := by
  refine NFAO.relFrom_induction
    (motive := fun (q : ℕ) (w v : List ℕ) => ∀ hq : q ∈ stAll c,
      ∃ (w' : List (InA c)) (v' : List (OutA c)) (p' : StQ c),
        p'.val = p ∧ w = w'.map Subtype.val ∧ v = v'.map Subtype.val ∧
          (codeNFAO c).relFrom ⟨q, hq⟩ w' v' p') ?_ ?_
  · intro hp
    exact ⟨[], [], ⟨p, hp⟩, rfl, rfl, rfl, NFAO.relFrom_nil _ _⟩
  · intro q q' u x w v ht _ ih hq
    have htc : (q, u, x, q') ∈ c.1 := ht
    have hq' : q' ∈ stAll c := tgt_mem_stAll (t := (q, u, x, q')) htc
    obtain ⟨w', v', p', hp', hw, hv, hrel⟩ := ih hq'
    obtain ⟨u', hu'⟩ : ∃ u' : List (InA c), u = u'.map Subtype.val :=
      exists_lift (fun y hy => trans_input_mem (t := (q, u, x, q')) htc hy)
    obtain ⟨x', hx'⟩ : ∃ x' : List (OutA c), x = x'.map Subtype.val :=
      exists_lift (fun y hy =>
        List.mem_cons_of_mem _ (trans_output_mem (t := (q, u, x, q')) htc hy))
    refine ⟨u' ++ w', x' ++ v', p', hp', by rw [hu', hw]; erw [List.map_append],
      by rw [hx', hv]; erw [List.map_append], ?_⟩
    refine NFAO.relFrom_step (q' := (⟨q', hq'⟩ : StQ c)) ?_ hrel
    show ((q : ℕ), u'.map Subtype.val, x'.map Subtype.val, q') ∈ c.1
    rw [← hu', ← hx']
    exact htc

/-- The relation described by the automaton over the finite alphabets is the
relation described by the code, read through the coercions. -/
theorem codeNFAO_rel (c : RelCode) (w : List (InA c)) (v : List (OutA c)) :
    (codeNFAO c).rel w v ↔ codeRel c (w.map Subtype.val) (v.map Subtype.val) := by
  constructor
  · intro h
    obtain ⟨q, hq, p, hp, hrel⟩ := (NFAO.rel_iff_relFrom _ _ _).1 h
    exact (NFAO.rel_iff_relFrom _ _ _).2 ⟨q.val, hq, p.val, hp, codeNFAO_sound hrel⟩
  · intro h
    obtain ⟨q, hq, p, hp, hrel⟩ := (NFAO.rel_iff_relFrom _ _ _).1 h
    obtain ⟨w', v', p', hp', hw, hv, hrel'⟩ := codeNFAO_complete hrel (init_mem_stAll hq)
    have hw2 : w' = w := (map_val_injective hw.symm)
    have hv2 : v' = v := (map_val_injective hv.symm)
    subst hw2; subst hv2
    refine (NFAO.rel_iff_relFrom _ _ _).2 ⟨⟨q, init_mem_stAll hq⟩, hq, p', ?_, hrel'⟩
    show p'.val ∈ c.2.2
    rw [hp']
    exact hp

/-! ## The function described by a code -/

/-- The function described by a code, over the finite alphabets of the code.
Outside the promise it is junk. -/
noncomputable def codeFun (c : RelCode) (w : List (InA c)) : List (OutA c) :=
  open Classical in
  if h : ∃ v : List (OutA c), codeRel c (w.map Subtype.val) (v.map Subtype.val)
    then h.choose else []

/-- The image of a string over the alphabet of the code is a string over the
alphabet of the code. -/
lemma codeWord_map {c : RelCode} (w : List (InA c)) : CodeWord c (w.map Subtype.val) := by
  intro x hx
  obtain ⟨a, -, rfl⟩ := List.mem_map.1 hx
  exact a.2

theorem codeFun_spec {c : RelCode} (hc : CodeFunctional c) (w : List (InA c)) :
    codeRel c (w.map Subtype.val) ((codeFun c w).map Subtype.val) := by
  obtain ⟨u, hu, -⟩ := hc _ (codeWord_map w)
  obtain ⟨v, rfl⟩ : ∃ v : List (OutA c), u = v.map Subtype.val :=
    exists_lift (fun y hy => List.mem_cons_of_mem _ (codeRel_output_mem hu hy))
  have hex : ∃ v : List (OutA c), codeRel c (w.map Subtype.val) (v.map Subtype.val) := ⟨v, hu⟩
  have heq : codeFun c w = hex.choose := dif_pos hex
  rw [heq]
  exact hex.choose_spec

theorem codeFun_eq {c : RelCode} (hc : CodeFunctional c) {w : List (InA c)} {v : List ℕ}
    (h : codeRel c (w.map Subtype.val) v) : v = (codeFun c w).map Subtype.val := by
  obtain ⟨u, -, huniq⟩ := hc _ (codeWord_map w)
  rw [huniq v h, huniq _ (codeFun_spec hc w)]

/-- Under the promise, the function described by a code is rational. -/
theorem isRationalFun_codeFun {c : RelCode} (hc : CodeFunctional c) :
    IsRationalFun (codeFun c) := by
  refine ⟨StQ c, inferInstance, codeNFAO c, fun w v => ?_⟩
  rw [codeNFAO_rel]
  constructor
  · rintro rfl
    exact codeFun_spec hc w
  · intro h
    exact map_val_injective (codeFun_eq hc h)

/-! ## The Mealy fragment -/

/-- Under the promise, the coded relation is length preserving exactly when the
function described by the code is. -/
lemma lengthPreserving_codeFun_iff {c : RelCode} (hc : CodeFunctional c) :
    LengthPreserving (codeFun c) ↔ (∀ w v, codeRel c w v → v.length = w.length) := by
  constructor
  · intro hlen w v hrel
    obtain ⟨w', rfl⟩ : ∃ w' : List (InA c), w = w'.map Subtype.val :=
      exists_lift (fun y hy => codeRel_codeWord hrel y hy)
    rw [codeFun_eq hc hrel]
    simpa using hlen w'
  · intro hlen w
    have := hlen _ _ (codeFun_spec hc w)
    simpa using this

/-- Under the promise, the function described by the code is prefix preserving
exactly when the coded relation is. -/
lemma prefixPreserving_codeFun_iff {c : RelCode} (hc : CodeFunctional c) :
    PrefixPreserving (codeFun c) ↔ PrefixCodes.PrefixCrit c := by
  constructor
  · intro hpre w v a u h1 h2
    have hword : CodeWord c (w ++ [a]) := codeRel_codeWord h2
    obtain ⟨w', rfl⟩ : ∃ w' : List (InA c), w = w'.map Subtype.val :=
      exists_lift (fun y hy => codeRel_codeWord h1 y hy)
    have ha : a ∈ codeAlphabet c := hword a (by simp)
    have hcat : w'.map Subtype.val ++ [a]
        = (w' ++ ([⟨a, ha⟩] : List (InA c))).map Subtype.val := by
      erw [List.map_append]
      rfl
    rw [hcat] at h2
    rw [codeFun_eq hc h1, codeFun_eq hc h2]
    exact List.IsPrefix.map Subtype.val (hpre _ _ ⟨[⟨a, ha⟩], rfl⟩)
  · intro hpc
    have step : ∀ (w : List (InA c)) (a : InA c), codeFun c w <+: codeFun c (w ++ [a]) := by
      intro w a
      have h1 := codeFun_spec hc w
      have h2 := codeFun_spec hc (w ++ [a])
      erw [List.map_append] at h2
      have := hpc (w.map Subtype.val) ((codeFun c w).map Subtype.val) a.val
        ((codeFun c (w ++ [a])).map Subtype.val) h1 (by simpa using h2)
      exact prefix_of_map_prefix Subtype.val_injective this
    have main : ∀ (t w : List (InA c)), codeFun c w <+: codeFun c (w ++ t) := by
      intro t
      induction t with
      | nil => intro w; simp
      | cons a t ih =>
          intro w
          have h1 : codeFun c w <+: codeFun c (w ++ [a]) := step w a
          have h2 : codeFun c (w ++ [a]) <+: codeFun c ((w ++ [a]) ++ t) := ih (w ++ [a])
          have h3 : (w ++ [a]) ++ t = w ++ (a :: t) := by simp
          rw [h3] at h2
          exact h1.trans h2
    intro w₁ w₂ h
    obtain ⟨t, rfl⟩ := h
    exact main t w₁

/-- Under the promise, the function described by a code is computed by a Mealy
machine exactly when it is length preserving and prefix preserving. -/
theorem isMealy_codeFun_iff {c : RelCode} (hc : CodeFunctional c) :
    IsMealy (codeFun c) ↔
      ((∀ w v, codeRel c w v → v.length = w.length) ∧ PrefixCodes.PrefixCrit c) := by
  rw [isMealy_iff_aux]
  constructor
  · rintro ⟨-, hpre, hlen⟩
    exact ⟨(lengthPreserving_codeFun_iff hc).1 hlen, (prefixPreserving_codeFun_iff hc).1 hpre⟩
  · rintro ⟨hlen, hpc⟩
    exact ⟨continuous_of_isRationalFun (isRationalFun_codeFun hc),
      (prefixPreserving_codeFun_iff hc).2 hpc, (lengthPreserving_codeFun_iff hc).2 hlen⟩

/-! ### From a machine over the alphabets of the code to a machine over `ℕ` -/

/-- A Mealy machine over the alphabets of a code, read as a machine over `ℕ`:
on a letter that the code cannot read it stays in place and writes `0`. -/
def widen {c : RelCode} {Q : Type} (M : Mealy (InA c) (OutA c) Q) : Mealy ℕ ℕ Q where
  init := M.init
  step := fun q a =>
    if h : a ∈ codeAlphabet c then
      ((M.step q ⟨a, h⟩).1, (M.step q ⟨a, h⟩).2.val)
    else (q, 0)

lemma widen_run {c : RelCode} {Q : Type} (M : Mealy (InA c) (OutA c) Q) (q : Q)
    (w : List (InA c)) :
    (widen M).run q (w.map Subtype.val) = (M.run q w).map Subtype.val := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih =>
      have ha : a.val ∈ codeAlphabet c := a.2
      have hstep : (widen M).step q a.val
          = ((M.step q a).1, (M.step q a).2.val) := by
        show (if h : a.val ∈ codeAlphabet c then
            ((M.step q ⟨a.val, h⟩).1, (M.step q ⟨a.val, h⟩).2.val)
          else (q, 0)) = _
        rw [dif_pos ha]
        simp only [Subtype.coe_eta]
      erw [List.map_cons, Mealy.run_cons, Mealy.run_cons, hstep, List.map_cons, ih]

lemma widen_eval {c : RelCode} {Q : Type} (M : Mealy (InA c) (OutA c) Q) (w : List (InA c)) :
    (widen M).eval (w.map Subtype.val) = (M.eval w).map Subtype.val :=
  widen_run M M.init w

/-- Under the promise, the property of Theorem `thm:decide-if-mealy` -- that the relation
described by the code agrees on the strings over its alphabet with a function
computed by a Mealy machine over `ℕ` -- is equivalent to the function described
by the code over its own alphabets being computed by a Mealy machine. -/
theorem mealyProperty_iff {c : RelCode} (hc : CodeFunctional c) :
    (∃ f : List ℕ → List ℕ,
        (∀ w, CodeWord c w → ∀ v, (codeRel c w v ↔ v = f w)) ∧ IsMealy f)
      ↔ IsMealy (codeFun c) := by
  constructor
  · rintro ⟨f, hagree, Q, hQ, M, rfl⟩
    -- the values of `codeFun c` are the values of `M.eval` read through the coercion
    have hval : ∀ w : List (InA c),
        (codeFun c w).map Subtype.val = M.eval (w.map Subtype.val) := by
      intro w
      have := codeFun_spec hc w
      exact (hagree _ (codeWord_map w) _).1 this
    rw [isMealy_iff_aux]
    refine ⟨continuous_of_isRationalFun (isRationalFun_codeFun hc), ?_, ?_⟩
    · intro w₁ w₂ h
      obtain ⟨t, rfl⟩ := h
      have hpre : M.eval (w₁.map Subtype.val) <+: M.eval ((w₁ ++ t).map Subtype.val) :=
        M.eval_prefix (by erw [List.map_append]; exact List.prefix_append _ _)
      rw [← hval w₁, ← hval (w₁ ++ t)] at hpre
      exact prefix_of_map_prefix Subtype.val_injective hpre
    · intro w
      have h1 : ((codeFun c w).map Subtype.val).length = (M.eval (w.map Subtype.val)).length := by
        rw [hval]
      simpa using h1
  · rintro ⟨Q, hQ, M, hM⟩
    refine ⟨(widen M).eval, ?_, ⟨Q, hQ, widen M, rfl⟩⟩
    intro w hw v
    obtain ⟨w', rfl⟩ : ∃ w' : List (InA c), w = w'.map Subtype.val := exists_lift hw
    rw [widen_eval, hM]
    constructor
    · intro h
      exact codeFun_eq hc h
    · rintro rfl
      exact codeFun_spec hc w'

end CodeRat
end Lax132576Proofs.Transducers
