/-
The map lifting (Definition `def:map-lifting`) of *Transducers* (M. Bojańczyk, June 25, 2026)
and its behaviour with respect to decompositions into prime Mealy machines
(Lemma `lem:map-lifting-decomposition-mealy`).
-/
import Lax765601Proofs.Source.PartA.PrimeClosure

namespace Lax765601Proofs.Transducers

variable {A B C Q : Type}

/-! ## Online functions

A string-to-string function is *online* if it produces exactly one output letter
per input letter, the letters produced so far depending only on the letters read
so far.  This is precisely the behaviour of a Mealy machine that is needed for
the description of the map lifting below. -/

/-- Reading one more input letter appends exactly one output letter. -/
def OneStep (f : List A → List B) : Prop :=
  f [] = [] ∧ ∀ (u : List A) (a : A), ∃ b : B, f (u ++ [a]) = f u ++ [b]

lemma OneStep.lengthPreserving {f : List A → List B} (hf : OneStep f) :
    LengthPreserving f := by
  intro w
  induction w using List.reverseRecOn with
  | nil => simp [hf.1]
  | append_singleton u a ih =>
      obtain ⟨b, hb⟩ := hf.2 u a
      simp [hb, ih]

lemma Mealy.oneStep (M : Mealy A B Q) : OneStep M.eval := by
  refine ⟨rfl, fun u a => ⟨(M.step (M.trans u M.init) a).2, ?_⟩⟩
  rw [M.eval_append]
  rfl

lemma OneStep.comp {f : List A → List B} {g : List B → List C}
    (hf : OneStep f) (hg : OneStep g) : OneStep (g ∘ f) := by
  refine ⟨by simp [hf.1, hg.1], fun u a => ?_⟩
  obtain ⟨b, hb⟩ := hf.2 u a
  obtain ⟨c, hc⟩ := hg.2 (f u) b
  exact ⟨c, by simp [hb, hc]⟩

lemma oneStep_id : OneStep (id : List A → List A) := ⟨rfl, fun _ a => ⟨a, rfl⟩⟩

lemma oneStep_of_compClosure {f : List A → List B}
    (h : CompClosure PrimeMealyFam A B f) : OneStep f := by
  induction h with
  | base hf =>
      rcases hf with ⟨Q, hQ, M, hM, _⟩ | ⟨Q, hQ, M, hM, _⟩ <;> exact hM ▸ M.oneStep
  | id A => exact oneStep_id
  | comp _ _ ihf ihg => exact ihf.comp ihg

/-! ## A direct description of the map lifting -/

/-- The map lifting, described position by position: `mapLiftAux f u w` is the
output on the input `w`, when the current block already contains `u`. -/
def mapLiftAux (f : List A → List B) : List A → List (Option A) → List (Option B)
  | _, [] => []
  | _, none :: w => none :: mapLiftAux f [] w
  | u, some a :: w => (f (u ++ [a])).getLast? :: mapLiftAux f (u ++ [a]) w

lemma splitSep_ne_nil (w : List (Option A)) : splitSep w ≠ [] := by
  induction w with
  | nil => simp [splitSep]
  | cons x w ih =>
      cases x with
      | none => simp [splitSep]
      | some a =>
          rw [splitSep]
          cases h : splitSep w with
          | nil => simp
          | cons u us => simp

lemma splitSep_map_some_append (u : List A) (w : List (Option A)) (b : List A)
    (bs : List (List A)) (h : splitSep w = b :: bs) :
    splitSep (u.map some ++ w) = (u ++ b) :: bs := by
  induction u with
  | nil => simpa using h
  | cons a u ih =>
      show splitSep (some a :: (u.map some ++ w)) = _
      rw [splitSep, ih]
      rfl

lemma intercalate_cons_cons (sep x : List B) (xs : List (List B)) (hxs : xs ≠ []) :
    List.intercalate sep (x :: xs) = x ++ sep ++ List.intercalate sep xs := by
  cases xs with
  | nil => exact absurd rfl hxs
  | cons y ys => simp [List.intercalate]

lemma mapLift_map_some_append {f : List A → List B} (hf : OneStep f) (u : List A)
    (w : List (Option A)) :
    mapLift f (u.map some ++ w) = (f u).map some ++ mapLiftAux f u w := by
  induction w generalizing u with
  | nil =>
      have h : splitSep (u.map some) = [u] := by
        have h0 := splitSep_map_some_append u ([] : List (Option A)) [] [] rfl
        simpa using h0
      simp [mapLift, mapLiftAux, h, List.intercalate]
  | cons x w ih =>
      cases x with
      | none =>
          have hsplit : splitSep (u.map some ++ (none :: w)) = u :: splitSep w := by
            rw [splitSep_map_some_append u (none :: w) [] (splitSep w) rfl]
            simp
          have hmap : mapLift f (u.map some ++ (none :: w))
              = (f u).map some ++ [none] ++ mapLift f w := by
            rw [mapLift, hsplit]
            rw [List.map_cons, intercalate_cons_cons _ _ _ (by
              simpa using (splitSep_ne_nil w).imp (fun h => by simp [h]))]
            rfl
          have hw : mapLift f w = mapLiftAux f [] w := by
            have := ih []
            simpa [hf.1] using this
          rw [hmap, hw]
          simp [mapLiftAux]
      | some a =>
          have hrw : u.map some ++ (some a :: w) = (u ++ [a]).map some ++ w := by
            simp
          obtain ⟨b, hb⟩ := hf.2 u a
          rw [hrw, ih (u ++ [a])]
          simp [mapLiftAux, hb]

/-- The map lifting, computed position by position. -/
lemma mapLift_eq_aux {f : List A → List B} (hf : OneStep f) (w : List (Option A)) :
    mapLift f w = mapLiftAux f [] w := by
  have := mapLift_map_some_append hf [] w
  simpa [hf.1] using this

/-! ## Map lifting commutes with composition -/

lemma mapLiftAux_comp {f : List A → List B} {g : List B → List C}
    (hf : OneStep f) (u : List A) (w : List (Option A)) :
    mapLiftAux g (f u) (mapLiftAux f u w) = mapLiftAux (g ∘ f) u w := by
  induction w generalizing u with
  | nil => rfl
  | cons x w ih =>
      cases x with
      | none =>
          show mapLiftAux g (f u) (none :: mapLiftAux f [] w) = _
          rw [mapLiftAux]
          rw [show mapLiftAux g [] (mapLiftAux f [] w) = mapLiftAux (g ∘ f) [] w by
            have := ih []
            simpa [hf.1] using this]
          rfl
      | some a =>
          obtain ⟨b, hb⟩ := hf.2 u a
          show mapLiftAux g (f u) ((f (u ++ [a])).getLast? :: mapLiftAux f (u ++ [a]) w) = _
          rw [hb, List.getLast?_concat]
          show (g (f u ++ [b])).getLast? :: mapLiftAux g (f u ++ [b]) (mapLiftAux f (u ++ [a]) w)
              = _
          rw [← hb, ih (u ++ [a])]
          rfl

lemma mapLift_comp {f : List A → List B} {g : List B → List C}
    (hf : OneStep f) (hg : OneStep g) :
    mapLift (g ∘ f) = mapLift g ∘ mapLift f := by
  funext w
  show mapLift (g ∘ f) w = mapLift g (mapLift f w)
  rw [mapLift_eq_aux (hf.comp hg), mapLift_eq_aux hf, mapLift_eq_aux hg]
  rw [show mapLiftAux g [] (mapLiftAux f [] w) = mapLiftAux g (f []) (mapLiftAux f [] w) by
    rw [hf.1]]
  exact (mapLiftAux_comp hf [] w).symm


lemma mapLift_id : mapLift (id : List A → List A) = id := by
  funext w
  rw [mapLift_eq_aux oneStep_id]
  have : ∀ (u : List A) (w : List (Option A)), mapLiftAux (id : List A → List A) u w = w := by
    intro u w
    induction w generalizing u with
    | nil => rfl
    | cons x w ih =>
        cases x with
        | none => simp [mapLiftAux, ih]
        | some a => simp [mapLiftAux, ih]
  exact this [] w

/-! ## The map lifting of a Mealy machine -/

lemma Mealy.trans_append_singleton (M : Mealy A B Q) (u : List A) (a : A) (q : Q) :
    M.trans (u ++ [a]) q = M.letterTrans a (M.trans u q) := by
  rw [Mealy.trans_append]
  rfl

lemma Mealy.eval_append_singleton_getLast? (M : Mealy A B Q) (u : List A) (a : A) :
    (M.eval (u ++ [a])).getLast? = some (M.step (M.trans u M.init) a).2 := by
  rw [M.eval_append]
  simp

lemma Mealy.trans_bijective_of_reversible {M : Mealy A B Q} (h : M.Reversible) (w : List A) :
    Function.Bijective (M.trans w) := by
  induction w with
  | nil => exact Function.bijective_id
  | cons a w ih =>
      have : M.trans (a :: w) = M.trans w ∘ M.letterTrans a := rfl
      rw [this]
      exact ih.comp (h a)

/-- The Mealy machine of the map lifting of a Mealy machine: it resets its state
at every separator. -/
def mapLiftMealy (M : Mealy A B Q) : Mealy (Option A) (Option B) Q where
  init := M.init
  step := fun q x =>
    match x with
    | none => (M.init, none)
    | some a => ((M.step q a).1, some (M.step q a).2)

lemma mapLiftMealy_run (M : Mealy A B Q) (w : List (Option A)) (u : List A) :
    (mapLiftMealy M).run (M.trans u M.init) w = mapLiftAux M.eval u w := by
  induction w generalizing u with
  | nil => rfl
  | cons x w ih =>
      cases x with
      | none =>
          show none :: (mapLiftMealy M).run M.init w = _
          rw [show M.init = M.trans [] M.init from rfl, ih []]
          rfl
      | some a =>
          show some (M.step (M.trans u M.init) a).2 ::
              (mapLiftMealy M).run ((M.step (M.trans u M.init) a).1) w = _
          rw [show (M.step (M.trans u M.init) a).1 = M.trans (u ++ [a]) M.init from
            (M.trans_append_singleton u a M.init).symm, ih (u ++ [a])]
          rw [mapLiftAux, M.eval_append_singleton_getLast?]

lemma mapLiftMealy_eval (M : Mealy A B Q) : (mapLiftMealy M).eval = mapLift M.eval := by
  funext w
  rw [mapLift_eq_aux M.oneStep]
  exact mapLiftMealy_run M w []

lemma mapLiftMealy_flipFlop {M : Mealy A B Q} (h : M.FlipFlop) : (mapLiftMealy M).FlipFlop := by
  intro x
  cases x with
  | none => exact Or.inr ⟨M.init, fun _ => rfl⟩
  | some a => exact h a

/-- The map lifting of a flip-flop machine is a flip-flop machine. -/
lemma mapLift_flipFlop {f : List A → List B} (h : IsFlipFlopMealy f) :
    IsFlipFlopMealy (mapLift f) := by
  obtain ⟨Q, hQ, M, hM, hff⟩ := h
  exact ⟨Q, hQ, mapLiftMealy M, by rw [mapLiftMealy_eval, hM], mapLiftMealy_flipFlop hff⟩

/-! ## The map lifting of a reversible machine

Following the book, the map lifting of a reversible machine is computed in three
stages: a reversible machine computing the state transformation of the prefix
that ignores the separators, a flip-flop machine storing that value at the last
separator, and a letter-to-letter homomorphism that applies the cancellation
law. -/

/-- Stage 1: the state transformation of the prefix, ignoring the separators.
The output at a position is the value *before* that position. -/
def gammaMealy (M : Mealy A B Q) : Mealy (Option A) (Q → Q) (Q → Q) where
  init := id
  step := fun t x =>
    match x with
    | none => (t, t)
    | some a => (fun q => M.letterTrans a (t q), t)

/-- Stage 2: store the value of the first stage at the last separator. -/
def storeMealy (A Q : Type) : Mealy ((Option A) × (Q → Q)) (Q → Q) (Q → Q) where
  init := id
  step := fun s xt =>
    match xt.1 with
    | none => (xt.2, s)
    | some _ => (s, s)

/-- Stage 3: the cancellation law, as a letter-to-letter homomorphism. -/
noncomputable def mapLiftHom (M : Mealy A B Q) : ((Option A × (Q → Q)) × (Q → Q)) → Option B :=
  haveI : Nonempty Q := ⟨M.init⟩
  fun p =>
    match p.1.1 with
    | none => none
    | some a => some (M.step (p.1.2 (Function.invFun p.2 M.init)) a).2

lemma gammaMealy_reversible {M : Mealy A B Q} (h : M.Reversible) : (gammaMealy M).Reversible := by
  intro x
  cases x with
  | none => exact Function.bijective_id
  | some a =>
      constructor
      · intro t₁ t₂ ht
        funext q
        exact (h a).injective (congrFun ht q)
      · intro r
        choose g hg using fun q => (h a).surjective (r q)
        exact ⟨g, funext hg⟩

lemma storeMealy_flipFlop : (storeMealy A Q).FlipFlop := by
  intro xt
  cases hx : xt.1 with
  | none => exact Or.inr ⟨xt.2, fun _ => by simp [Mealy.letterTrans, storeMealy, hx]⟩
  | some a => exact Or.inl (by funext s; simp [Mealy.letterTrans, storeMealy, hx])

/-- The composition of the three stages. -/
noncomputable def mapLiftRevMealy (M : Mealy A B Q) :
    Mealy (Option A) (Option B) ((Q → Q) × ((Q → Q) × Unit)) :=
  (gammaMealy M).withInput.compose
    ((storeMealy A Q).withInput.compose (homMealy (mapLiftHom M)))

lemma mapLiftRev_run {M : Mealy A B Q} (hrev : M.Reversible) (w : List (Option A)) :
    ∀ (u : List A) (γ s : Q → Q), (∀ q, γ q = M.trans u (s q)) → Function.Bijective s →
      (mapLiftRevMealy M).run (γ, s, ()) w = mapLiftAux M.eval u w := by
  haveI : Nonempty Q := ⟨M.init⟩
  induction w with
  | nil => intro u γ s _ _; rfl
  | cons x w ih =>
      intro u γ s hinv hs
      cases x with
      | none =>
          show none :: (mapLiftRevMealy M).run (γ, γ, ()) w = _
          rw [ih [] γ γ (fun q => rfl) ?_]
          · rfl
          · have hγ : γ = M.trans u ∘ s := funext hinv
            rw [hγ]
            exact (M.trans_bijective_of_reversible hrev u).comp hs
      | some a =>
          have hfix : γ (Function.invFun s M.init) = M.trans u M.init := by
            rw [hinv, Function.invFun_eq (hs.surjective M.init)]
          show some (M.step (γ (Function.invFun s M.init)) a).2 ::
              (mapLiftRevMealy M).run (fun q => M.letterTrans a (γ q), s, ()) w = _
          rw [hfix, ih (u ++ [a]) (fun q => M.letterTrans a (γ q)) s ?_ hs]
          · rw [mapLiftAux, M.eval_append_singleton_getLast?]
          · intro q
            show M.letterTrans a (γ q) = M.trans (u ++ [a]) (s q)
            rw [M.trans_append_singleton, hinv]

lemma mapLiftRevMealy_eval {M : Mealy A B Q} (hrev : M.Reversible) :
    (mapLiftRevMealy M).eval = mapLift M.eval := by
  funext w
  rw [mapLift_eq_aux M.oneStep]
  exact mapLiftRev_run hrev w [] id id (fun q => rfl) Function.bijective_id

/-- The map lifting of a reversible Mealy machine is a composition of prime
Mealy machines: a reversible machine, a flip-flop machine and a letter-to-letter
homomorphism. -/
lemma mapLift_reversible_compClosure [Finite A] [Finite Q] {M : Mealy A B Q}
    (hrev : M.Reversible) :
    CompClosure PrimeMealyFam (Option A) (Option B) (mapLift M.eval) := by
  have h1 : PrimeMealyFam (Option A) (Option A × (Q → Q)) (gammaMealy M).withInput.eval :=
    Or.inl ⟨Q → Q, inferInstance, (gammaMealy M).withInput, rfl,
      Mealy.withInput_reversible _ (gammaMealy_reversible hrev)⟩
  have h2 : PrimeMealyFam (Option A × (Q → Q)) ((Option A × (Q → Q)) × (Q → Q))
      (storeMealy A Q).withInput.eval :=
    Or.inr ⟨Q → Q, inferInstance, (storeMealy A Q).withInput, rfl,
      Mealy.withInput_flipFlop _ storeMealy_flipFlop⟩
  have h3 : PrimeMealyFam ((Option A × (Q → Q)) × (Q → Q)) (Option B)
      (List.map (mapLiftHom M)) := prime_map _
  have h4 := CompClosure.comp (CompClosure.base h1)
    (CompClosure.comp (CompClosure.base h2) (CompClosure.base h3))
  have hcomp : (List.map (mapLiftHom M) ∘ (storeMealy A Q).withInput.eval) ∘
      (gammaMealy M).withInput.eval = mapLift M.eval := by
    have h := mapLiftRevMealy_eval hrev
    rw [mapLiftRevMealy, Mealy.eval_compose, Mealy.eval_compose, homMealy_eval] at h
    exact h
  rwa [hcomp] at h4

/-- **Lemma `lem:map-lifting-decomposition-mealy`.**  If a Mealy machine decomposes into prime Mealy
machines, then the same is true for its map lifting. -/
theorem mapLift_compClosure {A B : Type} {f : List A → List B} (hA : Finite A)
    (hf : CompClosure PrimeMealyFam A B f) :
    CompClosure PrimeMealyFam (Option A) (Option B) (mapLift f) := by
  revert hA
  induction hf with
  | base hp =>
      intro hA
      haveI := hA
      rcases hp with ⟨Q, hQ, M, hM, hr⟩ | hff
      · haveI := hQ
        rw [← hM]
        exact mapLift_reversible_compClosure hr
      · exact CompClosure.base (Or.inr (mapLift_flipFlop hff))
  | id A =>
      intro _
      rw [mapLift_id]
      exact CompClosure.id _
  | @comp A₁ B₁ C₁ hfin f₁ g₁ hf₁ hg₁ ihf ihg =>
      intro hA₁
      haveI := hA₁
      haveI : Finite (Option B₁) := inferInstance
      rw [mapLift_comp (oneStep_of_compClosure hf₁) (oneStep_of_compClosure hg₁)]
      exact CompClosure.comp (ihf hA₁) (ihg hfin)

end Lax765601Proofs.Transducers