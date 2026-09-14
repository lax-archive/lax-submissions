/- Pre-composition of two-way transducers with a homomorphism all of whose blocks have the same
positive length (part of the proof of Corollary `cor:2dfa-closure-under-composition` of
*Transducers*, M. Bojańczyk).

The simulating transducer keeps in its state, besides the state of the simulated
transducer `N`, the offset of the head of `N` inside the block of the letter to
the right of its own head.  A step of `N` that stays inside a block does not
move the head of the simulating transducer, which is impossible for a two-way
transducer; it is implemented by a step to the right followed by a step to the
left, using the *bouncing* flag of the state.
-/
import Lax916827Proofs.Source.PartC.TwoWayHom
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-! ## Blocks of a homomorphism -/

section HomOf

variable {A B : Type} (φ : A → List B)

@[simp] lemma homOf_nil : homOf φ [] = [] := rfl

lemma homOf_cons (a : A) (v : List A) : homOf φ (a :: v) = φ a ++ homOf φ v := by
  simp [homOf]

lemma homOf_append (u v : List A) : homOf φ (u ++ v) = homOf φ u ++ homOf φ v := by
  simp [homOf]

/-- The last letter of the image of a string under a homomorphism with no empty
block. -/
lemma getLast?_homOf (hne : ∀ a, φ a ≠ []) (u : List A) :
    (homOf φ u).getLast? = u.getLast?.bind (fun z => (φ z).getLast?) := by
  induction u using List.reverseRecOn with
  | nil => simp
  | append_singleton u' z _ =>
      rw [homOf_append]
      have hz : homOf φ [z] = φ z := by simp [homOf]
      rw [hz, List.getLast?_append_of_ne_nil _ (hne z)]
      simp

end HomOf

/-! ## The simulating transducer -/

section Block

variable {A B C P : Type}

/-- The letter of the image to the left of the head, as a function of the letter
of the input to the left of the head, the letter to the right, and the offset
inside the block of the latter. -/
def imgL (φ : A → List B) (la rb : Option A) (j : ℕ) : Option B :=
  if j = 0 then la.bind (fun z => (φ z).getLast?) else rb.bind (fun a => (φ a)[j - 1]?)

/-- The letter of the image to the right of the head. -/
def imgR (φ : A → List B) (rb : Option A) (j : ℕ) : Option B :=
  rb.bind (fun a => (φ a)[j]?)

variable (N : TwoWay B C P) (φ : A → List B) (L : ℕ) (hL : 0 < L)

/-- The transducer simulating `N` on the image of the input under a
homomorphism all of whose blocks have length `L`. -/
def blockAut : TwoWay A C (P × Fin L × Bool) where
  init := (N.init, ⟨0, hL⟩, false)
  step := fun la s rb =>
    if s.2.2 then Sum.inr ((s.1, s.2.1, false), [], false)
    else
      match N.step (imgL φ la rb s.2.1) s.1 (imgR φ rb s.2.1) with
      | Sum.inl o => Sum.inl o
      | Sum.inr (p', o, true) =>
          if h : (s.2.1 : ℕ) + 1 < L then Sum.inr ((p', ⟨(s.2.1 : ℕ) + 1, h⟩, true), o, true)
          else Sum.inr ((p', ⟨0, hL⟩, false), o, true)
      | Sum.inr (p', o, false) =>
          if h : 0 < (s.2.1 : ℕ) then
            Sum.inr ((p', ⟨(s.2.1 : ℕ) - 1, by have := s.2.1.isLt; omega⟩, true), o, true)
          else Sum.inr ((p', ⟨L - 1, by omega⟩, false), o, false)

variable {N φ L hL}

@[simp] lemma blockAut_bounce (la rb : Option A) (p : P) (j : Fin L) :
    (blockAut N φ L hL).step la (p, j, true) rb = Sum.inr ((p, j, false), [], false) := by
  simp [blockAut]

lemma blockAut_halt {la rb : Option A} {p : P} {j : Fin L} {o : List C}
    (h : N.step (imgL φ la rb j) p (imgR φ rb j) = Sum.inl o) :
    (blockAut N φ L hL).step la (p, j, false) rb = Sum.inl o := by
  simp [blockAut, h]

lemma blockAut_right_stay {la rb : Option A} {p p' : P} {j : Fin L} {o : List C}
    (h : N.step (imgL φ la rb j) p (imgR φ rb j) = Sum.inr (p', o, true))
    (h' : (j : ℕ) + 1 < L) :
    (blockAut N φ L hL).step la (p, j, false) rb =
      Sum.inr ((p', ⟨(j : ℕ) + 1, h'⟩, true), o, true) := by
  simp [blockAut, h, h']

lemma blockAut_right_move {la rb : Option A} {p p' : P} {j : Fin L} {o : List C}
    (h : N.step (imgL φ la rb j) p (imgR φ rb j) = Sum.inr (p', o, true))
    (h' : ¬ (j : ℕ) + 1 < L) :
    (blockAut N φ L hL).step la (p, j, false) rb = Sum.inr ((p', ⟨0, hL⟩, false), o, true) := by
  simp [blockAut, h, h']

lemma blockAut_left_stay {la rb : Option A} {p p' : P} {j : Fin L} {o : List C}
    (h : N.step (imgL φ la rb j) p (imgR φ rb j) = Sum.inr (p', o, false))
    (h' : 0 < (j : ℕ)) :
    (blockAut N φ L hL).step la (p, j, false) rb =
      Sum.inr ((p', ⟨(j : ℕ) - 1, by have := j.isLt; omega⟩, true), o, true) := by
  simp [blockAut, h, h']

lemma blockAut_left_move {la rb : Option A} {p p' : P} {j : Fin L} {o : List C}
    (h : N.step (imgL φ la rb j) p (imgR φ rb j) = Sum.inr (p', o, false))
    (h' : ¬ 0 < (j : ℕ)) :
    (blockAut N φ L hL).step la (p, j, false) rb =
      Sum.inr ((p', ⟨L - 1, by omega⟩, false), o, false) := by
  simp [blockAut, h, h']

/-! ### The bouncing step -/

/-- A step of `N` that does not leave the current block: the head of the
simulating transducer moves to the right and comes back. -/
lemma blockAut_bounce_run {u v' : List A} {a : A} {p p' : P} {j j' : Fin L} {o : List C}
    (h : (blockAut N φ L hL).step u.getLast? (p, j, false) (a :: v').head? =
      Sum.inr ((p', j', true), o, true)) :
    (blockAut N φ L hL).Reaches (Cfg.conf u (p, j, false) (a :: v')) o
      (Cfg.conf u (p', j', false) (a :: v')) := by
  have h1 : (blockAut N φ L hL).stepCfg (Cfg.conf u (p, j, false) (a :: v')) =
      some (o, Cfg.conf (u ++ [a]) (p', j', true) v') := TwoWay.stepCfg_right_cons _ h
  have hlast : (u ++ [a]).getLast? = some a := by simp
  have h2 : (blockAut N φ L hL).stepCfg (Cfg.conf (u ++ [a]) (p', j', true) v') =
      some ([], Cfg.conf u (p', j', false) (a :: v')) := by
    have := TwoWay.stepCfg_left_some (M := blockAut N φ L hL) (v := v') hlast
      (q := (p', j', true)) (q' := (p', j', false)) (o := ([] : List C)) (by simp)
    simpa using this
  simpa using TwoWay.Reaches.step h1 (TwoWay.reaches_one h2)

/-! ### The simulation relation -/

/-- The relation between the configurations of `blockAut` and the
configurations of `N` on the image of the input. -/
def blockRel (φ : A → List B) (L : ℕ) :
    Cfg A (P × Fin L × Bool) → Cfg B P → Prop := fun X c =>
  (X = Cfg.halt ∧ c = Cfg.halt) ∨
    ∃ (u : List A) (p : P) (j : Fin L),
      ((X = Cfg.conf u (p, j, false) [] ∧ (j : ℕ) = 0 ∧ c = Cfg.conf (homOf φ u) p []) ∨
        ∃ (a : A) (v' : List A) (s t : List B),
          X = Cfg.conf u (p, j, false) (a :: v') ∧ φ a = s ++ t ∧ s.length = (j : ℕ) ∧
            c = Cfg.conf (homOf φ u ++ s) p (t ++ homOf φ v'))

lemma getElem?_length_append (s t : List B) : (s ++ t)[s.length]? = t.head? := by
  rw [List.getElem?_append_right (le_refl _)]
  simp [List.head?_eq_getElem?]

lemma getElem?_length_sub_one_append {s t : List B} (hs : s ≠ []) :
    (s ++ t)[s.length - 1]? = s.getLast? := by
  have hpos : 0 < s.length := List.length_pos_iff.mpr hs
  rw [List.getElem?_append_left (by omega), List.getLast?_eq_getElem?]

/-- The one-step condition of the simulation principle for `blockAut`. -/
lemma blockAut_step (hlen : ∀ a, (φ a).length = L)
    (X : Cfg A (P × Fin L × Bool)) (c : Cfg B P) (o : List C) (c' : Cfg B P)
    (hR : blockRel φ L X c) (hs : N.stepCfg c = some (o, c')) :
    ∃ Y, (blockAut N φ L hL).Reaches X o Y ∧ blockRel φ L Y c' := by
  have hne : ∀ a, φ a ≠ [] := by
    intro a h
    have := hlen a
    rw [h] at this
    simp at this
    omega
  rcases hR with ⟨-, rfl⟩ | ⟨u, p, j, hcase⟩
  · simp [TwoWay.stepCfg] at hs
  rcases hcase with ⟨rfl, hj, rfl⟩ | ⟨a, v', s, t, rfl, hst, hsl, rfl⟩
  · -- the head of `N` is at the right end of the image
    have hLl : (homOf φ u).getLast? = imgL φ u.getLast? none (j : ℕ) := by
      rw [imgL, if_pos hj, getLast?_homOf φ hne]
    have hRr : (([] : List B)).head? = imgR φ none (j : ℕ) := by simp [imgR]
    rcases hstep : N.step (homOf φ u).getLast? p (([] : List B)).head? with o₁ | ⟨p', o₁, dir⟩
    · rw [TwoWay.stepCfg_halt_eq N hstep] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      refine ⟨Cfg.halt, TwoWay.reaches_one (TwoWay.stepCfg_halt_eq _ ?_), Or.inl ⟨rfl, rfl⟩⟩
      refine blockAut_halt ?_
      simp only [List.head?_nil]
      rw [← hLl, ← hRr]
      exact hstep
    · cases dir with
      | true => rw [TwoWay.stepCfg_right_nil N hstep] at hs; simp at hs
      | false =>
          rcases hu : (homOf φ u).getLast? with _ | b
          · rw [TwoWay.stepCfg_left_none N hu hstep] at hs; simp at hs
          · rw [TwoWay.stepCfg_left_some N hu hstep] at hs
            simp only [Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨rfl, rfl⟩ := hs
            rw [getLast?_homOf φ hne] at hu
            rcases huz : u.getLast? with _ | z
            · rw [huz] at hu; simp at hu
            · rw [huz] at hu
              simp only [Option.bind_some] at hu
              obtain ⟨u'', rfl⟩ : ∃ u'', u = u'' ++ [z] :=
                ⟨u.dropLast, (List.dropLast_append_getLast? z huz).symm⟩
              have hzlast : (u'' ++ [z]).getLast? = some z := by simp
              have hdrop : (φ z).dropLast ++ [b] = φ z := List.dropLast_append_getLast? b hu
              have hhom : homOf φ (u'' ++ [z]) = homOf φ u'' ++ φ z := by
                rw [homOf_append]; simp [homOf]
              refine ⟨Cfg.conf u'' (p', ⟨L - 1, by omega⟩, false) [z], ?_, ?_⟩
              · have h0 : (blockAut N φ L hL).step (u'' ++ [z]).getLast? (p, j, false)
                    (([] : List A)).head? = Sum.inr ((p', ⟨L - 1, by omega⟩, false), o₁, false) := by
                  refine blockAut_left_move ?_ (by omega)
                  simp only [List.head?_nil]
                  rw [← hLl, ← hRr]
                  exact hstep
                have h1 := TwoWay.stepCfg_left_some (M := blockAut N φ L hL) hzlast h0
                refine TwoWay.reaches_one ?_
                simpa using h1
              · refine Or.inr ⟨u'', p', ⟨L - 1, by omega⟩, Or.inr
                  ⟨z, [], (φ z).dropLast, [b], rfl, hdrop.symm, ?_, ?_⟩⟩
                · have := hlen z
                  simp only [List.length_dropLast]
                  omega
                · rw [hhom, List.dropLast_append_of_ne_nil (hne z)]
                  simp
  · -- the head of `N` is inside the block of the letter `a`
    have hlt : (j : ℕ) < L := j.isLt
    have hlens : s.length + t.length = L := by
      have := hlen a
      rw [hst] at this
      simpa using this
    have ht : t ≠ [] := by
      intro h
      rw [h] at hlens
      simp at hlens
      omega
    have hLl : (homOf φ u ++ s).getLast? = imgL φ u.getLast? (some a) (j : ℕ) := by
      rcases hsnil : s.eq_nil_or_concat with h | ⟨s₁, x, h⟩
      · subst h
        have hj : (j : ℕ) = 0 := by simpa using hsl.symm
        rw [imgL, if_pos hj, List.append_nil, getLast?_homOf φ hne]
      · have hsne : s ≠ [] := by rw [h]; simp
        have hjpos : 0 < (j : ℕ) := by
          rw [← hsl]
          exact List.length_pos_iff.mpr hsne
        rw [imgL, if_neg (by omega), List.getLast?_append_of_ne_nil _ hsne]
        simp only [Option.bind_some, hst, ← hsl]
        exact (getElem?_length_sub_one_append hsne).symm
    have hRr : (t ++ homOf φ v').head? = imgR φ (some a) (j : ℕ) := by
      rw [imgR]
      simp only [Option.bind_some, hst, ← hsl]
      rw [getElem?_length_append]
      cases t with
      | nil => exact absurd rfl ht
      | cons b t₁ => simp
    rcases hstep : N.step (homOf φ u ++ s).getLast? p (t ++ homOf φ v').head? with
      o₁ | ⟨p', o₁, dir⟩
    · rw [TwoWay.stepCfg_halt_eq N hstep] at hs
      simp only [Option.some.injEq, Prod.mk.injEq] at hs
      obtain ⟨rfl, rfl⟩ := hs
      refine ⟨Cfg.halt, TwoWay.reaches_one (TwoWay.stepCfg_halt_eq _ ?_), Or.inl ⟨rfl, rfl⟩⟩
      refine blockAut_halt ?_
      simp only [List.head?_cons]
      rw [← hLl, ← hRr]
      exact hstep
    · cases dir with
      | true =>
          obtain ⟨b, t₁, rfl⟩ : ∃ b t₁, t = b :: t₁ := by
            cases t with
            | nil => exact absurd rfl ht
            | cons b t₁ => exact ⟨b, t₁, rfl⟩
          rw [show (b :: t₁) ++ homOf φ v' = b :: (t₁ ++ homOf φ v') by simp] at hstep hs
          rw [TwoWay.stepCfg_right_cons N hstep] at hs
          simp only [Option.some.injEq, Prod.mk.injEq] at hs
          obtain ⟨rfl, rfl⟩ := hs
          by_cases hlt' : (j : ℕ) + 1 < L
          · -- the head of `N` stays inside the block
            refine ⟨Cfg.conf u (p', ⟨(j : ℕ) + 1, hlt'⟩, false) (a :: v'), ?_, ?_⟩
            · refine blockAut_bounce_run ?_
              refine blockAut_right_stay ?_ hlt'
              simp only [List.head?_cons]
              rw [← hLl, ← hRr]
              exact hstep
            · refine Or.inr ⟨u, p', ⟨(j : ℕ) + 1, hlt'⟩, Or.inr
                ⟨a, v', s ++ [b], t₁, rfl, ?_, ?_, ?_⟩⟩
              · rw [hst]; simp
              · simp [hsl]
              · simp
          · -- the head of `N` enters the next block
            have ht₁ : t₁ = [] := by
              simp only [List.length_cons] at hlens
              have : t₁.length = 0 := by omega
              exact List.length_eq_zero_iff.mp this
            subst ht₁
            have hsb : s ++ [b] = φ a := hst.symm
            refine ⟨Cfg.conf (u ++ [a]) (p', ⟨0, hL⟩, false) v', ?_, ?_⟩
            · refine TwoWay.reaches_one (TwoWay.stepCfg_right_cons _ ?_)
              refine blockAut_right_move ?_ hlt'
              simp only [List.head?_cons]
              rw [← hLl, ← hRr]
              exact hstep
            · have hhom : homOf φ (u ++ [a]) = homOf φ u ++ s ++ [b] := by
                rw [homOf_append, show homOf φ [a] = φ a by simp [homOf], ← hsb,
                  List.append_assoc]
              cases v' with
              | nil =>
                  refine Or.inr ⟨u ++ [a], p', ⟨0, hL⟩, Or.inl ⟨rfl, rfl, ?_⟩⟩
                  rw [hhom]
                  simp
              | cons a₂ v₂ =>
                  refine Or.inr ⟨u ++ [a], p', ⟨0, hL⟩, Or.inr
                    ⟨a₂, v₂, [], φ a₂, rfl, by simp, by simp, ?_⟩⟩
                  rw [hhom]
                  simp [homOf_cons]
      | false =>
          rcases hsnil : s.eq_nil_or_concat with hsn | ⟨s₁, x, hsc⟩
          · -- the head of `N` is at the left end of the block
            subst hsn
            have hj : (j : ℕ) = 0 := by simpa using hsl.symm
            simp only [List.append_nil] at hstep hs hLl
            rcases hu : (homOf φ u).getLast? with _ | b
            · rw [TwoWay.stepCfg_left_none N hu hstep] at hs; simp at hs
            · rw [TwoWay.stepCfg_left_some N hu hstep] at hs
              simp only [Option.some.injEq, Prod.mk.injEq] at hs
              obtain ⟨rfl, rfl⟩ := hs
              rw [getLast?_homOf φ hne] at hu
              rcases huz : u.getLast? with _ | z
              · rw [huz] at hu; simp at hu
              · rw [huz] at hu
                simp only [Option.bind_some] at hu
                obtain ⟨u'', rfl⟩ : ∃ u'', u = u'' ++ [z] :=
                  ⟨u.dropLast, (List.dropLast_append_getLast? z huz).symm⟩
                have hzlast : (u'' ++ [z]).getLast? = some z := by simp
                have hdrop : (φ z).dropLast ++ [b] = φ z := List.dropLast_append_getLast? b hu
                have hhom : homOf φ (u'' ++ [z]) = homOf φ u'' ++ φ z := by
                  rw [homOf_append]; simp [homOf]
                refine ⟨Cfg.conf u'' (p', ⟨L - 1, by omega⟩, false) (z :: a :: v'), ?_, ?_⟩
                · have h0 : (blockAut N φ L hL).step (u'' ++ [z]).getLast? (p, j, false)
                    ((a :: v')).head? = Sum.inr ((p', ⟨L - 1, by omega⟩, false), o₁, false) := by
                    refine blockAut_left_move ?_ (by omega)
                    simp only [List.head?_cons]
                    rw [← hLl, ← hRr]
                    exact hstep
                  have h1 := TwoWay.stepCfg_left_some (M := blockAut N φ L hL) hzlast h0
                  refine TwoWay.reaches_one ?_
                  simpa using h1
                · refine Or.inr ⟨u'', p', ⟨L - 1, by omega⟩, Or.inr
                    ⟨z, a :: v', (φ z).dropLast, [b], rfl, hdrop.symm, ?_, ?_⟩⟩
                  · have := hlen z
                    simp only [List.length_dropLast]
                    omega
                  · rw [hhom, List.dropLast_append_of_ne_nil (hne z)]
                    simp only [List.cons_append, List.nil_append, homOf_cons]
                    rw [show φ a = t by simpa using hst]
          · -- the head of `N` stays inside the block
            have hsne : s ≠ [] := by rw [hsc]; simp
            have hjpos : 0 < (j : ℕ) := by
              rw [← hsl]; exact List.length_pos_iff.mpr hsne
            have hsl' : s.getLast? = some x := by rw [hsc]; simp
            have hsdrop : s.dropLast = s₁ := by rw [hsc]; simp
            have hlast : (homOf φ u ++ s).getLast? = some x := by
              rw [List.getLast?_append_of_ne_nil _ hsne, hsl']
            rw [TwoWay.stepCfg_left_some N hlast hstep] at hs
            simp only [Option.some.injEq, Prod.mk.injEq] at hs
            obtain ⟨rfl, rfl⟩ := hs
            refine ⟨Cfg.conf u (p', ⟨(j : ℕ) - 1, by omega⟩, false) (a :: v'), ?_, ?_⟩
            · refine blockAut_bounce_run ?_
              refine blockAut_left_stay ?_ hjpos
              simp only [List.head?_cons]
              rw [← hLl, ← hRr]
              exact hstep
            · refine Or.inr ⟨u, p', ⟨(j : ℕ) - 1, by omega⟩, Or.inr
                ⟨a, v', s₁, x :: t, rfl, ?_, ?_, ?_⟩⟩
              · rw [hst, hsc]; simp
              · have hlen1 : s.length = s₁.length + 1 := by rw [hsc]; simp
                show s₁.length = (j : ℕ) - 1
                omega
              · rw [List.dropLast_append_of_ne_nil hsne, hsdrop]
                simp

/-- The transducer `blockAut` computes the composition with the homomorphism. -/
theorem blockAut_computes (hlen : ∀ a, (φ a).length = L) {g : List B → List C}
    (hN : ∀ v, N.Computes v (g v)) (w : List A) :
    (blockAut N φ L hL).Computes w (g (homOf φ w)) := by
  refine TwoWay.computes_of_sim (blockRel φ L) (blockAut_step (hL := hL) hlen) ?_ ?_ (hN _)
  · cases w with
    | nil => exact Or.inr ⟨[], N.init, ⟨0, hL⟩, Or.inl ⟨rfl, rfl, rfl⟩⟩
    | cons a v' =>
        refine Or.inr ⟨[], N.init, ⟨0, hL⟩, Or.inr ⟨a, v', [], φ a, rfl, by simp, by simp, ?_⟩⟩
        simp [homOf_cons]
  · rintro Y (⟨rfl, -⟩ | ⟨u, p, j, ⟨-, -, h⟩ | ⟨a, v', s, t, -, -, -, h⟩⟩)
    · rfl
    · exact absurd h (by simp)
    · exact absurd h (by simp)

/-- Two-way transducers are closed under pre-composition with a homomorphism
all of whose blocks have the same positive length. -/
theorem isTwoWay_comp_blockHom {g : List B → List C} (hg : IsTwoWay g)
    (φ : A → List B) {L : ℕ} (hL : 0 < L) (hlen : ∀ a, (φ a).length = L) :
    IsTwoWay (fun w => g (homOf φ w)) := by
  obtain ⟨P, hP, N, hN⟩ := hg
  haveI := hP
  exact ⟨P × Fin L × Bool, inferInstance, blockAut N φ L hL,
    fun w => blockAut_computes hlen hN w⟩

end Block

end Lax916827Proofs.Transducers
