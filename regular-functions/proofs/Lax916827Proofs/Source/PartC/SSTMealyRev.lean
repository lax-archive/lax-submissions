/- Post-composition of a streaming string transducer with a *reversible* Mealy machine (a step of
the "regular to sst" half of Theorem `theorem:sst-two-way-equivalence` of *Transducers*, M.
Bojańczyk).

For every register `X` of the sst and every state `q` of the Mealy machine, the
new sst has a register `X_q`, which holds the image of the content of `X` under
the Mealy machine started in the state `q`.  Since the machine is reversible,
the state reached after reading the content of a register is a bijective
function of the state in which it is entered, and the updates of the registers
`X_q` are copyless.  The state of the new sst remembers, for every register, the
state transformation of its content, which is a permutation of the states.
-/
import Lax765601Proofs.Source.PartA.MealyBasic
import Lax916827Proofs.Source.PartC.SSTComp
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

variable {A B C : Type}

namespace MealyRevSST

variable {Q X : Type} (M : Mealy B C Q)

/-- The permutation of the states induced by a letter of a reversible Mealy
machine. -/
noncomputable def letterPerm (hM : M.Reversible) (b : B) : Equiv.Perm Q :=
  Equiv.ofBijective (M.letterTrans b) (hM b)

@[simp] lemma letterPerm_apply (hM : M.Reversible) (b : B) (q : Q) :
    letterPerm M hM b q = (M.step q b).1 := rfl

/-- The image, under the Mealy machine started in the state `q`, of a string
over `X + B` whose registers have the state transformations `τ`: every register
name `y` is replaced by the register name `(y, p)`, where `p` is the state of
the machine at the place where the content of `y` starts. -/
def walkOut (τ : X → Equiv.Perm Q) : Q → List (X ⊕ B) → List ((X × Q) ⊕ C)
  | _, [] => []
  | q, Sum.inl y :: s => Sum.inl (y, q) :: walkOut τ (τ y q) s
  | q, Sum.inr b :: s => Sum.inr (M.step q b).2 :: walkOut τ (M.step q b).1 s

/-- The state transformation of a string over `X + B` whose registers have the
state transformations `τ`; it is a permutation, because the machine is
reversible. -/
noncomputable def walkPerm (hM : M.Reversible) (τ : X → Equiv.Perm Q) :
    List (X ⊕ B) → Equiv.Perm Q
  | [] => Equiv.refl Q
  | Sum.inl y :: s => (τ y).trans (walkPerm hM τ s)
  | Sum.inr b :: s => (letterPerm M hM b).trans (walkPerm hM τ s)

variable {M}

lemma walkPerm_eq {hM : M.Reversible} {τ : X → Equiv.Perm Q} {η : X → List B}
    (hτ : ∀ x, ⇑(τ x) = M.trans (η x)) (s : List (X ⊕ B)) :
    ⇑(walkPerm M hM τ s) = M.trans (SST.subst η s) := by
  induction s with
  | nil => rfl
  | cons z s ih =>
      cases z with
      | inl y =>
          funext q
          show walkPerm M hM τ s (τ y q) = _
          rw [SST.subst_cons_inl, M.trans_append]
          rw [congrFun ih (τ y q), congrFun (hτ y) q]
      | inr b =>
          funext q
          show walkPerm M hM τ s ((M.step q b).1) = _
          rw [SST.subst_cons_inr]
          rw [show (b :: SST.subst η s) = [b] ++ SST.subst η s from rfl, M.trans_append]
          rw [congrFun ih ((M.step q b).1)]
          rfl

lemma subst_walkOut {τ : X → Equiv.Perm Q} {η : X → List B} {η' : X × Q → List C}
    (hη : ∀ x q, η' (x, q) = M.run q (η x)) (hτ : ∀ x, ⇑(τ x) = M.trans (η x))
    (q : Q) (s : List (X ⊕ B)) :
    SST.subst η' (walkOut M τ q s) = M.run q (SST.subst η s) := by
  induction s generalizing q with
  | nil => rfl
  | cons z s ih =>
      cases z with
      | inl y =>
          show SST.subst η' (Sum.inl (y, q) :: walkOut M τ (τ y q) s) = _
          rw [SST.subst_cons_inl, ih, hη y q, SST.subst_cons_inl, M.run_append,
            congrFun (hτ y) q]
      | inr b =>
          show SST.subst η' (Sum.inr (M.step q b).2 :: walkOut M τ ((M.step q b).1) s) = _
          rw [SST.subst_cons_inr, ih, SST.subst_cons_inr, M.run_cons]

/-! ### The copyless restriction -/

lemma map_fst_regsOf_walkOut (τ : X → Equiv.Perm Q) (q : Q) (s : List (X ⊕ B)) :
    (regsOf (walkOut M τ q s)).map Prod.fst = regsOf s := by
  induction s generalizing q with
  | nil => rfl
  | cons z s ih =>
      cases z with
      | inl y =>
          show (regsOf (Sum.inl (y, q) :: walkOut M τ (τ y q) s)).map Prod.fst = _
          simpa using ih (τ y q)
      | inr b =>
          show (regsOf (Sum.inr (M.step q b).2 :: walkOut M τ ((M.step q b).1) s)).map _ = _
          simpa using ih ((M.step q b).1)

lemma mem_regsOf_walkOut {τ : X → Equiv.Perm Q} {q : Q} {s : List (X ⊕ B)} {y : X} {p : Q}
    (h : (y, p) ∈ regsOf (walkOut M τ q s)) : y ∈ regsOf s := by
  have := map_fst_regsOf_walkOut (M := M) τ q s
  have : ((y, p) : X × Q).1 ∈ (regsOf (walkOut M τ q s)).map Prod.fst :=
    List.mem_map_of_mem h
  rwa [map_fst_regsOf_walkOut] at this

lemma nodup_regsOf_walkOut {τ : X → Equiv.Perm Q} (q : Q) {s : List (X ⊕ B)}
    (hs : (regsOf s).Nodup) : (regsOf (walkOut M τ q s)).Nodup := by
  have h := map_fst_regsOf_walkOut (M := M) τ q s
  exact List.Nodup.of_map Prod.fst (by rw [h]; exact hs)

/-- The states attached to a register name by `walkOut` determine the state in
which the walk was started: this is where reversibility is used, and it is what
makes the new register updates copyless. -/
lemma walkOut_state_inj (hM : M.Reversible) {τ : X → Equiv.Perm Q} :
    ∀ {s : List (X ⊕ B)}, (regsOf s).Nodup → ∀ {q q' : Q} {y : X} {p : Q},
      (y, p) ∈ regsOf (walkOut M τ q s) → (y, p) ∈ regsOf (walkOut M τ q' s) → q = q' := by
  intro s
  induction s with
  | nil => intro _ q q' y p h _; simp [walkOut, regsOf] at h
  | cons z s ih =>
      intro hs q q' y p h h'
      cases z with
      | inl y' =>
          rw [regsOf.cons_inl, List.nodup_cons] at hs
          obtain ⟨hy', hnd⟩ := hs
          rw [show walkOut M τ q (Sum.inl y' :: s)
                = Sum.inl (y', q) :: walkOut M τ (τ y' q) s from rfl,
            regsOf.cons_inl, List.mem_cons] at h
          rw [show walkOut M τ q' (Sum.inl y' :: s)
                = Sum.inl (y', q') :: walkOut M τ (τ y' q') s from rfl,
            regsOf.cons_inl, List.mem_cons] at h'
          rcases h with h | h
          · have hp : p = q := congrArg Prod.snd h
            rcases h' with h' | h'
            · have hp' : p = q' := congrArg Prod.snd h'
              exact hp.symm.trans hp'
            · have hy : y = y' := congrArg Prod.fst h
              exact absurd (hy ▸ mem_regsOf_walkOut (M := M) h') hy'
          · rcases h' with h' | h'
            · have hy : y = y' := congrArg Prod.fst h'
              exact absurd (hy ▸ mem_regsOf_walkOut (M := M) h) hy'
            · exact (τ y').injective (ih hnd h h')
      | inr b =>
          rw [regsOf.cons_inr] at hs
          rw [show walkOut M τ q (Sum.inr b :: s)
                = Sum.inr (M.step q b).2 :: walkOut M τ ((M.step q b).1) s from rfl,
            regsOf.cons_inr] at h
          rw [show walkOut M τ q' (Sum.inr b :: s)
                = Sum.inr (M.step q' b).2 :: walkOut M τ ((M.step q' b).1) s from rfl,
            regsOf.cons_inr] at h'
          exact (hM b).1 (ih hs h h')

/-! ### The new sst -/

variable (M)

/-- The sst computing `M.eval ∘ T.eval` for a reversible Mealy machine `M`: its
registers are the pairs `(x, q)`, holding the image under `M` started in `q` of
the content of the register `x` of `T`, and its states remember the state
transformation of the content of every register of `T`. -/
noncomputable def revComp {A QT : Type} [Fintype X] [Fintype Q] (T : SST A B QT X)
    (hM : M.Reversible) : SST A C (QT × (X → Equiv.Perm Q)) (X × Q) where
  init := (T.init, fun _ => Equiv.refl Q)
  step := fun p a =>
    (((T.step p.1 a).1, fun x => walkPerm M hM p.2 ((T.step p.1 a).2 x)),
      fun xq => walkOut M p.2 xq.2 ((T.step p.1 a).2 xq.1))
  step_copyless := by
    rintro ⟨qT, τ⟩ a
    have h := T.step_copyless qT a
    rw [copyless_iff] at h ⊢
    constructor
    · rintro ⟨x, q⟩
      exact nodup_regsOf_walkOut q (h.1 x)
    · rintro ⟨x, q⟩ ⟨x', q'⟩ hne y hy hy'
      have hx : y.1 ∈ regsOf ((T.step qT a).2 x) :=
        mem_regsOf_walkOut (M := M) (y := y.1) (p := y.2) (by simpa using hy)
      have hx' : y.1 ∈ regsOf ((T.step qT a).2 x') :=
        mem_regsOf_walkOut (M := M) (y := y.1) (p := y.2) (by simpa using hy')
      by_cases hxx : x = x'
      · subst hxx
        have hqq : q = q' :=
          walkOut_state_inj hM (h.1 x) (y := y.1) (p := y.2) (by simpa using hy)
            (by simpa using hy')
        exact hne (by rw [hqq])
      · exact h.2 x x' hxx y.1 hx hx'
  final := fun p => walkOut M p.2 M.init (T.final p.1)

lemma revComp_eval {A QT : Type} [Fintype X] [Fintype Q] (T : SST A B QT X)
    (hM : M.Reversible) (w : List A) :
    (revComp M T hM).eval w = M.eval (T.eval w) := by
  refine SST.eval_of_sim (T := T) (T' := revComp M T hM) (p := M.eval)
    (fun c c' => c'.1.1 = c.1 ∧ (∀ x q, c'.2 (x, q) = M.run q (c.2 x)) ∧
      ∀ x, ⇑(c'.1.2 x) = M.trans (c.2 x))
    ⟨rfl, fun _ _ => rfl, fun _ => rfl⟩ ?_ ?_ w
  · rintro ⟨qT, η⟩ ⟨⟨qT', τ⟩, η'⟩ a ⟨hq, hη, hτ⟩
    cases hq
    exact ⟨rfl, fun x q => subst_walkOut hη hτ q ((T.step qT a).2 x),
      fun x => walkPerm_eq hτ ((T.step qT a).2 x)⟩
  · rintro ⟨qT, η⟩ ⟨⟨qT', τ⟩, η'⟩ ⟨hq, hη, hτ⟩
    cases hq
    exact subst_walkOut hη hτ M.init (T.final qT)

end MealyRevSST

/-- **Post-composition with a reversible Mealy machine.**  For a reversible
Mealy machine the state reached after a register content is a *bijective*
function of the state in which that content is entered, so the family of
registers `X_q` (`q` a state of the machine), holding the image of the content
of `X` under the machine started in `q`, can be updated copylessly. -/
theorem isSST_comp_reversibleMealy {Q : Type} [Finite Q] {f : List A → List B}
    (hf : IsSST f) (M : Mealy B C Q) (hM : M.Reversible) :
    IsSST (fun w => M.eval (f w)) := by
  obtain ⟨QT, X, hQT, hX, T, rfl⟩ := hf
  haveI := hQT
  haveI : Fintype Q := Fintype.ofFinite Q
  exact ⟨QT × (X → Equiv.Perm Q), X × Q, inferInstance, inferInstance,
    MealyRevSST.revComp M T hM, funext fun w => MealyRevSST.revComp_eval M T hM w⟩

end Lax916827Proofs.Transducers
