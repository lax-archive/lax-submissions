/- Normalised streaming string transducers, and the reduction of an arbitrary sst to a normalised
one (a step in the proof of Theorem `theorem:sst-two-way-equivalence` of *Transducers*, M.
Bojańczyk).

The two-way transducer that simulates an sst has to perform a depth-first
traversal of the register flow tree.  Two features of the definition of an sst
get in the way of such a traversal, and both are removed here:

* the register update applied at a position depends on the *state* of the sst
  before that position, which the two-way transducer cannot see.  This is
  repaired by annotating every input letter with that state; the annotation is
  computed by a Mealy machine, hence is a rational function, and two-way
  transducers are closed under pre-composition with rational functions.

* a register may occur *several times* in the final output string `final q`
  (the copyless restriction constrains only the register updates), so the place
  at which the traversal has to be resumed when the content of a register has
  been output would not be determined by the register.  This is repaired by
  keeping `K + 1` copies of every register, where `K` bounds the number of
  register occurrences in a final output string: all the copies of a register
  hold the same value, and the occurrences in a final output string are given
  pairwise distinct copies.
-/
import Lax916827Proofs.Source.PartC.SSTBasic
import Lax765601Proofs.Source.PartA.MealyBasic
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-- A *normalised* streaming string transducer: the register update applied when
reading a letter depends only on that letter, the state after reading a string
depends only on its last letter, and no register occurs twice in a final output
string. -/
structure NSST (A B Q X : Type) [Fintype X] where
  /-- The state of the empty input. -/
  init : Q
  /-- The state after a string ending with the given letter. -/
  nxt : A → Q
  /-- The register update of a letter. -/
  upd : A → X → List (X ⊕ B)
  /-- Register updates are copyless. -/
  upd_copyless : ∀ a, Copyless (upd a)
  /-- The final output function. -/
  final : Q → List (X ⊕ B)
  /-- No register occurs twice in a final output string. -/
  final_nodup : ∀ q, (regsOf (final q)).Nodup

namespace NSST

variable {A B Q X : Type} [Fintype X]

/-- The state determined by the last letter of the input (`none` if empty). -/
def stateOf (N : NSST A B Q X) : Option A → Q
  | none => N.init
  | some a => N.nxt a

/-- The state after reading a string. -/
def state (N : NSST A B Q X) (w : List A) : Q := N.stateOf w.getLast?

/-- The register valuation after reading a string, from a given valuation. -/
def valFrom (N : NSST A B Q X) (η : X → List B) (w : List A) : X → List B :=
  w.foldl (fun η a x => SST.subst η (N.upd a x)) η

/-- The register valuation after reading a string. -/
def val (N : NSST A B Q X) (w : List A) : X → List B := N.valFrom (fun _ => []) w

/-- The semantics of a normalised sst. -/
def eval (N : NSST A B Q X) (w : List A) : List B :=
  SST.subst (N.val w) (N.final (N.state w))

@[simp] lemma val_nil (N : NSST A B Q X) : N.val [] = fun _ => [] := rfl

lemma valFrom_append (N : NSST A B Q X) (η : X → List B) (u v : List A) :
    N.valFrom η (u ++ v) = N.valFrom (N.valFrom η u) v := by
  simp [valFrom, List.foldl_append]

lemma val_concat (N : NSST A B Q X) (u : List A) (a : A) (x : X) :
    N.val (u ++ [a]) x = SST.subst (N.val u) (N.upd a x) := by
  simp [val, valFrom]

end NSST

/-! ## Tagging registers with copies -/

section Tag

variable {X B T : Type}

/-- Replace every register `x` of a string over `X + B` by the copy `(x, k)`. -/
def mapRegTag (k : T) (s : List (X ⊕ B)) : List ((X × T) ⊕ B) :=
  s.map (fun z => match z with | Sum.inl x => Sum.inl (x, k) | Sum.inr b => Sum.inr b)

@[simp] lemma mapRegTag_nil (k : T) : mapRegTag k ([] : List (X ⊕ B)) = [] := rfl

@[simp] lemma mapRegTag_cons_inl (k : T) (x : X) (s : List (X ⊕ B)) :
    mapRegTag k (Sum.inl x :: s) = Sum.inl (x, k) :: mapRegTag k s := rfl

@[simp] lemma mapRegTag_cons_inr (k : T) (b : B) (s : List (X ⊕ B)) :
    mapRegTag k (Sum.inr b :: s) = Sum.inr b :: mapRegTag k s := rfl

lemma regsOf_mapRegTag (k : T) (s : List (X ⊕ B)) :
    regsOf (mapRegTag k s) = (regsOf s).map (fun x => (x, k)) := by
  induction s with
  | nil => rfl
  | cons z s ih => cases z <;> simp [ih]

lemma subst_mapRegTag {η : X → List B} {η' : X × T → List B}
    (h : ∀ x k, η' (x, k) = η x) (k : T) (s : List (X ⊕ B)) :
    SST.subst η' (mapRegTag k s) = SST.subst η s := by
  induction s with
  | nil => rfl
  | cons z s ih => cases z <;> simp [ih, h]

/-- Tag the register occurrences of a string with pairwise distinct copies,
taken in order from the given list of tags. -/
def tagWith : List (X ⊕ B) → List T → List ((X × T) ⊕ B)
  | [], _ => []
  | Sum.inr b :: s, ks => Sum.inr b :: tagWith s ks
  | Sum.inl _ :: _, [] => []
  | Sum.inl x :: s, k :: ks => Sum.inl (x, k) :: tagWith s ks

lemma subst_tagWith {η : X → List B} {η' : X × T → List B}
    (h : ∀ x k, η' (x, k) = η x) :
    ∀ (s : List (X ⊕ B)) (ks : List T), (regsOf s).length ≤ ks.length →
      SST.subst η' (tagWith s ks) = SST.subst η s
  | [], _, _ => rfl
  | Sum.inr b :: s, ks, hlen => by
      simp only [tagWith, SST.subst_cons_inr]
      rw [subst_tagWith h s ks (by simpa [regsOf] using hlen)]
  | Sum.inl _ :: _, [], hlen => by simp [regsOf] at hlen
  | Sum.inl x :: s, k :: ks, hlen => by
      simp only [tagWith, SST.subst_cons_inl, h]
      have : (regsOf s).length ≤ ks.length := by
        simp only [regsOf.cons_inl, List.length_cons] at hlen
        omega
      rw [subst_tagWith h s ks this]

lemma tags_tagWith_sublist :
    ∀ (s : List (X ⊕ B)) (ks : List T), List.Sublist ((regsOf (tagWith s ks)).map Prod.snd) ks
  | [], ks => by simp [tagWith]
  | Sum.inr _ :: s, ks => by simpa [tagWith] using tags_tagWith_sublist s ks
  | Sum.inl _ :: _, [] => by simp [tagWith]
  | Sum.inl _ :: s, k :: ks => by
      simp only [tagWith, regsOf.cons_inl, List.map_cons]
      exact List.Sublist.cons₂ _ (tags_tagWith_sublist s ks)

lemma nodup_regsOf_tagWith (s : List (X ⊕ B)) {ks : List T} (hks : ks.Nodup) :
    (regsOf (tagWith s ks)).Nodup :=
  List.Nodup.of_map Prod.snd ((tags_tagWith_sublist s ks).nodup hks)

end Tag

/-! ## From an sst to a normalised sst -/

namespace SSTNorm

variable {A B Q X : Type} [Fintype X]

/-- The Mealy machine that annotates every letter with the state of the sst
before that letter. -/
def annot (T : SST A B Q X) : Mealy A (Q × A) Q where
  init := T.init
  step := fun q a => ((T.step q a).1, (q, a))

lemma annot_trans (T : SST A B Q X) (w : List A) :
    (annot T).trans w T.init = (T.runConfig w).1 := by
  have key : ∀ (w : List A) (c : Q × (X → List B)),
      (annot T).trans w c.1 = (w.foldl T.stepConfig c).1 := by
    intro w
    induction w with
    | nil => intro c; rfl
    | cons a w ih =>
        intro c
        rw [Mealy.trans_cons]
        exact ih (T.stepConfig c a)
  exact key w (T.init, fun _ => [])

/-- The register update of the normalised sst: the copy `(x, k)` is updated by
the update of `x`, with all its registers replaced by their `k`-th copies. -/
def updOf (T : SST A B Q X) (K : ℕ) (qa : Q × A) (y : X × Fin (K + 1)) :
    List ((X × Fin (K + 1)) ⊕ B) :=
  mapRegTag y.2 ((T.step qa.1 qa.2).2 y.1)

lemma updOf_copyless (T : SST A B Q X) (K : ℕ) (qa : Q × A) : Copyless (updOf T K qa) := by
  obtain ⟨q, a⟩ := qa
  obtain ⟨h1, h2⟩ := (copyless_iff _).1 (T.step_copyless q a)
  refine (copyless_iff _).2 ⟨?_, ?_⟩
  · rintro ⟨x, k⟩
    show (regsOf (mapRegTag k ((T.step q a).2 x))).Nodup
    rw [regsOf_mapRegTag]
    exact (h1 x).map (fun _ _ h => (Prod.mk.injEq _ _ _ _ ▸ h).1)
  · rintro ⟨x, k⟩ ⟨x', k'⟩ hne ⟨y, j⟩ hy hy'
    rw [show regsOf (updOf T K (q, a) (x, k)) = _ from regsOf_mapRegTag _ _, List.mem_map] at hy
    rw [show regsOf (updOf T K (q, a) (x', k')) = _ from regsOf_mapRegTag _ _, List.mem_map] at hy'
    obtain ⟨y1, hy1, he1⟩ := hy
    obtain ⟨y2, hy2, he2⟩ := hy'
    rw [Prod.mk.injEq] at he1 he2
    have hk : k = k' := he1.2.trans he2.2.symm
    have hx : x ≠ x' := by rintro rfl; exact hne (by rw [hk])
    exact h2 x x' hx y (he1.1 ▸ hy1) (he2.1 ▸ hy2)

/-- The normalised sst associated with an sst, over the annotated alphabet. -/
def norm (T : SST A B Q X) (K : ℕ) : NSST (Q × A) B Q (X × Fin (K + 1)) where
  init := T.init
  nxt := fun qa => (T.step qa.1 qa.2).1
  upd := updOf T K
  upd_copyless := updOf_copyless T K
  final := fun q => tagWith (T.final q) (List.finRange (K + 1))
  final_nodup := fun _ => nodup_regsOf_tagWith _ (List.nodup_finRange _)

lemma norm_valFrom (T : SST A B Q X) (K : ℕ) :
    ∀ (w : List A) (q : Q) (η : X → List B) (η' : X × Fin (K + 1) → List B),
      (∀ x k, η' (x, k) = η x) → ∀ (x : X) (k : Fin (K + 1)),
        (norm T K).valFrom η' ((annot T).run q w) (x, k) = (w.foldl T.stepConfig (q, η)).2 x := by
  intro w
  induction w with
  | nil => intro q η η' h x k; exact h x k
  | cons a w ih =>
      intro q η η' h x k
      have hstep : (norm T K).valFrom η' ((annot T).run q (a :: w))
          = (norm T K).valFrom (fun y => SST.subst η' ((norm T K).upd (q, a) y))
              ((annot T).run (T.step q a).1 w) := rfl
      rw [hstep]
      refine ih (T.step q a).1 (fun x => SST.subst η ((T.step q a).2 x)) _ ?_ x k
      intro x' k'
      exact subst_mapRegTag h k' ((T.step q a).2 x')

lemma norm_val (T : SST A B Q X) (K : ℕ) (w : List A) (x : X) (k : Fin (K + 1)) :
    (norm T K).val ((annot T).eval w) (x, k) = (T.runConfig w).2 x :=
  norm_valFrom T K w T.init (fun _ => []) (fun _ => []) (fun _ _ => rfl) x k

lemma norm_state (T : SST A B Q X) (K : ℕ) (w : List A) :
    (norm T K).state ((annot T).eval w) = (T.runConfig w).1 := by
  rcases List.eq_nil_or_concat w with rfl | ⟨u, a, rfl⟩
  · rfl
  · simp only [List.concat_eq_append]
    have hev : (annot T).eval (u ++ [a]) = (annot T).eval u ++ [((T.runConfig u).1, a)] := by
      rw [Mealy.eval_append, show (annot T).init = T.init from rfl, annot_trans]
      rfl
    have hrun : T.runConfig (u ++ [a]) = T.stepConfig (T.runConfig u) a := by
      rw [SST.runConfig_append]; rfl
    rw [NSST.state, hev, List.getLast?_concat, hrun]
    rfl

end SSTNorm

open SSTNorm in
/-- Every sst is, after annotating every input letter with the state of the sst
before that letter, computed by a normalised sst. -/
theorem exists_nsst_of_sst {A B Q X : Type} [Finite Q] [Fintype X] (T : SST A B Q X) :
    ∃ (Y : Type) (instY : Fintype Y) (N : @NSST (Q × A) B Q Y instY),
      ∀ w : List A, N.eval ((annot T).eval w) = T.eval w := by
  classical
  haveI : Fintype Q := Fintype.ofFinite Q
  set K : ℕ := Finset.univ.sup (fun q : Q => (regsOf (T.final q)).length) with hK
  have hKle : ∀ q : Q, (regsOf (T.final q)).length ≤ K := fun q =>
    Finset.le_sup (f := fun q : Q => (regsOf (T.final q)).length) (Finset.mem_univ q)
  refine ⟨X × Fin (K + 1), inferInstance, norm T K, fun w => ?_⟩
  have hlen : (regsOf (T.final (T.runConfig w).1)).length ≤ (List.finRange (K + 1)).length := by
    rw [List.length_finRange]
    exact le_trans (hKle _) (Nat.le_succ K)
  show SST.subst ((norm T K).val ((annot T).eval w))
      ((norm T K).final ((norm T K).state ((annot T).eval w))) = _
  rw [norm_state]
  exact subst_tagWith (η := (T.runConfig w).2) (fun x k => norm_val T K w x k) _ _ hlen

end Lax916827Proofs.Transducers
