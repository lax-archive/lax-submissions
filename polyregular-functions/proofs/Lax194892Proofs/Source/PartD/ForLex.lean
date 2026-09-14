/-
Part D: for-transducers -- the lexicographic order on the tuples of a nest of loops.

A nest of loops visits the tuples of positions in the lexicographic order given by the directions
of its loops (`Transducers.exec_nestLoops`).  This file makes that order explicit, as
`Transducers.LexLt`, proves that `Transducers.tuplesOf` is sorted and repetition-free for it, and
provides the tests of a for-transducer that compare two tuples held in position variables.  All of
this is used in the proof of Lemma `lem:for-closed-under-composition`, where the positions of the
output of the inner for-transducer are represented by tuples of positions of the input.
-/
import Lax194892Proofs.Source.PartD.ForPrenex

namespace Lax194892Proofs.Transducers

open scoped Classical

variable {A B : Type}

/-! ## The lexicographic order of a list of directions -/

/-- The strict lexicographic order on tuples of positions: the first coordinate where the tuples
differ decides, in the direction of the loop that binds it. -/
def LexLt : List Bool → List ℕ → List ℕ → Prop
  | d :: ds, a :: t, b :: u => (if d then a < b else b < a) ∨ (a = b ∧ LexLt ds t u)
  | _, _, _ => False

@[simp] lemma lexLt_nil (t u : List ℕ) : ¬ LexLt [] t u := by
  cases t <;> cases u <;> exact fun h => h

@[simp] lemma lexLt_nil_left (ds : List Bool) (u : List ℕ) : ¬ LexLt ds [] u := by
  cases ds <;> cases u <;> exact fun h => h

@[simp] lemma lexLt_nil_right (ds : List Bool) (t : List ℕ) : ¬ LexLt ds t [] := by
  cases ds <;> cases t <;> exact fun h => h

@[simp] lemma lexLt_cons (d : Bool) (ds : List Bool) (a b : ℕ) (t u : List ℕ) :
    LexLt (d :: ds) (a :: t) (b :: u)
      ↔ ((if d then a < b else b < a) ∨ (a = b ∧ LexLt ds t u)) := Iff.rfl

lemma lexLt_irrefl : ∀ (ds : List Bool) (t : List ℕ), ¬ LexLt ds t t := by
  intro ds
  induction ds with
  | nil => simp
  | cons d ds ih =>
      intro t
      cases t with
      | nil => simp
      | cons a t =>
          rw [lexLt_cons]
          rintro (h | ⟨-, h⟩)
          · cases d <;> simp at h
          · exact ih t h

lemma lexLt_trans : ∀ (ds : List Bool) (t u v : List ℕ),
    LexLt ds t u → LexLt ds u v → LexLt ds t v := by
  intro ds
  induction ds with
  | nil => simp
  | cons d ds ih =>
      intro t u v
      cases t with
      | nil => simp
      | cons a t =>
        cases u with
        | nil => simp
        | cons b u =>
          cases v with
          | nil => simp
          | cons c v =>
            rw [lexLt_cons, lexLt_cons, lexLt_cons]
            rintro (h1 | ⟨rfl, h1⟩) (h2 | ⟨rfl, h2⟩)
            · exact Or.inl (by cases d <;> simp at h1 h2 ⊢ <;> omega)
            · exact Or.inl h1
            · exact Or.inl h2
            · exact Or.inr ⟨rfl, ih _ _ _ h1 h2⟩

lemma lexLt_asymm (ds : List Bool) (t u : List ℕ) (h : LexLt ds t u) : ¬ LexLt ds u t :=
  fun h' => lexLt_irrefl ds t (lexLt_trans ds t u t h h')

lemma lexLt_trichotomy : ∀ (ds : List Bool) (t u : List ℕ), t.length = ds.length →
    u.length = ds.length → LexLt ds t u ∨ t = u ∨ LexLt ds u t := by
  intro ds
  induction ds with
  | nil =>
      intro t u ht hu
      simp at ht hu
      exact Or.inr (Or.inl (by rw [ht, hu]))
  | cons d ds ih =>
      intro t u ht hu
      cases t with
      | nil => simp at ht
      | cons a t =>
        cases u with
        | nil => simp at hu
        | cons b u =>
          simp only [List.length_cons, Nat.add_right_cancel_iff] at ht hu
          rcases lt_trichotomy a b with h | rfl | h
          · cases d
            · exact Or.inr (Or.inr (Or.inl (by simpa using h)))
            · exact Or.inl (Or.inl (by simpa using h))
          · rcases ih t u ht hu with h | rfl | h
            · exact Or.inl (Or.inr ⟨rfl, h⟩)
            · exact Or.inr (Or.inl rfl)
            · exact Or.inr (Or.inr (Or.inr ⟨rfl, h⟩))
          · cases d
            · exact Or.inl (Or.inl (by simpa using h))
            · exact Or.inr (Or.inr (Or.inl (by simpa using h)))

/-! ## The tuples of a nest are sorted -/

lemma sorted_loopRange (d : Bool) (n : ℕ) :
    (loopRange d n).Pairwise (fun a b => if d then a < b else b < a) := by
  cases d
  · simpa [loopRange, List.pairwise_reverse] using
      (List.pairwise_lt_range (n := n)).imp (fun {a b} h => h)
  · simpa [loopRange] using List.pairwise_lt_range (n := n)

lemma sorted_tuplesOf (L : List (Bool × ℕ)) (n : ℕ) :
    (tuplesOf L n).Pairwise (LexLt (L.map Prod.fst)) := by
  induction L with
  | nil => simp
  | cons a L ih =>
      obtain ⟨d, x⟩ := a
      rw [tuplesOf_cons]
      simp only [List.map_cons]
      rw [List.pairwise_flatMap]
      constructor
      · intro p _
        rw [List.pairwise_map]
        exact ih.imp (fun {t u} h => Or.inr ⟨rfl, h⟩)
      · refine (sorted_loopRange d n).imp ?_
        intro p q hpq t ht u hu
        simp only [List.mem_map] at ht hu
        obtain ⟨t', -, rfl⟩ := ht
        obtain ⟨u', -, rfl⟩ := hu
        exact Or.inl hpq

lemma nodup_tuplesOf (L : List (Bool × ℕ)) (n : ℕ) : (tuplesOf L n).Nodup := by
  refine (sorted_tuplesOf L n).imp ?_
  intro t u h heq
  subst heq
  exact lexLt_irrefl _ t h

/-! ## Splitting the tuples at a given one -/

/-- A sorted list splits at any of its members into the elements below it, the element, and the
elements above it. -/
lemma sorted_split {α : Type} (r : α → α → Prop) [DecidableRel r] (l : List α)
    (hs : l.Pairwise r) (hirr : ∀ a, ¬ r a a) (hasymm : ∀ a b, r a b → ¬ r b a)
    (htri : ∀ a b, a ∈ l → b ∈ l → r a b ∨ a = b ∨ r b a) (z : α) (hz : z ∈ l) :
    l = l.filter (fun t => decide (r t z)) ++ z :: l.filter (fun t => decide (r z t)) := by
  induction l with
  | nil => simp at hz
  | cons a l ih =>
      rcases List.mem_cons.mp hz with rfl | hz'
      · have h1 : (z :: l).filter (fun t => decide (r t z)) = [] := by
          rw [List.filter_cons_of_neg (by simp [hirr z])]
          refine List.filter_eq_nil_iff.mpr (fun t ht => ?_)
          simp only [decide_eq_true_eq]
          exact hasymm z t (List.rel_of_pairwise_cons hs ht)
        have h2 : (z :: l).filter (fun t => decide (r z t)) = l := by
          rw [List.filter_cons_of_neg (by simp [hirr z])]
          refine List.filter_eq_self.mpr (fun t ht => ?_)
          simp only [decide_eq_true_eq]
          exact List.rel_of_pairwise_cons hs ht
        rw [h1, h2]
        simp
      · have hra : r a z := List.rel_of_pairwise_cons hs hz'
        have hnza : ¬ r z a := hasymm a z hra
        rw [List.filter_cons_of_pos (by simp [hra]), List.filter_cons_of_neg (by simp [hnza])]
        rw [List.cons_append]
        refine congrArg (a :: ·) ?_
        exact ih hs.of_cons (fun b c hb hc => htri b c (List.mem_cons_of_mem _ hb)
          (List.mem_cons_of_mem _ hc)) hz'

lemma tuplesOf_split (L : List (Bool × ℕ)) (n : ℕ) (z : List ℕ) (hz : z ∈ tuplesOf L n) :
    tuplesOf L n
      = (tuplesOf L n).filter (fun t => decide (LexLt (L.map Prod.fst) t z)) ++
        z :: (tuplesOf L n).filter (fun t => decide (LexLt (L.map Prod.fst) z t)) := by
  refine sorted_split _ _ (sorted_tuplesOf L n) (lexLt_irrefl _) (lexLt_asymm _) ?_ z hz
  intro t u ht hu
  refine lexLt_trichotomy _ t u ?_ ?_
  · rw [length_of_mem_tuplesOf L n ht]; simp
  · rw [length_of_mem_tuplesOf L n hu]; simp

/-! ## Reversing all the loops -/

/-- Reversing the direction of every loop of a nest. -/
def negDirs (L : List (Bool × ℕ)) : List (Bool × ℕ) := L.map (fun a => (!a.1, a.2))

@[simp] lemma negDirs_nil : negDirs [] = [] := rfl

@[simp] lemma negDirs_cons (d : Bool) (x : ℕ) (L : List (Bool × ℕ)) :
    negDirs ((d, x) :: L) = (!d, x) :: negDirs L := rfl

@[simp] lemma map_snd_negDirs (L : List (Bool × ℕ)) :
    (negDirs L).map Prod.snd = L.map Prod.snd := by
  induction L with
  | nil => rfl
  | cons a L ih => obtain ⟨d, x⟩ := a; simp [negDirs]

lemma loopRange_not (d : Bool) (n : ℕ) : loopRange (!d) n = (loopRange d n).reverse := by
  cases d <;> simp [loopRange]

lemma reverse_flatMap {α β : Type} (l : List α) (f : α → List β) :
    (l.flatMap f).reverse = l.reverse.flatMap (fun a => (f a).reverse) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [List.flatMap_cons, ih]

/-- Reversing every loop of a nest reverses the order in which it visits the tuples. -/
lemma tuplesOf_negDirs (L : List (Bool × ℕ)) (n : ℕ) :
    tuplesOf (negDirs L) n = (tuplesOf L n).reverse := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      obtain ⟨d, x⟩ := a
      rw [negDirs_cons, tuplesOf_cons, tuplesOf_cons, loopRange_not, ih, reverse_flatMap]
      refine congrArg (fun f => (loopRange d n).reverse.flatMap f) ?_
      funext p
      rw [List.map_reverse]

/-! ## Comparing two tuples of position variables -/

/-- The test comparing two position variables in the direction of a loop. -/
def ltTest (d : Bool) (x y : ℕ) : ForTest A :=
  if d then ForTest.and (ForTest.lePos x y) (ForTest.not (ForTest.eqPos x y))
  else ForTest.and (ForTest.lePos y x) (ForTest.not (ForTest.eqPos x y))

/-- The test comparing two tuples of position variables in the lexicographic order. -/
def lexLtTest : List Bool → List ℕ → List ℕ → ForTest A
  | d :: ds, x :: xs, y :: ys =>
      ForTest.or (ltTest d x y) (ForTest.and (ForTest.eqPos x y) (lexLtTest ds xs ys))
  | _, _, _ => ForTest.not (ForTest.eqPos 0 0)

lemma holds_ltTest (w : List A) (pos : ℕ → ℕ) (bv : ℕ → Bool) (d : Bool) (x y : ℕ) :
    ForTest.Holds w pos bv (ltTest d x y : ForTest A)
      ↔ (if d then pos x < pos y else pos y < pos x) := by
  cases d <;> simp [ltTest, ForTest.Holds] <;> omega

lemma holds_lexLtTest (w : List A) (pos : ℕ → ℕ) (bv : ℕ → Bool) :
    ∀ (ds : List Bool) (xs ys : List ℕ),
      ForTest.Holds w pos bv (lexLtTest ds xs ys : ForTest A)
        ↔ LexLt ds (xs.map pos) (ys.map pos) := by
  intro ds
  induction ds with
  | nil => intro xs ys; simp [lexLtTest, ForTest.Holds]
  | cons d ds ih =>
      intro xs ys
      cases xs with
      | nil => simp [lexLtTest, ForTest.Holds]
      | cons x xs =>
        cases ys with
        | nil => simp [lexLtTest, ForTest.Holds]
        | cons y ys =>
          show (ForTest.Holds w pos bv (ltTest d x y) ∨
            ForTest.Holds w pos bv (ForTest.and (ForTest.eqPos x y)
              (lexLtTest ds xs ys : ForTest A))) ↔ _
          rw [holds_ltTest]
          simp only [List.map_cons, lexLt_cons]
          constructor
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨h1, (ih xs ys).mp h2⟩
          · rintro (h | ⟨h1, h2⟩)
            · exact Or.inl h
            · exact Or.inr ⟨h1, (ih xs ys).mpr h2⟩

/-- The test saying that two tuples of position variables are equal. -/
def eqTupleTest : List ℕ → List ℕ → ForTest A
  | x :: xs, y :: ys => ForTest.and (ForTest.eqPos x y) (eqTupleTest xs ys)
  | _, _ => ForTest.eqPos 0 0

lemma holds_eqTupleTest (w : List A) (pos : ℕ → ℕ) :
    ∀ (xs ys : List ℕ) (bv : ℕ → Bool), xs.length = ys.length →
      (ForTest.Holds w pos bv (eqTupleTest xs ys : ForTest A)
        ↔ xs.map pos = ys.map pos) := by
  intro xs
  induction xs with
  | nil => intro ys bv h; cases ys <;> simp_all [eqTupleTest, ForTest.Holds]
  | cons x xs ih =>
      intro ys bv h
      cases ys with
      | nil => simp at h
      | cons y ys =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at h
        show (pos x = pos y ∧ ForTest.Holds w pos bv (eqTupleTest xs ys : ForTest A)) ↔ _
        rw [ih ys bv h]
        simp

end Lax194892Proofs.Transducers
