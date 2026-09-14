/-
Annotating the gaps of the input with the behaviour of the sub-machine.

Fix a `(k+1)`-pebble automaton `N`.  By `RequestProject/PartD/PebbleSub.lean`, what happens above
the bottom pebble sitting at the gap `p` of `w` is a run of the `k`-pebble automaton
`subAut N c r₁` on the marked string `markSplit w p`.  If the languages of the `k`-pebble automata
are regular -- which is the induction hypothesis of the proof of Theorem
`thm:pebble-are-continuous` -- then the whole *gap data* at `p`, that is the function

  `(c, r₁) ↦ the outcome of the run above a bottom pebble at p entered in the state r₁`,

is determined by the state reached by a single finite automaton on `markSplit w p`.  Since that
state is computed from the prefix and the suffix of `w` at the gap `p`, the map that annotates
every gap of `w` with its gap data is computed by a bimachine, hence is continuous.
-/
import Lax194892Proofs.Source.PartD.PebbleSub
import Lax132576Proofs.Source.PartB.Bimachine
import Lax916827Proofs.Source.PartC.Statements
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

/-! ## A single automaton for a finite family of regular languages -/

open Classical in
/-- For a finite family of regular languages there is one finite automaton whose state after
reading a string determines the membership of that string in every language of the family. -/
theorem exists_dfa_of_family {A I : Type} [Finite I] (L : I → Language A)
    (hL : ∀ i, (L i).IsRegular) :
    ∃ (Z : Type) (_ : Fintype Z) (C : DFA A Z) (dec : Z → I → Prop),
      ∀ u i, u ∈ L i ↔ dec (C.eval u) i := by
  classical
  choose σ hσ M hM using hL
  haveI : Fintype I := Fintype.ofFinite I
  haveI : ∀ i, Fintype (σ i) := hσ
  refine ⟨(i : I) → σ i, Fintype.ofFinite _,
    { step := fun z a i => (M i).step (z i) a, start := fun i => (M i).start, accept := ∅ },
    fun z i => z i ∈ (M i).accept, ?_⟩
  have hev : ∀ (v : List A) (z : (i : I) → σ i),
      DFA.evalFrom
        { step := fun z a i => (M i).step (z i) a, start := fun i => (M i).start,
          accept := (∅ : Set ((i : I) → σ i)) } z v
        = fun i => (M i).evalFrom (z i) v := by
    intro v
    induction v with
    | nil => intro z; funext i; rfl
    | cons a v ih =>
        intro z
        rw [DFA.evalFrom_cons, ih]
        funext i
        rw [DFA.evalFrom_cons]
  intro u i
  have h1 : u ∈ (M i).accepts ↔ (M i).eval u ∈ (M i).accept := DFA.mem_accepts _
  rw [← hM i] at *
  rw [h1, DFA.eval, DFA.eval, hev]

/-! ## The gap data of a pebble automaton -/

variable {A R O : Type} {k : ℕ}

/-- The data attached to a gap of the input: for every possible pair of adjacent letters and
every state in which the bottom pebble gets covered, the outcome of the run above it. -/
abbrev GapData (A R O : Type) := (Option A × Option A) → R → Option (O ⊕ R)

open Classical in
/-- The gap data read off a marked input string. -/
noncomputable def gapVal (N : PebbleAut A R O (k + 1)) (u : List (A ⊕ A)) : GapData A R O :=
  fun c r₁ => (subAut N c r₁).answerOf u (Sum.inl (none, []))

/-! ## The annotation -/

/-- Flattening a list of singletons. -/
private lemma flatten_map_singleton {X Y : Type} (f : X → Y) (l : List X) :
    (l.map (fun x => [f x])).flatten = l.map f := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Running the suffix automaton of the annotation bimachine. -/
private lemma suffix_scan {Z : Type} (C : DFA (A ⊕ A) Z) (u : List A) :
    strTrans (fun (s : (Z → Z) × Option A) (a : A) =>
        ((fun y => s.1 (C.step y (Sum.inr a))), some a)) u.reverse (id, none)
      = ((fun y => C.evalFrom y (u.map Sum.inr)), u.head?) := by
  induction u with
  | nil => rfl
  | cons a u ih =>
      rw [List.reverse_cons]
      simp only [strTrans, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rw [show (List.foldl (fun (s : (Z → Z) × Option A) (a : A) =>
          ((fun y => s.1 (C.step y (Sum.inr a))), some a)) (id, none) u.reverse)
          = ((fun y => C.evalFrom y (u.map Sum.inr)), u.head?) from ih]
      simp only [List.map_cons, List.head?_cons, Prod.mk.injEq, and_true]
      funext y
      rw [DFA.evalFrom_cons]

/-- The annotation of the gaps of the input by the gap data is continuous, and it attaches to
the gap `i` the letter at position `i` (if any) together with the gap data at `i`. -/
theorem exists_annotation [Finite A] [Finite R] [Finite O] (N : PebbleAut A R O (k + 1))
    (hreg : ∀ (c : Option A × Option A) (r₁ : R) (x : O ⊕ R),
      Language.IsRegular {u : List (A ⊕ A) | (subAut N c r₁).Answers u (Sum.inl (none, [])) x}) :
    ∃ ann : List A → List (Option A × GapData A R O),
      Continuous ann ∧
      ∀ w : List A, ann w =
        (List.range (w.length + 1)).map (fun i => (w[i]?, gapVal N (markSplit w i))) := by
  classical
  obtain ⟨Z, hZ, C, dec, hdec⟩ :=
    exists_dfa_of_family
      (I := (Option A × Option A) × R × (O ⊕ R))
      (fun i => {u : List (A ⊕ A) | (subAut N i.1 i.2.1).Answers u (Sum.inl (none, [])) i.2.2})
      (fun i => hreg i.1 i.2.1 i.2.2)
  haveI := hZ
  -- the decoder from the state of `C` to the gap data
  set gd : Z → GapData A R O := fun z c r₁ =>
    if h : ∃ x, dec z (c, r₁, x) then some h.choose else none with hgd
  have hgdval : ∀ u : List (A ⊕ A), gapVal N u = gd (C.eval u) := by
    intro u
    funext c r₁
    have hiff : ∀ x, (subAut N c r₁).Answers u (Sum.inl (none, [])) x
        ↔ dec (C.eval u) (c, r₁, x) := fun x => hdec u (c, r₁, x)
    simp only [gapVal, hgd]
    by_cases h : ∃ x, dec (C.eval u) (c, r₁, x)
    · rw [dif_pos h]
      exact PebbleAut.answerOf_eq_some_iff.2 ((hiff _).2 h.choose_spec)
    · rw [dif_neg h]
      refine PebbleAut.answerOf_eq_none_iff.2 (fun x hx => h ⟨x, (hiff x).1 hx⟩)
  -- the annotation bimachine
  set BM : Bimachine A (Option A × GapData A R O) Z ((Z → Z) × Option A) :=
    { prefixInit := C.start
      prefixStep := fun z a => C.step z (Sum.inl a)
      suffixInit := (id, none)
      suffixStep := fun s a => ((fun y => s.1 (C.step y (Sum.inr a))), some a)
      out := fun z s => [(s.2, gd (s.1 z))] } with hBM
  have hpref : ∀ v : List A, strTrans BM.prefixStep v C.start = C.eval (v.map Sum.inl) := by
    intro v
    rw [DFA.eval, DFA.evalFrom, strTrans, List.foldl_map]
  have hval : ∀ w : List A, BM.eval w =
      (List.range (w.length + 1)).map (fun i => (w[i]?, gapVal N (markSplit w i))) := by
    intro w
    rw [Bimachine.eval]
    have hout : ∀ i, BM.out (strTrans BM.prefixStep (w.take i) BM.prefixInit)
        (strTrans BM.suffixStep (w.drop i).reverse BM.suffixInit)
        = [(w[i]?, gapVal N (markSplit w i))] := by
      intro i
      rw [show BM.prefixInit = C.start from rfl, hpref,
        show BM.suffixStep = (fun (s : (Z → Z) × Option A) (a : A) =>
          ((fun y => s.1 (C.step y (Sum.inr a))), some a)) from rfl,
        show BM.suffixInit = ((id : Z → Z), (none : Option A)) from rfl,
        suffix_scan C (w.drop i)]
      show [((w.drop i).head?, gd (C.evalFrom (C.eval ((w.take i).map Sum.inl))
        ((w.drop i).map Sum.inr)))] = _
      rw [List.head?_drop, hgdval, markSplit, DFA.eval, DFA.evalFrom_of_append]
    rw [List.map_congr_left (fun i _ => hout i),
      flatten_map_singleton (fun i => (w[i]?, gapVal N (markSplit w i)))]
  refine ⟨BM.eval, ?_, hval⟩
  exact continuous_of_isRationalFun
    (rationalFun_of_isBimachine ⟨Z, (Z → Z) × Option A, inferInstance, inferInstance, BM, rfl⟩)

end Lax194892Proofs.Transducers
