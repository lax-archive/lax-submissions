/-
The *neighbouring-block map combinator* is a regular operation.

This is the content of stages 1--3 of the induction step in the book's proof of
the snake lemma (see `RequestProject/PartC/SnakeReg.lean` and Section *Two-way transducers* of
*Transducers*, M. Bojańczyk).  There, a string

  `w₀ # w₁ # ⋯ # wₙ`

whose separators mark the record-breaking columns of a run has to be turned into

  `(w₀ # w₁) (w₁ # w₂) ⋯ (wₙ₋₁ # wₙ)`,

so that the map combinator of Lemma `lem:regular-closure-properties` can then be applied to each of
the blocks `wᵢ₋₁ # wᵢ`, which is where the loop part and the progress part of the `i`-th
record-breaker live.  The book performs this stage with map duplicate, which procures the two copies
of every `wᵢ` that are needed, and rational functions, which arrange the brackets and remove the
extra copies of `w₀` and of `wₙ`.

The main result is `Transducers.isRegularFun_pairMap`: if `f` is regular, then
so is

  `w₀ # ⋯ # wₙ  ↦  f (w₀ # w₁) · f (w₁ # w₂) ⋯ f (wₙ₋₁ # wₙ)`.

The construction is the one of the book.  A rational function appends a copy of
the separator at the end of every block, producing `w₀$ # w₁$ # ⋯ # wₙ$`; map
duplicate turns this into `w₀$w₀$ # ⋯ # wₙ$wₙ$`; and a *bilateral rewriting*
(`RequestProject/PartC/RatBi.lean`) -- which is what makes the two exceptional
blocks, the first and the last, treatable -- deletes the first copy of `w₀` and
the second copy of `wₙ` and re-brackets the rest.  Finally the map lifting of
`f` (Lemma `lem:regular-closure-properties`) is applied and a homomorphism erases the separators.
-/
import Lax916827Proofs.Source.PartC.RatBi
import Lax916827Proofs.Source.PartC.RegClosure
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace RegPair

open RegCl

variable {A B : Type}

/-! ## Strings presented as lists of blocks -/

/-- The string `b₀ # b₁ # ⋯ # bₙ` over `A + 1` with the blocks `b₀, …, bₙ`. -/
def blockStr (bs : List (List A)) : List (Option A) :=
  List.intercalate [none] (bs.map (fun b => b.map some))

@[simp] lemma blockStr_singleton (b : List A) : blockStr [b] = b.map some := by
  simp [blockStr, List.intercalate]

lemma blockStr_cons (b : List A) (bs : List (List A)) (hbs : bs ≠ []) :
    blockStr (b :: bs) = b.map some ++ none :: blockStr bs := by
  rw [blockStr, List.map_cons, intercalate_cons_cons _ _ _ (by simpa using hbs), blockStr,
    List.append_assoc]
  rfl

/-- Prefixing a letter to the first block prefixes it to the string. -/
lemma blockStr_cons_letter (a : A) (b : List A) (bs : List (List A)) :
    blockStr ((a :: b) :: bs) = some a :: blockStr (b :: bs) := by
  rcases bs with _ | ⟨c, cs⟩
  · simp
  · rw [blockStr_cons (a :: b) (c :: cs) (by simp), blockStr_cons b (c :: cs) (by simp)]
    simp

lemma splitSep_blockStr (bs : List (List A)) (hbs : bs ≠ []) : splitSep (blockStr bs) = bs :=
  splitSep_intercalate bs hbs

lemma mapLift_eq_blockStr (f : List A → List B) (w : List (Option A)) :
    mapLift f w = blockStr ((splitSep w).map f) := by
  rw [mapLift, blockStr, List.map_map]
  rfl

lemma mapLift_blockStr (f : List A → List B) (bs : List (List A)) (hbs : bs ≠ []) :
    mapLift f (blockStr bs) = blockStr (bs.map f) := by
  rw [mapLift_eq_blockStr, splitSep_blockStr bs hbs]

lemma del_blockStr (bs : List (List B)) : del (blockStr bs) = bs.flatten := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
      rcases bs with _ | ⟨c, cs⟩
      · simp only [blockStr_singleton, List.flatten_cons, List.flatten_nil, List.append_nil]
        have : ∀ v : List B, del (v.map some) = v := by
          intro v; induction v with
          | nil => rfl
          | cons x v ih2 => simpa [del, homOf] using ih2
        exact this b
      · rw [blockStr_cons _ _ (by simp)]
        have hd : ∀ (v : List B) (z : List (Option B)),
            del (v.map some ++ z) = v ++ del z := by
          intro v z; induction v with
          | nil => rfl
          | cons x v ih2 => simpa [del, homOf] using ih2
        rw [hd, show del (none :: blockStr (c :: cs)) = del (blockStr (c :: cs)) from rfl, ih]
        simp

/-- `splitSep u` has a nonempty tail exactly when `u` uses the separator. -/
lemma splitSep_tail_ne_nil_iff (u : List (Option A)) :
    (splitSep u).tail ≠ [] ↔ (none : Option A) ∈ u := by
  induction u with
  | nil => simp [splitSep]
  | cons x u ih =>
      cases x with
      | none => simp [splitSep, splitSep_ne_nil u]
      | some a =>
          rcases hu : splitSep u with _ | ⟨b, bs⟩
          · exact absurd hu (splitSep_ne_nil u)
          · rw [show splitSep (some a :: u) = (a :: b) :: bs by rw [splitSep, hu]]
            rw [hu] at ih
            simpa using ih

/-! ## Stage 1: a copy of the separator at the end of every block -/

/-- The block `w` with a copy of the separator appended. -/
def dollar (w : List A) : List (Option A) := w.map some ++ [none]

/-- The image of a letter under the first stage. -/
def enc1 : Option A → List (Option (Option A))
  | some a => [some (some a)]
  | none => [some none, none]

/-- **Stage 1**: `w₀ # ⋯ # wₙ ↦ w₀$ # ⋯ # wₙ$`, where the copy `$` of the
separator that ends each block is the letter `some none`. -/
def step1 : List (Option A) → List (Option (Option A))
  | [] => [some none]
  | x :: w => enc1 x ++ step1 w

lemma step1_eq (u : List (Option A)) :
    step1 u = blockStr ((splitSep u).map dollar) := by
  induction u with
  | nil => simp [step1, splitSep, dollar]
  | cons x u ih =>
      cases x with
      | none =>
          have hne : (splitSep u).map dollar ≠ [] := by
            simpa using splitSep_ne_nil u
          rw [show splitSep (none :: u) = [] :: splitSep u from rfl, List.map_cons,
            blockStr_cons _ _ hne]
          simp [step1, enc1, dollar, ih]
      | some a =>
          rcases hu : splitSep u with _ | ⟨b, bs⟩
          · exact absurd hu (splitSep_ne_nil u)
          · rw [show splitSep (some a :: u) = (a :: b) :: bs by rw [splitSep, hu]]
            rw [hu] at ih
            rw [List.map_cons, show dollar (a :: b) = some a :: dollar b from rfl,
              blockStr_cons_letter]
            rw [show step1 (some a :: u) = some (some a) :: step1 u from rfl, ih, List.map_cons]

lemma isRationalFun_step1 [Finite A] : IsRationalFun (step1 : List (Option A) → _) := by
  classical
  set psi : Unit → Option (Option A) → Option (Option A) → List (Option (Option A)) :=
    fun _ _ next => match next with
      | none => [some none]
      | some x => enc1 x with hpsi
  have key : ∀ (prev : Option (Option A)) (u : List (Option A)),
      ctxAux (psi ()) prev u = step1 u := by
    intro prev u
    induction u generalizing prev with
    | nil => rfl
    | cons x u ih => rw [ctxAux_cons, ih]; rfl
  have heq : ctxEval (fun _ (_ : Option A) => ()) () psi = (step1 : List (Option A) → _) :=
    funext fun u => key none u
  exact heq ▸ isRationalFun_ctxEval (fun _ (_ : Option A) => ()) () psi

/-! ## Stage 2: duplicating every block -/

lemma step2_blockStr (bs : List (List (Option A))) (hbs : bs ≠ []) :
    mapDuplicate (Option A) (blockStr bs) = blockStr (bs.map (fun b => b ++ b)) := by
  rw [mapDuplicate, mapLift_blockStr _ _ hbs]

/-! ## The pairing of the consecutive blocks -/

/-- The block `v # v'`. -/
def encPair (v v' : List A) : List (Option A) := v.map some ++ none :: v'.map some

/-- The list of the pairs of consecutive blocks: `[b₀ # b₁, b₁ # b₂, …]`. -/
def pairsList (bs : List (List A)) : List (List (Option A)) :=
  List.zipWith encPair bs bs.tail

@[simp] lemma pairsList_singleton (b : List A) : pairsList [b] = [] := rfl

lemma pairsList_cons_cons (b c : List A) (bs : List (List A)) :
    pairsList (b :: c :: bs) = encPair b c :: pairsList (c :: bs) := rfl

lemma pairsList_ne_nil (b c : List A) (bs : List (List A)) :
    pairsList (b :: c :: bs) ≠ [] := by
  rw [pairsList_cons_cons]; simp

/-- The pairs of consecutive blocks of a string over `A + 1`. -/
def pairBlocks (u : List (Option A)) : List (List (Option A)) := pairsList (splitSep u)

/-- **The neighbouring-block map combinator**: apply `f` to every pair of
consecutive blocks of the input and concatenate the results. -/
def pairMap (f : List (Option A) → List B) (u : List (Option A)) : List B :=
  ((pairBlocks u).map f).flatten

/-! ## Stage 3: re-bracketing -/

/-- The letters of a block, seen in the doubled alphabet. -/
def letStr (w : List A) : List (Option (Option A)) := w.map (fun a => some (some a))

@[simp] lemma letStr_nil : letStr ([] : List A) = [] := rfl

@[simp] lemma letStr_cons (a : A) (w : List A) :
    letStr (a :: w) = some (some a) :: letStr w := rfl

lemma map_some_map_some (w : List A) : (w.map some).map (some : Option A → _) = letStr w := by
  simp [letStr, List.map_map, Function.comp_def]

/-- The doubled block `w $ w $`. -/
def dblBlock (w : List A) : List (Option (Option A)) :=
  letStr w ++ some none :: (letStr w ++ [some none])

/-- The block `w $` duplicated, as a block of the string produced by stage 2. -/
def dupB (w : List A) : List (Option A) := dollar w ++ dollar w

lemma dupB_map_some (w : List A) : (dupB w).map (some : Option A → _) = dblBlock w := by
  simp [dupB, dollar, dblBlock, ← map_some_map_some]

/-- The prefix automaton of stage 3: whether we are still in the first block,
and whether a `$` has already been seen in the current block. -/
def mu3 : Bool × Bool → Option (Option A) → Bool × Bool
  | _, none => (false, false)
  | p, some none => (p.1, true)
  | p, some (some _) => p

/-- The suffix automaton of stage 3: whether the suffix has no separator. -/
def nu3 : Bool → Option (Option A) → Bool
  | _, none => false
  | s, some _ => s

/-- The output function of stage 3: the first copy of the first block and the
second copy of the last block are deleted, the first `$` of a block becomes a
separator and the second one stays a `$`. -/
def psi3 : Bool × Bool → Option (Option A) → Bool → List (Option (Option A))
  | _, none, _ => []
  | p, some none, s =>
      if p.2 then (if s then [] else [some none])
      else (if p.1 then [] else (if s then [] else [none]))
  | p, some (some a), s =>
      if p.2 then (if s then [] else [some (some a)])
      else (if p.1 then [] else [some (some a)])

/-- **Stage 3**: `w₀$w₀$ # ⋯ # wₙ$wₙ$ ↦ (w₀ # w₁)(w₁ # w₂) ⋯ (wₙ₋₁ # wₙ)`. -/
def step3 : List (Option (Option A)) → List (Option (Option A)) :=
  biEval mu3 (true, false) nu3 true psi3

lemma revTrans_letStr (w : List A) (t : Bool) : revTrans nu3 (letStr w) t = t := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [letStr_cons, revTrans_cons, ih]; rfl

lemma strTrans_append' {P C : Type} (μ : P → C → P) (u v : List C) (p : P) :
    strTrans μ (u ++ v) p = strTrans μ v (strTrans μ u p) := by
  simp [strTrans, List.foldl_append]

lemma strTrans_letStr (w : List A) (p : Bool × Bool) : strTrans mu3 (letStr w) p = p := by
  induction w generalizing p with
  | nil => rfl
  | cons a w ih => rw [letStr_cons, show strTrans mu3 (some (some a) :: letStr w) p
      = strTrans mu3 (letStr w) (mu3 p (some (some a))) from rfl,
      show mu3 p (some (some a)) = p from rfl, ih]

lemma biEvalT_letStr (p : Bool × Bool) (w : List A) (t : Bool) :
    biEvalT mu3 nu3 psi3 p (letStr w) t =
      if p.2 then (if t then [] else letStr w) else (if p.1 then [] else letStr w) := by
  induction w with
  | nil => obtain ⟨p1, p2⟩ := p; cases p1 <;> cases p2 <;> cases t <;> simp
  | cons a w ih =>
      rw [letStr_cons, biEvalT_cons, revTrans_letStr,
        show mu3 p (some (some a)) = p from rfl, ih]
      obtain ⟨p1, p2⟩ := p
      cases p1 <;> cases p2 <;> cases t <;> simp [psi3]

lemma strTrans_dblBlock (p1 : Bool) (w : List A) :
    strTrans mu3 (dblBlock w) (p1, false) = (p1, true) := by
  rw [dblBlock, strTrans_append', strTrans_letStr,
    show strTrans mu3 (some none :: (letStr w ++ [some none])) (p1, false)
      = strTrans mu3 (letStr w ++ [some none]) (mu3 (p1, false) (some (none : Option A)))
        from rfl,
    show mu3 (p1, false) (some (none : Option A)) = (p1, true) from rfl,
    strTrans_append', strTrans_letStr]
  rfl

lemma biEvalT_dblBlock (p1 t : Bool) (w : List A) :
    biEvalT mu3 nu3 psi3 (p1, false) (dblBlock w) t =
      biEvalT mu3 nu3 psi3 (p1, false) (letStr w) t ++
        (psi3 (p1, false) (some none) t ++
          (biEvalT mu3 nu3 psi3 (p1, true) (letStr w) t ++
            psi3 (p1, true) (some none) t)) := by
  have hr2 : revTrans nu3 (letStr w ++ [some none]) t = t := by
    rw [revTrans_append, revTrans_letStr]; rfl
  have hr1 : revTrans nu3 (some none :: (letStr w ++ [some none])) t = t := by
    rw [revTrans_cons, hr2]; rfl
  rw [dblBlock, biEvalT_append, hr1, strTrans_letStr, biEvalT_cons, hr2,
    show mu3 (p1, false) (some (none : Option A)) = (p1, true) from rfl,
    biEvalT_append, show revTrans nu3 ([some none] : List (Option (Option A))) t = t from rfl,
    strTrans_letStr, biEvalT_cons]
  simp

lemma biEvalT_dblBlock_first (w : List A) :
    biEvalT mu3 nu3 psi3 (true, false) (dblBlock w) false = letStr w ++ [some none] := by
  rw [biEvalT_dblBlock, biEvalT_letStr, biEvalT_letStr]
  simp [psi3]

lemma biEvalT_dblBlock_mid (w : List A) :
    biEvalT mu3 nu3 psi3 (false, false) (dblBlock w) false =
      letStr w ++ [none] ++ (letStr w ++ [some none]) := by
  rw [biEvalT_dblBlock, biEvalT_letStr, biEvalT_letStr]
  simp [psi3]

lemma biEvalT_dblBlock_last (w : List A) :
    biEvalT mu3 nu3 psi3 (false, false) (dblBlock w) true = letStr w := by
  rw [biEvalT_dblBlock, biEvalT_letStr, biEvalT_letStr]
  simp [psi3]

/-- The output of stage 3 on the blocks after the first one. -/
def tailOut : List (List A) → List (Option (Option A))
  | [] => []
  | [w] => letStr w
  | w :: (v :: ws) => letStr w ++ [none] ++ (letStr w ++ [some none]) ++ tailOut (v :: ws)

lemma revTrans_sep (z : List (Option (Option A))) (t : Bool) :
    revTrans nu3 (none :: z) t = false := rfl

lemma biEvalT_tail (ws : List (List A)) (hws : ws ≠ []) :
    biEvalT mu3 nu3 psi3 (false, false) (blockStr (ws.map dupB)) true = tailOut ws := by
  induction ws with
  | nil => exact absurd rfl hws
  | cons w ws ih =>
      rcases ws with _ | ⟨v, vs⟩
      · rw [List.map_cons, List.map_nil, blockStr_singleton, dupB_map_some,
          biEvalT_dblBlock_last]
        rfl
      · have hne : ((v :: vs).map dupB) ≠ [] := by simp
        rw [List.map_cons, blockStr_cons _ _ hne, dupB_map_some, biEvalT_append,
          revTrans_sep, biEvalT_dblBlock_mid, strTrans_dblBlock, biEvalT_cons,
          show psi3 (false, true) (none : Option (Option A))
            (revTrans nu3 (blockStr ((v :: vs).map dupB)) true) = [] from rfl,
          show mu3 (false, true) (none : Option (Option A)) = (false, false) from rfl,
          ih (by simp)]
        simp [tailOut]

lemma biEvalT_head (w : List A) (ws : List (List A)) (hws : ws ≠ []) :
    biEvalT mu3 nu3 psi3 (true, false) (blockStr ((w :: ws).map dupB)) true
      = letStr w ++ [some none] ++ tailOut ws := by
  have hne : (ws.map dupB) ≠ [] := by
    simpa using hws
  rw [List.map_cons, blockStr_cons _ _ hne, dupB_map_some, biEvalT_append,
    revTrans_sep, biEvalT_dblBlock_first, strTrans_dblBlock, biEvalT_cons,
    show psi3 (true, true) (none : Option (Option A))
      (revTrans nu3 (blockStr (ws.map dupB)) true) = [] from rfl,
    show mu3 (true, true) (none : Option (Option A)) = (false, false) from rfl,
    biEvalT_tail ws hws]
  simp

lemma step3_blockStr (w : List A) (ws : List (List A)) (hws : ws ≠ []) :
    step3 (blockStr ((w :: ws).map dupB)) = letStr w ++ [some none] ++ tailOut ws :=
  biEvalT_head w ws hws

lemma isRationalFun_step3 [Finite A] :
    IsRationalFun (step3 : List (Option (Option A)) → _) :=
  isRationalFun_biEval mu3 (true, false) nu3 true psi3

/-! ## The output of stage 3 is the pairing of the blocks -/

lemma encPair_map_some (v v' : List A) :
    (encPair v v').map (some : Option A → _) = letStr v ++ some none :: letStr v' := by
  simp [encPair, ← map_some_map_some]

lemma blockStr_pairsList (w : List A) (ws : List (List A)) (hws : ws ≠ []) :
    blockStr (pairsList (w :: ws)) = letStr w ++ [some none] ++ tailOut ws := by
  induction ws generalizing w with
  | nil => exact absurd rfl hws
  | cons v vs ih =>
      rcases vs with _ | ⟨z, zs⟩
      · rw [pairsList_cons_cons, pairsList_singleton, blockStr_singleton, encPair_map_some]
        simp [tailOut]
      · rw [pairsList_cons_cons, blockStr_cons _ _ (pairsList_ne_nil v z zs),
          encPair_map_some, ih v (by simp)]
        simp [tailOut]

/-! ## The main theorem -/

/-- The language of the strings over `A + 1` that use the separator. -/
def hasSep (A : Type) : Language (Option A) := {u | (none : Option A) ∈ u}

lemma isRegular_hasSep : (hasSep A).IsRegular := by
  classical
  refine ⟨Bool, inferInstance,
    ⟨fun s (x : Option A) => s || x.isNone, false, {true}⟩, ?_⟩
  have key : ∀ (s : Bool) (u : List (Option A)),
      List.foldl (fun s (x : Option A) => s || x.isNone) s u = true ↔
        (s = true ∨ (none : Option A) ∈ u) := by
    intro s u
    induction u generalizing s with
    | nil => simp
    | cons x u ih =>
        rw [List.foldl_cons, ih]
        cases x <;> simp
  ext u
  simp only [DFA.mem_accepts, DFA.eval, DFA.evalFrom, Set.mem_singleton_iff, hasSep]
  simpa using key false u

/-- The pipeline computing `pairMap f` on the inputs that use the separator. -/
noncomputable def pipeline (f : List (Option A) → List B) (u : List (Option A)) : List B :=
  del (mapLift f (step3 (mapDuplicate (Option A) (step1 u))))

lemma pipeline_eq (f : List (Option A) → List B) {u : List (Option A)}
    (hu : (none : Option A) ∈ u) : pipeline f u = pairMap f u := by
  obtain ⟨w, ws, hbs⟩ : ∃ w ws, splitSep u = w :: ws := by
    rcases h : splitSep u with _ | ⟨w, ws⟩
    · exact absurd h (splitSep_ne_nil u)
    · exact ⟨w, ws, rfl⟩
  have hws : ws ≠ [] := by
    have := (splitSep_tail_ne_nil_iff u).2 hu
    rwa [hbs] at this
  have hne : ((splitSep u).map dollar) ≠ [] := by simp [hbs]
  have hmap : ((splitSep u).map dollar).map (fun b => b ++ b) = (splitSep u).map dupB := by
    simp [List.map_map, Function.comp_def, dupB]
  obtain ⟨v, vs, rfl⟩ : ∃ v vs, ws = v :: vs := by
    rcases ws with _ | ⟨v, vs⟩
    · exact absurd rfl hws
    · exact ⟨v, vs, rfl⟩
  have hpairs : pairBlocks u ≠ [] := by
    rw [pairBlocks, hbs]; exact pairsList_ne_nil w v vs
  rw [pipeline, step1_eq, step2_blockStr _ hne, hmap, hbs, step3_blockStr w _ hws,
    ← blockStr_pairsList w _ hws,
    show pairsList (w :: v :: vs) = pairBlocks u by rw [pairBlocks, hbs],
    mapLift_blockStr _ _ hpairs, del_blockStr, pairMap]

open scoped Classical in
/-- **The neighbouring-block map combinator is a regular operation.**  If `f` is
regular, then so is the function

  `w₀ # w₁ # ⋯ # wₙ  ↦  f (w₀ # w₁) · f (w₁ # w₂) ⋯ f (wₙ₋₁ # wₙ)`

that applies `f` to every pair of consecutive blocks of the input and
concatenates the results (the empty string if the input has no separator at
all).

This is stages 1--3 of the induction step in the book's proof of the snake
lemma; the construction is the book's one, with map duplicate procuring the two
copies of every block and rational functions arranging the brackets. -/
theorem isRegularFun_pairMap [Finite A] [Finite B] {f : List (Option A) → List B}
    (hf : IsRegularFun f) : IsRegularFun (pairMap f) := by
  classical
  have h1 : IsRegularFun (step1 : List (Option A) → _) :=
    IsRegularFun.of_rational isRationalFun_step1
  have h2 : IsRegularFun (mapDuplicate (Option A)) := isRegularFun_mapDuplicate (Option A)
  have h3 : IsRegularFun (step3 : List (Option (Option A)) → _) :=
    IsRegularFun.of_rational isRationalFun_step3
  have h4 : IsRegularFun (mapLift f) := isRegularFun_mapLift hf
  have h5 : IsRegularFun (del : List (Option B) → List B) := isRegularFun_del
  have hpipe : IsRegularFun (pipeline f) :=
    ((((h1.comp h2).comp h3).comp h4).comp h5).congr (fun _ => rfl)
  have hconst : IsRegularFun (fun _ : List (Option A) => ([] : List B)) :=
    IsRegularFun.of_rational (isRationalFun_const [])
  refine (isRegularFun_cond hpipe hconst (isRegular_hasSep (A := A))).congr ?_
  intro u
  by_cases hu : u ∈ hasSep A
  · rw [if_pos hu]
    exact pipeline_eq f hu
  · rw [if_neg hu]
    have hu' : (splitSep u).tail = [] := by
      by_contra h
      exact hu ((splitSep_tail_ne_nil_iff u).1 h)
    rcases h : splitSep u with _ | ⟨w, ws⟩
    · exact absurd h (splitSep_ne_nil u)
    · rw [h] at hu'
      simp only [List.tail_cons] at hu'
      subst hu'
      simp [pairMap, pairBlocks, h]

end RegPair

end Lax916827Proofs.Transducers
