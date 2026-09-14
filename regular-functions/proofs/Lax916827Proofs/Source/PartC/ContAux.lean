/-
Auxiliary facts about continuity (Definition `def:continuity`) that are used in Part C of
*Transducers* (M. Bojańczyk, June 25, 2026).

Continuity is closed under composition, and the basic string operations of
Part C -- letter-to-letter maps, reversal, duplication -- are continuous.  The
main result of this file is that the map lifting of a continuous function is
continuous (Lemma `lem:map-lifting-continuous`), which is proved with the Myhill-Nerode theorem: the
left quotients of the inverse image are determined by the state of the
automaton at the beginning of the current block together with the left
quotients of the (finitely many) languages `{u | the block `u` takes the state
`p` to the state `q`}`.
-/
import Lax132576Proofs.Source.PartB.WeightedStatements
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-! ## Elementary closure properties of continuity -/

lemma continuous_id {A : Type} : Continuous (id : List A → List A) := fun _ hL => by simpa using hL

lemma Continuous.comp {A B C : Type} {f : List A → List B} {g : List B → List C}
    (hg : Continuous g) (hf : Continuous f) : Continuous (g ∘ f) :=
  fun L hL => hf _ (hg L hL)

/-- Continuity only depends on the function, so it transfers along pointwise
equality. -/
lemma Continuous.congr {A B : Type} {f g : List A → List B} (hf : Continuous f)
    (h : ∀ w, f w = g w) : Continuous g := by
  have : f = g := funext h
  exact this ▸ hf

/-! ## Letter-to-letter maps -/

/-- Precomposing a dfa with a letter-to-letter map. -/
def mapDFA {A B σ : Type} (M : DFA B σ) (h : A → B) : DFA A σ where
  step := fun q a => M.step q (h a)
  start := M.start
  accept := M.accept

lemma mapDFA_evalFrom {A B σ : Type} (M : DFA B σ) (h : A → B) (q : σ) (w : List A) :
    (mapDFA M h).evalFrom q w = M.evalFrom q (w.map h) := by
  induction w generalizing q with
  | nil => rfl
  | cons a w ih => rw [DFA.evalFrom_cons, ih]; rfl

/-- A letter-to-letter homomorphism is continuous. -/
lemma continuous_map {A B : Type} (h : A → B) : Continuous (fun w : List A => w.map h) := by
  rintro L ⟨σ, hσ, M, rfl⟩
  refine ⟨σ, hσ, mapDFA M h, ?_⟩
  ext w
  simp only [DFA.mem_accepts, DFA.eval, mapDFA_evalFrom]
  rfl

/-! ## Reversal and duplication (Lemma `lem:reversal-duplication-continuous`) -/

/-- String reversal is continuous. -/
lemma continuous_reverse {A : Type} : Continuous (List.reverse : List A → List A) := by
  intro L hL
  convert hL.reverse using 1

/-- The dfa recognising `{w | w ++ w ∈ M.accepts}`: it remembers the state
reached from the initial state, and the state transformation of the string read
so far. -/
def dupDFA {A σ : Type} (M : DFA A σ) : DFA A (σ × (σ → σ)) where
  step := fun s a => (M.step s.1 a, fun p => M.step (s.2 p) a)
  start := (M.start, id)
  accept := {s | s.2 s.1 ∈ M.accept}

lemma dupDFA_evalFrom {A σ : Type} (M : DFA A σ) (s : σ × (σ → σ)) (w : List A) :
    (dupDFA M).evalFrom s w = (M.evalFrom s.1 w, fun p => M.evalFrom (s.2 p) w) := by
  induction w generalizing s with
  | nil => simp [DFA.evalFrom]
  | cons a w ih => rw [DFA.evalFrom_cons, ih]; rfl

/-- String duplication is continuous. -/
lemma continuous_dup {A : Type} : Continuous (fun w : List A => w ++ w) := by
  classical
  rintro L ⟨σ, hσ, M, rfl⟩
  refine ⟨σ × (σ → σ), inferInstance, dupDFA M, ?_⟩
  ext w
  simp only [DFA.mem_accepts, DFA.eval, dupDFA_evalFrom, DFA.evalFrom_of_append]
  exact Iff.rfl

/-! ## Two lemmas on the map lifting -/

variable {A B : Type}

lemma mapLift_map_some (f : List A → List B) (u : List A) :
    mapLift f (u.map some) = (f u).map some := by
  have h : splitSep (u.map some) = [u] := by
    have h0 := splitSep_map_some_append u ([] : List (Option A)) [] [] rfl
    simpa using h0
  simp [mapLift, h, List.intercalate]

lemma mapLift_map_some_cons_none (f : List A → List B) (u : List A) (v : List (Option A)) :
    mapLift f (u.map some ++ none :: v) = (f u).map some ++ none :: mapLift f v := by
  have hsplit : splitSep (u.map some ++ (none :: v)) = u :: splitSep v := by
    rw [splitSep_map_some_append u (none :: v) [] (splitSep v) rfl]
    simp
  rw [mapLift, hsplit, List.map_cons,
    intercalate_cons_cons _ _ _ (by simpa using (splitSep_ne_nil v).imp (fun h => by simp [h]))]
  simp [mapLift]

/-! ## Continuity of the map lifting (Lemma `lem:map-lifting-continuous`) -/

section MapLift

variable (f : List A → List B) {σ : Type} (D : DFA (Option B) σ)

/-- The dfa reading a string over `B` as a block of a string over `B + 1`, from
the state `p`, and accepting if it arrives at the state `q`. -/
def blockDFA (p q : σ) : DFA B σ where
  step := fun s b => D.step s (some b)
  start := p
  accept := {q}

lemma blockDFA_evalFrom (p q : σ) (s : σ) (v : List B) :
    (blockDFA D p q).evalFrom s v = D.evalFrom s (v.map some) := by
  induction v generalizing s with
  | nil => rfl
  | cons b v ih => rw [DFA.evalFrom_cons, ih]; rfl

/-- The language of the blocks that take the state `p` to the state `q`. -/
def blockLang (p q : σ) : Language A := {u | D.evalFrom p ((f u).map some) = q}

lemma blockLang_isRegular [Fintype σ] (hf : Continuous f) (p q : σ) :
    (blockLang f D p q).IsRegular := by
  have hreg : Language.IsRegular ((blockDFA D p q).accepts) :=
    ⟨σ, inferInstance, blockDFA D p q, rfl⟩
  have hpre := hf _ hreg
  convert hpre using 1
  ext u
  simp only [DFA.mem_accepts, DFA.eval, blockDFA_evalFrom]
  exact Iff.rfl

/-- One step of the automaton that reads `mapLift f w`: the state consists of
the state of `D` at the beginning of the current block together with the part of
the current block that has been read so far. -/
def bstep (s : σ × List A) : Option A → σ × List A
  | some a => (s.1, s.2 ++ [a])
  | none => (D.step (D.evalFrom s.1 ((f s.2).map some)) none, [])

/-- The state of `D` after also reading the output of the current block. -/
def bfinal (s : σ × List A) : σ := D.evalFrom s.1 ((f s.2).map some)

/-- The automaton `bstep` computes the run of `D` on the map lifting. -/
lemma evalFrom_mapLift (v : List (Option A)) (u : List A) (p : σ) :
    D.evalFrom p (mapLift f (u.map some ++ v))
      = bfinal f D (List.foldl (bstep f D) (p, u) v) := by
  induction v generalizing u p with
  | nil => simp [mapLift_map_some, bfinal]
  | cons x v ih =>
      cases x with
      | some a =>
          have hrw : u.map some ++ (some a :: v) = (u ++ [a]).map some ++ v := by simp
          rw [hrw, ih (u ++ [a]) p]
          rfl
      | none =>
          rw [mapLift_map_some_cons_none, DFA.evalFrom_of_append, DFA.evalFrom_cons]
          have := ih [] (D.step (D.evalFrom p ((f u).map some)) none)
          simpa using this

/-- The behaviour of the automaton does not change if the current block is
replaced by a block with the same effect on all continuations. -/
lemma bfinal_foldl_congr {u u' : List A}
    (h : ∀ (x : List A) (p : σ),
      D.evalFrom p ((f (u ++ x)).map some) = D.evalFrom p ((f (u' ++ x)).map some)) :
    ∀ (v : List (Option A)) (p : σ),
      bfinal f D (List.foldl (bstep f D) (p, u) v)
        = bfinal f D (List.foldl (bstep f D) (p, u') v) := by
  intro v
  induction v generalizing u u' with
  | nil =>
      intro p
      have := h [] p
      simpa [bfinal] using this
  | cons x v ih =>
      intro p
      cases x with
      | some a =>
          refine ih (u := u ++ [a]) (u' := u' ++ [a]) (fun x q => ?_) p
          have := h ([a] ++ x) q
          simpa [List.append_assoc] using this
      | none =>
          have hp : D.evalFrom p ((f u).map some) = D.evalFrom p ((f u').map some) := by
            have := h [] p
            simpa using this
          show bfinal f D (List.foldl (bstep f D) (bstep f D (p, u) none) v)
            = bfinal f D (List.foldl (bstep f D) (bstep f D (p, u') none) v)
          simp only [bstep, hp]

/-- The tuple of left quotients of the block languages: a finite amount of
information about the current block. -/
def blockClass (u : List A) : σ × σ → Language A :=
  fun i => (blockLang f D i.1 i.2).leftQuotient u

lemma blockClass_eq_imp {u u' : List A} (h : blockClass f D u = blockClass f D u')
    (x : List A) (p : σ) :
    D.evalFrom p ((f (u ++ x)).map some) = D.evalFrom p ((f (u' ++ x)).map some) := by
  have hmem : x ∈ (blockLang f D p (D.evalFrom p ((f (u ++ x)).map some))).leftQuotient u := rfl
  have hcoord := congrFun h (p, D.evalFrom p ((f (u ++ x)).map some))
  rw [blockClass, blockClass] at hcoord
  simp only at hcoord
  rw [hcoord] at hmem
  exact hmem.symm

lemma bfinal_foldl_congr' (s s' : σ × List A) (h1 : s.1 = s'.1)
    (h2 : blockClass f D s.2 = blockClass f D s'.2) (v : List (Option A)) :
    bfinal f D (List.foldl (bstep f D) s v) = bfinal f D (List.foldl (bstep f D) s' v) := by
  obtain ⟨p, u⟩ := s
  obtain ⟨p', u'⟩ := s'
  simp only at h1 h2
  subst h1
  exact bfinal_foldl_congr f D (blockClass_eq_imp f D h2) v p

lemma finite_range_blockClass [Fintype σ] (hf : Continuous f) :
    (Set.range (blockClass f D)).Finite := by
  classical
  have hcoord : ∀ i : σ × σ, (Set.range (blockLang f D i.1 i.2).leftQuotient).Finite :=
    fun i => (blockLang_isRegular f D hf i.1 i.2).finite_range_leftQuotient
  refine Set.Finite.subset (Set.Finite.pi hcoord) ?_
  rintro s ⟨u, rfl⟩ i -
  exact ⟨u, rfl⟩

end MapLift

/-- If a function factors through a map with finite range, then it has finite
range itself. -/
lemma finite_range_of_factors {α β γ : Type} (F : α → β) (ψ : α → γ)
    (hψ : (Set.range ψ).Finite) (h : ∀ a a', ψ a = ψ a' → F a = F a') :
    (Set.range F).Finite := by
  classical
  have hfin : Finite (Set.range ψ) := hψ.to_subtype
  refine Set.Finite.subset (Set.finite_range (fun s : Set.range ψ => F s.2.choose)) ?_
  rintro b ⟨a, rfl⟩
  refine ⟨⟨ψ a, ⟨a, rfl⟩⟩, ?_⟩
  exact h _ a (Exists.choose_spec (⟨a, rfl⟩ : ∃ x, ψ x = ψ a))

/-- **Lemma `lem:map-lifting-continuous`.**  The map lifting of a continuous function is continuous. -/
theorem continuous_mapLift {f : List A → List B} (hf : Continuous f) :
    Continuous (mapLift f) := by
  classical
  rintro L ⟨σ, hσ, D, rfl⟩
  rw [Language.isRegular_iff_finite_range_leftQuotient]
  set P : Language (Option A) := {w | mapLift f w ∈ D.accepts} with hP
  have hquot : ∀ w : List (Option A), P.leftQuotient w =
      {v | bfinal f D (List.foldl (bstep f D)
        (List.foldl (bstep f D) (D.start, []) w) v) ∈ D.accept} := by
    intro w
    ext v
    have hev := evalFrom_mapLift f D (w ++ v) [] D.start
    simp only [List.map_nil, List.nil_append, List.foldl_append] at hev
    show mapLift f (w ++ v) ∈ D.accepts ↔ _
    rw [DFA.mem_accepts, DFA.eval, hev]
    exact Iff.rfl
  refine finite_range_of_factors P.leftQuotient
    (fun w => ((List.foldl (bstep f D) (D.start, []) w).1,
      blockClass f D (List.foldl (bstep f D) (D.start, []) w).2)) ?_ ?_
  · refine Set.Finite.subset ((Set.finite_univ (α := σ)).prod (finite_range_blockClass f D hf)) ?_
    rintro s ⟨w, rfl⟩
    exact ⟨Set.mem_univ _, ⟨_, rfl⟩⟩
  · intro w w' hww'
    simp only [Prod.mk.injEq] at hww'
    obtain ⟨h1, h2⟩ := hww'
    have hcong := fun v => bfinal_foldl_congr' f D _ _ h1 h2 v
    rw [hquot w, hquot w']
    ext v
    exact Iff.of_eq (congrArg (fun q => q ∈ D.accept) (hcong v))

end Lax916827Proofs.Transducers
