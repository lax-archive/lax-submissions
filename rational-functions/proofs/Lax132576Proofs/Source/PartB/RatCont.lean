/-
Continuity of rational relations (Theorem `thm:continuity-rational-relations`).

Given an nfa with output all of whose transitions read at most one letter, and
a deterministic automaton `D` for a regular language `L` over the output
alphabet, the inverse image of `L` is recognised by the epsilon-automaton whose
states are pairs (state of the nfa, state of `D`) and which runs `D` on the
output produced by each transition.
-/
import Lax132576Proofs.Source.PartB.Atomize
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace RatCont

variable {A B Q σ : Type} (M : NFAO A B Q) (D : DFA B σ)

/-- The epsilon-automaton recognising the inverse image of `D.accepts`. -/
def preNFA : εNFA A (Q × σ) where
  step := fun s a => {s' | ∃ x : List B, (s.1, a.toList, x, s'.1) ∈ M.δ ∧ s'.2 = D.evalFrom s.2 x}
  start := {s | s.1 ∈ M.init ∧ s.2 = D.start}
  accept := {s | s.1 ∈ M.final ∧ s.2 ∈ D.accept}

/-- Every run of the nfa gives a run of the epsilon-automaton.  This uses that
every transition reads at most one letter. -/
lemma isPath_of_relFrom (hM : ∀ t ∈ M.δ, t.2.1.length ≤ 1) {q q' : Q} {w : List A} {v : List B}
    (h : M.relFrom q w v q') (p : σ) :
    ∃ x : List (Option A), x.reduceOption = w ∧
      (preNFA M D).IsPath (q, p) (q', D.evalFrom p v) x := by
  -- We prove by induction on the path in M.relFrom
  -- Using relFrom_induction with target q'
  -- The motive tracks: for source q, input w, output v, and DFA state p,
  -- there exists a path in preNFA
  -- Prove for fixed q and q' first, then generalize
  have key : ∀ (q q' : Q) (w : List A) (v : List B) (p : σ),
      M.relFrom q w v q' →
      ∃ (xs : List (Option A)), xs.reduceOption = w ∧
        (preNFA M D).IsPath (q, p) (q', D.evalFrom p v) xs := by
    intro q q' w v p
    let motive := fun (src : Q) (wIn : List A) (vOutIn : List B) =>
        ∀ (pf : σ), ∃ (xs : List (Option A)), xs.reduceOption = wIn ∧
          (preNFA M D).IsPath (src, pf) (q', D.evalFrom pf vOutIn) xs
    show M.relFrom q w v q' →
        ∃ (xs : List (Option A)), xs.reduceOption = w ∧
          (preNFA M D).IsPath (q, p) (q', D.evalFrom p v) xs
    refine fun hrel => (NFAO.relFrom_induction (motive := motive) ?hnil ?hcons) hrel p
    · -- hnil: src = q', w = [], v = []
      intro pf
      use []
      simp
    · -- hcons
      intro q q'' u x w v ht htail ih
      have h_len := hM (q, u, x, q'') ht
      -- Since u.length ≤ 1, either u = [] or u = [a]
      rcases u with _ | ⟨a, us⟩
      · -- Case u = []: ε-transition to (q'', D.evalFrom pf x) for any pf
        intro pf
        have hε : (q'', D.evalFrom pf x) ∈ (preNFA M D).step (q, pf) none := by
          simp [preNFA]
          exact ⟨x, ht, rfl⟩
        -- ih gives us a path from q'' for DFA state D.evalFrom pf x
        obtain ⟨xs, hxsw, hpath⟩ := ih (D.evalFrom pf x)
        -- We use path none :: xs
        refine ⟨none :: xs, ?_, ?_⟩
        · simp [hxsw]
        · have heq : D.evalFrom pf (x ++ v) = D.evalFrom (D.evalFrom pf x) v := by
            simp [DFA.evalFrom, List.foldl_append]
          rw [heq]
          apply εNFA.IsPath.cons (q'', D.evalFrom pf x)
          · exact hε
          · exact hpath
      · -- Case u = [a]: consume input a
        -- Since u.length ≤ 1 and u = a :: us, us must be []
        have hus : us = [] := by simp_all
        subst hus
        intro pf
        have hstep : (q'', D.evalFrom pf x) ∈ (preNFA M D).step (q, pf) (some a) := by
          simp [preNFA]
          exact ⟨x, ht, rfl⟩
        -- ih gives us a path from q'' for DFA state D.evalFrom pf x
        obtain ⟨xs, hxsw, hpath⟩ := ih (D.evalFrom pf x)
        refine ⟨some a :: xs, ?_, ?_⟩
        · simp [hxsw]
        · have heq : D.evalFrom pf (x ++ v) = D.evalFrom (D.evalFrom pf x) v := by
            simp [DFA.evalFrom, List.foldl_append]
          rw [heq]
          apply εNFA.IsPath.cons (q'', D.evalFrom pf x)
          · exact hstep
          · exact hpath
  exact key q q' w v p h

/-- Every run of the epsilon-automaton gives a run of the nfa. -/
lemma relFrom_of_isPath : ∀ (x : List (Option A)) (q q' : Q) (p p' : σ),
    (preNFA M D).IsPath (q, p) (q', p') x →
      ∃ v : List B, M.relFrom q x.reduceOption v q' ∧ p' = D.evalFrom p v := by
  intro x
  induction x with
  | nil =>
    intro q q' p p' hp
    -- From IsPath (q, p) (q', p') [], we have (q, p) = (q', p')
    cases hp
    use []
    exact ⟨NFAO.relFrom_nil M q, rfl⟩
  | cons a as ih =>
    intro q q' p p' hp
    cases hp with
    | @cons t _ _ _ _ htrans hpath =>
      -- htrans : t ∈ (preNFA M D).step (q, p) a
      -- hpath : (preNFA M D).IsPath t (q', p') as
      -- Extract info from htrans
      have htrans' := htrans
      simp only [preNFA] at htrans'
      obtain ⟨x', hδ, ht2⟩ := htrans'
      -- Apply induction hypothesis
      obtain ⟨v', hrel, hp'⟩ := ih t.1 q' t.2 p' hpath
      -- Combine the transitions
      have hrel2 := NFAO.relFrom_step hδ hrel
      -- (a :: as).reduceOption = a.toList ++ as.reduceOption
      have hred : (a :: as).reduceOption = a.toList ++ as.reduceOption := by
        cases a with
        | none => rfl
        | some a' => rfl
      rw [hred]
      use x' ++ v'
      constructor
      · exact hrel2
      · rw [hp', ht2]
        have : ∀ p x v, D.evalFrom (D.evalFrom p x) v = D.evalFrom p (x ++ v) := by
          intro p x v
          induction x generalizing p with
          | nil => simp
          | cons b xs ihx => 
            simp [DFA.evalFrom_cons, ihx]
        exact this p x' v'

lemma preNFA_accepts (hM : ∀ t ∈ M.δ, t.2.1.length ≤ 1) :
    (preNFA M D).accepts = {w : List A | ∃ v, M.rel w v ∧ v ∈ D.accepts} := by
  ext w
  rw [εNFA.mem_accepts_iff_exists_path]
  constructor
  · rintro ⟨⟨q, p⟩, ⟨q', p'⟩, x, ⟨hq, rfl⟩, ⟨hq', hp'⟩, rfl, hpath⟩
    obtain ⟨v, hrel, hev⟩ := relFrom_of_isPath M D x q q' D.start p' hpath
    refine ⟨v, (M.rel_iff_relFrom _ v).2 ⟨q, hq, q', hq', hrel⟩, ?_⟩
    simpa [DFA.mem_accepts, DFA.eval, ← hev] using hp'
  · rintro ⟨v, hrel, hv⟩
    rw [NFAO.rel_iff_relFrom] at hrel
    obtain ⟨q, hq, q', hq', hrel⟩ := hrel
    obtain ⟨x, hx, hpath⟩ := isPath_of_relFrom M D hM hrel D.start
    exact ⟨(q, D.start), (q', D.evalFrom D.start v), x, ⟨hq, rfl⟩,
      ⟨hq', by simpa [DFA.mem_accepts, DFA.eval] using hv⟩, hx, hpath⟩

end RatCont

/-- The language accepted by an epsilon-automaton with finitely many states is
regular. -/
lemma isRegular_of_εNFA {A σ : Type} [Finite σ] (E : εNFA A σ) : E.accepts.IsRegular := by
  letI : Fintype σ := Fintype.ofFinite σ
  exact ⟨Set σ, inferInstance, E.toNFA.toDFA, by rw [NFA.toDFA_correct, εNFA.toNFA_correct]⟩

/-- **Theorem `thm:continuity-rational-relations`.**  The inverse image of a regular language under
a rational relation is regular. -/
theorem rationalRel_continuous_aux {A B : Type} {R : List A → List B → Prop}
    (hR : IsRationalRel R) : RelContinuous R := by
  intro L hL
  obtain ⟨σ, hσ, D, rfl⟩ := hL
  obtain ⟨Q, hQ, M, hatom, hrel⟩ := exists_atomic_nfao hR
  have hset : {w : List A | ∃ v, R w v ∧ v ∈ D.accepts} = (RatCont.preNFA M D).accepts := by
    rw [RatCont.preNFA_accepts M D (fun t ht => (hatom t ht).1)]
    ext w
    exact exists_congr fun v => and_congr_left' (hrel w v)
  rw [hset]
  exact isRegular_of_εNFA _

end Lax132576Proofs.Transducers
