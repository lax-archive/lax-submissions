/-
**The regular conditions on a string over the alphabet of snake letters, II: no directed cycle.**

A left-to-right automaton can check that the graph described by a string `w` over
`Transducers.SnakeLetter` has no directed cycle.  Its state after reading a prefix `u` is the
*reachability relation of the last column*

  `SnakeGraph.Reach u p q` : there is a nonempty directed path from `(p, |u|)` to `(q, |u|)` inside
  the graph of `u`,

together with one bit saying whether a cycle has already been seen.  The relation of the last column
is a finite amount of information -- a relation on `Q` -- and it is updated by a single letter: a
path from the new column to itself alternates between crossing the new letter and wandering in the
old graph, so the new relation is the transitive closure of `SnakeGraph.Cross`
(`SnakeGraph.reach_concat`).  A cycle survives in the prefixes: either it does not touch the last
column, and then it is already a cycle of the shorter prefix, or it does, and then it shows up on
the diagonal of the reachability relation (`SnakeGraph.hasCycle_concat`).
-/
import Lax916827Proofs.Source.PartC.SnakeAlphChar
import Lax916827Proofs.Source.PartC.RegAut
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace SnakeGraph

variable {Q B : Type}

/-! ## The reachability relation of the last column -/

/-- There is a nonempty directed path from `(p, |w|)` to `(q, |w|)` in the graph described by `w`.
Both vertices are in the *last* column of that graph. -/
def Reach (w : List (SnakeLetter Q B)) (p q : Q) : Prop :=
  Relation.TransGen (EdgeRel w) (p, w.length) (q, w.length)

/-- The graph described by `w` has a directed cycle. -/
def HasCycle (w : List (SnakeLetter Q B)) : Prop := ∃ v, Relation.TransGen (EdgeRel w) v v

lemma acyclic_iff_not_hasCycle (w : List (SnakeLetter Q B)) : Acyclic w ↔ ¬ HasCycle w := by
  constructor
  · rintro h ⟨v, hv⟩; exact h v hv
  · intro h v hv; exact h ⟨v, hv⟩

/-- One excursion of a path that starts and ends in the last column: it crosses the last letter to
the left, wanders in the graph of the shorter prefix, and crosses back to the right. -/
def Cross (c : SnakeLetter Q B) (R : Q → Q → Prop) (p q : Q) : Prop :=
  ∃ p' q' o o', c (true, p) = some (p', o) ∧ (p' = q' ∨ R p' q') ∧ c (false, q') = some (q, o')

/-- An edge of the graph of a prefix is an edge of the graph of the whole string. -/
lemma edge_append {w : List (SnakeLetter Q B)} {c : SnakeLetter Q B} {v v' : Vtx Q} {o : Option B}
    (h : Edge w v v' o) : Edge (w ++ [c]) v v' o := by
  rcases h with ⟨hc, c', hc', hcq⟩ | ⟨hc, c', hc', hcq⟩
  · refine Or.inl ⟨hc, c', ?_, hcq⟩
    rw [List.getElem?_append_left (by
      obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.1 hc'; exact h)]
    exact hc'
  · refine Or.inr ⟨hc, c', ?_, hcq⟩
    rw [List.getElem?_append_left (by
      obtain ⟨h, -⟩ := List.getElem?_eq_some_iff.1 hc'; exact h)]
    exact hc'

lemma edgeRel_append {w : List (SnakeLetter Q B)} {c : SnakeLetter Q B} {v v' : Vtx Q}
    (h : EdgeRel w v v') : EdgeRel (w ++ [c]) v v' := by
  obtain ⟨o, ho⟩ := h; exact ⟨o, edge_append ho⟩

/-- The graph of the empty string has no edge. -/
lemma not_edge_nil {v v' : Vtx Q} {o : Option B} : ¬ Edge ([] : List (SnakeLetter Q B)) v v' o := by
  rintro (⟨-, c, hc, -⟩ | ⟨-, c, hc, -⟩) <;> simp at hc

lemma not_transGen_nil {v v' : Vtx Q} :
    ¬ Relation.TransGen (EdgeRel ([] : List (SnakeLetter Q B))) v v' := by
  intro h
  induction h with
  | single h => obtain ⟨o, ho⟩ := h; exact not_edge_nil ho
  | tail _ h _ => obtain ⟨o, ho⟩ := h; exact not_edge_nil ho

lemma not_reach_nil {p q : Q} : ¬ Reach ([] : List (SnakeLetter Q B)) p q := not_transGen_nil

lemma not_hasCycle_nil : ¬ HasCycle ([] : List (SnakeLetter Q B)) := by
  rintro ⟨v, hv⟩
  exact not_transGen_nil hv

/-! ## Reading the last letter -/

lemma getElem?_append_self (w : List (SnakeLetter Q B)) (c : SnakeLetter Q B) :
    (w ++ [c])[w.length]? = some c := by
  rw [List.getElem?_append_right (le_refl _), Nat.sub_self]
  rfl

/-- An edge of the graph of `w ++ [c]` between two columns of the graph of `w` is an edge of the
graph of `w`. -/
lemma edge_of_append_le {w : List (SnakeLetter Q B)} {c : SnakeLetter Q B} {v v' : Vtx Q}
    {o : Option B} (h : Edge (w ++ [c]) v v' o) (hv : v.2 ≤ w.length) (hv' : v'.2 ≤ w.length) :
    Edge w v v' o := by
  rcases h with ⟨hc, c', hc', hcq⟩ | ⟨hc, c', hc', hcq⟩
  · refine Or.inl ⟨hc, c', ?_, hcq⟩
    rwa [List.getElem?_append_left (by omega)] at hc'
  · refine Or.inr ⟨hc, c', ?_, hcq⟩
    rwa [List.getElem?_append_left (by omega)] at hc'

/-- The edge of the last letter that leaves the last column. -/
lemma edge_last_left {w : List (SnakeLetter Q B)} {c : SnakeLetter Q B} {p p' : Q} {o : Option B}
    (h : c (true, p) = some (p', o)) :
    Edge (w ++ [c]) (p, w.length + 1) (p', w.length) o :=
  Or.inr ⟨rfl, c, getElem?_append_self w c, h⟩

/-- The edge of the last letter that enters the last column. -/
lemma edge_last_right {w : List (SnakeLetter Q B)} {c : SnakeLetter Q B} {q' q : Q} {o : Option B}
    (h : c (false, q') = some (q, o)) :
    Edge (w ++ [c]) (q', w.length) (q, w.length + 1) o :=
  Or.inl ⟨rfl, c, getElem?_append_self w c, h⟩

/-- Every edge leaving the last column is an edge of the last letter. -/
lemma edge_from_last {w : List (SnakeLetter Q B)} {c : SnakeLetter Q B} {p : Q} {v' : Vtx Q}
    {o : Option B} (h : Edge (w ++ [c]) (p, w.length + 1) v' o) :
    v'.2 = w.length ∧ c (true, p) = some (v'.1, o) := by
  rcases h with ⟨hc, c', hc', hcq⟩ | ⟨hc, c', hc', hcq⟩
  · exfalso
    rw [List.getElem?_eq_none (by simp)] at hc'
    exact absurd hc' (by simp)
  · have hc0 : w.length + 1 = v'.2 + 1 := hc
    have hv : v'.2 = w.length := by omega
    rw [hv, getElem?_append_self, Option.some_inj] at hc'
    subst hc'
    exact ⟨hv, hcq⟩

/-- Every edge entering the last column is an edge of the last letter. -/
lemma edge_to_last {w : List (SnakeLetter Q B)} {c : SnakeLetter Q B} {u : Vtx Q} {q : Q}
    {o : Option B} (h : Edge (w ++ [c]) u (q, w.length + 1) o) :
    u.2 = w.length ∧ c (false, u.1) = some (q, o) := by
  rcases h with ⟨hc, c', hc', hcq⟩ | ⟨hc, c', hc', hcq⟩
  · have hc0 : w.length + 1 = u.2 + 1 := hc
    have hv : u.2 = w.length := by omega
    rw [hv, getElem?_append_self, Option.some_inj] at hc'
    subst hc'
    exact ⟨hv, hcq⟩
  · exfalso
    rw [List.getElem?_eq_none (by simp)] at hc'
    exact absurd hc' (by simp)

/-- The last vertex of a nonempty path is a vertex of the graph. -/
lemma transGen_col_le {w : List (SnakeLetter Q B)} {v v' : Vtx Q}
    (h : Relation.TransGen (EdgeRel w) v v') : v'.2 ≤ w.length := by
  cases h with
  | single h => obtain ⟨o, ho⟩ := h; exact edge_col_le_right ho
  | tail _ h => obtain ⟨o, ho⟩ := h; exact edge_col_le_right ho

/-- One excursion out of the last column and back is a path of the graph. -/
lemma transGen_of_cross {w : List (SnakeLetter Q B)} {c : SnakeLetter Q B} {p q : Q}
    (h : Cross c (Reach w) p q) :
    Relation.TransGen (EdgeRel (w ++ [c])) (p, w.length + 1) (q, w.length + 1) := by
  obtain ⟨p', q', o, o', h1, h2, h3⟩ := h
  have e1 : EdgeRel (w ++ [c]) (p, w.length + 1) (p', w.length) := ⟨o, edge_last_left h1⟩
  have e2 : EdgeRel (w ++ [c]) (q', w.length) (q, w.length + 1) := ⟨o', edge_last_right h3⟩
  have mid : Relation.ReflTransGen (EdgeRel (w ++ [c])) (p', w.length) (q', w.length) := by
    rcases h2 with rfl | hR
    · exact Relation.ReflTransGen.refl
    · exact (Relation.TransGen.mono (fun _ _ hab => edgeRel_append hab) hR).to_reflTransGen
  exact Relation.TransGen.head e1 (Relation.TransGen.trans_right mid (Relation.TransGen.single e2))

/-! ## The two update lemmas -/

/-- **The reachability relation of the last column, after one more letter.** -/
theorem reach_concat (w : List (SnakeLetter Q B)) (c : SnakeLetter Q B) (p q : Q) :
    Reach (w ++ [c]) p q ↔ Relation.TransGen (Cross c (Reach w)) p q := by
  have hlen : (w ++ [c]).length = w.length + 1 := by simp
  constructor
  · intro h
    have h' : Relation.TransGen (EdgeRel (w ++ [c])) (p, w.length + 1) (q, w.length + 1) := by
      rw [← hlen]; exact h
    -- a path that starts in the last column is, at every moment, either back in the last column
    -- after finitely many excursions, or in the middle of one
    have key : ∀ x : Vtx Q, Relation.TransGen (EdgeRel (w ++ [c])) (p, w.length + 1) x →
        (x.2 = w.length + 1 → Relation.TransGen (Cross c (Reach w)) p x.1) ∧
        (x.2 ≤ w.length → ∃ z y o, (z = p ∨ Relation.TransGen (Cross c (Reach w)) p z) ∧
          c (true, z) = some (y, o) ∧
          Relation.ReflTransGen (EdgeRel w) (y, w.length) x) := by
      intro x hx
      induction hx with
      | @single x he =>
          obtain ⟨xq, xn⟩ := x
          obtain ⟨o, ho⟩ := he
          obtain ⟨hx2, hcq⟩ := edge_from_last ho
          have hx2' : xn = w.length := hx2
          subst hx2'
          exact ⟨fun h => absurd (show w.length = w.length + 1 from h) (by omega),
            fun _ => ⟨p, xq, o, Or.inl rfl, hcq, Relation.ReflTransGen.refl⟩⟩
      | @tail x1 x2 _ he ih =>
          obtain ⟨aq, an⟩ := x1
          obtain ⟨bq, bn⟩ := x2
          obtain ⟨o, ho⟩ := he
          have hble : bn ≤ w.length + 1 := by
            have h0 : bn ≤ (w ++ [c]).length := edge_col_le_right ho
            simpa using h0
          have hale : an ≤ w.length + 1 := by
            have h0 : an ≤ (w ++ [c]).length := edge_col_le_left ho
            simpa using h0
          rcases Nat.lt_or_ge an (w.length + 1) with han | han
          · have han' : an ≤ w.length := by omega
            obtain ⟨z, y, o1, hz, hcz, hrefl⟩ := ih.2 han'
            rcases Nat.lt_or_ge bn (w.length + 1) with hbn | hbn
            · have hbn' : bn ≤ w.length := by omega
              exact ⟨fun h => absurd (show bn = w.length + 1 from h) (by omega),
                fun _ => ⟨z, y, o1, hz, hcz, hrefl.tail ⟨o, edge_of_append_le ho han' hbn'⟩⟩⟩
            · have hbn' : bn = w.length + 1 := by omega
              subst hbn'
              obtain ⟨hac, hcc⟩ := edge_to_last ho
              have hac' : an = w.length := hac
              subst hac'
              have hyx : y = aq ∨ Reach w y aq := by
                rcases Relation.reflTransGen_iff_eq_or_transGen.1 hrefl with heq | htr
                · exact Or.inl (congrArg Prod.fst heq).symm
                · exact Or.inr htr
              have hcross : Cross c (Reach w) z bq := ⟨y, aq, o1, o, hcz, hyx, hcc⟩
              refine ⟨fun _ => ?_,
                fun h => absurd (show w.length + 1 ≤ w.length from h) (by omega)⟩
              rcases hz with rfl | htz
              · exact Relation.TransGen.single hcross
              · exact htz.tail hcross
          · have han' : an = w.length + 1 := by omega
            subst han'
            obtain ⟨hbc, hcc⟩ := edge_from_last ho
            have hbc' : bn = w.length := hbc
            subst hbc'
            exact ⟨fun h => absurd (show w.length = w.length + 1 from h) (by omega),
              fun _ => ⟨aq, bq, o, Or.inr (ih.1 rfl), hcc, Relation.ReflTransGen.refl⟩⟩
    exact (key (q, w.length + 1) h').1 rfl
  · intro h
    show Relation.TransGen (EdgeRel (w ++ [c])) (p, (w ++ [c]).length) (q, (w ++ [c]).length)
    rw [hlen]
    induction h with
    | @single q hc => exact transGen_of_cross hc
    | @tail q1 q2 _ hc ih => exact ih.trans (transGen_of_cross hc)

/-- A path of the graph of `w ++ [c]` either visits the last column or stays inside the graph of
`w`. -/
lemma path_split (w : List (SnakeLetter Q B)) (c : SnakeLetter Q B) {v v' : Vtx Q}
    (h : Relation.TransGen (EdgeRel (w ++ [c])) v v') :
    (∃ u : Vtx Q, u.2 = w.length + 1 ∧
        Relation.ReflTransGen (EdgeRel (w ++ [c])) v u ∧
        Relation.ReflTransGen (EdgeRel (w ++ [c])) u v') ∨
      Relation.TransGen (EdgeRel w) v v' := by
  induction h with
  | @single x he =>
      obtain ⟨o, ho⟩ := he
      have hvle : v.2 ≤ w.length + 1 := by
        have h0 : v.2 ≤ (w ++ [c]).length := edge_col_le_left ho
        simpa using h0
      have hxle : x.2 ≤ w.length + 1 := by
        have h0 : x.2 ≤ (w ++ [c]).length := edge_col_le_right ho
        simpa using h0
      rcases Nat.lt_or_ge w.length v.2 with hv | hv
      · exact Or.inl ⟨v, by omega, Relation.ReflTransGen.refl,
          Relation.ReflTransGen.single ⟨o, ho⟩⟩
      · rcases Nat.lt_or_ge w.length x.2 with hx | hx
        · exact Or.inl ⟨x, by omega, Relation.ReflTransGen.single ⟨o, ho⟩,
            Relation.ReflTransGen.refl⟩
        · exact Or.inr (Relation.TransGen.single ⟨o, edge_of_append_le ho hv hx⟩)
  | @tail x1 x2 _ he ih =>
      obtain ⟨o, ho⟩ := he
      rcases ih with ⟨u, hu, h1, h2⟩ | hw
      · exact Or.inl ⟨u, hu, h1, h2.tail ⟨o, ho⟩⟩
      · have hx1 : x1.2 ≤ w.length := transGen_col_le hw
        have hx2le : x2.2 ≤ w.length + 1 := by
          have h0 : x2.2 ≤ (w ++ [c]).length := edge_col_le_right ho
          simpa using h0
        rcases Nat.lt_or_ge w.length x2.2 with hx2 | hx2
        · refine Or.inl ⟨x2, by omega, ?_, Relation.ReflTransGen.refl⟩
          exact ((Relation.TransGen.mono (fun _ _ hab => edgeRel_append hab)
            hw).to_reflTransGen).tail ⟨o, ho⟩
        · exact Or.inr (hw.tail ⟨o, edge_of_append_le ho hx1 hx2⟩)

/-- **A cycle in the graph of `w ++ [c]`** either avoids the last column, and is then a cycle of the
graph of `w`, or it visits the last column, and is then visible on the diagonal of the reachability
relation of that column. -/
theorem hasCycle_concat (w : List (SnakeLetter Q B)) (c : SnakeLetter Q B) :
    HasCycle (w ++ [c]) ↔ HasCycle w ∨ ∃ q, Reach (w ++ [c]) q q := by
  have hlen : (w ++ [c]).length = w.length + 1 := by simp
  constructor
  · rintro ⟨v, hv⟩
    rcases path_split w c hv with ⟨u, hu, h1, h2⟩ | hw
    · obtain ⟨uq, un⟩ := u
      have hu' : un = w.length + 1 := hu
      subst hu'
      refine Or.inr ⟨uq, ?_⟩
      have hcyc : Relation.TransGen (EdgeRel (w ++ [c])) (uq, w.length + 1)
          (uq, w.length + 1) :=
        Relation.TransGen.trans_right h2 (Relation.TransGen.trans_left hv h1)
      show Relation.TransGen (EdgeRel (w ++ [c])) (uq, (w ++ [c]).length)
        (uq, (w ++ [c]).length)
      rw [hlen]
      exact hcyc
    · exact Or.inl ⟨v, hw⟩
  · rintro (⟨v, hv⟩ | ⟨q, hq⟩)
    · exact ⟨v, Relation.TransGen.mono (fun _ _ hab => edgeRel_append hab) hv⟩
    · exact ⟨(q, (w ++ [c]).length), hq⟩

/-! ## The automaton -/

/-- The state of the automaton: the reachability relation of the last column, and whether a cycle
has already been seen. -/
abbrev CycSt (Q : Type) := (Q → Q → Prop) × Prop

/-- One step of the automaton. -/
def cycStep : CycSt Q → SnakeLetter Q B → CycSt Q := fun s c =>
  (Relation.TransGen (Cross c s.1), s.2 ∨ ∃ q, Relation.TransGen (Cross c s.1) q q)

/-- The state of the automaton after reading `w` is the reachability relation of the last column of
`w` together with the presence of a cycle in the graph of `w`. -/
theorem foldl_cycStep (w : List (SnakeLetter Q B)) :
    w.foldl cycStep ((fun _ _ => False), False) = (Reach w, HasCycle w) := by
  induction w using List.reverseRecOn with
  | nil =>
      simp only [List.foldl_nil]
      refine Prod.ext ?_ ?_
      · funext p q
        exact propext ⟨False.elim, fun h => absurd h not_reach_nil⟩
      · exact propext ⟨False.elim, fun h => absurd h not_hasCycle_nil⟩
  | append_singleton v c ih =>
      rw [List.foldl_append, ih]
      simp only [List.foldl_cons, List.foldl_nil, cycStep]
      refine Prod.ext ?_ ?_
      · funext p q
        exact propext (reach_concat v c p q).symm
      · refine propext (Iff.trans ?_ (hasCycle_concat v c).symm)
        constructor
        · rintro (h | ⟨q, hq⟩)
          · exact Or.inl h
          · exact Or.inr ⟨q, (reach_concat v c q q).2 hq⟩
        · rintro (h | ⟨q, hq⟩)
          · exact Or.inl h
          · exact Or.inr ⟨q, (reach_concat v c q q).1 hq⟩

/-- **Having no directed cycle is a regular condition.** -/
theorem isRegular_acyclic [Finite Q] [Finite B] :
    Language.IsRegular {w : List (SnakeLetter Q B) | Acyclic w} := by
  classical
  have h := RegAut.isRegular_foldl (Γ := SnakeLetter Q B) (S := CycSt Q) cycStep
    ((fun _ _ => False), False) {s : CycSt Q | ¬ s.2}
  refine RegAut.isRegular_of_eq h (fun w => ?_)
  simp only [Set.mem_setOf_eq, foldl_cycStep]
  exact acyclic_iff_not_hasCycle w

end SnakeGraph

end Lax916827Proofs.Transducers
