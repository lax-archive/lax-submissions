/-
**When does a string over the alphabet of snake letters represent a snake graph?**

The graph `SnakeGraph.Edge w` described by a string `w` over the alphabet `Transducers.SnakeLetter`
is a snake graph -- all its edges lie on a single directed path -- exactly when

* every vertex has at most one outgoing edge (`SnakeGraph.OutDegLe1`) and at most one incoming edge
  (`SnakeGraph.InDegLe1`);
* the graph has no directed cycle (`SnakeGraph.Acyclic`);
* it has at most one source, i.e. at most one vertex with an outgoing but no incoming edge
  (`SnakeGraph.SrcUnique`).

This is `SnakeGraph.representsSnake_iff`.  The left-to-right implication is immediate from the
lemmas of `RequestProject/PartC/SnakeAlph.lean`.  For the converse: a graph whose vertices have at
most one outgoing and at most one incoming edge is a disjoint union of paths and cycles, so if it
has no cycle and at most one source, then it has at most one component with an edge.  The path is
built by walking forward from the source along the (unique) outgoing edges; the walk terminates
because the vertices that carry an edge are finitely many and an acyclic walk does not repeat a
vertex, and it covers all the edges because walking *backwards* from any vertex with an edge -- along
the unique incoming edges -- reaches a source, which must be *the* source.

The three conditions are the ones checked by the automata of
`RequestProject/PartC/SnakeAlphLoc.lean` and `RequestProject/PartC/SnakeAlphCyc.lean`.
-/
import Lax916827Proofs.Source.PartC.SnakeAlph
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace SnakeGraph

variable {Q B : Type}

/-! ## The four conditions -/

/-- Every vertex has at most one outgoing edge. -/
def OutDegLe1 (w : List (SnakeLetter Q B)) : Prop :=
  ∀ v v₁ v₂ o₁ o₂, Edge w v v₁ o₁ → Edge w v v₂ o₂ → v₁ = v₂ ∧ o₁ = o₂

/-- Every vertex has at most one incoming edge. -/
def InDegLe1 (w : List (SnakeLetter Q B)) : Prop :=
  ∀ u₁ u₂ v o₁ o₂, Edge w u₁ v o₁ → Edge w u₂ v o₂ → u₁ = u₂ ∧ o₁ = o₂

/-- The graph has no directed cycle. -/
def Acyclic (w : List (SnakeLetter Q B)) : Prop :=
  ∀ v, ¬ Relation.TransGen (EdgeRel w) v v

/-- The graph has at most one source. -/
def SrcUnique (w : List (SnakeLetter Q B)) : Prop := ∀ v v', Src w v → Src w v' → v = v'

/-! ## Iterating a partial function without cycles -/

/-- The `n`-th iterate of a partial function. -/
def iterOpt {V : Type} (f : V → Option V) : ℕ → V → Option V
  | 0, v => some v
  | n + 1, v => (iterOpt f n v).bind f

lemma iterOpt_add {V : Type} (f : V → Option V) (a b : ℕ) (v : V) :
    iterOpt f (a + b) v = (iterOpt f a v).bind (iterOpt f b) := by
  induction b with
  | zero => cases h : iterOpt f a v <;> simp [iterOpt, h]
  | succ b ih =>
      rw [show a + (b + 1) = (a + b) + 1 from rfl, iterOpt, ih]
      cases h : iterOpt f a v with
      | none => simp [iterOpt]
      | some z => simp [iterOpt]

lemma iterOpt_none {V : Type} (f : V → Option V) {n : ℕ} {v : V} (h : iterOpt f n v = none)
    (m : ℕ) (hm : n ≤ m) : iterOpt f m v = none := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [iterOpt_add, h]
  rfl

/-- An iteration without cycles inside a finite set stops. -/
lemma exists_iterOpt_none {V : Type} (f : V → Option V) (S : Set V) (hS : S.Finite)
    (hmaps : ∀ {u z : V}, f u = some z → z ∈ S)
    (hacyc : ∀ (u : V) (n : ℕ), 0 < n → iterOpt f n u ≠ some u) (v : V) :
    ∃ n, iterOpt f n v = none := by
  by_contra hcon
  push_neg at hcon
  -- the iterates are pairwise distinct and, from the first step on, live in `S`
  have hsome : ∀ n, ∃ z, iterOpt f n v = some z := by
    intro n
    rcases h : iterOpt f n v with _ | z
    · exact absurd h (hcon n)
    · exact ⟨z, rfl⟩
  set g : ℕ → V := fun n => (iterOpt f (n + 1) v).get (by
    rcases hsome (n + 1) with ⟨z, hz⟩; rw [hz]; exact rfl) with hg
  have hgval : ∀ n, iterOpt f (n + 1) v = some (g n) := by
    intro n
    rcases hsome (n + 1) with ⟨z, hz⟩
    simp [hg, hz]
  have hgS : ∀ n, g n ∈ S := by
    intro n
    rcases hsome n with ⟨y, hy⟩
    have : iterOpt f (n + 1) v = f y := by rw [iterOpt, hy]; rfl
    rw [hgval n] at this
    exact hmaps this.symm
  have hginj : Function.Injective g := by
    intro a b hab
    by_contra hne
    rcases Nat.lt_or_ge a b with hlt | hge
    · have h1 : iterOpt f (a + 1) v = some (g a) := hgval a
      have h2 : iterOpt f (b + 1) v = some (g a) := by rw [hgval b, hab]
      have hsplit : iterOpt f ((a + 1) + (b - a)) v = (iterOpt f (a + 1) v).bind
          (iterOpt f (b - a)) := iterOpt_add f _ _ v
      rw [show (a + 1) + (b - a) = b + 1 by omega, h2, h1] at hsplit
      exact hacyc (g a) (b - a) (by omega) hsplit.symm
    · have hlt : b < a := by omega
      have h1 : iterOpt f (b + 1) v = some (g b) := hgval b
      have h2 : iterOpt f (a + 1) v = some (g b) := by rw [hgval a, hab]
      have hsplit : iterOpt f ((b + 1) + (a - b)) v = (iterOpt f (b + 1) v).bind
          (iterOpt f (a - b)) := iterOpt_add f _ _ v
      rw [show (b + 1) + (a - b) = a + 1 by omega, h2, h1] at hsplit
      exact hacyc (g b) (a - b) (by omega) hsplit.symm
  exact Set.infinite_range_of_injective hginj (hS.subset (by
    rintro x ⟨n, rfl⟩; exact hgS n))

/-! ## The successor and the predecessor of a vertex -/

open Classical in
/-- The outgoing edge of `v`, if there is one. -/
noncomputable def nxtE (w : List (SnakeLetter Q B)) (v : Vtx Q) : Option (Vtx Q × Option B) :=
  if h : ∃ z : Vtx Q × Option B, Edge w v z.1 z.2 then some h.choose else none

open Classical in
/-- The incoming edge of `v`, if there is one. -/
noncomputable def prvE (w : List (SnakeLetter Q B)) (v : Vtx Q) : Option (Vtx Q × Option B) :=
  if h : ∃ z : Vtx Q × Option B, Edge w z.1 v z.2 then some h.choose else none

lemma nxtE_eq_none_iff {w : List (SnakeLetter Q B)} {v : Vtx Q} :
    nxtE w v = none ↔ ¬ HasOut w v := by
  classical
  rw [nxtE]
  constructor
  · intro h ⟨v', o, hvo⟩
    rw [dif_pos ⟨(v', o), hvo⟩] at h
    exact absurd h (by simp)
  · intro h
    rw [dif_neg]
    rintro ⟨z, hz⟩
    exact h ⟨z.1, z.2, hz⟩

lemma edge_of_nxtE {w : List (SnakeLetter Q B)} {v : Vtx Q} {z : Vtx Q × Option B}
    (h : nxtE w v = some z) : Edge w v z.1 z.2 := by
  classical
  rw [nxtE] at h
  split at h
  · rename_i hex
    rw [Option.some_inj] at h
    subst h
    exact hex.choose_spec
  · exact absurd h (by simp)

lemma nxtE_eq_some {w : List (SnakeLetter Q B)} (hout : OutDegLe1 w) {v v' : Vtx Q} {o : Option B}
    (h : Edge w v v' o) : nxtE w v = some (v', o) := by
  classical
  rcases hz : nxtE w v with _ | z
  · exact absurd ⟨v', o, h⟩ (nxtE_eq_none_iff.1 hz)
  · obtain ⟨h1, h2⟩ := hout v z.1 v' z.2 o (edge_of_nxtE hz) h
    rw [← h1, ← h2]

lemma prvE_eq_none_iff {w : List (SnakeLetter Q B)} {v : Vtx Q} :
    prvE w v = none ↔ ¬ HasIn w v := by
  classical
  rw [prvE]
  constructor
  · intro h ⟨u, o, hvo⟩
    rw [dif_pos ⟨(u, o), hvo⟩] at h
    exact absurd h (by simp)
  · intro h
    rw [dif_neg]
    rintro ⟨z, hz⟩
    exact h ⟨z.1, z.2, hz⟩

lemma edge_of_prvE {w : List (SnakeLetter Q B)} {v : Vtx Q} {z : Vtx Q × Option B}
    (h : prvE w v = some z) : Edge w z.1 v z.2 := by
  classical
  rw [prvE] at h
  split at h
  · rename_i hex
    rw [Option.some_inj] at h
    subst h
    exact hex.choose_spec
  · exact absurd h (by simp)

lemma prvE_eq_some {w : List (SnakeLetter Q B)} (hin : InDegLe1 w) {u v : Vtx Q} {o : Option B}
    (h : Edge w u v o) : prvE w v = some (u, o) := by
  classical
  rcases hz : prvE w v with _ | z
  · exact absurd ⟨u, o, h⟩ (prvE_eq_none_iff.1 hz)
  · obtain ⟨h1, h2⟩ := hin z.1 u v z.2 o (edge_of_prvE hz) h
    rw [← h1, ← h2]

/-- The vertex reached by the outgoing edge. -/
noncomputable def nxt (w : List (SnakeLetter Q B)) (v : Vtx Q) : Option (Vtx Q) :=
  (nxtE w v).map Prod.fst

/-- The vertex from which the incoming edge comes. -/
noncomputable def prv (w : List (SnakeLetter Q B)) (v : Vtx Q) : Option (Vtx Q) :=
  (prvE w v).map Prod.fst

@[simp] lemma iterOpt_zero {V : Type} (f : V → Option V) (v : V) : iterOpt f 0 v = some v := rfl

@[simp] lemma iterOpt_succ {V : Type} (f : V → Option V) (n : ℕ) (v : V) :
    iterOpt f (n + 1) v = (iterOpt f n v).bind f := rfl

/-! ## Walking forwards and backwards -/

/-- The label of the outgoing edge of `v`, if there is one. -/
noncomputable def labOf (w : List (SnakeLetter Q B)) (v : Vtx Q) : Option B :=
  (nxtE w v).elim none Prod.snd

/-- One step forward along the graph: a vertex with no outgoing edge stays put. -/
noncomputable def fstep (w : List (SnakeLetter Q B)) (v : Vtx Q) : Vtx Q := (nxt w v).getD v

/-- One step backward along the graph: a vertex with no incoming edge stays put. -/
noncomputable def bstep (w : List (SnakeLetter Q B)) (v : Vtx Q) : Vtx Q := (prv w v).getD v

section Walk

variable {w : List (SnakeLetter Q B)}

lemma nxt_eq_some_of_edge (hout : OutDegLe1 w) {v v' : Vtx Q} {o : Option B} (h : Edge w v v' o) :
    nxt w v = some v' := by
  simp [nxt, nxtE_eq_some hout h]

lemma labOf_eq_of_edge (hout : OutDegLe1 w) {v v' : Vtx Q} {o : Option B} (h : Edge w v v' o) :
    labOf w v = o := by
  simp [labOf, nxtE_eq_some hout h]

lemma fstep_eq_of_edge (hout : OutDegLe1 w) {v v' : Vtx Q} {o : Option B} (h : Edge w v v' o) :
    fstep w v = v' := by
  simp [fstep, nxt_eq_some_of_edge hout h]

lemma fstep_eq_self {v : Vtx Q} (h : ¬ HasOut w v) : fstep w v = v := by
  simp [fstep, nxt, nxtE_eq_none_iff.2 h]

lemma edge_fstep {v : Vtx Q} (h : HasOut w v) : Edge w v (fstep w v) (labOf w v) := by
  rcases hz : nxtE w v with _ | z
  · exact absurd h (nxtE_eq_none_iff.1 hz)
  · have he := edge_of_nxtE hz
    have h1 : fstep w v = z.1 := by simp [fstep, nxt, hz]
    have h2 : labOf w v = z.2 := by simp [labOf, hz]
    rw [h1, h2]
    exact he

lemma bstep_edge {v : Vtx Q} (h : HasIn w v) :
    Edge w (bstep w v) v ((prvE w v).elim none Prod.snd) := by
  rcases hz : prvE w v with _ | z
  · exact absurd h (prvE_eq_none_iff.1 hz)
  · have he := edge_of_prvE hz
    have h1 : bstep w v = z.1 := by simp [bstep, prv, hz]
    rw [h1]
    exact he

lemma hasOut_bstep {v : Vtx Q} (h : HasIn w v) : HasOut w (bstep w v) :=
  ⟨v, _, bstep_edge h⟩

lemma fstep_bstep (hout : OutDegLe1 w) {v : Vtx Q} (h : HasIn w v) : fstep w (bstep w v) = v :=
  fstep_eq_of_edge hout (bstep_edge h)

/-! ### The walk terminates -/

/-- The vertices that carry an edge are finitely many. -/
lemma finite_cols [Finite Q] : {v : Vtx Q | v.2 ≤ w.length}.Finite := by
  have hsub : {v : Vtx Q | v.2 ≤ w.length} ⊆ (Set.univ : Set Q) ×ˢ (Set.Iic w.length) := by
    rintro ⟨q, n⟩ h
    exact ⟨Set.mem_univ _, h⟩
  exact Set.Finite.subset (Set.Finite.prod Set.finite_univ (Set.finite_Iic _)) hsub

lemma iterOpt_getD {V : Type} (f : V → Option V) (g : V → V) (hg : ∀ u, g u = (f u).getD u)
    (v : V) : ∀ (n : ℕ) (z : V), iterOpt f n v = some z → g^[n] v = z := by
  intro n
  induction n with
  | zero => intro z h; simpa using h
  | succ n ih =>
      intro z h
      rw [iterOpt_succ] at h
      rcases hy : iterOpt f n v with _ | y
      · rw [hy] at h; exact absurd h (by simp)
      · rw [hy] at h
        rw [Function.iterate_succ_apply', ih y hy, hg]
        simp only [Option.bind_some] at h
        simp [h]

lemma exists_step_none {V : Type} (f : V → Option V) (v : V) :
    ∀ (n : ℕ), iterOpt f n v = none → ∃ t z, iterOpt f t v = some z ∧ f z = none := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (by simp)
  | succ n ih =>
      intro h
      rw [iterOpt_succ] at h
      rcases hy : iterOpt f n v with _ | y
      · exact ih hy
      · rw [hy] at h
        exact ⟨n, y, hy, by simpa using h⟩

lemma transGen_of_iterOpt_nxt :
    ∀ (n : ℕ) (u z : Vtx Q), 0 < n → iterOpt (nxt w) n u = some z →
      Relation.TransGen (EdgeRel w) u z := by
  intro n
  induction n with
  | zero => intro u z h; omega
  | succ n ih =>
      intro u z _ h
      rw [iterOpt_succ] at h
      rcases hy : iterOpt (nxt w) n u with _ | y
      · rw [hy] at h; exact absurd h (by simp)
      · rw [hy] at h
        simp only [Option.bind_some] at h
        have hy' : HasOut w y := by
          rcases hzz : nxtE w y with _ | zz
          · simp [nxt, hzz] at h
          · exact ⟨zz.1, zz.2, edge_of_nxtE hzz⟩
        have hfz : fstep w y = z := by simp [fstep, h]
        have hyz : Edge w y z (labOf w y) := by rw [← hfz]; exact edge_fstep hy'
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · have huy : u = y := by simpa using hy
          subst huy
          exact Relation.TransGen.single ⟨_, hyz⟩
        · exact (ih u y hn hy).tail ⟨_, hyz⟩

lemma transGen_of_iterOpt_prv :
    ∀ (n : ℕ) (u z : Vtx Q), 0 < n → iterOpt (prv w) n u = some z →
      Relation.TransGen (EdgeRel w) z u := by
  intro n
  induction n with
  | zero => intro u z h; omega
  | succ n ih =>
      intro u z _ h
      rw [iterOpt_succ] at h
      rcases hy : iterOpt (prv w) n u with _ | y
      · rw [hy] at h; exact absurd h (by simp)
      · rw [hy] at h
        simp only [Option.bind_some] at h
        have hy' : HasIn w y := by
          rcases hzz : prvE w y with _ | zz
          · simp [prv, hzz] at h
          · exact ⟨zz.1, zz.2, edge_of_prvE hzz⟩
        have hbz : bstep w y = z := by simp [bstep, h]
        have hyz : Edge w z y ((prvE w y).elim none Prod.snd) := by
          rw [← hbz]; exact bstep_edge hy'
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · have huy : u = y := by simpa using hy
          subst huy
          exact Relation.TransGen.single ⟨_, hyz⟩
        · exact Relation.TransGen.head ⟨_, hyz⟩ (ih u y hn hy)

/-- Walking forward along an acyclic graph reaches a vertex with no outgoing edge. -/
lemma exists_not_hasOut [Finite Q] (hacyc : Acyclic w) (v : Vtx Q) :
    ∃ n, ¬ HasOut w ((fstep w)^[n] v) := by
  have hex : ∃ n, iterOpt (nxt w) n v = none := by
    refine exists_iterOpt_none (nxt w) {u : Vtx Q | u.2 ≤ w.length} finite_cols ?_ ?_ v
    · intro u z hz
      rcases hy : nxtE w u with _ | y
      · simp [nxt, hy] at hz
      · have hz' : some y.1 = some z := by rw [← hz]; simp [nxt, hy]
        have he := edge_of_nxtE hy
        rw [Option.some_inj.1 hz'] at he
        exact edge_col_le_right he
    · intro u n hn hu
      exact hacyc u (transGen_of_iterOpt_nxt n u u hn hu)
  obtain ⟨n, hn⟩ := hex
  obtain ⟨t, z, hz, hfz⟩ := exists_step_none (nxt w) v n hn
  refine ⟨t, ?_⟩
  rw [iterOpt_getD (nxt w) (fstep w) (fun u => rfl) v t z hz]
  refine nxtE_eq_none_iff.1 ?_
  rcases hy : nxtE w z with _ | y
  · rfl
  · simp [nxt, hy] at hfz

/-- Walking backward along an acyclic graph reaches a vertex with no incoming edge. -/
lemma exists_not_hasIn [Finite Q] (hacyc : Acyclic w) (v : Vtx Q) :
    ∃ n, ¬ HasIn w ((bstep w)^[n] v) := by
  have hex : ∃ n, iterOpt (prv w) n v = none := by
    refine exists_iterOpt_none (prv w) {u : Vtx Q | u.2 ≤ w.length} finite_cols ?_ ?_ v
    · intro u z hz
      rcases hy : prvE w u with _ | y
      · simp [prv, hy] at hz
      · have hz' : some y.1 = some z := by rw [← hz]; simp [prv, hy]
        have he := edge_of_prvE hy
        rw [Option.some_inj.1 hz'] at he
        exact edge_col_le_left he
    · intro u n hn hu
      exact hacyc u (transGen_of_iterOpt_prv n u u hn hu)
  obtain ⟨n, hn⟩ := hex
  obtain ⟨t, z, hz, hfz⟩ := exists_step_none (prv w) v n hn
  refine ⟨t, ?_⟩
  rw [iterOpt_getD (prv w) (bstep w) (fun u => rfl) v t z hz]
  refine prvE_eq_none_iff.1 ?_
  rcases hy : prvE w z with _ | y
  · rfl
  · simp [prv, hy] at hfz

/-- Walking backwards from a vertex with an outgoing edge reaches the source of its component. -/
lemma exists_src_of_hasOut [Finite Q] (hout : OutDegLe1 w) (hacyc : Acyclic w) {u : Vtx Q}
    (hu : HasOut w u) :
    ∃ t, Src w ((bstep w)^[t] u) ∧ (fstep w)^[t] ((bstep w)^[t] u) = u := by
  classical
  have hex := exists_not_hasIn hacyc u
  have hnot : ¬ HasIn w ((bstep w)^[Nat.find hex] u) := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, HasIn w ((bstep w)^[j] u) := fun j hj =>
    not_not.1 (Nat.find_min hex hj)
  have hout' : ∀ j ≤ Nat.find hex, HasOut w ((bstep w)^[j] u) := by
    intro j
    induction j with
    | zero => intro _; exact hu
    | succ j _ =>
        intro hj
        rw [Function.iterate_succ_apply']
        exact hasOut_bstep (hmin j (by omega))
  have hback : ∀ j ≤ Nat.find hex, (fstep w)^[j] ((bstep w)^[j] u) = u := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
        intro hj
        rw [Function.iterate_succ_apply, Function.iterate_succ_apply',
          fstep_bstep hout (hmin j (by omega))]
        exact ih (by omega)
  exact ⟨Nat.find hex, ⟨hout' _ (le_refl _), hnot⟩, hback _ (le_refl _)⟩

end Walk

/-- The conditions are necessary. -/
theorem conditions_of_representsSnake {w : List (SnakeLetter Q B)} (h : RepresentsSnake w) :
    OutDegLe1 w ∧ InDegLe1 w ∧ Acyclic w ∧ SrcUnique w := by
  obtain ⟨m, p, lab, hp⟩ := h
  refine ⟨fun v v₁ v₂ o₁ o₂ h₁ h₂ => hp.outUnique h₁ h₂,
    fun u₁ u₂ v o₁ o₂ h₁ h₂ => hp.inUnique h₁ h₂, hp.acyclic, fun v v' hv hv' => ?_⟩
  rw [hp.src_eq hv, hp.src_eq hv']

/-! ## The characterisation -/

/-- **A string represents a snake graph iff the graph it describes has in- and out-degree at most
one, no cycle and at most one source.**

From left to right this is `SnakeGraph.conditions_of_representsSnake`.  From right to left: if the
graph has no edge at all it is the snake graph of length `0`; otherwise one walks backwards from a
vertex with an outgoing edge -- the walk terminates because the graph is finite and acyclic -- and
reaches a source, which is *the* source of the graph; the path that walks forward from that source
covers every edge, because every vertex with an outgoing edge is reached from the source in the same
way. -/
theorem representsSnake_iff [Finite Q] [Nonempty Q] (w : List (SnakeLetter Q B)) :
    RepresentsSnake w ↔ OutDegLe1 w ∧ InDegLe1 w ∧ Acyclic w ∧ SrcUnique w := by
  classical
  refine ⟨conditions_of_representsSnake, ?_⟩
  rintro ⟨hout, hin, hacyc, huniq⟩
  by_cases hedge : ∃ u v o, Edge w u v o
  · obtain ⟨u0, v0, o0, he0⟩ := hedge
    obtain ⟨s, hsrc0⟩ : ∃ s : Vtx Q, Src w s := by
      obtain ⟨t0, h0, -⟩ := exists_src_of_hasOut hout hacyc (u := u0) ⟨v0, o0, he0⟩
      exact ⟨_, h0⟩
    obtain ⟨m, hmnot, hmmin⟩ : ∃ m, ¬ HasOut w ((fstep w)^[m] s) ∧
        ∀ j < m, HasOut w ((fstep w)^[j] s) := by
      have hexm := exists_not_hasOut hacyc s
      exact ⟨Nat.find hexm, Nat.find_spec hexm, fun j hj => not_not.1 (Nat.find_min hexm hj)⟩
    have hedge' : ∀ t < m, Edge w ((fstep w)^[t] s) ((fstep w)^[t + 1] s)
        (labOf w ((fstep w)^[t] s)) := by
      intro t ht
      rw [Function.iterate_succ_apply']
      exact edge_fstep (hmmin t ht)
    have htrans : ∀ a d, a + d + 1 ≤ m →
        Relation.TransGen (EdgeRel w) ((fstep w)^[a] s) ((fstep w)^[a + d + 1] s) := by
      intro a d
      induction d with
      | zero => intro _; exact Relation.TransGen.single ⟨_, hedge' a (by omega)⟩
      | succ d ih => intro _; exact (ih (by omega)).tail ⟨_, hedge' (a + d + 1) (by omega)⟩
    have hstabd : ∀ d, (fstep w)^[m + d] s = (fstep w)^[m] s := by
      intro d
      induction d with
      | zero => rfl
      | succ d ih =>
          rw [show m + (d + 1) = (m + d) + 1 by omega, Function.iterate_succ_apply', ih,
            fstep_eq_self hmnot]
    refine ⟨m, fun t => (fstep w)^[t] s, fun t => labOf w ((fstep w)^[t] s), ⟨hedge', ?_, ?_⟩⟩
    · intro a ha b hb hab
      by_contra hne
      rcases Nat.lt_or_ge a b with hlt | hge
      · obtain ⟨d, rfl⟩ : ∃ d, b = a + d + 1 := ⟨b - a - 1, by omega⟩
        have ht := htrans a d (by omega)
        rw [← hab] at ht
        exact hacyc _ ht
      · obtain ⟨d, rfl⟩ : ∃ d, a = b + d + 1 := ⟨a - b - 1, by omega⟩
        have ht := htrans b d (by omega)
        rw [hab] at ht
        exact hacyc _ ht
    · intro u v' o hu
      obtain ⟨t, hsrct, hbt⟩ := exists_src_of_hasOut hout hacyc (u := u) ⟨v', o, hu⟩
      have hst : (bstep w)^[t] u = s := huniq _ _ hsrct hsrc0
      have hput : (fstep w)^[t] s = u := by rw [← hst]; exact hbt
      have htm : t < m := by
        by_contra hcon
        obtain ⟨d, hd⟩ : ∃ d, t = m + d := ⟨t - m, by omega⟩
        subst hd
        have h1 : (fstep w)^[m] s = u := by rw [← hstabd d]; exact hput
        apply hmnot
        rw [h1]
        exact ⟨v', o, hu⟩
      refine ⟨t, htm, hput, ?_, ?_⟩
      · rw [Function.iterate_succ_apply', hput, fstep_eq_of_edge hout hu]
      · rw [hput]
        exact labOf_eq_of_edge hout hu
  · push_neg at hedge
    refine ⟨0, fun _ => (Classical.arbitrary Q, 0), fun _ => none, ⟨?_, ?_, ?_⟩⟩
    · intro t ht
      exact absurd ht (by omega)
    · intro a ha b hb _
      omega
    · intro u v' o hu
      exact absurd hu (hedge u v' o)

end SnakeGraph

end Lax916827Proofs.Transducers
