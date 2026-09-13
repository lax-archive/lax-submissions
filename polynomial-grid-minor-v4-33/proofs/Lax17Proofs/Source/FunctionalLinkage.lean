import Lax17Proofs.Source.Paths

namespace Lax17Proofs

universe u v w

/-!
# Linkages from a finite partial successor relation

A standard linkage-splicing argument replaces several disjoint subpaths by a
new perfect routing between the same oriented boundary sets.  After the
replacement, every nonterminal vertex has a unique successor and every
non-source vertex has a unique predecessor.  This module packages the finite
argument that the resulting directed chains still form a perfect linkage.

The proof is deliberately independent of a particular path decomposition.
Termination uses finiteness: if the successor chain from a source never met a
target, the successor map on its finite reachable set would be injective and
hence surjective, giving the source a predecessor.
-/

namespace SimpleGraph
namespace TreewidthSparsifier


variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- Proof data for a finite directed collection of vertex-disjoint
source-to-target chains inside an undirected graph. -/
structure FunctionalLinkage
    (G : _root_.SimpleGraph V) (S T : Finset V) where
  step : V → V → Prop
  step_decidable : DecidableRel step := by classical exact Classical.decRel _
  step_adj : ∀ ⦃u v : V⦄, step u v → G.Adj u v
  right_unique : Relator.RightUnique step
  left_unique : Relator.LeftUnique step
  source_active : ∀ s ∈ S, ∃ v, step s v
  source_no_predecessor : ∀ s ∈ S, ∀ v, ¬ step v s
  successor_or_target :
    ∀ ⦃s v : V⦄,
      s ∈ S →
        Relation.ReflTransGen step s v →
          v ∈ T ∨ ∃ w, step v w
  card_eq : S.card = T.card

namespace FunctionalLinkage

variable {S T : Finset V} (F : FunctionalLinkage G S T)

local instance : DecidableRel F.step := F.step_decidable

/-- Vertices reachable by following successors from `s`. -/
noncomputable def reachableFrom (s : V) : Finset V := by
  classical
  exact Finset.univ.filter fun v =>
    Relation.ReflTransGen F.step s v

@[simp] theorem mem_reachableFrom (s v : V) :
    v ∈ F.reachableFrom s ↔
      Relation.ReflTransGen F.step s v := by
  classical
  simp [reachableFrom]

theorem source_mem_reachableFrom (s : V) :
    s ∈ F.reachableFrom s := by
  exact (F.mem_reachableFrom s s).mpr Relation.ReflTransGen.refl

/-- If a source chain contains no target, successor is a self-map of its
finite reachable set. -/
noncomputable def successorOnReachable
    {s : V} (hs : s ∈ S)
    (hno : Disjoint (F.reachableFrom s) T) :
    {v : V // v ∈ F.reachableFrom s} →
      {v : V // v ∈ F.reachableFrom s} :=
  fun v => by
    have hvReach :
        Relation.ReflTransGen F.step s v.1 :=
      (F.mem_reachableFrom s v.1).mp v.2
    have hvNotT : v.1 ∉ T := by
      intro hvT
      exact Finset.disjoint_left.mp hno v.2 hvT
    have hex : ∃ w, F.step v.1 w :=
      (F.successor_or_target hs hvReach).resolve_left hvNotT
    let w := Classical.choose hex
    have hvw : F.step v.1 w := Classical.choose_spec hex
    exact
      ⟨w, (F.mem_reachableFrom s w).mpr
        (Relation.ReflTransGen.tail hvReach hvw)⟩

theorem successorOnReachable_step
    {s : V} (hs : s ∈ S)
    (hno : Disjoint (F.reachableFrom s) T)
    (v : {v : V // v ∈ F.reachableFrom s}) :
    F.step v.1 (F.successorOnReachable hs hno v).1 := by
  classical
  dsimp [successorOnReachable]
  exact Classical.choose_spec
    (F.successor_or_target hs
      ((F.mem_reachableFrom s v.1).mp v.2)
      |>.resolve_left (by
        intro hvT
        exact Finset.disjoint_left.mp hno v.2 hvT))

theorem successorOnReachable_injective
    {s : V} (hs : s ∈ S)
    (hno : Disjoint (F.reachableFrom s) T) :
    Function.Injective (F.successorOnReachable hs hno) := by
  intro u v huv
  apply Subtype.ext
  have hu := F.successorOnReachable_step hs hno u
  have hv := F.successorOnReachable_step hs hno v
  have hval :
      (F.successorOnReachable hs hno u).1 =
        (F.successorOnReachable hs hno v).1 :=
    congrArg Subtype.val huv
  rw [hval] at hu
  exact F.left_unique hu hv

/-- Every source reaches a target by repeatedly following successors. -/
theorem exists_reaches_target {s : V} (hs : s ∈ S) :
    ∃ t : V,
      t ∈ T ∧ Relation.ReflTransGen F.step s t := by
  classical
  by_contra hnot
  have hno : Disjoint (F.reachableFrom s) T := by
    rw [Finset.disjoint_left]
    intro t htReach htT
    exact hnot ⟨t, htT, (F.mem_reachableFrom s t).mp htReach⟩
  let f := F.successorOnReachable hs hno
  have hf : Function.Injective f :=
    F.successorOnReachable_injective hs hno
  have hsurj : Function.Surjective f :=
    (Fintype.bijective_iff_injective_and_card f).2
      ⟨hf, rfl⟩ |>.2
  let source :
      {v : V // v ∈ F.reachableFrom s} :=
    ⟨s, F.source_mem_reachableFrom s⟩
  rcases hsurj source with ⟨p, hp⟩
  have hpStep : F.step p.1 s := by
    have hvalue : (f p).1 = s :=
      congrArg Subtype.val hp
    have hpStep' := F.successorOnReachable_step hs hno p
    dsimp [f] at hvalue
    rw [hvalue] at hpStep'
    exact hpStep'
  exact F.source_no_predecessor s hs p.1 hpStep

/-- Two successor chains that meet and start at sources have the same
source. -/
theorem source_eq_of_reaches_same
    {s₁ s₂ v : V} (hs₁ : s₁ ∈ S) (hs₂ : s₂ ∈ S)
    (h₁ : Relation.ReflTransGen F.step s₁ v)
    (h₂ : Relation.ReflTransGen F.step s₂ v) :
    s₁ = s₂ := by
  induction h₁ with
  | refl =>
      rcases Relation.ReflTransGen.cases_tail h₂ with h | ⟨p, _hp, hpv⟩
      · exact h
      · exact False.elim (F.source_no_predecessor s₁ hs₁ p hpv)
  | @tail u v hsu huv ih =>
      rcases Relation.ReflTransGen.cases_tail h₂ with h | ⟨p, hsp, hpv⟩
      · subst v
        exact False.elim (F.source_no_predecessor s₂ hs₂ u huv)
      · have hup : u = p := F.left_unique huv hpv
        subst p
        exact ih hsp

/-- The directed closure of `step` is graph reachability. -/
theorem graph_reachable_of_reflTransGen
    {u v : V} (h : Relation.ReflTransGen F.step u v) :
    G.Reachable u v := by
  rw [_root_.SimpleGraph.reachable_iff_reflTransGen]
  exact h.lift (fun x : V => x) (fun _ _ hxy => F.step_adj hxy)

/-- A chosen target reached from a source. -/
noncomputable def reachedTarget (s : {v : V // v ∈ S}) : V :=
  Classical.choose (F.exists_reaches_target s.2)

theorem reachedTarget_mem (s : {v : V // v ∈ S}) :
    F.reachedTarget s ∈ T :=
  (Classical.choose_spec (F.exists_reaches_target s.2)).1

theorem reaches_reachedTarget (s : {v : V // v ∈ S}) :
    Relation.ReflTransGen F.step s.1 (F.reachedTarget s) :=
  (Classical.choose_spec (F.exists_reaches_target s.2)).2

/-- The undirected graph consisting exactly of successor edges. -/
def stepGraph : _root_.SimpleGraph V where
  Adj u v := F.step u v ∨ F.step v u
  symm := by
    intro u v h
    exact h.symm
  loopless := ⟨by
    intro v h
    rcases h with h | h
    · have := F.step_adj h
      exact this.ne rfl
    · have := F.step_adj h
      exact this.ne rfl⟩

theorem stepGraph_le : F.stepGraph ≤ G := by
  intro u v huv
  rcases huv with huv | hvu
  · exact F.step_adj huv
  · exact (F.step_adj hvu).symm

/-- Starting at a source, even undirected reachability in the successor graph
can only move forward along its unique directed chain. -/
theorem directed_reachable_of_stepGraph_reflTransGen
    {s v : V} (hs : s ∈ S)
    (h : Relation.ReflTransGen F.stepGraph.Adj s v) :
    Relation.ReflTransGen F.step s v := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | @tail u v hsu huv ih =>
      rcases huv with huv | hvu
      · exact Relation.ReflTransGen.tail ih huv
      · rcases Relation.ReflTransGen.cases_tail ih with hEq | ⟨p, hsp, hpu⟩
        · subst u
          exact False.elim (F.source_no_predecessor s hs v hvu)
        · have hpv : p = v := F.left_unique hpu hvu
          simpa [hpv] using hsp

/-- A chosen graph path following the successor chain from a source to its
selected reachable target. -/
noncomputable def chainPathInStepGraph
    (s : {v : V // v ∈ S}) : GraphPath F.stepGraph := by
  have hreach : F.stepGraph.Reachable s.1 (F.reachedTarget s) := by
    rw [_root_.SimpleGraph.reachable_iff_reflTransGen]
    exact
      (F.reaches_reachedTarget s).lift (fun x : V => x)
        (fun _ _ hxy => Or.inl hxy)
  exact GraphPath.ofWalk (Classical.choice hreach)

noncomputable def chainPath (s : {v : V // v ∈ S}) : GraphPath G :=
  (F.chainPathInStepGraph s).mapLe F.stepGraph_le

@[simp] theorem chainPath_source (s : {v : V // v ∈ S}) :
    (F.chainPath s).source = s.1 := rfl

@[simp] theorem chainPath_target (s : {v : V // v ∈ S}) :
    (F.chainPath s).target = F.reachedTarget s := rfl

theorem chainPath_vertex_reachable
    (s : {v : V // v ∈ S}) {v : V}
    (hv : v ∈ (F.chainPath s).vertexSet) :
    Relation.ReflTransGen F.step s.1 v := by
  have hv' : v ∈ (F.chainPathInStepGraph s).vertexSet := by
    simpa [chainPath] using hv
  have hweak : F.stepGraph.Reachable s.1 v := by
    let Q := F.chainPathInStepGraph s
    have hvQ : v ∈ Q.vertexSet := by simpa [Q] using hv'
    exact (Q.takeUntil hvQ).walk.reachable
  rw [_root_.SimpleGraph.reachable_iff_reflTransGen] at hweak
  exact F.directed_reachable_of_stepGraph_reflTransGen s.2 hweak

/-- Enumerate the finite source set in a universe-zero index type. -/
noncomputable def sourceAt
    (_F : FunctionalLinkage G S T)
    (i : Fin S.card) : {v : V // v ∈ S} :=
  S.equivFin.symm i

/-- Directed functional-chain data produces a perfect path packing. -/
noncomputable def toPerfectPathPacking :
    PerfectPathPacking G S T where
  Index := Fin S.card
  path := fun i => F.chainPath (F.sourceAt i)
  connects := by
    intro i
    let s := F.sourceAt i
    exact Or.inl
      ⟨s.2, by simpa [s] using F.reachedTarget_mem s⟩
  node_disjoint := by
    intro i j hij
    rw [GraphPath.NodeDisjoint, Finset.disjoint_left]
    intro v hvi hvj
    have hsEq :=
      F.source_eq_of_reaches_same
        (F.sourceAt i).2 (F.sourceAt j).2
        (F.chainPath_vertex_reachable (F.sourceAt i) hvi)
        (F.chainPath_vertex_reachable (F.sourceAt j) hvj)
    apply hij
    apply S.equivFin.symm.injective
    exact Subtype.ext hsEq
  source_mem := by
    intro i
    simpa using (F.sourceAt i).2
  target_mem := by
    intro i
    simpa using F.reachedTarget_mem (F.sourceAt i)
  source_bijective := by
    constructor
    · intro i j hij
      apply S.equivFin.symm.injective
      apply Subtype.ext
      exact congrArg Subtype.val hij
    · intro s
      refine ⟨S.equivFin s, ?_⟩
      apply Subtype.ext
      simp [sourceAt]
  target_bijective := by
    apply (Fintype.bijective_iff_injective_and_card _).2
    constructor
    · intro i j hij
      have htarget :
          F.reachedTarget (F.sourceAt i) =
            F.reachedTarget (F.sourceAt j) :=
        congrArg Subtype.val hij
      have hsEq :=
        F.source_eq_of_reaches_same
          (F.sourceAt i).2 (F.sourceAt j).2
          (F.reaches_reachedTarget (F.sourceAt i))
          (by simpa [htarget] using
            F.reaches_reachedTarget (F.sourceAt j))
      apply S.equivFin.symm.injective
      exact Subtype.ext hsEq
    · rw [Fintype.card_fin, Fintype.card_coe]
      exact F.card_eq

end FunctionalLinkage
end TreewidthSparsifier
end SimpleGraph

end Lax17Proofs
