import Lax303502Proofs.LongestCycle
import Lax303502Proofs.CircularGluing
import Lax68.OuterplanarExcludedMinors

set_option autoImplicit false

universe u

namespace Lax303502Proofs

/-- The constructive converse of the outerplanar forbidden-minor theorem. -/
theorem excluded_minors_circular {V : Type u} [Fintype V] (G : SimpleGraph V)
    (hK : Lax68.Outerplanar.IsOuterplanarByExcludedMinors G) : Nonempty (CircularDrawing G) := by
  classical
  induction hn : Fintype.card V using Nat.strong_induction_on generalizing V with
  | h n ih =>
    have smaller (S : Set V) (hS : ∃ x, x ∉ S) : Nonempty (CircularDrawing (G.induce S)) := by
      obtain ⟨x,hx⟩ := hS
      have hcard : Fintype.card S < n := by
        rw [← hn]
        exact Fintype.card_subtype_lt hx
      exact ih _ hcard (G.induce S) (excludedMinors_induce hK S) rfl
    by_cases hsub : Subsingleton V
    · let := hsub
      exact ⟨⟨fun _ => 0,fun _ _ _ => Subsingleton.elim _ _,
        fun h _ _ => (h.ne (Subsingleton.elim _ _)).elim⟩⟩
    let : Nontrivial V := not_subsingleton_iff_nontrivial.mp hsub
    by_cases hpre : G.Preconnected
    · by_cases hacyc : G.IsAcyclic
      · obtain ⟨D⟩ := tree_parametric G ⟨⟨hpre⟩,hacyc⟩
        exact ⟨D.toCircular⟩
      by_cases hdel : ∀ v, (G.induce {v}ᶜ).Preconnected
      · have hcycle : ∃ a, ∃ p : G.Walk a a, p.IsCycle := by
          simpa only [SimpleGraph.IsAcyclic,not_forall,not_not] using hacyc
        obtain ⟨a,p,hp,hmax⟩ := exists_longest_cycle hcycle
        have hspan := longest_cycle_spanning hpre hdel hK.2 hp hmax
        exact ⟨spanningCycle_drawing p.getVert (cycle_index_injective hp)
          (fun i hi => p.adj_getVert_succ hi) (by simp)
          (fun v => cycle_index_of_mem hp (hspan v)) hK.1⟩
      push Not at hdel
      obtain ⟨v,hv⟩ := hdel
      obtain ⟨U,hU,⟨x,hx⟩,⟨y,hy,hyU⟩,hclosed⟩ := not_preconnected_partition hv
      have hvU : v ∉ U := fun h => hU h (by simp)
      have hyv : y ≠ v := by simpa using hy
      obtain ⟨D⟩ := smaller (insert v U) ⟨y,by simpa [hyv] using hyU⟩
      obtain ⟨E⟩ := smaller Uᶜ ⟨x,by simpa using hx⟩
      apply D.glue_vertex (E:=E) (v:=v)
      · ext z; simp; tauto
      · simp
      · exact hvU
      · intro z hz hz'
        rcases hz with hz | hz
        · exact hz
        · exact (hz' hz).elim
      · intro a b hab
        by_cases ha : a ∈ U
        · left
          refine ⟨Or.inr ha,?_⟩
          by_cases hb : b = v
          · exact Or.inl hb
          · exact Or.inr (hclosed a ha b (by simpa using hb) hab)
        · by_cases hb : b ∈ U
          · left
            refine ⟨?_,Or.inr hb⟩
            by_cases hav : a = v
            · exact Or.inl hav
            · exact (ha (hclosed b hb a (by simpa using hav) hab.symm)).elim
          · exact Or.inr ⟨ha,hb⟩
    · have huniv : ¬(G.induce Set.univ).Preconnected := by
        intro hh
        apply hpre
        intro x y
        obtain ⟨p⟩ := hh ⟨x,Set.mem_univ x⟩ ⟨y,Set.mem_univ y⟩
        exact ⟨p.map (SimpleGraph.Embedding.induce Set.univ).toHom⟩
      obtain ⟨U,_,⟨x,hx⟩,⟨y,_,hy⟩,hclosed⟩ := not_preconnected_partition huniv
      obtain ⟨D⟩ := smaller U ⟨y,hy⟩
      obtain ⟨E⟩ := smaller Uᶜ ⟨x,by simpa using hx⟩
      apply D.glue_disjoint (E:=E) (Set.union_compl_self U) (by simp [Set.disjoint_left])
      intro a b hab
      by_cases ha : a ∈ U
      · exact Or.inl ⟨ha,hclosed a ha b (Set.mem_univ b) hab⟩
      · exact Or.inr ⟨ha,fun hb => ha (hclosed b hb a (Set.mem_univ a) hab.symm)⟩

/--
---
conclusion: Lax68.OuterplanarExcludedMinors.outerplanar_iff_excludedMinors
---
A finite graph admits a straight-line drawing on a circle exactly when it has
neither a `K₄` nor a `K₂,₃` minor.

# Proof strategy

Induction first splits disconnected graphs and graphs with a cut vertex;
acyclic connected graphs use the tree construction. In the remaining case,
a longest cycle must span: an outside component has two distinct attachments;
consecutive attachments extend the cycle, and nonconsecutive attachments give
a `K₂,₃` minor. Put the spanning cycle in circular order. Two crossing chords
would give a `K₄` minor. Smaller pieces can be joined in separate arcs at a
shared vertex, so induction handles arbitrary finite graphs.

For the forward direction, normalize an arbitrary circle drawing to rational
circle parameters. Chords meet exactly when their endpoints alternate.
Connected disjoint branch sets cannot alternate, so choosing one representative
from each branch set preserves the circular drawing of every minor. Neither
`K₄` nor `K₂,₃` admits such an order. All geometry, gluing, and minor witnesses
are checked explicitly; no other open characterization is assumed.

# Attribution

First checked Diestel, *Graph Theory*, sixth edition,
[Chapter 4, Exercise 23](https://www.math.uni-hamburg.de/home/diestel/books/graph.theory/preview/Ch4.pdf),
which states this characterization without a worked solution. The direct
longest-cycle argument is in Madeleine Leander,
[*On the bunkbed conjecture* (2009), Theorem 14, printed page 37](https://kurser.math.su.se/pluginfile.php/16103/mod_folder/content/0/2009/2009_07_report.pdf).
We supply the disconnected and cut-vertex reductions explicitly before
using its argument for a graph with no cut vertex. The formal development
also supplies the circle geometry and connected-branch-set argument for
the forward implication.
-/
theorem outerplanar_iff_excludedMinors {V : Type*} {G : SimpleGraph V} :
    Finite V → (Lax68.Outerplanar.IsOuterplanar G ↔
      Lax68.Outerplanar.IsOuterplanarByExcludedMinors G) := by
  intro hfin
  let := Fintype.ofFinite V
  constructor
  · exact outerplanar_excludes_minors
  · intro hK
    obtain ⟨D⟩ := excluded_minors_circular G hK
    exact ⟨D.toParametric.toOuterplane⟩

end Lax303502Proofs
