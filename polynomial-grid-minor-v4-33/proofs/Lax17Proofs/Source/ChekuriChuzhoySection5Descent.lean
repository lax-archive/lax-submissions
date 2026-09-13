import Lax17Proofs.Source.ChekuriChuzhoySection5Clustering
import Lax17Proofs.Source.TreeOfSetsBandwidth

namespace Lax17Proofs

universe u v w

/-!
# Nonalgorithmic Section 5 potential descent

The paper presents nested iterative algorithms.  For the existential theorem,
well-foundedness of the natural-valued potential is sufficient: if every
valid non-output state has a valid strict successor, choose a state of minimum
attained potential and derive a contradiction.
-/

namespace SimpleGraph
namespace ChekuriChuzhoySection5Descent


/-- Generic finite-output descent.  Unlike a termination-bound proof, this
needs neither a list of execution states nor a discretized running time. -/
theorem output_of_natPotential_descent
    {State : Type*} (potential : State → ℕ) (Valid : State → Prop)
    (Output : Prop) (initial : State) (hinitial : Valid initial)
    (step : ∀ state, Valid state →
      Output ∨ ∃ next, Valid next ∧ potential next < potential state) :
    Output := by
  classical
  by_contra houtput
  have hstep : ∀ state, Valid state → ¬ Output →
      ∃ next, Valid next ∧ potential next < potential state := by
    intro state hvalid _
    rcases step state hvalid with hout | hnext
    · exact False.elim (houtput hout)
    · exact hnext
  rcases ChekuriChuzhoySection5Clustering.exists_good_of_potential_descent
      potential Valid (fun _ => Output) initial hinitial (by
        intro state hvalid hbad
        exact hstep state hvalid hbad) with
    ⟨_state, _hvalid, hout⟩
  exact houtput hout

/-- The outer Section 5 loop specialized to the desired bandwidth
tree-of-sets output.  The remaining source work is exactly the one-step
tree-or-potential-drop theorem. -/
theorem exists_bandwidthTreeOfSets_of_clustering_descent
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : _root_.SimpleGraph V}
    {m w alphaNum alphaDen : ℕ}
    (potential :
      ChekuriChuzhoySection5Clustering.VertexClustering V → ℕ)
    (Valid : ChekuriChuzhoySection5Clustering.VertexClustering V → Prop)
    (initial : ChekuriChuzhoySection5Clustering.VertexClustering V)
    (hinitial : Valid initial)
    (step : ∀ clustering, Valid clustering →
      Nonempty (BandwidthTreeOfSetsSystem G m w alphaNum alphaDen) ∨
        ∃ next, Valid next ∧ potential next < potential clustering) :
    Nonempty (BandwidthTreeOfSetsSystem G m w alphaNum alphaDen) := by
  exact output_of_natPotential_descent potential Valid
    (Nonempty (BandwidthTreeOfSetsSystem G m w alphaNum alphaDen))
    initial hinitial step

end ChekuriChuzhoySection5Descent
end SimpleGraph

end Lax17Proofs
