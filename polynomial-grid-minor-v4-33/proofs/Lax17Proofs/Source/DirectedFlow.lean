import Mathlib.Tactic
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Order.Compact

namespace Lax17Proofs

universe u v w

/-!
# Finite directed flows

This file contains the finite directed-network core used to internalize the
fractional max-flow/min-cut input needed by the Chekuri--Chuzhoy boosting
theorem.

The graph is a directed multigraph represented by a finite arc type `E`; the
tail and head maps may identify parallel arcs.  Capacities and flows are real
valued.  The first part formalizes the cut-excess identity and weak duality.
-/

namespace SimpleGraph


open Finset

/-- A finite directed multigraph with nonnegative real capacities.  Parallel
arcs are represented by distinct elements of the finite type `E`. -/
structure DirectedNetwork (V : Type u) (E : Type v) where
  /-- Tail of a directed arc. -/
  tail : E → V
  /-- Head of a directed arc. -/
  head : E → V
  /-- Arc capacity. -/
  cap : E → ℝ
  /-- Capacities are nonnegative. -/
  cap_nonneg : ∀ e, 0 ≤ cap e

namespace DirectedNetwork

variable {V : Type u} {E : Type v} [Fintype E] [DecidableEq V]
variable (N : DirectedNetwork V E)

/-- Sum a real-valued arc function over arcs with a decidable predicate. -/
noncomputable def arcSum (p : E → Prop) [DecidablePred p] (x : E → ℝ) : ℝ :=
  ∑ e : E, if p e then x e else 0

/-- Total outgoing value of `x` from a vertex. -/
noncomputable def outflow (x : E → ℝ) (v : V) : ℝ :=
  ∑ e : E, if N.tail e = v then x e else 0

/-- Total incoming value of `x` to a vertex. -/
noncomputable def inflow (x : E → ℝ) (v : V) : ℝ :=
  ∑ e : E, if N.head e = v then x e else 0

/-- Signed excess at a vertex: outgoing minus incoming flow. -/
noncomputable def excess (x : E → ℝ) (v : V) : ℝ :=
  N.outflow x v - N.inflow x v

theorem continuous_outflow (v : V) :
    Continuous fun x : E → ℝ => N.outflow x v := by
  classical
  unfold outflow
  refine continuous_finsetSum Finset.univ ?_
  intro e _he
  by_cases h : N.tail e = v
  · simpa [h] using (continuous_apply e : Continuous fun x : E → ℝ => x e)
  · simpa [h] using (continuous_const : Continuous fun _ : E → ℝ => (0 : ℝ))

theorem continuous_inflow (v : V) :
    Continuous fun x : E → ℝ => N.inflow x v := by
  classical
  unfold inflow
  refine continuous_finsetSum Finset.univ ?_
  intro e _he
  by_cases h : N.head e = v
  · simpa [h] using (continuous_apply e : Continuous fun x : E → ℝ => x e)
  · simpa [h] using (continuous_const : Continuous fun _ : E → ℝ => (0 : ℝ))

theorem continuous_excess (v : V) :
    Continuous fun x : E → ℝ => N.excess x v := by
  unfold excess
  exact (N.continuous_outflow v).sub (N.continuous_inflow v)

/-- A feasible `s`-`t` flow in a finite directed network. -/
structure IsFlow (s t : V) (x : E → ℝ) : Prop where
  /-- Flow is nonnegative on every arc. -/
  nonneg : ∀ e, 0 ≤ x e
  /-- Flow is bounded by capacity on every arc. -/
  le_cap : ∀ e, x e ≤ N.cap e
  /-- Flow is conserved away from the source and sink. -/
  conserved : ∀ v, v ≠ s → v ≠ t → N.excess x v = 0

/-- Flow value, defined as net outflow from the source. -/
noncomputable def value (s : V) (x : E → ℝ) : ℝ :=
  N.excess x s

theorem continuous_value (s : V) :
    Continuous fun x : E → ℝ => N.value s x := by
  unfold value
  exact N.continuous_excess s

/-- A flow whose value is maximum among feasible `s`-`t` flows. -/
def IsMaximumFlow (s t : V) (x : E → ℝ) : Prop :=
  N.IsFlow s t x ∧
    ∀ y : E → ℝ, N.IsFlow s t y → N.value s y ≤ N.value s x

/-- The feasible set of `s`-`t` flows, as a subset of the finite-dimensional
coordinate space `E → ℝ`. -/
def feasibleSet (s t : V) : Set (E → ℝ) :=
  {x | N.IsFlow s t x}

/-- The zero assignment is a feasible flow. -/
theorem zero_isFlow (s t : V) :
    N.IsFlow s t (fun _ : E => (0 : ℝ)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e
    norm_num
  · intro e
    exact N.cap_nonneg e
  · intro v _hs _ht
    simp [excess, outflow, inflow]

theorem feasibleSet_nonempty (s t : V) :
    (N.feasibleSet s t).Nonempty :=
  ⟨fun _ => 0, N.zero_isFlow s t⟩

private theorem isClosed_conservationSet (s t : V) :
    IsClosed {x : E → ℝ | ∀ v : V, v ≠ s → v ≠ t → N.excess x v = 0} := by
  classical
  rw [show {x : E → ℝ | ∀ v : V, v ≠ s → v ≠ t → N.excess x v = 0} =
      ⋂ v : V, {x : E → ℝ | v ≠ s → v ≠ t → N.excess x v = 0} by
        ext x
        simp]
  refine isClosed_iInter ?_
  intro v
  by_cases hvs : v = s
  · simp [hvs]
  · by_cases hvt : v = t
    · simp [hvt]
    · simpa [hvs, hvt] using
        isClosed_eq (N.continuous_excess v) continuous_const

/-- The feasible set of finite real-valued flows is compact: it is the closed
conservation subspace inside the product of compact capacity intervals. -/
theorem isCompact_feasibleSet (s t : V) :
    IsCompact (N.feasibleSet s t) := by
  classical
  let lo : E → ℝ := fun _ => 0
  let box : Set (E → ℝ) := Set.Icc lo N.cap
  let cons : Set (E → ℝ) :=
    {x | ∀ v : V, v ≠ s → v ≠ t → N.excess x v = 0}
  have hEq : N.feasibleSet s t = box ∩ cons := by
    ext x
    constructor
    · intro hx
      exact ⟨⟨fun e => hx.nonneg e, fun e => hx.le_cap e⟩, hx.conserved⟩
    · intro hx
      rcases hx with ⟨hbox, hcons⟩
      exact ⟨fun e => hbox.1 e, fun e => hbox.2 e, hcons⟩
  rw [hEq]
  exact (isCompact_Icc : IsCompact box).inter_right
    (by simpa [cons] using N.isClosed_conservationSet s t)

/-- A maximum feasible flow exists in every finite directed network with
nonnegative real capacities. -/
theorem exists_maximumFlow (s t : V) :
    ∃ x : E → ℝ, N.IsMaximumFlow s t x := by
  classical
  rcases (N.isCompact_feasibleSet s t).exists_isMaxOn
      (N.feasibleSet_nonempty s t)
      ((N.continuous_value s).continuousOn) with
    ⟨x, hxmem, hxmax⟩
  refine ⟨x, hxmem, ?_⟩
  intro y hy
  exact hxmax hy

/-- Flow leaving a vertex set. -/
noncomputable def cutOut (S : Finset V) (x : E → ℝ) : ℝ :=
  ∑ e : E, if N.tail e ∈ S ∧ N.head e ∉ S then x e else 0

/-- Flow entering a vertex set. -/
noncomputable def cutIn (S : Finset V) (x : E → ℝ) : ℝ :=
  ∑ e : E, if N.tail e ∉ S ∧ N.head e ∈ S then x e else 0

/-- Capacity of the directed cut leaving a vertex set. -/
noncomputable def cutCapacity (S : Finset V) : ℝ :=
  N.cutOut S N.cap

/-- A directed `s`-`t` cut. -/
def IsSTCut (s t : V) (S : Finset V) : Prop :=
  s ∈ S ∧ t ∉ S

/-- A directed `s`-`t` cut of minimum capacity. -/
def IsMinimumCut (s t : V) (S : Finset V) : Prop :=
  IsSTCut s t S ∧
    ∀ T : Finset V, IsSTCut s t T → N.cutCapacity S ≤ N.cutCapacity T

/-! ## Residual reachability -/

/-- The residual adjacency relation of a flow-like arc assignment.  A forward
residual step uses unsaturated capacity; a backward residual step cancels a
positive amount of existing flow. -/
def ResidualAdj (x : E → ℝ) (u v : V) : Prop :=
  (∃ e : E, N.tail e = u ∧ N.head e = v ∧ x e < N.cap e) ∨
    (∃ e : E, N.head e = u ∧ N.tail e = v ∧ 0 < x e)

/-- A data-carrying residual step.  This is the proof-relevant version of
`ResidualAdj`, used by the augmentation construction. -/
inductive ResidualStep (x : E → ℝ) : V → V → Type (max u v)
  | fwd (e : E) (h : x e < N.cap e) :
      ResidualStep x (N.tail e) (N.head e)
  | bwd (e : E) (h : 0 < x e) :
      ResidualStep x (N.head e) (N.tail e)

namespace ResidualStep

variable {N}

/-- The original arc modified by a residual step. -/
def edge {x : E → ℝ} {u v : V} :
    N.ResidualStep x u v → E
  | fwd e _ => e
  | bwd e _ => e

/-- The signed change contributed by a unit augmentation along one residual
step to an original arc. -/
def signedInc [DecidableEq E] {x : E → ℝ} {u v : V}
    (a : N.ResidualStep x u v) (e : E) : ℝ :=
  match a with
  | fwd f _ => if f = e then 1 else 0
  | bwd f _ => if f = e then -1 else 0

omit [Fintype E] [DecidableEq V] in
/-- Residual-step data implies the propositional residual adjacency relation. -/
theorem residualAdj {x : E → ℝ} {u v : V}
    (a : N.ResidualStep x u v) :
    N.ResidualAdj x u v := by
  cases a with
  | fwd e h => exact Or.inl ⟨e, rfl, rfl, h⟩
  | bwd e h => exact Or.inr ⟨e, rfl, rfl, h⟩

omit [Fintype E] [DecidableEq V] in
/-- Any propositional residual adjacency has data-carrying residual-step
witnesses. -/
theorem nonempty_ofResidualAdj {x : E → ℝ} {u v : V}
    (h : N.ResidualAdj x u v) :
    Nonempty (N.ResidualStep x u v) := by
  classical
  rcases h with ⟨e, htail, hhead, hcap⟩ | ⟨e, hhead, htail, hpos⟩
  · subst htail
    subst hhead
    exact ⟨ResidualStep.fwd e hcap⟩
  · subst hhead
    subst htail
    exact ⟨ResidualStep.bwd e hpos⟩

/-- A chosen data-carrying residual step for a propositional residual
adjacency. -/
noncomputable def ofResidualAdj {x : E → ℝ} {u v : V}
    (h : N.ResidualAdj x u v) :
    N.ResidualStep x u v :=
  Classical.choice (nonempty_ofResidualAdj (N := N) h)

end ResidualStep

/-- The residual quiver whose arrows are data-carrying residual steps. -/
@[reducible]
def residualQuiver (x : E → ℝ) : Quiver V where
  Hom u v := N.ResidualStep x u v

omit [Fintype E] [DecidableEq V] in
/-- Propositional residual reachability can be upgraded to a proof-relevant
path in the residual quiver. -/
theorem nonempty_residualPath_of_reachable
    {x : E → ℝ} {s t : V}
    (h : Relation.ReflTransGen (N.ResidualAdj x) s t) :
    Nonempty (@Quiver.Path V (N.residualQuiver x) s t) := by
  letI : Quiver V := N.residualQuiver x
  change Nonempty (Quiver.Path s t)
  induction h with
  | refl =>
      exact ⟨Quiver.Path.nil⟩
  | tail h huv ih =>
      rcases ih with ⟨p⟩
      exact ⟨Quiver.Path.cons p (ResidualStep.ofResidualAdj (N := N) huv)⟩

/-- The signed incidence vector of a residual path, expressed on the original
arc set.  A forward residual step contributes `+1` to its original arc, and a
backward residual step contributes `-1`. -/
def residualPathSignedInc [DecidableEq E] {x : E → ℝ}
    {u v : V} (p : @Quiver.Path V (N.residualQuiver x) u v) : E → ℝ := by
  letI : Quiver V := N.residualQuiver x
  induction p with
  | nil =>
      exact fun _ => 0
  | cons p a ih =>
      exact fun e => ih e + ResidualStep.signedInc a e

/-- Augment an arc assignment by `ε` along a residual path. -/
def augmentAlongResidualPath [DecidableEq E]
    {x : E → ℝ} {u v : V}
    (ε : ℝ) (p : @Quiver.Path V (N.residualQuiver x) u v) :
    E → ℝ :=
  fun e => x e + ε * N.residualPathSignedInc p e

omit [Fintype E] [DecidableEq V] in
@[simp] theorem augmentAlongResidualPath_apply [DecidableEq E]
    {x : E → ℝ} {u v : V}
    (ε : ℝ) (p : @Quiver.Path V (N.residualQuiver x) u v) (e : E) :
    N.augmentAlongResidualPath ε p e =
      x e + ε * N.residualPathSignedInc p e :=
  rfl

/-! ### Incidence bookkeeping for residual-path augmentation -/

private theorem residualStep_signedInc_excess [DecidableEq E]
    {x : E → ℝ} {u v : V} (a : N.ResidualStep x u v) (w : V) :
    N.excess (ResidualStep.signedInc a) w =
      (if u = w then 1 else 0) - (if v = w then 1 else 0) := by
  classical
  cases a with
  | fwd e h =>
      simp only [ResidualStep.signedInc, excess, outflow, inflow]
      have hout :
          (∑ f : E, if N.tail f = N.tail e then
              (if e = f then (1 : ℝ) else 0) else 0) = 1 := by
        simpa using
          (Finset.sum_eq_single
            (s := (Finset.univ : Finset E))
            (f := fun f : E =>
              if N.tail f = N.tail e then (if e = f then (1 : ℝ) else 0) else 0)
            e
            (by
              intro f _hf hfe
              have hef : e ≠ f := fun h => hfe h.symm
              simp [hef])
            (by
              intro he
              exact False.elim (he (Finset.mem_univ e))))
      have hin :
          (∑ f : E, if N.head f = N.head e then
              (if e = f then (1 : ℝ) else 0) else 0) = 1 := by
        simpa using
          (Finset.sum_eq_single
            (s := (Finset.univ : Finset E))
            (f := fun f : E =>
              if N.head f = N.head e then (if e = f then (1 : ℝ) else 0) else 0)
            e
            (by
              intro f _hf hfe
              have hef : e ≠ f := fun h => hfe h.symm
              simp [hef])
            (by
              intro he
              exact False.elim (he (Finset.mem_univ e))))
      by_cases htw : N.tail e = w
      · by_cases hhw : N.head e = w
        · have houtw :
              (∑ f : E, if N.tail f = w then
                  (if e = f then (1 : ℝ) else 0) else 0) = 1 := by
            simpa [htw] using hout
          have hinw :
              (∑ f : E, if N.head f = w then
                  (if e = f then (1 : ℝ) else 0) else 0) = 1 := by
            simpa [hhw] using hin
          simp [htw, hhw, houtw, hinw]
        · have houtw :
              (∑ f : E, if N.tail f = w then
                  (if e = f then (1 : ℝ) else 0) else 0) = 1 := by
            simpa [htw] using hout
          have hinw :
              (∑ f : E, if N.head f = w then
                  (if e = f then (1 : ℝ) else 0) else 0) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro f _hf
            by_cases hef : e = f
            · subst hef
              simp [hhw]
            · simp [hef]
          simp [htw, hhw, houtw, hinw]
      · by_cases hhw : N.head e = w
        · have houtw :
              (∑ f : E, if N.tail f = w then
                  (if e = f then (1 : ℝ) else 0) else 0) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro f _hf
            by_cases hef : e = f
            · subst hef
              simp [htw]
            · simp [hef]
          have hinw :
              (∑ f : E, if N.head f = w then
                  (if e = f then (1 : ℝ) else 0) else 0) = 1 := by
            simpa [hhw] using hin
          simp [htw, hhw, houtw, hinw]
        · have houtw :
              (∑ f : E, if N.tail f = w then
                  (if e = f then (1 : ℝ) else 0) else 0) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro f _hf
            by_cases hef : e = f
            · subst hef
              simp [htw]
            · simp [hef]
          have hinw :
              (∑ f : E, if N.head f = w then
                  (if e = f then (1 : ℝ) else 0) else 0) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro f _hf
            by_cases hef : e = f
            · subst hef
              simp [hhw]
            · simp [hef]
          simp [htw, hhw, houtw, hinw]
  | bwd e h =>
      simp only [ResidualStep.signedInc, excess, outflow, inflow]
      have hout :
          (∑ f : E, if N.tail f = N.tail e then
              (if e = f then (-1 : ℝ) else 0) else 0) = -1 := by
        simpa using
          (Finset.sum_eq_single
            (s := (Finset.univ : Finset E))
            (f := fun f : E =>
              if N.tail f = N.tail e then (if e = f then (-1 : ℝ) else 0) else 0)
            e
            (by
              intro f _hf hfe
              have hef : e ≠ f := fun h => hfe h.symm
              simp [hef])
            (by
              intro he
              exact False.elim (he (Finset.mem_univ e))))
      have hin :
          (∑ f : E, if N.head f = N.head e then
              (if e = f then (-1 : ℝ) else 0) else 0) = -1 := by
        simpa using
          (Finset.sum_eq_single
            (s := (Finset.univ : Finset E))
            (f := fun f : E =>
              if N.head f = N.head e then (if e = f then (-1 : ℝ) else 0) else 0)
            e
            (by
              intro f _hf hfe
              have hef : e ≠ f := fun h => hfe h.symm
              simp [hef])
            (by
              intro he
              exact False.elim (he (Finset.mem_univ e))))
      by_cases hhw : N.head e = w
      · by_cases htw : N.tail e = w
        · have houtw :
              (∑ f : E, if N.tail f = w then
                  (if e = f then (-1 : ℝ) else 0) else 0) = -1 := by
            simpa [htw] using hout
          have hinw :
              (∑ f : E, if N.head f = w then
                  (if e = f then (-1 : ℝ) else 0) else 0) = -1 := by
            simpa [hhw] using hin
          simp [hhw, htw, houtw, hinw]
        · have houtw :
              (∑ f : E, if N.tail f = w then
                  (if e = f then (-1 : ℝ) else 0) else 0) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro f _hf
            by_cases hef : e = f
            · subst hef
              simp [htw]
            · simp [hef]
          have hinw :
              (∑ f : E, if N.head f = w then
                  (if e = f then (-1 : ℝ) else 0) else 0) = -1 := by
            simpa [hhw] using hin
          simp [hhw, htw, houtw, hinw]
      · by_cases htw : N.tail e = w
        · have houtw :
              (∑ f : E, if N.tail f = w then
                  (if e = f then (-1 : ℝ) else 0) else 0) = -1 := by
            simpa [htw] using hout
          have hinw :
              (∑ f : E, if N.head f = w then
                  (if e = f then (-1 : ℝ) else 0) else 0) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro f _hf
            by_cases hef : e = f
            · subst hef
              simp [hhw]
            · simp [hef]
          simp [hhw, htw, houtw, hinw]
        · have houtw :
              (∑ f : E, if N.tail f = w then
                  (if e = f then (-1 : ℝ) else 0) else 0) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro f _hf
            by_cases hef : e = f
            · subst hef
              simp [htw]
            · simp [hef]
          have hinw :
              (∑ f : E, if N.head f = w then
                  (if e = f then (-1 : ℝ) else 0) else 0) = 0 := by
            refine Finset.sum_eq_zero ?_
            intro f _hf
            by_cases hef : e = f
            · subst hef
              simp [hhw]
            · simp [hef]
          simp [hhw, htw, houtw, hinw]

private theorem excess_add (x y : E → ℝ) (w : V) :
    N.excess (fun e => x e + y e) w = N.excess x w + N.excess y w := by
  classical
  simp only [excess, outflow, inflow]
  have hout :
      (∑ e : E, if N.tail e = w then x e + y e else 0) =
        (∑ e : E, if N.tail e = w then x e else 0) +
          (∑ e : E, if N.tail e = w then y e else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro e _he
    by_cases h : N.tail e = w <;> simp [h]
  have hin :
      (∑ e : E, if N.head e = w then x e + y e else 0) =
        (∑ e : E, if N.head e = w then x e else 0) +
          (∑ e : E, if N.head e = w then y e else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro e _he
    by_cases h : N.head e = w <;> simp [h]
  rw [hout, hin]
  ring

private theorem excess_smul (c : ℝ) (x : E → ℝ) (w : V) :
    N.excess (fun e => c * x e) w = c * N.excess x w := by
  classical
  simp only [excess, outflow, inflow]
  have hout :
      (∑ e : E, if N.tail e = w then c * x e else 0) =
        c * (∑ e : E, if N.tail e = w then x e else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro e _he
    by_cases h : N.tail e = w <;> simp [h]
  have hin :
      (∑ e : E, if N.head e = w then c * x e else 0) =
        c * (∑ e : E, if N.head e = w then x e else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro e _he
    by_cases h : N.head e = w <;> simp [h]
  rw [hout, hin]
  ring

private theorem residualPathSignedInc_excess [DecidableEq E]
    {x : E → ℝ} {u v : V}
    (p : @Quiver.Path V (N.residualQuiver x) u v) (w : V) :
    N.excess (N.residualPathSignedInc p) w =
      (if u = w then 1 else 0) - (if v = w then 1 else 0) := by
  classical
  letI : Quiver V := N.residualQuiver x
  induction p with
  | nil =>
      simp [residualPathSignedInc, excess, outflow, inflow]
  | cons p a ih =>
      rw [show N.residualPathSignedInc (Quiver.Path.cons p a) =
          fun e => N.residualPathSignedInc p e + ResidualStep.signedInc a e by rfl]
      rw [N.excess_add, ih, residualStep_signedInc_excess (N := N) a w]
      ring

theorem augmentAlongResidualPath_excess [DecidableEq E]
    {x : E → ℝ} {u v : V}
    (ε : ℝ) (p : @Quiver.Path V (N.residualQuiver x) u v) (w : V) :
    N.excess (N.augmentAlongResidualPath ε p) w =
      N.excess x w + ε * ((if u = w then 1 else 0) - (if v = w then 1 else 0)) := by
  classical
  rw [show N.augmentAlongResidualPath ε p =
      fun e => x e + (ε * N.residualPathSignedInc p e) by rfl]
  rw [N.excess_add, N.excess_smul, N.residualPathSignedInc_excess p w]

/-- If an augmentation along a residual source-sink path remains inside the
capacity box, then it is again a feasible flow.  The residual incidence
identity supplies conservation at every non-endpoint vertex. -/
theorem augmentAlongResidualPath_isFlow_of_bounds [DecidableEq E]
    {s t : V} {x : E → ℝ} (hflow : N.IsFlow s t x)
    (ε : ℝ) (p : @Quiver.Path V (N.residualQuiver x) s t)
    (hnonneg : ∀ e, 0 ≤ N.augmentAlongResidualPath ε p e)
    (hle_cap : ∀ e, N.augmentAlongResidualPath ε p e ≤ N.cap e) :
    N.IsFlow s t (N.augmentAlongResidualPath ε p) := by
  classical
  refine ⟨hnonneg, hle_cap, ?_⟩
  intro v hvs hvt
  rw [N.augmentAlongResidualPath_excess ε p v, hflow.conserved v hvs hvt]
  simp [hvs.symm, hvt.symm]

/-- The value increases by `ε` when augmenting along a residual `s`-`t` path,
provided `s ≠ t`. -/
theorem value_augmentAlongResidualPath [DecidableEq E]
    {s t : V} (hst : s ≠ t) {x : E → ℝ}
    (ε : ℝ) (p : @Quiver.Path V (N.residualQuiver x) s t) :
    N.value s (N.augmentAlongResidualPath ε p) = N.value s x + ε := by
  classical
  rw [value, N.augmentAlongResidualPath_excess ε p s, value]
  simp [hst.symm]

/-- Any positive feasible augmentation along a residual source-sink path
contradicts maximality. -/
theorem not_isMaximumFlow_of_feasible_residual_augmentation [DecidableEq E]
    {s t : V} (hst : s ≠ t) {x : E → ℝ} (hflow : N.IsFlow s t x)
    {ε : ℝ} (hε : 0 < ε)
    (p : @Quiver.Path V (N.residualQuiver x) s t)
    (hnonneg : ∀ e, 0 ≤ N.augmentAlongResidualPath ε p e)
    (hle_cap : ∀ e, N.augmentAlongResidualPath ε p e ≤ N.cap e) :
    ¬ N.IsMaximumFlow s t x := by
  intro hmax
  let y := N.augmentAlongResidualPath ε p
  have hyflow : N.IsFlow s t y :=
    N.augmentAlongResidualPath_isFlow_of_bounds hflow ε p hnonneg hle_cap
  have hy_le := hmax.2 y hyflow
  have hy_val : N.value s y = N.value s x + ε :=
    N.value_augmentAlongResidualPath hst ε p
  linarith

/-- Length of a residual path, exposed without relying on a local quiver
typeclass instance at use sites. -/
def residualPathLength {x : E → ℝ} {u v : V}
    (p : @Quiver.Path V (N.residualQuiver x) u v) : ℕ :=
  @Quiver.Path.length V (N.residualQuiver x) u v p

/-- Number of forward residual uses of an original arc along a residual path. -/
def residualPathForwardCount [DecidableEq E] {x : E → ℝ}
    {u v : V} (p : @Quiver.Path V (N.residualQuiver x) u v) (e : E) : ℕ := by
  letI : Quiver V := N.residualQuiver x
  induction p with
  | nil =>
      exact 0
  | cons p a ih =>
      exact ih +
        match a with
        | ResidualStep.fwd f _ => if f = e then 1 else 0
        | ResidualStep.bwd _ _ => 0

/-- Number of backward residual uses of an original arc along a residual path. -/
def residualPathBackwardCount [DecidableEq E] {x : E → ℝ}
    {u v : V} (p : @Quiver.Path V (N.residualQuiver x) u v) (e : E) : ℕ := by
  letI : Quiver V := N.residualQuiver x
  induction p with
  | nil =>
      exact 0
  | cons p a ih =>
      exact ih +
        match a with
        | ResidualStep.fwd _ _ => 0
        | ResidualStep.bwd f _ => if f = e then 1 else 0

omit [Fintype E] [DecidableEq V] in
theorem residualPathSignedInc_eq_counts [DecidableEq E]
    {x : E → ℝ} {u v : V}
    (p : @Quiver.Path V (N.residualQuiver x) u v) (e : E) :
    N.residualPathSignedInc p e =
      (N.residualPathForwardCount p e : ℝ) -
        (N.residualPathBackwardCount p e : ℝ) := by
  classical
  letI : Quiver V := N.residualQuiver x
  induction p with
  | nil =>
      simp [residualPathSignedInc, residualPathForwardCount,
        residualPathBackwardCount]
  | cons p a ih =>
      cases a with
      | fwd f hf =>
          rw [show N.residualPathSignedInc
              (Quiver.Path.cons p (ResidualStep.fwd f hf)) e =
                N.residualPathSignedInc p e +
                  ResidualStep.signedInc (ResidualStep.fwd f hf) e by rfl]
          rw [show N.residualPathForwardCount
              (Quiver.Path.cons p (ResidualStep.fwd f hf)) e =
                N.residualPathForwardCount p e + (if f = e then 1 else 0) by rfl]
          rw [show N.residualPathBackwardCount
              (Quiver.Path.cons p (ResidualStep.fwd f hf)) e =
                N.residualPathBackwardCount p e + 0 by rfl]
          rw [ih]
          by_cases hfe : f = e
          · simp [ResidualStep.signedInc, hfe]
            ring
          · simp [ResidualStep.signedInc, hfe]
      | bwd f hf =>
          rw [show N.residualPathSignedInc
              (Quiver.Path.cons p (ResidualStep.bwd f hf)) e =
                N.residualPathSignedInc p e +
                  ResidualStep.signedInc (ResidualStep.bwd f hf) e by rfl]
          rw [show N.residualPathForwardCount
              (Quiver.Path.cons p (ResidualStep.bwd f hf)) e =
                N.residualPathForwardCount p e + 0 by rfl]
          rw [show N.residualPathBackwardCount
              (Quiver.Path.cons p (ResidualStep.bwd f hf)) e =
                N.residualPathBackwardCount p e + (if f = e then 1 else 0) by rfl]
          rw [ih]
          by_cases hfe : f = e
          · simp [ResidualStep.signedInc, hfe]
            ring
          · simp [ResidualStep.signedInc, hfe]

omit [Fintype E] [DecidableEq V] in
theorem residualPathForwardCount_le_length [DecidableEq E]
    {x : E → ℝ} {u v : V}
    (p : @Quiver.Path V (N.residualQuiver x) u v) (e : E) :
    N.residualPathForwardCount p e ≤ N.residualPathLength p := by
  classical
  letI : Quiver V := N.residualQuiver x
  induction p with
  | nil =>
      simp [residualPathForwardCount]
  | cons p a ih =>
      cases a with
      | fwd f hf =>
          by_cases hfe : f = e
          · simpa [residualPathForwardCount, residualPathLength, hfe]
              using Nat.add_le_add_right ih 1
          · exact (by
              have hle : N.residualPathForwardCount p e ≤
                  N.residualPathLength p + 1 := ih.trans (Nat.le_succ _)
              simpa [residualPathForwardCount, residualPathLength, hfe] using hle)
      | bwd f hf =>
          exact (by
            have hle : N.residualPathForwardCount p e ≤
                N.residualPathLength p + 1 := ih.trans (Nat.le_succ _)
            simpa [residualPathForwardCount, residualPathLength] using hle)

omit [Fintype E] [DecidableEq V] in
theorem residualPathBackwardCount_le_length [DecidableEq E]
    {x : E → ℝ} {u v : V}
    (p : @Quiver.Path V (N.residualQuiver x) u v) (e : E) :
    N.residualPathBackwardCount p e ≤ N.residualPathLength p := by
  classical
  letI : Quiver V := N.residualQuiver x
  induction p with
  | nil =>
      simp [residualPathBackwardCount]
  | cons p a ih =>
      cases a with
      | fwd f hf =>
          exact (by
            have hle : N.residualPathBackwardCount p e ≤
                N.residualPathLength p + 1 := ih.trans (Nat.le_succ _)
            simpa [residualPathBackwardCount, residualPathLength] using hle)
      | bwd f hf =>
          by_cases hfe : f = e
          · simpa [residualPathBackwardCount, residualPathLength, hfe]
              using Nat.add_le_add_right ih 1
          · exact (by
              have hle : N.residualPathBackwardCount p e ≤
                  N.residualPathLength p + 1 := ih.trans (Nat.le_succ _)
              simpa [residualPathBackwardCount, residualPathLength, hfe] using hle)

omit [Fintype E] [DecidableEq V] in
theorem residualPathSignedInc_le_length [DecidableEq E]
    {x : E → ℝ} {u v : V}
    (p : @Quiver.Path V (N.residualQuiver x) u v) (e : E) :
    N.residualPathSignedInc p e ≤ (N.residualPathLength p : ℝ) := by
  classical
  rw [N.residualPathSignedInc_eq_counts p e]
  have hf : (N.residualPathForwardCount p e : ℝ) ≤
      (N.residualPathLength p : ℝ) := by
    exact_mod_cast N.residualPathForwardCount_le_length p e
  have hb : 0 ≤ (N.residualPathBackwardCount p e : ℝ) := by positivity
  linarith

omit [Fintype E] [DecidableEq V] in
theorem neg_residualPathSignedInc_le_length [DecidableEq E]
    {x : E → ℝ} {u v : V}
    (p : @Quiver.Path V (N.residualQuiver x) u v) (e : E) :
    -N.residualPathSignedInc p e ≤ (N.residualPathLength p : ℝ) := by
  classical
  rw [N.residualPathSignedInc_eq_counts p e]
  have hb : (N.residualPathBackwardCount p e : ℝ) ≤
      (N.residualPathLength p : ℝ) := by
    exact_mod_cast N.residualPathBackwardCount_le_length p e
  have hf : 0 ≤ (N.residualPathForwardCount p e : ℝ) := by positivity
  linarith

omit [Fintype E] [DecidableEq V] in
private theorem residualPathForwardCount_pos_of_signedInc_pos [DecidableEq E]
    {x : E → ℝ} {u v : V}
    {p : @Quiver.Path V (N.residualQuiver x) u v} {e : E}
    (h : 0 < N.residualPathSignedInc p e) :
    0 < N.residualPathForwardCount p e := by
  classical
  rw [N.residualPathSignedInc_eq_counts p e] at h
  by_contra hnot
  have hf : N.residualPathForwardCount p e = 0 := Nat.eq_zero_of_not_pos hnot
  have hb : 0 ≤ (N.residualPathBackwardCount p e : ℝ) := by positivity
  rw [hf] at h
  norm_num at h
  linarith

omit [Fintype E] [DecidableEq V] in
private theorem residualPathBackwardCount_pos_of_signedInc_neg [DecidableEq E]
    {x : E → ℝ} {u v : V}
    {p : @Quiver.Path V (N.residualQuiver x) u v} {e : E}
    (h : N.residualPathSignedInc p e < 0) :
    0 < N.residualPathBackwardCount p e := by
  classical
  rw [N.residualPathSignedInc_eq_counts p e] at h
  by_contra hnot
  have hb : N.residualPathBackwardCount p e = 0 := Nat.eq_zero_of_not_pos hnot
  have hf : 0 ≤ (N.residualPathForwardCount p e : ℝ) := by positivity
  rw [hb] at h
  norm_num at h
  linarith

omit [Fintype E] [DecidableEq V] in
private theorem residualPathForwardCount_pos_implies_slack [DecidableEq E]
    {x : E → ℝ} {u v : V}
    (p : @Quiver.Path V (N.residualQuiver x) u v) {e : E}
    (h : 0 < N.residualPathForwardCount p e) :
    x e < N.cap e := by
  classical
  letI : Quiver V := N.residualQuiver x
  induction p with
  | nil =>
      simp [residualPathForwardCount] at h
  | cons p a ih =>
      cases a with
      | fwd f hf =>
          by_cases hfe : f = e
          · simpa [hfe] using hf
          · have hp : 0 < N.residualPathForwardCount p e := by
              simpa [residualPathForwardCount, hfe] using h
            exact ih hp
      | bwd f hf =>
          have hp : 0 < N.residualPathForwardCount p e := by
            simpa [residualPathForwardCount] using h
          exact ih hp

omit [Fintype E] [DecidableEq V] in
private theorem residualPathBackwardCount_pos_implies_positive [DecidableEq E]
    {x : E → ℝ} {u v : V}
    (p : @Quiver.Path V (N.residualQuiver x) u v) {e : E}
    (h : 0 < N.residualPathBackwardCount p e) :
    0 < x e := by
  classical
  letI : Quiver V := N.residualQuiver x
  induction p with
  | nil =>
      simp [residualPathBackwardCount] at h
  | cons p a ih =>
      cases a with
      | fwd f hf =>
          have hp : 0 < N.residualPathBackwardCount p e := by
            simpa [residualPathBackwardCount] using h
          exact ih hp
      | bwd f hf =>
          by_cases hfe : f = e
          · simpa [hfe] using hf
          · have hp : 0 < N.residualPathBackwardCount p e := by
              simpa [residualPathBackwardCount, hfe] using h
            exact ih hp

/-- Per-edge upper bound on an augmentation parameter.  If the signed
incidence is positive, the bound is the remaining capacity divided by a
uniform path-length denominator; if it is negative, it is the existing flow
divided by the same denominator; if zero, the edge imposes no restriction. -/
noncomputable def residualAugmentBound [DecidableEq E]
    {x : E → ℝ} {u v : V}
    (p : @Quiver.Path V (N.residualQuiver x) u v) (e : E) : ℝ :=
  let d := N.residualPathSignedInc p e
  if 0 < d then (N.cap e - x e) / ((N.residualPathLength p + 1 : ℕ) : ℝ)
  else if d < 0 then x e / ((N.residualPathLength p + 1 : ℕ) : ℝ)
  else 1

omit [Fintype E] [DecidableEq V] in
private theorem residualAugmentBound_pos [DecidableEq E]
    {x : E → ℝ} {u v : V}
    (p : @Quiver.Path V (N.residualQuiver x) u v) (e : E) :
    0 < N.residualAugmentBound p e := by
  classical
  have hden : (0 : ℝ) < (N.residualPathLength p : ℝ) + 1 := by positivity
  unfold residualAugmentBound
  by_cases hpos : 0 < N.residualPathSignedInc p e
  · have hfpos : 0 < N.residualPathForwardCount p e :=
      residualPathForwardCount_pos_of_signedInc_pos (N := N) hpos
    have hslack : 0 < N.cap e - x e := by
      have hlt := N.residualPathForwardCount_pos_implies_slack p hfpos
      linarith
    simpa [hpos] using div_pos hslack hden
  · by_cases hneg : N.residualPathSignedInc p e < 0
    · have hbpos : 0 < N.residualPathBackwardCount p e :=
        residualPathBackwardCount_pos_of_signedInc_neg (N := N) hneg
      have hxpos : 0 < x e :=
        N.residualPathBackwardCount_pos_implies_positive p hbpos
      simpa [hpos, hneg] using div_pos hxpos hden
    · simp [hpos, hneg]

omit [DecidableEq V] in
private theorem exists_positive_le_residualAugmentBound [DecidableEq E]
    {x : E → ℝ} {u v : V}
    (p : @Quiver.Path V (N.residualQuiver x) u v) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ e : E, ε ≤ N.residualAugmentBound p e := by
  classical
  by_cases hE : (Finset.univ : Finset E).Nonempty
  · let ε : ℝ := (Finset.univ : Finset E).inf' hE
      (fun e => N.residualAugmentBound p e)
    have hεpos : 0 < ε := by
      rw [Finset.lt_inf'_iff]
      intro e _he
      exact N.residualAugmentBound_pos p e
    refine ⟨ε, hεpos, ?_⟩
    intro e
    exact Finset.inf'_le _ (Finset.mem_univ e)
  · refine ⟨1, by norm_num, ?_⟩
    intro e
    exact False.elim (hE ⟨e, Finset.mem_univ e⟩)

/-- Every residual source-sink path admits a positive augmentation parameter
that keeps all arc values inside their capacity intervals. -/
theorem exists_feasible_residual_augmentation [DecidableEq E]
    {s t : V} {x : E → ℝ} (hflow : N.IsFlow s t x)
    (p : @Quiver.Path V (N.residualQuiver x) s t) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ e, 0 ≤ N.augmentAlongResidualPath ε p e) ∧
        (∀ e, N.augmentAlongResidualPath ε p e ≤ N.cap e) := by
  classical
  rcases N.exists_positive_le_residualAugmentBound p with ⟨ε, hεpos, hεle⟩
  have hεnonneg : 0 ≤ ε := le_of_lt hεpos
  refine ⟨ε, hεpos, ?_, ?_⟩
  · intro e
    dsimp [augmentAlongResidualPath]
    let d := N.residualPathSignedInc p e
    have hLpos : (0 : ℝ) < (N.residualPathLength p : ℝ) + 1 := by positivity
    by_cases hneg : d < 0
    · have hnpos : ¬ 0 < d := by linarith
      have hneg' : N.residualPathSignedInc p e < 0 := by simpa [d] using hneg
      have hnpos' : ¬ 0 < N.residualPathSignedInc p e := by simpa [d] using hnpos
      have hεe := hεle e
      unfold residualAugmentBound at hεe
      simp [hnpos', hneg'] at hεe
      have hnegd_nonneg : 0 ≤ -d := by linarith
      have hnegd_le :
          -d ≤ (N.residualPathLength p : ℝ) + 1 := by
        have hle := N.neg_residualPathSignedInc_le_length p e
        dsimp [d]
        linarith
      have hx_nonneg : 0 ≤ x e := hflow.nonneg e
      have hdiv_nonneg : 0 ≤ x e / ((N.residualPathLength p : ℝ) + 1) :=
        div_nonneg hx_nonneg (le_of_lt hLpos)
      have hmul₁ :
          ε * (-d) ≤ (x e / ((N.residualPathLength p : ℝ) + 1)) * (-d) :=
        mul_le_mul_of_nonneg_right hεe hnegd_nonneg
      have hmul₂ :
          (x e / ((N.residualPathLength p : ℝ) + 1)) * (-d) ≤ x e := by
        have htmp :=
          mul_le_mul_of_nonneg_left hnegd_le hdiv_nonneg
        have hcancel :
            (x e / ((N.residualPathLength p : ℝ) + 1)) *
                ((N.residualPathLength p : ℝ) + 1) = x e := by
          field_simp [hLpos.ne']
        simpa [hcancel] using htmp
      have hmul : ε * (-d) ≤ x e := hmul₁.trans hmul₂
      have hrewrite : x e + ε * d = x e - ε * (-d) := by ring
      rw [hrewrite]
      linarith
    · have hd_nonneg : 0 ≤ d := le_of_not_gt hneg
      have hmul_nonneg : 0 ≤ ε * d := mul_nonneg hεnonneg hd_nonneg
      have hx_nonneg : 0 ≤ x e := hflow.nonneg e
      nlinarith
  · intro e
    dsimp [augmentAlongResidualPath]
    let d := N.residualPathSignedInc p e
    have hLpos : (0 : ℝ) < (N.residualPathLength p : ℝ) + 1 := by positivity
    by_cases hpos : 0 < d
    · have hpos' : 0 < N.residualPathSignedInc p e := by simpa [d] using hpos
      have hεe := hεle e
      unfold residualAugmentBound at hεe
      simp [hpos'] at hεe
      have hd_nonneg : 0 ≤ d := le_of_lt hpos
      have hd_le :
          d ≤ (N.residualPathLength p : ℝ) + 1 := by
        have hle := N.residualPathSignedInc_le_length p e
        dsimp [d]
        linarith
      have hslack_nonneg : 0 ≤ N.cap e - x e := by
        have hle := hflow.le_cap e
        linarith
      have hdiv_nonneg :
          0 ≤ (N.cap e - x e) / ((N.residualPathLength p : ℝ) + 1) :=
        div_nonneg hslack_nonneg (le_of_lt hLpos)
      have hmul₁ :
          ε * d ≤
            ((N.cap e - x e) / ((N.residualPathLength p : ℝ) + 1)) * d :=
        mul_le_mul_of_nonneg_right hεe hd_nonneg
      have hmul₂ :
          ((N.cap e - x e) / ((N.residualPathLength p : ℝ) + 1)) * d ≤
            N.cap e - x e := by
        have htmp := mul_le_mul_of_nonneg_left hd_le hdiv_nonneg
        have hcancel :
            ((N.cap e - x e) / ((N.residualPathLength p : ℝ) + 1)) *
                ((N.residualPathLength p : ℝ) + 1) = N.cap e - x e := by
          field_simp [hLpos.ne']
        simpa [hcancel] using htmp
      have hmul : ε * d ≤ N.cap e - x e := hmul₁.trans hmul₂
      linarith
    · have hd_nonpos : d ≤ 0 := le_of_not_gt hpos
      have hmul_nonpos : ε * d ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hεnonneg hd_nonpos
      have hle := hflow.le_cap e
      linarith

/-- A residual path out of a feasible flow gives a strictly better feasible
flow. -/
theorem exists_flow_value_gt_of_residualPath [DecidableEq E]
    {s t : V} (hst : s ≠ t) {x : E → ℝ} (hflow : N.IsFlow s t x)
    (p : @Quiver.Path V (N.residualQuiver x) s t) :
    ∃ y : E → ℝ, N.IsFlow s t y ∧ N.value s x < N.value s y := by
  rcases N.exists_feasible_residual_augmentation hflow p with
    ⟨ε, hεpos, hnonneg, hle_cap⟩
  let y := N.augmentAlongResidualPath ε p
  have hyflow : N.IsFlow s t y :=
    N.augmentAlongResidualPath_isFlow_of_bounds hflow ε p hnonneg hle_cap
  have hval : N.value s y = N.value s x + ε :=
    N.value_augmentAlongResidualPath hst ε p
  refine ⟨y, hyflow, ?_⟩
  linarith

/-- Maximum flows have no residual path from source to sink. -/
theorem no_residual_path_of_isMaximumFlow [DecidableEq E]
    {s t : V} (hst : s ≠ t) {x : E → ℝ}
    (hmax : N.IsMaximumFlow s t x) :
    ¬ Relation.ReflTransGen (N.ResidualAdj x) s t := by
  intro hreach
  rcases N.nonempty_residualPath_of_reachable hreach with ⟨p⟩
  rcases N.exists_flow_value_gt_of_residualPath hst hmax.1 p with
    ⟨y, hyflow, hygt⟩
  have hle := hmax.2 y hyflow
  linarith

/-- Vertices reachable from `s` in the residual relation. -/
noncomputable def residualReachableSet [Fintype V] (s : V) (x : E → ℝ) :
    Finset V := by
  classical
  exact Finset.univ.filter fun v =>
    Relation.ReflTransGen (N.ResidualAdj x) s v

omit [Fintype E] [DecidableEq V] in
theorem mem_residualReachableSet_iff [Fintype V]
    (s : V) (x : E → ℝ) (v : V) :
    v ∈ N.residualReachableSet s x ↔
      Relation.ReflTransGen (N.ResidualAdj x) s v := by
  classical
  simp [residualReachableSet]

omit [Fintype E] [DecidableEq V] in
/-- The source is residual-reachable from itself. -/
theorem source_mem_residualReachableSet [Fintype V]
    (s : V) (x : E → ℝ) :
    s ∈ N.residualReachableSet s x := by
  rw [N.mem_residualReachableSet_iff]

omit [Fintype E] [DecidableEq V] in
/-- Residual reachability is closed under one residual step. -/
theorem residualReachableSet_closed [Fintype V]
    {s u v : V} {x : E → ℝ}
    (hu : u ∈ N.residualReachableSet s x)
    (huv : N.ResidualAdj x u v) :
    v ∈ N.residualReachableSet s x := by
  rw [N.mem_residualReachableSet_iff] at hu ⊢
  exact Relation.ReflTransGen.tail hu huv

omit [Fintype E] [DecidableEq V] in
/-- If the sink is not residual-reachable, the residual reachable set is an
`s`-`t` cut. -/
theorem sink_notMem_residualReachableSet_of_not_reachable [Fintype V]
    {s t : V} {x : E → ℝ}
    (hno : ¬ Relation.ReflTransGen (N.ResidualAdj x) s t) :
    t ∉ N.residualReachableSet s x := by
  rw [N.mem_residualReachableSet_iff]
  exact hno

private theorem edge_contribution_sum_sub
    (S : Finset V) (a b : V) (r : ℝ) :
    S.sum (fun v => (if a = v then r else 0) - (if b = v then r else 0)) =
      (if a ∈ S then r else 0) - (if b ∈ S then r else 0) := by
  classical
  rw [Finset.sum_sub_distrib]
  congr 1
  · by_cases ha : a ∈ S
    · have hmain : S.sum (fun v => if a = v then r else 0) = r := by
        have hsingle :
            S.sum (fun v => (if a = v then r else 0 : ℝ)) =
              (if a = a then r else 0) := by
          refine Finset.sum_eq_single (s := S)
            (f := fun v => (if a = v then r else 0 : ℝ)) a ?_ ?_
          · intro v hv hne
            simp [hne.symm]
          · intro hnot
            exact False.elim (hnot ha)
        simpa using hsingle
      rw [hmain]
      simp [ha]
    · have hzero : S.sum (fun v => if a = v then r else 0) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro v hv
        have hne : a ≠ v := by
          intro h
          exact ha (by simpa [h] using hv)
        simp [hne]
      rw [hzero]
      simp [ha]
  · by_cases hb : b ∈ S
    · have hmain : S.sum (fun v => if b = v then r else 0) = r := by
        have hsingle :
            S.sum (fun v => (if b = v then r else 0 : ℝ)) =
              (if b = b then r else 0) := by
          refine Finset.sum_eq_single (s := S)
            (f := fun v => (if b = v then r else 0 : ℝ)) b ?_ ?_
          · intro v hv hne
            simp [hne.symm]
          · intro hnot
            exact False.elim (hnot hb)
        simpa using hsingle
      rw [hmain]
      simp [hb]
    · have hzero : S.sum (fun v => if b = v then r else 0) = 0 := by
        refine Finset.sum_eq_zero ?_
        intro v hv
        have hne : b ≠ v := by
          intro h
          exact hb (by simpa [h] using hv)
        simp [hne]
      rw [hzero]
      simp [hb]

private theorem edge_contribution_cut_cases
    (S : Finset V) (a b : V) (r : ℝ) :
    (if a ∈ S then r else 0) - (if b ∈ S then r else 0) =
      (if a ∈ S ∧ b ∉ S then r else 0) -
        (if a ∉ S ∧ b ∈ S then r else 0) := by
  by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;> simp [ha, hb]

/-- Sum of signed excess over a vertex set equals net flow across its boundary. -/
theorem sum_excess_eq_cutOut_sub_cutIn (S : Finset V) (x : E → ℝ) :
    S.sum (fun v => N.excess x v) = N.cutOut S x - N.cutIn S x := by
  classical
  simp only [excess, outflow, inflow, cutOut, cutIn]
  calc
    S.sum (fun v =>
        (∑ e : E, if N.tail e = v then x e else 0) -
          (∑ e : E, if N.head e = v then x e else 0))
        =
          (∑ e : E, ∑ v ∈ S, if N.tail e = v then x e else 0) -
            (∑ e : E, ∑ v ∈ S, if N.head e = v then x e else 0) := by
            rw [Finset.sum_sub_distrib]
            congr 1
            · rw [Finset.sum_comm]
            · rw [Finset.sum_comm]
    _ =
          ∑ e : E,
            ((∑ v ∈ S, if N.tail e = v then x e else 0) -
              (∑ v ∈ S, if N.head e = v then x e else 0)) := by
            rw [Finset.sum_sub_distrib]
    _ =
          ∑ e : E,
            ((if N.tail e ∈ S then x e else 0) -
              (if N.head e ∈ S then x e else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro e _he
            have h := edge_contribution_sum_sub S (N.tail e) (N.head e) (x e)
            rw [← h]
            rw [Finset.sum_sub_distrib]
    _ =
          ∑ e : E,
            ((if N.tail e ∈ S ∧ N.head e ∉ S then x e else 0) -
              (if N.tail e ∉ S ∧ N.head e ∈ S then x e else 0)) := by
            refine Finset.sum_congr rfl ?_
            intro e _he
            exact edge_contribution_cut_cases S (N.tail e) (N.head e) (x e)
    _ =
          (∑ e : E, if N.tail e ∈ S ∧ N.head e ∉ S then x e else 0) -
            (∑ e : E, if N.tail e ∉ S ∧ N.head e ∈ S then x e else 0) := by
            rw [Finset.sum_sub_distrib]

/-- Net-flow identity across an `s`-`t` cut. -/
theorem value_eq_cutOut_sub_cutIn_of_cut
    {s t : V} {x : E → ℝ} (hflow : N.IsFlow s t x)
    {S : Finset V} (hs : s ∈ S) (ht : t ∉ S) :
    N.value s x = N.cutOut S x - N.cutIn S x := by
  classical
  have hsum :
      S.sum (fun v => N.excess x v) = N.excess x s := by
    refine Finset.sum_eq_single s ?_ ?_
    · intro v hv hvs
      have hvt : v ≠ t := by
        intro h
        exact ht (by simpa [h] using hv)
      exact hflow.conserved v hvs hvt
    · intro hsnot
      exact False.elim (hsnot hs)
  unfold value
  rw [← hsum]
  exact N.sum_excess_eq_cutOut_sub_cutIn S x

/-- Weak duality: every feasible flow has value at most every directed
`s`-`t` cut capacity. -/
theorem value_le_cutCapacity_of_cut
    {s t : V} {x : E → ℝ} (hflow : N.IsFlow s t x)
    {S : Finset V} (hs : s ∈ S) (ht : t ∉ S) :
    N.value s x ≤ N.cutCapacity S := by
  classical
  rw [N.value_eq_cutOut_sub_cutIn_of_cut hflow hs ht]
  have hcutIn_nonneg : 0 ≤ N.cutIn S x := by
    unfold cutIn
    exact Finset.sum_nonneg fun e _ => by
      by_cases h : N.tail e ∉ S ∧ N.head e ∈ S
      · simpa [h] using hflow.nonneg e
      · simp [h]
  have hsub_le : N.cutOut S x - N.cutIn S x ≤ N.cutOut S x := by
    linarith
  have hout_le : N.cutOut S x ≤ N.cutCapacity S := by
    unfold cutOut cutCapacity
    exact Finset.sum_le_sum fun e _ => by
      by_cases h : N.tail e ∈ S ∧ N.head e ∉ S
      · simpa [h] using hflow.le_cap e
      · simp [h]
  exact hsub_le.trans hout_le

omit [Fintype E] [DecidableEq V] in
/-- On the residual reachable set, every original arc leaving the set is
saturated. -/
theorem eq_cap_of_mem_residualReachableSet_of_notMem
    [Fintype V] {s : V} {x : E → ℝ} {e : E}
    (hflow : ∀ e, x e ≤ N.cap e)
    (htail : N.tail e ∈ N.residualReachableSet s x)
    (hhead : N.head e ∉ N.residualReachableSet s x) :
    x e = N.cap e := by
  classical
  have hnot : ¬ x e < N.cap e := by
    intro hlt
    have hstep : N.ResidualAdj x (N.tail e) (N.head e) :=
      Or.inl ⟨e, rfl, rfl, hlt⟩
    exact hhead (N.residualReachableSet_closed htail hstep)
  exact le_antisymm (hflow e) (le_of_not_gt hnot)

omit [Fintype E] [DecidableEq V] in
/-- On the residual reachable set, every original arc entering the set carries
zero flow. -/
theorem eq_zero_of_notMem_residualReachableSet_of_mem
    [Fintype V] {s : V} {x : E → ℝ} {e : E}
    (hnonneg : ∀ e, 0 ≤ x e)
    (htail : N.tail e ∉ N.residualReachableSet s x)
    (hhead : N.head e ∈ N.residualReachableSet s x) :
    x e = 0 := by
  classical
  have hnot : ¬ 0 < x e := by
    intro hpos
    have hstep : N.ResidualAdj x (N.head e) (N.tail e) :=
      Or.inr ⟨e, rfl, rfl, hpos⟩
    exact htail (N.residualReachableSet_closed hhead hstep)
  exact le_antisymm (le_of_not_gt hnot) (hnonneg e)

/-- If there is no residual path from source to sink, the residual reachable
set gives a tight cut. -/
theorem value_eq_cutCapacity_of_no_residual_path
    [Fintype V] {s t : V} {x : E → ℝ} (hflow : N.IsFlow s t x)
    (hno : ¬ Relation.ReflTransGen (N.ResidualAdj x) s t) :
    N.value s x = N.cutCapacity (N.residualReachableSet s x) := by
  classical
  let S := N.residualReachableSet s x
  have hs : s ∈ S := N.source_mem_residualReachableSet s x
  have ht : t ∉ S := N.sink_notMem_residualReachableSet_of_not_reachable hno
  have hout :
      N.cutOut S x = N.cutCapacity S := by
    unfold cutOut cutCapacity
    refine Finset.sum_congr rfl ?_
    intro e _he
    by_cases h : N.tail e ∈ S ∧ N.head e ∉ S
    · have hsaturate : x e = N.cap e :=
        N.eq_cap_of_mem_residualReachableSet_of_notMem hflow.le_cap h.1 h.2
      simp [h, hsaturate]
    · simp [h]
  have hin :
      N.cutIn S x = 0 := by
    unfold cutIn
    refine Finset.sum_eq_zero ?_
    intro e _he
    by_cases h : N.tail e ∉ S ∧ N.head e ∈ S
    · have hzero : x e = 0 :=
        N.eq_zero_of_notMem_residualReachableSet_of_mem hflow.nonneg h.1 h.2
      simp [h, hzero]
    · simp [h]
  rw [N.value_eq_cutOut_sub_cutIn_of_cut hflow hs ht, hout, hin, sub_zero]

/-- If a maximum flow has no residual source-sink path, the residual reachable
set is a minimum cut and its capacity equals the maximum flow value. -/
theorem residualReachableSet_isMinimumCut_of_maximum_no_residual_path
    [Fintype V] {s t : V} {x : E → ℝ}
    (hmax : N.IsMaximumFlow s t x)
    (hno : ¬ Relation.ReflTransGen (N.ResidualAdj x) s t) :
    N.IsMinimumCut s t (N.residualReachableSet s x) ∧
      N.cutCapacity (N.residualReachableSet s x) = N.value s x := by
  classical
  let S := N.residualReachableSet s x
  have hs : s ∈ S := N.source_mem_residualReachableSet s x
  have ht : t ∉ S := N.sink_notMem_residualReachableSet_of_not_reachable hno
  have htight : N.value s x = N.cutCapacity S :=
    N.value_eq_cutCapacity_of_no_residual_path hmax.1 hno
  refine ⟨?_, htight.symm⟩
  refine ⟨⟨hs, ht⟩, ?_⟩
  intro T hT
  have hweak : N.value s x ≤ N.cutCapacity T :=
    N.value_le_cutCapacity_of_cut hmax.1 hT.1 hT.2
  rw [← htight]
  exact hweak

/-- Conditional max-flow/min-cut package: a maximum flow without a residual
source-sink path has the same value as a minimum cut.  The missing theorem in
the Ford--Fulkerson proof is precisely that every maximum flow has no residual
source-sink path. -/
theorem maxFlow_minCut_of_no_residual_path
    [Fintype V] {s t : V} {x : E → ℝ}
    (hmax : N.IsMaximumFlow s t x)
    (hno : ¬ Relation.ReflTransGen (N.ResidualAdj x) s t) :
    ∃ S : Finset V,
      N.IsMinimumCut s t S ∧ N.value s x = N.cutCapacity S := by
  refine ⟨N.residualReachableSet s x, ?_⟩
  rcases N.residualReachableSet_isMinimumCut_of_maximum_no_residual_path hmax hno with
    ⟨hmin, hcap⟩
  exact ⟨hmin, hcap.symm⟩

/-- Existence version of the conditional max-flow/min-cut theorem.  Once the
standard augmentation lemma proves that maximum flows have no residual
source-sink path, this theorem immediately yields a maximum flow and a minimum
cut with equal value. -/
theorem exists_maximumFlow_minimumCut_of_no_residual_for_maximum
    [Fintype V] (s t : V)
    (hno :
      ∀ x : E → ℝ, N.IsMaximumFlow s t x →
        ¬ Relation.ReflTransGen (N.ResidualAdj x) s t) :
    ∃ x : E → ℝ, ∃ S : Finset V,
      N.IsMaximumFlow s t x ∧ N.IsMinimumCut s t S ∧
        N.value s x = N.cutCapacity S := by
  rcases N.exists_maximumFlow s t with ⟨x, hmax⟩
  rcases N.maxFlow_minCut_of_no_residual_path hmax (hno x hmax) with
    ⟨S, hmin, heq⟩
  exact ⟨x, S, hmax, hmin, heq⟩

/-- Finite real-valued max-flow/min-cut theorem. -/
theorem exists_maximumFlow_minimumCut
    [Fintype V] [DecidableEq E] {s t : V} (hst : s ≠ t) :
    ∃ x : E → ℝ, ∃ S : Finset V,
      N.IsMaximumFlow s t x ∧ N.IsMinimumCut s t S ∧
        N.value s x = N.cutCapacity S := by
  exact N.exists_maximumFlow_minimumCut_of_no_residual_for_maximum s t
    (fun x hmax => N.no_residual_path_of_isMaximumFlow hst hmax)

end DirectedNetwork

end SimpleGraph

end Lax17Proofs
