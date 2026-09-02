import Lax3.DistFO
import Lax12.UniformQuasiWideness
import Mathlib.Data.Set.Card
import Mathlib.Order.Minimal

/-!
---
title: Scatter sentences
type: definition
---
A set of vertices is *r*-scattered if its members have pairwise
distance larger than *r*. A *scatter sentence* asserts that a
distinguished *r*-scattered set of the vertices satisfying a
one-variable formula β has at least *t* elements. Which scattered set
is distinguished is the content of a *scatter choice*: for each graph,
radius and vertex set it names a number that is the size of *some*
inclusion-wise maximal *r*-scattered subset of that set. The maximum
size of a scattered subset of the set, and the size the greedy process
produces when it runs through the vertices in order and takes every
vertex it can, are both scatter choices.

The locality theorem of `Lax3.Locality` rewrites a formula into a
boolean combination of local formulas and scatter sentences. Scatter
sentences of distance rank (*k*, *q*) are those whose parameters obey
the source's schedule: at most *k* + *q* witnesses, a local β of
distance rank (*k*+*i*, *q*−*i*) for some 1 ≤ *i* ≤ *q*, and a radius
between 4ρ⁻(*k*+*i*, *q*−*i*) and 9^(*k*+*i*)ρ⁻(*k*+*i*, *q*−*i*). The
lower bound makes β semantically (*r*/4)-local, which is what the proof
of the theorem consumes; the upper bound keeps the radius below
ρ⁻(*k*, *q*), which is what keeps the rank from growing.

This is §2.1 of the source note (arXiv:2606.23180), specialized to the
finite colored graphs of `Lax3.ColoredGraphs`.

# Formalization notes

The scatter choice is per graph, radius and vertex set; the source's is
per structure, radius and formula β. The two agree wherever a scatter
sentence is evaluated, since the vertex set involved is always
{*a* : β(*a*) holds}, and the coarser form is strictly stronger: it
forces the same value for two formulas defining the same set, and it is
uniform in the coloring, so a scatter value cannot change when colors
are added that β does not mention. Both are properties the algorithm
needs and neither is available from the source's form. The dependence
on the graph is genuine and stays.

"*r*-scattered" is Lax12's `DistIndependent`: a set is distance-*r*
independent in `G` when every walk between two distinct members is
longer than *r*, which is the source's "pairwise distance larger than
*r*" in the Gaifman graph, since the Gaifman graph of a colored graph
is the graph. It is used as it stands and not restated here.
Inclusion-wise maximality is mathlib's `Maximal`, over the property of
being a scattered subset of the given set.

Over `Fin n` every vertex set is finite, so the source's value ∞ — for
structures with arbitrarily large scattered subsets — cannot arise and
is not carried; `ScatterChoice.size` is ℕ-valued.

The distance rank of a scatter sentence is the source's condition
(2)/(eq:scatter-radius) verbatim, with the bound *t* ≤ *k* + *q* stated
alongside the radius window rather than in the surrounding prose.
Nothing here requires *q* ≥ 1: for *q* = 0 the condition 1 ≤ *i* ≤ *q*
is unsatisfiable, so no scatter sentence has distance rank (*k*, 0),
which is the source's convention made into a fact.
-/

namespace Lax3.ScatterSentences

open Lax3.ColoredGraphs Lax3.DistFO Lax12.UniformQuasiWideness

/-- A choice of scatter values: for every graph `G`, radius `r` and
vertex set `X`, a number `size G r X` which is the cardinality of some
inclusion-wise maximal `r`-scattered subset of `X`. This is the
source's "fix arbitrarily and once and for all a value `s`", made a
parameter: every statement about scatter sentences holds for every
choice. -/
structure ScatterChoice where
  /-- The chosen scatter value of a graph, radius and vertex set. -/
  size : ∀ {n : ℕ}, SimpleGraph (Fin n) → ℕ → Set (Fin n) → ℕ
  /-- The chosen value is realized by an inclusion-wise maximal
  `r`-scattered subset of `X`. -/
  spec : ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (r : ℕ) (X : Set (Fin n)),
    ∃ S : Set (Fin n), S ⊆ X ∧
      Maximal (fun T => T ⊆ X ∧ DistIndependent G r T) S ∧ S.ncard = size G r X

/-- A scatter sentence: there is an `r`-scattered set of `t` vertices
satisfying the one-variable formula `β`, in the sense fixed by a
scatter choice. -/
structure ScatterSentence (L : ℕ) where
  /-- The radius at which the witnesses are scattered. -/
  r : ℕ
  /-- The one-variable formula the witnesses satisfy. -/
  β : DistFO L 1
  /-- The number of witnesses demanded. -/
  t : ℕ

variable {L n : ℕ}

/-- The scatter sentence holds in the colored graph `(G, col)` when the
chosen scatter value of the set defined by `β`, at radius `r`, is at
least `t`. -/
def ScatterSentence.Sat (choice : ScatterChoice) (G : SimpleGraph (Fin n))
    (col : Coloring n L) (σ : ScatterSentence L) : Prop :=
  σ.t ≤ choice.size G σ.r {a | DistFO.Sat G col (fun _ => a) σ.β}

/-- The scatter sentence has distance rank `(k, q)`: it demands at most
`k + q` witnesses, and for some `1 ≤ i ≤ q` its formula `β` is local of
distance rank `(k + i, q - i)` and its radius lies in the source's
window `4ρ⁻(k + i, q - i) ≤ r ≤ 9 ^ (k + i) · ρ⁻(k + i, q - i)`. -/
def ScatterSentence.DRank (k q : ℕ) (σ : ScatterSentence L) : Prop :=
  σ.t ≤ k + q ∧ ∃ i, 1 ≤ i ∧ i ≤ q ∧ DistFO.IsLocal σ.β ∧
    DistFO.DRank (k + i) (q - i) σ.β ∧
    4 * rhoMinus (k + i) (q - i) ≤ σ.r ∧ σ.r ≤ 9 ^ (k + i) * rhoMinus (k + i) (q - i)

end Lax3.ScatterSentences
