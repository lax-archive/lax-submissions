import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic

/-!
---
title: A uniform sample is unlikely to miss a large set
type: lemma
---
Let A be nonempty, let X be a subset of A of size at least 6c²L, and suppose
c≥1 and |A|≤N≤2^L. A uniformly chosen subset of A of size ceil(|A|/(2c²))
avoids X with probability at most 1/N³. This is the finite counting form of
Lemma 3.7 of Dreier--Kuske.

# Formalization notes

The numerator counts samples disjoint from X and the denominator counts
all subsets of the prescribed size. The assumptions guarantee that the
denominator is positive. Natural ceiling division is written explicitly.
This is a theorem about ideal fixed-size uniform samples; its connection
to the program's finite random keys is a separate proof obligation.
-/

namespace Lax235315.UniformSampleAvoidance

/-- The fraction of fixed-size samples avoiding X is at most N to the power -3. -/
axiom miss_fraction_le {n : ℕ} {A X : Finset (Fin n)} {c N L : ℕ}
    (hc : 1 ≤ c) (hA : A.Nonempty) (hX : X ⊆ A)
    (hXcard : 6 * c ^ 2 * L ≤ X.card)
    (hAN : A.card ≤ N) (hNpow : N ≤ 2 ^ L) :
    let s := (A.card + 2 * c ^ 2 - 1) / (2 * c ^ 2)
    (((A.powersetCard s).filter (fun W => Disjoint W X)).card : ℝ) /
      (A.powersetCard s).card ≤ 1 / (N : ℝ) ^ 3

end Lax235315.UniformSampleAvoidance
