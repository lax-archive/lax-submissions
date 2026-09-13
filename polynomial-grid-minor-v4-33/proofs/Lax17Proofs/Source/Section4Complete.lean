import Lax17Proofs.Source.Section4Assembly
import Lax17Proofs.Source.Section45PseudoGrid

namespace Lax17Proofs

universe u v w

/-!
# Chuzhoy--Tan Section 4, complete pseudo-grid branch

This module assembles the source-faithful path contractions and slicing from
Section 4.2, the cleanup and happy-cluster construction from Sections
4.3--4.4, the weak Path-of-Sets input from Section 4.5, and the bounded-degree
strongification from Section 4.6.
-/

namespace SimpleGraph


namespace Section4Assembly

open Finset

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : _root_.SimpleGraph V}

/-- Chuzhoy--Tan Sections 4.2--4.5, starting with the depth-`64*g^4`
pseudo-grid supplied by Theorem 4.1.

The output graph is a minor of the original host, has maximum degree four,
and carries the complete input consumed by the already-proved Section 4.5
weak Path-of-Sets assembly. -/
theorem section45Input_of_pseudoGrid_depth64
    {A B X : Finset V} {g kappa : ℕ}
    {P : PerfectPathPacking G A B} {Q : PerfectPathPacking G A X}
    (Gamma : PseudoGrid G A B X g (64 * g ^ 4) P Q)
    (hminimal : P.IsMinimumTheorem41Pair Q)
    (hg : 2 ≤ g)
    (hlarge : 2 ^ 22 * g ^ 10 * Nat.log 2 g ≤ kappa)
    (hPcard : P.card = kappa) :
    ∃ (W : Type u), ∃ (_ : Fintype W), ∃ (_ : DecidableEq W),
      ∃ (J : _root_.SimpleGraph W), ∃ N : ℕ,
        IsMinor J G ∧
          MaxDegreeAtMost J 4 ∧
            Nonempty
              (Section45.Section45Input J N
                (8 * g ^ 4 * Nat.log 2 g) (16 * g ^ 4) (g ^ 2)) := by
  classical
  let M := 8 * g ^ 4 * Nat.log 2 g
  let sliceWidth := 2 ^ 11 * g ^ 6
  let Dhat := 16 * g ^ 4
  let ell := g ^ 2
  have hM : 0 < M := by
    dsimp [M]
    have hlog : 0 < Nat.log 2 g :=
      Nat.log_pos (by norm_num) hg
    positivity
  have hsliceWidth : 0 < sliceWidth := by
    dsimp [sliceWidth]
    positivity
  have hDhat : 0 < Dhat := by
    dsimp [Dhat]
    positivity
  have hell : 0 < ell := by
    dsimp [ell]
    positivity
  have hbudget :
      M * sliceWidth + (M + 1) * Gamma.rowPacking.card ≤
        Gamma.goodQSet.card := by
    simpa [M, sliceWidth] using
      SimpleGraph.Section4Assembly.PseudoGrid.section42_slicing_budget_depth64
        Gamma hg hlarge hPcard
  have hgoodPos : 0 < Gamma.goodQSet.card := by
    have hmainPos : 0 < M * sliceWidth := Nat.mul_pos hM hsliceWidth
    exact hmainPos.trans_le
      ((Nat.le_add_right (M * sliceWidth)
        ((M + 1) * Gamma.rowPacking.card)).trans hbudget)
  have hgood : Gamma.goodQSet.Nonempty := Finset.card_pos.mp hgoodPos
  have hGammaLower :
      64 * g ^ 4 ≤ Gamma.rowPacking.card :=
    Gamma.rowPacking_card_bounds_of_goodQSet_nonempty hgood |>.1
  have hGammaUpper :
      Gamma.rowPacking.card ≤ (64 * g ^ 4) * g ^ 2 :=
    Gamma.rowPacking_card_bounds_of_goodQSet_nonempty hgood |>.2
  rcases
      Gamma.section42_slicing_minor_of_pseudoGrid_actualPaths
        hminimal (by positivity) hM hsliceWidth hbudget with
    ⟨W, hWfin, hWdec, J, A', B', S, T, R, Qpack, sigma,
      hminor, hdegree, hunique, hRcard, hQcard, hdense, hwidth⟩
  letI : Fintype W := hWfin
  letI : DecidableEq W := hWdec
  have hRLower : 64 * g ^ 4 ≤ R.card := by
    rw [hRcard]
    exact hGammaLower
  have hRUpper : R.card ≤ (64 * g ^ 4) * g ^ 2 := by
    rw [hRcard]
    exact hGammaUpper
  let params : Section4Parameters g R.card :=
    section4Parameters hg hRLower hRUpper
  have hintersects :
      PathSlicing.PathPackingIntersectsLinkage R Qpack := by
    intro q
    have hpos :
        0 <
          ((Finset.univ : Finset R.Index).filter fun r =>
            ¬ Disjoint (Qpack.path q).vertexSet (R.path r).vertexSet).card :=
      (by positivity : 0 < 64 * g ^ 4).trans_le (hdense q)
    rcases Finset.card_pos.mp hpos with ⟨r, hr⟩
    exact ⟨r, (Finset.mem_filter.1 hr).2⟩
  have hscale : 8 * ell ≤ Dhat := by
    dsimp [ell, Dhat]
    nlinarith [sq_nonneg (g ^ 2)]
  have hdense' :
      ∀ q : Qpack.Index,
        4 * Dhat ≤
          ((Finset.univ : Finset R.Index).filter fun r =>
            ¬ Disjoint (Qpack.path q).vertexSet (R.path r).vertexSet).card := by
    intro q
    convert hdense q using 1 <;> simp [Dhat] <;> ring
  have hcleanup :
      2 * (Fintype.card R.Index) * (4 * ell) ≤
        (2 * Dhat) * sliceWidth := by
    change 2 * R.card * (4 * ell) ≤ (2 * Dhat) * sliceWidth
    calc
      2 * R.card * (4 * ell)
          ≤ 2 * ((64 * g ^ 4) * g ^ 2) * (4 * ell) :=
        Nat.mul_le_mul_right (4 * ell)
          (Nat.mul_le_mul_left 2 hRUpper)
      _ ≤ (2 * Dhat) * sliceWidth := by
        dsimp [ell, Dhat, sliceWidth]
        nlinarith [sq_nonneg (g ^ 6)]
  rcases
      PathSlicing.exists_slicedHappyCores sigma Qpack
        hell hDhat hsliceWidth hscale hwidth hdense' hcleanup with
    ⟨cores⟩
  have hinput :
      Nonempty
        (Section45.Section45Input J R.card M Dhat ell) :=
    cores.section45Input_of_slicedHappyCores
      hintersects hell hscale
        (by simpa [params, ell] using params.theorem415_rows)
        (by
          have h := params.theorem415_square
          rw [params.weakWidth_eq, params.retainedDepth_eq] at h
          simpa [ell, Dhat] using h)
        (by
          have h := params.theorem415_large
          rw [params.weakWidth_eq, params.retainedDepth_eq,
            params.sliceCount_eq] at h
          simpa [ell, Dhat, M] using h)
  refine ⟨W, hWfin, hWdec, J, R.card, hminor, hdegree, ?_⟩
  simpa [M, Dhat, ell] using hinput

/-- The complete proof-producing input for Chuzhoy--Tan Section 4.

No paper-level proposition is assumed here: the weak system is produced from
the depth-`64*g^4` pseudo-grid above, and every such weak system is
strongified by the degree-four theorem from Section 4.6. -/
theorem section4WeakToStrongAssemblyInput10_proved :
    CrossbarTheorem.Section4WeakToStrongAssemblyInput10.{u} 20000 := by
  intro V _ _ H A B X g kappa P Q hg hpow hAB hAX hBX hdegree hlarge
    hPcard hQcard hminimal Gamma
  rcases
      section45Input_of_pseudoGrid_depth64
        Gamma hminimal hg hlarge hPcard with
    ⟨W, hWfin, hWdec, J, N, hminor, hJdegree, hinput⟩
  letI : Fintype W := hWfin
  letI : DecidableEq W := hWdec
  rcases hinput with ⟨weakInput⟩
  refine
    ⟨W, hWfin, hWdec, J, N,
      8 * g ^ 4 * Nat.log 2 g, 16 * g ^ 4, g ^ 2,
      strongifiedWidth (g ^ 2), hminor, ?_, ?_, weakInput, ?_⟩
  · have hgSq : 0 < g ^ 2 := by positivity
    nlinarith
  · exact le_twentyThousand_mul_strongifiedWidth (by positivity)
  · intro Pweak
    exact
      ⟨strongificationData_of_weakPathOfSetsSystem_maxDegreeFour
        Pweak hJdegree⟩

end Section4Assembly

namespace CrossbarTheorem

/-- Axiom-free exponent-ten crossbar dichotomy, obtained from Theorem 4.1 and
the fully formalized Sections 4.2--4.6 pseudo-grid branch. -/
theorem crossbar_or_strong_pathOfSets_minor_degree10_proved :
    ∃ c : ℕ, 0 < c ∧
      ∀ {V : Type u} [Fintype V] [DecidableEq V]
        (H : _root_.SimpleGraph V) {g kappa : ℕ}
        {A B X : Finset V},
          2 ≤ g →
            CrossbarContract.IsPowerOfTwo g →
              A.card = kappa →
                B.card = kappa →
                  X.card = kappa →
                    Disjoint A B →
                      Disjoint A X →
                        Disjoint B X →
                          2 ^ 22 * g ^ 10 * Nat.log 2 g ≤ kappa →
                            (∀ x ∈ X, DegreeEquals H x 1) →
                              (Pab : PathPacking H A B) →
                                Pab.card = kappa →
                                  (Pax : PathPacking H A X) →
                                    Pax.card = kappa →
                                      Nonempty (Crossbar H A B X (g ^ 2)) ∨
                                        ∃ ell w : ℕ,
                                          g ^ 2 ≤ c * ell ∧
                                            g ^ 2 ≤ c * w ∧
                                              CrossbarContract.HasStrongPathOfSetsMinor
                                                H ell w :=
  crossbar_or_strong_pathOfSets_minor_degree10_of_weakToStrongAssemblyInput
    (by norm_num)
    Section4Assembly.section4WeakToStrongAssemblyInput10_proved

end CrossbarTheorem

end SimpleGraph

end Lax17Proofs
