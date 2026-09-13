import Lax17Proofs.Source.Exponent7.AmortizedRecursiveSlicing

namespace Lax17Proofs

/-!
# Finite amortized slicing controller

Recursive slice layers form a finite run indexed by the initial
`slice-count * width` potential. Each nonterminal layer retires its productive
slices and refines every remaining small slice with binary fanout.
Observation 5.4 and Theorem 4.6 bound the accumulated loss.
-/

namespace SimpleGraph
namespace Exponent7

open Finset
open Exponent8

universe u v

/-- One layer whose large slices contribute to the productive outcome. -/
structure AmortizedProductiveLayer
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W)
    (A B X : Finset V)
    (P : PerfectPathPacking G A B)
    (Q : PerfectPathPacking G A X)
    {Abar Bbar Sbar Tbar : Finset W}
    (Rbar : PerfectPathPacking H Abar Bbar)
    (Qbar : PathPacking H Sbar Tbar)
    (g Dhat h Dstar : ℕ) where
  m : ℕ
  width : ℕ
  layer :
    RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) Dhat
  continuing : amortizedStopThreshold h Dstar < width

namespace AmortizedProductiveLayer

variable
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {g Dhat h Dstar : ℕ}

noncomputable def indices
    (L : AmortizedProductiveLayer
      G H A B X P Q Rbar Qbar g Dhat h Dstar) :
    Finset (Fin L.m) :=
  L.layer.largeIndices (amortizedRowCap h L.width)

noncomputable def potential
    (L : AmortizedProductiveLayer
      G H A B X P Q Rbar Qbar g Dhat h Dstar) : ℕ :=
  L.indices.card * L.width

noncomputable def rowMass
    (L : AmortizedProductiveLayer
      G H A B X P Q Rbar Qbar g Dhat h Dstar) : ℕ :=
  ∑ i ∈ L.indices, (L.layer.cleanup i).rows.card

theorem potential_le_weighted_rowMass
    (L : AmortizedProductiveLayer
      G H A B X P Q Rbar Qbar g Dhat h Dstar)
    (hh : 0 < h) (hD : 0 < Dstar) :
    L.potential ≤ 2048 * h * L.rowMass := by
  exact largePotential_le_weighted_rowMass
    L.layer hh hD L.continuing

end AmortizedProductiveLayer

/-- A finite run of actual recursive slice layers.

`terminal` retains the current active potential.  `productiveOnly` is used
when no small slice remains.  `refined` records one actual binary
Observation 5.4/Theorem 4.6 transition and continues from its produced
layer. -/
inductive AmortizedSlicingRun
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W)
    (A B X : Finset V)
    (P : PerfectPathPacking G A B)
    (Q : PerfectPathPacking G A X)
    {Abar Bbar Sbar Tbar : Finset W}
    (Rbar : PerfectPathPacking H Abar Bbar)
    (Qbar : PathPacking H Sbar Tbar)
    (g Dhat h Dstar : ℕ) : ℕ → Type (max u v)
  | terminal {m width : ℕ}
      (layer :
        RecursiveSliceLayer
          G H A B X P Q Rbar Qbar
          m width (4 * g ^ 2) Dhat)
      (stopped : width ≤ amortizedStopThreshold h Dstar) :
      AmortizedSlicingRun
        G H A B X P Q Rbar Qbar g Dhat h Dstar
        (m * width)
  | productiveOnly {m width : ℕ}
      (layer :
        RecursiveSliceLayer
          G H A B X P Q Rbar Qbar
          m width (4 * g ^ 2) Dhat)
      (continuing : amortizedStopThreshold h Dstar < width)
      (small_empty :
        (layer.smallIndices
          (amortizedRowCap h width)).card = 0) :
      AmortizedSlicingRun
        G H A B X P Q Rbar Qbar g Dhat h Dstar
        (m * width)
  | refined {m width : ℕ}
      (layer :
        RecursiveSliceLayer
          G H A B X P Q Rbar Qbar
          m width (4 * g ^ 2) Dhat)
      (continuing : amortizedStopThreshold h Dstar < width)
      (small_nonempty :
        0 < (layer.smallIndices
          (amortizedRowCap h width)).card)
      (h_pos : 0 < h)
      (Dstar_pos : 0 < Dstar)
      (loss_le_Dstar : amortizedLoss g ≤ Dstar)
      (next :
        RecursiveSliceLayer
          G H A B X P Q Rbar Qbar
          ((layer.smallIndices
            (amortizedRowCap h width)).card * 2)
          (amortizedChildWidth (amortizedLoss g) h width)
          (4 * g ^ 2) Dhat)
      (tail :
        AmortizedSlicingRun
          G H A B X P Q Rbar Qbar g Dhat h Dstar
          (((layer.smallIndices
            (amortizedRowCap h width)).card * 2) *
              amortizedChildWidth (amortizedLoss g) h width)) :
      AmortizedSlicingRun
        G H A B X P Q Rbar Qbar g Dhat h Dstar
        (m * width)

namespace AmortizedSlicingRun

variable
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {g Dhat h Dstar : ℕ}

/-- Actual number of binary refinements. -/
noncomputable def steps :
    {initial : ℕ} →
      AmortizedSlicingRun
        G H A B X P Q Rbar Qbar g Dhat h Dstar initial → ℕ
  | _, .terminal _ _ => 0
  | _, .productiveOnly _ _ _ => 0
  | _, .refined _ _ _ _ _ _ _ tail => steps tail + 1

/-- Productive layers encountered by the run, in depth order. -/
noncomputable def productiveLayers :
    {initial : ℕ} →
      AmortizedSlicingRun
        G H A B X P Q Rbar Qbar g Dhat h Dstar initial →
      List
        (AmortizedProductiveLayer
          G H A B X P Q Rbar Qbar g Dhat h Dstar)
  | _, .terminal _ _ => []
  | _, .productiveOnly layer continuing _ =>
      [{ m := _
         width := _
         layer := layer
         continuing := continuing }]
  | _, .refined layer continuing _ _ _ _ _ tail =>
      { m := _
        width := _
        layer := layer
        continuing := continuing } ::
        productiveLayers tail

/-- Sum of all retired productive potentials. -/
noncomputable def productivePotential
    {initial : ℕ}
    (run :
      AmortizedSlicingRun
        G H A B X P Q Rbar Qbar g Dhat h Dstar initial) : ℕ :=
  (run.productiveLayers.map
    AmortizedProductiveLayer.potential).sum

/-- Potential of the final active layer; zero if every slice became
productive. -/
noncomputable def terminalPotential :
    {initial : ℕ} →
      AmortizedSlicingRun
        G H A B X P Q Rbar Qbar g Dhat h Dstar initial → ℕ
  | _, .terminal (m := m) (width := width) _ _ => m * width
  | _, .productiveOnly _ _ _ => 0
  | _, .refined _ _ _ _ _ _ _ tail => terminalPotential tail

/-- Number of slices in the final active layer; zero when every slice became
productive. -/
noncomputable def terminalSliceCount :
    {initial : ℕ} →
      AmortizedSlicingRun
        G H A B X P Q Rbar Qbar g Dhat h Dstar initial → ℕ
  | _, .terminal (m := m) _ _ => m
  | _, .productiveOnly _ _ _ => 0
  | _, .refined _ _ _ _ _ _ _ tail => terminalSliceCount tail

/-- Convert an actual slicing run into the abstract potential trace. -/
noncomputable def toPotentialTrace :
    {initial : ℕ} →
      (run :
        AmortizedSlicingRun
          G H A B X P Q Rbar Qbar g Dhat h Dstar initial) →
      AmortizedPotentialTrace (8 * h) initial
  | _, .terminal (m := m) (width := width) _ _ =>
      .terminal (m * width)
  | _, .productiveOnly (m := m) (width := width) _ _ _ =>
      .terminal (m * width)
  | _, .refined (m := m) (width := width)
      layer continuing small_nonempty h_pos Dstar_pos
        loss_le_Dstar next tail =>
      let largeCount :=
        (layer.largeIndices (amortizedRowCap h width)).card
      let smallCount :=
        (layer.smallIndices (amortizedRowCap h width)).card
      let qNext :=
        amortizedChildWidth (amortizedLoss g) h width
      let loss :=
        m * width -
          (largeCount * width + (2 * smallCount) * qNext)
      have hpartition : largeCount + smallCount = m := by
        have hpart :=
          layer.smallIndices_card_add_largeIndices_card
            (amortizedRowCap h width)
        dsimp [largeCount, smallCount]
        omega
      have hstep :=
        amortized_count_step hpartition
          (two_mul_amortizedChildWidth_le
            (amortizedLoss g) h width)
          (amortizedChildWidth_retention
            (h := h) (Dstar := Dstar)
            (delta := amortizedLoss g)
            (q := width)
            h_pos Dstar_pos loss_le_Dstar
            continuing)
      .step
        (largeCount * width) loss
        (by
          simpa [largeCount, smallCount, qNext, loss,
            Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hstep.1)
        (by
          simpa [largeCount, smallCount, qNext, loss,
            Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hstep.2)
        (toPotentialTrace tail)

@[simp] theorem steps_toPotentialTrace
    {initial : ℕ}
    (run :
      AmortizedSlicingRun
        G H A B X P Q Rbar Qbar g Dhat h Dstar initial) :
    run.toPotentialTrace.steps = run.steps := by
  induction run with
  | terminal layer stopped =>
      simp [toPotentialTrace, steps, AmortizedPotentialTrace.steps]
  | productiveOnly layer continuing small_empty =>
      simp [toPotentialTrace, steps, AmortizedPotentialTrace.steps]
  | refined layer continuing small_nonempty h_pos Dstar_pos
      loss_le_Dstar next tail ih =>
      simp [toPotentialTrace, steps, AmortizedPotentialTrace.steps, ih]

@[simp] theorem outcome_toPotentialTrace
    {initial : ℕ}
    (run :
      AmortizedSlicingRun
        G H A B X P Q Rbar Qbar g Dhat h Dstar initial) :
    run.toPotentialTrace.outcome =
      run.productivePotential + run.terminalPotential := by
  induction run with
  | terminal layer stopped =>
      simp [toPotentialTrace, productivePotential, productiveLayers,
        terminalPotential, AmortizedPotentialTrace.outcome]
  | @productiveOnly m width layer continuing small_empty =>
      have hpart :=
        layer.smallIndices_card_add_largeIndices_card
          (amortizedRowCap h width)
      have hlarge :
          (layer.largeIndices (amortizedRowCap h width)).card = m := by
        omega
      simp [toPotentialTrace, productivePotential, productiveLayers,
        terminalPotential, AmortizedPotentialTrace.outcome,
        AmortizedProductiveLayer.potential,
        AmortizedProductiveLayer.indices, hlarge]
  | refined layer continuing small_nonempty h_pos Dstar_pos
      loss_le_Dstar next tail ih =>
      simp [toPotentialTrace, productivePotential, productiveLayers,
        terminalPotential, AmortizedPotentialTrace.outcome, ih,
        AmortizedProductiveLayer.potential,
        AmortizedProductiveLayer.indices, Nat.add_assoc]

/-- The seven-eighths potential guarantee for an actual slicing run. -/
theorem seven_mul_initial_le_outcomes
    {initial : ℕ} (hh : 0 < h)
    (run :
      AmortizedSlicingRun
        G H A B X P Q Rbar Qbar g Dhat h Dstar initial)
    (hsteps : run.steps ≤ h) :
    7 * initial ≤
      8 * (run.productivePotential + run.terminalPotential) := by
  simpa using
    run.toPotentialTrace.seven_mul_initial_le_eight_mul_outcome
      hh (by simpa using hsteps)

/-- A run contains at most one productive layer per refinement level, plus
the possible final all-productive layer. -/
theorem productiveLayers_length_le_steps_add_one
    {initial : ℕ}
    (run :
      AmortizedSlicingRun
        G H A B X P Q Rbar Qbar g Dhat h Dstar initial) :
    run.productiveLayers.length ≤ run.steps + 1 := by
  induction run with
  | terminal layer stopped =>
      simp [productiveLayers, steps]
  | productiveOnly layer continuing small_empty =>
      simp [productiveLayers, steps]
  | refined layer continuing small_nonempty h_pos Dstar_pos
      loss_le_Dstar next tail ih =>
      simp [productiveLayers, steps]
      omega

/-- A division-free maximum/average lemma for a nonempty finite list. -/
theorem exists_sum_le_length_mul
    {α : Type*} (xs : List α) (f : α → ℕ)
    (hne : xs ≠ []) :
    ∃ x ∈ xs, (xs.map f).sum ≤ xs.length * f x := by
  induction xs with
  | nil => exact (hne rfl).elim
  | cons a tail ih =>
      by_cases htail : tail = []
      · subst tail
        exact ⟨a, by simp, by simp⟩
      · obtain ⟨x, hx, hsum⟩ := ih htail
        by_cases hxa : f x ≤ f a
        · refine ⟨a, by simp, ?_⟩
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          calc
            f a + (tail.map f).sum
                ≤ f a + tail.length * f x :=
              Nat.add_le_add_left hsum _
            _ ≤ f a + tail.length * f a :=
              Nat.add_le_add_left
                (Nat.mul_le_mul_left tail.length hxa) _
            _ = (tail.length + 1) * f a := by ring
        · have hax : f a ≤ f x :=
            Nat.le_of_lt (Nat.lt_of_not_ge hxa)
          refine ⟨x, by simp [hx], ?_⟩
          simp only [List.map_cons, List.sum_cons, List.length_cons]
          calc
            f a + (tail.map f).sum
                ≤ f x + tail.length * f x :=
              Nat.add_le_add hax hsum
            _ = (tail.length + 1) * f x := by ring

/-- Positive terminal potential exposes the actual final slicing layer. -/
theorem exists_terminalLayer_of_terminalPotential_pos
    {initial : ℕ}
    (run :
      AmortizedSlicingRun
        G H A B X P Q Rbar Qbar g Dhat h Dstar initial)
    (hpositive : 0 < run.terminalPotential) :
    ∃ (m width : ℕ)
      (L : RecursiveSliceLayer
        G H A B X P Q Rbar Qbar
        m width (4 * g ^ 2) Dhat),
      width ≤ amortizedStopThreshold h Dstar ∧
      run.terminalPotential = m * width ∧
      run.terminalSliceCount = m := by
  induction run with
  | terminal layer stopped =>
      exact ⟨_, _, layer, stopped, rfl, rfl⟩
  | productiveOnly layer continuing small_empty =>
      simp [terminalPotential] at hpositive
  | refined layer continuing small_nonempty h_pos Dstar_pos
      loss_le_Dstar next tail ih =>
      exact ih (by simpa [terminalPotential] using hpositive)

end AmortizedSlicingRun

/-- The two outcomes exposed by the amortized controller.

The productive branch returns one actual recursive layer and a
division-free retained-row mass bound.  The terminal branch returns the
actual final narrow layer and a lower bound on its slice count. -/
inductive AmortizedSlicingDichotomy
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    (G : _root_.SimpleGraph V) (H : _root_.SimpleGraph W)
    (A B X : Finset V)
    (P : PerfectPathPacking G A B)
    (Q : PerfectPathPacking G A X)
    {Abar Bbar Sbar Tbar : Finset W}
    (Rbar : PerfectPathPacking H Abar Bbar)
    (Qbar : PathPacking H Sbar Tbar)
    (g Dhat h Dstar initial : ℕ) : Type (max u v)
  | productive
      (L : AmortizedProductiveLayer
        G H A B X P Q Rbar Qbar g Dhat h Dstar)
      (mass :
        7 * initial ≤
          16 * (h + 1) * (2048 * h) * L.rowMass)
  | terminal {m width : ℕ}
      (L : RecursiveSliceLayer
        G H A B X P Q Rbar Qbar
        m width (4 * g ^ 2) Dhat)
      (width_pos : 0 < width)
      (width_le :
        width ≤ amortizedStopThreshold h Dstar)
      (count :
        7 * initial ≤
          16 * m * amortizedStopThreshold h Dstar)

namespace AmortizedSlicingRun

/-- Extract one usable productive depth or the actual terminal layer. -/
theorem exists_dichotomy
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {g Dhat h Dstar initial : ℕ}
    (run :
      AmortizedSlicingRun
        G H A B X P Q Rbar Qbar g Dhat h Dstar initial)
    (hh : 0 < h) (hDstar : 0 < Dstar)
    (hinitial : 0 < initial)
    (hsteps : run.steps ≤ h) :
    Nonempty
      (AmortizedSlicingDichotomy
        G H A B X P Q Rbar Qbar
        g Dhat h Dstar initial) := by
  have houtcomes :=
    run.seven_mul_initial_le_outcomes hh hsteps
  have hsplit :
      7 * initial ≤ 16 * run.productivePotential ∨
        7 * initial ≤ 16 * run.terminalPotential := by
    omega
  rcases hsplit with hproductive | hterminal
  · have hpotential :
        0 < run.productivePotential := by
      omega
    have hnonempty : run.productiveLayers ≠ [] := by
      intro hempty
      rw [productivePotential, hempty] at hpotential
      simp at hpotential
    obtain ⟨L, hL, hmax⟩ :=
      exists_sum_le_length_mul run.productiveLayers
        AmortizedProductiveLayer.potential hnonempty
    have hlength :
        run.productiveLayers.length ≤ h + 1 :=
      run.productiveLayers_length_le_steps_add_one.trans
        (Nat.add_le_add_right hsteps 1)
    have hrow :=
      L.potential_le_weighted_rowMass hh hDstar
    refine ⟨AmortizedSlicingDichotomy.productive L ?_⟩
    calc
        7 * initial
            ≤ 16 * run.productivePotential :=
          hproductive
        _ ≤ 16 *
              (run.productiveLayers.length * L.potential) :=
          Nat.mul_le_mul_left 16 hmax
        _ ≤ 16 * ((h + 1) * L.potential) :=
          Nat.mul_le_mul_left 16
            (Nat.mul_le_mul_right L.potential hlength)
        _ ≤ 16 * ((h + 1) * (2048 * h * L.rowMass)) :=
          Nat.mul_le_mul_left 16
            (Nat.mul_le_mul_left (h + 1) hrow)
        _ = 16 * (h + 1) * (2048 * h) * L.rowMass := by
          ring
  · have hpotential :
        0 < run.terminalPotential := by
      omega
    obtain ⟨m, width, L, hwidth, hpot, hcount⟩ :=
      run.exists_terminalLayer_of_terminalPotential_pos hpotential
    have hwidthPos : 0 < width := by
      rw [hpot] at hpotential
      exact pos_of_mul_pos_right hpotential (Nat.zero_le m)
    refine
      ⟨AmortizedSlicingDichotomy.terminal
        L hwidthPos hwidth ?_⟩
    calc
        7 * initial
            ≤ 16 * run.terminalPotential :=
          hterminal
        _ = 16 * (m * width) := by rw [hpot]
        _ ≤ 16 *
              (m * amortizedStopThreshold h Dstar) :=
          Nat.mul_le_mul_left 16
            (Nat.mul_le_mul_left m hwidth)
        _ = 16 * m * amortizedStopThreshold h Dstar := by
          ring

end AmortizedSlicingRun

/-! ## Construction with finite fuel -/

/-- Build the actual amortized run for at most `fuel` binary refinements. -/
theorem exists_amortizedSlicingRun
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {g Dhat h Dstar m width : ℕ}
    (C : RecursiveSlicingContext
      G H A B X P Q Rbar Qbar Dhat)
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) Dhat)
    (hg : 0 < g)
    (hh : 0 < h)
    (hDstar : 0 < Dstar)
    (hloss : amortizedLoss g ≤ Dstar)
    (hadditive :
      Rbar.card * (4 * g ^ 2) ≤
        Dhat * (8 * g ^ 4))
    (hpruning :
      2 * Rbar.card * (4 * g ^ 2) ≤
        Dhat * Dstar)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (g ^ 2)))
    (fuel : ℕ)
    (hwidthFuel :
      width ≤ 2 ^ fuel * amortizedStopThreshold h Dstar) :
    ∃ run :
      AmortizedSlicingRun
        G H A B X P Q Rbar Qbar
        g Dhat h Dstar (m * width),
      run.steps ≤ fuel ∧
        run.terminalPotential ≤
          run.terminalSliceCount *
            amortizedStopThreshold h Dstar := by
  induction fuel generalizing m width with
  | zero =>
      refine ⟨.terminal L (by simpa using hwidthFuel), ?_, ?_⟩
      · simp [AmortizedSlicingRun.steps]
      · have hwidth :
            width ≤ amortizedStopThreshold h Dstar := by
          simpa using hwidthFuel
        simp only [AmortizedSlicingRun.terminalPotential,
          AmortizedSlicingRun.terminalSliceCount]
        exact Nat.mul_le_mul_left m hwidth
  | succ fuel ih =>
      by_cases hstop : width ≤ amortizedStopThreshold h Dstar
      · refine ⟨.terminal L hstop, ?_, ?_⟩
        · simp [AmortizedSlicingRun.steps]
        · simp only [AmortizedSlicingRun.terminalPotential,
            AmortizedSlicingRun.terminalSliceCount]
          exact Nat.mul_le_mul_left m hstop
      · have hcontinue :
            amortizedStopThreshold h Dstar < width :=
          Nat.lt_of_not_ge hstop
        let rowCap := amortizedRowCap h width
        by_cases hempty : (L.smallIndices rowCap).card = 0
        · refine
            ⟨.productiveOnly L hcontinue
                (by simpa [rowCap] using hempty), ?_, ?_⟩
          · simp [AmortizedSlicingRun.steps]
          · simp [AmortizedSlicingRun.terminalPotential,
              AmortizedSlicingRun.terminalSliceCount]
        · have hsmall :
              0 < (L.smallIndices rowCap).card :=
            Nat.pos_of_ne_zero hempty
          let widthNext :=
            amortizedChildWidth (amortizedLoss g) h width
          have hwidthNext : 0 < widthNext :=
            amortizedChildWidth_pos
              hh hDstar hloss hcontinue
          have hbudgetRaw :=
            amortizedChildWidth_budget
              hh hDstar hloss hcontinue
          have hbudget :
              2 * widthNext + (2 + 1) * rowCap +
                  (8 * g ^ 4 + 4 * g ^ 4) ≤ width := by
            dsimp [widthNext, rowCap] at hbudgetRaw ⊢
            rw [show 8 * g ^ 4 + 4 * g ^ 4 = 12 * g ^ 4 by ring]
            simpa [amortizedLoss] using hbudgetRaw
          have hDstarNext : Dstar ≤ widthNext :=
            Dstar_le_amortizedChildWidth
              hh hDstar hloss hcontinue
          have hmassNext :
              2 * Rbar.card * (4 * g ^ 2) ≤
                Dhat * widthNext :=
            hpruning.trans
              (Nat.mul_le_mul_left Dhat hDstarNext)
          obtain ⟨next⟩ :=
            refineAllSmallSlicesAdditive
              C L hg (by norm_num : 0 < 2) hwidthNext
              (by simpa [rowCap] using hsmall)
              hadditive hbudget hmassNext hnoCrossbar
          have hwidthFuelNext :
              widthNext ≤
                2 ^ fuel * amortizedStopThreshold h Dstar := by
            have hhalf :=
              two_mul_amortizedChildWidth_le
                (amortizedLoss g) h width
            have hroot :
                width ≤
                  2 * (2 ^ fuel *
                    amortizedStopThreshold h Dstar) := by
              calc
                width ≤
                    2 ^ (Nat.succ fuel) *
                      amortizedStopThreshold h Dstar :=
                  hwidthFuel
                _ = 2 * (2 ^ fuel *
                      amortizedStopThreshold h Dstar) := by
                  rw [pow_succ]
                  ring
            have :
                2 * widthNext ≤
                  2 * (2 ^ fuel *
                    amortizedStopThreshold h Dstar) :=
              hhalf.trans hroot
            omega
          obtain ⟨tail, htail, hterminal⟩ :=
            ih next hwidthFuelNext
          let run :
              AmortizedSlicingRun
                G H A B X P Q Rbar Qbar
                g Dhat h Dstar (m * width) :=
            .refined L hcontinue
              (by simpa [rowCap] using hsmall)
              hh hDstar hloss next tail
          refine ⟨run, ?_, ?_⟩
          · dsimp [run]
            simp only [AmortizedSlicingRun.steps]
            omega
          · simpa [run, AmortizedSlicingRun.terminalPotential,
              AmortizedSlicingRun.terminalSliceCount] using hterminal

/-- The proof-producing logarithmic-depth controller.

It returns either one actual depth carrying enough productive row mass, or
one actual terminal slicing with enough narrow slices.  All constants are
division-free and no semantic recursion hypothesis remains. -/
theorem exists_amortizedSlicingDichotomy
    {V : Type u} {W : Type v}
    [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
    {G : _root_.SimpleGraph V} {H : _root_.SimpleGraph W}
    {A B X : Finset V}
    {P : PerfectPathPacking G A B}
    {Q : PerfectPathPacking G A X}
    {Abar Bbar Sbar Tbar : Finset W}
    {Rbar : PerfectPathPacking H Abar Bbar}
    {Qbar : PathPacking H Sbar Tbar}
    {g Dhat h Dstar m width : ℕ}
    (C : RecursiveSlicingContext
      G H A B X P Q Rbar Qbar Dhat)
    (L : RecursiveSliceLayer
      G H A B X P Q Rbar Qbar
      m width (4 * g ^ 2) Dhat)
    (hg : 0 < g)
    (hh : 0 < h)
    (hDstar : 0 < Dstar)
    (hloss : amortizedLoss g ≤ Dstar)
    (hadditive :
      Rbar.card * (4 * g ^ 2) ≤
        Dhat * (8 * g ^ 4))
    (hpruning :
      2 * Rbar.card * (4 * g ^ 2) ≤
        Dhat * Dstar)
    (hnoCrossbar :
      ¬ Nonempty (Crossbar G A B X (g ^ 2)))
    (hinitial : 0 < m * width)
    (hwidthDepth :
      width ≤ 2 ^ h * amortizedStopThreshold h Dstar) :
    Nonempty
      (AmortizedSlicingDichotomy
        G H A B X P Q Rbar Qbar
        g Dhat h Dstar (m * width)) := by
  obtain ⟨run, hsteps, _⟩ :=
    exists_amortizedSlicingRun
      C L hg hh hDstar hloss hadditive hpruning
      hnoCrossbar h hwidthDepth
  exact run.exists_dichotomy
    hh hDstar hinitial hsteps

end Exponent7
end SimpleGraph

end Lax17Proofs
