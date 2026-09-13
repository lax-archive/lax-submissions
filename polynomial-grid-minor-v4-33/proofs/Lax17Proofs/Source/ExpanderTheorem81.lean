import Lax17Proofs.Source.ExpanderLemma82
import Lax17Proofs.Source.SubcubicExpansion

namespace Lax17Proofs

universe u v w

/-!
# Theorem 8.1 from the expansion-diameter lemma

This file closes the finite, natural-number-scale form of Theorem 8.1 from
`expander.pdf`.

The key point not captured by the broad oracle interfaces in
`ExpanderMinor.lean` is that the paper's algorithm applies Lemma 8.2 only to
first-crossing states where the accumulated side `A` is still below one third
of the host.  The induction below keeps this invariant explicitly.  If a move
causes `A` to cross one third, the first-crossing arithmetic already in
`ExpanderMinor.lean` proves that it crosses into the balanced range, so the
algorithm stops immediately.
-/

namespace SimpleGraph


namespace Theorem81InvariantState

variable {W : Type v} {V : Type u}
variable [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
variable {H : _root_.SimpleGraph W} {G : _root_.SimpleGraph V}
variable {d branchScale : ℕ}

/-- A preterminal first-crossing state: the accumulated side `A` has not yet
reached one third of the host. -/
def BelowOneThird {d r : ℕ}
    (R : Theorem81InvariantState H G d r) : Prop :=
  3 * R.state.A.card < Fintype.card V

/-- The initial state is below the first-crossing threshold as soon as the
host is nonempty. -/
theorem initial_belowOneThird {d r : ℕ}
    (hn : 0 < Fintype.card V) :
    BelowOneThird (initial H G d r) := by
  simpa [BelowOneThird, initial, Theorem81State.initial_A] using hn

/-- In a below-one-third state, the target-size budget prevents the reservoir
from being empty: `A` occupies less than one third of the host, and the active
branch sets occupy at most one third. -/
theorem C_nonempty_of_belowOneThird_targetSmall
    (R : Theorem81InvariantState H G d (branchScale * Nat.log 2 (Fintype.card V)))
    [Fintype H.edgeSet]
    {targetScale : ℕ}
    (hdpos : 0 < d)
    (hbelow : BelowOneThird R)
    (hscale : 3 * d * branchScale ≤ targetScale)
    (hsmall : TargetSmallForHost (V := V) H targetScale) :
    R.state.C.Nonempty := by
  classical
  by_contra hCempty
  rw [Finset.not_nonempty_iff_eq_empty] at hCempty
  have hcoverAB : R.state.A ∪ R.state.B = (Finset.univ : Finset V) := by
    ext x
    have hcover : x ∈ R.state.A ∪ R.state.B ∪ R.state.C := by
      simp [R.state.cover]
    constructor
    · intro _hx
      simp
    · intro _hx
      rw [Finset.mem_union, Finset.mem_union] at hcover
      rcases hcover with hxAB | hxC
      · simpa [Finset.mem_union] using hxAB
      · simp [hCempty] at hxC
  have hABdisj : Disjoint R.state.A R.state.B := R.state.disjoint_A_B
  have hABcard :
      R.state.A.card + R.state.B.card = Fintype.card V := by
    calc
      R.state.A.card + R.state.B.card =
          (R.state.A ∪ R.state.B).card := by
            rw [Finset.card_union_of_disjoint hABdisj]
      _ = Fintype.card V := by
            rw [hcoverAB, Finset.card_univ]
  have hBbudget :
      3 * (d * R.state.B.card) ≤ Fintype.card V :=
    R.state.three_mul_d_mul_B_card_le_of_active_branch_bound
      R.branch_bound
      (R.state.active_branch_budget_of_targetSmall
        R.state.active_card_le_targetComplexity le_rfl hscale hsmall)
  have hBthird : 3 * R.state.B.card ≤ Fintype.card V := by
    have hd1 : 1 ≤ d := Nat.succ_le_of_lt hdpos
    have hB_le_dB : R.state.B.card ≤ d * R.state.B.card := by
      calc
        R.state.B.card = 1 * R.state.B.card := by rw [one_mul]
        _ ≤ d * R.state.B.card := Nat.mul_le_mul_right _ hd1
    exact (Nat.mul_le_mul_left 3 hB_le_dB).trans hBbudget
  have hbelow' : 3 * R.state.A.card < Fintype.card V := hbelow
  have hstrict :
      3 * (R.state.A.card + R.state.B.card) <
        2 * Fintype.card V := by
    omega
  have hnot : ¬ 3 * (R.state.A.card + R.state.B.card) <
        2 * Fintype.card V := by
    rw [hABcard]
    omega
  exact hnot hstrict

/-- A below-one-third progress principle terminates at a first-crossing state.
This is the paper's induction, restricted to reachable preterminal states. -/
theorem exists_firstCrossingTerminal_of_below_progress {d r : ℕ}
    (hprogress :
      ∀ R : Theorem81InvariantState H G d r,
        BelowOneThird R →
        ¬ FirstCrossingTerminal R →
          ∃ R' : Theorem81InvariantState H G d r,
            FirstCrossingTerminal R' ∨
              (Step R R' ∧ BelowOneThird R')) :
    0 < Fintype.card V →
    ∃ R : Theorem81InvariantState H G d r,
      FirstCrossingTerminal R := by
  intro hn
  classical
  let rel := Descends (H := H) (G := G) (d := d) (r := r)
  have hwf : WellFounded rel :=
    descends_wellFounded (H := H) (G := G) (d := d) (r := r)
  have hfrom :
      ∀ R : Theorem81InvariantState H G d r,
        BelowOneThird R →
          ∃ T : Theorem81InvariantState H G d r,
          FirstCrossingTerminal T := by
    intro R hbelow
    refine hwf.induction
      (C := fun R : Theorem81InvariantState H G d r =>
        BelowOneThird R →
          ∃ T : Theorem81InvariantState H G d r,
            FirstCrossingTerminal T) R ?_ hbelow
    intro R ih hbelow
    by_cases hterm : FirstCrossingTerminal R
    · exact ⟨R, hterm⟩
    · rcases hprogress R hbelow hterm with ⟨R', hR' | hR'⟩
      · exact ⟨R', hR'⟩
      · rcases hR' with ⟨hstep, hbelow'⟩
        exact ih R' (step_descends hstep) hbelow'
  exact hfrom (initial H G d r) (initial_belowOneThird hn)

/-- Inserting a new branch set does not change the accumulated separator side,
so it preserves the below-one-third invariant. -/
theorem insertVertex_step_belowOneThird {d r : ℕ}
    (R : Theorem81InvariantState H G d r)
    {i : W} (hi : i ∉ R.state.active) {Y frontier' : Finset V}
    (hYsubsetC : Y ⊆ R.state.C)
    (hYnonempty : Y.Nonempty)
    (hYconnected : (G.induce {v : V | v ∈ Y}).Connected)
    (hadj :
      ∀ j : W, j ∈ R.state.active → H.Adj i j →
        ∃ x ∈ Y, ∃ y ∈ R.state.model.branchSet j, G.Adj x y)
    (hfrontier' :
      IsRelativeExternalNeighborhood G R.state.A
        (R.state.C \ Y) frontier')
    (hYcard : Y.card ≤ r)
    (hbelow : BelowOneThird R) :
    Step R
        (R.insertVertex hi hYsubsetC hYnonempty hYconnected
          hadj hfrontier' hYcard) ∧
      BelowOneThird
        (R.insertVertex hi hYsubsetC hYnonempty hYconnected
          hadj hfrontier' hYcard) := by
  constructor
  · exact Step.insert R hi hYsubsetC hYnonempty hYconnected
      hadj hfrontier' hYcard
  · simpa [BelowOneThird, Theorem81InvariantState.insertVertex,
      Theorem81State.insertVertex] using hbelow

/-- Moving a Lemma-8.2 low-expansion reservoir set into `A` either reaches the
first crossing, in which case the half-reservoir bound gives the upper balance
inequality, or it remains below one third. -/
theorem moveReservoirSetToA_terminal_or_below {d r : ℕ}
    (R : Theorem81InvariantState H G d r)
    {U frontier' frontierU : Finset V}
    (hUsubsetC : U ⊆ R.state.C)
    (hUnonempty : U.Nonempty)
    (hUhalf : 2 * U.card ≤ R.state.C.card)
    (hfrontier' :
      IsRelativeExternalNeighborhood G (R.state.A ∪ U)
        (R.state.C \ U) frontier')
    (hfrontierU :
      IsRelativeExternalNeighborhood G U (R.state.C \ U) frontierU)
    (hUsmall : d * frontierU.card ≤ U.card)
    (hbelow : BelowOneThird R) :
    FirstCrossingTerminal
        (R.moveReservoirSetToA hUsubsetC hfrontier'
          hfrontierU hUsmall) ∨
      (Step R
          (R.moveReservoirSetToA hUsubsetC hfrontier'
            hfrontierU hUsmall) ∧
        BelowOneThird
          (R.moveReservoirSetToA hUsubsetC hfrontier'
            hfrontierU hUsmall)) := by
  let R' :=
    R.moveReservoirSetToA hUsubsetC hfrontier' hfrontierU hUsmall
  have hstep : Step R R' :=
    Step.moveReservoir R hUsubsetC hUnonempty hfrontier'
      hfrontierU hUsmall
  have hbal : 3 * R'.state.A.card ≤ 2 * Fintype.card V := by
    have hbal0 :=
      R.A_union_reservoir_subset_balanced_of_below_one_third
        hUsubsetC hUhalf hbelow
    simpa [R', Theorem81InvariantState.moveReservoirSetToA,
      Theorem81State.moveReservoirSetToA] using hbal0
  by_cases hcross : Fintype.card V ≤ 3 * R'.state.A.card
  · left
    exact Or.inr ⟨hcross, hbal⟩
  · right
    refine ⟨hstep, ?_⟩
    exact Nat.lt_of_not_ge hcross

/-- The target-size budget makes each active branch set small enough that
dumping a stranded branch into `A` either gives a balanced first crossing or
keeps `A` below one third. -/
theorem moveActiveBranchToA_terminal_or_below
    (R : Theorem81InvariantState H G d
      ((15 * d) * Nat.log 2 (Fintype.card V)))
    [Fintype H.edgeSet]
    {i : W} (hi : i ∈ R.state.active)
    (hno :
      ∀ ⦃x c : V⦄, x ∈ R.state.model.branchSet i →
        c ∈ R.state.C → ¬ G.Adj c x)
    {targetScale : ℕ}
    (hdpos : 0 < d)
    (hscale : 3 * d * (15 * d) ≤ targetScale)
    (hsmall : TargetSmallForHost (V := V) H targetScale)
    (hbelow : BelowOneThird R) :
    FirstCrossingTerminal
        (R.moveActiveBranchToA_noReservoirNeighbor hi hno) ∨
      (Step R (R.moveActiveBranchToA_noReservoirNeighbor hi hno) ∧
        BelowOneThird
          (R.moveActiveBranchToA_noReservoirNeighbor hi hno)) := by
  let R' := R.moveActiveBranchToA_noReservoirNeighbor hi hno
  have hstep : Step R R' := Step.moveActive R hi hno
  have hscaleBranch : 3 * (15 * d) ≤ targetScale := by
    have hd1 : 1 ≤ d := Nat.succ_le_of_lt hdpos
    calc
      3 * (15 * d) = 3 * 1 * (15 * d) := by ring
      _ ≤ 3 * d * (15 * d) := by
        exact Nat.mul_le_mul_right (15 * d) (Nat.mul_le_mul_left 3 hd1)
      _ ≤ targetScale := hscale
  have hbal : 3 * R'.state.A.card ≤ 2 * Fintype.card V := by
    have hbal0 :=
      R.A_union_branch_balanced_of_targetSmall
        hi le_rfl hscaleBranch hsmall hbelow
    simpa [R', Theorem81InvariantState.moveActiveBranchToA_noReservoirNeighbor,
      Theorem81State.moveActiveBranchToA_noReservoirNeighbor,
      Theorem81State.moveActiveBranchToA] using hbal0
  by_cases hcross : Fintype.card V ≤ 3 * R'.state.A.card
  · left
    exact Or.inr ⟨hcross, hbal⟩
  · right
    refine ⟨hstep, ?_⟩
    exact Nat.lt_of_not_ge hcross

end Theorem81InvariantState

/-- The fixed-constant subcubic form of Theorem 8.1.

This is the self-contained proof of the paper's iterative argument after the
standard reduction to maximum degree three.  Lemma 8.2 is applied only to
states whose current side `A` is still below one third of the host; when a
low-expansion or stranded-branch move crosses that threshold, the first
crossing arithmetic immediately produces the balanced separator certificate. -/
theorem expanderMinorTheoremAtSubcubic_explicit
    {separatorScale targetScale n₀ : ℕ}
    (hsepPos : 0 < separatorScale)
    (hn₀ : 2 ≤ n₀)
    (hscale : 3 * separatorScale * (15 * separatorScale) ≤ targetScale) :
    ExpanderMinorTheoremAtSubcubic.{u, v}
      separatorScale targetScale n₀ := by
  intro V _ _ W _ _ G _ H _ _ hmax hn hsmall
  classical
  let r := (15 * separatorScale) * Nat.log 2 (Fintype.card V)
  have hnpos : 0 < Fintype.card V := by
    omega
  have hlog : 0 < Nat.log 2 (Fintype.card V) := by
    rw [Nat.log_pos_iff]
    exact ⟨hn₀.trans hn, Nat.one_lt_two⟩
  have hprogress :
      ∀ R : Theorem81InvariantState H G separatorScale r,
        Theorem81InvariantState.BelowOneThird R →
        ¬ Theorem81InvariantState.FirstCrossingTerminal R →
          ∃ R' : Theorem81InvariantState H G separatorScale r,
            Theorem81InvariantState.FirstCrossingTerminal R' ∨
              (Theorem81InvariantState.Step R R' ∧
                Theorem81InvariantState.BelowOneThird R') := by
    intro R hbelow hnot
    have hC : R.state.C.Nonempty :=
      Theorem81InvariantState.C_nonempty_of_belowOneThird_targetSmall
        (R := R) (branchScale := 15 * separatorScale)
        (targetScale := targetScale)
        hsepPos hbelow hscale hsmall
    rcases
        Theorem81InvariantState.exists_inactive_of_not_firstCrossingTerminal
          (R := R) hnot with
      ⟨i, hi⟩
    rcases theorem81_lowExpansion_or_reservoirDiameter_log_bound
        (V := V) (W := W) (G := G) (H := H)
        (d := separatorScale) (r := r)
        hsepPos hlog R hC with hlow | hdiam
    · rcases hlow with
        ⟨U, frontierU, hUsubsetC, hUnonempty, hUhalf,
          hfrontierU, hUsmall⟩
      let frontier' : Finset V :=
        relativeExternalNeighborhood G (R.state.A ∪ U) (R.state.C \ U)
      have hfrontier' :
          IsRelativeExternalNeighborhood G (R.state.A ∪ U)
            (R.state.C \ U) frontier' := by
        exact isRelativeExternalNeighborhood_relativeExternalNeighborhood
          G (R.state.A ∪ U) (R.state.C \ U)
      refine ⟨R.moveReservoirSetToA hUsubsetC hfrontier'
        hfrontierU hUsmall, ?_⟩
      exact
        Theorem81InvariantState.moveReservoirSetToA_terminal_or_below
          R hUsubsetC hUnonempty hUhalf hfrontier'
          hfrontierU hUsmall hbelow
    · rcases hdiam with ⟨hCnonempty, m, hdiamBound, hm⟩
      let N := activeNeighborFinset H R.state.active i
      by_cases hNnonempty : N.Nonempty
      · by_cases hcontacts :
          ∀ j : W, j ∈ N →
            Theorem81InvariantState.BranchHasReservoirNeighbor R j
        · rcases
            Theorem81InvariantState.exists_contactSet_of_all_branchHasReservoirNeighbor
              (R := R) (i := i) hcontacts with
            ⟨Cts, hCtsC, hCtsCard, hCtsContacts⟩
          have hCtsNonempty : Cts.Nonempty := by
            rcases hNnonempty with ⟨j, hjN⟩
            rcases hCtsContacts j hjN with
              ⟨c, hcCts, _x, _hx, _hcx⟩
            exact ⟨c, hcCts⟩
          have hCtsCard3 : Cts.card ≤ 3 :=
            hCtsCard.trans
              (activeNeighborFinset_card_le_three_of_subcubic
                (H := H) (I := R.state.active) (i := i) hmax)
          have hCtsFit : Cts.card * (m + 1) ≤ r := by
            have hm' :
                m ≤ 4 * (separatorScale *
                  Nat.log 2 (Fintype.card V)) := by
              simpa [Nat.mul_assoc] using hm
            have hprodPos :
                1 ≤ separatorScale * Nat.log 2 (Fintype.card V) :=
              Nat.succ_le_of_lt (Nat.mul_pos hsepPos hlog)
            have hthree :
                3 * (m + 1) ≤
                  15 * (separatorScale *
                    Nat.log 2 (Fintype.card V)) := by
              omega
            calc
              Cts.card * (m + 1) ≤ 3 * (m + 1) := by
                exact Nat.mul_le_mul_right (m + 1) hCtsCard3
              _ ≤ 15 * (separatorScale *
                    Nat.log 2 (Fintype.card V)) := hthree
              _ = r := by
                simp [r, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
          rcases
              Theorem81InvariantState.connectedReservoirHull_of_reservoirDiameterBound
                (R := R) (Cts := Cts) (m := m)
                hdiamBound hCtsC hCtsNonempty hCtsFit with
            ⟨Y, frontier', hCtsY, hYsubsetC, hYnonempty,
              hYconnected, hfrontier', hYcard⟩
          have hadj :
              ∀ j : W, j ∈ R.state.active → H.Adj i j →
                ∃ x ∈ Y, ∃ y ∈ R.state.model.branchSet j,
                  G.Adj x y :=
            Theorem81InvariantState.adjacency_of_contactSet
              (R := R) (i := i) (Cts := Cts) (Y := Y)
              hCtsContacts hCtsY
          refine ⟨R.insertVertex hi hYsubsetC hYnonempty hYconnected
            hadj hfrontier' hYcard, Or.inr ?_⟩
          exact
            Theorem81InvariantState.insertVertex_step_belowOneThird
              R hi hYsubsetC hYnonempty hYconnected hadj
              hfrontier' hYcard hbelow
        · push Not at hcontacts
          rcases hcontacts with ⟨j, hjN, hnoBranch⟩
          rcases (mem_activeNeighborFinset).1 hjN with
            ⟨hjactive, _hij⟩
          have hno :
              ∀ ⦃x c : V⦄, x ∈ R.state.model.branchSet j →
                c ∈ R.state.C → ¬ G.Adj c x :=
            Theorem81InvariantState.noReservoirNeighbor_of_not_branchHasReservoirNeighbor
              hnoBranch
          refine ⟨R.moveActiveBranchToA_noReservoirNeighbor hjactive hno,
            ?_⟩
          exact
            Theorem81InvariantState.moveActiveBranchToA_terminal_or_below
              R hjactive hno hsepPos hscale hsmall hbelow
      · rcases hCnonempty with ⟨c, hc⟩
        let Y : Finset V := {c}
        let frontier' : Finset V :=
          relativeExternalNeighborhood G R.state.A (R.state.C \ Y)
        have hYsubsetC : Y ⊆ R.state.C := by
          intro x hx
          have hxc : x = c := by simpa [Y] using hx
          simpa [hxc] using hc
        have hYnonempty : Y.Nonempty := by
          exact ⟨c, by simp [Y]⟩
        have hYconnected :
            (G.induce {v : V | v ∈ Y}).Connected := by
          haveI : Nonempty {v : V | v ∈ Y} :=
            ⟨⟨c, by simp [Y]⟩⟩
          haveI : Subsingleton {v : V | v ∈ Y} := by
            constructor
            intro x y
            apply Subtype.ext
            have hx : x.1 = c := by simpa [Y] using x.2
            have hy : y.1 = c := by simpa [Y] using y.2
            exact hx.trans hy.symm
          exact _root_.SimpleGraph.Connected.of_subsingleton
        have hnoActiveNeighbor :
            ∀ j : W, j ∈ R.state.active → ¬ H.Adj i j := by
          intro j hjactive hij
          exact hNnonempty
            ⟨j, (mem_activeNeighborFinset).2 ⟨hjactive, hij⟩⟩
        have hadj :
            ∀ j : W, j ∈ R.state.active → H.Adj i j →
              ∃ x ∈ Y, ∃ y ∈ R.state.model.branchSet j,
                G.Adj x y := by
          intro j hj hij
          exact False.elim (hnoActiveNeighbor j hj hij)
        have hfrontier' :
            IsRelativeExternalNeighborhood G R.state.A
              (R.state.C \ Y) frontier' := by
          exact isRelativeExternalNeighborhood_relativeExternalNeighborhood
            G R.state.A (R.state.C \ Y)
        have hYcard : Y.card ≤ r := by
          have hrpos : 0 < r := by
            exact Nat.mul_pos (Nat.mul_pos (by norm_num) hsepPos) hlog
          have hr1 : 1 ≤ r := Nat.succ_le_of_lt hrpos
          simpa [Y] using hr1
        refine ⟨R.insertVertex hi hYsubsetC hYnonempty hYconnected
          hadj hfrontier' hYcard, Or.inr ?_⟩
        exact
          Theorem81InvariantState.insertVertex_step_belowOneThird
            R hi hYsubsetC hYnonempty hYconnected hadj
            hfrontier' hYcard hbelow
  rcases
      Theorem81InvariantState.exists_firstCrossingTerminal_of_below_progress
        (H := H) (G := G) (d := separatorScale) (r := r)
        hprogress hnpos with
    ⟨R, hR⟩
  exact R.separator_or_minor_of_first_crossing
    (branchScale := 15 * separatorScale) (targetScale := targetScale)
    le_rfl hscale hsmall hR

/-- Full fixed-constant Theorem 8.1, using the formal subcubic expansion
reduction and the subcubic proof above. -/
theorem expanderMinorTheoremAt_explicit
    {separatorScale : ℕ} (hsepPos : 0 < separatorScale) :
    ExpanderMinorTheoremAt.{u, v} separatorScale
      ((3 * separatorScale * (15 * separatorScale)) * 8) 2 := by
  exact
    expanderMinorTheoremAt_of_subcubicExpansion
      (separatorScale := separatorScale)
      (subcubicTargetScale := 3 * separatorScale * (15 * separatorScale))
      (targetScale := (3 * separatorScale * (15 * separatorScale)) * 8)
      (n₀ := 2) (complexityScale := 8)
      le_rfl
      subcubicMinorExpansionProvider
      (expanderMinorTheoremAtSubcubic_explicit
        hsepPos (by norm_num) le_rfl)

/-- Theorem 8.1 as a theorem family: every positive separator scale has an
explicit target-size denominator and threshold for the separator/minor
alternative. -/
theorem expanderMinorTheorem_explicit :
    ExpanderMinorTheorem.{u, v} := by
  intro separatorScale hsepPos
  refine ⟨(3 * separatorScale * (15 * separatorScale)) * 8, 2, ?_, ?_⟩
  · exact Nat.mul_pos
      (Nat.mul_pos
        (Nat.mul_pos (by norm_num) hsepPos)
        (Nat.mul_pos (by norm_num) hsepPos))
      (by norm_num)
  · exact expanderMinorTheoremAt_explicit hsepPos

end SimpleGraph

end Lax17Proofs
