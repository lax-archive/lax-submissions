import Lax17Proofs.Source.Exponent8.ThreeRoundRecursion

namespace Lax17Proofs

/-!
# Explicit parameters for the exponent-eight-and-a-half experiment

This module gives an actual inhabitant of `ThreeRoundParameters` under the
Section 4 bounds

`N <= 64 * g^6`, `Dhat = 32 * g^4`, and `2 <= g`.

The counts are chosen as

`64 g^2 f L, 32 g^2 f^2 L, 16 g^2 f^3 L, 8 g^2 f^4 L`,

where `f = sqrt(g) + 1` and `L = log_2(g) + 1`.  The widths are defined by
the three exact refinement recurrences, starting from `16 g^4`.  No
asymptotic notation or division is used.
-/

namespace SimpleGraph
namespace Exponent8

def e8Fanout (g : ℕ) : ℕ := Nat.sqrt g + 1
def e8LogFactor (g : ℕ) : ℕ := Nat.log 2 g + 1

def e8M0 (g : ℕ) : ℕ :=
  64 * g ^ 2 * e8Fanout g * e8LogFactor g
def e8M1 (g : ℕ) : ℕ :=
  32 * g ^ 2 * (e8Fanout g) ^ 2 * e8LogFactor g
def e8M2 (g : ℕ) : ℕ :=
  16 * g ^ 2 * (e8Fanout g) ^ 3 * e8LogFactor g
def e8M3 (g : ℕ) : ℕ :=
  8 * g ^ 2 * (e8Fanout g) ^ 4 * e8LogFactor g

def e8Cap0 (g : ℕ) : ℕ := 64 * g ^ 5 * e8Fanout g
def e8Cap1 (g : ℕ) : ℕ := 128 * g ^ 5
def e8Cap2 (g : ℕ) : ℕ := 256 * g ^ 4 * e8Fanout g

def e8W3 (g : ℕ) : ℕ := 16 * g ^ 4
def e8W2 (g : ℕ) : ℕ :=
  2 * (e8Fanout g * e8W3 g +
    (e8Fanout g + 1) * e8Cap2 g + 4 * g ^ 4)
def e8W1 (g : ℕ) : ℕ :=
  2 * (e8Fanout g * e8W2 g +
    (e8Fanout g + 1) * e8Cap1 g + 4 * g ^ 4)
def e8W0 (g : ℕ) : ℕ :=
  2 * (e8Fanout g * e8W1 g +
    (e8Fanout g + 1) * e8Cap0 g + 4 * g ^ 4)

def e8AssemblyMass (N g : ℕ) : ℕ :=
  32 * N * g ^ 2 * e8LogFactor g

def e8Constant : ℕ := 536870912

namespace ThreeRoundParameters

theorem e8_sqrt_pos {g : ℕ} (hg : 2 ≤ g) :
    0 < Nat.sqrt g := by
  rw [Nat.sqrt_pos]
  omega

theorem e8_fanout_le_two_sqrt {g : ℕ} (hg : 2 ≤ g) :
    e8Fanout g ≤ 2 * Nat.sqrt g := by
  unfold e8Fanout
  have hs := e8_sqrt_pos hg
  omega

theorem e8_g_le_fanout_sq (g : ℕ) :
    g ≤ e8Fanout g * e8Fanout g := by
  exact Nat.le_of_lt (Nat.lt_succ_sqrt g)

theorem e8_sqrt_sq_le (g : ℕ) :
    Nat.sqrt g * Nat.sqrt g ≤ g :=
  Nat.sqrt_le g

theorem e8_fanout_mul_sqrt_le_two_g {g : ℕ} (hg : 2 ≤ g) :
    e8Fanout g * Nat.sqrt g ≤ 2 * g := by
  calc
    e8Fanout g * Nat.sqrt g ≤
        (2 * Nat.sqrt g) * Nat.sqrt g :=
      Nat.mul_le_mul_right _ (e8_fanout_le_two_sqrt hg)
    _ = 2 * (Nat.sqrt g * Nat.sqrt g) := by ring
    _ ≤ 2 * g := Nat.mul_le_mul_left 2 (Nat.sqrt_le g)

theorem e8_fanout_succ_mul_le_six_g {g : ℕ} (hg : 2 ≤ g) :
    (e8Fanout g + 1) * e8Fanout g ≤ 6 * g := by
  have hf := e8_fanout_le_two_sqrt hg
  have hsle : Nat.sqrt g ≤ g := Nat.sqrt_le_self g
  have hsq := Nat.sqrt_le g
  nlinarith

theorem e8W2_le {g : ℕ} (hg : 2 ≤ g) :
    e8W2 g ≤ 4096 * g ^ 5 := by
  have hf : e8Fanout g ≤ 2 * g :=
    (e8_fanout_le_two_sqrt hg).trans
      (Nat.mul_le_mul_left 2 (Nat.sqrt_le_self g))
  have hff := e8_fanout_succ_mul_le_six_g hg
  have hcoef :
      2 * (16 * e8Fanout g +
        256 * ((e8Fanout g + 1) * e8Fanout g) + 4) ≤
        4096 * g := by
    omega
  calc
    e8W2 g =
        g ^ 4 *
          (2 * (16 * e8Fanout g +
            256 * ((e8Fanout g + 1) * e8Fanout g) + 4)) := by
      simp [e8W2, e8W3, e8Cap2]
      ring
    _ ≤ g ^ 4 * (4096 * g) :=
      Nat.mul_le_mul_left _ hcoef
    _ = 4096 * g ^ 5 := by ring

theorem e8W1_le {g : ℕ} (hg : 2 ≤ g) :
    e8W1 g ≤ 32768 * g ^ 5 * Nat.sqrt g := by
  have hf := e8_fanout_le_two_sqrt hg
  have hs := e8_sqrt_pos hg
  have hcoef :
      2 * (4096 * e8Fanout g +
        128 * (e8Fanout g + 1) + 4) ≤
        32768 * Nat.sqrt g := by
    omega
  have hg4g5 : 4 * g ^ 4 ≤ 4 * g ^ 5 := by
    have hg1 : 1 ≤ g := by omega
    calc
      4 * g ^ 4 = (4 * g ^ 4) * 1 := by ring
      _ ≤ (4 * g ^ 4) * g := Nat.mul_le_mul_left _ hg1
      _ = 4 * g ^ 5 := by ring
  calc
    e8W1 g =
        2 * (e8Fanout g * e8W2 g +
          (e8Fanout g + 1) * e8Cap1 g + 4 * g ^ 4) := rfl
    _ ≤
        2 * (e8Fanout g * (4096 * g ^ 5) +
          (e8Fanout g + 1) * (128 * g ^ 5) + 4 * g ^ 5) := by
      gcongr
      · exact e8W2_le hg
      · simp [e8Cap1]
    _ =
        g ^ 5 * (2 * (4096 * e8Fanout g +
          128 * (e8Fanout g + 1) + 4)) := by ring
    _ ≤ g ^ 5 * (32768 * Nat.sqrt g) :=
      Nat.mul_le_mul_left _ hcoef
    _ = 32768 * g ^ 5 * Nat.sqrt g := by ring

theorem e8W0_le {g : ℕ} (hg : 2 ≤ g) :
    e8W0 g ≤ 262144 * g ^ 6 := by
  have hfs := e8_fanout_mul_sqrt_le_two_g hg
  have hff := e8_fanout_succ_mul_le_six_g hg
  have hcoef :
      2 * (32768 * (e8Fanout g * Nat.sqrt g) +
        64 * ((e8Fanout g + 1) * e8Fanout g) + 4) ≤
        262144 * g := by
    omega
  have hg4g5 : 4 * g ^ 4 ≤ 4 * g ^ 5 := by
    have hg1 : 1 ≤ g := by omega
    calc
      4 * g ^ 4 = (4 * g ^ 4) * 1 := by ring
      _ ≤ (4 * g ^ 4) * g := Nat.mul_le_mul_left _ hg1
      _ = 4 * g ^ 5 := by ring
  calc
    e8W0 g =
        2 * (e8Fanout g * e8W1 g +
          (e8Fanout g + 1) * e8Cap0 g + 4 * g ^ 4) := rfl
    _ ≤
        2 * (e8Fanout g *
            (32768 * g ^ 5 * Nat.sqrt g) +
          (e8Fanout g + 1) *
            (64 * g ^ 5 * e8Fanout g) + 4 * g ^ 5) := by
      gcongr
      · exact e8W1_le hg
      · simp [e8Cap0]
    _ =
        g ^ 5 *
          (2 * (32768 * (e8Fanout g * Nat.sqrt g) +
            64 * ((e8Fanout g + 1) * e8Fanout g) + 4)) := by
      ring
    _ ≤ g ^ 5 * (262144 * g) :=
      Nat.mul_le_mul_left _ hcoef
    _ = 262144 * g ^ 6 := by ring

theorem e8M0_le {g : ℕ} (hg : 2 ≤ g) :
    e8M0 g ≤
      128 * g ^ 2 * Nat.sqrt g * e8LogFactor g := by
  calc
    e8M0 g =
        64 * g ^ 2 * e8Fanout g * e8LogFactor g := rfl
    _ ≤
        64 * g ^ 2 * (2 * Nat.sqrt g) * e8LogFactor g := by
      gcongr
      exact e8_fanout_le_two_sqrt hg
    _ = 128 * g ^ 2 * Nat.sqrt g * e8LogFactor g := by
      ring

/-- Explicit inhabitance of every numerical field in
`ThreeRoundParameters`. -/
noncomputable def explicitExponentEightParameters
    (g N Dhat : ℕ)
    (hg : 2 ≤ g)
    (hN : N ≤ 64 * g ^ 6)
    (hDhat : Dhat = 32 * g ^ 4) :
    ThreeRoundParameters g N Dhat := by
  let f := e8Fanout g
  let ell := e8LogFactor g
  have hfpos : 0 < f := by
    dsimp [f, e8Fanout]
    omega
  have hspos : 0 < Nat.sqrt g := e8_sqrt_pos hg
  have hellpos : 0 < ell := by
    dsimp [ell, e8LogFactor]
    omega
  have hgf2 : g ≤ f ^ 2 := by
    simpa [pow_two] using e8_g_le_fanout_sq g
  have hg2f4 : g ^ 2 ≤ f ^ 4 := by
    calc
      g ^ 2 ≤ (f ^ 2) ^ 2 := Nat.pow_le_pow_left hgf2 2
      _ = f ^ 4 := by ring
  refine
    { C := e8Constant
      logExp := 1
      fanout := f
      m0 := e8M0 g
      m1 := e8M1 g
      m2 := e8M2 g
      m3 := e8M3 g
      w0 := e8W0 g
      w1 := e8W1 g
      w2 := e8W2 g
      w3 := e8W3 g
      cap0 := e8Cap0 g
      cap1 := e8Cap1 g
      cap2 := e8Cap2 g
      assemblyMass := e8AssemblyMass N g
      fanout_eq := rfl
      g_le_fanout_sq := by
        simpa [f] using e8_g_le_fanout_sq g
      g_at_least_two := hg
      Dhat_pos := by
        rw [hDhat]
        positivity
      theorem411_scale := by
        rw [hDhat]
        have hg1 : 1 ≤ g := by omega
        nlinarith [Nat.pow_le_pow_left hg1 2]
      counts_pos := by
        simp only [e8M0, e8M1, e8M2, e8M3]
        exact ⟨by positivity, by positivity, by positivity, by positivity⟩
      widths_pos := by
        simp only [e8W0, e8W1, e8W2, e8W3]
        exact ⟨by positivity, by positivity, by positivity, by positivity⟩
      count01 := by
        simp [e8M0, e8M1, f]
        ring_nf
        exact le_rfl
      count12 := by
        simp [e8M1, e8M2, f]
        ring_nf
        exact le_rfl
      count23 := by
        simp [e8M2, e8M3, f]
        ring_nf
        exact le_rfl
      refineBudget01 := by
        simp [e8W0, e8W1, e8Cap0, f]
      refineBudget12 := by
        simp [e8W1, e8W2, e8Cap1, f]
      refineBudget23 := by
        simp [e8W2, e8W3, e8Cap2, f]
      largeMass0 := by
        have hN' :
            64 * N * g ^ 2 * ell ≤
              4096 * g ^ 8 * ell := by
          calc
            64 * N * g ^ 2 * ell ≤
                64 * (64 * g ^ 6) * g ^ 2 * ell := by
              gcongr
            _ = 4096 * g ^ 8 * ell := by ring
        have hcap :
            4096 * g ^ 8 * ell ≤
              e8M0 g * e8Cap0 g := by
          calc
            4096 * g ^ 8 * ell =
                (4096 * g ^ 7 * ell) * g := by ring
            _ ≤ (4096 * g ^ 7 * ell) * (f ^ 2) :=
              Nat.mul_le_mul_left _ hgf2
            _ = e8M0 g * e8Cap0 g := by
              simp [e8M0, e8Cap0, f, ell]
              ring
        calc
          2 * e8AssemblyMass N g =
              64 * N * g ^ 2 * ell := by
            simp [e8AssemblyMass, ell]
            ring
          _ ≤ e8M0 g * e8Cap0 g := hN'.trans hcap
      largeMass1 := by
        have hN' :
            64 * N * g ^ 2 * ell ≤
              4096 * g ^ 8 * ell := by
          calc
            64 * N * g ^ 2 * ell ≤
                64 * (64 * g ^ 6) * g ^ 2 * ell := by
              gcongr
            _ = 4096 * g ^ 8 * ell := by ring
        have hcap :
            4096 * g ^ 8 * ell ≤
              e8M1 g * e8Cap1 g := by
          calc
            4096 * g ^ 8 * ell =
                (4096 * g ^ 7 * ell) * g := by ring
            _ ≤ (4096 * g ^ 7 * ell) * (f ^ 2) :=
              Nat.mul_le_mul_left _ hgf2
            _ = e8M1 g * e8Cap1 g := by
              simp [e8M1, e8Cap1, f, ell]
              ring
        calc
          2 * e8AssemblyMass N g =
              64 * N * g ^ 2 * ell := by
            simp [e8AssemblyMass, ell]
            ring
          _ ≤ e8M1 g * e8Cap1 g := hN'.trans hcap
      largeMass2 := by
        have hN' :
            64 * N * g ^ 2 * ell ≤
              4096 * g ^ 8 * ell := by
          calc
            64 * N * g ^ 2 * ell ≤
                64 * (64 * g ^ 6) * g ^ 2 * ell := by
              gcongr
            _ = 4096 * g ^ 8 * ell := by ring
        have hcap :
            4096 * g ^ 8 * ell ≤
              e8M2 g * e8Cap2 g := by
          calc
            4096 * g ^ 8 * ell =
                (4096 * g ^ 6 * ell) * g ^ 2 := by ring
            _ ≤ (4096 * g ^ 6 * ell) * f ^ 4 :=
              Nat.mul_le_mul_left _ hg2f4
            _ = e8M2 g * e8Cap2 g := by
              simp [e8M2, e8Cap2, f, ell]
              ring
        calc
          2 * e8AssemblyMass N g =
              64 * N * g ^ 2 * ell := by
            simp [e8AssemblyMass, ell]
            ring
          _ ≤ e8M2 g * e8Cap2 g := hN'.trans hcap
      finalSliceCount := by
        calc
          8 * g ^ 4 * (Nat.log 2 g + 1) =
              (8 * g ^ 2 * ell) * g ^ 2 := by
            simp [ell, e8LogFactor]
            ring
          _ ≤ (8 * g ^ 2 * ell) * f ^ 4 :=
            Nat.mul_le_mul_left _ hg2f4
          _ = e8M3 g := by
            simp [e8M3, f, ell]
            ring
      finalPruning := by
        rw [hDhat]
        calc
          2 * N * (4 * g ^ 2) ≤
              2 * (64 * g ^ 6) * (4 * g ^ 2) := by
            gcongr
          _ = (32 * g ^ 4) * e8W3 g := by
            simp [e8W3]
            ring
      localCost := by
        have hm0 := e8M0_le hg
        have hw0 := e8W0_le hg
        have hm0w0 :
            e8M0 g * e8W0 g ≤
              33554432 * g ^ 8 * Nat.sqrt g *
                e8LogFactor g := by
          calc
            e8M0 g * e8W0 g ≤
                (128 * g ^ 2 * Nat.sqrt g * e8LogFactor g) *
                  (262144 * g ^ 6) :=
              Nat.mul_le_mul hm0 hw0
            _ =
                33554432 * g ^ 8 * Nat.sqrt g *
                  e8LogFactor g := by ring
        have hfactor :
            1 ≤ g ^ 2 * Nat.sqrt g * e8LogFactor g := by
          have hpositive :
              0 < g ^ 2 * Nat.sqrt g * e8LogFactor g := by
            apply Nat.mul_pos
            · exact Nat.mul_pos (by positivity) hspos
            · simpa [ell] using hellpos
          omega
        have hNsmall :
            N ≤ 64 * g ^ 8 * Nat.sqrt g * e8LogFactor g := by
          calc
            N ≤ 64 * g ^ 6 := hN
            _ = (64 * g ^ 6) * 1 := by ring
            _ ≤ (64 * g ^ 6) *
                (g ^ 2 * Nat.sqrt g * e8LogFactor g) :=
              Nat.mul_le_mul_left _ hfactor
            _ = 64 * g ^ 8 * Nat.sqrt g *
                e8LogFactor g := by ring
        have hm0N :
            e8M0 g * N ≤
              8192 * g ^ 8 * Nat.sqrt g * e8LogFactor g := by
          calc
            e8M0 g * N ≤
                (128 * g ^ 2 * Nat.sqrt g * e8LogFactor g) *
                  (64 * g ^ 6) :=
              Nat.mul_le_mul hm0 hN
            _ =
                8192 * g ^ 8 * Nat.sqrt g *
                  e8LogFactor g := by ring
        have hsuccN :
            (e8M0 g + 1) * N ≤
              8256 * g ^ 8 * Nat.sqrt g * e8LogFactor g := by
          calc
            (e8M0 g + 1) * N = e8M0 g * N + N := by ring
            _ ≤
                8192 * g ^ 8 * Nat.sqrt g * e8LogFactor g +
                  64 * g ^ 8 * Nat.sqrt g * e8LogFactor g :=
              Nat.add_le_add hm0N hNsmall
            _ =
                8256 * g ^ 8 * Nat.sqrt g *
                  e8LogFactor g := by ring
        calc
          8 * (e8M0 g * e8W0 g + (e8M0 g + 1) * N) ≤
              8 * (33554432 * g ^ 8 * Nat.sqrt g *
                e8LogFactor g +
                8256 * g ^ 8 * Nat.sqrt g *
                  e8LogFactor g) := by
            gcongr
          _ =
              (8 * (33554432 + 8256)) *
                (g ^ 8 * Nat.sqrt g * e8LogFactor g) := by
            ring
          _ ≤
              e8Constant *
                (g ^ 8 * Nat.sqrt g * e8LogFactor g) :=
            Nat.mul_le_mul_right _
              (by
                unfold e8Constant
                decide)
          _ =
              e8Constant * g ^ 8 * Nat.sqrt g *
                e8LogFactor g := by ring
          _ =
              exponentEightLocalThreshold e8Constant 1 g := by
            simp [exponentEightLocalThreshold, e8LogFactor] }

end ThreeRoundParameters
end Exponent8
end SimpleGraph

end Lax17Proofs
