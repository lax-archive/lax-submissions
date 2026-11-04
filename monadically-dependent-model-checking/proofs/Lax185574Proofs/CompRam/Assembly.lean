import Lax185574Proofs.CompRam.SizeEnd
import Lax185574Proofs.CompRam.PolyBound
import Lax185574Proofs.RamSwitch
import Lax185574.FarComposition
import Lax185574.Restriction
import Lax185574.RankShift
import Lax185574.CanonicalForm

/-!
The assembly of lem:compose from a glue program.

`GlueHyp`: for an input shift `sI` and all literal exponents and every
`D ≥ sI + 4`, some glue program meets `GlueSpec` with the query shift
`D + 20`. `far_of_glue`: from `GlueHyp` and the three cited algorithms
(lem:restrict, lem:shift, obs:canonical), the statement of lem:compose.
The composite is the loop driver of the glue program and the callee
`switch R S C D`. Soundness is `comp_sound`, the run is `comp_run` with
the sizes of `size_ok`. All sizes are polynomial in the length of the
input, with a degree that depends on `k` and `q` (`PB`), and the entries
enter only through the admissibility of the input, whose exponent
`2 E + 2` is fixed before `k` and `q`.
-/

namespace Lax185574Proofs.CompRam

open Lax808846.Ram Lax808846.RamComputes Lax185574.Computing Lax185574.WordEncoding
open Lax185574Proofs.Words Lax185574.TypeTrees Lax185574.PartialGraphs Lax185574Proofs.TreeAlgo
open Lax185574Proofs.Simulate Lax185574Proofs.RamSim Lax185574.GaifmanGraph
open Lax3.DistFO (rhoMinus)

/-- **The hypothesis on the glue program.** -/
def GlueHyp : Prop :=
  ∃ sI : ℕ, ∀ eR eS eC D : ℕ, sI + 4 ≤ D →
    ∃ (Gp : Program) (cG E : ℕ), 1 ≤ E ∧ GlueSpec Gp sI (D + 20) eR eS eC cG E

/-! ### Arithmetic -/

/-- The sizes of the rounds as a function of `X = |x| + 1`. -/
def Lf (K q X : ℕ) : ℕ := Lsz ⟨X, K, 0, q⟩ (5 * X ^ (q + 1))

/-- The length of a result at depth `q`. -/
def Ff (K q X : ℕ) : ℕ := (8 * (X + K + 10)) ^ (q + 1)

/-- The length of the lists of extensions. -/
def LXf (K q X : ℕ) : ℕ := 2 * X * (Ff K q X + K + 9) + 2 * X + 2

theorem Lf_eq (K q X : ℕ) : Lf K q X = 2 * (1 + 7 * (q + 1) * (LXf K q X + 7)) +
    4 * (LXf K q X + Ff K q X + K + 6 + 50000) + X + 5 * X ^ (q + 1) + 2 * K + LXf K q X +
    Ff K q X + 60000 := rfl

theorem pb_Lf (K q : ℕ) : PB (Lf K q) := by
  have hF : PB (Ff K q) := (((PB.id.add (PB.const K)).add (PB.const 10)).cmul 8).pow _
  have hLX : PB (LXf K q) :=
    (((PB.id.cmul 2).mul ((hF.add (PB.const K)).add (PB.const 9))).add (PB.id.cmul 2)).add
      (PB.const 2)
  have h1 : PB fun X => 2 * (1 + 7 * (q + 1) * (LXf K q X + 7)) :=
    ((PB.const 1).add ((PB.const (7 * (q + 1))).mul (hLX.add (PB.const 7)))).cmul 2
  have h2 : PB fun X => 4 * (LXf K q X + Ff K q X + K + 6 + 50000) :=
    ((((hLX.add hF).add (PB.const K)).add (PB.const 6)).add (PB.const 50000)).cmul 4
  have h3 := ((((((h1.add h2).add PB.id).add ((PB.xpow (q + 1)).cmul 5)).add (PB.const (2 * K))).add
    hLX).add hF).add (PB.const 60000)
  exact PB.mono h3 fun X _ => le_of_eq (Lf_eq K q X)

theorem Lsz_mono {n : ℕ} {G : PartialGraph (Fin n)} {k q l1 l2 : ℕ} {u₁ : Fin l1 → Fin n}
    {u₂ : Fin l2 → Fin n} {X m m' : ℕ} (hX : (xT G k q u₁ u₂).length ≤ X) (hm : m ≤ m') :
    Lsz (szP G k q u₁ u₂) m ≤ Lsz ⟨X, k + q + 1, 0, q⟩ m' := by
  simp only [Lsz, SzP.LS, SzP.LQ, SzP.LX, SzP.F, szP]
  gcongr

theorem roundT_mono {eR eS eC C A Ks cG L L' : ℕ} (h : L ≤ L') :
    roundT eR eS eC C A Ks cG L ≤ roundT eR eS eC C A Ks cG L' := by
  simp only [roundT]; gcongr

/-- The room of the regions. -/
theorem bigR_le {eR eS eC C A Ks sQ cG E L L' M Z : ℕ} (hE : 1 ≤ E) (hL : L ≤ L') (hZ : M + 1 ≤ Z) :
    bigR eR eS eC C A Ks sQ cG E L M ≤
      2 ^ (sQ + 20) * (cG * (3 * L' + 1) ^ E + crunBig eR eS eC C A + C * (L' + 1) ^ A + Ks + L' + 1) *
        Z ^ E := by
  simp only [bigR]
  set Cb := crunBig eR eS eC C A
  have hZ1 : 1 ≤ Z := by omega
  have h1 : (3 * L + M + 1) ^ E ≤ (3 * L' + 1) ^ E * Z ^ E := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by nlinarith) E
  have h2 : Z ≤ Z ^ E := Nat.le_self_pow (by omega) Z
  have h3 : C * (L + 1) ^ A ≤ C * (L' + 1) ^ A := by gcongr
  have h4 : Cb + C * (L + 1) ^ A + Ks + L + M + 1 ≤
      (Cb + C * (L' + 1) ^ A + Ks + L' + 1) * Z ^ E := by
    have : Cb + C * (L + 1) ^ A + Ks + L + M + 1 ≤ (Cb + C * (L' + 1) ^ A + Ks + L' + 1) * Z := by
      generalize hS' : Cb + C * (L' + 1) ^ A + Ks + L' + 1 = S' at *
      have hS : Cb + C * (L + 1) ^ A + Ks + L + 1 ≤ S' := by omega
      have : S' * (M + 1) ≤ S' * Z := Nat.mul_le_mul_left _ hZ
      have : M + S' ≤ S' * (M + 1) := by
        have : 1 ≤ S' := by omega
        nlinarith
      omega
    exact le_trans this (Nat.mul_le_mul_left _ h2)
  rw [Nat.mul_assoc (2 ^ (sQ + 20))]
  apply Nat.mul_le_mul_left
  have : cG * (3 * L + M + 1) ^ E ≤ cG * (3 * L' + 1) ^ E * Z ^ E := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ h1
  nlinarith

/-- Two halves of the word fit. -/
theorem room_arith {V Z E e c cV X a aV w : ℕ} (hV : V ≤ cV * X ^ aV) (hX : 1 ≤ X) (hZ : 1 ≤ Z)
    (hc : 16 * (cV ^ 2 + 1) ≤ c) (ha : 2 * aV ≤ a) (he : 2 * E ≤ e) (hT : c * X ^ a ≤ 2 ^ w)
    (hA : c * Z ^ e ≤ 2 ^ w) : 8 * (V * Z ^ E) ≤ 2 ^ w := by
  have h1 : 2 * (V * Z ^ E) ≤ V ^ 2 + (Z ^ E) ^ 2 := by nlinarith [sq_nonneg ((V : ℤ) - Z ^ E)]
  have h2 : V ^ 2 ≤ cV ^ 2 * X ^ a := by
    calc V ^ 2 ≤ (cV * X ^ aV) ^ 2 := Nat.pow_le_pow_left hV 2
      _ = cV ^ 2 * X ^ (2 * aV) := by rw [mul_pow, ← pow_mul, Nat.mul_comm aV]
      _ ≤ cV ^ 2 * X ^ a := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right hX ha)
  have h3 : (Z ^ E) ^ 2 ≤ Z ^ e := by
    rw [← pow_mul]; exact Nat.pow_le_pow_right hZ (by omega)
  have h4 : 16 * (cV ^ 2 * X ^ a) ≤ 2 ^ w := by
    calc 16 * (cV ^ 2 * X ^ a) ≤ 16 * (cV ^ 2 + 1) * X ^ a := by rw [Nat.mul_assoc]; gcongr; omega
      _ ≤ c * X ^ a := Nat.mul_le_mul_right _ hc
      _ ≤ _ := hT
  have h5 : 16 * Z ^ e ≤ 2 ^ w := by
    have : 16 ≤ c := by nlinarith
    exact le_trans (Nat.mul_le_mul_right _ this) hA
  omega

end Lax185574Proofs.CompRam
