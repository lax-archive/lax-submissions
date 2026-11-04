import Lax185574Proofs.ResolveRam.Slots
import Lax185574Proofs.LoopScript

/-!
The queries and answers of the calls in the five slots, and the
specification of the glue program of lem:resolve-lift.

A call puts its real query into its slot and the fixed queries into the
other four (`rQ`). The answer of the switch is `rY`. The glue program
writes in round `j` a head `hd j` (tag, state length, window length,
state) followed by the query of call `j`, and after the last call `0`
followed by the word of the output. The heads are left to the glue
program (`RGlueAt` asks for some `hd`), as in thm:mc.

`RGlueAt` is what the composite needs of the glue program at one
instance: at every word length `v` at which the entries of its input are
below `2 ^ (v - sI)`, every halting run of a round has the scripted
output, with entries below `2 ^ (v - sI - 4)`, and the guard `RGuard` of
the call holds. If the scripted input and output fit into `2 ^ (v - sQ)`
with room, the round halts within `tG j` steps. The times `tG j` add up
to the bound of lem:resolve-lift with the constants of the glue, and the
heads are at most the size of the input plus `|G|` times a polynomial in
`M + T`.
-/

namespace Lax185574Proofs.ResolveRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ScatterTypes
open Lax185574.ResolveLift Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo
open Lax185574.DistanceMatrix
open Lax185574Proofs.Words Lax185574Proofs.Simulate Lax185574Proofs.RamSim

variable {n : ℕ} (G : PartialGraph (Fin n)) (k₀ q₀ : ℕ)

/-! ### The slots -/

/-- The query of slot A (rank shift). -/
noncomputable def qA : RCall → List ℕ
  | .shift τ => toWord τ
  | _ => qA0

/-- The query of slot B (far tree). -/
noncomputable def qB : RCall → List ℕ
  | .ftree τ => toWord (τ, stpCut (τ.k + 1) (stp G k₀ q₀))
  | _ => qB0

/-- The query of slot C (composition). -/
noncomputable def qC : RCall → List ℕ
  | .compose σ ν => toWord (σ, ν)
  | _ => qC0

/-- The query of slot E (canonical form). -/
def qE : RCall → List ℕ
  | .canon ws => toWord ws
  | _ => qE0

/-- The query of slot F (scatter type). -/
noncomputable def qF : RCall → List ℕ
  | .stp => toWord (G, k₀, q₀, distMatrix G, family G k₀ q₀)
  | _ => qF0

noncomputable def yA : RCall → List ℕ
  | .shift τ => toWord (shOf G τ)
  | _ => yA0

noncomputable def yB : RCall → List ℕ
  | .ftree τ => toWord ((faOf G τ).map toWord)
  | _ => yB0

noncomputable def yC : RCall → List ℕ
  | .compose σ ν => toWord (coOf G σ ν)
  | _ => yC0

def yE : RCall → List ℕ
  | .canon ws => canonW ws
  | _ => yE0

noncomputable def yF : RCall → List ℕ
  | .stp => toWord (stp G k₀ q₀)
  | _ => yF0

/-- The query of a call to the switch. -/
noncomputable def rQ (c : RCall) : List ℕ :=
  sw5In (qA c) (qB G k₀ q₀ c) (qC c) (qE c) (qF G k₀ q₀ c)

/-- The answer of the switch to a call. -/
noncomputable def rY (c : RCall) : List ℕ :=
  yA G c ++ yB G c ++ yC G c ++ yE c ++ yF G k₀ q₀ c

/-- The query of the slot that does the work of a call. -/
noncomputable def realQ : RCall → List ℕ
  | .stp => toWord (G, k₀, q₀, distMatrix G, family G k₀ q₀)
  | .shift τ => toWord τ
  | .ftree τ => toWord (τ, stpCut (τ.k + 1) (stp G k₀ q₀))
  | .compose σ ν => toWord (σ, ν)
  | .canon ws => toWord ws

/-- The literal exponent of the guard of a call. -/
def eOf (eS eF eC eK eT : ℕ) : RCall → ℕ
  | .stp => eT
  | .shift _ => eS
  | .ftree _ => eF
  | .compose _ _ => eC
  | .canon _ => eK

/-- The guard of a call at word length `v` with shift `sQ`: the real
query and the size `X` of the input of the composite are small for the
literal exponent of the slot. -/
def RGuard (eS eF eC eK eT X v sQ : ℕ) (c : RCall) : Prop :=
  ((realQ G k₀ q₀ c).length + maxEntry (realQ G k₀ q₀ c) + 1 + X) ^ (eOf eS eF eC eK eT c + 1) ≤
    2 ^ (v - sQ)

/-! ### The rounds of the glue program -/

section rounds

variable (x : List ℕ) (cs : List RCall) (hd : ℕ → List ℕ) (z : List ℕ)

/-- The output of round `j` of the glue program. -/
noncomputable def gOut (j : ℕ) : List ℕ :=
  match cs[j]? with
  | some c => hd j ++ rQ G k₀ q₀ c
  | none => 0 :: z

/-- The state `a` of the loop driver before round `j`. -/
noncomputable def gA : ℕ → List ℕ
  | 0 => lpA0 x
  | j + 1 => gOut G k₀ q₀ cs hd z j

/-- The callee output `b` of the loop driver before round `j`. -/
noncomputable def gB : ℕ → List ℕ
  | 0 => []
  | j + 1 => match cs[j]? with
    | some c => rY G k₀ q₀ c
    | none => []

/-- The input of round `j` of the glue program. -/
noncomputable def gU (j : ℕ) : List ℕ := lpU x (gA G k₀ q₀ x cs hd z j) (gB G k₀ q₀ cs j)

end rounds

/-- The input of lem:resolve-lift. -/
noncomputable def xIn (P Q : ℕ) (s : Bool) : List ℕ :=
  toWord (G, distMatrix G, P, Q, s, family G k₀ q₀)

/-- The output of lem:resolve-lift. -/
noncomputable def zOut (P Q : ℕ) (s : Bool) : List ℕ :=
  toWord (resolveBy G s P Q, distMatrix (resolveBy G s P Q), family (resolveBy G s P Q) k₀ q₀)

/-- The size of the input. -/
def ySz (x : List ℕ) : ℕ := x.length + maxEntry x + 1

/-- The bound of lem:resolve-lift with a constant `c` and a degree `a`. -/
noncomputable def rBound (P Q : ℕ) (s : Bool) (c a : ℕ) : ℕ :=
  c * (n + 1) * (n + 1) *
    (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ a

/-- **The glue program at one instance.** -/
structure RGlueAt (Gp : Program) (sI sQ eS eF eC eK eT cG aG : ℕ) (P Q : ℕ) (s : Bool) : Prop where
  rounds : ∃ (hd : ℕ → List ℕ) (tG : ℕ → ℕ),
    let x := xIn G k₀ q₀ P Q s
    let cs := rcalls G P Q s k₀ q₀
    let z := zOut G k₀ q₀ P Q s
    let R := cs.length
    let E := eS + eF + eC + eK + eT + 2
    (∀ j < R, hd j ≠ [] ∧ (hd j).head? ≠ some 0 ∧ (hd j).getD 1 0 + 3 = (hd j).length) ∧
    (∑ j ∈ Finset.range (R + 1), tG j) ≤ rBound G k₀ q₀ P Q s cG aG ∧
    (∀ j < R, ySz (hd j) ≤ cG * (ySz x + (n + 1) *
      (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ aG)) ∧
    (∀ j ≤ R, ∀ v, sI ≤ v → (∀ e ∈ gU G k₀ q₀ x cs hd z j, e < 2 ^ (v - sI)) →
      (∀ o t, RunsTo v Gp (gU G k₀ q₀ x cs hd z j) o t →
        o = gOut G k₀ q₀ cs hd z j ∧ (∀ e ∈ o, e < 2 ^ (v - sI - 4)) ∧
        ∀ c, cs[j]? = some c → RGuard G k₀ q₀ eS eF eC eK eT (ySz x) v sQ c) ∧
      (cG * (ySz (gU G k₀ q₀ x cs hd z j) + ySz (gOut G k₀ q₀ cs hd z j) + ySz x) ^ E ≤
          2 ^ (v - sQ) →
        ∃ t ≤ tG j, RunsTo v Gp (gU G k₀ q₀ x cs hd z j) (gOut G k₀ q₀ cs hd z j) t))

/-- **The hypothesis on the glue program.** There is an input shift `sI`
such that for all literal exponents of the guards and every `D ≥ sI + 4`
some glue program meets `RGlueAt` with query shift `2 D + 20` on every
instance, with constants of the rank. -/
def RGlueHyp : Prop :=
  ∃ sI : ℕ, ∀ eS eF eC eK eT D : ℕ, sI + 4 ≤ D → ∃ Gp : Program, ∀ k q : ℕ, ∃ cG aG : ℕ,
    ∀ (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool), 1 ≤ k →
      RGlueAt G k q Gp sI (2 * D + 20) eS eF eC eK eT cG aG P Q s

end Lax185574Proofs.ResolveRam
