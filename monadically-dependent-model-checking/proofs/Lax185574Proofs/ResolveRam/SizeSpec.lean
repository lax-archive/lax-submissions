import Lax185574Proofs.ResolveRam.SlotTime
import Lax185574Proofs.ResolveRam.CountT

/-!
The size bounds that the time bound of lem:resolve-lift needs, at one
instance, with a constant `C` and a degree `A`.

Write `H = resolve^±_{P,Q}(G)`, `M` for the largest size of a tree of
the family, `T` for `treeCount` and `X` for the size of the input. The
number of calls is at most `C (n + 1)(T + 1)^A`, the time bounds of the
callees add up to at most `C (n + 1)²(M + T + 1)^A`, and so do the
lengths of the query and the answer of every call and the length of the
output. Every entry of these words is at most `C` times their length
plus `X`.
-/

namespace Lax185574Proofs.ResolveRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.TypeTrees Lax185574.ScatterTypes
open Lax185574.ResolveLift Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo
open Lax185574Proofs.Words

variable {n : ℕ} (G : PartialGraph (Fin n)) (k₀ q₀ : ℕ)

/-- The polynomial part of the bounds: `(n + 1)²(M + T + 1)^A`. -/
noncomputable def polyB (P Q : ℕ) (s : Bool) (C A : ℕ) : ℕ :=
  C * (n + 1) * (n + 1) *
    (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ A

/-- **The size bounds at one instance.** -/
structure CallBounds (P Q : ℕ) (s : Bool) (C A : ℕ) : Prop where
  calls : (rcalls G P Q s k₀ q₀).length ≤
    C * (n + 1) * (treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ A
  time : ((rcalls G P Q s k₀ q₀).map (realT G k₀ q₀)).sum ≤ polyB G k₀ q₀ P Q s C A
  len : ∀ c ∈ rcalls G P Q s k₀ q₀,
    (rQ G k₀ q₀ c).length + (rY G k₀ q₀ c).length ≤ polyB G k₀ q₀ P Q s C A
  zlen : (zOut G k₀ q₀ P Q s).length ≤ polyB G k₀ q₀ P Q s C A
  ent : ∀ c ∈ rcalls G P Q s k₀ q₀, maxEntry (rQ G k₀ q₀ c) + maxEntry (rY G k₀ q₀ c) ≤
    C * ((rQ G k₀ q₀ c).length + (rY G k₀ q₀ c).length + ySz (xIn G k₀ q₀ P Q s))
  zent : maxEntry (zOut G k₀ q₀ P Q s) ≤
    C * ((zOut G k₀ q₀ P Q s).length + ySz (xIn G k₀ q₀ P Q s))

/-- The statement that the size bounds hold with constants of the rank. -/
def SizeHyp : Prop :=
  ∀ k₀ q₀ : ℕ, 1 ≤ k₀ → ∃ C A : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool),
    CallBounds G k₀ q₀ P Q s C A

end Lax185574Proofs.ResolveRam
