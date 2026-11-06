import Lax185574.DefinableFlips
import Lax185574.DpMinimality

/-!
---
title: Definable flips preserve dp-minimality
type: corollary
---
Let 𝒞 be a dp-minimal graph class and s ∈ ℕ. The class consisting of all
s-definable flips of graphs from 𝒞 is dp-minimal.

# Formalization notes

The class of s-definable flips is `definableFlipClass` of
`Lax185574.DefinableFlips`.
-/

namespace Lax185574.DpMinimalFlips

open Lax185574.Graphs Lax185574.DpMinimality Lax185574.DefinableFlips

/-- **Definable flips preserve dp-minimality.** The `s`-definable flips
of the graphs of a dp-minimal class form a dp-minimal class. -/
axiom dpMinimal_definableFlipClass (C : GraphClass) (hC : DpMinimal C) (s : ℕ) :
    DpMinimal (definableFlipClass C s)

end Lax185574.DpMinimalFlips
