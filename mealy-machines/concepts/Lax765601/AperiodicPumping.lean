import Lax765601.MealyMachine
import Lax765601.Aperiodicity

/-!
---
title: Aperiodicity as a pumping property
type: theorem
---
A function $f$ computed by a Mealy machine is aperiodic if and only if for all
input strings $u, v, w$ there are output strings $x, y, z$ and a number $k$ such
that
$$f(u v^{n+k} w) = x y^n z \qquad \text{for all } n > 0$$
(Claim A.2.9 of *Transducers*). The right-to-left direction is immediate, since
the last letter of $x y^n z$ does not depend on $n$. For the other direction,
aperiodicity fixes the last $|v|$ letters of $f(u v^n)$ for large $n$, so that
from some point on the output ends with repetitions of a fixed string $y$ of
length $|v|$, and fixes the last $|w|$ letters of $f(u v^n w)$, which gives $z$.
The pumping form is what makes aperiodicity compatible with composition: the
shift $k$ of $f \cdot g$ is the sum of the shifts of $f$ and $g$.

# Formalization notes

`npow v n` is `vⁿ`. The hypothesis that `f` is computed by a Mealy machine is
used only in the left-to-right direction; no finiteness of the alphabets is
needed.
-/

namespace Lax765601.AperiodicPumping

open Lax765601.MealyMachine Lax765601.Aperiodicity

/-- A Mealy function is aperiodic if and only if it has the pumping property: for
all `u, v, w` there are `x, y, z` and `k` with `f (u v^(n+k) w) = x yⁿ z` for all
`n > 0`. -/
axiom aperiodic_iff_pumping {A B : Type} {f : List A → List B} (hf : IsMealy f) :
    Aperiodic f ↔
      ∀ u v w : List A, ∃ (x y z : List B) (k : ℕ), ∀ n > 0,
        f (u ++ npow v (n + k) ++ w) = x ++ npow y n ++ z

end Lax765601.AperiodicPumping
