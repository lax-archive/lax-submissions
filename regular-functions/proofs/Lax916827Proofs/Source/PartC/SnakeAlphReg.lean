/-
**Lemma `lem:output-of-snake-graph-is-regular`, over the book's alphabet of snake letters.**

> Let `C` be the alphabet used to represent snakes with state `Q` and output alphabet `B`.  For
> every `k ∈ {1, …, |Q|}`, the following function is regular:
>
>   `w ∈ C*  ↦  ε` if `w` does not represent a snake graph of width `≤ k`, and otherwise the output
>   of the snake graph.

That function is `SnakeGraph.snakeOut k`, over the alphabet `Transducers.SnakeLetter Q B` of
`RequestProject/PartC/SnakeAlph.lean`, and the lemma is `SnakeGraph.snakeOut_isRegular`.

The proof does not repeat the induction on the width of the book: it *reuses* the form of the snake
lemma that the project already proves, `Transducers.boundedWidth_isRegular`, which says that the
width-bounded output function of a two-way transducer is regular.  The two ingredients are:

* the strings that represent a snake graph of width at most `k` form a regular language: the
  conditions are that in- and out-degrees are at most one and that no column is visited more than
  `k` times, which are conditions on pairs of consecutive letters
  (`RequestProject/PartC/SnakeAlphLocLang.lean`), that there is at most one source (same file), and
  that there is no directed cycle, which a left-to-right automaton checks by keeping track of the
  reachability relation of the current column (`RequestProject/PartC/SnakeAlphCyc.lean`);
  `SnakeGraph.representsSnake_iff` is the reason why these conditions are exactly the book's "all
  edges lie on a single directed path";
* on those strings the output of the snake graph is computed by the two-way transducer
  `SnakeGraph.snakeTrans` that walks along the snake (`RequestProject/PartC/SnakeAlphRun.lean`), and
  its run halts, so its width is bounded by the number of states and the width-bounded output
  function of `Transducers.boundedWidth_isRegular` already computes it.

The two are combined by the conditional of Lemma `lem:regular-closure-properties`
(`Transducers.isRegularFun_cond`).
-/
import Lax916827Proofs.Source.PartC.SnakeAlphLocLang
import Lax916827Proofs.Source.PartC.SnakeAlphCyc
import Lax916827Proofs.Source.PartC.SnakeAlphRun
import Lax916827Proofs.Source.PartC.RegClosure
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace SnakeGraph

variable {Q B : Type}

/-- The strings over the alphabet of snake letters that represent a snake graph of width at most
`k`, described by the four conditions of `SnakeGraph.representsSnake_iff`. -/
def SnakeLang (Q B : Type) (k : ℕ) : Language (SnakeLetter Q B) :=
  {w | (OutDegLe1 w ∧ InDegLe1 w ∧ SnakeWidthLe w k) ∧ SrcUnique w ∧ Acyclic w}

lemma isRegular_snakeLang [Finite Q] [Finite B] (k : ℕ) : (SnakeLang Q B k).IsRegular := by
  have h := RegAut.isRegular_and (isRegular_locOK (Q := Q) (B := B) k)
    (RegAut.isRegular_and (isRegular_srcUnique (Q := Q) (B := B)) (isRegular_acyclic (Q := Q)
      (B := B)))
  exact RegAut.isRegular_of_eq h (fun w => Iff.rfl)

/-- **Lemma `lem:output-of-snake-graph-is-regular`** (the output of a snake graph is regular).
Let `C = Transducers.SnakeLetter Q B` be the alphabet used to represent snakes with states `Q` and
output alphabet `B`.  For every `k`, the function that maps a string `w ∈ C*` to the output of the
snake graph it represents -- and to the empty string when `w` does not represent a snake graph of
width at most `k` -- is a regular function.

*Two remarks on the statement.*  The book states the lemma for `k ∈ {1, …, |Q|}`; it is proved here
for every `k : ℕ`, which is more general (and the restriction is immaterial, since a column has at
most `|Q|` vertices, so every snake graph over `Q` has width at most `|Q|`).  The book's alphabet
`C` has, besides the slices, a special letter for the empty input; for snake graphs it is not
needed, since the empty string already represents the snake graph with a single column and no edge,
whose output is empty. -/
theorem snakeOut_isRegular [Finite Q] [Finite B] (k : ℕ) :
    IsRegularFun (snakeOut (Q := Q) (B := B) k) := by
  classical
  by_cases hQ : Nonempty Q
  · haveI := hQ
    have hcond : IsRegularFun (fun w : List (SnakeLetter Q B) =>
        if w ∈ SnakeLang Q B k then
          TwoWay.widthOut (snakeTrans Q B) (Nat.card (Option Q)) w else ([] : List B)) :=
      isRegularFun_cond (boundedWidth_isRegular (snakeTrans Q B) _)
        (IsRegularFun.of_rational (isRationalFun_const [])) (isRegular_snakeLang k)
    refine hcond.congr (fun w => ?_)
    by_cases hw : w ∈ SnakeLang Q B k
    · obtain ⟨⟨h1, h2, hwid⟩, h3, h4⟩ := hw
      have hrep : RepresentsSnake w := (representsSnake_iff w).2 ⟨h1, h2, h4, h3⟩
      rw [if_pos (show w ∈ SnakeLang Q B k from ⟨⟨h1, h2, hwid⟩, h3, h4⟩)]
      exact (snakeOut_eq hwid (snakeOutIs_widthOut hrep)).symm
    · rw [if_neg hw]
      refine (snakeOut_of_not ?_).symm
      rintro ⟨hwid, v, hv⟩
      obtain ⟨m, p, lab, hpath, -⟩ := hv
      obtain ⟨h1, h2, h4, h3⟩ := conditions_of_representsSnake ⟨m, p, lab, hpath⟩
      exact hw ⟨⟨h1, h2, hwid⟩, h3, h4⟩
  · -- there is no vertex at all, so no string represents a snake graph
    have hnil : ∀ w : List (SnakeLetter Q B), snakeOut k w = [] := by
      intro w
      refine snakeOut_of_not ?_
      rintro ⟨-, v, m, p, lab, -, -⟩
      exact hQ ⟨(p 0).1⟩
    exact (IsRegularFun.of_rational (isRationalFun_const [])).congr (fun w => (hnil w).symm)

end SnakeGraph

end Lax916827Proofs.Transducers
