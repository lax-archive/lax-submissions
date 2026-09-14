/-
**Completeness of the checking automaton of stage 1 of the induction step of the
book's snake lemma.**

Every good input carries an annotation that the checking automaton accepts: the
one built from the record-breaker decomposition of its run, which is a chain of
pieces (`Transducers.TwoWay.Chk.nonempty_chainData_of_good`), and every chain of
pieces is described by an accepted annotation
(`Transducers.TwoWay.Chk.exists_mem_chkLang_of_chainData`).
-/
import Lax916827Proofs.Source.PartC.SnakeChkRB
import Lax916827Proofs.Source.PartC.SnakeChkBuild
import Lax916827Proofs.Source.PartC.SnakeChkRel
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace TwoWay

namespace Chk

open RegPair

variable {A B Q S : Type}

/-- **The checking automaton is complete**: every good input has an annotation
that the checking automaton accepts. -/
theorem chk_complete [Finite A] [Finite B] [Finite Q] [Inhabited S]
    (M : TwoWay A B Q) {K : ℕ} (hK : 2 ≤ K) (stp : S → A → S) (ini : S)
    (acc : PieceParam A Q → S → Prop)
    (hacc : ∀ (p : PieceParam A Q) (v : List A),
      v ∈ WinCond M (K - 1) p ↔ acc p (v.foldl stp ini))
    {w : List A} (hgood : GoodInput M K w) :
    ∃ u ∈ ChkLang M K stp ini acc, u.map lt = w := by
  obtain ⟨d⟩ := nonempty_chainData_of_good M hK hgood
  exact exists_mem_chkLang_of_chainData M stp ini acc hacc d

end Chk

end TwoWay

end Lax916827Proofs.Transducers
