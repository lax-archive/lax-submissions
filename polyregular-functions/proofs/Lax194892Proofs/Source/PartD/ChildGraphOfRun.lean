/-
**The child configuration graph of a configuration of a pebble transducer.**

This file joins the two halves of the previous two files: the string representation of a child
configuration graph built from an abstract list of children
(`RequestProject/PartD/ChildPath.lean`) and the children of a configuration of a pebble transducer
(`RequestProject/PartD/ChildSem.lean`).  For a configuration `(q, st)` whose list of children is
`ch 0, …, ch m` it produces the string `Transducers.CG.cgOfChildren` over the alphabet
`Transducers.CG.CGLetter` and proves

  `Transducers.CG.cgOutIs_cgOfChildren`:
  `CGOutIs (cgOfChildren w st nid ch m) (the string representations of the children)`,

which is the statement that this string *is* the string representation of the child configuration
graph of `(q, st)`, in the sense of `RequestProject/PartD/ChildGraph.lean`.  Together with Claim
`claim:from-child-configuration-graph-to-children`
(`Transducers.from_child_configuration_graph_to_children`) it says that a for-transducer which is
given this string outputs the string representations of the children, in order of execution.
-/
import Lax194892Proofs.Source.PartD.ChildSem
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace CG

open Pebble

variable {A B Q : Type} {k : ℕ} {M : Pebble A B Q k} {w : List A} {st : List ℕ} {q : Q}
  {ch : ℕ → Vtx Q} {m : ℕ} {nid : Fin k}

/-- **The string representation of a configuration**: one letter per gap of the input, carrying the
state, the input letter that follows the gap, and the pebbles that sit in the gap.  This is the
shape used throughout Section D.2; see the header of `RequestProject/PartD/PebEnc.lean`. -/
def confEnc (q : Q) (st : List ℕ) (w : List A) : List (ConfLetter A Q k) :=
  (List.range (w.length + 1)).map fun p => (q, w[p]?, PebEnc.ann k st p)

/-- **The string representation of the child configuration graph** of a configuration whose list of
children is `ch 0, …, ch m`. -/
noncomputable def cgOfChildren (w : List A) (st : List ℕ) (nid : Fin k) (ch : ℕ → Vtx Q) (m : ℕ) :
    List (CGLetter A Q k) :=
  cgOfPath (fun j => w[j]?) (fun j => PebEnc.ann k st j) nid w.length ch m

/-- Adding a pebble on top of the stack adds exactly its own mark to the annotation. -/
lemma ann_append_singleton (st : List ℕ) (p j : ℕ) (nid : Fin k)
    (hnid : (nid : ℕ) = st.length) :
    PebEnc.ann k (st ++ [p]) j =
      fun i => PebEnc.ann k st j i || (decide (i = nid) && decide (p = j)) := by
  funext i
  rcases lt_trichotomy (i : ℕ) st.length with h | h | h
  · have h1 : (st ++ [p])[(i : ℕ)]? = st[(i : ℕ)]? := List.getElem?_append_left h
    have h2 : ¬ (i = nid) := by
      intro hc
      rw [hc, hnid] at h
      omega
    simp only [PebEnc.ann, h1, decide_eq_false_iff_not.2 h2, Bool.false_and, Bool.or_false]
  · have h1 : (st ++ [p])[(i : ℕ)]? = some p := by
      rw [List.getElem?_append_right (by omega), h]
      simp
    have h2 : st[(i : ℕ)]? = none := List.getElem?_eq_none (by omega)
    have h3 : i = nid := Fin.ext (by omega)
    simp only [PebEnc.ann]
    rw [h1, h2, decide_eq_true h3, Bool.true_and]
    simp
  · have h1 : (st ++ [p])[(i : ℕ)]? = none := by
      refine List.getElem?_eq_none ?_
      simp
      omega
    have h2 : st[(i : ℕ)]? = none := List.getElem?_eq_none (by omega)
    have h3 : ¬ (i = nid) := by
      intro hc
      rw [hc, hnid] at h
      omega
    simp only [PebEnc.ann, h1, h2, decide_eq_false_iff_not.2 h3, Bool.false_and, Bool.or_false]

/-- **The letter that the graph attaches to a child is the string representation of that child.** -/
lemma confAt_cgOfChildren (v : Vtx Q) (hnid : (nid : ℕ) = st.length) :
    confAt (cgOfChildren w st nid ch m) v = confEnc v.1 (st ++ [v.2]) w := by
  rw [cgOfChildren, confAt_cgOfPath, confEnc]
  refine List.map_congr_left ?_
  intro j _
  rw [ann_append_singleton st v.2 j nid hnid]

/-- **The string `cgOfChildren` represents the child configuration graph**: the run of children that
it describes is the list of children, and its output is the concatenation of their string
representations, in order of execution. -/
theorem cgOutIs_cgOfChildren (hseq : IsChildSeq M w q st ch m) (hnid : (nid : ℕ) = st.length) :
    CGOutIs (cgOfChildren w st nid ch m)
      (((List.range (m + 1)).map fun t => confEnc (ch t).1 (st ++ [(ch t).2]) w).flatten) := by
  refine ⟨m, ch, ?_, ?_⟩
  · exact cgPath_cgOfPath hseq.distinct hseq.column_le fun t ht => (hseq.next t ht).column_adjacent
  · rw [cgOut]
    congr 1
    refine List.map_congr_left ?_
    intro t _
    exact (confAt_cgOfChildren (ch t) hnid).symm

end CG

end Lax194892Proofs.Transducers
