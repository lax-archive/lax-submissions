/-
The string encoding of the reachable configuration graph of a two-way transducer, as described in
the proof of Theorem `thm:continuity-2dfas` of *Transducers* (M. Bojańczyk).

The book slices the configuration graph of a two-way transducer on a fixed input into one small
graph per input letter, and represents the whole graph as a string over a finite alphabet `C`:

> the alphabet for the string representation, call it `C`, consists of bipartite graphs, where the
> vertices are two copies of `Q`, edges are directed and labelled with output strings, each vertex
> has at most one outgoing edge, and this edge must go to the other copy of `Q`.  This alphabet is
> finite, since we use only labels of edges that arise from transitions of the transducer.  There is
> an edge case for the empty input string […]  Therefore, the alphabet `C` contains a special letter
> for this configuration graph.

Here is how that alphabet is rendered.  A slice letter is a function which assigns to every vertex
-- a state `q` in the left copy (`(false, q)`, standing for the cut to the left of the sliced
letter) or in the right copy (`(true, q)`, the cut to its right) -- the outgoing edge of that vertex
inside the slice:

* `VOut.nil`: no outgoing edge in this slice;
* `VOut.move q' l`: an edge to the state `q'` *in the other copy*, labelled with the output string
  `l`;
* `VOut.halt l`: the transducer halts at this vertex, producing the output string `l`.

Writing the target as a state of the other copy is exactly the book's condition that a vertex has at
most one outgoing edge and that this edge goes to the other copy of `Q`; the labels range over the
finite set `TwoWay.Lab M` of output strings that occur in the transition function of `M`, which is
the book's reason for `C` being finite.  The halting vertex of the configuration graph is not a
vertex of any copy of `Q`, so the edge leading to it is recorded by `VOut.halt`, on both copies of
the cut where the transducer halts.  Finally `CLet` adds the book's special letter for the empty
input, which carries the output string produced by the transducer when it halts immediately (and no
label when the run on the empty input does not halt).

The encoding `TwoWay.enc M w` of an input `w` records, in the slice of the letter at position `i`,
the outgoing edges of the *reachable* configurations at the cuts `i` and `i + 1`: a vertex which the
run of `M` on `w` does not visit gets `VOut.nil`, and so does a visited vertex whose outgoing edge
crosses a different letter.  This is the book's *reachable* configuration graph.

`TwoWay.pathTrans M` is the two-way transducer over the alphabet `C` which walks along the encoded
graph and prints the labels it meets; `ConfGraphRun.lean` proves that it computes the same output as
`M`, which is the sense in which the encoding agrees with the run semantics of `TwoWayRun.lean`.
-/
import Lax916827Proofs.Source.PartC.TwoWayAnnot
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-! ## The alphabet `C` -/

/-- The outgoing edge of a vertex inside one slice of the configuration graph: either there is no
outgoing edge, or there is an edge to a state of the other copy of `Q`, or the transducer halts at
this vertex.  Edges are labelled by output strings, taken from a type `L` of labels. -/
inductive VOut (Q L : Type) where
  /-- No outgoing edge inside this slice. -/
  | nil : VOut Q L
  /-- An edge to the state `q'` of the other copy of `Q`, labelled `l`. -/
  | move (q' : Q) (l : L) : VOut Q L
  /-- The transducer halts here, producing the output string `l`. -/
  | halt (l : L) : VOut Q L

namespace VOut

variable {Q L : Type}

/-- An injective encoding of `VOut Q L`, used to see that it is a finite type. -/
def code : VOut Q L → Option (Option Q × L)
  | nil => none
  | move q l => some (some q, l)
  | halt l => some (none, l)

lemma code_injective : Function.Injective (code (Q := Q) (L := L)) := by
  intro x y h
  cases x <;> cases y <;> simp_all [code]

instance [Finite Q] [Finite L] : Finite (VOut Q L) := Finite.of_injective _ code_injective

end VOut

/-- A letter of the book's alphabet `C` for a non-empty input: a bipartite graph on two copies of
`Q`, given by the outgoing edge of each of its vertices.  The vertex `(false, q)` is the state `q`
in the left copy (the cut to the left of the sliced letter) and `(true, q)` is the state `q` in the
right copy (the cut to its right). -/
abbrev Slice (Q L : Type) := Bool × Q → VOut Q L

/-- The book's alphabet `C`: slices of a configuration graph, together with a special letter for the
configuration graph of the empty input, which carries the output string of the halting transition,
if there is one. -/
abbrev CLet (Q L : Type) := Slice Q L ⊕ Option L

namespace TwoWay

variable {A B Q : Type}

/-! ## The labels: the output strings of the transitions of `M` -/

/-- The output string produced by a transition of `M`. -/
def transOut (M : TwoWay A B Q) (l : Option A) (q : Q) (r : Option A) : List B :=
  match M.step l q r with
  | Sum.inl o => o
  | Sum.inr (_, o, _) => o

/-- The set of output strings that occur in the transition function of `M`. -/
def OutLabels (M : TwoWay A B Q) : Set (List B) :=
  Set.range (fun p : Option A × Q × Option A => M.transOut p.1 p.2.1 p.2.2)

/-- The finite set of edge labels of the configuration graph of `M`. -/
abbrev Lab (M : TwoWay A B Q) : Type := {o : List B // o ∈ OutLabels M}

instance labFinite [Finite A] [Finite Q] (M : TwoWay A B Q) : Finite (Lab M) :=
  Set.Finite.to_subtype (Set.finite_range _)

/-- The label of the edge produced by a transition of `M`. -/
def labOf (M : TwoWay A B Q) (l : Option A) (q : Q) (r : Option A) : Lab M :=
  ⟨M.transOut l q r, ⟨(l, q, r), rfl⟩⟩

@[simp] lemma labOf_val (M : TwoWay A B Q) (l : Option A) (q : Q) (r : Option A) :
    (labOf M l q r).val = M.transOut l q r := rfl

/-! ## The encoding of the reachable configuration graph -/

/-- The outgoing edge recorded, in the direction `d`, for the vertex given by the state `q` at a cut
whose adjacent letters are `l` and `r`.  A slice records the edges that cross the letter it slices:
the left copy records the transitions that move right (`d = true`), the right copy the transitions
that move left (`d = false`).  A halting transition is recorded on both copies of its cut. -/
def edgeOf (M : TwoWay A B Q) (l : Option A) (q : Q) (r : Option A) (d : Bool) : VOut Q (Lab M) :=
  match M.step l q r with
  | Sum.inl _ => VOut.halt (labOf M l q r)
  | Sum.inr (q', _, dir) => if dir = d then VOut.move q' (labOf M l q r) else VOut.nil

lemma transOut_halt {M : TwoWay A B Q} {l r : Option A} {q : Q} {o : List B}
    (h : M.step l q r = Sum.inl o) : M.transOut l q r = o := by
  simp only [transOut, h]

lemma transOut_move {M : TwoWay A B Q} {l r : Option A} {q q' : Q} {o : List B} {d : Bool}
    (h : M.step l q r = Sum.inr (q', o, d)) : M.transOut l q r = o := by
  simp only [transOut, h]

lemma edgeOf_halt {M : TwoWay A B Q} {l r : Option A} {q : Q} {o : List B}
    (h : M.step l q r = Sum.inl o) (d : Bool) : edgeOf M l q r d = VOut.halt (labOf M l q r) := by
  simp only [edgeOf, h]

lemma edgeOf_move {M : TwoWay A B Q} {l r : Option A} {q q' : Q} {o : List B} {d : Bool}
    (h : M.step l q r = Sum.inr (q', o, d)) :
    edgeOf M l q r d = VOut.move q' (labOf M l q r) := by
  simp only [edgeOf, h, if_pos]

lemma edgeOf_move_ne {M : TwoWay A B Q} {l r : Option A} {q q' : Q} {o : List B} {d d' : Bool}
    (h : M.step l q r = Sum.inr (q', o, d)) (hd : d ≠ d') : edgeOf M l q r d' = VOut.nil := by
  simp only [edgeOf, h, if_neg hd]

open scoped Classical in
/-- The outgoing edge, in the direction `d`, of the vertex given by the state `q` at the cut `j` of
the input `w`.  Only *reachable* configurations have outgoing edges: this is the reachable part of
the configuration graph. -/
noncomputable def cutV (M : TwoWay A B Q) (w : List A) (j : ℕ) (q : Q) (d : Bool) :
    VOut Q (Lab M) :=
  if Visits M w (Cfg.conf (w.take j) q (w.drop j)) then edgeOf M (prevAt w j) q w[j]? d
  else VOut.nil

/-- The slice of the reachable configuration graph of `M` on `w` at the letter of position `i`. -/
noncomputable def encSlice (M : TwoWay A B Q) (w : List A) (i : ℕ) : Slice Q (Lab M) :=
  fun v => cutV M w (if v.1 then i + 1 else i) v.2 (!v.1)

/-- The special letter for the empty input: it carries the output string of the halting transition
of `M` on the empty input, if the run on the empty input halts. -/
def emptyOut (M : TwoWay A B Q) : Option (Lab M) :=
  match M.step none M.init none with
  | Sum.inl _ => some (labOf M none M.init none)
  | Sum.inr _ => none

/-- **The string representation of the reachable configuration graph** of `M` on the input `w`: one
slice per input letter, and the special letter for the empty input. -/
noncomputable def enc (M : TwoWay A B Q) (w : List A) : List (CLet Q (Lab M)) :=
  if w.isEmpty then [Sum.inr (emptyOut M)]
  else (List.range w.length).map (fun i => Sum.inl (encSlice M w i))

@[simp] lemma enc_nil (M : TwoWay A B Q) : enc M [] = [Sum.inr (emptyOut M)] := rfl

lemma enc_of_ne_nil {M : TwoWay A B Q} {w : List A} (hw : w ≠ []) :
    enc M w = (List.range w.length).map (fun i => Sum.inl (encSlice M w i)) := by
  rw [enc, if_neg (by simpa using hw)]

lemma enc_length {M : TwoWay A B Q} {w : List A} (hw : w ≠ []) : (enc M w).length = w.length := by
  rw [enc_of_ne_nil hw]; simp

lemma enc_getElem? {M : TwoWay A B Q} {w : List A} (hw : w ≠ []) {i : ℕ} (hi : i < w.length) :
    (enc M w)[i]? = some (Sum.inl (encSlice M w i)) := by
  rw [enc_of_ne_nil hw, List.getElem?_map, List.getElem?_range hi]
  rfl

/-! ## The two-way transducer that walks along an encoded configuration graph -/

variable {L : Type}

/-- The outgoing edge, at the current cut, that is recorded by the letter to the right of the
head. -/
def readR (r : Option (CLet Q L)) (q : Q) : VOut Q L :=
  match r with
  | some (Sum.inl s) => s (false, q)
  | some (Sum.inr (some lab)) => VOut.halt lab
  | _ => VOut.nil

/-- The outgoing edge, at the current cut, that is recorded by the letter to the left of the
head. -/
def readL (l : Option (CLet Q L)) (q : Q) : VOut Q L :=
  match l with
  | some (Sum.inl s) => s (true, q)
  | _ => VOut.nil

/-- The two-way transducer over the alphabet `C` which walks along the path of an encoded
configuration graph, printing the labels of the edges it follows.  On a string that does not
represent a configuration graph its behaviour is irrelevant; it then halts with no output. -/
def pathTrans (M : TwoWay A B Q) : TwoWay (CLet Q (Lab M)) B Q where
  init := M.init
  step := fun l q r =>
    match readR r q with
    | VOut.move q' lab => Sum.inr (q', lab.val, true)
    | VOut.halt lab => Sum.inl lab.val
    | VOut.nil =>
      match readL l q with
      | VOut.move q' lab => Sum.inr (q', lab.val, false)
      | VOut.halt lab => Sum.inl lab.val
      | VOut.nil => Sum.inl []

@[simp] lemma pathTrans_init (M : TwoWay A B Q) : (pathTrans M).init = M.init := rfl

lemma pathTrans_step (M : TwoWay A B Q) (l : Option (CLet Q (Lab M))) (q : Q)
    (r : Option (CLet Q (Lab M))) :
    (pathTrans M).step l q r =
      match readR r q with
      | VOut.move q' lab => Sum.inr (q', lab.val, true)
      | VOut.halt lab => Sum.inl lab.val
      | VOut.nil =>
        match readL l q with
        | VOut.move q' lab => Sum.inr (q', lab.val, false)
        | VOut.halt lab => Sum.inl lab.val
        | VOut.nil => Sum.inl [] := rfl

lemma pathTrans_step_readR_move {M : TwoWay A B Q} {l r : Option (CLet Q (Lab M))} {q q' : Q}
    {lab : Lab M} (h : readR r q = VOut.move q' lab) :
    (pathTrans M).step l q r = Sum.inr (q', lab.val, true) := by
  rw [pathTrans_step, h]

lemma pathTrans_step_readR_halt {M : TwoWay A B Q} {l r : Option (CLet Q (Lab M))} {q : Q}
    {lab : Lab M} (h : readR r q = VOut.halt lab) :
    (pathTrans M).step l q r = Sum.inl lab.val := by
  rw [pathTrans_step, h]

lemma pathTrans_step_readL_move {M : TwoWay A B Q} {l r : Option (CLet Q (Lab M))} {q q' : Q}
    {lab : Lab M} (hr : readR r q = VOut.nil) (h : readL l q = VOut.move q' lab) :
    (pathTrans M).step l q r = Sum.inr (q', lab.val, false) := by
  rw [pathTrans_step, hr, h]

lemma pathTrans_step_readL_halt {M : TwoWay A B Q} {l r : Option (CLet Q (Lab M))} {q : Q}
    {lab : Lab M} (hr : readR r q = VOut.nil) (h : readL l q = VOut.halt lab) :
    (pathTrans M).step l q r = Sum.inl lab.val := by
  rw [pathTrans_step, hr, h]

/-- The configuration of `pathTrans M` that corresponds to a configuration of `M`. -/
noncomputable def encCfg (M : TwoWay A B Q) (w : List A) :
    Cfg A Q → Cfg (CLet Q (Lab M)) Q
  | Cfg.conf u q _ => Cfg.conf ((enc M w).take u.length) q ((enc M w).drop u.length)
  | Cfg.halt => Cfg.halt

@[simp] lemma encCfg_halt (M : TwoWay A B Q) (w : List A) :
    encCfg M w Cfg.halt = Cfg.halt := rfl

@[simp] lemma encCfg_conf (M : TwoWay A B Q) (w u v : List A) (q : Q) :
    encCfg M w (Cfg.conf u q v) =
      Cfg.conf ((enc M w).take u.length) q ((enc M w).drop u.length) := rfl

end TwoWay

end Lax916827Proofs.Transducers
