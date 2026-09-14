/-
**From a configuration to its child configuration graph, and to its children.**

This file finishes the route of Section D.2 of *Transducers* (M. Bojańczyk):

* Claim `claim:from-configuration-to-child-configuration-graph` -- there is a for-transducer which
  inputs the string representation of a configuration and outputs the string representation of its
  child configuration graph.  As the book says, the function is in fact *rational*; that is how it
  is obtained here, from the atoms of `RequestProject/PartD/CGAtom.lean` through
  `Transducers.MarkRat.isRationalFun_of_atoms`.
* Lemma `lem:children-of-configuration-in-pebble-run` -- there is a for-transducer which inputs the
  string representation of a configuration and outputs the concatenation of the string
  representations of its children, in order of execution.  This is the composition of the previous
  claim with Claim `claim:from-child-configuration-graph-to-children`
  (`Transducers.from_child_configuration_graph_to_children`), exactly as the book concludes.
-/
import Lax194892Proofs.Source.PartD.CGSem
import Lax194892Proofs.Source.PartD.ChildGraphFor
import Lax194892Proofs.Source.PartC.MarkRat
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers
open Lax314295Proofs Lax314295Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace CGL

open MarkStr RegAut Pebble

open scoped Classical

variable {A B Q : Type} {k : ℕ}

/-! ## Directions and columns -/

/-- The direction opposite to a given one. -/
def revDir : CG.Dir → CG.Dir := Option.map not

@[simp] lemma colOf_none (x : ℕ) : colOf x none = x := rfl

lemma colOf_dirOf {x c : ℕ} (h₁ : c ≤ x + 1) (h₂ : x ≤ c + 1) : colOf x (CG.dirOf x c) = c := by
  rcases lt_trichotomy c x with h | h | h
  · rw [CG.dirOf_pred h]
    show x - 1 = c
    omega
  · subst h
    rw [CG.dirOf_self]
    rfl
  · rw [show c = x + 1 from by omega, CG.dirOf_succ]
    rfl

lemma spotOk_dirOf {x c n : ℕ} (h₁ : c ≤ x + 1) (h₂ : x ≤ c + 1) (hc : c ≤ n) :
    SpotOk (spotOfDir (CG.dirOf x c)) x n := by
  rcases lt_trichotomy c x with h | h | h
  · rw [CG.dirOf_pred h]
    show 1 ≤ x
    omega
  · subst h
    rw [CG.dirOf_self]
    trivial
  · rw [show c = x + 1 from by omega, CG.dirOf_succ]
    show x + 1 ≤ n
    omega

lemma revDir_dirOf {x c : ℕ} (h₁ : c ≤ x + 1) (h₂ : x ≤ c + 1) :
    revDir (CG.dirOf x c) = CG.dirOf c x := by
  rcases lt_trichotomy c x with h | h | h
  · rw [CG.dirOf_pred h, show x = c + 1 from by omega, CG.dirOf_succ]
    rfl
  · subst h
    rw [CG.dirOf_self]
    rfl
  · rw [show c = x + 1 from by omega, CG.dirOf_succ, CG.dirOf_pred (by omega)]
    rfl

/-! ## The finite family of atoms -/

/-- **The index type of the atoms** of the child configuration graph. -/
abbrev AtomIdx (A Q : Type) (k : ℕ) : Type :=
  Fin k ⊕ Q ⊕ Option A ⊕ Fin k ⊕ Unit ⊕ (Fin k × Q × Q) ⊕ (Fin k × Q × CG.Dir × Q × CG.Dir)

/-- The index of the atom `Transducers.CGL.hgtL`. -/
def iHgt (i : Fin k) : AtomIdx A Q k := Sum.inl i

/-- The index of the atom `Transducers.CGL.stateL`. -/
def iState (q : Q) : AtomIdx A Q k := Sum.inr (Sum.inl q)

/-- The index of the atom `Transducers.CGL.lettL`. -/
def iLett (a : Option A) : AtomIdx A Q k := Sum.inr (Sum.inr (Sum.inl a))

/-- The index of the atom `Transducers.CGL.pebL`. -/
def iPeb (i : Fin k) : AtomIdx A Q k := Sum.inr (Sum.inr (Sum.inr (Sum.inl i)))

/-- The index of the atom `Transducers.CGL.zeroL`. -/
def iZero : AtomIdx A Q k := Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl ()))))

/-- The index of the atom `Transducers.CGL.firstL`. -/
def iFirst (nid : Fin k) (q q' : Q) : AtomIdx A Q k :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl (nid, q, q'))))))

/-- The index of the atom `Transducers.CGL.edgeL`. -/
def iEdge (nid : Fin k) (qa : Q) (da : CG.Dir) (qb : Q) (db : CG.Dir) : AtomIdx A Q k :=
  Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (nid, qa, da, qb, db))))))

/-- **The atoms of the child configuration graph**, as a family indexed by a finite type. -/
noncomputable def atomOf (M : Pebble A B Q k) : AtomIdx A Q k → Language (MLetter A Q k)
  | Sum.inl i => hgtL i
  | Sum.inr (Sum.inl q) => stateL q
  | Sum.inr (Sum.inr (Sum.inl a)) => lettL a
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) => pebL i
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))) => zeroL
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))))) => firstL M p.1 p.2.1 p.2.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr p))))) =>
      edgeL M p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

variable [Finite A] [Finite Q]

lemma atomOf_isRegular (M : Pebble A B Q k) :
    ∀ j : AtomIdx A Q k, (atomOf M j).IsRegular
  | Sum.inl i => hgtL_isRegular i
  | Sum.inr (Sum.inl q) => stateL_isRegular q
  | Sum.inr (Sum.inr (Sum.inl a)) => lettL_isRegular a
  | Sum.inr (Sum.inr (Sum.inr (Sum.inl i))) => pebL_isRegular i
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl _)))) => zeroL_isRegular
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inl p))))) =>
      firstL_isRegular M p.1 p.2.1 p.2.2
  | Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr p))))) =>
      edgeL_isRegular M p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2

/-- The vector of truth values of the atoms in the position `x` of the string `u`. -/
noncomputable def bitsOf (M : Pebble A B Q k) (u : List (CG.ConfLetter A Q k)) (x : ℕ)
    (j : AtomIdx A Q k) : Bool := decide (markAt2 u x x ∈ atomOf M j)

omit [Finite A] [Finite Q] in
lemma bitsOf_eq_true_iff (M : Pebble A B Q k) (u : List (CG.ConfLetter A Q k)) (x : ℕ)
    (j : AtomIdx A Q k) : bitsOf M u x j = true ↔ markAt2 u x x ∈ atomOf M j := by
  simp [bitsOf]

/-! ## The letter that the atoms produce -/

/-- The number of pebbles of the stack, read off the `hgt` atoms. -/
noncomputable def hgtCount (d : AtomIdx A Q k → Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin k => d (iHgt i) = true)).card

/-- **The letter of the child configuration graph** that the vector of truth values `d` of the
atoms produces, for the moving pebble `nid`. -/
noncomputable def outLetter (d : AtomIdx A Q k → Bool) (nid : Fin k) : CG.CGLetter A Q k where
  lett := if ha : ∃ a : Option A, d (iLett a) = true then ha.choose else none
  peb := fun i => d (iPeb i)
  nid := nid
  src := fun q' => d iZero &&
    decide (∃ q : Q, d (iState q) = true ∧ d (iFirst nid q q') = true)
  nxt := fun q' =>
    if he : ∃ p : Q × CG.Dir, d (iEdge nid q' none p.1 p.2) = true then some he.choose else none
  prv := fun q' =>
    if he : ∃ p : Q × CG.Dir, d (iEdge nid p.1 p.2 q' none) = true
      then some (he.choose.1, revDir he.choose.2) else none

/-- **The output of the rational function in one position of the input.** -/
noncomputable def outOf (d : AtomIdx A Q k → Bool) : List (CG.CGLetter A Q k) :=
  if h : hgtCount d < k then [outLetter d ⟨hgtCount d, h⟩] else []

/-- **The rational function** that maps the string representation of a configuration to the string
representation of its child configuration graph. -/
noncomputable def cgOfConf (M : Pebble A B Q k) (u : List (CG.ConfLetter A Q k)) :
    List (CG.CGLetter A Q k) :=
  if u = [] then [] else ((List.range u.length).map fun x => outOf (bitsOf M u x)).flatten

theorem isRationalFun_cgOfConf (M : Pebble A B Q k) : IsRationalFun (cgOfConf M) :=
  MarkRat.isRationalFun_of_atoms (atom := atomOf M) (atomOf_isRegular M) outOf []
    (bitsOf M) (bitsOf_eq_true_iff M) (cgOfConf M) (fun _ => rfl)

/-! ## The letter that the atoms produce is the letter of the child configuration graph -/

section Correct

variable {M : Pebble A B Q k} {q₀ : Q} {st : List ℕ} {w : List A} {ch : ℕ → CG.Vtx Q} {m : ℕ}
  {nid : Fin k} {x : ℕ}

/-- The letter that the child configuration graph attaches to the gap `j`. -/
noncomputable def cgLetterAt (w : List A) (st : List ℕ) (nid : Fin k) (ch : ℕ → CG.Vtx Q)
    (m j : ℕ) : CG.CGLetter A Q k where
  lett := w[j]?
  peb := PebEnc.ann k st j
  nid := nid
  src := fun q' => decide ((q', j) = ch 0)
  nxt := fun q' => (CG.idxAt ch m (q', j)).map fun t => ((ch (t + 1)).1, CG.dirOf j (ch (t + 1)).2)
  prv := fun q' => (CG.idxSuccAt ch m (q', j)).map fun t => ((ch t).1, CG.dirOf (ch t).2 j)

omit [Finite A] [Finite Q] in
lemma cgOfChildren_eq_map :
    CG.cgOfChildren (k := k) w st nid ch m
      = (List.range (w.length + 1)).map (cgLetterAt w st nid ch m) := rfl

variable (hseq : CG.IsChildSeq M w q₀ st ch m) (hnid : (nid : ℕ) = st.length)
  (hstk : st.length < k) (hstb : ∀ p ∈ st, p ≤ w.length) (hx : x ≤ w.length)

include hseq hnid hstk hstb hx

omit [Finite A] [Finite Q] in
lemma bits_edge (qa : Q) (da : CG.Dir) (qb : Q) (db : CG.Dir) :
    bitsOf M (CG.confEnc q₀ st w) x (iEdge nid qa da qb db) = true ↔
      SpotOk (spotOfDir da) x w.length ∧ SpotOk (spotOfDir db) x w.length ∧
        CG.ChildStar M w st (ch 0) (qa, colOf x da) ∧
        CG.NextChild M w st (qa, colOf x da) (qb, colOf x db) := by
  rw [bitsOf_eq_true_iff]
  exact mem_edgeL_iff M hseq hnid hstk hstb hx

omit [Finite A] [Finite Q] in
/-- The outgoing edge produced by the atoms is the one of the child configuration graph. -/
lemma outLetter_nxt (q' : Q) :
    (if he : ∃ p : Q × CG.Dir,
        bitsOf M (CG.confEnc q₀ st w) x (iEdge nid q' none p.1 p.2) = true
      then some he.choose else none)
      = (CG.idxAt ch m (q', x)).map fun t => ((ch (t + 1)).1, CG.dirOf x (ch (t + 1)).2) := by
  have hd_edge := bits_edge hseq hnid hstk hstb hx
  cases hidx : CG.idxAt ch m (q', x) with
  | none =>
      have hno : ¬ ∃ p : Q × CG.Dir,
          bitsOf M (CG.confEnc q₀ st w) x (iEdge nid q' none p.1 p.2) = true := by
        rintro ⟨p, hp⟩
        obtain ⟨-, -, hcs, hnc⟩ := (hd_edge q' none p.1 p.2).1 hp
        rw [colOf_none] at hcs hnc
        obtain ⟨s, hsm, hchs⟩ := (CG.childStar_iff_mem hseq _).1 hcs
        have hslt : s < m := by
          by_contra hcon
          have hsm' : s = m := by omega
          subst hsm'
          exact hseq.stop _ (by rw [hchs]; exact hnc)
        rw [← hchs, CG.idxAt_eq_some hseq.distinct hslt] at hidx
        simp at hidx
      rw [dif_neg hno, Option.map_none]
  | some t =>
      obtain ⟨htm, hcht⟩ := CG.idxAt_spec hidx
      have hnext : CG.NextChild M w st (ch t) (ch (t + 1)) := hseq.next t htm
      have hxt : (ch t).2 = x := congrArg Prod.snd hcht
      obtain ⟨hadj1, hadj2⟩ := hnext.column_adjacent
      have hcle : (ch (t + 1)).2 ≤ w.length := hseq.column_le (t + 1) (by omega)
      have hspot : SpotOk (spotOfDir (CG.dirOf x (ch (t + 1)).2)) x w.length :=
        spotOk_dirOf (by omega) (by omega) hcle
      have hcolc : colOf x (CG.dirOf x (ch (t + 1)).2) = (ch (t + 1)).2 :=
        colOf_dirOf (by omega) (by omega)
      have hcs0 : CG.ChildStar M w st (ch 0) (q', colOf x none) := by
        rw [colOf_none, ← hcht]
        exact hseq.childStar (le_of_lt htm)
      have hnc0 : CG.NextChild M w st (q', colOf x none)
          ((ch (t + 1)).1, colOf x (CG.dirOf x (ch (t + 1)).2)) := by
        rw [colOf_none, hcolc, Prod.mk.eta, ← hcht]
        exact hnext
      have hex : ∃ p : Q × CG.Dir,
          bitsOf M (CG.confEnc q₀ st w) x (iEdge nid q' none p.1 p.2) = true :=
        ⟨((ch (t + 1)).1, CG.dirOf x (ch (t + 1)).2),
          (hd_edge q' none _ _).2 ⟨trivial, hspot, hcs0, hnc0⟩⟩
      rw [dif_pos hex, Option.map_some]
      congr 1
      obtain ⟨-, hsp2, -, hnc2⟩ :=
        (hd_edge q' none hex.choose.1 hex.choose.2).1 hex.choose_spec
      rw [colOf_none] at hnc2
      have huniq : (hex.choose.1, colOf x hex.choose.2) = ch (t + 1) := by
        refine hnc2.unique ?_
        rw [← hcht]
        exact hnext
      have h1 : hex.choose.1 = (ch (t + 1)).1 := by rw [← huniq]
      have h2 : colOf x hex.choose.2 = (ch (t + 1)).2 := by rw [← huniq]
      refine Prod.ext h1 ?_
      refine colOf_inj hsp2 hspot ?_
      rw [h2, hcolc]

omit [Finite A] [Finite Q] in
/-- The incoming edge produced by the atoms is the one of the child configuration graph. -/
lemma outLetter_prv (q' : Q) :
    (if he : ∃ p : Q × CG.Dir,
        bitsOf M (CG.confEnc q₀ st w) x (iEdge nid p.1 p.2 q' none) = true
      then some (he.choose.1, revDir he.choose.2) else none)
      = (CG.idxSuccAt ch m (q', x)).map fun t => ((ch t).1, CG.dirOf (ch t).2 x) := by
  have hd_edge := bits_edge hseq hnid hstk hstb hx
  cases hidx : CG.idxSuccAt ch m (q', x) with
  | none =>
      have hno : ¬ ∃ p : Q × CG.Dir,
          bitsOf M (CG.confEnc q₀ st w) x (iEdge nid p.1 p.2 q' none) = true := by
        rintro ⟨p, hp⟩
        obtain ⟨-, -, hcs, hnc⟩ := (hd_edge p.1 p.2 q' none).1 hp
        rw [colOf_none] at hnc
        obtain ⟨s, hsm, hchs⟩ := (CG.childStar_iff_mem hseq _).1 hcs
        rw [← hchs] at hnc
        have hslt : s < m := by
          by_contra hcon
          have hsm' : s = m := by omega
          subst hsm'
          exact hseq.stop _ hnc
        have hsucc : ((q', x) : CG.Vtx Q) = ch (s + 1) := hnc.unique (hseq.next s hslt)
        rw [hsucc, CG.idxSuccAt_eq_some hseq.distinct hslt] at hidx
        simp at hidx
      rw [dif_neg hno, Option.map_none]
  | some t =>
      obtain ⟨htm, hcht⟩ := CG.idxSuccAt_spec hidx
      have hnext : CG.NextChild M w st (ch t) (ch (t + 1)) := hseq.next t htm
      have hxt : (ch (t + 1)).2 = x := congrArg Prod.snd hcht
      obtain ⟨hadj1, hadj2⟩ := hnext.column_adjacent
      have hcle : (ch t).2 ≤ w.length := hseq.column_le t (by omega)
      have hspot : SpotOk (spotOfDir (CG.dirOf x (ch t).2)) x w.length :=
        spotOk_dirOf (by omega) (by omega) hcle
      have hcolc : colOf x (CG.dirOf x (ch t).2) = (ch t).2 := colOf_dirOf (by omega) (by omega)
      have hcs0 : CG.ChildStar M w st (ch 0) ((ch t).1, colOf x (CG.dirOf x (ch t).2)) := by
        rw [hcolc, Prod.mk.eta]
        exact hseq.childStar (by omega)
      have hnc0 : CG.NextChild M w st ((ch t).1, colOf x (CG.dirOf x (ch t).2))
          (q', colOf x none) := by
        rw [hcolc, Prod.mk.eta, colOf_none, ← hcht]
        exact hnext
      have hex : ∃ p : Q × CG.Dir,
          bitsOf M (CG.confEnc q₀ st w) x (iEdge nid p.1 p.2 q' none) = true :=
        ⟨((ch t).1, CG.dirOf x (ch t).2), (hd_edge _ _ q' none).2 ⟨hspot, trivial, hcs0, hnc0⟩⟩
      rw [dif_pos hex, Option.map_some]
      congr 1
      obtain ⟨hsp2, -, hcs2, hnc2⟩ :=
        (hd_edge hex.choose.1 hex.choose.2 q' none).1 hex.choose_spec
      rw [colOf_none] at hnc2
      obtain ⟨s, hsm, hchs⟩ := (CG.childStar_iff_mem hseq _).1 hcs2
      rw [← hchs] at hnc2
      have hslt : s < m := by
        by_contra hcon
        have hsm' : s = m := by omega
        subst hsm'
        exact hseq.stop _ hnc2
      have hsucc : ((q', x) : CG.Vtx Q) = ch (s + 1) := hnc2.unique (hseq.next s hslt)
      have hst : s = t := by
        have h1 : ch (s + 1) = ch (t + 1) := by rw [← hsucc, hcht]
        have := hseq.distinct (s + 1) (t + 1) (by omega) (by omega) h1
        omega
      subst hst
      have h1 : hex.choose.1 = (ch s).1 := by rw [hchs]
      have h2 : colOf x hex.choose.2 = (ch s).2 := by rw [hchs]
      have h3 : hex.choose.2 = CG.dirOf x (ch s).2 := by
        refine colOf_inj hsp2 hspot ?_
        rw [h2, hcolc]
      rw [Prod.mk.injEq]
      refine ⟨h1, ?_⟩
      rw [h3, revDir_dirOf (by omega) (by omega)]

omit [Finite A] [Finite Q] in
/-- **The letter produced by the atoms in the gap `x` is the letter that the child configuration
graph attaches to that gap.** -/
theorem outOf_bitsOf :
    outOf (bitsOf M (CG.confEnc q₀ st w) x) = [cgLetterAt w st nid ch m x] := by
  have hd_hgt : ∀ i : Fin k,
      bitsOf M (CG.confEnc q₀ st w) x (iHgt i) = true ↔ (i : ℕ) < st.length := fun i => by
    rw [bitsOf_eq_true_iff]
    exact mem_hgtL_iff i hstb
  have hd_state : ∀ q : Q,
      bitsOf M (CG.confEnc q₀ st w) x (iState q) = true ↔ q = q₀ := fun q => by
    rw [bitsOf_eq_true_iff]
    exact mem_stateL_iff q
  have hd_lett : ∀ a : Option A,
      bitsOf M (CG.confEnc q₀ st w) x (iLett a) = true ↔ a = w[x]? := fun a => by
    rw [bitsOf_eq_true_iff]
    exact mem_lettL_iff a hx
  have hd_peb : ∀ i : Fin k,
      bitsOf M (CG.confEnc q₀ st w) x (iPeb i) = true ↔ PebEnc.ann k st x i = true := fun i => by
    rw [bitsOf_eq_true_iff]
    exact mem_pebL_iff i hx
  have hd_zero : bitsOf M (CG.confEnc q₀ st w) x iZero = true ↔ x = 0 := by
    rw [bitsOf_eq_true_iff]
    exact mem_zeroL_iff hx
  have hd_first : ∀ q q' : Q,
      bitsOf M (CG.confEnc q₀ st w) x (iFirst nid q q') = true ↔
        CG.FirstChild M w q st (q', 0) := fun q q' => by
    rw [bitsOf_eq_true_iff]
    exact mem_firstL_iff M hnid hstk hstb hx hx
  have hcnt : hgtCount (bitsOf M (CG.confEnc q₀ st w) x) = st.length := by
    rw [hgtCount]
    have he : (Finset.univ.filter
          (fun i : Fin k => bitsOf M (CG.confEnc q₀ st w) x (iHgt i) = true))
        = (Finset.range st.length).attachFin (fun i hi => by
            simp only [Finset.mem_range] at hi; omega) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_attachFin,
        Finset.mem_range]
      exact hd_hgt i
    rw [he, Finset.card_attachFin, Finset.card_range]
  have hfin : (⟨st.length, hstk⟩ : Fin k) = nid := Fin.ext hnid.symm
  rw [outOf]
  simp only [hcnt]
  rw [dif_pos hstk, hfin]
  congr 1
  rw [outLetter, cgLetterAt]
  simp only [CG.CGLetter.mk.injEq]
  refine ⟨?_, ?_, trivial, ?_, ?_, ?_⟩
  · have hexa : ∃ a : Option A, bitsOf M (CG.confEnc q₀ st w) x (iLett a) = true :=
      ⟨w[x]?, (hd_lett _).2 rfl⟩
    rw [dif_pos hexa]
    exact (hd_lett _).1 hexa.choose_spec
  · funext i
    exact Bool.eq_iff_iff.2 (hd_peb i)
  · funext q'
    refine Bool.eq_iff_iff.2 ?_
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, hd_zero]
    constructor
    · rintro ⟨hx0, q, hq, hf⟩
      have hqq : q = q₀ := (hd_state q).1 hq
      subst hqq
      have hfc : CG.FirstChild M w q st (q', 0) := (hd_first q q').1 hf
      have h0 : ((q', 0) : CG.Vtx Q) = ch 0 := hfc.unique hseq.first
      rw [hx0]
      exact h0
    · intro h0
      have hcol : (ch 0).2 = 0 := hseq.first.column_zero
      have h2 : x = (ch 0).2 := congrArg Prod.snd h0
      have hx0 : x = 0 := by omega
      refine ⟨hx0, q₀, (hd_state q₀).2 rfl, (hd_first q₀ q').2 ?_⟩
      have heq : ((q', 0) : CG.Vtx Q) = ch 0 := by rw [← h0, hx0]
      rw [heq]
      exact hseq.first
  · funext q'
    exact outLetter_nxt hseq hnid hstk hstb hx q'
  · funext q'
    exact outLetter_prv hseq hnid hstk hstb hx q'

end Correct

/-! ## The rational function on genuine configuration encodings -/

lemma flatten_map_singleton {alpha beta : Type} (l : List alpha) (g : alpha → List beta)
    (f : alpha → beta) (h : ∀ a, a ∈ l → g a = [f a]) :
    (l.map g).flatten = l.map f := by
  induction l with
  | nil => simp
  | cons a t ih =>
      have ha : g a = [f a] := h a (by simp)
      have ht : (t.map g).flatten = t.map f := ih fun b hb => h b (by simp [hb])
      simp [ha, ht]

omit [Finite A] [Finite Q] in
/-- **On the string representation of a configuration, `cgOfConf` outputs the string
representation of the child configuration graph of that configuration.** -/
theorem cgOfConf_confEnc {M : Pebble A B Q k} {q₀ : Q} {st : List ℕ} {w : List A}
    {ch : ℕ → CG.Vtx Q} {m : ℕ} {nid : Fin k}
    (hseq : CG.IsChildSeq M w q₀ st ch m) (hnid : (nid : ℕ) = st.length)
    (hstk : st.length < k) (hstb : ∀ p, p ∈ st → p ≤ w.length) :
    cgOfConf M (CG.confEnc q₀ st w) = CG.cgOfChildren w st nid ch m := by
  have hlen := confEnc_length (k := k) q₀ st w
  have hne : CG.confEnc (k := k) q₀ st w ≠ [] := by
    intro h
    rw [h] at hlen
    simp at hlen
  rw [cgOfConf, if_neg hne, hlen, cgOfChildren_eq_map]
  refine flatten_map_singleton _ _ _ ?_
  intro x hx
  rw [List.mem_range] at hx
  exact outOf_bitsOf hseq hnid hstk hstb (by omega)

end CGL

/-- **Claim `claim:from-configuration-to-child-configuration-graph`.**  There is a for-transducer
which inputs the string representation of a configuration of a pebble transducer and outputs the
string representation of the child configuration graph of that configuration.

As in the book, the transducer is obtained as a *rational* function
(`Transducers.CGL.isRationalFun_cgOfConf`): the child configuration graph is described by finitely
many regular properties of the input and of the position being processed
(`RequestProject/PartD/CGAtom.lean`), and `Transducers.MarkRat.isRationalFun_of_atoms` turns such a
description into a rational function.

The hypothesis `st.length < k` is the one the book uses without stating it: a configuration whose
stack already has `k` pebbles has no children at all, so its child configuration graph is not the
graph considered here.  The hypothesis `(nid : ℕ) = st.length` merely records in the output
alphabet the height of the children's stacks, which is `st.length + 1`. -/
theorem from_configuration_to_child_configuration_graph
    {A B Q : Type} [Finite A] [Finite Q] {k : ℕ} (M : Pebble A B Q k) :
    ∃ f : List (CG.ConfLetter A Q k) → List (CG.CGLetter A Q k), IsForTransducer f ∧
      ∀ (q₀ : Q) (st : List ℕ) (w : List A) (ch : ℕ → CG.Vtx Q) (m : ℕ) (nid : Fin k),
        (∀ p, p ∈ st → p ≤ w.length) → st.length < k → (nid : ℕ) = st.length →
        CG.IsChildSeq M w q₀ st ch m →
        f (CG.confEnc q₀ st w) = CG.cgOfChildren w st nid ch m := by
  refine ⟨CGL.cgOfConf M, ?_, ?_⟩
  · exact (polyregular_iff_forTransducer _).1
      (IsPolyregular.of_regular (IsRegularFun.of_rational (CGL.isRationalFun_cgOfConf M)))
  · intro q₀ st w ch m nid hstb hstk hnid hseq
    exact CGL.cgOfConf_confEnc hseq hnid hstk hstb

/-- **Lemma `lem:children-of-configuration-in-pebble-run`.**  There is a for-transducer which inputs
the string representation of a configuration and outputs the concatenation of the string
representations of its children, in the order in which the run of the pebble transducer visits
them.

This is the composition of Claim `claim:from-configuration-to-child-configuration-graph`
(`Transducers.from_configuration_to_child_configuration_graph`) with Claim
`claim:from-child-configuration-graph-to-children`
(`Transducers.from_child_configuration_graph_to_children`), exactly as the book concludes; the
composition is a for-transducer by `Transducers.forTransducer_comp`.

As in that claim, the hypothesis `st.length < k` is the book's own case distinction: it says
explicitly that if the stack already has `k` pebbles then there can be no children. -/
theorem children_of_configuration_in_pebble_run
    {A B Q : Type} [Finite A] [Finite Q] {k : ℕ} (M : Pebble A B Q k) :
    ∃ f : List (CG.ConfLetter A Q k) → List (CG.ConfLetter A Q k), IsForTransducer f ∧
      ∀ (q₀ : Q) (st : List ℕ) (w : List A) (ch : ℕ → CG.Vtx Q) (m : ℕ),
        (∀ p, p ∈ st → p ≤ w.length) → st.length < k →
        CG.IsChildSeq M w q₀ st ch m →
        f (CG.confEnc q₀ st w)
          = ((List.range (m + 1)).map fun t => CG.confEnc (ch t).1 (st ++ [(ch t).2]) w).flatten
    := by
  obtain ⟨g, hg, hgspec⟩ := from_configuration_to_child_configuration_graph M
  obtain ⟨h, hh, hhspec⟩ :=
    from_child_configuration_graph_to_children (A := A) (Q := Q) k
  refine ⟨h ∘ g, forTransducer_comp hg hh, ?_⟩
  intro q₀ st w ch m hstb hstk hseq
  have hnid : ((⟨st.length, hstk⟩ : Fin k) : ℕ) = st.length := rfl
  have hgv := hgspec q₀ st w ch m ⟨st.length, hstk⟩ hstb hstk hnid hseq
  rw [Function.comp_apply, hgv]
  exact hhspec _ _ (CG.cgOutIs_cgOfChildren hseq hnid)

end Lax194892Proofs.Transducers
