/-
**Reading the snake graph locally.**

The edges at a column `x` of the graph described by a string `w` over the alphabet
`Transducers.SnakeLetter` are carried by the two letters around that column: the letter at position
`x - 1` (`SnakeLoc.prevAt w x`) and the letter at position `x` (`w[x]?`).  This file expresses the
data of the column -- the outgoing edges of its vertices, their incoming edges, which of them are
sources and which of them carry an edge at all -- as functions of that pair of letters, and proves
that these local readings agree with the global definitions of
`RequestProject/PartC/SnakeAlph.lean`.

This is what makes the conditions "in-degree and out-degree at most one" and "no column is visited
more than `k` times" conditions on *pairs of consecutive letters*, hence regular
(`RequestProject/PartC/SnakeAlphLocLang.lean`), and it is also how the two-way transducer of
`RequestProject/PartC/SnakeAlphRun.lean` decides where to go next.
-/
import Lax916827Proofs.Source.PartC.SnakeAlph
import Lax916827Proofs.Source.PartC.SnakeLocLang
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace SnakeGraph

variable {Q B : Type}

/-- The letter to the left of the column `x`, i.e. the letter at position `x - 1`. -/
abbrev prevLet (w : List (SnakeLetter Q B)) (x : ℕ) : Option (SnakeLetter Q B) :=
  SnakeLoc.prevAt w x

/-- The outgoing edge of the vertex `(q, x)` that crosses to the column `x + 1`, read off the letter
`r` at the position `x`. -/
def outR (r : Option (SnakeLetter Q B)) (q : Q) : Option (Q × Option B) :=
  r.bind (fun c => c (false, q))

/-- The outgoing edge of the vertex `(q, x)` that crosses to the column `x - 1`, read off the letter
`l` at the position `x - 1`. -/
def outL (l : Option (SnakeLetter Q B)) (q : Q) : Option (Q × Option B) :=
  l.bind (fun c => c (true, q))

/-- The vertex `(q, x)` has an outgoing edge, read off the letters around the column `x`. -/
def HasOutAt (l r : Option (SnakeLetter Q B)) (q : Q) : Prop :=
  (outR r q).isSome ∨ (outL l q).isSome

/-- The vertex `(q, x)` has an incoming edge, read off the letters around the column `x`: either
from the column `x - 1`, by an edge of the letter `l` that crosses to the right, or from the column
`x + 1`, by an edge of the letter `r` that crosses to the left. -/
def HasInAt (l r : Option (SnakeLetter Q B)) (q : Q) : Prop :=
  (∃ p o, outR l p = some (q, o)) ∨ (∃ p o, outL r p = some (q, o))

/-- The vertex `(q, x)` is a source, read off the letters around the column `x`. -/
def IsSrcAt (l r : Option (SnakeLetter Q B)) (q : Q) : Prop :=
  HasOutAt l r q ∧ ¬ HasInAt l r q

/-- The vertex `(q, x)` carries an edge, read off the letters around the column `x`. -/
def IncidentAt (l r : Option (SnakeLetter Q B)) (q : Q) : Prop :=
  HasOutAt l r q ∨ HasInAt l r q

/-! ## The local readings agree with the graph -/

variable {w : List (SnakeLetter Q B)}

@[simp] lemma prevLet_zero : prevLet w 0 = none := rfl

lemma prevLet_succ (y : ℕ) : prevLet w (y + 1) = w[y]? := by
  simp [SnakeLoc.prevAt]

lemma edge_right_iff {q q' : Q} {x : ℕ} {o : Option B} :
    Edge w (q, x) (q', x + 1) o ↔ outR w[x]? q = some (q', o) := by
  constructor
  · rintro (⟨-, c, hc, hcq⟩ | ⟨hx, -⟩)
    · rw [outR, hc]; exact hcq
    · omega
  · intro h
    refine Or.inl ⟨rfl, ?_⟩
    rcases hc : w[x]? with _ | c
    · rw [outR, hc] at h; exact absurd h (by simp)
    · exact ⟨c, rfl, by rw [outR, hc] at h; exact h⟩

lemma edge_left_iff {q q' : Q} {y : ℕ} {o : Option B} :
    Edge w (q, y + 1) (q', y) o ↔ outL (prevLet w (y + 1)) q = some (q', o) := by
  rw [prevLet_succ]
  constructor
  · rintro (⟨hx, -⟩ | ⟨-, c, hc, hcq⟩)
    · omega
    · rw [outL, hc]; exact hcq
  · intro h
    refine Or.inr ⟨rfl, ?_⟩
    rcases hc : w[y]? with _ | c
    · rw [outL, hc] at h; exact absurd h (by simp)
    · exact ⟨c, rfl, by rw [outL, hc] at h; exact h⟩

/-- An edge goes to the next or to the previous column. -/
lemma edge_col {v v' : Vtx Q} {o : Option B} (h : Edge w v v' o) :
    v'.2 = v.2 + 1 ∨ v.2 = v'.2 + 1 := by
  rcases h with ⟨h, -⟩ | ⟨h, -⟩
  · exact Or.inl h
  · exact Or.inr h

lemma hasOut_iff {q : Q} {x : ℕ} : HasOut w (q, x) ↔ HasOutAt (prevLet w x) w[x]? q := by
  constructor
  · rintro ⟨v', o, hv⟩
    rcases edge_col hv with hc | hc
    · left
      have hv' : Edge w (q, x) (v'.1, x + 1) o := by
        rwa [show ((v'.1, x + 1) : Vtx Q) = v' by
          rw [Prod.ext_iff]; exact ⟨rfl, by simpa using hc.symm⟩]
      rw [edge_right_iff.1 hv']
      exact rfl
    · right
      obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨v'.2, by simpa using hc⟩
      have hc' : y + 1 = v'.2 + 1 := hc
      have hv2 : v'.2 = y := by omega
      have hv' : Edge w (q, y + 1) (v'.1, y) o := by
        rwa [show ((v'.1, y) : Vtx Q) = v' by rw [Prod.ext_iff]; exact ⟨rfl, hv2.symm⟩]
      rw [edge_left_iff.1 hv']
      exact rfl
  · rintro (h | h)
    · obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 h
      exact ⟨(z.1, x + 1), z.2, edge_right_iff.2 (by rw [hz])⟩
    · obtain ⟨z, hz⟩ := Option.isSome_iff_exists.1 h
      rcases Nat.eq_zero_or_pos x with rfl | hpos
      · rw [outL, prevLet_zero] at hz; exact absurd hz (by simp)
      · obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
        exact ⟨(z.1, y), z.2, edge_left_iff.2 (by rw [hz])⟩

lemma hasIn_iff {q : Q} {x : ℕ} : HasIn w (q, x) ↔ HasInAt (prevLet w x) w[x]? q := by
  constructor
  · rintro ⟨u, o, hu⟩
    rcases edge_col hu with hc | hc
    · -- `u` is in the column `x - 1` and the edge crosses to the right
      left
      have hx : x = u.2 + 1 := by simpa using hc
      subst hx
      have hu' : Edge w (u.1, u.2) (q, u.2 + 1) o := by rwa [show (u.1, u.2) = u from rfl]
      exact ⟨u.1, o, by rw [prevLet_succ]; exact edge_right_iff.1 hu'⟩
    · -- `u` is in the column `x + 1` and the edge crosses to the left
      right
      have hx : u.2 = x + 1 := by simpa using hc
      have hu' : Edge w (u.1, x + 1) (q, x) o := by
        rwa [show ((u.1, x + 1) : Vtx Q) = u by rw [Prod.ext_iff]; exact ⟨rfl, hx.symm⟩]
      have := edge_left_iff (w := w) (q := u.1) (q' := q) (y := x) (o := o) |>.1 hu'
      rw [prevLet_succ] at this
      exact ⟨u.1, o, this⟩
  · rintro (⟨p, o, hp⟩ | ⟨p, o, hp⟩)
    · rcases Nat.eq_zero_or_pos x with rfl | hpos
      · rw [outR, prevLet_zero] at hp; exact absurd hp (by simp)
      · obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
        rw [prevLet_succ] at hp
        exact ⟨(p, y), o, edge_right_iff.2 hp⟩
    · exact ⟨(p, x + 1), o, edge_left_iff.2 (by rw [prevLet_succ]; exact hp)⟩

/-- The two shapes of an outgoing edge of `(q, x)`. -/
lemma edge_out_cases {q : Q} {x : ℕ} {v' : Vtx Q} {o : Option B} (h : Edge w (q, x) v' o) :
    (v'.2 = x + 1 ∧ outR w[x]? q = some (v'.1, o)) ∨
      (x = v'.2 + 1 ∧ outL (prevLet w x) q = some (v'.1, o)) := by
  rcases edge_col h with hc | hc
  · have hc' : v'.2 = x + 1 := by simpa using hc
    refine Or.inl ⟨hc', ?_⟩
    have hv' : Edge w (q, x) (v'.1, x + 1) o := by
      rwa [show ((v'.1, x + 1) : Vtx Q) = v' by rw [Prod.ext_iff]; exact ⟨rfl, hc'.symm⟩]
    exact edge_right_iff.1 hv'
  · have hc' : x = v'.2 + 1 := by simpa using hc
    refine Or.inr ⟨hc', ?_⟩
    subst hc'
    have hv' : Edge w (q, v'.2 + 1) (v'.1, v'.2) o := by
      rwa [show ((v'.1, v'.2) : Vtx Q) = v' from rfl]
    exact edge_left_iff.1 hv'

/-- The two shapes of an incoming edge of `(q, x)`. -/
lemma edge_in_cases {q : Q} {x : ℕ} {u : Vtx Q} {o : Option B} (h : Edge w u (q, x) o) :
    (x = u.2 + 1 ∧ outR (prevLet w x) u.1 = some (q, o)) ∨
      (u.2 = x + 1 ∧ outL w[x]? u.1 = some (q, o)) := by
  rcases edge_col h with hc | hc
  · have hc' : x = u.2 + 1 := by simpa using hc
    refine Or.inl ⟨hc', ?_⟩
    subst hc'
    have hu' : Edge w (u.1, u.2) (q, u.2 + 1) o := by rwa [show (u.1, u.2) = u from rfl]
    rw [prevLet_succ]
    exact edge_right_iff.1 hu'
  · have hc' : u.2 = x + 1 := by simpa using hc
    refine Or.inr ⟨hc', ?_⟩
    have hu' : Edge w (u.1, x + 1) (q, x) o := by
      rwa [show ((u.1, x + 1) : Vtx Q) = u by rw [Prod.ext_iff]; exact ⟨rfl, hc'.symm⟩]
    have := edge_left_iff (w := w) (q := u.1) (q' := q) (y := x) (o := o) |>.1 hu'
    rwa [prevLet_succ] at this

lemma edge_of_outR {q q' : Q} {x : ℕ} {o : Option B} (h : outR w[x]? q = some (q', o)) :
    Edge w (q, x) (q', x + 1) o := edge_right_iff.2 h

lemma edge_of_outL {q q' : Q} {y : ℕ} {o : Option B}
    (h : outL (prevLet w (y + 1)) q = some (q', o)) : Edge w (q, y + 1) (q', y) o :=
  edge_left_iff.2 h

/-- Beyond the end of the string there is no letter on either side of a column. -/
lemma letters_none_of_lt {x : ℕ} (h : w.length < x) : prevLet w x = none ∧ w[x]? = none := by
  refine ⟨?_, List.getElem?_eq_none (by omega)⟩
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  rw [prevLet_succ]
  exact List.getElem?_eq_none (by omega)

@[simp] lemma outR_none (q : Q) : outR (none : Option (SnakeLetter Q B)) q = none := rfl

@[simp] lemma outL_none (q : Q) : outL (none : Option (SnakeLetter Q B)) q = none := rfl

lemma src_iff {q : Q} {x : ℕ} : Src w (q, x) ↔ IsSrcAt (prevLet w x) w[x]? q := by
  rw [Src, IsSrcAt, hasOut_iff, hasIn_iff]

lemma incident_iff {q : Q} {x : ℕ} : Incident w (q, x) ↔ IncidentAt (prevLet w x) w[x]? q := by
  rw [Incident, IncidentAt, hasOut_iff, hasIn_iff]

end SnakeGraph

end Lax916827Proofs.Transducers
