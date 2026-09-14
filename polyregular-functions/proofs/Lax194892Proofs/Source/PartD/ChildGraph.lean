/-
**The string representation of a child configuration graph.**

Section D.2 of *Transducers* (M. Bojańczyk) proves Lemma
`lem:children-of-configuration-in-pebble-run` -- the children of a configuration of a pebble
transducer can be produced by a for-transducer -- by going through an auxiliary object, the *child
configuration graph*:

> The children of the input configuration can be described as a directed graph, in which an edge
> represents a run between two configurations of height `ℓ+1` that are not separated by any
> configuration of height `ℓ+1`.  [...]  The picture also contains additional annotation (in red),
> which gives us the input string and the positions of pebbles `{1,…,ℓ}` that stay fixed throughout
> the run.  We use the name *child configuration graph* for this graph.  The child configuration
> graph can be represented as a string over a fixed finite alphabet, whose length is the same as
> the input string.  This string contains the red annotation of the input string together with the
> positions of pebble `ℓ+1` in each child.

This file introduces that alphabet, `Transducers.CG.CGLetter`, and the graph a string over it
describes, in the style of `RequestProject/PartC/SnakeAlph.lean` (the alphabet of snake graphs) and
of `RequestProject/PartD/PebEnc.lean` (the string representation of a configuration).

A letter of the alphabet describes one **gap** of the input string of the pebble transducer, that
is, one *column* of the graph, and consists of

* `lett`: the input letter that follows the gap -- absent exactly for the last gap, so that a
  string of length `n + 1` describes an input string of length `n`;
* `peb`: the set of the fixed pebbles `1, …, ℓ` that sit in this gap (the book's red annotation);
* `nid`: the index of the pebble `ℓ + 1`, the one that moves from child to child;
* `src`: the set of states `q` such that `(q, this column)` is the first child in order of
  execution;
* `nxt`: for each state `q`, the outgoing edge of the vertex `(q, this column)` -- the state of the
  next child and the direction in which the column changes, which is one of `left`, `stay`,
  `right` (unlike the snake graphs of Part C, a child configuration graph may have edges inside a
  column, because the excursion between two consecutive children need not move pebble `ℓ + 1`);
* `prv`: for each state `q`, the *incoming* edge of the vertex `(q, this column)`, recorded in the
  same shape.

The last component is redundant -- an incoming edge is an outgoing edge of another vertex -- but it
is what makes the representation *locally checkable*: consistency of `nxt` and `prv` involves only
two adjacent letters, and it already forces every vertex to have at most one incoming edge, hence
forces the graph to be a union of a path and of vertex-disjoint pieces that the path never enters.
This is the property `Transducers.CG.Chk`, and it is what a machine reading the string can verify
in one sweep; without it, following the edges from the source could run around a cycle forever.
The book does not spell out any such condition, because it never runs a machine on an *arbitrary*
string over the alphabet.

`Transducers.CG.CGPath u m p` says that `p 0, …, p m` is the run of children that `u` describes:
`p 0` is the unique source, each `p (t+1)` is the vertex that the edge out of `p t` leads to, and
`p m` has no outgoing edge.  Because the edges are given by a *function* `nxt`, such a path is
unique (`Transducers.CG.cgOutIs_unique`), so
`Transducers.CG.CGOutIs u v` -- `v` is the concatenation of the string representations of the
children, in order of execution -- determines `v`.
-/
import Lax194892Proofs.Source.PartD.PebEnc
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace CG

/-- The direction of an edge of a child configuration graph: `none` stays inside the column,
`some true` goes one column to the right, `some false` one column to the left. -/
abbrev Dir := Option Bool

/-- The column that the direction `d` leads to from the column `p`; there is no column to the left
of the first one. -/
def dest (p : ℕ) : Dir → Option ℕ
  | none => some p
  | some true => some (p + 1)
  | some false => if p = 0 then none else some (p - 1)

/-- **The alphabet of the string representation of a child configuration graph.**  One letter
describes one gap of the input string of the pebble transducer; see the header of this file. -/
structure CGLetter (A Q : Type) (k : ℕ) where
  /-- The input letter that follows this gap, absent for the last gap. -/
  lett : Option A
  /-- The fixed pebbles that sit in this gap. -/
  peb : Fin k → Bool
  /-- The index of the pebble that moves from child to child. -/
  nid : Fin k
  /-- The states `q` for which `(q, this column)` is the first child. -/
  src : Q → Bool
  /-- The outgoing edge of `(q, this column)`. -/
  nxt : Q → Option (Q × Dir)
  /-- The incoming edge of `(q, this column)`. -/
  prv : Q → Option (Q × Dir)

instance {A Q : Type} {k : ℕ} [Finite A] [Finite Q] : Finite (CGLetter A Q k) := by
  have h : Function.Injective
      (fun c : CGLetter A Q k => (c.lett, c.peb, c.nid, c.src, c.nxt, c.prv)) := by
    intro a b hab
    cases a; cases b; simp_all
  exact Finite.of_injective _ h

/-- **The alphabet of the string representation of a configuration**, in the shape of
`Transducers.PebEnc.PairLetter` but for a single configuration: the state, the input letter that
follows the gap, and the set of pebbles sitting in the gap. -/
abbrev ConfLetter (A Q : Type) (k : ℕ) := Q × Option A × (Fin k → Bool)

/-- A vertex of a child configuration graph: a state and a column. -/
abbrev Vtx (Q : Type) := Q × ℕ

variable {A Q : Type} {k : ℕ}

/-- The vertex that the edge out of `v` leads to, if there is one. -/
def succOf (u : List (CGLetter A Q k)) (v : Vtx Q) : Option (Vtx Q) :=
  (u[v.2]?).bind fun c => (c.nxt v.1).bind fun x => (dest v.2 x.2).map fun p' => (x.1, p')

/-- The vertex `v` is marked as the first child. -/
def IsSrc (u : List (CGLetter A Q k)) (v : Vtx Q) : Prop :=
  ∃ c, u[v.2]? = some c ∧ c.src v.1 = true

/-- **The string representation of the child that the vertex `v` stands for**: one letter per gap,
carrying the state of the child, the input letter, the fixed pebbles, and the pebble `nid`, which
sits in the column of `v`. -/
def confAt (u : List (CGLetter A Q k)) (v : Vtx Q) : List (ConfLetter A Q k) :=
  u.mapIdx fun j c => (v.1, c.lett, fun i => c.peb i || (decide (i = c.nid) && decide (v.2 = j)))

@[simp] lemma confAt_length (u : List (CGLetter A Q k)) (v : Vtx Q) :
    (confAt u v).length = u.length := by
  simp [confAt]

/-- The letter to the left of the gap `i`. -/
def leftLet (u : List (CGLetter A Q k)) (i : ℕ) : Option (CGLetter A Q k) :=
  if i = 0 then none else u[i - 1]?

open Classical in
/-- **The local consistency test on two adjacent letters** `a` (the letter of the column to the
left) and `b`: every edge that `nxt` records between these two columns, or inside the column of
`b`, is recorded by `prv` at its target, and a vertex marked as the first child has no incoming
edge. -/
noncomputable def pairOK (a b : Option (CGLetter A Q k)) : Bool := decide (
  (∀ q q' : Q, ∀ ca cb, a = some ca → b = some cb → ca.nxt q = some (q', some true) →
      cb.prv q' = some (q, some true)) ∧
  (∀ q q' : Q, ∀ ca cb, a = some ca → b = some cb → cb.nxt q = some (q', some false) →
      ca.prv q' = some (q, some false)) ∧
  (∀ q q' : Q, ∀ cb, b = some cb → cb.nxt q = some (q', none) → cb.prv q' = some (q, none)) ∧
  (∀ q : Q, ∀ cb, b = some cb → cb.src q = true → cb.prv q = none))

/-- **The string is locally consistent**: the test `pairOK` succeeds at every gap. -/
def Chk (u : List (CGLetter A Q k)) : Prop := ∀ i ≤ u.length, pairOK (leftLet u i) u[i]? = true

/-- **The run of children described by `u`**: `p 0` is the unique vertex marked as the first child,
each `p (t+1)` is reached from `p t` by the edge that `u` records, and `p m` has no outgoing edge.
The string is required to be locally consistent, and every vertex of the run to be a real column. -/
structure CGPath (u : List (CGLetter A Q k)) (m : ℕ) (p : ℕ → Vtx Q) : Prop where
  /-- The string is locally consistent. -/
  chk : Chk u
  /-- `p 0` is the unique vertex marked as the first child. -/
  srcEq : ∀ v, IsSrc u v ↔ v = p 0
  /-- Every vertex of the run sits in a real column. -/
  inRange : ∀ t ≤ m, (u[(p t).2]?).isSome
  /-- Consecutive children are joined by the recorded edge. -/
  step : ∀ t < m, succOf u (p t) = some (p (t + 1))
  /-- The last child has no outgoing edge. -/
  last : succOf u (p m) = none

/-- **The concatenation of the string representations of the children**, in order of execution. -/
def cgOut (u : List (CGLetter A Q k)) (m : ℕ) (p : ℕ → Vtx Q) : List (ConfLetter A Q k) :=
  ((List.range (m + 1)).map fun t => confAt u (p t)).flatten

/-- `v` is **the string representation of the children** of the configuration whose child
configuration graph `u` represents. -/
def CGOutIs (u : List (CGLetter A Q k)) (v : List (ConfLetter A Q k)) : Prop :=
  ∃ m p, CGPath u m p ∧ v = cgOut u m p

/-! ## A string represents at most one run of children -/

lemma CGPath.p_zero_eq {u : List (CGLetter A Q k)} {m m' : ℕ} {p p' : ℕ → Vtx Q}
    (h : CGPath u m p) (h' : CGPath u m' p') : p 0 = p' 0 :=
  (h'.srcEq (p 0)).1 ((h.srcEq (p 0)).2 rfl)

lemma CGPath.eq_of_le {u : List (CGLetter A Q k)} {m m' : ℕ} {p p' : ℕ → Vtx Q}
    (h : CGPath u m p) (h' : CGPath u m' p') : ∀ t, t ≤ m → t ≤ m' → p t = p' t := by
  intro t
  induction t with
  | zero => intro _ _; exact h.p_zero_eq h'
  | succ t ih =>
      intro ht ht'
      have hpt := ih (by omega) (by omega)
      have := h.step t (by omega)
      rw [hpt, h'.step t (by omega)] at this
      exact (Option.some.injEq _ _ ▸ this).symm

lemma CGPath.length_eq {u : List (CGLetter A Q k)} {m m' : ℕ} {p p' : ℕ → Vtx Q}
    (h : CGPath u m p) (h' : CGPath u m' p') : m = m' := by
  by_contra hne
  rcases Nat.lt_or_ge m m' with hlt | hge
  · have hpm := h.eq_of_le h' m (by omega) (by omega)
    have := h'.step m hlt
    rw [← hpm, h.last] at this
    simp at this
  · have hlt : m' < m := by omega
    have hpm := h.eq_of_le h' m' (by omega) (by omega)
    have := h.step m' hlt
    rw [hpm, h'.last] at this
    simp at this

/-- **A string represents at most one list of children.** -/
theorem cgOutIs_unique {u : List (CGLetter A Q k)} {v v' : List (ConfLetter A Q k)}
    (h : CGOutIs u v) (h' : CGOutIs u v') : v = v' := by
  obtain ⟨m, p, hp, rfl⟩ := h
  obtain ⟨m', p', hp', rfl⟩ := h'
  have hmm : m = m' := hp.length_eq hp'
  subst hmm
  unfold cgOut
  congr 1
  refine List.map_congr_left ?_
  intro t ht
  rw [List.mem_range] at ht
  rw [hp.eq_of_le hp' t (by omega) (by omega)]

/-! ## Following the edges -/

/-- One step along the edges, on the option type. -/
def nxtOpt (u : List (CGLetter A Q k)) : Option (Vtx Q) → Option (Vtx Q)
  | none => none
  | some v => succOf u v

/-- The string representation of the child at a vertex, if the vertex sits in a real column. -/
def emitOf (u : List (CGLetter A Q k)) : Option (Vtx Q) → List (ConfLetter A Q k)
  | none => []
  | some v => if (u[v.2]?).isSome then confAt u v else []

/-- **The output of the walk along the edges**, started at `o` and truncated after `n` steps. -/
def walkOut (u : List (CGLetter A Q k)) (o : Option (Vtx Q)) (n : ℕ) :
    List (ConfLetter A Q k) :=
  ((List.range n).map fun t => emitOf u ((nxtOpt u)^[t] o)).flatten

@[simp] lemma walkOut_zero (u : List (CGLetter A Q k)) (o : Option (Vtx Q)) :
    walkOut u o 0 = [] := by simp [walkOut]

lemma walkOut_succ (u : List (CGLetter A Q k)) (o : Option (Vtx Q)) (n : ℕ) :
    walkOut u o (n + 1) = emitOf u o ++ walkOut u (nxtOpt u o) n := by
  unfold walkOut
  rw [List.range_succ_eq_map]
  simp only [List.map_cons, List.map_map, List.flatten_cons, Function.iterate_zero_apply]
  congr 1

@[simp] lemma walkOut_none (u : List (CGLetter A Q k)) (n : ℕ) : walkOut u none n = [] := by
  induction n with
  | zero => simp
  | succ n ih => rw [walkOut_succ]; simpa [emitOf, nxtOpt] using ih

/-! ## Local consistency forbids two edges into the same vertex -/

lemma succOf_eq_some_iff {u : List (CGLetter A Q k)} {v v' : Vtx Q} :
    succOf u v = some v' ↔
      ∃ c, u[v.2]? = some c ∧ ∃ d, c.nxt v.1 = some (v'.1, d) ∧ dest v.2 d = some v'.2 := by
  simp only [succOf, Option.bind_eq_some_iff, Option.map_eq_some_iff]
  constructor
  · rintro ⟨c, hc, x, hx, p', hp', rfl⟩
    exact ⟨c, hc, x.2, by simpa using hx, hp'⟩
  · rintro ⟨c, hc, d, hd, hp⟩
    exact ⟨c, hc, (v'.1, d), hd, v'.2, hp, rfl⟩

lemma succOf_of_out_of_range {u : List (CGLetter A Q k)} {v : Vtx Q} (h : u[v.2]? = none) :
    succOf u v = none := by
  simp [succOf, h]

lemma succOf_col_lt {u : List (CGLetter A Q k)} {v v' : Vtx Q} (h : succOf u v = some v') :
    v.2 < u.length := by
  obtain ⟨c, hc, -⟩ := succOf_eq_some_iff.1 h
  exact (List.getElem?_eq_some_iff.1 hc).1

lemma dest_le {p c : ℕ} {d : Dir} (h : dest p d = some c) : c ≤ p + 1 := by
  cases d with
  | none => simp only [dest, Option.some.injEq] at h; omega
  | some x =>
      cases x with
      | true => simp only [dest, Option.some.injEq] at h; omega
      | false =>
          simp only [dest] at h
          split at h
          · exact absurd h (by simp)
          · simp only [Option.some.injEq] at h; omega

lemma dest_ne_zero {p c : ℕ} {d : Dir} (h : dest p d = some c) (hd : d = some false) :
    p ≠ 0 ∧ c = p - 1 := by
  subst hd
  simp only [dest] at h
  split at h
  · exact absurd h (by simp)
  · simp only [Option.some.injEq] at h
    exact ⟨by omega, h.symm⟩

lemma succOf_col_le {u : List (CGLetter A Q k)} {v v' : Vtx Q} (h : succOf u v = some v') :
    v'.2 ≤ u.length := by
  have hlt := succOf_col_lt h
  obtain ⟨c, -, d, -, hd⟩ := succOf_eq_some_iff.1 h
  cases d with
  | none => simp only [dest, Option.some.injEq] at hd; omega
  | some b =>
      cases b with
      | true => simp only [dest, Option.some.injEq] at hd; omega
      | false => obtain ⟨-, h2⟩ := dest_ne_zero hd rfl; omega

lemma dest_inj {a b c : ℕ} {d : Dir} (ha : dest a d = some c) (hb : dest b d = some c) : a = b := by
  cases d with
  | none => simp only [dest, Option.some.injEq] at ha hb; omega
  | some x =>
      cases x with
      | true => simp only [dest, Option.some.injEq] at ha hb; omega
      | false =>
          obtain ⟨ha1, ha2⟩ := dest_ne_zero ha rfl
          obtain ⟨hb1, hb2⟩ := dest_ne_zero hb rfl
          omega

lemma pairOK_iff (a b : Option (CGLetter A Q k)) :
    pairOK a b = true ↔
      ((∀ q q' : Q, ∀ ca cb, a = some ca → b = some cb → ca.nxt q = some (q', some true) →
          cb.prv q' = some (q, some true)) ∧
        (∀ q q' : Q, ∀ ca cb, a = some ca → b = some cb → cb.nxt q = some (q', some false) →
          ca.prv q' = some (q, some false)) ∧
        (∀ q q' : Q, ∀ cb, b = some cb → cb.nxt q = some (q', none) → cb.prv q' = some (q, none)) ∧
        (∀ q : Q, ∀ cb, b = some cb → cb.src q = true → cb.prv q = none)) := by
  simp only [pairOK, decide_eq_true_eq]

/-- On a locally consistent string, the incoming edge of a vertex is recorded by `prv`. -/
lemma prv_of_succOf {u : List (CGLetter A Q k)} (hchk : Chk u) {x v : Vtx Q}
    (h : succOf u x = some v) {c : CGLetter A Q k} (hc : u[v.2]? = some c) :
    ∃ d, c.prv v.1 = some (x.1, d) ∧ dest x.2 d = some v.2 := by
  obtain ⟨cx, hcx, d, hnx, hd⟩ := succOf_eq_some_iff.1 h
  have hxlt : x.2 < u.length := (List.getElem?_eq_some_iff.1 hcx).1
  have hvlt : v.2 < u.length := (List.getElem?_eq_some_iff.1 hc).1
  refine ⟨d, ?_, hd⟩
  cases d with
  | none =>
      simp only [dest, Option.some.injEq] at hd
      have hcc : cx = c := by
        have hv : u[v.2]? = some cx := by rw [← hd]; exact hcx
        rw [hv] at hc
        exact Option.some.inj hc
      have hp := ((pairOK_iff (leftLet u x.2) u[x.2]?).1 (hchk x.2 (by omega))).2.2.1
        x.1 v.1 cx hcx hnx
      rw [← hcc]
      exact hp
  | some bdir =>
      cases bdir with
      | true =>
          simp only [dest, Option.some.injEq] at hd
          have hv2 : v.2 = x.2 + 1 := hd.symm
          have hleft : leftLet u v.2 = some cx := by
            simp only [leftLet, hv2]
            rw [if_neg (by omega)]
            simpa using hcx
          exact ((pairOK_iff (leftLet u v.2) u[v.2]?).1 (hchk v.2 (by omega))).1
            x.1 v.1 cx c hleft hc hnx
      | false =>
          obtain ⟨hne, hd2⟩ := dest_ne_zero hd rfl
          have hx2 : x.2 = v.2 + 1 := by omega
          have hleft : leftLet u x.2 = some c := by
            simp only [leftLet, hx2]
            rw [if_neg (by omega)]
            simpa using hc
          exact ((pairOK_iff (leftLet u x.2) u[x.2]?).1 (hchk x.2 (by omega))).2.1
            x.1 v.1 c cx hleft hcx hnx

/-- On a locally consistent string, a vertex has at most one incoming edge. -/
lemma indeg_le_one {u : List (CGLetter A Q k)} (hchk : Chk u) {x y v : Vtx Q}
    (hv : (u[v.2]?).isSome) (hx : succOf u x = some v) (hy : succOf u y = some v) : x = y := by
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.1 hv
  obtain ⟨dx, hpx, hdx⟩ := prv_of_succOf hchk hx hc
  obtain ⟨dy, hpy, hdy⟩ := prv_of_succOf hchk hy hc
  rw [hpx] at hpy
  simp only [Option.some.injEq, Prod.mk.injEq] at hpy
  obtain ⟨h1, h2⟩ := hpy
  subst h2
  exact Prod.ext h1 (dest_inj hdx hdy)

/-- On a locally consistent string, the vertex marked as the first child has no incoming edge. -/
lemma no_pred_of_isSrc {u : List (CGLetter A Q k)} (hchk : Chk u) {v x : Vtx Q}
    (hsrc : IsSrc u v) (h : succOf u x = some v) : False := by
  obtain ⟨c, hc, hs⟩ := hsrc
  obtain ⟨d, hpd, -⟩ := prv_of_succOf hchk h hc
  have hvlt : v.2 < u.length := (List.getElem?_eq_some_iff.1 hc).1
  have := (pairOK_iff (leftLet u v.2) u[v.2]?).1 (hchk v.2 (by omega))
  rw [this.2.2.2 v.1 c hc hs] at hpd
  simp at hpd

/-! ## The walk from the first child terminates -/

section Term

variable [Finite Q] {u : List (CGLetter A Q k)}

omit [Finite Q] in
private lemma iterate_nxtOpt_none (d : ℕ) : (nxtOpt u)^[d] (none : Option (Vtx Q)) = none := by
  induction d with
  | zero => rfl
  | succ d ih => rw [Function.iterate_succ_apply', ih]; rfl

omit [Finite Q] in
private lemma orbit_none_of_none {o : Option (Vtx Q)} {s t : ℕ} (hst : s ≤ t)
    (h : (nxtOpt u)^[s] o = none) : (nxtOpt u)^[t] o = none := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hst
  rw [show s + d = d + s from by omega, Function.iterate_add_apply, h, iterate_nxtOpt_none]

omit [Finite Q] in
private lemma orbit_col_le {v₀ : Vtx Q} (hv₀ : v₀.2 ≤ u.length) :
    ∀ t, ∀ v, (nxtOpt u)^[t] (some v₀) = some v → v.2 ≤ u.length := by
  intro t
  induction t with
  | zero =>
      intro v h
      simp only [Function.iterate_zero_apply, Option.some.injEq] at h
      subst h
      exact hv₀
  | succ t ih =>
      intro v h
      rw [Function.iterate_succ_apply'] at h
      cases hp : (nxtOpt u)^[t] (some v₀) with
      | none => rw [hp] at h; exact absurd h (by simp [nxtOpt])
      | some x =>
          rw [hp] at h
          exact succOf_col_le (by simpa [nxtOpt] using h)

omit [Finite Q] in
private lemma orbit_inj (hchk : Chk u) {v₀ : Vtx Q} (hsrc : IsSrc u v₀) :
    ∀ t s, s < t → (nxtOpt u)^[t] (some v₀) ≠ none →
      (nxtOpt u)^[s] (some v₀) ≠ (nxtOpt u)^[t] (some v₀) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
      intro s hst hne heq
      -- the value is `some x`
      cases hx : (nxtOpt u)^[t] (some v₀) with
      | none => exact hne hx
      | some x =>
          rw [hx] at heq
          -- `x` is in range: otherwise the walk stops right after step `s`
          have hxrange : (u[x.2]?).isSome := by
            by_contra hcon
            have h0 : (nxtOpt u)^[s + 1] (some v₀) = none := by
              rw [Function.iterate_succ_apply', heq]
              simpa [nxtOpt] using
                succOf_of_out_of_range (Option.not_isSome_iff_eq_none.1 hcon)
            exact hne (orbit_none_of_none (by omega) h0)
          match s, hst with
          | 0, _ =>
              -- `x = v₀` has an incoming edge, contradicting that it is the first child
              have hx0 : x = v₀ := by
                simpa using heq.symm
              obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
              cases hy : (nxtOpt u)^[t'] (some v₀) with
              | none =>
                  rw [Function.iterate_succ_apply', hy] at hx
                  exact absurd hx (by simp [nxtOpt])
              | some y =>
                  rw [Function.iterate_succ_apply', hy] at hx
                  refine no_pred_of_isSrc hchk hsrc (x := y) ?_
                  rw [← hx0]
                  simpa [nxtOpt] using hx
          | s' + 1, _ =>
              obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
              cases hy : (nxtOpt u)^[t'] (some v₀) with
              | none =>
                  rw [Function.iterate_succ_apply', hy] at hx
                  exact absurd hx (by simp [nxtOpt])
              | some y =>
                  cases hz : (nxtOpt u)^[s'] (some v₀) with
                  | none =>
                      rw [Function.iterate_succ_apply', hz] at heq
                      exact absurd heq (by simp [nxtOpt])
                  | some z =>
                      rw [Function.iterate_succ_apply', hy] at hx
                      rw [Function.iterate_succ_apply', hz] at heq
                      have hzy : z = y :=
                        indeg_le_one hchk hxrange (by simpa [nxtOpt] using heq)
                          (by simpa [nxtOpt] using hx)
                      refine ih t' (by omega) s' (by omega) (by rw [hy]; simp) ?_
                      rw [hz, hy, hzy]

/-- **The walk along the edges, started at the first child, terminates**, provided the string is
locally consistent.  This is what makes it possible for a machine to follow the edges without
looping forever. -/
theorem exists_walk_stop (hchk : Chk u) {v₀ : Vtx Q} (hsrc : IsSrc u v₀) :
    ∃ n, (nxtOpt u)^[n] (some v₀) = none := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨c₀, hc₀, -⟩ := id hsrc
  have hv₀ : v₀.2 ≤ u.length := le_of_lt (List.getElem?_eq_some_iff.1 hc₀).1
  have hcol : ∀ t, ∀ v, (nxtOpt u)^[t] (some v₀) = some v → v.2 ≤ u.length :=
    orbit_col_le hv₀
  have hsome : ∀ t, ∃ v, (nxtOpt u)^[t] (some v₀) = some v := by
    intro t
    cases h : (nxtOpt u)^[t] (some v₀) with
    | none => exact absurd h (hcon t)
    | some v => exact ⟨v, rfl⟩
  choose g hg using hsome
  have hginj : Function.Injective
      (fun t => ((g t).1, (⟨(g t).2, by
        have := hcol t (g t) (hg t); omega⟩ : Fin (u.length + 1))) :
        ℕ → Q × Fin (u.length + 1)) := by
    intro s t hst
    simp only [Prod.mk.injEq, Fin.mk.injEq] at hst
    have hgg : g s = g t := Prod.ext hst.1 hst.2
    by_contra hne
    rcases Nat.lt_or_ge s t with hlt | hge
    · exact orbit_inj hchk hsrc t s hlt (by rw [hg t]; simp) (by rw [hg s, hg t, hgg])
    · have hlt : t < s := by omega
      exact orbit_inj hchk hsrc s t hlt (by rw [hg s]; simp) (by rw [hg s, hg t, hgg])
  have hfin : Finite ℕ := Finite.of_injective _ hginj
  exact (not_finite_iff_infinite.2 inferInstance) hfin

end Term

/-! ## The walk reproduces the run of children -/

lemma walkOut_succ_right (u : List (CGLetter A Q k)) (o : Option (Vtx Q)) (n : ℕ) :
    walkOut u o (n + 1) = walkOut u o n ++ emitOf u ((nxtOpt u)^[n] o) := by
  unfold walkOut
  rw [List.range_succ]
  simp

lemma walkOut_eq_of_stop {u : List (CGLetter A Q k)} {o : Option (Vtx Q)} {m : ℕ}
    (hstop : ∀ t, m < t → (nxtOpt u)^[t] o = none) : ∀ n, m < n → walkOut u o n = walkOut u o (m + 1) := by
  intro n hn
  obtain ⟨d, rfl⟩ : ∃ d, n = m + 1 + d := ⟨n - (m + 1), by omega⟩
  induction d with
  | zero => rfl
  | succ d ih =>
      rw [show m + 1 + (d + 1) = (m + 1 + d) + 1 from by omega, walkOut_succ_right,
        ih (by omega), hstop (m + 1 + d) (by omega)]
      simp [emitOf]

lemma CGPath.orbit_eq {u : List (CGLetter A Q k)} {m : ℕ} {p : ℕ → Vtx Q} (h : CGPath u m p) :
    ∀ t ≤ m, (nxtOpt u)^[t] (some (p 0)) = some (p t) := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
      intro ht
      rw [Function.iterate_succ_apply', ih (by omega)]
      exact h.step t (by omega)

lemma CGPath.orbit_none {u : List (CGLetter A Q k)} {m : ℕ} {p : ℕ → Vtx Q} (h : CGPath u m p) :
    ∀ t, m < t → (nxtOpt u)^[t] (some (p 0)) = none := by
  intro t ht
  have hm1 : (nxtOpt u)^[m + 1] (some (p 0)) = none := by
    rw [Function.iterate_succ_apply', h.orbit_eq m le_rfl]
    exact h.last
  obtain ⟨d, rfl⟩ : ∃ d, t = (m + 1) + d := ⟨t - (m + 1), by omega⟩
  rw [show m + 1 + d = d + (m + 1) from by omega, Function.iterate_add_apply, hm1]
  clear ht
  induction d with
  | zero => rfl
  | succ d ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- **The walk along the edges produces exactly the string representations of the children.** -/
lemma CGPath.walkOut_eq {u : List (CGLetter A Q k)} {m : ℕ} {p : ℕ → Vtx Q} (h : CGPath u m p)
    {n : ℕ} (hn : (nxtOpt u)^[n] (some (p 0)) = none) :
    walkOut u (some (p 0)) n = cgOut u m p := by
  have hmn : m < n := by
    by_contra hcon
    rw [h.orbit_eq n (by omega)] at hn
    simp at hn
  rw [walkOut_eq_of_stop h.orbit_none n hmn]
  unfold walkOut cgOut
  congr 1
  refine List.map_congr_left ?_
  intro t ht
  rw [List.mem_range] at ht
  rw [h.orbit_eq t (by omega)]
  simp only [emitOf, if_pos (h.inRange t (by omega))]

end CG

end Lax194892Proofs.Transducers
