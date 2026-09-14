/-
**Walking along a snake graph with a two-way transducer.**

This is what makes Lemma `lem:output-of-snake-graph-is-regular` follow from the version of the snake
lemma that is already proved in `RequestProject/PartC/SnakeReg.lean`
(`Transducers.boundedWidth_isRegular`, the regularity of the width-bounded output function of a
two-way transducer).

`SnakeGraph.snakeTrans Q B` is a two-way transducer over the alphabet `Transducers.SnakeLetter Q B`
whose states are `Option Q`.  In the state `none` it *looks for the source* of the snake: it moves
right until it stands at a column that contains a vertex with an outgoing but no incoming edge, and
halts at the right end of the input if it never finds one.  From the source on it *walks along the
snake*: in the state `some q` it takes the outgoing edge of the vertex `(q, x)` at the current
column `x`, prints its label, and moves to the column of the target; when the current vertex has no
outgoing edge, it halts.

On a string that represents a snake graph the source is unique, so the run of the transducer is
exactly: a sweep from the leftmost column to the source, and then the path that carries all the
edges of the graph.  Its output is therefore the output of the snake graph
(`SnakeGraph.computes_snakeTrans`), and since the run halts, its width is at most the number of
states, so the *width-bounded* output function of the transducer already computes the output of the
snake graph (`SnakeGraph.snakeOutIs_widthOut`).
-/
import Lax916827Proofs.Source.PartC.SnakeAlphLoc
import Lax916827Proofs.Source.PartC.SnakeAlphChar
import Lax916827Proofs.Source.PartC.TwoWayCompAux
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace SnakeGraph

variable {Q B : Type}

/-! ## The transducer -/

/-- The outgoing edge of the vertex `(q, x)` -- the target state, the label and the direction of the
step -- read off the letters `l` and `r` around the column `x`.  The edge that crosses to the right
is looked at first; on a string that represents a snake graph a vertex has at most one outgoing edge,
so the order does not matter. -/
def stepEdge (l r : Option (SnakeLetter Q B)) (q : Q) : Option ((Q × Option B) × Bool) :=
  match outR r q with
  | some z => some (z, true)
  | none =>
    match outL l q with
    | some z => some (z, false)
    | none => none

open Classical in
/-- A source of the column with the letters `l` and `r` around it, if it has one. -/
noncomputable def srcAt (l r : Option (SnakeLetter Q B)) : Option Q :=
  if h : ∃ q, IsSrcAt l r q then some h.choose else none

open Classical in
/-- The transition function of the transducer that walks along a snake graph. -/
noncomputable def snakeStep (l : Option (SnakeLetter Q B)) (s : Option Q)
    (r : Option (SnakeLetter Q B)) : List B ⊕ (Option Q × List B × Bool) :=
  match s.orElse (fun _ => srcAt l r) with
  | some q =>
      match stepEdge l r q with
      | some ((q', o), d) => Sum.inr (some q', o.toList, d)
      | none => Sum.inl []
  | none =>
      match r with
      | none => Sum.inl []
      | some _ => Sum.inr (none, [], true)

/-- **The two-way transducer that walks along a snake graph** and prints the labels of the edges it
follows.  It starts in the state `none`, in which it looks for the source of the snake. -/
noncomputable def snakeTrans (Q B : Type) : TwoWay (SnakeLetter Q B) B (Option Q) where
  init := none
  step := snakeStep

@[simp] lemma snakeTrans_init : (snakeTrans Q B).init = none := rfl

@[simp] lemma snakeTrans_step (l : Option (SnakeLetter Q B)) (s : Option Q)
    (r : Option (SnakeLetter Q B)) : (snakeTrans Q B).step l s r = snakeStep l s r := rfl

/-! ## The configurations of the transducer -/

variable {w : List (SnakeLetter Q B)}

/-- The configuration of the transducer at the column `x`, in the state `s`. -/
def cfgAt (w : List (SnakeLetter Q B)) (s : Option Q) (x : ℕ) :
    Cfg (SnakeLetter Q B) (Option Q) :=
  Cfg.conf (w.take x) s (w.drop x)

lemma step_eq_snakeStep {x : ℕ} (hx : x ≤ w.length) (s : Option Q) :
    (snakeTrans Q B).step (w.take x).getLast? s (w.drop x).head?
      = snakeStep (prevLet w x) s w[x]? := by
  have h1 : (w.take x).getLast? = prevLet w x := TwoWay.take_getLast?' w hx
  have h2 : (w.drop x).head? = w[x]? := by
    rw [List.head?_eq_getElem?, List.getElem?_drop, Nat.add_zero]
  rw [snakeTrans_step, h1, h2]

lemma stepCfg_snake_halt {x : ℕ} {s : Option Q} {o : List B} (hx : x ≤ w.length)
    (h : snakeStep (prevLet w x) s w[x]? = Sum.inl o) :
    (snakeTrans Q B).stepCfg (cfgAt w s x) = some (o, Cfg.halt) := by
  refine TwoWay.stepCfg_halt_eq (snakeTrans Q B) ?_
  rw [step_eq_snakeStep hx]
  exact h

lemma stepCfg_snake_right {x : ℕ} {s s' : Option Q} {o : List B} (hx : x < w.length)
    (h : snakeStep (prevLet w x) s w[x]? = Sum.inr (s', o, true)) :
    (snakeTrans Q B).stepCfg (cfgAt w s x) = some (o, cfgAt w s' (x + 1)) := by
  have hd : w.drop x = w[x] :: w.drop (x + 1) := List.drop_eq_getElem_cons hx
  have hstep : (snakeTrans Q B).step (w.take x).getLast? s (w.drop x).head?
      = Sum.inr (s', o, true) := by
    rw [step_eq_snakeStep (le_of_lt hx)]
    exact h
  rw [cfgAt, hd]
  rw [TwoWay.stepCfg_right_cons (snakeTrans Q B) (by rw [← hd]; exact hstep)]
  rw [cfgAt, List.take_succ_eq_append_getElem hx]

lemma stepCfg_snake_left {x : ℕ} {s s' : Option Q} {o : List B} (hx : 0 < x)
    (hxle : x ≤ w.length) (h : snakeStep (prevLet w x) s w[x]? = Sum.inr (s', o, false)) :
    (snakeTrans Q B).stepCfg (cfgAt w s x) = some (o, cfgAt w s' (x - 1)) := by
  obtain ⟨y, rfl⟩ : ∃ y, x = y + 1 := ⟨x - 1, by omega⟩
  have hy : y < w.length := by omega
  have hsplit : w.take (y + 1) = w.take y ++ [w[y]] := List.take_succ_eq_append_getElem hy
  have hlast : (w.take (y + 1)).getLast? = some w[y] := by
    rw [hsplit, List.getLast?_concat]
  have hdl : (w.take (y + 1)).dropLast = w.take y := by
    rw [hsplit, List.dropLast_concat]
  have hdrop : w[y] :: w.drop (y + 1) = w.drop y := (List.drop_eq_getElem_cons hy).symm
  have hstep : (snakeTrans Q B).step (w.take (y + 1)).getLast? s (w.drop (y + 1)).head?
      = Sum.inr (s', o, false) := by
    rw [step_eq_snakeStep hxle]
    exact h
  rw [cfgAt, TwoWay.stepCfg_left_some (snakeTrans Q B) hlast hstep, hdl, hdrop]
  simp [cfgAt]

/-! ## Looking for the source -/

/-- Sweeping right through columns that contain no source. -/
lemma reaches_seek : ∀ (d x : ℕ), x + d ≤ w.length →
    (∀ z, x ≤ z → z < x + d → srcAt (prevLet w z) w[z]? = none) →
    (snakeTrans Q B).Reaches (cfgAt w none x) [] (cfgAt w none (x + d)) := by
  intro d
  induction d with
  | zero => intro x _ _; simpa using TwoWay.Reaches.refl (cfgAt w none x)
  | succ d ih =>
      intro x hle hno
      have hx : x < w.length := by omega
      have hcx : w[x]? = some w[x] := List.getElem?_eq_getElem hx
      have hno' : srcAt (prevLet w x) (some w[x]) = none := by
        rw [← hcx]; exact hno x (le_refl _) (by omega)
      have hstep : snakeStep (prevLet w x) none w[x]? = Sum.inr (none, [], true) := by
        simp [snakeStep, hcx, hno']
      have h1 := stepCfg_snake_right hx hstep
      have h2 := ih (x + 1) (by omega) (fun z hz hz' => hno z (by omega) (by omega))
      have h3 := (TwoWay.reaches_one h1).trans h2
      simpa [show x + 1 + d = x + (d + 1) by omega] using h3

/-! ## Walking along the snake -/

/-- The output of the last `d` edges of a path, starting at the step `t`. -/
def pathOutFrom (lab : ℕ → Option B) (t : ℕ) : ℕ → List B
  | 0 => []
  | d + 1 => (lab t).toList ++ pathOutFrom lab (t + 1) d

lemma pathOutFrom_eq (lab : ℕ → Option B) : ∀ (d t : ℕ),
    pathOutFrom lab t d = ((List.range' t d).map (fun i => (lab i).toList)).flatten := by
  intro d
  induction d with
  | zero => intro t; rfl
  | succ d ih => intro t; rw [pathOutFrom, ih]; rfl

lemma pathOutFrom_zero (lab : ℕ → Option B) (m : ℕ) : pathOutFrom lab 0 m = pathOut lab m := by
  rw [pathOutFrom_eq, pathOut, List.range_eq_range']

variable {m : ℕ} {p : ℕ → Vtx Q} {lab : ℕ → Option B}

/-- From the source on, the transducer follows the edges of the path and prints their labels. -/
lemma reaches_walk (hp : IsSnakePath w m p lab) : ∀ (d t : ℕ), t + d = m → (p t).2 ≤ w.length →
    ∀ s : Option Q, s.orElse (fun _ => srcAt (prevLet w (p t).2) w[(p t).2]?) = some (p t).1 →
      (snakeTrans Q B).Reaches (cfgAt w s (p t).2) (pathOutFrom lab t d) Cfg.halt := by
  intro d
  induction d with
  | zero =>
      intro t htm hcol s hs
      rw [Nat.add_zero] at htm
      subst htm
      have hno : ¬ HasOutAt (prevLet w (p t).2) w[(p t).2]? (p t).1 := by
        intro hh
        exact hp.no_hasOut_last (hasOut_iff.2 hh)
      have h1 : outR w[(p t).2]? (p t).1 = none := by
        rcases h : outR w[(p t).2]? (p t).1 with _ | z
        · rfl
        · exact absurd (Or.inl (by rw [h]; rfl)) hno
      have h2 : outL (prevLet w (p t).2) (p t).1 = none := by
        rcases h : outL (prevLet w (p t).2) (p t).1 with _ | z
        · rfl
        · exact absurd (Or.inr (by rw [h]; rfl)) hno
      have hse : stepEdge (prevLet w (p t).2) w[(p t).2]? (p t).1 = none := by
        simp [stepEdge, h1, h2]
      have hss : snakeStep (prevLet w (p t).2) s w[(p t).2]? = Sum.inl [] := by
        simp only [snakeStep, hs, hse]
      exact TwoWay.reaches_one (stepCfg_snake_halt hcol hss)
  | succ d ih =>
      intro t htm hcol s hs
      have htlt : t < m := by omega
      have hedge := hp.edge t htlt
      have hcol' : (p (t + 1)).2 ≤ w.length := col_le_of_hasIn (hp.hasIn_succ htlt)
      have hs' : (some (p (t + 1)).1).orElse
          (fun _ => srcAt (prevLet w (p (t + 1)).2) w[(p (t + 1)).2]?)
          = some (p (t + 1)).1 := rfl
      have hrest := ih (t + 1) (by omega) hcol' (some (p (t + 1)).1) hs'
      rcases hR : outR w[(p t).2]? (p t).1 with _ | z
      · -- the edge of the path goes to the left
        rcases edge_out_cases hedge with ⟨-, hcon⟩ | ⟨hxy, hL⟩
        · rw [hR] at hcon; exact absurd hcon (by simp)
        · have hse : stepEdge (prevLet w (p t).2) w[(p t).2]? (p t).1
              = some (((p (t + 1)).1, lab t), false) := by
            simp [stepEdge, hR, hL]
          have hss : snakeStep (prevLet w (p t).2) s w[(p t).2]?
              = Sum.inr (some (p (t + 1)).1, (lab t).toList, false) := by
            simp only [snakeStep, hs, hse]
          have hstep := stepCfg_snake_left (by omega) hcol hss
          have hidx : (p t).2 - 1 = (p (t + 1)).2 := by omega
          rw [hidx] at hstep
          have := (TwoWay.reaches_one hstep).trans hrest
          rw [pathOutFrom]
          exact this
      · -- the edge of the path goes to the right
        have hz : Edge w (p t) (z.1, (p t).2 + 1) z.2 := edge_of_outR (by rw [hR])
        obtain ⟨heq, hlab⟩ := hp.outUnique hz hedge
        have hse : stepEdge (prevLet w (p t).2) w[(p t).2]? (p t).1 = some (z, true) := by
          simp [stepEdge, hR]
        have hss : snakeStep (prevLet w (p t).2) s w[(p t).2]?
            = Sum.inr (some z.1, z.2.toList, true) := by
          simp only [snakeStep, hs, hse]
        have hxlt : (p t).2 < w.length := by
          have : w[(p t).2]? ≠ none := by
            intro hcon
            rw [outR, hcon] at hR
            exact absurd hR (by simp)
          rcases Nat.lt_or_ge (p t).2 w.length with h | h
          · exact h
          · exact absurd (List.getElem?_eq_none h) this
        have hstep := stepCfg_snake_right hxlt hss
        have h1 : z.1 = (p (t + 1)).1 := congrArg Prod.fst heq
        have h2 : (p t).2 + 1 = (p (t + 1)).2 := congrArg Prod.snd heq
        rw [h1, h2] at hstep
        rw [hlab] at hstep
        have := (TwoWay.reaches_one hstep).trans hrest
        rw [pathOutFrom]
        exact this

/-! ## The run of the transducer on a string that represents a snake graph -/

/-- **The transducer computes the output of the snake graph.** -/
theorem computes_snakeTrans {w : List (SnakeLetter Q B)} {v : List B} (h : SnakeOutIs w v) :
    (snakeTrans Q B).Computes w v := by
  classical
  obtain ⟨m, p, lab, hp, rfl⟩ := h
  have hcfg0 : cfgAt w none 0 = Cfg.conf [] (snakeTrans Q B).init w := by
    simp [cfgAt]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- the graph has no edge: the transducer sweeps to the right end and halts
    have hnoedge : ∀ u u' o, ¬ Edge w u u' o := by
      intro u u' o hu
      obtain ⟨t, ht, -⟩ := hp.covers _ _ _ hu
      omega
    have hnosrc : ∀ z, srcAt (prevLet w z) w[z]? = none := by
      intro z
      rw [srcAt, dif_neg]
      rintro ⟨q, hq⟩
      obtain ⟨⟨v', o, hv⟩, -⟩ := src_iff.2 hq
      exact hnoedge _ _ _ hv
    have hseek := reaches_seek (w := w) w.length 0 (by omega)
      (fun z _ _ => hnosrc z)
    rw [Nat.zero_add] at hseek
    have hhalt : (snakeTrans Q B).stepCfg (cfgAt w none w.length) = some ([], Cfg.halt) := by
      refine stepCfg_snake_halt (le_refl _) ?_
      have hgn : w[w.length]? = (none : Option (SnakeLetter Q B)) :=
        List.getElem?_eq_none (le_refl _)
      have hns : srcAt (prevLet w w.length) (none : Option (SnakeLetter Q B)) = none := by
        rw [← hgn]; exact hnosrc w.length
      simp [snakeStep, hns]
    have hrun := hseek.trans (TwoWay.reaches_one hhalt)
    show (snakeTrans Q B).Reaches (Cfg.conf [] (snakeTrans Q B).init w) (pathOut lab 0) Cfg.halt
    rw [← hcfg0, show pathOut lab 0 = ([] : List B) from rfl]
    simpa using hrun
  · -- the source of the snake is the first vertex of the path
    have hsrc : Src w (p 0) := ⟨hp.hasOut_of_lt hm, hp.no_hasIn_zero⟩
    have hx0 : (p 0).2 ≤ w.length := col_le_of_hasOut hsrc.1
    have hnosrc : ∀ z, z < (p 0).2 → srcAt (prevLet w z) w[z]? = none := by
      intro z hz
      rw [srcAt, dif_neg]
      rintro ⟨q, hq⟩
      have hzz : ((q, z) : Vtx Q) = p 0 := hp.src_eq (src_iff.2 hq)
      have : z = (p 0).2 := congrArg Prod.snd hzz
      omega
    have hseek := reaches_seek (w := w) (p 0).2 0 (by omega)
      (fun z _ hz => hnosrc z (by omega))
    rw [Nat.zero_add] at hseek
    have hex : ∃ q, IsSrcAt (prevLet w (p 0).2) w[(p 0).2]? q := ⟨(p 0).1, src_iff.1 hsrc⟩
    have hsrcat : srcAt (prevLet w (p 0).2) w[(p 0).2]? = some (p 0).1 := by
      rw [srcAt, dif_pos hex]
      have hzz : ((hex.choose, (p 0).2) : Vtx Q) = p 0 := hp.src_eq (src_iff.2 hex.choose_spec)
      exact congrArg some (congrArg Prod.fst hzz)
    have hwalk := reaches_walk hp m 0 (by omega) hx0 none (by simpa using hsrcat)
    have hrun := hseek.trans hwalk
    show (snakeTrans Q B).Reaches (Cfg.conf [] (snakeTrans Q B).init w) (pathOut lab m) Cfg.halt
    rw [← hcfg0, ← pathOutFrom_zero]
    simpa using hrun

/-- **The width-bounded output function of the transducer computes the output of the snake graph.**
The run halts, so its width is at most the number `|Q| + 1` of states of `snakeTrans Q B`, and the
width-bounded output function agrees with the output of the run. -/
theorem snakeOutIs_widthOut [Finite Q] [Finite B] {w : List (SnakeLetter Q B)}
    (h : RepresentsSnake w) :
    SnakeOutIs w (TwoWay.widthOut (snakeTrans Q B) (Nat.card (Option Q)) w) := by
  obtain ⟨m, p, lab, hp⟩ := h
  have hv : SnakeOutIs w (pathOut lab m) := ⟨m, p, lab, hp, rfl⟩
  have hcomp := computes_snakeTrans hv
  obtain ⟨T, hT, -⟩ := TwoWay.exists_halt_time (snakeTrans Q B) w hcomp
  rw [TwoWay.widthOut, if_pos (TwoWay.widthLe_card (snakeTrans Q B) w hT),
    TwoWay.runOut_eq (snakeTrans Q B) w hcomp]
  exact hv

end SnakeGraph

end Lax916827Proofs.Transducers
