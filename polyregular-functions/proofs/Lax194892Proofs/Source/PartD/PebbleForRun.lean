/-
Part D: the run of the pebble transducer that simulates a for-transducer in prenex form.

The machine is defined in `RequestProject/PartD/PebbleForDef.lean`.  Its run is described by
three statements, one for each level of the description of a nest of loops:

* `PebFor.Setup.IterStmt j`: one iteration of the loop `j`, that is, the whole of the nest below
  it for one position of its variable, followed by the move to the next position (or by the end
  of the loop);
* `PebFor.Setup.LoopStmt j`: all the remaining iterations of the loop `j`;
* `PebFor.Setup.ClaimStmt j`: the loops `j, j+1, …` of the nest, from the moment the machine is
  about to push the pebble of the loop `j`.

`ClaimStmt j` follows from `LoopStmt j`, which follows from `IterStmt j`, which follows from
`ClaimStmt (j+1)` -- or, when the loop `j` is the innermost one, from the run of the body.  A
downward induction on `j` then gives `ClaimStmt 0`, and the theorem follows.

Because the machine has no instruction that does nothing, a phase change is always fused with the
action that accompanies it: the machine is "about to start the loop `j`" (`Setup.AtEnter`) not
only in the phase `Ph.enter j` but also, for instance, in the phase `Ph.init (j-1)` of a forward
loop, where the pebble that has just been pushed is already at the first position of its loop.
The three statements above are therefore stated for any state from which the machine performs the
step that starts the loop.
-/
import Lax194892Proofs.Source.PartD.PebbleForDef
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace PebFor

open PolyEnum

variable {A B : Type}

/-! ## Transitivity of the reachability relation of a pebble transducer -/

namespace Pebble

variable {Q : Type} {k : ℕ} {M : Pebble A B Q k} {w : List A}

lemma reaches_trans {c c' c'' : PebbleCfg Q} {v v' : List B}
    (h : M.Reaches w c v c') (h' : M.Reaches w c' v' c'') : M.Reaches w c (v ++ v') c'' := by
  induction h with
  | refl c => simpa using h'
  | step hs _ ih => exact (List.append_assoc _ _ _ ▸ Pebble.Reaches.step hs (ih h'))

lemma reaches_one {c c' : PebbleCfg Q} {v : List B} (h : M.stepCfg w c = some (v, c')) :
    M.Reaches w c v c' := by
  simpa using Pebble.Reaches.step h (Pebble.Reaches.refl c')

end Pebble

/-! ## The positions that a loop still has to visit -/

/-- The next position of a loop of direction `d` over a string of length `n`, after `p`. -/
def nextPos (d : Bool) (n p : ℕ) : Option ℕ :=
  if d then (if p + 1 < n then some (p + 1) else none)
  else (if p = 0 then none else some (p - 1))

/-- The positions that a loop of direction `d` over a string of length `n` still has to visit,
starting from `p`. -/
def remPos (d : Bool) (n p : ℕ) : List ℕ :=
  if d then List.range' p (n - p) else (List.range (p + 1)).reverse

lemma remPos_eq_loopRange_true {n : ℕ} : remPos true n 0 = loopRange true n := by
  simp [remPos, List.range_eq_range']

lemma remPos_eq_loopRange_false {n : ℕ} (hn : 0 < n) :
    remPos false n (n - 1) = loopRange false n := by
  have : n - 1 + 1 = n := by omega
  simp [remPos, this]

lemma remPos_cons (d : Bool) {n p : ℕ} (hp : p < n) :
    remPos d n p = p :: (nextPos d n p).elim [] (remPos d n) := by
  cases d
  · unfold remPos nextPos
    by_cases hp0 : p = 0
    · subst hp0; simp
    · simp only [if_false, if_neg hp0, Bool.false_eq_true]
      have h1 : p + 1 = (p - 1 + 1) + 1 := by omega
      rw [h1, List.range_succ, List.reverse_append]
      simp [Option.elim]
      omega
  · unfold remPos nextPos
    by_cases h1 : p + 1 < n
    · simp only [if_true, if_pos h1, Option.elim]
      have h2 : n - p = (n - (p + 1)) + 1 := by omega
      rw [h2, List.range'_succ]
    · simp only [if_true, if_neg h1, Option.elim]
      have h2 : n - p = 1 := by omega
      rw [h2]
      simp

lemma mem_remPos {d : Bool} {n p q : ℕ} (h : q ∈ remPos d n p) (hp : p < n) : q < n := by
  cases d
  · simp only [remPos, if_false, Bool.false_eq_true, List.mem_reverse, List.mem_range] at h
    omega
  · simp only [remPos, if_true, List.mem_range'] at h
    omega

lemma getLast?_cons_concat (a p : ℕ) (pre : List ℕ) :
    (a :: (pre ++ [p])).getLast? = some p := by
  rw [← List.cons_append, List.getLast?_append]
  simp

lemma dropLast_cons_concat (a p : ℕ) (pre : List ℕ) :
    (a :: (pre ++ [p])).dropLast = a :: pre := by
  rw [← List.cons_append, List.dropLast_concat]

/-! ## The data of the simulation -/

/-- All the data of the simulation of a for-transducer in prenex form by a pebble transducer. -/
structure Setup (A B : Type) where
  /-- The number of loops of the nest. -/
  k : ℕ
  /-- The number of Boolean variables that the machine keeps. -/
  m : ℕ
  /-- A bound on the length of the output of the epilogue. -/
  N : ℕ
  /-- The input string. -/
  w : List A
  /-- The nest of loops. -/
  L : List (Bool × ℕ)
  /-- The nest has `k` loops. -/
  hk : L.length = k
  /-- The body of the nest. -/
  body : ForProg A B
  /-- The epilogue. -/
  epilogue : ForProg A B
  /-- The loop variable that a position variable of the body refers to. -/
  vf : ℕ → Fin (k + 1)
  /-- The body is loop-free. -/
  hbody : body.LoopFree
  /-- The epilogue is loop-free. -/
  hepi : epilogue.LoopFree
  /-- The body outputs at most one letter per iteration. -/
  hone : body.OutputsAtMostOne
  /-- The Boolean variables of the body are among the first `m` ones. -/
  hm : ∀ i ∈ body.boolVars, i < m
  /-- `vf` is the map of `Transducers.virt`. -/
  hvf : ∀ i, ((vf i : ℕ)) = virt L i
  /-- The epilogue produces at most `N` letters. -/
  hN : outBound epilogue ≤ N

namespace Setup

variable (S : Setup A B)

/-- The length of the input string. -/
def n : ℕ := S.w.length

/-- The simulating machine. -/
noncomputable def M : Pebble A B (PSt A B S.k S.m S.N) (S.k + 1) :=
  peb S.k S.m S.N S.L S.body S.epilogue S.vf

/-- The configuration of the machine whose loop pebbles are at the positions `ps`. -/
def cfgAt (q : PSt A B S.k S.m S.N) (ps : List ℕ) : PebbleCfg (PSt A B S.k S.m S.N) :=
  PebbleCfg.conf q (0 :: ps)

/-- The order of the positions of the variables. -/
def ordTrue (ps : List ℕ) : Fin (S.k + 1) → Fin (S.k + 1) → Bool :=
  fun i j => decide (posOf ps (i : ℕ) ≤ posOf ps (j : ℕ))

/-- The order matrix of a state is correct for the positions `ps`. -/
def Good (o : Fin (S.k + 1) → Fin (S.k + 1) → Bool) (pd : Option (Fin (S.k + 1) × Bool))
    (ps : List ℕ) : Prop :=
  fixOrd S.k o pd (viewOf S.w (0 :: ps)) = S.ordTrue ps

/-- The variable index `j`, capped at `k`. -/
def fin' (j : ℕ) : Fin (S.k + 1) := ⟨min j S.k, by omega⟩

/-- One iteration of the body, at the tuple `pre ++ t`. -/
noncomputable def nestStep (pre : List ℕ) (bv : ℕ → Bool) (t : List ℕ) : (ℕ → Bool) × List B :=
  ForProg.exec S.w S.body (setTuple S.L (pre ++ t) (fun _ => 0)) bv

/-- The run of the loops `j, j+1, …` of the nest, when the loops before `j` are at the positions
`pre`. -/
noncomputable def nestRun (pre : List ℕ) (j : ℕ) (bv : ℕ → Bool) : (ℕ → Bool) × List B :=
  runList (S.nestStep pre) (tuplesOf (S.L.drop j) S.n) bv

/-- The machine is about to start the loop `j` (or to run the body, if `j = k`), with the
Boolean variables set to `s`.

Because the machine has no instruction that does nothing, the phase change is fused with the
action that accompanies it, and the Boolean valuation `s` that the machine is going to use is not
necessarily the one stored in `q`: it is the one that the step itself computes.  The predicate is
therefore stated for the step of the machine, and takes `s` as a parameter. -/
def AtEnter (q : PSt A B S.k S.m S.N) (s : Fin S.m → Bool) (j : ℕ) (ps : List ℕ) : Prop :=
  stepFn S.k S.m S.N S.L S.body S.epilogue S.vf q (viewOf S.w (0 :: ps))
    = enterAct S.k S.m S.N S.L S.body S.epilogue S.vf (S.fin' j) s
        (fixOrd S.k q.ord q.pend (viewOf S.w (0 :: ps))) (viewOf S.w (0 :: ps))

/-- The machine is about to advance the loop `j`, with the Boolean variables set to `s`. -/
def AtAdv (q : PSt A B S.k S.m S.N) (s : Fin S.m → Bool) (j : ℕ) (ps : List ℕ) : Prop :=
  stepFn S.k S.m S.N S.L S.body S.epilogue S.vf q (viewOf S.w (0 :: ps))
    = advAct S.k S.m S.N S.L (S.fin' j) s
        (fixOrd S.k q.ord q.pend (viewOf S.w (0 :: ps))) (viewOf S.w (0 :: ps))

/-- The machine is about to run the epilogue, with the Boolean variables set to `s`. -/
def AtEpi (q : PSt A B S.k S.m S.N) (s : Fin S.m → Bool) (ps : List ℕ) : Prop :=
  stepFn S.k S.m S.N S.L S.body S.epilogue S.vf q (viewOf S.w (0 :: ps))
    = epiAct S.k S.m S.N S.epilogue s
        (fixOrd S.k q.ord q.pend (viewOf S.w (0 :: ps))) (viewOf S.w (0 :: ps))

/-- What the machine is about to do once the loops `j, j+1, …` are over: advance the loop `j-1`,
or -- if `j = 0` -- run the epilogue. -/
def AtNext (q : PSt A B S.k S.m S.N) (s : Fin S.m → Bool) (j : ℕ) (ps : List ℕ) : Prop :=
  if j = 0 then S.AtEpi q s ps else S.AtAdv q s (j - 1) ps

/-- One iteration of the loop `j`: the nest below the loop `j` runs for the position `p` of its
variable, and then the loop moves on. -/
def IterStmt (j : ℕ) : Prop :=
  ∀ (pre : List ℕ), pre.length = j → (∀ x ∈ pre, x < S.n) →
  ∀ (p : ℕ), p < S.n →
  ∀ (bvr : ℕ → Bool), (∀ i, S.m ≤ i → bvr i = false) →
  ∀ (q : PSt A B S.k S.m S.N), S.Good q.ord q.pend (pre ++ [p]) →
    S.AtEnter q (resBV S.m bvr) (j + 1) (pre ++ [p]) →
    ∃ q' : PSt A B S.k S.m S.N,
      (match nextPos (dirOf S.L j) S.n p with
        | some p' =>
            S.Good q'.ord q'.pend (pre ++ [p']) ∧
              S.AtEnter q' (resBV S.m (S.nestRun (pre ++ [p]) (j + 1) bvr).1) (j + 1)
                (pre ++ [p']) ∧
              S.M.Reaches S.w (S.cfgAt q (pre ++ [p]))
                (S.nestRun (pre ++ [p]) (j + 1) bvr).2 (S.cfgAt q' (pre ++ [p']))
        | none =>
            S.Good q'.ord q'.pend pre ∧
              S.AtNext q' (resBV S.m (S.nestRun (pre ++ [p]) (j + 1) bvr).1) j pre ∧
              S.M.Reaches S.w (S.cfgAt q (pre ++ [p]))
                (S.nestRun (pre ++ [p]) (j + 1) bvr).2 (S.cfgAt q' pre))

/-- All the remaining iterations of the loop `j`. -/
def LoopStmt (j : ℕ) : Prop :=
  ∀ (pre : List ℕ), pre.length = j → (∀ x ∈ pre, x < S.n) →
  ∀ (p : ℕ), p < S.n →
  ∀ (bvr : ℕ → Bool), (∀ i, S.m ≤ i → bvr i = false) →
  ∀ (q : PSt A B S.k S.m S.N), S.Good q.ord q.pend (pre ++ [p]) →
    S.AtEnter q (resBV S.m bvr) (j + 1) (pre ++ [p]) →
    ∃ q' : PSt A B S.k S.m S.N,
      S.Good q'.ord q'.pend pre ∧
      S.AtNext q' (resBV S.m
          (runList (fun bv x => S.nestRun (pre ++ [x]) (j + 1) bv)
            (remPos (dirOf S.L j) S.n p) bvr).1) j pre ∧
      S.M.Reaches S.w (S.cfgAt q (pre ++ [p]))
        (runList (fun bv x => S.nestRun (pre ++ [x]) (j + 1) bv)
          (remPos (dirOf S.L j) S.n p) bvr).2 (S.cfgAt q' pre)

/-- The loops `j, j+1, …` of the nest. -/
def ClaimStmt (j : ℕ) : Prop :=
  ∀ (pre : List ℕ), pre.length = j → (∀ x ∈ pre, x < S.n) →
  ∀ (bvr : ℕ → Bool), (∀ i, S.m ≤ i → bvr i = false) →
  ∀ (q : PSt A B S.k S.m S.N), S.Good q.ord q.pend pre →
    S.AtEnter q (resBV S.m bvr) j pre →
    ∃ q' : PSt A B S.k S.m S.N,
      S.Good q'.ord q'.pend pre ∧
      S.AtNext q' (resBV S.m (S.nestRun pre j bvr).1) j pre ∧
      S.M.Reaches S.w (S.cfgAt q pre) (S.nestRun pre j bvr).2 (S.cfgAt q' pre)

/-! ## The order matrix is repaired correctly -/

private lemma bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

lemma good_same (ps : List ℕ) : S.Good (S.ordTrue ps) none ps := rfl

lemma good_push (ps : List ℕ) : S.Good (S.ordTrue ps) none (ps ++ [0]) := by
  show S.ordTrue ps = S.ordTrue (ps ++ [0])
  funext i j
  simp only [ordTrue, posOf_snoc_zero]

lemma good_right {pre : List ℕ} {p : ℕ} {x : Fin (S.k + 1)} (hx : (x : ℕ) = pre.length) :
    S.Good (S.ordTrue (pre ++ [p])) (some (x, true)) (pre ++ [p + 1]) := by
  unfold Good ordTrue
  funext i j
  have hxi : (i = x) = ((i : ℕ) = pre.length) := by rw [eq_iff_iff, Fin.ext_iff, hx]
  have hxj : (j = x) = ((j : ℕ) = pre.length) := by rw [eq_iff_iff, Fin.ext_iff, hx]
  refine bool_ext ?_
  by_cases hi : (i : ℕ) = pre.length <;> by_cases hj : (j : ℕ) = pre.length <;>
    simp [fixOrd_some, coin_viewOf, posOf_snoc, hxi, hxj, hi, hj, hx]; omega

lemma good_left {pre : List ℕ} {p : ℕ} {x : Fin (S.k + 1)} (hx : (x : ℕ) = pre.length)
    (hp : 0 < p) :
    S.Good (S.ordTrue (pre ++ [p])) (some (x, false)) (pre ++ [p - 1]) := by
  unfold Good ordTrue
  funext i j
  have hxi : (i = x) = ((i : ℕ) = pre.length) := by rw [eq_iff_iff, Fin.ext_iff, hx]
  have hxj : (j = x) = ((j : ℕ) = pre.length) := by rw [eq_iff_iff, Fin.ext_iff, hx]
  refine bool_ext ?_
  by_cases hi : (i : ℕ) = pre.length <;> by_cases hj : (j : ℕ) = pre.length <;>
    simp [fixOrd_some, coin_viewOf, posOf_snoc, hxi, hxj, hi, hj, hx] <;> omega

lemma good_pop {pre : List ℕ} {p : ℕ} {x : Fin (S.k + 1)} (hx : (x : ℕ) = pre.length)
    (hlt : pre.length < S.k) :
    S.Good (popFix S.k (S.ordTrue (pre ++ [p])) x (viewOf S.w (0 :: (pre ++ [p])))) none pre := by
  have hk : posOf (pre ++ [p]) S.k = 0 := posOf_of_length_le (by simp; omega)
  have hz : posOf pre pre.length = 0 := posOf_of_length_le (le_refl _)
  show popFix S.k (S.ordTrue (pre ++ [p])) x (viewOf S.w (0 :: (pre ++ [p]))) = S.ordTrue pre
  funext i j
  have hxi : (i = x) = ((i : ℕ) = pre.length) := by rw [eq_iff_iff, Fin.ext_iff, hx]
  have hxj : (j = x) = ((j : ℕ) = pre.length) := by rw [eq_iff_iff, Fin.ext_iff, hx]
  refine bool_ext ?_
  by_cases hi : (i : ℕ) = pre.length <;> by_cases hj : (j : ℕ) = pre.length <;>
    simp [popFix, ordTrue, coin_viewOf, hk, hz, posOf_snoc, hxi, hxj, hi, hj]

/-! ## One step of the machine -/

lemma step_def (q : PSt A B S.k S.m S.N) (ps : List ℕ) :
    S.M.step q (viewOf S.w (0 :: ps))
      = stepFn S.k S.m S.N S.L S.body S.epilogue S.vf q (viewOf S.w (0 :: ps)) := rfl

lemma stepCfg_out {q q' : PSt A B S.k S.m S.N} {ps : List ℕ} {b : B}
    (h : S.M.step q (viewOf S.w (0 :: ps)) = (q', PebbleAction.out b)) :
    S.M.stepCfg S.w (S.cfgAt q ps) = some ([b], S.cfgAt q' ps) := by
  simp only [cfgAt, Pebble.stepCfg, h]

lemma stepCfg_terminate {q q' : PSt A B S.k S.m S.N} {ps : List ℕ}
    (h : S.M.step q (viewOf S.w (0 :: ps)) = (q', PebbleAction.terminate)) :
    S.M.stepCfg S.w (S.cfgAt q ps) = some ([], PebbleCfg.halt) := by
  simp only [cfgAt, Pebble.stepCfg, h]

lemma stepCfg_push {q q' : PSt A B S.k S.m S.N} {ps : List ℕ}
    (h : S.M.step q (viewOf S.w (0 :: ps)) = (q', PebbleAction.push)) (hlt : ps.length < S.k) :
    S.M.stepCfg S.w (S.cfgAt q ps) = some ([], S.cfgAt q' (ps ++ [0])) := by
  simp only [cfgAt, Pebble.stepCfg, h]
  rw [if_pos (by simpa using hlt)]
  simp

lemma stepCfg_pop {q q' : PSt A B S.k S.m S.N} {pre : List ℕ} {p : ℕ}
    (h : S.M.step q (viewOf S.w (0 :: (pre ++ [p]))) = (q', PebbleAction.pop)) :
    S.M.stepCfg S.w (S.cfgAt q (pre ++ [p])) = some ([], S.cfgAt q' pre) := by
  simp only [cfgAt, Pebble.stepCfg, h]
  rw [if_neg (by simp)]
  simp [dropLast_cons_concat]

lemma stepCfg_right {q q' : PSt A B S.k S.m S.N} {pre : List ℕ} {p : ℕ}
    (h : S.M.step q (viewOf S.w (0 :: (pre ++ [p]))) = (q', PebbleAction.move true))
    (hp : p < S.w.length) :
    S.M.stepCfg S.w (S.cfgAt q (pre ++ [p])) = some ([], S.cfgAt q' (pre ++ [p + 1])) := by
  simp only [cfgAt, Pebble.stepCfg, h, getLast?_cons_concat, dropLast_cons_concat]
  simp [hp]

lemma stepCfg_left {q q' : PSt A B S.k S.m S.N} {pre : List ℕ} {p : ℕ}
    (h : S.M.step q (viewOf S.w (0 :: (pre ++ [p]))) = (q', PebbleAction.move false))
    (hp : 0 < p) :
    S.M.stepCfg S.w (S.cfgAt q (pre ++ [p])) = some ([], S.cfgAt q' (pre ++ [p - 1])) := by
  simp only [cfgAt, Pebble.stepCfg, h, getLast?_cons_concat, dropLast_cons_concat]
  simp [hp]

/-! ## Running the body of the nest on the current tuple -/

lemma posOf_eq_Tof {t : List ℕ} (ht : t.length = S.k) (j : Fin (S.k + 1)) :
    posOf t (j : ℕ) = Tof S.k t j := by
  rcases lt_or_ge (j : ℕ) S.k with h | h
  · unfold posOf Tof
    rw [List.getD_append _ _ _ _ (by omega)]
  · have hj : (j : ℕ) = S.k := by omega
    unfold posOf Tof
    rw [hj, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega), List.getElem?_append_right (by omega)]
    simp [ht]

lemma blk_exec {t : List ℕ} (ht : t.length = S.k) (hlt : ∀ p ∈ t, p < S.w.length)
    (s : Fin S.m → Bool) :
    bodyRun S.k S.m S.body S.vf s (blkOf S.k (S.ordTrue t) (viewOf S.w (0 :: t)))
      = ForProg.exec S.w S.body (setTuple S.L t (fun _ => 0)) (extBV S.m s) := by
  classical
  have htL : t.length = S.L.length := by rw [ht, S.hk]
  have hpos : ∀ i, setTuple S.L t (fun _ => 0) i = Tof S.k t (S.vf i) :=
    fun i => setTuple_eq_Tof S.k S.vf htL S.hvf i
  have hle : ∀ i j, S.ordTrue t i j = decide (Tof S.k t i ≤ Tof S.k t j) := by
    intro i j
    simp only [ordTrue, posOf_eq_Tof S ht]
  have hletk : letAt (viewOf S.w (0 :: t)) S.k = S.w[0]? := by
    rw [letAt_viewOf, posOf_of_length_le (le_of_eq ht)]
  by_cases hw : S.w = []
  · have ht0 : t = [] := by
      cases t with
      | nil => rfl
      | cons p tt => exact absurd (hlt p (by simp)) (by simp [hw])
    have hblk : blkOf S.k (S.ordTrue t) (viewOf S.w (0 :: t)) = none := by
      unfold blkOf
      rw [hletk, hw]
      rfl
    have hzero : ∀ i, setTuple S.L t (fun _ => 0) i = 0 := by
      intro i
      rw [hpos i, Tof, ht0]
      rcases hj : ((S.vf i : ℕ)) with _ | nn <;> simp [List.getD_eq_getElem?_getD]
    rw [hblk]
    show ForProg.exec ([] : List A) S.body (fun _ => 0) (extBV S.m s) = _
    rw [hw]
    exact ForProg.exec_congr_pos _ _ _ _ _ (fun i _ => (hzero i).symm)
  · obtain ⟨a0, hg0⟩ : ∃ a, S.w[0]? = some a := by
      cases hcw : S.w with
      | nil => exact absurd hcw hw
      | cons a rest => exact ⟨a, rfl⟩
    have hwpos : 0 < S.w.length := by
      cases hcw : S.w with
      | nil => exact absurd hcw hw
      | cons a rest => simp
    set bl : Blk A S.k :=
      ⟨fun i => (letAt (viewOf S.w (0 :: t)) (i : ℕ)).getD a0, S.ordTrue t⟩ with hbl
    have hblk : blkOf S.k (S.ordTrue t) (viewOf S.w (0 :: t)) = some bl := by
      unfold blkOf
      rw [hletk, hg0]
    have hTlt : ∀ i : Fin (S.k + 1), Tof S.k t i < S.w.length := by
      intro i
      rw [← posOf_eq_Tof S ht]
      rcases lt_or_ge (i : ℕ) t.length with h | h
      · refine hlt _ ?_
        unfold posOf
        rw [List.getD_eq_getElem _ _ h]
        exact List.getElem_mem h
      · rw [posOf_of_length_le h]
        exact hwpos
    have hlets : ∀ i : Fin (S.k + 1), S.w[Tof S.k t i]? = some (bl.lets i) := by
      intro i
      have h1 : letAt (viewOf S.w (0 :: t)) (i : ℕ) = S.w[Tof S.k t i]? := by
        rw [letAt_viewOf, posOf_eq_Tof S ht]
      obtain ⟨x, hx⟩ : ∃ x, S.w[Tof S.k t i]? = some x :=
        ⟨_, List.getElem?_eq_getElem (hTlt i)⟩
      rw [hx]
      simp only [hbl, h1, hx, Option.getD_some]
    have hlets' : ∀ i j, Tof S.k t i = Tof S.k t j → bl.lets i = bl.lets j := by
      intro i j hij
      have h1 := hlets i
      have h2 := hlets j
      rw [hij] at h1
      exact Option.some_inj.mp (h1.symm.trans h2)
    have hle' : ∀ i j, bl.le i j = decide (Tof S.k t i ≤ Tof S.k t j) := hle
    have hcons : ∀ i j, cpos bl i = cpos bl j → bl.lets i = bl.lets j :=
      cpos_consistent bl (Tof S.k t) hle' hlets'
    have hex : ForProg.exec (cword bl) S.body (fun i => ((cpos bl (S.vf i) : ℕ))) (extBV S.m s)
        = ForProg.exec S.w S.body (setTuple S.L t (fun _ => 0)) (extBV S.m s) := by
      refine (ForProg.exec_congr_view S.w (cword bl) S.body S.hbody _ _ _ ?_ ?_).symm
      · intro i _ j _
        rw [hpos i, hpos j]
        exact (cpos_le_iff bl (Tof S.k t) hle' (S.vf i) (S.vf j)).symm
      · intro i _
        rw [hpos i, hlets (S.vf i), cword_getElem bl hcons (S.vf i)]
    rw [hblk]
    exact hex

/-! ## Elementary facts about the variable indices -/

lemma fin'_val {j : ℕ} (hj : j ≤ S.k) : ((S.fin' j : Fin (S.k + 1)) : ℕ) = j := by
  simp only [fin']
  omega

lemma fsucc_fin' (j : ℕ) : fsucc S.k (S.fin' j) = S.fin' (j + 1) := by
  refine Fin.ext ?_
  simp only [fsucc, fin']
  omega

/-! ## The step of the machine in each phase -/

lemma step_adv (q : PSt A B S.k S.m S.N) (j : Fin (S.k + 1)) (hph : q.ph = Ph.adv j)
    (ps : List ℕ) :
    S.M.step q (viewOf S.w (0 :: ps))
      = advAct S.k S.m S.N S.L j q.bv (fixOrd S.k q.ord q.pend (viewOf S.w (0 :: ps)))
          (viewOf S.w (0 :: ps)) := by
  obtain ⟨bv, o, pd, ph⟩ := q
  subst hph
  rfl

lemma step_chk (q : PSt A B S.k S.m S.N) (j : Fin (S.k + 1)) (hph : q.ph = Ph.chk j)
    (ps : List ℕ) :
    S.M.step q (viewOf S.w (0 :: ps))
      = (match letAt (viewOf S.w (0 :: ps)) (j : ℕ) with
        | none => popAct S.k S.m S.N j q.bv
            (fixOrd S.k q.ord q.pend (viewOf S.w (0 :: ps))) (viewOf S.w (0 :: ps))
        | some _ => enterAct S.k S.m S.N S.L S.body S.epilogue S.vf (fsucc S.k j) q.bv
            (fixOrd S.k q.ord q.pend (viewOf S.w (0 :: ps))) (viewOf S.w (0 :: ps))) := by
  obtain ⟨bv, o, pd, ph⟩ := q
  subst hph
  rfl

lemma step_init (q : PSt A B S.k S.m S.N) (j : Fin (S.k + 1)) (hph : q.ph = Ph.init j)
    (ps : List ℕ) :
    S.M.step q (viewOf S.w (0 :: ps))
      = (match letAt (viewOf S.w (0 :: ps)) (j : ℕ) with
        | none => popAct S.k S.m S.N j q.bv
            (fixOrd S.k q.ord q.pend (viewOf S.w (0 :: ps))) (viewOf S.w (0 :: ps))
        | some _ =>
            if dirOf S.L (j : ℕ) then
              enterAct S.k S.m S.N S.L S.body S.epilogue S.vf (fsucc S.k j) q.bv
                (fixOrd S.k q.ord q.pend (viewOf S.w (0 :: ps))) (viewOf S.w (0 :: ps))
            else
              (⟨q.bv, fixOrd S.k q.ord q.pend (viewOf S.w (0 :: ps)), some (j, true), Ph.seek j⟩,
                PebbleAction.move true)) := by
  obtain ⟨bv, o, pd, ph⟩ := q
  subst hph
  rfl

lemma step_seek (q : PSt A B S.k S.m S.N) (j : Fin (S.k + 1)) (hph : q.ph = Ph.seek j)
    (ps : List ℕ) :
    S.M.step q (viewOf S.w (0 :: ps))
      = (match letAt (viewOf S.w (0 :: ps)) (j : ℕ) with
        | none => (⟨q.bv, fixOrd S.k q.ord q.pend (viewOf S.w (0 :: ps)), some (j, false),
            Ph.enter (fsucc S.k j)⟩, PebbleAction.move false)
        | some _ => (⟨q.bv, fixOrd S.k q.ord q.pend (viewOf S.w (0 :: ps)), some (j, true),
            Ph.seek j⟩, PebbleAction.move true)) := by
  obtain ⟨bv, o, pd, ph⟩ := q
  subst hph
  rfl

lemma step_enter (q : PSt A B S.k S.m S.N) (j : Fin (S.k + 1)) (hph : q.ph = Ph.enter j)
    (ps : List ℕ) :
    S.M.step q (viewOf S.w (0 :: ps))
      = enterAct S.k S.m S.N S.L S.body S.epilogue S.vf j q.bv
          (fixOrd S.k q.ord q.pend (viewOf S.w (0 :: ps))) (viewOf S.w (0 :: ps)) := by
  obtain ⟨bv, o, pd, ph⟩ := q
  subst hph
  rfl

lemma step_epiStart (q : PSt A B S.k S.m S.N) (hph : q.ph = Ph.epiStart) (ps : List ℕ) :
    S.M.step q (viewOf S.w (0 :: ps))
      = epiAct S.k S.m S.N S.epilogue q.bv
          (fixOrd S.k q.ord q.pend (viewOf S.w (0 :: ps))) (viewOf S.w (0 :: ps)) := by
  obtain ⟨bv, o, pd, ph⟩ := q
  subst hph
  rfl

lemma step_start (q : PSt A B S.k S.m S.N) (hph : q.ph = Ph.start) (ps : List ℕ) :
    S.M.step q (viewOf S.w (0 :: ps))
      = ((⟨q.bv, fixOrd S.k q.ord q.pend (viewOf S.w (0 :: ps)), none, Ph.enter 0⟩ :
            PSt A B S.k S.m S.N), PebbleAction.push) := by
  obtain ⟨bv, o, pd, ph⟩ := q
  subst hph
  rfl

lemma step_epi (q : PSt A B S.k S.m S.N) (l : BddList B S.N) (hph : q.ph = Ph.epi l)
    (ps : List ℕ) :
    S.M.step q (viewOf S.w (0 :: ps))
      = (match l.val with
        | [] => (⟨q.bv, fixOrd S.k q.ord q.pend (viewOf S.w (0 :: ps)), none, Ph.epi l⟩,
            PebbleAction.terminate)
        | b :: _ => (⟨q.bv, fixOrd S.k q.ord q.pend (viewOf S.w (0 :: ps)), none,
            Ph.epi (BddList.tail l)⟩, PebbleAction.out b)) := by
  obtain ⟨bv, o, pd, ph⟩ := q
  subst hph
  rfl

/-! ## Recognising the phase of the machine -/

lemma fpred_fin' {j : ℕ} (hj : j ≤ S.k) : fpred S.k (S.fin' j) = S.fin' (j - 1) := by
  refine Fin.ext ?_
  simp only [fpred, fin']
  omega

lemma flast_eq_fin' : flast S.k = S.fin' (S.k - 1) := by
  refine Fin.ext ?_
  simp only [flast, fin']
  omega

lemma atEnter_of_ph (q : PSt A B S.k S.m S.N) (j : ℕ) (hph : q.ph = Ph.enter (S.fin' j))
    (ps : List ℕ) : S.AtEnter q q.bv j ps := S.step_enter q (S.fin' j) hph ps

lemma atAdv_of_ph (q : PSt A B S.k S.m S.N) (j : ℕ) (hph : q.ph = Ph.adv (S.fin' j))
    (ps : List ℕ) : S.AtAdv q q.bv j ps := S.step_adv q (S.fin' j) hph ps

lemma atEpi_of_ph (q : PSt A B S.k S.m S.N) (hph : q.ph = Ph.epiStart) (ps : List ℕ) :
    S.AtEpi q q.bv ps := S.step_epiStart q hph ps

/-- The phase in which the machine is left by a `pop` that ends the loop `j`. -/
lemma atNext_of_pop {j : ℕ} (hj : j ≤ S.k) (q : PSt A B S.k S.m S.N) (ps : List ℕ)
    (hph : q.ph = (if ((S.fin' j : Fin (S.k + 1)) : ℕ) = 0 then (Ph.epiStart : Ph B S.k S.N)
      else Ph.adv (fpred S.k (S.fin' j)))) : S.AtNext q q.bv j ps := by
  have hjv : ((S.fin' j : Fin (S.k + 1)) : ℕ) = j := S.fin'_val hj
  rw [hjv] at hph
  unfold AtNext
  by_cases hj0 : j = 0
  · rw [if_pos hj0]
    rw [if_pos hj0] at hph
    exact S.atEpi_of_ph q hph ps
  · rw [if_neg hj0]
    rw [if_neg hj0, S.fpred_fin' hj] at hph
    exact S.atAdv_of_ph q (j - 1) hph ps

/-! ## Advancing a loop -/

lemma letAt_snoc {pre : List ℕ} {p : ℕ} {x : Fin (S.k + 1)} (hx : (x : ℕ) = pre.length) :
    letAt (viewOf S.w (0 :: (pre ++ [p]))) (x : ℕ) = S.w[p]? := by
  rw [letAt_viewOf, posOf_snoc, if_pos hx]

lemma coin_top {pre : List ℕ} {p : ℕ} {x : Fin (S.k + 1)} (hx : (x : ℕ) = pre.length)
    (hlen : pre.length < S.k) :
    coin (viewOf S.w (0 :: (pre ++ [p]))) S.k (x : ℕ) = decide (p = 0) := by
  have h1 : posOf (pre ++ [p]) (x : ℕ) = p := by rw [posOf_snoc, if_pos hx]
  have h2 : posOf (pre ++ [p]) S.k = 0 := posOf_of_length_le (by simp; omega)
  rw [coin_viewOf, h1, h2]

/-- From the phase `adv j` the machine moves the pebble of the loop `j` to the next position of
that loop, or -- if the loop is over -- pops it. -/
lemma adv_run {j : ℕ} (hj : j < S.k) {pre : List ℕ} (hpre : pre.length = j) {p : ℕ}
    (hp : p < S.n) (q : PSt A B S.k S.m S.N) (s : Fin S.m → Bool)
    (hph : S.AtAdv q s j (pre ++ [p])) (hgood : S.Good q.ord q.pend (pre ++ [p])) :
    ∃ q' : PSt A B S.k S.m S.N,
      (match nextPos (dirOf S.L j) S.n p with
        | some p' => S.Good q'.ord q'.pend (pre ++ [p']) ∧ S.AtEnter q' s (j + 1) (pre ++ [p']) ∧
            S.M.Reaches S.w (S.cfgAt q (pre ++ [p])) [] (S.cfgAt q' (pre ++ [p']))
        | none => S.Good q'.ord q'.pend pre ∧ S.AtNext q' s j pre ∧
            S.M.Reaches S.w (S.cfgAt q (pre ++ [p])) [] (S.cfgAt q' pre)) := by
  have hjv : ((S.fin' j : Fin (S.k + 1)) : ℕ) = j := S.fin'_val (le_of_lt hj)
  have hxv : ((S.fin' j : Fin (S.k + 1)) : ℕ) = pre.length := by rw [hjv, hpre]
  have hprek : pre.length < S.k := by omega
  have hpw : p < S.w.length := hp
  have hstep : S.M.step q (viewOf S.w (0 :: (pre ++ [p])))
      = advAct S.k S.m S.N S.L (S.fin' j) s (S.ordTrue (pre ++ [p]))
          (viewOf S.w (0 :: (pre ++ [p]))) := by
    rw [S.step_def q (pre ++ [p]), hph, hgood]
  have hdx : dirOf S.L ((S.fin' j : Fin (S.k + 1)) : ℕ) = dirOf S.L j := by rw [hjv]
  cases hd : dirOf S.L j with
  | true =>
      set q1 : PSt A B S.k S.m S.N :=
        ⟨s, S.ordTrue (pre ++ [p]), some (S.fin' j, true), Ph.chk (S.fin' j)⟩ with hq1
      have hact : S.M.step q (viewOf S.w (0 :: (pre ++ [p]))) = (q1, PebbleAction.move true) := by
        rw [hstep]
        simp only [advAct, hdx, hd, if_true, hq1]
      have hr1 : S.M.stepCfg S.w (S.cfgAt q (pre ++ [p]))
          = some ([], S.cfgAt q1 (pre ++ [p + 1])) := S.stepCfg_right hact hpw
      have hg1 : fixOrd S.k q1.ord q1.pend (viewOf S.w (0 :: (pre ++ [p + 1])))
          = S.ordTrue (pre ++ [p + 1]) := S.good_right hxv
      have hlet : letAt (viewOf S.w (0 :: (pre ++ [p + 1]))) ((S.fin' j : Fin (S.k + 1)) : ℕ)
          = S.w[p + 1]? := S.letAt_snoc hxv
      by_cases hlt : p + 1 < S.n
      · obtain ⟨a, ha⟩ : ∃ a, S.w[p + 1]? = some a :=
          ⟨_, List.getElem?_eq_getElem (show p + 1 < S.w.length from hlt)⟩
        rw [show nextPos true S.n p = some (p + 1) from by simp [nextPos, hlt]]
        refine ⟨q1, hg1, ?_, ?_⟩
        · unfold AtEnter
          rw [show stepFn S.k S.m S.N S.L S.body S.epilogue S.vf q1
                (viewOf S.w (0 :: (pre ++ [p + 1])))
              = S.M.step q1 (viewOf S.w (0 :: (pre ++ [p + 1]))) from rfl,
            S.step_chk q1 (S.fin' j) rfl, hlet, ha, fsucc_fin']
        · exact Pebble.reaches_one hr1
      · have hlt' : ¬ (p + 1 < S.w.length) := hlt
        have ha : S.w[p + 1]? = none := List.getElem?_eq_none (by omega)
        set q2 : PSt A B S.k S.m S.N :=
          ⟨q1.bv, popFix S.k (S.ordTrue (pre ++ [p + 1])) (S.fin' j)
              (viewOf S.w (0 :: (pre ++ [p + 1]))), none,
            if ((S.fin' j : Fin (S.k + 1)) : ℕ) = 0 then Ph.epiStart
              else Ph.adv (fpred S.k (S.fin' j))⟩ with hq2
        have hact2 : S.M.step q1 (viewOf S.w (0 :: (pre ++ [p + 1])))
            = (q2, PebbleAction.pop) := by
          simp only [S.step_chk q1 (S.fin' j) rfl, hlet, ha, hg1, popAct, hq2]
        have hr2 : S.M.stepCfg S.w (S.cfgAt q1 (pre ++ [p + 1]))
            = some ([], S.cfgAt q2 pre) := S.stepCfg_pop hact2
        rw [show nextPos true S.n p = none from by simp [nextPos, hlt]]
        refine ⟨q2, S.good_pop hxv hprek, S.atNext_of_pop (le_of_lt hj) q2 pre rfl, ?_⟩
        exact (show ([] : List B) = [] ++ [] from rfl) ▸
          Pebble.reaches_trans (Pebble.reaches_one hr1) (Pebble.reaches_one hr2)
  | false =>
      have hcoin : coin (viewOf S.w (0 :: (pre ++ [p]))) S.k ((S.fin' j : Fin (S.k + 1)) : ℕ)
          = decide (p = 0) := S.coin_top hxv hprek
      by_cases hp0 : p = 0
      · subst hp0
        set q2 : PSt A B S.k S.m S.N :=
          ⟨s, popFix S.k (S.ordTrue (pre ++ [0])) (S.fin' j)
              (viewOf S.w (0 :: (pre ++ [0]))), none,
            if ((S.fin' j : Fin (S.k + 1)) : ℕ) = 0 then Ph.epiStart
              else Ph.adv (fpred S.k (S.fin' j))⟩ with hq2
        have hact : S.M.step q (viewOf S.w (0 :: (pre ++ [0]))) = (q2, PebbleAction.pop) := by
          rw [hstep]
          simp only [advAct, hdx, hd, if_false, Bool.false_eq_true, hcoin, decide_true, if_true,
            popAct, hq2]
        have hr1 : S.M.stepCfg S.w (S.cfgAt q (pre ++ [0])) = some ([], S.cfgAt q2 pre) :=
          S.stepCfg_pop hact
        rw [show nextPos false S.n 0 = none from by simp [nextPos]]
        exact ⟨q2, S.good_pop hxv hprek, S.atNext_of_pop (le_of_lt hj) q2 pre rfl,
          Pebble.reaches_one hr1⟩
      · set q1 : PSt A B S.k S.m S.N :=
          ⟨s, S.ordTrue (pre ++ [p]), some (S.fin' j, false),
            Ph.enter (fsucc S.k (S.fin' j))⟩ with hq1
        have hact : S.M.step q (viewOf S.w (0 :: (pre ++ [p]))) = (q1, PebbleAction.move false) := by
          rw [hstep]
          simp only [advAct, hdx, hd, if_false, Bool.false_eq_true, hcoin, hp0, decide_false,
            hq1]
        have hr1 : S.M.stepCfg S.w (S.cfgAt q (pre ++ [p]))
            = some ([], S.cfgAt q1 (pre ++ [p - 1])) :=
          S.stepCfg_left hact (Nat.pos_of_ne_zero hp0)
        rw [show nextPos false S.n p = some (p - 1) from by simp [nextPos, hp0]]
        refine ⟨q1, S.good_left hxv (Nat.pos_of_ne_zero hp0), ?_, Pebble.reaches_one hr1⟩
        exact S.atEnter_of_ph q1 (j + 1) (by rw [hq1, fsucc_fin']) (pre ++ [p - 1])

/-! ## Running the body -/

/-- One iteration of the body of the nest, for the tuple `t` of positions of the loop
variables. -/
lemma body_run {t : List ℕ} (ht : t.length = S.k) (hlt : ∀ x ∈ t, x < S.n)
    (bvr : ℕ → Bool) (hbvr : ∀ i, S.m ≤ i → bvr i = false)
    (q : PSt A B S.k S.m S.N) (hgood : S.Good q.ord q.pend t)
    (hen : S.AtEnter q (resBV S.m bvr) S.k t) :
    ∃ q' : PSt A B S.k S.m S.N,
      S.Good q'.ord q'.pend t ∧
      S.AtNext q' (resBV S.m (ForProg.exec S.w S.body (setTuple S.L t (fun _ => 0)) bvr).1)
        S.k t ∧
      S.M.Reaches S.w (S.cfgAt q t)
        (ForProg.exec S.w S.body (setTuple S.L t (fun _ => 0)) bvr).2 (S.cfgAt q' t) := by
  classical
  have key : ∀ (E1 : ℕ → Bool) (E2 : List B), E2.length ≤ 1 →
      S.M.step q (viewOf S.w (0 :: t))
        = (match E2 with
          | [] => afterAct S.k S.m S.N S.L S.epilogue (resBV S.m E1) (S.ordTrue t)
              (viewOf S.w (0 :: t))
          | b :: _ => (⟨resBV S.m E1, S.ordTrue t, none, afterPh B S.k S.N⟩,
              PebbleAction.out b)) →
      ∃ q' : PSt A B S.k S.m S.N, S.Good q'.ord q'.pend t ∧ S.AtNext q' (resBV S.m E1) S.k t ∧
        S.M.Reaches S.w (S.cfgAt q t) E2 (S.cfgAt q' t) := by
    intro E1 E2 hlen hstep
    cases E2 with
    | nil =>
        refine ⟨q, hgood, ?_, Pebble.Reaches.refl _⟩
        unfold AtNext
        by_cases hk0 : S.k = 0
        · rw [if_pos hk0]
          show stepFn S.k S.m S.N S.L S.body S.epilogue S.vf q (viewOf S.w (0 :: t))
            = epiAct S.k S.m S.N S.epilogue (resBV S.m E1)
                (fixOrd S.k q.ord q.pend (viewOf S.w (0 :: t))) (viewOf S.w (0 :: t))
          rw [hgood, ← S.step_def q t, hstep]
          simp only [afterAct, if_pos hk0]
        · rw [if_neg hk0]
          show stepFn S.k S.m S.N S.L S.body S.epilogue S.vf q (viewOf S.w (0 :: t))
            = advAct S.k S.m S.N S.L (S.fin' (S.k - 1)) (resBV S.m E1)
                (fixOrd S.k q.ord q.pend (viewOf S.w (0 :: t))) (viewOf S.w (0 :: t))
          rw [hgood, ← S.step_def q t, hstep]
          simp only [afterAct, if_neg hk0, S.flast_eq_fin']
    | cons b rest =>
        have hrest : rest = [] := by simpa using hlen
        subst hrest
        refine ⟨⟨resBV S.m E1, S.ordTrue t, none, afterPh B S.k S.N⟩, S.good_same t, ?_, ?_⟩
        · unfold AtNext
          by_cases hk0 : S.k = 0
          · rw [if_pos hk0]
            refine S.atEpi_of_ph _ ?_ t
            simp only [afterPh, if_pos hk0]
          · rw [if_neg hk0]
            refine S.atAdv_of_ph _ (S.k - 1) ?_ t
            simp only [afterPh, if_neg hk0, S.flast_eq_fin']
        · exact Pebble.reaches_one (S.stepCfg_out hstep)
  refine key _ _ (S.hone S.w _ _) ?_
  have hbe : bodyRun S.k S.m S.body S.vf (resBV S.m bvr)
      (blkOf S.k (S.ordTrue t) (viewOf S.w (0 :: t)))
      = ForProg.exec S.w S.body (setTuple S.L t (fun _ => 0)) bvr := by
    rw [S.blk_exec ht hlt (resBV S.m bvr), extBV_resBV S.m bvr hbvr]
  rw [S.step_def q t, hen, hgood]
  unfold enterAct
  rw [if_pos (S.fin'_val (le_refl S.k))]
  unfold bodyAct
  rw [hbe]
  rfl

end Setup

end PebFor

end Lax194892Proofs.Transducers
