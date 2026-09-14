/-
The `k`-pebble transducer that simulates a `(k+1)`-pebble transducer on the marked square.

Let `M` be a `(k+1)`-pebble transducer over the alphabet `A`, and let `w` be an input.  Put
`N = w.length + 2`, `u = pad w` and `S = markedSquare (Option A) u`; the gaps of `S` are the pairs
`(i, j)` of a block `i < N` and an offset `j < N`, written `gp w i j = i * N + j`, together with
the last gap `N * N`.  A gap `p` of `w` is encoded by the offset `p + 1`, which is an offset in the
interior of a block because of the padding.

A stack `[p₁, …, p_ℓ]` of pebbles of `M` is encoded by the stack

* `[]`                                        if `ℓ = 0`;
* `[gp w p₁ (p₁ + 1)]`                        if `ℓ = 1` -- the *marked gap* of the block `p₁`;
* `[gp w p₁ (p₂ + 1), …, gp w p₁ (p_ℓ + 1)]`  if `ℓ ≥ 2`

of pebbles of the simulating machine, which therefore needs only `k` pebbles: the bottom pebble of
`M` is remembered by the *block* in which all the other pebbles sit.  In the third case the two
letters adjacent to `p₁` are remembered in the state (`ctxOf`), and whether a pebble `p` of the
block `p₁` is at the same gap as `p₁` is visible because `gp w p₁ (p + 1)` is then the marked gap
of the block.  This is what the decoding `decView` of a view does, and
`PebSq.decView_encStack` is the statement that it decodes the view of the encoded stack into the
view of the stack.

Because the simulating machine has no instruction that does nothing, the moves that the encoding
requires -- from the marked gap of a block to the marked gap of the next one, from a gap of a block
to the offset `1` of that block, and so on -- are performed in auxiliary *phases* (`Ph`), during
which the machine walks in one direction until one of the three tests of
`RequestProject/PartD/PebbleSquareIdx.lean` succeeds.
-/
import Lax194892Proofs.Source.PartD.PebbleSquareIdx
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace PebSq

/-! ## The simulating machine -/

/-- The alphabet of the marked square of the padded input. -/
abbrev Alph (A : Type) := Option A ⊕ Option A

/-- The phases of the simulating machine: `run` mirrors a step of the simulated machine, and the
five other phases walk the topmost pebble to the gap where the encoding requires it.

* `mR`, `mL`: walk right (resp. left) to the next marked gap;
* `s1`: walk left to the start of the block, then take one step to the right;
* `sM`: walk left to the start of the block, then walk right to the marked gap;
* `coin`: walk right until the topmost pebble meets a lower one, then continue as `s1`. -/
inductive Ph
  | run
  | mR
  | mL
  | s1
  | sM
  | coin
  deriving DecidableEq

instance : Finite Ph := by
  have h : Function.Injective (fun p : Ph => match p with
      | Ph.run => (0 : Fin 6) | Ph.mR => 1 | Ph.mL => 2
      | Ph.s1 => 3 | Ph.sM => 4 | Ph.coin => 5) := by
    intro p p' h
    cases p <;> cases p' <;> simp_all
  exact Finite.of_injective _ h

/-- The state of the simulating machine: the state of the simulated machine, whether the stack of
the simulated machine is higher than the encoded one, the two letters adjacent to the bottom
pebble, and the phase. -/
abbrev PSt (A Q : Type) := Q × Bool × (Option A × Option A) × Ph

variable {A B Q : Type} {k : ℕ}

/-- The letter of the input, forgotten by the marked square. -/
def decLet : Option (Alph A) → Option A
  | none => none
  | some (Sum.inl x) => x
  | some (Sum.inr x) => x

/-- The view of the simulated machine, decoded from the view of the simulating machine. -/
def decView (deep : Bool) (ct : Option A × Option A) (V : PebbleView (Alph A)) : PebbleView A :=
  if deep then
    (ct, true :: V.map (fun e => isMarkE e.1)) ::
      V.map (fun e => ((decLet e.1.1, decLet e.1.2), isMarkE e.1 :: e.2))
  else V.map (fun e => ((decLet e.1.1, decLet e.1.2), e.2))

/-- The action of the simulating machine that mirrors an action of the simulated machine. -/
def transl (deep : Bool) (ct : Option A × Option A) (V : PebbleView (Alph A))
    (q' : Q) : PebbleAction B → PSt A Q × PebbleAction B
  | PebbleAction.out b => ((q', deep, ct, Ph.run), PebbleAction.out b)
  | PebbleAction.terminate => ((q', deep, ct, Ph.run), PebbleAction.terminate)
  | PebbleAction.move d =>
      if deep then ((q', deep, ct, Ph.run), PebbleAction.move d)
      else ((q', false, ct, if d then Ph.mR else Ph.mL), PebbleAction.move d)
  | PebbleAction.push =>
      if deep then ((q', true, ct, Ph.coin), PebbleAction.push)
      else
        match V.getLast? with
        | none => ((q', false, ct, Ph.mR), PebbleAction.push)
        | some e => ((q', true, (decLet e.1.1, decLet e.1.2), Ph.s1), PebbleAction.move false)
  | PebbleAction.pop =>
      if deep then
        (if V.length = 1 then ((q', false, (none, none), Ph.sM), PebbleAction.move false)
          else ((q', true, ct, Ph.run), PebbleAction.pop))
      else ((q', false, ct, Ph.run), PebbleAction.pop)

/-- One step of the simulating machine. -/
def runStep (M : Pebble A B Q k) :
    PSt A Q → PebbleView (Alph A) → PSt A Q × PebbleAction B
  | (q, deep, ct, Ph.run), V =>
      transl deep ct V (M.step q (decView deep ct V)).1 (M.step q (decView deep ct V)).2
  | (q, deep, ct, Ph.mR), V =>
      if topMark V then
        transl deep ct V (M.step q (decView deep ct V)).1 (M.step q (decView deep ct V)).2
      else ((q, deep, ct, Ph.mR), PebbleAction.move true)
  | (q, deep, ct, Ph.mL), V =>
      if topMark V then
        transl deep ct V (M.step q (decView deep ct V)).1 (M.step q (decView deep ct V)).2
      else ((q, deep, ct, Ph.mL), PebbleAction.move false)
  | (q, deep, ct, Ph.s1), V =>
      if topStart V then ((q, deep, ct, Ph.run), PebbleAction.move true)
      else ((q, deep, ct, Ph.s1), PebbleAction.move false)
  | (q, deep, ct, Ph.sM), V =>
      if topStart V then ((q, deep, ct, Ph.mR), PebbleAction.move true)
      else ((q, deep, ct, Ph.sM), PebbleAction.move false)
  | (q, deep, ct, Ph.coin), V =>
      if topCoin V then ((q, deep, ct, Ph.s1), PebbleAction.move false)
      else ((q, deep, ct, Ph.coin), PebbleAction.move true)

/-- The `k`-pebble transducer that simulates the `(k+1)`-pebble transducer `M` on the marked
square of the padded input. -/
def sim (M : Pebble A B Q (k + 1)) : Pebble (Alph A) B (PSt A Q) k where
  init := (M.init, false, (none, none), Ph.run)
  step := runStep M

/-! ## The encoding of a stack -/

/-- The marked square of the padded input. -/
def sqOf (w : List A) : List (Alph A) := markedSquare (Option A) (pad w)

/-- The gap of the marked square at the offset `j` of the block `i`. -/
def gp (w : List A) (i j : ℕ) : ℕ := i * (w.length + 2) + j

lemma pad_len (w : List A) : (pad w).length = w.length + 2 := pad_length w

@[simp] lemma sqOf_length (w : List A) :
    (sqOf w).length = (w.length + 2) * (w.length + 2) := by
  rw [sqOf, markedSquare_length, pad_len]

lemma pad_get {w : List A} {j : ℕ} (h : j < (pad w).length) : (pad w)[j] = padLet w j := by
  have h1 : (pad w)[j]? = some (padLet w j) := pad_getElem? (by simpa [pad_len] using h)
  rw [List.getElem?_eq_getElem h] at h1
  exact Option.some_inj.mp h1

/-- The encoding of the stack of the simulated machine. -/
def encStack (w : List A) : List ℕ → List ℕ
  | [] => []
  | [p] => [gp w p (p + 1)]
  | p₁ :: p₂ :: rest => (p₂ :: rest).map (fun p => gp w p₁ (p + 1))

/-- The two letters adjacent to the bottom pebble. -/
def ctxOf (w : List A) : List ℕ → Option A × Option A
  | [] => (none, none)
  | p :: _ => (padLet w p, padLet w (p + 1))

/-- The two letters adjacent to the bottom pebble, as remembered by the simulating machine: they
are only needed when the stack of the simulated machine is higher than the encoded one. -/
def ctxSt (w : List A) (st : List ℕ) : Option A × Option A :=
  if 2 ≤ st.length then ctxOf w st else (none, none)

/-- The state of the simulating machine that encodes a state and a stack of the simulated
machine. -/
def encSt (w : List A) (q : Q) (st : List ℕ) : PSt A Q :=
  (q, decide (2 ≤ st.length), ctxSt w st, Ph.run)

/-- The configuration of the simulating machine that encodes a configuration of the simulated
machine. -/
def encCfg (w : List A) : PebbleCfg Q → PebbleCfg (PSt A Q)
  | PebbleCfg.halt => PebbleCfg.halt
  | PebbleCfg.conf q st => PebbleCfg.conf (encSt w q st) (encStack w st)

/-! ## The letters at an encoded gap -/

lemma decLet_ite {c : Prop} [Decidable c] (y : Option A) :
    decLet (some (if c then Sum.inl y else Sum.inr y)) = y := by
  by_cases h : c <;> simp [h, decLet]

/-- The two letters adjacent to an encoded gap decode to the two letters adjacent to the gap of
the input that it encodes. -/
lemma decLet_at {w : List A} {i p : ℕ} (hi : i ≤ w.length) (hp : p ≤ w.length) :
    decLet (if gp w i (p + 1) = 0 then none else (sqOf w)[gp w i (p + 1) - 1]?) = padLet w p ∧
      decLet ((sqOf w)[gp w i (p + 1)]?) = padLet w (p + 1) := by
  have hN : (pad w).length = w.length + 2 := pad_len w
  have hi' : i < (pad w).length := by omega
  have hp1 : p + 1 < (pad w).length := by omega
  have hp0 : p < (pad w).length := by omega
  constructor
  · rw [if_neg (by simp [gp])]
    have hidx : gp w i (p + 1) - 1 = i * (pad w).length + p := by simp [gp, hN]
    rw [sqOf, hidx, markedSquare_getElem? hi' hp0, decLet_ite, pad_get hp0]
  · have hidx : gp w i (p + 1) = i * (pad w).length + (p + 1) := by simp [gp, hN]
    rw [sqOf, hidx, markedSquare_getElem? hi' hp1, decLet_ite, pad_get hp1]

/-- Whether an encoded gap is the marked gap of its block. -/
lemma isMarkE_at {w : List A} {i p : ℕ} (hi : i ≤ w.length) (hp : p ≤ w.length) :
    isMarkE ((if gp w i (p + 1) = 0 then none else (sqOf w)[gp w i (p + 1) - 1]?),
      (sqOf w)[gp w i (p + 1)]?) = decide (p = i) := by
  have hN : (pad w).length = w.length + 2 := pad_len w
  have hidx : gp w i (p + 1) = i * (pad w).length + (p + 1) := by simp [gp, hN]
  rw [sqOf, hidx, isMarkE_coord (u := pad w) (by omega) (by omega) (by omega)]
  simp only [decide_eq_decide]
  omega

/-! ## The decoding of the view of an encoded stack -/

/-- **The view of the encoded stack decodes to the view of the stack.** -/
lemma decView_encStack {w : List A} {st : List ℕ}
    (hval : ∀ p ∈ st, p ≤ w.length) :
    decView (decide (2 ≤ st.length)) (ctxOf w st) (viewOf (sqOf w) (encStack w st))
      = viewOf w st := by
  match st with
  | [] => simp [encStack, viewOf, decView]
  | [p] =>
      have hp : p ≤ w.length := hval p (by simp)
      have hl := decLet_at (w := w) (i := p) (p := p) hp hp
      simp only [encStack, viewOf, decView, List.length_singleton, List.map_cons, List.map_nil,
        decide_eq_true_eq, Nat.reduceLeDiff]
      refine List.cons_eq_cons.mpr ⟨?_, rfl⟩
      have h1 : (if p = 0 then none else w[p - 1]?) = padLet w p := by
        simp [padLet]
      have h2 : w[p]? = padLet w (p + 1) := by simp [padLet]
      rw [Prod.mk.injEq]
      refine ⟨?_, by simp⟩
      rw [Prod.mk.injEq]
      exact ⟨by rw [hl.1, h1], by rw [hl.2, h2]⟩
  | p₁ :: p₂ :: rest =>
      have hp₁ : p₁ ≤ w.length := hval p₁ (by simp)
      set R := p₂ :: rest with hR
      have hRval : ∀ p ∈ R, p ≤ w.length := by
        intro p hp; exact hval p (by simp [hR] at hp ⊢; tauto)
      have hdeep : decide (2 ≤ (p₁ :: R).length) = true := by
        simp [hR]
      rw [hdeep]
      have henc : encStack w (p₁ :: R) = R.map (fun p => gp w p₁ (p + 1)) := by
        simp [encStack, hR]
      rw [henc, decView, if_pos rfl]
      have hview : viewOf (sqOf w) (R.map (fun p => gp w p₁ (p + 1)))
          = R.map (fun p =>
            (((if gp w p₁ (p + 1) = 0 then none else (sqOf w)[gp w p₁ (p + 1) - 1]?),
              (sqOf w)[gp w p₁ (p + 1)]?),
              R.map (fun q => decide (gp w p₁ (q + 1) = gp w p₁ (p + 1))))) := by
        simp only [viewOf, List.map_map, Function.comp_def]
      rw [hview]
      simp only [List.map_map, Function.comp_def]
      rw [viewOf]
      simp only [List.map_cons]
      refine List.cons_eq_cons.mpr ⟨?_, ?_⟩
      · -- the bottom pebble
        rw [Prod.mk.injEq]
        constructor
        · rw [ctxOf, Prod.mk.injEq]
          constructor
          · simp [padLet]
          · simp [padLet]
        · refine List.cons_eq_cons.mpr ⟨by simp, ?_⟩
          refine List.map_congr_left ?_
          intro p hp
          rw [isMarkE_at hp₁ (hRval p hp)]
      · -- the pebbles above the bottom one
        refine List.map_congr_left ?_
        intro p hp
        have hple : p ≤ w.length := hRval p hp
        have hl := decLet_at (w := w) (i := p₁) (p := p) hp₁ hple
        rw [Prod.mk.injEq]
        constructor
        · rw [Prod.mk.injEq]
          refine ⟨?_, ?_⟩
          · rw [hl.1]; simp [padLet]
          · rw [hl.2]; simp [padLet]
        · rw [isMarkE_at hp₁ hple]
          refine List.cons_eq_cons.mpr ⟨by simp [eq_comm], ?_⟩
          refine List.map_congr_left ?_
          intro q _
          simp only [decide_eq_decide, gp]
          omega

/-- The view of the encoded stack decodes to the view of the stack, in the form in which the
simulating machine uses it. -/
lemma decView_encSt {w : List A} {st : List ℕ} (hval : ∀ p ∈ st, p ≤ w.length) :
    decView (decide (2 ≤ st.length)) (ctxSt w st) (viewOf (sqOf w) (encStack w st))
      = viewOf w st := by
  by_cases h : 2 ≤ st.length
  · rw [ctxSt, if_pos h]
    exact decView_encStack hval
  · rw [ctxSt, if_neg h, decide_eq_false h, decView, if_neg (by simp)]
    have := decView_encStack (w := w) (st := st) hval
    rw [decide_eq_false h, decView, if_neg (by simp)] at this
    exact this

end PebSq

end Lax194892Proofs.Transducers
