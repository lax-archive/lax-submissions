/- Post-composition of a streaming string transducer with a *flip-flop* Mealy machine (a step of the
"regular to sst" half of Theorem `theorem:sst-two-way-equivalence` of *Transducers*, M. Bojańczyk).

In a flip-flop machine every letter either keeps the state or resets it to a
fixed one.  The content of a register is therefore split into its part up to and
including the first reset letter -- whose image depends on the state in which it
is entered, and is kept in one register `X_q` for every state `q` -- and the
remaining part, whose image does not depend on that state and is kept in a
single register `X_right`.  The state of the new sst remembers, for every
register, the state of the machine after the first and after the last reset
letter of its content.
-/
import Lax765601Proofs.Source.PartA.MealyBasic
import Lax916827Proofs.Source.PartC.SSTComp
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

variable {A B C : Type}

namespace MealyFFSST

open scoped Classical

variable {Q X : Type} (M : Mealy B C Q)

/-! ### Splitting a string at its first reset letter -/

/-- A letter is a *reset* letter if it does not keep the state. -/
def IsReset (b : B) : Prop := M.letterTrans b ≠ id

/-- The part of a string up to and including its first reset letter (the whole
string if there is none). -/
noncomputable def leftPart : List B → List B
  | [] => []
  | b :: v => if IsReset M b then [b] else b :: leftPart v

/-- The part of a string after its first reset letter (empty if there is
none). -/
noncomputable def rightPart : List B → List B
  | [] => []
  | b :: v => if IsReset M b then v else rightPart v

/-- A string contains a reset letter. -/
def HasReset (v : List B) : Prop := ∃ b ∈ v, IsReset M b

variable {M}

@[simp] lemma leftPart_nil : leftPart M ([] : List B) = [] := rfl
@[simp] lemma rightPart_nil : rightPart M ([] : List B) = [] := rfl

lemma leftPart_cons_reset {b : B} (h : IsReset M b) (v : List B) :
    leftPart M (b :: v) = [b] := by simp [leftPart, h]

lemma leftPart_cons_not {b : B} (h : ¬ IsReset M b) (v : List B) :
    leftPart M (b :: v) = b :: leftPart M v := by simp [leftPart, h]

lemma rightPart_cons_reset {b : B} (h : IsReset M b) (v : List B) :
    rightPart M (b :: v) = v := by simp [rightPart, h]

lemma rightPart_cons_not {b : B} (h : ¬ IsReset M b) (v : List B) :
    rightPart M (b :: v) = rightPart M v := by simp [rightPart, h]

@[simp] lemma hasReset_nil : ¬ HasReset M ([] : List B) := by simp [HasReset]

lemma hasReset_cons {b : B} {v : List B} :
    HasReset M (b :: v) ↔ IsReset M b ∨ HasReset M v := by
  simp [HasReset, or_and_right, exists_or]

lemma leftPart_append_rightPart (v : List B) : leftPart M v ++ rightPart M v = v := by
  induction v with
  | nil => rfl
  | cons b v ih =>
      by_cases h : IsReset M b
      · simp [leftPart_cons_reset h, rightPart_cons_reset h]
      · simp [leftPart_cons_not h, rightPart_cons_not h, ih]

lemma trans_eq_id_of_not_hasReset {v : List B} (h : ¬ HasReset M v) : M.trans v = id := by
  induction v with
  | nil => rfl
  | cons b v ih =>
      rw [hasReset_cons, not_or] at h
      have hb : M.letterTrans b = id := by
        by_contra hb
        exact h.1 hb
      funext q
      rw [M.trans_cons, ih h.2]
      simp [hb]

lemma leftPart_of_not_hasReset {v : List B} (h : ¬ HasReset M v) : leftPart M v = v := by
  induction v with
  | nil => rfl
  | cons b v ih =>
      rw [hasReset_cons, not_or] at h
      rw [leftPart_cons_not h.1, ih h.2]

lemma rightPart_of_not_hasReset {v : List B} (h : ¬ HasReset M v) : rightPart M v = [] := by
  induction v with
  | nil => rfl
  | cons b v ih =>
      rw [hasReset_cons, not_or] at h
      rw [rightPart_cons_not h.1, ih h.2]

/-- The state of the machine after the first reset letter of a string; if there
is no reset letter, this is the image of the initial state, which is not used. -/
noncomputable def entry (M : Mealy B C Q) (v : List B) : Q := M.trans (leftPart M v) M.init

/-- The state of the machine after the whole string, started in the initial
state; for a string with a reset letter this does not depend on the starting
state. -/
noncomputable def exitS (M : Mealy B C Q) (v : List B) : Q := M.trans v M.init

lemma letterTrans_eq_id_of_not_reset {b : B} (h : ¬ IsReset M b) : M.letterTrans b = id := by
  by_contra hb
  exact h hb

lemma entry_cons_not {b : B} (h : ¬ IsReset M b) (v : List B) : entry M (b :: v) = entry M v := by
  rw [entry, leftPart_cons_not h, M.trans_cons, letterTrans_eq_id_of_not_reset h]
  rfl

/-- For a flip-flop machine, the state after the part up to the first reset
letter does not depend on the starting state. -/
lemma trans_leftPart_const (hM : M.FlipFlop) {v : List B} (h : HasReset M v) (q : Q) :
    M.trans (leftPart M v) q = entry M v := by
  induction v with
  | nil => exact absurd h (by simp)
  | cons b v ih =>
      by_cases hb : IsReset M b
      · rcases hM b with h1 | ⟨q₀, hq₀⟩
        · exact absurd h1 hb
        · rw [leftPart_cons_reset hb, entry, leftPart_cons_reset hb]
          show M.trans [b] q = M.trans [b] M.init
          show M.letterTrans b q = M.letterTrans b M.init
          rw [hq₀, hq₀]
      · rw [hasReset_cons] at h
        have hv : HasReset M v := h.resolve_left hb
        rw [leftPart_cons_not hb, M.trans_cons, letterTrans_eq_id_of_not_reset hb,
          entry_cons_not hb]
        exact ih hv

lemma trans_const (hM : M.FlipFlop) {v : List B} (h : HasReset M v) (q : Q) :
    M.trans v q = exitS M v := by
  have hsplit : v = leftPart M v ++ rightPart M v := (leftPart_append_rightPart v).symm
  calc M.trans v q = M.trans (rightPart M v) (M.trans (leftPart M v) q) := by
        conv_lhs => rw [hsplit]
        rw [M.trans_append]
    _ = M.trans (rightPart M v) (entry M v) := by rw [trans_leftPart_const hM h]
    _ = M.trans v M.init := by
        conv_rhs => rw [hsplit]
        rw [M.trans_append, trans_leftPart_const hM h]

/-! ### The splitting of a concatenation -/

lemma leftPart_append_of_not {v : List B} (h : ¬ HasReset M v) (w : List B) :
    leftPart M (v ++ w) = v ++ leftPart M w := by
  induction v with
  | nil => rfl
  | cons b v ih =>
      rw [hasReset_cons, not_or] at h
      rw [List.cons_append, leftPart_cons_not h.1, ih h.2, List.cons_append]

lemma rightPart_append_of_not {v : List B} (h : ¬ HasReset M v) (w : List B) :
    rightPart M (v ++ w) = rightPart M w := by
  induction v with
  | nil => rfl
  | cons b v ih =>
      rw [hasReset_cons, not_or] at h
      rw [List.cons_append, rightPart_cons_not h.1, ih h.2]

lemma hasReset_append (v w : List B) : HasReset M (v ++ w) ↔ HasReset M v ∨ HasReset M w := by
  simp [HasReset, or_and_right, exists_or]

lemma leftPart_append_of_has {v : List B} (h : HasReset M v) (w : List B) :
    leftPart M (v ++ w) = leftPart M v := by
  induction v with
  | nil => exact absurd h (by simp)
  | cons b v ih =>
      by_cases hb : IsReset M b
      · rw [List.cons_append, leftPart_cons_reset hb, leftPart_cons_reset hb]
      · rw [hasReset_cons] at h
        rw [List.cons_append, leftPart_cons_not hb, leftPart_cons_not hb,
          ih (h.resolve_left hb)]

lemma rightPart_append_of_has {v : List B} (h : HasReset M v) (w : List B) :
    rightPart M (v ++ w) = rightPart M v ++ w := by
  induction v with
  | nil => exact absurd h (by simp)
  | cons b v ih =>
      by_cases hb : IsReset M b
      · rw [List.cons_append, rightPart_cons_reset hb, rightPart_cons_reset hb]
      · rw [hasReset_cons] at h
        rw [List.cons_append, rightPart_cons_not hb, rightPart_cons_not hb,
          ih (h.resolve_left hb)]

lemma entry_append_of_not {v : List B} (h : ¬ HasReset M v) (w : List B) :
    entry M (v ++ w) = entry M w := by
  rw [entry, leftPart_append_of_not h, M.trans_append, trans_eq_id_of_not_hasReset h]
  rfl

lemma entry_append_of_has {v : List B} (h : HasReset M v) (w : List B) :
    entry M (v ++ w) = entry M v := by
  rw [entry, leftPart_append_of_has h, entry]

lemma exitS_append_of_not {v : List B} (h : ¬ HasReset M v) (w : List B) :
    exitS M (v ++ w) = exitS M w := by
  rw [exitS, M.trans_append, trans_eq_id_of_not_hasReset h, exitS]
  rfl

lemma exitS_append (v w : List B) : exitS M (v ++ w) = M.trans w (exitS M v) := by
  rw [exitS, M.trans_append, exitS]

lemma trans_rightPart_entry (hM : M.FlipFlop) {v : List B} (h : HasReset M v) :
    M.trans (rightPart M v) (entry M v) = exitS M v := by
  conv_rhs => rw [exitS, show v = leftPart M v ++ rightPart M v from
    (leftPart_append_rightPart v).symm]
  rw [M.trans_append, trans_leftPart_const hM h]

/-! ### The symbolic register updates -/

variable (M)

/-- The state of the machine after the content of the register `y`, when the
content is entered in the state `p` and the information kept about `y` is
`info y`. -/
def nextSt (info : X → Option (Q × Q)) (p : Q) (y : X) : Q := (info y).elim p Prod.snd

/-- The image of a string over `X + B` that is read from a *known* state `p`;
this is used after the first reset letter, where the state of the machine no
longer depends on the state in which the whole string is entered.  A register
`y` contributes both of its parts. -/
noncomputable def walkStr (info : X → Option (Q × Q)) :
    Q → List (X ⊕ B) → List ((X × Option Q) ⊕ C)
  | _, [] => []
  | p, Sum.inr b :: s => Sum.inr (M.step p b).2 :: walkStr info ((M.step p b).1) s
  | p, Sum.inl y :: s =>
      Sum.inl (y, some p) :: Sum.inl (y, none) :: walkStr info (nextSt info p y) s

/-- The state of the machine after a string over `X + B` read from the state
`p`. -/
noncomputable def walkState (info : X → Option (Q × Q)) : Q → List (X ⊕ B) → Q
  | p, [] => p
  | p, Sum.inr b :: s => walkState info ((M.step p b).1) s
  | p, Sum.inl y :: s => walkState info (nextSt info p y) s

/-- The image of the part of a string over `X + B` up to and including its first
reset letter, read from the state `q`. -/
noncomputable def leftStr (info : X → Option (Q × Q)) (q : Q) :
    List (X ⊕ B) → List ((X × Option Q) ⊕ C)
  | [] => []
  | Sum.inr b :: s =>
      if IsReset M b then [Sum.inr (M.step q b).2]
      else Sum.inr (M.step q b).2 :: leftStr info q s
  | Sum.inl y :: s =>
      match info y with
      | none => Sum.inl (y, some q) :: leftStr info q s
      | some _ => [Sum.inl (y, some q)]

/-- The image of the part of a string over `X + B` after its first reset
letter. -/
noncomputable def rightStr (info : X → Option (Q × Q)) :
    List (X ⊕ B) → List ((X × Option Q) ⊕ C)
  | [] => []
  | Sum.inr b :: s =>
      if IsReset M b then walkStr M info (M.letterTrans b M.init) s
      else rightStr info s
  | Sum.inl y :: s =>
      match info y with
      | none => rightStr info s
      | some e => Sum.inl (y, none) :: walkStr M info e.2 s

/-- The new value of the information kept about a register: the state after the
first reset letter and the state after the whole content, or `none` if there is
no reset letter. -/
noncomputable def newInfo (info : X → Option (Q × Q)) :
    List (X ⊕ B) → Option (Q × Q)
  | [] => none
  | Sum.inr b :: s =>
      if IsReset M b then
        some (M.letterTrans b M.init, walkState M info (M.letterTrans b M.init) s)
      else newInfo info s
  | Sum.inl y :: s =>
      match info y with
      | none => newInfo info s
      | some e => some (e.1, walkState M info e.2 s)

variable {M}

/-! #### The defining equations -/

section Equations

variable {info : X → Option (Q × Q)} {y : X} {b : B} {p q : Q} {s : List (X ⊕ B)}

@[simp] lemma walkStr_nil (info : X → Option (Q × Q)) (p : Q) :
    walkStr M info p ([] : List (X ⊕ B)) = [] := rfl

lemma walkStr_cons_inr :
    walkStr M info p (Sum.inr b :: s) =
      Sum.inr (M.step p b).2 :: walkStr M info ((M.step p b).1) s := rfl

lemma walkStr_cons_inl :
    walkStr M info p (Sum.inl y :: s) =
      Sum.inl (y, some p) :: Sum.inl (y, none) :: walkStr M info (nextSt info p y) s := rfl

@[simp] lemma walkState_nil (info : X → Option (Q × Q)) (p : Q) :
    walkState M info p ([] : List (X ⊕ B)) = p := rfl

lemma walkState_cons_inr :
    walkState M info p (Sum.inr b :: s) = walkState M info ((M.step p b).1) s := rfl

lemma walkState_cons_inl :
    walkState M info p (Sum.inl y :: s) = walkState M info (nextSt info p y) s := rfl

@[simp] lemma leftStr_nil (info : X → Option (Q × Q)) (q : Q) :
    leftStr M info q ([] : List (X ⊕ B)) = [] := rfl

lemma leftStr_cons_inr_reset (h : IsReset M b) :
    leftStr M info q (Sum.inr b :: s) = [Sum.inr (M.step q b).2] := by
  simp [leftStr, h]

lemma leftStr_cons_inr_not (h : ¬ IsReset M b) :
    leftStr M info q (Sum.inr b :: s) =
      Sum.inr (M.step q b).2 :: leftStr M info q s := by
  simp [leftStr, h]

lemma leftStr_cons_inl_none (h : info y = none) :
    leftStr M info q (Sum.inl y :: s) = Sum.inl (y, some q) :: leftStr M info q s := by
  simp [leftStr, h]

lemma leftStr_cons_inl_some {e : Q × Q} (h : info y = some e) :
    leftStr M info q (Sum.inl y :: s) = [Sum.inl (y, some q)] := by
  simp [leftStr, h]

@[simp] lemma rightStr_nil (info : X → Option (Q × Q)) :
    rightStr M info ([] : List (X ⊕ B)) = [] := rfl

lemma rightStr_cons_inr_reset (h : IsReset M b) :
    rightStr M info (Sum.inr b :: s) = walkStr M info (M.letterTrans b M.init) s := by
  simp [rightStr, h]

lemma rightStr_cons_inr_not (h : ¬ IsReset M b) :
    rightStr M info (Sum.inr b :: s) = rightStr M info s := by
  simp [rightStr, h]

lemma rightStr_cons_inl_none (h : info y = none) :
    rightStr M info (Sum.inl y :: s) = rightStr M info s := by
  simp [rightStr, h]

lemma rightStr_cons_inl_some {e : Q × Q} (h : info y = some e) :
    rightStr M info (Sum.inl y :: s) = Sum.inl (y, none) :: walkStr M info e.2 s := by
  simp [rightStr, h]

@[simp] lemma newInfo_nil (info : X → Option (Q × Q)) :
    newInfo M info ([] : List (X ⊕ B)) = none := rfl

lemma newInfo_cons_inr_reset (h : IsReset M b) :
    newInfo M info (Sum.inr b :: s) =
      some (M.letterTrans b M.init, walkState M info (M.letterTrans b M.init) s) := by
  simp [newInfo, h]

lemma newInfo_cons_inr_not (h : ¬ IsReset M b) :
    newInfo M info (Sum.inr b :: s) = newInfo M info s := by
  simp [newInfo, h]

lemma newInfo_cons_inl_none (h : info y = none) :
    newInfo M info (Sum.inl y :: s) = newInfo M info s := by
  simp [newInfo, h]

lemma newInfo_cons_inl_some {e : Q × Q} (h : info y = some e) :
    newInfo M info (Sum.inl y :: s) = some (e.1, walkState M info e.2 s) := by
  simp [newInfo, h]

lemma nextSt_none (h : info y = none) (p : Q) : nextSt info p y = p := by
  simp [nextSt, h]

lemma nextSt_some {e : Q × Q} (h : info y = some e) (p : Q) : nextSt info p y = e.2 := by
  simp [nextSt, h]

end Equations
/-! ### The semantics of the symbolic updates

Throughout this section the following data is fixed: the contents `η` of the
registers of the original sst, the contents `η'` of the registers of the new
sst, and the information `info` kept in the state of the new sst.  The three
hypotheses `hinfo`, `hL` and `hR` are the invariant of the construction. -/

section Semantics

variable {info : X → Option (Q × Q)} {η : X → List B} {η' : X × Option Q → List C}

/-- The image of a string splits as the image of its left part followed by the
image of its right part. -/
lemma run_split (hM : M.FlipFlop) (p : Q) (v : List B) :
    M.run p v = M.run p (leftPart M v) ++ M.run (entry M v) (rightPart M v) := by
  by_cases h : HasReset M v
  · conv_lhs => rw [show v = leftPart M v ++ rightPart M v from
      (leftPart_append_rightPart v).symm]
    rw [M.run_append, trans_leftPart_const hM h]
  · rw [leftPart_of_not_hasReset h, rightPart_of_not_hasReset h]
    simp

lemma not_hasReset_of_info_none
    (hinfo : ∀ x, info x =
      if HasReset M (η x) then some (entry M (η x), exitS M (η x)) else none)
    {y : X} (h : info y = none) : ¬ HasReset M (η y) := by
  rw [hinfo y] at h
  by_cases hy : HasReset M (η y)
  · rw [if_pos hy] at h; exact absurd h (by simp)
  · exact hy

lemma hasReset_of_info_some
    (hinfo : ∀ x, info x =
      if HasReset M (η x) then some (entry M (η x), exitS M (η x)) else none)
    {y : X} {e : Q × Q} (h : info y = some e) :
    HasReset M (η y) ∧ e = (entry M (η y), exitS M (η y)) := by
  rw [hinfo y] at h
  by_cases hy : HasReset M (η y)
  · rw [if_pos hy] at h
    exact ⟨hy, (Option.some_inj.1 h).symm⟩
  · rw [if_neg hy] at h; exact absurd h (by simp)

lemma nextSt_eq (hM : M.FlipFlop)
    (hinfo : ∀ x, info x =
      if HasReset M (η x) then some (entry M (η x), exitS M (η x)) else none)
    (p : Q) (y : X) : nextSt info p y = M.trans (η y) p := by
  cases h : info y with
  | none =>
      rw [nextSt_none h, trans_eq_id_of_not_hasReset (not_hasReset_of_info_none hinfo h)]
      rfl
  | some e =>
      obtain ⟨hy, rfl⟩ := hasReset_of_info_some hinfo h
      rw [nextSt_some h, trans_const hM hy]

/-- **(E)**  `walkState` computes the state transformation of the string. -/
lemma walkState_eq (hM : M.FlipFlop)
    (hinfo : ∀ x, info x =
      if HasReset M (η x) then some (entry M (η x), exitS M (η x)) else none)
    (p : Q) (s : List (X ⊕ B)) : walkState M info p s = M.trans (SST.subst η s) p := by
  induction s generalizing p with
  | nil => rfl
  | cons z s ih =>
      cases z with
      | inl y =>
          rw [walkState_cons_inl, ih, SST.subst_cons_inl, M.trans_append,
            nextSt_eq hM hinfo p y]
      | inr b =>
          rw [walkState_cons_inr, ih, SST.subst_cons_inr, M.trans_cons]
          rfl

/-- **(A)**  `walkStr` computes the image of the string read from a known
state. -/
lemma subst_walkStr (hM : M.FlipFlop)
    (hinfo : ∀ x, info x =
      if HasReset M (η x) then some (entry M (η x), exitS M (η x)) else none)
    (hL : ∀ x q, η' (x, some q) = M.run q (leftPart M (η x)))
    (hR : ∀ x, η' (x, none) = M.run (entry M (η x)) (rightPart M (η x)))
    (p : Q) (s : List (X ⊕ B)) :
    SST.subst η' (walkStr M info p s) = M.run p (SST.subst η s) := by
  induction s generalizing p with
  | nil => rfl
  | cons z s ih =>
      cases z with
      | inl y =>
          rw [walkStr_cons_inl, SST.subst_cons_inl, SST.subst_cons_inl, ih, hL, hR,
            SST.subst_cons_inl, M.run_append, nextSt_eq hM hinfo p y,
            run_split hM p (η y), List.append_assoc]
      | inr b =>
          rw [walkStr_cons_inr, SST.subst_cons_inr, ih, SST.subst_cons_inr, M.run_cons]

/-- **(B)**  `leftStr` computes the image of the left part of the string. -/
lemma subst_leftStr
    (hinfo : ∀ x, info x =
      if HasReset M (η x) then some (entry M (η x), exitS M (η x)) else none)
    (hL : ∀ x q, η' (x, some q) = M.run q (leftPart M (η x)))
    (q : Q) (s : List (X ⊕ B)) :
    SST.subst η' (leftStr M info q s) = M.run q (leftPart M (SST.subst η s)) := by
  induction s with
  | nil => rfl
  | cons z s ih =>
      cases z with
      | inl y =>
          cases h : info y with
          | none =>
              have hy := not_hasReset_of_info_none hinfo h
              rw [leftStr_cons_inl_none h, SST.subst_cons_inl, ih, hL, SST.subst_cons_inl,
                leftPart_append_of_not hy, M.run_append, trans_eq_id_of_not_hasReset hy,
                leftPart_of_not_hasReset hy]
              rfl
          | some e =>
              obtain ⟨hy, rfl⟩ := hasReset_of_info_some hinfo h
              rw [leftStr_cons_inl_some h, SST.subst_cons_inl, SST.subst_nil,
                List.append_nil, hL, SST.subst_cons_inl, leftPart_append_of_has hy]
      | inr b =>
          by_cases hb : IsReset M b
          · rw [leftStr_cons_inr_reset hb, SST.subst_cons_inr, SST.subst_nil,
              SST.subst_cons_inr, leftPart_cons_reset hb]
            rfl
          · have hstep : (M.step q b).1 = q := by
              show M.letterTrans b q = q
              rw [letterTrans_eq_id_of_not_reset hb]; rfl
            rw [leftStr_cons_inr_not hb, SST.subst_cons_inr, ih, SST.subst_cons_inr,
              leftPart_cons_not hb, M.run_cons, hstep]

/-- **(C)**  `rightStr` computes the image of the right part of the string. -/
lemma subst_rightStr (hM : M.FlipFlop)
    (hinfo : ∀ x, info x =
      if HasReset M (η x) then some (entry M (η x), exitS M (η x)) else none)
    (hL : ∀ x q, η' (x, some q) = M.run q (leftPart M (η x)))
    (hR : ∀ x, η' (x, none) = M.run (entry M (η x)) (rightPart M (η x)))
    (s : List (X ⊕ B)) :
    SST.subst η' (rightStr M info s)
      = M.run (entry M (SST.subst η s)) (rightPart M (SST.subst η s)) := by
  induction s with
  | nil => rfl
  | cons z s ih =>
      cases z with
      | inl y =>
          cases h : info y with
          | none =>
              have hy := not_hasReset_of_info_none hinfo h
              rw [rightStr_cons_inl_none h, ih, SST.subst_cons_inl,
                entry_append_of_not hy, rightPart_append_of_not hy]
          | some e =>
              obtain ⟨hy, rfl⟩ := hasReset_of_info_some hinfo h
              rw [rightStr_cons_inl_some h, SST.subst_cons_inl, hR,
                subst_walkStr hM hinfo hL hR, SST.subst_cons_inl,
                entry_append_of_has hy, rightPart_append_of_has hy, M.run_append,
                trans_rightPart_entry hM hy]
      | inr b =>
          by_cases hb : IsReset M b
          · rw [rightStr_cons_inr_reset hb, subst_walkStr hM hinfo hL hR,
              SST.subst_cons_inr, rightPart_cons_reset hb, entry, leftPart_cons_reset hb]
            rfl
          · rw [rightStr_cons_inr_not hb, ih, SST.subst_cons_inr, rightPart_cons_not hb,
              entry_cons_not hb]

/-- **(D)**  `newInfo` computes the information about the new content. -/
lemma newInfo_eq (hM : M.FlipFlop)
    (hinfo : ∀ x, info x =
      if HasReset M (η x) then some (entry M (η x), exitS M (η x)) else none)
    (s : List (X ⊕ B)) :
    newInfo M info s = if HasReset M (SST.subst η s) then
      some (entry M (SST.subst η s), exitS M (SST.subst η s)) else none := by
  induction s with
  | nil => rw [newInfo_nil, SST.subst_nil, if_neg hasReset_nil]
  | cons z s ih =>
      cases z with
      | inl y =>
          cases h : info y with
          | none =>
              have hy := not_hasReset_of_info_none hinfo h
              rw [newInfo_cons_inl_none h, ih, SST.subst_cons_inl]
              by_cases hv : HasReset M (SST.subst η s)
              · rw [if_pos hv, if_pos ((hasReset_append _ _).2 (Or.inr hv)),
                  entry_append_of_not hy, exitS_append_of_not hy]
              · rw [if_neg hv, if_neg (by rw [hasReset_append]; tauto)]
          | some e =>
              obtain ⟨hy, rfl⟩ := hasReset_of_info_some hinfo h
              rw [newInfo_cons_inl_some h, SST.subst_cons_inl,
                if_pos ((hasReset_append _ _).2 (Or.inl hy)), entry_append_of_has hy,
                exitS_append, walkState_eq hM hinfo]
      | inr b =>
          by_cases hb : IsReset M b
          · have hres : HasReset M (b :: SST.subst η s) := hasReset_cons.2 (Or.inl hb)
            rw [newInfo_cons_inr_reset hb, SST.subst_cons_inr, if_pos hres,
              walkState_eq hM hinfo]
            have hentry : entry M (b :: SST.subst η s) = M.letterTrans b M.init := by
              rw [entry, leftPart_cons_reset hb]; rfl
            have hexit : exitS M (b :: SST.subst η s)
                = M.trans (SST.subst η s) (M.letterTrans b M.init) := by
              rw [exitS, M.trans_cons]
            rw [hentry, hexit]
          · have hentry : entry M (b :: SST.subst η s) = entry M (SST.subst η s) :=
              entry_cons_not hb _
            have hexit : exitS M (b :: SST.subst η s) = exitS M (SST.subst η s) := by
              rw [exitS, M.trans_cons, letterTrans_eq_id_of_not_reset hb]
              rfl
            rw [newInfo_cons_inr_not hb, ih, SST.subst_cons_inr, hentry, hexit]
            by_cases hv : HasReset M (SST.subst η s)
            · rw [if_pos hv, if_pos (hasReset_cons.2 (Or.inr hv))]
            · rw [if_neg hv, if_neg (by rw [hasReset_cons]; tauto)]

end Semantics

/-! ### The copyless restriction -/

section Copyless

variable {info : X → Option (Q × Q)}

lemma mem_regsOf_walkStr {p : Q} {s : List (X ⊕ B)} {z : X × Option Q}
    (h : z ∈ regsOf (walkStr M info p s)) : z.1 ∈ regsOf s := by
  induction s generalizing p with
  | nil => simp at h
  | cons w s ih =>
      cases w with
      | inl y =>
          rw [walkStr_cons_inl, regsOf.cons_inl, regsOf.cons_inl, List.mem_cons,
            List.mem_cons] at h
          rcases h with rfl | rfl | h
          · simp
          · simp
          · simpa using Or.inr (ih h)
      | inr b =>
          rw [walkStr_cons_inr, regsOf.cons_inr] at h
          simpa using ih h

lemma mem_regsOf_leftStr {q : Q} {s : List (X ⊕ B)} {z : X × Option Q}
    (h : z ∈ regsOf (leftStr M info q s)) : z.1 ∈ regsOf s ∧ z.2 = some q := by
  induction s with
  | nil => simp at h
  | cons w s ih =>
      cases w with
      | inl y =>
          cases hy : info y with
          | none =>
              rw [leftStr_cons_inl_none hy, regsOf.cons_inl, List.mem_cons] at h
              rcases h with rfl | h
              · exact ⟨by simp, rfl⟩
              · exact ⟨by simp [(ih h).1], (ih h).2⟩
          | some e =>
              rw [leftStr_cons_inl_some hy] at h
              simp only [regsOf.cons_inl, regsOf.nil, List.mem_cons, List.not_mem_nil,
                or_false] at h
              subst h
              exact ⟨by simp, rfl⟩
      | inr b =>
          by_cases hb : IsReset M b
          · rw [leftStr_cons_inr_reset hb] at h
            simp at h
          · rw [leftStr_cons_inr_not hb, regsOf.cons_inr] at h
            exact ⟨by simp [(ih h).1], (ih h).2⟩

lemma mem_regsOf_rightStr {s : List (X ⊕ B)} {z : X × Option Q}
    (h : z ∈ regsOf (rightStr M info s)) : z.1 ∈ regsOf s := by
  induction s with
  | nil => simp at h
  | cons w s ih =>
      cases w with
      | inl y =>
          cases hy : info y with
          | none =>
              rw [rightStr_cons_inl_none hy] at h
              simpa using Or.inr (ih h)
          | some e =>
              rw [rightStr_cons_inl_some hy, regsOf.cons_inl, List.mem_cons] at h
              rcases h with rfl | h
              · simp
              · simpa using Or.inr (mem_regsOf_walkStr h)
      | inr b =>
          by_cases hb : IsReset M b
          · rw [rightStr_cons_inr_reset hb] at h
            simpa using mem_regsOf_walkStr h
          · rw [rightStr_cons_inr_not hb] at h
            simpa using ih h

lemma nodup_regsOf_walkStr (p : Q) {s : List (X ⊕ B)} (hs : (regsOf s).Nodup) :
    (regsOf (walkStr M info p s)).Nodup := by
  induction s generalizing p with
  | nil => simp
  | cons w s ih =>
      cases w with
      | inl y =>
          rw [regsOf.cons_inl, List.nodup_cons] at hs
          rw [walkStr_cons_inl, regsOf.cons_inl, regsOf.cons_inl]
          refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, ih _ hs.2⟩⟩
          · intro hmem
            rcases List.mem_cons.1 hmem with hEq | hmem'
            · exact absurd hEq (by simp)
            · exact hs.1 (mem_regsOf_walkStr hmem')
          · intro hmem
            exact hs.1 (mem_regsOf_walkStr hmem)
      | inr b =>
          rw [regsOf.cons_inr] at hs
          rw [walkStr_cons_inr, regsOf.cons_inr]
          exact ih _ hs

/-- The registers used by the two parts of a copyless update are pairwise
distinct: this is what makes the new update copyless. -/
lemma nodup_regsOf_left_right (q : Q) {s : List (X ⊕ B)} (hs : (regsOf s).Nodup) :
    (regsOf (leftStr M info q s) ++ regsOf (rightStr M info s)).Nodup := by
  induction s with
  | nil => simp
  | cons w s ih =>
      cases w with
      | inl y =>
          rw [regsOf.cons_inl, List.nodup_cons] at hs
          obtain ⟨hy, hnd⟩ := hs
          cases hyy : info y with
          | none =>
              rw [leftStr_cons_inl_none hyy, rightStr_cons_inl_none hyy, regsOf.cons_inl,
                List.cons_append]
              refine List.nodup_cons.2 ⟨?_, ih hnd⟩
              intro hmem
              rcases List.mem_append.1 hmem with hm | hm
              · exact hy (mem_regsOf_leftStr hm).1
              · exact hy (mem_regsOf_rightStr hm)
          | some e =>
              rw [leftStr_cons_inl_some hyy, rightStr_cons_inl_some hyy]
              simp only [regsOf.cons_inl, regsOf.nil, List.singleton_append]
              refine List.nodup_cons.2 ⟨?_, List.nodup_cons.2 ⟨?_, nodup_regsOf_walkStr _ hnd⟩⟩
              · intro hmem
                rcases List.mem_cons.1 hmem with hEq | hm
                · exact absurd hEq (by simp)
                · exact hy (mem_regsOf_walkStr hm)
              · intro hmem
                exact hy (mem_regsOf_walkStr hmem)
      | inr b =>
          rw [regsOf.cons_inr] at hs
          by_cases hb : IsReset M b
          · rw [leftStr_cons_inr_reset hb, rightStr_cons_inr_reset hb]
            simpa using nodup_regsOf_walkStr _ hs
          · rw [leftStr_cons_inr_not hb, rightStr_cons_inr_not hb, regsOf.cons_inr]
            exact ih hs

end Copyless

/-! ### The new sst -/

variable (M)

/-- The register update of the new sst: the register `(x, some q)` gets the
image of the left part of the new content of `x`, read from `q`, and the
register `(x, none)` gets the image of its right part. -/
noncomputable def ffUpdate (info : X → Option (Q × Q)) (u : X → List (X ⊕ B)) :
    X × Option Q → List ((X × Option Q) ⊕ C)
  | (x, some q) => leftStr M info q (u x)
  | (x, none) => rightStr M info (u x)

@[simp] lemma ffUpdate_some (info : X → Option (Q × Q)) (u : X → List (X ⊕ B))
    (x : X) (q : Q) : ffUpdate M info u (x, some q) = leftStr M info q (u x) := rfl

@[simp] lemma ffUpdate_none (info : X → Option (Q × Q)) (u : X → List (X ⊕ B))
    (x : X) : ffUpdate M info u (x, none) = rightStr M info (u x) := rfl

/-- The sst computing `M.eval ∘ T.eval` for a flip-flop Mealy machine `M`: its
registers are the pairs `(x, some q)`, holding the image of the left part of the
content of `x` read from `q`, and the pairs `(x, none)`, holding the image of its
right part; its states remember, for every register of `T`, whether its content
contains a reset letter and, if so, the states of `M` after the first reset
letter and after the whole content. -/
noncomputable def ffComp {QT : Type} [Fintype X] [Fintype Q] (T : SST A B QT X) :
    SST A C (QT × (X → Option (Q × Q))) (X × Option Q) where
  init := (T.init, fun _ => none)
  step := fun p a =>
    (((T.step p.1 a).1, fun x => newInfo M p.2 ((T.step p.1 a).2 x)),
      ffUpdate M p.2 (T.step p.1 a).2)
  step_copyless := by
    rintro ⟨qT, info⟩ a
    show Copyless (ffUpdate M info (T.step qT a).2)
    have h := T.step_copyless qT a
    rw [copyless_iff] at h ⊢
    have hmem : ∀ (x : X) (o : Option Q) (z : X × Option Q),
        z ∈ regsOf (ffUpdate M info (T.step qT a).2 (x, o)) → z.1 ∈ regsOf ((T.step qT a).2 x) := by
      rintro x (_ | q) z hz
      · rw [ffUpdate_none] at hz
        exact mem_regsOf_rightStr hz
      · rw [ffUpdate_some] at hz
        exact (mem_regsOf_leftStr hz).1
    constructor
    · rintro ⟨x, (_ | q)⟩
      · rw [ffUpdate_none]
        exact (nodup_regsOf_left_right (info := info) M.init (h.1 x)).of_append_right
      · rw [ffUpdate_some]
        exact (nodup_regsOf_left_right (info := info) q (h.1 x)).of_append_left
    · rintro ⟨x, o⟩ ⟨x', o'⟩ hne z hz hz'
      by_cases hxx : x = x'
      · subst hxx
        have hoo : o ≠ o' := fun hh => hne (by rw [hh])
        cases o with
        | none =>
            cases o' with
            | none => exact hoo rfl
            | some q' =>
                rw [ffUpdate_none] at hz
                rw [ffUpdate_some] at hz'
                exact (List.nodup_append.1
                  (nodup_regsOf_left_right (info := info) q' (h.1 x))).2.2 z hz' z hz rfl
        | some q =>
            cases o' with
            | none =>
                rw [ffUpdate_some] at hz
                rw [ffUpdate_none] at hz'
                exact (List.nodup_append.1
                  (nodup_regsOf_left_right (info := info) q (h.1 x))).2.2 z hz z hz' rfl
            | some q' =>
                rw [ffUpdate_some] at hz
                rw [ffUpdate_some] at hz'
                have h1 := (mem_regsOf_leftStr hz).2
                have h2 := (mem_regsOf_leftStr hz').2
                exact hoo (h1.symm.trans h2)
      · exact h.2 x x' hxx z.1 (hmem _ _ _ hz) (hmem _ _ _ hz')
  final := fun p => walkStr M p.2 M.init (T.final p.1)

lemma ffComp_eval {QT : Type} [Fintype X] [Fintype Q] (T : SST A B QT X)
    (hM : M.FlipFlop) (w : List A) : (ffComp M T).eval w = M.eval (T.eval w) := by
  refine SST.eval_of_sim (T := T) (T' := ffComp M T) (p := M.eval)
    (fun c c' => c'.1.1 = c.1 ∧
      (∀ x, c'.1.2 x =
        if HasReset M (c.2 x) then some (entry M (c.2 x), exitS M (c.2 x)) else none) ∧
      (∀ x q, c'.2 (x, some q) = M.run q (leftPart M (c.2 x))) ∧
      (∀ x, c'.2 (x, none) = M.run (entry M (c.2 x)) (rightPart M (c.2 x))))
    ⟨rfl, fun x => by rw [if_neg hasReset_nil]; rfl, fun _ _ => rfl, fun _ => rfl⟩ ?_ ?_ w
  · rintro ⟨qT, η⟩ ⟨⟨qT', info⟩, η'⟩ a ⟨hq, hinfo, hL, hR⟩
    cases hq
    refine ⟨rfl, fun x => ?_, fun x q => ?_, fun x => ?_⟩
    · exact newInfo_eq hM hinfo _
    · exact subst_leftStr hinfo hL q _
    · exact subst_rightStr hM hinfo hL hR _
  · rintro ⟨qT, η⟩ ⟨⟨qT', info⟩, η'⟩ ⟨hq, hinfo, hL, hR⟩
    cases hq
    exact subst_walkStr hM hinfo hL hR M.init (T.final qT)

end MealyFFSST

/-- **Post-composition with a flip-flop Mealy machine.**  In a flip-flop machine
every letter either keeps the state or resets it to a fixed one, so the image of
the content of a register depends on the state in which it is entered only up to
and including its first reset letter.  Keeping that part in one register for
every state of the machine, and the rest in a single register, gives a copyless
sst. -/
theorem isSST_comp_flipFlopMealy {Q : Type} [Finite Q] {f : List A → List B}
    (hf : IsSST f) (M : Mealy B C Q) (hM : M.FlipFlop) :
    IsSST (fun w => M.eval (f w)) := by
  obtain ⟨QT, X, hQT, hX, T, rfl⟩ := hf
  haveI := hQT
  haveI : Fintype Q := Fintype.ofFinite Q
  exact ⟨QT × (X → Option (Q × Q)), X × Option Q, inferInstance, inferInstance,
    MealyFFSST.ffComp M T, funext fun w => MealyFFSST.ffComp_eval M T hM w⟩

end Lax916827Proofs.Transducers
