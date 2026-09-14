/-
Part D: adding one innermost loop to the enumeration of the tuples of positions.

This file contains the streaming string transducer that turns the marked square of the
enumeration `enum k L w` into the enumeration `enum (k+1) (L ++ [(d, x)]) w`, and the proof that
it does so.  Together with the fact that marked squaring is a prime polyregular function and that
a streaming string transducer computes a regular function (Theorem
`theorem:sst-two-way-equivalence`), this shows that the enumeration of the tuples visited by a
nest of for-loops is polyregular.

The transducer reads the marked square copy by copy; the copies are separated by the end marker
`Ann.eos`, which occurs once at the end of every copy.  Inside a copy it keeps exactly one block:
the one in which the underlining stops.  A block is kept when the letters of the block that are
underlined form a nonempty proper prefix of it (the state `BS.trans`), or when all the letters of
the block are underlined but the separator that follows it is not (the state `BS.allL`); the
second case is the last copy of the group of copies that belong to the same tuple, and it is
where the group is flushed into the output.
-/
import Lax194892Proofs.Source.PartD.PolyEnum
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace PolyEnum

/-! ## The transducer -/

/-- The pattern of underlinings seen in the block that is being read. -/
inductive BS : Type
  /-- Nothing read yet. -/
  | empty : BS
  /-- Only underlined letters. -/
  | allL : BS
  /-- Underlined letters, then letters that are not underlined. -/
  | trans : BS
  /-- Only letters that are not underlined. -/
  | allR : BS
  deriving DecidableEq

/-- Reading one more letter, underlined or not. -/
def BS.advance : BS → Bool → BS
  | BS.empty, true => BS.allL
  | BS.empty, false => BS.allR
  | BS.allL, true => BS.allL
  | BS.allL, false => BS.trans
  | BS.trans, _ => BS.trans
  | BS.allR, _ => BS.allR

/-- The registers of the transducer. -/
inductive Reg : Type
  /-- The output produced so far. -/
  | res : Reg
  /-- The copies of the block currently being expanded, in the order prescribed by the
  direction of the new loop. -/
  | grp : Reg
  /-- The block currently being read. -/
  | cur : Reg
  deriving DecidableEq, Fintype

variable {A : Type} {k : ℕ}

/-- A register valuation, written out. -/
def regs (r g c : List (Ann A (k + 1))) : Reg → List (Ann A (k + 1))
  | Reg.res => r
  | Reg.grp => g
  | Reg.cur => c

@[simp] lemma regs_res (r g c : List (Ann A (k + 1))) : regs r g c Reg.res = r := rfl
@[simp] lemma regs_grp (r g c : List (Ann A (k + 1))) : regs r g c Reg.grp = g := rfl
@[simp] lemma regs_cur (r g c : List (Ann A (k + 1))) : regs r g c Reg.cur = c := rfl

/-- The group of copies extended by the block that has just been read, in the order prescribed
by the direction `d` of the new loop. -/
def blkPush (d : Bool) : List (Reg ⊕ Ann A (k + 1)) :=
  if d then [Sum.inl Reg.grp, Sum.inl Reg.cur, Sum.inr Ann.sep]
  else [Sum.inl Reg.cur, Sum.inr Ann.sep, Sum.inl Reg.grp]

/-- The concatenation `g` with a complete copy `blk` (separator included), in the order
prescribed by `d`. -/
def pushBlk (d : Bool) (g blk : List (Ann A (k + 1))) : List (Ann A (k + 1)) :=
  if d then g ++ blk else blk ++ g

/-- The concatenation `g` with the block `c`, in the order prescribed by `d`. -/
def pushList (d : Bool) (g c : List (Ann A (k + 1))) : List (Ann A (k + 1)) :=
  if d then g ++ (c ++ [Ann.sep]) else (c ++ [Ann.sep]) ++ g

lemma pushList_eq (d : Bool) (g c : List (Ann A (k + 1))) :
    pushList d g c = pushBlk d g (c ++ [Ann.sep]) := rfl

/-- The register update of the transducer on one letter. -/
def stepUpd (d : Bool) (q : BS) : Ann A k ⊕ Ann A k → Reg → List (Reg ⊕ Ann A (k + 1))
  | Sum.inl (Ann.letter a m) => fun r =>
      match r with
      | Reg.cur => [Sum.inl Reg.cur, Sum.inr (Ann.letter a (Fin.snoc m true))]
      | Reg.res => [Sum.inl Reg.res]
      | Reg.grp => [Sum.inl Reg.grp]
  | Sum.inr (Ann.letter a m) => fun r =>
      match r with
      | Reg.cur => [Sum.inl Reg.cur, Sum.inr (Ann.letter a (Fin.snoc m false))]
      | Reg.res => [Sum.inl Reg.res]
      | Reg.grp => [Sum.inl Reg.grp]
  | Sum.inl Ann.sep => fun r =>
      match r with
      | Reg.cur => []
      | Reg.res => [Sum.inl Reg.res]
      | Reg.grp => [Sum.inl Reg.grp]
  | Sum.inr Ann.sep =>
      match q with
      | BS.trans => fun r =>
          match r with
          | Reg.cur => []
          | Reg.res => [Sum.inl Reg.res]
          | Reg.grp => blkPush d
      | BS.allL => fun r =>
          match r with
          | Reg.cur => []
          | Reg.res => Sum.inl Reg.res :: blkPush d
          | Reg.grp => []
      | BS.empty => fun r =>
          match r with
          | Reg.cur => []
          | Reg.res => [Sum.inl Reg.res]
          | Reg.grp => [Sum.inl Reg.grp]
      | BS.allR => fun r =>
          match r with
          | Reg.cur => []
          | Reg.res => [Sum.inl Reg.res]
          | Reg.grp => [Sum.inl Reg.grp]
  | Sum.inl Ann.eos => fun r =>
      match r with
      | Reg.cur => []
      | Reg.res => [Sum.inl Reg.res]
      | Reg.grp => [Sum.inl Reg.grp]
  | Sum.inr Ann.eos => fun r =>
      match r with
      | Reg.cur => []
      | Reg.res => [Sum.inl Reg.res]
      | Reg.grp => [Sum.inl Reg.grp]

/-- The state change of the transducer on one letter. -/
def stepSt (q : BS) : Ann A k ⊕ Ann A k → BS
  | Sum.inl (Ann.letter _ _) => q.advance true
  | Sum.inr (Ann.letter _ _) => q.advance false
  | Sum.inl Ann.sep => BS.empty
  | Sum.inr Ann.sep => BS.empty
  | Sum.inl Ann.eos => BS.empty
  | Sum.inr Ann.eos => BS.empty

lemma copyless_stepUpd (d : Bool) (q : BS) (z : Ann A k ⊕ Ann A k) :
    Copyless (stepUpd d q z) := by
  rw [copyless_iff]
  constructor
  · intro x
    cases d <;> rcases z with z | z <;> cases z <;> cases q <;> cases x <;>
      simp [stepUpd, blkPush]
  · intro x x' hne y hy hy'
    cases d <;> rcases z with z | z <;> cases z <;> cases q <;> cases x <;> cases x' <;>
      simp_all [stepUpd, blkPush]

/-- The streaming string transducer that turns the marked square of an enumeration into the
enumeration with one more (innermost) variable, running forwards when `d` is true and backwards
when it is false. -/
def stepSST (d : Bool) (A : Type) (k : ℕ) : SST (Ann A k ⊕ Ann A k) (Ann A (k + 1)) BS Reg where
  init := BS.empty
  step := fun q z => (stepSt q z, stepUpd d q z)
  step_copyless := fun q z => copyless_stepUpd d q z
  final := fun _ => [Sum.inl Reg.res, Sum.inr Ann.eos]

/-- The function computed by the transducer of one step. -/
def stepFun (d : Bool) (A : Type) (k : ℕ) :
    List (Ann A k ⊕ Ann A k) → List (Ann A (k + 1)) := (stepSST d A k).eval

/-! ## One letter at a time -/

section Steps

variable (d : Bool)

private lemma step_regs (q : BS) (z : Ann A k ⊕ Ann A k) (r g c : List (Ann A (k + 1))) :
    (stepSST d A k).stepConfig (q, regs r g c) z
      = (stepSt q z, fun x => SST.subst (regs r g c) (stepUpd d q z x)) := rfl

@[simp] lemma step_inl_letter (q : BS) (a : A) (m : Fin k → Bool) (r g c : List (Ann A (k + 1))) :
    (stepSST d A k).stepConfig (q, regs r g c) (Sum.inl (Ann.letter a m))
      = (q.advance true, regs r g (c ++ [Ann.letter a (Fin.snoc m true)])) := by
  rw [step_regs]
  refine Prod.ext rfl ?_
  funext x
  cases x <;> simp [stepUpd, SST.subst]

@[simp] lemma step_inr_letter (q : BS) (a : A) (m : Fin k → Bool) (r g c : List (Ann A (k + 1))) :
    (stepSST d A k).stepConfig (q, regs r g c) (Sum.inr (Ann.letter a m))
      = (q.advance false, regs r g (c ++ [Ann.letter a (Fin.snoc m false)])) := by
  rw [step_regs]
  refine Prod.ext rfl ?_
  funext x
  cases x <;> simp [stepUpd, SST.subst]

@[simp] lemma step_inl_sep (q : BS) (r g c : List (Ann A (k + 1))) :
    (stepSST d A k).stepConfig (q, regs r g c) (Sum.inl (Ann.sep : Ann A k))
      = (BS.empty, regs r g []) := by
  rw [step_regs]
  refine Prod.ext rfl ?_
  funext x
  cases x <;> simp [stepUpd, SST.subst]

@[simp] lemma step_inl_eos (q : BS) (r g c : List (Ann A (k + 1))) :
    (stepSST d A k).stepConfig (q, regs r g c) (Sum.inl (Ann.eos : Ann A k))
      = (BS.empty, regs r g []) := by
  rw [step_regs]
  refine Prod.ext rfl ?_
  funext x
  cases x <;> simp [stepUpd, SST.subst]

@[simp] lemma step_inr_eos (q : BS) (r g c : List (Ann A (k + 1))) :
    (stepSST d A k).stepConfig (q, regs r g c) (Sum.inr (Ann.eos : Ann A k))
      = (BS.empty, regs r g []) := by
  rw [step_regs]
  refine Prod.ext rfl ?_
  funext x
  cases x <;> simp [stepUpd, SST.subst]

lemma step_inr_sep_trans (r g c : List (Ann A (k + 1))) :
    (stepSST d A k).stepConfig (BS.trans, regs r g c) (Sum.inr (Ann.sep : Ann A k))
      = (BS.empty, regs r (pushList d g c) []) := by
  rw [step_regs]
  refine Prod.ext rfl ?_
  funext x
  cases x <;> cases d <;> simp [stepUpd, SST.subst, blkPush, pushList]

lemma step_inr_sep_allL (r g c : List (Ann A (k + 1))) :
    (stepSST d A k).stepConfig (BS.allL, regs r g c) (Sum.inr (Ann.sep : Ann A k))
      = (BS.empty, regs (r ++ pushList d g c) [] []) := by
  rw [step_regs]
  refine Prod.ext rfl ?_
  funext x
  cases x <;> cases d <;> simp [stepUpd, SST.subst, blkPush, pushList]

lemma step_inr_sep_empty (r g c : List (Ann A (k + 1))) :
    (stepSST d A k).stepConfig (BS.empty, regs r g c) (Sum.inr (Ann.sep : Ann A k))
      = (BS.empty, regs r g []) := by
  rw [step_regs]
  refine Prod.ext rfl ?_
  funext x
  cases x <;> simp [stepUpd, SST.subst]

lemma step_inr_sep_allR (r g c : List (Ann A (k + 1))) :
    (stepSST d A k).stepConfig (BS.allR, regs r g c) (Sum.inr (Ann.sep : Ann A k))
      = (BS.empty, regs r g []) := by
  rw [step_regs]
  refine Prod.ext rfl ?_
  funext x
  cases x <;> simp [stepUpd, SST.subst]

end Steps

/-! ## Running over a block of letters -/

/-- The letters of a block, with the extra annotation bit `b` for the new variable. -/
def markBlock (k : ℕ) (t : List ℕ) (b : Bool) : ℕ → List A → List (Ann A (k + 1))
  | _, [] => []
  | i, a :: rest => Ann.letter a (Fin.snoc (annOf k t i) b) :: markBlock k t b (i + 1) rest

@[simp] lemma markBlock_nil (t : List ℕ) (b : Bool) (i : ℕ) :
    markBlock (A := A) k t b i [] = [] := rfl

lemma markBlock_append (t : List ℕ) (b : Bool) : ∀ (i : ℕ) (u v : List A),
    markBlock k t b i (u ++ v) = markBlock k t b i u ++ markBlock k t b (i + u.length) v := by
  intro i u
  induction u generalizing i with
  | nil => intro v; simp
  | cons a u ih => intro v; simp [markBlock, ih, Nat.add_right_comm, Nat.add_assoc]

/-- The two halves of a copy of a block make up the block annotated by the extended tuple. -/
lemma markBlock_split {t : List ℕ} (ht : t.length = k) (pre suf : List A) (hpre : pre ≠ []) :
    markBlock k t true 0 pre ++ markBlock k t false pre.length suf
      = blockAt (k + 1) (pre ++ suf) (t ++ [pre.length - 1]) := by
  have key : ∀ (b : Bool) (v : List A) (i : ℕ),
      (∀ j, i ≤ j → j < i + v.length → (decide (j ≤ pre.length - 1) = b)) →
      markBlock k t b i v = blockFrom (k + 1) (t ++ [pre.length - 1]) i v := by
    intro b v
    induction v with
    | nil => intro i _; rfl
    | cons a v ih =>
        intro i h
        have h0 : decide (i ≤ pre.length - 1) = b := h i le_rfl (by simp)
        simp only [markBlock, blockFrom_cons, annOf_append_singleton ht, h0]
        rw [ih (i + 1) (fun j hj hj' => h j (by omega) (by simp at hj' ⊢; omega))]
  have hp : 1 ≤ pre.length := List.length_pos_iff.mpr hpre
  have hap := blockFrom_append (A := A) (k := k + 1) (t ++ [pre.length - 1]) 0 pre suf
  simp only [Nat.zero_add] at hap
  rw [key true pre 0 (fun j _ hj => by simp at hj ⊢; omega),
    key false suf pre.length (fun j hj _ => by simp; omega), ← hap]
  rfl

section Run

variable (d : Bool) {t : List ℕ}

/-- Running over a block of underlined letters. -/
lemma run_inl_block (v : List A) : ∀ (i : ℕ) (q : BS) (r g c : List (Ann A (k + 1))),
    ((blockFrom k t i v).map Sum.inl).foldl (stepSST d A k).stepConfig (q, regs r g c)
      = ((v.foldl (fun s _ => s.advance true) q), regs r g (c ++ markBlock k t true i v)) := by
  induction v with
  | nil => intro i q r g c; simp
  | cons a v ih =>
      intro i q r g c
      simp only [blockFrom_cons, List.map_cons, List.foldl_cons, step_inl_letter, markBlock]
      rw [ih]
      simp

/-- Running over a block of letters that are not underlined. -/
lemma run_inr_block (v : List A) : ∀ (i : ℕ) (q : BS) (r g c : List (Ann A (k + 1))),
    ((blockFrom k t i v).map Sum.inr).foldl (stepSST d A k).stepConfig (q, regs r g c)
      = ((v.foldl (fun s _ => s.advance false) q), regs r g (c ++ markBlock k t false i v)) := by
  induction v with
  | nil => intro i q r g c; simp
  | cons a v ih =>
      intro i q r g c
      simp only [blockFrom_cons, List.map_cons, List.foldl_cons, step_inr_letter, markBlock]
      rw [ih]
      simp

lemma foldl_advance_true_empty (v : List A) (hv : v ≠ []) :
    v.foldl (fun s (_ : A) => s.advance true) BS.empty = BS.allL := by
  cases v with
  | nil => exact absurd rfl hv
  | cons a v =>
      show v.foldl _ (BS.empty.advance true) = _
      have : ∀ (u : List A), u.foldl (fun s (_ : A) => s.advance true) BS.allL = BS.allL := by
        intro u; induction u with
        | nil => rfl
        | cons b u ih => exact ih
      exact this v

lemma foldl_advance_false_allL (v : List A) :
    v.foldl (fun s (_ : A) => s.advance false) BS.allL
      = if v = [] then BS.allL else BS.trans := by
  have htr : ∀ (u : List A), u.foldl (fun s (_ : A) => s.advance false) BS.trans = BS.trans := by
    intro u; induction u with
    | nil => rfl
    | cons b u ih => exact ih
  cases v with
  | nil => simp
  | cons a v => simp [show (BS.allL.advance false) = BS.trans from rfl, htr]

lemma foldl_advance_false_empty (v : List A) :
    v.foldl (fun s (_ : A) => s.advance false) BS.empty
      = if v = [] then BS.empty else BS.allR := by
  have hr : ∀ (u : List A), u.foldl (fun s (_ : A) => s.advance false) BS.allR = BS.allR := by
    intro u; induction u with
    | nil => rfl
    | cons b u ih => exact ih
  cases v with
  | nil => simp
  | cons a v => simp [show (BS.empty.advance false) = BS.allR from rfl, hr]

end Run

/-! ## Factors that the transducer throws away -/

section Drops

variable (d : Bool)

/-- A factor which, read entirely underlined from a clean configuration, leaves the
configuration unchanged. -/
def DropsL (d : Bool) (s : List (Ann A k)) : Prop :=
  ∀ r g : List (Ann A (k + 1)),
    (s.map Sum.inl).foldl (stepSST d A k).stepConfig (BS.empty, regs r g [])
      = (BS.empty, regs r g [])

/-- A factor which, read entirely not underlined from a clean configuration, leaves the
configuration unchanged. -/
def DropsR (d : Bool) (s : List (Ann A k)) : Prop :=
  ∀ r g : List (Ann A (k + 1)),
    (s.map Sum.inr).foldl (stepSST d A k).stepConfig (BS.empty, regs r g [])
      = (BS.empty, regs r g [])

lemma DropsL.append {s₁ s₂ : List (Ann A k)} (h₁ : DropsL d s₁) (h₂ : DropsL d s₂) :
    DropsL d (s₁ ++ s₂) := by
  intro r g
  rw [List.map_append, List.foldl_append, h₁, h₂]

lemma DropsR.append {s₁ s₂ : List (Ann A k)} (h₁ : DropsR d s₁) (h₂ : DropsR d s₂) :
    DropsR d (s₁ ++ s₂) := by
  intro r g
  rw [List.map_append, List.foldl_append, h₁, h₂]

@[simp] lemma DropsL.nil : DropsL (A := A) (k := k) d [] := by intro r g; rfl

@[simp] lemma DropsR.nil : DropsR (A := A) (k := k) d [] := by intro r g; rfl

lemma dropsL_eos : DropsL (A := A) (k := k) d [Ann.eos] := by
  intro r g; simp

lemma dropsR_eos : DropsR (A := A) (k := k) d [Ann.eos] := by
  intro r g; simp

lemma dropsL_block (w : List A) (t : List ℕ) :
    DropsL d (blockAt k w t ++ [Ann.sep]) := by
  intro r g
  rw [List.map_append, List.foldl_append]
  simp only [blockAt, run_inl_block, List.map_cons, List.map_nil, List.foldl_cons,
    List.foldl_nil, step_inl_sep]

lemma dropsR_block (w : List A) (t : List ℕ) :
    DropsR d (blockAt k w t ++ [Ann.sep]) := by
  intro r g
  rw [List.map_append, List.foldl_append]
  simp only [blockAt, run_inr_block, List.map_cons, List.map_nil, List.foldl_cons,
    List.foldl_nil]
  rw [foldl_advance_false_empty]
  by_cases hw : w = []
  · simp [hw, step_inr_sep_empty]
  · simp [hw, step_inr_sep_allR]

/-- The blocks of an enumeration, without the final end marker. -/
def blocksOf (k : ℕ) (w : List A) (ts : List (List ℕ)) : List (Ann A k) :=
  ts.flatMap (fun t => blockAt k w t ++ [Ann.sep])

lemma dropsL_blocksOf (w : List A) (ts : List (List ℕ)) : DropsL d (blocksOf k w ts) := by
  induction ts with
  | nil => simp [blocksOf]
  | cons t ts ih =>
      have : blocksOf k w (t :: ts) = (blockAt k w t ++ [Ann.sep]) ++ blocksOf k w ts := by
        simp [blocksOf]
      rw [this]
      exact (dropsL_block d w t).append d ih

lemma dropsR_blocksOf (w : List A) (ts : List (List ℕ)) : DropsR d (blocksOf k w ts) := by
  induction ts with
  | nil => simp [blocksOf]
  | cons t ts ih =>
      have : blocksOf k w (t :: ts) = (blockAt k w t ++ [Ann.sep]) ++ blocksOf k w ts := by
        simp [blocksOf]
      rw [this]
      exact (dropsR_block d w t).append d ih

end Drops

/-! ## One copy, and one group of copies -/

section Group

variable (d : Bool) {t : List ℕ}

/-- The block of the enumeration produced for the tuple `t` extended by the position `p`. -/
def blkOf (k : ℕ) (w : List A) (t : List ℕ) (p : ℕ) : List (Ann A (k + 1)) :=
  blockAt (k + 1) w (t ++ [p]) ++ [Ann.sep]

/-- **One copy.**  Running over the copy of the marked square whose underlining stops at the
last letter of `pre`, inside the block of the tuple `t`. -/
lemma run_copy (ht : t.length = k) (X : List (Ann A k)) (hX : DropsL d X)
    (rest : List (Ann A k)) (hrest : DropsR d rest)
    (pre suf : List A) (hpre : pre ≠ []) (r g : List (Ann A (k + 1))) :
    (((X ++ blockFrom k t 0 pre).map Sum.inl
        ++ (blockFrom k t pre.length suf ++ ([Ann.sep] ++ rest)).map Sum.inr)).foldl
        (stepSST d A k).stepConfig (BS.empty, regs r g [])
      = if suf = [] then
          (BS.empty, regs (r ++ pushBlk d g (blkOf k (pre ++ suf) t (pre.length - 1))) [] [])
        else (BS.empty, regs r (pushBlk d g (blkOf k (pre ++ suf) t (pre.length - 1))) []) := by
  have hblk : ([] ++ markBlock k t true 0 pre ++ markBlock k t false pre.length suf) ++ [Ann.sep]
      = blkOf k (pre ++ suf) t (pre.length - 1) := by
    simp only [List.nil_append]
    rw [markBlock_split ht pre suf hpre]
    rfl
  rw [List.foldl_append, List.map_append, List.map_append, List.map_append, List.foldl_append,
    List.foldl_append, List.foldl_append, hX, run_inl_block, foldl_advance_true_empty pre hpre,
    run_inr_block, foldl_advance_false_allL]
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil]
  by_cases hs : suf = []
  · rw [if_pos hs, if_pos hs, step_inr_sep_allL, hrest, pushList_eq, hblk]
  · rw [if_neg hs, if_neg hs, step_inr_sep_trans, hrest, pushList_eq, hblk]

/-- The list of the positions of a group of copies, in the order in which they are produced. -/
def grpRange (a m : ℕ) : List ℕ := (List.range m).map (a + ·)

@[simp] lemma grpRange_zero (a : ℕ) : grpRange a 0 = [] := rfl

lemma grpRange_succ (a m : ℕ) : grpRange a (m + 1) = a :: grpRange (a + 1) m := by
  simp only [grpRange, List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
  refine congrArg (fun l => a :: l) (List.map_congr_left ?_)
  intro i _
  simp only [Function.comp_def]
  omega

/-- **One group of copies.**  Running over the copies of the marked square whose underlining
stops inside the block of the tuple `t`, at a position of `suf`. -/
lemma run_group (ht : t.length = k) (w : List A) :
    ∀ (pre suf : List A) (_ : pre ++ suf = w) (_ : suf ≠ [])
      (X : List (Ann A k)) (_ : DropsL d X)
      (rest : List (Ann A k)) (_ : DropsR d rest) (r g : List (Ann A (k + 1))),
      (msSeg (X ++ blockFrom k t 0 pre) (blockFrom k t pre.length suf)
          ([Ann.sep] ++ rest)).foldl (stepSST d A k).stepConfig (BS.empty, regs r g [])
        = (BS.empty,
            regs (r ++ (if d then g ++ (grpRange pre.length suf.length).flatMap (blkOf k w t)
              else ((grpRange pre.length suf.length).reverse).flatMap (blkOf k w t) ++ g)) [] []) :=
  by
  intro pre suf
  induction suf generalizing pre with
  | nil => intro _ hsuf; exact absurd rfl hsuf
  | cons a suf ih =>
      intro hw _ X hX rest hrest r g
      have hsplit : blockFrom k t pre.length (a :: suf)
          = [Ann.letter a (annOf k t pre.length)] ++ blockFrom k t (pre.length + 1) suf := rfl
      have hpre1 : (X ++ blockFrom k t 0 pre) ++ [Ann.letter a (annOf k t pre.length)]
          = X ++ blockFrom k t 0 (pre ++ [a]) := by
        rw [blockFrom_append]
        simp
      have hlen : (pre ++ [a]).length = pre.length + 1 := by simp
      have hww : pre ++ [a] ++ suf = w := by rw [List.append_assoc]; exact hw
      have hcopy := run_copy d ht X hX rest hrest (pre ++ [a]) suf (by simp) r g
      rw [hlen, hww] at hcopy
      simp only [Nat.add_sub_cancel] at hcopy
      rw [hsplit, msSeg_append, List.foldl_append, msSeg_singleton, hpre1, hcopy]
      cases suf with
      | nil =>
          rw [if_pos rfl, blockFrom_nil, msSeg_nil, List.foldl_nil]
          simp only [List.length_cons, List.length_nil, Nat.zero_add, grpRange_succ,
            grpRange_zero, List.flatMap_cons, List.flatMap_nil, List.reverse_cons,
            List.reverse_nil, List.nil_append, List.append_nil]
          cases d <;> simp [pushBlk]
      | cons b suf =>
          rw [if_neg (List.cons_ne_nil b suf)]
          have hih := ih (pre ++ [a]) hww (List.cons_ne_nil b suf) X hX rest hrest r
            (pushBlk d g (blkOf k w t pre.length))
          rw [hlen] at hih
          rw [hih]
          congr 2
          simp only [List.length_cons]
          cases d <;>
            simp [pushBlk, grpRange_succ, List.flatMap_cons, List.reverse_cons,
              List.append_assoc]

end Group

end PolyEnum

end Lax194892Proofs.Transducers
