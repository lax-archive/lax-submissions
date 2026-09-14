/-
Part D: the correctness of the transducer of one step, and the polyregularity of the enumeration.

`RequestProject/PartD/PolyStep.lean` runs the streaming string transducer `stepSST` over one copy
and over one group of copies of a marked square.  This file assembles those runs into the
correctness statement of the whole transducer,

  `stepFun d A k (markedSquare (enum k L w)) = enum (k+1) (L ++ [(d, x)]) w`,

and deduces, by induction on the list of loops, that the enumeration `enum` of the tuples of
positions visited by a nest of loops is a polyregular function of the input string: marked squaring
is a prime polyregular function and a streaming string transducer computes a regular function
(Theorem `theorem:sst-two-way-equivalence`).
-/
import Lax194892Proofs.Source.PartD.PolyStep
import Lax194892Proofs.Source.PartD.ForPrenex
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace PolyEnum

variable {A : Type} {k : ℕ}

/-! ## The group of copies produced for one tuple -/

/-- The copies of the block of the tuple `t` in which the new variable points at each position of
the input, in the order prescribed by the direction `d` of the new loop. -/
def grpOf (d : Bool) (k : ℕ) (w : List A) (t : List ℕ) : List (Ann A (k + 1)) :=
  (loopRange d w.length).flatMap (blkOf k w t)

lemma grpRange_zero_eq (m : ℕ) : grpRange 0 m = List.range m := by
  simp [grpRange]

@[simp] lemma grpOf_nil (d : Bool) (t : List ℕ) : grpOf d k ([] : List A) t = [] := by
  cases d <;> simp [grpOf]

/-! ## Running over one block of the enumeration -/

/-- **One block.**  Running over the copies of the marked square whose underlining ends inside the
block of the tuple `t` appends to the output register the whole group of copies of that block. -/
lemma run_block (d : Bool) {t : List ℕ} (ht : t.length = k) (w : List A)
    (X : List (Ann A k)) (hX : DropsL d X) (rest : List (Ann A k)) (hrest : DropsR d rest)
    (r : List (Ann A (k + 1))) :
    (msSeg X (blockAt k w t ++ [Ann.sep]) rest).foldl (stepSST d A k).stepConfig
        (BS.empty, regs r [] [])
      = (BS.empty, regs (r ++ grpOf d k w t) [] []) := by
  rw [msSeg_append, List.foldl_append]
  have hfirst : (msSeg X (blockAt k w t) ([Ann.sep] ++ rest)).foldl (stepSST d A k).stepConfig
      (BS.empty, regs r [] []) = (BS.empty, regs (r ++ grpOf d k w t) [] []) := by
    by_cases hw : w = []
    · subst hw
      simp [blockAt]
    · have h := run_group d ht w [] w (by simp) hw X hX rest hrest r []
      simp only [List.length_nil, List.append_nil, blockAt] at h ⊢
      rw [show X ++ blockFrom k t 0 ([] : List A) = X from by simp] at h
      rw [h]
      congr 2
      cases d <;>
        simp [grpOf, grpRange_zero_eq, loopRange]
  have hsplit : (X ++ blockAt k w t) ++ [Ann.sep] = X ++ (blockAt k w t ++ [Ann.sep]) :=
    List.append_assoc _ _ _
  have hXfull : DropsL d (X ++ (blockAt k w t ++ [Ann.sep])) := hX.append d (dropsL_block d w t)
  rw [hfirst, msSeg_singleton, hsplit, List.foldl_append, hXfull, hrest]

/-! ## Running over all the blocks -/

/-- **All the blocks.**  Running over the copies of the marked square whose underlining ends inside
one of the blocks of the tuples `ts`. -/
lemma run_blocks (d : Bool) (w : List A) :
    ∀ (ts : List (List ℕ)), (∀ t ∈ ts, t.length = k) →
      ∀ (X : List (Ann A k)), DropsL d X → ∀ (rest : List (Ann A k)), DropsR d rest →
        ∀ r : List (Ann A (k + 1)),
          (msSeg X (blocksOf k w ts) rest).foldl (stepSST d A k).stepConfig
              (BS.empty, regs r [] [])
            = (BS.empty, regs (r ++ ts.flatMap (grpOf d k w)) [] []) := by
  intro ts
  induction ts with
  | nil => intro _ X _ rest _ r; simp [blocksOf]
  | cons t ts ih =>
      intro hlen X hX rest hrest r
      have hb : blocksOf k w (t :: ts) = (blockAt k w t ++ [Ann.sep]) ++ blocksOf k w ts := by
        simp [blocksOf]
      rw [hb, msSeg_append, List.foldl_append,
        run_block d (hlen t (by simp)) w X hX (blocksOf k w ts ++ rest)
          ((dropsR_blocksOf d w ts).append d hrest) r,
        ih (fun s hs => hlen s (by simp [hs]))
          (X ++ (blockAt k w t ++ [Ann.sep])) (hX.append d (dropsL_block d w t)) rest hrest _]
      simp [List.flatMap_cons, List.append_assoc]

/-! ## The correctness of one step -/

lemma subst_final (r g c : List (Ann A (k + 1))) :
    SST.subst (regs r g c) [Sum.inl Reg.res, Sum.inr (Ann.eos : Ann A (k + 1))]
      = r ++ [Ann.eos] := by
  simp [SST.subst]

lemma regs_empty : (fun _ => ([] : List (Ann A (k + 1)))) = regs [] [] [] := by
  funext x; cases x <;> rfl

/-- Running the transducer of one step over the marked square of an enumeration. -/
lemma stepFun_blocks (d : Bool) (w : List A) (ts : List (List ℕ))
    (hlen : ∀ t ∈ ts, t.length = k) :
    stepFun d A k (markedSquare (Ann A k) (blocksOf k w ts ++ [Ann.eos]))
      = ts.flatMap (grpOf d k w) ++ [Ann.eos] := by
  have hms : markedSquare (Ann A k) (blocksOf k w ts ++ [Ann.eos])
      = msSeg [] (blocksOf k w ts) [Ann.eos]
        ++ msSeg (blocksOf k w ts) [Ann.eos] [] := by
    rw [markedSquare_eq_msSeg, msSeg_append]; simp
  simp only [stepFun, SST.eval, SST.runConfig, hms, List.foldl_append, regs_empty,
    show (stepSST d A k).init = BS.empty from rfl]
  rw [run_blocks d w ts hlen [] (DropsL.nil d) [Ann.eos] (dropsR_eos d) []]
  rw [msSeg_singleton]
  have hL : DropsL d (blocksOf k w ts ++ [Ann.eos]) :=
    (dropsL_blocksOf d w ts).append d (dropsL_eos d)
  rw [List.foldl_append, hL]
  simp only [List.map_nil, List.foldl_nil]
  rw [show ((stepSST d A k).final BS.empty)
      = [Sum.inl Reg.res, Sum.inr (Ann.eos : Ann A (k + 1))] from rfl]
  rw [subst_final]
  simp

/-! ## The tuples of an extended nest -/

lemma tuplesOf_append_singleton (d : Bool) (x n : ℕ) :
    ∀ L : List (Bool × ℕ),
      tuplesOf (L ++ [(d, x)]) n
        = (tuplesOf L n).flatMap (fun t => (loopRange d n).map (fun p => t ++ [p])) := by
  intro L
  induction L with
  | nil =>
      simp only [List.nil_append, tuplesOf_cons, tuplesOf_nil, List.flatMap_cons,
        List.flatMap_nil, List.map_cons, List.map_nil, List.nil_append]
      induction (loopRange d n) with
      | nil => rfl
      | cons a l ih => simp [ih]
  | cons a L ih =>
      obtain ⟨e, y⟩ := a
      rw [List.cons_append, tuplesOf_cons, tuplesOf_cons, List.flatMap_assoc]
      refine List.flatMap_congr (fun p _ => ?_)
      rw [ih, List.map_flatMap, List.flatMap_map]
      refine List.flatMap_congr (fun t _ => ?_)
      simp [List.map_map, Function.comp_def]

/-- **One step of the enumeration.**  The transducer of one step turns the marked square of the
enumeration of a nest of loops into the enumeration of the nest with one more innermost loop. -/
theorem stepFun_enum (d : Bool) (x : ℕ) (L : List (Bool × ℕ)) (w : List A) :
    stepFun d A L.length (markedSquare (Ann A L.length) (enum L.length L w))
      = enum (L.length + 1) (L ++ [(d, x)]) w := by
  have hlen : ∀ t ∈ tuplesOf L w.length, t.length = L.length :=
    fun t ht => length_of_mem_tuplesOf L w.length ht
  have henum : enum L.length L w = blocksOf L.length w (tuplesOf L w.length) ++ [Ann.eos] := rfl
  rw [henum, stepFun_blocks d w (tuplesOf L w.length) hlen]
  have hts : tuplesOf (L ++ [(d, x)]) w.length
      = (tuplesOf L w.length).flatMap
          (fun t => (loopRange d w.length).map (fun p => t ++ [p])) :=
    tuplesOf_append_singleton d x w.length L
  have hlen' : (L ++ [(d, x)]).length = L.length + 1 := by simp
  have : enum (L.length + 1) (L ++ [(d, x)]) w
      = blocksOf (L.length + 1) w (tuplesOf (L ++ [(d, x)]) w.length) ++ [Ann.eos] := rfl
  rw [this, hts]
  congr 1
  simp only [blocksOf, List.flatMap_assoc, List.flatMap_map]
  refine List.flatMap_congr (fun t _ => ?_)
  simp only [grpOf]
  rfl

end PolyEnum

end Lax194892Proofs.Transducers
