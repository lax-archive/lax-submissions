/-
Part D: scanning the enumeration of the tuples of positions.

This is the second phase of the proof that a for-transducer in prenex form computes a polyregular
function (the right-to-left inclusion of Theorem `thm:for-transducers-are-polyregular`).  A
streaming string transducer reads the enumeration produced by the first phase -- one annotated copy
of the input per tuple of positions visited by the nest of loops -- and runs the body of the nest
on each copy, keeping the Boolean variables of the for-transducer in its state.  At the end of the
input it runs the epilogue.

The machine cannot store the copy it is reading, but it does not have to: the body is loop-free, so
by `Transducers.ForProg.exec_congr_view` it only sees the letters under its position variables and
the order of those variables.  Those fit in a finite memory (`Transducers.PolyEnum.Blk`), and the
machine runs the body on the canonical string `Transducers.PolyEnum.cword` built from them.
-/
import Lax194892Proofs.Source.PartD.PolyScanAux
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace PolyEnum

open scoped Classical

variable {A B : Type}

/-! ## Bounded Boolean valuations -/

/-- The valuation of all the Boolean variables given by the values of the first `m` ones. -/
def extBV (m : ℕ) (s : Fin m → Bool) : ℕ → Bool := fun i => if h : i < m then s ⟨i, h⟩ else false

/-- The values of the first `m` Boolean variables. -/
def resBV (m : ℕ) (bv : ℕ → Bool) : Fin m → Bool := fun j => bv (j : ℕ)

lemma extBV_resBV (m : ℕ) (bv : ℕ → Bool) (h : ∀ i, m ≤ i → bv i = false) :
    extBV m (resBV m bv) = bv := by
  funext i
  by_cases hi : i < m
  · simp [extBV, resBV, hi]
  · simp [extBV, hi, h i (by omega)]

/-! ## The state of the scanning machine -/

/-- The state of the machine that scans the enumeration: the values of the Boolean variables of the
for-transducer, the first letter of the input, and what is known about the copy being read. -/
structure ScanSt (A : Type) (k m : ℕ) where
  /-- The values of the Boolean variables. -/
  bv : Fin m → Bool
  /-- The first letter of the input string, if any. -/
  fst : Option A
  /-- What is known about the annotated copy being read. -/
  cur : Option (Blk A k)

instance {A : Type} {k m : ℕ} [Finite A] : Finite (ScanSt A k m) := by
  have h : Function.Injective (fun q : ScanSt A k m => (q.bv, q.fst, q.cur)) := by
    intro q q' h
    cases q; cases q'
    simp_all
  exact Finite.of_injective _ h

/-! ## The machine -/

/-- The annotation of a letter of the enumeration, extended by the bit of the constant variable
`0`, which marks the first position. -/
def annBits (k : ℕ) (b : Bool) (mm : Fin k → Bool) : Fin (k + 1) → Bool := Fin.snoc mm b

/-- Reading one more letter of the copy. -/
def pushLetter (k : ℕ) (a : A) (bits : Fin (k + 1) → Bool) : Option (Blk A k) → Blk A k
  | none => ⟨fun _ => a, fun i j => (!bits i || bits j)⟩
  | some v => ⟨fun j => if bits j then a else v.lets j, fun i j => v.le i j && (!bits i || bits j)⟩

/-- Running the body of the nest of loops on the copy that has just been read, on the canonical
string built from what the machine remembers of it. -/
noncomputable def bodyRun (k m : ℕ) (body : ForProg A B) (vf : ℕ → Fin (k + 1))
    (s : Fin m → Bool) : Option (Blk A k) → (ℕ → Bool) × List B
  | none => ForProg.exec ([] : List A) body (fun _ => 0) (extBV m s)
  | some v => ForProg.exec (cword v) body (fun i => ((cpos v (vf i) : ℕ))) (extBV m s)

/-- One step of the machine: the new state and the new content of its single register. -/
noncomputable def scanStep (k m : ℕ) (body : ForProg A B) (vf : ℕ → Fin (k + 1))
    (q : ScanSt A k m) : Ann A k → ScanSt A k m × List (Unit ⊕ B)
  | Ann.letter a mm =>
      (⟨q.bv, if q.cur.isNone then some a else q.fst,
        some (pushLetter k a (annBits k q.cur.isNone mm) q.cur)⟩, [Sum.inl ()])
  | Ann.sep =>
      (⟨resBV m (bodyRun k m body vf q.bv q.cur).1, q.fst, none⟩,
        Sum.inl () :: (bodyRun k m body vf q.bv q.cur).2.map Sum.inr)
  | Ann.eos => (q, [Sum.inl ()])

lemma regsOf_map_inr (l : List B) : regsOf (l.map (Sum.inr : B → Unit ⊕ B)) = [] := by
  induction l with
  | nil => rfl
  | cons b l ih => simp [ih]

/-- The machine that scans the enumeration and runs the body of the nest of loops on each copy,
followed by the epilogue. -/
noncomputable def scanSST (k m : ℕ) (body epilogue : ForProg A B) (vf : ℕ → Fin (k + 1)) :
    SST (Ann A k) B (ScanSt A k m) Unit where
  init := ⟨fun _ => false, none, none⟩
  step := fun q z => ((scanStep k m body vf q z).1, fun _ => (scanStep k m body vf q z).2)
  step_copyless := by
    intro q z
    rw [copyless_iff]
    refine ⟨fun x => ?_, fun x x' hxx' => absurd (Subsingleton.elim x x') hxx'⟩
    cases z with
    | letter a mm => simp [scanStep, regsOf]
    | sep => cases q; simp [scanStep]
    | eos => simp [scanStep, regsOf]
  final := fun q =>
    Sum.inl () :: ((ForProg.exec q.fst.toList epilogue (fun _ => 0) (extBV m q.bv)).2).map Sum.inr

/-- The function computed by the scanning machine. -/
noncomputable def scanFun (k m : ℕ) (body epilogue : ForProg A B) (vf : ℕ → Fin (k + 1)) :
    List (Ann A k) → List B := (scanSST k m body epilogue vf).eval

/-! ## One step of the machine -/

section Steps

variable (k m : ℕ) (body epilogue : ForProg A B) (vf : ℕ → Fin (k + 1))

lemma subst_one (R : List B) : SST.subst (fun _ : Unit => R) [Sum.inl ()] = R := by
  simp [SST.subst]

lemma subst_out (R l : List B) :
    SST.subst (fun _ : Unit => R) (Sum.inl () :: l.map Sum.inr) = R ++ l := by
  induction l with
  | nil => simp [SST.subst]
  | cons b l ih => simp [SST.subst] at ih ⊢; simp [ih]

@[simp] lemma step_letter (q : ScanSt A k m) (R : List B) (a : A) (mm : Fin k → Bool) :
    (scanSST k m body epilogue vf).stepConfig (q, fun _ => R) (Ann.letter a mm)
      = (⟨q.bv, if q.cur.isNone then some a else q.fst,
          some (pushLetter k a (annBits k q.cur.isNone mm) q.cur)⟩, fun _ => R) := by
  refine Prod.ext rfl ?_
  funext x
  exact subst_one R

@[simp] lemma step_sep (q : ScanSt A k m) (R : List B) :
    (scanSST k m body epilogue vf).stepConfig (q, fun _ => R) (Ann.sep : Ann A k)
      = (⟨resBV m (bodyRun k m body vf q.bv q.cur).1, q.fst, none⟩,
         fun _ => R ++ (bodyRun k m body vf q.bv q.cur).2) := by
  refine Prod.ext rfl ?_
  funext x
  exact subst_out R _

@[simp] lemma step_eos (q : ScanSt A k m) (R : List B) :
    (scanSST k m body epilogue vf).stepConfig (q, fun _ => R) (Ann.eos : Ann A k)
      = (q, fun _ => R) := by
  refine Prod.ext rfl ?_
  funext x
  exact subst_one R

end Steps

/-! ## The positions of the variables of a copy -/

/-- The position of each of the `k` loop variables, and of the constant variable `0`. -/
def Tof (k : ℕ) (t : List ℕ) : Fin (k + 1) → ℕ := fun j => (t ++ [0]).getD (j : ℕ) 0

/-- The annotation of a letter of the enumeration, extended by the bit of the constant variable,
marks the positions that are at most the position of each variable. -/
lemma annBits_eq {k : ℕ} {t : List ℕ} (ht : t.length = k) (i : ℕ) :
    annBits k (decide (i = 0)) (annOf k t i) = fun j => decide (i ≤ Tof k t j) := by
  have h := annOf_append_singleton ht 0 i
  have h0 : decide (i ≤ 0) = decide (i = 0) := by
    by_cases hi : i = 0 <;> simp [hi]
  rw [h0] at h
  funext j
  rw [annBits, ← h]
  rfl

/-- The position of every variable of a copy is a position of the input string. -/
lemma Tof_lt {k : ℕ} {L : List (Bool × ℕ)} {t : List ℕ} {n : ℕ} (ht : t ∈ tuplesOf L n)
    (hk : L.length = k) (hn : 0 < n) (j : Fin (k + 1)) : Tof k t j < n := by
  have hlen : t.length = L.length := length_of_mem_tuplesOf L n ht
  have hmem : ∀ p ∈ t, p < n := mem_tuplesOf_lt L n ht
  rcases Nat.lt_or_ge (j : ℕ) t.length with hj | hj
  · have : (t ++ [0]).getD (j : ℕ) 0 = t.getD (j : ℕ) 0 := List.getD_append _ _ _ _ hj
    rw [Tof, this, List.getD_eq_getElem _ _ hj]
    exact hmem _ (List.getElem_mem hj)
  · have hjj : (j : ℕ) = t.length := by
      have := j.2
      omega
    rw [Tof, List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega)]
    simpa [hjj] using hn


/-- A Boolean identity used when one more letter of a copy is read: adding the position `p` to the
prefix already read updates the recorded order of the marked positions. -/
lemma minStep_and (x y p : ℕ) :
    (decide (min x (p - 1) ≤ y) && (!decide (p ≤ x) || decide (p ≤ y)))
      = decide (min x (p + 1 - 1) ≤ y) := by
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true,
    decide_eq_true_eq, decide_eq_false_iff_not]
  omega

/-! ## Running over one copy -/

section Block

variable (k m : ℕ) (body epilogue : ForProg A B) (vf : ℕ → Fin (k + 1))

/-- Running over a prefix of one annotated copy: the machine ends up remembering, for every
variable, the letter at the last marked position read so far, and the order of those positions. -/
lemma run_block_prefix {t : List ℕ} (ht : t.length = k) (w : List A)
    (s : Fin m → Bool) (f0 : Option A) (R : List B) :
    ∀ p : ℕ, 1 ≤ p → p ≤ w.length →
      ∃ v : Blk A k,
        (blockFrom k t 0 (w.take p)).foldl (scanSST k m body epilogue vf).stepConfig
            (⟨s, f0, none⟩, fun _ => R)
          = (⟨s, w[0]?, some v⟩, fun _ => R) ∧
        (∀ j, w[min (Tof k t j) (p - 1)]? = some (v.lets j)) ∧
        (∀ i j, v.le i j = decide (min (Tof k t i) (p - 1) ≤ Tof k t j)) := by
  intro p hp
  induction p, hp using Nat.le_induction with
  | base =>
      intro hw
      have hw0 : (0 : ℕ) < w.length := by omega
      have hget : w[0]? = some w[0] := List.getElem?_eq_getElem hw0
      have htake : w.take 1 = [w[0]] := by
        rw [List.take_add_one, List.take_zero, hget]
        rfl
      refine ⟨pushLetter k w[0] (annBits k true (annOf k t 0)) none, ?_, ?_, ?_⟩
      · rw [htake]
        simp only [blockFrom_cons, blockFrom_nil, List.foldl_cons, List.foldl_nil]
        rw [step_letter]
        simp [hget]
      · intro j
        have hb : annBits k true (annOf k t 0) = fun j => decide (0 ≤ Tof k t j) := by
          simpa using annBits_eq ht 0
        simp only [pushLetter, hb, Nat.sub_self, Nat.min_zero]
        simp
      · intro i j
        have hb : annBits k true (annOf k t 0) = fun j => decide (0 ≤ Tof k t j) := by
          simpa using annBits_eq ht 0
        simp [pushLetter, hb]
  | succ p hp ih =>
      intro hw
      have hpw : p < w.length := by omega
      have hget : w[p]? = some w[p] := List.getElem?_eq_getElem hpw
      obtain ⟨v, hfold, hlets, hle⟩ := ih (by omega)
      have htake : w.take (p + 1) = w.take p ++ [w[p]] := by
        rw [List.take_add_one, hget]
        rfl
      have hlen : (w.take p).length = p := by
        rw [List.length_take]
        omega
      have hb : annBits k false (annOf k t p) = fun j => decide (p ≤ Tof k t j) := by
        have := annBits_eq ht p
        rw [show decide (p = 0) = false from by simp; omega] at this
        exact this
      refine ⟨pushLetter k w[p] (fun j => decide (p ≤ Tof k t j)) (some v), ?_, ?_, ?_⟩
      · rw [htake, blockFrom_append, hlen, List.foldl_append, hfold]
        simp only [blockFrom_cons, blockFrom_nil, List.foldl_cons, List.foldl_nil]
        rw [step_letter]
        simp [hb]
      · intro j
        by_cases hbj : p ≤ Tof k t j
        · have : min (Tof k t j) (p + 1 - 1) = p := by omega
          rw [this]
          simp only [pushLetter, hbj, decide_true, if_pos]
          exact hget
        · have h1 : min (Tof k t j) (p + 1 - 1) = Tof k t j := by omega
          have h2 : min (Tof k t j) (p - 1) = Tof k t j := by omega
          rw [h1]
          have := hlets j
          rw [h2] at this
          simpa [pushLetter, hbj] using this
      · intro i j
        simpa [pushLetter, hle i j] using minStep_and (Tof k t i) (Tof k t j) p

/-- Running over one whole annotated copy. -/
lemma run_block_all {L : List (Bool × ℕ)} {t : List ℕ} {w : List A}
    (hk : L.length = k) (htm : t ∈ tuplesOf L w.length) (hw : w ≠ [])
    (s : Fin m → Bool) (f0 : Option A) (R : List B) :
    ∃ v : Blk A k,
      (blockAt k w t).foldl (scanSST k m body epilogue vf).stepConfig
          (⟨s, f0, none⟩, fun _ => R)
        = (⟨s, w[0]?, some v⟩, fun _ => R) ∧
      (∀ j, w[Tof k t j]? = some (v.lets j)) ∧
      (∀ i j, v.le i j = decide (Tof k t i ≤ Tof k t j)) := by
  have hn : 0 < w.length := List.length_pos_iff.mpr hw
  have ht : t.length = k := by
    rw [length_of_mem_tuplesOf L w.length htm, hk]
  have hlt : ∀ j, Tof k t j < w.length := fun j => Tof_lt htm hk hn j
  obtain ⟨v, hfold, hlets, hle⟩ :=
    run_block_prefix k m body epilogue vf ht w s f0 R w.length hn le_rfl
  refine ⟨v, ?_, ?_, ?_⟩
  · have hbl : blockAt k w t = blockFrom k t 0 (w.take w.length) := by
      rw [List.take_length]
      rfl
    rw [hbl]
    exact hfold
  · intro j
    have := hlets j
    rwa [show min (Tof k t j) (w.length - 1) = Tof k t j from by have := hlt j; omega] at this
  · intro i j
    have := hle i j
    rwa [show min (Tof k t i) (w.length - 1) = Tof k t i from by have := hlt i; omega] at this

end Block

/-! ## Running over one copy and the separator that follows it -/

section Sep

variable (k m : ℕ) (body epilogue : ForProg A B) (vf : ℕ → Fin (k + 1))

/-- The valuation of the position variables produced by a tuple, read off the positions of the
variables of the corresponding copy. -/
lemma setTuple_eq_Tof {L : List (Bool × ℕ)} {t : List ℕ} (ht : t.length = L.length)
    (hvf : ∀ i, ((vf i : ℕ)) = virt L i) (i : ℕ) :
    setTuple L t (fun _ => 0) i = Tof k t (vf i) := by
  rw [setTuple_getD L t ht, Tof, hvf]

/-- Running over one annotated copy and the separator that follows it: the machine performs
exactly one iteration of the body of the nest of loops. -/
lemma run_block_sep {L : List (Bool × ℕ)} {t : List ℕ} {w : List A}
    (hk : L.length = k) (hbody : body.LoopFree) (hvf : ∀ i, ((vf i : ℕ)) = virt L i)
    (htm : t ∈ tuplesOf L w.length) (s : Fin m → Bool) (f0 : Option A) (R : List B) :
    (blockAt k w t ++ [Ann.sep]).foldl (scanSST k m body epilogue vf).stepConfig
        (⟨s, f0, none⟩, fun _ => R)
      = (⟨resBV m (ForProg.exec w body (setTuple L t (fun _ => 0)) (extBV m s)).1,
          (w[0]?).or f0, none⟩,
         fun _ => R ++ (ForProg.exec w body (setTuple L t (fun _ => 0)) (extBV m s)).2) := by
  have htlen : t.length = L.length := length_of_mem_tuplesOf L w.length htm
  have hpos : ∀ i, setTuple L t (fun _ => 0) i = Tof k t (vf i) :=
    setTuple_eq_Tof k vf htlen hvf
  by_cases hw : w = []
  · subst hw
    have ht0 : t = [] := by
      have hlt := mem_tuplesOf_lt L 0 htm
      cases t with
      | nil => rfl
      | cons p t => exact absurd (hlt p (by simp)) (by omega)
    have hzero : ∀ i, setTuple L t (fun _ => 0) i = 0 := by
      intro i
      rw [hpos i, Tof, ht0]
      rcases hj : ((vf i : ℕ)) with _ | n <;> simp [List.getD_eq_getElem?_getD]
    have hbl : blockAt k ([] : List A) t = [] := rfl
    rw [hbl, List.nil_append, List.foldl_cons, List.foldl_nil, step_sep]
    have hex : ForProg.exec ([] : List A) body (fun _ => 0) (extBV m s)
        = ForProg.exec ([] : List A) body (setTuple L t (fun _ => 0)) (extBV m s) :=
      ForProg.exec_congr_pos _ _ _ _ _ (fun i _ => (hzero i).symm)
    simp [bodyRun, hex]
  · obtain ⟨v, hfold, hlets, hle⟩ := run_block_all k m body epilogue vf hk htm hw s f0 R
    obtain ⟨a0, hg0⟩ : ∃ a, w[0]? = some a := by
      cases w with
      | nil => exact absurd rfl hw
      | cons a w => exact ⟨a, rfl⟩
    have hlets' : ∀ i j, Tof k t i = Tof k t j → v.lets i = v.lets j := by
      intro i j hij
      have h1 := hlets i
      have h2 := hlets j
      rw [hij] at h1
      exact Option.some_inj.mp (h1.symm.trans h2)
    have hcons : ∀ i j, cpos v i = cpos v j → v.lets i = v.lets j :=
      cpos_consistent v (Tof k t) hle hlets'
    have hex : ForProg.exec (cword v) body (fun i => ((cpos v (vf i) : ℕ))) (extBV m s)
        = ForProg.exec w body (setTuple L t (fun _ => 0)) (extBV m s) := by
      refine (ForProg.exec_congr_view w (cword v) body hbody _ _ _ ?_ ?_).symm
      · intro i _ j _
        rw [hpos i, hpos j]
        exact (cpos_le_iff v (Tof k t) hle (vf i) (vf j)).symm
      · intro i _
        rw [hpos i, hlets (vf i), cword_getElem v hcons (vf i)]
    rw [List.foldl_append, hfold, List.foldl_cons, List.foldl_nil, step_sep]
    simp [bodyRun, hex, hg0]

end Sep

/-! ## Running over the whole enumeration -/

section Blocks

variable (k m : ℕ) (body epilogue : ForProg A B) (vf : ℕ → Fin (k + 1))

/-- Running over a list of annotated copies: the machine performs one iteration of the body per
copy. -/
lemma run_all_blocks {L : List (Bool × ℕ)} {w : List A}
    (hk : L.length = k) (hbody : body.LoopFree) (hvf : ∀ i, ((vf i : ℕ)) = virt L i)
    (hm : ∀ i ∈ body.boolVars, i < m) :
    ∀ (ts : List (List ℕ)), (∀ t ∈ ts, t ∈ tuplesOf L w.length) →
      ∀ (bv : ℕ → Bool), (∀ i, m ≤ i → bv i = false) → ∀ (f0 : Option A) (R : List B),
        (ts.flatMap (fun t => blockAt k w t ++ [Ann.sep])).foldl
            (scanSST k m body epilogue vf).stepConfig (⟨resBV m bv, f0, none⟩, fun _ => R)
          = (⟨resBV m (runList
                (fun bv t => ForProg.exec w body (setTuple L t (fun _ => 0)) bv) ts bv).1,
              (if ts = [] then f0 else (w[0]?).or f0), none⟩,
             fun _ => R ++ (runList
               (fun bv t => ForProg.exec w body (setTuple L t (fun _ => 0)) bv) ts bv).2) := by
  intro ts
  induction ts with
  | nil => intro _ bv _ f0 R; simp
  | cons t ts ih =>
      intro hts bv hbv f0 R
      have hbve : extBV m (resBV m bv) = bv := extBV_resBV m bv hbv
      have hstep := run_block_sep k m body epilogue vf hk hbody hvf
        (hts t (by simp)) (resBV m bv) f0 R
      rw [hbve] at hstep
      set bv' := (ForProg.exec w body (setTuple L t (fun _ => 0)) bv).1 with hbv'def
      set out := (ForProg.exec w body (setTuple L t (fun _ => 0)) bv).2 with houtdef
      have hbv' : ∀ i, m ≤ i → bv' i = false := by
        intro i hi
        rw [hbv'def, ForProg.exec_bv_unchanged _ _ _ _ (fun hmem => absurd (hm i hmem) (by omega))]
        exact hbv i hi
      have hrest := ih (fun t' ht' => hts t' (by simp [ht'])) bv' hbv' ((w[0]?).or f0) (R ++ out)
      rw [List.flatMap_cons, List.foldl_append, hstep, hrest, runList_cons]
      refine Prod.ext ?_ ?_
      · refine congrArg (fun o => ScanSt.mk _ o none) ?_
        by_cases hts' : ts = []
        · simp [hts']
        · simp only [hts', if_false, if_neg (by simp : ¬ (t :: ts = []))]
          cases hw0 : w[0]? <;> simp
      · funext x
        simp [houtdef, hbv'def, List.append_assoc]

/-- A nest of loops over a nonempty input visits at least one tuple. -/
lemma tuplesOf_ne_nil (L : List (Bool × ℕ)) {n : ℕ} (hn : 0 < n) : tuplesOf L n ≠ [] := by
  induction L with
  | nil => simp
  | cons a L ih =>
      obtain ⟨d, x⟩ := a
      obtain ⟨t, ht⟩ := List.exists_mem_of_ne_nil _ ih
      have h0 : (0 : ℕ) ∈ loopRange d n := mem_loopRange.mpr hn
      refine List.ne_nil_of_mem (a := 0 :: t) ?_
      rw [tuplesOf_cons]
      exact List.mem_flatMap.mpr ⟨0, h0, List.mem_map.mpr ⟨t, ht, rfl⟩⟩

lemma option_toList_getElem? (o : Option A) : (o.toList)[0]? = o := by
  cases o <;> simp

/-- **The scanning machine computes the for-transducer.**  On the enumeration of the tuples of
positions of the nest of loops, the machine outputs exactly what the program in prenex form
outputs. -/
theorem scan_enum {L : List (Bool × ℕ)} (hk : L.length = k) (hbody : body.LoopFree)
    (hepi : epilogue.LoopFree) (hvf : ∀ i, ((vf i : ℕ)) = virt L i)
    (hm : ∀ i ∈ body.boolVars, i < m) (w : List A) :
    scanFun k m body epilogue vf (enum k L w)
      = ForProg.eval (ForProg.seq (ForProg.nestLoops L body) epilogue) w := by
  classical
  set step : (ℕ → Bool) → List ℕ → (ℕ → Bool) × List B :=
    fun bv t => ForProg.exec w body (setTuple L t (fun _ => 0)) bv with hstepdef
  set ts := tuplesOf L w.length with htsdef
  set BV := (runList step ts (fun _ => false)).1 with hBVdef
  set OUT := (runList step ts (fun _ => false)).2 with hOUTdef
  have hBV : ∀ i, m ≤ i → BV i = false := by
    have hfix := runList_fix step ts (fun _ => false)
      (fun bv => (fun i => if m ≤ i then bv i else false)) ?_
    · intro i hi
      have := congrFun hfix i
      simpa [hi] using this
    · intro bv t
      funext i
      by_cases hi : m ≤ i
      · simp only [hi, if_true, hstepdef]
        rw [ForProg.exec_bv_unchanged _ _ _ _ (fun hmem => absurd (hm i hmem) (by omega))]
      · simp [hi]
  have hinit : (scanSST k m body epilogue vf).init
      = (⟨resBV m (fun _ => false), none, none⟩ : ScanSt A k m) := rfl
  have hrun : (scanSST k m body epilogue vf).runConfig (enum k L w)
      = (⟨resBV m BV, (if ts = [] then none else w[0]?), none⟩, fun _ => OUT) := by
    rw [SST.runConfig, hinit, enum, List.foldl_append]
    rw [run_all_blocks k m body epilogue vf hk hbody hvf hm ts (fun t ht => ht)
      (fun _ => false) (fun i _ => rfl) none []]
    rw [List.foldl_cons, List.foldl_nil, step_eos]
    refine Prod.ext ?_ (by funext x; simp [hOUTdef, hstepdef])
    refine congrArg (fun o => ScanSt.mk (resBV m BV) o none) ?_
    by_cases hts : ts = [] <;> simp [hts]
  have hfst : ∀ i ∈ epilogue.posVars,
      w[(fun _ : ℕ => 0) i]? = ((if ts = [] then none else w[0]?) : Option A).toList[0]? := by
    intro i _
    by_cases hts : ts = []
    · have hw : w = [] := by
        by_contra hw
        exact tuplesOf_ne_nil L (List.length_pos_iff.mpr hw) (by rw [← htsdef]; exact hts)
      simp [hts, hw]
    · simp [hts, option_toList_getElem?]
  rw [scanFun, SST.eval, hrun]
  simp only [scanSST, subst_out]
  rw [extBV_resBV m BV hBV]
  have hepi' : ForProg.exec ((if ts = [] then none else w[0]?) : Option A).toList epilogue
      (fun _ => 0) BV = ForProg.exec w epilogue (fun _ => 0) BV := by
    refine (ForProg.exec_congr_view w _ epilogue hepi _ _ _ ?_ hfst).symm
    intro i _ j _
    simp
  rw [hepi']
  rw [ForProg.eval, exec_seq, exec_nestLoops]

end Blocks

end PolyEnum

end Lax194892Proofs.Transducers
