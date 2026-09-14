/-
The list constructor and the list deconstructor are regular under string representation.  Part of
the easy direction of Theorem `thm:regular-terms` of *Transducers* (M. Bojańczyk).

The constructor `1 + A × A* → A*` maps `L 1` to `[]` and `R (a,l)` to `a :: l`.  Under string
representation the second case turns `R (a,[a₂,…])` into `[a,a₂,…]`, so the comma that follows the
representation of `a` in the output is present exactly when the tail is not empty -- which is not
known when the machine reaches that place in the input.  As for distributivity, the function is
therefore written as the concatenation of two machines: the first writes `[`, the representation of
`a`, and the comma if there is a tail (which it discovers one letter later, when the tail is
already open), and the second writes the entries of the tail and the closing `]`.

The deconstructor `A* → 1 + A × A*` needs no such splitting: whether the input list is empty is
decided by the letter that follows the opening bracket, and one machine can wait for it before
writing anything.
-/
import Lax709149Proofs.Source.PartC.CombMach
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax709149Proofs.Transducers
namespace Comb

/-! ## The list constructor -/

/-- The modes of the first machine of the list constructor. -/
inductive ConsMode | s0 | sOpen | sA | sBrack | sPend | dead
  deriving DecidableEq, Fintype

/-- The modes of the second machine of the list constructor. -/
inductive Cons2Mode | t0 | tL | tOpen | tA | tBrack | tBody | dead
  deriving DecidableEq, Fintype

/-- The first machine of the list constructor: it writes the opening bracket, the head, and the
comma that separates the head from the tail if the tail is not empty. -/
def consMach1 : Mach ConsMode Sym8 where
  step := fun m e c => match m with
    | .s0 => if c = Sym8.left then .dead else .sOpen
    | .sOpen => .sA
    | .sA => if e = 1 ∧ c = Sym8.comma then .sBrack else .sA
    | .sBrack => .sPend
    | .sPend => .dead
    | .dead => .dead
  out := fun m e c => match m with
    | .s0 => [Sym8.lbrack]
    | .sOpen => []
    | .sA => if e = 1 ∧ c = Sym8.comma then [] else [c]
    | .sBrack => []
    | .sPend => if c = Sym8.rbrack then [] else [Sym8.comma]
    | .dead => []
  fin := fun _ _ => []

/-- The second machine of the list constructor: it writes the entries of the tail and the closing
bracket. -/
def consMach2 : Mach Cons2Mode Sym8 where
  step := fun m e c => match m with
    | .t0 => if c = Sym8.left then .tL else .tOpen
    | .tL => .dead
    | .tOpen => .tA
    | .tA => if e = 1 ∧ c = Sym8.comma then .tBrack else .tA
    | .tBrack => .tBody
    | .tBody => if e = 2 ∧ c = Sym8.rbrack then .dead else .tBody
    | .dead => .dead
  out := fun m e c => match m with
    | .t0 => []
    | .tL => [Sym8.rbrack]
    | .tOpen => []
    | .tA => []
    | .tBrack => []
    | .tBody => if e = 2 ∧ c = Sym8.rbrack then [Sym8.rbrack] else [c]
    | .dead => []
  fin := fun _ _ => []

@[simp] lemma consMach1_out_s0 (e : ℕ) (c : Sym8) : consMach1.out .s0 e c = [Sym8.lbrack] := rfl
@[simp] lemma consMach1_step_s0_left (e : ℕ) : consMach1.step .s0 e Sym8.left = .dead := rfl
@[simp] lemma consMach1_step_s0_right (e : ℕ) : consMach1.step .s0 e Sym8.right = .sOpen := rfl
@[simp] lemma consMach1_out_sOpen (e : ℕ) (c : Sym8) : consMach1.out .sOpen e c = [] := rfl
@[simp] lemma consMach1_step_sOpen (e : ℕ) (c : Sym8) : consMach1.step .sOpen e c = .sA := rfl
@[simp] lemma consMach1_out_sA_comma : consMach1.out .sA 1 Sym8.comma = [] := rfl
@[simp] lemma consMach1_step_sA_comma : consMach1.step .sA 1 Sym8.comma = .sBrack := rfl
@[simp] lemma consMach1_out_sBrack (e : ℕ) (c : Sym8) : consMach1.out .sBrack e c = [] := rfl
@[simp] lemma consMach1_step_sBrack (e : ℕ) (c : Sym8) : consMach1.step .sBrack e c = .sPend := rfl
@[simp] lemma consMach1_step_sPend (e : ℕ) (c : Sym8) : consMach1.step .sPend e c = .dead := rfl
@[simp] lemma consMach1_out_dead (e : ℕ) (c : Sym8) : consMach1.out .dead e c = [] := rfl
@[simp] lemma consMach1_step_dead (e : ℕ) (c : Sym8) : consMach1.step .dead e c = .dead := rfl
@[simp] lemma consMach1_fin (m : ConsMode) (e : ℕ) : consMach1.fin m e = [] := rfl

@[simp] lemma consMach2_out_t0 (e : ℕ) (c : Sym8) : consMach2.out .t0 e c = [] := rfl
@[simp] lemma consMach2_step_t0_left (e : ℕ) : consMach2.step .t0 e Sym8.left = .tL := rfl
@[simp] lemma consMach2_step_t0_right (e : ℕ) : consMach2.step .t0 e Sym8.right = .tOpen := rfl
@[simp] lemma consMach2_out_tL (e : ℕ) (c : Sym8) : consMach2.out .tL e c = [Sym8.rbrack] := rfl
@[simp] lemma consMach2_step_tL (e : ℕ) (c : Sym8) : consMach2.step .tL e c = .dead := rfl
@[simp] lemma consMach2_out_tOpen (e : ℕ) (c : Sym8) : consMach2.out .tOpen e c = [] := rfl
@[simp] lemma consMach2_step_tOpen (e : ℕ) (c : Sym8) : consMach2.step .tOpen e c = .tA := rfl
@[simp] lemma consMach2_out_tA (e : ℕ) (c : Sym8) : consMach2.out .tA e c = [] := rfl
@[simp] lemma consMach2_step_tA_comma : consMach2.step .tA 1 Sym8.comma = .tBrack := rfl
@[simp] lemma consMach2_out_tBrack (e : ℕ) (c : Sym8) : consMach2.out .tBrack e c = [] := rfl
@[simp] lemma consMach2_step_tBrack (e : ℕ) (c : Sym8) : consMach2.step .tBrack e c = .tBody := rfl
@[simp] lemma consMach2_out_tBody_rbrack :
    consMach2.out .tBody 2 Sym8.rbrack = [Sym8.rbrack] := rfl
@[simp] lemma consMach2_step_tBody_rbrack : consMach2.step .tBody 2 Sym8.rbrack = .dead := rfl
@[simp] lemma consMach2_out_dead (e : ℕ) (c : Sym8) : consMach2.out .dead e c = [] := rfl
@[simp] lemma consMach2_step_dead (e : ℕ) (c : Sym8) : consMach2.step .dead e c = .dead := rfl
@[simp] lemma consMach2_fin (m : Cons2Mode) (e : ℕ) : consMach2.fin m e = [] := rfl

section Cons

variable (A : Ty)

/-- The domain of the list constructor. -/
def consDom : Ty := Ty.sum Ty.one (Ty.prod A (Ty.list A))

lemma consDom_height : (consDom A).height = A.height + 2 := by
  simp [consDom, Ty.height]
  omega

/-- The counter at depth `1`, inside the brackets of the pair. -/
def c1 : Fin ((consDom A).height + 1) := ⟨1, by rw [consDom_height]; omega⟩

/-- The counter at depth `2`, inside the brackets of the tail list. -/
def c2 : Fin ((consDom A).height + 1) := ⟨2, by rw [consDom_height]; omega⟩

@[simp] lemma c1_val : (c1 A).1 = 1 := rfl
@[simp] lemma c2_val : (c2 A).1 = 2 := rfl

lemma dstep_c0_lpar : dstep (0 : Fin ((consDom A).height + 1)) Sym8.lpar = c1 A := by
  refine Fin.ext ?_
  rw [dstep_open (by simp) (by simp only [Fin.val_zero]; rw [consDom_height]; omega)]
  rfl

lemma dstep_c1_lbrack : dstep (c1 A) Sym8.lbrack = c2 A := by
  refine Fin.ext ?_
  rw [dstep_open (by simp) (by simp only [c1_val]; rw [consDom_height]; omega)]
  rfl

lemma consCapA : (1 : ℤ) + (A.height : ℤ) ≤ ((consDom A).height : ℤ) := by
  rw [consDom_height]; push_cast; omega

lemma consCapA2 : (2 : ℤ) + (A.height : ℤ) ≤ ((consDom A).height : ℤ) := by
  rw [consDom_height]; push_cast; omega

/-- The run of the first machine on the input `L 1`. -/
theorem consMach1_run_left (u : Ty.one.Elt) :
    consMach1.run ((consDom A).height) .s0 ((consDom A).repr (Sum.inl u)) = [Sym8.lbrack] := by
  show consMach1.runFrom ((consDom A).height) (ConsMode.s0, 0) (Sym8.left :: [Sym8.one])
    = [Sym8.lbrack]
  rw [Mach.runFrom_cons]
  simp only [consMach1_out_s0, consMach1_step_s0_left,
    dstep_neutral (by simp : wt Sym8.left = 0)]
  rw [Mach.runFrom_dead _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)]
  simp

/-- The run of the second machine on the input `L 1`. -/
theorem consMach2_run_left (u : Ty.one.Elt) :
    consMach2.run ((consDom A).height) .t0 ((consDom A).repr (Sum.inl u)) = [Sym8.rbrack] := by
  show consMach2.runFrom ((consDom A).height) (Cons2Mode.t0, 0) (Sym8.left :: [Sym8.one])
    = [Sym8.rbrack]
  rw [Mach.runFrom_cons, Mach.runFrom_cons]
  simp only [consMach2_out_t0, consMach2_step_t0_left, consMach2_out_tL, consMach2_step_tL]
  simp

private lemma consMach1_copies_sA : consMach1.Copies .sA (c1 A).1 (fun c => [c]) := by
  intro e c _ htr
  have hne : ¬ (e = 1 ∧ c = Sym8.comma) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  exact ⟨by simp only [consMach1, hne, if_false], by simp only [consMach1, hne, if_false]⟩

private lemma consMach2_erases_tA : consMach2.Copies .tA (c1 A).1 (fun _ => []) := by
  intro e c _ htr
  have hne : ¬ (e = 1 ∧ c = Sym8.comma) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  exact ⟨by simp only [consMach2, hne, if_false], rfl⟩

private lemma consMach2_copies_tBody : consMach2.Copies .tBody (c2 A).1 (fun c => [c]) := by
  intro e c _ htr
  have hne : ¬ (e = 2 ∧ c = Sym8.rbrack) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  exact ⟨by simp only [consMach2, hne, if_false], by simp only [consMach2, hne, if_false]⟩

private lemma consMach2_comma_tBody : consMach2.CopiesComma .tBody (c2 A).1 (fun c => [c]) :=
  ⟨rfl, rfl⟩

/-- The run of the first machine on the input `R (a,l)`, up to the tail. -/
theorem consMach1_run_right (a : A.Elt) (l : List A.Elt) :
    consMach1.run ((consDom A).height) .s0 ((consDom A).repr (Sum.inr (a, l)))
      = Sym8.lbrack :: (A.repr a ++ (match l with | [] => [] | _ :: _ => [Sym8.comma])) := by
  show consMach1.runFrom ((consDom A).height) (ConsMode.s0, 0)
      (Sym8.right :: (Sym8.lpar :: (A.repr a ++ Sym8.comma ::
        ((Ty.list A).repr l ++ [Sym8.rpar])))) = _
  rw [Mach.runFrom_cons]
  simp only [consMach1_out_s0, consMach1_step_s0_right,
    dstep_neutral (by simp : wt Sym8.right = 0)]
  rw [Mach.runFrom_cons]
  simp only [consMach1_out_sOpen, consMach1_step_sOpen, dstep_c0_lpar, List.nil_append]
  rw [Mach.runFrom_repr _ _ _ (fun c => [c]) A a (c1 A) _ (consCapA A) (consMach1_copies_sA A),
    flatten_map_single, Mach.runFrom_cons]
  simp only [c1_val, consMach1_out_sA_comma, consMach1_step_sA_comma,
    dstep_neutral (by simp : wt Sym8.comma = 0), List.nil_append]
  have hlist : (Ty.list A).repr l ++ [Sym8.rpar]
      = Sym8.lbrack :: (joinSep (l.map A.repr) ++ [Sym8.rbrack] ++ [Sym8.rpar]) := by
    simp [Ty.repr]
  rw [hlist, Mach.runFrom_cons]
  simp only [consMach1_out_sBrack, consMach1_step_sBrack, dstep_c1_lbrack, List.nil_append]
  cases l with
  | nil =>
      simp only [List.map_nil, joinSep_nil, List.nil_append, List.cons_append]
      rw [Mach.runFrom_cons]
      simp only [consMach1_step_sPend]
      rw [Mach.runFrom_dead _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)]
      simp [consMach1]
  | cons a2 l2 =>
      obtain ⟨c, w, hcw, hc⟩ := repr_eq_cons A a2
      have hbody : joinSep ((a2 :: l2).map A.repr) ++ [Sym8.rbrack] ++ [Sym8.rpar]
          = c :: (w ++ joinSepTail A l2 ++ [Sym8.rbrack] ++ [Sym8.rpar]) := by
        rw [joinSep_cons, hcw]
        simp
      rw [hbody, Mach.runFrom_cons]
      simp only [consMach1_step_sPend]
      rw [Mach.runFrom_dead _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)]
      have hcne : c ≠ Sym8.rbrack := by rintro rfl; simp [transparent] at hc
      simp [consMach1, hcne]

/-- The run of the second machine on the input `R (a,l)`. -/
theorem consMach2_run_right (a : A.Elt) (l : List A.Elt) :
    consMach2.run ((consDom A).height) .t0 ((consDom A).repr (Sum.inr (a, l)))
      = joinSep (l.map A.repr) ++ [Sym8.rbrack] := by
  show consMach2.runFrom ((consDom A).height) (Cons2Mode.t0, 0)
      (Sym8.right :: (Sym8.lpar :: (A.repr a ++ Sym8.comma ::
        ((Ty.list A).repr l ++ [Sym8.rpar])))) = _
  rw [Mach.runFrom_cons]
  simp only [consMach2_out_t0, consMach2_step_t0_right,
    dstep_neutral (by simp : wt Sym8.right = 0), List.nil_append]
  rw [Mach.runFrom_cons]
  simp only [consMach2_out_tOpen, consMach2_step_tOpen, dstep_c0_lpar, List.nil_append]
  rw [Mach.runFrom_repr _ _ _ (fun _ => []) A a (c1 A) _ (consCapA A) (consMach2_erases_tA A)]
  simp only [flatten_map_nil, List.nil_append]
  rw [Mach.runFrom_cons]
  simp only [c1_val, consMach2_out_tA, consMach2_step_tA_comma,
    dstep_neutral (by simp : wt Sym8.comma = 0), List.nil_append]
  have hlist : (Ty.list A).repr l ++ [Sym8.rpar]
      = Sym8.lbrack :: (joinSep (l.map A.repr) ++ ([Sym8.rbrack] ++ [Sym8.rpar])) := by
    simp [Ty.repr]
  rw [hlist, Mach.runFrom_cons]
  simp only [consMach2_out_tBrack, consMach2_step_tBrack, dstep_c1_lbrack, List.nil_append]
  rw [Mach.runFrom_joinSep _ _ _ (fun c => [c]) A (c2 A) (consCapA2 A) (consMach2_copies_tBody A)
    (consMach2_comma_tBody A) l _, flatten_map_single]
  rw [List.singleton_append, Mach.runFrom_cons]
  simp only [c2_val, consMach2_out_tBody_rbrack, consMach2_step_tBody_rbrack]
  rw [Mach.runFrom_dead _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)]
  simp

/-- **The list constructor is regular under string representation.** -/
theorem isRegularUnderRepr_cons :
    IsRegularUnderRepr (A := consDom A) (B := Ty.list A)
      (fun x => Sum.elim (fun _ => []) (fun p => p.1 :: p.2) x) := by
  refine ⟨fun w => consMach1.run ((consDom A).height) .s0 w
      ++ consMach2.run ((consDom A).height) .t0 w,
    isRegularFun_concat (consMach1.isRegularFun_run _ _) (consMach2.isRegularFun_run _ _), ?_⟩
  rintro (u | ⟨a, l⟩)
  · dsimp only
    rw [consMach1_run_left, consMach2_run_left]
    simp [Ty.repr]
  · dsimp only
    rw [consMach1_run_right, consMach2_run_right]
    cases l with
    | nil => simp [Ty.repr]
    | cons a2 l2 =>
        show Sym8.lbrack :: (A.repr a ++ [Sym8.comma])
            ++ (joinSep ((a2 :: l2).map A.repr) ++ [Sym8.rbrack])
          = (Ty.list A).repr (a :: a2 :: l2)
        rw [Ty.repr_list]
        simp only [List.map_cons]
        rw [joinSep_cons_cons]
        simp

end Cons

/-! ## The list deconstructor -/

/-- The modes of the machine of the list deconstructor. -/
inductive UnconsMode | start | pend | copy1 | rest | dead
  deriving DecidableEq, Fintype

/-- The machine of the list deconstructor: it waits for the letter after the opening bracket to
decide whether the list is empty, and then copies the head and the tail. -/
def unconsMach : Mach UnconsMode Sym8 where
  step := fun m e c => match m with
    | .start => .pend
    | .pend => if c = Sym8.rbrack then .dead else .copy1
    | .copy1 => if e = 1 ∧ (c = Sym8.comma ∨ c = Sym8.rbrack) then
        (if c = Sym8.comma then .rest else .dead) else .copy1
    | .rest => if e = 1 ∧ c = Sym8.rbrack then .dead else .rest
    | .dead => .dead
  out := fun m e c => match m with
    | .start => []
    | .pend => if c = Sym8.rbrack then [Sym8.left, Sym8.one] else [Sym8.right, Sym8.lpar, c]
    | .copy1 => if e = 1 ∧ c = Sym8.comma then [Sym8.comma, Sym8.lbrack]
        else if e = 1 ∧ c = Sym8.rbrack then [Sym8.comma, Sym8.lbrack, Sym8.rbrack, Sym8.rpar]
        else [c]
    | .rest => if e = 1 ∧ c = Sym8.rbrack then [Sym8.rbrack, Sym8.rpar] else [c]
    | .dead => []
  fin := fun _ _ => []

@[simp] lemma unconsMach_out_start (e : ℕ) (c : Sym8) : unconsMach.out .start e c = [] := rfl
@[simp] lemma unconsMach_step_start (e : ℕ) (c : Sym8) : unconsMach.step .start e c = .pend := rfl
@[simp] lemma unconsMach_out_dead (e : ℕ) (c : Sym8) : unconsMach.out .dead e c = [] := rfl
@[simp] lemma unconsMach_step_dead (e : ℕ) (c : Sym8) : unconsMach.step .dead e c = .dead := rfl
@[simp] lemma unconsMach_fin (m : UnconsMode) (e : ℕ) : unconsMach.fin m e = [] := rfl

section Uncons

variable (A : Ty)

lemma listHeight : (Ty.list A).height = A.height + 1 := by
  rw [Ty.height]; omega

/-- The counter at depth `1`, inside the brackets of the input list. -/
def u1 : Fin ((Ty.list A).height + 1) := ⟨1, by rw [listHeight]; omega⟩

@[simp] lemma u1_val : (u1 A).1 = 1 := rfl

lemma dstep_u0_lbrack : dstep (0 : Fin ((Ty.list A).height + 1)) Sym8.lbrack = u1 A := by
  refine Fin.ext ?_
  rw [dstep_open (by simp) (by simp only [Fin.val_zero]; rw [listHeight]; omega)]
  rfl

lemma unconsCap : (1 : ℤ) + (A.height : ℤ) ≤ ((Ty.list A).height : ℤ) := by
  rw [listHeight]; push_cast; omega

private lemma uncons_copies_copy1 : unconsMach.Copies .copy1 (u1 A).1 (fun c => [c]) := by
  intro e c _ htr
  have hnc : ¬ (e = 1 ∧ c = Sym8.comma) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  have hnb : ¬ (e = 1 ∧ c = Sym8.rbrack) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  have hno : ¬ (e = 1 ∧ (c = Sym8.comma ∨ c = Sym8.rbrack)) := by
    rintro ⟨rfl, (rfl | rfl)⟩
    · exact absurd (htr rfl) (by simp [transparent])
    · exact absurd (htr rfl) (by simp [transparent])
  exact ⟨by simp only [unconsMach, hno, if_false],
    by simp only [unconsMach, hnc, hnb, if_false]⟩

private lemma uncons_copies_rest : unconsMach.Copies .rest (u1 A).1 (fun c => [c]) := by
  intro e c _ htr
  have hnb : ¬ (e = 1 ∧ c = Sym8.rbrack) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  exact ⟨by simp only [unconsMach, hnb, if_false], by simp only [unconsMach, hnb, if_false]⟩

private lemma uncons_comma_rest : unconsMach.CopiesComma .rest (u1 A).1 (fun c => [c]) :=
  ⟨rfl, rfl⟩

/-- **The list deconstructor is regular under string representation.** -/
theorem unconsMach_run (l : List A.Elt) :
    unconsMach.run ((Ty.list A).height) .start ((Ty.list A).repr l)
      = (Ty.sum Ty.one (Ty.prod A (Ty.list A))).repr
          (match l with | [] => Sum.inl () | a :: l' => Sum.inr (a, l')) := by
  show unconsMach.runFrom ((Ty.list A).height) (UnconsMode.start, 0)
      (Sym8.lbrack :: (joinSep (l.map A.repr) ++ [Sym8.rbrack])) = _
  rw [Mach.runFrom_cons]
  simp only [unconsMach_out_start, unconsMach_step_start, dstep_u0_lbrack, List.nil_append]
  cases l with
  | nil =>
      simp only [List.map_nil, joinSep_nil, List.nil_append]
      rw [Mach.runFrom_cons]
      simp only [u1_val]
      rw [show unconsMach.step .pend 1 Sym8.rbrack = UnconsMode.dead from rfl,
        show unconsMach.out .pend 1 Sym8.rbrack = [Sym8.left, Sym8.one] from rfl,
        Mach.runFrom_dead _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)]
      simp [Ty.repr]
  | cons a l' =>
      obtain ⟨c, w, hcw, hc⟩ := repr_eq_cons A a
      have hcne : c ≠ Sym8.rbrack := by rintro rfl; simp [transparent] at hc
      rw [joinSep_cons, List.append_assoc]
      rw [Mach.runFrom_repr_cons _ _ _ _ (fun c => [c]) A a c w hcw (u1 A) _ (unconsCap A)
        (by simp only [u1_val]; simp only [unconsMach, hcne, if_false]) (uncons_copies_copy1 A)]
      simp only [u1_val, flatten_map_single]
      rw [show unconsMach.out .pend 1 c = [Sym8.right, Sym8.lpar, c] from by
        simp only [unconsMach, hcne, if_false]]
      cases l' with
      | nil =>
          simp only [joinSepTail_nil, List.nil_append]
          rw [Mach.runFrom_cons]
          simp only [u1_val]
          rw [show unconsMach.step .copy1 1 Sym8.rbrack = UnconsMode.dead from rfl,
            show unconsMach.out .copy1 1 Sym8.rbrack
              = [Sym8.comma, Sym8.lbrack, Sym8.rbrack, Sym8.rpar] from rfl,
            Mach.runFrom_dead _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)]
          simp [Ty.repr, hcw]
      | cons a2 l2 =>
          rw [joinSepTail_cons,
            show (Sym8.comma :: joinSep ((a2 :: l2).map A.repr)) ++ [Sym8.rbrack]
              = Sym8.comma :: (joinSep ((a2 :: l2).map A.repr) ++ [Sym8.rbrack]) from rfl,
            Mach.runFrom_cons]
          simp only [u1_val]
          rw [show unconsMach.step .copy1 1 Sym8.comma = UnconsMode.rest from rfl,
            show unconsMach.out .copy1 1 Sym8.comma = [Sym8.comma, Sym8.lbrack] from rfl,
            dstep_neutral (by simp : wt Sym8.comma = 0)]
          rw [Mach.runFrom_joinSep _ _ _ (fun c => [c]) A (u1 A) (unconsCap A)
            (uncons_copies_rest A) (uncons_comma_rest A) (a2 :: l2) _, flatten_map_single]
          rw [Mach.runFrom_cons]
          simp only [u1_val]
          rw [show unconsMach.step .rest 1 Sym8.rbrack = UnconsMode.dead from rfl,
            show unconsMach.out .rest 1 Sym8.rbrack = [Sym8.rbrack, Sym8.rpar] from rfl,
            Mach.runFrom_dead _ _ _ (fun _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)]
          simp [Ty.repr, hcw]

theorem isRegularUnderRepr_uncons :
    IsRegularUnderRepr (A := Ty.list A) (B := Ty.sum Ty.one (Ty.prod A (Ty.list A)))
      (fun l => match l with | [] => Sum.inl () | a :: l' => Sum.inr (a, l')) :=
  ⟨unconsMach.run ((Ty.list A).height) .start, unconsMach.isRegularFun_run _ _,
    fun l => unconsMach_run A l⟩

end Uncons

end Comb
end Lax709149Proofs.Transducers
