/-
Distributivity is regular under string representation.  This is the case of the easy direction of
Theorem `thm:regular-terms` of *Transducers* (M. Bojańczyk) that the book works through.

The input of `distr` is `(a, L b)` or `(a, R c)`, and the output is `L (a,b)` or `R (a,c)`.  The
delicate point, as the book says, is the parsing: the letter that decides between the two cases
sits after the representation of `a`, whose length is unbounded, whereas the output has to start
with `L` or `R`.  So no machine that reads the input once from left to right computes this
function.  It is however the *concatenation* of two such machines -- one writing the marker, one
writing the pair -- and regular functions are closed under pointwise concatenation.
-/
import Lax709149Proofs.Source.PartC.CombAtomProj
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax709149Proofs.Transducers
namespace Comb

/-! ## The two machines -/

/-- The modes of the machine writing the marker: before the opening bracket, inside the first
component, at the letter `L` or `R`, and after it. -/
inductive MMode | start | inA | atMark | after
  deriving DecidableEq, Fintype

/-- The machine that writes the marker `L` or `R` of the output of `distr`. -/
def markMach : Mach MMode Sym8 where
  step := fun m e c => match m with
    | .start => .inA
    | .inA => if e = 1 ∧ c = Sym8.comma then .atMark else .inA
    | .atMark => .after
    | .after => .after
  out := fun m _e c => match m with
    | .start => []
    | .inA => []
    | .atMark => [c]
    | .after => []
  fin := fun _ _ => []

/-- The modes of the machine writing the pair: before the opening bracket, inside the first
component, at the marker letter, inside the second component, and after the closing bracket. -/
inductive QMode | start | inA | skip | inB | stop
  deriving DecidableEq, Fintype

/-- The machine that writes the pair of the output of `distr`. -/
def pairMach : Mach QMode Sym8 where
  step := fun m e c => match m with
    | .start => .inA
    | .inA => if e = 1 ∧ c = Sym8.comma then .skip else .inA
    | .skip => .inB
    | .inB => if e = 1 ∧ c = Sym8.rpar then .stop else .inB
    | .stop => .stop
  out := fun m e c => match m with
    | .start => [Sym8.lpar]
    | .inA => if e = 1 ∧ c = Sym8.comma then [Sym8.comma] else [c]
    | .skip => []
    | .inB => if e = 1 ∧ c = Sym8.rpar then [Sym8.rpar] else [c]
    | .stop => []
  fin := fun _ _ => []

@[simp] lemma markMach_step_start (e : ℕ) (c : Sym8) : markMach.step .start e c = .inA := rfl
@[simp] lemma markMach_out_start (e : ℕ) (c : Sym8) : markMach.out .start e c = [] := rfl
@[simp] lemma markMach_out_inA (e : ℕ) (c : Sym8) : markMach.out .inA e c = [] := rfl
@[simp] lemma markMach_step_inA_comma : markMach.step .inA 1 Sym8.comma = .atMark := rfl
@[simp] lemma markMach_step_atMark (e : ℕ) (c : Sym8) : markMach.step .atMark e c = .after := rfl
@[simp] lemma markMach_out_atMark (e : ℕ) (c : Sym8) : markMach.out .atMark e c = [c] := rfl
@[simp] lemma markMach_step_after (e : ℕ) (c : Sym8) : markMach.step .after e c = .after := rfl
@[simp] lemma markMach_out_after (e : ℕ) (c : Sym8) : markMach.out .after e c = [] := rfl
@[simp] lemma markMach_fin (m : MMode) (e : ℕ) : markMach.fin m e = [] := rfl

@[simp] lemma pairMach_step_start (e : ℕ) (c : Sym8) : pairMach.step .start e c = .inA := rfl
@[simp] lemma pairMach_out_start (e : ℕ) (c : Sym8) : pairMach.out .start e c = [Sym8.lpar] := rfl
@[simp] lemma pairMach_step_inA_comma : pairMach.step .inA 1 Sym8.comma = .skip := rfl
@[simp] lemma pairMach_out_inA_comma : pairMach.out .inA 1 Sym8.comma = [Sym8.comma] := rfl
@[simp] lemma pairMach_step_skip (e : ℕ) (c : Sym8) : pairMach.step .skip e c = .inB := rfl
@[simp] lemma pairMach_out_skip (e : ℕ) (c : Sym8) : pairMach.out .skip e c = [] := rfl
@[simp] lemma pairMach_step_inB_rpar : pairMach.step .inB 1 Sym8.rpar = .stop := rfl
@[simp] lemma pairMach_out_inB_rpar : pairMach.out .inB 1 Sym8.rpar = [Sym8.rpar] := rfl
@[simp] lemma pairMach_fin (m : QMode) (e : ℕ) : pairMach.fin m e = [] := rfl

/-! ## The run of the two machines -/

section Distr

variable (A B C : Ty)

/-- The type of the input of `distr`. -/
private def dom : Ty := Ty.prod A (Ty.sum B C)

private lemma dom_height_pos : 1 ≤ (dom A B C).height := by
  rw [dom, Ty.height]; omega

/-- The state of the counter at depth `1`. -/
private def e1 : Fin ((dom A B C).height + 1) := ⟨1, by have := dom_height_pos A B C; omega⟩

@[simp] private lemma e1_val : (e1 A B C).1 = 1 := rfl

private lemma dstep_zero_lpar' :
    dstep (0 : Fin ((dom A B C).height + 1)) Sym8.lpar = e1 A B C := by
  refine Fin.ext ?_
  rw [dstep_open (by simp) (by have := dom_height_pos A B C; simpa using this)]
  rfl

private lemma capA' : (1 : ℤ) + (A.height : ℤ) ≤ ((dom A B C).height : ℤ) := by
  have : A.height ≤ max A.height (Ty.sum B C).height := Nat.le_max_left _ _
  rw [dom, Ty.height]
  push_cast
  omega

private lemma capS' : (1 : ℤ) + ((Ty.sum B C).height : ℤ) ≤ ((dom A B C).height : ℤ) := by
  have : (Ty.sum B C).height ≤ max A.height (Ty.sum B C).height := Nat.le_max_right _ _
  rw [dom, Ty.height]
  push_cast
  omega

private lemma mark_copies_inA :
    markMach.Copies .inA (e1 A B C).1 (fun _ => []) := by
  intro e c _ htr
  have hne : ¬ (e = 1 ∧ c = Sym8.comma) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  exact ⟨by simp only [markMach, hne, if_false], rfl⟩

private lemma mark_copies_after :
    markMach.Copies .after (e1 A B C).1 (fun _ => []) := fun _ _ _ _ => ⟨rfl, rfl⟩

private lemma pair_copies_inA :
    pairMach.Copies .inA (e1 A B C).1 (fun c => [c]) := by
  intro e c _ htr
  have hne : ¬ (e = 1 ∧ c = Sym8.comma) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  exact ⟨by simp only [pairMach, hne, if_false], by simp only [pairMach, hne, if_false]⟩

private lemma pair_copies_inB :
    pairMach.Copies .inB (e1 A B C).1 (fun c => [c]) := by
  intro e c _ htr
  have hne : ¬ (e = 1 ∧ c = Sym8.rpar) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  exact ⟨by simp only [pairMach, hne, if_false], by simp only [pairMach, hne, if_false]⟩

theorem markMach_run_inl (a : A.Elt) (b : B.Elt) :
    markMach.run ((dom A B C).height) .start ((dom A B C).repr (a, Sum.inl b)) = [Sym8.left] := by
  show markMach.runFrom ((dom A B C).height) (MMode.start, 0)
      (Sym8.lpar :: (A.repr a ++ Sym8.comma :: ((Ty.sum B C).repr (Sum.inl b) ++ [Sym8.rpar])))
    = [Sym8.left]
  rw [Mach.runFrom_cons]
  simp only [markMach_out_start, markMach_step_start, dstep_zero_lpar', List.nil_append]
  rw [Mach.runFrom_repr _ _ _ (fun _ => []) A a (e1 A B C) _ (capA' A B C) (mark_copies_inA A B C)]
  simp only [flatten_map_nil, List.nil_append]
  rw [Mach.runFrom_cons]
  simp only [e1_val, markMach_out_inA, markMach_step_inA_comma,
    dstep_neutral (by simp : wt Sym8.comma = 0), List.nil_append]
  rw [Mach.runFrom_repr_cons _ _ _ _ (fun _ => []) (Ty.sum B C) (Sum.inl b) Sym8.left (B.repr b)
    rfl (e1 A B C) _ (capS' A B C) (by simp) (mark_copies_after A B C)]
  simp only [e1_val, markMach_out_atMark, flatten_map_nil, List.nil_append]
  rw [Mach.runFrom_cons]
  simp

theorem markMach_run_inr (a : A.Elt) (c : C.Elt) :
    markMach.run ((dom A B C).height) .start ((dom A B C).repr (a, Sum.inr c)) = [Sym8.right] := by
  show markMach.runFrom ((dom A B C).height) (MMode.start, 0)
      (Sym8.lpar :: (A.repr a ++ Sym8.comma :: ((Ty.sum B C).repr (Sum.inr c) ++ [Sym8.rpar])))
    = [Sym8.right]
  rw [Mach.runFrom_cons]
  simp only [markMach_out_start, markMach_step_start, dstep_zero_lpar', List.nil_append]
  rw [Mach.runFrom_repr _ _ _ (fun _ => []) A a (e1 A B C) _ (capA' A B C) (mark_copies_inA A B C)]
  simp only [flatten_map_nil, List.nil_append]
  rw [Mach.runFrom_cons]
  simp only [e1_val, markMach_out_inA, markMach_step_inA_comma,
    dstep_neutral (by simp : wt Sym8.comma = 0), List.nil_append]
  rw [Mach.runFrom_repr_cons _ _ _ _ (fun _ => []) (Ty.sum B C) (Sum.inr c) Sym8.right (C.repr c)
    rfl (e1 A B C) _ (capS' A B C) (by simp) (mark_copies_after A B C)]
  simp only [e1_val, markMach_out_atMark, flatten_map_nil, List.nil_append]
  rw [Mach.runFrom_cons]
  simp

theorem pairMach_run_inl (a : A.Elt) (b : B.Elt) :
    pairMach.run ((dom A B C).height) .start ((dom A B C).repr (a, Sum.inl b))
      = (Ty.prod A B).repr (a, b) := by
  show pairMach.runFrom ((dom A B C).height) (QMode.start, 0)
      (Sym8.lpar :: (A.repr a ++ Sym8.comma :: ((Ty.sum B C).repr (Sum.inl b) ++ [Sym8.rpar])))
    = Sym8.lpar :: (A.repr a ++ Sym8.comma :: (B.repr b ++ [Sym8.rpar]))
  rw [Mach.runFrom_cons]
  simp only [pairMach_out_start, pairMach_step_start, dstep_zero_lpar']
  rw [Mach.runFrom_repr _ _ _ (fun c => [c]) A a (e1 A B C) _ (capA' A B C) (pair_copies_inA A B C),
    flatten_map_single, Mach.runFrom_cons]
  simp only [e1_val, pairMach_out_inA_comma, pairMach_step_inA_comma,
    dstep_neutral (by simp : wt Sym8.comma = 0)]
  rw [Mach.runFrom_repr_cons _ _ _ _ (fun c => [c]) (Ty.sum B C) (Sum.inl b) Sym8.left (B.repr b)
    rfl (e1 A B C) _ (capS' A B C) (by simp) (pair_copies_inB A B C)]
  simp only [e1_val, pairMach_out_skip, flatten_map_single, List.nil_append]
  rw [Mach.runFrom_cons]
  simp

theorem pairMach_run_inr (a : A.Elt) (c : C.Elt) :
    pairMach.run ((dom A B C).height) .start ((dom A B C).repr (a, Sum.inr c))
      = (Ty.prod A C).repr (a, c) := by
  show pairMach.runFrom ((dom A B C).height) (QMode.start, 0)
      (Sym8.lpar :: (A.repr a ++ Sym8.comma :: ((Ty.sum B C).repr (Sum.inr c) ++ [Sym8.rpar])))
    = Sym8.lpar :: (A.repr a ++ Sym8.comma :: (C.repr c ++ [Sym8.rpar]))
  rw [Mach.runFrom_cons]
  simp only [pairMach_out_start, pairMach_step_start, dstep_zero_lpar']
  rw [Mach.runFrom_repr _ _ _ (fun c => [c]) A a (e1 A B C) _ (capA' A B C) (pair_copies_inA A B C),
    flatten_map_single, Mach.runFrom_cons]
  simp only [e1_val, pairMach_out_inA_comma, pairMach_step_inA_comma,
    dstep_neutral (by simp : wt Sym8.comma = 0)]
  rw [Mach.runFrom_repr_cons _ _ _ _ (fun c => [c]) (Ty.sum B C) (Sum.inr c) Sym8.right (C.repr c)
    rfl (e1 A B C) _ (capS' A B C) (by simp) (pair_copies_inB A B C)]
  simp only [e1_val, pairMach_out_skip, flatten_map_single, List.nil_append]
  rw [Mach.runFrom_cons]
  simp

/-- **Distributivity is regular under string representation.** -/
theorem isRegularUnderRepr_distr :
    IsRegularUnderRepr (A := Ty.prod A (Ty.sum B C)) (B := Ty.sum (Ty.prod A B) (Ty.prod A C))
      (fun x => Sum.elim (fun b => Sum.inl (x.1, b)) (fun c => Sum.inr (x.1, c)) x.2) := by
  refine ⟨fun w => markMach.run ((dom A B C).height) .start w
      ++ pairMach.run ((dom A B C).height) .start w,
    isRegularFun_concat (markMach.isRegularFun_run _ _) (pairMach.isRegularFun_run _ _), ?_⟩
  rintro ⟨a, b | c⟩
  · show markMach.run _ _ ((dom A B C).repr (a, Sum.inl b))
      ++ pairMach.run _ _ ((dom A B C).repr (a, Sum.inl b)) = _
    rw [markMach_run_inl, pairMach_run_inl]
    rfl
  · show markMach.run _ _ ((dom A B C).repr (a, Sum.inr c))
      ++ pairMach.run _ _ ((dom A B C).repr (a, Sum.inr c)) = _
    rw [markMach_run_inr, pairMach_run_inr]
    rfl

end Distr

end Comb
end Lax709149Proofs.Transducers
