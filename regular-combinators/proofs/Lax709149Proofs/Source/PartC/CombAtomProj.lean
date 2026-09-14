/-
The atomic terms that only involve products and co-products -- identity, the two projections, the
two co-projections and distributivity -- are regular under string representation.  Part of the easy
direction of Theorem `thm:regular-terms` of *Transducers* (M. Bojańczyk).

Identity and the co-projections are immediate: under string representation they are the identity
and the prepending of a letter.  The projections are machines of `CombMach.lean`: they copy the
component they keep and erase the other, the two being separated by the unique comma at bracket
depth `1`.

Distributivity is the example the book works through.  It is *not* computed by a machine that reads
the input once from left to right, because its output starts with the letter `L` or `R` according
to a letter that sits in the middle of the input.  It is however the concatenation of two such
machines, one writing the marker `L` or `R` and one writing the pair, and regular functions are
closed under pointwise concatenation (`Transducers.isRegularFun_concat`); this is
`CombAtomDistr.lean`.
-/
import Lax709149Proofs.Source.PartC.CombMach
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax709149Proofs.Transducers
namespace Comb

/-! ## Identity and the co-projections -/

theorem isRegularUnderRepr_id (A : Ty) : IsRegularUnderRepr (fun x : A.Elt => x) :=
  ⟨fun w => w, isRegularFun_id, fun _ => rfl⟩

theorem isRegularUnderRepr_inl (A B : Ty) :
    IsRegularUnderRepr (A := A) (B := Ty.sum A B) (fun a => Sum.inl a) :=
  ⟨fun w => Sym8.left :: w, IsRegularFun.of_rational (isRationalFun_cons _), fun _ => rfl⟩

theorem isRegularUnderRepr_inr (A B : Ty) :
    IsRegularUnderRepr (A := B) (B := Ty.sum A B) (fun b => Sum.inr b) :=
  ⟨fun w => Sym8.right :: w, IsRegularFun.of_rational (isRationalFun_cons _), fun _ => rfl⟩

/-! ## The modes of a machine reading a pair -/

/-- The modes of the machines that read a pair: before the opening bracket, inside the first
component, inside the second one, and after the closing bracket. -/
inductive PMode | start | inA | inB | stop
  deriving DecidableEq, Fintype

/-! ## The projections -/

/-- The machine of the first projection: it copies the first component and erases the second. -/
def fstMach : Mach PMode Sym8 where
  step := fun m e c => match m with
    | .start => .inA
    | .inA => if e = 1 ∧ c = Sym8.comma then .inB else .inA
    | .inB => if e = 1 ∧ c = Sym8.rpar then .stop else .inB
    | .stop => .stop
  out := fun m e c => match m with
    | .start => []
    | .inA => if e = 1 ∧ c = Sym8.comma then [] else [c]
    | .inB => []
    | .stop => []
  fin := fun _ _ => []

/-- The machine of the second projection: it erases the first component and copies the second. -/
def sndMach : Mach PMode Sym8 where
  step := fun m e c => match m with
    | .start => .inA
    | .inA => if e = 1 ∧ c = Sym8.comma then .inB else .inA
    | .inB => if e = 1 ∧ c = Sym8.rpar then .stop else .inB
    | .stop => .stop
  out := fun m e c => match m with
    | .start => []
    | .inA => []
    | .inB => if e = 1 ∧ c = Sym8.rpar then [] else [c]
    | .stop => []
  fin := fun _ _ => []

@[simp] lemma fstMach_step_start (e : ℕ) (c : Sym8) : fstMach.step .start e c = .inA := rfl
@[simp] lemma fstMach_out_start (e : ℕ) (c : Sym8) : fstMach.out .start e c = [] := rfl
@[simp] lemma fstMach_step_inA_comma : fstMach.step .inA 1 Sym8.comma = .inB := rfl
@[simp] lemma fstMach_out_inA_comma : fstMach.out .inA 1 Sym8.comma = [] := rfl
@[simp] lemma fstMach_step_inB_rpar : fstMach.step .inB 1 Sym8.rpar = .stop := rfl
@[simp] lemma fstMach_out_inB (e : ℕ) (c : Sym8) : fstMach.out .inB e c = [] := rfl
@[simp] lemma fstMach_fin (m : PMode) (e : ℕ) : fstMach.fin m e = [] := rfl

@[simp] lemma sndMach_step_start (e : ℕ) (c : Sym8) : sndMach.step .start e c = .inA := rfl
@[simp] lemma sndMach_out_start (e : ℕ) (c : Sym8) : sndMach.out .start e c = [] := rfl
@[simp] lemma sndMach_step_inA_comma : sndMach.step .inA 1 Sym8.comma = .inB := rfl
@[simp] lemma sndMach_out_inA (e : ℕ) (c : Sym8) : sndMach.out .inA e c = [] := rfl
@[simp] lemma sndMach_step_inB_rpar : sndMach.step .inB 1 Sym8.rpar = .stop := rfl
@[simp] lemma sndMach_out_inB_rpar : sndMach.out .inB 1 Sym8.rpar = [] := rfl
@[simp] lemma sndMach_fin (m : PMode) (e : ℕ) : sndMach.fin m e = [] := rfl

section Proj

variable (A B : Ty)

lemma height_prod_pos : 1 ≤ (Ty.prod A B).height := by
  rw [Ty.height]; omega

lemma capA : (1 : ℤ) + (A.height : ℤ) ≤ ((Ty.prod A B).height : ℤ) := by
  have : A.height ≤ max A.height B.height := Nat.le_max_left _ _
  rw [Ty.height]
  push_cast
  omega

lemma capB : (1 : ℤ) + (B.height : ℤ) ≤ ((Ty.prod A B).height : ℤ) := by
  have : B.height ≤ max A.height B.height := Nat.le_max_right _ _
  rw [Ty.height]
  push_cast
  omega

/-- The state of the counter at depth `1`, inside the brackets of a pair. -/
def d1 : Fin ((Ty.prod A B).height + 1) := ⟨1, by have := height_prod_pos A B; omega⟩

@[simp] lemma d1_val : (d1 A B).1 = 1 := rfl

lemma dstep_zero_lpar :
    dstep (0 : Fin ((Ty.prod A B).height + 1)) Sym8.lpar = d1 A B := by
  refine Fin.ext ?_
  rw [dstep_open (by simp) (by have := height_prod_pos A B; simpa using this)]
  rfl

theorem fstMach_run (a : A.Elt) (b : B.Elt) :
    fstMach.run ((Ty.prod A B).height) .start ((Ty.prod A B).repr (a, b)) = A.repr a := by
  have hcopyA : ∀ e c, (d1 A B).1 ≤ e → (e = (d1 A B).1 → transparent c = true) →
      fstMach.step .inA e c = .inA ∧ fstMach.out .inA e c = [c] := by
    intro e c _ htr
    have hne : ¬ (e = 1 ∧ c = Sym8.comma) := by
      rintro ⟨rfl, rfl⟩
      exact absurd (htr rfl) (by simp [transparent])
    exact ⟨by simp only [fstMach, hne, if_false], by simp only [fstMach, hne, if_false]⟩
  have heraseB : ∀ e c, (d1 A B).1 ≤ e → (e = (d1 A B).1 → transparent c = true) →
      fstMach.step .inB e c = .inB ∧ fstMach.out .inB e c = (fun _ => ([] : List Sym8)) c := by
    intro e c _ htr
    have hne : ¬ (e = 1 ∧ c = Sym8.rpar) := by
      rintro ⟨rfl, rfl⟩
      exact absurd (htr rfl) (by simp [transparent])
    exact ⟨by simp only [fstMach, hne, if_false], rfl⟩
  show fstMach.runFrom ((Ty.prod A B).height) (PMode.start, 0)
      (Sym8.lpar :: (A.repr a ++ Sym8.comma :: (B.repr b ++ [Sym8.rpar]))) = A.repr a
  rw [Mach.runFrom_cons]
  simp only [fstMach_out_start, fstMach_step_start, dstep_zero_lpar, List.nil_append]
  rw [Mach.runFrom_repr _ _ _ (fun c => [c]) A a (d1 A B) _ (capA A B) hcopyA,
    flatten_map_single, Mach.runFrom_cons]
  simp only [d1_val, fstMach_out_inA_comma, fstMach_step_inA_comma,
    dstep_neutral (by simp : wt Sym8.comma = 0), List.nil_append]
  rw [Mach.runFrom_repr _ _ _ (fun _ => []) B b (d1 A B) _ (capB A B) heraseB]
  simp

theorem sndMach_run (a : A.Elt) (b : B.Elt) :
    sndMach.run ((Ty.prod A B).height) .start ((Ty.prod A B).repr (a, b)) = B.repr b := by
  have heraseA : ∀ e c, (d1 A B).1 ≤ e → (e = (d1 A B).1 → transparent c = true) →
      sndMach.step .inA e c = .inA ∧ sndMach.out .inA e c = (fun _ => ([] : List Sym8)) c := by
    intro e c _ htr
    have hne : ¬ (e = 1 ∧ c = Sym8.comma) := by
      rintro ⟨rfl, rfl⟩
      exact absurd (htr rfl) (by simp [transparent])
    exact ⟨by simp only [sndMach, hne, if_false], rfl⟩
  have hcopyB : ∀ e c, (d1 A B).1 ≤ e → (e = (d1 A B).1 → transparent c = true) →
      sndMach.step .inB e c = .inB ∧ sndMach.out .inB e c = [c] := by
    intro e c _ htr
    have hne : ¬ (e = 1 ∧ c = Sym8.rpar) := by
      rintro ⟨rfl, rfl⟩
      exact absurd (htr rfl) (by simp [transparent])
    exact ⟨by simp only [sndMach, hne, if_false], by simp only [sndMach, hne, if_false]⟩
  show sndMach.runFrom ((Ty.prod A B).height) (PMode.start, 0)
      (Sym8.lpar :: (A.repr a ++ Sym8.comma :: (B.repr b ++ [Sym8.rpar]))) = B.repr b
  rw [Mach.runFrom_cons]
  simp only [sndMach_out_start, sndMach_step_start, dstep_zero_lpar, List.nil_append]
  rw [Mach.runFrom_repr _ _ _ (fun _ => []) A a (d1 A B) _ (capA A B) heraseA]
  simp only [List.map_const', List.flatten_replicate_nil, List.nil_append]
  rw [Mach.runFrom_cons]
  simp only [d1_val, sndMach_out_inA, sndMach_step_inA_comma,
    dstep_neutral (by simp : wt Sym8.comma = 0), List.nil_append]
  rw [Mach.runFrom_repr _ _ _ (fun c => [c]) B b (d1 A B) _ (capB A B) hcopyB,
    flatten_map_single, Mach.runFrom_cons]
  simp

theorem isRegularUnderRepr_fst :
    IsRegularUnderRepr (fun x : (Ty.prod A B).Elt => x.1) :=
  ⟨fstMach.run ((Ty.prod A B).height) .start,
    fstMach.isRegularFun_run _ _, fun x => fstMach_run A B x.1 x.2⟩

theorem isRegularUnderRepr_snd :
    IsRegularUnderRepr (fun x : (Ty.prod A B).Elt => x.2) :=
  ⟨sndMach.run ((Ty.prod A B).height) .start,
    sndMach.isRegularFun_run _ _, fun x => sndMach_run A B x.1 x.2⟩

end Proj

end Comb
end Lax709149Proofs.Transducers
