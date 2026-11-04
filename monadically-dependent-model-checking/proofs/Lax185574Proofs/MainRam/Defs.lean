import Lax185574Proofs.LegacyInstance
import Lax710763.MonadicDependence
import Lax808846.RamComputes
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Lax185574.FewTypes
import Lax185574.ConstructionModelChecking
import Lax185574Proofs.RamPipeBack
import Lax185574Proofs.RamPipeFwd
import Lax185574Proofs.RamDovetail
import Lax185574Proofs.Compose.Basic
import Lax185574Proofs.LegacyInputs

/-!
The program of thm:main: definitions. Thread `i` of a dovetailer runs
`threadProg` on `i :: x`. The thread unpairs `i` into `(r, d, j)`, runs
the program of thm:skel-few-types with `ε = 1/j`, clips the entries of
its output, validates the clipped word as a construction script of the
input graph, runs the program of thm:mc on the validated instance, and
writes the flag of the validation followed by the answer. The thread
accepts exactly when the validation succeeds.

The glue programs are given by their specifications here, so that the
composition can be checked independently of their code.
-/

namespace Lax185574Proofs.MainRam

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate
open Lax185574Proofs.RamSim
open Lax3.FirstOrder Lax271696.GraphEncoding Lax185574.WordEncoding Lax185574.SequenceEncoding
open Lax185574.ConstructionSequences Lax185574.PartialGraphs Lax185574.InstanceEncoding

/-! ### The numbers of a thread -/

/-- The radius of thread `i`. -/
def triR (i : ℕ) : ℕ := (Nat.unpair (Nat.unpair i).1).1

/-- The depth of thread `i`. -/
def triD (i : ℕ) : ℕ := (Nat.unpair (Nat.unpair i).1).2

/-- The denominator of `ε` of thread `i`, at least one. -/
def triJ (i : ℕ) : ℕ := (Nat.unpair i).2 + 1

/-- The thread with the numbers `r`, `d` and `j ≥ 1`. -/
def triIdx (r d j : ℕ) : ℕ := Nat.pair (Nat.pair r d) (j - 1)

theorem tri_idx (r d j : ℕ) (hj : 1 ≤ j) :
    triR (triIdx r d j) = r ∧ triD (triIdx r d j) = d ∧ triJ (triIdx r d j) = j := by
  simp only [triR, triD, triJ, triIdx, Nat.unpair_pair]
  exact ⟨trivial, trivial, by omega⟩

/-- The word written by the unpairing program: `r, d` and the word of
`1/j`. -/
def triWord (i : ℕ) : List ℕ := [triR i, triD i, 0, 1, triJ i]

theorem triWord_eq (i : ℕ) (g : List ℕ) :
    triWord i ++ g = toWord (triR i, triD i, ((triJ i : ℚ))⁻¹) ++ g := by
  have hj : 0 < triJ i := by simp only [triJ]; omega
  change _ = triR i :: triD i :: (toWord (((triJ i : ℚ))⁻¹.num, ((triJ i : ℚ))⁻¹.den) ++ g)
  rw [Rat.inv_natCast_num_of_pos hj, Rat.inv_natCast_den_of_pos hj]
  rfl

/-! ### Rewrites -/

/-- The input itself. -/
def ρid : Rewrite 1 := [.slice 0 (.lit 0) none]

/-- The output of the first program. -/
def ρout : Rewrite 2 := [.slice 0 (.lit 0) none]

/-- The input of the program of thm:skel-few-types: the output of the
unpairing program, then the graph block of `i :: x`, whose length is
`3 + n + 2E` by its header. -/
def ρU : Rewrite 2 :=
  [.slice 0 (.lit 0) none,
   .slice 1 (.lit 1) (some (.add (.lit 3) (.add (.entry 1 1) (.mul (.lit 2) (.entry 1 2)))))]

/-- The input of the second half of a thread: the length of the
script, the length of `i :: x`, the script, and `x`. -/
def ρQ : Rewrite 2 :=
  [.expr (.len 0), .expr (.len 1), .slice 0 (.lit 0) none, .slice 1 (.lit 1) none]

/-- Drop the flag. -/
def ρdrop : Rewrite 1 := [.slice 0 (.lit 1) none]

/-- The flag, then the output of the model-checking program. -/
def ρW : Rewrite 2 := [.expr (.entry 1 0), .slice 0 (.lit 0) none]

/-! ### Clipping and validation -/

/-- The clipped list: every entry reduced to `v` bits and then capped
at the length of the list. -/
def clipList (v : ℕ) (u : List ℕ) : List ℕ := u.map fun a => min (a % 2 ^ v) u.length

/-- The word `y` is the word of a script on `n` vertices whose run is a
construction sequence of `G`. -/
def ValidScript (n : ℕ) (G : SimpleGraph (Fin n)) (y : List ℕ) : Prop :=
  ∃ σ : Script n, y = toWord σ ∧ IsConstructionSequence G σ.run

/-- The word of the graph without vertices and of its script without
steps. -/
def dummyWord : List ℕ := [0, 0, 0, 0, 0]

open Classical in
/-- The output of the validation: the flag `1` and the instance of
thm:mc, or the flag `0` and an instance on the empty graph. -/
noncomputable def vOut (n : ℕ) (G : SimpleGraph (Fin n)) (φ : FO 0) (g y : List ℕ) : List ℕ :=
  if ValidScript n G y then 1 :: (g ++ y ++ toWord φ) else 0 :: (dummyWord ++ toWord φ)

/-! ### Specifications of the glue programs -/

/-- The unpairing program. -/
def UnpairSpec (U : Program) (c : ℕ) : Prop :=
  ∀ (w i : ℕ) (x : List ℕ), (∀ v ∈ i :: x, c * (i + v + 2) ^ 2 ≤ 2 ^ w) →
    ∃ t ≤ c * (i + 2) ^ 2, RunsTo w U (i :: x) (triWord i) t

/-- The clipping program. -/
def ClipSpec (Cl : Program) (c : ℕ) : Prop :=
  ∀ (v : ℕ) (u : List ℕ), 4 ≤ v → u.length < 2 ^ v →
    ∃ t ≤ c * (u.length + 1), RunsTo v Cl u (clipList v u) t

/-- The validation program. Its input is the length of the script, the
length of `x` plus one, the script and `x`. -/
def ValidSpec (V : Program) (c : ℕ) : Prop :=
  ∀ (v n : ℕ) (G : SimpleGraph (Fin n)) (φ : FO 0) (g y : List ℕ),
    EncodesGraph g n G → (∀ a ∈ y, a ≤ y.length + (g ++ toWord φ).length + 2) →
    c * (y.length + (g ++ toWord φ).length + 2) ^ 2 ≤ 2 ^ v →
    ∃ t ≤ c * ((y.length + 1) * (n + 1) ^ 2 + (g ++ toWord φ).length + 1),
      RunsTo v V (y.length :: ((g ++ toWord φ).length + 1) :: (y ++ (g ++ toWord φ)))
        (vOut n G φ g y) t

/-- The output program: it copies its two entries. -/
def WrapSpec (Wr : Program) (c : ℕ) : Prop :=
  ∀ (v a b : ℕ), 4 ≤ v → a ≤ 1 → b ≤ 1 → ∃ t ≤ c, RunsTo v Wr [a, b] [a, b] t

/-! ### The thread program -/

section prog

variable (U FT Cl V M Wr : Program)

/-- Unpair, then the program of thm:skel-few-types. -/
def firstHalf : Program := pipeProg U FT ρid ρU

/-- The model-checking program on the instance, then the output. -/
def lastQuarter : Program := pipeProg M Wr ρdrop ρW

/-- Validation, then the last quarter. -/
def secondQuarter : Program := pipeProg V (lastQuarter M Wr) ρid ρout

/-- Clipping, then the rest. -/
def secondHalf : Program := pipeProg Cl (secondQuarter V M Wr) ρid ρout

/-- The thread program. -/
def threadProg : Program := pipeProg (firstHalf U FT) (secondHalf Cl V M Wr) ρid ρQ

end prog

/-! ### Rewrite facts -/

theorem ρid_apply (x : List ℕ) : ρid.apply (fun _ => x) = x := by
  simp [ρid, Rewrite.apply, Segment.apply, HExpr.eval]

theorem ρid_cost (x : List ℕ) : ρid.cost (fun _ => x) = 3 := rfl

theorem ρid_fits {w : ℕ} {x : List ℕ} (hx : x.length < 2 ^ w) : ρid.Fits w (fun _ => x) := by
  refine ⟨fun _ => hx, by rw [ρid_apply]; exact hx, ?_⟩
  intro seg hs
  simp only [ρid, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  exact ⟨trivial, by show 0 < 2 ^ w; positivity⟩

theorem ρout_apply (y x : List ℕ) : ρout.apply ![y, x] = y := by
  simp [ρout, Rewrite.apply, Segment.apply, HExpr.eval]

theorem ρout_cost (y x : List ℕ) : ρout.cost ![y, x] = 3 := rfl

theorem ρout_fits {w : ℕ} {y x : List ℕ} (hy : y.length < 2 ^ w) (hx : x.length < 2 ^ w) :
    ρout.Fits w ![y, x] := by
  refine ⟨fun i => by fin_cases i <;> simpa, by rw [ρout_apply]; exact hy, ?_⟩
  intro seg hs
  simp only [ρout, List.mem_cons, List.not_mem_nil, or_false] at hs
  subst hs
  exact ⟨trivial, by show 0 < 2 ^ w; positivity⟩

theorem ρdrop_apply (a : ℕ) (x : List ℕ) : ρdrop.apply (fun _ => a :: x) = x := by
  simp [ρdrop, Rewrite.apply, Segment.apply, HExpr.eval]

theorem ρdrop_cost (x : List ℕ) : ρdrop.cost (fun _ => x) = 3 := rfl

theorem ρdrop_fits {w : ℕ} {x : List ℕ} (hw : 1 ≤ w) (hx : x.length < 2 ^ w) :
    ρdrop.Fits w (fun _ => x) := by
  refine ⟨fun _ => hx, ?_, ?_⟩
  · simp only [ρdrop, Rewrite.apply, Segment.apply, HExpr.eval, List.map_cons, List.map_nil,
      List.flatten_cons, List.flatten_nil, List.append_nil, List.length_drop]
    omega
  · intro seg hs
    simp only [ρdrop, List.mem_cons, List.not_mem_nil, or_false] at hs
    subst hs
    exact ⟨trivial, by show 1 < 2 ^ w; exact Nat.one_lt_two_pow (by omega)⟩

theorem ρW_apply (z : List ℕ) (a : ℕ) (x : List ℕ) : ρW.apply ![z, a :: x] = a :: z := by
  simp [ρW, Rewrite.apply, Segment.apply, HExpr.eval]

theorem ρW_cost (z x : List ℕ) : ρW.cost ![z, x] = 5 := rfl

theorem ρW_fits {w : ℕ} {z : List ℕ} {a : ℕ} {x : List ℕ} (hw : 1 ≤ w)
    (hz : z.length + 1 < 2 ^ w) (hx : x.length + 1 < 2 ^ w) : ρW.Fits w ![z, a :: x] := by
  refine ⟨fun i => by fin_cases i <;> simp <;> omega, by rw [ρW_apply]; simpa using hz, ?_⟩
  intro seg hs
  simp only [ρW, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact (show 0 < 2 ^ w by positivity)
  · exact ⟨trivial, by show 0 < 2 ^ w; positivity⟩

theorem ρQ_apply (y x : List ℕ) (i : ℕ) :
    ρQ.apply ![y, i :: x] = y.length :: (x.length + 1) :: (y ++ x) := by
  simp [ρQ, Rewrite.apply, Segment.apply, HExpr.eval]

theorem ρQ_cost (y x : List ℕ) : ρQ.cost ![y, x] = 9 := rfl

theorem ρQ_fits {w : ℕ} {y x : List ℕ} {i : ℕ} (hw : 1 ≤ w)
    (h : y.length + x.length + 2 < 2 ^ w) : ρQ.Fits w ![y, i :: x] := by
  refine ⟨fun j => by fin_cases j <;> simp <;> omega, by rw [ρQ_apply]; simp; omega, ?_⟩
  intro seg hs
  simp only [ρQ, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · trivial
  · trivial
  · exact ⟨trivial, by show 0 < 2 ^ w; positivity⟩
  · exact ⟨trivial, by show 1 < 2 ^ w; exact Nat.one_lt_two_pow (by omega)⟩

theorem ρU_apply {g φw : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} (hg : EncodesGraph g n G)
    (z : List ℕ) (i : ℕ) : ρU.apply ![z, i :: (g ++ φw)] = z ++ g := by
  have hl := hg.length_eq
  have h0 : g.getD 0 0 = n := hg.vertexCount_eq
  have h1 : (g ++ φw).getD 0 0 = n := by
    rw [List.getD_append _ _ _ _ (by omega)]; exact h0
  have h2 : (g ++ φw).getD 1 0 = edgeCount g := by
    rw [List.getD_append _ _ _ _ (by omega)]; rfl
  simp only [ρU, Rewrite.apply, Segment.apply, HExpr.eval, List.map_cons, List.map_nil,
    List.flatten_cons, List.flatten_nil, List.append_nil, Matrix.cons_val_zero,
    Matrix.cons_val_one, List.drop_zero, List.getD_cons_succ, h1, h2]
  congr 1
  rw [List.drop_one, List.tail_cons, List.take_append_of_le_length (by omega), List.take_of_length_le
    (by omega)]

theorem ρU_cost (z x : List ℕ) : ρU.cost ![z, x] = 12 := rfl

theorem ρU_fits {w : ℕ} {g φw z : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {i : ℕ}
    (hg : EncodesGraph g n G) (hw : 1 ≤ w) (hz : z.length < 2 ^ w)
    (h : g.length + φw.length + 1 < 2 ^ w) (hzg : z.length + g.length < 2 ^ w) :
    ρU.Fits w ![z, i :: (g ++ φw)] := by
  have hl := hg.length_eq
  have h0 : g.getD 0 0 = n := hg.vertexCount_eq
  have h1 : (g ++ φw).getD 0 0 = n := by
    rw [List.getD_append _ _ _ _ (by omega)]; exact h0
  have h2 : (g ++ φw).getD 1 0 = edgeCount g := by
    rw [List.getD_append _ _ _ _ (by omega)]; rfl
  refine ⟨fun j => by fin_cases j <;> simp <;> omega, by rw [ρU_apply hg]; simpa using hzg, ?_⟩
  intro seg hs
  simp only [ρU, List.mem_cons, List.not_mem_nil, or_false] at hs
  have hw2 : 1 < 2 ^ w := Nat.one_lt_two_pow (by omega)
  have hw3 : 2 < 2 ^ w := by
    rcases Nat.lt_or_ge w 2 with h' | h'
    · have : w = 1 := by omega
      subst this; omega
    · calc 2 < 2 ^ 2 := by norm_num
        _ ≤ 2 ^ w := Nat.pow_le_pow_right (by norm_num) h'
  rcases hs with rfl | rfl
  · exact ⟨trivial, by show 0 < 2 ^ w; positivity⟩
  · refine ⟨trivial, hw2, ⟨trivial, hw2, trivial, hw3⟩, ?_⟩
    simp only [HExpr.eval, Matrix.cons_val_one, Matrix.cons_val_zero, Matrix.head_cons,
      List.getD_cons_succ, h1, h2]
    omega

end Lax185574Proofs.MainRam
