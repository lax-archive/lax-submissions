import Lax185574Proofs.RamDoveCode

/-!
The invariant of the dovetailer between slots.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate
open Lax185574Proofs.Ruler

/-- The record of thread `i`. -/
def dvCtx (B i : ℕ) : ℕ := i * dvR B + 40

/-- The memory of thread `i`: `2 ^ (w - K - i)` cells, after those of
the threads before it, in the upper half of memory. -/
def dvBase (w K i : ℕ) : ℕ := 2 ^ (w - 1) + 2 * (2 ^ (w - K) - 2 ^ (w - K - i))

/-- The geometry of thread `i`. -/
def dvGeo (w K B i : ℕ) : Geo := ⟨w - K - i, dvBase w K i, dvCtx B i + 4, B + 1⟩

/-- A suspended thread `i` in state `s`: its record and its memory. -/
structure Saved (w K B : ℕ) (x : List ℕ) (i : ℕ) (S s : State) : Prop where
  pc : S.mem (dvCtx B i) = s.pc
  cur : S.mem (dvCtx B i + 1) ≤ x.length + 1
  inp : s.inp = (i :: x).drop (S.mem (dvCtx B i + 1))
  oc : S.mem (dvCtx B i + 2) = s.out.length
  ocB : s.out.length ≤ B + 1
  alive : S.mem (dvCtx B i + 3) = 0
  buf : ∀ k < s.out.length, S.mem (dvCtx B i + 4 + k) = s.out.getD k 0
  mem : ∀ a < 2 ^ (w - K - i), S.mem (dvBase w K i + a) = s.mem a
  cword : ∀ a, s.mem a < 2 ^ (w - K - i)
  input : s.input = i :: x

/-- Thread `i` after `c` slots: alive in the state reached by `c` steps,
or dead, and then it has no accepting run with a short output. -/
def TInv (w K B : ℕ) (Q : Program) (x : List ℕ) (i c : ℕ) (S : State) : Prop :=
  (∃ s, run (w - i - K) Q c (initState (i :: x)) = some s ∧ (s.pc < Q.length ∨ s.pc = 0) ∧
    Saved w K B x i S s) ∨
  (S.mem (dvCtx B i + 3) ≠ 0 ∧
    ∀ y t, y.length ≤ B → ¬ RunsTo (w - i - K) Q (i :: x) (1 :: y) t)

/-- The scheduler's constants. -/
structure DConst (w K B : ℕ) (x : List ℕ) (S : State) : Prop where
  word : WordMem w S.mem
  zero : S.mem rZ = 0
  one : S.mem rOne = 1
  len0 : S.mem 16 = 1
  len1 : S.mem 18 = x.length
  st1 : S.mem 19 = 0
  tot : S.mem rTot = x.length + 1
  cap : S.mem rCap = B + 1
  wm : S.mem 26 = 2 ^ w - 1
  size0 : S.mem 27 = 2 ^ (w - K)
  half : S.mem 28 = 2 ^ (w - 1)
  two : S.mem 29 = 2
  rsize : S.mem 34 = dvR B
  rbase : S.mem 35 = 40
  kk : S.mem 36 = K
  input : S.input = x
  out : S.out = []

/-- The invariant at the start of slot `j`. -/
structure DInv (w K B : ℕ) (Q : Program) (x : List ℕ) (j : ℕ) (S : State) : Prop where
  const : DConst w K B x S
  pc : S.pc = dvL0
  slot : S.mem 20 = j % 2 ^ w
  pos : 1 ≤ j
  threads : ∀ i, i + K < w → TInv w K B Q x i (count i j) S

/-- The global size conditions. -/
structure DGlob (w K B : ℕ) (Q : Program) (x : List ℕ) : Prop where
  kw : K < w
  k2 : Q.length + 2 ≤ K
  room : 40 + dvR B * w ≤ 2 ^ (w - 1)
  xlen : x.length < 2 ^ (w - 1)

/-! ### Arithmetic -/

theorem two_pow_sub_one_div_two_pow {w a : ℕ} (h : a ≤ w) :
    (2 ^ w - 1) / 2 ^ a = 2 ^ (w - a) - 1 := by
  have e : 2 ^ w = 2 ^ (w - a) * 2 ^ a := by rw [← pow_add]; congr 1; omega
  have h1 : 1 ≤ 2 ^ a := Nat.one_le_two_pow
  have h2 : 1 ≤ 2 ^ (w - a) := Nat.one_le_two_pow
  rw [e]
  apply Nat.div_eq_of_lt_le
  · rw [Nat.sub_mul, one_mul]; omega
  · rw [Nat.sub_add_cancel h2, ← Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr
      (by positivity : 2 ^ (w - a) * 2 ^ a ≠ 0))]
    have : 2 ^ (w - a) * 2 ^ a ≥ 2 ^ (w - a) := Nat.le_mul_of_pos_right _ (by positivity)
    omega

theorem two_pow_le_two_pow_of_le {a b : ℕ} (h : a ≤ b) : 2 ^ a ≤ 2 ^ b :=
  Nat.pow_le_pow_right (by norm_num) h

/-- The memory of thread `i` lies in the upper half, below the memory
of thread `i + 1`. -/
theorem dvBase_bounds {w K i : ℕ} (hK : 2 ≤ K) (hi : i + K < w) :
    2 ^ (w - 1) ≤ dvBase w K i ∧ dvBase w K i + 2 ^ (w - K - i) ≤ 2 ^ w ∧
    dvBase w K i + 2 ^ (w - K - i) ≤ dvBase w K (i + 1) := by
  have a1 : 2 ^ (w - K - i) ≤ 2 ^ (w - K) := two_pow_le_two_pow_of_le (by omega)
  have a2 : 2 ^ (w - K) * 2 ≤ 2 ^ (w - 1) := by
    rw [← pow_succ]; exact two_pow_le_two_pow_of_le (by omega)
  have a3 : 2 ^ w = 2 ^ (w - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  have a4 : 2 ^ (w - K - i) = 2 ^ (w - K - (i + 1)) * 2 := by
    rw [← pow_succ]; congr 1; omega
  have a5 : 2 ^ (w - K - (i + 1)) ≤ 2 ^ (w - K - i) := two_pow_le_two_pow_of_le (by omega)
  simp only [dvBase]
  refine ⟨by omega, by omega, by omega⟩

end Lax185574Proofs.RamSim
