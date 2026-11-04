import Lax185574Proofs.RamSimBack

/-!
The parallel combinator of two programs: layout and code.

Two programs `P₀` and `P₁` run as threads on the same input, each
simulated at word length `w - K` by the blocks of `RamSimRun` in its own
memory region, with its output in a buffer of two cells. The threads
take turns, one simulated step each. The program counter of the
inactive thread is not stored in memory. It is part of the address of
the code: there is a block for every instruction `i` of the active
thread `b` and every position `o` of the other thread, where `o` equals
the length of the other program once that thread is dead. A switch of
threads saves the cells of the simulation that differ between the
threads (base, cursor, buffer start, output count) and loads those of
the other thread. A halting thread whose output is `1 :: y` with
`y` of length at most one ends the machine with output `y`. Any other
halting thread, and a thread that overflows its buffer, is dead. If
both threads are dead, the machine loops.

Every turn costs a constant number of steps that does not depend on the
programs, which is why the code is a product over pairs of program
counters.
-/

namespace Lax185574Proofs.RamPar

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.RamSim

/-! ### Layout -/

/-- The program of thread `b`. -/
def thr (P₀ P₁ : Program) (b : Bool) : Program := cond b P₁ P₀

/-- The length of the program of thread `b`. -/
def nT (P₀ P₁ : Program) (b : Bool) : ℕ := (thr P₀ P₁ b).length

/-- A bound on both program lengths. -/
def nN (P₀ P₁ : Program) : ℕ := P₀.length + P₁.length + 1

theorem nT_lt (P₀ P₁ : Program) (b : Bool) : nT P₀ P₁ b < nN P₀ P₁ := by
  cases b <;> simp [nT, thr, nN]

/-- The index of the slot of thread `b` at instruction `i`, with the
other thread at `o`. -/
def idx (N : ℕ) (b : Bool) (i o : ℕ) : ℕ := (b.toNat * N + i) * N + o

/-- The length of the initialization. -/
abbrev hH : ℕ := 15

/-- The address of a slot. Slots have length `32`. -/
def slotA (P₀ P₁ : Program) (b : Bool) (i o : ℕ) : ℕ := hH + 32 * idx (nN P₀ P₁) b i o

/-- The save area of the cells of thread `b`. -/
def sv (b : Bool) : ℕ := 40 + 4 * b.toNat

/-- The output buffer of thread `b`. -/
def ob (b : Bool) : ℕ := 48 + 4 * b.toNat

/-- Where thread `b` lives at word length `w`. -/
def geo (w K : ℕ) (b : Bool) : Geo := ⟨w - K, 2 ^ (w - 2) * (b.toNat + 1), ob b, 2⟩

/-- The exit handler of thread `b` with the other thread at `o`. -/
def exitA (P₀ P₁ : Program) (b : Bool) (o : ℕ) : ℕ := slotA P₀ P₁ b (nT P₀ P₁ b) o

/-- The handler of a dead thread. -/
def deadA (P₀ P₁ : Program) (b : Bool) (o : ℕ) : ℕ := exitA P₀ P₁ b o + 13

/-- The compile-time data of the blocks of thread `b` with the other
thread at `o`. Every successor instruction goes to the switch code of
its slot. -/
def code (P₀ P₁ : Program) (b : Bool) (o : ℕ) : Code where
  ks := [.input]
  tb := 16
  mode := .buffer (deadA P₀ P₁ b o)
  tgt := fun l => if l < nT P₀ P₁ b then slotA P₀ P₁ b l o + 23 else exitA P₀ P₁ b o
  exit := exitA P₀ P₁ b o

/-- Copy cells: `d ← s` for every pair, in order. -/
def cpCode (cs : List (ℕ × ℕ)) : Program := cs.map fun c => .add c.1 c.2 0

/-- The memory after the copies. -/
def cpMem : List (ℕ × ℕ) → (ℕ → ℕ) → ℕ → ℕ
  | [], m => m
  | c :: cs, m => cpMem cs (Function.update m c.1 (m c.2))

/-- Save the cells of thread `b`. -/
def svL (b : Bool) : List (ℕ × ℕ) := [(sv b, 3), (sv b + 1, 4), (sv b + 2, 6), (sv b + 3, 7)]

/-- Load the cells of thread `b`. -/
def ldL (b : Bool) : List (ℕ × ℕ) := [(3, sv b), (4, sv b + 1), (6, sv b + 2), (7, sv b + 3)]

/-- The switch code after a step of thread `b` to instruction `l`, with
the other thread at `o`. -/
def stubCode (P₀ P₁ : Program) (b : Bool) (l o : ℕ) : Program :=
  if o < nT P₀ P₁ (!b) then cpCode (svL b ++ ldL (!b)) ++ [.jump (slotA P₀ P₁ (!b) o l)]
  else [.jump (slotA P₀ P₁ b l o)]

/-- The handler of a dead thread `b`: continue with the other thread,
or loop. -/
def deadCode (P₀ P₁ : Program) (b : Bool) (o : ℕ) : Program :=
  if o < nT P₀ P₁ (!b) then cpCode (ldL (!b)) ++ [.jump (slotA P₀ P₁ (!b) o (nT P₀ P₁ b))]
  else [.jump (deadA P₀ P₁ b o)]

/-- The exit handler at address `E`: test whether the buffer holds
`1 :: y` with `y` of length at most one, and if so write `y` and halt. -/
def exitCode (P₀ P₁ : Program) (b : Bool) (o E : ℕ) : Program :=
  [.jzero 7 (E + 13), .load 12 6, .sub 9 12 1, .sub 14 1 12, .add 9 9 14, .jzero 9 (E + 7),
    .jump (E + 13), .sub 14 7 1, .jzero 14 (E + 12), .add 9 6 1, .load 12 9, .write 12, .halt] ++
    deadCode P₀ P₁ b o

/-- The slot at address `A` of thread `b` at `i`, other thread at `o`. -/
def slotCode (P₀ P₁ : Program) (A : ℕ) (b : Bool) (i o : ℕ) : Program :=
  match (thr P₀ P₁ b)[i]? with
  | some ins => pad 23 (instrCode (code P₀ P₁ b o) A i ins) ++ pad 9 (stubCode P₀ P₁ b i o)
  | none => pad 32 (if i = nT P₀ P₁ b then exitCode P₀ P₁ b o A else [])

/-- The constants, the table of the input, and the cells of both
threads. Thread `0` is loaded, the cells of thread `1` are saved. -/
def initCode (K : ℕ) : Program :=
  [.set 1 1, .not 2 0, .set 9 K, .shiftl 10 1 9, .div 2 2 10, .inputLength 5, .set 8 2,
    .add 16 5 0, .not 9 0, .set 10 4, .div 9 9 10, .add 3 9 1, .add 44 3 3, .set 6 48,
    .set 46 52]

@[simp] theorem initCode_length (K : ℕ) : (initCode K).length = hH := rfl

/-- **The parallel combinator.** -/
def parProg (K : ℕ) (P₀ P₁ : Program) : Program :=
  initCode K ++ ((List.range (2 * nN P₀ P₁ * nN P₀ P₁)).map fun k =>
    slotCode P₀ P₁ (hH + 32 * k) (decide (k / nN P₀ P₁ / nN P₀ P₁ = 1)) (k / nN P₀ P₁ % nN P₀ P₁)
      (k % nN P₀ P₁)).flatten

/-! ### Placement -/

theorem blockLen_input : blockLen [SegKind.input] = 23 := rfl

theorem cpCode_length (cs : List (ℕ × ℕ)) : (cpCode cs).length = cs.length := by
  simp [cpCode]

theorem stubCode_length_le (P₀ P₁ : Program) (b : Bool) (l o : ℕ) :
    (stubCode P₀ P₁ b l o).length ≤ 9 := by
  unfold stubCode; split_ifs <;> simp [cpCode, svL, ldL]

theorem exitCode_length_le (P₀ P₁ : Program) (b : Bool) (o E : ℕ) :
    (exitCode P₀ P₁ b o E).length ≤ 32 := by
  unfold exitCode deadCode; split_ifs <;> simp [cpCode, ldL]

theorem slotCode_length (P₀ P₁ : Program) (A : ℕ) (b : Bool) (i o : ℕ) :
    (slotCode P₀ P₁ A b i o).length = 32 := by
  cases h : (thr P₀ P₁ b)[i]? with
  | some ins =>
      have h1 : (instrCode (code P₀ P₁ b o) A i ins).length ≤ 23 := instrCode_length_le _ _ _ _
      have h2 := stubCode_length_le P₀ P₁ b i o
      simp only [slotCode, h]
      rw [List.length_append, pad_length h1, pad_length h2]
  | none =>
      simp only [slotCode, h]
      split_ifs
      · exact pad_length (exitCode_length_le _ _ _ _ _)
      · exact pad_length (by simp)

theorem divmod {N q r : ℕ} (hr : r < N) : (q * N + r) / N = q ∧ (q * N + r) % N = r := by
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hr, Nat.zero_add]
  · rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hr]

theorem idx_lt {N i o : ℕ} (b : Bool) (hi : i < N) (ho : o < N) : idx N b i o < 2 * N * N := by
  have h1 : b.toNat * N + i + 1 ≤ 2 * N := by cases b <;> simp <;> omega
  unfold idx
  calc (b.toNat * N + i) * N + o < (b.toNat * N + i) * N + N := by omega
    _ = (b.toNat * N + i + 1) * N := by ring
    _ ≤ 2 * N * N := Nat.mul_le_mul_right _ h1

theorem pad_fits {p : Program} {A L : ℕ} {c : Program} (h : Fits p A (pad L c)) : Fits p A c :=
  (fits_append.1 h).1

variable {K : ℕ} {P₀ P₁ : Program}

theorem slot_fits {b : Bool} {i o : ℕ} (hi : i < nN P₀ P₁) (ho : o < nN P₀ P₁) :
    Fits (parProg K P₀ P₁) (slotA P₀ P₁ b i o) (slotCode P₀ P₁ (slotA P₀ P₁ b i o) b i o) := by
  intro j hj
  rw [slotCode_length] at hj
  have hk := idx_lt (N := nN P₀ P₁) b hi ho
  obtain ⟨d1, m1⟩ := divmod (N := nN P₀ P₁) (q := b.toNat * nN P₀ P₁ + i) ho
  obtain ⟨d2, m2⟩ := divmod (N := nN P₀ P₁) (q := b.toNat) hi
  have hb : decide (b.toNat = 1) = b := by cases b <;> rfl
  unfold parProg
  rw [List.getElem?_append_right (by simp only [initCode_length, slotA]; omega), initCode_length,
    show slotA P₀ P₁ b i o + j - hH = 32 * idx (nN P₀ P₁) b i o + j by
      simp only [slotA]; omega,
    getElem?_flatten_uniform _ (fun c hc => by
      rw [List.mem_map] at hc
      obtain ⟨k, -, rfl⟩ := hc
      exact slotCode_length _ _ _ _ _ _) _ j hj,
    List.getElem?_map, List.getElem?_range hk]
  simp only [Option.map_some, Option.bind_some, idx, d1, m1, d2, hb]
  rw [m2]
  rfl

theorem block_fits {b : Bool} {i o : ℕ} {ins : Instr} (hins : (thr P₀ P₁ b)[i]? = some ins)
    (ho : o < nN P₀ P₁) :
    Fits (parProg K P₀ P₁) (slotA P₀ P₁ b i o)
      (instrCode (code P₀ P₁ b o) (slotA P₀ P₁ b i o) i ins) := by
  have hi : i < nT P₀ P₁ b := (List.getElem?_eq_some_iff.mp hins).1
  have hf := slot_fits (K := K) (b := b) (lt_trans hi (nT_lt P₀ P₁ b)) ho
  simp only [slotCode, hins] at hf
  exact pad_fits (fits_append.1 hf).1

theorem stub_fits {b : Bool} {i o : ℕ} (hi : i < nT P₀ P₁ b) (ho : o < nN P₀ P₁) :
    Fits (parProg K P₀ P₁) (slotA P₀ P₁ b i o + 23) (stubCode P₀ P₁ b i o) := by
  obtain ⟨ins, hins⟩ : ∃ ins, (thr P₀ P₁ b)[i]? = some ins :=
    ⟨_, List.getElem?_eq_getElem (by simpa [nT] using hi)⟩
  have hf := slot_fits (K := K) (b := b) (lt_trans hi (nT_lt P₀ P₁ b)) ho
  simp only [slotCode, hins] at hf
  have h1 : (instrCode (code P₀ P₁ b o) (slotA P₀ P₁ b i o) i ins).length ≤ 23 :=
    instrCode_length_le _ _ _ _
  have := (fits_append.1 hf).2
  rw [pad_length h1] at this
  exact pad_fits this

theorem exit_fits {b : Bool} {o : ℕ} (ho : o < nN P₀ P₁) :
    Fits (parProg K P₀ P₁) (exitA P₀ P₁ b o) (exitCode P₀ P₁ b o (exitA P₀ P₁ b o)) := by
  have hf := slot_fits (K := K) (b := b) (nT_lt P₀ P₁ b) ho
  have hn : (thr P₀ P₁ b)[nT P₀ P₁ b]? = none := List.getElem?_eq_none (by simp [nT])
  simp only [slotCode, hn, if_true] at hf
  exact pad_fits hf

theorem dead_fits {b : Bool} {o : ℕ} (ho : o < nN P₀ P₁) :
    Fits (parProg K P₀ P₁) (deadA P₀ P₁ b o) (deadCode P₀ P₁ b o) := by
  have := (fits_append.1 (exit_fits (K := K) (b := b) ho)).2
  simpa [deadA] using this

/-! ### Copies -/

theorem x_copy {w : ℕ} {p : Program} {a c : ℕ} {s : State} (h : p[s.pc]? = some (.add a c 0))
    (hm : WordMem w s.mem) (h0 : s.mem 0 = 0) (ha : a < 2 ^ w) (hc : c < 2 ^ w) :
    Exec w p 1 s { s with pc := s.pc + 1, mem := Function.update s.mem a (s.mem c) } := by
  have := x_add (w := w) h ha hc (two_pow_pos w)
  simpa only [h0, Nat.add_zero, Nat.mod_eq_of_lt (hm c)] using this

theorem cp_spec {w : ℕ} {p : Program} :
    ∀ (cs : List (ℕ × ℕ)) (A : ℕ) (s : State), Fits p A (cpCode cs) → s.pc = A →
      WordMem w s.mem → s.mem 0 = 0 → (∀ c ∈ cs, c.1 ≠ 0 ∧ c.1 < 2 ^ w ∧ c.2 < 2 ^ w) →
      Exec w p cs.length s { s with pc := A + cs.length, mem := cpMem cs s.mem }
  | [], A, s, _, hpc, _, _, _ => by
      simp only [List.length_nil, Nat.add_zero, cpMem]
      rw [← hpc]; exact Exec.refl _
  | c :: cs, A, s, hf, hpc, hm, h0, hc => by
      have hf' : Fits p A (.add c.1 c.2 0 :: cpCode cs) := hf
      rw [fits_cons] at hf'
      obtain ⟨hc1, hc2, hc3⟩ := hc c (by simp)
      have e1 := x_copy (w := w) (s := s) (by rw [hpc]; exact hf'.1) hm h0 hc2 hc3
      have e2 := cp_spec cs (A + 1) { s with pc := s.pc + 1, mem := Function.update s.mem c.1 (s.mem c.2) }
        hf'.2 (by simp [hpc]) (hm.update _ (hm _))
        (by simp [Ne.symm hc1, h0])
        (fun d hd => hc d (by simp [hd]))
      have := e1.trans e2
      simp only [List.length_cons, cpMem]
      exact (this.cast (by omega)).of_eq (by congr 1; omega)

theorem cpMem_of_not_mem :
    ∀ (cs : List (ℕ × ℕ)) (m : ℕ → ℕ) (a : ℕ), (∀ c ∈ cs, c.1 ≠ a) → cpMem cs m a = m a
  | [], _, _, _ => rfl
  | c :: cs, m, a, h => by
      simp only [cpMem]
      rw [cpMem_of_not_mem cs _ a (fun d hd => h d (by simp [hd])),
        Function.update_of_ne (Ne.symm (h c (by simp)))]

theorem cpMem_swap (b : Bool) (m : ℕ → ℕ) :
    cpMem (svL b ++ ldL (!b)) m 3 = m (sv (!b)) ∧ cpMem (svL b ++ ldL (!b)) m 4 = m (sv (!b) + 1) ∧
    cpMem (svL b ++ ldL (!b)) m 6 = m (sv (!b) + 2) ∧ cpMem (svL b ++ ldL (!b)) m 7 = m (sv (!b) + 3) ∧
    cpMem (svL b ++ ldL (!b)) m (sv b) = m 3 ∧ cpMem (svL b ++ ldL (!b)) m (sv b + 1) = m 4 ∧
    cpMem (svL b ++ ldL (!b)) m (sv b + 2) = m 6 ∧ cpMem (svL b ++ ldL (!b)) m (sv b + 3) = m 7 := by
  cases b <;> simp [cpMem, svL, ldL, sv]

theorem cpMem_load (b : Bool) (m : ℕ → ℕ) :
    cpMem (ldL b) m 3 = m (sv b) ∧ cpMem (ldL b) m 4 = m (sv b + 1) ∧
    cpMem (ldL b) m 6 = m (sv b + 2) ∧ cpMem (ldL b) m 7 = m (sv b + 3) := by
  cases b <;> simp [cpMem, ldL, sv]

theorem sv_ge (b : Bool) : 40 ≤ sv b ∧ sv b ≤ 44 := by cases b <;> simp [sv]

theorem ob_ge (b : Bool) : 48 ≤ ob b ∧ ob b ≤ 52 := by cases b <;> simp [ob]

end Lax185574Proofs.RamPar
