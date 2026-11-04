import Lax185574Proofs.RamSimInstr

/-!
The block of every instruction, and the simulation of one instruction
of the simulated program.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec

variable {w : ℕ} {p : Program}
variable {g : Geo} {x' out₀ : List ℕ}

/-- The block simulating instruction `ins` at simulated address `i`,
placed at machine address `A`. -/
def instrCode (C : Code) (A i : ℕ) : Instr → Program
  | .set a n => [.set rR n, .and rR rR rMask] ++ (stCode a rR ++ [.jump (C.tgt (i + 1))])
  | .load a b => ldCode rB b ++ ([.add rT rB rBase, .load rR rT] ++
      (stCode a rR ++ [.jump (C.tgt (i + 1))]))
  | .store a b => ldCode rB a ++ (ldCode rC b ++ [.add rT rB rBase, .store rT rC,
      .jump (C.tgt (i + 1))])
  | .add a b c => binCode (.add rR rB rC) a b c (C.tgt (i + 1))
  | .sub a b c => binCode (.sub rR rB rC) a b c (C.tgt (i + 1))
  | .mul a b c => binCode (.mul rR rB rC) a b c (C.tgt (i + 1))
  | .div a b c => binCode (.div rR rB rC) a b c (C.tgt (i + 1))
  | .and a b c => binCode (.and rR rB rC) a b c (C.tgt (i + 1))
  | .shiftl a b c => binCode (.shiftl rR rB rC) a b c (C.tgt (i + 1))
  | .not a b => ldCode rB b ++ ([.sub rR rMask rB] ++ (stCode a rR ++ [.jump (C.tgt (i + 1))]))
  | .jump l => [.jump (C.tgt l)]
  | .jzero a l => ldCode rB a ++ [.jzero rB (C.tgt l), .jump (C.tgt (i + 1))]
  | .jeof l => [.sub rU rTot rCur, .jzero rU (C.tgt l), .jump (C.tgt (i + 1))]
  | .inputLength a => [.and rR rTot rMask] ++ (stCode a rR ++ [.jump (C.tgt (i + 1))])
  | .inputLoad a b => ldCode rD b ++ (chainCode C.ks C.tb (A + 4) (A + 4 + chainLen C.ks) ++
      ([.and rR rR rMask] ++ (stCode a rR ++ [.jump (C.tgt (i + 1))])))
  | .halt => [.jump C.exit]
  | .read a => readCode C.ks C.tb A C.exit a (C.tgt (i + 1))
  | .write a =>
      match C.mode with
      | .direct => ldCode rB a ++ [.write rB, .jump (C.tgt (i + 1))]
      | .buffer ovf => ldCode rB a ++ [.sub rU rCap rOC, .jzero rU ovf, .add rT rOB rOC,
          .store rT rB, .add rOC rOC rOne, .jump (C.tgt (i + 1))]

/-- A bound on the length of every block. -/
def blockLen (ks : List SegKind) : ℕ := chainLen ks + 16

theorem instrCode_length_le (C : Code) (A i : ℕ) (ins : Instr) :
    (instrCode C A i ins).length ≤ blockLen C.ks := by
  cases ins <;> simp [instrCode, blockLen, binCode, readCode, chainCode_length]
  all_goals first | omega | (split <;> simp)

/-- A bound on the number of steps of every block. -/
def stepBound (ks : List SegKind) : ℕ := 6 * ks.length + 16

theorem Reaches.setPc {ks : List SegKind} {tb : ℕ} {mode : OutMode} {n : ℕ} {S : State}
    {pc : ℕ} {s : State} (h : Reaches w p g ks tb mode x' out₀ n S pc s) (l : ℕ) :
    Reaches w p g ks tb mode x' out₀ n S pc { s with pc := l } := by
  obtain ⟨S', e, hpc, R, fr⟩ := h
  exact ⟨S', e, hpc, R.setPc l, fr⟩

theorem Rel.out_le {ks : List SegKind} {tb : ℕ} {ovf : ℕ} {s S : State}
    (R : Rel w g ks tb (.buffer ovf) x' out₀ s S) : s.out.length ≤ g.cap := R.out.2.2.2.2.1

/-- What one block achieves: the step of the simulated machine, its
halting, or an overflow of the output buffer. -/
def BlockOK (w : ℕ) (p : Program) (g : Geo) (C : Code) (x' out₀ : List ℕ) (ins : Instr)
    (s S : State) : Prop :=
  (∀ s', ins.effect g.v s = some s' → (∀ ovf, C.mode = .buffer ovf → s'.out.length ≤ g.cap) →
    ∃ n ≤ stepBound C.ks, Reaches w p g C.ks C.tb C.mode x' out₀ n S (C.tgt s'.pc) s') ∧
  (ins.effect g.v s = none →
    ∃ n ≤ stepBound C.ks, Reaches w p g C.ks C.tb C.mode x' out₀ n S C.exit s) ∧
  (∀ s' ovf, C.mode = .buffer ovf → ins.effect g.v s = some s' → g.cap < s'.out.length →
    ∃ n ≤ stepBound C.ks, ∃ S', Exec w p n S S' ∧ S'.pc = ovf ∧ Frame g S S' ∧ S'.out = S.out)

theorem BlockOK.of_some {C : Code} {ins : Instr} {s S s₁ : State}
    (R : Rel w g C.ks C.tb C.mode x' out₀ s S)
    (heff : ins.effect g.v s = some s₁) (hout : s₁.out = s.out)
    (h : ∃ n ≤ stepBound C.ks, Reaches w p g C.ks C.tb C.mode x' out₀ n S (C.tgt s₁.pc) s₁) :
    BlockOK w p g C x' out₀ ins s S := by
  refine ⟨fun s' hs' _ => ?_, fun hn => ?_, fun s' ovf hm hs' hlt => ?_⟩
  · rw [heff] at hs'; cases hs'; exact h
  · rw [heff] at hn; cases hn
  · rw [heff] at hs'
    obtain rfl := Option.some.inj hs'
    rw [hout] at hlt
    have R' := R
    rw [hm] at R'
    have := R'.out_le
    omega

theorem BlockOK.of_none {C : Code} {ins : Instr} {s S : State}
    (heff : ins.effect g.v s = none)
    (h : ∃ n ≤ stepBound C.ks, Reaches w p g C.ks C.tb C.mode x' out₀ n S C.exit s) :
    BlockOK w p g C x' out₀ ins s S := by
  refine ⟨fun s' hs' _ => ?_, fun _ => h, fun s' ovf _ hs' _ => ?_⟩
  · rw [heff] at hs'; cases hs'
  · rw [heff] at hs'; cases hs'

theorem block_spec (C : Code) {s S : State} {A : ℕ} {ins : Instr}
    (R : Rel w g C.ks C.tb C.mode x' out₀ s S) (hpc : S.pc = A)
    (hf : Fits p A (instrCode C A s.pc ins)) : BlockOK w p g C x' out₀ ins s S := by
  have hv := R.env.hv
  have sb : 15 ≤ stepBound C.ks := by simp [stepBound]
  cases ins with
  | set a n =>
      exact BlockOK.of_some R (effect_set _ _ _ _) rfl
        ⟨_, by omega, (set_spec R hpc hf).setPc _⟩
  | load a b =>
      exact BlockOK.of_some R (effect_load_eq _ _ _ _) rfl
        ⟨_, by omega, (load_spec R hpc hf).setPc _⟩
  | store a b =>
      exact BlockOK.of_some R (effect_store_eq _ _ _ _) rfl
        ⟨_, by omega, (store_spec R hpc hf).setPc _⟩
  | add a b c =>
      exact BlockOK.of_some R (effect_add_eq _ _ _ _ _) rfl ⟨_, by omega,
        Reaches.setPc (binop_spec (f := fun x y => x + y) (r := fun x y => (x + y) % 2 ^ w)
          (fun S h _ hw => x_add h (by omega) (by omega) (by omega))
          (fun x y _ _ => Nat.mod_lt _ (by positivity))
          (fun x y _ _ => mod_mod_of_le hv) R hpc hf) _⟩
  | sub a b c =>
      exact BlockOK.of_some R (effect_sub_eq _ _ _ _ _) rfl ⟨_, by omega,
        Reaches.setPc (binop_spec (f := fun x y => x - y) (r := fun x y => x - y)
          (fun S h hm hw => x_sub h hm (by omega) (by omega) (by omega))
          (fun x y hx _ => by omega)
          (fun x y _ _ => rfl) R hpc hf) _⟩
  | mul a b c =>
      exact BlockOK.of_some R (effect_mul_eq _ _ _ _ _) rfl ⟨_, by omega,
        Reaches.setPc (binop_spec (f := fun x y => x * y) (r := fun x y => (x * y) % 2 ^ w)
          (fun S h _ hw => x_mul h (by omega) (by omega) (by omega))
          (fun x y _ _ => Nat.mod_lt _ (by positivity))
          (fun x y _ _ => mod_mod_of_le hv) R hpc hf) _⟩
  | div a b c =>
      exact BlockOK.of_some R (effect_div_eq _ _ _ _ _) rfl ⟨_, by omega,
        Reaches.setPc (binop_spec (f := fun x y => x / y) (r := fun x y => x / y)
          (fun S h hm hw => x_div h hm (by omega) (by omega) (by omega))
          (fun x y hx _ => lt_of_le_of_lt (Nat.div_le_self _ _) hx)
          (fun x y _ _ => rfl) R hpc hf) _⟩
  | and a b c =>
      exact BlockOK.of_some R (effect_and_eq _ _ _ _ _) rfl ⟨_, by omega,
        Reaches.setPc (binop_spec (f := fun x y => Nat.land x y) (r := fun x y => Nat.land x y)
          (fun S h hm hw => x_and h hm (by omega) (by omega) (by omega))
          (fun x y hx _ => lt_of_le_of_lt (land_le_left _ _) hx)
          (fun x y _ _ => rfl) R hpc hf) _⟩
  | shiftl a b c =>
      exact BlockOK.of_some R (effect_shiftl_eq _ _ _ _ _) rfl ⟨_, by omega,
        Reaches.setPc (binop_spec (f := fun x y => x * 2 ^ y) (r := fun x y => (x * 2 ^ y) % 2 ^ w)
          (fun S h _ hw => x_shiftl h (by omega) (by omega) (by omega))
          (fun x y _ _ => Nat.mod_lt _ (by positivity))
          (fun x y _ _ => mod_mod_of_le hv) R hpc hf) _⟩
  | not a b =>
      exact BlockOK.of_some R (effect_not_eq _ _ _ _) rfl
        ⟨_, by omega, (not_spec R hpc hf).setPc _⟩
  | jump l =>
      exact BlockOK.of_some R (effect_jump _ _ _) rfl
        ⟨_, by omega, (jump_spec R hpc hf).setPc _⟩
  | jzero a l =>
      obtain ⟨n, hn, h⟩ := jzero_spec R hpc hf
      refine BlockOK.of_some R (effect_jzero_eq _ _ _ _) rfl ⟨n, by omega, ?_⟩
      have h' := h.setPc (if s.mem (a % 2 ^ g.v) = 0 then l else s.pc + 1)
      split_ifs at h' ⊢ <;> exact h'
  | jeof l =>
      obtain ⟨n, hn, h⟩ := jeof_spec R hpc hf
      refine BlockOK.of_some R (effect_jeof _ _ _) rfl ⟨n, by omega, ?_⟩
      have h' := h.setPc (if s.inp.isEmpty then l else s.pc + 1)
      split_ifs at h' ⊢ <;> exact h'
  | inputLength a =>
      exact BlockOK.of_some R (effect_inputLength _ _ _) rfl
        ⟨_, by omega, (inputLength_spec R hpc hf).setPc _⟩
  | inputLoad a b =>
      obtain ⟨n, hn, h⟩ := inputLoad_spec R hpc hf
      exact BlockOK.of_some R (effect_inputLoad_eq _ _ _ _) rfl
        ⟨n, by simp only [stepBound]; omega, h.setPc _⟩
  | halt =>
      exact BlockOK.of_none (effect_halt _ _) ⟨1, by omega, jump_spec R hpc hf⟩
  | read a =>
      cases hs : s.inp with
      | nil =>
          refine BlockOK.of_none (by rw [effect_read_eq, hs]; rfl) ⟨2, by omega, ?_⟩
          exact read_none R hpc hf hs
      | cons u rest =>
          obtain ⟨n, hn, h⟩ := read_some R hpc hf hs
          exact BlockOK.of_some
            (s₁ := { s with pc := s.pc + 1, mem := setCell g.v s.mem a u, inp := rest })
            R (by rw [effect_read_eq, hs]; rfl) rfl
            ⟨n, by simp only [stepBound]; omega, h.setPc _⟩
  | write a =>
      have heff := effect_write_eq g.v a s
      have hle : ∀ ovf, C.mode = .buffer ovf → s.out.length ≤ g.cap := by
        intro ovf hm
        have R' := R
        rw [hm] at R'
        exact R'.out_le
      cases hmode : C.mode with
      | direct =>
          simp only [instrCode, hmode] at hf
          have R' : Rel w g C.ks C.tb .direct x' out₀ s S := hmode ▸ R
          have h := (write_direct R' hpc hf).setPc (s.pc + 1)
          refine ⟨fun s' hs' _ => ?_, fun hn => ?_, fun s' ovf hm _ _ => ?_⟩
          · rw [heff] at hs'; obtain rfl := Option.some.inj hs'; rw [hmode]
            exact ⟨_, by omega, h⟩
          · rw [heff] at hn; cases hn
          · rw [hmode] at hm; cases hm
      | buffer ovf =>
          simp only [instrCode, hmode] at hf
          have R' : Rel w g C.ks C.tb (.buffer ovf) x' out₀ s S := hmode ▸ R
          have hb := write_buffer R' hpc hf
          have hle' := hle ovf hmode
          refine ⟨fun s' hs' hcap => ?_, fun hn => ?_, fun s' ovf' hm hs' hlt => ?_⟩
          · rw [heff] at hs'; obtain rfl := Option.some.inj hs'; rw [hmode]
            have := hcap ovf hmode
            simp only [List.length_append, List.length_cons, List.length_nil] at this
            exact ⟨_, by omega, (hb.1 (by omega)).setPc (s.pc + 1)⟩
          · rw [heff] at hn; cases hn
          · rw [heff] at hs'; obtain rfl := Option.some.inj hs'
            rw [hmode] at hm; cases hm
            simp only [List.length_append, List.length_cons, List.length_nil] at hlt
            obtain ⟨S', e, hpc', fr, ho⟩ := hb.2 (by omega)
            exact ⟨_, by omega, S', e, hpc', fr, ho⟩

/-! ### Layout -/

/-- Pad a block to length `L` with `halt`. -/
def pad (L : ℕ) (c : Program) : Program := c ++ List.replicate (L - c.length) .halt

theorem pad_length {L : ℕ} {c : Program} (h : c.length ≤ L) : (pad L c).length = L := by
  simp [pad]; omega

/-- The blocks of `p₀`, block `i` at `H + L * i`. -/
def blocks (C : Code) (H L : ℕ) (p₀ : Program) : Program :=
  (p₀.mapIdx fun i ins => pad L (instrCode C (H + L * i) i ins)).flatten

theorem getElem?_flatten_uniform {L : ℕ} (bs : List Program) (hL : ∀ b ∈ bs, b.length = L)
    (i j : ℕ) (hj : j < L) : bs.flatten[L * i + j]? = (bs[i]?).bind (·[j]?) := by
  induction bs generalizing i with
  | nil => simp
  | cons b bs ih =>
      have hb : b.length = L := hL b (by simp)
      rw [List.flatten_cons]
      cases i with
      | zero =>
          simp only [Nat.mul_zero, Nat.zero_add, List.getElem?_cons_zero, Option.bind_some]
          rw [List.getElem?_append_left (by omega)]
      | succ i =>
          rw [List.getElem?_append_right (by rw [hb]; nlinarith), hb,
            show L * (i + 1) + j - L = L * i + j by rw [Nat.mul_succ]; omega,
            ih (fun b hb' => hL b (by simp [hb'])) i]
          simp

theorem blocks_length (C : Code) (H L : ℕ) (p₀ : Program) (hL : blockLen C.ks ≤ L) :
    (blocks C H L p₀).length = L * p₀.length := by
  simp only [blocks, List.length_flatten]
  rw [List.sum_eq_card_nsmul _ L]
  · simp [Nat.mul_comm]
  · intro x hx
    rw [List.mem_map] at hx
    obtain ⟨b, hb, rfl⟩ := hx
    rw [List.mem_mapIdx] at hb
    obtain ⟨i, hi, rfl⟩ := hb
    exact pad_length ((instrCode_length_le _ _ _ _).trans hL)

theorem blocks_fits (C : Code) {H L : ℕ} {p₀ pre post : Program} (hL : blockLen C.ks ≤ L)
    (hpre : pre.length = H) {i : ℕ} {ins : Instr} (hi : p₀[i]? = some ins) :
    Fits (pre ++ blocks C H L p₀ ++ post) (H + L * i) (instrCode C (H + L * i) i ins) := by
  intro j hj
  have hlen := instrCode_length_le C (H + L * i) i ins
  have hiL : i < p₀.length := (List.getElem?_eq_some_iff.mp hi).1
  have hbl := blocks_length C H L p₀ hL
  have hjL : j < L := by omega
  have hlt : L * i + j < L * p₀.length := by
    have : L * (i + 1) ≤ L * p₀.length := Nat.mul_le_mul_left _ (by omega)
    rw [Nat.mul_succ] at this; omega
  rw [List.append_assoc, List.getElem?_append_right (by omega), hpre,
    show H + L * i + j - H = L * i + j by omega, List.getElem?_append_left (by omega)]
  rw [blocks, getElem?_flatten_uniform _ (fun b hb => by
      rw [List.mem_mapIdx] at hb
      obtain ⟨k, hk, rfl⟩ := hb
      exact pad_length ((instrCode_length_le _ _ _ _).trans hL)) i j hjL]
  rw [List.getElem?_mapIdx, hi]
  simp only [Option.map_some, Option.bind_some, pad]
  rw [List.getElem?_append_left hj]

/-! ### Runs -/

theorem effect_out_prefix {i : Instr} {v : ℕ} {s s' : State} (h : i.effect v s = some s') :
    s.out <+: s'.out := by
  cases i <;> simp only [effect_set, effect_load_eq, effect_store_eq, effect_add_eq,
    effect_sub_eq, effect_mul_eq, effect_div_eq, effect_and_eq, effect_shiftl_eq,
    effect_not_eq, effect_jump, effect_jzero_eq, effect_jeof, effect_inputLength,
    effect_inputLoad_eq, effect_halt, effect_read_eq, effect_write_eq] at h
  all_goals first
    | (cases h; exact List.prefix_refl _)
    | (cases h; exact List.prefix_append _ _)
    | skip
  · cases h
  · cases hs : s.inp.head? with
    | none => simp [hs] at h
    | some v => simp only [hs, Option.map_some, Option.some.injEq] at h; subst h; exact List.prefix_refl _

theorem run_out_prefix {v k : ℕ} {p₀ : Program} {s s' : State} (h : run v p₀ k s = some s') :
    s.out <+: s'.out := by
  induction k generalizing s with
  | zero => cases h; exact List.prefix_refl _
  | succ k ih =>
      rw [run_succ] at h
      cases hs : step v p₀ s with
      | none => simp [hs] at h
      | some t =>
          rw [hs] at h
          refine List.IsPrefix.trans ?_ (ih h)
          rw [step_eq] at hs
          cases hp : p₀[s.pc]? with
          | none => simp [hp] at hs
          | some i => exact effect_out_prefix (by simpa [hp] using hs)

/-- The simulation of a whole run of `p₀`: started in a state
representing `s` at the address of `s`'s counter, the machine reaches
the exit, representing the terminal state. -/
theorem sim_run (C : Code) {p₀ pre post : Program} {H L : ℕ}
    (hp : p = pre ++ blocks C H L p₀ ++ post) (hpre : pre.length = H) (hL : blockLen C.ks ≤ L)
    (htgt : ∀ l, C.tgt l = if l < p₀.length then H + L * l else C.exit) :
    ∀ (k : ℕ) (s s_end S : State), run g.v p₀ k s = some s_end → step g.v p₀ s_end = none →
      (∀ ovf, C.mode = .buffer ovf → s_end.out.length ≤ g.cap) →
      Rel w g C.ks C.tb C.mode x' out₀ s S → S.pc = C.tgt s.pc →
      ∃ n ≤ stepBound C.ks * (k + 1),
        Reaches w p g C.ks C.tb C.mode x' out₀ n S C.exit s_end := by
  intro k
  induction k with
  | zero =>
      intro s s_end S hr hs _ R hpc
      cases hr
      by_cases hlt : s.pc < p₀.length
      · obtain ⟨ins, hins⟩ : ∃ ins, p₀[s.pc]? = some ins := ⟨_, List.getElem?_eq_getElem hlt⟩
        rw [htgt, if_pos hlt] at hpc
        have hf := hp ▸ blocks_fits C hL hpre (post := post) hins
        have B := block_spec C R hpc hf
        rw [step_eq, hins] at hs
        obtain ⟨n, hn, h⟩ := B.2.1 hs
        exact ⟨n, by omega, h⟩
      · rw [htgt, if_neg hlt] at hpc
        exact ⟨0, by omega, S, Exec.refl S, hpc, R, Frame.refl g S⟩
  | succ k ih =>
      intro s s_end S hr hs hcap R hpc
      rw [run_succ] at hr
      cases hst : step g.v p₀ s with
      | none => simp [hst] at hr
      | some s₁ =>
          rw [hst] at hr
          have hst' := hst
          rw [step_eq] at hst'
          cases hins : p₀[s.pc]? with
          | none => simp [hins] at hst'
          | some ins =>
              simp only [hins, Option.bind_some] at hst'
              have hlt : s.pc < p₀.length := (List.getElem?_eq_some_iff.mp hins).1
              rw [htgt, if_pos hlt] at hpc
              have hf := hp ▸ blocks_fits C hL hpre (post := post) hins
              have B := block_spec C R hpc hf
              have hcap₁ : ∀ ovf, C.mode = .buffer ovf → s₁.out.length ≤ g.cap := by
                intro ovf hm
                have := (run_out_prefix hr).length_le
                have := hcap ovf hm
                omega
              obtain ⟨n₁, hn₁, S₁, e₁, hpc₁, R₁, fr₁⟩ := B.1 s₁ hst' hcap₁
              obtain ⟨n₂, hn₂, S₂, e₂, hpc₂, R₂, fr₂⟩ := ih s₁ s_end S₁ hr hs hcap R₁ hpc₁
              refine ⟨n₁ + n₂, ?_, S₂, e₁.trans e₂, hpc₂, R₂, fr₁.trans fr₂⟩
              rw [Nat.mul_succ]; omega

end Lax185574Proofs.RamSim
