import Lax185574Proofs.RamSimCore

/-!
One instruction of a simulated program, executed by a block of machine
code at a larger word length.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec

variable {w : ℕ} {p : Program}

@[simp] theorem ldCode_length (V a : ℕ) : (ldCode V a).length = 4 := rfl
@[simp] theorem stCode_length (a V : ℕ) : (stCode a V).length = 4 := rfl

/-- Where a simulation lives: the simulated word length `v`, the base of
the simulated memory, and the output buffer. -/
structure Geo where
  v : ℕ
  base : ℕ
  ob : ℕ
  cap : ℕ

/-- The cells a simulation step may write. -/
def Geo.W (g : Geo) (a : ℕ) : Prop :=
  a = rCur ∨ a = rOC ∨ (rT ≤ a ∧ a ≤ rU) ∨ (g.base ≤ a ∧ a < g.base + 2 ^ g.v) ∨
    (g.ob ≤ a ∧ a < g.ob + g.cap)

/-- Output goes to the output tape, or to a memory buffer whose
overflow jumps to `ovf`. -/
inductive OutMode
  | direct
  | buffer (ovf : ℕ)

/-- How the simulated output is represented. -/
def OutRel (w : ℕ) (g : Geo) (out₀ : List ℕ) (s S : State) : OutMode → Prop
  | .direct => S.out = out₀ ++ s.out
  | .buffer _ => S.out = out₀ ∧ S.mem rOB = g.ob ∧ S.mem rOC = s.out.length ∧
      S.mem rCap = g.cap ∧ s.out.length ≤ g.cap ∧ 16 ≤ g.ob ∧ g.ob + g.cap ≤ 2 ^ w ∧
      (g.ob + g.cap ≤ g.base ∨ g.base + 2 ^ g.v ≤ g.ob) ∧
      ∀ j < s.out.length, S.mem (g.ob + j) = s.out.getD j 0

/-- The machine state `S` represents the simulated state `s` on the
simulated input `x'`. The program counter is not part of it. -/
structure Rel (w : ℕ) (g : Geo) (ks : List SegKind) (tb : ℕ) (mode : OutMode)
    (x' out₀ : List ℕ) (s S : State) : Prop where
  env : Env w g.v g.base S
  cword : ∀ a, s.mem a < 2 ^ g.v
  mem : ∀ a < 2 ^ g.v, S.mem (g.base + a) = s.mem a
  input : s.input = x'
  cur : S.mem rCur ≤ x'.length
  inp : s.inp = x'.drop (S.mem rCur)
  tot : S.mem rTot = x'.length
  table : ∃ segs, TableOK w g.W S ks tb segs ∧ segs.flatten = x'
  tb16 : 16 ≤ tb
  tbw : tb + 2 * ks.length < 2 ^ w
  out : OutRel w g out₀ s S mode

/-- A step changes only writable cells, and neither input. -/
def Frame (g : Geo) (S S' : State) : Prop :=
  S'.input = S.input ∧ S'.inp = S.inp ∧ ∀ a, ¬ g.W a → S'.mem a = S.mem a

theorem Frame.refl (g : Geo) (S : State) : Frame g S S := ⟨rfl, rfl, fun _ _ => rfl⟩

theorem Frame.trans {g : Geo} {S S₁ S₂ : State} (h₁ : Frame g S S₁) (h₂ : Frame g S₁ S₂) :
    Frame g S S₂ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, fun a ha => (h₂.2.2 a ha).trans (h₁.2.2 a ha)⟩

theorem Frame.temps {g : Geo} {S S' : State} (hi : S'.input = S.input) (hn : S'.inp = S.inp)
    (h : ∀ a, (a < rT ∨ rU < a) → S'.mem a = S.mem a) : Frame g S S' :=
  ⟨hi, hn, fun a ha => h a (by simp only [Geo.W] at ha; omega)⟩

variable {g : Geo} {ks : List SegKind} {tb : ℕ} {mode : OutMode} {x' out₀ : List ℕ}

/-- Changing only temporaries keeps the representation. -/
theorem Rel.temps {s S S₁ : State} (R : Rel w g ks tb mode x' out₀ s S)
    (h : ∀ a, (a < rT ∨ rU < a) → S₁.mem a = S.mem a) (hm : WordMem w S₁.mem)
    (hi : S₁.input = S.input) (ho : S₁.out = S.out) : Rel w g ks tb mode x' out₀ s S₁ := by
  have E := R.env
  have low := E.low
  refine
    { env := ⟨hm, by rw [h _ (by omega)]; exact E.zero, by rw [h _ (by omega)]; exact E.one,
        by rw [h _ (by omega)]; exact E.mask, by rw [h _ (by omega)]; exact E.baseCell,
        E.room, E.low, E.hv⟩
      cword := R.cword
      mem := fun a ha => by rw [h _ (by omega)]; exact R.mem a ha
      input := R.input
      cur := by rw [h _ (by omega)]; exact R.cur
      inp := by rw [h _ (by omega)]; exact R.inp
      tot := by rw [h _ (by omega)]; exact R.tot
      table := by
        obtain ⟨segs, hT, hx⟩ := R.table
        exact ⟨segs, hT.frame (fun a ha => h a (by simp only [Geo.W] at ha; omega)) hi, hx⟩
      tb16 := R.tb16
      tbw := R.tbw
      out := ?_ }
  have ho' := R.out
  cases mode with
  | direct => simp only [OutRel] at ho' ⊢; rw [ho, ho']
  | buffer ovf =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ho'
      refine ⟨ho.trans h1, by rw [h _ (by omega)]; exact h2, by rw [h _ (by omega)]; exact h3,
        by rw [h _ (by omega)]; exact h4, h5, h6, h7, h8, fun j hj => ?_⟩
      rw [h _ (by omega)]; exact h9 j hj

/-- The program counter of the simulated state is not represented. -/
theorem Rel.setPc {s S : State} (R : Rel w g ks tb mode x' out₀ s S) (l : ℕ) :
    Rel w g ks tb mode x' out₀ { s with pc := l } S := by
  cases mode <;> exact
    { env := R.env, cword := R.cword, mem := R.mem, input := R.input, cur := R.cur,
      inp := R.inp, tot := R.tot, table := R.table, tb16 := R.tb16, tbw := R.tbw,
      out := R.out }

theorem setCell_eq_update (v : ℕ) (m : ℕ → ℕ) (a x : ℕ) :
    setCell v m a x = Function.update m (a % 2 ^ v) (x % 2 ^ v) := by
  funext b; rw [setCell_eq, Function.update_apply]

/-- Store `rR` into simulated cell `a` and jump to `l`. -/
theorem finish_spec {s S : State} {a l A val : ℕ} (R : Rel w g ks tb mode x' out₀ s S)
    (hf : Fits p A (stCode a rR ++ [.jump l])) (hpc : S.pc = A)
    (hval : S.mem rR = val % 2 ^ g.v) :
    ∃ S', Exec w p 5 S S' ∧ S'.pc = l ∧
      Rel w g ks tb mode x' out₀ { s with mem := setCell g.v s.mem a val } S' ∧
      Frame g S S' ∧ S'.out = S.out := by
  rw [fits_append] at hf
  obtain ⟨hf1, hf2⟩ := hf
  have E := R.env
  have low := E.low
  have room := E.room
  have hav : a % 2 ^ g.v < 2 ^ g.v := Nat.mod_lt _ (by positivity)
  have hw := E.hw
  have e := (st_spec E hf1 hpc (by omega) (by decide)).trans
    (x_jump (fetch hf2 (i := 0) (by simp [stCode, addrCode]) rfl))
  set X := g.base + a % 2 ^ g.v
  obtain ⟨S', e, hS'⟩ := (⟨_, e, rfl⟩ : ∃ S', Exec w p (4 + 1) S S' ∧ S' = _)
  have hmem : S'.mem = Function.update (Function.update S.mem rT X) X (S.mem rR) := by
    subst hS'; rfl
  have hX : g.W X := Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega⟩)))
  have hfr : ∀ b, ¬ g.W b → S'.mem b = S.mem b := by
    intro b hb
    have h1 : b ≠ X := fun h => hb (h ▸ hX)
    have h2 : b ≠ rT := by rintro rfl; exact hb (Or.inr (Or.inr (Or.inl ⟨le_refl _, by omega⟩)))
    rw [hmem, Function.update_of_ne h1, Function.update_of_ne h2]
  have hlow : ∀ b, b < 16 → b ≠ rT → S'.mem b = S.mem b := by
    intro b hb h2
    rw [hmem, Function.update_of_ne (by omega), Function.update_of_ne h2]
  have hm' : WordMem w S'.mem := by
    rw [hmem]; exact (E.word.update _ (by omega)).update _ (E.word _)
  have hin : S'.input = S.input := by subst hS'; rfl
  refine ⟨S', e, by subst hS'; rfl, ?_, ⟨hin, by subst hS'; rfl, hfr⟩, by subst hS'; rfl⟩
  refine
    { env := ⟨hm', by rw [hlow _ (by omega) (by omega)]; exact E.zero,
        by rw [hlow _ (by omega) (by omega)]; exact E.one,
        by rw [hlow _ (by omega) (by omega)]; exact E.mask,
        by rw [hlow _ (by omega) (by omega)]; exact E.baseCell, E.room, E.low, E.hv⟩
      cword := fun b => by
        simp only [setCell_eq_update, Function.update_apply]
        split_ifs
        · exact Nat.mod_lt _ (by positivity)
        · exact R.cword b
      mem := fun b hb => by
        simp only [setCell_eq_update, Function.update_apply, hmem]
        by_cases hbX : b = a % 2 ^ g.v
        · subst hbX
          simp only [X, if_true, hval]
        · rw [if_neg (by omega), if_neg (by omega), if_neg hbX]
          exact R.mem b hb
      input := R.input
      cur := by rw [hlow _ (by omega) (by omega)]; exact R.cur
      inp := by rw [hlow _ (by omega) (by omega)]; exact R.inp
      tot := by rw [hlow _ (by omega) (by omega)]; exact R.tot
      table := by
        obtain ⟨segs, hT, hx⟩ := R.table
        exact ⟨segs, hT.frame hfr hin, hx⟩
      tb16 := R.tb16
      tbw := R.tbw
      out := ?_ }
  have ho' := R.out
  have hout : S'.out = S.out := by subst hS'; rfl
  cases mode with
  | direct => simp only [OutRel] at ho' ⊢; rw [hout, ho']
  | buffer ovf =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := ho'
      refine ⟨hout.trans h1, by rw [hlow _ (by omega) (by omega)]; exact h2,
        by rw [hlow _ (by omega) (by omega)]; exact h3,
        by rw [hlow _ (by omega) (by omega)]; exact h4, h5, h6, h7, h8, fun j hj => ?_⟩
      have hj' : j < s.out.length := hj
      rw [hmem, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      exact h9 j hj'

/-! ### Steps that change only temporaries -/

/-- `S'` differs from `S` at most in the temporaries `rT` to `rU`. -/
def TempsOnly (S S' : State) : Prop :=
  (∀ a, (a < rT ∨ rU < a) → S'.mem a = S.mem a) ∧ S'.input = S.input ∧ S'.inp = S.inp ∧
    S'.out = S.out

theorem TempsOnly.refl (S : State) : TempsOnly S S := ⟨fun _ _ => rfl, rfl, rfl, rfl⟩

theorem TempsOnly.trans {S S₁ S₂ : State} (h₁ : TempsOnly S S₁) (h₂ : TempsOnly S₁ S₂) :
    TempsOnly S S₂ :=
  ⟨fun a ha => (h₂.1 a ha).trans (h₁.1 a ha), h₂.2.1.trans h₁.2.1, h₂.2.2.1.trans h₁.2.2.1,
    h₂.2.2.2.trans h₁.2.2.2⟩

theorem TempsOnly.update {S : State} {pc a x : ℕ} (ha : rT ≤ a ∧ a ≤ rU) :
    TempsOnly S { S with pc := pc, mem := Function.update S.mem a x } :=
  ⟨fun b hb => Function.update_of_ne (by omega) _ _, rfl, rfl, rfl⟩

theorem TempsOnly.update₂ {S : State} {pc a x b y : ℕ} (ha : rT ≤ a ∧ a ≤ rU)
    (hb : rT ≤ b ∧ b ≤ rU) :
    TempsOnly S { S with pc := pc, mem := Function.update (Function.update S.mem a x) b y } :=
  ⟨fun c hc => by
    show Function.update (Function.update S.mem a x) b y c = S.mem c
    rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega)],
    rfl, rfl, rfl⟩

theorem TempsOnly.setPc {S : State} {pc : ℕ} : TempsOnly S { S with pc := pc } :=
  TempsOnly.refl S

theorem TempsOnly.frame {g : Geo} {S S' : State} (h : TempsOnly S S') : Frame g S S' :=
  Frame.temps h.2.1 h.2.2.1 h.1

theorem Env.temps {v base : ℕ} {S S' : State} (E : Env w v base S) (h : TempsOnly S S')
    (hm : WordMem w S'.mem) : Env w v base S' :=
  ⟨hm, by rw [h.1 _ (by omega)]; exact E.zero, by rw [h.1 _ (by omega)]; exact E.one,
    by rw [h.1 _ (by omega)]; exact E.mask, by rw [h.1 _ (by omega)]; exact E.baseCell,
    E.room, E.low, E.hv⟩

theorem Rel.tempsOnly {s S S' : State} (R : Rel w g ks tb mode x' out₀ s S) (h : TempsOnly S S')
    (hm : WordMem w S'.mem) : Rel w g ks tb mode x' out₀ s S' :=
  R.temps h.1 hm h.2.1 h.2.2.2

/-- Load simulated cell `a` into `V`, as a step on temporaries. -/
theorem ld_spec' {v base V a A : ℕ} {S : State} (E : Env w v base S)
    (hf : Fits p A (ldCode V a)) (hpc : S.pc = A) (hV : rT ≤ V ∧ V ≤ rU) :
    ∃ S', Exec w p 4 S S' ∧ S'.pc = A + 4 ∧ S'.mem V = S.mem (base + a % 2 ^ v) ∧
      (∀ x, x ≠ rT → x ≠ V → S'.mem x = S.mem x) ∧
      TempsOnly S S' ∧ Env w v base S' := by
  have hw := E.hw
  have e := ld_spec E hf hpc (by omega)
  refine ⟨_, e, rfl, by simp, fun x h1 h2 => ?_, TempsOnly.update₂ (by omega) hV,
    E.temps (TempsOnly.update₂ (by omega) hV) (E.word.exec e)⟩
  show Function.update (Function.update S.mem rT _) V _ x = S.mem x
  rw [Function.update_of_ne h2, Function.update_of_ne h1]

/-- A value computed into `rR` by temporaries-only code, then stored. -/
theorem value_finish {s S S₁ : State} {n₁ a l A₁ val : ℕ} (R : Rel w g ks tb mode x' out₀ s S)
    (e₁ : Exec w p n₁ S S₁) (h₁ : TempsOnly S S₁) (hpc₁ : S₁.pc = A₁)
    (hf : Fits p A₁ (stCode a rR ++ [.jump l])) (hval : S₁.mem rR = val % 2 ^ g.v) :
    ∃ S', Exec w p (n₁ + 5) S S' ∧ S'.pc = l ∧
      Rel w g ks tb mode x' out₀ { s with mem := setCell g.v s.mem a val } S' ∧
      Frame g S S' := by
  have R₁ := R.tempsOnly h₁ (R.env.word.exec e₁)
  obtain ⟨S', e, hpc', R', hfr, -⟩ := finish_spec R₁ hf hpc₁ hval
  exact ⟨S', e₁.trans e, hpc', R', h₁.frame.trans hfr⟩

theorem effect_eq_some {i : Instr} {v : ℕ} {s s' : State} (h : i.effect v s = some s') :
    i.effect v s = some s' := h

/-! ### The blocks -/

/-- Compile-time data of a simulation: the segment kinds and table, the
output mode, where simulated labels go, and where a halt goes. -/
structure Code where
  ks : List SegKind
  tb : ℕ
  mode : OutMode
  tgt : ℕ → ℕ
  exit : ℕ

/-- A binary operation `op` of `rB` and `rC` into `rR`. -/
def binCode (op : Instr) (a b c l : ℕ) : Program :=
  ldCode rB b ++ (ldCode rC c ++ ([op, .and rR rR rMask] ++ (stCode a rR ++ [.jump l])))

theorem binop_spec {op : Instr} {f r : ℕ → ℕ → ℕ} {s S : State} {a b c l A : ℕ}
    (hop : ∀ S : State, p[S.pc]? = some op → WordMem w S.mem → 16 < 2 ^ w →
      Exec w p 1 S { S with pc := S.pc + 1, mem := Function.update S.mem rR (r (S.mem rB) (S.mem rC)) })
    (hr : ∀ x y, x < 2 ^ w → y < 2 ^ w → r x y < 2 ^ w)
    (hrf : ∀ x y, x < 2 ^ g.v → y < 2 ^ g.v → r x y % 2 ^ g.v = f x y % 2 ^ g.v)
    (R : Rel w g ks tb mode x' out₀ s S) (hpc : S.pc = A) (hf : Fits p A (binCode op a b c l)) :
    ∃ S', Exec w p (4 + 4 + 1 + 1 + 5) S S' ∧ S'.pc = l ∧
      Rel w g ks tb mode x' out₀
        { s with mem := setCell g.v s.mem a (f (s.mem (b % 2 ^ g.v)) (s.mem (c % 2 ^ g.v))) } S' ∧
      Frame g S S' := by
  simp only [binCode] at hf
  obtain ⟨hf1, hf⟩ := fits_append.1 hf
  obtain ⟨hf2, hf⟩ := fits_append.1 hf
  obtain ⟨hf3, hf4⟩ := fits_append.1 hf
  have E := R.env
  have hw := E.hw
  have hbv : b % 2 ^ g.v < 2 ^ g.v := Nat.mod_lt _ (by positivity)
  have hcv : c % 2 ^ g.v < 2 ^ g.v := Nat.mod_lt _ (by positivity)
  obtain ⟨S1, e1, hpc1, hB1, -, t1, E1⟩ := ld_spec' E hf1 hpc (V := rB) (by omega)
  obtain ⟨S2, e2, hpc2, hC2, o2, t2, E2⟩ := ld_spec' E1 hf2 (by simpa using hpc1)
    (V := rC) (by omega)
  have hB2 : S2.mem rB = s.mem (b % 2 ^ g.v) := by
    rw [o2 _ (by decide) (by decide), hB1, R.mem _ hbv]
  have hC2' : S2.mem rC = s.mem (c % 2 ^ g.v) := by
    have := E.low
    rw [hC2, t1.1 _ (by omega), R.mem _ hcv]
  have hm2 := E2.word
  have e3 := hop S2 (fetch hf3 (i := 0) (by simp [hpc2]) rfl) hm2 hw
  have hrw : r (S2.mem rB) (S2.mem rC) < 2 ^ w := hr _ _ (hm2 _) (hm2 _)
  have e4 := e3.trans (x_and (fetch hf3 (i := 1) (by simp [hpc2]) rfl)
    (hm2.update _ hrw) (by omega) (by omega) (by omega))
  obtain ⟨S4, e4, hS4⟩ := (⟨_, e4, rfl⟩ : ∃ S', Exec w p (1 + 1) S2 S' ∧ S' = _)
  have t4 : TempsOnly S2 S4 := by subst hS4; exact TempsOnly.update₂ (by omega) (by omega)
  have hR4 : S4.mem rR = f (s.mem (b % 2 ^ g.v)) (s.mem (c % 2 ^ g.v)) % 2 ^ g.v := by
    subst hS4
    simp only [Function.update_self]
    rw [Function.update_of_ne (show (2 : ℕ) ≠ 12 by decide), E2.mask,
      land_mask, hB2, hC2', hrf _ _ (R.cword _) (R.cword _)]
  have hpc4 : S4.pc = A + 4 + 4 + 2 := by subst hS4; simp [hpc2]
  obtain ⟨S', e', hpc', R', hfr⟩ := value_finish R ((e1.trans e2).trans e4) (t1.trans (t2.trans t4))
    hpc4 (hf4.congr (by simp)) hR4
  exact ⟨S', e', hpc', R', hfr⟩

end Lax185574Proofs.RamSim
