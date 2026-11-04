import Lax185574Proofs.RamSimRun
import Mathlib.Data.Fin.VecNotation

/-!
Rewritten inputs. A rewrite reads from `s` sources and produces a list:
a concatenation of segments, each a single computed entry or a slice of
a source. A source is the machine's input or a list in memory. Computed
entries are ring expressions over literals, source entries and source
lengths. The machine evaluates them in `w` bits, which is correct modulo
`2 ^ w`. Indices, slice bounds and exponents must be exact, which is
`Rewrite.Fits`.
-/

namespace Lax185574Proofs.Simulate

open Lax808846.Ram

/-- Expressions over `s` sources. -/
inductive HExpr (s : ℕ)
  | lit (n : ℕ)
  | entry (src : Fin s) (i : ℕ)
  | len (src : Fin s)
  | add (a b : HExpr s)
  | mul (a b : HExpr s)
  | pow (a b : HExpr s)

variable {s : ℕ}

def HExpr.eval (xs : Fin s → List ℕ) : HExpr s → ℕ
  | lit n => n
  | entry src i => (xs src).getD i 0
  | len src => (xs src).length
  | add a b => a.eval xs + b.eval xs
  | mul a b => a.eval xs * b.eval xs
  | pow a b => a.eval xs ^ b.eval xs

/-- Cost of evaluating an expression, with powers by a counting loop. -/
def HExpr.cost (xs : Fin s → List ℕ) : HExpr s → ℕ
  | lit _ => 1
  | entry _ _ => 1
  | len _ => 1
  | add a b => a.cost xs + b.cost xs + 1
  | mul a b => a.cost xs + b.cost xs + 1
  | pow a b => a.cost xs + b.cost xs + b.eval xs + 1

/-- Indices and exponents are exact words. -/
def HExpr.Fits (w : ℕ) (xs : Fin s → List ℕ) : HExpr s → Prop
  | lit _ => True
  | entry _ i => i < 2 ^ w
  | len _ => True
  | add a b => a.Fits w xs ∧ b.Fits w xs
  | mul a b => a.Fits w xs ∧ b.Fits w xs
  | pow a b => a.Fits w xs ∧ b.Fits w xs ∧ b.eval xs < 2 ^ w

/-- The number of nodes of an expression. -/
def HExpr.size : HExpr s → ℕ
  | lit _ => 1
  | entry _ _ => 1
  | len _ => 1
  | add a b => a.size + b.size + 1
  | mul a b => a.size + b.size + 1
  | pow a b => a.size + b.size + 1

/-- A segment: one computed entry, or the slice of a source from
`start` of length `len` (`none`: to the end), clipped to the source. -/
inductive Segment (s : ℕ)
  | expr (e : HExpr s)
  | slice (src : Fin s) (start : HExpr s) (len : Option (HExpr s))

def Segment.apply (xs : Fin s → List ℕ) : Segment s → List ℕ
  | expr e => [e.eval xs]
  | slice src st none => (xs src).drop (st.eval xs)
  | slice src st (some l) => ((xs src).drop (st.eval xs)).take (l.eval xs)

def Segment.cost (xs : Fin s → List ℕ) : Segment s → ℕ
  | expr e => e.cost xs + 1
  | slice _ st none => st.cost xs + 1
  | slice _ st (some l) => st.cost xs + l.cost xs + 1

def Segment.Fits (w : ℕ) (xs : Fin s → List ℕ) : Segment s → Prop
  | expr e => e.Fits w xs
  | slice _ st none => st.Fits w xs ∧ st.eval xs < 2 ^ w
  | slice _ st (some l) =>
      st.Fits w xs ∧ st.eval xs < 2 ^ w ∧ l.Fits w xs ∧ l.eval xs < 2 ^ w

/-- A rewrite over `s` sources. -/
abbrev Rewrite (s : ℕ) := List (Segment s)

def Rewrite.apply (ρ : Rewrite s) (xs : Fin s → List ℕ) : List ℕ :=
  (ρ.map (·.apply xs)).flatten

/-- Setup cost: evaluating all expressions once, plus one per segment. -/
def Rewrite.cost (ρ : Rewrite s) (xs : Fin s → List ℕ) : ℕ :=
  (ρ.map (·.cost xs)).sum + 1

/-- Everything the simulator must know exactly fits in a word: the
source lengths, the length of the result, and every index, slice bound
and exponent. -/
def Rewrite.Fits (ρ : Rewrite s) (w : ℕ) (xs : Fin s → List ℕ) : Prop :=
  (∀ i, (xs i).length < 2 ^ w) ∧ (ρ.apply xs).length < 2 ^ w ∧
    ∀ seg ∈ ρ, seg.Fits w xs

end Lax185574Proofs.Simulate

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec Lax185574Proofs.Simulate

variable {w : ℕ} {p : Program} {s : ℕ}

/-! ### Sources -/

/-- Where a source lives: the machine's input, or memory from the
address held by cell `bc`. Its length is held by cell `lc`. -/
structure Src where
  kind : SegKind
  lc : ℕ

/-- Source `src` holds the list `xs` in `S`. Its cells avoid `Q`. The
kind `val` is not a source kind and is never correct. -/
def SrcOK (w : ℕ) (Q : ℕ → Prop) (S : State) (src : Src) (xs : List ℕ) : Prop :=
  S.mem src.lc = xs.length ∧ xs.length < 2 ^ w ∧ src.lc < 2 ^ w ∧ ¬ Q src.lc ∧
    match src.kind with
    | .val => False
    | .input => S.input = xs
    | .mem bc => bc < 2 ^ w ∧ ¬ Q bc ∧ S.mem bc + xs.length ≤ 2 ^ w ∧
        ∀ i < xs.length, S.mem (S.mem bc + i) = xs.getD i 0 % 2 ^ w ∧ ¬ Q (S.mem bc + i)

theorem SrcOK.frame {Q : ℕ → Prop} {S S' : State} {src : Src} {xs : List ℕ}
    (h : SrcOK w Q S src xs) (hQ : ∀ a, ¬ Q a → S'.mem a = S.mem a)
    (hi : S'.input = S.input) : SrcOK w Q S' src xs := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨by rw [hQ _ h4]; exact h1, h2, h3, h4, ?_⟩
  rcases hk : src.kind with _ | _ | bc
  · rw [hk] at h5; exact h5.elim
  · rw [hk] at h5; simp only; rw [hi]; exact h5
  · rw [hk] at h5
    obtain ⟨h6, h7, h8, h9⟩ := h5
    refine ⟨h6, h7, by rw [hQ _ h7]; exact h8, fun i hi' => ?_⟩
    rw [hQ _ h7]
    obtain ⟨h10, h11⟩ := h9 i hi'
    exact ⟨by rw [hQ _ h11]; exact h10, h11⟩

theorem SrcOK.anti {Q Q' : ℕ → Prop} {S : State} {src : Src} {xs : List ℕ}
    (h : SrcOK w Q S src xs) (hQ : ∀ a, Q' a → Q a) : SrcOK w Q' S src xs := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, fun h => h4 (hQ _ h), ?_⟩
  rcases hk : src.kind with _ | _ | bc
  · rw [hk] at h5; exact h5.elim
  · rw [hk] at h5; exact h5
  · rw [hk] at h5
    obtain ⟨h6, h7, h8, h9⟩ := h5
    exact ⟨h6, fun h => h7 (hQ _ h), h8, fun i hi => ⟨(h9 i hi).1, fun h => (h9 i hi).2 (hQ _ h)⟩⟩

/-! ### Evaluating expressions -/

/-- Evaluate `e` into cell `te + d`, using the cells above it. -/
def evalCode (srcs : Fin s → Src) (te : ℕ) : HExpr s → ℕ → ℕ → Program
  | .lit n, d, _ => [.set (te + d) n]
  | .entry src i, d, A =>
      match (srcs src).kind with
      | .mem bc => [.set (te + d) 0, .set rU i, .sub rT (srcs src).lc rU, .jzero rT (A + 6),
          .add rT rU bc, .load (te + d) rT]
      | _ => [.set rT i, .inputLoad (te + d) rT]
  | .len src, d, _ => [.add (te + d) (srcs src).lc rZ]
  | .add a b, d, A => evalCode srcs te a d A ++ (evalCode srcs te b (d + 1)
      (A + (evalCode srcs te a d A).length) ++ [.add (te + d) (te + d) (te + d + 1)])
  | .mul a b, d, A => evalCode srcs te a d A ++ (evalCode srcs te b (d + 1)
      (A + (evalCode srcs te a d A).length) ++ [.mul (te + d) (te + d) (te + d + 1)])
  | .pow a b, d, A =>
      let L₀ := A + (evalCode srcs te a d A).length +
        (evalCode srcs te b (d + 1) (A + (evalCode srcs te a d A).length)).length + 1
      evalCode srcs te a d A ++ (evalCode srcs te b (d + 1)
        (A + (evalCode srcs te a d A).length) ++
        [.set (te + d + 2) 1, .jzero (te + d + 1) (L₀ + 4),
          .mul (te + d + 2) (te + d + 2) (te + d), .sub (te + d + 1) (te + d + 1) rOne,
          .jump L₀, .add (te + d) (te + d + 2) rZ])

theorem evalCode_length (srcs : Fin s → Src) (te : ℕ) (e : HExpr s) (d A A' : ℕ) :
    (evalCode srcs te e d A).length = (evalCode srcs te e d A').length := by
  induction e generalizing d A A' with
  | lit n => rfl
  | entry src i => simp only [evalCode]; split <;> rfl
  | len src => rfl
  | add a b iha ihb =>
      simp only [evalCode, List.length_append]
      rw [iha d A A', ihb (d + 1) _ (A' + (evalCode srcs te a d A').length)]
  | mul a b iha ihb =>
      simp only [evalCode, List.length_append]
      rw [iha d A A', ihb (d + 1) _ (A' + (evalCode srcs te a d A').length)]
  | pow a b iha ihb =>
      simp only [evalCode, List.length_append]
      rw [iha d A A', ihb (d + 1) _ (A' + (evalCode srcs te a d A').length)]
      simp

/-- The counting loop of a power: multiply `acc` by `b` while `ctr`
counts down. -/
theorem pow_loop {acc ctr bc L₀ : ℕ} (hacc : acc < 2 ^ w) (hctr : ctr < 2 ^ w)
    (hbc : bc < 2 ^ w) (hne : acc ≠ ctr) (hone : 1 ≠ ctr) (hone' : 1 ≠ acc)
    (hf : Fits p L₀ [.jzero ctr (L₀ + 4), .mul acc acc bc, .sub ctr ctr rOne, .jump L₀]) :
    ∀ (r : ℕ) (S : State), S.pc = L₀ → S.mem ctr = r → WordMem w S.mem → S.mem rOne = 1 →
      bc ≠ acc → bc ≠ ctr →
      ∃ m, Exec w p (4 * r + 1) S { S with pc := L₀ + 4, mem := m } ∧
        m acc = S.mem acc * S.mem bc ^ r % 2 ^ w ∧
        ∀ c, c ≠ acc → c ≠ ctr → m c = S.mem c := by
  intro r
  induction r with
  | zero =>
      intro S hpc hc hm h1 _ _
      refine ⟨S.mem, (x_jzero_pos (fetch hf (i := 0) (by simp [hpc]) rfl) hctr hc).of_eq rfl,
        ?_, fun _ _ _ => rfl⟩
      simp [Nat.mod_eq_of_lt (hm acc)]
  | succ r ih =>
      intro S hpc hc hm h1 hba hbc'
      have e := (((x_jzero_neg (w := w) (s := S) (fetch hf (i := 0) (by simp [hpc]) rfl) hctr
        (by omega)).trans (x_mul (fetch hf (i := 1) (by simp [hpc]) rfl) hacc hacc hbc)).trans
        (x_sub (fetch hf (i := 2) (by simp [hpc]) rfl) (hm.update _ (Nat.mod_lt _ (by positivity)))
          hctr hctr (by omega))).trans (x_jump (fetch hf (i := 3) (by simp [hpc]) rfl))
      obtain ⟨S1, e, hS1⟩ := (⟨_, e, rfl⟩ : ∃ S', Exec w p (1 + 1 + 1 + 1) S S' ∧ S' = _)
      have hm1 : ∀ c, S1.mem c = if c = ctr then r else
          if c = acc then S.mem acc * S.mem bc % 2 ^ w else S.mem c := by
        intro c; subst hS1; dsimp only
        have hS : Function.update S.mem acc (S.mem acc * S.mem bc % 2 ^ w) 1 = 1 := by
          rw [Function.update_of_ne hone']; exact h1
        have hT : Function.update S.mem acc (S.mem acc * S.mem bc % 2 ^ w) ctr = r + 1 := by
          rw [Function.update_of_ne hne.symm]; exact hc
        rw [Function.update_apply, hS, hT, Nat.add_sub_cancel, Function.update_apply]
      obtain ⟨m, e', hacc', hrest⟩ := ih S1 (by subst hS1; rfl) (by rw [hm1, if_pos rfl])
        (hm.exec e) (by rw [hm1, if_neg hone, if_neg hone']; exact h1) hba hbc'
      refine ⟨m, (e.trans e').of_eq (by subst hS1; rfl) |>.cast (by ring), ?_, fun c h1 h2 => ?_⟩
      · rw [hacc', hm1, hm1, if_neg hne, if_pos rfl, if_neg hbc', if_neg hba, Nat.mod_mul_mod,
          pow_succ, mul_assoc, mul_comm (S.mem bc ^ r)]
      · rw [hrest c h1 h2, hm1, if_neg h2, if_neg h1]

theorem Fits.sub {p : Program} {A : ℕ} {c : Program} (h : Fits p A c) (i n : ℕ) :
    Fits p (A + i) ((c.drop i).take n) := by
  intro j hj
  simp only [List.length_take, List.length_drop] at hj
  rw [Nat.add_assoc, h (i + j) (by omega), List.getElem?_take, if_pos (by omega),
    List.getElem?_drop]

/-- `S'` differs from `S` only in `rT`, `rU` and the cells from `lo` to
`hi`, and not in the tapes. -/
def EvalFrame (lo hi : ℕ) (S S' : State) : Prop :=
  (∀ c, c ≠ rT → c ≠ rU → (c < lo ∨ hi ≤ c) → S'.mem c = S.mem c) ∧
    S'.input = S.input ∧ S'.inp = S.inp ∧ S'.out = S.out

theorem EvalFrame.trans {lo hi : ℕ} {S S₁ S₂ : State} (h₁ : EvalFrame lo hi S S₁)
    (h₂ : EvalFrame lo hi S₁ S₂) : EvalFrame lo hi S S₂ :=
  ⟨fun c h1 h2 h3 => (h₂.1 c h1 h2 h3).trans (h₁.1 c h1 h2 h3), h₂.2.1.trans h₁.2.1,
    h₂.2.2.1.trans h₁.2.2.1, h₂.2.2.2.trans h₁.2.2.2⟩

theorem EvalFrame.mono {lo hi lo' hi' : ℕ} {S S' : State} (h : EvalFrame lo hi S S')
    (hlo : lo' ≤ lo) (hhi : hi ≤ hi') : EvalFrame lo' hi' S S' :=
  ⟨fun c h1 h2 h3 => h.1 c h1 h2 (by omega), h.2.1, h.2.2.1, h.2.2.2⟩

theorem EvalFrame.srcOK {Q : ℕ → Prop} {lo hi : ℕ} {S S' : State} (h : EvalFrame lo hi S S')
    (hQ : ∀ a, a = rT ∨ a = rU ∨ (lo ≤ a ∧ a < hi) → Q a) {src : Src} {xs : List ℕ}
    (hs : SrcOK w Q S src xs) : SrcOK w Q S' src xs :=
  hs.frame (fun a ha => h.1 a (fun e => ha (hQ a (Or.inl e))) (fun e => ha (hQ a (Or.inr (Or.inl e))))
    (by by_contra hc; exact ha (hQ a (Or.inr (Or.inr (by omega)))))) h.2.1

theorem eval_spec (srcs : Fin s → Src) (te : ℕ) (xs : Fin s → List ℕ) (Q : ℕ → Prop)
    (e : HExpr s) :
    ∀ (d A : ℕ) (S : State), Fits p A (evalCode srcs te e d A) → S.pc = A →
      WordMem w S.mem → S.mem rZ = 0 → S.mem rOne = 1 → (∀ k, SrcOK w Q S (srcs k) (xs k)) →
      e.Fits w xs → 16 ≤ te → te + d + e.size + 2 < 2 ^ w →
      (∀ a, a = rT ∨ a = rU ∨ (te + d ≤ a ∧ a < te + d + e.size + 2) → Q a) →
      ∃ n ≤ 6 * e.cost xs, ∃ S', Exec w p n S S' ∧
        S'.pc = A + (evalCode srcs te e d A).length ∧ S'.mem (te + d) = e.eval xs % 2 ^ w ∧
        EvalFrame (te + d) (te + d + e.size + 2) S S' := by
  induction e with
  | lit n =>
      intro d A S hf hpc hm hz h1 hsrc hfit hte htop hQ
      refine ⟨1, by simp [HExpr.cost], _, x_set (fetch hf (i := 0) (by simp [hpc]) rfl)
        (by simp [HExpr.size] at htop; omega), by simp [hpc, evalCode], by simp [HExpr.eval],
        fun c _ _ hc => Function.update_of_ne (by simp [HExpr.size] at hc; omega) _ _,
        rfl, rfl, rfl⟩
  | len src =>
      intro d A S hf hpc hm hz h1 hsrc hfit hte htop hQ
      obtain ⟨hl1, hl2, hl3, -⟩ := hsrc src
      refine ⟨1, by simp [HExpr.cost], _, x_add (fetch hf (i := 0) (by simp [hpc]) rfl)
        (by simp [HExpr.size] at htop; omega) hl3 (by omega), by simp [hpc, evalCode],
        by simp [HExpr.eval, hl1, hz, Nat.mod_eq_of_lt hl2],
        fun c _ _ hc => Function.update_of_ne (by simp [HExpr.size] at hc; omega) _ _,
        rfl, rfl, rfl⟩
  | entry src i =>
      intro d A S hf hpc hm hz h1 hsrc hfit hte htop hQ
      simp only [HExpr.Fits] at hfit
      simp only [HExpr.size] at htop hQ
      obtain ⟨hl1, hl2, hl3, hl4, hl5⟩ := hsrc src
      simp only [evalCode] at hf ⊢
      rcases hk : (srcs src).kind with _ | _ | bc
      · rw [hk] at hl5; exact hl5.elim
      · rw [hk] at hf hl5
        have e := (x_set (w := w) (s := S) (fetch hf (i := 0) (by simp [hpc]) rfl)
          (by omega)).trans (x_inputLoad (fetch hf (i := 1) (by simp [hpc]) rfl)
            (hm.update _ (Nat.mod_lt _ (by positivity))) (by omega) (by omega))
        refine ⟨_, by simp [HExpr.cost], _, e, by simp [hpc], ?_, ?_, rfl, rfl, rfl⟩
        · simp only [Function.update_self, HExpr.eval, Nat.mod_eq_of_lt hfit, hl5,
            List.getD_eq_getElem?_getD]
        · intro c h1 h2 _
          simp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne h1]
      · rw [hk] at hf hl5
        obtain ⟨hb1, hb2, hb3, hb4⟩ := hl5
        have hbT : bc ≠ rT := fun h => hb2 (hQ _ (Or.inl h))
        have hbU : bc ≠ rU := fun h => hb2 (hQ _ (Or.inr (Or.inl h)))
        have hlT : (srcs src).lc ≠ rT := fun h => hl4 (hQ _ (Or.inl h))
        have hlU : (srcs src).lc ≠ rU := fun h => hl4 (hQ _ (Or.inr (Or.inl h)))
        have hld : (srcs src).lc ≠ te + d := fun h => hl4 (hQ _ (Or.inr (Or.inr (by omega))))
        have hbd : bc ≠ te + d := fun h => hb2 (hQ _ (Or.inr (Or.inr (by omega))))
        have e := ((x_set (w := w) (s := S) (fetch hf (i := 0) (by simp [hpc]) rfl)
          (by omega)).trans (x_set (fetch hf (i := 1) (by simp [hpc]) rfl) (by omega))).trans
          (x_sub (fetch hf (i := 2) (by simp [hpc]) rfl)
            ((hm.update _ (Nat.mod_lt _ (by positivity))).update _ (Nat.mod_lt _ (by positivity)))
            (by omega) hl3 (by omega))
        obtain ⟨S3, e, hS3⟩ := (⟨_, e, rfl⟩ : ∃ S', Exec w p (1 + 1 + 1) S S' ∧ S' = _)
        have hT3 : S3.mem rT = (xs src).length - i := by
          subst hS3; dsimp only
          rw [Function.update_self, Function.update_of_ne hlU, Function.update_of_ne hld,
            Function.update_self, hl1, Nat.mod_eq_of_lt hfit]
        have hm3 : ∀ c, c ≠ rT → c ≠ rU → c ≠ te + d → S3.mem c = S.mem c := by
          intro c h1 h2 h3; subst hS3; dsimp only
          rw [Function.update_of_ne h1, Function.update_of_ne h2, Function.update_of_ne h3]
        have hU3 : S3.mem rU = i := by
          subst hS3; dsimp only
          rw [Function.update_of_ne (by decide), Function.update_self, Nat.mod_eq_of_lt hfit]
        have hd3 : S3.mem (te + d) = 0 := by
          subst hS3; dsimp only
          rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
            Function.update_self, Nat.zero_mod]
        have hpc3 : S3.pc = A + 3 := by subst hS3; simp [hpc]
        have hw3 := hm.exec e
        by_cases hin : i < (xs src).length
        · have e' := ((x_jzero_neg (w := w) (s := S3) (fetch hf (i := 3) (by simp [hpc3]) rfl)
            (by omega) (by rw [hT3]; omega)).trans (x_add (fetch hf (i := 4) (by simp [hpc3]) rfl)
              (by omega) (by omega) hb1)).trans (x_load (fetch hf (i := 5) (by simp [hpc3]) rfl)
              (hw3.update _ (Nat.mod_lt _ (by positivity))) (by omega) (by omega))
          refine ⟨_, by simp [HExpr.cost], _, e.trans e', by simp [hpc3], ?_, ?_,
            by subst hS3; rfl, by subst hS3; rfl, by subst hS3; rfl⟩
          · obtain ⟨hv, hq⟩ := hb4 i hin
            have hiT : S.mem bc + i ≠ rT := fun h => hq (hQ _ (Or.inl h))
            have hiU : S.mem bc + i ≠ rU := fun h => hq (hQ _ (Or.inr (Or.inl h)))
            have hid : S.mem bc + i ≠ te + d := fun h => hq (hQ _ (Or.inr (Or.inr (by omega))))
            simp only [Function.update_self]
            rw [hU3, hm3 _ hbT hbU hbd, Nat.mod_eq_of_lt (by omega), Function.update_of_ne
              (by omega), Nat.add_comm, hm3 _ hiT hiU hid, hv, HExpr.eval]
          · intro c h1 h2 h3
            simp only
            rw [Function.update_of_ne (by omega), Function.update_of_ne h1,
              hm3 _ h1 h2 (by omega)]
        · have e' := x_jzero_pos (w := w) (s := S3) (fetch hf (i := 3) (by simp [hpc3]) rfl)
            (by omega) (by rw [hT3]; omega)
          refine ⟨_, by simp [HExpr.cost], _, e.trans e', by simp, ?_, ?_,
            by subst hS3; rfl, by subst hS3; rfl, by subst hS3; rfl⟩
          · simp only [hd3, HExpr.eval, List.getD_eq_getElem?_getD,
              List.getElem?_eq_none (by omega : (xs src).length ≤ i), Option.getD_none,
              Nat.zero_mod]
          · intro c h1 h2 h3
            simp only
            rw [hm3 _ h1 h2 (by omega)]
  | add a b iha ihb =>
      intro d A S hf hpc hm hz h1 hsrc hfit hte htop hQ
      simp only [HExpr.Fits] at hfit
      simp only [HExpr.size] at htop hQ
      simp only [evalCode, HExpr.size] at hf ⊢
      obtain ⟨hfa, hf⟩ := fits_append.1 hf
      obtain ⟨hfb, hfo⟩ := fits_append.1 hf
      obtain ⟨na, hna, Sa, ea, hpca, hva, fra⟩ := iha d A S hfa hpc hm hz h1 hsrc hfit.1 hte
        (by omega) (fun a ha => hQ a (by omega))
      have hsrc' := fun k => fra.srcOK (fun a ha => hQ a (by omega)) (hsrc k)
      obtain ⟨nb, hnb, Sb, eb, hpcb, hvb, frb⟩ := ihb (d + 1) _ Sa hfb hpca (hm.exec ea)
        (by rw [fra.1 _ (by omega) (by omega) (by omega)]; exact hz)
        (by rw [fra.1 _ (by omega) (by omega) (by omega)]; exact h1) hsrc' hfit.2 hte
        (by omega) (fun a ha => hQ a (by omega))
      have hva' : Sb.mem (te + d) = a.eval xs % 2 ^ w := by
        rw [frb.1 _ (by omega) (by omega) (by omega)]; exact hva
      have hmb := (hm.exec ea).exec eb
      have hvb' : Sb.mem (te + d + 1) = b.eval xs % 2 ^ w := hvb
      have e := (ea.trans eb).trans (x_add (fetch hfo (i := 0) (by simp [hpcb]) rfl)
        (by omega) (by omega) (by omega))
      refine ⟨na + nb + 1, by simp only [HExpr.cost]; omega, _, e, by simp [hpcb]; omega,
        ?_, ?_⟩
      · simp only [Function.update_self, hva', hvb', HExpr.eval, ← Nat.add_mod]
      · refine (fra.mono (by omega) (by omega)).trans ((frb.mono (by omega) (by omega)).trans
          ⟨fun c h1 h2 h3 => Function.update_of_ne (by omega) _ _, rfl, rfl, rfl⟩)
  | mul a b iha ihb =>
      intro d A S hf hpc hm hz h1 hsrc hfit hte htop hQ
      simp only [HExpr.Fits] at hfit
      simp only [HExpr.size] at htop hQ
      simp only [evalCode, HExpr.size] at hf ⊢
      obtain ⟨hfa, hf⟩ := fits_append.1 hf
      obtain ⟨hfb, hfo⟩ := fits_append.1 hf
      obtain ⟨na, hna, Sa, ea, hpca, hva, fra⟩ := iha d A S hfa hpc hm hz h1 hsrc hfit.1 hte
        (by omega) (fun a ha => hQ a (by omega))
      have hsrc' := fun k => fra.srcOK (fun a ha => hQ a (by omega)) (hsrc k)
      obtain ⟨nb, hnb, Sb, eb, hpcb, hvb, frb⟩ := ihb (d + 1) _ Sa hfb hpca (hm.exec ea)
        (by rw [fra.1 _ (by omega) (by omega) (by omega)]; exact hz)
        (by rw [fra.1 _ (by omega) (by omega) (by omega)]; exact h1) hsrc' hfit.2 hte
        (by omega) (fun a ha => hQ a (by omega))
      have hva' : Sb.mem (te + d) = a.eval xs % 2 ^ w := by
        rw [frb.1 _ (by omega) (by omega) (by omega)]; exact hva
      have hmb := (hm.exec ea).exec eb
      have hvb' : Sb.mem (te + d + 1) = b.eval xs % 2 ^ w := hvb
      have e := (ea.trans eb).trans (x_mul (fetch hfo (i := 0) (by simp [hpcb]) rfl)
        (by omega) (by omega) (by omega))
      refine ⟨na + nb + 1, by simp only [HExpr.cost]; omega, _, e, by simp [hpcb]; omega,
        ?_, ?_⟩
      · simp only [Function.update_self, hva', hvb', HExpr.eval, ← Nat.mul_mod]
      · refine (fra.mono (by omega) (by omega)).trans ((frb.mono (by omega) (by omega)).trans
          ⟨fun c h1 h2 h3 => Function.update_of_ne (by omega) _ _, rfl, rfl, rfl⟩)
  | pow a b iha ihb =>
      intro d A S hf hpc hm hz h1 hsrc hfit hte htop hQ
      simp only [HExpr.Fits] at hfit
      simp only [HExpr.size] at htop hQ
      simp only [evalCode, HExpr.size] at hf ⊢
      obtain ⟨hfa, hf⟩ := fits_append.1 hf
      obtain ⟨hfb, hfo⟩ := fits_append.1 hf
      obtain ⟨na, hna, Sa, ea, hpca, hva, fra⟩ := iha d A S hfa hpc hm hz h1 hsrc hfit.1 hte
        (by omega) (fun a ha => hQ a (by omega))
      have hsrc' := fun k => fra.srcOK (fun a ha => hQ a (by omega)) (hsrc k)
      obtain ⟨nb, hnb, Sb, eb, hpcb, hvb, frb⟩ := ihb (d + 1) _ Sa hfb hpca (hm.exec ea)
        (by rw [fra.1 _ (by omega) (by omega) (by omega)]; exact hz)
        (by rw [fra.1 _ (by omega) (by omega) (by omega)]; exact h1) hsrc' hfit.2.1 hte
        (by omega) (fun a ha => hQ a (by omega))
      have hva' : Sb.mem (te + d) = a.eval xs % 2 ^ w := by
        rw [frb.1 _ (by omega) (by omega) (by omega)]; exact hva
      have hmb := (hm.exec ea).exec eb
      have hvb' : Sb.mem (te + d + 1) = b.eval xs % 2 ^ w := hvb
      have hbx : b.eval xs % 2 ^ w = b.eval xs := Nat.mod_eq_of_lt hfit.2.2
      have hfl := Fits.sub hfo 1 4
      have e1 := x_set (w := w) (s := Sb) (fetch hfo (i := 0) (by simp [hpcb]) rfl)
        (show te + d + 2 < 2 ^ w by omega)
      obtain ⟨Sc, e1, hSc⟩ := (⟨_, e1, rfl⟩ : ∃ S', Exec w p 1 Sb S' ∧ S' = _)
      have hmc : ∀ c, c ≠ te + d + 2 → Sc.mem c = Sb.mem c := fun c hc => by
        subst hSc; exact Function.update_of_ne hc _ _
      obtain ⟨m, e2, hacc, hrest⟩ := pow_loop (p := p) (w := w) (acc := te + d + 2)
        (ctr := te + d + 1) (bc := te + d) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) hfl (b.eval xs) Sc (by subst hSc; simp [hpcb])
        (by rw [hmc _ (by omega), hvb', hbx]) (hmb.exec e1)
        (by rw [hmc _ (by omega), frb.1 _ (by omega) (by omega) (by omega),
          fra.1 _ (by omega) (by omega) (by omega)]; exact h1) (by omega) (by omega)
      have e3 := ((ea.trans eb).trans (e1.trans e2)).trans (x_add (fetch hfo (i := 5)
        (by simp [hpcb]) rfl) (show te + d < 2 ^ w by omega) (show te + d + 2 < 2 ^ w by omega)
        (by omega))
      refine ⟨na + nb + (1 + (4 * b.eval xs + 1)) + 1, by simp only [HExpr.cost]; omega, _, e3,
        by simp; omega, ?_, ?_⟩
      · have hSc2 : Sc.mem (te + d + 2) = 1 := by
          subst hSc; dsimp only; rw [Function.update_self, Nat.one_mod_eq_one.mpr (by omega)]
        have hSc0 : Sc.mem (te + d) = a.eval xs % 2 ^ w := by rw [hmc _ (by omega), hva']
        have hm0 : m rZ = 0 := by
          rw [hrest _ (by omega) (by omega), hmc _ (by omega),
            frb.1 _ (by omega) (by omega) (by omega), fra.1 _ (by omega) (by omega) (by omega), hz]
        simp only [Function.update_self]
        rw [hacc, hSc2, hSc0, hm0, HExpr.eval, one_mul, Nat.add_zero, Nat.mod_mod,
          ← Nat.pow_mod]
      · refine (fra.mono (by omega) (by omega)).trans ((frb.mono (by omega) (by omega)).trans
          ⟨fun c h1 h2 h3 => ?_, by subst hSc; rfl, by subst hSc; rfl, by subst hSc; rfl⟩)
        simp only
        rw [Function.update_of_ne (by omega), hrest _ (by omega) (by omega), hmc _ (by omega)]

/-! ### Segments -/

/-- The kind of the table entry of a segment. -/
def segKind (srcs : Fin s → Src) : Segment s → SegKind
  | .expr _ => .val
  | .slice src _ _ => (srcs src).kind

/-- The cells an evaluation of the segment uses above `te`. -/
def _root_.Lax185574Proofs.Simulate.Segment.size : Segment s → ℕ
  | .expr e => e.size
  | .slice _ st none => st.size
  | .slice _ st (some l) => st.size + l.size + 1

/-- Compute the table entry of segment `k` and add its length to `rTot`. -/
def segCode (srcs : Fin s → Src) (te tb k A : ℕ) : Segment s → Program
  | .expr e => evalCode srcs te e 0 A ++
      [.add (tb + 2 * k + 1) te rZ, .set (tb + 2 * k) 1, .add rTot rTot (tb + 2 * k)]
  | .slice src st none => evalCode srcs te st 0 A ++
      [.add (tb + 2 * k + 1) te rZ, .sub (tb + 2 * k) (srcs src).lc te,
        .add rTot rTot (tb + 2 * k)]
  | .slice src st (some l) => evalCode srcs te st 0 A ++
      (evalCode srcs te l 1 (A + (evalCode srcs te st 0 A).length) ++
      [.add (tb + 2 * k + 1) te rZ, .sub rU (srcs src).lc te, .sub rT rU (te + 1),
        .sub (tb + 2 * k) rU rT, .add rTot rTot (tb + 2 * k)])

theorem SegOK.frame₂ {Q P : ℕ → Prop} {S S' : State} {len st : ℕ} {seg : List ℕ}
    {k : SegKind} (h : SegOK w Q S len st seg k) (hP : ∀ a, ¬ P a → S'.mem a = S.mem a)
    (hi : S'.input = S.input)
    (hk : ∀ bc, k = .mem bc → ¬ P bc ∧ ∀ d < len, ¬ P (S.mem bc + st + d)) :
    SegOK w Q S' len st seg k := by
  cases k with
  | val => exact h
  | input => simpa only [SegOK, hi] using h
  | mem bc =>
      obtain ⟨hP1, hP2⟩ := hk bc rfl
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      refine ⟨h1, fun h => by rw [hP _ hP1]; exact h2 h, h3, h4, fun d hd => ?_⟩
      rw [hP _ hP1]
      obtain ⟨h6, h7⟩ := h5 d hd
      exact ⟨by rw [hP _ (hP2 d hd)]; exact h6, h7⟩

/-- The table entry of a slice of source `src` from `st` of length `len`. -/
theorem SrcOK.segOK {Q Q' : ℕ → Prop} {S : State} {src : Src} {xs : List ℕ} {st len : ℕ}
    (h : SrcOK w Q S src xs) (hQ : ∀ a, Q' a → Q a) (hlen : len ≤ xs.length - st) :
    SegOK w Q' S len st ((xs.drop st).take len) src.kind := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  rcases hk : src.kind with _ | _ | bc
  · rw [hk] at h5; exact h5.elim
  · rw [hk] at h5
    exact ⟨by rw [h5], fun h0 => by rw [h5]; omega, by rw [h5]; exact h2⟩
  · rw [hk] at h5
    obtain ⟨h6, h7, h8, h9⟩ := h5
    refine ⟨by simp; omega, fun _ => by omega, h6, fun h => h7 (hQ _ h), fun d hd => ?_⟩
    obtain ⟨h10, h11⟩ := h9 (st + d) (by omega)
    refine ⟨?_, fun h => h11 (hQ _ (by rw [← Nat.add_assoc]; exact h))⟩
    rw [Nat.add_assoc, h10, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take, if_pos hd, List.getElem?_drop]

theorem take_min_drop (xs : List ℕ) (st l : ℕ) :
    (xs.drop st).take (xs.length - st - (xs.length - st - l)) = (xs.drop st).take l := by
  rw [show xs.length - st - (xs.length - st - l) = min l (xs.drop st).length by
    simp; omega]
  rcases le_total l (xs.drop st).length with h | h
  · rw [min_eq_left h]
  · rw [min_eq_right h, List.take_of_length_le h, List.take_of_length_le le_rfl]

theorem seg_spec (srcs : Fin s → Src) (te tb k A T0 : ℕ) (xs : Fin s → List ℕ)
    (Q Q' : ℕ → Prop) (hQQ : ∀ a, Q' a → Q a) (seg : Segment s) (S : State)
    (hf : Fits p A (segCode srcs te tb k A seg)) (hpc : S.pc = A) (hm : WordMem w S.mem)
    (hz : S.mem rZ = 0) (h1 : S.mem rOne = 1) (hsrc : ∀ j, SrcOK w Q S (srcs j) (xs j))
    (hfit : seg.Fits w xs) (hte : 16 ≤ te) (htop : te + seg.size + 3 < 2 ^ w)
    (hQ : ∀ a, a = rT ∨ a = rU ∨ a = rTot ∨ a = tb + 2 * k ∨ a = tb + 2 * k + 1 ∨
      (te ≤ a ∧ a < te + seg.size + 3) → Q a)
    (htb : 16 ≤ tb + 2 * k) (htbte : tb + 2 * k + 2 ≤ te) (hT : S.mem rTot = T0)
    (hT' : T0 + (seg.apply xs).length < 2 ^ w) :
    ∃ n ≤ 6 * seg.cost xs + 5, ∃ S', Exec w p n S S' ∧
      S'.pc = A + (segCode srcs te tb k A seg).length ∧
      S'.mem (tb + 2 * k) = (seg.apply xs).length ∧
      SegOK w Q' S' (S'.mem (tb + 2 * k)) (S'.mem (tb + 2 * k + 1)) (seg.apply xs)
        (segKind srcs seg) ∧
      S'.mem rTot = T0 + (seg.apply xs).length ∧
      (∀ c, c ≠ rT → c ≠ rU → c ≠ rTot → c ≠ tb + 2 * k → c ≠ tb + 2 * k + 1 →
        (c < te ∨ te + seg.size + 3 ≤ c) → S'.mem c = S.mem c) ∧
      S'.input = S.input ∧ S'.inp = S.inp ∧ S'.out = S.out ∧
      (∀ src st l, seg = .slice src st l → S'.mem (tb + 2 * k + 1) = st.eval xs) := by
  have a1 : rTot ≠ tb + 2 * k := by omega
  have a2 : rTot ≠ tb + 2 * k + 1 := by omega
  have a3 : tb + 2 * k ≠ tb + 2 * k + 1 := by omega
  have h1w : 1 % 2 ^ w = 1 := Nat.one_mod_eq_one.mpr (by omega)
  cases seg with
  | expr e =>
      simp only [Segment.size] at htop hQ
      simp only [Segment.Fits] at hfit
      simp only [segCode] at hf ⊢
      obtain ⟨hfe, hft⟩ := fits_append.1 hf
      obtain ⟨n, hn, S1, e1, hpc1, hv1, fr1⟩ := eval_spec srcs te xs Q e 0 A S hfe hpc hm hz h1
        hsrc hfit hte (by omega) (fun a ha => hQ a (by omega))
      have hz1 : S1.mem rZ = 0 := by rw [fr1.1 _ (by omega) (by omega) (by omega)]; exact hz
      have hT1 : S1.mem rTot = T0 := by rw [fr1.1 _ (by omega) (by omega) (by omega)]; exact hT
      have e2 := ((x_add (w := w) (s := S1) (fetch hft (i := 0) (by simp [hpc1]) rfl) (by omega)
        (by omega) (by omega)).trans (x_set (fetch hft (i := 1) (by simp [hpc1]) rfl)
          (by omega))).trans (x_add (fetch hft (i := 2) (by simp [hpc1]) rfl) (by omega)
            (by omega) (by omega))
      obtain ⟨S2, e2, hS2⟩ := (⟨_, e2, rfl⟩ : ∃ S', Exec w p (1 + 1 + 1) S1 S' ∧ S' = _)
      have hlen : (Segment.apply xs (.expr e)).length = 1 := rfl
      have hv1' : S1.mem te = e.eval xs % 2 ^ w := hv1
      have hT01 : (T0 + 1) % 2 ^ w = T0 + 1 := Nat.mod_eq_of_lt (by simp [Segment.apply] at hT'; omega)
      have hm2 : ∀ c, S2.mem c = if c = rTot then T0 + 1 else if c = tb + 2 * k then 1 else
          if c = tb + 2 * k + 1 then e.eval xs % 2 ^ w else S1.mem c := by
        intro c; subst hS2; dsimp only
        simp only [Function.update_apply, if_neg a1, if_neg a2, if_neg a3, if_true, hT1, hz1,
          Nat.add_zero, hv1', h1w, hT01, Nat.mod_mod]
      refine ⟨n + (1 + 1 + 1), by simp only [Segment.cost]; omega, S2, e1.trans e2,
        by subst hS2; simp [hpc1]; omega, by rw [hm2, if_neg a1.symm, if_pos rfl]; rfl, ?_,
        by rw [hm2, if_pos rfl]; rfl, fun c h1 h2 h3 h4 h5 h6 => ?_,
        by subst hS2; exact fr1.2.1, by subst hS2; exact fr1.2.2.1, by subst hS2; exact fr1.2.2.2,
        fun _ _ _ h => by cases h⟩
      · rw [hm2 (tb + 2 * k), if_neg a1.symm, if_pos rfl, hm2 (tb + 2 * k + 1), if_neg a2.symm,
          if_neg a3.symm, if_pos rfl]
        exact ⟨rfl, e.eval xs, rfl, rfl⟩
      · rw [hm2, if_neg h3, if_neg h4, if_neg h5,
          fr1.1 _ h1 h2 (by simp only [Segment.size] at h6; omega)]
  | slice src st l =>
    cases l with
    | none =>
      simp only [Segment.size] at htop hQ
      simp only [Segment.Fits] at hfit
      simp only [segCode, segKind, Segment.apply] at hf hT' ⊢
      obtain ⟨hfe, hft⟩ := fits_append.1 hf
      obtain ⟨n, hn, S1, e1, hpc1, hv1, fr1⟩ := eval_spec srcs te xs Q st 0 A S hfe hpc hm hz h1
        hsrc hfit.1 hte (by omega) (fun a ha => hQ a (by omega))
      have hsrc1 := fun j => fr1.srcOK (fun a ha => hQ a (by omega)) (hsrc j)
      obtain ⟨hl1, hl2, hl3, hl4, -⟩ := hsrc1 src
      have hz1 : S1.mem rZ = 0 := by rw [fr1.1 _ (by omega) (by omega) (by omega)]; exact hz
      have hT1 : S1.mem rTot = T0 := by rw [fr1.1 _ (by omega) (by omega) (by omega)]; exact hT
      have hv1' : S1.mem te = st.eval xs := by
        rw [show te = te + 0 from rfl, hv1, Nat.mod_eq_of_lt hfit.2]
      have hlcB : (srcs src).lc ≠ tb + 2 * k + 1 := fun h => hl4 (hQ _ (by omega))
      have e2 := ((x_add (w := w) (s := S1) (fetch hft (i := 0) (by simp [hpc1]) rfl) (by omega)
        (by omega) (by omega)).trans (x_sub (fetch hft (i := 1) (by simp [hpc1]) rfl)
          ((hm.exec e1).update _ (Nat.mod_lt _ (by positivity))) (by omega) hl3
          (by omega))).trans (x_add (fetch hft (i := 2) (by simp [hpc1]) rfl) (by omega)
            (by omega) (by omega))
      obtain ⟨S2, e2, hS2⟩ := (⟨_, e2, rfl⟩ : ∃ S', Exec w p (1 + 1 + 1) S1 S' ∧ S' = _)
      have hTl : (T0 + ((xs src).length - st.eval xs)) % 2 ^ w =
          T0 + ((xs src).length - st.eval xs) := Nat.mod_eq_of_lt (by simp at hT'; omega)
      have hm2 : ∀ c, S2.mem c = if c = rTot then T0 + ((xs src).length - st.eval xs) else
          if c = tb + 2 * k then (xs src).length - st.eval xs else
          if c = tb + 2 * k + 1 then st.eval xs else S1.mem c := by
        intro c; subst hS2; dsimp only
        simp only [Function.update_apply, if_neg a1, if_neg a2, if_neg a3, if_true, hT1, hz1,
          Nat.add_zero, hv1', if_neg hlcB, if_neg (show te ≠ tb + 2 * k + 1 by omega), hl1,
          Nat.mod_eq_of_lt hfit.2]
        rw [hTl]
      have hfr : ∀ c, ¬ Q c → S2.mem c = S.mem c := by
        intro c hc
        rw [hm2, if_neg (fun h => hc (hQ _ (by omega))), if_neg (fun h => hc (hQ _ (by omega))),
          if_neg (fun h => hc (hQ _ (by omega))), fr1.1 _ (fun h => hc (hQ _ (by omega)))
            (fun h => hc (hQ _ (by omega))) (by by_contra h; exact hc (hQ _ (by omega)))]
      have hin2 : S2.input = S.input := by subst hS2; exact fr1.2.1
      refine ⟨n + (1 + 1 + 1), by simp only [Segment.cost]; omega, S2, e1.trans e2,
        by subst hS2; simp [hpc1]; omega, by rw [hm2, if_neg a1.symm, if_pos rfl]; simp, ?_,
        by rw [hm2, if_pos rfl]; simp, fun c h1 h2 h3 h4 h5 h6 => ?_, hin2,
        by subst hS2; exact fr1.2.2.1, by subst hS2; exact fr1.2.2.2, fun _ _ _ h => by
          cases h; rw [hm2, if_neg a2.symm, if_neg a3.symm, if_pos rfl]⟩
      · rw [hm2 (tb + 2 * k), if_neg a1.symm, if_pos rfl, hm2 (tb + 2 * k + 1), if_neg a2.symm,
          if_neg a3.symm, if_pos rfl]
        have := ((hsrc src).frame hfr hin2).segOK (Q' := Q') hQQ (st := st.eval xs)
          (len := (xs src).length - st.eval xs) le_rfl
        rwa [List.take_of_length_le (by simp)] at this
      · rw [hm2, if_neg h3, if_neg h4, if_neg h5,
          fr1.1 _ h1 h2 (by simp only [Segment.size] at h6; omega)]
    | some l =>
      simp only [Segment.size] at htop hQ
      simp only [Segment.Fits] at hfit
      simp only [segCode, segKind, Segment.apply] at hf hT' ⊢
      obtain ⟨hfe, hf⟩ := fits_append.1 hf
      obtain ⟨hfl, hft⟩ := fits_append.1 hf
      obtain ⟨n, hn, S1, e1, hpc1, hv1, fr1⟩ := eval_spec srcs te xs Q st 0 A S hfe hpc hm hz h1
        hsrc hfit.1 hte (by omega) (fun a ha => hQ a (by omega))
      have hsrc1 := fun j => fr1.srcOK (fun a ha => hQ a (by omega)) (hsrc j)
      obtain ⟨n', hn', S2, e2, hpc2, hv2, fr2⟩ := eval_spec srcs te xs Q l 1 _ S1 hfl hpc1
        (hm.exec e1) (by rw [fr1.1 _ (by omega) (by omega) (by omega)]; exact hz)
        (by rw [fr1.1 _ (by omega) (by omega) (by omega)]; exact h1) hsrc1 hfit.2.2.1 hte
        (by omega) (fun a ha => hQ a (by omega))
      have hsrc2 := fun j => fr2.srcOK (fun a ha => hQ a (by omega)) (hsrc1 j)
      obtain ⟨hl1, hl2, hl3, hl4, -⟩ := hsrc2 src
      have hz2 : S2.mem rZ = 0 := by
        rw [fr2.1 _ (by omega) (by omega) (by omega), fr1.1 _ (by omega) (by omega) (by omega)]
        exact hz
      have hT2 : S2.mem rTot = T0 := by
        rw [fr2.1 _ (by omega) (by omega) (by omega), fr1.1 _ (by omega) (by omega) (by omega)]
        exact hT
      have hv1' : S2.mem te = st.eval xs := by
        rw [fr2.1 _ (by omega) (by omega) (by omega), show te = te + 0 from rfl, hv1,
          Nat.mod_eq_of_lt hfit.2.1]
      have hv2' : S2.mem (te + 1) = l.eval xs := by
        have : S2.mem (te + 1) = HExpr.eval xs l % 2 ^ w := hv2
        rw [this, Nat.mod_eq_of_lt hfit.2.2.2]
      have hlcB : (srcs src).lc ≠ tb + 2 * k + 1 := fun h => hl4 (hQ _ (by omega))
      have hlcU : (srcs src).lc ≠ rU := fun h => hl4 (hQ _ (by omega))
      have hm2w := (hm.exec e1).exec e2
      have hpc2' : S2.pc = A + (evalCode srcs te st 0 A).length +
          (evalCode srcs te l 1 (A + (evalCode srcs te st 0 A).length)).length := hpc2
      obtain ⟨S3, e3, hpc3, hm3, hi3, hn3, ho3⟩ := (x_add (w := w) (s := S2)
        (fetch hft (i := 0) (by simp [hpc2']) rfl) (by omega) (by omega) (by omega)).upd
      obtain ⟨S4, e4, hpc4, hm4, hi4, hn4, ho4⟩ := (x_sub (w := w) (s := S3)
        (fetch hft (i := 1) (by simp [hpc3, hpc2']) rfl) (hm2w.exec e3) (by omega) hl3
        (by omega)).upd
      obtain ⟨S5, e5, hpc5, hm5, hi5, hn5, ho5⟩ := (x_sub (w := w) (s := S4)
        (fetch hft (i := 2) (by simp [hpc4, hpc3, hpc2']) rfl) ((hm2w.exec e3).exec e4)
        (by omega) (by omega) (by omega)).upd
      obtain ⟨S6, e6, hpc6, hm6, hi6, hn6, ho6⟩ := (x_sub (w := w) (s := S5)
        (fetch hft (i := 3) (by simp [hpc5, hpc4, hpc3, hpc2']) rfl)
        (((hm2w.exec e3).exec e4).exec e5) (by omega) (by omega) (by omega)).upd
      obtain ⟨S7, e7, hpc7, hm7, hi7, hn7, ho7⟩ := (x_add (w := w) (s := S6)
        (fetch hft (i := 4) (by simp [hpc6, hpc5, hpc4, hpc3, hpc2']) rfl) (by omega) (by omega)
        (by omega)).upd
      have hM : S4.mem rU = (xs src).length - st.eval xs := by
        rw [hm4, if_pos rfl, hm3, if_neg hlcB, hl1, hm3, if_neg (by omega), hv1']
      have hU5 : S5.mem rU = (xs src).length - st.eval xs := by rw [hm5, if_neg (by decide), hM]
      have hT5 : S5.mem rT = (xs src).length - st.eval xs - l.eval xs := by
        rw [hm5, if_pos rfl, hM, hm4, if_neg (by omega), hm3, if_neg (by omega), hv2']
      have hB6 : S6.mem (tb + 2 * k) = (xs src).length - st.eval xs -
          ((xs src).length - st.eval xs - l.eval xs) := by
        rw [hm6, if_pos rfl, hU5, hT5]
      have hlen : (List.take (l.eval xs) (List.drop (st.eval xs) (xs src))).length =
          (xs src).length - st.eval xs - ((xs src).length - st.eval xs - l.eval xs) := by
        simp; omega
      have h72 : ∀ c, c ≠ rTot → c ≠ tb + 2 * k → c ≠ tb + 2 * k + 1 → c ≠ rU → c ≠ rT →
          S7.mem c = S2.mem c := by
        intro c h1 h2 h3 h4 h5
        rw [hm7, if_neg h1, hm6, if_neg h2, hm5, if_neg h5, hm4, if_neg h4, hm3, if_neg h3]
      have h20 : ∀ c, c ≠ rT → c ≠ rU → (c < te ∨ te + (st.size + l.size + 1) + 3 ≤ c) →
          S2.mem c = S.mem c := by
        intro c h1 h2 h3
        rw [fr2.1 _ h1 h2 (by omega), fr1.1 _ h1 h2 (by omega)]
      have hB7 : S7.mem (tb + 2 * k) = (xs src).length - st.eval xs -
          ((xs src).length - st.eval xs - l.eval xs) := by
        rw [hm7, if_neg a1.symm, hB6]
      have hB17 : S7.mem (tb + 2 * k + 1) = st.eval xs := by
        rw [hm7, if_neg a2.symm, hm6, if_neg a3.symm, hm5, if_neg (by omega), hm4,
          if_neg (by omega), hm3, if_pos rfl, hv1', hz2, Nat.add_zero,
          Nat.mod_eq_of_lt hfit.2.1]
      have hTot7 : S7.mem rTot = T0 + (List.take (l.eval xs)
          (List.drop (st.eval xs) (xs src))).length := by
        rw [hm7, if_pos rfl, hm6, if_neg a1, hm5, if_neg (by decide), hm4, if_neg (by decide),
          hm3, if_neg a2, hT2, hB6, ← hlen, Nat.mod_eq_of_lt (by omega)]
      have hfr : ∀ c, ¬ Q c → S7.mem c = S.mem c := by
        intro c hc
        rw [h72 c (fun h => hc (hQ _ (by omega))) (fun h => hc (hQ _ (by omega)))
          (fun h => hc (hQ _ (by omega))) (fun h => hc (hQ _ (by omega)))
          (fun h => hc (hQ _ (by omega))), h20 c (fun h => hc (hQ _ (by omega)))
          (fun h => hc (hQ _ (by omega))) (by by_contra h; exact hc (hQ _ (by omega)))]
      have hin7 : S7.input = S.input := by rw [hi7, hi6, hi5, hi4, hi3, fr2.2.1, fr1.2.1]
      refine ⟨n + n' + (1 + 1 + 1 + 1 + 1), by simp only [Segment.cost]; omega, S7,
        (e1.trans e2).trans ((((e3.trans e4).trans e5).trans e6).trans e7),
        by simp [hpc7, hpc6, hpc5, hpc4, hpc3, hpc2']; omega, by rw [hB7, hlen], ?_, hTot7,
        fun c h1 h2 h3 h4 h5 h6 => ?_, hin7,
        by rw [hn7, hn6, hn5, hn4, hn3, fr2.2.2.1, fr1.2.2.1],
        by rw [ho7, ho6, ho5, ho4, ho3, fr2.2.2.2, fr1.2.2.2], fun _ _ _ h => by
          cases h; exact hB17⟩
      · rw [hB7, hB17]
        have := ((hsrc src).frame hfr hin7).segOK (Q' := Q') hQQ (st := st.eval xs)
          (len := (xs src).length - st.eval xs - ((xs src).length - st.eval xs - l.eval xs))
          (by omega)
        rwa [take_min_drop] at this
      · simp only [Segment.size] at h6
        rw [h72 c h3 h4 h5 h2 h1, h20 c h1 h2 (by omega)]

/-- Compute the table entries of the segments `ρ`, the first at index `k`. -/
def rwCode (srcs : Fin s → Src) (te tb : ℕ) : List (Segment s) → ℕ → ℕ → Program
  | [], _, _ => []
  | seg :: ρ, k, A => segCode srcs te tb k A seg ++
      rwCode srcs te tb ρ (k + 1) (A + (segCode srcs te tb k A seg).length)

theorem Segment.cost_pos (xs : Fin s → List ℕ) (seg : Segment s) : 1 ≤ seg.cost xs := by
  cases seg with
  | expr e => simp [Segment.cost]
  | slice src st l => cases l <;> simp [Segment.cost]

theorem SrcOK.avoid {Q : ℕ → Prop} {S : State} {src : Src} {ys : List ℕ} {bc : ℕ}
    (h : SrcOK w Q S src ys) (hk : src.kind = .mem bc) {st len : ℕ}
    (hlen : len ≤ ys.length - st) : ¬ Q bc ∧ ∀ d < len, ¬ Q (S.mem bc + st + d) := by
  obtain ⟨-, -, -, -, h5⟩ := h
  rw [hk] at h5
  obtain ⟨-, h7, -, h9⟩ := h5
  exact ⟨h7, fun d hd => by rw [Nat.add_assoc]; exact (h9 (st + d) (by omega)).2⟩

theorem rw_spec (srcs : Fin s → Src) (te tb D : ℕ) (xs : Fin s → List ℕ) (Q Q' : ℕ → Prop)
    (hQQ : ∀ a, Q' a → Q a) (hte : 16 ≤ te) (htb : 16 ≤ tb) (hD : te + D < 2 ^ w) :
    ∀ (ρ : Rewrite s) (k A T0 : ℕ) (S : State), Fits p A (rwCode srcs te tb ρ k A) → S.pc = A →
      WordMem w S.mem → S.mem rZ = 0 → S.mem rOne = 1 → (∀ j, SrcOK w Q S (srcs j) (xs j)) →
      (∀ seg ∈ ρ, seg.Fits w xs ∧ seg.size + 3 ≤ D) →
      (∀ a, a = rT ∨ a = rU ∨ a = rTot ∨ (tb + 2 * k ≤ a ∧ a < tb + 2 * (k + ρ.length)) ∨
        (te ≤ a ∧ a < te + D) → Q a) →
      (∀ a, tb + 2 * k ≤ a → a < tb + 2 * (k + ρ.length) → ¬ Q' a) →
      tb + 2 * (k + ρ.length) ≤ te → S.mem rTot = T0 → T0 + (Rewrite.apply ρ xs).length < 2 ^ w →
      ∃ n ≤ 11 * (ρ.map (·.cost xs)).sum, ∃ S', Exec w p n S S' ∧
        S'.pc = A + (rwCode srcs te tb ρ k A).length ∧
        TableOK w Q' S' (ρ.map (segKind srcs)) (tb + 2 * k) (ρ.map (·.apply xs)) ∧
        S'.mem rTot = T0 + (Rewrite.apply ρ xs).length ∧
        (∀ c, c ≠ rT → c ≠ rU → c ≠ rTot → (c < tb + 2 * k ∨ tb + 2 * (k + ρ.length) ≤ c) →
          (c < te ∨ te + D ≤ c) → S'.mem c = S.mem c) ∧
        S'.input = S.input ∧ S'.inp = S.inp ∧ S'.out = S.out := by
  intro ρ
  induction ρ with
  | nil =>
      intro k A T0 S hf hpc hm hz h1 hsrc hseg hQ hQ' htbte hT hT'
      exact ⟨0, by simp, S, Exec.refl S, by simp [hpc, rwCode], by simp [TableOK],
        by simp [hT, Rewrite.apply], fun _ _ _ _ _ _ => rfl, rfl, rfl, rfl⟩
  | cons seg ρ ih =>
      intro k A T0 S hf hpc hm hz h1 hsrc hseg hQ hQ' htbte hT hT'
      simp only [rwCode] at hf ⊢
      simp only [List.length_cons] at hQ hQ' htbte
      obtain ⟨hf1, hf2⟩ := fits_append.1 hf
      have hseg1 := hseg seg (by simp)
      have happ : (Rewrite.apply (seg :: ρ) xs).length =
          (seg.apply xs).length + (Rewrite.apply ρ xs).length := by
        simp [Rewrite.apply]
      obtain ⟨n₁, hn₁, S1, e1, hpc1, hlen1, hok1, hT1, fr1, hi1, hn1, ho1, hst1⟩ :=
        seg_spec srcs te tb k A T0 xs Q Q' hQQ seg S hf1 hpc hm hz h1 hsrc hseg1.1 hte
          (by omega) (fun a ha => hQ a (by omega)) (by omega) (by omega) hT (by omega)
      have hfr1 : ∀ c, ¬ Q c → S1.mem c = S.mem c := fun c hc =>
        fr1 c (fun h => hc (hQ _ (by omega))) (fun h => hc (hQ _ (by omega)))
          (fun h => hc (hQ _ (by omega))) (fun h => hc (hQ _ (by omega)))
          (fun h => hc (hQ _ (by omega))) (by by_contra h; exact hc (hQ _ (by omega)))
      have hsrc1 := fun j => (hsrc j).frame hfr1 hi1
      obtain ⟨n₂, hn₂, S2, e2, hpc2, htab2, hT2, fr2, hi2, hn2, ho2⟩ :=
        ih (k + 1) _ (T0 + (seg.apply xs).length) S1 hf2 hpc1 (hm.exec e1)
          (by rw [fr1 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact hz)
          (by rw [fr1 _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h1)
          hsrc1 (fun s hs => hseg s (by simp [hs])) (fun a ha => hQ a (by omega))
          (fun a h1 h2 => hQ' a (by omega) (by omega)) (by omega) hT1 (by omega)
      have hB : S2.mem (tb + 2 * k) = S1.mem (tb + 2 * k) :=
        fr2 _ (by omega) (by omega) (by omega) (by omega) (by omega)
      have hB1 : S2.mem (tb + 2 * k + 1) = S1.mem (tb + 2 * k + 1) :=
        fr2 _ (by omega) (by omega) (by omega) (by omega) (by omega)
      refine ⟨n₁ + n₂, ?_, S2, e1.trans e2, by rw [hpc2]; simp; omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · have := Segment.cost_pos xs seg
        simp only [List.map_cons, List.sum_cons]; omega
      · refine ⟨hQ' _ (by omega) (by omega), hQ' _ (by omega) (by omega), ?_, ?_⟩
        · rw [hB, hB1]
          refine hok1.frame₂ (P := fun c => c = rT ∨ c = rU ∨ c = rTot ∨
            (tb + 2 * (k + 1) ≤ c ∧ c < tb + 2 * (k + 1 + ρ.length)) ∨ (te ≤ c ∧ c < te + D))
            (fun c hc => fr2 c (fun h => hc (Or.inl h)) (fun h => hc (Or.inr (Or.inl h)))
              (fun h => hc (Or.inr (Or.inr (Or.inl h))))
              (by by_contra h; exact hc (Or.inr (Or.inr (Or.inr (Or.inl (by omega))))))
              (by by_contra h; exact hc (Or.inr (Or.inr (Or.inr (Or.inr (by omega)))))))
            hi2 ?_
          intro bc hk
          cases seg with
          | expr e => simp [segKind] at hk
          | slice src st l =>
              simp only [segKind] at hk
              have hle : S1.mem (tb + 2 * k) ≤ (xs src).length - S1.mem (tb + 2 * k + 1) := by
                rw [hlen1]
                rw [hst1 src st l rfl]
                cases l <;> simp [Segment.apply]
              obtain ⟨hb, hd⟩ := (hsrc1 src).avoid hk hle
              exact ⟨fun h => hb (hQ _ (by omega)), fun d hd' => fun h => hd d hd' (hQ _ (by omega))⟩
        · simpa [Nat.mul_add, Nat.add_assoc] using htab2
      · rw [hT2, happ, Nat.add_assoc]
      · intro c h1 h2 h3 h4 h5
        simp only [List.length_cons] at h4
        have := hseg1.2
        rw [fr2 c h1 h2 h3 (by omega) h5, fr1 c h1 h2 h3 (by omega) (by omega) (by omega)]
      · rw [hi2, hi1]
      · rw [hn2, hn1]
      · rw [ho2, ho1]

end Lax185574Proofs.RamSim
