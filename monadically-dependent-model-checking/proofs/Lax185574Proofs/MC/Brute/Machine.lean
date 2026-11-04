import Lax185574Proofs.Legacy
import Mathlib.Tactic

/-!
A stack machine that evaluates a first-order sentence on a graph, for
the brute-force thread of thm:mc.

The machine reads the prefix code of the formula (`InstanceEncoding.code`)
from a word `cd`. Its configuration is a mode (evaluate the subformula at
a position, or return a truth value), a stack of frames, and the
assignment of the bound variables as a list (de Bruijn levels). It uses
the end positions `fe` of the subformulas, which a program computes
beforehand, and the adjacency test `A`. `machine_eval` shows that
evaluating the code of `ψ` returns its truth value with the same stack
and assignment, in at most `bsteps n ψ` steps.
-/

namespace Lax185574Proofs.MC.Brute

open Lax3.FirstOrder Lax185574.InstanceEncoding

/-- A frame of the stack. -/
inductive Fr
  /-- Negate the returned value. -/
  | neg
  /-- The left conjunct is being evaluated, the right one starts at `r`. -/
  | andL (r : ℕ)
  /-- The right conjunct is being evaluated. -/
  | andR
  /-- The quantified subformula at `pc` is being evaluated with value `v`. -/
  | ex (pc v : ℕ)
  deriving DecidableEq

/-- A configuration. -/
structure Cfg where
  /-- Evaluate (`true`) or return (`false`). -/
  ev : Bool
  /-- The position evaluated. -/
  pos : ℕ
  /-- The value returned. -/
  val : Bool
  /-- The stack, top first. -/
  stk : List Fr
  /-- The assignment, by level. -/
  asg : List ℕ

/-- One step, or `none` once the empty stack receives a value. -/
def step (n : ℕ) (A : ℕ → ℕ → Bool) (cd : List ℕ) (fe : ℕ → ℕ) (c : Cfg) : Option Cfg :=
  if c.ev then
    match cd.getD c.pos 0 with
    | 0 => some ⟨false, c.pos,
        A (c.asg.getD (cd.getD (c.pos + 1) 0) 0) (c.asg.getD (cd.getD (c.pos + 2) 0) 0), c.stk, c.asg⟩
    | 1 => some ⟨false, c.pos,
        c.asg.getD (cd.getD (c.pos + 1) 0) 0 == c.asg.getD (cd.getD (c.pos + 2) 0) 0, c.stk, c.asg⟩
    | 2 => some { c with pos := c.pos + 1, stk := .neg :: c.stk }
    | 3 => some { c with pos := c.pos + 1, stk := .andL (fe (c.pos + 1)) :: c.stk }
    | _ => if n = 0 then some { c with ev := false, val := false }
        else some ⟨true, c.pos + 1, c.val, .ex (c.pos + 1) 0 :: c.stk, c.asg ++ [0]⟩
  else
    match c.stk with
    | [] => none
    | .neg :: s => some { c with val := !c.val, stk := s }
    | .andL r :: s => if c.val then some { c with ev := true, pos := r, stk := .andR :: s }
        else some { c with stk := s }
    | .andR :: s => some { c with stk := s }
    | .ex pc v :: s => if c.val then some { c with stk := s, asg := c.asg.dropLast }
        else if v + 1 < n then
          some ⟨true, pc, c.val, .ex pc (v + 1) :: s, c.asg.dropLast ++ [v + 1]⟩
        else some { c with stk := s, asg := c.asg.dropLast }

/-- `t` steps. -/
def iter (n : ℕ) (A : ℕ → ℕ → Bool) (cd : List ℕ) (fe : ℕ → ℕ) : ℕ → Cfg → Option Cfg
  | 0, c => some c
  | t + 1, c => (step n A cd fe c).bind (iter n A cd fe t)

theorem iter_add (n : ℕ) (A : ℕ → ℕ → Bool) (cd : List ℕ) (fe : ℕ → ℕ) :
    ∀ (s t : ℕ) (c : Cfg), iter n A cd fe (s + t) c = (iter n A cd fe s c).bind (iter n A cd fe t)
  | 0, t, c => by simp [iter]
  | s + 1, t, c => by
      rw [show s + 1 + t = (s + t) + 1 by omega, iter, iter]
      cases step n A cd fe c with
      | none => rfl
      | some c' => exact iter_add n A cd fe s t c'

theorem iter_trans {n : ℕ} {A : ℕ → ℕ → Bool} {cd : List ℕ} {fe : ℕ → ℕ} {s t : ℕ} {c c' c'' : Cfg}
    (h₁ : iter n A cd fe s c = some c') (h₂ : iter n A cd fe t c' = some c'') :
    iter n A cd fe (s + t) c = some c'' := by
  rw [iter_add, h₁]; exact h₂

theorem iter_one {n : ℕ} {A : ℕ → ℕ → Bool} {cd : List ℕ} {fe : ℕ → ℕ} {c c' : Cfg}
    (h : step n A cd fe c = some c') : iter n A cd fe 1 c = some c' := by
  simp [iter, h]

/-- The steps the machine takes on a formula. -/
def bsteps (n : ℕ) : {k : ℕ} → FO k → ℕ
  | _, .adj _ _ => 1
  | _, .eq _ _ => 1
  | _, .not φ => bsteps n φ + 2
  | _, .and φ ψ => bsteps n φ + bsteps n ψ + 3
  | _, .ex φ => n * (bsteps n φ + 1) + 2

/-- The assignment `m` as a list. -/
def asgOf {n k : ℕ} (m : Fin k → Fin n) : List ℕ := List.ofFn fun i => (m i : ℕ)

theorem asgOf_snoc {n k : ℕ} (m : Fin k → Fin n) (v : Fin n) :
    asgOf (Fin.snoc m v : Fin (k + 1) → Fin n) = asgOf m ++ [(v : ℕ)] := by
  simp only [asgOf, List.ofFn_succ', Fin.snoc_last, List.concat_eq_append]
  congr 2
  funext i
  simp [Fin.snoc_castSucc]

theorem asgOf_getD {n k : ℕ} (m : Fin k → Fin n) (i : Fin k) : (asgOf m).getD i 0 = m i := by
  simp [asgOf, List.getD_eq_getElem?_getD]

end Lax185574Proofs.MC.Brute

namespace Lax185574Proofs.MC.Brute

open Lax3.FirstOrder Lax185574.InstanceEncoding

/-- The word `w` sits at position `p` of `cd`. -/
def CodeAt (cd : List ℕ) (p : ℕ) (w : List ℕ) : Prop := ∀ j < w.length, cd.getD (p + j) 0 = w.getD j 0

/-- `fe` gives the end of the left conjunct of every conjunction. -/
def FeOK (cd : List ℕ) (fe : ℕ → ℕ) : {k : ℕ} → FO k → ℕ → Prop
  | _, .adj _ _, _ => True
  | _, .eq _ _, _ => True
  | _, .not φ, p => FeOK cd fe φ (p + 1)
  | _, .and φ ψ, p => fe (p + 1) = p + 1 + (code φ).length ∧ FeOK cd fe φ (p + 1) ∧
      FeOK cd fe ψ (p + 1 + (code φ).length)
  | _, .ex φ, p => FeOK cd fe φ (p + 1)

theorem CodeAt.tail {cd : List ℕ} {p a : ℕ} {w : List ℕ} (h : CodeAt cd p (a :: w)) :
    CodeAt cd (p + 1) w := by
  intro j hj
  have := h (j + 1) (by simp; omega)
  rw [show p + 1 + j = p + (j + 1) by omega, this]; simp

theorem CodeAt.left {cd : List ℕ} {p : ℕ} {u v : List ℕ} (h : CodeAt cd p (u ++ v)) :
    CodeAt cd p u := by
  intro j hj
  rw [h j (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem CodeAt.right {cd : List ℕ} {p : ℕ} {u v : List ℕ} (h : CodeAt cd p (u ++ v)) :
    CodeAt cd (p + u.length) v := by
  intro j hj
  rw [show p + u.length + j = p + (u.length + j) by omega, h _ (by simp; omega)]
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem CodeAt.head {cd : List ℕ} {p a : ℕ} {w : List ℕ} (h : CodeAt cd p (a :: w)) :
    cd.getD p 0 = a := by
  have := h 0 (by simp); simpa using this

variable {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {A : ℕ → ℕ → Bool}
  {cd : List ℕ} {fe : ℕ → ℕ}

/-- The values of a frame are small. -/
def FrOK (L n : ℕ) : Fr → Prop
  | .andL r => r ≤ L
  | .ex pc v => pc ≤ L ∧ v < n
  | _ => True

/-- The values of a configuration are small. -/
def Small (L n : ℕ) (c : Cfg) : Prop :=
  c.pos ≤ L ∧ c.stk.length ≤ L ∧ c.asg.length ≤ L ∧ (∀ x ∈ c.asg, x < n) ∧ ∀ f ∈ c.stk, FrOK L n f

/-- Every configuration of the first `t` steps is small. -/
def AllSmall (L n : ℕ) (A : ℕ → ℕ → Bool) (cd : List ℕ) (fe : ℕ → ℕ) (t : ℕ) (c : Cfg) : Prop :=
  ∀ t' ≤ t, ∃ c', iter n A cd fe t' c = some c' ∧ Small L n c'

theorem AllSmall.trans {L : ℕ} {t₁ t₂ : ℕ} {c c₁ : Cfg} (h₁ : AllSmall L n A cd fe t₁ c)
    (he : iter n A cd fe t₁ c = some c₁) (h₂ : AllSmall L n A cd fe t₂ c₁) :
    AllSmall L n A cd fe (t₁ + t₂) c := by
  intro t' ht'
  by_cases h : t' ≤ t₁
  · exact h₁ t' h
  · obtain ⟨c', hc', hs⟩ := h₂ (t' - t₁) (by omega)
    exact ⟨c', by rw [show t' = t₁ + (t' - t₁) by omega]; exact iter_trans he hc', hs⟩

theorem AllSmall.one {L : ℕ} {c c' : Cfg} (hc : Small L n c) (hs : step n A cd fe c = some c')
    (hc' : Small L n c') : AllSmall L n A cd fe 1 c := by
  intro t' ht'
  rcases Nat.lt_or_eq_of_le ht' with h | rfl
  · obtain rfl : t' = 0 := by omega
    exact ⟨c, rfl, hc⟩
  · exact ⟨c', iter_one hs, hc'⟩

theorem AllSmall.mono {L t t' : ℕ} {c : Cfg} (h : AllSmall L n A cd fe t c) (ht : t' ≤ t) :
    AllSmall L n A cd fe t' c := fun t'' h'' => h t'' (le_trans h'' ht)

theorem asgOf_small {k : ℕ} (m : Fin k → Fin n) : ∀ x ∈ asgOf m, x < n := by
  intro x hx; simp only [asgOf, List.mem_ofFn] at hx; obtain ⟨i, rfl⟩ := hx; exact (m i).isLt

theorem length_asgOf {k : ℕ} (m : Fin k → Fin n) : (asgOf m).length = k := by simp [asgOf]

theorem AllSmall.last {L t : ℕ} {c c' : Cfg} (h : AllSmall L n A cd fe t c)
    (he : iter n A cd fe t c = some c') : Small L n c' := by
  obtain ⟨c'', h'', hs⟩ := h t le_rfl
  rw [he] at h''; cases h''; exact hs

/-- **The machine evaluates.** Evaluating the code of `ψ` at `p` returns
its truth value with the stack and the assignment unchanged, and all
configurations on the way are small. -/
theorem machine_eval (hA : ∀ u v : Fin n, A u v = decide (G.Adj u v)) (L : ℕ) :
    ∀ {k : ℕ} (ψ : FO k) (p : ℕ), CodeAt cd p (code ψ) → FeOK cd fe ψ p →
      p + (code ψ).length ≤ L → k + (code ψ).length ≤ L →
      ∀ (m : Fin k → Fin n) (s : List Fr) (b : Bool), s.length + (code ψ).length ≤ L →
      (∀ f ∈ s, FrOK L n f) → ∃ t ≤ bsteps n ψ, ∃ p' b',
        (b' = true ↔ Sat G m ψ) ∧
        iter n A cd fe t ⟨true, p, b, s, asgOf m⟩ = some ⟨false, p', b', s, asgOf m⟩ ∧
        AllSmall L n A cd fe t ⟨true, p, b, s, asgOf m⟩
  | _, .adj i j, p, hc, _, hpL, hkL, m, s, b, hsL, hfr => by
      have h0 := hc.head
      have h1 := hc.tail.head
      have h2 := hc.tail.tail.head
      have hsm : ∀ (ev : Bool) (q : ℕ) (b : Bool), q ≤ p → Small L n ⟨ev, q, b, s, asgOf m⟩ :=
        fun ev q b hq => ⟨by simp [code] at hpL; simp; omega, by simp [code] at hsL; simp; omega,
          by simp [code, length_asgOf] at hkL ⊢; omega, asgOf_small m, hfr⟩
      have hst : step n A cd fe ⟨true, p, b, s, asgOf m⟩ =
          some ⟨false, p, A (m i) (m j), s, asgOf m⟩ := by
        simp only [step, if_true, h0]
        rw [h1, show p + 2 = p + 1 + 1 by omega, h2, asgOf_getD, asgOf_getD]
      exact ⟨1, le_rfl, p, A (m i) (m j), by simp [hA, Sat], iter_one hst,
        AllSmall.one (hsm _ _ _ le_rfl) hst (hsm _ _ _ le_rfl)⟩
  | _, .eq i j, p, hc, _, hpL, hkL, m, s, b, hsL, hfr => by
      have h0 := hc.head
      have h1 := hc.tail.head
      have h2 := hc.tail.tail.head
      have hsm : ∀ (ev : Bool) (q : ℕ) (b : Bool), q ≤ p → Small L n ⟨ev, q, b, s, asgOf m⟩ :=
        fun ev q b hq => ⟨by simp [code] at hpL; simp; omega, by simp [code] at hsL; simp; omega,
          by simp [code, length_asgOf] at hkL ⊢; omega, asgOf_small m, hfr⟩
      have hst : step n A cd fe ⟨true, p, b, s, asgOf m⟩ =
          some ⟨false, p, ((m i : ℕ) == (m j : ℕ)), s, asgOf m⟩ := by
        simp only [step, if_true, h0]
        rw [h1, show p + 2 = p + 1 + 1 by omega, h2, asgOf_getD, asgOf_getD]
      exact ⟨1, le_rfl, p, _, by simp [Sat, Fin.val_inj], iter_one hst,
        AllSmall.one (hsm _ _ _ le_rfl) hst (hsm _ _ _ le_rfl)⟩
  | _, .not φ, p, hc, hf, hpL, hkL, m, s, b, hsL, hfr => by
      have h0 := hc.head
      simp only [code, List.length_cons] at hpL hkL hsL
      obtain ⟨t, ht, p', b', hb', hr, hsm⟩ := machine_eval hA L φ (p + 1) hc.tail hf (by omega)
        (by omega) m (.neg :: s) b (by simp; omega)
        (by intro f hf'; simp at hf'; rcases hf' with rfl | hf'; trivial; exact hfr f hf')
      have hs₀ : Small L n ⟨true, p, b, s, asgOf m⟩ :=
        ⟨by simp; omega, by simp; omega, by simp [length_asgOf]; omega, asgOf_small m, hfr⟩
      have hst₁ : step n A cd fe ⟨true, p, b, s, asgOf m⟩ =
          some ⟨true, p + 1, b, .neg :: s, asgOf m⟩ := by simp only [step, if_true, h0]
      have hst₂ : step n A cd fe ⟨false, p', b', .neg :: s, asgOf m⟩ =
          some ⟨false, p', !b', s, asgOf m⟩ := by simp [step]
      have hend := hsm.last hr
      have hs₁ : Small L n ⟨true, p + 1, b, .neg :: s, asgOf m⟩ :=
        ⟨by simp; omega, by simp; omega, by simp [length_asgOf]; omega, asgOf_small m,
          by intro f hf'; simp at hf'; rcases hf' with rfl | hf'; trivial; exact hfr f hf'⟩
      refine ⟨1 + t + 1, by simp [bsteps]; omega, p', !b', by simp [Sat, ← hb'],
        iter_trans (iter_trans (iter_one hst₁) hr) (iter_one hst₂), ?_⟩
      exact AllSmall.trans (AllSmall.trans (AllSmall.one hs₀ hst₁ hs₁) (iter_one hst₁) hsm)
        (iter_trans (iter_one hst₁) hr)
        (AllSmall.one hend hst₂ ⟨hend.1, by simp; omega, hend.2.2.1,
          hend.2.2.2.1, fun f hf' => hend.2.2.2.2 f (by simp [hf'])⟩)
  | _, .and φ ψ, p, hc, hf, hpL, hkL, m, s, b, hsL, hfr => by
      have h0 := hc.head
      obtain ⟨hfe, hf₁, hf₂⟩ := hf
      simp only [code, List.length_cons, List.length_append] at hpL hkL hsL
      have hc₁ : CodeAt cd (p + 1) (code φ) := hc.tail.left
      have hc₂ : CodeAt cd (p + 1 + (code φ).length) (code ψ) := hc.tail.right
      have hfrL : ∀ f ∈ Fr.andL (fe (p + 1)) :: s, FrOK L n f := by
        intro f hf'; simp at hf'; rcases hf' with rfl | hf'
        · show fe (p + 1) ≤ L; omega
        · exact hfr f hf'
      obtain ⟨t₁, ht₁, p₁, b₁, hb₁, hr₁, hsm₁⟩ := machine_eval hA L φ (p + 1) hc₁ hf₁ (by omega)
        (by omega) m (.andL (fe (p + 1)) :: s) b (by simp; omega) hfrL
      have hs : step n A cd fe ⟨true, p, b, s, asgOf m⟩ =
          some ⟨true, p + 1, b, .andL (fe (p + 1)) :: s, asgOf m⟩ := by
        simp only [step, if_true, h0]
      have hs₀ : Small L n ⟨true, p, b, s, asgOf m⟩ :=
        ⟨by simp; omega, by simp; omega, by simp [length_asgOf]; omega, asgOf_small m, hfr⟩
      have hs₁ : Small L n ⟨true, p + 1, b, .andL (fe (p + 1)) :: s, asgOf m⟩ :=
        ⟨by simp; omega, by simp; omega, by simp [length_asgOf]; omega, asgOf_small m, hfrL⟩
      have hend₁ := hsm₁.last hr₁
      have A₁ := AllSmall.trans (AllSmall.one hs₀ hs hs₁) (iter_one hs) hsm₁
      cases b₁ with
      | true =>
        have hfr₂ : ∀ f ∈ Fr.andR :: s, FrOK L n f := by
          intro f hf'; simp at hf'; rcases hf' with rfl | hf'; trivial; exact hfr f hf'
        obtain ⟨t₂, ht₂, p₂, b₂, hb₂, hr₂, hsm₂⟩ := machine_eval hA L ψ (p + 1 + (code φ).length)
          hc₂ hf₂ (by omega) (by omega) m (.andR :: s) true (by simp; omega) hfr₂
        have hst₂ : step n A cd fe ⟨false, p₁, true, .andL (fe (p + 1)) :: s, asgOf m⟩ =
            some ⟨true, p + 1 + (code φ).length, true, .andR :: s, asgOf m⟩ := by simp [step, hfe]
        have hs₂ : Small L n ⟨true, p + 1 + (code φ).length, true, .andR :: s, asgOf m⟩ :=
          ⟨by simp; omega, by simp; omega, by simp [length_asgOf]; omega, asgOf_small m, hfr₂⟩
        have hst₃ : step n A cd fe ⟨false, p₂, b₂, .andR :: s, asgOf m⟩ =
            some ⟨false, p₂, b₂, s, asgOf m⟩ := by simp [step]
        have hend₂ := hsm₂.last hr₂
        have e₁ := iter_trans (iter_one hs) hr₁
        have e₂ := iter_trans e₁ (iter_one hst₂)
        have e₃ := iter_trans e₂ hr₂
        refine ⟨1 + t₁ + 1 + t₂ + 1, by simp [bsteps]; omega, p₂, b₂, ?_, iter_trans e₃ (iter_one hst₃),
          ?_⟩
        · simp only [Sat, ← hb₂]; simp at hb₁; tauto
        · refine AllSmall.trans (AllSmall.trans (AllSmall.trans A₁ e₁ (AllSmall.one hend₁ hst₂ hs₂))
            e₂ hsm₂) e₃ (AllSmall.one hend₂ hst₃ ⟨hend₂.1, by simp; omega, hend₂.2.2.1,
              hend₂.2.2.2.1, fun f hf' => hend₂.2.2.2.2 f (by simp [hf'])⟩)
      | false =>
        have hst₂ : step n A cd fe ⟨false, p₁, false, .andL (fe (p + 1)) :: s, asgOf m⟩ =
            some ⟨false, p₁, false, s, asgOf m⟩ := by simp [step]
        have e₁ := iter_trans (iter_one hs) hr₁
        refine ⟨1 + t₁ + 1, by simp [bsteps]; omega, p₁, false, ?_, iter_trans e₁ (iter_one hst₂), ?_⟩
        · simp only [Sat]; simp at hb₁; tauto
        · exact AllSmall.trans A₁ e₁ (AllSmall.one hend₁ hst₂ ⟨hend₁.1, by simp; omega,
            hend₁.2.2.1, hend₁.2.2.2.1, fun f hf' => hend₁.2.2.2.2 f (by simp [hf'])⟩)
  | k, .ex φ, p, hc, hf, hpL, hkL, m, s, b, hsL, hfr => by
      have h0 := hc.head
      simp only [code, List.length_cons] at hpL hkL hsL
      have hs₀ : Small L n ⟨true, p, b, s, asgOf m⟩ :=
        ⟨by simp; omega, by simp; omega, by simp [length_asgOf]; omega, asgOf_small m, hfr⟩
      have hsmR : ∀ (q : ℕ) (b : Bool), q ≤ L → Small L n ⟨false, q, b, s, asgOf m⟩ :=
        fun q b hq => ⟨hq, by simp; omega, by simp [length_asgOf]; omega, asgOf_small m, hfr⟩
      by_cases hn : n = 0
      · subst hn
        have hst : step 0 A cd fe ⟨true, p, b, s, asgOf m⟩ = some ⟨false, p, false, s, asgOf m⟩ := by
          simp only [step, if_true, h0]
        refine ⟨1, by simp [bsteps], p, false, ?_, iter_one hst,
          AllSmall.one hs₀ hst (hsmR p false (by omega))⟩
        simp only [Sat]; constructor
        · intro h; cases h
        · rintro ⟨v, -⟩; exact v.elim0
      · have hsmV : ∀ v (b : Bool), v < n → Small L n ⟨true, p + 1, b, .ex (p + 1) v :: s, asgOf m ++ [v]⟩ :=
          fun v b hv => ⟨by simp; omega, by simp; omega, by simp [length_asgOf]; omega,
            by intro x hx; simp at hx; rcases hx with hx | rfl; exact asgOf_small m x hx; exact hv,
            by intro f hf'; simp at hf'; rcases hf' with rfl | hf'
               · exact ⟨by omega, hv⟩
               · exact hfr f hf'⟩
        have loop : ∀ j, ∀ v, v + j = n - 1 → ∀ b',
            ∃ t ≤ (j + 1) * (bsteps n φ + 1), ∃ p' b'',
              (b'' = true ↔ ∃ u : Fin n, v ≤ u ∧ Sat G (Fin.snoc m u) φ) ∧
              iter n A cd fe t ⟨true, p + 1, b', .ex (p + 1) v :: s, asgOf m ++ [v]⟩ =
                some ⟨false, p', b'', s, asgOf m⟩ ∧
              AllSmall L n A cd fe t ⟨true, p + 1, b', .ex (p + 1) v :: s, asgOf m ++ [v]⟩ := by
          intro j
          induction j with
          | zero =>
              intro v hv b'
              have hvn : v < n := by omega
              obtain ⟨t, ht, p', b₁, hb₁, hr, hsm⟩ := machine_eval hA L φ (p + 1) hc.tail hf
                (by omega) (by omega) (Fin.snoc m ⟨v, hvn⟩) (.ex (p + 1) v :: s) b' (by simp; omega)
                (by intro f hf'; simp at hf'; rcases hf' with rfl | hf'
                    · exact ⟨by omega, hvn⟩
                    · exact hfr f hf')
              rw [asgOf_snoc] at hr hsm
              have hend := hsm.last hr
              cases b₁ with
              | true =>
                have hst : step n A cd fe ⟨false, p', true, .ex (p + 1) v :: s, asgOf m ++ [v]⟩ =
                    some ⟨false, p', true, s, asgOf m⟩ := by simp [step]
                refine ⟨t + 1, by simp; omega, p', true, ?_, iter_trans hr (iter_one hst),
                  AllSmall.trans hsm hr (AllSmall.one hend hst (hsmR p' true hend.1))⟩
                simp only [true_iff]; exact ⟨⟨v, hvn⟩, le_rfl, hb₁.mp rfl⟩
              | false =>
                have hst : step n A cd fe ⟨false, p', false, .ex (p + 1) v :: s, asgOf m ++ [v]⟩ =
                    some ⟨false, p', false, s, asgOf m⟩ := by
                  simp [step, show ¬ v + 1 < n by omega]
                refine ⟨t + 1, by simp; omega, p', false, ?_, iter_trans hr (iter_one hst),
                  AllSmall.trans hsm hr (AllSmall.one hend hst (hsmR p' false hend.1))⟩
                simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
                intro u hu h
                have : u = ⟨v, hvn⟩ := by ext; simp; have := u.isLt; omega
                rw [this] at h; simp at hb₁; exact hb₁ h
          | succ j ih =>
              intro v hv b'
              have hvn : v < n := by omega
              obtain ⟨t, ht, p', b₁, hb₁, hr, hsm⟩ := machine_eval hA L φ (p + 1) hc.tail hf
                (by omega) (by omega) (Fin.snoc m ⟨v, hvn⟩) (.ex (p + 1) v :: s) b' (by simp; omega)
                (by intro f hf'; simp at hf'; rcases hf' with rfl | hf'
                    · exact ⟨by omega, hvn⟩
                    · exact hfr f hf')
              rw [asgOf_snoc] at hr hsm
              have hend := hsm.last hr
              cases b₁ with
              | true =>
                have hst : step n A cd fe ⟨false, p', true, .ex (p + 1) v :: s, asgOf m ++ [v]⟩ =
                    some ⟨false, p', true, s, asgOf m⟩ := by simp [step]
                refine ⟨t + 1, by nlinarith, p', true, ?_, iter_trans hr (iter_one hst),
                  AllSmall.trans hsm hr (AllSmall.one hend hst (hsmR p' true hend.1))⟩
                simp only [true_iff]; exact ⟨⟨v, hvn⟩, le_rfl, hb₁.mp rfl⟩
              | false =>
                obtain ⟨t', ht', p'', b'', hb'', hr', hsm'⟩ := ih (v + 1) (by omega) false
                have hst : step n A cd fe ⟨false, p', false, .ex (p + 1) v :: s, asgOf m ++ [v]⟩ =
                    some ⟨true, p + 1, false, .ex (p + 1) (v + 1) :: s, asgOf m ++ [v + 1]⟩ := by
                  simp [step, show v + 1 < n by omega]
                have e₁ := iter_trans hr (iter_one hst)
                refine ⟨t + 1 + t', by nlinarith, p'', b'', ?_, iter_trans e₁ hr',
                  AllSmall.trans (AllSmall.trans hsm hr (AllSmall.one hend hst
                    (hsmV (v + 1) false (by omega)))) e₁ hsm'⟩
                rw [hb'']
                constructor
                · rintro ⟨u, hu, h⟩; exact ⟨u, by omega, h⟩
                · rintro ⟨u, hu, h⟩
                  refine ⟨u, ?_, h⟩
                  rcases Nat.lt_or_eq_of_le hu with h' | h'
                  · exact h'
                  · exfalso
                    have : u = ⟨v, hvn⟩ := Fin.ext h'.symm
                    rw [this] at h; simp at hb₁; exact hb₁ h
        obtain ⟨t, ht, p', b', hb', hr, hsm⟩ := loop (n - 1) 0 (by omega) b
        have hst : step n A cd fe ⟨true, p, b, s, asgOf m⟩ =
            some ⟨true, p + 1, b, .ex (p + 1) 0 :: s, asgOf m ++ [0]⟩ := by
          simp only [step, if_true, h0, hn, if_false]
        refine ⟨1 + t, ?_, p', b', ?_, iter_trans (iter_one hst) hr,
          AllSmall.trans (AllSmall.one hs₀ hst (hsmV 0 b (by omega))) (iter_one hst) hsm⟩
        · simp only [bsteps]
          have : (n - 1 + 1) = n := by omega
          rw [this] at ht; omega
        · rw [hb']; simp [Sat]

/-- The number of steps is at most `3 |code ψ| (n + 1) ^ rank ψ`. -/
theorem bsteps_le (n : ℕ) : ∀ {k : ℕ} (ψ : FO k),
    bsteps n ψ ≤ 3 * (code ψ).length * (n + 1) ^ rank ψ
  | _, .adj _ _ => by simp [bsteps, code, rank]
  | _, .eq _ _ => by simp [bsteps, code, rank]
  | _, .not φ => by
      have ih := bsteps_le n φ
      have : 1 ≤ (n + 1) ^ rank φ := Nat.one_le_pow _ _ (by omega)
      simp only [bsteps, code, rank, List.length_cons]
      nlinarith
  | _, .and φ ψ => by
      have ih₁ := bsteps_le n φ
      have ih₂ := bsteps_le n ψ
      have e₁ : (n + 1) ^ rank φ ≤ (n + 1) ^ max (rank φ) (rank ψ) :=
        Nat.pow_le_pow_right (by omega) (le_max_left _ _)
      have e₂ : (n + 1) ^ rank ψ ≤ (n + 1) ^ max (rank φ) (rank ψ) :=
        Nat.pow_le_pow_right (by omega) (le_max_right _ _)
      have : 1 ≤ (n + 1) ^ max (rank φ) (rank ψ) := Nat.one_le_pow _ _ (by omega)
      simp only [bsteps, code, rank, List.length_cons, List.length_append]
      have h₁ := Nat.mul_le_mul_left (3 * (code φ).length) e₁
      have h₂ := Nat.mul_le_mul_left (3 * (code ψ).length) e₂
      nlinarith
  | _, .ex φ => by
      have ih := bsteps_le n φ
      have h1 : 1 ≤ (n + 1) ^ rank φ := Nat.one_le_pow _ _ (by omega)
      simp only [bsteps, code, rank, List.length_cons, pow_succ]
      have := Nat.mul_le_mul_left n ih
      nlinarith

end Lax185574Proofs.MC.Brute
