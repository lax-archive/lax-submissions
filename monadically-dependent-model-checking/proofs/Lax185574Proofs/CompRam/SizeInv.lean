import Lax185574Proofs.CompRam.SizeBasic

/-!
The size invariant of the stack machine of lem:compose.

`SzP` holds the parameters: `Λ` bounds the node words, `K` the ranks and
arities, `B0` the entries of the node words, `q` the depth of the root.
A result handed down by a frame of depth `d` has length at most `F d`,
an extension word of a frame of depth `d` at most `F (d - 1) + K + 8`,
and every word built by the machine has entries below `B1`.

`FOK`: a frame holds node words `A`, `B` (and `SA`, `SB` once they are
asked for) of length at most `Λ` with entries below `B0`, small atoms and
extension words, and an index `i` below the number of extensions.
`Chain`: the depths grow by one from the top of the stack down to `q`.
`ROKs`: a state is a stack of good frames whose top asks the question
of its phase, or the final word, which is small. `round_ok`: a round
with the right answer keeps `ROKs`.
-/

namespace Lax185574Proofs.CompRam

open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574Proofs.TreeAlgo
open Lax185574.TypeTrees Lax185574.PartialGraphs

/-- The parameters of the size bounds. -/
structure SzP where
  /-- The length of the node words. -/
  Λ : ℕ
  /-- The bound on ranks and arities. -/
  K : ℕ
  /-- The bound on the entries of node words. -/
  B0 : ℕ
  /-- The depth of the root. -/
  q : ℕ

namespace SzP

/-- The length of a result at depth `d`. -/
def F (P : SzP) (d : ℕ) : ℕ := (8 * (P.Λ + P.K + 10)) ^ (d + 1)

/-- The length of the words of the lists of extensions and of questions. -/
def LX (P : SzP) : ℕ := 2 * P.Λ * (P.F P.q + P.K + 9) + 2 * P.Λ + 2

/-- The bound on all entries. -/
def B1 (P : SzP) : ℕ := P.B0 + P.K + P.LX + P.F P.q + 10

theorem F_mono (P : SzP) {d d' : ℕ} (h : d ≤ d') : P.F d ≤ P.F d' :=
  Nat.pow_le_pow_right (by omega) (by omega)

theorem F_zero (P : SzP) : 2 * P.Λ + 1 ≤ P.F 0 := by simp only [F, zero_add, pow_one]; omega

theorem F_succ (P : SzP) (d : ℕ) :
    2 * P.Λ + 2 + 2 * P.Λ * (P.F d + P.K + 9) ≤ P.F (d + 1) := by
  simp only [F]
  set a := 8 * (P.Λ + P.K + 10) with ha
  rw [pow_succ a (d + 1)]
  have h1 : a ≤ a ^ (d + 1) := Nat.le_self_pow (by omega) _
  generalize a ^ (d + 1) = X at h1 ⊢
  nlinarith

theorem F_le_LX (P : SzP) (d : ℕ) (hd : d ≤ P.q) : P.F d ≤ P.B1 := by
  have := P.F_mono hd; simp only [B1]; omega

end SzP

/-! ### The depths of the stack -/

/-- The depths grow by one from the top down to `q`. -/
def Chain (q : ℕ) : List Fr → Prop
  | [] => True
  | [f] => f.d = q
  | f :: g :: S => g.d = f.d + 1 ∧ Chain q (g :: S)

theorem chain_top {q : ℕ} {f g : Fr} {S : List Fr} (h : Chain q (f :: S)) (hd : g.d = f.d) :
    Chain q (g :: S) := by
  cases S with
  | nil => simp only [Chain] at h ⊢; omega
  | cons p S => exact ⟨by rw [hd]; exact h.1, h.2⟩

theorem chain_pop {q : ℕ} {f p : Fr} {S : List Fr} (h : Chain q (f :: p :: S)) :
    Chain q (p :: S) ∧ p.d = f.d + 1 := ⟨h.2, h.1⟩

theorem chain_length {q : ℕ} : ∀ {f : Fr} {S : List Fr}, Chain q (f :: S) → f.d + S.length = q
  | f, [], h => by simpa [Chain] using h
  | f, p :: S, h => by
    have := chain_length h.2
    have := h.1
    simp only [List.length_cons]; omega

/-! ### Frames -/

/-- A good frame. -/
structure FOK (P : SzP) (f : Fr) : Prop where
  ar : f.l1 + f.l2 ≤ f.kk
  rk : f.kk + f.d ≤ P.K
  ph : f.ph ≤ 5
  hd : f.ph ≠ 0 → 1 ≤ f.d
  A : NW f.d f.l1 f.A ∧ Small P.Λ P.B0 f.A
  B : NW f.d f.l2 f.B ∧ Small P.Λ P.B0 f.B
  SB : 2 ≤ f.ph → NW (f.d - 1) f.l2 f.SB ∧ Small P.Λ P.B0 f.SB
  SA : 3 ≤ f.ph → NW (f.d - 1) f.l1 f.SA ∧ Small P.Λ P.B0 f.SA
  AT : 1 ≤ f.ph → Small (2 * P.Λ + 1) P.B1 f.AT
  ex0 : f.ph ≤ 2 → f.EX = [] ∧ f.i = 0
  exl : f.EX.length ≤ f.i
  exw : ∀ e ∈ f.EX, Small (P.F (f.d - 1) + P.K + 8) P.B1 e
  i34 : f.ph = 3 ∨ f.ph = 4 → f.i < nA f + nB f
  i4 : f.ph = 4 → f.i < nA f
  i5 : f.ph = 5 → f.i ≤ nA f + nB f
  sa0 : Small P.Λ P.B0 f.SA
  sb0 : Small P.Λ P.B0 f.SB
  at0 : Small (2 * P.Λ + 1) P.B1 f.AT

/-- A good stack. -/
def SOK (P : SzP) (S : List Fr) : Prop :=
  Chain P.q S ∧ (∀ f ∈ S, FOK P f) ∧ ∀ f ∈ S.tail, f.ph = 3

/-- The question of the top frame in its phase. -/
def QOf (P : SzP) (f : Fr) (q : Qry) : Prop :=
  (f.ph = 0 ∧ q = .ca (atomsQ f)) ∨ (f.ph = 1 ∧ q = .sh ([f.kk, f.d, f.l2] ++ f.B)) ∨
    (f.ph = 2 ∧ q = .sh ([f.kk, f.d, f.l1] ++ f.A)) ∨
    (f.ph = 4 ∧ ∃ R, Small (P.F (f.d - 1)) P.B1 R ∧ q = .re (reQuery f R)) ∨
    (f.ph = 5 ∧ q = .ca f.EX)

/-- A good state. -/
def ROKs (P : SzP) : Res → Prop
  | .call S q => SOK P S ∧ ∃ f S', S = f :: S' ∧ QOf P f q
  | .done z => Small (P.F P.q + 3) P.B1 z
  | .err => True

/-! ### Words of good frames -/

theorem sd_small {ws : List (List ℕ)} {Λ B : ℕ} (h : Small Λ B (toWord ws)) (hΛ : Λ ≤ B) :
    Small Λ B (toWord (sortedDistinct ws)) := by
  have h1 := h.1
  refine ⟨le_trans (length_toWord_sortedDistinct_le ws) h.1, fun e he => ?_⟩
  rcases mem_toWord_cases he with rfl | ⟨w, hw, rfl⟩ | ⟨w, hw, he'⟩
  · have := length_sortedDistinct_le ws
    have := count_lt_toWord ws
    omega
  · have := length_le_toWord (mem_sortedDistinct.1 hw)
    omega
  · exact h.2 e (mem_toWord_of_mem (mem_sortedDistinct.1 hw) he')

theorem nA_lt {P : SzP} {f : Fr} (h : FOK P f) (hd : 1 ≤ f.d) : nA f < P.Λ := by
  have hA := h.A
  rw [show f.d = f.d - 1 + 1 by omega] at hA
  have := extsOf_count hA.1
  have := hA.2.1
  simp only [nA]; omega

theorem nB_lt {P : SzP} {f : Fr} (h : FOK P f) (hd : 1 ≤ f.d) : nB f < P.Λ := by
  have hB := h.B
  rw [show f.d = f.d - 1 + 1 by omega] at hB
  have := extsOf_count hB.1
  have := hB.2.1
  simp only [nB]; omega

theorem i_le {P : SzP} {f : Fr} (h : FOK P f) : f.i ≤ 2 * P.Λ := by
  by_cases h2 : f.ph ≤ 2
  · rw [(h.ex0 h2).2]; omega
  · have hd := h.hd (by omega)
    have := nA_lt h hd
    have := nB_lt h hd
    have := h.ph
    rcases (show f.ph = 3 ∨ f.ph = 4 ∨ f.ph = 5 by omega) with h3 | h3 | h3
    · have := h.i34 (Or.inl h3); omega
    · have := h.i34 (Or.inr h3); omega
    · have := h.i5 h3; omega

/-- The atoms of the result of a frame. -/
theorem atomsQ_small {P : SzP} {f : Fr} (h : FOK P f) :
    Small (2 * P.Λ) P.B1 (toWord (atomsQ f)) := by
  have hA := atomsOf_small h.A.1 h.A.2
  have hB := atomsOf_small h.B.1 h.B.2
  have hl := length_toWord_append (atomsOf f.A) ((atomsOf f.B).map (renAtom f.l1))
  rw [length_toWord_map_renAtom] at hl
  have hK : f.l1 ≤ P.K := by have := h.ar; have := h.rk; omega
  have hB1 : P.B0 + P.K + 2 * P.Λ + 2 ≤ P.B1 := by simp only [SzP.B1, SzP.LX]; nlinarith
  have hA1 := hA.1
  have hB1' := hB.1
  refine ⟨by unfold atomsQ; omega, fun e he => ?_⟩
  unfold atomsQ at he
  rcases mem_toWord_cases he with rfl | ⟨w, hw, rfl⟩ | ⟨w, hw, he'⟩
  · have := count_lt_toWord (atomsOf f.A ++ (atomsOf f.B).map (renAtom f.l1))
    omega
  · have := length_le_toWord hw
    omega
  · rcases List.mem_append.1 hw with hw | hw
    · have := hA.2 e (mem_toWord_of_mem hw he'); omega
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hw
      have := renAtom_lt (l := f.l1) (B := P.B0) (fun v hv => hB.2 v (mem_toWord_of_mem hc hv)) e he'
      omega

end Lax185574Proofs.CompRam
