import Lax185574Proofs.CompRam.Script
import Lax185574Proofs.RamSwitch
import Lax185574Proofs.RamLoopCode

/-!
The words of the glue program of lem:compose.

A frame is kept as seven words: its numbers `[d, kk, l1, l2, ph, i]`, the
words `A`, `B`, `SA`, `SB`, `AT` and the word of the list `EX`. The state
of the glue after round `j - 1` is `0 :: j :: toWord (stWords S)`, where
the leading `0` is the start of the window of the input, which the glue
never asks for, and `j` counts the rounds. The glue writes
`[1, |state|, 0] ++ state ++ qWord q` for a question `q`, and `0 :: z`
for the output `z`.

The callee is `switch R S C` (restriction, rank shift, canonical form).
It answers all three parts of its query, so a question to one of them
comes with fixed questions to the other two: the restriction of the tree
of the empty tuple of the graph `G0` on no vertices along `J = []`, the
rank shift of `tree_{1,1}(0)` of the graph `G1` with one vertex, and the
canonical form of the empty list. The answer of the switch is the
concatenation of the three answers, and the glue picks its own part by
the phase of the top frame (`pick`).
-/

namespace Lax185574Proofs.CompRam

open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574Proofs.TreeAlgo
open Lax185574.TypeTrees Lax185574.PartialGraphs Lax185574.DistanceLogic
open Lax185574Proofs.Simulate Lax185574Proofs.RamSim Lax185574.SequenceEncoding

/-- The words of a frame. -/
def frWords (f : Fr) : List (List ℕ) :=
  [[f.d, f.kk, f.l1, f.l2, f.ph, f.i], f.A, f.B, f.SA, f.SB, f.AT, toWord f.EX]

/-- The words of a stack. -/
def stWords (S : List Fr) : List (List ℕ) := (S.map frWords).flatten

/-- The state of the glue with the round counter `j`. -/
def stWord (j : ℕ) (S : List Fr) : List ℕ := 0 :: j :: toWord (stWords S)

/-- The graph on no vertices. -/
def G0 : PartialGraph (Fin 0) := unresolved fun i => i.elim0

/-- The graph with one vertex, of color `0`. -/
def G1 : PartialGraph (Fin 1) := unresolved fun _ => 0

/-- The fixed question to the restriction. -/
noncomputable def dRq : List ℕ := toWord (tree G0 0 0 (Fin.elim0 : Fin 0 → Fin 0), ([] : List (Fin 0)))

/-- Its answer. -/
noncomputable def dRa : List ℕ :=
  toWord (tree G0 0 0 (fun i : Fin ([] : List (Fin 0)).length =>
    (Fin.elim0 : Fin 0 → Fin 0) (([] : List (Fin 0)).get i)))

/-- The fixed question to the rank shift. -/
noncomputable def dSq : List ℕ := toWord (tree G1 1 (0 + 1) ![(0 : Fin 1)])

/-- Its answer. -/
noncomputable def dSa : List ℕ := toWord (tree G1 (1 + 1) 0 ![(0 : Fin 1)])

/-- The query of the switch for a question. -/
noncomputable def qWord : Qry → List ℕ
  | .re w => swIn w dSq [0]
  | .sh w => swIn dRq w [0]
  | .ca ws => swIn dRq dSq (toWord ws)

/-- The answer of the switch to the query of a question with answer `b`. -/
noncomputable def ansWord : Qry → List ℕ → List ℕ
  | .re _, b => b ++ dSa ++ [0]
  | .sh _, b => dRa ++ b ++ [0]
  | .ca _, b => dRa ++ dSa ++ b

/-- The part of the answer of the switch that belongs to the question of
a frame in phase `ph`. -/
noncomputable def pick (ph : ℕ) (o : List ℕ) : List ℕ :=
  if ph = 4 then o.take (o.length - dSa.length - 1)
  else if ph = 1 ∨ ph = 2 then (o.drop dRa.length).take (o.length - dRa.length - 1)
  else o.drop (dRa.length + dSa.length)

/-- The question goes to the callee that the phase expects. -/
def Fits : ℕ → Qry → Prop
  | ph, .re _ => ph = 4
  | ph, .sh _ => ph = 1 ∨ ph = 2
  | ph, .ca _ => ph ≠ 4 ∧ ph ≠ 1 ∧ ph ≠ 2

theorem pick_ansWord {ph : ℕ} {q : Qry} (h : Fits ph q) (b : List ℕ) : pick ph (ansWord q b) = b := by
  cases q with
  | re w =>
    simp only [Fits] at h
    simp only [pick, ansWord, h, if_true, List.length_append, List.length_singleton]
    rw [show b.length + dSa.length + 1 - dSa.length - 1 = b.length by omega, List.append_assoc]
    simp
  | sh w =>
    simp only [Fits] at h
    have h4 : ph ≠ 4 := by omega
    simp only [pick, ansWord, h4, if_false, h, if_true, List.length_append, List.length_singleton]
    rw [List.append_assoc, List.drop_left]
    rw [show dRa.length + b.length + 1 - dRa.length - 1 = b.length by omega]
    simp
  | ca ws =>
    simp only [Fits] at h
    obtain ⟨h4, h1, h2⟩ := h
    simp only [pick, ansWord, h4, if_false, h1, h2, or_self]
    rw [← List.length_append, List.drop_left]

/-- The output of the glue for an outcome of a round, with the round
counter `j` of the next round. -/
noncomputable def outW (j : ℕ) : Res → List ℕ
  | .call S q => [1, (stWord j S).length, 0] ++ stWord j S ++ qWord q
  | .done z => 0 :: z
  | .err => []

/-- The input of a round after a call, with the answer `o` of the switch. -/
def glueIn (j : ℕ) (S : List Fr) (o : List ℕ) : List ℕ :=
  [1, (stWord j S).length] ++ stWord j S ++ (o.length :: o)

theorem lpQ_outW (j : ℕ) (S : List Fr) (q : Qry) : lpQ (outW j (.call S q)) = qWord q := by
  simp only [lpQ, outW, List.getD_eq_getElem?_getD, List.cons_append, List.nil_append,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
  rw [show 3 + (stWord j S).length = ([1, (stWord j S).length, 0] ++ stWord j S).length by simp; omega]
  rw [← List.cons_append, ← List.cons_append, ← List.cons_append]
  simp

theorem lpU_outW (x : List ℕ) (j : ℕ) (S : List Fr) (q : Qry) (o : List ℕ) :
    lpU x (outW j (.call S q)) o = glueIn j S o := by
  have hst : stWord j S = 0 :: j :: toWord (stWords S) := rfl
  simp only [lpU, outW, glueIn, List.getD_eq_getElem?_getD, List.cons_append, List.nil_append,
    List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some, List.take_zero, List.drop_succ_cons,
    List.drop_zero, List.append_nil]
  rw [hst]
  simp only [List.nil_append, List.cons_append, List.length_cons]
  rw [show List.take ((toWord (stWords S)).length + 1 + 1) (0 :: j :: (toWord (stWords S) ++ qWord q)) =
    0 :: j :: toWord (stWords S) by rw [← List.cons_append, ← List.cons_append, List.take_left' (by simp)]]
  rfl

theorem lpU_first (x : List ℕ) : lpU x (lpA0 x) [] = [0, x.length] ++ x ++ [0] := by
  simp [lpU, lpA0]

/-! ### The fixed questions -/

theorem atoms_empty_tuple {V : Type*} [Finite V] (G : PartialGraph V) (k q : ℕ) (v : Fin 0 → V) :
    Node.atoms (node G k q v) = ∅ := by
  ext φ
  simp only [mem_atoms_node, Finset.notMem_empty, iff_false, not_and]
  intro h
  cases φ with
  | eq i => exact i.elim0
  | edge i => exact i.elim0
  | nonEdge i => exact i.elim0
  | color Y i => exact i.elim0
  | distLe r i => exact i.elim0
  | distColorLt r Y i => exact i.elim0
  | not => exact h.elim
  | and => exact h.elim
  | exLocal => exact h.elim

theorem dRq_eq : dRq = [0, 0, 0, 0, 0] := by
  have h := atoms_empty_tuple G0 0 0 (Fin.elim0 : Fin 0 → Fin 0)
  show toWord (tree G0 0 0 (Fin.elim0 : Fin 0 → Fin 0)) ++ toWord ([] : List (Fin 0)) = _
  rw [toWord_tree_eq, toWord_node_zero, h,
    show Finset.words (∅ : Finset (DistFO 0)) = [] by simp [Finset.words]]
  rfl

theorem dRa_eq : dRa = [0, 0, 0, 0] := by
  have h := atoms_empty_tuple G0 0 0 (fun i : Fin ([] : List (Fin 0)).length =>
    (Fin.elim0 : Fin 0 → Fin 0) (([] : List (Fin 0)).get i))
  show toWord (tree G0 0 0 _) = _
  rw [toWord_tree_eq, toWord_node_zero, h,
    show Finset.words (∅ : Finset (DistFO 0)) = [] by simp [Finset.words]]
  rfl

theorem dSq_tree : dSq = toWord (tree G1 1 (0 + 1) ![(0 : Fin 1)]) := rfl

theorem dSa_tree : dSa = toWord (tree G1 (1 + 1) 0 ![(0 : Fin 1)]) := rfl

/-! ### The question of the top frame -/

theorem child_ph (f : Fr) : (child f).ph = 0 := by
  unfold child; split <;> rfl

theorem advance_fits (f : Fr) (S : List Fr) :
    ∃ g S' q, advance f S = .call (g :: S') q ∧ Fits g.ph q := by
  unfold advance
  split
  · exact ⟨_, _, _, rfl, by simp [Fits, child_ph]⟩
  · exact ⟨_, _, _, rfl, by simp [Fits]⟩

theorem ret_fits (R h : List ℕ) (S : List Fr) :
    (∃ z, ret R h S = .done z) ∨ ∃ g S' q, ret R h S = .call (g :: S') q ∧ Fits g.ph q := by
  cases S with
  | nil => exact Or.inl ⟨_, rfl⟩
  | cons p S =>
    right
    by_cases hi : p.i < nA p
    · rw [ret_lt _ _ _ _ hi]; exact ⟨_, _, _, rfl, by simp [Fits]⟩
    · rw [ret_ge _ _ _ _ hi]; exact advance_fits _ _

/-- **Every question goes to the callee that the phase of the new top
frame expects.** -/
theorem round_fits (S : List Fr) (b : List ℕ) :
    round S b = .err ∨ (∃ z, round S b = .done z) ∨
      ∃ g S' q, round S b = .call (g :: S') q ∧ Fits g.ph q := by
  cases S with
  | nil => exact Or.inl rfl
  | cons f S =>
    by_cases h0 : f.ph = 0
    · by_cases hd : f.d = 0
      · rw [round_ph0_zero f S b h0 hd]; exact Or.inr (ret_fits _ _ _)
      · rw [round_ph0_succ f S b h0 hd]; exact Or.inr (Or.inr ⟨_, _, _, rfl, by simp [Fits]⟩)
    by_cases h1 : f.ph = 1
    · rw [round_ph1 f S b h1]; exact Or.inr (Or.inr ⟨_, _, _, rfl, by simp [Fits]⟩)
    by_cases h2 : f.ph = 2
    · rw [round_ph2 f S b h2]; exact Or.inr (Or.inr (advance_fits _ _))
    by_cases h4 : f.ph = 4
    · rw [round_ph4 f S b h4]; exact Or.inr (Or.inr (advance_fits _ _))
    by_cases h5 : f.ph = 5
    · rw [round_ph5 f S b h5]; exact Or.inr (ret_fits _ _ _)
    exact Or.inl (by simp [round, h0, h1, h2, h4, h5])

theorem fresh_fits (d kk l1 l2 : ℕ) (A B : List ℕ) : Fits (fresh d kk l1 l2 A B).ph (.ca (atomsQ (fresh d kk l1 l2 A B))) := by
  simp [Fits, fresh]

end Lax185574Proofs.CompRam
