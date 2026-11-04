import Lax185574.ConstructionModelChecking
import Lax185574Proofs.LegacyInputs
import Lax185574Proofs.Interface.SeqBridge
import Lax185574Proofs.Interface.KitG3

/-!
A weak form of `Lax185574.ConstructionModelChecking` for a program that
reads the graph in compressed sparse row form, a script and a sentence
of `Lax3.FirstOrder`, derived from the concept.

The older statement, a program that halts with the answer at every
admissible word length, does not follow from the concept, which claims
halting only once the time fits into a word. `WeakCMC` keeps the two
clauses apart. Every halting run at an admissible word length outputs
the answer, and the program halts within
`c · λ · (n+1)² · (K+1)^b + c · |x|` once this number fits into a word.
The term `c · |x|` pays for converting the compressed sparse row word,
whose target array may list a neighbor several times.

The program is the pipe `csr_bridge` of the converter into the algorithm
of the concept, applied to the sentence `ofFO φ`, which is `φ` as a
sentence of `Lax185574.FirstOrderLogic`.
-/

namespace Lax185574Proofs.Shim.ConstructionModelChecking

open Lax3.FirstOrder Lax271696.GraphEncoding Lax808846.Ram
open Lax185574.Encoding Lax185574.WordEncoding Lax185574.PartialGraphs
open Lax185574.ConstructionSequences Lax185574.Width
open Lax185574.ConstructionModelChecking (EncodesInput)
open Lax185574Proofs.Interface
open scoped Lax185574.FirstOrderLogic

/-- A formula of `Lax3.FirstOrder` as a formula without colors. -/
def ofFO : {k : ℕ} → FO k → Lax185574.FirstOrderLogic.Formula Empty k
  | _, .adj i j => .adj i j
  | _, .eq i j => .eq i j
  | _, .not φ => .not (ofFO φ)
  | _, .and φ ψ => .and (ofFO φ) (ofFO ψ)
  | _, .ex φ => .ex (ofFO φ)

theorem toFO_ofFO : ∀ {k : ℕ} (φ : FO k), Formula.toFO (ofFO φ) = φ
  | _, .adj _ _ => rfl
  | _, .eq _ _ => rfl
  | _, .not φ => by simp only [ofFO, Formula.toFO, toFO_ofFO φ]
  | _, .and φ ψ => by simp only [ofFO, Formula.toFO, toFO_ofFO φ, toFO_ofFO ψ]
  | _, .ex φ => by simp only [ofFO, Formula.toFO, toFO_ofFO φ]

open Classical in
/-- Model checking along a construction sequence for the older input
format: soundness at every admissible word length, and halting once the
time fits into a word. -/
def WeakCMC : Prop :=
  ∃ (p : Program) (e : ℕ), ∀ φ : FO 0, ∃ r d c b : ℕ,
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (s : List (PartialGraph (Fin n))) (K w : ℕ)
      (x : List ℕ),
      IsConstructionSequence G s → width r d s ≤ K → EncodesInput x n G s φ →
      (∀ v ∈ x, c * (x.length + v + 1) ^ e ≤ 2 ^ w) →
        (∀ z t, RunsTo w p x z t → z = if Sat G Fin.elim0 φ then [1] else [0]) ∧
        (c * s.length * (n + 1) ^ 2 * (K + 1) ^ b + c * x.length ≤ 2 ^ w →
          ∃ t ≤ c * s.length * (n + 1) ^ 2 * (K + 1) ^ b + c * x.length,
            RunsTo w p x (if Sat G Fin.elim0 φ then [1] else [0]) t)

open Classical in
theorem exists_program_modelChecking_sequence_weak : WeakCMC := by
  obtain ⟨A, hA⟩ := Lax185574.ConstructionModelChecking.exists_program_modelChecking_sequence
  obtain ⟨q, Kq, hq⟩ := csr_bridge 0 A.program
  refine ⟨q, 3 * A.wordExponent + 2, fun φ => ?_⟩
  obtain ⟨r, d, c, b, hc⟩ := hA (ofFO φ)
  obtain ⟨c', hc'⟩ : ∃ c', c' = 4 * 8 ^ A.wordExponent * c + 8 * c + Kq * (2 * c + 2) + Kq :=
    ⟨_, rfl⟩
  refine ⟨r, d, c', b, fun n G s K w x hcs hK ⟨g, y, hg, ⟨σ, hy, hs⟩, hx⟩ hadm => ?_⟩
  subst hy hs hx
  set G' := Lax185574.Graphs.Graph.ofSimpleGraph G with hG'
  have hdec := hc G' σ hcs
  unfold Lax185574.Algorithms.Algorithm.Decides at hdec
  have ha : encode (G', σ, ofFO φ) = [] ++ toWord G ++ (encode σ ++ encode φ) := by
    simp only [KitG3.encode_pair, encode_graph, encode_formula, toFO_ofFO, List.nil_append]; rfl
  have hans : encode (decide (G' ⊨ ofFO φ)) = if Sat G Fin.elim0 φ then [1] else [0] := by
    rw [decide_models_word, toFO_ofFO]; rfl
  have hx : g ++ encode σ ++ encode φ = [] ++ g ++ (encode σ ++ encode φ) := by simp
  rw [hx] at hadm ⊢
  obtain ⟨hs, hh⟩ := csr_shim hq rfl hg ha hdec (by omega) (le_refl _) w hadm
  rw [hans] at hs hh
  refine ⟨hs, fun hfit => ?_⟩
  -- the time
  set X := ([] ++ g ++ (encode σ ++ encode φ)).length with hX
  have hl1 := one_le_length_run σ
  set M := σ.run.length * (n + 1) ^ 2 with hM
  set Tw := M * (width r d σ.run + 1) ^ b with hTw
  set TK := M * (K + 1) ^ b with hTK
  have hTT : Tw ≤ TK := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) b)
  have hnM : (n + 1) ^ 2 ≤ M := Nat.le_mul_of_pos_left _ hl1
  have hMT : M ≤ Tw := Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega))
  have hT1 : 1 ≤ Tw := le_trans (Nat.one_le_pow _ _ (by omega)) (le_trans hnM hMT)
  have hTKe : c' * σ.run.length * (n + 1) ^ 2 * (K + 1) ^ b = c' * TK := by
    rw [hTK, hM]; ring
  rw [hTKe] at hfit ⊢
  have hTw : (Tw : ℝ) = σ.run.length * ((n : ℝ) + 1) ^ 2 * ((width r d σ.run : ℝ) + 1) ^ b := by
    rw [hTw, hM]; push_cast; ring
  have hfitA : (c : ℝ) * (σ.run.length * ((n : ℝ) + 1) ^ 2 * ((width r d σ.run : ℝ) + 1) ^ b)
      + c ≤ 2 ^ (w - 2) := by
    rw [← hTw]
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp
    have h8 : 8 * c * Tw ≤ 2 ^ w := by
      have : 8 * c * Tw ≤ c' * TK := Nat.mul_le_mul (by omega) hTT
      omega
    have h4w : 4 ≤ 2 ^ w := by
      have : 8 * 1 * 1 ≤ 8 * c * Tw := Nat.mul_le_mul (Nat.mul_le_mul_left _ h0) hT1
      omega
    have e4 := two_pow_four h4w
    have : c * Tw + c ≤ 2 ^ (w - 2) := by
      have : c ≤ c * Tw := Nat.le_mul_of_pos_right _ hT1
      have : 8 * c * Tw = 4 * (2 * (c * Tw)) := by ring
      omega
    exact_mod_cast this
  obtain ⟨t, ht, hr⟩ := hh hfitA
  refine ⟨t, ?_, hr⟩
  have ht' : (t : ℝ) ≤ Kq * ((c : ℝ) * Tw + c + ((n : ℝ) + 1) ^ 2 + X + 1) := by
    rw [hTw]; exact ht
  have hX1 : 1 ≤ X := by
    have := hg.length_eq
    have : g.length ≤ X := by simp [hX]
    omega
  have h1 : (t : ℝ) ≤ ((Kq * ((2 * c + 2) * Tw + X) : ℕ) : ℝ) := by
    refine le_trans ht' ?_
    have hn : (((n + 1) ^ 2 : ℕ) : ℝ) ≤ Tw := by exact_mod_cast le_trans hnM hMT
    have hT1r : (1 : ℝ) ≤ Tw := by exact_mod_cast hT1
    have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
    have hK0 : (0 : ℝ) ≤ Kq := Nat.cast_nonneg _
    push_cast at hn ⊢
    apply mul_le_mul_of_nonneg_left _ hK0
    nlinarith
  have h2 : Kq * ((2 * c + 2) * Tw + X) ≤ c' * TK + c' * X := by
    have : Kq * ((2 * c + 2) * Tw + X) = Kq * (2 * c + 2) * Tw + Kq * X := by ring
    rw [this]
    exact Nat.add_le_add (Nat.mul_le_mul (by omega) hTT) (Nat.mul_le_mul_right _ (by omega))
  have h3 : t ≤ Kq * ((2 * c + 2) * Tw + X) := by exact_mod_cast h1
  omega

end Lax185574Proofs.Shim.ConstructionModelChecking
