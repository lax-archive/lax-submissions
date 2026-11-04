import Lax185574.ChainConstructionSequences
import Lax185574Proofs.Conversions.ChainComposition
import Lax185574Proofs.RamPipe
import Lax185574Proofs.Compose.WordBounds
import Lax185574Proofs.Interface.KitG3

/-!
Proof of lem:better-definable-mw-from-sets (`ChainConstructionSequences`)
from lem:better-mw (`BetterMergeSequences`) and
cl:from-merge-to-construction (`MergeToConstruction`). The function half
is `Conversions.ChainComposition.exists_composition`. The program pipes
the two programs. The second one needs the graph again, so a first
phase computes the length of the graph word at the front of the input,
and the second phase gets that length in front of the input, which
lets a rewrite cut the graph out.

Every phase is guaranteed to halt at every word length at which the
input is admissible, because the word-length exponent of the composite
is large enough for the time bounds of the phases to fit. So the
composite halts there with the right output, and since the machine is
deterministic, every halting run has that output.
-/

namespace Lax185574Proofs.ChainConstructionSequences

open Lax808846.Ram Lax808846.RamComputes Lax185574.WordEncoding Lax185574.Computing
open Lax185574.Chains Lax185574.ConstructionSequences Lax185574.ConstructionWidth
open Lax185574.SequenceEncoding Lax185574.LocalDefinability Lax185574.MergeSequences
open Lax185574.ChainConstructionSequences
open Lax185574Proofs.Simulate Lax185574Proofs.Compose

/-! ### The rewrites -/

/-- The whole input. -/
def ρId : Rewrite 1 := [.slice 0 (.lit 0) none]
/-- The length of the graph word, then the input. -/
def ρLen : Rewrite 2 := [.expr (.entry 0 0), .slice 1 (.lit 0) none]
/-- The input without its first entry. -/
def ρTail : Rewrite 1 := [.slice 0 (.lit 1) none]
/-- The graph word, cut out of the second source by the length in its
first entry, then the first source. -/
def ρGraph : Rewrite 2 := [.slice 1 (.lit 1) (some (.entry 1 0)), .slice 0 (.lit 0) none]

theorem ρId_apply (x : List ℕ) : ρId.apply (fun _ => x) = x := by
  simp [ρId, Rewrite.apply, Segment.apply, HExpr.eval]

theorem ρLen_apply (g : ℕ) (x : List ℕ) : ρLen.apply ![[g], x] = g :: x := by
  simp [ρLen, Rewrite.apply, Segment.apply, HExpr.eval]

theorem ρTail_apply (g : ℕ) (x : List ℕ) : ρTail.apply (fun _ => g :: x) = x := by
  simp [ρTail, Rewrite.apply, Segment.apply, HExpr.eval]

theorem ρGraph_apply (y a b : List ℕ) : ρGraph.apply ![y, a.length :: (a ++ b)] = a ++ y := by
  simp [ρGraph, Rewrite.apply, Segment.apply, HExpr.eval]

theorem ρId_cost (x : List ℕ) : ρId.cost (fun _ => x) = 3 := by
  simp [ρId, Rewrite.cost, Segment.cost, HExpr.cost]

theorem ρLen_cost (xs : Fin 2 → List ℕ) : ρLen.cost xs = 5 := by
  simp [ρLen, Rewrite.cost, Segment.cost, HExpr.cost]

theorem ρTail_cost (x : List ℕ) : ρTail.cost (fun _ => x) = 3 := by
  simp [ρTail, Rewrite.cost, Segment.cost, HExpr.cost]

theorem ρGraph_cost (xs : Fin 2 → List ℕ) : ρGraph.cost xs = 6 := by
  simp [ρGraph, Rewrite.cost, Segment.cost, HExpr.cost]

theorem ρId_fits {w : ℕ} {x : List ℕ} (h : x.length < 2 ^ w) : ρId.Fits w (fun _ => x) := by
  refine ⟨fun _ => h, by rw [ρId_apply]; exact h, ?_⟩
  intro seg hs
  simp only [ρId, List.mem_singleton] at hs
  subst hs
  exact ⟨trivial, by show 0 < 2 ^ w; positivity⟩

theorem ρLen_fits {w g : ℕ} {x : List ℕ} (h : x.length + 1 < 2 ^ w) :
    ρLen.Fits w ![[g], x] := by
  refine ⟨fun i => ?_, by rw [ρLen_apply]; simpa using h, ?_⟩
  · fin_cases i
    · show 1 < 2 ^ w; omega
    · show x.length < 2 ^ w; omega
  · intro seg hs
    simp only [ρLen, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · show 0 < 2 ^ w; positivity
    · exact ⟨trivial, by show 0 < 2 ^ w; positivity⟩

theorem ρTail_fits {w g : ℕ} {x : List ℕ} (h : x.length + 1 < 2 ^ w) :
    ρTail.Fits w (fun _ => g :: x) := by
  refine ⟨fun _ => by simpa using h, by rw [ρTail_apply]; omega, ?_⟩
  intro seg hs
  simp only [ρTail, List.mem_singleton] at hs
  subst hs
  exact ⟨trivial, by show 1 < 2 ^ w; omega⟩

theorem ρGraph_fits {w : ℕ} {y a b : List ℕ} (hy : y.length < 2 ^ w)
    (h : a.length + b.length + 1 < 2 ^ w) (h' : a.length + y.length < 2 ^ w) :
    ρGraph.Fits w ![y, a.length :: (a ++ b)] := by
  refine ⟨fun i => ?_, by rw [ρGraph_apply]; simpa using h', ?_⟩
  · fin_cases i <;> simp <;> omega
  · intro seg hs
    simp only [ρGraph, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · refine ⟨trivial, by show 1 < 2 ^ w; omega, by show 0 < 2 ^ w; positivity, ?_⟩
      show a.length < 2 ^ w
      omega
    · exact ⟨trivial, by show 0 < 2 ^ w; positivity⟩

/-! ### Sizes -/

theorem toWord_graph_length_ge {n : ℕ} (G : SimpleGraph (Fin n)) : n + 1 ≤ (toWord G).length := by
  rw [toWord_graph_length]
  have : ∀ bs : List (List ℕ), bs.length ≤ (blocksWord bs).length := by
    intro bs; induction bs with
    | nil => simp [blocksWord]
    | cons u bs ih => rw [blocksWord_cons]; simp [blk]; omega
  have := this (graphBlocks G)
  rw [graphBlocks_length] at this
  omega

theorem toWord_chain_length_ge {n : ℕ} (S : List (Finset (Fin n))) :
    S.length + 1 ≤ (toWord S).length := by
  change S.length + 1 ≤ (S.length :: (S.map toWord).flatten).length
  have : ∀ l : List (Finset (Fin n)), l.length ≤ ((l.map toWord).flatten).length := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
        simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
        have : 1 ≤ (toWord a).length := by
          change 1 ≤ (toWord (Finset.words a)).length
          change 1 ≤ ((Finset.words a).length :: _).length
          simp
        omega
  have := this S
  simp only [List.length_cons]
  omega

/-- The word of a merge sequence of length `m` on `n` vertices. -/
theorem wb_mergeSequence {n : ℕ} (ms : List (Setoid (Fin n) × SimpleGraph (Fin n))) :
    WB ms ((ms.length + 1) * ((n + 1) * ((n + 1) * (n + 3) + 2) +
      (n + 1) * ((n + 1) * (n + 3) + 1) + 1)) :=
  wb_list fun a _ => wb_prod (wb_setoid a.1) (wb_graph a.2)

/-! ### Arithmetic for the admissibility -/

/-- If `c · A^e ≤ 16 W` and `16 k ≤ c` and `j ≤ e`, then `k · A^j ≤ W`. -/
theorem small {c e A W k j : ℕ} (h : c * A ^ e ≤ 16 * W) (hk : 16 * k ≤ c) (hj : j ≤ e)
    (hA : 1 ≤ A) : k * A ^ j ≤ W := by
  have h1 : A ^ j ≤ A ^ e := Nat.pow_le_pow_right hA hj
  have h2 : 16 * (k * A ^ j) ≤ c * A ^ e := by
    calc 16 * (k * A ^ j) = (16 * k) * A ^ j := by ring
      _ ≤ c * A ^ e := Nat.mul_le_mul hk h1
  omega

set_option maxHeartbeats 1600000 in
/-- The statement for simple graphs on `Fin n` and the older
`Lax185574.Computing.Computes`.

The proof of lem:better-definable-mw-from-sets: run the algorithm of
lem:better-mw on the graph and the chain, and then the algorithm of
cl:from-merge-to-construction on the graph and the merge sequence. The
properties of the output are those of the composed functions
(`ChainComposition.exists_composition`). The times add up to
`O(m n³) + O(m n²)`. On the word RAM, a first phase computes the length
of the graph word, so that the graph can be passed to the second
algorithm.
-/
theorem exists_constructionSequence_of_chain_old :
    ∃ (p : Program) (e A : ℕ)
      (M : ∀ n : ℕ, SimpleGraph (Fin n) → List (Finset (Fin n)) → Script n),
      (∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))), IsChain S →
        IsConstructionSequence G (M n G S).run ∧
        (∀ v ∈ toWord (M n G S), v ≤ wordLength (M n G S) + n) ∧
        (M n G S).run.length ≤ A * (n + 1) * (chainBound G S 1 + 1) ∧
        ∀ r : ℕ, 1 ≤ r →
          constructionWidth r (M n G S).run ≤ chainBound G S r ∧
            IsRadiusDefinable G (M n G S).run r (2 * S.length + 1) (chainBound G S r) 7) ∧
      ∃ c : ℕ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : List (Finset (Fin n))), IsChain S →
        Computes p e c (G, S) (M n G S) (fun _ => c * (S.length + 1) * (n + 1) ^ 3) := by
  obtain ⟨p₁, e₁, M₁, p₂, e₂, A, M₂, hprop, ⟨c₁, hc₁⟩, ⟨c₂, hc₂⟩⟩ :=
    Lax185574Proofs.Conversions.ChainComposition.exists_composition
  obtain ⟨pI, KI, hI⟩ := pipe p₁ p₂ ρTail ρGraph
  obtain ⟨p, K₀, h₀⟩ := pipe graphLengthProg pI ρId ρLen
  refine ⟨p, e₁ + 8 * e₂ + 8, A, fun n G S => M₂ n G (M₁ n G S),
    fun n G S hS => (hprop n G S hS).2.2, ?_⟩
  set c := 16 * (c₁ + c₂ + c₂ * 3 ^ (8 * e₂) + 2 * 3 ^ 8 + K₀ + KI + 4) +
    K₀ * (708 + KI * (c₁ + c₂ + 9)) with hc
  refine ⟨c, fun n G S hS w hadm => ?_⟩
  set e := e₁ + 8 * e₂ + 8
  obtain ⟨hms, hmslen, -⟩ := hprop n G S hS
  set ms := M₁ n G S
  set m := S.length
  set xG := toWord G
  set xS := toWord S
  set x := toWord (G, S)
  have hx : x = xG ++ xS := rfl
  set y := toWord ms
  set z := toWord (M₂ n G ms)
  set L := x.length
  have hLG : n + 1 ≤ xG.length := toWord_graph_length_ge G
  have hLS : m + 1 ≤ xS.length := toWord_chain_length_ge S
  have hL : L = xG.length + xS.length := by simp [L, hx]
  -- the admissibility of `x`, at its first entry `n`
  have hnx : n ∈ x := by
    rw [hx]; apply List.mem_append_left
    rw [show xG = n :: blocksWord (graphBlocks G) from toWord_graph G]; simp
  set A' := L + n + 1
  have hA1 : 1 ≤ A' := by omega
  set W := 2 ^ (w - 4)
  have hcA : c * A' ^ e ≤ 2 ^ w := hadm n hnx
  have hw4 : 4 ≤ w := by
    by_contra hlt
    have h1 : 2 ^ w ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : c ≤ c * A' ^ e := Nat.le_mul_of_pos_right _ (pow_pos hA1 _)
    omega
  have h2w : 2 ^ w = 16 * W := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_add]; congr 1; omega
  have h2w2 : 2 ^ (w - 2) = 4 * W := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have hw24 : w - 2 - 2 = w - 4 := by omega
  rw [h2w] at hcA
  have sm : ∀ k j, 16 * k ≤ c → j ≤ e → k * A' ^ j ≤ W := fun k j hk hj => small hcA hk hj hA1
  have hnA : n + 1 ≤ A' := by omega
  have hmA : m + 1 ≤ A' := by omega
  have hLA : L + 1 ≤ A' := by omega
  -- the first algorithm
  have hadm₁ : WordAdmissible e₁ c₁ (w - 4) (toWord (G, S)) := by
    intro v hv
    have := hadm v hv
    rw [h2w] at this
    exact small this (by omega) (by omega) (by omega)
  have hT₁ : c₁ * (m + 1) * (n + 1) ^ 3 ≤ W := by
    have := sm c₁ 4 (by omega) (by omega)
    calc c₁ * (m + 1) * (n + 1) ^ 3 ≤ c₁ * A' * A' ^ 3 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hmA) (Nat.pow_le_pow_left hnA _)
      _ = c₁ * A' ^ 4 := by ring
      _ ≤ W := this
  obtain ⟨t₁, ht₁, hrun₁⟩ := ((hc₁ n G S hS) (w - 4) hadm₁).2 hT₁ x rfl
  -- the sizes of the merge sequence
  set D := 3 * A'
  have hD3 : 3 ≤ D := by omega
  have hn3 : n + 3 ≤ D := by omega
  have hn1D : n + 1 ≤ D := by omega
  have hwbG : WB G (2 * D ^ 3) := (wb_graph G).mono (by
    have : (n + 1) * (n + 3) + 1 ≤ 2 * D ^ 2 := by nlinarith
    calc (n + 1) * ((n + 1) * (n + 3) + 1) ≤ D * (2 * D ^ 2) := Nat.mul_le_mul hn1D this
      _ = 2 * D ^ 3 := by ring)
  have hwbm : WB ms (6 * D ^ 4) := (wb_mergeSequence ms).mono (by
    rw [hmslen]
    have h1 : (n + 1) * ((n + 1) * (n + 3) + 2) ≤ 3 * D ^ 3 := by
      have : (n + 1) * (n + 3) + 2 ≤ 3 * D ^ 2 := by nlinarith
      calc (n + 1) * ((n + 1) * (n + 3) + 2) ≤ D * (3 * D ^ 2) := Nat.mul_le_mul hn1D this
        _ = 3 * D ^ 3 := by ring
    have h2 : (n + 1) * ((n + 1) * (n + 3) + 1) ≤ 2 * D ^ 3 := by
      have : (n + 1) * (n + 3) + 1 ≤ 2 * D ^ 2 := by nlinarith
      calc (n + 1) * ((n + 1) * (n + 3) + 1) ≤ D * (2 * D ^ 2) := Nat.mul_le_mul hn1D this
        _ = 2 * D ^ 3 := by ring
    have h3 : 1 ≤ D ^ 3 := Nat.one_le_pow _ _ (by omega)
    calc (m + 1) * ((n + 1) * ((n + 1) * (n + 3) + 2) + (n + 1) * ((n + 1) * (n + 3) + 1) + 1)
        ≤ D * (6 * D ^ 3) := Nat.mul_le_mul (by omega) (by omega)
      _ = 6 * D ^ 4 := by ring)
  have hwb2 : WB (G, ms) (8 * D ^ 4) := (wb_prod hwbG hwbm).mono (by
    have : D ^ 3 ≤ D ^ 4 := Nat.pow_le_pow_right (by omega) (by omega)
    omega)
  have hD8 : 17 * D ^ 4 ≤ D ^ 8 := by
    have : 17 ≤ D ^ 4 := le_trans (by norm_num) (Nat.pow_le_pow_left hD3 4)
    calc 17 * D ^ 4 ≤ D ^ 4 * D ^ 4 := Nat.mul_le_mul_right _ this
      _ = D ^ 8 := by ring
  have hD8W : 2 * D ^ 8 ≤ W := by
    have := sm (2 * 3 ^ 8) 8 (by omega) (by omega)
    calc 2 * D ^ 8 = 2 * 3 ^ 8 * A' ^ 8 := by simp only [D]; ring
      _ ≤ W := this
  have hD4 : 1 ≤ D ^ 4 := Nat.one_le_pow _ _ (by omega)
  -- the second algorithm
  have hx₂ : toWord (G, ms) = xG ++ y := rfl
  have hadm₂ : WordAdmissible e₂ c₂ (w - 4) (toWord (G, ms)) := by
    intro v hv
    have h1 : (toWord (G, ms)).length + v + 1 ≤ D ^ 8 := by
      have := hwb2.1; have := hwb2.2 v hv; omega
    calc c₂ * ((toWord (G, ms)).length + v + 1) ^ e₂ ≤ c₂ * (D ^ 8) ^ e₂ := by gcongr
      _ = c₂ * 3 ^ (8 * e₂) * A' ^ (8 * e₂) := by
          simp only [D]; rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]; ring
      _ ≤ W := sm (c₂ * 3 ^ (8 * e₂)) (8 * e₂) (by omega) (by omega)
  have hT₂ : c₂ * (ms.length + 1) * (n + 1) ^ 2 ≤ W := by
    have := sm c₂ 3 (by omega) (by omega)
    rw [hmslen]
    calc c₂ * (m + 1) * (n + 1) ^ 2 ≤ c₂ * A' * A' ^ 2 :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hmA) (Nat.pow_le_pow_left hnA _)
      _ = c₂ * A' ^ 3 := by ring
      _ ≤ W := this
  obtain ⟨t₂, ht₂, hrun₂⟩ := ((hc₂ n G ms hms) (w - 4) hadm₂).2 hT₂ _ rfl
  -- the inner pipe, at `w - 2`
  have hylen : y.length + 1 < W := by
    have : y.length ≤ 6 * D ^ 4 := hwbm.1
    omega
  have hxGlen : xG.length + L + 2 < W := by
    have : L + 1 ≤ D ^ 4 := by
      calc L + 1 ≤ A' := hLA
        _ ≤ A' ^ 4 := Nat.le_self_pow (n := 4) (by norm_num) A'
        _ ≤ D ^ 4 := Nat.pow_le_pow_left (show A' ≤ D by omega) 4
    omega
  have hxeq : xG.length :: x = xG.length :: (xG ++ xS) := rfl
  have hrunI₁ : RunsTo (w - 2 - 2) p₁ (ρTail.apply fun _ => xG.length :: x) y t₁ := by
    rw [ρTail_apply, hw24]; exact hrun₁
  have hrunI₂ : RunsTo (w - 2 - 2) p₂ (ρGraph.apply ![y, xG.length :: x]) z t₂ := by
    rw [hx, ρGraph_apply, hw24]; exact hrun₂
  have hKI : KI ≤ W := by have := sm KI 0 (by omega) (by omega); simpa using this
  have hK0 : K₀ ≤ W := by have := sm K₀ 0 (by omega) (by omega); simpa using this
  have hf₁ : ρTail.Fits (w - 2) (fun _ => xG.length :: x) := by
    refine ρTail_fits (w := w - 2) (g := xG.length) (x := x) ?_
    rw [h2w2]; omega
  have hf₂ : ρGraph.Fits (w - 2) ![y, xG.length :: x] := by
    rw [hx]
    refine ρGraph_fits (w := w - 2) (y := y) (a := xG) (b := xS) ?_ ?_ ?_
    · rw [h2w2]; omega
    · rw [h2w2]; omega
    · rw [h2w2]; omega
  have hKI' : KI ≤ 2 ^ (w - 2 - 2) := by rw [hw24]; exact hKI
  have hy' : y.length < 2 ^ (w - 2 - 2) := by rw [hw24]; omega
  obtain ⟨tI, htI, hrunI⟩ := hI (w - 2) (xG.length :: x) y z t₁ t₂ hKI' hy' hf₁ hf₂
    hrunI₁ hrunI₂
  -- the length of the graph word, at `w - 2`
  have hgl : (toWord G).length = xG.length := rfl
  obtain ⟨tg, htg, hrung⟩ := graphLength_runsTo G xS (w - 2) (4 * W - 11)
    (by omega)
    (by
      intro v hv
      have := hadm v hv
      rw [h2w] at this
      have h1 : 4 * (L + v + 1) ≤ W := by
        have := small (k := 4) (j := 1) this (by omega) (by omega) (by omega)
        simpa using this
      omega)
    (by rw [h2w2]; omega)
  -- the outer pipe
  have hrun₀ : RunsTo (w - 2) graphLengthProg (ρId.apply fun _ => x) [xG.length] tg := by
    rw [ρId_apply]; exact hrung
  have hrunI' : RunsTo (w - 2) pI (ρLen.apply ![[xG.length], x]) z tI := by
    rw [ρLen_apply]; exact hrunI
  obtain ⟨t, ht, hrun⟩ := h₀ w x [xG.length] z tg tI
    (by rw [h2w2]; omega)
    (by rw [h2w2]; simp; omega)
    (ρId_fits (by rw [h2w]; omega)) (ρLen_fits (by rw [h2w]; omega)) hrun₀ hrunI'
  -- conclusion
  have htime : t ≤ c * (m + 1) * (n + 1) ^ 3 := by
    rw [ρId_cost, ρLen_cost] at ht
    rw [ρTail_cost, ρGraph_cost] at htI
    have hG2 : xG.length ≤ 3 * (n + 1) ^ 2 := toWord_graph_length_le G
    have htg' : tg ≤ 700 * (n + 1) ^ 3 := by
      have : 10 * ((9 * xG.length + 40) * (n + 1)) + 1 ≤ 700 * (n + 1) ^ 3 := by
        have h1 : 1 ≤ n + 1 := by omega
        have h2 : 1 ≤ (n + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
        have h3 : (n + 1) ^ 3 = (n + 1) ^ 2 * (n + 1) := by ring
        nlinarith
      rw [hgl] at htg
      exact htg.trans this
    set P := (m + 1) * (n + 1) ^ 3
    have hP1 : 1 ≤ P := Nat.one_le_iff_ne_zero.mpr (by positivity)
    have h1 : t₁ ≤ c₁ * P := by simp only [P]; rw [← mul_assoc]; exact ht₁
    have h2 : t₂ ≤ c₂ * P := by
      rw [hmslen] at ht₂
      calc t₂ ≤ c₂ * (m + 1) * (n + 1) ^ 2 := ht₂
        _ ≤ c₂ * (m + 1) * (n + 1) ^ 3 := Nat.mul_le_mul_left _
            (Nat.pow_le_pow_right (by omega) (by omega))
        _ = c₂ * P := by ring
    have h3 : tg ≤ 700 * P := htg'.trans (by
      simp only [P]; nlinarith [Nat.one_le_pow 3 (n + 1) (by omega)])
    have h4 : tI ≤ KI * ((c₁ + c₂ + 9) * P) := htI.trans (Nat.mul_le_mul_left _ (by nlinarith))
    have h5 : t ≤ K₀ * ((708 + KI * (c₁ + c₂ + 9)) * P) := ht.trans (Nat.mul_le_mul_left _ (by
      have : KI * ((c₁ + c₂ + 9) * P) = KI * (c₁ + c₂ + 9) * P := by ring
      nlinarith))
    calc t ≤ K₀ * ((708 + KI * (c₁ + c₂ + 9)) * P) := h5
      _ = K₀ * (708 + KI * (c₁ + c₂ + 9)) * P := by ring
      _ ≤ c * P := Nat.mul_le_mul_right _ (by omega)
      _ = c * (m + 1) * (n + 1) ^ 3 := by simp only [P]; ring
  refine ⟨fun y' t' h => (Lax808846Proofs.Machine.runsTo_unique h hrun).1, fun _ y' hy' => ?_⟩
  rw [Set.mem_singleton_iff] at hy'
  subst hy'
  exact ⟨t, htime, hrun⟩

open Lax185574.Graphs Lax185574.Algorithms Lax185574Proofs.Interface
open Lax185574Proofs.Interface.KitG3

/--
---
conclusion: Lax185574.ChainConstructionSequences.exists_constructionSequence_of_chain
---
The statement for graphs and `Algorithm.Computes`, from
the version for simple graphs: the algorithm is the program
with its exponent, the script of a graph is that of its simple graph,
and the constants stay the same.
-/
theorem exists_constructionSequence_of_chain :
    ∃ (A : Algorithm) (c K : ℕ) (script : (G : Graph) → List (Finset (Fin G.n)) → Script G.n),
      ∀ (G : Graph) (S : List (Finset (Fin G.n))), IsChain S →
        let σ := script G S
        IsConstructionSequence G.toSimpleGraph σ.run ∧ σ.HasSmallNumbers ∧
        σ.run.length ≤ K * (G.n + 1) * (chainBound G.toSimpleGraph S 1 + 1) ∧
        (∀ r : ℕ, 1 ≤ r →
          constructionWidth r σ.run ≤ chainBound G.toSimpleGraph S r ∧
          IsRadiusDefinable G.toSimpleGraph σ.run r (2 * S.length + 1)
            (chainBound G.toSimpleGraph S r) 7) ∧
        A.Computes c (G, S) σ ((S.length + 1) * (G.n + 1) ^ 3) := by
  obtain ⟨p, e, K, M, hM, c, hc⟩ := exists_constructionSequence_of_chain_old
  refine ⟨⟨p, e⟩, c, K, fun G S => M G.n G.toSimpleGraph S, fun G S hS => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := hM G.n G.toSimpleGraph S hS
  refine ⟨a1, a2, a3, a4, computes_congr (encode_graph_pair G S).symm rfl
    (computes_of_old le_rfl ?_ (hc G.n G.toSimpleGraph S hS))⟩
  have := one_le_succ_mul_succ_pow S.length G.n 3
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  push_cast
  nlinarith

end Lax185574Proofs.ChainConstructionSequences
