import Lax185574Proofs.LegacyInstance
import Lax710763.MonadicDependence
import Lax808846.RamComputes
import Lax185574.Algorithms
import Lax185574Proofs.Interface.Encode
import Lax185574Proofs.Interface.MDBridge
import Lax185574Proofs.Interface.NbrToCsr
import Lax185574Proofs.Interface.Precomp

/-!
The model-checking theorem in the form of `Lax185574.Algorithms`.

`OldHeadline` is the form in which the model-checking theorem is first
proved, from thm:skel-few-types and thm:mc. Its program reads
a graph in compressed sparse row form followed by the sentence, its
graph classes are those of the archive and its sentences those of
`Lax3.FirstOrder`. `NewHeadline` is the statement of
`Lax185574.ModelChecking.exists_program_modelChecking`, for graphs,
sentences and algorithms of this submission: an algorithm decides `G ⊨ φ` from
`(G, φ)` in time `O(n^(3+ε))`.

The algorithm of `NewHeadline` is the pipe of `nbrToCsr`, which turns
the word of the graph into its compressed sparse row word, into the
program of `OldHeadline`. The converter takes time linear in the length
of the graph word, which is `O(n²)`. So is the linear term of the old
time bound, and both are within `n^(3+ε)`. A monadically dependent
class gives a monadically dependent class of the archive by
`monadicallyDependent_toOld`, and satisfaction agrees by
`models_iff_sat`.
-/

namespace Lax185574Proofs.Interface

open Lax808846.Ram Lax808846.RamComputes Lax808846Proofs.Machine Lax185574Proofs.Simulate
open Lax185574.Encoding Lax185574.WordEncoding Lax185574.Algorithms
open Lax808846Proofs.Compile Lax808846Proofs.Reasoning Lax185574Proofs.Words

section Statements

open Lax3.FirstOrder
open Lax199508.GraphClasses Lax710763.MonadicDependence
open Lax808846.Ram Lax808846.RamComputes
open Lax185574.InstanceEncoding

open Classical in
/-- The model-checking theorem for programs reading a graph in compressed
sparse row form, graph classes of the archive and sentences of
`Lax3.FirstOrder`: the former statement of
`Lax185574.ModelChecking.exists_program_modelChecking`. -/
def OldHeadline : Prop :=
    ∃ (p : Program) (e : ℕ),
      ∀ (C : GraphClass), MonadicallyDependent C →
      ∀ (φ : FO 0) (ε : ℝ), 0 < ε →
        ∃ c : ℕ,
          ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (w : ℕ), C n G →
            ComputesInTime w p
              {x | EncodesInstance x n G φ ∧
                ∀ v ∈ x, c * (x.length + v + 1) ^ e ≤ 2 ^ w}
              (fun _ => if Sat G Fin.elim0 φ then [1] else [0])
              (fun x => ⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + ε)⌋₊ + c * x.length)

end Statements

open Lax185574.Graphs Lax185574.FirstOrderLogic

/-- The model-checking theorem for the graphs, sentences and algorithms
of this submission. -/
def NewHeadline : Prop :=
  ∃ A : Algorithm, ∀ C : GraphClass, Lax185574.MonadicDependence.MonadicallyDependent C →
    ∀ (φ : Sentence) (ε : ℝ), 0 < ε → ∃ c : ℕ,
      ∀ G ∈ C, A.Decides c (G, φ) (G ⊨ φ) ((G.n : ℝ) ^ (3 + ε))

/-! ### The rewrite after the converter -/

/-- The rewrite `![y, x] ↦ y.drop 1 ++ x.drop y₀`: the converted graph,
followed by the input after the graph word. -/
def csrRw : Rewrite 2 := [.slice 0 (.lit 1) none, .slice 1 (.entry 0 0) none]

theorem csrRw_apply (y x : List ℕ) : csrRw.apply ![y, x] = y.drop 1 ++ x.drop (y.getD 0 0) := by
  simp [csrRw, Rewrite.apply, Segment.apply, HExpr.eval]

theorem csrRw_cost (y x : List ℕ) : csrRw.cost ![y, x] = 5 := by
  simp [csrRw, Rewrite.cost, Segment.cost, HExpr.cost]

theorem csrRw_fits {w : ℕ} {y x : List ℕ} (hy : y.length < 2 ^ w) (hx : x.length < 2 ^ w)
    (h0 : y.getD 0 0 < 2 ^ w) (hr : (csrRw.apply ![y, x]).length < 2 ^ w) (h1 : 1 < 2 ^ w) :
    csrRw.Fits w ![y, x] := by
  refine ⟨fun i => ?_, hr, ?_⟩
  · fin_cases i <;> simpa
  · intro seg hseg
    simp only [csrRw, List.mem_cons, List.mem_nil_iff, or_false] at hseg
    rcases hseg with rfl | rfl
    · exact ⟨trivial, by simpa [HExpr.eval] using h1⟩
    · refine ⟨by simp [HExpr.Fits], by simpa [HExpr.eval] using h0⟩

/-! ### Bounds on the words -/

theorem maxEntry_le_sum (x : List ℕ) : maxEntry x ≤ x.sum := by
  by_cases hx : x = []
  · subst hx; simp [maxEntry]
  · exact List.le_sum_of_mem (maxEntry_mem hx)

theorem length_flatten_nbLists_le {n : ℕ} (G : SimpleGraph (Fin n)) :
    (nbLists G).flatten.length ≤ n * n := by
  rw [List.length_flatten]
  have h := List.sum_le_card_nsmul ((nbLists G).map List.length) n (by
    intro a ha
    simp only [nbLists, List.map_ofFn, List.mem_ofFn, Function.comp] at ha
    obtain ⟨v, rfl⟩ := ha
    rw [length_sortedVals]
    exact (Finset.card_le_univ _).trans (by simp))
  simpa [length_nbLists] using h

theorem csrWord_entry_le {n : ℕ} (G : SimpleGraph (Fin n)) {v : ℕ}
    (hv : v ∈ csrWord (nbLists G)) : v ≤ n + (nbLists G).flatten.length := by
  simp only [csrWord, List.mem_cons, List.mem_append, length_nbLists] at hv
  rcases hv with rfl | rfl | hv | hv
  · omega
  · omega
  · simp only [arrOf, List.mem_map, List.mem_range] at hv
    obtain ⟨i, -, rfl⟩ := hv
    have := offs_le (nbLists G) i; omega
  · have := flatten_nbLists_lt G hv; omega

/-! ### Real bounds -/

theorem rpow_succ_le {ε : ℝ} (hε : 0 < ε) {Q : ℕ} (hQ : (2 : ℝ) ^ (3 + ε) ≤ Q) (n : ℕ) :
    ((n : ℝ) + 1) ^ (3 + ε) ≤ Q * ((n : ℝ) ^ (3 + ε) + 1) := by
  have h0 : (0 : ℝ) ≤ (n : ℝ) ^ (3 + ε) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h8 : (1 : ℝ) ≤ (2 : ℝ) ^ (3 + ε) := Real.one_le_rpow (by norm_num) (by linarith)
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, zero_add, Real.one_rpow,
      Real.zero_rpow (show (3 : ℝ) + ε ≠ 0 by linarith)]
    linarith
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have h1 : ((n : ℝ) + 1) ^ (3 + ε) ≤ (2 * (n : ℝ)) ^ (3 + ε) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    rw [Real.mul_rpow (by norm_num) (by positivity)] at h1
    nlinarith

theorem sq_le_rpow {ε : ℝ} (hε : 0 < ε) (n : ℕ) :
    ((n * n : ℕ) : ℝ) ≤ (n : ℝ) ^ (3 + ε) + 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have := Real.rpow_nonneg (le_refl (0 : ℝ)) (3 + ε)
    norm_num
    linarith
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have : (n : ℝ) ^ (2 : ℝ) ≤ (n : ℝ) ^ (3 + ε) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
    push_cast
    nlinarith

/-! ### The theorem -/

open Classical in
theorem decide_models_word (G : Graph) (φ : Sentence) :
    encode (decide (G ⊨ φ)) =
      (open Classical in
        if Lax3.FirstOrder.Sat G.toSimpleGraph Fin.elim0 (Formula.toFO φ) then [1] else [0]) := by
  classical
  rw [encode_eq_toWord]
  by_cases h : G ⊨ φ
  · have h' := (models_iff_sat G φ).mp h
    simp [h, h', word_simps]
  · have h' : ¬ Lax3.FirstOrder.Sat G.toSimpleGraph Fin.elim0 (Formula.toFO φ) :=
      fun hs => h ((models_iff_sat G φ).mpr hs)
    simp [h, h', word_simps]

/-- **The model-checking theorem in the new form**, from the old one. -/
theorem modelChecking_of_old : OldHeadline → NewHeadline := by
  rintro ⟨p, e, hp⟩
  obtain ⟨q, K, hq⟩ := pipe_after (compileProgram nbrLayout nbrToCsr) p csrRw
  refine ⟨⟨q, e + 1⟩, fun C hC φ ε hε => ?_⟩
  obtain ⟨c, hc⟩ := hp (toOld C) (monadicallyDependent_toOld hC) (Formula.toFO φ) ε hε
  obtain ⟨L, hL⟩ : ∃ L, L = (toWord (Formula.toFO φ)).length := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, (2 : ℝ) ^ (3 + ε) ≤ Q := ⟨⌈(2 : ℝ) ^ (3 + ε)⌉₊, Nat.le_ceil _⟩
  obtain ⟨D, hD⟩ : ∃ D, D = 3409 + c * Q + c * (5 + L) := ⟨_, rfl⟩
  obtain ⟨c', hc'⟩ : ∃ c', c' = K * D + 4 * c * 3 ^ e + 4 * K + 200 := ⟨_, rfl⟩
  refine ⟨c', fun G hG => ?_⟩
  -- the words
  have hSn : (nbLists G.toSimpleGraph).flatten.length ≤ G.n * G.n :=
    length_flatten_nbLists_le G.toSimpleGraph
  have hgl : (nbWord (nbLists G.toSimpleGraph)).length =
      1 + G.n + 2 * (nbLists G.toSimpleGraph).flatten.length := by
    rw [length_nbWord, length_nbLists]
  have hx : encode (G, φ) = nbWord (nbLists G.toSimpleGraph) ++ toWord (Formula.toFO φ) := by
    rw [encode_graph_sentence, toWord_graph_eq]
  set ls := nbLists G.toSimpleGraph with hls
  set S := ls.flatten.length with hS
  set g := nbWord ls with hg
  set f := toWord (Formula.toFO φ) with hf
  set n := G.n with hn
  have hlsl : ls.length = n := length_nbLists _
  have hxl : (g ++ f).length = 1 + n + 2 * S + L := by rw [List.length_append, hgl, hL]
  have hz0l : (csrWord ls ++ f).length = 3 + n + S + L := by
    simp only [csrWord, List.length_append, List.length_cons, length_arrOf, hlsl, hL]
    omega
  have happ : csrRw.apply ![g.length :: csrWord ls, g ++ f] = csrWord ls ++ f := by
    rw [csrRw_apply]; simp
  have hfs : f.sum ≤ (g ++ f).sum := by simp
  have hz0e : ∀ v ∈ csrWord ls ++ f, v ≤ (g ++ f).length + (g ++ f).sum := by
    intro v hv
    rcases List.mem_append.mp hv with hv | hv
    · have : v ≤ n + S := csrWord_entry_le G.toSimpleGraph hv
      omega
    · have := List.le_sum_of_mem hv; omega
  have hinst : Lax185574.InstanceEncoding.EncodesInstance (csrWord ls ++ f) n G.toSimpleGraph
      (Formula.toFO φ) := ⟨csrWord ls, encodesGraph_csrWord G.toSimpleGraph, rfl⟩
  have hmem : toOld C n G.toSimpleGraph := (toOld_iff C G).mpr hG
  unfold Algorithm.Decides Algorithm.Computes
  rw [hx, decide_models_word]
  intro w hw
  simp only at hw
  -- the word length
  obtain ⟨X, hX⟩ : ∃ X, X = (g ++ f).length := ⟨_, rfl⟩
  obtain ⟨Sx, hSx⟩ : ∃ Sx, Sx = (g ++ f).sum := ⟨_, rfl⟩
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = X + Sx + 1 := ⟨_, rfl⟩
  rw [← hX, ← hSx, ← hZ] at hw
  have hM : maxEntry (g ++ f) ≤ Sx := hSx ▸ maxEntry_le_sum _
  have hZ1 : 1 ≤ Z := by omega
  have hZZ : Z ≤ Z ^ (e + 1) := Nat.le_self_pow (by omega) Z
  have hZe : Z ^ e ≤ Z ^ (e + 1) := Nat.pow_le_pow_right hZ1 (by omega)
  have hc'Z : c' * Z ≤ 2 ^ w := (Nat.mul_le_mul_left _ hZZ).trans hw
  have hc'Ze : c' * Z ^ e ≤ 2 ^ w := (Nat.mul_le_mul_left _ hZe).trans hw
  have hc'1 : c' ≤ 2 ^ w := (Nat.le_mul_of_pos_right _ hZ1).trans hc'Z
  have hw2 : 2 ≤ w := by
    by_contra h
    have : 2 ^ w ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨V, hV⟩ : ∃ V, V = 2 ^ (w - 2) := ⟨_, rfl⟩
  have h4V : 2 ^ w = 4 * V := by
    rw [hV, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
  have hVw : V ≤ 2 ^ w := by omega
  -- the converter
  have hconv : 2 * ((g ++ f).length + maxEntry (g ++ f) + 2) + 16 ≤ 2 ^ (w - 2) := by
    rw [← hV, ← hX]
    have : 200 * Z ≤ c' * Z := Nat.mul_le_mul_right _ (by omega)
    omega
  obtain ⟨t₁, ht₁, hr₁⟩ := nbrToCsr_runsTo ls f (w - 2) hconv
  -- the old program
  have hadm : ∀ v ∈ csrWord ls ++ f, c * ((csrWord ls ++ f).length + v + 1) ^ e ≤ 2 ^ (w - 2) := by
    intro v hv
    have h1 : (csrWord ls ++ f).length + v + 1 ≤ 3 * Z := by
      have := hz0e v hv; omega
    have h2 : c * ((csrWord ls ++ f).length + v + 1) ^ e ≤ c * 3 ^ e * Z ^ e := by
      rw [mul_assoc, ← mul_pow]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 e)
    have h3 : 4 * c * 3 ^ e * Z ^ e ≤ c' * Z ^ e := Nat.mul_le_mul_right _ (by omega)
    rw [← hV]
    have : 4 * c * 3 ^ e * Z ^ e = 4 * (c * 3 ^ e * Z ^ e) := by ring
    omega
  obtain ⟨t₂, ht₂, hr₂⟩ := hc n G.toSimpleGraph (w - 2) hmem (csrWord ls ++ f) ⟨hinst, hadm⟩
  have huniq : ∀ z' t, RunsTo (w - 2) p (csrWord ls ++ f) z' t →
      z' = (open Classical in
        if Lax3.FirstOrder.Sat G.toSimpleGraph Fin.elim0 (Formula.toFO φ) then [1] else [0]) :=
    fun z' t h => (runsTo_unique h hr₂).1
  -- the pipe
  have hyl : (g.length :: csrWord ls).length = 4 + n + S := by
    simp only [csrWord, List.length_cons, List.length_append, length_arrOf, hlsl]
    omega
  have hKV : K ≤ 2 ^ (w - 2) := by rw [← hV]; omega
  have hxV : (g ++ f).length < 2 ^ (w - 2) := by
    rw [← hV, ← hX]
    have : 200 * Z ≤ c' * Z := Nat.mul_le_mul_right _ (by omega)
    omega
  have hyV : (g.length :: csrWord ls).length < 2 ^ (w - 2) := by
    rw [← hV, hyl]
    have : 200 * Z ≤ c' * Z := Nat.mul_le_mul_right _ (by omega)
    omega
  have hfit : csrRw.Fits w ![g.length :: csrWord ls, g ++ f] := by
    refine csrRw_fits (by omega) (by omega) ?_ ?_ (by omega)
    · simp only [List.getD_cons_zero]; omega
    · rw [happ, hz0l]; omega
  rw [← happ] at hr₂ huniq
  obtain ⟨⟨t, ht, hrun⟩, hsound⟩ := hq w (g ++ f) (g.length :: csrWord ls) _ t₁ t₂ hKV hxV hyV
    hfit hr₁ hr₂ huniq
  refine ⟨fun z' t' h => hsound z' t' h, fun _ => ⟨t, ?_, hrun⟩⟩
  -- the time
  rw [csrRw_cost] at ht
  set P := (n : ℝ) ^ (3 + ε) with hP
  have hP0 : 0 ≤ P := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hnn := sq_le_rpow hε n
  rw [← hP] at hnn
  have hnr : (n : ℝ) ≤ P + 1 := le_trans (by exact_mod_cast Nat.le_mul_self n) hnn
  have hSr : (S : ℝ) ≤ P + 1 := le_trans (by exact_mod_cast hSn) hnn
  have hfl : (⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + ε)⌋₊ : ℝ) ≤ c * Q * (P + 1) := by
    refine (Nat.floor_le (by positivity)).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (rpow_succ_le hε hQ n) (Nat.cast_nonneg _)
  have ht₁r : (t₁ : ℝ) ≤ 700 * (1 + n + 2 * S) + 601 := by
    have : t₁ ≤ 700 * (1 + n + 2 * S) + 601 := by rw [← hgl]; exact ht₁
    exact_mod_cast this
  have ht₂r : (t₂ : ℝ) ≤ ⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + ε)⌋₊ + c * (3 + n + S + L) := by
    have : t₂ ≤ ⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + ε)⌋₊ + c * (3 + n + S + L) := by
      rw [← hz0l]; exact ht₂
    exact_mod_cast this
  have htr : (t : ℝ) ≤ K * ((t₁ : ℝ) + t₂ + 3 + 5) := by exact_mod_cast ht
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hcn : (c : ℝ) * n ≤ c * (P + 1) := mul_le_mul_of_nonneg_left hnr hc0
  have hcS : (c : ℝ) * S ≤ c * (P + 1) := mul_le_mul_of_nonneg_left hSr hc0
  have hcL : (c : ℝ) * (3 + L) ≤ c * (3 + L) * (P + 1) :=
    le_mul_of_one_le_right (by positivity) (by linarith)
  have hsum : (t₁ : ℝ) + t₂ + 3 + 5 ≤ D * (P + 1) := by
    rw [hD]; push_cast
    nlinarith
  have hKD : (K : ℝ) * D ≤ c' := by
    have : K * D ≤ c' := by rw [hc']; omega
    exact_mod_cast this
  calc (t : ℝ) ≤ K * ((t₁ : ℝ) + t₂ + 3 + 5) := htr
    _ ≤ K * (D * (P + 1)) := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg _)
    _ = K * D * (P + 1) := by ring
    _ ≤ c' * (P + 1) := mul_le_mul_of_nonneg_right hKD (by linarith)
    _ = c' * P + c' := by ring

end Lax185574Proofs.Interface
