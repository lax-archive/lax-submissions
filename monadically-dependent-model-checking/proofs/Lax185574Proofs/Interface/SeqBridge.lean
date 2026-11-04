import Lax185574Proofs.Interface.ConvPipe
import Lax185574Proofs.Interface.Headline
import Lax185574.Algorithms
import Lax185574Proofs.Words.PrefixFree

/-!
The two directions between programs that read a graph in compressed
sparse row form and algorithms that read the word of the graph.

`nbr_wrap` turns an older program, which halts on every admissible
compressed sparse row input within a time `T₀`, into an algorithm in
the sense of `Lax185574.Algorithms` on the corresponding input with the
word of the graph. The algorithm is the pipe `nbr_bridge`.
`csr_shim` goes the other way, with `csr_bridge`, for an algorithm whose
statement holds at the word lengths the converted input needs. The
lemmas `wrap_adm` and `shim_adm` translate the conditions on the word
length.
-/

namespace Lax185574Proofs.Interface

open Lax808846.Ram Lax185574.Encoding Lax185574.Algorithms Lax185574.WordEncoding
open Lax185574Proofs.Words Lax271696.GraphEncoding Lax185574Proofs.Compose
open Lax808846Proofs.Machine

universe u v

/-! ### Sizes of the two graph words -/

theorem length_csrWord_le (ls : List (List ℕ)) :
    (csrWord ls).length ≤ (nbWord ls).length + 2 := by
  rw [length_csrWord, length_nbWord]; omega

theorem csrWord_entry_le_length {n : ℕ} (H : SimpleGraph (Fin n)) {v : ℕ}
    (hv : v ∈ csrWord (nbLists H)) : v ≤ (nbWord (nbLists H)).length := by
  have := csrWord_entry_le H hv
  rw [length_nbWord, length_nbLists]; omega

theorem toWord_graph_entry_le' {n : ℕ} (G : SimpleGraph (Fin n)) : ∀ v ∈ toWord G, v ≤ n := by
  classical
  intro v hv
  rw [toWord_graph] at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · exact le_rfl
  · simp only [blocksWord, graphBlocks, List.mem_flatten, List.mem_map, List.mem_ofFn] at hv
    obtain ⟨_, ⟨_, ⟨u, rfl⟩, rfl⟩, hvu⟩ := hv
    rcases List.mem_cons.mp hvu with rfl | hvu
    · have : (Finset.words (Finset.univ.filter (G.Adj u))).length ≤ n := by
        simp only [Finset.words, Finset.length_sort]
        exact Finset.card_image_le.trans ((Finset.card_le_univ _).trans (by simp))
      rw [setBlock_length]; omega
    · simp only [setBlock, List.mem_flatten, List.mem_map] at hvu
      obtain ⟨_, ⟨w, hw, rfl⟩, hvw⟩ := hvu
      simp only [Finset.words, Finset.mem_sort, Finset.mem_image] at hw
      obtain ⟨a, -, rfl⟩ := hw
      change v ∈ [1, a.val] at hvw
      simp at hvw
      have := a.isLt
      omega

theorem sum_toWord_graph_le {n : ℕ} (G : SimpleGraph (Fin n)) :
    (toWord G).sum ≤ n * (toWord G).length := by
  have := List.sum_le_card_nsmul (toWord G) n (toWord_graph_entry_le' G)
  simpa [mul_comm] using this

theorem sum_le_length_mul_max (x : List ℕ) : x.sum ≤ x.length * maxEntry x := by
  have := List.sum_le_card_nsmul x (maxEntry x) (fun v hv => le_maxEntry hv)
  simpa using this

/-! ### Lengths of encodings -/

theorem length_encode_nat_rat (r : ℕ) (ε : ℚ) : (encode (r, ε)).length = 4 := by
  change ([r] ++ (toWord ε.num ++ [ε.den])).length = 4
  rcases ε.num with m | m <;> rfl

theorem length_encode_nat_nat_rat (r q : ℕ) (ε : ℚ) : (encode (r, q, ε)).length = 5 := by
  change ([r] ++ ([q] ++ (toWord ε.num ++ [ε.den]))).length = 5
  rcases ε.num with m | m <;> rfl

open Lax185574.ConstructionSequences in
/-- The word of a script is three entries per step plus `n + 1`. -/
theorem length_encode_script_le {n : ℕ} (σ : Script n) :
    (encode σ).length ≤ 3 * σ.run.length + n := by
  change (toWord (List.ofFn σ.colors) ++ toWord σ.steps).length ≤ _
  rw [Lax185574Proofs.Compose.toWord_list_nat]
  have hs : toWord σ.steps = σ.steps.length :: (σ.steps.map toWord).flatten := rfl
  have hf : ((σ.steps.map toWord).flatten).length = 3 * σ.steps.length := by
    rw [List.length_flatten, List.map_map]
    have : ∀ st ∈ σ.steps, (List.length ∘ toWord) st = 3 := fun st _ =>
      Lax185574Proofs.Compose.stepCode_length st
    rw [List.map_congr_left this, List.map_const', List.sum_replicate, smul_eq_mul, mul_comm]
  rw [List.length_append, List.length_cons, hs, List.length_cons, hf]
  simp only [List.length_ofFn, Script.run, List.length_scanl]
  omega

open Lax185574.ConstructionSequences in
theorem one_le_length_run {n : ℕ} (σ : Script n) : 1 ≤ σ.run.length := by
  simp [Script.run, List.length_scanl]

/-! ### Word lengths -/

/-- The admissibility of the converted input, for the wrapper: the
condition of the algorithm at `w` gives the condition of the older
program at `w - 2`. -/
theorem wrap_adm {c e c' w K : ℕ} (P R : List ℕ) {n : ℕ} (H : SimpleGraph (Fin n))
    (hc : 4 * c * 3 ^ e + K ≤ c')
    (h : c' * ((P ++ nbWord (nbLists H) ++ R).length + (P ++ nbWord (nbLists H) ++ R).sum + 1)
      ^ (e + 1) ≤ 2 ^ w) :
    K * ((P ++ nbWord (nbLists H) ++ R).length + (P ++ nbWord (nbLists H) ++ R).sum + 1) ≤
        2 ^ w ∧
      ∀ v ∈ P ++ csrWord (nbLists H) ++ R,
        c * ((P ++ csrWord (nbLists H) ++ R).length + v + 1) ^ e ≤ 2 ^ (w - 2) := by
  set x := P ++ nbWord (nbLists H) ++ R with hx
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = x.length + x.sum + 1 := ⟨_, rfl⟩
  rw [← hZ] at h ⊢
  have hZ1 : 1 ≤ Z := by omega
  have hZZ : Z ≤ Z ^ (e + 1) := Nat.le_self_pow (by omega) Z
  have hZe : Z ^ e ≤ Z ^ (e + 1) := Nat.pow_le_pow_right hZ1 (by omega)
  have hKZ : K * Z ≤ 2 ^ w :=
    le_trans (Nat.mul_le_mul (by omega) hZZ) h
  have hc1 : 4 ≤ 2 ^ w ∨ c = 0 := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · exact Or.inr h0
    · left
      have : 4 * 1 * 1 * 1 ≤ 4 * c * 3 ^ e * Z ^ e :=
        Nat.mul_le_mul (Nat.mul_le_mul (by omega) (Nat.one_le_pow _ _ (by norm_num)))
          (Nat.one_le_pow _ _ hZ1)
      have : 4 * c * 3 ^ e * Z ^ e ≤ c' * Z ^ (e + 1) :=
        Nat.mul_le_mul (by omega) hZe
      omega
  refine ⟨hKZ, fun v hv => ?_⟩
  rcases hc1 with h4 | h0
  swap
  · subst h0; simp
  rw [two_pow_four h4] at h
  have hxl : (P ++ csrWord (nbLists H) ++ R).length ≤ x.length + 2 := by
    have := length_csrWord_le (nbLists H)
    simp only [hx, List.length_append]; omega
  have hv' : v ≤ x.length + x.sum := by
    simp only [List.mem_append] at hv
    rcases hv with (hv | hv) | hv
    · have : v ≤ x.sum := List.le_sum_of_mem (by simp [hx, hv])
      omega
    · have := csrWord_entry_le_length H hv
      have : (nbWord (nbLists H)).length ≤ x.length := by
        simp only [hx, List.length_append]; omega
      omega
    · have : v ≤ x.sum := List.le_sum_of_mem (by simp [hx, hv])
      omega
  have h1 : (P ++ csrWord (nbLists H) ++ R).length + v + 1 ≤ 3 * Z := by omega
  calc c * ((P ++ csrWord (nbLists H) ++ R).length + v + 1) ^ e ≤ c * (3 * Z) ^ e :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 e)
    _ = c * 3 ^ e * Z ^ e := by rw [mul_pow]; ring
    _ ≤ 2 ^ (w - 2) := by
        have : 4 * (c * 3 ^ e * Z ^ e) ≤ c' * Z ^ (e + 1) := by
          have : 4 * (c * 3 ^ e * Z ^ e) = 4 * c * 3 ^ e * Z ^ e := by ring
          rw [this]; exact Nat.mul_le_mul (by omega) hZe
        omega

/-- The admissibility of the converted input, for the shim: the
condition of the older program at `w` gives the fit of the converter and
the condition of the algorithm at `w - 2`. -/
theorem shim_adm {c e c' e' w K : ℕ} {P g R : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)}
    (hg : EncodesGraph g n G) (hc : 4 * 8 ^ e * c + K ≤ c') (he : 3 * e + 2 ≤ e')
    (h : ∀ v ∈ P ++ g ++ R, c' * ((P ++ g ++ R).length + v + 1) ^ e' ≤ 2 ^ w) :
    c' * ((P ++ g ++ R).length + maxEntry (P ++ g ++ R) + 1) ^ e' ≤ 2 ^ w ∧
      K * ((P ++ g ++ R).length + maxEntry (P ++ g ++ R) + 1) ^ 2 ≤ 2 ^ w ∧
      c * ((P ++ toWord G ++ R).length + (P ++ toWord G ++ R).sum + 1) ^ e ≤ 2 ^ (w - 2) := by
  set x := P ++ g ++ R with hx
  have hglen := hg.length_eq
  have hne : x ≠ [] := by
    intro h0
    have := congrArg List.length h0
    simp only [hx, List.length_append, List.length_nil] at this
    omega
  have hM := h _ (maxEntry_mem hne)
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = x.length + maxEntry x + 1 := ⟨_, rfl⟩
  rw [← hZ] at hM ⊢
  have hZ1 : 1 ≤ Z := by omega
  have hZ2 : Z ^ 2 ≤ Z ^ e' := Nat.pow_le_pow_right hZ1 (by omega)
  have hZ3 : Z ^ (3 * e) ≤ Z ^ e' := Nat.pow_le_pow_right hZ1 (by omega)
  refine ⟨hM, le_trans (Nat.mul_le_mul (by omega) hZ2) hM, ?_⟩
  -- sizes of the converted word
  have hnM : n ≤ maxEntry x := le_maxEntry (by
    rw [hx]; simp only [List.mem_append]; left; right
    rw [← hg.vertexCount_eq]; unfold vertexCount
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  have hn1 : n + 1 ≤ Z := by omega
  have hyl : (toWord G).length ≤ 3 * (n + 1) ^ 2 := toWord_graph_length_le G
  have hys : (toWord G).sum ≤ n * (toWord G).length := sum_toWord_graph_le G
  have hPR : P.length + R.length ≤ x.length := by simp only [hx, List.length_append]; omega
  have hPRs : P.sum + R.sum ≤ x.length * maxEntry x := by
    have := sum_le_length_mul_max x
    have : P.sum + R.sum ≤ x.sum := by simp only [hx, List.sum_append]; omega
    omega
  have hn2 : (n + 1) ^ 2 ≤ Z ^ 2 := Nat.pow_le_pow_left hn1 2
  have hZZ2 : Z ≤ Z ^ 2 := Nat.le_self_pow (by norm_num) Z
  have hZ23 : Z ^ 2 ≤ Z ^ 3 := Nat.pow_le_pow_right hZ1 (by omega)
  have hxZ : x.length * maxEntry x ≤ Z ^ 2 := by
    have : x.length * maxEntry x ≤ Z * Z := Nat.mul_le_mul (by omega) (by omega)
    nlinarith
  have hnY : n * (toWord G).length ≤ 3 * Z ^ 3 := by
    have : n * (toWord G).length ≤ Z * (3 * Z ^ 2) :=
      Nat.mul_le_mul (by omega) (le_trans hyl (Nat.mul_le_mul_left _ hn2))
    have e3 : Z * (3 * Z ^ 2) = 3 * Z ^ 3 := by ring
    omega
  have hsz : (P ++ toWord G ++ R).length + (P ++ toWord G ++ R).sum + 1 ≤ 8 * Z ^ 3 := by
    simp only [List.length_append, List.sum_append]
    omega
  calc c * ((P ++ toWord G ++ R).length + (P ++ toWord G ++ R).sum + 1) ^ e
      ≤ c * (8 * Z ^ 3) ^ e := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsz e)
    _ = c * 8 ^ e * Z ^ (3 * e) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ 2 ^ (w - 2) := by
        have h4 : 4 * (c * 8 ^ e * Z ^ (3 * e)) ≤ c' * Z ^ e' := by
          have : 4 * (c * 8 ^ e * Z ^ (3 * e)) = 4 * 8 ^ e * c * Z ^ (3 * e) := by ring
          rw [this]; exact Nat.mul_le_mul (by omega) hZ3
        rcases Nat.eq_zero_or_pos (c * 8 ^ e * Z ^ (3 * e)) with h0 | h0
        · rw [h0]; exact Nat.zero_le _
        · have h4w : 4 ≤ 2 ^ w := by omega
          rw [two_pow_four h4w] at hM
          omega

/-! ### The wrapper -/

/-- **An older program as an algorithm on the word of the graph.** -/
theorem nbr_wrap {k e c K c' : ℕ} {p q : Program} (hq : NbrBridge k p q K)
    {α : Type u} {β : Type v} [Encode α] [Encode β] {a : α} {b : β} {P R : List ℕ}
    (hP : P.length = k) {n : ℕ} (H : SimpleGraph (Fin n))
    (ha : encode a = P ++ nbWord (nbLists H) ++ R) (T₀ : ℕ) {T : ℝ}
    (hold : ∀ w, (∀ v ∈ P ++ csrWord (nbLists H) ++ R,
        c * ((P ++ csrWord (nbLists H) ++ R).length + v + 1) ^ e ≤ 2 ^ w) →
      ∃ t ≤ T₀, RunsTo w p (P ++ csrWord (nbLists H) ++ R) (encode b) t)
    (hc' : 4 * c * 3 ^ e + K ≤ c')
    (hT : ((K * (T₀ + (encode a).length + 1) : ℕ) : ℝ) ≤ c' * T + c') :
    (⟨q, e + 1⟩ : Algorithm).Computes c' a b T := by
  intro w hw
  simp only at hw
  rw [ha] at hw
  obtain ⟨hK, hadm⟩ := wrap_adm P R H hc' hw
  obtain ⟨hf, hb⟩ := hq w P R (nbLists H) hP hK
  obtain ⟨t₂, ht₂, hr₂⟩ := hold (w - 2) hadm
  simp only
  rw [ha]
  refine ⟨fun y t h => ?_, fun _ => ?_⟩
  · obtain ⟨t₂', -, h'⟩ := hb y t h
    exact (runsTo_unique h' hr₂).1
  · obtain ⟨t, ht, hr⟩ := hf _ t₂ hr₂
    refine ⟨t, le_trans ?_ hT, hr⟩
    have : t ≤ K * (T₀ + (encode a).length + 1) := by
      rw [ha]; exact le_trans ht (Nat.mul_le_mul_left _ (by omega))
    exact_mod_cast this

/-! ### The shim -/

/-- **An algorithm on the word of the graph as an older program.** Both
clauses at a word length where the older condition holds: soundness,
and halting once the time of the algorithm fits at `w - 2`. -/
theorem csr_shim {k c K c' e' : ℕ} {A : Algorithm} {q : Program} (hq : CsrBridge k A.program q K)
    {α : Type u} {β : Type v} [Encode α] [Encode β] {a : α} {b : β} {P g R : List ℕ}
    (hP : P.length = k) {n : ℕ} {G : SimpleGraph (Fin n)} (hg : EncodesGraph g n G)
    (ha : encode a = P ++ toWord G ++ R) {T : ℝ} (hA : A.Computes c a b T)
    (hc : 4 * 8 ^ A.wordExponent * c + K ≤ c') (he : 3 * A.wordExponent + 2 ≤ e') (w : ℕ)
    (h : ∀ v ∈ P ++ g ++ R, c' * ((P ++ g ++ R).length + v + 1) ^ e' ≤ 2 ^ w) :
    (∀ y t, RunsTo w q (P ++ g ++ R) y t → y = encode b) ∧
      ((c : ℝ) * T + c ≤ 2 ^ (w - 2) →
        ∃ t : ℕ, (t : ℝ) ≤ K * ((c : ℝ) * T + c + (n + 1) ^ 2 + (P ++ g ++ R).length + 1) ∧
          RunsTo w q (P ++ g ++ R) (encode b) t) := by
  obtain ⟨-, hK, hadm⟩ := shim_adm hg hc he h
  obtain ⟨hf, hb⟩ := hq w P R g n G hP hg hK
  rw [← ha] at hadm hf hb
  obtain ⟨hs, hh⟩ := hA (w - 2) hadm
  refine ⟨fun y t hr => ?_, fun hT => ?_⟩
  · obtain ⟨t₂, -, h₂⟩ := hb y t hr
    exact hs y t₂ h₂
  · obtain ⟨t₂, ht₂, h₂⟩ := hh hT
    obtain ⟨t, ht, hr⟩ := hf _ t₂ h₂
    refine ⟨t, ?_, hr⟩
    have ht' : (t : ℝ) ≤ K * ((t₂ : ℝ) + (n + 1) ^ 2 + (P ++ g ++ R).length + 1) := by
      exact_mod_cast ht
    have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
    nlinarith

/-! ### Time bounds with a prefix -/

/-- The constant of `seq_wrap`. -/
def seqConst (K c e Q k : ℕ) : ℕ := K * (c * Q + 5 * c + c * k + k + 5) + 4 * c * 3 ^ e + K

theorem le_seqConst (K c e Q k : ℕ) : c ≤ seqConst K c e Q k := by
  have : c ≤ 4 * c * 3 ^ e := by
    have := Nat.one_le_pow e 3 (by norm_num)
    nlinarith
  unfold seqConst; omega

/-- **The wrapper for a prefix and a graph**, with the older time
`⌊c · (n+1)^(3+η)⌋ + c · |x|` and the new time `n^(3+η)`. -/
theorem seq_wrap {k e c K : ℕ} {p q : Program} (hq : NbrBridge k p q K)
    {α : Type u} {β : Type v} [Encode α] [Encode β] {a : α} {b : β} {P : List ℕ}
    (hP : P.length = k) {n : ℕ} (H : SimpleGraph (Fin n))
    (ha : encode a = P ++ nbWord (nbLists H)) {η : ℝ} (hη : 0 < η) {Q : ℕ}
    (hQ : (2 : ℝ) ^ (3 + η) ≤ Q)
    (hold : ∀ w, (∀ v ∈ P ++ csrWord (nbLists H),
        c * ((P ++ csrWord (nbLists H)).length + v + 1) ^ e ≤ 2 ^ w) →
      ∃ t ≤ ⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + η)⌋₊ + c * (P ++ csrWord (nbLists H)).length,
        RunsTo w p (P ++ csrWord (nbLists H)) (encode b) t) :
    (⟨q, e + 1⟩ : Algorithm).Computes (seqConst K c e Q k) a b ((n : ℝ) ^ (3 + η)) := by
  have ha' : encode a = P ++ nbWord (nbLists H) ++ [] := by rw [ha, List.append_nil]
  refine nbr_wrap (R := []) hq hP H ha'
    (⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + η)⌋₊ + c * (P ++ csrWord (nbLists H)).length)
    (fun w hw => by rw [List.append_nil] at hw ⊢; exact hold w hw)
    (by unfold seqConst; omega) ?_
  -- the time
  set ls := nbLists H
  set S := ls.flatten.length with hS
  have hSn : S ≤ n * n := length_flatten_nbLists_le H
  have hlsl : ls.length = n := length_nbLists H
  have hxl : (encode a).length = k + 1 + n + 2 * S := by
    rw [ha, List.length_append, length_nbWord, hlsl, hP]; ring
  have hzl : (P ++ csrWord ls).length = k + 3 + n + S := by
    rw [List.length_append, length_csrWord, hlsl, hP]; ring
  rw [hzl, hxl]
  set N := (n : ℝ) ^ (3 + η) with hN
  have hN0 : 0 ≤ N := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hnn := sq_le_rpow hη n
  rw [← hN] at hnn
  have hnr : (n : ℝ) ≤ N + 1 := le_trans (by exact_mod_cast Nat.le_mul_self n) hnn
  have hSr : (S : ℝ) ≤ N + 1 := le_trans (by exact_mod_cast hSn) hnn
  have hfl : (⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + η)⌋₊ : ℝ) ≤ c * Q * (N + 1) := by
    refine (Nat.floor_le (by positivity)).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (rpow_succ_le hη hQ n) (Nat.cast_nonneg _)
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hcn : (c : ℝ) * n ≤ c * (N + 1) := mul_le_mul_of_nonneg_left hnr hc0
  have hcS : (c : ℝ) * S ≤ c * (N + 1) := mul_le_mul_of_nonneg_left hSr hc0
  have hck : (c : ℝ) * (k + 3) ≤ c * (k + 3) * (N + 1) :=
    le_mul_of_one_le_right (by positivity) (by linarith)
  have hk : ((k : ℝ) + 2) ≤ (k + 2) * (N + 1) :=
    le_mul_of_one_le_right (by positivity) (by linarith)
  have hsum : ((⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + η)⌋₊ + c * (k + 3 + n + S) +
      (k + 1 + n + 2 * S) + 1 : ℕ) : ℝ) ≤ (c * Q + 5 * c + c * k + k + 5 : ℕ) * (N + 1) := by
    push_cast
    nlinarith
  have hD : (K : ℝ) * (c * Q + 5 * c + c * k + k + 5 : ℕ) ≤ seqConst K c e Q k := by
    have : K * (c * Q + 5 * c + c * k + k + 5) ≤ seqConst K c e Q k := by unfold seqConst; omega
    exact_mod_cast this
  push_cast at hsum ⊢
  calc (K : ℝ) * (⌊(c : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + η)⌋₊ + c * (k + 3 + n + S) +
        (k + 1 + n + 2 * S) + 1)
      ≤ K * ((c * Q + 5 * c + c * k + k + 5) * (N + 1)) :=
        mul_le_mul_of_nonneg_left hsum hK0
    _ = K * (c * Q + 5 * c + c * k + k + 5) * (N + 1) := by ring
    _ ≤ seqConst K c e Q k * (N + 1) := by
        push_cast at hD
        exact mul_le_mul_of_nonneg_right hD (by linarith)
    _ = seqConst K c e Q k * N + seqConst K c e Q k := by ring

/-- **The shim for a prefix and a graph**: halting of the older program
at every word length where its condition holds, within the older time
`⌊c' · (n+1)^(3+η)⌋ + c' · |x|`. The algorithm is used with the time
`n^(3 + min η 1)`. -/
theorem seq_shim {k c K c' : ℕ} {A : Algorithm} {q : Program} (hq : CsrBridge k A.program q K)
    {α : Type u} {β : Type v} [Encode α] [Encode β] {a : α} {b : β} {P g : List ℕ}
    (hP : P.length = k) {n : ℕ} {G : SimpleGraph (Fin n)} (hg : EncodesGraph g n G)
    (ha : encode a = P ++ toWord G) {η : ℝ} (hη : 0 < η)
    (hA : A.Computes c a b ((n : ℝ) ^ (3 + min η 1)))
    (hc' : 4 * 8 ^ A.wordExponent * c + 8 * c + K * (c + 2) + K ≤ c') (w : ℕ)
    (h : ∀ v ∈ P ++ g, c' * ((P ++ g).length + v + 1) ^ (3 * A.wordExponent + 4) ≤ 2 ^ w) :
    ∃ t ≤ ⌊(c' : ℝ) * ((n : ℝ) + 1) ^ ((3 : ℝ) + η)⌋₊ + c' * (P ++ g).length,
      RunsTo w q (P ++ g) (encode b) t := by
  have ha' : encode a = P ++ toWord G ++ [] := by rw [ha, List.append_nil]
  have h' : ∀ v ∈ P ++ g ++ [], c' * ((P ++ g ++ []).length + v + 1) ^ (3 * A.wordExponent + 4)
      ≤ 2 ^ w := by simpa using h
  obtain ⟨hM, -, -⟩ := shim_adm (K := K) (c := c) (e := A.wordExponent) hg (by omega) (by omega) h'
  obtain ⟨-, hh⟩ := csr_shim hq hP hg ha' hA (by omega) (by omega) w h'
  simp only [List.append_nil] at hM hh
  set x := P ++ g with hx
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = x.length + maxEntry x + 1 := ⟨_, rfl⟩
  rw [← hZ] at hM
  have hglen := hg.length_eq
  have hx1 : 1 ≤ x.length := by
    have : g.length ≤ x.length := by simp only [hx, List.length_append]; omega
    omega
  have hnM : n ≤ maxEntry x := le_maxEntry (by
    rw [hx]; simp only [List.mem_append]; right
    rw [← hg.vertexCount_eq]; unfold vertexCount
    rw [List.getD_eq_getElem _ _ (by omega)]; exact List.getElem_mem _)
  have hn1 : n + 1 ≤ Z := by omega
  have hZ1 : 1 ≤ Z := by omega
  -- the time of the algorithm fits
  set η' := min η 1 with hη'
  have hη'0 : 0 < η' := lt_min hη one_pos
  have hη'1 : η' ≤ 1 := min_le_right _ _
  have hη'η : η' ≤ η := min_le_left _ _
  have hn4 : (n : ℝ) ^ (3 + η') ≤ ((n + 1 : ℕ) : ℝ) ^ (4 : ℕ) := by
    have h1 : (n : ℝ) ^ (3 + η') ≤ ((n : ℝ) + 1) ^ (3 + η') :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) (by linarith)
    have h2 : ((n : ℝ) + 1) ^ (3 + η') ≤ ((n : ℝ) + 1) ^ ((4 : ℕ) : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)])
        (by push_cast; linarith)
    rw [Real.rpow_natCast] at h2
    push_cast
    linarith
  have hZ4 : (n + 1) ^ 4 ≤ Z ^ (3 * A.wordExponent + 4) :=
    le_trans (Nat.pow_le_pow_left hn1 4) (Nat.pow_le_pow_right hZ1 (by omega))
  have hfitN : 8 * c * (n + 1) ^ 4 ≤ 2 ^ w :=
    le_trans (Nat.mul_le_mul (by omega) hZ4) hM
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg _
  have hfit : (c : ℝ) * (n : ℝ) ^ (3 + η') + c ≤ 2 ^ (w - 2) := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; simp
    have h4w : 4 ≤ 2 ^ w := by
      have : 8 * 1 * 1 ≤ 8 * c * (n + 1) ^ 4 :=
        Nat.mul_le_mul (by omega) (Nat.one_le_pow _ _ (by omega))
      omega
    have e4 := two_pow_four h4w
    have h1 : (8 * c * (n + 1) ^ 4 : ℝ) ≤ 4 * 2 ^ (w - 2) := by
      have : 8 * c * (n + 1) ^ 4 ≤ 4 * 2 ^ (w - 2) := by omega
      exact_mod_cast this
    have h2 : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) ^ (4 : ℕ) := by
      have : 1 ≤ (n + 1) ^ 4 := Nat.one_le_pow _ _ (by omega)
      exact_mod_cast this
    have h3 : (c : ℝ) * (n : ℝ) ^ (3 + η') ≤ c * ((n + 1 : ℕ) : ℝ) ^ (4 : ℕ) :=
      mul_le_mul_of_nonneg_left hn4 hc0
    push_cast at h1 h2 h3 ⊢
    nlinarith
  obtain ⟨t, ht, hr⟩ := hh hfit
  refine ⟨t, ?_, hr⟩
  -- the time of the older program
  set Y := ((n : ℝ) + 1) ^ ((3 : ℝ) + η) with hY
  have hn1r : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hY1 : 1 ≤ Y := Real.one_le_rpow hn1r (by linarith)
  have hnY : (n : ℝ) ^ (3 + η') ≤ Y :=
    le_trans (Real.rpow_le_rpow (Nat.cast_nonneg _) (by linarith) (by linarith))
      (Real.rpow_le_rpow_of_exponent_le hn1r (by linarith))
  have h2Y : ((n : ℝ) + 1) ^ 2 ≤ Y := by
    have := Real.rpow_le_rpow_of_exponent_le hn1r (show ((2 : ℕ) : ℝ) ≤ (3 : ℝ) + η by
      push_cast; linarith)
    rwa [Real.rpow_natCast] at this
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hxr : (1 : ℝ) ≤ x.length := by exact_mod_cast hx1
  have htr : (t : ℝ) ≤ c' * Y + c' * x.length := by
    have hcK : ((K * (c + 2) : ℕ) : ℝ) ≤ c' := by exact_mod_cast (show K * (c + 2) ≤ c' by omega)
    push_cast at hcK
    have h1 : (K : ℝ) * ((c : ℝ) * (n : ℝ) ^ (3 + η') + c + ((n : ℝ) + 1) ^ 2 + x.length + 1) ≤
        K * ((c + 1) * Y + (c + 2) * x.length) := by
      apply mul_le_mul_of_nonneg_left _ hK0
      nlinarith
    have h2 : (K : ℝ) * ((c + 1) * Y + (c + 2) * x.length) ≤ c' * Y + c' * x.length := by
      have : (K : ℝ) * (c + 1) ≤ c' := by nlinarith
      nlinarith
    push_cast at ht
    linarith
  rcases le_or_gt t (c' * x.length) with hle | hlt
  · omega
  · have : t - c' * x.length ≤ ⌊(c' : ℝ) * Y⌋₊ := by
      apply Nat.le_floor
      push_cast [Nat.cast_sub hlt.le]
      linarith
    omega

/-! ### Choosing the script and decoding the input -/

open Lax185574.ConstructionSequences in
/-- A script whose encoding is `f x`, if there is one. -/
noncomputable def scriptOf (f : List ℕ → List ℕ) (n : ℕ) (x : List ℕ) : Script n :=
  open Classical in
  if h : ∃ σ : Script n, f x = encode σ then Classical.choose h else ⟨fun _ => 0, []⟩

open Lax185574.ConstructionSequences in
theorem scriptOf_spec {f : List ℕ → List ℕ} {n : ℕ} {x : List ℕ}
    {s : List (Lax185574.PartialGraphs.PartialGraph (Fin n))} (hs : EncodesSequence (f x) s) :
    f x = encode (scriptOf f n x) ∧ s = (scriptOf f n x).run := by
  obtain ⟨σ, h1, h2⟩ := hs
  have h : ∃ σ : Script n, f x = encode σ := ⟨σ, h1⟩
  have hspec : f x = encode (scriptOf f n x) := by
    unfold scriptOf; rw [dif_pos h]; exact Classical.choose_spec h
  refine ⟨hspec, ?_⟩
  exact encodesSequence_unique ⟨σ, h1, h2⟩ ⟨_, hspec, rfl⟩

/-- The graph of a compressed sparse row word is determined by the
word. -/
theorem encodesGraph_unique' {g : List ℕ} {n n' : ℕ} {G : SimpleGraph (Fin n)}
    {G' : SimpleGraph (Fin n')} (h : EncodesGraph g n G) (h' : EncodesGraph g n' G') :
    (⟨n, G⟩ : Σ n, SimpleGraph (Fin n)) = ⟨n', G'⟩ := by
  have hn : n = n' := h.vertexCount_eq.symm.trans h'.vertexCount_eq
  subst hn
  have : G = G' := by
    ext u v
    rw [h.adj_iff, h'.adj_iff]
  rw [this]

/-- The output of a function of the decoded prefix and graph, and `[]`
on words that encode nothing. -/
noncomputable def decodePre {π : Type u} [Encode π] (F : π → (Σ n, SimpleGraph (Fin n)) → List ℕ)
    (x : List ℕ) : List ℕ :=
  open Classical in
  if h : ∃ p : π × (Σ n, SimpleGraph (Fin n)), ∃ g : List ℕ,
      EncodesGraph g p.2.1 p.2.2 ∧ x = encode p.1 ++ g then
    F (Classical.choose h).1 (Classical.choose h).2 else []

theorem decodePre_eq {π : Type u} [Encode π] [PrefixFree π]
    (F : π → (Σ n, SimpleGraph (Fin n)) → List ℕ) {x g : List ℕ} {a : π} {n : ℕ}
    {G : SimpleGraph (Fin n)} (hg : EncodesGraph g n G) (hx : x = encode a ++ g) :
    decodePre F x = F a ⟨n, G⟩ := by
  subst hx
  have h : ∃ p : π × (Σ n, SimpleGraph (Fin n)), ∃ g' : List ℕ,
      EncodesGraph g' p.2.1 p.2.2 ∧ encode a ++ g = encode p.1 ++ g' :=
    ⟨(a, ⟨n, G⟩), g, hg, rfl⟩
  unfold decodePre
  rw [dif_pos h]
  obtain ⟨g', hg', hx'⟩ := Classical.choose_spec h
  obtain ⟨h1, h2⟩ := Lax185574Proofs.Words.prefix_inj' hx'
  subst h2
  have h3 : (Classical.choose h).2 = ⟨n, G⟩ := encodesGraph_unique' hg' hg
  rw [← h1, h3]

end Lax185574Proofs.Interface
