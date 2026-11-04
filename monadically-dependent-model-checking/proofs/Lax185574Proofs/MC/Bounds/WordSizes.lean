import Lax185574Proofs.Lib.DistMatrix
import Lax185574Proofs.MC.Bounds.CallSteps
import Lax185574Proofs.MC.Bounds.TreeMax
import Lax185574Proofs.MC.Bounds.TreeEntries

/-!
The sizes of the words of the pipeline of thm:mc.

`Small u L M` says that the word `u` has length at most `L` and entries
at most `L + M`. The word of a partial graph on `n` vertices is small
for `L = 5 (n + 1) ^ 2`, the word of the family of its trees for
`L = 1 + n (T + c)` with `T` a bound on the tree lengths, and `M` a bound
on the colors in both cases. For the calls of a script `σ`, the query
`callQ` and the answer `callY` are small for `L = callB n T q φ =
2 (n + 2) (T + 5 (n + 1) + kq q φ)`, with `T = treeMax σ.run q`, the
constant `kq` of the rank and the sentence, and `M` the largest entry of
the word of `σ`.
-/

namespace Lax185574Proofs.MC

open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.ConstructionSequences Lax185574.TypeTrees Lax185574.PartialGraphEncoding
open Lax185574.ResolveLift Lax185574Proofs.Words Lax185574Proofs.Simulate

/-- The word `u` has length at most `L` and entries at most `L + M`. -/
def Small (u : List ℕ) (L M : ℕ) : Prop := u.length ≤ L ∧ ∀ e ∈ u, e ≤ L + M

theorem Small.mono {u : List ℕ} {L M L' M' : ℕ} (h : Small u L M) (hL : L ≤ L') (hM : M ≤ M') :
    Small u L' M' :=
  ⟨le_trans h.1 hL, fun e he => le_trans (h.2 e he) (by omega)⟩

theorem Small.append {u v : List ℕ} {L L' M : ℕ} (hu : Small u L M) (hv : Small v L' M) :
    Small (u ++ v) (L + L') M := by
  refine ⟨by simp only [List.length_append]; have := hu.1; have := hv.1; omega, fun e he => ?_⟩
  rcases List.mem_append.1 he with h | h
  · have := hu.2 e h; omega
  · have := hv.2 e h; omega

/-- The length plus the largest entry of a fixed word. -/
def fixW (u : List ℕ) : ℕ := u.length + maxEntry u

theorem small_fix (u : List ℕ) (M : ℕ) : Small u (fixW u) M :=
  ⟨by unfold fixW; omega, fun e he => by have := le_maxEntry he; unfold fixW; omega⟩

theorem small_nat {P M : ℕ} (h : P ≤ M) : Small (toWord P) 1 M :=
  ⟨by simp [word_simps], fun e he => by simp [word_simps] at he; omega⟩

theorem small_bool (b : Bool) (M : ℕ) : Small (toWord b) 1 M :=
  ⟨by simp [word_simps], fun e he => by simp [word_simps] at he; split_ifs at he <;> omega⟩

theorem small_swIn {a b c : List ℕ} {La Lb Lc M : ℕ} (ha : Small a La M) (hb : Small b Lb M)
    (hc : Small c Lc M) : Small (swIn a b c) (3 + 2 * (La + Lb + Lc)) M := by
  have h3 : Small [a.length, b.length, c.length] (3 + La + Lb + Lc) M :=
    ⟨by simp; omega, fun e he => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      have := ha.1; have := hb.1; have := hc.1
      rcases he with rfl | rfl | rfl <;> omega⟩
  have := ((h3.append ha).append hb).append hc
  simp only [swIn]
  exact this.mono (by omega) le_rfl

/-! ### Words of functions, finite sets and graphs -/

theorem toWord_fun_eq {α : Type*} [WordEncoding α] {n : ℕ} (f : Fin n → α) :
    toWord f = n :: ((List.ofFn f).map toWord).flatten := by
  show (List.ofFn f).length :: ((List.ofFn f).map toWord).flatten = _
  rw [List.length_ofFn]

theorem length_flatten_le {α : Type*} [WordEncoding α] (l : List α) {ℓ : ℕ}
    (h : ∀ a ∈ l, (toWord a).length ≤ ℓ) : ((l.map toWord).flatten).length ≤ l.length * ℓ := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.flatten_cons, List.length_append, List.length_cons]
    have h1 := h a (by simp)
    have h2 := ih (fun b hb => h b (by simp [hb]))
    nlinarith

theorem length_toWord_fun {α : Type*} [WordEncoding α] {n ℓ : ℕ} (f : Fin n → α)
    (h : ∀ i, (toWord (f i)).length ≤ ℓ) : (toWord f).length ≤ 1 + n * ℓ := by
  rw [toWord_fun_eq, List.length_cons]
  have := length_flatten_le (List.ofFn f) (ℓ := ℓ) (by
    intro a ha; obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha; exact h i)
  rw [List.length_ofFn] at this
  omega

theorem mem_toWord_fun {α : Type*} [WordEncoding α] {n : ℕ} (f : Fin n → α) {e : ℕ}
    (he : e ∈ toWord f) : e = n ∨ ∃ i, e ∈ toWord (f i) := by
  rw [toWord_fun_eq] at he
  rcases List.mem_cons.1 he with h | h
  · exact Or.inl h
  · simp only [List.mem_flatten, List.mem_map, List.mem_ofFn] at h
    obtain ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, h⟩ := h
    exact Or.inr ⟨i, h⟩

theorem length_frames_le {ws : List (List ℕ)} {ℓ : ℕ} (h : ∀ u ∈ ws, u.length ≤ ℓ) :
    (frames ws).length ≤ ws.length * (ℓ + 1) := by
  induction ws with
  | nil => simp [frames]
  | cons a ws ih =>
    have h1 := h a (by simp)
    have h2 := ih (fun u hu => h u (by simp [hu]))
    simp only [frames, List.map_cons, List.flatten_cons, List.length_append,
      List.length_cons] at h2 ⊢
    nlinarith

theorem length_toWord_finset {α : Type*} [WordEncoding α] (S : Finset α) {ℓ : ℕ}
    (h : ∀ a ∈ S, (toWord a).length ≤ ℓ) : (toWord S).length ≤ 1 + S.card * (ℓ + 1) := by
  change (toWord (Finset.words S)).length ≤ _
  rw [toWord_words, List.length_cons]
  have hw : ∀ u ∈ Finset.words S, u.length ≤ ℓ := by
    intro u hu
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 ((Finset.mem_sort _).1 hu)
    exact h a ha
  have hl : (Finset.words S).length ≤ S.card := by
    simp only [Finset.words, Finset.length_sort]; exact Finset.card_image_le
  have := length_frames_le hw
  have : (Finset.words S).length * (ℓ + 1) ≤ S.card * (ℓ + 1) := Nat.mul_le_mul_right _ hl
  omega

theorem small_finset_fin {n : ℕ} (S : Finset (Fin n)) (M : ℕ) : Small (toWord S) (2 * n + 1) M := by
  have hl : (toWord S).length ≤ 2 * n + 1 := by
    have := length_toWord_finset S (ℓ := 1) (fun a _ => by simp [word_simps])
    have hc : S.card ≤ n := by simpa using Finset.card_le_univ S
    omega
  refine ⟨hl, fun e he => ?_⟩
  rcases mem_toWord_finset S he with h | ⟨a, -, -, h⟩
  · omega
  · simp only [word_simps, List.mem_singleton] at h
    have := a.isLt; omega

theorem small_graph {n : ℕ} (H : SimpleGraph (Fin n)) (M : ℕ) :
    Small (toWord H) (1 + n * (2 * n + 1)) M := by
  classical
  change Small (toWord fun v : Fin n => Finset.univ.filter (H.Adj v)) _ M
  refine ⟨length_toWord_fun _ (fun i => (small_finset_fin _ M).1), fun e he => ?_⟩
  rcases mem_toWord_fun _ he with h | ⟨i, h⟩
  · nlinarith
  · have := (small_finset_fin _ M).2 e h
    have : 1 ≤ n := by have := i.isLt; omega
    nlinarith

/-- The word of a partial graph. -/
theorem small_pgraph {n M : ℕ} (H : PartialGraph (Fin n)) (hM : ∀ v, H.color v ≤ M) :
    Small (toWord H) (5 * (n + 1) ^ 2) M := by
  have hc : Small (toWord H.color) (1 + n) M := by
    refine ⟨by simpa using length_toWord_fun H.color (ℓ := 1) (fun i => by simp [word_simps]),
      fun e he => ?_⟩
    rcases mem_toWord_fun _ he with h | ⟨i, h⟩
    · omega
    · simp only [word_simps, List.mem_singleton] at h; have := hM i; omega
  have := (hc.append (small_graph H.edge M)).append (small_graph H.nonEdge M)
  show Small (toWord H.color ++ (toWord H.edge ++ toWord H.nonEdge)) _ M
  rw [← List.append_assoc]
  exact this.mono (by nlinarith) le_rfl

/-- The word of a list of words given as a family. -/
theorem small_words {n L M : ℕ} (f : Fin n → List ℕ) (h : ∀ i, Small (f i) L M) :
    Small (toWord (List.ofFn f)) (1 + n * (L + 1)) M := by
  have e : toWord (List.ofFn f) = toWord f := rfl
  rw [e]
  refine ⟨length_toWord_fun f (fun i => by
    rw [Lax185574Proofs.Words.toWord_listNat]; simp only [List.length_cons]; have := (h i).1; omega),
    fun e he => ?_⟩
  rcases mem_toWord_fun _ he with h1 | ⟨i, h1⟩
  · nlinarith
  · have hn : 1 ≤ n := by have := i.isLt; omega
    have : L + 1 ≤ n * (L + 1) := Nat.le_mul_of_pos_left _ hn
    rw [Lax185574Proofs.Words.toWord_listNat, List.mem_cons] at h1
    rcases h1 with h1 | h1
    · have := (h i).1; omega
    · have := (h i).2 e h1; omega

/-- The word of a distance matrix. -/
theorem small_dist {n : ℕ} (G : PartialGraph (Fin n)) (M : ℕ) :
    Small (toWord (Lax185574.DistanceMatrix.distMatrix G)) (1 + n * (n + 1)) M :=
  ⟨by rw [Lax185574Proofs.DistMatrix.length_toWord_distMatrix],
    fun e he => by have := Lax185574Proofs.DistMatrix.toWord_distMatrix_le G e he; nlinarith⟩

/-- The constant of the entries of a tree of arity one. -/
def treeCst (q : ℕ) : ℕ := 1 + q + nodeCst 1 q 1

theorem small_tree {n T M : ℕ} (H : PartialGraph (Fin n)) (q : ℕ) (a : Fin n)
    (hT : wordLength (tree H 1 q ![a]) ≤ T) (hM : ∀ v, H.color v ≤ M) :
    Small (toWord (tree H 1 q ![a])) (T + treeCst q) M := by
  refine ⟨by unfold wordLength at hT; omega, fun e he => ?_⟩
  unfold wordLength at hT
  have e1 : nodeCst 1 q (Nat.succ 0) = nodeCst 1 q 1 := rfl
  rcases tree_entry H 1 q ![a] he with h | h | ⟨v, rfl⟩
  · omega
  · unfold treeCst; rw [e1] at h; omega
  · have := hM v; omega

theorem small_family {n T M : ℕ} (H : PartialGraph (Fin n)) (q : ℕ)
    (hT : ∀ a, wordLength (tree H 1 q ![a]) ≤ T) (hM : ∀ v, H.color v ≤ M) :
    Small (toWord (family H 1 q)) (1 + n * (T + treeCst q)) M := by
  refine ⟨length_toWord_fun _ (fun i => (small_tree H q i (hT i) hM).1), fun e he => ?_⟩
  rcases mem_toWord_fun _ he with h | ⟨i, h⟩
  · have : 1 ≤ T + treeCst q := by unfold treeCst; omega
    nlinarith
  · have := (small_tree H q i (hT i) hM).2 e h
    have : T + treeCst q ≤ n * (T + treeCst q) :=
      Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (fun h0 => (h0 ▸ i).elim0))
    omega

/-! ### The calls of a script -/

theorem le_foldr_max {l : List ℕ} {x : ℕ} (h : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

theorem tree_le_treeMax {n : ℕ} (s : List (PartialGraph (Fin n))) (q : ℕ) {t : ℕ}
    (ht : t < s.length) (a : Fin n) : wordLength (tree (sAt s t) 1 q ![a]) ≤ treeMax s q := by
  unfold treeMax
  refine le_trans ?_ (le_foldr_max (List.mem_map.2 ⟨t, List.mem_range.2 ht, rfl⟩))
  exact Finset.le_sup (f := fun a : Fin n => wordLength (tree (sAt s t) 1 q ![a]))
    (Finset.mem_univ a)

theorem color_le_script {n : ℕ} (σ : Script n) {t : ℕ} (ht : t < σ.run.length) (v : Fin n) :
    (sAt σ.run t).color v ≤ maxEntry (toWord σ) := by
  have : sAt σ.run t ∈ σ.run := by
    simp only [sAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
    exact List.getElem_mem ht
  exact le_maxEntry (color_mem_script σ this v)

theorem step_le_script {n : ℕ} (σ : Script n) {t : ℕ} {st : Step} (h : σ.steps[t]? = some st) :
    ∀ e ∈ stepCode st, e ≤ maxEntry (toWord σ) := by
  intro e he
  apply le_maxEntry
  have hw : toWord σ = toWord σ.colors ++ toWord σ.steps := rfl
  rw [hw]
  apply List.mem_append_right
  show e ∈ σ.steps.length :: (σ.steps.map toWord).flatten
  simp only [List.mem_cons, List.mem_flatten, List.mem_map]
  exact Or.inr ⟨_, ⟨st, List.mem_of_getElem? h, rfl⟩, he⟩

/-- The constant of the sizes of the calls: the constants of the trees,
the fixed queries and answers, and the localization of the sentence. -/
noncomputable def kq (q : ℕ) (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  3 * treeCst q + 20 + fixW (toWord (loc q φ)) + fixW qM0 + fixW qR0 + fixW qE0 +
    fixW yM0 + fixW zR0 + fixW uE0

/-- The bound of the sizes of the calls. -/
noncomputable def callB (n T q : ℕ) (φ : Lax3.FirstOrder.FO 0) : ℕ :=
  2 * (n + 2) * (T + 6 * (n + 1) + kq q φ)

theorem callB_lin {n T q : ℕ} {φ : Lax3.FirstOrder.FO 0} {L : ℕ}
    (h : L ≤ 2 * (T + 6 * (n + 1) + kq q φ)) : L ≤ callB n T q φ := by
  unfold callB
  generalize T + 6 * (n + 1) + kq q φ = A at h ⊢
  nlinarith

theorem arith_res (n T c K a b : ℕ) (h : c + a + b + 20 ≤ K) :
    3 + 2 * (a + (5 * (n + 1) ^ 2 + (1 + n * (n + 1)) + 3 + (1 + n * (T + c))) + b) ≤
      2 * (n + 2) * (T + 6 * (n + 1) + K) := by
  nlinarith

theorem arith_res' (n T c K a b : ℕ) (h : c + a + b + 20 ≤ K) :
    a + (5 * (n + 1) ^ 2 + (1 + n * (n + 1)) + (1 + n * (T + c))) + b ≤
      2 * (n + 2) * (T + 6 * (n + 1) + K) := by
  nlinarith

theorem arith_jobs (n T c K a b : ℕ) (h : c + a + b + 20 ≤ K) :
    3 + 2 * ((1 + n * (T + c + 2 + 1)) + a + b) ≤ 2 * (n + 2) * (T + 6 * (n + 1) + K) := by
  nlinarith

theorem arith_jobs' (n T c K a b : ℕ) (h : c + a + b + 20 ≤ K) :
    (1 + n * (T + c + 1)) + a + b ≤ 2 * (n + 2) * (T + 6 * (n + 1) + K) := by
  nlinarith

/-- **Sizes of a call.** The query and the answer of a call of a script
are small for `callB`. -/
theorem small_call {n : ℕ} (σ : Script n) (q : ℕ) (φ : Lax3.FirstOrder.FO 0) {c : PCall n}
    (hc : c ∈ pcalls n σ.steps) :
    Small (callQ σ.run q φ c) (callB n (treeMax σ.run q) q φ) (maxEntry (toWord σ)) ∧
      Small (callY σ.run q φ c) (callB n (treeMax σ.run q) q φ) (maxEntry (toWord σ)) := by
  set s := σ.run
  set T := treeMax s q
  set M := maxEntry (toWord σ)
  have hl : s.length = σ.steps.length + 1 := by simp [s, Script.run]
  have hcol : ∀ t, t < s.length → ∀ v, (sAt s t).color v ≤ M := fun t ht v => color_le_script σ ht v
  have hfrom := fromStep_pcalls hc
  have hM := small_fix qM0 M
  have hR := small_fix qR0 M
  have hE := small_fix qE0 M
  have hM' := small_fix yM0 M
  have hR' := small_fix zR0 M
  have hE' := small_fix uE0 M
  have hkq : treeCst q + fixW (toWord (loc q φ)) + fixW qM0 + fixW qR0 + fixW qE0 + fixW yM0 +
      fixW zR0 + fixW uE0 + 20 ≤ kq q φ := by unfold kq; omega
  cases c with
  | merge t P Q =>
    simp only [FromStep] at hfrom
    have ht : t < σ.steps.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hfrom; simp at hfrom
    have hPQ := step_le_script σ hfrom
    simp only [stepCode] at hPQ
    have hP : P ≤ M := hPQ P (by simp)
    have hQ : Q ≤ M := hPQ Q (by simp)
    by_cases hpq : P = Q
    · simp only [callQ, callY, callQM, callQR, callQE, callYM, callYR, callYE, hpq, if_true]
      exact ⟨(small_swIn hM hR hE).mono (callB_lin (by omega)) le_rfl,
        ((hM'.append hR').append hE').mono (callB_lin (by omega)) le_rfl⟩
    · have hm : merge (sAt s t) P Q = sAt s (t + 1) := by
        rw [sAt_run_succ σ ht]
        rw [List.getElem?_eq_getElem ht] at hfrom
        simp only [Option.some.injEq] at hfrom
        rw [hfrom]; rfl
      have hqm : Small (toWord (mjobs (sAt s t) q P Q)) (1 + n * (T + treeCst q + 2 + 1)) M := by
        refine small_words _ (fun a => ?_)
        have hq1 := small_tree (T := T) (sAt s t) q a (tree_le_treeMax s q (by omega) a)
          (hcol t (by omega))
        have := hq1.append ((small_nat hP).append (small_nat hQ))
        exact this.mono (by omega) le_rfl
      have hym : Small (toWord (mans (sAt s t) q P Q)) (1 + n * (T + treeCst q + 1)) M :=
        small_words _ (fun a => small_tree (T := T) (merge (sAt s t) P Q) q a
          (by rw [hm]; exact tree_le_treeMax s q (by omega) a) (by rw [hm]; exact hcol _ (by omega)))
      simp only [callQ, callY, callQM, callQR, callQE, callYM, callYR, callYE, hpq, if_false]
      refine ⟨(small_swIn hqm hR hE).mono ?_ le_rfl, ((hym.append hR').append hE').mono ?_ le_rfl⟩
      · unfold callB
        exact arith_jobs n T (treeCst q) (kq q φ) (fixW qR0) (fixW qE0) (by omega)
      · unfold callB
        exact arith_jobs' n T (treeCst q) (kq q φ) (fixW zR0) (fixW uE0) (by omega)
  | resolve t sg P Q =>
    simp only [FromStep] at hfrom
    have ht : t < σ.steps.length := by
      by_contra h; rw [List.getElem?_eq_none (by omega)] at hfrom; simp at hfrom
    have hPQ := step_le_script σ hfrom
    have hP : P ≤ M := hPQ P (by cases sg <;> simp [stepCode])
    have hQ : Q ≤ M := hPQ Q (by cases sg <;> simp [stepCode])
    have hrs : resolveBy (sAt s t) sg P Q = sAt s (t + 1) := by
      rw [sAt_run_succ σ ht]
      rw [List.getElem?_eq_getElem ht] at hfrom
      simp only [Option.some.injEq] at hfrom
      rw [hfrom]; cases sg <;> rfl
    have hg := small_pgraph (sAt s t) (hcol t (by omega))
    have hf := small_family (T := T) (sAt s t) q (fun a => tree_le_treeMax s q (by omega) a)
      (hcol t (by omega))
    have hg' := small_pgraph (resolveBy (sAt s t) sg P Q) (by rw [hrs]; exact hcol _ (by omega))
    have hf' := small_family (T := T) (resolveBy (sAt s t) sg P Q) q
      (fun a => by rw [hrs]; exact tree_le_treeMax s q (by omega) a)
      (by rw [hrs]; exact hcol _ (by omega))
    have hqr : Small (toWord (sAt s t, Lax185574.DistanceMatrix.distMatrix (sAt s t), P, Q, sg,
        family (sAt s t) 1 q))
        (5 * (n + 1) ^ 2 + (1 + n * (n + 1)) + 3 + (1 + n * (T + treeCst q))) M := by
      have := hg.append ((small_dist (sAt s t) M).append ((small_nat hP).append
        ((small_nat hQ).append ((small_bool sg M).append hf))))
      exact this.mono (by omega) le_rfl
    have hyr : Small (toWord (resolveBy (sAt s t) sg P Q,
        Lax185574.DistanceMatrix.distMatrix (resolveBy (sAt s t) sg P Q),
        family (resolveBy (sAt s t) sg P Q) 1 q))
        (5 * (n + 1) ^ 2 + (1 + n * (n + 1)) + (1 + n * (T + treeCst q))) M :=
      (hg'.append ((small_dist _ M).append hf')).mono (by omega) le_rfl
    simp only [callQ, callY, callQM, callQR, callQE, callYM, callYR, callYE]
    refine ⟨(small_swIn hM hqr hE).mono ?_ le_rfl, ((hM'.append hyr).append hE').mono ?_ le_rfl⟩
    · unfold callB
      exact arith_res n T (treeCst q) (kq q φ) (fixW qM0) (fixW qE0) (by omega)
    · unfold callB
      exact arith_res' n T (treeCst q) (kq q φ) (fixW yM0) (fixW uE0) (by omega)
  | eval a =>
    have ht : s.length - 1 < s.length := by omega
    have he1 := small_tree (T := T) (sAt s (s.length - 1)) q a (tree_le_treeMax s q ht a)
      (hcol _ ht)
    have he := he1.append (small_fix (toWord (loc q φ)) M)
    simp only [callQ, callY, callQM, callQR, callQE, callYM, callYR, callYE]
    exact ⟨(small_swIn hM hR he).mono (callB_lin (by omega)) le_rfl,
      ((hM'.append hR').append (small_bool _ M)).mono (callB_lin (by omega)) le_rfl⟩

end Lax185574Proofs.MC
