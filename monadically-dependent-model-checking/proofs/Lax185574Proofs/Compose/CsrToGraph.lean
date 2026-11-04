import Lax185574.DefinableSequences
import Lax185574Proofs.Compose.GraphLength
import Lax185574Proofs.Words.Computes
import Lax185574Proofs.LegacyInputs

/-!
From the compressed sparse row form of a graph to the word of the graph.

The compressed sparse row word of a graph on `n` vertices is `n`, the
number `E` of edges, the `n + 1` offsets and the `2E` targets. The block
of a vertex may list a neighbor several times. The word of the graph
(`Lax185574.WordEncoding`) lists, for each vertex, the number of its
neighbors and then the words `1, u` of its neighbors `u` in increasing
order. The command `csrToGraph` reads the offsets and targets into
arrays, and then for every vertex marks its targets in an array of
size `n`, counts the marks and writes the marked vertices in
increasing order. It takes time `O(n² + |g|)`.
-/

namespace Lax185574Proofs.Compose

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax808846Proofs.Simulation
open Lax185574.WordEncoding Lax271696.GraphEncoding

/-! ### The words of a set of vertices -/

theorem single_le {a b : ℕ} (h : a ≤ b) : ([a] : List ℕ) ≤ [b] := by
  rcases Nat.lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (List.Lex.rel h)
  · exact le_rfl

/-- The words of a set of vertices are the singletons of its elements,
in increasing order. -/
theorem words_fin {n : ℕ} (S : Finset (Fin n)) :
    Finset.words S = ((List.range n).filter (fun z => ∃ h : z < n, (⟨z, h⟩ : Fin n) ∈ S)).map
      (fun z => [z]) := by
  classical
  unfold Finset.words
  apply List.Perm.eq_of_pairwise' (r := (· ≤ ·)) (Finset.pairwise_sort _ _)
  · rw [List.pairwise_map]
    exact ((List.pairwise_lt_range).filter _).imp fun h => single_le (le_of_lt h)
  · apply List.perm_of_nodup_nodup_toFinset_eq (Finset.sort_nodup _ _)
    · refine (List.Nodup.filter _ List.nodup_range).map ?_
      intro a b h; simpa using h
    · rw [Finset.sort_toFinset]
      ext u
      simp only [Finset.mem_image, List.mem_toFinset, List.mem_map, List.mem_filter, List.mem_range]
      constructor
      · rintro ⟨v, hv, rfl⟩
        refine ⟨v.val, ⟨v.isLt, ?_⟩, rfl⟩
        simp only [decide_eq_true_eq]
        exact ⟨v.isLt, hv⟩
      · rintro ⟨z, ⟨hz, hS⟩, rfl⟩
        simp only [decide_eq_true_eq] at hS
        obtain ⟨h, hS⟩ := hS
        exact ⟨⟨z, h⟩, hS, rfl⟩

/-- The block written for a vertex whose neighbors are the numbers
satisfying `P`. -/
def markBlock (n : ℕ) (P : ℕ → Prop) [DecidablePred P] : List ℕ :=
  ((List.range n).filter P).length :: ((List.range n).filter P).flatMap fun z => [1, z]

theorem setBlock_fin {n : ℕ} (S : Finset (Fin n)) (P : ℕ → Prop) [DecidablePred P]
    (hP : ∀ z, P z ↔ ∃ h : z < n, (⟨z, h⟩ : Fin n) ∈ S) :
    blk (setBlock S) = markBlock n P := by
  classical
  have hw : Finset.words S = ((List.range n).filter P).map (fun z => [z]) := by
    rw [words_fin]
    congr 1
    exact List.filter_congr fun z _ => by simp [hP z]
  have hs : setBlock S = ((List.range n).filter P).flatMap fun z => [1, z] := by
    rw [setBlock, hw, List.map_map, List.flatMap]
    congr 1
  have hl : (setBlock S).length = 2 * ((List.range n).filter P).length := by
    rw [setBlock_length, hw, List.length_map]
  rw [blk, hl, hs, markBlock, Nat.mul_div_cancel_left _ (by norm_num)]

/-! ### The compressed sparse row word -/

/-- A compressed sparse row word consists of its header, its offsets
and its targets. -/
theorem csr_shape {g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} (h : EncodesGraph g n G) :
    g = n :: edgeCount g :: (arrOf (n + 1) (offset g) ++ arrOf (2 * edgeCount g) (target g)) := by
  have hlen := h.length_eq
  have hn := h.vertexCount_eq
  apply List.ext_getElem
  · simp [hlen]; omega
  intro k h₁ h₂
  have hk : g[k] = g.getD k 0 := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁]
  rw [hk]
  rcases k with _ | _ | k
  · simp only [List.getElem_cons_zero]; rw [← hn]; rfl
  · simp only [List.getElem_cons_succ, List.getElem_cons_zero]; rfl
  · simp only [List.getElem_cons_succ]
    by_cases hkn : k < n + 1
    · rw [List.getElem_append_left (by simpa using hkn)]
      simp only [arrOf, List.getElem_map, List.getElem_range, offset]
      congr 1; omega
    · rw [List.getElem_append_right (by simpa using hkn)]
      simp only [arrOf, List.getElem_map, List.getElem_range, List.length_map, List.length_range,
        target, hn]
      congr 1; omega

/-! ### Reading into an array -/

/-- Read `cnt` numbers into the array `a`. -/
def readArr (a : String) : Com :=
  .seq (.assign "i" (.lit 0)) (.while (.lt (.var "i") (.var "cnt"))
    (.seq (.read "v") (.seq (.store a (.var "i") (.var "v")) (.assign "i" (.add (.var "i") (.lit 1))))))

theorem readArr_spec {B : ℕ} (a : String) (l rest : List ℕ) (hlB : l.length < B)
    (hv : ∀ v ∈ l, v < B) {σ : Env} (hc : σ.vars "cnt" = l.length)
    (hinp : σ.inp = l ++ rest) (ha : σ.arrs a = arrOf l.length (fun _ => 0)) :
    ∃ σ', Run B (readArr a) σ σ' (12 * l.length + 6) ∧ σ'.inp = rest ∧ σ'.arrs a = l ∧
      (∀ y, y ∉ (readArr a).wvars → σ'.vars y = σ.vars y) ∧
      (∀ b, b ∉ (readArr a).warrs → σ'.arrs b = σ.arrs b) ∧ σ'.out = σ.out := by
  let I : Env → Prop := fun τ => τ.vars "i" ≤ l.length ∧ τ.vars "cnt" = l.length ∧
    τ.inp = l.drop (τ.vars "i") ++ rest ∧
    τ.arrs a = arrOf l.length (fun k => if k < τ.vars "i" then l.getD k 0 else 0)
  have hbody : Spec B (fun τ => I τ ∧ τ.vars "i" < l.length)
      (.seq (.read "v") (.seq (.store a (.var "i") (.var "v")) (.assign "i" (.add (.var "i") (.lit 1)))))
      (fun τ τ' => I τ' ∧ τ'.vars "i" = τ.vars "i" + 1) 8 := by
    rintro τ ⟨⟨hi, hcnt, hinp, ha⟩, hlt⟩
    have hinp' : τ.inp = l[τ.vars "i"] :: (l.drop (τ.vars "i" + 1) ++ rest) := by
      rw [hinp, List.drop_eq_getElem_cons hlt]; rfl
    have hlv : l[τ.vars "i"] < B := hv _ (List.getElem_mem _)
    refine ⟨_, (Run.seq (Run.read hinp') (Run.seq (Run.store (idx := τ.vars "i")
      (v := l[τ.vars "i"]) ?_ ?_ ?_) (Run.assign (v := τ.vars "i" + 1) ?_))).mono (by simp), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp; omega
    · simp; omega
    · simp [ha]; omega
    · simp; omega
    · simp; omega
    · simp [hcnt]
    · simp
    · simp only [vars_setVar, if_true, arrs_setVar, arrs_setArr, inp_setVar]
      simp only [if_pos rfl, ha, set_arrOf]
      apply arrOf_congr
      intro k hk
      by_cases hk' : k = τ.vars "i"
      · subst hk'; simp [List.getD_eq_getElem?_getD, hlt]
      · simp only [hk', if_false]
        by_cases hki : k < τ.vars "i"
        · simp [hki, show k < τ.vars "i" + 1 by omega]
        · simp [hki, show ¬ k < τ.vars "i" + 1 by omega]
    · simp
  have h := Spec.forRangeZero (B := B) "i" "cnt" I l.length 8 hlB (fun _ h => h.1) (fun _ h => h.2.1) hbody
  have h0 : I (σ.setVar "i" 0) := by
    refine ⟨by simp, by simp [hc], by simp [hinp], ?_⟩
    simp [ha]
  obtain ⟨σ', hr, ⟨-, -, hinp', ha'⟩, hi'⟩ := h.run h0
  refine ⟨σ', hr, by rw [hi'] at hinp'; simpa using hinp', ?_, fun y hy => hr.frame_var y hy,
    fun b hb => hr.frame_arr b hb, hr.out_eq (by simp [readArr, Com.NoWrite])⟩
  rw [ha', hi']
  refine List.ext_getElem (by simp) fun k h₁ h₂ => ?_
  simp only [arrOf, List.getElem_map, List.getElem_range]
  simp at h₁
  simp [h₁, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h₁]

/-! ### The work for one vertex -/

/-- Clear the mark array. -/
def clearMk : Com :=
  .seq (.assign "z" (.lit 0)) (.while (.lt (.var "z") (.var "n"))
    (.seq (.store "mk" (.var "z") (.lit 0)) (.assign "z" (.add (.var "z") (.lit 1)))))

/-- Mark the targets of vertex `u`. -/
def markMk : Com :=
  .seq (.assign "j" (.get "of" (.var "u")))
    (.seq (.assign "hi" (.get "of" (.add (.var "u") (.lit 1))))
      (.while (.lt (.var "j") (.var "hi"))
        (.seq (.store "mk" (.get "tg" (.var "j")) (.lit 1)) (.assign "j" (.add (.var "j") (.lit 1))))))

/-- Count the marks into `d`. -/
def countMk : Com :=
  .seq (.assign "d" (.lit 0)) (.seq (.assign "z" (.lit 0)) (.while (.lt (.var "z") (.var "n"))
    (.seq (.assign "d" (.add (.var "d") (.get "mk" (.var "z")))) (.assign "z" (.add (.var "z") (.lit 1))))))

/-- Write `1, z` for every marked `z`, in increasing order. -/
def emitMk : Com :=
  .seq (.assign "z" (.lit 0)) (.while (.lt (.var "z") (.var "n"))
    (.seq (.ite (.eq (.get "mk" (.var "z")) (.lit 1)) (.seq (.write (.lit 1)) (.write (.var "z"))) .skip)
      (.assign "z" (.add (.var "z") (.lit 1)))))

/-- The block of vertex `u`. -/
def vertexBody : Com :=
  .seq clearMk (.seq markMk (.seq countMk (.seq (.write (.var "d"))
    (.seq emitMk (.assign "u" (.add (.var "u") (.lit 1)))))))

/-- The indicator of a predicate. -/
noncomputable def ind (P : ℕ → Prop) : ℕ → ℕ := open Classical in fun z => if P z then 1 else 0

theorem clearMk_spec {B N : ℕ} (hN : N < B) (f : ℕ → ℕ) {σ : Env} (hn : σ.vars "n" = N)
    (hmk : σ.arrs "mk" = arrOf N f) :
    ∃ σ', Run B clearMk σ σ' (11 * N + 6) ∧ σ'.arrs "mk" = arrOf N (fun _ => 0) ∧
      (∀ y, y ∉ clearMk.wvars → σ'.vars y = σ.vars y) ∧
      (∀ b, b ∉ clearMk.warrs → σ'.arrs b = σ.arrs b) ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp := by
  let I : Env → Prop := fun τ => τ.vars "z" ≤ N ∧ τ.vars "n" = N ∧
    τ.arrs "mk" = arrOf N (fun k => if k < τ.vars "z" then 0 else f k)
  have hbody : Spec B (fun τ => I τ ∧ τ.vars "z" < N)
      (.seq (.store "mk" (.var "z") (.lit 0)) (.assign "z" (.add (.var "z") (.lit 1))))
      (fun τ τ' => I τ' ∧ τ'.vars "z" = τ.vars "z" + 1) 7 := by
    rintro τ ⟨⟨hz, hn, hm⟩, hlt⟩
    refine ⟨_, (Run.seq (Run.store (idx := τ.vars "z") (v := 0) ?_ ?_ ?_)
      (Run.assign (v := τ.vars "z" + 1) ?_)).mono (by simp), ⟨?_, ?_, ?_⟩, ?_⟩
    · simp; omega
    · simp; omega
    · simp [hm]; omega
    · simp; omega
    · simp; omega
    · simp [hn]
    · simp only [vars_setVar, if_true, arrs_setVar, arrs_setArr, if_pos rfl, hm, set_arrOf]
      apply arrOf_congr
      intro k hk
      by_cases hk' : k = τ.vars "z"
      · simp [hk']
      · by_cases hki : k < τ.vars "z"
        · simp [hk', hki, show k < τ.vars "z" + 1 by omega]
        · simp [hk', hki, show ¬ k < τ.vars "z" + 1 by omega]
    · simp
  have h := Spec.forRangeZero (B := B) "z" "n" I N 7 hN (fun _ h => h.1) (fun _ h => h.2.1) hbody
  have h0 : I (σ.setVar "z" 0) := ⟨by simp, by simp [hn], by simp [hmk]⟩
  obtain ⟨σ', hr, ⟨-, -, hm'⟩, hz'⟩ := h.run h0
  refine ⟨σ', hr.mono (by omega), ?_, fun y hy => hr.frame_var y hy, fun b hb => hr.frame_arr b hb,
    hr.out_eq (by decide), hr.frame_inp (by decide)⟩
  rw [hm', hz']
  exact arrOf_congr fun k hk => by simp [hk]

/-- The targets in the block of `u`. -/
def Marked (o t : ℕ → ℕ) (u z : ℕ) : Prop := ∃ j, o u ≤ j ∧ j < o (u + 1) ∧ t j = z

theorem markMk_spec {B N D u : ℕ} {o t : ℕ → ℕ} (hNB : N + 1 < B) (hDB : D < B)
    (hu : u < N) (hmono : o u ≤ o (u + 1)) (hoD : o (u + 1) ≤ D) (ht : ∀ j < D, t j < N)
    {σ : Env} (hvu : σ.vars "u" = u) (hof : σ.arrs "of" = arrOf (N + 1) o)
    (htg : σ.arrs "tg" = arrOf D t) (hmk : σ.arrs "mk" = arrOf N (fun _ => 0)) :
    ∃ σ', Run B markMk σ σ' (12 * (o (u + 1) - o u) + 12) ∧
      σ'.arrs "mk" = arrOf N (ind (Marked o t u)) ∧
      (∀ y, y ∉ markMk.wvars → σ'.vars y = σ.vars y) ∧
      (∀ b, b ∉ markMk.warrs → σ'.arrs b = σ.arrs b) ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp := by
  classical
  have hou : o u < B := by omega
  have hou1 : o (u + 1) < B := by omega
  let I : Env → Prop := fun τ => o u ≤ τ.vars "j" ∧ τ.vars "j" ≤ o (u + 1) ∧
    τ.vars "hi" = o (u + 1) ∧ τ.arrs "tg" = arrOf D t ∧
    τ.arrs "mk" = arrOf N (fun z => if ∃ j, o u ≤ j ∧ j < τ.vars "j" ∧ t j = z then 1 else 0)
  have hbody : Spec B (fun τ => I τ ∧ τ.vars "j" < o (u + 1))
      (.seq (.store "mk" (.get "tg" (.var "j")) (.lit 1)) (.assign "j" (.add (.var "j") (.lit 1))))
      (fun τ τ' => I τ' ∧ τ'.vars "j" = τ.vars "j" + 1) 8 := by
    rintro τ ⟨⟨hj1, hj2, hhi, htg', hm⟩, hlt⟩
    have hjD : τ.vars "j" < D := by omega
    have htj := ht _ hjD
    refine ⟨_, (Run.seq (Run.store (idx := t (τ.vars "j")) (v := 1) ?_ ?_ ?_)
      (Run.assign (v := τ.vars "j" + 1) ?_)).mono (by simp), ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [evalB_get_iff, evalB_var_iff, htg']
      exact ⟨_, ⟨rfl, by omega⟩, getElem?_arrOf _ hjD, by omega⟩
    · simp; omega
    · simp [hm]; omega
    · simp; omega
    · simp; omega
    · simp; omega
    · simp [hhi]
    · simp [htg']
    · simp only [vars_setVar, if_true, arrs_setVar, arrs_setArr, if_pos rfl, hm, set_arrOf]
      apply arrOf_congr
      intro k hk
      by_cases hk' : k = t (τ.vars "j")
      · simp only [hk', if_true]
        rw [if_pos ⟨τ.vars "j", hj1, by omega, rfl⟩]
      · simp only [hk', if_false]
        congr 1
        apply propext
        constructor
        · rintro ⟨j, h1, h2, h3⟩; exact ⟨j, h1, by omega, h3⟩
        · rintro ⟨j, h1, h2, h3⟩
          refine ⟨j, h1, ?_, h3⟩
          rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp h2) with h | h
          · exact h
          · subst h; exact absurd h3.symm hk'
    · simp
  have h := Spec.forRange (B := B) "j" "hi" I (o (u + 1)) 8 (12 * (o (u + 1) - o u) + 4)
    (fun _ h => by have := h.2.1; omega) (fun _ h => by rw [h.2.2.1]; omega) (fun _ h => h.2.2.1)
    (fun _ h => h.2.1) hbody (P := I) (fun _ h => h) (fun τ h => by have := h.1; omega)
  set σ₁ := σ.setVar "j" (o u)
  set σ₂ := σ₁.setVar "hi" (o (u + 1))
  have h0 : I σ₂ := by
    refine ⟨by simp [σ₂, σ₁], by simp [σ₂, σ₁]; omega, by simp [σ₂], by simp [σ₂, σ₁, htg], ?_⟩
    simp only [σ₂, σ₁, arrs_setVar, hmk, vars_setVar]
    simp only [show ("j" : String) = "hi" ↔ False by decide, if_false, if_true]
    exact arrOf_congr fun k _ => by
      rw [if_neg]; rintro ⟨j, h1, h2, -⟩; omega
  obtain ⟨σ', hr, ⟨-, -, -, -, hm'⟩, hj'⟩ := h.run h0
  have r₁ : Run B (.assign "j" (.get "of" (.var "u"))) σ σ₁ 3 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_get_iff, evalB_var_iff, hof, hvu]
    exact ⟨u, ⟨rfl, by omega⟩, getElem?_arrOf _ (by omega), hou⟩
  have r₂ : Run B (.assign "hi" (.get "of" (.add (.var "u") (.lit 1)))) σ₁ σ₂ 5 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_get_iff, evalB_bin_iff, evalB_var_iff, evalB_lit_iff, σ₁, arrs_setVar, hof,
      vars_setVar]
    simp only [show ("u" : String) = "j" ↔ False by decide, if_false, hvu]
    exact ⟨u + 1, ⟨u, 1, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩,
      getElem?_arrOf _ (by omega), hou1⟩
  have hrun : Run B markMk σ σ' (12 * (o (u + 1) - o u) + 12) :=
    (r₁.seq (r₂.seq hr)).mono (by omega)
  refine ⟨σ', hrun, ?_, fun y hy => hrun.frame_var y hy, fun b hb => hrun.frame_arr b hb,
    hrun.out_eq (by decide), hrun.frame_inp (by decide)⟩
  rw [hm', hj']
  rfl

theorem ind_le_one (P : ℕ → Prop) (z : ℕ) : ind P z ≤ 1 := by
  classical
  unfold ind; split_ifs <;> simp

theorem countMk_spec {B N : ℕ} (hN : N + 1 < B) (P : ℕ → Prop) [DecidablePred P] {σ : Env}
    (hn : σ.vars "n" = N) (hmk : σ.arrs "mk" = arrOf N (ind P)) :
    ∃ σ', Run B countMk σ σ' (13 * N + 10) ∧ σ'.vars "d" = ((List.range N).filter P).length ∧
      (∀ y, y ∉ countMk.wvars → σ'.vars y = σ.vars y) ∧
      (∀ b, b ∉ countMk.warrs → σ'.arrs b = σ.arrs b) ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp := by
  let I : Env → Prop := fun τ => τ.vars "z" ≤ N ∧ τ.vars "n" = N ∧ τ.arrs "mk" = arrOf N (ind P) ∧
    τ.vars "d" = ((List.range (τ.vars "z")).filter P).length
  have hcnt : ∀ z, ((List.range z).filter P).length ≤ z := fun z => by
    have := List.length_filter_le P (List.range z); simpa using this
  have hbody : Spec B (fun τ => I τ ∧ τ.vars "z" < N)
      (.seq (.assign "d" (.add (.var "d") (.get "mk" (.var "z")))) (.assign "z" (.add (.var "z") (.lit 1))))
      (fun τ τ' => I τ' ∧ τ'.vars "z" = τ.vars "z" + 1) 9 := by
    rintro τ ⟨⟨hz, hn, hm, hd⟩, hlt⟩
    have hdz := hcnt (τ.vars "z")
    have hi1 := ind_le_one P (τ.vars "z")
    refine ⟨_, (Run.seq (Run.assign (v := τ.vars "d" + ind P (τ.vars "z")) ?_)
      (Run.assign (v := τ.vars "z" + 1) ?_)).mono (by simp), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
    · simp only [evalB_bin_iff, evalB_var_iff, evalB_get_iff, hm]
      exact ⟨_, _, ⟨rfl, by omega⟩, ⟨_, ⟨rfl, by omega⟩, getElem?_arrOf _ hlt, by omega⟩, rfl,
        by omega⟩
    · simp; omega
    · simp; omega
    · simp [hn]
    · simp [hm]
    · simp only [vars_setVar, if_true]
      simp only [show ("d" : String) = "z" ↔ False by decide, if_false, hd]
      rw [List.range_succ, List.filter_append]
      unfold ind
      split_ifs with hP <;> simp [hP]
    · simp
  have h := Spec.forRangeZero (B := B) "z" "n" I N 9 (by omega) (fun _ h => h.1) (fun _ h => h.2.1) hbody
  set σ₁ := σ.setVar "d" 0
  have h0 : I (σ₁.setVar "z" 0) := ⟨by simp, by simp [σ₁, hn], by simp [σ₁, hmk], by simp [σ₁]⟩
  obtain ⟨σ', hr, ⟨-, -, -, hd'⟩, hz'⟩ := h.run h0
  have hrun : Run B countMk σ σ' (13 * N + 10) :=
    ((Run.assign (v := 0) (by simp; omega)).seq hr).mono (by simp; omega)
  refine ⟨σ', hrun, by rw [hd', hz'], fun y hy => hrun.frame_var y hy,
    fun b hb => hrun.frame_arr b hb, hrun.out_eq (by decide), hrun.frame_inp (by decide)⟩

theorem emitMk_spec {B N : ℕ} (hN : N + 1 < B) (P : ℕ → Prop) [DecidablePred P] {σ : Env}
    (hn : σ.vars "n" = N) (hmk : σ.arrs "mk" = arrOf N (ind P)) :
    ∃ σ', Run B emitMk σ σ' (17 * N + 6) ∧
      σ'.out = σ.out ++ ((List.range N).filter P).flatMap (fun z => [1, z]) ∧
      (∀ y, y ∉ emitMk.wvars → σ'.vars y = σ.vars y) ∧
      (∀ b, b ∉ emitMk.warrs → σ'.arrs b = σ.arrs b) ∧ σ'.inp = σ.inp := by
  let I : Env → Prop := fun τ => τ.vars "z" ≤ N ∧ τ.vars "n" = N ∧ τ.arrs "mk" = arrOf N (ind P) ∧
    τ.out = σ.out ++ ((List.range (τ.vars "z")).filter P).flatMap (fun z => [1, z])
  have hbody : Spec B (fun τ => I τ ∧ τ.vars "z" < N)
      (.seq (.ite (.eq (.get "mk" (.var "z")) (.lit 1)) (.seq (.write (.lit 1)) (.write (.var "z"))) .skip)
        (.assign "z" (.add (.var "z") (.lit 1))))
      (fun τ τ' => I τ' ∧ τ'.vars "z" = τ.vars "z" + 1) 13 := by
    rintro τ ⟨⟨hz, hn, hm, hout⟩, hlt⟩
    have hget : (Expr.get "mk" (.var "z")).evalB B τ = some (ind P (τ.vars "z")) := by
      simp only [evalB_get_iff, evalB_var_iff, hm]
      exact ⟨_, ⟨rfl, by omega⟩, getElem?_arrOf _ hlt, by have := ind_le_one P (τ.vars "z"); omega⟩
    have hc := evalB_condEq (B := B) (f := .lit 1) hget (evalB_lit (n := 1) (by omega))
    by_cases hP : P (τ.vars "z")
    · have hi : ind P (τ.vars "z") = 1 := by simp [ind, hP]
      rw [hi] at hc
      refine ⟨_, (Run.seq (Run.ite_true (by simpa using hc) (Run.seq (Run.write (v := 1) ?_)
        (Run.write (v := τ.vars "z") ?_))) (Run.assign (v := τ.vars "z" + 1) ?_)).mono (by simp),
        ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · simp; omega
      · simp; omega
      · simp; omega
      · simp; omega
      · simp [hn]
      · simp [hm]
      · simp only [vars_setVar, if_true, out_setVar]
        rw [hout, List.range_succ, List.filter_append, List.flatMap_append]
        simp [hP]
      · simp
    · have hi : ind P (τ.vars "z") = 0 := by simp [ind, hP]
      rw [hi] at hc
      refine ⟨_, (Run.seq (Run.ite_false (by simpa using hc) Run.skip)
        (Run.assign (v := τ.vars "z" + 1) ?_)).mono (by simp), ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · simp; omega
      · simp; omega
      · simp [hn]
      · simp [hm]
      · simp only [vars_setVar, if_true, out_setVar]
        rw [hout, List.range_succ, List.filter_append, List.flatMap_append]
        simp [hP]
      · simp
  have h := Spec.forRangeZero (B := B) "z" "n" I N 13 (by omega) (fun _ h => h.1) (fun _ h => h.2.1) hbody
  have h0 : I (σ.setVar "z" 0) := ⟨by simp, by simp [hn], by simp [hmk], by simp⟩
  obtain ⟨σ', hr, ⟨-, -, -, hout'⟩, hz'⟩ := h.run h0
  refine ⟨σ', hr.mono (by omega), by rw [hout', hz'], fun y hy => hr.frame_var y hy,
    fun b hb => hr.frame_arr b hb, hr.frame_inp (by decide)⟩

open Classical in
theorem vertexBody_spec {B N D u : ℕ} {o t : ℕ → ℕ} (hNB : N + 1 < B) (hDB : D < B)
    (hu : u < N) (hmono : o u ≤ o (u + 1)) (hoD : o (u + 1) ≤ D) (ht : ∀ j < D, t j < N)
    {σ : Env} (hn : σ.vars "n" = N) (hvu : σ.vars "u" = u) (hof : σ.arrs "of" = arrOf (N + 1) o)
    (htg : σ.arrs "tg" = arrOf D t) (f : ℕ → ℕ) (hmk : σ.arrs "mk" = arrOf N f) :
    ∃ σ', Run B vertexBody σ σ' (41 * N + 12 * (o (u + 1) - o u) + 40) ∧
      σ'.out = σ.out ++ markBlock N (Marked o t u) ∧ σ'.vars "n" = N ∧ σ'.vars "u" = u + 1 ∧
      σ'.arrs "of" = arrOf (N + 1) o ∧ σ'.arrs "tg" = arrOf D t ∧
      σ'.arrs "mk" = arrOf N (ind (Marked o t u)) := by
  obtain ⟨σ₁, r₁, hm₁, hv₁, ha₁, ho₁, -⟩ := clearMk_spec (B := B) (by omega) f hn hmk
  have hn₁ : σ₁.vars "n" = N := by rw [hv₁ "n" (by decide), hn]
  have hu₁ : σ₁.vars "u" = u := by rw [hv₁ "u" (by decide), hvu]
  have hof₁ : σ₁.arrs "of" = arrOf (N + 1) o := by rw [ha₁ "of" (by decide), hof]
  have htg₁ : σ₁.arrs "tg" = arrOf D t := by rw [ha₁ "tg" (by decide), htg]
  obtain ⟨σ₂, r₂, hm₂, hv₂, ha₂, ho₂, -⟩ :=
    markMk_spec hNB hDB hu hmono hoD ht hu₁ hof₁ htg₁ hm₁
  have hn₂ : σ₂.vars "n" = N := by rw [hv₂ "n" (by decide), hn₁]
  have hu₂ : σ₂.vars "u" = u := by rw [hv₂ "u" (by decide), hu₁]
  have hof₂ : σ₂.arrs "of" = arrOf (N + 1) o := by rw [ha₂ "of" (by decide), hof₁]
  have htg₂ : σ₂.arrs "tg" = arrOf D t := by rw [ha₂ "tg" (by decide), htg₁]
  obtain ⟨σ₃, r₃, hd₃, hv₃, ha₃, ho₃, -⟩ := countMk_spec hNB (Marked o t u) hn₂ hm₂
  have hn₃ : σ₃.vars "n" = N := by rw [hv₃ "n" (by decide), hn₂]
  have hu₃ : σ₃.vars "u" = u := by rw [hv₃ "u" (by decide), hu₂]
  have hd3B : σ₃.vars "d" < B := by
    have := List.length_filter_le (Marked o t u) (List.range N); simp at this; omega
  set σ₄ : Env := { σ₃ with out := σ₃.out ++ [σ₃.vars "d"] }
  have r₄ : Run B (.write (.var "d")) σ₃ σ₄ 2 := (Run.write (by simp; omega)).mono (by simp)
  obtain ⟨σ₅, r₅, ho₅, hv₅, ha₅, -⟩ := emitMk_spec (σ := σ₄) hNB (Marked o t u) (by simp [σ₄, hn₃])
    (by simp only [σ₄]; rw [ha₃ "mk" (by decide), hm₂])
  have hu₅ : σ₅.vars "u" = u := by rw [hv₅ "u" (by decide)]; simp [σ₄, hu₃]
  have r₆ : Run B (.assign "u" (.add (.var "u") (.lit 1))) σ₅ (σ₅.setVar "u" (u + 1)) 4 :=
    (Run.assign (by simp [hu₅]; omega)).mono (by simp)
  refine ⟨_, (r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq r₆))))).mono (by omega), ?_, ?_, by simp,
    ?_, ?_, ?_⟩
  · simp only [out_setVar, ho₅, σ₄, ho₃, ho₂, ho₁, hd₃, markBlock, List.append_assoc]
    simp
  · simp only [vars_setVar]
    simp only [show ("n" : String) = "u" ↔ False by decide, if_false]
    rw [hv₅ "n" (by decide)]; simp [σ₄, hn₃]
  · simp only [arrs_setVar]
    rw [ha₅ "of" (by decide)]; simp only [σ₄]; rw [ha₃ "of" (by decide), hof₂]
  · simp only [arrs_setVar]
    rw [ha₅ "tg" (by decide)]; simp only [σ₄]; rw [ha₃ "tg" (by decide), htg₂]
  · simp only [arrs_setVar]
    rw [ha₅ "mk" (by decide)]; simp only [σ₄]; rw [ha₃ "mk" (by decide), hm₂]

/-! ### The program -/

/-- The loop over the vertices. -/
def vertexLoop : Com := .seq (.assign "u" (.lit 0)) (.while (.lt (.var "u") (.var "n")) vertexBody)

/-- From the compressed sparse row word to the word of the graph. -/
def csrToGraph : Com :=
  .seq (.read "n") (.seq (.read "E") (.seq (.assign "cnt" (.add (.var "n") (.lit 1)))
    (.seq (readArr "of") (.seq (.assign "cnt" (.add (.var "E") (.var "E")))
      (.seq (readArr "tg") (.seq (.write (.var "n")) vertexLoop))))))

def csrLayout : Layout where
  scalars := ["n", "E", "cnt", "i", "v", "u", "z", "j", "hi", "d"]
  arrays := ["of", "tg", "mk"]
  temps := 4

theorem csrToGraph_ok : Com.Ok csrLayout csrToGraph := by
  simp [csrToGraph, vertexLoop, vertexBody, clearMk, markMk, countMk, emitMk, readArr, csrLayout,
    Com.Ok, Cond.Ok, Expr.Ok, condExpr]

open Classical in
theorem vertexLoop_spec {B N D : ℕ} {o t : ℕ → ℕ} (hNB : N + 1 < B) (hDB : D < B)
    (hmono : ∀ u < N, o u ≤ o (u + 1)) (hoD : o N ≤ D) (ht : ∀ j < D, t j < N)
    {σ : Env} (hn : σ.vars "n" = N) (hof : σ.arrs "of" = arrOf (N + 1) o)
    (htg : σ.arrs "tg" = arrOf D t) (f : ℕ → ℕ) (hmk : σ.arrs "mk" = arrOf N f) :
    ∃ σ', Run B vertexLoop σ σ' ((41 * N + 50) * N + 12 * (o N - o 0) + 6) ∧
      σ'.out = σ.out ++ (List.range N).flatMap (fun u => markBlock N (Marked o t u)) := by
  have hmono' : ∀ u v, u ≤ v → v ≤ N → o u ≤ o v := by
    intro u v huv hv
    induction v, huv using Nat.le_induction with
    | base => exact le_rfl
    | succ v _ ih => exact (ih (by omega)).trans (hmono v (by omega))
  let I : Env → Prop := fun τ => τ.vars "n" = N ∧ τ.vars "u" ≤ N ∧ τ.arrs "of" = arrOf (N + 1) o ∧
    τ.arrs "tg" = arrOf D t ∧ (∃ f, τ.arrs "mk" = arrOf N f) ∧
    τ.out = σ.out ++ (List.range (τ.vars "u")).flatMap (fun u => markBlock N (Marked o t u))
  obtain ⟨σ', K, hr, ⟨hn', hu', -, -, -, hout'⟩, hfalse, hK⟩ :=
    Run.while_potential (B := B) (b := .lt (.var "u") (.var "n")) (c := vertexBody) I
      (fun τ => (41 * N + 50) * (N - τ.vars "u") + 12 * (o N - o (τ.vars "u")))
      (fun τ ⟨hn, hu, _⟩ => evalB_condLt_vars (by omega) (by omega))
      (by
        rintro τ ⟨hn, hu, hof, htg, ⟨f, hmk⟩, hout⟩ hc
        have hlt : τ.vars "u" < N := by have := lt_of_condLt_true hc; rwa [hn] at this
        have h1 := hmono _ hlt
        have h2 := hmono' (τ.vars "u" + 1) N (by omega) le_rfl
        obtain ⟨τ', hr, hout', hn', hu', hof', htg', hmk'⟩ :=
          vertexBody_spec hNB hDB hlt h1 (h2.trans hoD) ht hn rfl hof htg f hmk
        refine ⟨τ', _, hr, ⟨hn', by omega, hof', htg', ⟨_, hmk'⟩, ?_⟩, ?_⟩
        · rw [hout', hout, hu', List.range_succ, List.flatMap_append]; simp
        · rw [hu']
          simp only [Cond.size, Expr.size]
          have : (41 * N + 50) * (N - τ.vars "u") = (41 * N + 50) * (N - (τ.vars "u" + 1)) +
              (41 * N + 50) := by
            rw [show N - τ.vars "u" = N - (τ.vars "u" + 1) + 1 by omega]; ring
          omega)
      (show I (σ.setVar "u" 0) from ⟨by simp [hn], by simp, by simp [hof], by simp [htg],
        ⟨f, by simp [hmk]⟩, by simp⟩)
  have huN : σ'.vars "u" = N := by
    have := le_of_condLt_false hfalse; rw [hn'] at this; omega
  refine ⟨σ', ((Run.assign (v := 0) (by simp; omega)).seq hr).mono ?_, by rw [hout', huN]⟩
  simp only [Cond.size, Expr.size, vars_setVar, if_true, Nat.sub_zero] at hK
  simp only [Expr.size]
  omega

/-- The array lengths of the run. -/
def csrExt (n E : ℕ) : String → ℕ :=
  fun a => if a = "of" then n + 1 else if a = "tg" then 2 * E else if a = "mk" then n else 0

open Classical in
theorem markBlocks_eq {g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} (h : EncodesGraph g n G) :
    (List.range n).flatMap (fun u => markBlock n (Marked (offset g) (target g) u)) =
      blocksWord (graphBlocks G) := by
  have hmono : ∀ u v, u ≤ v → v ≤ n → offset g u ≤ offset g v := by
    intro u v huv hv
    induction v, huv using Nat.le_induction with
    | base => exact le_rfl
    | succ v _ ih => exact (ih (by omega)).trans (h.offset_mono v (by omega))
  rw [List.flatMap, blocksWord, graphBlocks]
  congr 1
  apply List.ext_getElem (by simp)
  intro u h₁ h₂
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  simp only [List.length_map, List.length_range] at h₁
  rw [setBlock_fin _ (Marked (offset g) (target g) u)]
  intro z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, h1, h2, h3⟩
    have hj : j < 2 * edgeCount g := by
      have := hmono (u + 1) n (by omega) le_rfl
      rw [h.offset_last] at this; omega
    have hz : z < n := by rw [← h3]; exact h.target_lt j hj
    refine ⟨hz, (h.adj_iff ⟨u, h₁⟩ ⟨z, hz⟩).mpr ⟨j, h1, h2, ?_⟩⟩
    simpa using h3
  · rintro ⟨hz, hadj⟩
    obtain ⟨j, h1, h2, h3⟩ := (h.adj_iff ⟨u, h₁⟩ ⟨z, hz⟩).mp hadj
    exact ⟨j, h1, h2, by simpa using h3⟩

theorem csrToGraph_run {g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} (h : EncodesGraph g n G)
    (B : ℕ) (hB : g.length + Words.maxEntry g + 2 ≤ B) :
    ∃ σ', Run B csrToGraph (initEnv (csrExt n (edgeCount g)) g) σ'
        (60 * ((n + 1) ^ 2 + g.length)) ∧ σ'.out = toWord G := by
  classical
  have hshape := csr_shape h
  have hlen := h.length_eq
  have hol : offset g n = 2 * edgeCount g := h.offset_last
  have hoz : offset g 0 = 0 := h.offset_zero
  set E := edgeCount g
  set o := offset g
  set t := target g
  have hent : ∀ v ∈ g, v < B := fun v hv => by have := Words.le_maxEntry hv; omega
  have hnB : n + 1 < B := by
    have : n ∈ g := by rw [hshape]; simp
    have := hent n this; omega
  have hEB : 2 * E < B := by omega
  have hoffs : ∀ v ∈ arrOf (n + 1) o, v < B := fun v hv => hent v (by rw [hshape]; simp [hv])
  have htgs : ∀ v ∈ arrOf (2 * E) t, v < B := fun v hv => hent v (by rw [hshape]; simp [hv])
  set σ₀ := initEnv (csrExt n E) g
  have hinp₀ : σ₀.inp = n :: E :: (arrOf (n + 1) o ++ arrOf (2 * E) t) := hshape
  set σ₁ : Env := { σ₀.setVar "n" n with inp := E :: (arrOf (n + 1) o ++ arrOf (2 * E) t) }
  have r₁ : Run B (.read "n") σ₀ σ₁ 1 := Run.read hinp₀
  set σ₂ : Env := { σ₁.setVar "E" E with inp := arrOf (n + 1) o ++ arrOf (2 * E) t }
  have r₂ : Run B (.read "E") σ₁ σ₂ 1 := Run.read rfl
  set σ₃ := σ₂.setVar "cnt" (n + 1)
  have r₃ : Run B (.assign "cnt" (.add (.var "n") (.lit 1))) σ₂ σ₃ 4 :=
    (Run.assign (by simp [σ₂, σ₁]; omega)).mono (by simp)
  obtain ⟨σ₄, r₄, hinp₄, hof₄, hv₄, ha₄, ho₄⟩ := readArr_spec (B := B) "of" (arrOf (n + 1) o)
    (arrOf (2 * E) t) (by simp; omega) hoffs (σ := σ₃) (by simp [σ₃]) (by simp [σ₃, σ₂])
    (by simp [σ₃, σ₂, σ₁, σ₀, initEnv, csrExt, replicate_eq_arrOf])
  set σ₅ := σ₄.setVar "cnt" (E + E)
  have hE₄ : σ₄.vars "E" = E := by rw [hv₄ "E" (by decide)]; simp [σ₃, σ₂]
  have hn₄ : σ₄.vars "n" = n := by rw [hv₄ "n" (by decide)]; simp [σ₃, σ₂, σ₁]
  have r₅ : Run B (.assign "cnt" (.add (.var "E") (.var "E"))) σ₄ σ₅ 4 :=
    (Run.assign (by simp [hE₄]; omega)).mono (by simp)
  obtain ⟨σ₆, r₆, -, htg₆, hv₆, ha₆, ho₆⟩ := readArr_spec (B := B) "tg" (arrOf (2 * E) t) []
    (by simp; omega) htgs (σ := σ₅) (by simp [σ₅]; omega) (by simp [σ₅, hinp₄])
    (by
      simp only [σ₅, arrs_setVar]
      rw [ha₄ "tg" (by decide)]
      simp [σ₃, σ₂, σ₁, σ₀, initEnv, csrExt, replicate_eq_arrOf])
  have hn₆ : σ₆.vars "n" = n := by rw [hv₆ "n" (by decide)]; simp [σ₅, hn₄]
  set σ₇ : Env := { σ₆ with out := σ₆.out ++ [n] }
  have r₇ : Run B (.write (.var "n")) σ₆ σ₇ 2 := (Run.write (by simp [hn₆]; omega)).mono (by simp)
  have hof₇ : σ₇.arrs "of" = arrOf (n + 1) o := by
    simp only [σ₇]; rw [ha₆ "of" (by decide)]; simp [σ₅, hof₄]
  have hmk₇ : σ₇.arrs "mk" = arrOf n (fun _ => 0) := by
    simp only [σ₇]; rw [ha₆ "mk" (by decide)]
    simp only [σ₅, arrs_setVar]; rw [ha₄ "mk" (by decide)]
    simp [σ₃, σ₂, σ₁, σ₀, initEnv, csrExt, replicate_eq_arrOf]
  have hmono : ∀ u < n, o u ≤ o (u + 1) := fun u hu => h.offset_mono u hu
  obtain ⟨σ₈, r₈, ho₈⟩ := vertexLoop_spec (B := B) (D := 2 * E) (o := o) (t := t) hnB hEB hmono
    (le_of_eq hol) (fun j hj => h.target_lt j hj) (σ := σ₇) (by simp [σ₇, hn₆]) hof₇
    (by simp [σ₇, htg₆]) _ hmk₇
  refine ⟨σ₈, (r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq (r₆.seq (r₇.seq r₈))))))).mono ?_, ?_⟩
  · rw [hol, hoz]
    have h1 : (41 * n + 50) * n = 41 * (n * n) + 50 * n := by ring
    have h2 : (n + 1) ^ 2 = n * n + 2 * n + 1 := by ring
    simp only [length_arrOf]
    rw [h1, h2]
    omega
  · have hout4 : σ₄.out = [] := by rw [ho₄]; simp [σ₃, σ₂, σ₁, σ₀, initEnv]
    have hout6 : σ₆.out = [] := by rw [ho₆]; simp [σ₅, hout4]
    rw [ho₈, toWord_graph, ← markBlocks_eq h]
    simp only [σ₇, hout6]
    rfl

/-- **From compressed sparse rows to the word of the graph**, on the
word RAM, in time `O(n² + |g|)`. -/
theorem csrToGraph_runsTo {g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} (h : EncodesGraph g n G)
    (w : ℕ) (hw : 4 * (g.length + Words.maxEntry g + 2) + 16 ≤ 2 ^ w) :
    ∃ t ≤ 600 * ((n + 1) ^ 2 + g.length) + 1,
      Lax808846.Ram.RunsTo w (compileProgram csrLayout csrToGraph) g (toWord G) t := by
  set B := g.length + Words.maxEntry g + 2
  obtain ⟨σ', ⟨k, hk, hbs⟩, hout⟩ := csrToGraph_run h B le_rfl
  have hfit : csrLayout.FitsWords B w :=
    ⟨by omega, by omega, by simp [Layout.span, csrLayout]; omega⟩
  obtain ⟨t, ht, hrun⟩ := compileProgram_runsTo hfit csrToGraph_ok
    (fun v hv => by have := Words.le_maxEntry hv; omega) hbs
  rw [hout] at hrun
  refine ⟨t, ht.trans ?_, hrun⟩
  simp only [Layout.const]
  omega

end Lax185574Proofs.Compose
