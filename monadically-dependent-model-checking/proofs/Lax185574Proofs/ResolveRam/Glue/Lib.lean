import Lax185574Proofs.ResolveRam.Glue.PieceSpec
import Lax185574Proofs.Words.TreeNode

/-!
Growing the word library and writing ranges of its words.

The word library holds the list `ws` in the arrays `a`, `st`, `ln`
(`WordsAt`), with the number of words in `m` and their total length in
`lt`. `lbApp src` appends the segment of length `lL` of the array `src`
from `ls` as a new word (`lbApp_run`). `lbFr src` appends `lN` words
that are framed in `src` from `ls` (`lbFr_run`), and `lbRng` appends
copies of the words `lo, …, lo + lN - 1` of the library (`lbRng_run`).
`emRng` appends the frames of the words `lo, …, lo + lN - 1` of the
library to the buffer (`emRng_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue

theorem sv2 (σ : Env) (x : String) (a b : ℕ) : (σ.setVar x a).setVar x b = σ.setVar x b := by
  cases σ; simp only [Env.setVar, Env.mk.injEq, and_true]; funext y; split_ifs <;> rfl

/-- A step that changes only the scalar `x`, to `v`. -/
structure Only (x : String) (v : ℕ) (σ σ' : Env) : Prop where
  self : σ'.vars x = v
  vars : ∀ y, y ≠ x → σ'.vars y = σ.vars y
  arrs : σ'.arrs = σ.arrs
  out : σ'.out = σ.out
  inp : σ'.inp = σ.inp

theorem Only.of_setVar (σ : Env) (x : String) (v : ℕ) : Only x v σ (σ.setVar x v) :=
  ⟨by simp, fun y hy => by simp [hy], rfl, rfl, rfl⟩

/-- An assignment, with an opaque result. -/
theorem asg_run {B : ℕ} {x : String} {e : Expr} {v : ℕ} {σ : Env} (h : e.evalB B σ = some v) :
    ∃ σ', Run B (.assign x e) σ σ' (1 + e.size) ∧ Only x v σ σ' :=
  ⟨_, Run.assign h, Only.of_setVar σ x v⟩

/-- The words `lo, …, lo + N - 1` of a list. -/
def rng (L : List (List ℕ)) (lo N : ℕ) : List (List ℕ) := (L.drop lo).take N

theorem rng_succ {L : List (List ℕ)} {lo k : ℕ} (h : lo + k < L.length) :
    rng L lo (k + 1) = rng L lo k ++ [L[lo + k]] := by
  unfold rng
  rw [List.take_add_one, List.getElem?_drop, List.getElem?_eq_getElem h, Option.toList_some]

theorem rng_append_left {L M : List (List ℕ)} {lo N : ℕ} (h : lo + N ≤ L.length) :
    rng (L ++ M) lo N = rng L lo N := by
  unfold rng
  rw [List.drop_append_of_le_length (by omega), List.take_append_of_le_length (by simp; omega)]

theorem length_rng {L : List (List ℕ)} {lo N : ℕ} (h : lo + N ≤ L.length) : (rng L lo N).length = N := by
  simp [rng]; omega

theorem total_append (a b : List (List ℕ)) : total (a ++ b) = total a + total b := by
  simp [total]

theorem total_single (w : List ℕ) : total [w] = w.length := by simp [total]

theorem off_append_left {ws : List (List ℕ)} (M : List (List ℕ)) {i : ℕ} (h : i ≤ ws.length) :
    off (ws ++ M) i = off ws i := by
  simp [off, List.take_append_of_le_length h]

theorem off_append_len (ws M : List (List ℕ)) : off (ws ++ M) ws.length = total ws := by
  simp [off, total]

/-- `WordsAt` for the library with one more word. -/
theorem wordsAt_snoc {ws : List (List ℕ)} {w : List ℕ} {τ τ' : Env} (h : WordsAt ws τ)
    (hst : ∀ i, i < ws.length → (τ'.arrs "st")[i]? = (τ.arrs "st")[i]?)
    (hst' : (τ'.arrs "st")[ws.length]? = some (total ws))
    (hln : ∀ i, i < ws.length → (τ'.arrs "ln")[i]? = (τ.arrs "ln")[i]?)
    (hln' : (τ'.arrs "ln")[ws.length]? = some w.length)
    (ha : ∀ j, j < total ws → (τ'.arrs "a")[j]? = (τ.arrs "a")[j]?)
    (ha' : ∀ j (hj : j < w.length), (τ'.arrs "a")[total ws + j]? = some w[j]) :
    WordsAt (ws ++ [w]) τ' where
  st i hi := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hi
    rcases Nat.lt_or_ge i ws.length with h1 | h1
    · rw [hst i h1, h.st i h1, off_append_left _ h1.le]
    · obtain rfl : i = ws.length := by omega
      rw [hst', off_append_len]
  ln i hi := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hi
    rcases Nat.lt_or_ge i ws.length with h1 | h1
    · rw [hln i h1, h.ln i h1, List.getElem_append_left h1]
    · obtain rfl : i = ws.length := by omega
      rw [hln']; simp
  a i hi j hj := by
    simp only [List.length_append, List.length_cons, List.length_nil] at hi
    rcases Nat.lt_or_ge i ws.length with h1 | h1
    · have hj' : j < ws[i].length := by rwa [List.getElem_append_left h1] at hj
      have hoi := off_add_le h1
      have hoff : off ws i + ws[i].length ≤ total ws := hoi
      rw [off_append_left _ h1.le, ha _ (by omega), h.a i h1 j hj']
      simp [List.getElem_append_left h1]
    · obtain rfl : i = ws.length := by omega
      have hj' : j < w.length := by simpa using hj
      rw [off_append_len, ha' j hj']
      simp

/-! ### Appending a segment -/

/-- The body of the copy: `a[lt + ci] := src[ls + ci]`. -/
def cpA (src : String) : Com :=
  .store "a" (.add (.var "lt") (.var "ci")) (.get src (.add (.var "ls") (.var "ci")))

/-- Append the segment of length `lL` of `src` from `ls` as a new word. -/
def lbApp (src : String) : Com :=
  .seq (.store "st" (.var "m") (.var "lt")) (.seq (.store "ln" (.var "m") (.var "lL"))
    (.seq (forUp "ci" (.var "lL") (cpA src))
      (.seq (.assign "lt" (.add (.var "lt") (.var "lL"))) (.assign "m" (.add (.var "m") (.lit 1))))))

/-- The segment of `src` from `s` is `w`. -/
def SegAt (src : String) (s : ℕ) (w : List ℕ) (τ : Env) : Prop :=
  ∀ j (hj : j < w.length), (τ.arrs src)[s + j]? = some w[j]

/-- The library holds `ws`, with its count and total length. -/
structure Lib (ws : List (List ℕ)) (τ : Env) : Prop where
  at_ : WordsAt ws τ
  m : τ.vars "m" = ws.length
  lt : τ.vars "lt" = total ws

theorem Lib.of {ws : List (List ℕ)} {τ τ' : Env} (h : Lib ws τ) (hm : τ'.vars "m" = τ.vars "m")
    (hlt : τ'.vars "lt" = τ.vars "lt") (ha : τ'.arrs "a" = τ.arrs "a") (hst : τ'.arrs "st" = τ.arrs "st")
    (hln : τ'.arrs "ln" = τ.arrs "ln") : Lib ws τ' :=
  ⟨h.at_.of_arrs ha hst hln, by rw [hm, h.m], by rw [hlt, h.lt]⟩

/-- **Appending a segment to the library.** -/
theorem lbApp_run {W : ℕ} {src : String} {ws : List (List ℕ)} {w : List ℕ} {s : ℕ} {τ : Env}
    (hL : Lib ws τ) (hs : τ.vars "ls" = s) (hl : τ.vars "lL" = w.length) (hseg : SegAt src s w τ)
    (hsrc : src ≠ "st" ∧ src ≠ "ln") (hsa : src = "a" → s + w.length ≤ total ws)
    (hca : total ws + w.length ≤ (τ.arrs "a").length) (hcst : ws.length < (τ.arrs "st").length)
    (hcln : ws.length < (τ.arrs "ln").length) (hB : total ws + w.length + ws.length + 1 ≤ W)
    (hsB : s + w.length ≤ W) (hv : ∀ v ∈ w, v ≤ W) :
    ∃ τ', Run (W + 1) (lbApp src) τ τ' (w.length * 18 + 30) ∧ Lib (ws ++ [w]) τ' ∧
      (∀ y, y ∉ ["ci", "lt", "m"] → τ'.vars y = τ.vars y) ∧
      (∀ b, b ∉ ["a", "st", "ln"] → τ'.arrs b = τ.arrs b) ∧
      (∀ b, (τ'.arrs b).length = (τ.arrs b).length) ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  have hm := hL.m
  have hlt := hL.lt
  set N := w.length
  set T := total ws
  set τ1 := τ.setArr "st" ws.length T
  have r1 : Run (W + 1) (.store "st" (.var "m") (.var "lt")) τ τ1 3 :=
    Run.store (ev_var hm (by omega)) (ev_var hlt (by omega)) hcst
  set τ2 := τ1.setArr "ln" ws.length N
  have r2 : Run (W + 1) (.store "ln" (.var "m") (.var "lL")) τ1 τ2 3 :=
    Run.store (ev_var (by simp [τ1, hm]) (by omega)) (ev_var (by simp [τ1, hl]) (by omega))
      (by simp [τ1]; omega)
  -- the copy loop
  let I : ℕ → Env → Prop := fun k ρ => ρ.vars "lt" = T ∧ ρ.vars "ls" = s ∧ ρ.vars "lL" = N ∧
    (∀ b, b ≠ "a" → ρ.arrs b = τ2.arrs b) ∧ (ρ.arrs "a").length = (τ.arrs "a").length ∧
    (∀ j, j < T → (ρ.arrs "a")[j]? = (τ.arrs "a")[j]?) ∧
    (∀ j (hj : j < N), j < k → (ρ.arrs "a")[T + j]? = some w[j]) ∧
    (∀ j, src = "a" → T ≤ j → (ρ.arrs "a")[j]? = (τ.arrs "a")[j]? ∨ True)
  have hI0 : I 0 (τ2.setVar "ci" 0) := by
    refine ⟨by simp [τ2, τ1, hlt], by simp [τ2, τ1, hs], by simp [τ2, τ1, hl], fun b hb => by simp,
      by simp [τ2, τ1], fun j _ => by simp [τ2, τ1], fun j hj h0 => absurd h0 (by omega),
      fun _ _ _ => Or.inr trivial⟩
  obtain ⟨τ3, r3, ⟨i1, i2, i3, i4, i5, i6, i7, -⟩, -⟩ := forUp_run (B := W + 1) (i := "ci")
    (e := .var "lL") (body := cpA src) (N := N) (K := 9) I (σ := τ2) (by omega)
    (fun k _ ρ hI _ => ev_var hI.2.2.1 (by omega)) hI0
    (by
      rintro k hk ρ ⟨i1, i2, i3, i4, i5, i6, i7, -⟩ hci
      have hsrcv : (ρ.arrs src)[s + k]? = some w[k] := by
        by_cases hsa' : src = "a"
        · subst hsa'
          have := hsa rfl
          rw [i6 _ (by omega)]
          exact hseg k hk
        · rw [i4 src hsa', show τ2.arrs src = τ.arrs src by
            simp [τ2, τ1, hsrc.1, hsrc.2]]
          exact hseg k hk
      have hwk : w[k] ≤ W := hv _ (List.getElem_mem hk)
      have rs : Run (W + 1) (cpA src) ρ (ρ.setArr "a" (T + k) w[k]) 9 :=
        (Run.store (ev_add (ev_var i1 (by omega)) (ev_var hci (by omega)) (by omega))
          (evalB_get (ev_add (ev_var i2 (by omega)) (ev_var hci (by omega)) (by omega)) hsrcv
            (by omega)) (by rw [i5]; omega)).mono (by simp [Expr.size])
      refine ⟨_, rs, by simp [hci], by simp [i1], by simp [i2], by simp [i3], fun b hb => ?_, by simp [i5],
        fun j hj => ?_, fun j hj hjk => ?_, fun _ _ _ => Or.inr trivial⟩
      · simp only [arrs_setVar, arrs_setArr, if_neg hb]; exact i4 b hb
      · simp only [arrs_setVar, arrs_setArr, ↓reduceIte, List.getElem?_set]
        rw [if_neg (by omega)]; exact i6 j hj
      · simp only [arrs_setVar, arrs_setArr, ↓reduceIte, List.getElem?_set]
        rcases Nat.lt_or_ge j k with h1 | h1
        · rw [if_neg (by omega)]; exact i7 j hj h1
        · obtain rfl : j = k := by omega
          rw [if_pos rfl, if_pos (by rw [i5]; omega)])
  set τ4 := τ3.setVar "lt" (T + N)
  have r4 : Run (W + 1) (.assign "lt" (.add (.var "lt") (.var "lL"))) τ3 τ4 4 :=
    (Run.assign (ev_add (ev_var i1 (by omega)) (ev_var i3 (by omega)) (by omega))).mono (by simp [Expr.size])
  have hm3 : τ3.vars "m" = ws.length := by
    rw [r3.frame_var "m" (by simp [forUp, cpA, Com.wvars])]; simp [τ2, τ1, hm]
  set τ5 := τ4.setVar "m" (ws.length + 1)
  have r5 : Run (W + 1) (.assign "m" (.add (.var "m") (.lit 1))) τ4 τ5 4 :=
    (Run.assign (ev_add (ev_var (by simp [τ4, hm3]) (by omega)) (evalB_lit (by omega)) (by omega))).mono
      (by simp [Expr.size])
  have hrun : Run (W + 1) (lbApp src) τ τ5 (N * 18 + 30) := by
    unfold lbApp
    exact (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 r5)))).mono (by simp [Expr.size]; omega)
  have hst5 : τ5.arrs "st" = τ2.arrs "st" := by simp [τ5, τ4]; exact i4 "st" (by decide)
  have hln5 : τ5.arrs "ln" = τ2.arrs "ln" := by simp [τ5, τ4]; exact i4 "ln" (by decide)
  have ha5 : τ5.arrs "a" = τ3.arrs "a" := by simp [τ5, τ4]
  refine ⟨τ5, hrun, ⟨wordsAt_snoc hL.at_ (fun i hi => ?_) ?_ (fun i hi => ?_) ?_
    (fun j hj => by rw [ha5]; exact i6 j hj) (fun j hj => by rw [ha5]; exact i7 j hj hj),
    by simp [τ5], by simp [τ5, τ4, total_append, total_single, T, N]⟩,
    fun y hy => ?_, fun b hb => ?_, fun b => Run.length_arrs hrun b, hrun.out_eq (by simp [lbApp, forUp, cpA, Com.NoWrite]),
    hrun.frame_inp (by simp [lbApp, forUp, cpA, Com.reads])⟩
  · rw [hst5]; simp only [τ2, τ1, arrs_setArr, ↓reduceIte, List.getElem?_set]
    simp [show (ws.length = i) = False by simp; omega, show ("ln" : String) ≠ "st" by decide]
  · rw [hst5]; simp [τ2, τ1, show ("ln" : String) ≠ "st" by decide, List.getElem?_set, hcst, T]
  · rw [hln5]; simp only [τ2, τ1, arrs_setArr, ↓reduceIte, List.getElem?_set]
    simp [show (ws.length = i) = False by simp; omega]
  · rw [hln5]; simp [τ2, τ1, List.getElem?_set, hcln, N]
  · exact hrun.frame_var y (by simp [lbApp, forUp, cpA, Com.wvars] at hy ⊢; tauto)
  · exact hrun.frame_arr b (by simp [lbApp, forUp, cpA, Com.warrs] at hb ⊢; tauto)

/-! ### Appending framed words -/

theorem frames_take_succ {L : List (List ℕ)} {k : ℕ} (hk : k < L.length) :
    frames (L.take (k + 1)) = frames (L.take k) ++ (L[k].length :: L[k]) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, frames_append, frames_single]

theorem frames_take_prefix {L : List (List ℕ)} (k : ℕ) :
    ∃ R, frames L = frames (L.take k) ++ R := by
  refine ⟨frames (L.drop k), ?_⟩
  rw [← frames_append, List.take_append_drop]

theorem length_frames (L : List (List ℕ)) : (frames L).length = total L + L.length := by
  induction L with
  | nil => simp [frames, total]
  | cons a l ih =>
    have : frames (a :: l) = (a.length :: a) ++ frames l := by simp [frames]
    rw [this, total_cons]; simp [ih]; omega

theorem total_take_le (L : List (List ℕ)) (k : ℕ) : total (L.take k) ≤ total L := by
  have := List.take_append_drop k L
  have h2 := total_append (L.take k) (L.drop k)
  rw [this] at h2; omega

theorem mem_frames {L : List (List ℕ)} {v : ℕ} (h : v ∈ frames L) :
    (∃ w ∈ L, v = w.length) ∨ ∃ w ∈ L, v ∈ w := by
  simp only [frames, List.mem_flatten, List.mem_map] at h
  obtain ⟨_, ⟨w, hw, rfl⟩, hv⟩ := h
  rcases List.mem_cons.1 hv with h | h
  · exact Or.inl ⟨w, hw, h⟩
  · exact Or.inr ⟨w, hw, h⟩

theorem le_maxLen {L : List (List ℕ)} {w : List ℕ} (h : w ∈ L) : w.length ≤ maxLen L := by
  induction L with
  | nil => simp at h
  | cons a l ih =>
    simp only [maxLen, List.map_cons, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact le_trans (ih h) (le_max_right _ _)

/-- The body of `lbFr`. -/
def lbFrBody (src : String) : Com :=
  .seq (.assign "lL" (.get src (.var "ls"))) (.seq (.assign "ls" (.add (.var "ls") (.lit 1)))
    (.seq (lbApp src) (.assign "ls" (.add (.var "ls") (.var "lL")))))

/-- Append the `lN` words framed in `src` from `ls`. -/
def lbFr (src : String) : Com := forUp "fk" (.var "lN") (lbFrBody src)

/-- **Appending framed words.** -/
theorem lbFr_run {W : ℕ} {src : String} {ws L : List (List ℕ)} {p : ℕ} {τ : Env}
    (hL : Lib ws τ) (hs : τ.vars "ls" = p) (hN : τ.vars "lN" = L.length)
    (hseg : SegAt src p (frames L) τ) (hsrc : src ∉ ["a", "st", "ln"])
    (hca : total ws + total L ≤ (τ.arrs "a").length)
    (hcst : ws.length + L.length ≤ (τ.arrs "st").length)
    (hcln : ws.length + L.length ≤ (τ.arrs "ln").length)
    (hB : total ws + total L + ws.length + L.length + p + 1 ≤ W)
    (hv : ∀ w ∈ L, ∀ v ∈ w, v ≤ W) :
    ∃ τ', Run (W + 1) (lbFr src) τ τ' (18 * total L + 60 * L.length + 10) ∧ Lib (ws ++ L) τ' ∧
      τ'.vars "ls" = p + (frames L).length ∧
      (∀ y, y ∉ ["fk", "ci", "lt", "m", "lL", "ls"] → τ'.vars y = τ.vars y) ∧
      (∀ b, b ∉ ["a", "st", "ln"] → τ'.arrs b = τ.arrs b) ∧
      (∀ b, (τ'.arrs b).length = (τ.arrs b).length) ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  have hsa : src ≠ "a" := fun h => hsrc (by simp [h])
  have hsst : src ≠ "st" := fun h => hsrc (by simp [h])
  have hsln : src ≠ "ln" := fun h => hsrc (by simp [h])
  have hfl := length_frames L
  have hget : ∀ k (hk : k < L.length) j, j < L[k].length + 1 →
      (frames L)[(frames (L.take k)).length + j]? = (L[k].length :: L[k])[j]? := by
    intro k hk j hj
    have h1 : frames L = frames (L.take k) ++ ((L[k].length :: L[k]) ++ frames (L.drop (k + 1))) := by
      rw [← List.append_assoc, ← frames_take_succ hk, ← frames_append, List.take_append_drop]
    rw [h1, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
      List.getElem?_append_left (by simpa using hj)]
  have hsrcv : ∀ i, i < (frames L).length → (τ.arrs src)[p + i]? = (frames L)[i]? := by
    intro i hi; rw [hseg i hi, List.getElem?_eq_getElem hi]
  have htk : ∀ k, total (L.take k) ≤ total L := total_take_le L
  let I : ℕ → Env → Prop := fun k ρ => Lib (ws ++ L.take k) ρ ∧
    ρ.vars "ls" = p + (frames (L.take k)).length ∧ ρ.vars "lN" = L.length ∧
    (∀ b, b ∉ ["a", "st", "ln"] → ρ.arrs b = τ.arrs b) ∧ (∀ b, (ρ.arrs b).length = (τ.arrs b).length) ∧
    (∀ y, y ∉ ["fk", "ci", "lt", "m", "lL", "ls"] → ρ.vars y = τ.vars y) ∧ ρ.out = τ.out ∧ ρ.inp = τ.inp
  have hI0 : I 0 (τ.setVar "fk" 0) := ⟨by simpa using hL.of (by simp) (by simp) (by simp) (by simp) (by simp),
    by simp [hs, frames], by simp [hN], fun b _ => by simp, fun b => by simp,
    fun y hy => by simp at hy ⊢; intro h; simp [h] at hy, rfl, rfl⟩
  obtain ⟨τ', r, ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩, -⟩ := FarRam.forUp_run_sum (B := W + 1) (i := "fk")
    (e := .var "lN") (body := lbFrBody src) (N := L.length) (fun k => 18 * (L.getD k []).length + 50) I
    (σ := τ) (by omega)
    (fun k _ ρ hI _ => ev_var hI.2.2.1 (by omega)) hI0
    (by
      rintro k hk ρ ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ hfk
      set F := frames (L.take k)
      have htk1 : total (L.take k) + L[k].length ≤ total L := by
        have := htk (k + 1)
        rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, total_append,
          total_single] at this; exact this
      have hFk : F.length + L[k].length + 1 ≤ (frames L).length := by
        simp only [F]; rw [length_frames, length_frames, List.length_take]; omega
      have hwl : L[k].length ≤ total L := by omega
      rw [List.getD_eq_getElem _ _ hk]
      have hsr : (ρ.arrs src)[p + F.length]? = some L[k].length := by
        have h0 := hget k hk 0 (by omega)
        simp only [Nat.add_zero] at h0
        rw [i4 src hsrc, hsrcv _ (by omega), h0]; rfl
      set ρ1 := ρ.setVar "lL" L[k].length
      have r1 : Run (W + 1) (.assign "lL" (.get src (.var "ls"))) ρ ρ1 3 :=
        (Run.assign (evalB_get (ev_var i2 (by omega)) hsr (by omega))).mono (by simp [Expr.size])
      set ρ2 := ρ1.setVar "ls" (p + F.length + 1)
      have r2 : Run (W + 1) (.assign "ls" (.add (.var "ls") (.lit 1))) ρ1 ρ2 4 :=
        (Run.assign (ev_add (ev_var (by simp [ρ1, i2]) (by omega)) (evalB_lit (by omega))
          (by omega))).mono (by simp [Expr.size])
      have hL2 : Lib (ws ++ L.take k) ρ2 := i1.of (by simp [ρ2, ρ1]) (by simp [ρ2, ρ1]) (by simp [ρ2, ρ1])
        (by simp [ρ2, ρ1]) (by simp [ρ2, ρ1])
      have htl : total (ws ++ L.take k) + L[k].length ≤ total ws + total L := by
        rw [total_append]
        have : total (L.take (k + 1)) ≤ total L := htk _
        rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, total_append,
          total_single] at this; omega
      obtain ⟨ρ3, r3, L3, v3, a3, l3, o3, n3⟩ := lbApp_run (W := W) (src := src) (w := L[k])
        (s := p + F.length + 1) hL2 (by simp [ρ2]) (by simp [ρ2, ρ1])
        (fun j hj => by
          simp only [ρ2, ρ1, arrs_setVar]
          rw [i4 src hsrc, show p + F.length + 1 + j = p + (F.length + (j + 1)) by omega,
            hsrcv _ (by omega), hget k hk (j + 1) (by omega)]
          simp [List.getElem?_eq_getElem hj])
        ⟨hsst, hsln⟩ (fun h => absurd h hsa) (by simp [ρ2, ρ1, i5]; omega)
        (by simp [ρ2, ρ1, i5]; omega) (by simp [ρ2, ρ1, i5]; omega) (by simp; omega)
        (by omega) (fun v hv' => hv _ (List.getElem_mem hk) v hv')
      have hl3 : ρ3.vars "lL" = L[k].length := by rw [v3 _ (by decide)]; simp [ρ2, ρ1]
      have hs3 : ρ3.vars "ls" = p + F.length + 1 := by rw [v3 _ (by decide)]; simp [ρ2]
      set ρ4 := ρ3.setVar "ls" (p + F.length + 1 + L[k].length)
      have r4 : Run (W + 1) (.assign "ls" (.add (.var "ls") (.var "lL"))) ρ3 ρ4 4 :=
        (Run.assign (ev_add (ev_var hs3 (by omega)) (ev_var hl3 (by omega)) (by omega))).mono
          (by simp [Expr.size])
      have hrun : Run (W + 1) (lbFrBody src) ρ ρ4 (18 * L[k].length + 50) := by
        unfold lbFrBody
        exact (Run.seq r1 (Run.seq r2 (Run.seq r3 r4))).mono (by omega)
      have hfk4 : ρ4.vars "fk" = k := by
        rw [hrun.frame_var "fk" (by simp [lbFrBody, lbApp, forUp, cpA, Com.wvars]), hfk]
      refine ⟨ρ4, hrun, hfk4, ?_, ?_, ?_, fun b hb => ?_, fun b => ?_, fun y hy => ?_, ?_, ?_⟩
      · have : ws ++ L.take (k + 1) = ws ++ L.take k ++ [L[k]] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, List.append_assoc]
        rw [this]
        exact L3.of (by simp [ρ4]) (by simp [ρ4]) (by simp [ρ4]) (by simp [ρ4]) (by simp [ρ4])
      · simp only [vars_setVar, ρ4]; simp
        rw [frames_take_succ hk]; simp [F]; omega
      · simp only [vars_setVar, ρ4]; simp; rw [v3 _ (by decide)]; simp [ρ2, ρ1, i3]
      · simp only [arrs_setVar, ρ4]; rw [a3 b hb]; simp [ρ2, ρ1, i4 b hb]
      · simp only [arrs_setVar, ρ4]; rw [l3 b]; simp [ρ2, ρ1, i5 b]
      · have hy' : y ≠ "fk" ∧ y ≠ "ls" ∧ y ≠ "lL" ∧ y ∉ ["ci", "lt", "m"] := by
          simp at hy ⊢; tauto
        simp only [ρ4, vars_setVar, if_neg hy'.1, if_neg hy'.2.1]
        rw [v3 y hy'.2.2.2]
        simp only [ρ2, ρ1, vars_setVar, if_neg hy'.2.1, if_neg hy'.2.2.1]
        exact i6 y hy
      · show ρ3.out = τ.out
        rw [o3]; exact i7
      · show ρ3.inp = τ.inp
        rw [n3]; exact i8)
  refine ⟨τ', r.mono ?_, by simpa using i1, by rw [i2, List.take_of_length_le le_rfl], i6, i4, i5, i7, i8⟩
  have e1 : ∑ k ∈ Finset.range L.length, (18 * (L.getD k []).length + 50 + (Expr.var "lN").size + 7) =
      18 * total (L.take L.length) + L.length * 58 := by
    rw [← sum_len_take, ← sum_lin]; simp only [Expr.size]
  rw [e1, List.take_of_length_le le_rfl]; simp only [Expr.size]; omega

/-! ### Copying words of the library -/

theorem rng_sub (L : List (List ℕ)) (lo N : ℕ) : (rng L lo N).Sublist L :=
  (List.take_sublist _ _).trans (List.drop_sublist _ _)

theorem total_le_of_sub {l L : List (List ℕ)} (h : l.Sublist L) : total l ≤ total L := by
  induction h with
  | slnil => simp [total]
  | cons a _ ih => rw [total_cons]; omega
  | cons_cons a _ ih => rw [total_cons, total_cons]; omega

theorem maxLen_le_total (L : List (List ℕ)) : maxLen L ≤ total L := by
  induction L with
  | nil => simp [maxLen]
  | cons a l ih =>
    simp only [maxLen, List.map_cons, List.foldr_cons] at ih ⊢
    rw [total_cons]; omega

theorem wordsAt_get {ws : List (List ℕ)} {τ : Env} (h : WordsAt ws τ) {i : ℕ} (hi : i < ws.length) :
    SegAt "a" (off ws i) ws[i] τ := fun j hj => h.a i hi j hj

theorem wordsAt_append_left {ws M : List (List ℕ)} {τ : Env} (h : WordsAt (ws ++ M) τ) {i : ℕ}
    (hi : i < ws.length) : (τ.arrs "st")[i]? = some (off ws i) ∧ (τ.arrs "ln")[i]? = some ws[i].length ∧
      SegAt "a" (off ws i) ws[i] τ := by
  have hi' : i < (ws ++ M).length := by simp; omega
  refine ⟨by rw [h.st i hi', off_append_left _ hi.le], by rw [h.ln i hi', List.getElem_append_left hi],
    fun j hj => ?_⟩
  have := h.a i hi' j (by rwa [List.getElem_append_left hi])
  simpa [off_append_left _ hi.le, List.getElem_append_left hi] using this

/-- The body of `lbRng`. -/
def lbRngBody : Com :=
  .seq (.assign "ls" (.get "st" (.add (.var "lo") (.var "fk"))))
    (.seq (.assign "lL" (.get "ln" (.add (.var "lo") (.var "fk")))) (lbApp "a"))

/-- Append copies of the words `lo, …, lo + lN - 1` of the library. -/
def lbRng : Com := forUp "fk" (.var "lN") lbRngBody

/-- **Copying words of the library to its end.** -/
theorem lbRng_run {W : ℕ} {ws : List (List ℕ)} {lo N : ℕ} {τ : Env}
    (hL : Lib ws τ) (hlo : τ.vars "lo" = lo) (hN : τ.vars "lN" = N) (hr : lo + N ≤ ws.length)
    (hca : 2 * total ws ≤ (τ.arrs "a").length) (hcst : ws.length + N ≤ (τ.arrs "st").length)
    (hcln : ws.length + N ≤ (τ.arrs "ln").length) (hB : 2 * total ws + 2 * ws.length + 1 ≤ W)
    (hv : ∀ w ∈ ws, ∀ v ∈ w, v ≤ W) :
    ∃ τ', Run (W + 1) lbRng τ τ' (18 * total (rng ws lo N) + 60 * N + 10) ∧ Lib (ws ++ rng ws lo N) τ' ∧
      (∀ y, y ∉ ["fk", "ci", "lt", "m", "lL", "ls"] → τ'.vars y = τ.vars y) ∧
      (∀ b, b ∉ ["a", "st", "ln"] → τ'.arrs b = τ.arrs b) ∧
      (∀ b, (τ'.arrs b).length = (τ.arrs b).length) ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  have hrt : total (rng ws lo N) ≤ total ws := total_le_of_sub (rng_sub ws lo N)
  have hml := maxLen_le_total ws
  let I : ℕ → Env → Prop := fun k ρ => Lib (ws ++ rng ws lo k) ρ ∧ ρ.vars "lo" = lo ∧ ρ.vars "lN" = N ∧
    (∀ b, b ∉ ["a", "st", "ln"] → ρ.arrs b = τ.arrs b) ∧ (∀ b, (ρ.arrs b).length = (τ.arrs b).length) ∧
    (∀ y, y ∉ ["fk", "ci", "lt", "m", "lL", "ls"] → ρ.vars y = τ.vars y) ∧ ρ.out = τ.out ∧ ρ.inp = τ.inp
  have hI0 : I 0 (τ.setVar "fk" 0) := ⟨by simpa [rng] using hL.of (by simp) (by simp) (by simp) (by simp) (by simp),
    by simp [hlo], by simp [hN], fun b _ => by simp, fun b => by simp,
    fun y hy => by simp at hy ⊢; intro h; simp [h] at hy, rfl, rfl⟩
  obtain ⟨τ', r, ⟨i1, -, -, i4, i5, i6, i7, i8⟩, -⟩ := FarRam.forUp_run_sum (B := W + 1) (i := "fk")
    (e := .var "lN") (body := lbRngBody) (N := N) (fun k => 18 * ((ws.drop lo).getD k []).length + 50) I
    (σ := τ) (by omega)
    (fun k _ ρ hI _ => ev_var hI.2.2.1 (by omega)) hI0
    (by
      rintro k hk ρ ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ hfk
      have hik : lo + k < ws.length := by omega
      rw [getD_drop hik]
      have hrk : (rng ws lo k).length = k := length_rng (by omega)
      have hrk1 : total (rng ws lo k) + ws[lo + k].length ≤ total ws := by
        have := total_le_of_sub (rng_sub ws lo (k + 1))
        rwa [rng_succ hik, total_append, total_single] at this
      obtain ⟨hst, hln, hseg⟩ := wordsAt_append_left i1.at_ hik
      have hoff := off_add_le hik
      have hoff' : off ws (lo + k) + ws[lo + k].length ≤ total ws := hoff
      set ρ1 := ρ.setVar "ls" (off ws (lo + k))
      have r1 : Run (W + 1) (.assign "ls" (.get "st" (.add (.var "lo") (.var "fk")))) ρ ρ1 5 :=
        (Run.assign (evalB_get (ev_add (ev_var i2 (by omega)) (ev_var hfk (by omega)) (by omega)) hst
          (by omega))).mono (by simp [Expr.size])
      set ρ2 := ρ1.setVar "lL" ws[lo + k].length
      have r2 : Run (W + 1) (.assign "lL" (.get "ln" (.add (.var "lo") (.var "fk")))) ρ1 ρ2 5 :=
        (Run.assign (evalB_get (ev_add (ev_var (x := "lo") (v := lo) (by simp [ρ1, i2]) (by omega))
          (ev_var (x := "fk") (v := k) (by simp [ρ1, hfk]) (by omega)) (by omega)) (by simpa [ρ1] using hln)
          (by omega))).mono (by simp [Expr.size])
      have hL2 : Lib (ws ++ rng ws lo k) ρ2 := i1.of (by simp [ρ2, ρ1]) (by simp [ρ2, ρ1]) (by simp [ρ2, ρ1])
        (by simp [ρ2, ρ1]) (by simp [ρ2, ρ1])
      obtain ⟨ρ3, r3, L3, v3, a3, l3, o3, n3⟩ := lbApp_run (W := W) (src := "a") (w := ws[lo + k])
        (s := off ws (lo + k)) hL2 (by simp [ρ2, ρ1]) (by simp [ρ2])
        (fun j hj => by simpa [ρ2, ρ1] using hseg j hj) ⟨by decide, by decide⟩
        (fun _ => by rw [total_append]; omega) (by simp [ρ2, ρ1, i5, total_append]; omega)
        (by simp [ρ2, ρ1, i5]; omega) (by simp [ρ2, ρ1, i5]; omega) (by simp [total_append]; omega)
        (by omega) (fun v hv' => hv _ (List.getElem_mem hik) v hv')
      have hrun : Run (W + 1) lbRngBody ρ ρ3 (18 * ws[lo + k].length + 50) := by
        unfold lbRngBody
        exact (Run.seq r1 (Run.seq r2 r3)).mono (by omega)
      have hfk3 : ρ3.vars "fk" = k := by
        rw [hrun.frame_var "fk" (by simp [lbRngBody, lbApp, forUp, cpA, Com.wvars]), hfk]
      refine ⟨ρ3, hrun, hfk3, ?_, ?_, ?_, fun b hb => ?_, fun b => ?_, fun y hy => ?_, ?_, ?_⟩
      · rw [rng_succ hik, ← List.append_assoc]
        exact L3.of (by simp) (by simp) (by simp) (by simp) (by simp)
      · simp; rw [v3 _ (by decide)]; simp [ρ2, ρ1, i2]
      · simp; rw [v3 _ (by decide)]; simp [ρ2, ρ1, i3]
      · simp only [arrs_setVar]; rw [a3 b hb]; simp [ρ2, ρ1, i4 b hb]
      · simp only [arrs_setVar]; rw [l3 b]; simp [ρ2, ρ1, i5 b]
      · have hy' : y ≠ "fk" ∧ y ≠ "ls" ∧ y ≠ "lL" ∧ y ∉ ["ci", "lt", "m"] := by
          simp at hy ⊢; tauto
        simp only [vars_setVar, if_neg hy'.1]
        rw [v3 y hy'.2.2.2]
        simp only [ρ2, ρ1, vars_setVar, if_neg hy'.2.1, if_neg hy'.2.2.1]
        exact i6 y hy
      · show ρ3.out = τ.out
        rw [o3]; exact i7
      · show ρ3.inp = τ.inp
        rw [n3]; exact i8)
  refine ⟨τ', r.mono ?_, i1, i6, i4, i5, i7, i8⟩
  have e1 : ∑ k ∈ Finset.range N, (18 * ((ws.drop lo).getD k []).length + 50 + (Expr.var "lN").size + 7) =
      18 * total (rng ws lo N) + N * 58 := by
    rw [rng, ← sum_len_take, ← sum_lin]; simp only [Expr.size]
  rw [e1]; simp only [Expr.size]; omega

/-! ### Writing words of the library -/

/-- Append the frames of the words `lo, …, lo + lN - 1` of the library to the buffer. -/
def emRng : Com := forUp "fk" (.var "lN") (.seq (.assign "ow" (.add (.var "lo") (.var "fk"))) cpWord)

/-- **Writing the frames of a range of words.** -/
theorem emRng_run {W : ℕ} {ws : List (List ℕ)} {lo N : ℕ} {τ : Env} {pre : List ℕ}
    (hw : WordsAt ws τ) (hlo : τ.vars "lo" = lo) (hN : τ.vars "lN" = N) (hr : lo + N ≤ ws.length)
    (hF : Filled "OB" "po" pre τ) (hcap : pre.length + total ws + ws.length ≤ (τ.arrs "OB").length)
    (hB : pre.length + total ws + ws.length + 1 ≤ W) (hv : ∀ w ∈ ws, ∀ v ∈ w, v ≤ W)
    (ha : total ws ≤ (τ.arrs "a").length) :
    ∃ τ', Run (W + 1) emRng τ τ' (20 * total (rng ws lo N) + 40 * N + 10) ∧
      Filled "OB" "po" (pre ++ frames (rng ws lo N)) τ' ∧ OFr τ τ' ["fk", "ow", "wa", "wl", "po", "ci"] := by
  have hml := maxLen_le_total ws
  have hrs := size_sub (rng_sub ws lo N)
  let I : ℕ → Env → Prop := fun k ρ => Filled "OB" "po" (pre ++ frames (rng ws lo k)) ρ ∧
    OFr τ ρ ["fk", "ow", "wa", "wl", "po", "ci"]
  have hI0 : I 0 (τ.setVar "fk" 0) := ⟨by simpa [rng, frames] using hF.setVar (by decide) 0,
    (OFr.setVar τ "fk" 0).mono (by decide)⟩
  obtain ⟨τ', r, ⟨F, O⟩, -⟩ := FarRam.forUp_run_sum (B := W + 1) (i := "fk") (e := .var "lN")
    (body := .seq (.assign "ow" (.add (.var "lo") (.var "fk"))) cpWord) (N := N)
    (fun k => 20 * ((ws.drop lo).getD k []).length + 30) I (σ := τ) (by omega)
    (fun k _ ρ hI _ => ev_var (by rw [hI.2.vars _ (by decide), hN]) (by omega)) hI0
    (by
      rintro k hk ρ ⟨F, O⟩ hfk
      have hik : lo + k < ws.length := by omega
      rw [getD_drop hik]
      have hrk : frames (rng ws lo k) ++ (ws[lo + k].length :: ws[lo + k]) = frames (rng ws lo (k + 1)) := by
        rw [rng_succ hik, frames_append, frames_single]
      have hsk := size_sub (rng_sub ws lo (k + 1))
      have hfl := length_frames (rng ws lo (k + 1))
      have hfl' := congrArg List.length hrk
      simp only [List.length_append, List.length_cons] at hfl'
      set ρ1 := ρ.setVar "ow" (lo + k)
      have r1 : Run (W + 1) (.assign "ow" (.add (.var "lo") (.var "fk"))) ρ ρ1 4 :=
        (Run.assign (ev_add (ev_var (by rw [O.vars _ (by decide), hlo]) (by omega)) (ev_var hfk (by omega))
          (by omega))).mono (by simp [Expr.size])
      have ea : ρ1.arrs "a" = τ.arrs "a" := by simp only [ρ1, arrs_setVar]; exact O.arrs "a" (by decide)
      have hw1 : WordsAt ws ρ1 := hw.of_arrs ea
        (by simp only [ρ1, arrs_setVar]; exact O.arrs "st" (by decide))
        (by simp only [ρ1, arrs_setVar]; exact O.arrs "ln" (by decide))
      obtain ⟨ρ2, r2, F2, O2⟩ := cpWord_run (W := W) (i := lo + k) hw1 (by simp [ρ1]) hik
        (F.setVar (by decide) _) (by simp [ρ1, O.len]; omega) (by simp; omega) (by omega)
        (hv _ (List.getElem_mem hik)) (by rw [ea]; omega)
      refine ⟨ρ2, (Run.seq r1 r2).mono (by omega), by rw [O2.vars _ (by decide)]; simp [ρ1, hfk], ?_, ?_⟩
      · rw [← hrk, ← List.append_assoc]; exact F2.setVar (by decide) _
      · exact ((((O.trans (OFr.setVar ρ "ow" _)).trans O2).trans (OFr.setVar ρ2 "fk" _))).mono (by decide))
  have e1 : ∑ k ∈ Finset.range N, (20 * ((ws.drop lo).getD k []).length + 30 + (Expr.var "lN").size + 7) =
      20 * total (rng ws lo N) + N * 38 := by
    rw [rng, ← sum_len_take, ← sum_lin]; simp only [Expr.size]
  exact ⟨τ', r.mono (by rw [e1]; simp only [Expr.size]; omega), F, O⟩

end Lax185574Proofs.ResolveRam.Glue
