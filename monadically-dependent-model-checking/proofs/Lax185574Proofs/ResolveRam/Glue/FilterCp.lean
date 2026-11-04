import Lax185574Proofs.ResolveRam.Glue.Ans
import Lax185574Proofs.Words.TreeCopy
import Lax185574Proofs.FarRam.Loops

/-!
Writing a filtered list of words of the state.

The words `ws` are in the arrays of the word library. `filterCp test`
appends to the buffer the word of the list of the words `ws[lo + k]`,
`k < N`, that pass a test: first a placeholder for the count, then for
every word the command `test` sets `fb`, and the word is copied if
`fb = 1`; at the end the count replaces the placeholder
(`filterCp_run`). The test is given by its specification `TestOK`: from
the word `ow` it sets `fb` to `1` exactly for the words with property
`p`, writes no array and only the scalars `tv`.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue
open Lax185574.WordEncoding

/-- The body of the filter loop. -/
def filterBody (test : Com) : Com :=
  .seq (.assign "ow" (.add (.var "flo") (.var "fi"))) (.seq test
    (.ite (.eq (.var "fb") (.lit 1)) (.seq cpWord (.assign "fc" (.add (.var "fc") (.lit 1)))) .skip))

/-- Write the filtered list of the words `flo, …, flo + fN - 1`. -/
def filterCp (test : Com) : Com :=
  .seq (.assign "fp" (.var "po")) (.seq (push1 "OB" "po" (.lit 0)) (.seq (.assign "fc" (.lit 0))
    (.seq (forUp "fi" (.var "fN") (filterBody test)) (.store "OB" (.var "fp") (.var "fc")))))

/-- The specification of a test: on word `ow` of `ws` it sets `fb` to
`1` for the words with property `p` and to `0` otherwise, at cost at
most `K`, writing only the scalars `tv`, no array, and no tape. -/
def TestOK (W : ℕ) (test : Com) (ws : List (List ℕ)) (p : List ℕ → Bool) (tv : List String)
    (C : Env → Prop) (K : ℕ) : Prop :=
  ∀ (τ : Env) (i : ℕ) (hi : i < ws.length), WordsAt ws τ → C τ → τ.vars "ow" = i →
    ∃ τ', Run (W + 1) test τ τ' K ∧ τ'.vars "fb" = (if p ws[i] then 1 else 0) ∧
      (∀ y, y ∉ tv → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp

/-- The selected words among the first `k` of the range. -/
def selW (ws : List (List ℕ)) (lo k : ℕ) (p : List ℕ → Bool) : List (List ℕ) :=
  ((ws.drop lo).take k).filter p

theorem selW_succ {ws : List (List ℕ)} {lo k : ℕ} {p : List ℕ → Bool} (h : lo + k < ws.length) :
    selW ws lo (k + 1) p = selW ws lo k p ++ (if p ws[lo + k] then [ws[lo + k]] else []) := by
  unfold selW
  rw [List.take_add_one, List.getElem?_drop, List.getElem?_eq_getElem h, Option.toList_some,
    List.filter_append]
  by_cases hp : p ws[lo + k] <;> simp [hp]

theorem frames_append (a b : List (List ℕ)) : frames (a ++ b) = frames a ++ frames b := by
  simp [frames]

theorem frames_single (w : List ℕ) : frames [w] = w.length :: w := by simp [frames]

theorem total_cons (w : List ℕ) (l : List (List ℕ)) : total (w :: l) = w.length + total l := by
  simp [total]

theorem size_sub {l ws : List (List ℕ)} (h : l.Sublist ws) :
    l.length + total l ≤ ws.length + total ws := by
  induction h with
  | slnil => simp [total]
  | cons a _ ih => rw [total_cons]; simp; omega
  | cons_cons a _ ih => rw [total_cons, total_cons]; simp; omega

theorem selW_sub (ws : List (List ℕ)) (lo k : ℕ) (p : List ℕ → Bool) : (selW ws lo k p).Sublist ws :=
  List.filter_sublist.trans ((List.take_sublist _ _).trans (List.drop_sublist _ _))

/-- The scalars that the filter writes besides those of the test. -/
def fV : List String := ["fi", "fc", "fp", "ow", "wa", "wl", "po", "ci"]

theorem ofr_of_test {τ τ' : Env} {tv : List String} (hv : ∀ y, y ∉ tv → τ'.vars y = τ.vars y)
    (ha : τ'.arrs = τ.arrs) (ho : τ'.out = τ.out) (hi : τ'.inp = τ.inp) : OFr τ τ' tv :=
  ⟨hv, fun b _ => by rw [ha], by rw [ha], ho, hi⟩

theorem ofr_sub {τ τ' : Env} {xs ys : List String} (h : OFr τ τ' xs) (hs : ∀ y ∈ xs, y ∈ ys) :
    OFr τ τ' ys := h.mono hs

theorem sub_twice {tv : List String} : ∀ y ∈ (tv ++ fV) ++ (tv ++ fV), y ∈ tv ++ fV := by
  intro y hy; rcases List.mem_append.1 hy with h | h <;> exact h

theorem sub_fV {tv xs : List String} (h : ∀ y ∈ xs, y ∈ fV) : ∀ y ∈ xs, y ∈ tv ++ fV :=
  fun y hy => List.mem_append_right _ (h y hy)

theorem sub_app {tv xs : List String} (h : ∀ y ∈ xs, y ∈ fV) :
    ∀ y ∈ (tv ++ fV) ++ xs, y ∈ tv ++ fV := by
  intro y hy; rcases List.mem_append.1 hy with h' | h'
  · exact h'
  · exact List.mem_append_right _ (h y h')

theorem getElem?_mid (pre F : List ℕ) (a b : ℕ) (i : ℕ) (h : i ≠ pre.length) :
    (pre ++ a :: F)[i]? = (pre ++ b :: F)[i]? := by
  rcases Nat.lt_or_ge i pre.length with h1 | h1
  · rw [List.getElem?_append_left h1, List.getElem?_append_left h1]
  · rw [List.getElem?_append_right h1, List.getElem?_append_right h1]
    obtain ⟨j, hj⟩ : ∃ j, i - pre.length = j + 1 := ⟨i - pre.length - 1, by omega⟩
    rw [hj]; rfl

/-! ### Sums of word lengths -/

theorem sum_lin (N a b : ℕ) (x : ℕ → ℕ) :
    ∑ k ∈ Finset.range N, (a * x k + b) = a * ∑ k ∈ Finset.range N, x k + N * b := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]; simp

theorem total_take_succ (l : List (List ℕ)) (k : ℕ) :
    total (l.take (k + 1)) = total (l.take k) + (l.getD k []).length := by
  rw [List.take_add_one]
  rcases Nat.lt_or_ge k l.length with h | h
  · rw [List.getElem?_eq_getElem h, Option.toList_some, Words.total_append,
      List.getD_eq_getElem _ _ h]; simp [total]
  · rw [List.getElem?_eq_none h, List.getD_eq_default _ _ h]; simp

/-- The sum of the lengths of the first `N` words of a list. -/
theorem sum_len_take (l : List (List ℕ)) (N : ℕ) :
    ∑ k ∈ Finset.range N, (l.getD k []).length = total (l.take N) := by
  induction N with
  | zero => simp [total]
  | succ N ih => rw [Finset.sum_range_succ, ih, total_take_succ]

theorem getD_drop {ws : List (List ℕ)} {lo k : ℕ} (h : lo + k < ws.length) :
    (ws.drop lo).getD k [] = ws[lo + k] := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_drop]

/-- **Writing a filtered list of words.** -/
theorem filterCp_run {W lo N K : ℕ} {test : Com} {ws : List (List ℕ)} {p : List ℕ → Bool}
    {tv : List String} {C : Env → Prop} {σ : Env} {pre : List ℕ}
    (htv : ∀ y ∈ tv, y ∉ ["fi", "fc", "flo", "fN", "fp", "ow", "wa", "wl", "po", "ci", "W"])
    (hC : ∀ τ τ', C τ → OFr τ τ' (tv ++ fV) → C τ')
    (htest : TestOK W test ws p tv C K)
    (hw : WordsAt ws σ) (hCσ : C σ) (hlo : σ.vars "flo" = lo) (hN : σ.vars "fN" = N)
    (hr : lo + N ≤ ws.length) (hF : Filled "OB" "po" pre σ)
    (hcap : pre.length + 1 + total ws + ws.length ≤ (σ.arrs "OB").length)
    (hB : pre.length + 2 + total ws + ws.length ≤ W) (hv : ∀ w ∈ ws, ∀ v ∈ w, v ≤ W)
    (ha : total ws ≤ (σ.arrs "a").length) (hWv : σ.vars "W" = W) :
    ∃ σ', Run (W + 1) (filterCp test) σ σ'
        (N * (K + 50) + 20 * total ((ws.drop lo).take N) + 50) ∧
      Filled "OB" "po" (pre ++ toWord (selW ws lo N p)) σ' ∧ WordsAt ws σ' ∧ C σ' ∧
      OFr σ σ' (tv ++ fV) := by
  have hkeep : ∀ y ∈ ["flo", "fN", "W"], y ∉ tv ++ fV := by
    intro y hy h
    rcases List.mem_append.1 h with h | h
    · exact htv y h (by simp at hy ⊢; tauto)
    · simp [fV] at h hy; rcases hy with rfl | rfl | rfl <;> simp_all
  have hfV : ∀ y ∈ fV, y ∈ tv ++ fV := fun y h => List.mem_append_right _ h
  set L := (σ.arrs "OB").length
  have hpo : σ.vars "po" = pre.length := hF.pos
  set σ1 := σ.setVar "fp" pre.length
  have r1 : Run (W + 1) (.assign "fp" (.var "po")) σ σ1 2 := Run.assign (ev_var hpo (by omega))
  have hF1 : Filled "OB" "po" pre σ1 := hF.setVar (by decide) _
  obtain ⟨σ2, r2, F2, o2⟩ := push1_ofr (W := W) (e := .lit 0) (v := 0) hF1 (evalB_lit (by omega))
    (by simp [σ1]; omega) (by omega)
  set σ3 := σ2.setVar "fc" 0
  have r3 : Run (W + 1) (.assign "fc" (.lit 0)) σ2 σ3 2 := Run.assign (evalB_lit (by omega))
  have hF3 : Filled "OB" "po" (pre ++ [0]) σ3 := F2.setVar (by decide) _
  have o13 : OFr σ (σ3.setVar "fi" 0) (tv ++ fV) :=
    ofr_sub ((((OFr.setVar σ "fp" _).trans o2).trans (OFr.setVar σ2 "fc" 0)).trans (OFr.setVar σ3 "fi" 0))
      (sub_fV (by decide))
  have hfp3 : (σ3.setVar "fi" 0).vars "fp" = pre.length := by
    simp only [σ3, vars_setVar]; simp; rw [o2.vars "fp" (by decide)]; simp [σ1]
  -- the loop
  let I : ℕ → Env → Prop := fun k τ =>
    Filled "OB" "po" (pre ++ [0] ++ frames (selW ws lo k p)) τ ∧
    τ.vars "fc" = (selW ws lo k p).length ∧ WordsAt ws τ ∧ C τ ∧ OFr σ τ (tv ++ fV) ∧
    τ.vars "fp" = pre.length
  have hI0 : I 0 (σ3.setVar "fi" 0) :=
    ⟨by simpa [selW, frames] using hF3.setVar (y := "fi") (by decide) 0, by simp [σ3, selW],
      hw.of_arrs (by rw [o13.arrs _ (by decide)]) (by rw [o13.arrs _ (by decide)])
        (by rw [o13.arrs _ (by decide)]), hC σ _ hCσ o13, o13, hfp3⟩
  have hsel : ∀ k, (frames (selW ws lo k p)).length ≤ total ws + ws.length := fun k => by
    rw [length_frames]; have := size_sub (selW_sub ws lo k p); omega
  obtain ⟨σ4, r4, ⟨F4, c4, w4, C4, o4, p4⟩, -⟩ := FarRam.forUp_run_sum (B := W + 1) (i := "fi")
    (e := .var "fN") (body := filterBody test) (N := N)
    (fun k => 20 * ((ws.drop lo).getD k []).length + (K + 40)) I (σ := σ3)
    (by omega) (fun k _ τ hI _ => ev_var (by rw [hI.2.2.2.2.1.vars _ (hkeep "fN" (by simp)), hN])
      (by omega))
    hI0 (by
      rintro k hk τ ⟨Fτ, cτ, wτ, Cτ, oτ, pτ⟩ hfi
      have hloτ : τ.vars "flo" = lo := by rw [oτ.vars _ (hkeep "flo" (by simp)), hlo]
      have hik : lo + k < ws.length := by omega
      rw [getD_drop hik]
      set τ1 := τ.setVar "ow" (lo + k)
      have r1' : Run (W + 1) (.assign "ow" (.add (.var "flo") (.var "fi"))) τ τ1 4 :=
        (Run.assign (ev_add (ev_var hloτ (by omega)) (ev_var hfi (by omega)) (by omega))).mono
          (by simp [Expr.size])
      have o1' : OFr τ τ1 (tv ++ fV) := ofr_sub (OFr.setVar τ "ow" _) (by simp [fV])
      have wτ1 : WordsAt ws τ1 := wτ.of_arrs (by simp [τ1]) (by simp [τ1]) (by simp [τ1])
      have Cτ1 : C τ1 := hC τ τ1 Cτ o1'
      obtain ⟨τ2, r2', fb2, v2, a2, o2', i2⟩ := htest τ1 (lo + k) hik wτ1 Cτ1 (by simp [τ1])
      have o2t : OFr τ1 τ2 tv := ofr_of_test v2 a2 o2' i2
      have o12 : OFr τ τ2 (tv ++ fV) := ofr_sub (o1'.trans o2t) (fun y hy => by
        rcases List.mem_append.1 hy with h | h; exact h; exact List.mem_append_left _ h)
      have hnt : ∀ y ∈ fV, y ∉ tv := fun y hy ht => htv y ht (by simp [fV] at hy ⊢; tauto)
      have v2' : ∀ y ∈ fV, τ2.vars y = τ1.vars y := fun y hy => v2 y (hnt y hy)
      have Fτ2 : Filled "OB" "po" (pre ++ [0] ++ frames (selW ws lo k p)) τ2 :=
        Fτ.congr (by rw [v2' "po" (by simp [fV])]; simp [τ1]) (by rw [a2]; simp [τ1])
      have wτ2 : WordsAt ws τ2 := wτ1.of_arrs (by rw [a2]) (by rw [a2]) (by rw [a2])
      have hc2 : (Cond.eq (.var "fb") (.lit 1)).evalB (W + 1) τ2 = some (p ws[lo + k]) := by
        rw [evalB_condEq (ev_var fb2 (by split_ifs <;> omega)) (evalB_lit (by omega))]
        by_cases hp : p ws[lo + k] <;> simp [hp]
      have hτ2fi : τ2.vars "fi" = k := by rw [v2' "fi" (by simp [fV])]; simp [τ1, hfi]
      have hτ2fp : τ2.vars "fp" = pre.length := by rw [v2' "fp" (by simp [fV])]; simp [τ1, pτ]
      have hτ2fc : τ2.vars "fc" = (selW ws lo k p).length := by
        rw [v2' "fc" (by simp [fV])]; simp [τ1, cτ]
      have hlenτ : (τ2.arrs "OB").length = L := by rw [o12.len, oτ.len]
      have haτ : τ2.arrs "a" = σ.arrs "a" := by rw [o12.arrs _ (by decide), oτ.arrs _ (by decide)]
      have hsel1 := selW_succ (p := p) hik
      have hwl : ws[lo + k].length ≤ total ws := by
        unfold total; rw [List.length_flatten]
        exact List.le_sum_of_mem (List.mem_map_of_mem (List.getElem_mem hik))
      by_cases hp : p ws[lo + k]
      · have hlen1 := hsel (k + 1)
        rw [hsel1, if_pos hp, frames_append, frames_single] at hlen1
        simp only [List.length_append, List.length_cons, List.length_nil] at hlen1
        obtain ⟨τ3, r3', F3, o3'⟩ := cpWord_run (W := W) wτ2
          (by rw [v2' "ow" (by simp [fV])]; simp [τ1]) hik Fτ2
          (by rw [hlenτ]; simp only [List.length_append, List.length_cons, List.length_nil]; omega)
          (by simp only [List.length_append, List.length_cons, List.length_nil]; omega) (by omega)
          (hv _ (List.getElem_mem _)) (by rw [haτ]; exact ha)
        set τ4 := τ3.setVar "fc" ((selW ws lo k p).length + 1)
        have hsk := hsel k
        rw [length_frames] at hsk
        have r4' : Run (W + 1) (.assign "fc" (.add (.var "fc") (.lit 1))) τ3 τ4 4 :=
          (Run.assign (ev_add (ev_var (by rw [o3'.vars _ (by decide), hτ2fc]) (by omega))
            (evalB_lit (by omega)) (by omega))).mono (by simp [Expr.size])
        have o24 : OFr τ2 τ4 (tv ++ fV) := ofr_sub (o3'.trans (OFr.setVar τ3 "fc" _))
          (sub_fV (by decide))
        refine ⟨τ4, ?_, by simp [τ4]; rw [o3'.vars "fi" (by decide), hτ2fi], ?_⟩
        · unfold filterBody
          refine (Run.seq r1' (Run.seq r2' (Run.ite_true (by rw [hc2, hp]) (Run.seq r3' r4')))).mono ?_
          simp only [Cond.size, Expr.size]
          omega
        · have o14 : OFr τ (τ4.setVar "fi" (k + 1)) (tv ++ fV) :=
            ofr_sub ((o12.trans o24).trans (OFr.setVar τ4 "fi" (k + 1))) (fun y hy => by
              rcases List.mem_append.1 hy with h | h; exact sub_twice y h; simp only [List.mem_singleton] at h; subst h; exact List.mem_append_right _ (by decide))
          refine ⟨?_, by
              simp only [τ4, vars_setVar, show ("fc" : String) ≠ "fi" by decide, if_false, ↓reduceIte]
              rw [hsel1, if_pos hp, List.length_append, List.length_singleton], ?_, hC τ _ Cτ o14, ofr_sub (oτ.trans o14)
              sub_twice, ?_⟩
          · rw [hsel1, if_pos hp, frames_append, frames_single, ← List.append_assoc]
            exact (F3.setVar (by decide) _).setVar (by decide) _
          · exact wτ.of_arrs (by rw [o14.arrs _ (by decide)]) (by rw [o14.arrs _ (by decide)])
              (by rw [o14.arrs _ (by decide)])
          · simp [τ4]; rw [o3'.vars _ (by decide), hτ2fp]
      · refine ⟨τ2, ?_, hτ2fi, ?_⟩
        · unfold filterBody
          refine (Run.seq r1' (Run.seq r2' (Run.ite_false (by rw [hc2]; simp [hp]) Run.skip))).mono ?_
          simp only [Cond.size, Expr.size]
          omega
        · have o14 : OFr τ (τ2.setVar "fi" (k + 1)) (tv ++ fV) :=
            ofr_sub (o12.trans (OFr.setVar τ2 "fi" (k + 1)))
              (sub_app (by decide))
          refine ⟨?_, by
              simp only [vars_setVar, if_neg (show ("fc" : String) ≠ "fi" by decide)]
              rw [hsel1, if_neg hp, List.append_nil, hτ2fc], ?_, hC τ _ Cτ o14, ofr_sub (oτ.trans o14)
              sub_twice, by simp [hτ2fp]⟩
          · rw [hsel1, if_neg hp, List.append_nil]; exact Fτ2.setVar (by decide) _
          · exact wτ.of_arrs (by rw [o14.arrs _ (by decide)]) (by rw [o14.arrs _ (by decide)])
              (by rw [o14.arrs _ (by decide)]))
  -- the count
  have hlen4 : (σ4.arrs "OB").length = L := o4.len
  have hcnt : (selW ws lo N p).length ≤ ws.length := (selW_sub ws lo N p).length_le
  have hsN := hsel N
  rw [length_frames] at hsN
  have r5 : Run (W + 1) (.store "OB" (.var "fp") (.var "fc")) σ4
      (σ4.setArr "OB" pre.length (selW ws lo N p).length) 3 :=
    (Run.store (ev_var p4 (by omega)) (ev_var c4 (by omega)) (by rw [hlen4]; omega)).mono
      (by simp [Expr.size])
  have o45 : OFr σ4 (σ4.setArr "OB" pre.length (selW ws lo N p).length) [] :=
    ⟨fun _ _ => by simp, fun b hb => by simp [hb], by simp, by simp, by simp⟩
  refine ⟨_, ?_, ?_, ?_, hC σ4 _ C4 (ofr_sub o45 (by simp)), ofr_sub (o4.trans o45) (by simp)⟩
  · unfold filterCp
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 r5)))).mono ?_
    have e1 : ∑ k ∈ Finset.range N, (20 * ((ws.drop lo).getD k []).length + (K + 40) + (Expr.var "fN").size + 7) =
        20 * total ((ws.drop lo).take N) + N * (K + 48) := by
      rw [← sum_len_take, ← sum_lin]; simp only [Expr.size]; congr 1
    rw [e1]; simp only [Expr.size]
    have : N * (K + 48) ≤ N * (K + 50) := Nat.mul_le_mul_left _ (by omega)
    omega
  · rw [toWord_words]
    refine ⟨by simp [F4.pos], fun i hi => ?_⟩
    rw [← List.getElem?_eq_getElem hi]
    simp only [arrs_setArr, ↓reduceIte, List.getElem?_set]
    by_cases hip : pre.length = i
    · subst hip
      rw [if_pos rfl, if_pos (by rw [hlen4]; simp at hi; omega)]
      simp
    · rw [if_neg hip, getElem?_mid pre _ _ 0 i (Ne.symm hip)]
      have hi' : i < (pre ++ [0] ++ frames (selW ws lo N p)).length := by simp at hi ⊢; omega
      rw [F4.get i hi', ← List.getElem?_eq_getElem hi']
      simp
  · exact w4.of_arrs (by simp) (by simp) (by simp)

end Lax185574Proofs.ResolveRam.Glue
