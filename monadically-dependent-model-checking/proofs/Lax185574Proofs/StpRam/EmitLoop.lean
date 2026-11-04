import Lax185574Proofs.StpRam.Emit

/-!
The loops over radii and sorted words that write the triples of the
scatter type, and the same loops counting them.

For `er = 0, …, R1 − 1` the radius is `gr = er + 1`. For every index
`es` below `cnt` the word `u` of index `ord[es]` is the next sorted
distinct word, its level is `u₀ − k`, and if `gr` is at most the radius
bound `rt[u₀ − k]` of the level, the value is computed by `greedyCmd`
and the triple is written by `emitTriple`.
-/

namespace Lax185574Proofs.StpRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib
open Lax185574Proofs.Words

/-- The words written for the radius `r`. -/
def emitR {n : ℕ} (adj : Fin n → List (Fin n)) (A : List (List ℕ)) (k q r : ℕ) : List (List ℕ) :=
  ((sortedDistinct A).filter fun u => r ≤ radius k q (u.headD 0 - k)).map (triple adj A k q r)

/-- The words written for the radius `r` and the first `s` sorted words. -/
def emitRk {n : ℕ} (adj : Fin n → List (Fin n)) (A : List (List ℕ)) (k q r s : ℕ) :
    List (List ℕ) :=
  (((sortedDistinct A).take s).filter fun u => r ≤ radius k q (u.headD 0 - k)).map
    (triple adj A k q r)

/-- The words written for the first `j` radii. -/
def emitPre {n : ℕ} (adj : Fin n → List (Fin n)) (A : List (List ℕ)) (k q j : ℕ) :
    List (List ℕ) :=
  (List.range j).flatMap fun r' => emitR adj A k q (r' + 1)

theorem emitPre_full {n : ℕ} (adj : Fin n → List (Fin n)) (A : List (List ℕ)) (k q : ℕ) :
    emitPre adj A k q (radius k q 1) = emitList adj A k q := rfl

theorem emitPre_succ {n : ℕ} (adj : Fin n → List (Fin n)) (A : List (List ℕ)) (k q j : ℕ) :
    emitPre adj A k q (j + 1) = emitPre adj A k q j ++ emitR adj A k q (j + 1) := by
  simp [emitPre, List.range_succ, List.flatMap_append]

theorem emitRk_full {n : ℕ} (adj : Fin n → List (Fin n)) (A : List (List ℕ)) (k q r : ℕ) :
    emitRk adj A k q r (sortedDistinct A).length = emitR adj A k q r := by
  simp [emitRk, emitR]

theorem emitRk_succ {n : ℕ} (adj : Fin n → List (Fin n)) (A : List (List ℕ)) (k q r s : ℕ)
    (hs : s < (sortedDistinct A).length) :
    emitRk adj A k q r (s + 1) = emitRk adj A k q r s ++
      (if r ≤ radius k q ((sortedDistinct A)[s].headD 0 - k) then
        [triple adj A k q r (sortedDistinct A)[s]] else []) := by
  simp only [emitRk, List.take_add_one, List.getElem?_eq_getElem hs, Option.toList_some,
    List.filter_append, List.map_append]
  congr 1
  by_cases h : r ≤ radius k q ((sortedDistinct A)[s].headD 0 - k)
  · rw [if_pos h, List.filter_cons_of_pos (by simpa using h)]; rfl
  · rw [if_neg h, List.filter_cons_of_neg (by simpa using h)]; rfl

theorem frames_append' (l l' : List (List ℕ)) : frames (l ++ l') = frames l ++ frames l' := by
  simp [frames]

theorem length_triple {n : ℕ} (adj : Fin n → List (Fin n)) (A : List (List ℕ)) (k q r : ℕ)
    (u : List ℕ) : (triple adj A k q r u).length = u.length + 2 := by
  simp [triple]

/-- The context of the loops. -/
def ECtx (A : List (List ℕ)) (n nsE nsN : ℕ) (oE tE oN tN g : ℕ → ℕ) (k q R1 : ℕ) (τ : Env) : Prop :=
  GraphAt n nsE nsN oE tE oN tN τ ∧ WordsAt A τ ∧ τ.vars "kk" = k ∧ τ.vars "cap" = k + q ∧
    τ.vars "R1" = R1 ∧ τ.vars "cnt" = (sortedDistinct A).length ∧
    (∀ s < (sortedDistinct A).length, (τ.arrs "ord").getD s 0 < A.length ∧
      wd A ((τ.arrs "ord").getD s 0) = (sortedDistinct A).getD s []) ∧
    τ.arrs "rt" = arrOf (q + 1) (radius k q) ∧ τ.arrs "dd" = arrOf (n * n) g ∧
    (τ.arrs "dn").length = n ∧ (τ.arrs "bl").length = n ∧
    (sortedDistinct A).length ≤ (τ.arrs "ord").length

theorem ECtx.of_eq {A : List (List ℕ)} {n nsE nsN : ℕ} {oE tE oN tN g : ℕ → ℕ} {k q R1 : ℕ}
    {τ τ' : Env} (h : ECtx A n nsE nsN oE tE oN tN g k q R1 τ)
    (hv : ∀ x ∈ ["n", "kk", "cap", "R1", "cnt"], τ'.vars x = τ.vars x)
    (ha : ∀ x ∈ ["eo", "et", "no", "nt", "a", "st", "ln", "ord", "rt", "dd"], τ'.arrs x = τ.arrs x)
    (hl : ∀ x ∈ ["dn", "bl"], (τ'.arrs x).length = (τ.arrs x).length) :
    ECtx A n nsE nsN oE tE oN tN g k q R1 τ' := by
  obtain ⟨hG, hw, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  refine ⟨hG.of_arrs (hv "n" (by simp)) (ha "eo" (by simp)) (ha "et" (by simp)) (ha "no" (by simp))
      (ha "nt" (by simp)),
    hw.of_arrs (ha "a" (by simp)) (ha "st" (by simp)) (ha "ln" (by simp)),
    by rw [hv "kk" (by simp), h1], by rw [hv "cap" (by simp), h2], by rw [hv "R1" (by simp), h3],
    by rw [hv "cnt" (by simp), h4], by rw [ha "ord" (by simp)]; exact h5, by rw [ha "rt" (by simp), h6],
    by rw [ha "dd" (by simp), h7], by rw [hl "dn" (by simp), h8], by rw [hl "bl" (by simp), h9],
    by rw [ha "ord" (by simp)]; exact h10⟩

/-- The step of the inner loop. -/
def innerBody : Com :=
  .seq (.assign "gu" (.get "ord" (.var "es")))
    (.seq (.assign "gi" (.sub (.get "a" (.get "st" (.var "gu"))) (.var "kk")))
      (.ite (.lt (.get "rt" (.var "gi")) (.var "gr")) .skip (.seq greedyCmd emitTriple)))

/-- What the loops need of the list `A` of tree words. -/
structure AFacts (A : List (List ℕ)) (n k q L : ℕ) : Prop where
  len : A.length = q * n
  head : ∀ u ∈ A, k + 1 ≤ u.headD 0 ∧ u.headD 0 ≤ k + q
  ne : ∀ u ∈ A, u ≠ []
  maxl : ∀ u ∈ A, u.length ≤ L

/-- The cost bound of one step of the inner loop. -/
def innerCost (n L c : ℕ) : ℕ := greedyCost n L c + 13 * L + 60

set_option maxHeartbeats 1000000 in
/-- **A step of the inner loop.** -/
theorem innerBody_run {B n nsE nsN k q R1 L : ℕ} {oE tE oN tN g : ℕ → ℕ} {A : List (List ℕ)}
    {adj : Fin n → List (Fin n)} (hD : ∀ (s v : Fin n) (r : ℕ), DT g n s v r ↔ v ∈ Lax185574Proofs.TreeAlgo.ballFrom adj s r)
    (hF : AFacts A n k q L) (hb : WordsBound B A) (hR1 : R1 = radius k q 1)
    (hnB : n + 2 < B) (hnnB : n * n < B) (hgB : ∀ j < n * n, g j < B) (hRB : R1 + 1 < B)
    (hcB : k + q + 1 < B)
    (htB : total A + 3 < B)
    {σ : Env} (hC : ECtx A n nsE nsN oE tE oN tN g k q R1 σ) {s r : ℕ}
    (hs : σ.vars "es" = s) (hsl : s < (sortedDistinct A).length) (hr : σ.vars "gr" = r)
    (hr1 : 1 ≤ r) (hrR : r ≤ R1) :
    ∃ σ', Run B innerBody σ σ' (innerCost n L (k + q)) ∧
      ECtx A n nsE nsN oE tE oN tN g k q R1 σ' ∧ σ'.vars "es" = s ∧ σ'.vars "gr" = r ∧
      σ'.out = σ.out ++ frames (if r ≤ radius k q ((sortedDistinct A)[s].headD 0 - k) then
        [triple adj A k q r (sortedDistinct A)[s]] else []) := by
  obtain ⟨hG, hw, hkk, hcap, hR, hcnt, hord, hrt, hdm, hdn, hbl, hol⟩ := hC
  have hlen := hb.len
  set SD := sortedDistinct A with hSD
  have hSDA : SD.length ≤ A.length := length_sortedDistinct_le A
  obtain ⟨hoA, hwo⟩ := hord s hsl
  set ui := (σ.arrs "ord").getD s 0 with hui
  have hu : A[ui] = SD[s] := by rw [← wd_eq hoA, hwo, List.getD_eq_getElem _ _ hsl]
  have huA : A[ui] ∈ A := List.getElem_mem hoA
  obtain ⟨hk1, hkq⟩ := hF.head _ huA
  have hne := hF.ne _ huA
  obtain ⟨x, xs, hxs⟩ : ∃ x xs, A[ui] = x :: xs := List.exists_cons_of_ne_nil hne
  have hhead : A[ui].headD 0 = x := by rw [hxs]; rfl
  set lev := x - k with hlev
  have hlev1 : 1 ≤ lev := by omega
  have hlevq : lev ≤ q := by omega
  have hrad : radius k q lev ≤ R1 := by rw [hR1]; exact radius_le_one k q lev hlev1 hlevq
  have hxB : x < B := hb.ent _ huA x (by rw [hxs]; simp)
  -- the two assignments
  set τ1 := σ.setVar "gu" ui with hτ1
  have hords : (σ.arrs "ord")[s]? = some ui := by
    rw [hui, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
  have r1 : Run B (.assign "gu" (.get "ord" (.var "es"))) σ τ1 3 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_get_iff, evalB_var_iff]
    exact ⟨s, ⟨hs.symm, by omega⟩, hords, by omega⟩
  set τ2 := τ1.setVar "gi" lev with hτ2
  have hent0 : (σ.arrs "a")[off A ui]? = some x := by
    have := hw.a ui hoA 0 (by rw [hxs]; simp)
    rw [Nat.add_zero] at this
    rw [this]; simp [hxs]
  have r2 : Run B (.assign "gi" (.sub (.get "a" (.get "st" (.var "gu"))) (.var "kk"))) τ1 τ2 6 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_get_iff, evalB_var_iff]
    refine ⟨x, k, ⟨off A ui, ⟨ui, ⟨by simp [hτ1], by simp [hτ1]; omega⟩, by
        simp only [hτ1, arrs_setVar]; exact hw.st ui hoA, by have := off_add_le hoA; omega⟩,
        by simp only [hτ1, arrs_setVar]; exact hent0, hxB⟩,
      ⟨by simp [hτ1, hkk], by simp [hτ1, hkk]; omega⟩, by simp [Bop.apply, hlev], by omega⟩
  have hrtv : (τ2.arrs "rt")[lev]? = some (radius k q lev) := by
    simp only [hτ2, hτ1, arrs_setVar, hrt]; exact getElem?_arrOf _ (by omega)
  have hgr2 : τ2.vars "gr" = r := by simp [hτ2, hτ1, hr]
  have he1 : (Expr.get "rt" (.var "gi")).evalB B τ2 = some (radius k q lev) := by
    simp only [evalB_get_iff, evalB_var_iff]
    exact ⟨lev, ⟨by simp [hτ2], by simp [hτ2]; omega⟩, hrtv, by omega⟩
  have he2 : (Expr.var "gr").evalB B τ2 = some r := by
    simp only [evalB_var_iff]; exact ⟨hgr2.symm, by rw [hgr2]; omega⟩
  have hcond := evalB_condLt he1 he2
  have hlevS : SD[s].headD 0 - k = lev := by rw [← hu, hhead]
  have hC2 : ECtx A n nsE nsN oE tE oN tN g k q R1 τ2 :=
    ECtx.of_eq (τ := σ) ⟨hG, hw, hkk, hcap, hR, hcnt, hord, hrt, hdm, hdn, hbl, hol⟩
      (fun x hx => by simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [hτ2, hτ1])
      (fun x hx => by simp [hτ2, hτ1])
      (fun x hx => by simp [hτ2, hτ1])
  have hsize : (Cond.lt (.get "rt" (.var "gi")) (.var "gr")).size = 4 := rfl
  by_cases hlt : radius k q lev < r
  · -- the radius is above the bound of the level
    refine ⟨τ2, (Run.seq r1 (Run.seq r2 (Run.ite_true (by rw [hcond]; simp [hlt]) Run.skip))).mono ?_,
      hC2, by simp [hτ2, hτ1, hs], by simp [hτ2, hτ1, hr], ?_⟩
    · simp only [innerCost, hsize]; omega
    · rw [hlevS, if_neg (by omega)]; simp [hτ2, hτ1, frames]
  -- the value
  obtain ⟨hG2, hw2, -, -, -, -, -, -, hdm2, hdn2, hbl2, -⟩ := hC2
  obtain ⟨τ3, r3, hgc3, hG3, hw3⟩ := greedyCmd_run (B := B) (i := lev) (r := r) (ui := ui)
    (c := k + q) (L := L) hG2 hw2 hb hnB hnnB hgB (by omega) hcB hlev1
    (by rw [hF.len]; have : (lev - 1) * n + n = lev * n := by
          rcases lev with _ | l
          · omega
          · simp [Nat.add_mul]
        rw [this]; exact Nat.mul_le_mul_right _ hlevq) hoA hF.maxl
    (by simp [hτ2]) hgr2 (by simp [hτ2, hτ1]) (by simp [hτ2, hτ1, hcap]) hdm2 hdn2 hbl2
  have hgcv : τ3.vars "gc" = min (greedyW adj A lev r SD[s]).length (k + q) := by
    rw [hgc3, length_greedyN_eq_D hD, wd_eq hoA, hu]
  have hf3 : ∀ x, x ∉ greedyCmd.wvars → τ3.vars x = τ2.vars x := fun x hx => r3.frame_var x hx
  have ha3 : ∀ x, x ∉ greedyCmd.warrs → τ3.arrs x = τ2.arrs x := fun x hx => r3.frame_arr x hx
  have hgu3 : τ3.vars "gu" = ui := by rw [hf3 "gu" (by decide)]; simp [hτ2, hτ1]
  have hgr3 : τ3.vars "gr" = r := by rw [hf3 "gr" (by decide), hgr2]
  have hvalB : min (greedyW adj A lev r SD[s]).length (k + q) < B := by omega
  obtain ⟨τ4, r4, hout4⟩ := emitTriple_run hw3 hb hgu3 hoA hgr3 (by omega) hgcv hvalB htB
  have hf4 : ∀ x, x ∉ emitTriple.wvars → τ4.vars x = τ3.vars x := fun x hx => r4.frame_var x hx
  have ha4 : ∀ x, x ∉ emitTriple.warrs → τ4.arrs x = τ3.arrs x := fun x hx => r4.frame_arr x hx
  have hl3 := run_length_arrs r3
  have hl4 := run_length_arrs r4
  refine ⟨τ4, (Run.seq r1 (Run.seq r2 (Run.ite_false (by rw [hcond]; simp [hlt])
    (Run.seq r3 r4)))).mono ?_, ?_, ?_, ?_, ?_⟩
  · have hlu : A[ui].length ≤ L := hF.maxl _ huA
    simp only [innerCost, hsize]; omega
  · refine ECtx.of_eq (τ := σ) ⟨hG, hw, hkk, hcap, hR, hcnt, hord, hrt, hdm, hdn, hbl, hol⟩ ?_ ?_ ?_
    · intro x hx; simp at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl <;>
        (rw [hf4 _ (by decide), hf3 _ (by decide)]; simp [hτ2, hτ1])
    · intro x hx; simp at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (rw [ha4 _ (by decide), ha3 _ (by decide)]; simp [hτ2, hτ1])
    · intro x hx; rw [hl4, hl3]; simp [hτ2, hτ1]
  · rw [hf4 "es" (by decide), hf3 "es" (by decide)]; simp [hτ2, hτ1, hs]
  · rw [hf4 "gr" (by decide), hgr3]
  · rw [hout4, r3.out_eq (by decide)]
    rw [hlevS, if_pos (by omega)]
    simp only [hτ2, hτ1, out_setVar, frames, List.map_cons, List.map_nil, List.flatten_cons,
      List.flatten_nil, List.append_nil, triple]
    rw [hlevS, hu]
    simp only [List.cons_append, List.length_cons, List.length_append, List.length_singleton, List.cons.injEq, List.append_cancel_left_eq]
    exact ⟨by simp only [List.length_nil]; rfl, trivial, rfl⟩

end Lax185574Proofs.StpRam
