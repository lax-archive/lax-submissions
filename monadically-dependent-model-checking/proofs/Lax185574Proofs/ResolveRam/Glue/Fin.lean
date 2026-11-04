import Lax185574Proofs.ResolveRam.Glue.R0Out

/-!
The end of a round of the glue program of lem:resolve-lift.

The round has filled the buffer `OB` with its output `o`, and for a
round with a call, the query `q` of the working slot is the segment of
length `ql` from `qa`. `finCall e d` stores the size `X` of the input of
the composite (scalar `gX`) behind the output, checks the guard on the
query followed by `X`, checks that the entries of the output are below
`W / 32 / 32` and writes the output (`finCall_run`). `finEnd` only checks
the entries and writes (`finEnd_run`). Either sets `ovf` if a check fails.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue

/-- The end of a round with a call. -/
def finCall (e d : ℕ) : Com :=
  .seq (.store "OB" (.var "po") (.var "gX")) (.seq (.assign "ql" (.add (.var "ql") (.lit 1)))
    (.seq (guardChk e d) (.seq entChk wrAll)))

/-- The end of the last round. -/
def finEnd : Com := .seq entChk wrAll

/-- The guard as the program checks it. -/
def guardOK (W e d X : ℕ) (q : List ℕ) : Prop :=
  min ((q.length + 1 + max (maxEntry q) X + 1) ^ (e + 1)) W ≤ W / min (2 ^ d) W

instance (W e d X : ℕ) (q : List ℕ) : Decidable (guardOK W e d X q) := by
  unfold guardOK; infer_instance

theorem seg_eq_of {A L : List ℕ} {a : ℕ} (h : ∀ i < L.length, A[a + i]? = L[i]?) :
    seg A a L.length = L := by
  apply List.ext_getElem?
  intro i
  simp only [seg, List.getElem?_take, List.getElem?_drop]
  split_ifs with hi
  · exact h i hi
  · rw [List.getElem?_eq_none (by omega)]

theorem maxEntry_append_X (q : List ℕ) (X : ℕ) : maxEntry (q ++ [X]) = max (maxEntry q) X :=
  maxEntry_append_single q X

/-- **The end of a round with a call.** -/
theorem finCall_run {W e d X : ℕ} {σ : Env} {pre q : List ℕ} (hW : σ.vars "W" = W) (hW32 : 32 ≤ W)
    (hF : Filled "OB" "po" (pre ++ q) σ) (hqa : σ.vars "qa" = pre.length) (hql : σ.vars "ql" = q.length)
    (hgX : σ.vars "gX" = X) (hcap : (σ.arrs "OB").length = W + 1) (hlen : (pre ++ q).length + 1 ≤ W)
    (hv : ∀ v ∈ pre ++ q, v ≤ W) (hX : X ≤ W) (hovf : σ.vars "ovf" = 0) :
    ∃ σ', Run (W + 1) (finCall e d) σ σ'
        ((pre ++ q).length * 72 + 60 * (e + 1) + 30 * 2 ^ d + 400) ∧
      σ'.out = σ.out ++ (pre ++ q) ∧
      σ'.vars "ovf" = (if guardOK W e d X q ∧ maxEntry (pre ++ q) < W / 32 / 32 then 0 else 1) := by
  set o := pre ++ q
  have hol : o.length = pre.length + q.length := by simp [o]
  have hpo : σ.vars "po" = o.length := hF.pos
  have hlo : o.length < (σ.arrs "OB").length := by omega
  -- store X behind the output
  set σ1 := σ.setArr "OB" o.length X
  have r1 : Run (W + 1) (.store "OB" (.var "po") (.var "gX")) σ σ1 3 :=
    Run.store (ev_var hpo (by omega)) (ev_var hgX (by omega)) hlo
  have hF1 : ∀ i, i < o.length + 1 → (σ1.arrs "OB")[i]? = (o ++ [X])[i]? := by
    intro i hi
    simp only [σ1, arrs_setArr, ↓reduceIte, List.getElem?_set]
    rcases Nat.lt_or_ge i o.length with h | h
    · rw [if_neg (by omega), hF.get i h, List.getElem?_append_left h, List.getElem?_eq_getElem h]
    · obtain rfl : i = o.length := by omega
      rw [if_pos rfl, if_pos hlo]; simp
  set σ2 := σ1.setVar "ql" (q.length + 1)
  have r2 : Run (W + 1) (.assign "ql" (.add (.var "ql") (.lit 1))) σ1 σ2 4 :=
    (Run.assign (ev_add (ev_var (by simp [σ1, hql]) (by simp at hlen; omega)) (evalB_lit (by omega))
      (by simp at hlen; omega))).mono (by simp [Expr.size])
  have hseg : seg (σ2.arrs "OB") pre.length (q.length + 1) = q ++ [X] := by
    have := seg_eq_of (A := σ2.arrs "OB") (L := q ++ [X]) (a := pre.length) (fun i hi => by
      simp only [List.length_append, List.length_cons, List.length_nil] at hi
      simp only [σ2, arrs_setVar]
      rw [hF1 _ (by omega), show o ++ [X] = pre ++ (q ++ [X]) by simp [o],
        List.getElem?_append_right (by omega), Nat.add_sub_cancel_left])
    simpa using this
  have hlen2 : (σ2.arrs "OB").length = W + 1 := by simp [σ2, σ1, hcap]
  obtain ⟨σ3, r3, h3, f3, a3, o3, i3⟩ := guardChk_run (W := W) (e := e) (d := d) (a := pre.length)
    (N := q.length + 1) (σ := σ2) (by simp [σ2, σ1, hW]) (by omega) (by simp [σ2, σ1, hqa])
    (by simp [σ2]) (by rw [hlen2]; simp [o] at hlen; omega) (by simp [o] at hlen; omega)
    (by rw [hseg]; intro v hv'; rcases List.mem_append.1 hv' with h | h
        · exact hv v (List.mem_append_right _ h)
        · simp at h; omega)
  simp only [hseg, maxEntry_append_X, List.length_append, List.length_cons, List.length_nil] at h3
  have hW3 : σ3.vars "W" = W := by rw [f3 _ (by decide)]; simp [σ2, σ1, hW]
  have hF3 : Filled "OB" "po" o σ3 := by
    refine ⟨by rw [f3 _ (by decide)]; simp [σ2, σ1, hpo], fun i hi => ?_⟩
    rw [a3]; simp only [σ2, arrs_setVar]
    rw [hF1 i (by omega), List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
  obtain ⟨σ4, r4, h4, f4, a4, o4, i4⟩ := entChk_run (o := o) hW3 hW32 hF3 (by omega) hv
  have hF4 : Filled "OB" "po" o σ4 := hF3.congr (f4 _ (by decide)) (by rw [a4])
  obtain ⟨σ5, r5, ho5⟩ := wrAll_run (B := W + 1) hF4 (by omega) (fun v hv' => by have := hv v hv'; omega)
  have hov5 : σ5.vars "ovf" = σ4.vars "ovf" := r5.frame_var _ (by simp [wrAll, forUp, Com.wvars])
  refine ⟨σ5, ?_, ?_, ?_⟩
  · unfold finCall
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 r5)))).mono ?_
    omega
  · rw [ho5, o4, o3]; simp [σ2, σ1]
  · rw [hov5, h4, h3]
    have h2o : σ2.vars "ovf" = 0 := by simp [σ2, σ1, hovf]
    rw [h2o]
    unfold guardOK
    by_cases hg : min ((q.length + 1 + max (maxEntry q) X + 1) ^ (e + 1)) W ≤ W / min (2 ^ d) W <;>
      by_cases he : maxEntry o < W / 32 / 32 <;> simp [hg, he]

/-- **The end of the last round.** -/
theorem finEnd_run {W : ℕ} {σ : Env} {o : List ℕ} (hW : σ.vars "W" = W) (hW32 : 32 ≤ W)
    (hF : Filled "OB" "po" o σ) (hlen : o.length + 1 ≤ W) (hv : ∀ v ∈ o, v ≤ W)
    (hovf : σ.vars "ovf" = 0) :
    ∃ σ', Run (W + 1) finEnd σ σ' (o.length * 42 + 36) ∧ σ'.out = σ.out ++ o ∧
      σ'.vars "ovf" = (if maxEntry o < W / 32 / 32 then 0 else 1) := by
  obtain ⟨σ4, r4, h4, f4, a4, o4, i4⟩ := entChk_run (o := o) hW hW32 hF (by omega) hv
  have hF4 : Filled "OB" "po" o σ4 := hF.congr (f4 _ (by decide)) (by rw [a4])
  obtain ⟨σ5, r5, ho5⟩ := wrAll_run (B := W + 1) hF4 (by omega) (fun v hv' => by have := hv v hv'; omega)
  have hov5 : σ5.vars "ovf" = σ4.vars "ovf" := r5.frame_var _ (by simp [wrAll, forUp, Com.wvars])
  refine ⟨σ5, (Run.seq r4 r5).mono (by omega), by rw [ho5, o4], ?_⟩
  rw [hov5, h4, hovf]

end Lax185574Proofs.ResolveRam.Glue
