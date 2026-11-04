import Lax185574Proofs.FarRam.ScanSel
import Lax185574Proofs.Words.Emit


/-!
The output of the far-tree program: `0`, the number of selected entries,
and the frames of their trees, in the order of the entries.
-/

namespace Lax185574Proofs.FarRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.EvalRam
open Lax185574.WordEncoding

/-- Write the frame of the tree of entry `zs`. -/
def writeNu : Com :=
  .seq (.assign "pa" (.add (.get "st" (.var "zs")) (.lit 1)))
    (.seq (.assign "la" (.sub (.get "ln" (.var "zs")) (.lit 2))) (.seq (.write (.var "la"))
      (.seq (.assign "k" (.lit 0)) (.while (.lt (.var "k") (.var "la")) writeEntry))))

theorem writeNu_run {B : ℕ} {W : List (List ℕ)} {σ : Env} (hw : WordsAt W σ) (hb : WordsBound B W)
    {i : ℕ} (hi : σ.vars "zs" = i) (hil : i < W.length) (h2 : 2 ≤ W[i].length) :
    ∃ σ', Run B writeNu σ σ' (13 * W[i].length + 30) ∧
      σ'.out = σ.out ++ ((nuPart W[i]).length :: nuPart W[i]) ∧
      ∀ z, z ∉ ["pa", "la", "k"] → σ'.vars z = σ.vars z := by
  have hoi := off_add_le hil
  have hlen := hb.len
  set u := nuPart W[i] with hu
  have hul : u.length = W[i].length - 2 := by simp [hu, nuPart]; omega
  have hea : ∀ k (h : k < u.length), (σ.arrs "a")[off W i + 1 + k]? = some u[k] :=
    fun k hk => nuPart_entries hw hil k hk
  have hent : ∀ x ∈ u, x < B := fun x hx => hb.ent _ (List.getElem_mem hil) x
    (List.mem_of_mem_drop (List.mem_of_mem_take hx))
  set σ0 : Env := { ((σ.setVar "pa" (off W i + 1)).setVar "la" u.length) with
    out := σ.out ++ [u.length] } with hσ0
  let I : Env → Prop := fun τ => τ.vars "pa" = off W i + 1 ∧ τ.vars "la" = u.length ∧
    τ.vars "k" ≤ u.length ∧ τ.arrs "a" = σ.arrs "a" ∧
    τ.out = σ.out ++ (u.length :: u.take (τ.vars "k")) ∧ ∀ z, z ∉ ["pa", "la", "k"] → τ.vars z = σ.vars z
  obtain ⟨σ', hloop, ⟨hpa, hla, hkle, ha, hout, hfv⟩, hfalse⟩ :=
    Run.while_count (B := B) (b := .lt (.var "k") (.var "la")) (c := writeEntry) I
      (fun τ => u.length - τ.vars "k") 9
      (fun τ ⟨_, hla, hkle, _⟩ => evalB_condLt_vars (by omega) (by rw [hla]; omega))
      (by
        rintro τ ⟨hpa, hla, hkle, ha, hout, hfv⟩ hc
        have hk : τ.vars "k" < u.length := by
          have := lt_of_condLt_true hc; rwa [hla] at this
        have hget : (τ.arrs "a")[off W i + 1 + τ.vars "k"]? = some u[τ.vars "k"] := by
          rw [ha]; exact hea _ hk
        refine ⟨_, Run.seq (Run.write (v := u[τ.vars "k"]) ?_) (Run.assign (v := τ.vars "k" + 1) ?_),
          ⟨by simp [hpa], by simp [hla], by simp; omega, by simp [ha], ?_, fun z hz => ?_⟩, by simp; omega⟩
        · simp only [evalB_get_iff, evalB_bin_iff, evalB_var_iff, hpa]
          exact ⟨_, ⟨_, _, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by simp only [Bop.apply_add]; omega⟩,
            hget, hent _ (List.getElem_mem hk)⟩
        · simp; omega
        · simp only [vars_setVar, if_true]
          rw [hout, List.take_add_one, List.getElem?_eq_getElem hk]
          simp
        · simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
          simp [vars_setVar, hz.2.2, hfv z (by simp [hz.1, hz.2.1, hz.2.2])])
      (show I (σ0.setVar "k" 0) by
        refine ⟨by simp [hσ0], by simp [hσ0], by simp, by simp [hσ0], by simp [hσ0], fun z hz => ?_⟩
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hz
        simp [hσ0, vars_setVar, hz.1, hz.2.1, hz.2.2])
  have hku : σ'.vars "k" = u.length := by
    have := le_of_condLt_false hfalse; rw [hla] at this; omega
  refine ⟨σ', ?_, by rw [hout, hku, List.take_length], hfv⟩
  unfold writeNu
  refine (Run.seq (Run.assign (v := off W i + 1) ?_) (Run.seq (Run.assign (v := u.length) ?_)
    (Run.seq (Run.write (v := u.length) ?_) (Run.seq (Run.assign (v := 0) ?_) hloop)))).mono ?_
  · simp only [evalB_bin_iff, evalB_get_iff, evalB_var_iff, evalB_lit_iff, hi]
    exact ⟨off W i, 1, ⟨i, ⟨rfl, by omega⟩, hw.st i hil, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩
  · simp only [evalB_bin_iff, evalB_get_iff, evalB_var_iff, evalB_lit_iff, vars_setVar, arrs_setVar]
    exact ⟨W[i].length, 2, ⟨i, ⟨by simp [hi], by simp [hi]; omega⟩, hw.ln i hil, by omega⟩,
      ⟨rfl, by omega⟩, by simp [hul, Bop.apply], by omega⟩
  · simp; omega
  · simp; omega
  · simp; omega

def cntSel : Com :=
  .seq (.assign "zm" (.lit 0))
    (forUp "zs" (.var "ns") (.assign "zm" (.add (.var "zm") (.get "sel" (.var "zs")))))

def outBody : Com := .ite (.eq (.get "sel" (.var "zs")) (.lit 1)) writeNu .skip

def outPhase : Com :=
  .seq cntSel (.seq (.write (.lit 0)) (.seq (.write (.var "zm")) (forUp "zs" (.var "ns") outBody)))

/-- The words written: the trees of the selected entries. -/
def outList (W : List (List ℕ)) (sl : ℕ → Bool) (n : ℕ) : List (List ℕ) :=
  ((List.range n).filter sl).map fun i => nuPart (wd W i)

theorem outList_succ (W : List (List ℕ)) (sl : ℕ → Bool) (n : ℕ) :
    outList W sl (n + 1) = outList W sl n ++ (if sl n then [nuPart (wd W n)] else []) := by
  simp only [outList, List.range_succ, List.filter_append, List.map_append]
  cases h : sl n <;> simp [h]

def outCost (W : List (List ℕ)) (nS : ℕ) : ℕ :=
  nS * 16 + (∑ i ∈ Finset.range nS, (13 * (wd W i).length + 48)) + 30

/-- **The output.** -/
theorem outPhase_spec (B : ℕ) (W : List (List ℕ)) (nS : ℕ) (sl : ℕ → Bool) (σ : Env)
    (hw : WordsAt W σ) (hb : WordsBound B W) (hns : σ.vars "ns" = nS) (hnW : nS ≤ W.length)
    (hsel : ∀ i < nS, (σ.arrs "sel")[i]? = some (bv (sl i))) (h2 : ∀ i < nS, 2 ≤ (wd W i).length)
    (hB : nS + 2 < B) :
    ∃ σ', Run B outPhase σ σ' (outCost W nS) ∧
      σ'.out = σ.out ++ 0 :: toWord (outList W sl nS) := by
  have hlen := hb.len
  -- the count
  obtain ⟨σ1, r1, ⟨hns1, hzm1, ha1, ho1⟩, -⟩ := forUp_run (B := B) (i := "zs") (e := .var "ns")
    (body := .assign "zm" (.add (.var "zm") (.get "sel" (.var "zs")))) (N := nS) (K := 8)
    (fun k τ => τ.vars "ns" = nS ∧ τ.vars "zm" = (outList W sl k).length ∧ τ.arrs = σ.arrs ∧
      τ.out = σ.out) (σ := σ.setVar "zm" 0) (by omega)
    (fun k _ τ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.1.symm, by rw [hI.1]; omega⟩)
    ⟨by simp [hns], by simp [outList], by simp, by simp⟩
    (fun k hk τ ⟨hn, hzm, ha, ho⟩ hzs => by
      have hl : (outList W sl k).length ≤ k := by
        simp only [outList, List.length_map]
        have := List.length_filter_le sl (List.range k); simpa using this
      refine ⟨τ.setVar "zm" ((outList W sl k).length + bv (sl k)), (Run.assign ?_).mono (by simp),
        by simp [hzs], by simp [hn], ?_, by simp [ha], by simp [ho]⟩
      · simp only [evalB_bin_iff, evalB_var_iff, evalB_get_iff]
        refine ⟨_, _, ⟨hzm.symm, by omega⟩, ⟨k, ⟨hzs.symm, by omega⟩, by rw [ha]; exact hsel k hk,
          by have := bv_le (sl k); omega⟩, rfl, by have := bv_le (sl k); omega⟩
      · simp only [vars_setVar, if_true, outList_succ, List.length_append]
        cases sl k <;> simp [bv])
  have hzmB : σ1.vars "zm" < B := by
    rw [hzm1]
    have : (outList W sl nS).length ≤ nS := by
      simp only [outList, List.length_map]
      have := List.length_filter_le sl (List.range nS); simpa using this
    omega
  set σ2 : Env := { ({ σ1 with out := σ1.out ++ [0] } : Env) with
    out := σ1.out ++ [0] ++ [(outList W sl nS).length] }
  -- the frames
  obtain ⟨σ3, r3, ⟨hw3, hns3, hsel3, hout3⟩, -⟩ := forUp_run_sum (B := B) (i := "zs") (e := .var "ns")
    (body := outBody) (N := nS) (fun i => 13 * (wd W i).length + 40)
    (fun k τ => WordsAt W τ ∧ τ.vars "ns" = nS ∧ τ.arrs "sel" = σ.arrs "sel" ∧
      τ.out = σ2.out ++ frames (outList W sl k)) (σ := σ2) (by omega)
    (fun k _ τ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.2.1.symm, by rw [hI.2.1]; omega⟩)
    ⟨hw.of_arrs (by simp [σ2, ha1]) (by simp [σ2, ha1]) (by simp [σ2, ha1]), by simp [σ2, hns1],
      by simp [σ2, ha1], by simp [σ2, outList, frames]⟩
    (fun k hk τ ⟨hwτ, hn, hs, ho⟩ hzs => by
      have hkW : k < W.length := by omega
      have hc : (Cond.eq (.get "sel" (.var "zs")) (.lit 1)).evalB B τ = some (sl k) :=
        evalB_bit (by simp only [evalB_var_iff]; exact ⟨hzs.symm, by omega⟩) (by rw [hs]; exact hsel k hk)
          (by omega)
      by_cases hsk : sl k = true
      · obtain ⟨τ', hr', hout', hfv'⟩ := writeNu_run hwτ hb hzs hkW (by have := h2 k hk; rwa [wd_eq hkW] at this)
        have hfa : ∀ a, τ'.arrs a = τ.arrs a := fun a => hr'.frame_arr a (by simp [writeNu, writeEntry, Com.warrs])
        refine ⟨τ', (Run.ite_true (by rw [hc, hsk]) hr').mono ?_, by rw [hfv' "zs" (by decide), hzs],
          hwτ.of_arrs (by simp [hfa]) (by simp [hfa]) (by simp [hfa]), by simp [hfv' "ns" (by decide), hn],
          by simp [hfa, hs], ?_⟩
        · rw [wd_eq hkW]; simp only [Cond.size, Expr.size]; omega
        · simp only [out_setVar]
          rw [hout', ho, outList_succ, if_pos hsk, frames_append, wd_eq hkW]
          simp [frames]
      · have hsk' : sl k = false := by simpa using hsk
        refine ⟨τ, (Run.ite_false (by rw [hc, hsk']) Run.skip).mono (by simp), hzs,
          hwτ.of_arrs (by simp) (by simp) (by simp),
          by simp [hn], by simp [hs], ?_⟩
        simp [ho, outList_succ, hsk'])
  have r3' : Run B (forUp "zs" (.var "ns") outBody) σ2 σ3
      ((∑ i ∈ Finset.range nS, (13 * (wd W i).length + 48)) + 6) := by
    refine r3.mono (le_of_eq ?_)
    simp only [Expr.size]
  refine ⟨σ3, ?_, ?_⟩
  · unfold outPhase cntSel
    refine (Run.seq (Run.seq (Run.assign (evalB_lit (by omega))) r1) (Run.seq (Run.write (evalB_lit (by omega)))
      (Run.seq (Run.write (v := (outList W sl nS).length) ?_) r3'))).mono ?_
    · simp only [evalB_var_iff]; exact ⟨hzm1.symm, hzmB⟩
    · simp only [outCost, Expr.size]
      omega
  · rw [hout3, toWord_words]; simp [σ2, ho1]

end Lax185574Proofs.FarRam
