import Lax185574Proofs.Words.Compare

/-!
Writing a word held in the arrays of `Lax185574Proofs.Words.Read`.

The command `writeWord` writes the frame of word `ow`, its length
followed by its entries, to the output tape. It uses the scalars `pa`,
`la` and `k`, and writes no array.
-/

namespace Lax185574Proofs.Words

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- Write one entry of the word and advance `k`. -/
def writeEntry : Com :=
  .seq (.write (.get "a" (.add (.var "pa") (.var "k")))) (.assign "k" (.add (.var "k") (.lit 1)))

/-- Write the frame of word `ow`. -/
def writeWord : Com :=
  .seq (.assign "pa" (.get "st" (.var "ow"))) (.seq (.assign "la" (.get "ln" (.var "ow")))
    (.seq (.write (.var "la")) (.seq (.assign "k" (.lit 0))
      (.while (.lt (.var "k") (.var "la")) writeEntry))))

/-- **Writing a word.** With the words `ws` in the arrays, `writeWord`
appends the frame of word `ow` to the output, in time linear in its
length. -/
theorem writeWord_run {B : ℕ} {ws : List (List ℕ)} {σ : Env} (hw : WordsAt ws σ)
    (hb : WordsBound B ws) {i : ℕ} (hi : σ.vars "ow" = i) (hil : i < ws.length) :
    ∃ σ', Run B writeWord σ σ' (13 * ws[i].length + 14) ∧
      σ'.out = σ.out ++ (ws[i].length :: ws[i]) := by
  have hoi := off_add_le hil
  have hlen := hb.len
  generalize hu : ws[i] = u at hoi
  have hea : ∀ k (h : k < u.length), (σ.arrs "a")[off ws i + k]? = some u[k] := by
    subst hu; exact hw.a i hil
  have hent : ∀ x ∈ u, x < B := by subst hu; exact hb.ent _ (List.getElem_mem hil)
  have hln : (σ.arrs "ln")[i]? = some u.length := by subst hu; exact hw.ln i hil
  set σ0 : Env := { ((σ.setVar "pa" (off ws i)).setVar "la" u.length) with
    out := σ.out ++ [u.length] } with hσ0
  let I : Env → Prop := fun τ => τ.vars "pa" = off ws i ∧ τ.vars "la" = u.length ∧
    τ.vars "k" ≤ u.length ∧ τ.arrs "a" = σ.arrs "a" ∧
    τ.out = σ.out ++ (u.length :: u.take (τ.vars "k"))
  obtain ⟨σ', hloop, ⟨hpa, hla, hkle, ha, hout⟩, hfalse⟩ :=
    Run.while_count (B := B) (b := .lt (.var "k") (.var "la")) (c := writeEntry) I
      (fun τ => u.length - τ.vars "k") 9
      (fun τ ⟨_, hla, hkle, _⟩ => evalB_condLt_vars (by omega) (by rw [hla]; omega))
      (by
        rintro τ ⟨hpa, hla, hkle, ha, hout⟩ hc
        have hk : τ.vars "k" < u.length := by
          have := lt_of_condLt_true hc; rwa [hla] at this
        have hget : (τ.arrs "a")[off ws i + τ.vars "k"]? = some u[τ.vars "k"] := by
          rw [ha]; exact hea _ hk
        refine ⟨_, Run.seq (Run.write (v := u[τ.vars "k"]) ?_) (Run.assign (v := τ.vars "k" + 1) ?_),
          ⟨by simp [hpa], by simp [hla], by simp; omega, by simp [ha], ?_⟩, by simp; omega⟩
        · simp only [evalB_get_iff, evalB_bin_iff, evalB_var_iff, hpa]
          exact ⟨_, ⟨_, _, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by simp only [Bop.apply_add]; omega⟩,
            hget,
            hent _ (List.getElem_mem hk)⟩
        · simp; omega
        · simp only [vars_setVar, if_true]
          rw [hout, List.take_add_one, List.getElem?_eq_getElem hk]
          simp)
      (show I (σ0.setVar "k" 0) by
        refine ⟨by simp [hσ0], by simp [hσ0], by simp, by simp [hσ0], by simp [hσ0]⟩)
  have hku : σ'.vars "k" = u.length := by
    have := le_of_condLt_false hfalse; rw [hla] at this; omega
  refine ⟨σ', ?_, by rw [hout, hku, List.take_length]⟩
  unfold writeWord
  refine (Run.seq (Run.assign (v := off ws i) ?_) (Run.seq (Run.assign (v := u.length) ?_)
    (Run.seq (Run.write (v := u.length) ?_) (Run.seq (Run.assign (v := 0) ?_) hloop)))).mono ?_
  · simp only [evalB_get_iff, evalB_var_iff, hi]
    exact ⟨i, ⟨rfl, by omega⟩, hw.st i hil, by omega⟩
  · simp only [evalB_get_iff, evalB_var_iff, vars_setVar, arrs_setVar]
    exact ⟨i, ⟨by simp [hi], by simp [hi]; omega⟩, hln, by omega⟩
  · simp; omega
  · simp; omega
  · simp; omega

end Lax185574Proofs.Words
