import Lax808846Proofs.Tactic
import Lax185574Proofs.Words.Lex
import Lax185574Proofs.Words.Read

/-!
Comparing two words held in the arrays of `Lax185574Proofs.Words.Read`.

The command `cmpWords` compares word `ci` with word `cj`
lexicographically and leaves the result in `c`: `0` if the first is
smaller, `1` if they are equal and `2` if it is larger. It walks both
words with the counter `k` until they differ or one of them ends. It
uses the scalars `pa`, `pb`, `la`, `lb`, `k` and `c`, and writes no
array.
-/

namespace Lax185574Proofs.Words

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning

/-- The entry of word `ci` at `k`, read through `pa`. -/
def entA : Expr := .get "a" (.add (.var "pa") (.var "k"))
/-- The entry of word `cj` at `k`, read through `pb`. -/
def entB : Expr := .get "a" (.add (.var "pb") (.var "k"))

/-- One round of the comparison. -/
def cmpStep : Com :=
  .ite (.lt (.var "k") (.var "la"))
    (.ite (.lt (.var "k") (.var "lb"))
      (.ite (.lt entA entB) (.assign "c" (.lit 0))
        (.ite (.lt entB entA) (.assign "c" (.lit 2))
          (.assign "k" (.add (.var "k") (.lit 1)))))
      (.assign "c" (.lit 2)))
    (.ite (.lt (.var "k") (.var "lb")) (.assign "c" (.lit 0)) (.assign "c" (.lit 1)))

/-- The state of the comparison of `u` and `v`. -/
structure CmpState (B : ℕ) (u v : List ℕ) (sa sb : ℕ) (ρ : Env) : Prop where
  pa : ρ.vars "pa" = sa
  pb : ρ.vars "pb" = sb
  la : ρ.vars "la" = u.length
  lb : ρ.vars "lb" = v.length
  kle : ρ.vars "k" ≤ u.length
  klb : ρ.vars "k" ≤ v.length
  pre : u.take (ρ.vars "k") = v.take (ρ.vars "k")
  ea : ∀ j (h : j < u.length), (ρ.arrs "a")[sa + j]? = some u[j]
  eb : ∀ j (h : j < v.length), (ρ.arrs "a")[sb + j]? = some v[j]
  ua : ∀ x ∈ u, x < B
  vb : ∀ x ∈ v, x < B
  fa : sa + u.length < B
  fb : sb + v.length < B
  three : 3 < B

theorem getD_of_getElem? {l : List ℕ} {i x : ℕ} (h : l[i]? = some x) : l.getD i 0 = x := by
  rw [List.getD_eq_getElem?_getD, h]; rfl

theorem lt_length_of_getElem? {l : List ℕ} {i x : ℕ} (h : l[i]? = some x) : i < l.length :=
  (List.getElem?_eq_some_iff.mp h).1

theorem CmpState.setVar {B : ℕ} {u v : List ℕ} {sa sb : ℕ} {ρ : Env}
    (h : CmpState B u v sa sb ρ) (x : String) (n : ℕ) (hx : x ∉ ["pa", "pb", "la", "lb", "k"]) :
    CmpState B u v sa sb (ρ.setVar x n) := by
  have h1 : x ≠ "pa" := fun e => hx (by simp [e])
  have h2 : x ≠ "pb" := fun e => hx (by simp [e])
  have h3 : x ≠ "la" := fun e => hx (by simp [e])
  have h4 : x ≠ "lb" := fun e => hx (by simp [e])
  have h5 : x ≠ "k" := fun e => hx (by simp [e])
  obtain ⟨hpa, hpb, hla, hlb, hkle, hklb, hpre, hea, heb, hua, hvb, hfa, hfb, h3'⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, hea, heb, hua, hvb, hfa, hfb, h3'⟩ <;>
    simp [Ne.symm h1, Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, *]

theorem cmpStep_spec (B : ℕ) (u v : List ℕ) (sa sb : ℕ) :
    Spec B (fun ρ => CmpState B u v sa sb ρ ∧ ρ.vars "c" = 3) cmpStep
      (fun ρ ρ' => CmpState B u v sa sb ρ' ∧
        ((ρ'.vars "c" = 3 ∧ ρ'.vars "k" = ρ.vars "k" + 1 ∧ ρ.vars "k" < u.length) ∨
          (ρ'.vars "c" = cmpCode u v ∧ ρ'.vars "k" = ρ.vars "k"))) 32 := by
  rintro ρ ⟨hs, hc⟩
  have hs' := hs
  obtain ⟨hpa, hpb, hla, hlb, hkle, hklb, hpre, hea, heb, hua, hvb, hfa, hfb, h3⟩ := hs'
  generalize hk : ρ.vars "k" = k at hkle hklb hpre
  have hA : ∀ h : k < u.length, (ρ.arrs "a").getD (sa + k) 0 = u[k] :=
    fun h => getD_of_getElem? (hea k h)
  have hB' : ∀ h : k < v.length, (ρ.arrs "a").getD (sb + k) 0 = v[k] :=
    fun h => getD_of_getElem? (heb k h)
  have hAl : k < u.length → sa + k < (ρ.arrs "a").length :=
    fun h => lt_length_of_getElem? (hea k h)
  have hBl : k < v.length → sb + k < (ρ.arrs "a").length :=
    fun h => lt_length_of_getElem? (heb k h)
  have hAB : ∀ h : k < u.length, u[k] < B := fun h => hua _ (List.getElem_mem h)
  have hBB : ∀ h : k < v.length, v[k] < B := fun h => hvb _ (List.getElem_mem h)
  have hAl' : ρ.vars "k" < ρ.vars "la" → ρ.vars "pa" + ρ.vars "k" < (ρ.arrs "a").length := by
    rw [hla, hpa, hk]; exact hAl
  have hBl' : ρ.vars "k" < ρ.vars "lb" → ρ.vars "pb" + ρ.vars "k" < (ρ.arrs "a").length := by
    rw [hlb, hpb, hk]; exact hBl
  have hAB' : ρ.vars "k" < ρ.vars "la" → (ρ.arrs "a").getD (ρ.vars "pa" + ρ.vars "k") 0 < B := by
    rw [hla, hpa, hk]; intro h; rw [hA h]; exact hAB h
  have hBB' : ρ.vars "k" < ρ.vars "lb" → (ρ.arrs "a").getD (ρ.vars "pb" + ρ.vars "k") 0 < B := by
    rw [hlb, hpb, hk]; intro h; rw [hB' h]; exact hBB h
  unfold cmpStep entA entB
  run_vcg
  · rename_i h1 h2 h3
    simp only [hpa, hpb, hla, hlb, hk] at h1 h2 h3
    rw [hA h1, hB' h2] at h3
    exact ⟨hs.setVar "c" 0 (by decide), Or.inr ⟨by simp [cmpCode_of_lt_at h1 h2 hpre h3],
      by simp [hk]⟩⟩
  · rename_i h1 h2 h3 h4
    simp only [hpa, hpb, hla, hlb, hk] at h1 h2 h3 h4
    rw [hA h1, hB' h2] at h4
    exact ⟨hs.setVar "c" 2 (by decide), Or.inr ⟨by simp [cmpCode_of_gt_at h1 h2 hpre h4],
      by simp [hk]⟩⟩
  · rename_i h1 h2 h3 h4
    simp only [hpa, hpb, hla, hlb, hk] at h1 h2 h3 h4
    rw [hA h1, hB' h2] at h3 h4
    have heq : u[k] = v[k] := by omega
    refine ⟨⟨by simp [hpa], by simp [hpb], by simp [hla], by simp [hlb], by simp; omega,
      by simp; omega, ?_, hs.ea, hs.eb, hua, hvb, hfa, hfb, hs.three⟩, Or.inl ⟨by simp [hc], by simp [hk],
      by omega⟩⟩
    simp only [vars_setVar, if_true, hk]
    rw [List.take_add_one, List.take_add_one, hpre, List.getElem?_eq_getElem h1,
      List.getElem?_eq_getElem h2, heq]
  · rename_i h1 h2
    simp only [hla, hlb, hk] at h1 h2
    exact ⟨hs.setVar "c" 2 (by decide), Or.inr ⟨by simp [cmpCode_of_end_right h1 (by omega) hpre],
      by simp [hk]⟩⟩
  · rename_i h1 h2
    simp only [hla, hlb, hk] at h1 h2
    exact ⟨hs.setVar "c" 0 (by decide), Or.inr ⟨by simp [cmpCode_of_end_left (by omega) h2 hpre],
      by simp [hk]⟩⟩
  · rename_i h1 h2
    simp only [hla, hlb, hk] at h1 h2
    exact ⟨hs.setVar "c" 1 (by decide),
      Or.inr ⟨by simp [cmpCode_of_end_both (by omega) (by omega) hpre], by simp [hk]⟩⟩

/-- Compare word `ci` with word `cj`: `c` becomes `0`, `1` or `2` as the
first is smaller than, equal to or larger than the second. -/
def cmpWords : Com :=
  .seq (.assign "pa" (.get "st" (.var "ci"))) (.seq (.assign "pb" (.get "st" (.var "cj")))
    (.seq (.assign "la" (.get "ln" (.var "ci"))) (.seq (.assign "lb" (.get "ln" (.var "cj")))
      (.seq (.assign "k" (.lit 0)) (.seq (.assign "c" (.lit 3))
        (.while (.eq (.var "c") (.lit 3)) cmpStep))))))

/-- The words are below the bound: their number, their total length and
their entries. -/
structure WordsBound (B : ℕ) (ws : List (List ℕ)) : Prop where
  /-- The number of words and the total length. -/
  len : ws.length + total ws < B
  /-- The entries. -/
  ent : ∀ u ∈ ws, ∀ x ∈ u, x < B
  /-- The comparison results and the literals of the programs. -/
  three : 3 < B

theorem cmpLoop_run {B : ℕ} {u v : List ℕ} {sa sb : ℕ} {σ : Env}
    (hs : CmpState B u v sa sb σ) (hk : σ.vars "k" = 0) (hc : σ.vars "c" = 3) :
    ∃ σ', Run B (.while (.eq (.var "c") (.lit 3)) cmpStep) σ σ' (36 * u.length + 40) ∧
      σ'.vars "c" = cmpCode u v := by
  have hdef : ∀ τ, (CmpState B u v sa sb τ ∧ (τ.vars "c" = 3 ∨ τ.vars "c" = cmpCode u v)) →
      ∃ b, (Cond.eq (.var "c") (.lit 3)).evalB B τ = some b := by
    rintro τ ⟨hτ, hcτ⟩
    refine ⟨_, evalB_condEq (evalB_var ?_) (evalB_lit hτ.three)⟩
    have := cmpCode_le_two u v
    have := hτ.three
    omega
  obtain ⟨σ', K, hrun, ⟨hs', hc'⟩, hfalse, hK⟩ :=
    Run.while_potential (B := B) (b := .eq (.var "c") (.lit 3)) (c := cmpStep)
      (fun τ => CmpState B u v sa sb τ ∧ (τ.vars "c" = 3 ∨ τ.vars "c" = cmpCode u v))
      (fun τ => 36 * (u.length - τ.vars "k") + (if τ.vars "c" = 3 then 36 else 0)) hdef
      (by
        rintro τ ⟨hτ, -⟩ htrue
        have hc3 : τ.vars "c" = 3 := by
          simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff] at htrue
          obtain ⟨m, n, ⟨rfl, -⟩, ⟨rfl, -⟩, h⟩ := htrue
          simpa using h.symm
        obtain ⟨τ', hr, hτ', hcase⟩ := cmpStep_spec B u v sa sb τ ⟨hτ, hc3⟩
        refine ⟨τ', 32, hr, ⟨hτ', ?_⟩, ?_⟩
        · rcases hcase with ⟨h1, -, -⟩ | ⟨h1, -⟩
          · exact Or.inl h1
          · exact Or.inr h1
        · have hu3 : cmpCode u v ≠ 3 := by have := cmpCode_le_two u v; omega
          rcases hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2⟩
          · simp only [h1, hc3, if_true, h2, size_condEq, size_var, size_lit]; omega
          · simp only [h1, hc3, if_true, hu3, if_false, h2, size_condEq, size_var, size_lit]; omega)
      ⟨hs, Or.inl hc⟩
  refine ⟨σ', hrun.mono ?_, ?_⟩
  · simp only [hk, hc, if_true, size_condEq, size_var, size_lit] at hK; omega
  · rcases hc' with h | h
    · simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff] at hfalse
      obtain ⟨m, n, ⟨rfl, -⟩, ⟨rfl, -⟩, h'⟩ := hfalse
      simp [h] at h'
    · exact h

/-- **Comparing two words.** With the words `ws` in the arrays,
`cmpWords` sets `c` to the comparison code of word `ci` and word `cj`,
in time linear in the length of word `ci`. -/
theorem cmpWords_run {B : ℕ} {ws : List (List ℕ)} {σ : Env} (hw : WordsAt ws σ)
    (hb : WordsBound B ws) {i j : ℕ} (hi : σ.vars "ci" = i) (hj : σ.vars "cj" = j)
    (hil : i < ws.length) (hjl : j < ws.length) :
    ∃ σ', Run B cmpWords σ σ' (36 * ws[i].length + 56) ∧
      σ'.vars "c" = cmpCode ws[i] ws[j] := by
  have hoi := off_add_le hil
  have hoj := off_add_le hjl
  have hlen := hb.len
  set σ0 : Env := (((((σ.setVar "pa" (off ws i)).setVar "pb" (off ws j)).setVar "la"
    ws[i].length).setVar "lb" ws[j].length).setVar "k" 0).setVar "c" 3 with hσ0
  have hs : CmpState B ws[i] ws[j] (off ws i) (off ws j) σ0 :=
    ⟨by simp [hσ0], by simp [hσ0], by simp [hσ0], by simp [hσ0], by simp [hσ0], by simp [hσ0],
      by simp [hσ0], fun k hk => by simpa [hσ0] using hw.a i hil k hk,
      fun k hk => by simpa [hσ0] using hw.a j hjl k hk,
      hb.ent _ (List.getElem_mem hil), hb.ent _ (List.getElem_mem hjl), by omega, by omega,
      hb.three⟩
  obtain ⟨σ', hr, hc⟩ := cmpLoop_run hs (by simp [hσ0]) (by simp [hσ0])
  refine ⟨σ', ?_, hc⟩
  unfold cmpWords
  refine (Run.seq (Run.assign ?_) (Run.seq (Run.assign ?_) (Run.seq (Run.assign ?_)
    (Run.seq (Run.assign ?_) (Run.seq (Run.assign ?_) (Run.seq (Run.assign ?_) hr)))))).mono
    (by simp; omega)
  · simp only [evalB_get_iff, evalB_var_iff, hi]
    exact ⟨i, ⟨rfl, by omega⟩, hw.st i hil, by omega⟩
  · simp only [evalB_get_iff, evalB_var_iff, vars_setVar, hj, arrs_setVar]
    exact ⟨j, ⟨by simp, by simp; omega⟩, hw.st j hjl, by omega⟩
  · simp only [evalB_get_iff, evalB_var_iff, vars_setVar, arrs_setVar]
    exact ⟨i, ⟨by simp [hi], by simp [hi]; omega⟩, hw.ln i hil, by omega⟩
  · simp only [evalB_get_iff, evalB_var_iff, vars_setVar, arrs_setVar]
    exact ⟨j, ⟨by simp [hj], by simp [hj]; omega⟩, hw.ln j hjl, by omega⟩
  · simp; omega
  · simp; exact hb.three

end Lax185574Proofs.Words
