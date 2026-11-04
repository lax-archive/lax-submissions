import Lax185574Proofs.Conversions.Ram.Basic

/-!
A buffer of numbers in the array `buf`, filled from the front.

The scalar `p` is the number of entries written so far. `pushVars`
appends the values of the scalars `s1`, `s2`, `s3`. `writeBuf` writes
the whole buffer to the output.
-/

namespace Lax185574Proofs.Conversions.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words

/-- The buffer holds `l`, in an array of length `cap`. -/
structure BufAt (cap : ℕ) (l : List ℕ) (τ : Env) : Prop where
  len : (τ.arrs "buf").length = cap
  hp : τ.vars "p" = l.length
  get : ∀ i (h : i < l.length), (τ.arrs "buf")[i]? = some l[i]

theorem BufAt.of_eq {cap : ℕ} {l : List ℕ} {τ τ' : Env} (h : BufAt cap l τ)
    (hp : τ'.vars "p" = τ.vars "p") (hb : τ'.arrs "buf" = τ.arrs "buf") : BufAt cap l τ' :=
  ⟨by rw [hb, h.len], by rw [hp, h.hp], by rw [hb]; exact h.get⟩

/-- Append the values of `s1`, `s2` and `s3`. -/
def pushVars : Com :=
  .seq (.store "buf" (.var "p") (.var "s1"))
    (.seq (.store "buf" (.add (.var "p") (.lit 1)) (.var "s2"))
      (.seq (.store "buf" (.add (.var "p") (.lit 2)) (.var "s3"))
        (.assign "p" (.add (.var "p") (.lit 3)))))

theorem getElem?_set_prefix {l : List ℕ} {b : List ℕ} {k v : ℕ}
    (hb : ∀ i (h : i < l.length), b[i]? = some l[i]) (hk : k = l.length) (hlen : k < b.length) :
    ∀ i (h : i < (l ++ [v]).length), (b.set k v)[i]? = some (l ++ [v])[i] := by
  intro i hi
  rw [List.getElem?_set]
  simp only [List.length_append, List.length_singleton] at hi
  by_cases hik : k = i
  · subst hik
    have hl' : l.length < b.length := hk ▸ hlen
    simp [hl', hk]
  · rw [if_neg hik]
    have : i < l.length := by omega
    rw [hb i this, List.getElem_append_left this]

theorem pushVars_run {B cap : ℕ} {l : List ℕ} {τ : Env} (h : BufAt cap l τ)
    (hcap : l.length + 3 ≤ cap) (hB : cap + 3 < B) (h1 : τ.vars "s1" < B) (h2 : τ.vars "s2" < B)
    (h3 : τ.vars "s3" < B) :
    ∃ τ', Run B pushVars τ τ' 20 ∧
      BufAt cap (l ++ [τ.vars "s1", τ.vars "s2", τ.vars "s3"]) τ' ∧
      (∀ y, y ≠ "p" → τ'.vars y = τ.vars y) ∧ (∀ a, a ≠ "buf" → τ'.arrs a = τ.arrs a) ∧
      τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  set p := l.length
  set τ1 := τ.setArr "buf" p (τ.vars "s1") with hτ1
  set τ2 := τ1.setArr "buf" (p + 1) (τ.vars "s2") with hτ2
  set τ3 := τ2.setArr "buf" (p + 2) (τ.vars "s3") with hτ3
  have hb1 : ∀ i (hi : i < (l ++ [τ.vars "s1"]).length), (τ1.arrs "buf")[i]? =
      some (l ++ [τ.vars "s1"])[i] := by
    simp only [hτ1, arrs_setArr, if_true]
    exact getElem?_set_prefix h.get rfl (by rw [h.len]; omega)
  have hb2 : ∀ i (hi : i < (l ++ [τ.vars "s1"] ++ [τ.vars "s2"]).length), (τ2.arrs "buf")[i]? =
      some (l ++ [τ.vars "s1"] ++ [τ.vars "s2"])[i] := by
    simp only [hτ2, arrs_setArr, if_true]
    exact getElem?_set_prefix hb1 (by simp [p]) (by simp [hτ1, h.len]; omega)
  have hb3 : ∀ i (hi : i < (l ++ [τ.vars "s1"] ++ [τ.vars "s2"] ++ [τ.vars "s3"]).length),
      (τ3.arrs "buf")[i]? = some (l ++ [τ.vars "s1"] ++ [τ.vars "s2"] ++ [τ.vars "s3"])[i] := by
    simp only [hτ3, arrs_setArr, if_true]
    exact getElem?_set_prefix hb2 (by simp [p]) (by simp [hτ2, hτ1, h.len]; omega)
  have hp := h.hp
  have hl := h.len
  refine ⟨τ3.setVar "p" (p + 3), ?_, ⟨by simp [hτ3, hτ2, hτ1, h.len], by simp [p], ?_⟩,
    fun y hy => by simp [hy, hτ3, hτ2, hτ1], fun a ha => by simp [ha, hτ3, hτ2, hτ1],
    by simp [hτ3, hτ2, hτ1], by simp [hτ3, hτ2, hτ1]⟩
  · refine (Run.seq (Run.store (idx := p) (v := τ.vars "s1") ?_ ?_ ?_) (Run.seq
      (Run.store (idx := p + 1) (v := τ.vars "s2") ?_ ?_ ?_) (Run.seq
      (Run.store (idx := p + 2) (v := τ.vars "s3") ?_ ?_ ?_) (Run.assign ?_)))).mono (by simp)
    · simp [hp]; omega
    · simp; omega
    · omega
    · simp [hτ1, hp]; omega
    · simp [hτ1]; omega
    · simp [hτ1]; omega
    · simp [hτ2, hτ1, hp]; omega
    · simp [hτ2, hτ1]; omega
    · simp [hτ2, hτ1]; omega
    · simp [hτ3, hτ2, hτ1, hp]; omega
  · intro i hi
    simp only [arrs_setVar]
    have := hb3 i (by simpa using hi)
    simpa using this

/-- Write `buf[0], …, buf[p-1]`. -/
def writeBuf : Com := forUp "i" (.var "p") (.write (.get "buf" (.var "i")))

theorem writeBuf_run {B cap : ℕ} {l : List ℕ} {τ : Env} (h : BufAt cap l τ) (hB : cap < B)
    (hl : ∀ v ∈ l, v < B) :
    ∃ τ', Run B writeBuf τ τ' (cap * 12 + 6) ∧ τ'.out = τ.out ++ l := by
  have hlc : l.length ≤ cap := by
    by_contra hc
    have := h.get cap (by omega)
    rw [List.getElem?_eq_none (by rw [h.len])] at this
    exact absurd this (by simp)
  let I : ℕ → Env → Prop := fun k ρ => BufAt cap l ρ ∧ ρ.out = τ.out ++ l.take k
  obtain ⟨ρ, hr, ⟨-, ho⟩, -⟩ :=
    forUp_run (B := B) (i := "i") (e := .var "p") (body := .write (.get "buf" (.var "i")))
      (N := l.length) (K := 4) I (by omega)
      (fun k _ ρ hI _ => by rw [evalB_var (by rw [hI.1.hp]; omega), hI.1.hp])
      (σ := τ) ⟨h.of_eq (by simp) (by simp), by simp⟩
      (by
        rintro k hk ρ ⟨hb, ho⟩ hik
        refine ⟨_, (Run.write (v := l[k]) (evalB_get (by rw [evalB_var (by omega), hik])
          (hb.get k hk) (hl _ (List.getElem_mem hk)))).mono (by simp), by simp [hik],
          hb.of_eq (by simp) (by simp), ?_⟩
        simp only [out_setVar, ho]
        rw [List.take_add_one, List.getElem?_eq_getElem hk, List.append_assoc]
        rfl)
  refine ⟨ρ, hr.mono ?_, by rw [ho, List.take_length]⟩
  simp only [size_var]
  nlinarith

end Lax185574Proofs.Conversions.Ram
