import Lax185574Proofs.MainRam.ValidStep

/-!
The validation program, part six: writing the output, the flag and
the instance of thm:mc, or the flag `0` and the instance on the empty
graph.
-/

namespace Lax185574Proofs.MainRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax185574Proofs.Words Lax185574Proofs.Conversions.Ram

/-- Write the first `cnt` entries of `arr`. -/
def wArr (arr : String) (cnt : Expr) : Com := forUp "k" cnt (.write (.get arr (.var "k")))

theorem wArr_run {B N : ℕ} {σ : Env} {arr : String} {cnt : Expr} {l : List ℕ}
    (hl : σ.arrs arr = l) (hN : N ≤ l.length) (hNB : N < B) (hlB : ∀ a ∈ l, a < B)
    (hc : ∀ τ, (∀ z, z ≠ "k" → τ.vars z = σ.vars z) → cnt.evalB B τ = some N) :
    ∃ σ', Run B (wArr arr cnt) σ σ' (N * (3 + cnt.size + 7) + cnt.size + 5) ∧
      σ'.out = σ.out ++ l.take N ∧ (∀ z, z ≠ "k" → σ'.vars z = σ.vars z) ∧
      σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp := by
  let I : ℕ → Env → Prop := fun k τ => τ.out = σ.out ++ l.take k ∧
    (∀ z, z ≠ "k" → τ.vars z = σ.vars z) ∧ τ.arrs = σ.arrs ∧ τ.inp = σ.inp
  obtain ⟨σ', hr, ⟨ho, hv, ha, hi⟩, -⟩ := forUp_run (B := B) (i := "k") (e := cnt)
    (body := .write (.get arr (.var "k"))) (N := N) (K := 3) I (σ := σ) hNB
    (fun k _ τ hI _ => hc τ hI.2.1)
    ⟨by simp, fun z hz => by simp [hz], by simp, by simp⟩
    (by
      rintro k hk τ ⟨ho, hv, ha, hi⟩ hkk
      have hkl : k < l.length := by omega
      have he : (Expr.get arr (.var "k")).evalB B τ = some l[k] :=
        evalB_get (by rw [evalB_var (by rw [hkk]; omega), hkk]) (by rw [ha, hl]; simp [hkl])
          (hlB _ (List.getElem_mem hkl))
      refine ⟨_, (Run.write he).mono (by simp), by simp [hkk], ?_, fun z hz => by
        simp [hz, hv z hz], by simp [ha], by simp [hi]⟩
      show τ.out ++ [l[k]] = _
      rw [ho, List.take_succ, List.getElem?_eq_getElem hkl, List.append_assoc]; rfl)
  exact ⟨σ', hr, ho, hv, ha, hi⟩

def outValid : Com :=
  .seq (.write (.lit 1)) (.seq (.write (.var "n")) (.seq (.write (.var "E"))
    (.seq (wArr "of" (.add (.var "n") (.lit 1))) (.seq (wArr "tg" (.add (.var "E") (.var "E")))
      (.seq (wArr "Y" (.var "L")) (wArr "F" (.var "nF")))))))

def outInvalid : Com :=
  .seq (.write (.lit 0)) (.seq (.write (.lit 0)) (.seq (.write (.lit 0)) (.seq (.write (.lit 0))
    (.seq (.write (.lit 0)) (.seq (.write (.lit 0)) (wArr "F" (.var "nF")))))))

def outPh : Com := .ite (.eq (.var "ok") (.lit 1)) outValid outInvalid

/-- Writing three arrays after another, all framed. -/
theorem wArr_var {B N : ℕ} {τ : Env} {x : String} (hx : x ≠ "k") (hv : τ.vars x = N)
    (hNB : N < B) : ∀ ρ : Env, (∀ z, z ≠ "k" → ρ.vars z = τ.vars z) →
      (Expr.var x).evalB B ρ = some N := fun ρ h => by
  rw [evalB_var (by rw [h x hx, hv]; omega), h x hx, hv]

theorem outPh_run {B : ℕ} {σ : Env} {n E : ℕ} {ofv tgv y φw : List ℕ} (hok : σ.vars "ok" ≤ 1)
    (hn : σ.vars "n" = n) (hE : σ.vars "E" = E) (hL : σ.vars "L" = y.length)
    (hnF : σ.vars "nF" = φw.length) (hof : σ.arrs "of" = ofv) (htg : σ.arrs "tg" = tgv)
    (hY : σ.arrs "Y" = y) (hF : σ.arrs "F" = φw) (hofl : ofv.length = n + 1)
    (htgl : tgv.length = E + E)
    (hB : n + E + E + y.length + φw.length + 2 < B)
    (hent : ∀ a ∈ ofv ++ tgv ++ y ++ φw, a < B) :
    ∃ σ', Run B outPh σ σ' (14 * (n + E + E + y.length + φw.length) + 100) ∧
      σ'.out = σ.out ++ (if σ.vars "ok" = 1 then 1 :: n :: E :: (ofv ++ tgv ++ y ++ φw)
        else 0 :: 0 :: 0 :: 0 :: 0 :: 0 :: φw) := by
  have hofB : ∀ a ∈ ofv, a < B := fun a ha => hent a (by simp [ha])
  have htgB : ∀ a ∈ tgv, a < B := fun a ha => hent a (by simp [ha])
  have hyB : ∀ a ∈ y, a < B := fun a ha => hent a (by simp [ha])
  have hφB : ∀ a ∈ φw, a < B := fun a ha => hent a (by simp [ha])
  by_cases h1 : σ.vars "ok" = 1
  · have hc : (Cond.eq (.var "ok") (.lit 1)).evalB B σ = some true := by
      rw [evalB_condEq' (evalB_var (by omega)) (evalB_lit (by omega)), h1]; rfl
    have ws : ∀ (ρ : Env) (e : Expr) (v : ℕ), e.evalB B ρ = some v → ∃ ρ',
        Run B (.write e) ρ ρ' (1 + e.size) ∧ ρ'.out = ρ.out ++ [v] ∧ ρ'.vars = ρ.vars ∧
          ρ'.arrs = ρ.arrs := fun ρ e v h => ⟨_, Run.write h, rfl, rfl, rfl⟩
    obtain ⟨σ1, w1, o1, v1, a1⟩ := ws σ (.lit 1) 1 (evalB_lit (by omega))
    obtain ⟨σ2, w2, o2, v2, a2⟩ := ws σ1 (.var "n") n (by rw [evalB_var (by rw [v1, hn]; omega), v1, hn])
    obtain ⟨σ3, w3, o3, v3, a3⟩ := ws σ2 (.var "E") E
      (by rw [evalB_var (by rw [v2, v1, hE]; omega), v2, v1, hE])
    have hv3 : ∀ z, σ3.vars z = σ.vars z := fun z => by rw [v3, v2, v1]
    obtain ⟨σ4, w4, ho4, hv4, ha4, -⟩ := wArr_run (B := B) (N := n + 1) (σ := σ3) (arr := "of")
      (cnt := .add (.var "n") (.lit 1)) (l := ofv) (by rw [a3, a2, a1, hof]) (by omega) (by omega) hofB
      (fun ρ h => by
        have := evalB_bin (op := .add) (evalB_var (x := "n") (σ := ρ) (B := B)
          (by rw [h "n" (by decide), hv3, hn]; omega)) (evalB_lit (n := 1) (by omega))
          (by show ρ.vars "n" + 1 < B; rw [h "n" (by decide), hv3, hn]; omega)
        simpa [h "n" (by decide), hv3, hn] using this)
    obtain ⟨σ5, w5, ho5, hv5, ha5, -⟩ := wArr_run (B := B) (N := E + E) (σ := σ4) (arr := "tg")
      (cnt := .add (.var "E") (.var "E")) (l := tgv) (by rw [ha4, a3, a2, a1]; exact htg) (by omega)
      (by omega) htgB
      (fun ρ h => by
        have hE' : ρ.vars "E" = E := by rw [h "E" (by decide), hv4 "E" (by decide), hv3, hE]
        have := evalB_bin (op := .add) (evalB_var (x := "E") (σ := ρ) (B := B)
          (by rw [hE']; omega)) (evalB_var (x := "E") (σ := ρ) (B := B) (by rw [hE']; omega))
          (by show ρ.vars "E" + ρ.vars "E" < B; rw [hE']; omega)
        simpa [hE'] using this)
    obtain ⟨σ6, w6, ho6, hv6, ha6, -⟩ := wArr_run (B := B) (N := y.length) (σ := σ5) (arr := "Y")
      (cnt := .var "L") (l := y) (by rw [ha5, ha4, a3, a2, a1]; exact hY) le_rfl (by omega) hyB
      (wArr_var (by decide) (by rw [hv5 "L" (by decide), hv4 "L" (by decide), hv3, hL])
        (by omega))
    obtain ⟨σ7, w7, ho7, -, -, -⟩ := wArr_run (B := B) (N := φw.length) (σ := σ6) (arr := "F")
      (cnt := .var "nF") (l := φw) (by rw [ha6, ha5, ha4, a3, a2, a1]; exact hF) le_rfl (by omega) hφB
      (wArr_var (by decide) (by rw [hv6 "nF" (by decide), hv5 "nF" (by decide),
        hv4 "nF" (by decide), hv3, hnF]) (by omega))
    refine ⟨σ7, (Run.ite_true hc (w1.seq (w2.seq (w3.seq (w4.seq (w5.seq (w6.seq w7)))))
      )).mono (by simp [wArr]; omega), ?_⟩
    rw [ho7, ho6, ho5, ho4, o3, o2, o1, if_pos h1, List.take_of_length_le (by omega),
      List.take_of_length_le (by omega), List.take_of_length_le le_rfl, List.take_of_length_le le_rfl]
    simp
  · have hc : (Cond.eq (.var "ok") (.lit 1)).evalB B σ = some false := by
      rw [evalB_condEq' (evalB_var (by omega)) (evalB_lit (by omega))]; simp [h1]
    have w0 : ∀ ρ : Env, ∃ ρ', Run B (.write (.lit 0)) ρ ρ' 2 ∧ ρ'.out = ρ.out ++ [0] ∧
        ρ'.vars = ρ.vars ∧ ρ'.arrs = ρ.arrs :=
      fun ρ => ⟨_, (Run.write (evalB_lit (by omega))).mono (by simp), rfl, rfl, rfl⟩
    obtain ⟨τ1, u1, o1, v1, a1⟩ := w0 σ
    obtain ⟨τ2, u2, o2, v2, a2⟩ := w0 τ1
    obtain ⟨τ3, u3, o3, v3, a3⟩ := w0 τ2
    obtain ⟨τ4, u4, o4, v4, a4⟩ := w0 τ3
    obtain ⟨τ5, u5, o5, v5, a5⟩ := w0 τ4
    obtain ⟨τ6, u6, o6, v6, a6⟩ := w0 τ5
    obtain ⟨σ7, w7, ho7, -, -, -⟩ := wArr_run (B := B) (N := φw.length) (σ := τ6) (arr := "F")
      (cnt := .var "nF") (l := φw) (by rw [a6, a5, a4, a3, a2, a1]; exact hF) le_rfl (by omega)
      hφB (wArr_var (by decide) (by rw [v6, v5, v4, v3, v2, v1]; exact hnF) (by omega))
    have hseq := u1.seq (u2.seq (u3.seq (u4.seq (u5.seq (u6.seq w7)))))
    refine ⟨σ7, (Run.ite_false hc hseq).mono (by simp; omega), ?_⟩
    rw [ho7, if_neg h1, o6, o5, o4, o3, o2, o1, List.take_of_length_le le_rfl]
    simp

end Lax185574Proofs.MainRam
