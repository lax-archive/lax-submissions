import Lax185574Proofs.Words.ForLoop
import Lax185574Proofs.Words.Read

/-!
Two small commands for glue programs that check the values they pass on.

`chkE e` sets the scalar `ovf` to `1` if the value of `e` exceeds the
threshold in `T`. `rdChk arr` reads `cnt` numbers off the input into the
array `arr` from position `bs` on, and checks each of them against `T`.
It uses the scalars `i` and `w`. The flag `ovf` stays `0` exactly if it
was `0` and every number read is at most `T`.
-/

namespace Lax185574Proofs.JobMap

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words

/-- Set `ovf` if the value of `e` exceeds `T`. -/
def chkE (e : Expr) : Com := .ite (.lt (.var "T") e) (.assign "ovf" (.lit 1)) .skip

theorem chkE_run {B : ℕ} {e : Expr} {σ : Env} {v : ℕ} (hB : 1 < B) (he : e.evalB B σ = some v)
    (hT : σ.vars "T" < B) (hovf : σ.vars "ovf" ≤ 1) :
    ∃ σ', Run B (chkE e) σ σ' (e.size + 5) ∧ σ'.vars "ovf" ≤ 1 ∧
      (σ'.vars "ovf" = 0 ↔ σ.vars "ovf" = 0 ∧ v ≤ σ.vars "T") ∧
      (∀ y, y ≠ "ovf" → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧
      σ'.out = σ.out := by
  have hc := evalB_condLt (evalB_var hT) he
  by_cases h : σ.vars "T" < v
  · refine ⟨σ.setVar "ovf" 1, (Run.ite_true (by rw [hc]; simp [h])
      (Run.assign (evalB_lit hB))).mono (by simp; omega), by simp, by simp; omega,
      fun y hy => by simp [hy], by simp, by simp, by simp⟩
  · refine ⟨σ, (Run.ite_false (by rw [hc]; simp [h]) Run.skip).mono (by simp; omega), hovf,
      by omega, fun y _ => rfl, rfl, rfl, rfl⟩

/-- One round of `rdChk`: read a number, store it, check it. -/
def rdBody (arr : String) : Com :=
  .seq (.read "w") (.seq (.store arr (.add (.var "bs") (.var "i")) (.var "w")) (chkE (.var "w")))

/-- Read `cnt` numbers into `arr` from position `bs` on, checking each. -/
def rdChk (arr : String) : Com := forUp "i" (.var "cnt") (rdBody arr)

theorem rdChk_run {B : ℕ} (arr : String) {u rest : List ℕ} {σ : Env} {b0 : ℕ} (hB : 1 < B)
    (hinp : σ.inp = u ++ rest) (hcnt : σ.vars "cnt" = u.length) (hbs : σ.vars "bs" = b0)
    (hlen : b0 + u.length ≤ (σ.arrs arr).length) (hb0 : b0 + u.length < B)
    (hu : ∀ y ∈ u, y < B) (hT : σ.vars "T" < B) (hovf : σ.vars "ovf" ≤ 1) :
    ∃ σ', Run B (rdChk arr) σ σ' (u.length * 20 + 6) ∧ σ'.inp = rest ∧
      σ'.arrs arr = (σ.arrs arr).take b0 ++ u ++ (σ.arrs arr).drop (b0 + u.length) ∧
      σ'.vars "ovf" ≤ 1 ∧ (σ'.vars "ovf" = 0 ↔ σ.vars "ovf" = 0 ∧ ∀ y ∈ u, y ≤ σ.vars "T") := by
  set l := σ.arrs arr with hl
  set T := σ.vars "T" with hTd
  obtain ⟨σ', hr, ⟨hin, harr, -, -, -, hov1, hov⟩, -⟩ := forUp_run (B := B) (i := "i")
    (e := .var "cnt") (body := rdBody arr) (N := u.length) (K := 12)
    (fun k τ => τ.inp = u.drop k ++ rest ∧ τ.arrs arr = l.take b0 ++ u.take k ++ l.drop (b0 + k) ∧
      τ.vars "cnt" = u.length ∧ τ.vars "bs" = b0 ∧ τ.vars "T" = T ∧ τ.vars "ovf" ≤ 1 ∧
      (τ.vars "ovf" = 0 ↔ σ.vars "ovf" = 0 ∧ ∀ y ∈ u.take k, y ≤ T))
    (σ := σ) (by omega)
    (fun k _ τ hI _ => by
      simp only [evalB_var_iff]; exact ⟨hI.2.2.1.symm, by rw [hI.2.2.1]; omega⟩)
    ⟨by simp [hinp], by simp [hl, List.take_append_drop], by simp [hcnt], by simp [hbs],
      by simp [hTd], by simp [hovf], by simp⟩
    (fun k hk τ ⟨hin, harr, hc, hb, hTT, ho1, ho⟩ hik => by
      have hin' : τ.inp = u[k] :: (u.drop (k + 1) ++ rest) := by
        rw [hin, List.drop_eq_getElem_cons hk]; rfl
      have huk : u[k] < B := hu _ (List.getElem_mem hk)
      set τ1 : Env := { τ.setVar "w" u[k] with inp := u.drop (k + 1) ++ rest } with hτ1
      have hlenτ : (τ.arrs arr).length = l.length := by
        rw [harr]; simp; omega
      have hst : Run B (.store arr (.add (.var "bs") (.var "i")) (.var "w")) τ1
          (τ1.setArr arr (b0 + k) u[k]) 5 := by
        refine (Run.store (idx := b0 + k) (v := u[k]) ?_ ?_ ?_).mono (by simp)
        · simp [hτ1, hb, hik]; omega
        · simp [hτ1]; exact huk
        · simp [hτ1, hlenτ]; omega
      set τ2 := τ1.setArr arr (b0 + k) u[k] with hτ2
      obtain ⟨τ3, r3, h31, h3o, h3v, h3a, h3i, -⟩ := chkE_run (B := B) (σ := τ2) (e := .var "w")
        (v := u[k]) hB (by simp [hτ2, hτ1]; exact huk) (by simp [hτ2, hτ1, hTT]; omega)
        (by simp [hτ2, hτ1]; omega)
      refine ⟨τ3, (Run.seq (Run.read hin') (Run.seq hst r3)).mono (by simp), ?_, ?_⟩
      · rw [h3v "i" (by decide)]; simp [hτ2, hτ1, hik]
      · have hv : ∀ y, y ≠ "ovf" → τ3.vars y = τ2.vars y := h3v
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simp [h3i, hτ2, hτ1]
        · simp only [arrs_setVar, h3a, hτ2, arrs_setArr, if_true, hτ1]
          rw [harr, set_prefix' (by simp; omega) (by omega), List.take_add_one,
            List.getElem?_eq_getElem hk]
          simp only [Option.toList_some, List.append_assoc, List.singleton_append,
            Nat.add_assoc]
        · simp [hv "cnt" (by decide), hτ2, hτ1, hc]
        · simp [hv "bs" (by decide), hτ2, hτ1, hb]
        · simp [hv "T" (by decide), hτ2, hτ1, hTT]
        · simp only [vars_setVar]; simpa using h31
        · simp only [vars_setVar, show ("ovf" = "i") = False by decide, if_false]
          rw [h3o]
          simp only [hτ2, hτ1, vars_setArr, vars_setVar, show ("ovf" = "w") = False by decide,
            if_false, hTT, ho]
          rw [List.take_add_one, List.getElem?_eq_getElem hk]
          simp only [Option.toList_some, List.mem_append, List.mem_singleton]
          constructor
          · rintro ⟨⟨h1, h2⟩, h3⟩
            exact ⟨h1, fun y hy => hy.elim (h2 y) (fun e => e ▸ h3)⟩
          · rintro ⟨h1, h2⟩
            exact ⟨⟨h1, fun y hy => h2 y (Or.inl hy)⟩, h2 _ (Or.inr rfl)⟩)
  refine ⟨σ', hr.mono (by simp), by simpa using hin, ?_, hov1, ?_⟩
  · rw [harr, List.take_length]
  · rw [hov, List.take_length]

end Lax185574Proofs.JobMap
