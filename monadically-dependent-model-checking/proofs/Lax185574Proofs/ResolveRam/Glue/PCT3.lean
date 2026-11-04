import Lax185574Proofs.ResolveRam.Glue.PCT2
import Lax185574Proofs.ResolveRam.Glue.Input

/-!
The color table as a tape program.

`ctIn` reads the input of the composite, computes the classes of the
colors, computes from the distance matrix the codes of the distances from
the class of `P` and from the class of `Q` to every class (`ctTab`),
finds the sorted colors with their first vertices (`rounds`) and writes
the word of the color table (`ctIn_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib
open Lax808846Proofs.Reasoning.Lib.Csr Lax185574Proofs.Words Lax185574Proofs.Conversions.Ram
open Lax185574Proofs.StpRam Lax185574.PartialGraphs Lax185574.WordEncoding Lax185574Proofs.ResolveRam

/-! ### The tables -/

/-- The two tables, from the distance matrix: the codes of the distances
from every vertex to the class of `P` and their least value over each
class into `c1`, and the same for `Q` into `ct`. -/
def ctTab : Com :=
  .seq (dtLoop "dm" "gp") (.seq (clsLoop "c1") (.seq (dtLoop "dm" "gq") (clsLoop "ct")))

theorem ctTab_run {B n P Q : ℕ} {col cl : ℕ → ℕ} {f : ℕ → ℕ → ℕ} {D : List ℕ} {σ : Env}
    (hn : σ.vars "n" = n) (hco : σ.arrs "co" = arrOf n col) (hcl : σ.arrs "cl" = arrOf n cl)
    (hdd : σ.arrs "dd" = D) (hD : ∀ u < n, ∀ x < n, D[2 + u * (n + 1) + x]? = some (f u x))
    (hP : σ.vars "gp" = P) (hQ : σ.vars "gq" = Q)
    (hdm : (σ.arrs "dm").length = n) (hct : (σ.arrs "ct").length = n) (hc1 : (σ.arrs "c1").length = n)
    (hclc : ∀ v < n, cl v < n) (hfB : ∀ u < n, ∀ x < n, f u x < B) (hcolB : ∀ v < n, col v < B)
    (hPB : P < B) (hQB : Q < B) (hDB : D.length < B) (hnB : n + 1 < B) :
    ∃ σ', Run B ctTab σ σ' (2 * (n * (n * 88 + 17) + 6) + 2 * (n * 60 + 20)) ∧
      σ'.arrs "c1" = arrOf n (clsVal cl (dtVal col f n P) n) ∧
      σ'.arrs "ct" = arrOf n (clsVal cl (dtVal col f n Q) n) ∧
      σ'.arrs "co" = σ.arrs "co" ∧ σ'.vars "n" = n ∧
      (∀ a, a ∉ ctTab.warrs → σ'.arrs a = σ.arrs a) ∧ (∀ x, x ∉ ctTab.wvars → σ'.vars x = σ.vars x) := by
  have hd : "dm" ≠ "co" ∧ "dm" ≠ "dd" := by decide
  obtain ⟨σ1, r1, hC1, hm1⟩ := dtLoop_run (B := B) (dst := "dm") (Xv := "gp") (f := f) hd (by decide)
    ⟨hn, hP, hco, hdd⟩ hD hfB hcolB hPB hDB hnB hdm
  have htB : ∀ X, ∀ v < n, dtVal col f n X v < B := fun X v hv => dtVal_lt hv hfB n le_rfl
  obtain ⟨σ2, r2, hc12, hn2, hcl2, hdm2⟩ := clsLoop_run (B := B) (dst := "c1") (by decide) hC1.vn
    (by rw [r1.frame_arr "cl" (by decide), hcl]) hm1 hclc (htB P) hnB
    (by rw [r1.frame_arr "c1" (by decide), hc1])
  have hC2 : DtCtx "gq" n Q col D σ2 := ⟨hn2,
    by rw [r2.frame_var "gq" (by decide), r1.frame_var "gq" (by decide), hQ],
    by rw [r2.frame_arr "co" (by decide), hC1.aco], by rw [r2.frame_arr "dd" (by decide), hC1.add]⟩
  obtain ⟨σ3, r3, hC3, hm3⟩ := dtLoop_run (B := B) (dst := "dm") (Xv := "gq") (f := f) hd (by decide)
    hC2 hD hfB hcolB hQB hDB hnB (by rw [hdm2, hm1]; simp)
  obtain ⟨σ4, r4, hct4, hn4, -, -⟩ := clsLoop_run (B := B) (dst := "ct") (by decide) hC3.vn
    (by rw [r3.frame_arr "cl" (by decide), hcl2, r1.frame_arr "cl" (by decide), hcl]) hm3 hclc (htB Q) hnB
    (by rw [r3.frame_arr "ct" (by decide), r2.frame_arr "ct" (by decide), r1.frame_arr "ct" (by decide), hct])
  have hrun : Run B ctTab σ σ4 (2 * (n * (n * 88 + 17) + 6) + 2 * (n * 60 + 20)) := by
    unfold ctTab
    exact (Run.seq r1 (Run.seq r2 (Run.seq r3 r4))).mono (by omega)
  refine ⟨σ4, hrun, ?_, hct4, hrun.frame_arr "co" (by decide), hn4, fun a ha => hrun.frame_arr a ha,
    fun x hx => hrun.frame_var x hx⟩
  rw [r4.frame_arr "c1" (by decide), r3.frame_arr "c1" (by decide), hc12]

/-! ### The output -/

/-- One color of the output. -/
def oBody : Com :=
  .seq (.write (.get "sy" (.var "c"))) (.seq (.write (.get "c1" (.get "su" (.var "c"))))
    (.write (.get "ct" (.get "su" (.var "c")))))

/-- Write the color table. -/
def outL : Com := .seq (.write (.mul (.lit 3) (.var "cnt"))) (forUp "c" (.var "cnt") oBody)

theorem outL_run {B n : ℕ} {L : List ℕ} {g₁ g₂ h : ℕ → ℕ} {f₁ f₂ : ℕ → ℕ} {σ : Env}
    (hcnt : σ.vars "cnt" = L.length)
    (hsy : ∀ j (hj : j < L.length), (σ.arrs "sy")[j]? = some L[j])
    (hsu : ∀ j (hj : j < L.length), (σ.arrs "su")[j]? = some (h L[j]))
    (hc1 : σ.arrs "c1" = arrOf n g₁) (hct : σ.arrs "ct" = arrOf n g₂)
    (hh : ∀ y ∈ L, h y < n) (h1 : ∀ y ∈ L, g₁ (h y) = f₁ y) (h2 : ∀ y ∈ L, g₂ (h y) = f₂ y)
    (hLB : ∀ y ∈ L, y < B ∧ f₁ y < B ∧ f₂ y < B) (hnB : n < B) (h3B : 3 * L.length + 3 < B) :
    ∃ σ', Run B outL σ σ' (L.length * 30 + 20) ∧
      σ'.out = σ.out ++ ((L.flatMap fun Y => [Y, f₁ Y, f₂ Y]).length :: L.flatMap fun Y => [Y, f₁ Y, f₂ Y]) := by
  set σ0 : Env := { σ with out := σ.out ++ [3 * L.length] }
  have r0 : Run B (.write (.mul (.lit 3) (.var "cnt"))) σ σ0 4 :=
    (Run.write (by simp [hcnt]; omega)).mono (by simp)
  let I : ℕ → Env → Prop := fun k τ => τ.vars "cnt" = L.length ∧ τ.arrs = σ.arrs ∧
    τ.out = σ.out ++ [3 * L.length] ++ (L.take k).flatMap fun Y => [Y, f₁ Y, f₂ Y]
  obtain ⟨σ', r1, ⟨-, -, ho⟩, -⟩ := forUp_run (B := B) (i := "c") (e := .var "cnt") (body := oBody)
    (N := L.length) (K := 18) I (σ := σ0) (by omega)
    (fun k _ τ hI _ => by rw [evalB_var_iff, hI.1]; omega)
    ⟨by simp [σ0, hcnt], by simp [σ0], by simp [σ0]⟩
    (by
      rintro k hk τ ⟨hc, ha, hoτ⟩ hck
      have hy := hLB _ (List.getElem_mem hk)
      have hhk := hh _ (List.getElem_mem hk)
      set τ1 : Env := { τ with out := τ.out ++ [L[k]] }
      set τ2 : Env := { τ1 with out := τ1.out ++ [f₁ L[k]] }
      set τ3 : Env := { τ2 with out := τ2.out ++ [f₂ L[k]] }
      have e1 : (Expr.get "sy" (.var "c")).evalB B τ = some L[k] := by
        simp only [evalB_get_iff, evalB_var_iff]
        exact ⟨k, ⟨hck.symm, by omega⟩, by rw [ha]; exact hsy k hk, hy.1⟩
      have e2 : (Expr.get "c1" (.get "su" (.var "c"))).evalB B τ1 = some (f₁ L[k]) := by
        simp only [evalB_get_iff, evalB_var_iff]
        refine ⟨h L[k], ⟨k, ⟨by simp [τ1, hck], by simp [τ1, hck]; omega⟩, by simp [τ1, ha]; exact hsu k hk,
          by omega⟩, ?_, hy.2.1⟩
        simp [τ1, ha, hc1, hhk, h1 _ (List.getElem_mem hk)]
      have e3 : (Expr.get "ct" (.get "su" (.var "c"))).evalB B τ2 = some (f₂ L[k]) := by
        simp only [evalB_get_iff, evalB_var_iff]
        refine ⟨h L[k], ⟨k, ⟨by simp [τ2, τ1, hck], by simp [τ2, τ1, hck]; omega⟩,
          by simp [τ2, τ1, ha]; exact hsu k hk, by omega⟩, ?_, hy.2.2⟩
        simp [τ2, τ1, ha, hct, hhk, h2 _ (List.getElem_mem hk)]
      refine ⟨τ3, (Run.seq (Run.write e1) (Run.seq (Run.write e2) (Run.write e3))).mono (by simp),
        by simp [τ3, τ2, τ1, hck], by simp [τ3, τ2, τ1, hc], by simp [τ3, τ2, τ1, ha], ?_⟩
      simp only [τ3, τ2, τ1, hoτ, List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some,
        List.flatMap_append, List.append_assoc]
      simp)
  refine ⟨σ', (Run.seq r0 r1).mono (by simp; omega), ?_⟩
  rw [ho, List.take_of_length_le le_rfl]
  simp [List.length_flatMap]
  ring

end Lax185574Proofs.ResolveRam.Glue
