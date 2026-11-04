import Lax185574Proofs.MC.Brute.Step
import Lax185574Proofs.MainRam.ValidProg

/-!
The adjacency matrix of the input graph, for the brute-force thread.

After the two header entries of the compressed sparse row word, `grBody`
reads the offsets and the targets (`readArr`), builds the matrix `A` of
the validation program (`adjPh`), and copies it into the array `bfA` of
the evaluation machine, which has the length of every other array of
the machine. `grBody_run` gives the run, with `adjOf` deciding the
adjacency of `G`.
-/

namespace Lax185574Proofs.MC.Brute

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MainRam Lax185574Proofs.Compose Lax271696.GraphEncoding
open Classical

/-- Copy the matrix `A` into `bfA`. -/
def cpA : Com :=
  forUp "bfi" (.mul (.var "n") (.var "n")) (.store "bfA" (.var "bfi") (.get "A" (.var "bfi")))

/-- Read the offsets and targets and build the matrix. -/
def grBody : Com :=
  .seq (.assign "cnt" (.add (.var "n") (.lit 1))) (.seq (readArr "of")
  (.seq (.assign "cnt" (.add (.var "E") (.var "E"))) (.seq (readArr "tg")
  (.seq adjPh (.seq (.assign "bfn" (.var "n")) cpA)))))

theorem cpA_run {B N : ℕ} {f : ℕ → ℕ} (hNB : N * N < B) (hf : ∀ i, f i < B) {σ : Env}
    (hn : σ.vars "n" = N) (hA : σ.arrs "A" = arrOf (N * N) f) (hb : (σ.arrs "bfA").length = B)
    (hz : ∀ i, (σ.arrs "bfA").getD i 0 = 0) :
    ∃ σ', Run B cpA σ σ' (N * N * 20 + 10) ∧ (σ'.arrs "bfA").length = B ∧
      (∀ i, (σ'.arrs "bfA").getD i 0 = if i < N * N then f i else 0) := by
  obtain ⟨σ', hr, ⟨hn', hA', hb', hv'⟩, -⟩ := forUp_run (B := B) (i := "bfi")
    (e := .mul (.var "n") (.var "n")) (body := .store "bfA" (.var "bfi") (.get "A" (.var "bfi")))
    (N := N * N) (K := 4)
    (fun k τ => τ.vars "n" = N ∧ τ.arrs "A" = arrOf (N * N) f ∧ (τ.arrs "bfA").length = B ∧
      ∀ i, (τ.arrs "bfA").getD i 0 = if i < k then f i else 0) (σ := σ) hNB
    (fun k _ τ hI _ => by
      have h1 : τ.vars "n" < B := by
        rw [hI.1]; rcases Nat.eq_zero_or_pos N with h | h
        · subst h; omega
        · nlinarith
      have := evalB_bin (op := .mul) (evalB_var (σ := τ) h1) (evalB_var h1) (by simp [hI.1]; omega)
      simpa [hI.1] using this)
    ⟨by simp [hn], by simp [hA], by simp [hb], fun i => by
      simp only [arrs_setVar, Nat.not_lt_zero, if_false]; exact hz i⟩
    (by
      rintro k hk τ ⟨hn1, hA1, hb1, hv1⟩ hik
      refine ⟨τ.setArr "bfA" k (f k), (Run.store (idx := k) (v := f k) (evalB_var (by omega) |>.trans
        (by rw [hik])) ?_ (by omega)).mono (by simp), by simp [hik], ?_⟩
      · rw [evalB_get_iff]
        exact ⟨k, evalB_var (by omega) |>.trans (by rw [hik]), by rw [hA1]; exact getElem?_arrOf _ hk,
          hf k⟩
      · refine ⟨by simp [hn1], by simp [hA1], by simp [hb1], fun i => ?_⟩
        simp only [arrs_setVar, arrs_setArr, if_true]
        rw [List.getD_eq_getElem?_getD, List.getElem?_set]
        by_cases hki : k = i
        · subst hki; rw [if_pos rfl, if_pos (by omega), if_pos (by omega)]; rfl
        · rw [if_neg hki, ← List.getD_eq_getElem?_getD, hv1 i]
          by_cases h : i < k
          · simp [h, show i < k + 1 by omega]
          · simp [h, show ¬ i < k + 1 by omega])
  refine ⟨σ', hr.mono ?_, hb', hv'⟩
  simp
  nlinarith

theorem div_lt_of_rm {N i : ℕ} (hi : i < N * N) : i / N < N := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst h; simp at hi
  · exact Nat.div_lt_of_lt_mul hi

/-- **The matrix.** From the offsets and targets on the input, `grBody`
builds the adjacency matrix of `G` in `bfA`. -/
theorem grBody_run {B n : ℕ} {G : SimpleGraph (Fin n)} {g rest : List ℕ}
    (hg : EncodesGraph g n G) {σ : Env} (hn : σ.vars "n" = n) (hE : σ.vars "E" = edgeCount g)
    (hinp : σ.inp = ofL g n ++ (tgL g n ++ rest)) (hB : n * n + 2 * edgeCount g + 2 < B)
    (hv : ∀ a ∈ g, a < B)
    (hof : σ.arrs "of" = arrOf (n + 1) (fun _ => 0))
    (htg : σ.arrs "tg" = arrOf (2 * edgeCount g) (fun _ => 0))
    (hA : σ.arrs "A" = arrOf (n * n) (fun _ => 0))
    (hbl : (σ.arrs "bfA").length = B) (hbz : ∀ i, (σ.arrs "bfA").getD i 0 = 0) :
    ∃ σ', Run B grBody σ σ' (50 * (n * n + g.length) + 100) ∧ σ'.inp = rest ∧
      σ'.vars "bfn" = n ∧ (σ'.arrs "bfA").length = B ∧ (∀ i, (σ'.arrs "bfA").getD i 0 ≤ 1) ∧
      (∀ u v : Fin n, adjOf σ' n u v = decide (G.Adj u v)) := by
  obtain ⟨hgs, hofl, htgl⟩ := graph_split hg
  set E := edgeCount g with hEdef
  have hgl : g.length = 3 + n + 2 * E := hg.length_eq
  have hofB : ∀ a ∈ ofL g n, a < B := fun a ha => hv a (by rw [hgs]; simp [ha])
  have htgB : ∀ a ∈ tgL g n, a < B := fun a ha => hv a (by rw [hgs]; simp [ha])
  have hnB : n + 1 < B := by nlinarith
  -- offsets
  have e1 : (Expr.add (.var "n") (.lit 1)).evalB B σ = some (n + 1) := by
    simp only [Expr.add_def, evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
    exact ⟨σ.vars "n", 1, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, by simp [hn], by omega⟩
  set σ1 := σ.setVar "cnt" (n + 1)
  obtain ⟨σ2, r2, hi2, ha2, fv2, fa2, -⟩ := readArr_spec (B := B) "of" (ofL g n) (tgL g n ++ rest)
    (by rw [hofl]; omega) hofB (σ := σ1) (by simp [σ1, hofl]) (by simp [σ1, hinp]) (by simp [σ1, hof, hofl])
  have hE2 : σ2.vars "E" = E := by rw [fv2 "E" (by rw [readArr_wvars]; decide)]; simp [σ1, hE]
  have hn2 : σ2.vars "n" = n := by rw [fv2 "n" (by rw [readArr_wvars]; decide)]; simp [σ1, hn]
  -- targets
  have e3 : (Expr.add (.var "E") (.var "E")).evalB B σ2 = some (2 * E) := by
    simp only [Expr.add_def, evalB_bin_iff, evalB_var_iff]
    exact ⟨σ2.vars "E", σ2.vars "E", ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, by simp [hE2]; omega, by omega⟩
  set σ3 := σ2.setVar "cnt" (2 * E)
  obtain ⟨σ4, r4, hi4, ha4, fv4, fa4, -⟩ := readArr_spec (B := B) "tg" (tgL g n) rest
    (by rw [htgl]; omega) htgB (σ := σ3) (by simp [σ3, htgl]) (by simp [σ3, hi2])
    (by simp [σ3, fa2 "tg" (by rw [readArr_warrs]; decide), σ1, htg, htgl])
  have hn4 : σ4.vars "n" = n := by rw [fv4 "n" (by rw [readArr_wvars]; decide)]; simp [σ3, hn2]
  -- the matrix
  set o : ℕ → ℕ := fun i => (ofL g n).getD i 0 with ho
  set t : ℕ → ℕ := fun j => (tgL g n).getD j 0 with ht
  have hmono : ∀ u < n, o u ≤ o (u + 1) := fun u hu => by
    have := hg.offset_mono u hu
    rwa [offset_eq hg (by omega), offset_eq hg (by omega)] at this
  have hlast : o n = 2 * E := by
    have := hg.offset_last; rwa [offset_eq hg le_rfl] at this
  have hoB : ∀ i ≤ n, o i ≤ 2 * E := by
    intro i hi
    induction hi using Nat.decreasingInduction with
    | self => exact le_of_eq hlast
    | of_succ k hk ih => exact le_trans (hmono k hk) ih
  have htB : ∀ j < 2 * E, t j < n := fun j hj => by
    have := hg.target_lt j hj; rwa [target_eq hg] at this
  obtain ⟨σ5, r5, hA5, hn5, ha5, -, hi5⟩ := adjPh_run (B := B) (N := n) (D := 2 * E) (o := o)
    (t := t) (by omega) hmono hoB htB hn4
    (by rw [fa4 "of" (by rw [readArr_warrs]; decide)]; simp only [σ3, arrs_setVar]; rw [ha2]; conv_lhs => rw [list_eq_arrOf (ofL g n), hofl])
    (by rw [ha4]; conv_lhs => rw [list_eq_arrOf (tgL g n), htgl])
    (by rw [fa4 "A" (by rw [readArr_warrs]; decide)]; simp only [σ3, arrs_setVar]
        rw [fa2 "A" (by rw [readArr_warrs]; decide)]
        simp [σ3, σ1, hA])
  have hbA5 : σ5.arrs "bfA" = σ.arrs "bfA" := by
    rw [ha5 "bfA" (by decide), fa4 "bfA" (by rw [readArr_warrs]; decide)]; simp only [σ3, arrs_setVar]
    rw [fa2 "bfA" (by rw [readArr_warrs]; decide)]; simp [σ3, σ1]
  set σ6 := σ5.setVar "bfn" n
  obtain ⟨σ7, r7, hl7, hv7⟩ := cpA_run (B := B) (N := n)
    (f := fun i => if InBlock o t (i / n) (i % n) then 1 else 0) (by omega)
    (fun i => by split <;> omega) (σ := σ6) (by simp [σ6, hn5]) (by simp [σ6, hA5])
    (by simp [σ6, hbA5, hbl]) (by intro i; simp only [σ6, arrs_setVar, hbA5]; exact hbz i)
  have hn7 : σ7.vars "bfn" = n := by
    rw [r7.frame_var "bfn" (by simp [cpA, forUp, Com.wvars])]; simp [σ6]
  have hinp7 : σ7.inp = rest := by
    rw [r7.frame_inp (by simp [cpA, forUp, Com.reads])]; simp [σ6, hi5, hi4]
  refine ⟨σ7, ?_, hinp7, hn7, hl7, fun i => by rw [hv7]; split_ifs <;> omega, fun u v => ?_⟩
  · unfold grBody
    refine ((Run.seq (Run.assign e1) (Run.seq r2 (Run.seq (Run.assign e3) (Run.seq r4
      (Run.seq r5 (Run.seq (Run.assign (v := n) ?_) r7))))))).mono ?_
    · simp [hn5]; omega
    · simp only [Expr.size, size_add, size_var, size_lit, ofL, tgL] at *
      nlinarith
  · simp only [adjOf]
    have hu := u.isLt
    have hvv := v.isLt
    have hlt : (u : ℕ) * n + v < n * n := rowMajor_lt hu hvv
    rw [hv7, if_pos hlt]
    obtain ⟨d1, d2⟩ := div_mod_rm (N := n) (u := u) hvv
    simp only [d1, d2]
    have := inBlock_iff hg u v
    by_cases hb : G.Adj u v
    · rw [if_pos (this.mpr hb)]; simp [hb]
    · rw [if_neg (fun h => hb (this.mp h))]; simp [hb]

end Lax185574Proofs.MC.Brute
