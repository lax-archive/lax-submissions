import Lax185574Proofs.ResolveRam.Glue.PEx2
import Lax185574Proofs.ResolveRam.Glue.R0Out

/-!
Scans over the input of lem:resolve-lift held in the array `x`, for the
item words of level `0`.

`skL A` moves `tf` over a list of words at `tf` of the array `A`
(`skL_run`). It reads only the list, so it applies to an array that is
longer than the data. `tskG` moves `tu` over the word of a graph stored
in `x` (`tskG_run`), as `skipG` does with `pp`. `lvTree` appends the
frame of the item word `0 :: 0 :: w` of the tree word `w` at `tu`, and
moves `tu` to its end (`lvTree_run`). The end of the tree word is the end
of its atom list, or of its extension list if the depth is positive.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Compose
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees

/-! ### Skipping a list of words -/

/-- Move `tf` over one frame of the array `A`. -/
def skNext (A : String) : Com := .assign "tf" (.add (.add (.var "tf") (.get A (.var "tf"))) (.lit 1))

/-- Move `tf` over the list of words at `tf` of the array `A`. -/
def skL (A : String) : Com :=
  .seq (.assign "tn" (.get A (.var "tf"))) (.seq (.assign "tf" (.add (.var "tf") (.lit 1)))
    (forUp "tz" (.var "tn") (skNext A)))

/-- **Skipping a list of words.** -/
theorem skL_run {W : ℕ} {A : String} {X : List ℕ} {p : ℕ} {E : List (List ℕ)} {r : List ℕ} {τ : Env}
    (ha : τ.arrs A = X) (hd : X.drop p = toWord E ++ r) (hp : τ.vars "tf" = p)
    (hB : p + (toWord E).length + 2 < W + 1) (hv : ∀ v ∈ toWord E, v < W + 1) :
    ∃ τ', Run (W + 1) (skL A) τ τ' (20 * (toWord E).length + 20) ∧
      τ'.vars "tf" = p + (toWord E).length ∧ τ'.arrs = τ.arrs ∧ OFr τ τ' ["tn", "tf", "tz"] := by
  obtain ⟨-, hpos, -, -, -⟩ := listAt hd
  have hlen : E.length < (toWord E).length := by
    rw [toWord_words, List.length_cons, Words.length_frames]; omega
  have hx0 : X[p]? = some E.length := by
    have := getElem?_of_drop hd (i := 0) (by rw [toWord_words]; simp)
    simpa [toWord_words] using this
  have hEl : E.length < W + 1 := hv _ (by rw [toWord_words]; simp)
  set τ1 := τ.setVar "tn" E.length
  have r1 : Run (W + 1) (.assign "tn" (.get A (.var "tf"))) τ τ1 3 :=
    (Run.assign (evalB_get (ev_var hp (by omega)) (by rw [ha]; exact hx0) hEl)).mono
      (by simp [Expr.size])
  set τ2 := τ1.setVar "tf" (p + 1)
  have r2 : Run (W + 1) (.assign "tf" (.add (.var "tf") (.lit 1))) τ1 τ2 4 :=
    (Run.assign (ev_add (ev_var (by simp [τ1, hp]) (by omega)) (evalB_lit (by omega)) (by omega))).mono
      (by simp [Expr.size])
  let J : ℕ → Env → Prop := fun z ρ => ρ.vars "tf" = p + 1 + (frames (E.take z)).length ∧
    ρ.vars "tn" = E.length ∧ ρ.arrs = τ.arrs ∧ OFr τ ρ ["tn", "tf", "tz"]
  obtain ⟨τ3, r3, ⟨f3, -, a3, o3⟩, -⟩ := forUp_run (B := W + 1) (i := "tz") (e := .var "tn")
    (body := skNext A) (N := E.length) (K := 7) J (σ := τ2) (by omega)
    (fun z _ ρ hJ _ => ev_var hJ.2.1 (by omega))
    ⟨by simp [τ2, frames], by simp [τ2, τ1], by simp [τ2, τ1],
      (((OFr.setVar τ "tn" _).trans (OFr.setVar τ1 "tf" _)).trans (OFr.setVar τ2 "tz" 0)).mono
        (by decide)⟩
    (by
      rintro z hz ρ ⟨fρ, nρ, aρ, oρ⟩ hzρ
      obtain ⟨hp1, hp2⟩ := hpos z hz.le
      rw [frames_drop hz] at hp2
      have hxz : X[frPos X p z]? = some E[z].length := by
        have := getElem?_of_drop hp2 (i := 0) (by simp); simpa using this
      have hfs := length_frames_take_succ hz
      have hf1 : (frames (E.take (z + 1))).length + 1 ≤ (toWord E).length := by
        have := frames_take_le E (z + 1)
        rw [toWord_words, List.length_cons]; omega
      have hEz : E[z].length < W + 1 := hv _ (by
        rw [toWord_words]; apply List.mem_cons_of_mem
        rw [frames_split E z, frames_drop hz]; simp)
      refine ⟨ρ.setVar "tf" (p + 1 + (frames (E.take (z + 1))).length), ?_, by simp [hzρ], ?_⟩
      · unfold skNext
        refine (Run.assign ?_).mono (by simp [Expr.size])
        have := ev_add (ev_add (ev_var fρ (by omega)) (evalB_get (ev_var fρ (by omega))
          (by rw [aρ, ha, ← hp1]; exact hxz) hEz) (by omega)) (evalB_lit (n := 1) (B := W + 1) (σ := ρ)
          (by omega)) (by omega)
        rw [hfs, show p + 1 + ((frames (E.take z)).length + 1 + E[z].length) =
          p + 1 + (frames (E.take z)).length + E[z].length + 1 by omega]
        exact this
      · refine ⟨by simp, by simp [nρ], by simp [aρ], ?_⟩
        exact ((oρ.trans (OFr.setVar ρ "tf" _)).trans (OFr.setVar _ "tz" _)).mono (by decide))
  refine ⟨τ3, ?_, ?_, a3, o3⟩
  · unfold skL
    refine (Run.seq r1 (Run.seq r2 r3)).mono ?_
    simp only [Expr.size]; omega
  · rw [f3, List.take_length, toWord_words, List.length_cons]; omega

/-! ### Skipping the word of a graph -/

/-- Skip one block of a graph word at `tu`. -/
def tskBlk : Com :=
  .assign "tu" (.add (.add (.var "tu") (.lit 1)) (.add (.get "x" (.var "tu")) (.get "x" (.var "tu"))))

/-- Skip the word of a graph at `tu`. -/
def tskG : Com :=
  .seq (.assign "tgc" (.get "x" (.var "tu"))) (.seq (.assign "tu" (.add (.var "tu") (.lit 1)))
    (forUp "tcv" (.var "tgc") tskBlk))

/-- **Skipping a graph word.** Adapted from `skipG_run`. -/
theorem tskG_run {B n : ℕ} (H : SimpleGraph (Fin n)) {X rest : List ℕ} {p : ℕ} {σ : Env}
    (hX : PreAt "x" X σ) (hd : X.drop p = toWord H ++ rest) (hp : σ.vars "tu" = p)
    (hB : X.length + 1 < B) (hv : ∀ v ∈ X, v < B) :
    ∃ σ', Run B tskG σ σ' (n * 20 + 20) ∧ σ'.vars "tu" = p + (toWord H).length ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp ∧
      (∀ y, y ∉ ["tu", "tgc", "tcv"] → σ'.vars y = σ.vars y) := by
  rw [toWord_graph] at hd
  set bs := graphBlocks H
  have hbl : bs.length = n := graphBlocks_length H
  have hev : ∀ i (h : i < bs.length), bs[i].length = 2 * (bs[i].length / 2) := by
    intro i h
    have := graphBlocks_even H _ (List.getElem_mem h)
    omega
  have hpX : p < X.length := by
    by_contra h
    rw [List.drop_eq_nil_of_le (by omega)] at hd
    simp at hd
  have hx0 : X[p] = n := by
    obtain ⟨_, h⟩ := preAt_seg (j := 0) hd (by simp); simpa using h
  set σ1 := σ.setVar "tgc" n
  have r1 : Run B (.assign "tgc" (.get "x" (.var "tu"))) σ σ1 3 := by
    have := Run.assign (B := B) (σ := σ) (x := "tgc") (e := .get "x" (.var "tu")) (v := n)
      (evalB_get (ev_var hp (by omega)) (by rw [hX.get hpX, hx0]) (by rw [← hx0]; exact hv _ (by simp)))
    simpa [Expr.size] using this
  set σ2 := σ1.setVar "tu" (p + 1)
  have r2 : Run B (.assign "tu" (.add (.var "tu") (.lit 1))) σ1 σ2 4 :=
    (Run.assign (ev_add (ev_var (by simp [σ1, hp]) (by omega)) (evalB_lit (by omega)) (by omega))).mono
      (by simp [Expr.size])
  have hXtail : X.drop (p + 1) = blocksWord bs ++ rest := by
    rw [← List.drop_drop, hd]; simp
  let I : ℕ → Env → Prop := fun k τ => τ.vars "tu" = p + 1 + (blocksWord (bs.take k)).length ∧
    τ.vars "tgc" = n ∧ τ.arrs = σ.arrs
  have hlenX : p + 1 + (blocksWord bs).length ≤ X.length := by
    have := congrArg List.length hXtail
    rw [List.length_drop, List.length_append] at this
    omega
  have hnB : n < B := by rw [← hx0]; exact hv _ (List.getElem_mem hpX)
  obtain ⟨σ', hr, hI, -⟩ := forUp_run (B := B) (i := "tcv") (e := .var "tgc") (body := tskBlk)
    (N := n) (K := 12) I (σ := σ2) (by omega) (fun k _ τ hI _ => ev_var hI.2.1 (by omega))
    ⟨by simp [σ2, blocksWord], by simp [σ2, σ1], by simp [σ2, σ1]⟩
    (by
      rintro k hk τ ⟨hpp, hgc, har⟩ hcv
      have hk' : k < bs.length := by omega
      have hdrop : X.drop (p + 1 + (blocksWord (bs.take k)).length) =
          blk bs[k] ++ (blocksWord (bs.drop (k + 1)) ++ rest) := by
        have e1 : blocksWord bs = blocksWord (bs.take k) ++ blocksWord (bs.drop k) := by
          rw [← blocksWord_append, List.take_append_drop]
        rw [← List.drop_drop, hXtail, e1, List.append_assoc, List.drop_left, blocksWord_drop hk',
          List.append_assoc]
      obtain ⟨hlt, hval⟩ := preAt_seg (j := 0) hdrop (by simp [blk])
      simp only [blk, List.getElem_cons_zero, Nat.add_zero] at hlt hval
      have hd2 := hev k hk'
      have hgetτ : (τ.arrs "x")[p + 1 + (blocksWord (bs.take k)).length]? = some (bs[k].length / 2) := by
        rw [har, hX.get hlt, hval]
      have hdB : bs[k].length / 2 < B := by rw [← hval]; exact hv _ (List.getElem_mem _)
      have hsum : (blocksWord (bs.take (k + 1))).length =
          (blocksWord (bs.take k)).length + 1 + (bs[k].length / 2 + bs[k].length / 2) := by
        rw [blocksWord_take_succ hk']; omega
      have hle := blocksWord_take_le bs (k + 1)
      refine ⟨τ.setVar "tu" (p + 1 + (blocksWord (bs.take (k + 1))).length), ?_, by simp [hcv],
        by simp, by simp [hgc], by simp [har]⟩
      obtain ⟨a0, ha0⟩ : ∃ a0, (blocksWord (bs.take k)).length = a0 := ⟨_, rfl⟩
      obtain ⟨g0, hg0⟩ : ∃ g0, bs[k].length / 2 = g0 := ⟨_, rfl⟩
      obtain ⟨c0, hc0⟩ : ∃ c0, (blocksWord bs).length = c0 := ⟨_, rfl⟩
      obtain ⟨h0, hh0⟩ : ∃ h0, (blocksWord (bs.take (k + 1))).length = h0 := ⟨_, rfl⟩
      rw [ha0, hg0, hh0] at hsum
      rw [hh0, hc0] at hle
      rw [hc0] at hlenX
      rw [ha0] at hpp hgetτ
      rw [hg0] at hgetτ hdB
      have e1 : (Expr.add (.var "tu") (.lit 1)).evalB B τ = some (p + 1 + a0 + 1) :=
        ev_add (ev_var hpp (by omega)) (evalB_lit (by omega)) (by omega)
      have e2 : (Expr.get "x" (.var "tu")).evalB B τ = some g0 :=
        evalB_get (ev_var hpp (by omega)) hgetτ hdB
      have e3 := ev_add e2 e2 (show g0 + g0 < B by omega)
      have e4 := ev_add e1 e3 (show p + 1 + a0 + 1 + (g0 + g0) < B by omega)
      rw [hh0]
      refine (Run.assign e4).mono ?_ |>.congr (by congr 1; omega)
      simp [Expr.size])
  obtain ⟨hpp', hgc', har'⟩ := hI
  have hrun : Run B tskG σ σ' (n * 20 + 20) := by
    unfold tskG
    refine (Run.seq r1 (Run.seq r2 hr)).mono ?_
    simp only [Expr.size]; omega
  refine ⟨σ', hrun, ?_, har', hrun.out_eq (by decide), hrun.frame_inp (by decide),
    fun y hy => hrun.frame_var y (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [tskG, tskBlk, forUp, Com.wvars]; tauto)⟩
  have hbw : (blocksWord (bs.take n)).length = (blocksWord (graphBlocks H)).length := by
    rw [List.take_of_length_le (by rw [hbl])]
  rw [hpp', hbw, toWord_graph]
  simp only [List.length_cons]; omega

end Lax185574Proofs.ResolveRam.Glue
