import Lax185574Proofs.ResolveRam.Glue.Head
import Lax185574Proofs.MC.Glue.Out
import Lax185574Proofs.Compose.GraphLength

/-!
Reading the input of the first round of the glue program of
lem:resolve-lift into an array, and finding its parts there.

`rdX` reads the `nx` entries of the input into the array `x` and their
maximum into `mx` (`rdX_run`). `skipG` moves the position `pp` over the
word of a graph on `Fin n` stored in `x` (`skipG_run`): the word is `n`
and a block per vertex, the number `d` of its neighbors and the pairs
`1, z`. So after the colors and the two graphs `pp` is the length of the
word of the partial graph, and `P`, `Q`, the sign and the family follow
(`locate_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC.Glue Lax185574Proofs.Compose
open Lax185574.WordEncoding Lax185574.PartialGraphs

/-! ### Reading the input -/

/-- Read one entry into `x` at `ci` and keep the maximum in `mx`. -/
def rdBody : Com :=
  .seq (.read "v") (.seq (.store "x" (.var "ci") (.var "v"))
    (.ite (.lt (.var "mx") (.var "v")) (.assign "mx" (.var "v")) .skip))

/-- Read `nx` entries into `x`, with their maximum in `mx`. -/
def rdX : Com := .seq (.assign "mx" (.lit 0)) (forUp "ci" (.var "nx") rdBody)

theorem maxEntry_take_succ {x : List ℕ} {k : ℕ} (h : k < x.length) :
    maxEntry (x.take (k + 1)) = max (maxEntry (x.take k)) x[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem h, Option.toList_some, maxEntry_append_single]

/-- **Reading the input.** -/
theorem rdX_run {B : ℕ} {x rest : List ℕ} {σ : Env} (hinp : σ.inp = x ++ rest)
    (hnx : σ.vars "nx" = x.length) (hlen : x.length ≤ (σ.arrs "x").length) (hB : x.length + 1 < B)
    (hv : ∀ v ∈ x, v < B) :
    ∃ σ', Run B rdX σ σ' (x.length * 30 + 10) ∧ σ'.inp = rest ∧ σ'.vars "mx" = maxEntry x ∧
      (∀ i (h : i < x.length), (σ'.arrs "x")[i]? = some x[i]) ∧
      (σ'.arrs "x").length = (σ.arrs "x").length ∧ σ'.out = σ.out ∧
      (∀ y, y ∉ ["mx", "ci", "v"] → σ'.vars y = σ.vars y) ∧ (∀ a, a ≠ "x" → σ'.arrs a = σ.arrs a) := by
  set L := (σ.arrs "x").length
  let I : ℕ → Env → Prop := fun k τ => τ.inp = x.drop k ++ rest ∧ τ.vars "mx" = maxEntry (x.take k) ∧
    (∀ i (h : i < k) (h' : i < x.length), (τ.arrs "x")[i]? = some x[i]) ∧ (τ.arrs "x").length = L ∧
    τ.vars "nx" = x.length
  set σ0 := σ.setVar "mx" 0
  have hmxB : ∀ k, maxEntry (x.take k) < B := fun k => by
    have : ∀ v ∈ x.take k, v < B := fun v hv' => hv v (List.mem_of_mem_take hv')
    have := maxEntry_le (b := B - 1) (fun v hv' => by have := this v hv'; omega)
    omega
  obtain ⟨σ', hr, hI, hci⟩ := forUp_run (B := B) (i := "ci") (e := .var "nx") (body := rdBody)
    (N := x.length) (K := 12) I (σ := σ0) (by omega)
    (fun k _ τ hI _ => ev_var hI.2.2.2.2 (by omega))
    ⟨by simp [σ0, hinp], by simp [σ0, maxEntry], fun i h => absurd h (by omega), by simp [σ0, L],
      by simp [σ0, hnx]⟩
    (by
      rintro k hk τ ⟨hin, hmx, hx, hL, hn⟩ hcik
      have hcons : x.drop k = x[k] :: x.drop (k + 1) := List.drop_eq_getElem_cons hk
      have hxk : x[k] < B := hv _ (List.getElem_mem hk)
      set τ1 : Env := { τ.setVar "v" x[k] with inp := x.drop (k + 1) ++ rest }
      have r1 : Run B (.read "v") τ τ1 1 := Run.read (by rw [hin, hcons]; rfl)
      have r2 : Run B (.store "x" (.var "ci") (.var "v")) τ1 (τ1.setArr "x" k x[k]) 3 :=
        Run.store (ev_var (by simp [τ1, hcik]) (by omega)) (ev_var (by simp [τ1]) hxk)
          (by simp [τ1, hL]; omega)
      set τ2 := τ1.setArr "x" k x[k]
      have hτ2mx : τ2.vars "mx" = maxEntry (x.take k) := by simp [τ2, τ1, hmx]
      have hτ2v : τ2.vars "v" = x[k] := by simp [τ2, τ1]
      have hc := evalB_condLt (B := B) (σ := τ2) (e := .var "mx") (f := .var "v")
        (ev_var hτ2mx (hmxB k)) (ev_var hτ2v hxk)
      have hstore : ∀ i (h : i < k + 1) (h' : i < x.length), (τ2.arrs "x")[i]? = some x[i] := by
        intro i h h'
        simp only [τ2, τ1, arrs_setArr, arrs_setVar, ↓reduceIte, List.getElem?_set]
        rcases Nat.lt_or_ge i k with hik | hik
        · rw [if_neg (by omega)]; exact hx i hik h'
        · obtain rfl : i = k := by omega
          rw [if_pos rfl, if_pos (by rw [hL]; omega)]
      by_cases hlt : maxEntry (x.take k) < x[k]
      · refine ⟨τ2.setVar "mx" x[k], ?_, by simp [τ2, τ1, hcik], ?_⟩
        · unfold rdBody
          exact (Run.seq r1 (Run.seq r2 (Run.ite_true (by rw [hc, decide_eq_true hlt])
            (Run.assign (ev_var hτ2v hxk))))).mono (by simp [Expr.size, Cond.size])
        · refine ⟨by simp [τ2, τ1], by simp [maxEntry_take_succ hk]; omega, fun i h h' => ?_,
            by simp [τ2, τ1, hL], by simp [τ2, τ1, hn]⟩
          simpa using hstore i h h'
      · refine ⟨τ2, ?_, by simp [τ2, τ1, hcik], ?_⟩
        · unfold rdBody
          exact (Run.seq r1 (Run.seq r2 (Run.ite_false (by rw [hc, decide_eq_false hlt])
            Run.skip))).mono (by simp [Expr.size, Cond.size])
        · refine ⟨by simp [τ2, τ1], by simp [τ2, τ1, maxEntry_take_succ hk, hmx]; omega,
            fun i h h' => ?_, by simp [τ2, τ1, hL], by simp [τ2, τ1, hn]⟩
          simpa using hstore i h h')
  obtain ⟨hin', hmx', hx', hL', -⟩ := hI
  have hrun : Run B rdX σ σ' (x.length * 30 + 10) := by
    unfold rdX
    refine (Run.seq (Run.assign (evalB_lit (by omega))) hr).mono ?_
    simp only [Expr.size]; omega
  refine ⟨σ', hrun, by simpa using hin', by simpa using hmx', fun i h => hx' i h h, by rw [hL'],
    hrun.out_eq (by decide), fun y hy => hrun.frame_var y (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [rdX, rdBody, forUp, Com.wvars]; tauto),
    fun a ha => hrun.frame_arr a (by simp [rdX, rdBody, forUp, Com.warrs]; exact ha)⟩

/-! ### Skipping a graph word -/

/-- Skip one block of a graph word at `pp`. -/
def skipBlk : Com :=
  .assign "pp" (.add (.add (.var "pp") (.lit 1)) (.add (.get "x" (.var "pp")) (.get "x" (.var "pp"))))

/-- Skip the word of a graph at `pp`. -/
def skipG : Com :=
  .seq (.assign "gc" (.get "x" (.var "pp"))) (.seq (.assign "pp" (.add (.var "pp") (.lit 1)))
    (forUp "cv" (.var "gc") skipBlk))

/-- The array holds the list `X` as a prefix. -/
def PreAt (a : String) (X : List ℕ) (τ : Env) : Prop := ∀ i (h : i < X.length), (τ.arrs a)[i]? = some X[i]

theorem PreAt.get {a : String} {X : List ℕ} {τ : Env} (h : PreAt a X τ) {i : ℕ} (hi : i < X.length) :
    (τ.arrs a)[i]? = some X[i] := h i hi

theorem preAt_seg {X : List ℕ} {p : ℕ} {u rest : List ℕ} (h : X.drop p = u ++ rest) {j : ℕ}
    (hj : j < u.length) : ∃ hh : p + j < X.length, X[p + j] = u[j] := by
  have hl : p + j < X.length := by
    have := congrArg List.length h; simp at this; omega
  refine ⟨hl, ?_⟩
  have : (X.drop p)[j]'(by simp; omega) = (u ++ rest)[j]'(by simp; omega) := by simp only [h]
  rw [List.getElem_drop, List.getElem_append_left hj] at this
  exact this

/-- **Skipping a graph word.** -/
theorem skipG_run {B n : ℕ} (H : SimpleGraph (Fin n)) {X rest : List ℕ} {p : ℕ} {σ : Env}
    (hX : PreAt "x" X σ) (hd : X.drop p = toWord H ++ rest) (hp : σ.vars "pp" = p)
    (hB : X.length + 1 < B) (hv : ∀ v ∈ X, v < B) :
    ∃ σ', Run B skipG σ σ' (n * 20 + 20) ∧ σ'.vars "pp" = p + (toWord H).length ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp ∧
      (∀ y, y ∉ ["pp", "gc", "cv"] → σ'.vars y = σ.vars y) := by
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
  set σ1 := σ.setVar "gc" n
  have r1 : Run B (.assign "gc" (.get "x" (.var "pp"))) σ σ1 3 := by
    have := Run.assign (B := B) (σ := σ) (x := "gc") (e := .get "x" (.var "pp")) (v := n)
      (evalB_get (ev_var hp (by omega)) (by rw [hX.get hpX, hx0]) (by rw [← hx0]; exact hv _ (by simp)))
    simpa [Expr.size] using this
  set σ2 := σ1.setVar "pp" (p + 1)
  have r2 : Run B (.assign "pp" (.add (.var "pp") (.lit 1))) σ1 σ2 4 :=
    (Run.assign (ev_add (ev_var (by simp [σ1, hp]) (by omega)) (evalB_lit (by omega)) (by omega))).mono
      (by simp [Expr.size])
  have hXtail : X.drop (p + 1) = blocksWord bs ++ rest := by
    rw [← List.drop_drop, hd]; simp
  let I : ℕ → Env → Prop := fun k τ => τ.vars "pp" = p + 1 + (blocksWord (bs.take k)).length ∧
    τ.vars "gc" = n ∧ τ.arrs = σ.arrs
  have hlenX : p + 1 + (blocksWord bs).length ≤ X.length := by
    have := congrArg List.length hXtail
    rw [List.length_drop, List.length_append] at this
    omega
  have hnB : n < B := by rw [← hx0]; exact hv _ (List.getElem_mem hpX)
  obtain ⟨σ', hr, hI, -⟩ := forUp_run (B := B) (i := "cv") (e := .var "gc") (body := skipBlk)
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
      refine ⟨τ.setVar "pp" (p + 1 + (blocksWord (bs.take (k + 1))).length), ?_, by simp [hcv],
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
      have e1 : (Expr.add (.var "pp") (.lit 1)).evalB B τ = some (p + 1 + a0 + 1) :=
        ev_add (ev_var hpp (by omega)) (evalB_lit (by omega)) (by omega)
      have e2 : (Expr.get "x" (.var "pp")).evalB B τ = some g0 :=
        evalB_get (ev_var hpp (by omega)) hgetτ hdB
      have e3 := ev_add e2 e2 (show g0 + g0 < B by omega)
      have e4 := ev_add e1 e3 (show p + 1 + a0 + 1 + (g0 + g0) < B by omega)
      rw [hh0]
      refine (Run.assign e4).mono ?_ |>.congr (by congr 1; omega)
      simp [Expr.size])
  obtain ⟨hpp', hgc', har'⟩ := hI
  have hrun : Run B skipG σ σ' (n * 20 + 20) := by
    unfold skipG
    refine (Run.seq r1 (Run.seq r2 hr)).mono ?_
    simp only [Expr.size]; omega
  refine ⟨σ', hrun, ?_, har', hrun.out_eq (by decide), hrun.frame_inp (by decide),
    fun y hy => hrun.frame_var y (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [skipG, skipBlk, forUp, Com.wvars]; tauto)⟩
  have hbw : (blocksWord (bs.take n)).length = (blocksWord (graphBlocks H)).length := by
    rw [List.take_of_length_le (by rw [hbl])]
  rw [hpp', hbw, toWord_graph]
  simp only [List.length_cons]; omega

end Lax185574Proofs.ResolveRam.Glue
