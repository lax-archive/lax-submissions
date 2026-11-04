import Lax185574Proofs.StpRam.Middle
import Lax185574Proofs.StpRam.FinalRound
import Lax185574Proofs.LoopGlue

/-!
The glue program of lem:compute-stp.

It reads the tag and the length of the state and dispatches: tag `0`
is the first round (`round0`), tag `1` a middle round (`mid`) and tag
`2` the final round (`finalRound`). The three rounds are stated here on
the input that the loop driver hands to the glue program, from the
initial environment of IMP+.
-/

namespace Lax185574Proofs.StpRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574.TypeTrees Lax185574.PartialGraphs
open Lax185574.ScatterTypes Lax185574.DistanceMatrix

/-- The glue program. -/
def glue : Com := .seq (.read "tg") (.seq (.read "sl")
  (.ite (.eq (.var "tg") (.lit 0)) round0 (.ite (.eq (.var "tg") (.lit 1)) mid finalRound)))

theorem condEq_lit {B : ℕ} {ρ : Env} {x : String} {a n : ℕ} (h : ρ.vars x = a) (ha : a < B)
    (hn : n < B) : (Cond.eq (.var x) (.lit n)).evalB B ρ = some (a == n) := by
  simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff]
  exact ⟨a, n, ⟨h.symm, by omega⟩, ⟨rfl, hn⟩, rfl⟩

/-- The environment after reading the tag and the length. -/
def afterHead (ext : String → ℕ) (tg sl : ℕ) (rest : List ℕ) : Env :=
  { ((initEnv ext (tg :: sl :: rest)).setVar "tg" tg).setVar "sl" sl with inp := rest }

theorem head_run {B : ℕ} (ext : String → ℕ) (tg sl : ℕ) (rest : List ℕ) :
    Run B (.seq (.read "tg") (.read "sl")) (initEnv ext (tg :: sl :: rest)) (afterHead ext tg sl rest) 2 :=
  Run.seq (Run.read rfl) (Run.read rfl)

theorem glue_of {B tg sl K K' : ℕ} {ext : String → ℕ} {rest : List ℕ} {σ' : Env}
    (hc : Run B (.ite (.eq (.var "tg") (.lit 0)) round0 (.ite (.eq (.var "tg") (.lit 1)) mid finalRound))
      (afterHead ext tg sl rest) σ' K)
    (hK : K + 2 ≤ K') : Run B glue (initEnv ext (tg :: sl :: rest)) σ' K' := by
  have := Run.seq (Run.read (B := B) (x := "tg") (σ := initEnv ext (tg :: sl :: rest)) rfl)
    (Run.seq (Run.read (B := B) (x := "sl") rfl) hc)
  exact this.mono (by omega)

/-- **The first round of the glue program.** -/
theorem glue_round0 {B n k q L : ℕ} (G : PartialGraph (Fin n)) (f : Fin n → TypeTree) (hn : 1 ≤ n)
    {Dw Dt : List ℕ} (hDw : Dw = n :: Dt) (hDt : Dt.length = n * (n + 1))
    (ext : String → ℕ) (hL : ∀ i, (toWord (f i)).length ≤ L)
    (heo : ext "eo" = n + 1) (het : ext "et" = offL G.edge n)
    (hno : ext "no" = n + 1) (hnt : ext "nt" = offL G.nonEdge n)
    (hxl : 8 + (toWord f).length + n ≤ ext "x")
    (hnB : n + 1 < B) (hEB : offL G.edge n + 1 < B) (hNB : offL G.nonEdge n + 1 < B)
    (hB : 2 * ((toWord G).length + Dw.length + (toWord f).length) + n + 20 < B)
    (hv : ∀ v ∈ toWord f, v < B) (hk : k < B) (hq : q < B) :
    ∃ σ', Run B glue (initEnv ext ([0, ((toWord G ++ [k, q]) ++ Dw ++ toWord f).length] ++
        ((toWord G ++ [k, q]) ++ Dw ++ toWord f) ++ [0])) σ'
        (winCost n + 9 * (n * (n + 1)) + n * (48 * L + 110) + 100 * ((toWord f).length + n) + 1030) ∧
      σ'.out = (if q = 0 then [0, 0] else
        [1, (stState n k q 0 ((toWord G).length + 2 + Dw.length) (famW f) []).length, 0] ++
          stState n k q 0 ((toWord G).length + 2 + Dw.length) (famW f) [] ++ toWord (f ⟨0, hn⟩)) := by
  set N := ((toWord G ++ [k, q]) ++ Dw ++ toWord f).length with hN
  have hNl : N = (toWord G).length + 2 + Dw.length + (toWord f).length := by simp [hN]; omega
  have hu : [0, N] ++ ((toWord G ++ [k, q]) ++ Dw ++ toWord f) ++ [0] =
      0 :: N :: ((toWord G ++ [k, q]) ++ Dw ++ toWord f ++ [0]) := by simp
  rw [hu]
  obtain ⟨σ', r, ho⟩ := round0_run (B := B) (L := L) G f hn hDw hDt (σ := afterHead ext 0 N
    ((toWord G ++ [k, q]) ++ Dw ++ toWord f ++ [0])) hL (by simp [afterHead])
    (by simp [afterHead, hNl]) (by simp [afterHead, initEnv, heo]) (by simp [afterHead, initEnv, het])
    (by simp [afterHead, initEnv, hno]) (by simp [afterHead, initEnv, hnt])
    (by simp [afterHead, initEnv]; omega) hnB hEB hNB hB hv hk hq
  refine ⟨σ', glue_of (Run.ite_true ?_ r) (by simp [Cond.size, Expr.size]; omega), ?_⟩
  · rw [condEq_lit (a := 0) (by simp [afterHead]) (by omega) (by omega)]; rfl
  · rw [ho]; simp [afterHead, initEnv]

/-- **A middle round of the glue program.** -/
theorem glue_mid {B n k q j gl : ℕ} {F A : List (List ℕ)} {b : List ℕ} (ext : String → ℕ)
    (hF : F.length = n) (hA : A.length = j) (hn : 1 ≤ n) (hj : j < q * n)
    (hxl : (stState n k q (j + 1) gl F (A ++ [b])).length ≤ ext "x")
    (hB : (stState n k q (j + 1) gl F (A ++ [b])).length + q * n + gl + 10 < B)
    (hv : ∀ v ∈ stState n k q j gl F A ++ (b.length :: b), v < B) :
    ∃ σ', Run B glue (initEnv ext (1 :: (stState n k q j gl F A).length ::
        (stState n k q j gl F A ++ (b.length :: b)))) σ'
        (100 * (stState n k q (j + 1) gl F (A ++ [b])).length + 420) ∧
      σ'.out = [midTag n q j, (stState n k q (j + 1) gl F (A ++ [b])).length, midWin n q j gl] ++
        stState n k q (j + 1) gl F (A ++ [b]) ++ (F ++ (A ++ [b])).getD (midIdx n q j) [] := by
  have hSl := length_stState n k q j gl F A
  have hSl' := length_stState n k q (j + 1) gl F (A ++ [b])
  have hAl : (toWord (A ++ [b])).length = (toWord A).length + 1 + b.length := by
    rw [toWord_snoc, toWord_words]; simp; omega
  obtain ⟨σ', r, ho⟩ := mid_run (B := B) hF hA hn hj (τ := afterHead ext 1 (stState n k q j gl F A).length
    (stState n k q j gl F A ++ (b.length :: b))) (by simp [afterHead])
    (by simp [afterHead, initEnv]; omega) hB hv
  refine ⟨σ', glue_of (Run.ite_false ?_ (Run.ite_true ?_ r)) (by simp [Cond.size, Expr.size]; omega), ?_⟩
  · rw [condEq_lit (a := 1) (by simp [afterHead]) (by omega) (by omega)]; rfl
  · rw [condEq_lit (a := 1) (by simp [afterHead]) (by omega) (by omega)]; rfl
  · rw [ho]; simp [afterHead, initEnv]

/-- **The final round of the glue program.** -/
theorem glue_final {B n k q sl gl : ℕ} (G : PartialGraph (Fin n)) {F : List (List ℕ)} {b : List ℕ}
    {L : ℕ} (ext : String → ℕ) (hFL : ∀ u ∈ F, u.length ≤ L)
    (hAL : ∀ u ∈ answers G k q, u.length ≤ L) (hq : 1 ≤ q)
    (heo : ext "eo" = n + 1) (het : ext "et" = offL G.edge n)
    (hno : ext "no" = n + 1) (hnt : ext "nt" = offL G.nonEdge n)
    (ha : total (answers G k q) ≤ ext "a") (hst : (answers G k q).length ≤ ext "st")
    (hln : (answers G k q).length ≤ ext "ln") (hrt : ext "rt" = q + 1)
    (hord : (answers G k q).length ≤ ext "ord") (hdd : ext "dd" = n * n) (hdn : ext "dn" = n)
    (hbl : ext "bl" = n)
    (hb : WordsBound B (answers G k q)) (hnB : n + 2 < B) (hnnB : n * n < B)
    (hEB : offL G.edge n + 1 < B)
    (hNB : offL G.nonEdge n + 1 < B) (hFB : F.length < B) (hLB : L < B)
    (hAB : (toWord (answers G k q)).length < B) (hAv : ∀ v ∈ toWord (answers G k q), v < B)
    (hRB : radius k q 0 + 1 < B) (h9B : 9 < B)
    (hTB : radius k q 1 * (answers G k q).length + 1 < B) (htB : total (answers G k q) + 3 < B) :
    ∃ σ', Run B glue (initEnv ext (2 :: sl :: ((toWord G ++ [k, q]) ++ toWord (distMatrix G) ++
        stState n k q (q * n) gl F (answers G k q) ++ (b.length :: b)))) σ'
        (readCost n L F.length (toWord (answers G k q)).length +
          finalCost n k q L (answers G k q).length (radius k q 1) + 20) ∧
      σ'.out = 0 :: toWord (stp G k q) := by
  obtain ⟨σ', r, ho⟩ := finalRound_run (B := B) G (hd := [0, n, k, q, q * n, gl]) (rest := b.length :: b)
    (Fs := F) rfl hFL hAL hq (σ := afterHead ext 2 sl ((toWord G ++ [k, q]) ++ toWord (distMatrix G) ++
      stState n k q (q * n) gl F (answers G k q) ++ (b.length :: b)))
    (by simp [afterHead, stState]) (by simp [afterHead, initEnv, heo]) (by simp [afterHead, initEnv, het])
    (by simp [afterHead, initEnv, hno]) (by simp [afterHead, initEnv, hnt])
    (by simp [afterHead, initEnv]; omega) (by simp [afterHead, initEnv]; omega)
    (by simp [afterHead, initEnv]; omega) (by simp [afterHead, initEnv, hrt])
    (by simp [afterHead, initEnv]; omega) (by simp [afterHead, initEnv, hdd])
    (by simp [afterHead, initEnv, hdn]) (by simp [afterHead, initEnv, hbl])
    hb hnB hnnB hEB hNB hFB hLB hAB hAv hRB h9B hTB htB
  refine ⟨σ', glue_of (Run.ite_false ?_ (Run.ite_false ?_ r)) (by simp [Cond.size, Expr.size]; omega), ?_⟩
  · rw [condEq_lit (a := 2) (by simp [afterHead]) (by omega) (by omega)]; rfl
  · rw [condEq_lit (a := 2) (by simp [afterHead]) (by omega) (by omega)]; rfl
  · rw [ho]; simp [afterHead, initEnv]

end Lax185574Proofs.StpRam
