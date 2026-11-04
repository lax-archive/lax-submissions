import Lax185574Proofs.ResolveRam.Glue.ReadX

/-!
The first round of the glue program of lem:resolve-lift.

The round reads the input `x` into the array `x` (`rdX`) and finds the
end `pp` of the word of the partial graph and the end `pq` of the word
of its distance matrix (`locate`). For `n = 0` it outputs `0 :: zOut`,
six zeros. Otherwise it fills the buffer with the head of the position
of the scatter type (`hdOf_stp`) and the query of the switch for the
call of the scatter type (`rQ_stp`): the fixed queries of the four
other slots and the query of slot F, which is the word of the partial
graph, `k₀`, `q₀`, the word of the distance matrix and the word of the
family, all copied from `x` (`fill0_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Compose
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam Lax185574.DistanceMatrix

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-! ### The output on words -/

/-- The fixed part of the query of the switch in front of the query of
slot F. -/
noncomputable def s3W : List ℕ := Simulate.swIn qA0 qB0 qC0

theorem rQ_stp : rQ G k₀ q₀ .stp =
    [s3W.length, qE0.length, (qF G k₀ q₀ .stp).length] ++ s3W ++ qE0 ++ qF G k₀ q₀ .stp := rfl

theorem swAt_stp_ws : (swAt G P Q s k₀ q₀ .stp).ws = [[], [], [], []] := rfl

theorem hdOf_stp :
    hdOf G P Q s k₀ q₀ .stp = [(xIn G k₀ q₀ P Q s).length + 1, 22, (xIn G k₀ q₀ P Q s).length, 0, ySz (xIn G k₀ q₀ P Q s),
      (xIn G k₀ q₀ P Q s).length, n, P, Q, if s then 1 else 0, k₀, q₀, 0, 0, 0, 0, 0, 0, 0, 0,
      4, 0, 0, 0, 0] := by
  simp only [hdOf, stOf, scW, winOf, tagOf, true_or, if_true, swAt_stp_ws, curW]
  rfl

/-- The split of the input. -/
theorem xIn_split :
    xIn G k₀ q₀ P Q s = toWord G ++ (toWord (distMatrix G) ++ ([P, Q, if s then 1 else 0] ++
      toWord (family G k₀ q₀))) := by
  rw [toWord_xIn]; simp

theorem qF_len : (qF G k₀ q₀ .stp).length + 1 = (xIn G k₀ q₀ P Q s).length := by
  rw [qF_stp, xIn_split]; simp; omega

/-! ### Locating the parts -/

theorem ev_mul {B : ℕ} {e f : Expr} {σ : Env} {m n : ℕ} (he : e.evalB B σ = some m)
    (hf : f.evalB B σ = some n) (h : m * n < B) : (Expr.mul e f).evalB B σ = some (m * n) :=
  evalB_bin he hf h

/-- The end of the word of the distance matrix, from the end `pp` of the
word of the partial graph and `n`. -/
def pqE : Expr := .add (.add (.var "pp") (.mul (.var "gn") (.add (.var "gn") (.lit 1)))) (.lit 1)

/-- Find `n`, the end `pp` of the word of the partial graph and the end
`pq` of the word of its distance matrix. -/
def locate : Com :=
  .seq (.assign "gn" (.get "x" (.lit 0))) (.seq (.assign "pp" (.add (.var "gn") (.lit 1)))
    (.seq skipG (.seq skipG (.assign "pq" pqE))))

theorem pqE_evalB {B p m : ℕ} {τ : Env} (hp : τ.vars "pp" = p) (hn : τ.vars "gn" = m)
    (hB : p + m * (m + 1) + 1 < B) : pqE.evalB B τ = some (p + m * (m + 1) + 1) := by
  have h1 : m * (m + 1) < B := by omega
  have h2 : m + 1 < B := by nlinarith
  exact ev_add (ev_add (ev_var hp (by omega)) (ev_mul (ev_var hn (by omega))
    (ev_add (ev_var hn (by omega)) (evalB_lit (by omega)) h2) h1) (by omega)) (evalB_lit (by omega)) hB

theorem locate_run {B : ℕ} {X rest : List ℕ} {σ : Env} (hX : PreAt "x" X σ)
    (hd : X = toWord G ++ (toWord (distMatrix G) ++ rest)) (hB : X.length + 1 < B)
    (hv : ∀ v ∈ X, v < B) :
    ∃ σ', Run B locate σ σ' (n * 40 + 80) ∧ σ'.vars "gn" = n ∧
      σ'.vars "pp" = (toWord G).length ∧
      σ'.vars "pq" = (toWord G).length + (toWord (distMatrix G)).length ∧
      σ'.arrs = σ.arrs ∧ σ'.out = σ.out ∧ σ'.inp = σ.inp ∧
      (∀ y, y ∉ ["gn", "pp", "gc", "cv", "pq"] → σ'.vars y = σ.vars y) := by
  have hDl := Lax185574Proofs.DistMatrix.length_toWord_distMatrix G
  have hXl : (toWord G).length + (toWord (distMatrix G)).length ≤ X.length := by
    rw [hd]; simp only [List.length_append]; omega
  generalize toWord (distMatrix G) ++ rest = rest' at hd
  have hG := StpRam.toWord_pg G
  rw [hG] at hd
  have hX0 : X.length ≠ 0 := by rw [hd]; simp
  have hx0 : X[0]'(by omega) = n := by simp [hd]
  set σ1 := σ.setVar "gn" n
  have r1 : Run B (.assign "gn" (.get "x" (.lit 0))) σ σ1 3 := by
    have := Run.assign (B := B) (σ := σ) (x := "gn") (e := .get "x" (.lit 0)) (v := n)
      (evalB_get (evalB_lit (by omega)) (by rw [hX.get (by omega), hx0])
        (by rw [← hx0]; exact hv _ (List.getElem_mem _)))
    simpa [Expr.size] using this
  have hnB : n + 1 < B := by
    have : n < X.length := by rw [hd]; simp
    omega
  set σ2 := σ1.setVar "pp" (n + 1)
  have r2 : Run B (.assign "pp" (.add (.var "gn") (.lit 1))) σ1 σ2 4 :=
    (Run.assign (ev_add (ev_var (by simp [σ1]) (by omega)) (evalB_lit (by omega)) (by omega))).mono
      (by simp [Expr.size])
  have hX2 : PreAt "x" X σ2 := fun i h => by simpa [σ2, σ1] using hX i h
  have hd1 : X.drop (n + 1) = toWord G.edge ++ (toWord G.nonEdge ++ rest') := by
    rw [hd]; simp
  obtain ⟨σ3, r3, hp3, ha3, ho3, hi3, hv3⟩ := skipG_run G.edge hX2 hd1 (by simp [σ2]) hB hv
  have hX3 : PreAt "x" X σ3 := fun i h => by rw [ha3]; exact hX2 i h
  have hd2 : X.drop (n + 1 + (toWord G.edge).length) = toWord G.nonEdge ++ rest' := by
    rw [← List.drop_drop, hd1, List.drop_left]
  obtain ⟨σ4, r4, hp4, ha4, ho4, hi4, hv4⟩ := skipG_run G.nonEdge hX3 hd2 hp3 hB hv
  have hpg : n + 1 + (toWord G.edge).length + (toWord G.nonEdge).length = (toWord G).length := by
    rw [hG]; simp; omega
  have hn4 : σ4.vars "gn" = n := by rw [hv4 _ (by decide), hv3 _ (by decide)]; simp [σ2, σ1]
  have hp4' : σ4.vars "pp" = (toWord G).length := by rw [hp4, ← hpg]
  have e5 := pqE_evalB (B := B) hp4' hn4 (by omega)
  set σ5 := σ4.setVar "pq" ((toWord G).length + n * (n + 1) + 1)
  have r5 : Run B (.assign "pq" pqE) σ4 σ5 (1 + pqE.size) := Run.assign e5
  have hrun : Run B locate σ σ5 (n * 40 + 80) := by
    unfold locate
    exact (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 r5)))).mono (by simp [pqE, Expr.size]; omega)
  refine ⟨σ5, hrun, by simp [σ5, hn4], by simp [σ5, hp4'], by simp [σ5]; omega,
    by simp only [σ5, arrs_setVar]; rw [ha4, ha3]; simp [σ2, σ1], by change σ4.out = σ.out; rw [ho4, ho3]; rfl,
    by change σ4.inp = σ.inp; rw [hi4, hi3]; rfl, fun y hy => hrun.frame_var y (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [locate, skipG, skipBlk, forUp, Com.wvars]; tauto)⟩

end Lax185574Proofs.ResolveRam.Glue
