import Lax185574Proofs.Chain.Ram.ChainSmall
import Lax185574Proofs.Chain.Ram.WTree
import Lax185574Proofs.Words.ComputesLe

/-!
The program of the chain theorem.

`chainProg` reads `(r, ε, G)`, writes `[V, ∅]` if `G` has at most one
vertex, and otherwise computes `q`, the greedy Welzl procedure, the
ordering, the damping sequence and the suffix unions, and writes the
chain. Its layout is `chainLayout` and its array lengths `chainExt`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram Lax185574Proofs.Chain Lax185574.WordEncoding

/-- **The program.** -/
def chainProg : Com :=
  .seq readIn (.ite (.lt (.var "n") (.lit 2)) smallOut
    (.seq qPart (.seq wtCom (.seq ordCom tailCom))))

/-- The layout of the program. -/
def chainLayout : Lax808846Proofs.Compile.Layout :=
  ⟨["tr", "qsg", "qa", "qden", "n", "r", "d", "k", "x1", "x", "w", "qc", "qP", "qb", "qm", "qi",
    "qj", "qcar", "qv", "qd", "fw", "qle", "ok", "q", "D", "wx", "wa", "wb", "bt", "bj", "bk", "ns",
    "wcnt", "wbf", "wu", "wv", "wbu", "wbv", "ca1", "ca2", "blt", "olen", "ou", "oz", "ov", "op",
    "oi", "ot", "M", "b", "ca", "m", "sc", "kp", "kf", "t1", "t2", "t3", "stop", "ru", "rt", "ty",
    "tk", "cu", "cz", "a", "z", "fl", "y", "h", "rc", "go", "s", "hy", "ok2", "hz", "oj"],
    ["adj", "qx", "qy", "act", "wc", "xb", "xt", "su", "sv", "ol", "pos", "inA", "ch", "inS", "p2",
    "p3", "inB", "lab", "key", "tab", "lab2", "labk", "cnt", "sz", "rep", "mark", "Sl", "lst"], 16⟩

open Lax808846Proofs.Compile in
/-- `Expr.Ok` as a Boolean. -/
def exprOkB (L : Layout) : Expr → ℕ → Bool
  | .lit _, _ => true
  | .var x, _ => L.scalars.contains x
  | .get a i, d => L.arrays.contains a && exprOkB L i d && decide (d < L.temps)
  | .bin _ e f, d => exprOkB L f d && exprOkB L e (d + 1) && decide (d < L.temps)

open Lax808846Proofs.Compile in
/-- `Com.Ok` as a Boolean. -/
def comOkB (L : Layout) : Com → Bool
  | .skip => true
  | .assign x e => L.scalars.contains x && exprOkB L e 0
  | .store a i e => L.arrays.contains a && exprOkB L i 0 && exprOkB L e 1 && decide (0 < L.temps)
  | .seq c d => comOkB L c && comOkB L d
  | .ite b c d => exprOkB L (condExpr b) 0 && comOkB L c && comOkB L d
  | .while b c => exprOkB L (condExpr b) 0 && comOkB L c
  | .read x => L.scalars.contains x
  | .write e => exprOkB L e 0 && decide (0 < L.temps)

open Lax808846Proofs.Compile in
theorem exprOk_of {L : Layout} : ∀ (e : Expr) (d : ℕ), exprOkB L e d = true → Expr.Ok L e d
  | .lit _, _, _ => by simp [Expr.Ok]
  | .var x, _, h => by simpa [exprOkB, Expr.Ok] using h
  | .get a i, d, h => by
    simp only [exprOkB, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
    exact ⟨h.1.1, exprOk_of i d h.1.2, h.2⟩
  | .bin _ e f, d, h => by
    simp only [exprOkB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨exprOk_of f d h.1.1, exprOk_of e (d + 1) h.1.2, h.2⟩

open Lax808846Proofs.Compile in
theorem comOk_of {L : Layout} : ∀ c : Com, comOkB L c = true → Com.Ok L c
  | .skip, _ => by simp [Com.Ok]
  | .assign x e, h => by
    simp only [comOkB, Bool.and_eq_true, List.contains_iff_mem] at h
    exact ⟨h.1, exprOk_of e 0 h.2⟩
  | .store a i e, h => by
    simp only [comOkB, Bool.and_eq_true, List.contains_iff_mem, decide_eq_true_eq] at h
    exact ⟨h.1.1.1, exprOk_of i 0 h.1.1.2, exprOk_of e 1 h.1.2, h.2⟩
  | .seq c d, h => by
    simp only [comOkB, Bool.and_eq_true] at h
    exact ⟨comOk_of c h.1, comOk_of d h.2⟩
  | .ite b c d, h => by
    simp only [comOkB, Bool.and_eq_true] at h
    exact ⟨exprOk_of _ 0 h.1.1, comOk_of c h.1.2, comOk_of d h.2⟩
  | .while b c, h => by
    simp only [comOkB, Bool.and_eq_true] at h
    exact ⟨exprOk_of _ 0 h.1, comOk_of c h.2⟩
  | .read x, h => by simpa [comOkB, Com.Ok] using h
  | .write e, h => by
    simp only [comOkB, Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨exprOk_of e 0 h.1, h.2⟩

theorem chainProg_ok : Lax808846Proofs.Compile.Com.Ok chainLayout chainProg :=
  comOk_of _ (by decide)

/-- The array lengths of the program, for `n` vertices and digit length `P`. -/
def chainExt (n P : ℕ) : String → ℕ := fun a =>
  if a = "adj" ∨ a = "cnt" ∨ a = "xt" then n * n
  else if a = "xb" then n * n * (2 * n + 2)
  else if a = "qx" ∨ a = "qy" then P
  else if a = "tab" then n * (n + 4)
  else if a = "ch" then (n + 1) * n
  else n

/-- The cost of the program. -/
noncomputable def chainCost (n r : ℕ) (ε : ℚ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ :=
  if n < 2 then n * (17 * n + 15) + 100 + n * 20 else
  n * (17 * n + 15) + 100 + n * 20 +
    qCost n ε.num.natAbs (2 * r * ε.den) (ε.num.natAbs + 2 * r * ε.den + 2) +
    300 * (n + 1) ^ 3 * (Finset.univ.sup (fun x => stepCross G x (welzlTree G).steps) + 1) *
      (Finset.univ.sup (fun x => stepCross G x (welzlTree G).steps) + Nat.log 2 n + 2) +
    n * (n * 60 + 200) + tailCost G r (welzlVOrder G) (qOf n r ε)

theorem replicate_get {m i : ℕ} (h : i < m) : (List.replicate m 0)[i]? = some 0 := by
  simp [h]

theorem idx_lt {n u v : ℕ} (hu : u < n) (hv : v < n) : u * n + v < n * n :=
  calc u * n + v < u * n + n := Nat.add_lt_add_left hv _
    _ = (u + 1) * n := (Nat.succ_mul u n).symm
    _ ≤ n * n := Nat.mul_le_mul_right _ hu

/-- **The run of the program.** -/
theorem chainProg_run {n r : ℕ} {ε : ℚ} (hr : 1 ≤ r) (hε : 0 < ε) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] :
    ∃ σ' K, Run (valBound 64 3 (toWord (r, ε, G))) chainProg
      (initEnv (chainExt n (ε.num.natAbs + 2 * r * ε.den + 2)) (toWord (r, ε, G))) σ' K ∧
      σ'.out = toWord (chainAlg G r ε) ∧ K ≤ chainCost n r ε G := by
  set x := toWord (r, ε, G) with hx
  set a := ε.num.natAbs with ha
  set c := 2 * r * ε.den with hc
  set P := a + c + 2 with hP
  set B := valBound 64 3 x with hB
  have hxw := toWord_input (r := r) hε G
  rw [← hx] at hxw
  have hmem : ∀ v ∈ [r, 0, a, ε.den, n], v ≤ maxEntry x := fun v hv => le_maxEntry (by
    rw [hxw]; simp at hv ⊢; tauto)
  set X := x.length + maxEntry x + 1 with hX
  have hlx : 1 ≤ x.length := by rw [hxw]; simp
  have hnX : n + 2 ≤ X := by have := hmem n (by simp); omega
  have hrX : r + 2 ≤ X := by have := hmem r (by simp); omega
  have haX : a + 2 ≤ X := by have := hmem a (by simp); omega
  have hdX : ε.den + 2 ≤ X := by have := hmem ε.den (by simp); omega
  have hBX : B = 64 * X ^ 3 := rfl
  clear_value B X
  have hX2 : 2 ≤ X := by omega
  have hXX : X ≤ X * X := Nat.le_mul_self X
  have hX4 : 4 ≤ X * X := Nat.mul_le_mul hX2 hX2
  have hXXX : X * X ≤ X ^ 3 := by
    rw [pow_succ, pow_two]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hnn : (n + 2) * (n + 2) ≤ X * X := Nat.mul_le_mul hnX hnX
  have hcX : c ≤ 2 * (X * X) := by
    have : r * ε.den ≤ X * X := Nat.mul_le_mul (by omega) (by omega)
    simp only [hc]; rw [Nat.mul_assoc]; omega
  have hn4 : n * (n + 4) ≤ (n + 2) * (n + 2) := by
    have : (n + 2) * (n + 2) = n * (n + 4) + 4 := by ring
    omega
  have hB1 : n * n + n + 1 < B := by
    have : n * n ≤ (n + 2) * (n + 2) := Nat.mul_le_mul (by omega) (by omega)
    omega
  have hBq : (n + 2) * (n + 2) + 2 * (a + c + 2) + 10 < B := by omega
  have hBw : (n + 2) ^ 3 * 8 < B := by
    have : (n + 2) ^ 3 ≤ X ^ 3 := Nat.pow_le_pow_left hnX 3
    omega
  have hBd : DampBound n B := by
    refine ⟨?_, ?_⟩
    · unfold PdBound; omega
    · have h2 : 15 * (n + 3) * (n + 1) * (n + 1) ≤ 15 * (2 * X) * X * X := by
        gcongr <;> omega
      have h3 : 15 * (2 * X) * X * X = 30 * X ^ 3 := by ring
      omega
  have hrB : r < B := by omega
  -- reading
  obtain ⟨σ1, hr1, hinp1, htr1, hqa1, hqd1, hn1, hadj1, hv1, ha1, ho1⟩ :=
    readIn_run (B := B) (n := n) (r := r) hε G hB1 (σ := initEnv (chainExt n P) x)
      (by simp [initEnv, hx]) (by simp [initEnv, chainExt])
  have harr0 : ∀ a', σ1.arrs a' = if a' = "adj" then σ1.arrs "adj" else
      List.replicate (chainExt n P a') 0 := fun a' => by
    split_ifs with h
    · rw [h]
    · rw [ha1 a' h]; simp [initEnv]
  have hcond : (Cond.lt (.var "n") (.lit 2)).evalB B σ1 = some (decide (n < 2)) := by
    rw [evalB_condLt (evalB_var (by rw [hn1]; omega)) (evalB_lit (by omega)), hn1]
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · obtain ⟨σ2, hr2, ho2⟩ := smallOut_run (B := B) (n := n) (by omega) hn1
    refine ⟨σ2, _, Run.seq hr1 (Run.ite_true (by rw [hcond]; simp [hn2]) hr2), ?_, ?_⟩
    · rw [ho2, ho1, toWord_small G r ε (by omega)]; simp [initEnv]
    · unfold chainCost; rw [if_pos hn2]; simp; omega
  · have hrep : ∀ a', a' ≠ "adj" → σ1.arrs a' = List.replicate (chainExt n P a') 0 := fun a' h => by
      rw [harr0 a', if_neg h]
    obtain ⟨σ2, hr2, hq2, hv2, ha2, ho2⟩ :=
      qPart_run (B := B) (n := n) (r := r) (ε := ε) hr hn1 htr1 hqa1 hqd1
        (by rw [hrep _ (by decide)]; simp [chainExt, hP, ha, hc])
        (by rw [hrep _ (by decide)]; simp [chainExt, hP, ha, hc]) hBq
    have hkeep2 : ∀ a', a' ∉ ["adj", "qx", "qy"] → σ2.arrs a' = List.replicate (chainExt n P a') 0 :=
      fun a' h => by
        rw [ha2 a' (by simp at h ⊢; tauto), hrep a' (by simp at h; tauto)]
    have hn2' : σ2.vars "n" = n := by rw [hv2 "n" (by decide), hn1]
    have hadj2 : Mat σ2 "adj" n (fun u v => ind (gA G u v)) := hadj1.of_eq (ha2 _ (by decide))
    obtain ⟨σ3, K3, hr3, hact3, hns3, hsu3, hsv3, hv3, ha3, -, ho3, hK3⟩ :=
      wtCom_run (B := B) (G := G) hBw hn2' hadj2
        (by rw [hkeep2 _ (by decide)]; simp [chainExt])
        (by rw [hkeep2 _ (by decide)]; simp [chainExt])
        (by rw [hkeep2 _ (by decide)]; simp [chainExt])
        (by rw [hkeep2 _ (by decide)]; simp [chainExt])
        (by rw [hkeep2 _ (by decide)]; simp [chainExt])
        (by rw [hkeep2 _ (by decide)]; simp [chainExt])
        (fun i hi => by rw [hkeep2 _ (by decide)]; exact replicate_get (by simp [chainExt]; omega))
        (fun i hi => by rw [hkeep2 _ (by decide)]; exact replicate_get (by simp [chainExt]; omega))
    have hn3 : σ3.vars "n" = n := by rw [hv3 "n" (by decide), hn2']
    obtain ⟨σ4, hr4, hpos4, hv4, ha4⟩ :=
      ordCom_run (B := B) G (by omega) hn3 hact3 (by rw [hns3]; simp [wSteps])
        (fun j hj => by
          have hj' : j < (welzlTree G).steps.length := by simpa [wSteps] using hj
          simpa [wSteps] using hsu3 j hj')
        (fun j hj => by
          have hj' : j < (welzlTree G).steps.length := by simpa [wSteps] using hj
          simpa [wSteps] using hsv3 j hj')
        (by rw [ha3 _ (by decide), hkeep2 _ (by decide)]; simp [chainExt])
        (by rw [ha3 _ (by decide), hkeep2 _ (by decide)]; simp [chainExt])
    have hkeep4 : ∀ a', a' ∉ ["adj", "qx", "qy", "act", "wc", "su", "sv", "xb", "xt", "ol", "pos"] →
        σ4.arrs a' = List.replicate (chainExt n P a') 0 := fun a' h => by
      rw [ha4 a' (by simp at h ⊢; tauto), ha3 a' (by simp at h ⊢; tauto), hkeep2 a' (by simp at h ⊢; tauto)]
    have hz : ∀ a', a' ∈ ["inA", "inB", "inS", "Sl", "p2", "p3", "mark", "rep", "lab", "key", "lab2",
        "labk", "sz", "lst"] → σ4.arrs a' = List.replicate n 0 := fun a' h => by
      have hnot : a' ∉ ["adj", "qx", "qy", "act", "wc", "su", "sv", "xb", "xt", "ol", "pos"] := by
        simp at h ⊢
        rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> decide
      have he : chainExt n P a' = n := by
        simp at h
        rcases h with h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp [chainExt]
      rw [hkeep4 a' hnot, he]
    have hpre : TailPre n r G (welzlVOrder G) (qOf n r ε) σ4 := by
      refine ⟨by rw [hv4 _ (by decide), hn3], by rw [hv4 _ (by decide), hv3 _ (by decide),
          hv2 _ (by decide), htr1], by rw [hv4 _ (by decide), hv3 _ (by decide), hq2],
        hadj2.of_eq (by rw [ha4 _ (by decide), ha3 _ (by decide)]), hpos4,
        fun a' h => by rw [hz a' h]; simp, by rw [hkeep4 _ (by decide)]; simp [chainExt],
        by rw [hkeep4 _ (by decide)]; simp [chainExt], by rw [hkeep4 _ (by decide)]; simp [chainExt],
        fun t ht => by rw [hkeep4 _ (by decide)] at ht ⊢; exact replicate_get (by simpa using ht),
        ⟨by rw [hkeep4 _ (by decide)]; simp [chainExt], fun u hu v hv => by
          rw [hkeep4 _ (by decide)]; exact replicate_get (by simp [chainExt]; exact idx_lt hu hv)⟩,
        ⟨by rw [hz _ (by simp)]; simp, fun u hu => by rw [hz _ (by simp)]; exact replicate_get hu⟩,
        ⟨by rw [hz _ (by simp)]; simp, fun u hu => by rw [hz _ (by simp)]; exact replicate_get hu⟩⟩
    obtain ⟨σ5, hr5, ho5⟩ := tailCom_run (r := r) hε hn2 hBd hrB hpre
    refine ⟨σ5, _, Run.seq hr1 (Run.ite_false (by rw [hcond]; simp; omega)
      (Run.seq hr2 (Run.seq (hr3.mono hK3) (Run.seq hr4 hr5)))), ?_, ?_⟩
    · rw [ho5, hr4.out_eq (by decide), ho3, ho2, ho1]; simp [initEnv]
    · unfold chainCost; rw [if_neg (by omega)]; simp only [Cond.size, Expr.size]; omega

end Lax185574Proofs.Chain.Ram
