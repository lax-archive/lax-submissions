import Lax185574Proofs.MC.Bounds.RealT
import Lax185574Proofs.MC.Asm.Regions
import Lax185574Proofs.MC.Asm.Calls

/-!
The time of the pipeline thread.

The pipeline runs on `x = [n] ++ toWord σ ++ toWord φ`. Let `X = |x| +
max x + 1` and `T = treeMax`. Every round of the glue program has guard
quantity at most `C₁ X² (T + 1)` (`base_le`, from `round_small`), so
the number `pBnd` below bounds the three quantities of `pipe_run`. If
`2 ^ (D + 30 + sI) · pBnd · X ^ 5 ≤ 2 ^ w`, then the pipeline halts with
`1 :: mcAns` within `KL (2 cG |x| + (m + 2) mcR + 4)` for the number `m` of steps. Here `mcR` bounds the cost of a round
with its call. It does not involve `|x|`, and it is quadratic in `n`,
since every step has one call and every call costs `O((n + 1)²)` up to a
factor polynomial in `T` and `K`.
-/

namespace Lax185574Proofs.MC

open Lax808846.Ram Lax185574Proofs.Words Lax185574Proofs.RamSim Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.SequenceEncoding Lax185574.PartialGraphs
open Lax185574.ConstructionSequences Lax185574.TypeTrees Lax185574.PartialGraphEncoding
open Lax185574.ResolveLift Lax185574.Width
open Lax3.DistFO (rhoMinus rhoPlus)

theorem ite_le_self (c : Prop) [Decidable c] (a : ℕ) : (if c then a else 0) ≤ a := by
  split <;> omega

theorem maxEntry_le_bound {l : List ℕ} {B : ℕ} (h : ∀ e ∈ l, e ≤ B) : maxEntry l ≤ B := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    show max a (maxEntry l) ≤ B
    exact max_le (h a (by simp)) (ih fun e he => h e (by simp [he]))

/-- The constant of the guard quantities of the rounds. -/
noncomputable def pC1 (cG q : ℕ) (φ : Lax3.FirstOrder.FO 0) : ℕ := 9 * cG + 12 * kq q φ + 100

/-- **The guard quantity of a round, arithmetic.** -/
theorem base_le {X T n L M cG kq : ℕ} (hX : L + M + 1 = X) (hn : n + 1 ≤ X) :
    2 * X + cG * (L + M + n * T + (n + 1) ^ 2) + 3 * (cG * (n * T + (n + 1) ^ 2)) +
        3 * (2 * (n + 2) * (T + 6 * (n + 1) + kq)) + 8 ≤
      (9 * cG + 12 * kq + 100) * (X ^ 2 * (T + 1)) := by
  have h1 : 1 ≤ X := by omega
  have hXX : X ≤ X ^ 2 := Nat.le_self_pow (by norm_num) _
  have hP2 : X ^ 2 ≤ X ^ 2 * (T + 1) := Nat.le_mul_of_pos_right _ (by omega)
  have hXT : X * T ≤ X ^ 2 * (T + 1) := by
    calc X * T ≤ X ^ 2 * T := Nat.mul_le_mul_right _ hXX
      _ ≤ X ^ 2 * (T + 1) := Nat.mul_le_mul_left _ (by omega)
  have hnT : n * T ≤ X * T := Nat.mul_le_mul_right _ (by omega)
  have hn2 : (n + 1) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left hn _
  set P := X ^ 2 * (T + 1) with hP
  have hA : L + M + n * T + (n + 1) ^ 2 ≤ 3 * P := by omega
  have hB : n * T + (n + 1) ^ 2 ≤ 2 * P := by omega
  have hA' : cG * (L + M + n * T + (n + 1) ^ 2) ≤ 3 * (cG * P) := by
    calc _ ≤ cG * (3 * P) := Nat.mul_le_mul_left _ hA
      _ = 3 * (cG * P) := by ring
  have hB' : cG * (n * T + (n + 1) ^ 2) ≤ 2 * (cG * P) := by
    calc _ ≤ cG * (2 * P) := Nat.mul_le_mul_left _ hB
      _ = 2 * (cG * P) := by ring
  have hC : 2 * (n + 2) * (T + 6 * (n + 1) + kq) ≤ 2 * (2 * X) * (T + 6 * X + kq) :=
    Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (by omega)
  have hC' : 2 * (2 * X) * (T + 6 * X + kq) = 4 * (X * T) + 24 * X ^ 2 + 4 * (kq * X) := by ring
  have hkX : kq * X ≤ kq * P := Nat.mul_le_mul_left _ (by omega)
  have hE : (9 * cG + 12 * kq + 100) * P = 9 * (cG * P) + 12 * (kq * P) + 100 * P := by ring
  rw [hE]
  generalize cG * P = a at *
  generalize kq * P = b at *
  generalize kq * X = c at *
  generalize X * T = d at *
  generalize X ^ 2 = e at *
  generalize 2 * (n + 2) * (T + 6 * (n + 1) + kq) = f at *
  omega

/-- The bound of the heads of the rounds, with largest entry. -/
noncomputable def pH1 (cG L M n T : ℕ) : ℕ := cG * (L + M + n * T + (n + 1) ^ 2)

/-- The bound of the heads of the rounds, with window length. -/
noncomputable def pH2 (cG n T : ℕ) : ℕ := cG * (n * T + (n + 1) ^ 2)

/-- The bound of the guard quantities, the callee time bounds and the
constants of the callees. -/
noncomputable def pBnd (eM eR eE cG Ks n T q K X : ℕ) (φ : Lax3.FirstOrder.FO 0) (k : CCst) : ℕ :=
  (cG + 1) * (pC1 cG q φ * (X ^ 2 * (T + 1))) ^ (eM + eR + eE + 1) + realB n T q K φ k +
    (Ks + k.cM ^ (eM + 1) + k.cR ^ (eR + 1) + k.cE ^ (eE + 1) + 3 * k.d + 1)

/-- The cost of a round with its call. -/
noncomputable def mcR (cG Ks n T q K : ℕ) (φ : Lax3.FirstOrder.FO 0) (k : CCst) : ℕ :=
  cG * (3 * pH2 cG n T + 2 * callB n T q φ + 7) +
    Ks * (realB n T q K φ k + 3 * k.d + callB n T q φ + 1) + 2

/-- **The time of the pipeline thread.** -/
theorem pipe_time {pM pR pE G sw P0 : Program} {eM eR eE Ks KL D sI cG K : ℕ} {k : CCst}
    {φ : Lax3.FirstOrder.FO 0}
    (hC : CalleeRun pM pR pE eM eR eE (Lax3.FirstOrder.rank φ) k) (hsw : SwSpec sw Ks D pM pR pE)
    (hP0 : LoopSpec P0 G sw KL) (hD : sI + 4 ≤ D) {n : ℕ} (hn : 1 ≤ n)
    {Gr : SimpleGraph (Fin n)} {σ : Script n} (hcs : IsConstructionSequence Gr σ.run)
    (hK : width (rhoPlus 1 (Lax3.FirstOrder.rank φ))
      (rhoPlus 1 (Lax3.FirstOrder.rank φ) + 1 + Lax3.FirstOrder.rank φ) σ.run ≤ K)
    (hgl : GlueAt G sI (D + 16) eM eR eE cG φ ([n] ++ toWord σ ++ toWord φ) σ.run σ.steps) {w : ℕ}
    (h : 2 ^ (D + 30 + sI) * pBnd eM eR eE cG Ks n (treeMax σ.run (Lax3.FirstOrder.rank φ))
      (Lax3.FirstOrder.rank φ) K
      (([n] ++ toWord σ ++ toWord φ).length + maxEntry ([n] ++ toWord σ ++ toWord φ) + 1) φ k *
      (([n] ++ toWord σ ++ toWord φ).length + maxEntry ([n] ++ toWord σ ++ toWord φ) + 1) ^ 5 ≤
        2 ^ w) :
    ∃ t ≤ KL * (2 * cG * ([n] ++ toWord σ ++ toWord φ).length +
        (σ.steps.length + 2) * mcR cG Ks n (treeMax σ.run (Lax3.FirstOrder.rank φ))
          (Lax3.FirstOrder.rank φ) K φ k + 4),
      RunsTo w P0 ([n] ++ toWord σ ++ toWord φ) (1 :: mcAns Gr φ) t := by
  obtain ⟨hd, hhd, hH1, hH2, hrd⟩ := hgl.rounds hn
  set q := Lax3.FirstOrder.rank φ with hq
  set x := [n] ++ toWord σ ++ toWord φ with hx
  set s := σ.run with hs
  set T := treeMax s q with hT
  set X := x.length + maxEntry x + 1 with hXd
  set cs := pcalls n σ.steps with hcs'
  set R := cs.length with hR
  set B := pBnd eM eR eE cG Ks n T q K X φ k with hBd
  set ans := finAns s q φ with hans
  -- the calls are small
  have hMx : maxEntry (toWord σ) ≤ maxEntry x :=
    maxEntry_le_of_sub (fun e he => by simp [x, he])
  have hnx : n ≤ maxEntry x := le_maxEntry (by simp [x])
  have hcall : ∀ c ∈ cs, Small (callQ s q φ c) (callB n T q φ) (maxEntry x) ∧
      Small (callY s q φ c) (callB n T q φ) (maxEntry x) := fun c hc =>
    let h := small_call σ q φ hc; ⟨h.1.mono le_rfl hMx, h.2.mono le_rfl hMx⟩
  have hH1' : ∀ j < R, (hd j).length + maxEntry (hd j) ≤ pH1 cG x.length (maxEntry x) n T := hH1
  have hH2' : ∀ j < R, (hd j).length + (hd j).getD 2 0 ≤ pH2 cG n T := hH2
  have hrs1 : ∀ j ≤ R, (pU x s q φ cs hd ans j).length + (glueOut s q φ cs hd ans j).length + 1 ≤
      (if j = 0 then x.length else 0) + 3 * pH2 cG n T + 2 * callB n T q φ + 7 := fun j hj =>
    (round_small (H1 := pH1 cG x.length (maxEntry x) n T) (H2 := pH2 cG n T)
      (CB := callB n T q φ) hhd hH1' hH2' hcall hj).1
  have hrs2 : ∀ j ≤ R, ∀ e ∈ pU x s q φ cs hd ans j ++ glueOut s q φ cs hd ans j,
      e ≤ x.length + maxEntry x + pH1 cG x.length (maxEntry x) n T + callB n T q φ + 1 :=
    fun j hj => (round_small (H1 := pH1 cG x.length (maxEntry x) n T) (H2 := pH2 cG n T)
      (CB := callB n T q φ) hhd hH1' hH2' hcall hj).2
  -- the guard quantity of a round
  have hbase : ∀ j ≤ R, (pU x s q φ cs hd ans j).length + (glueOut s q φ cs hd ans j).length +
      maxEntry (pU x s q φ cs hd ans j ++ glueOut s q φ cs hd ans j) + 1 ≤
        pC1 cG q φ * (X ^ 2 * (T + 1)) := by
    intro j hj
    have h1 := hrs1 j hj
    have h3 := maxEntry_le_bound (hrs2 j hj)
    have h4 : 2 * X + pH1 cG x.length (maxEntry x) n T + 3 * pH2 cG n T + 3 * callB n T q φ + 8 ≤
        pC1 cG q φ * (X ^ 2 * (T + 1)) :=
      base_le (T := T) (cG := cG) (kq := kq q φ) hXd.symm (show n + 1 ≤ X by omega)
    have h5 : (if j = 0 then x.length else 0) ≤ x.length := by split_ifs <;> omega
    omega
  have hBe : (cG + 1) * (pC1 cG q φ * (X ^ 2 * (T + 1))) ^ (eM + eR + eE + 1) +
      realB n T q K φ k +
      (Ks + k.cM ^ (eM + 1) + k.cR ^ (eR + 1) + k.cE ^ (eE + 1) + 3 * k.d + 1) = B := by
    rw [hBd]; rfl
  have hB1 : ∀ j ≤ R, (cG + 1) * ((pU x s q φ cs hd ans j).length +
      (glueOut s q φ cs hd ans j).length +
      maxEntry (pU x s q φ cs hd ans j ++ glueOut s q φ cs hd ans j) + 1) ^
        (eM + eR + eE + 1) ≤ B := by
    intro j hj
    have := Nat.mul_le_mul_left (cG + 1) (Nat.pow_le_pow_left (hbase j hj) (eM + eR + eE + 1))
    omega
  have hB2 : ∀ (j : ℕ) (c : PCall n), cs[j]? = some c → realT s q φ k c ≤ B := by
    intro j c hc
    have : realT s q φ k c ≤ realB n T q K φ k := realT_le σ q hK φ k (List.mem_of_getElem? hc)
    omega
  have hB3 : Ks + k.cM ^ (eM + 1) + k.cR ^ (eR + 1) + k.cE ^ (eE + 1) + 3 * k.d + 1 ≤ B := by
    omega
  have hBpos : 1 ≤ B := by omega
  -- the regions
  have hRx : R ≤ (x.length + 1) ^ 2 := calls_le_input [n] σ (toWord φ)
  obtain ⟨hw, hxw, hreg⟩ := regions_big hBpos hRx h
  have hsz : (2 * R + 3) ^ 2 ≤ lpCap w := by
    have hX1 : 1 ≤ X := by omega
    have hRX : R ≤ X ^ 2 := le_trans hRx (Nat.pow_le_pow_left (by omega) _)
    have hX2 : 1 ≤ X ^ 2 := Nat.one_le_pow _ _ hX1
    have h5 : (2 * R + 3) ^ 2 ≤ 25 * X ^ 4 := by
      have : 2 * R + 3 ≤ 5 * X ^ 2 := by omega
      calc (2 * R + 3) ^ 2 ≤ (5 * X ^ 2) ^ 2 := Nat.pow_le_pow_left this _
        _ = 25 * X ^ 4 := by ring
    have h6 : X ^ 4 ≤ X ^ 5 := Nat.pow_le_pow_right hX1 (by omega)
    have h7 : 2 ^ 30 * X ^ 5 ≤ 2 ^ w := by
      refine le_trans ?_ h
      have : 2 ^ 30 ≤ 2 ^ (D + 30 + sI) * B := by
        calc 2 ^ 30 ≤ 2 ^ (D + 30 + sI) := two_pow_mono (by omega)
          _ ≤ 2 ^ (D + 30 + sI) * B := Nat.le_mul_of_pos_right _ hBpos
      exact Nat.mul_le_mul_right _ this
    obtain ⟨-, h8⟩ := lpCap_bounds hw
    have h9 : 25 * X ^ 4 ≤ 2 ^ 27 * X ^ 5 := by
      calc 25 * X ^ 4 ≤ 2 ^ 27 * X ^ 4 := Nat.mul_le_mul_right _ (by norm_num)
        _ ≤ 2 ^ 27 * X ^ 5 := Nat.mul_le_mul_left _ h6
    have e30 : 2 ^ 30 * X ^ 5 = 8 * (2 ^ 27 * X ^ 5) := by ring
    omega
  obtain ⟨t, ht, hrun⟩ := pipe_run hC hsw hP0 hD rfl hhd hrd hB1 hB2 hB3
    (fun i hi => (hreg i hi).1) hw hxw hsz
  have hrun' : RunsTo w P0 x ans t := hrun
  have hfe : ans = 1 :: mcAns Gr φ := finAns_eq (by omega) hcs φ
  rw [hfe] at hrun'
  refine ⟨t, le_trans ht (Nat.mul_le_mul_left _ ?_), hrun'⟩
  show (∑ j ∈ Finset.range R, (bG x s q φ cs hd ans cG j + bP s q φ cs k Ks j + 2)) +
      (bG x s q φ cs hd ans cG R + 1) + ans.length + 1 ≤ _
  -- the sum of the rounds
  have hglue : ∀ j ≤ R, bG x s q φ cs hd ans cG j ≤
      (if j = 0 then cG * x.length else 0) + cG * (3 * pH2 cG n T + 2 * callB n T q φ + 7) := by
    intro j hj
    have h1 := hrs1 j hj
    have h1' : (pU x s q φ cs hd ans j).length + (glueOut s q φ cs hd ans j).length + 1 ≤
        (if j = 0 then x.length else 0) + (3 * pH2 cG n T + 2 * callB n T q φ + 7) := by omega
    have h2 : cG * ((pU x s q φ cs hd ans j).length + (glueOut s q φ cs hd ans j).length + 1) ≤
        cG * (if j = 0 then x.length else 0) + cG * (3 * pH2 cG n T + 2 * callB n T q φ + 7) := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left cG h1'
    show cG * ((pU x s q φ cs hd ans j).length + (glueOut s q φ cs hd ans j).length + 1) ≤ _
    split_ifs at h2 ⊢ <;> omega
  set M := mcR cG Ks n T q K φ k with hMd
  have hF : ∀ j (hj : j < R), bG x s q φ cs hd ans cG j + bP s q φ cs k Ks j + 2 ≤
      (if j = 0 then cG * x.length else 0) + callCost M M cs[j] := by
    intro j hj
    have hc : cs[j]? = some cs[j] := List.getElem?_eq_getElem hj
    have hmem : cs[j] ∈ cs := List.getElem_mem hj
    have h1 := hglue j hj.le
    have h2 : realT s q φ k cs[j] ≤ realB n T q K φ k := realT_le σ q hK φ k hmem
    have h3 : (callY s q φ cs[j]).length ≤ callB n T q φ := (hcall _ hmem).2.1
    have hbP : bP s q φ cs k Ks j ≤ Ks * (realB n T q K φ k + 3 * k.d + callB n T q φ + 1) := by
      simp only [bP, hc]
      exact Nat.mul_le_mul_left _ (by omega)
    have hcc : callCost M M cs[j] = M := by cases cs[j] <;> rfl
    rw [hcc, hMd, mcR]
    omega
  have hsum := sum_rounds_le (le_refl M) σ.steps _ hF
  have hlast := hglue R le_rfl
  have hfa : ans.length ≤ 2 := (finAns_small s q φ).1
  have hAc : cG * (3 * pH2 cG n T + 2 * callB n T q φ + 7) ≤ M := by
    rw [hMd, mcR]; omega
  have hlast' : bG x s q φ cs hd ans cG R ≤ cG * x.length + M :=
    le_trans hlast (Nat.add_le_add (ite_le_self (R = 0) (cG * x.length)) hAc)
  have hall := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hsum
    (Nat.add_le_add_right hlast' 1)) hfa) (le_refl 1)
  refine le_trans hall (le_of_eq ?_)
  ring

end Lax185574Proofs.MC
