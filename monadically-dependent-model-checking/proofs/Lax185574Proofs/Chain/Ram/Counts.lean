import Lax185574Proofs.Chain.Ram.TpSpec

/-!
Neighbor counts per label.

For a labelling `L` in the array `labk`, the command `cntPhase` fills
the `n × n` matrix `cnt` with the number of neighbors of `u` with label
`c` (`cntN`), and `szPhase` fills `sz` with the number of vertices with
label `c` (`szN`). Both expect their arrays to be zero. The adjacency
matrix is `adj`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram

theorem card_filter_range_succ (p : ℕ → Prop) [DecidablePred p] (k : ℕ) :
    ((range (k + 1)).filter p).card = ((range k).filter p).card + if p k then 1 else 0 := by
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [card_insert_of_notMem (by simp)]
  · simp

theorem card_filter_range_le (p : ℕ → Prop) [DecidablePred p] (k : ℕ) :
    ((range k).filter p).card ≤ k :=
  (card_filter_le _ _).trans (by simp)

/-- The index `cu · n + labk[cz]`. -/
def cntIdx : Expr := .add (.mul (.var "cu") (.var "n")) (.get "labk" (.var "cz"))

/-- Count the neighbor `cz` of `cu`. -/
def cntBody : Com :=
  .ite (.eq (.get "adj" (rm "cu" "cz")) (.lit 1))
    (.store "cnt" cntIdx (.add (.get "cnt" cntIdx) (.lit 1))) .skip

/-- Fill `cnt`. -/
def cntPhase : Com := forUp "cu" (.var "n") (forUp "cz" (.var "n") cntBody)

/-- The index `labk[cz]`. -/
def szIdx : Expr := .get "labk" (.var "cz")

/-- Fill `sz`. -/
def szPhase : Com := forUp "cz" (.var "n") (.store "sz" szIdx (.add (.get "sz" szIdx) (.lit 1)))

/-- The context of the counting phases. -/
structure CntCtx (n : ℕ) (G : SimpleGraph (Fin n)) (L : ℕ → ℕ) (τ : Env) : Prop where
  hn : τ.vars "n" = n
  hadj : Mat τ "adj" n (fun u v => ind (gA G u v))
  hlabk : Vec τ "labk" n L

variable {n : ℕ} {G : SimpleGraph (Fin n)}

open Classical in
/-- The count of neighbors of `u` among the first `k` vertices with label `c`. -/
noncomputable def cntK (G : SimpleGraph (Fin n)) (L : ℕ → ℕ) (u k c : ℕ) : ℕ :=
  ((range k).filter fun z => gA G u z ∧ L z = c).card

open Classical in
theorem cntK_succ (L : ℕ → ℕ) (u k c : ℕ) :
    cntK G L u (k + 1) c = cntK G L u k c + if gA G u k ∧ L k = c then 1 else 0 := by
  classical
  unfold cntK; rw [card_filter_range_succ]

theorem cntK_le (L : ℕ → ℕ) (u k c : ℕ) : cntK G L u k c ≤ k := by
  classical
  unfold cntK; exact card_filter_range_le _ _

theorem cntK_n (L : ℕ → ℕ) (u c : ℕ) : cntK G L u n c = cntN G L u c := rfl

theorem cntPhase_run {B : ℕ} {L : ℕ → ℕ} (Ctx : Env → Prop) (hL : ∀ u < n, L u < n)
    (hB : n * n + n + 2 < B)
    (hC : ∀ τ, Ctx τ → CntCtx n G L τ)
    (hCu : ∀ τ v, Ctx τ → Ctx (τ.setVar "cu" v)) (hCz : ∀ τ v, Ctx τ → Ctx (τ.setVar "cz" v))
    (hCa : ∀ τ i v, Ctx τ → Ctx (τ.setArr "cnt" i v))
    {σ : Env} (hσ : Ctx σ) (hz : Mat σ "cnt" n (fun _ _ => 0)) :
    ∃ σ', Run B cntPhase σ σ' (n * (n * 60 + 20) + 10) ∧ Ctx σ' ∧
      Mat σ' "cnt" n (fun u c => cntN G L u c) := by
  classical
  have hnn : n ≤ n * n := Nat.le_mul_self n
  let I : ℕ → Env → Prop := fun u τ => Ctx τ ∧ (τ.arrs "cnt").length = n * n ∧
    ∀ u' < n, ∀ c < n, (τ.arrs "cnt")[u' * n + c]? = some (if u' < u then cntN G L u' c else 0)
  obtain ⟨σ', hr, ⟨hC', hl', hm'⟩, -⟩ :=
    forUp_run (B := B) (i := "cu") (e := .var "n") (body := forUp "cz" (.var "n") cntBody) (N := n) (K := n * 50 + 10) I (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [(hC τ hI.1).hn]; omega), (hC τ hI.1).hn])
      (σ := σ) ⟨hCu _ _ hσ, by simp [hz.len], fun u' hu c hc => by
        simpa using hz.get u' hu c hc⟩
      (by
        rintro u hu τ ⟨hCτ, hlen, hm⟩ hcu
        let J : ℕ → Env → Prop := fun k ρ => Ctx ρ ∧ ρ.vars "cu" = u ∧
          (ρ.arrs "cnt").length = n * n ∧
          ∀ u' < n, ∀ c < n, (ρ.arrs "cnt")[u' * n + c]? = some
            (if u' < u then cntN G L u' c else if u' = u then cntK G L u k c else 0)
        obtain ⟨ρ, hrI, ⟨hCρ, huρ, hlρ, hmρ⟩, -⟩ :=
          forUp_run (B := B) (i := "cz") (e := .var "n") (body := cntBody) (N := n) (K := 40) J (by omega)
            (fun k _ ρ hI _ => by rw [evalB_var (by rw [(hC ρ hI.1).hn]; omega), (hC ρ hI.1).hn])
            (σ := τ) ⟨hCz _ _ hCτ, by simp [hcu], by simp [hlen], fun u' hu' c hc => by
              simp only [arrs_setVar]
              rw [hm u' hu' c hc]
              by_cases h1 : u' < u
              · simp [h1]
              · by_cases h2 : u' = u
                · subst h2; simp [cntK]
                · simp [h1, h2]⟩
            (by
              rintro k hk ρ ⟨hCρ, huρ, hlρ, hmρ⟩ hcz
              have hR := hC ρ hCρ
              have hLk := hL k hk
              have hidx : u * n + L k < n * n := rowMajor_lt hu hLk
              have hev : cntIdx.evalB B ρ = some (u * n + L k) := by
                have h1 := hR.hlabk.evalB (B := B) hcz hk (by omega) (by omega)
                have h2 := evalB_bin (op := .mul) (evalB_var (x := "cu") (σ := ρ) (B := B)
                  (by rw [huρ]; omega)) (evalB_var (x := "n") (by rw [hR.hn]; omega))
                  (by simp [huρ, hR.hn]; nlinarith)
                have h3 := evalB_bin (op := .add) h2 h1 (by simp [huρ, hR.hn]; omega)
                simpa [cntIdx, huρ, hR.hn] using h3
              have hold := hmρ u hu (L k) hLk
              simp only [lt_irrefl, if_false, if_true] at hold
              have hadj : (Expr.get "adj" (rm "cu" "cz")).evalB B ρ = some (ind (gA G u k)) :=
                hR.hadj.evalB hR.hn huρ hcz hu hk (by omega) (by omega)
                  (by have := ind_le_one (gA G u k); omega)
              have hcB : cntK G L u k (L k) + 1 < B := by
                have := cntK_le (G := G) L u k (L k); omega
              have hcond : (Cond.eq (.get "adj" (rm "cu" "cz")) (.lit 1)).evalB B ρ =
                  some (decide (ind (gA G u k) = 1)) := evalB_condEq' hadj (evalB_lit (by omega))
              by_cases hg : gA G u k
              · refine ⟨ρ.setArr "cnt" (u * n + L k) (cntK G L u k (L k) + 1),
                  (Run.ite_true (by rw [hcond]; simp [ind, hg])
                    (Run.store (i := cntIdx) hev (evalB_bin (op := .add) (evalB_get hev hold
                      (by omega)) (evalB_lit (by omega)) (by simp; omega))
                      (by omega))).mono (by simp [cntIdx, rm]), by simp [hcz], ?_⟩
                refine ⟨hCz _ _ (hCa _ _ _ hCρ), by simp [huρ], by simp [hlρ],
                  fun u' hu' c hc => ?_⟩
                simp only [arrs_setVar, arrs_setArr, if_true]
                rw [List.getElem?_set]
                by_cases he : u * n + L k = u' * n + c
                · obtain ⟨rfl, rfl⟩ := rowMajor_inj hLk hc he
                  simp [hlρ, hidx, cntK_succ, hg]
                · rw [if_neg he, hmρ u' hu' c hc]
                  by_cases h1 : u' < u
                  · simp [h1]
                  · by_cases h2 : u' = u
                    · subst h2
                      have hc' : L k ≠ c := fun h => he (by rw [h])
                      simp [cntK_succ, hc']
                    · simp [h1, h2]
              · refine ⟨ρ, (Run.ite_false (by rw [hcond]; simp [ind, hg]) Run.skip).mono (by simp), hcz, ?_⟩
                refine ⟨hCz _ _ hCρ, by simp [huρ], by simp [hlρ], fun u' hu' c hc => ?_⟩
                simp only [arrs_setVar]
                rw [hmρ u' hu' c hc]
                by_cases h1 : u' < u
                · simp [h1]
                · by_cases h2 : u' = u
                  · subst h2; simp [cntK_succ, hg]
                  · simp [h1, h2])
        refine ⟨ρ, hrI.mono (by simp; omega), huρ, hCu _ _ hCρ, by simp [hlρ],
          fun u' hu' c hc => ?_⟩
        simp only [arrs_setVar]
        rw [hmρ u' hu' c hc]
        by_cases h1 : u' < u
        · simp [h1, show u' < u + 1 by omega]
        · by_cases h2 : u' = u
          · subst h2; simp [cntK_n]
          · simp [h1, h2, show ¬ u' < u + 1 by omega])
  refine ⟨σ', hr.mono (by simp; nlinarith), hC', ⟨hl', fun u hu c hc => ?_⟩⟩
  rw [hm' u hu c hc]; simp [hu]

open Classical in
/-- The number of the first `k` vertices with label `c`. -/
noncomputable def szK (L : ℕ → ℕ) (k c : ℕ) : ℕ := ((range k).filter fun z => L z = c).card

open Classical in
theorem szK_succ (L : ℕ → ℕ) (k c : ℕ) :
    szK L (k + 1) c = szK L k c + if L k = c then 1 else 0 := by
  classical
  unfold szK; rw [card_filter_range_succ]

theorem szK_le (L : ℕ → ℕ) (k c : ℕ) : szK L k c ≤ k := by
  classical
  unfold szK; exact card_filter_range_le _ _

theorem szPhase_run {B : ℕ} {L : ℕ → ℕ} (Ctx : Env → Prop) (hL : ∀ u < n, L u < n)
    (hB : n + 2 < B)
    (hC : ∀ τ, Ctx τ → CntCtx n G L τ)
    (hCz : ∀ τ v, Ctx τ → Ctx (τ.setVar "cz" v))
    (hCa : ∀ τ i v, Ctx τ → Ctx (τ.setArr "sz" i v))
    {σ : Env} (hσ : Ctx σ) (hz : Vec σ "sz" n (fun _ => 0)) :
    ∃ σ', Run B szPhase σ σ' (n * 30 + 10) ∧ Ctx σ' ∧ Vec σ' "sz" n (fun c => szN n L c) := by
  classical
  let I : ℕ → Env → Prop := fun k τ => Ctx τ ∧ (τ.arrs "sz").length = n ∧
    ∀ c < n, (τ.arrs "sz")[c]? = some (szK L k c)
  obtain ⟨σ', hr, ⟨hC', hl', hm'⟩, -⟩ :=
    forUp_run (B := B) (i := "cz") (e := .var "n")
      (body := .store "sz" szIdx (.add (.get "sz" szIdx) (.lit 1))) (N := n) (K := 20) I (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [(hC τ hI.1).hn]; omega), (hC τ hI.1).hn])
      (σ := σ) ⟨hCz _ _ hσ, by simp [hz.len], fun c hc => by simpa [szK] using hz.get c hc⟩
      (by
        rintro k hk τ ⟨hCτ, hlen, hm⟩ hcz
        have hR := hC τ hCτ
        have hLk := hL k hk
        have hev : szIdx.evalB B τ = some (L k) :=
          hR.hlabk.evalB (B := B) hcz hk (by omega) (by omega)
        have hold := hm (L k) hLk
        have hcB : szK L k (L k) + 1 < B := by have := szK_le L k (L k); omega
        refine ⟨τ.setArr "sz" (L k) (szK L k (L k) + 1),
          (Run.store (i := szIdx) hev (evalB_bin (op := .add) (evalB_get hev hold (by omega))
            (evalB_lit (by omega)) (by simp; omega)) (by omega)).mono (by simp [szIdx]),
          by simp [hcz], hCz _ _ (hCa _ _ _ hCτ), by simp [hlen], fun c hc => ?_⟩
        simp only [arrs_setVar, arrs_setArr, if_true]
        rw [List.getElem?_set]
        by_cases he : L k = c
        · subst he; simp [hlen, hLk, szK_succ]
        · rw [if_neg he, hm c hc, szK_succ, if_neg he]; rfl)
  exact ⟨σ', hr.mono (by simp; omega), hC', ⟨hl', fun c hc => hm' c hc⟩⟩

end Lax185574Proofs.Chain.Ram
