import Lax185574Proofs.FarRam.Out


/-!
The last round of the far-tree program: the radius search, the pass over
the extensions, the scan of the scatter type and the output.
-/

namespace Lax185574Proofs.FarRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.EvalRam
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo
open Lax3.DistFO (rhoMinus)

def finalCmd : Com := .seq radPhase (.seq extPhase (.seq scanSel outPhase))

theorem outList_eq_farList (X : List ℕ) (W : List (List ℕ)) (k q ℓ nS : ℕ) (hnW : nS ≤ W.length) :
    outList W (fun i => selW X (W.drop nS) k q (rhoMinus (k + 1) q) (radW X (rhoMinus (k + 1) q) ℓ) ℓ
      (canonW X (4 * radW X (rhoMinus (k + 1) q) ℓ - 2 * rhoMinus (k + 1) q) ℓ) (wd W i)) nS =
      farList X (W.drop nS) k q ℓ (W.take nS) := by
  unfold outList farList
  set p := selW X (W.drop nS) k q (rhoMinus (k + 1) q) (radW X (rhoMinus (k + 1) q) ℓ) ℓ
      (canonW X (4 * radW X (rhoMinus (k + 1) q) ℓ - 2 * rhoMinus (k + 1) q) ℓ)
  have hS : W.take nS = (List.range nS).map (wd W) := by
    apply List.ext_getElem (by simp; omega)
    intro i h1 h2
    simp only [List.getElem_take, List.getElem_map, List.getElem_range]
    rw [wd_eq (by simp at h1; omega)]
  rw [hS, List.filter_map, List.map_map]
  rfl

theorem stable_wordsAt {c : Com} (W : List (List ℕ)) (ha : "a" ∉ c.warrs) (hst : "st" ∉ c.warrs)
    (hln : "ln" ∉ c.warrs) : Stable (WordsAt W) c :=
  fun τ τ' _ h2 _ _ _ h => h.of_arrs (h2 "a" ha) (h2 "st" hst) (h2 "ln" hln)

theorem stable_out {c : Com} (o : List ℕ) : Stable (fun τ => τ.out = o) c :=
  fun _ τ' _ _ _ ho _ h => by show τ'.out = o; rw [ho]; exact h

def finalCost (X : List ℕ) (W : List (List ℕ)) (k q ℓ nS R : ℕ) : ℕ :=
  radCost X ℓ ((k + (q + 1) + 1) * q) (9 ^ (ℓ - 1) * rhoMinus (k + 1) q) + extCost X ℓ R +
    scanCost W ℓ R nS + outCost W nS + 3

/-- **The last round.** -/
theorem finalCmd_run (B : ℕ) (X : List ℕ) {q ℓ : ℕ} (t : Node (q + 1) ℓ) (rest : List ℕ)
    (hx : X.drop 0 = toWord t ++ rest) (k : ℕ) (W : List (List ℕ)) (nS : ℕ) (σ : Env)
    (hR : RootAt X ℓ σ) (hk : σ.vars "hk" = k) (hq : σ.vars "hq" = q + 1) (hw : WordsAt W σ)
    (hns : σ.vars "ns" = nS) (hWl : W.length = nS + (Node.exts t).words.length)
    (hbt : ℓ ≤ (σ.arrs "bt").length) (hmt : (Node.exts t).words.length * ℓ ≤ (σ.arrs "mt").length)
    (hfar : (Node.exts t).words.length ≤ (σ.arrs "far").length)
    (heqa : (Node.exts t).words.length ≤ (σ.arrs "eqa").length) (hsel : nS ≤ (σ.arrs "sel").length)
    (h3 : ∀ j < nS, 3 ≤ (wd W j).length) (hb : WordsBound B W) (hX : ∀ v ∈ X, v < B)
    (hXB : X.length + 5 < B) (h9 : 9 < B)
    (hRB : 4 * (9 ^ (ℓ - 1) * rhoMinus (k + 1) q) + 2 * rhoMinus (k + 1) q + 2 < B)
    (hEB : (k + (q + 1) + 1) * q + 1 < B) (hkB : k + q + 3 < B)
    (hNB : (Node.exts t).words.length * ℓ + ℓ + nS + (Node.exts t).words.length + 2 < B) :
    ∃ σ', Run B finalCmd σ σ' (finalCost X W k q ℓ nS (Node.exts t).words.length) ∧
      σ'.out = σ.out ++ 0 :: toWord (farList X (W.drop nS) k q ℓ (W.take nS)) := by
  set R := (Node.exts t).words.length with hRdef
  set r := rhoMinus (k + 1) q
  have hL0 : ListFacts X 0 := by obtain ⟨r', hr'⟩ := atoms_drop hx; exact listFacts_of hr'
  -- the radius search
  let C1 : Env → Prop := fun τ => WordsAt W τ ∧ τ.vars "ns" = nS ∧ τ.out = σ.out ∧
    R * ℓ ≤ (τ.arrs "mt").length ∧ R ≤ (τ.arrs "far").length ∧ R ≤ (τ.arrs "eqa").length ∧
    nS ≤ (τ.arrs "sel").length
  have hS1 : ∀ c : Com, "a" ∉ c.warrs → "st" ∉ c.warrs → "ln" ∉ c.warrs → "ns" ∉ c.wvars →
      c.NoWrite → Stable C1 c := fun c h1 h2 h3' h4 _ =>
    (stable_wordsAt W h1 h2 h3').and ((stable_var "ns" nS h4).and
      ((stable_out σ.out).and ((stable_len "mt" _).and ((stable_len "far" _).and
          ((stable_len "eqa" _).and (stable_len "sel" _))))))
  obtain ⟨σ1, r1, hC1, hR1, hk1, hq1, hr01, hrho1, hbt1⟩ := radPhase_spec B X k q ℓ C1
    (hS1 radPhase (by decide) (by decide) (by decide) (by decide) (by decide)) hL0 hX hXB
    (by omega) hRB hEB hkB h9 σ ⟨⟨hw, hns, rfl, hmt, hfar, heqa, hsel⟩, hR, hk, hq, hbt⟩
  set ρ := radW X r ℓ
  set s := 4 * ρ - 2 * r
  have hρU : ρ ≤ 9 ^ (ℓ - 1) * r := by
    obtain ⟨-, h⟩ := radW_bounds X r ℓ
    have : r ≤ 9 ^ (ℓ - 1) * r := Nat.le_mul_of_pos_left _ (Nat.one_le_pow _ _ (by norm_num))
    exact le_trans h (max_le this le_rfl)
  -- the extensions
  let C2 : Env → Prop := fun τ => C1 τ ∧ τ.vars "hk" = k ∧ τ.vars "hq" = q + 1 ∧ τ.vars "rho" = ρ ∧
    BtAt X ℓ s ℓ τ
  have hS2 : Stable C2 extPhase := (hS1 extPhase (by decide) (by decide) (by decide) (by decide)
    (by decide)).and ((stable_var "hk" k (by decide)).and ((stable_var "hq" (q + 1) (by decide)).and
      ((stable_var "rho" ρ (by decide)).and (stable_btAt X ℓ s ℓ (by decide)))))
  have hrB : r < B := by omega
  have hRℓ : R * ℓ + ℓ + 1 < B := by omega
  have hR1B : R + 1 < B := by omega
  obtain ⟨σ2, r2, hC2, hF2, hRw2⟩ := extPhase_spec B X t rest hx r C2 hS2 hX hXB hrB hRℓ hR1B σ1 ⟨⟨hC1, hk1, hq1, hrho1, hbt1⟩, hR1, hr01, hC1.2.2.2.1, hC1.2.2.2.2.1⟩
  rw [← hRdef] at r2
  -- the scan
  obtain ⟨⟨hw2, hns2, hout2, -, -, heqa2, hsel2⟩, hk2, hq2, hrho2, hbt2⟩ := hC2
  have hS3 : Stable (fun τ => τ.out = σ.out) scanSel := stable_out σ.out
  obtain ⟨σ3, r3, hout3, hF3, hR3, hSA3⟩ := scanSel_spec B X W nS R r ℓ s k q ρ _ hS3 hb h3 (by omega)
    (by omega) (by omega) (by omega) h9 σ2
    ⟨hout2, ⟨hw2, hns2, hF2.2.2.1, hWl, heqa2⟩, ⟨hRw2, hbt2, hF2.1.2.2, hrho2, hk2, hq2, hsel2⟩⟩
  -- the output
  obtain ⟨σ4, r4, hout4⟩ := outPhase_spec B W nS _ σ3 hF3.1 hb hF3.2.1 (by omega) hSA3
    (fun i hi => by have := h3 i hi; omega) (by omega)
  refine ⟨σ4, ?_, ?_⟩
  · unfold finalCmd
    exact (Run.seq r1 (Run.seq r2 (Run.seq r3 r4))).mono (by simp only [finalCost]; omega)
  · rw [hout4, hout3, outList_eq_farList X W k q ℓ nS (by omega)]

end Lax185574Proofs.FarRam
