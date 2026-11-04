import Lax185574Proofs.Chain.Ram.ChainSeq
import Lax185574Proofs.Conversions.Ram.Encode

/-!
Writing the chain.

The chain is the list of the unions `B_i` of the suffixes of the damping
sequence. A vertex `v` lies in `B_i` if and only if `i` is below `lst[v]`,
one more than the last index of a set of the sequence containing `v`
(`lstCom`). The command `outCom` writes the length of the chain and then
every `B_i` as its size followed by the frames of its members.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram Lax185574Proofs.Chain Lax185574.WordEncoding

variable {n : ℕ}

/-- `v` lies in a set `D j` with `i ≤ j < M`. -/
def inSuf (D : ℕ → Finset (Fin n)) (M i v : ℕ) : Prop := ∃ j, i ≤ j ∧ j < M ∧ inBN (D j) v

open Classical in
theorem suffixUnions_eq (D : ℕ → Finset (Fin n)) (M : ℕ) :
    suffixUnions ((List.range M).map D ++ [∅]) =
      (List.range (M + 1)).map fun i => univ.filter fun v : Fin n => inSuf D M i v := by
  unfold suffixUnions
  simp only [List.length_append, List.length_map, List.length_range, List.length_singleton]
  refine List.map_congr_left fun i hi => ?_
  refine Finset.ext fun v => ?_
  rw [Finset.mem_filter, mem_biUnion]
  simp only [mem_Ico, mem_univ, true_and, inSuf]
  constructor
  · rintro ⟨j, ⟨h1, h2⟩, hv⟩
    rcases Nat.lt_or_ge j M with hj | hj
    · refine ⟨j, h1, hj, v.2, ?_⟩
      rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp; omega)]
        at hv
      simpa using hv
    · have : j = M := by omega
      subst this
      rw [List.getD_eq_getElem _ _ (by simp), List.getElem_append_right (by simp)] at hv
      simp at hv
  · rintro ⟨j, h1, h2, _, hv⟩
    refine ⟨j, ⟨h1, by omega⟩, ?_⟩
    rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_left (by simp; omega)]
    simpa using hv

open Classical in
/-- **The word of the chain.** -/
theorem toWord_suffix (D : ℕ → Finset (Fin n)) (M : ℕ) :
    toWord (suffixUnions ((List.range M).map D ++ [∅])) =
      (M + 1) :: (List.range (M + 1)).flatMap fun i =>
        (below n (inSuf D M i)).length :: elemFrames (below n (inSuf D M i)) := by
  rw [suffixUnions_eq]
  change ((List.range (M + 1)).map _).length :: (((List.range (M + 1)).map _).map toWord).flatten = _
  simp only [List.length_map, List.length_range, List.map_map, List.flatMap]
  congr 2
  refine List.map_congr_left fun i _ => ?_
  have hs : sortedVals (univ.filter fun v : Fin n => inSuf D M i v) = below n (inSuf D M i) :=
    sortedVals_eq_below _ _ fun u => by simp
  simp only [Function.comp, toWord_finset_fin, hs, ← length_sortedVals]

/-! ### The last index -/

/-- Record the last index of a set containing each vertex. -/
def lstCom : Com :=
  .seq (rowFill "lst" (.var "b") (.lit 0))
    (forUp "oj" (.var "m") (forUp "ov" (.var "n")
      (.ite (.eq (.get "ch" (rm "oj" "ov")) (.lit 1))
        (.store "lst" (.var "ov") (.add (.var "oj") (.lit 1))) .skip)))

/-- `lst` describes the suffix unions of the first `k` sets. -/
def LstOK (D : ℕ → Finset (Fin n)) (k : ℕ) (L : ℕ → ℕ) : Prop :=
  ∀ v < n, L v ≤ k ∧ ∀ i, (i < L v ↔ inSuf D k i v)

theorem LstOK.zero (D : ℕ → Finset (Fin n)) : LstOK D 0 (fun _ => 0) := fun v _ =>
  ⟨le_rfl, fun i => ⟨fun h => absurd h (Nat.not_lt_zero _), fun ⟨j, _, h, _⟩ => absurd h (by omega)⟩⟩

open Classical in
theorem LstOK.succ {D : ℕ → Finset (Fin n)} {k : ℕ} {L : ℕ → ℕ} (h : LstOK D k L) :
    LstOK D (k + 1) (fun u => if inBN (D k) u then k + 1 else L u) := by
  intro v hv
  obtain ⟨h1, h2⟩ := h v hv
  by_cases hk : inBN (D k) v
  · simp only [if_pos hk]
    refine ⟨le_rfl, fun i => ⟨fun hi => ⟨k, by omega, by omega, hk⟩, fun ⟨j, hj1, hj2, _⟩ => by
      omega⟩⟩
  · simp only [if_neg hk]
    refine ⟨by omega, fun i => (h2 i).trans ⟨fun ⟨j, a, b, c⟩ => ⟨j, a, by omega, c⟩,
      fun ⟨j, a, b, c⟩ => ⟨j, a, ?_, c⟩⟩⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp b with b | rfl
    · exact b
    · exact absurd c hk

theorem LstOK.congr {D : ℕ → Finset (Fin n)} {k : ℕ} {L L' : ℕ → ℕ} (h : LstOK D k L)
    (he : ∀ v < n, L' v = L v) : LstOK D k L' := fun v hv => by rw [he v hv]; exact h v hv

theorem lstCom_run {B M : ℕ} {D : ℕ → Finset (Fin n)} (hMn : M ≤ n) (hB : (n + 1) * n + n + 2 < B)
    {σ : Env} (hn : σ.vars "n" = n) (hm : σ.vars "m" = M)
    (hch : ∀ j < M, ∀ u < n, (σ.arrs "ch")[j * n + u]? = some (ind (inBN (D j) u)))
    (hlst : (σ.arrs "lst").length = n) :
    ∃ σ', Run B lstCom σ σ' (n * (n * 30 + 40) + 40) ∧
      (∀ x, x ∉ ["b", "oj", "ov"] → σ'.vars x = σ.vars x) ∧
      (∀ a, a ≠ "lst" → σ'.arrs a = σ.arrs a) ∧ (σ'.arrs "lst").length = n ∧
      LstOK D M (fun v => (σ'.arrs "lst").getD v 0) := by
  classical
  have hnB : n < B := by nlinarith
  obtain ⟨σ1, hr1, hv1, ha1, hl1, hg1⟩ :=
    fillKeep_run (B' := B) (arr := "lst") (e := .lit 0) (f := fun _ => 0) (base := 0) (K := 3)
      hnB hn (by omega) (.var "b") (fun τ k hv ha hb hk => by simp [hb]; omega)
      (fun τ k hv ha hb hk => by simp; omega) (by simp)
  let I : ℕ → Env → Prop := fun k τ => (∀ x, x ∉ ["b", "oj", "ov"] → τ.vars x = σ.vars x) ∧
    (∀ a, a ≠ "lst" → τ.arrs a = σ.arrs a) ∧ (τ.arrs "lst").length = n ∧
    LstOK D k (fun v => (τ.arrs "lst").getD v 0)
  have hI0 : I 0 (σ1.setVar "oj" 0) := by
    refine ⟨fun x hx => ?_, fun a ha => by simpa using ha1 a ha, by simp [hl1, hlst], ?_⟩
    · have : x ≠ "oj" := by intro e; subst e; simp at hx
      simp [this, hv1 x (by intro e; subst e; simp at hx)]
    · refine (LstOK.zero D).congr fun v hv => ?_
      simp only [arrs_setVar]
      rw [List.getD_eq_getElem?_getD, hg1 v, if_pos ⟨by omega, by omega⟩]; rfl
  obtain ⟨σ2, hr2, ⟨hv2, ha2, hl2, hok2⟩, -⟩ :=
    forUp_run (B := B) (i := "oj") (e := .var "m")
      (body := forUp "ov" (.var "n") (.ite (.eq (.get "ch" (rm "oj" "ov")) (.lit 1))
        (.store "lst" (.var "ov") (.add (.var "oj") (.lit 1))) .skip))
      (N := M) (K := n * 30 + 10) I (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [hI.1 "m" (by decide), hm]; omega),
        hI.1 "m" (by decide), hm]) hI0
      (by
        rintro k hk τ ⟨hvτ, haτ, hlτ, hokτ⟩ hojk
        let L0 : ℕ → ℕ := fun v => (τ.arrs "lst").getD v 0
        let J : ℕ → Env → Prop := fun w ρ => (∀ x, x ∉ ["b", "oj", "ov"] → ρ.vars x = σ.vars x) ∧
          ρ.vars "oj" = k ∧ (∀ a, a ≠ "lst" → ρ.arrs a = σ.arrs a) ∧ (ρ.arrs "lst").length = n ∧
          ∀ u < n, (ρ.arrs "lst").getD u 0 = if u < w ∧ inBN (D k) u then k + 1 else L0 u
        obtain ⟨ρ, hrI, ⟨hvρ, hojρ, haρ, hlρ, hgρ⟩, -⟩ :=
          forUp_run (B := B) (i := "ov") (e := .var "n")
            (body := .ite (.eq (.get "ch" (rm "oj" "ov")) (.lit 1))
              (.store "lst" (.var "ov") (.add (.var "oj") (.lit 1))) .skip)
            (N := n) (K := 20) J (by omega)
            (fun k _ ρ hI _ => by rw [evalB_var (by rw [hI.1 "n" (by decide), hn]; omega),
              hI.1 "n" (by decide), hn])
            (σ := τ) ⟨fun x hx => by
                have : x ≠ "ov" := by intro e; subst e; simp at hx
                simp [this, hvτ x hx], by simp [hojk], fun a ha => by simpa using haτ a ha,
              by simp [hlτ], fun u hu => by simp [L0]⟩
            (by
              rintro w hw ρ ⟨hvρ, hojρ, haρ, hlρ, hgρ⟩ hovw
              have hnρ : ρ.vars "n" = n := by rw [hvρ "n" (by decide), hn]
              have hidx : k * n + w < (n + 1) * n := by
                have := rowMajor_lt (show k < n + 1 by omega) hw; omega
              have hch' : (ρ.arrs "ch")[k * n + w]? = some (ind (inBN (D k) w)) := by
                rw [haρ "ch" (by decide)]; exact hch k hk w hw
              have hev := evalB_getRM (B := B) (a := "ch") hojρ hnρ hovw hw (by omega) (by omega)
                hch' (by have := ind_le_one (inBN (D k) w); omega)
              have hcond : (Cond.eq (.get "ch" (rm "oj" "ov")) (.lit 1)).evalB B ρ =
                  some (decide (ind (inBN (D k) w) = 1)) := evalB_condEq' hev (evalB_lit (by omega))
              by_cases hin : inBN (D k) w
              · refine ⟨ρ.setArr "lst" w (k + 1), (Run.ite_true (by rw [hcond]; simp [ind, hin])
                  (Run.store (i := .var "ov") (idx := w) (by simp [hovw]; omega)
                    (by simp [hojρ]; omega) (by rw [hlρ]; exact hw))).mono (by simp [rm]),
                  by simp [hovw], ?_⟩
                refine ⟨fun x hx => ?_, by simp [hojρ], fun a ha => by
                    simp only [arrs_setVar, arrs_setArr, if_neg ha]; exact haρ a ha,
                  by simp [hlρ], fun u hu => ?_⟩
                · have : x ≠ "ov" := by intro e; subst e; simp at hx
                  simp [this, hvρ x hx]
                · simp only [arrs_setVar, arrs_setArr, if_true, List.getD_eq_getElem?_getD,
                    List.getElem?_set]
                  by_cases huw : w = u
                  · subst huw; simp [hlρ, hu, hin]
                  · rw [if_neg huw]
                    have := hgρ u hu
                    rw [List.getD_eq_getElem?_getD] at this
                    rw [this]
                    by_cases hlt : u < w
                    · simp [hlt, show u < w + 1 by omega]
                    · simp [hlt, show ¬ u < w + 1 by omega]
              · refine ⟨ρ, (Run.ite_false (by rw [hcond]; simp [ind, hin]) Run.skip).mono
                  (by simp [rm]), hovw, ?_⟩
                refine ⟨fun x hx => ?_, by simp [hojρ], fun a ha => by simpa using haρ a ha,
                  by simp [hlρ], fun u hu => ?_⟩
                · have : x ≠ "ov" := by intro e; subst e; simp at hx
                  simp [this, hvρ x hx]
                · simp only [arrs_setVar]
                  rw [hgρ u hu]
                  by_cases huw : u = w
                  · subst huw; simp [hin]
                  · by_cases hlt : u < w
                    · simp [hlt, show u < w + 1 by omega]
                    · simp [hlt, show ¬ u < w + 1 by omega])
        refine ⟨ρ, hrI.mono (by simp [rm]; omega), by rw [hrI.frame_var "oj" (by decide), hojk],
          ⟨fun x hx => ?_, fun a ha => by simpa using haρ a ha, by simp [hlρ], ?_⟩⟩
        · have : x ≠ "oj" := by intro e; subst e; simp at hx
          simp [this, hvρ x hx]
        · refine hokτ.succ.congr fun u hu => ?_
          simp only [arrs_setVar]
          rw [hgρ u hu]
          simp [hu, L0])
  refine ⟨σ2, (Run.seq hr1 hr2).mono ?_, fun x hx => ?_, fun a ha => by rw [ha2 a ha],
    hl2, hok2⟩
  · have : M * (n * 30 + 10 + 1 + 7) ≤ n * (n * 30 + 18) := Nat.mul_le_mul_right _ hMn
    simp; nlinarith
  · exact hv2 x hx

/-! ### Writing -/

/-- `w ∈ B_oi`. -/
def outC : Cond := .lt (.var "oi") (.get "lst" (.var "w"))

/-- Write one set. -/
def outSet : Com := .seq (countRow outC) (.seq (.write (.var "d")) (emitRow outC))

/-- Write the chain. -/
def outCom : Com :=
  .seq (.write (.add (.var "m") (.lit 1))) (forUp "oi" (.add (.var "m") (.lit 1)) outSet)

open Classical in
theorem outCom_run {B M : ℕ} {D : ℕ → Finset (Fin n)} (hMn : M ≤ n) (hB : 2 * n + 4 < B)
    {σ : Env} (hn : σ.vars "n" = n) (hm : σ.vars "m" = M) (hl : (σ.arrs "lst").length = n)
    (hok : LstOK D M (fun v => (σ.arrs "lst").getD v 0)) :
    ∃ σ', Run B outCom σ σ' ((n + 1) * (n * 60 + 80) + 20) ∧
      σ'.out = σ.out ++ ((M + 1) :: (List.range (M + 1)).flatMap fun i =>
        (below n (inSuf D M i)).length :: elemFrames (below n (inSuf D M i))) := by
  let Ctx : Env → Prop := fun τ => (∀ x, x ∉ ["oi", "w", "d"] → τ.vars x = σ.vars x) ∧
    τ.arrs = σ.arrs
  have hC : ∀ τ x v, Ctx τ → x ∈ ["oi", "w", "d"] → Ctx (τ.setVar x v) := fun τ x v h hx =>
    ⟨fun y hy => by
      have : y ≠ x := by intro e; subst e; exact hy hx
      simp [this, h.1 y hy], h.2⟩
  have hcond : ∀ τ i k, Ctx τ → τ.vars "oi" = i → i ≤ M → τ.vars "w" = k → k < n →
      outC.evalB B τ = some (decide (inSuf D M i k)) := by
    intro τ i k h hi hiM hk hkn
    have hlk : (σ.arrs "lst").getD k 0 ≤ M := (hok k hkn).1
    have hget : (τ.arrs "lst")[k]? = some ((σ.arrs "lst").getD k 0) := by
      rw [h.2, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; simp
    have hiB : i < B := by omega
    rw [show outC = .lt (.var "oi") (.get "lst" (.var "w")) from rfl,
      evalB_condLt (evalB_var (by rw [hi]; exact hiB))
        (evalB_get (evalB_var (by rw [hk]; omega)) (by rw [hk]; exact hget) (by omega)), hi]
    congr 1
    exact decide_eq_decide.2 ((hok k hkn).2 i)
  let F : ℕ → List ℕ := fun i =>
    (below n (inSuf D M i)).length :: elemFrames (below n (inSuf D M i))
  let I : ℕ → Env → Prop := fun k τ => Ctx τ ∧
    τ.out = σ.out ++ ((M + 1) :: (List.range k).flatMap F)
  have hlenle : ∀ i, (below n (inSuf D M i)).length ≤ n := fun i => length_below_le n _
  obtain ⟨σ1, hr1, ⟨hC1, ho1⟩, -⟩ :=
    forUp_run (B := B) (i := "oi") (e := .add (.var "m") (.lit 1)) (body := outSet) (N := M + 1)
      (K := n * 60 + 60) I (by omega)
      (fun k _ τ hI _ => by
        have := evalB_bin (op := .add) (evalB_var (x := "m") (σ := τ) (B := B)
          (by rw [hI.1.1 "m" (by decide), hm]; omega)) (evalB_lit (n := 1) (by omega))
          (by simp [hI.1.1 "m" (by decide), hm]; omega)
        simpa [hI.1.1 "m" (by decide), hm] using this)
      (σ := { σ with out := σ.out ++ [M + 1] }) ⟨hC _ _ _ ⟨fun _ _ => rfl, rfl⟩ (by simp),
        by simp⟩
      (by
        rintro i hi τ ⟨hCτ, hoτ⟩ hoi
        obtain ⟨τ1, hr1, ⟨hC1, hi1⟩, hd1, ho1⟩ :=
          countRow_run (B := B) (n := n) (c := outC) (fun ρ => Ctx ρ ∧ ρ.vars "oi" = i)
            (inSuf D M i) (by omega) (fun ρ h => by rw [h.1.1 "n" (by decide), hn])
            (fun ρ x h => ⟨hC _ _ _ h.1 (by simp), by simp [h.2]⟩)
            (fun ρ x h => ⟨hC _ _ _ h.1 (by simp), by simp [h.2]⟩)
            (fun ρ k h hk hkn => hcond ρ i k h.1 h.2 (by omega) hk hkn) ⟨hCτ, hoi⟩
        have hw : Run B (.write (.var "d")) τ1 { τ1 with out := τ1.out ++ [(below n (inSuf D M i)).length] } 2 :=
          (Run.write (by simp [hd1]; have := hlenle i; omega)).mono (by simp)
        obtain ⟨τ2, hr2, ⟨hC2, hi2⟩, ho2⟩ :=
          emitRow_run (B := B) (n := n) (c := outC) (fun ρ => Ctx ρ ∧ ρ.vars "oi" = i)
            (inSuf D M i) (by omega) (fun ρ h => by rw [h.1.1 "n" (by decide), hn])
            (fun ρ x h => ⟨hC _ _ _ h.1 (by simp), by simp [h.2]⟩)
            (fun ρ o h => ⟨⟨fun y hy => h.1.1 y hy, h.1.2⟩, h.2⟩)
            (fun ρ k h hk hkn => hcond ρ i k h.1 h.2 (by omega) hk hkn)
            (σ := { τ1 with out := τ1.out ++ [(below n (inSuf D M i)).length] })
            ⟨⟨fun y hy => hC1.1 y hy, hC1.2⟩, hi1⟩
        refine ⟨τ2, (Run.seq hr1 (Run.seq hw hr2)).mono (by simp [outC]; omega), hi2, ?_, ?_⟩
        · exact hC _ _ _ hC2 (by simp)
        · show τ2.out = _
          rw [ho2]
          simp only
          rw [ho1, hoτ]
          simp [List.range_succ, List.flatMap_append, F])
  refine ⟨σ1, (Run.seq (Run.write (by simp [hm]; omega)) hr1).mono (by simp; nlinarith), ?_⟩
  rw [ho1]

end Lax185574Proofs.Chain.Ram
