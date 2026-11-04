import Lax185574Proofs.ResolveRam.Glue.PieceSpec
import Lax185574Proofs.ResolveRam.Glue.PHop2

/-!
Looking up a color in the color table.

The color table is word `oc` of the word library, of the shape
`cs.flatMap fun Y => [Y, f Y, g Y]`. `ctLook` scans its triples for the
color in `tY` and sets `th` to `1` if the color is in the table, and
`tx`, `tz` to the two entries of its triple (`0` if it is not there).
These are `inCT` and `tabLook` (`ctLook_run`), so they give the flags and
the tables of `dwOf`.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.FarRam Lax185574Proofs.EvalRam
open Lax185574.WordEncoding

theorem length_flat3 (cs : List ℕ) (f g : ℕ → ℕ) :
    (cs.flatMap fun Y => [Y, f Y, g Y]).length = 3 * cs.length := by
  induction cs with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, ih, List.length_cons]; simp; omega

theorem getElem?_flat3 (cs : List ℕ) (f g : ℕ → ℕ) {k : ℕ} (hk : k < cs.length) :
    (cs.flatMap fun Y => [Y, f Y, g Y])[3 * k]? = some cs[k] ∧
    (cs.flatMap fun Y => [Y, f Y, g Y])[3 * k + 1]? = some (f cs[k]) ∧
    (cs.flatMap fun Y => [Y, f Y, g Y])[3 * k + 2]? = some (g cs[k]) := by
  induction cs generalizing k with
  | nil => simp at hk
  | cons a l ih =>
    rcases k with _ | k
    · simp
    · have := ih (k := k) (by simpa using hk)
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.getElem_cons_succ]
      refine ⟨?_, ?_, ?_⟩
      · rw [show 3 * (k + 1) = 3 * k + 2 + 1 by ring]; simpa using this.1
      · rw [show 3 * (k + 1) + 1 = 3 * k + 1 + 2 + 1 by ring]; simpa using this.2.1
      · rw [show 3 * (k + 1) + 2 = 3 * k + 2 + 2 + 1 by ring]; simpa using this.2.2

theorem take_succ_memN {cs : List ℕ} {k : ℕ} (hk : k < cs.length) (Y : ℕ) :
    (Y ∈ cs.take (k + 1)) = (Y ∈ cs.take k ∨ cs[k] = Y) := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.mem_append, List.mem_singleton, eq_iff_iff]
  exact or_congr_right eq_comm

/-- One triple. -/
def ctBody : Com :=
  .ite (.eq (.var "th") (.lit 0))
    (.ite (.eq (.get "a" (.add (.var "tcb") (.mul (.var "tck") (.lit 3)))) (.var "tY"))
      (.seq (.assign "th" (.lit 1)) (.seq
        (.assign "tx" (.get "a" (.add (.add (.var "tcb") (.mul (.var "tck") (.lit 3))) (.lit 1))))
        (.assign "tz" (.get "a" (.add (.add (.var "tcb") (.mul (.var "tck") (.lit 3))) (.lit 2))))))
      .skip) .skip

/-- Look up the color `tY` in the table, word `oc` of the library. -/
def ctLook : Com :=
  .seq (.assign "th" (.lit 0)) (.seq (.assign "tx" (.lit 0)) (.seq (.assign "tz" (.lit 0))
    (.seq (.assign "tcn" (.div (.get "ln" (.var "oc")) (.lit 3)))
      (.seq (.assign "tcb" (.get "st" (.var "oc"))) (forUp "tck" (.var "tcn") ctBody)))))

/-- The scalars that `ctLook` writes. -/
def ctV : List String := ["th", "tx", "tz", "tcn", "tcb", "tck"]

theorem ctLook_wvars : ∀ y ∈ ctLook.wvars, y ∈ ctV := by decide

theorem ctLook_warrs : ctLook.warrs = [] := by decide

theorem ctLook_reads : ¬ ctLook.reads := by decide

theorem ctLook_noWrite : ctLook.NoWrite := by decide

/-- **Looking up a color in the table.** -/
theorem ctLook_run {B : ℕ} {ws : List (List ℕ)} {oc Y : ℕ} {cs : List ℕ} {f g : ℕ → ℕ} {τ : Env}
    (hw : WordsAt ws τ) (hoc : oc < ws.length) (hct : ws[oc] = cs.flatMap fun Y => [Y, f Y, g Y])
    (hocv : τ.vars "oc" = oc) (hY : τ.vars "tY" = Y) (hYB : Y < B)
    (hB : total ws + ws.length + 4 < B) (hv : ∀ v ∈ ws[oc], v < B) :
    ∃ τ', Run B ctLook τ τ' (20 * ws[oc].length + 40) ∧
      τ'.vars "th" = bv (decide (Y ∈ cs)) ∧
      τ'.vars "tx" = (if Y ∈ cs then f Y else 0) ∧ τ'.vars "tz" = (if Y ∈ cs then g Y else 0) ∧
      (∀ y, y ∉ ctV → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  have hlen := length_flat3 cs f g
  rw [← hct] at hlen
  have hoff := off_add_le hoc
  have hst := hw.st oc hoc
  have hln := hw.ln oc hoc
  set c := off ws oc
  have ent : ∀ j (hj : j < ws[oc].length), (τ.arrs "a")[c + j]? = some ws[oc][j] := hw.a oc hoc
  have hCB : 3 * cs.length < B := by omega
  set τ1 := (((τ.setVar "th" 0).setVar "tx" 0).setVar "tz" 0).setVar "tcn" cs.length
  set τ2 := τ1.setVar "tcb" c
  have ra : Run B (.assign "th" (.lit 0)) τ (τ.setVar "th" 0) 2 := Run.assign (evalB_lit (by omega))
  have rb : Run B (.assign "tx" (.lit 0)) (τ.setVar "th" 0) ((τ.setVar "th" 0).setVar "tx" 0) 2 :=
    Run.assign (evalB_lit (by omega))
  have rc : Run B (.assign "tz" (.lit 0)) ((τ.setVar "th" 0).setVar "tx" 0)
      (((τ.setVar "th" 0).setVar "tx" 0).setVar "tz" 0) 2 := Run.assign (evalB_lit (by omega))
  have rd : Run B (.assign "tcn" (.div (.get "ln" (.var "oc")) (.lit 3)))
      (((τ.setVar "th" 0).setVar "tx" 0).setVar "tz" 0) τ1 5 := by
    refine (Run.assign ?_).mono (by simp [Expr.size])
    have e1 : (Expr.get "ln" (.var "oc")).evalB B (((τ.setVar "th" 0).setVar "tx" 0).setVar "tz" 0) =
        some ws[oc].length :=
      evalB_get (ev_var (v := oc) (by simp [hocv]) (by omega)) (by simpa using hln) (by omega)
    have := evalB_bin (op := .div) e1 (evalB_lit (n := 3) (B := B) (by omega)) (by
      simp only [Bop.apply]; omega)
    rw [show Bop.div.apply ws[oc].length 3 = cs.length by simp only [Bop.apply]; omega] at this
    exact this
  have r2 : Run B (.assign "tcb" (.get "st" (.var "oc"))) τ1 τ2 3 :=
    (Run.assign (evalB_get (ev_var (v := oc) (by simp [τ1, hocv]) (by omega)) (by simpa [τ1] using hst)
      (by omega))).mono (by simp [Expr.size])
  let I : ℕ → Env → Prop := fun k ρ => ρ.arrs = τ.arrs ∧ ρ.vars "tcb" = c ∧ ρ.vars "tcn" = cs.length ∧
    ρ.vars "th" = bv (decide (Y ∈ cs.take k)) ∧ ρ.vars "tx" = (if Y ∈ cs.take k then f Y else 0) ∧
    ρ.vars "tz" = (if Y ∈ cs.take k then g Y else 0) ∧ ρ.vars "tY" = Y ∧
    (∀ y, y ∉ ctV → ρ.vars y = τ.vars y)
  obtain ⟨τ3, r3, ⟨a3, -, -, h3, x3, z3, -, v3⟩, -⟩ := forUp_run (B := B) (i := "tck") (e := .var "tcn")
    (body := ctBody) (N := cs.length) (K := 40) I (σ := τ2) (by omega)
    (fun k _ ρ hI _ => ev_var hI.2.2.1 (by omega))
    ⟨by simp [τ2, τ1], by simp [τ2], by simp [τ2, τ1], by simp [τ2, τ1], by simp [τ2, τ1],
      by simp [τ2, τ1], by simp [τ2, τ1, hY], fun y hy => by
        simp only [ctV, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
        simp [τ2, τ1, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1, hy.2.2.2.2.1, hy.2.2.2.2.2]⟩
    (by
      rintro k hk ρ ⟨aρ, bρ, nρ, hρ, xρ, zρ, yρ, vρ⟩ hkρ
      obtain ⟨e0, e1, e2⟩ := getElem?_flat3 cs f g hk
      rw [← hct] at e0 e1 e2
      have g0 := ent (3 * k) (by omega)
      have g1 := ent (3 * k + 1) (by omega)
      have g2 := ent (3 * k + 2) (by omega)
      rw [List.getElem?_eq_getElem (by omega)] at e0 e1 e2
      simp only [Option.some.injEq] at e0 e1 e2
      rw [e0] at g0; rw [e1] at g1; rw [e2] at g2
      have vB : ∀ j (hj : j < ws[oc].length), ws[oc][j] < B := fun j hj => hv _ (List.getElem_mem hj)
      have b0 : cs[k] < B := by rw [← e0]; exact vB _ _
      have b1 : f cs[k] < B := by rw [← e1]; exact vB _ _
      have b2 : g cs[k] < B := by rw [← e2]; exact vB _ _
      have hth : ρ.vars "th" < B := by rw [hρ]; exact lt_of_le_of_lt (bv_le _) (by omega)
      have ea : ∀ ρ' : Env, ρ'.vars "tcb" = c → ρ'.vars "tck" = k → ρ'.arrs = τ.arrs →
          (Expr.get "a" (.add (.var "tcb") (.mul (.var "tck") (.lit 3)))).evalB B ρ' = some cs[k] ∧
          (Expr.get "a" (.add (.add (.var "tcb") (.mul (.var "tck") (.lit 3))) (.lit 1))).evalB B ρ' =
            some (f cs[k]) ∧
          (Expr.get "a" (.add (.add (.var "tcb") (.mul (.var "tck") (.lit 3))) (.lit 2))).evalB B ρ' =
            some (g cs[k]) := by
        intro ρ' h1 h2 h3
        have hcB : c < B := by omega
        have hkB : k < B := by omega
        have hm3 : k * 3 < B := by omega
        have hcm : c + k * 3 < B := by omega
        have em : (Expr.add (.var "tcb") (.mul (.var "tck") (.lit 3))).evalB B ρ' = some (c + 3 * k) := by
          have := ev_add (ev_var h1 hcB) (evalB_bin (op := .mul) (ev_var h2 hkB)
            (evalB_lit (n := 3) (by omega)) hm3) hcm
          simpa [Bop.apply, Nat.mul_comm] using this
        refine ⟨evalB_get em (by rw [h3]; exact g0) b0, evalB_get (ev_add em (evalB_lit (by omega)) (by omega))
          (by rw [h3, Nat.add_assoc]; exact g1) b1,
          evalB_get (ev_add em (evalB_lit (by omega)) (by omega)) (by rw [h3, Nat.add_assoc]; exact g2) b2⟩
      have htake := take_succ_memN hk Y
      have fr : ∀ ρ' : Env, (∀ y, y ≠ "th" → y ≠ "tx" → y ≠ "tz" → ρ'.vars y = ρ.vars y) →
          (∀ y, y ∉ ctV → ρ'.vars y = τ.vars y) := fun ρ' h y hy => by
        simp only [ctV, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
        rw [h y hy.1 hy.2.1 hy.2.2.1, vρ y (by simp [ctV]; tauto)]
      by_cases hin : Y ∈ cs.take k
      · have h1 : ρ.vars "th" = 1 := by rw [hρ, decide_eq_true hin]; rfl
        refine ⟨ρ, (Run.ite_false (by rw [evalB_condEq (ev_var h1 (by omega)) (evalB_lit (by omega))]; rfl)
          Run.skip).mono (by simp [Cond.size, Expr.size]), hkρ, ?_⟩
        have hin' : Y ∈ cs.take (k + 1) := by rw [htake]; exact Or.inl hin
        refine ⟨by simp [aρ], by simp [bρ], by simp [nρ], by simp [hρ, hin, hin'], by simp [xρ, hin, hin'],
          by simp [zρ, hin, hin'], by simp [yρ], fun y hy => ?_⟩
        have : y ≠ "tck" := by rintro rfl; simp [ctV] at hy
        simp [this, vρ y hy]
      · have h0 : ρ.vars "th" = 0 := by rw [hρ, decide_eq_false hin]; rfl
        have c0 : (Cond.eq (.var "th") (.lit 0)).evalB B ρ = some true := by
          rw [evalB_condEq (ev_var h0 (by omega)) (evalB_lit (by omega))]; rfl
        obtain ⟨q0, -, -⟩ := ea ρ bρ hkρ aρ
        have cY := evalB_condEq q0 (ev_var yρ hYB)
        by_cases hyk : cs[k] = Y
        · set ρ1 := ρ.setVar "th" 1
          set ρ2 := ρ1.setVar "tx" (f cs[k])
          set ρ3 := ρ2.setVar "tz" (g cs[k])
          obtain ⟨-, q1, -⟩ := ea ρ1 (by simp [ρ1, bρ]) (by simp [ρ1, hkρ]) (by simp [ρ1, aρ])
          obtain ⟨-, -, q2⟩ := ea ρ2 (by simp [ρ2, ρ1, bρ]) (by simp [ρ2, ρ1, hkρ]) (by simp [ρ2, ρ1, aρ])
          refine ⟨ρ3, (Run.ite_true c0 (Run.ite_true (by rw [cY]; simp [hyk])
            (Run.seq (Run.assign (evalB_lit (by omega))) (Run.seq (Run.assign q1) (Run.assign q2))))).mono
              (by simp [Cond.size, Expr.size]), by simp [ρ3, ρ2, ρ1, hkρ], ?_⟩
          have hin' : Y ∈ cs.take (k + 1) := by rw [htake]; exact Or.inr hyk
          refine ⟨by simp [ρ3, ρ2, ρ1, aρ], by simp [ρ3, ρ2, ρ1, bρ], by simp [ρ3, ρ2, ρ1, nρ],
            by simp [ρ3, ρ2, ρ1, hin'], by simp [ρ3, ρ2, ρ1, hin', hyk], by simp [ρ3, ρ2, ρ1, hin', hyk],
            by simp [ρ3, ρ2, ρ1, yρ], fun y hy => ?_⟩
          have : y ≠ "tck" := by rintro rfl; simp [ctV] at hy
          simp only [vars_setVar, this, if_false]
          exact fr ρ3 (fun y a b c => by simp [ρ3, ρ2, ρ1, a, b, c]) y hy
        · refine ⟨ρ, (Run.ite_true c0 (Run.ite_false (by rw [cY]; simp [hyk]) Run.skip)).mono
            (by simp [Cond.size, Expr.size]), hkρ, ?_⟩
          have hin' : Y ∉ cs.take (k + 1) := by rw [htake]; exact fun h => h.elim hin hyk
          refine ⟨by simp [aρ], by simp [bρ], by simp [nρ], by simp [hρ, hin, hin'], by simp [xρ, hin, hin'],
            by simp [zρ, hin, hin'], by simp [yρ], fun y hy => ?_⟩
          have : y ≠ "tck" := by rintro rfl; simp [ctV] at hy
          simp [this, vρ y hy])
  have hrun : Run B ctLook τ τ3 (20 * ws[oc].length + 40) := by
    unfold ctLook
    refine (Run.seq ra (Run.seq rb (Run.seq rc (Run.seq rd (Run.seq r2 r3))))).mono ?_
    simp only [Expr.size]
    omega
  obtain ⟨fa, fo, fi⟩ := run_frame hrun ctLook_warrs ctLook_reads ctLook_noWrite
  refine ⟨τ3, hrun, ?_, ?_, ?_, v3, fa, fo, fi⟩
  · rw [h3, List.take_length]
  · rw [x3, List.take_length]
  · rw [z3, List.take_length]

end Lax185574Proofs.ResolveRam.Glue
