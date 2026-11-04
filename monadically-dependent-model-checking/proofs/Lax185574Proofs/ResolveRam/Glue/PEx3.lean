import Lax185574Proofs.ResolveRam.Glue.PEx2

/-!
The header of the expansion of an item of lem:resolve-lift.

The item word is `p :: g :: k :: (q + 1) :: ℓ :: toWord t`. `exHdr` reads
`k + 1`, `q`, `ℓ`, `ℓ + 1` into `tk1`, `tqq`, `tL`, `tl1`, sets the
header `k + 1, q, ℓ + 1` of the children into `th0`, `th1`, `th2`, the
new position `ti2 = ℓ`, the radius `ts = rhoPlus (k + 1) q` and the count
`pc = 0` (`exHdr_run`). `exSkip` moves over the atom list of the root and
leaves the position and the length of the list of extensions in `te`,
`tne` (`exSkip_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.EvalRam Lax185574Proofs.FarRam
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo
open Lax3.DistFO (rhoPlus)

/-- Read the header of the item. -/
def exHdr : Com :=
  .seq (.assign "tb0" (.get "st" (.var "ow")))
  (.seq (.assign "tk1" (.add (.get "a" (.add (.var "tb0") (.lit 2))) (.lit 1)))
  (.seq (.assign "tqq" (.sub (.get "a" (.add (.var "tb0") (.lit 3))) (.lit 1)))
  (.seq (.assign "tL" (.get "a" (.add (.var "tb0") (.lit 4))))
  (.seq (.assign "tl1" (.add (.var "tL") (.lit 1)))
  (.seq (.assign "ti2" (.var "tL"))
  (.seq (.assign "th0" (.var "tk1")) (.seq (.assign "th1" (.var "tqq")) (.seq (.assign "th2" (.var "tl1"))
  (.seq (.assign "tE" (.mul (.add (.var "tk1") (.var "tqq")) (.add (.var "tqq") (.lit 1))))
  (.seq (powLoop "ts" "tk" "tE") (.assign "pc" (.lit 0))))))))))))

/-- The scalars that `exHdr` writes. -/
def hdrV : List String := ["tb0", "tk1", "tqq", "tL", "tl1", "ti2", "th0", "th1", "th2", "tE", "ts", "tk", "pc"]

theorem exHdr_wvars : ∀ y ∈ exHdr.wvars, y ∈ hdrV := by decide
theorem exHdr_warrs : exHdr.warrs = [] := by decide
theorem exHdr_reads : ¬ exHdr.reads := by decide
theorem exHdr_noWrite : exHdr.NoWrite := by decide

/-- The values that `exHdr` sets. -/
structure HdrAt (b k q ℓ R : ℕ) (τ : Env) : Prop where
  b0 : τ.vars "tb0" = b
  k1 : τ.vars "tk1" = k + 1
  qq : τ.vars "tqq" = q
  L : τ.vars "tL" = ℓ
  l1 : τ.vars "tl1" = ℓ + 1
  i2 : τ.vars "ti2" = ℓ
  h0 : τ.vars "th0" = k + 1
  h1 : τ.vars "th1" = q
  h2 : τ.vars "th2" = ℓ + 1
  s : τ.vars "ts" = R

/-- **The header of the item.** -/
theorem exHdr_run {W : ℕ} {ws : List (List ℕ)} {ow p g k q ℓ : ℕ} {t : Node (q + 1) ℓ} {τ : Env}
    (hw : WordsAt ws τ) (how : ow < ws.length) (hit : ws[ow] = itemW ((p, g), ⟨k, q + 1, ℓ, t⟩))
    (howv : τ.vars "ow" = ow) (hT : total ws + ws.length + 4 ≤ W) (hv : ∀ u ∈ ws[ow], u + 1 ≤ W)
    (hR : rhoPlus (k + 1) q ≤ W) (h9 : 9 < W) :
    ∃ τ', Run (W + 1) exHdr τ τ' (20 * rhoPlus (k + 1) q + 120) ∧
      HdrAt (off ws ow) k q ℓ (rhoPlus (k + 1) q) τ' ∧ τ'.vars "pc" = 0 ∧
      (∀ y, y ∉ hdrV → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  have hitw : ws[ow] = p :: g :: k :: (q + 1) :: ℓ :: toWord t := by rw [hit]; rfl
  have hl5 : 5 ≤ ws[ow].length := by rw [hitw]; simp
  have hoff := off_add_le how
  set b := off ws ow
  have e2 : (τ.arrs "a")[b + 2]? = some k := by rw [hw.a ow how 2 (by omega)]; simp [hitw]
  have e3 : (τ.arrs "a")[b + 3]? = some (q + 1) := by rw [hw.a ow how 3 (by omega)]; simp [hitw]
  have e4 : (τ.arrs "a")[b + 4]? = some ℓ := by rw [hw.a ow how 4 (by omega)]; simp [hitw]
  have bk : k + 1 ≤ W := hv k (by rw [hitw]; simp)
  have bq : q + 2 ≤ W := hv (q + 1) (by rw [hitw]; simp)
  have bl : ℓ + 1 ≤ W := hv ℓ (by rw [hitw]; simp)
  set E := (k + 1 + q) * (q + 1)
  have hE : rhoPlus (k + 1) q = 9 ^ E := rfl
  have hEl := le_pow_nine E
  -- the assignments, one environment after the other
  set τ1 := τ.setVar "tb0" b
  set τ2 := τ1.setVar "tk1" (k + 1)
  set τ3 := τ2.setVar "tqq" q
  set τ4 := τ3.setVar "tL" ℓ
  set τ5 := τ4.setVar "tl1" (ℓ + 1)
  set τ6 := τ5.setVar "ti2" ℓ
  set τ7 := τ6.setVar "th0" (k + 1)
  set τ8 := τ7.setVar "th1" q
  set τ9 := τ8.setVar "th2" (ℓ + 1)
  set τ10 := τ9.setVar "tE" E
  have ga : ∀ ρ : Env, ρ.vars "tb0" = b → ρ.arrs "a" = τ.arrs "a" → ∀ j v, (τ.arrs "a")[b + j]? = some v →
      v < W + 1 → j < 5 → (Expr.get "a" (.add (.var "tb0") (.lit j))).evalB (W + 1) ρ = some v :=
    fun ρ h1 h2 j v h hvB hj =>
      evalB_get (ev_add (ev_var h1 (by omega)) (evalB_lit (by omega)) (by omega)) (by rw [h2]; exact h) hvB
  have r1 : Run (W + 1) (.assign "tb0" (.get "st" (.var "ow"))) τ τ1 3 :=
    (Run.assign (evalB_get (ev_var howv (by omega)) (hw.st ow how) (by omega))).mono (by simp [Expr.size])
  have r2 : Run (W + 1) (.assign "tk1" (.add (.get "a" (.add (.var "tb0") (.lit 2))) (.lit 1))) τ1 τ2 7 :=
    (Run.assign (ev_add (ga τ1 (by simp [τ1]) (by simp [τ1]) 2 k e2 (by omega) (by omega))
      (evalB_lit (by omega)) (by omega))).mono (by simp [Expr.size])
  have r3 : Run (W + 1) (.assign "tqq" (.sub (.get "a" (.add (.var "tb0") (.lit 3))) (.lit 1))) τ2 τ3 7 :=
    (Run.assign (ev_sub (ga τ2 (by simp [τ2, τ1]) (by simp [τ2, τ1]) 3 (q + 1) e3 (by omega) (by omega))
      (evalB_lit (by omega)) (by omega))).mono (by simp [Expr.size])
  have r4 : Run (W + 1) (.assign "tL" (.get "a" (.add (.var "tb0") (.lit 4)))) τ3 τ4 5 :=
    (Run.assign (ga τ3 (by simp [τ3, τ2, τ1]) (by simp [τ3, τ2, τ1]) 4 ℓ e4 (by omega) (by omega))).mono
      (by simp [Expr.size])
  have r5 : Run (W + 1) (.assign "tl1" (.add (.var "tL") (.lit 1))) τ4 τ5 4 :=
    (Run.assign (ev_add (ev_var (by simp [τ4]) (by omega)) (evalB_lit (by omega)) (by omega))).mono
      (by simp [Expr.size])
  have r6 : Run (W + 1) (.assign "ti2" (.var "tL")) τ5 τ6 2 := Run.assign (ev_var (by simp [τ5, τ4]) (by omega))
  have r7 : Run (W + 1) (.assign "th0" (.var "tk1")) τ6 τ7 2 :=
    Run.assign (ev_var (by simp [τ6, τ5, τ4, τ3, τ2]) (by omega))
  have r8 : Run (W + 1) (.assign "th1" (.var "tqq")) τ7 τ8 2 :=
    Run.assign (ev_var (by simp [τ7, τ6, τ5, τ4, τ3]) (by omega))
  have r9 : Run (W + 1) (.assign "th2" (.var "tl1")) τ8 τ9 2 :=
    Run.assign (ev_var (by simp [τ8, τ7, τ6, τ5]) (by omega))
  have r10 : Run (W + 1) (.assign "tE" (.mul (.add (.var "tk1") (.var "tqq")) (.add (.var "tqq") (.lit 1))))
      τ9 τ10 8 := by
    have hq : q + 1 ≤ E := Nat.le_mul_of_pos_left _ (by omega)
    have hk : k + 1 + q ≤ E := Nat.le_mul_of_pos_right _ (by omega)
    have : E < W + 1 := by have := le_pow_nine E; rw [hE] at hR; omega
    refine (Run.assign (evalB_bin (ev_add (ev_var (by simp [τ9, τ8, τ7, τ6, τ5, τ4, τ3, τ2]) (by omega))
      (ev_var (by simp [τ9, τ8, τ7, τ6, τ5, τ4, τ3]) (by omega)) (by omega))
      (ev_add (ev_var (by simp [τ9, τ8, τ7, τ6, τ5, τ4, τ3]) (by omega)) (evalB_lit (by omega)) (by omega))
      (by simp only [Bop.apply]; omega))).mono (by simp [Expr.size])
  obtain ⟨τ11, r11, ⟨a11, f11⟩, s11, -⟩ := powLoop_run (B := W + 1) (x := "ts") (i := "tk") (n := "tE")
    (fun ρ => ρ.arrs = τ.arrs ∧ ∀ y, y ≠ "ts" → y ≠ "tk" → ρ.vars y = τ10.vars y) E
    (by rw [← hE]; omega) (by omega) (by omega) (by decide) (by decide) (by decide)
    (fun ρ v ⟨h1, h2⟩ => ⟨by simp [h1], fun y a b => by simp [a, h2 y a b]⟩)
    (fun ρ v ⟨h1, h2⟩ => ⟨by simp [h1], fun y a b => by simp [b, h2 y a b]⟩) τ10
    ⟨⟨by simp [τ10, τ9, τ8, τ7, τ6, τ5, τ4, τ3, τ2, τ1], fun _ _ _ => rfl⟩, by simp [τ10]⟩
  set τ12 := τ11.setVar "pc" 0
  have r12 : Run (W + 1) (.assign "pc" (.lit 0)) τ11 τ12 2 := Run.assign (evalB_lit (by omega))
  have hrun : Run (W + 1) exHdr τ τ12 (20 * rhoPlus (k + 1) q + 120) := by
    unfold exHdr
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7 (Run.seq r8
      (Run.seq r9 (Run.seq r10 (Run.seq r11 r12))))))))))).mono ?_
    rw [hE]; omega
  obtain ⟨fa, fo, fi⟩ := run_frame hrun exHdr_warrs exHdr_reads exHdr_noWrite
  have g11 : ∀ y, y ≠ "ts" → y ≠ "tk" → y ≠ "pc" → τ12.vars y = τ10.vars y := fun y a b c => by
    simp only [τ12, vars_setVar, c, if_false]; exact f11 y a b
  refine ⟨τ12, hrun, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, by simp [τ12],
    fun y hy => hrun.frame_var y (fun h => hy (exHdr_wvars y h)), fa, fo, fi⟩
  all_goals first
    | (rw [g11 _ (by decide) (by decide) (by decide)]; simp [τ10, τ9, τ8, τ7, τ6, τ5, τ4, τ3, τ2, τ1])
    | (simp only [τ12, vars_setVar, show ("ts" : String) ≠ "pc" by decide, if_false]; rw [s11, hE])

/-- Skip the atom list of the root, and find the list of extensions. -/
def exSkip : Com :=
  .seq (.assign "te" (.add (.var "tb0") (.lit 5))) (.seq (.assign "tne" (.get "a" (.var "te")))
    (.seq (frLoop .skip) (.seq (.assign "te" (.var "tf")) (.assign "tne" (.get "a" (.var "te"))))))

/-- The scalars that `exSkip` writes. -/
def skipV : List String := ["te", "tne", "tf", "tz"]

theorem exSkip_wvars : ∀ y ∈ exSkip.wvars, y ∈ skipV := by decide
theorem exSkip_warrs : exSkip.warrs = [] := by decide
theorem exSkip_reads : ¬ exSkip.reads := by decide
theorem exSkip_noWrite : exSkip.NoWrite := by decide

/-- **The list of extensions.** -/
theorem exSkip_run {W : ℕ} {X : List ℕ} {b : ℕ} {q ℓ : ℕ} {t : Node (q + 1) ℓ} {r : List ℕ} {τ : Env}
    (ha : τ.arrs "a" = X) (hd : X.drop (b + 5) = toWord t ++ r) (hb : τ.vars "tb0" = b)
    (hB : b + 5 + (toWord t).length + 2 < W + 1) (hv : ∀ v ∈ toWord t, v < W + 1) :
    ∃ τ', Run (W + 1) exSkip τ τ' (20 * (toWord t).length + 40) ∧
      τ'.vars "te" = b + 5 + (toWord (Node.atoms t).words).length ∧
      τ'.vars "tne" = (Node.exts t).words.length ∧
      X.drop (b + 5 + (toWord (Node.atoms t).words).length) = toWord (Node.exts t).words ++ r ∧
      (∀ y, y ∉ skipV → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  obtain ⟨hs1, -⟩ := nodeSplit hd
  set A := (Node.atoms t).words
  set E := (Node.exts t).words
  have hlt : (toWord t).length = (toWord A).length + (toWord E).length := by
    rw [toWord_node_succ]; simp [A, E]
  have hdE : X.drop (b + 5 + (toWord A).length) = toWord E ++ r := by
    rw [← List.drop_drop, hs1]; simp
  have hA0 : X[b + 5]? = some A.length := by
    have := getElem?_of_drop hs1 (i := 0) (by simp [toWord_words]); simpa [toWord_words] using this
  have hE0 : X[b + 5 + (toWord A).length]? = some E.length := by
    have := getElem?_of_drop hdE (i := 0) (by simp [toWord_words]); simpa [toWord_words] using this
  have hAl : A.length < (toWord A).length := by rw [toWord_words, List.length_cons, Words.length_frames]; omega
  have hEl : E.length < (toWord E).length := by rw [toWord_words, List.length_cons, Words.length_frames]; omega
  have hvA : ∀ v ∈ toWord A, v < W + 1 := fun v h => hv v (by rw [toWord_node_succ]; exact List.mem_append_left _ h)
  set τ1 := τ.setVar "te" (b + 5)
  set τ2 := τ1.setVar "tne" A.length
  have r1 : Run (W + 1) (.assign "te" (.add (.var "tb0") (.lit 5))) τ τ1 4 :=
    (Run.assign (ev_add (ev_var hb (by omega)) (evalB_lit (by omega)) (by omega))).mono (by simp [Expr.size])
  have r2 : Run (W + 1) (.assign "tne" (.get "a" (.var "te"))) τ1 τ2 3 :=
    (Run.assign (evalB_get (ev_var (v := b + 5) (by simp [τ1]) (by omega)) (by simp [τ1, ha, hA0])
      (by omega))).mono
      (by simp [Expr.size])
  obtain ⟨τ3, r3, I3, f3⟩ := frLoop_run (W := W) (body := .skip) (e := b + 5) (E := A) (X := X)
    (fun _ => 1) (fun _ ρ => ρ.arrs = τ.arrs ∧ ∀ y, y ∉ skipV → ρ.vars y = τ.vars y) (τ := τ2)
    (by simp [τ2, τ1, ha]) hs1 (by simp [τ2, τ1]) (by simp [τ2]) (by omega) hvA
    (fun _ ρ x ⟨h1, h2⟩ => ⟨by simp [h1], fun y hy => by
      have : y ≠ "tf" := by rintro rfl; simp [skipV] at hy
      simp [this, h2 y hy]⟩)
    (fun _ ρ x ⟨h1, h2⟩ => ⟨by simp [h1], fun y hy => by
      have : y ≠ "tz" := by rintro rfl; simp [skipV] at hy
      simp [this, h2 y hy]⟩)
    ⟨by simp [τ2, τ1], fun y hy => by
      simp only [skipV, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [τ2, τ1, hy.1, hy.2.1]⟩
    (fun z _ ρ hI hz _ ha' hn => ⟨ρ, Run.skip, hI, hz, rfl, ha', hn⟩)
  set τ4 := τ3.setVar "te" (b + 5 + (toWord A).length)
  set τ5 := τ4.setVar "tne" E.length
  have r4 : Run (W + 1) (.assign "te" (.var "tf")) τ3 τ4 2 := Run.assign (ev_var f3 (by omega))
  have r5 : Run (W + 1) (.assign "tne" (.get "a" (.var "te"))) τ4 τ5 3 :=
    (Run.assign (evalB_get (ev_var (v := b + 5 + (toWord A).length) (by simp [τ4]) (by omega))
      (by simp [τ4, I3.1, ha, hE0]) (by omega))).mono
      (by simp [Expr.size])
  have hrun : Run (W + 1) exSkip τ τ5 (20 * (toWord t).length + 40) := by
    unfold exSkip
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 r5)))).mono ?_
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
    omega
  obtain ⟨fa, fo, fi⟩ := run_frame hrun exSkip_warrs exSkip_reads exSkip_noWrite
  exact ⟨τ5, hrun, by simp [τ5, τ4], by simp [τ5], hdE, fun y hy => hrun.frame_var y
    (fun h => hy (exSkip_wvars y h)), fa, fo, fi⟩

end Lax185574Proofs.ResolveRam.Glue
