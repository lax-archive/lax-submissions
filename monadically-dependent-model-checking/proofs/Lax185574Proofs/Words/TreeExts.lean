import Lax185574Proofs.Words.TreeAtoms

/-!
The candidates for the extensions of a transformed node.

The command `exList` scans the list of extensions at `y`. For the frame
`i` it maps the guard with the hook command `grdCmd` and, unless the
extension is dropped, forms the word of the new guard followed by the
transformed child. The transformed children are already in the buffer `b`:
child `i` is node `cc = fc + i`, whose word starts at `bs[cc]` and has
length `bl[cc]`. The candidates are left in the arrays `a`, `st` and `ln`,
ready for `collect`.
-/

namespace Lax185574Proofs.Words

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding

/-- The hook `cmd` maps a guard as `gsub` does: from the guard `gi` and
the depth `dd` it computes the new guard `ng`, and `drp = 1` if the
extension is dropped. -/
def GrdOK (cmd : Com) (gsub : ℕ → ℕ → Option ℕ) (Dat : Env → Prop) (B Kg : ℕ) : Prop :=
  Spec B (fun τ => Dat τ ∧ τ.vars "gi" < B ∧ τ.vars "dd" < B) cmd (fun τ τ' =>
    τ'.vars "ng" = (gsub (τ.vars "dd") (τ.vars "gi")).getD 0 ∧ τ'.vars "ng" < B ∧
    τ'.vars "drp" = (if (gsub (τ.vars "dd") (τ.vars "gi")).isSome then 0 else 1)) Kg

/-- Copy one entry of the child word from the buffer. -/
def exCopy : Com :=
  .seq (.store "a" (.var "ap") (.get "b" (.add (.var "cs") (.var "ck"))))
    (.seq (.assign "ap" (.add (.var "ap") (.lit 1))) (.assign "ck" (.add (.var "ck") (.lit 1))))

/-- Copy the child word. -/
def exCopies : Com := .while (.lt (.var "ck") (.var "cl")) exCopy

/-- The child word `T` is in the buffer from `s` on. -/
def BufWord (T : List ℕ) (s : ℕ) (τ : Env) : Prop :=
  ∀ k (hk : k < T.length), (τ.arrs "b")[s + k]? = some T[k]

theorem exCopies_spec (B : ℕ) (T : List ℕ) (s a0 Alen : ℕ) (hT : ∀ v ∈ T, v < B)
    (hA : a0 + T.length ≤ Alen) (hAB : a0 + T.length < B) (hsB : s + T.length < B) :
    Spec B (fun τ => BufWord T s τ ∧ τ.vars "cs" = s ∧ τ.vars "cl" = T.length ∧ τ.vars "ck" = 0 ∧
        τ.vars "ap" = a0 ∧ (τ.arrs "a").length = Alen)
      exCopies
      (fun τ τ' => τ'.vars "ap" = a0 + T.length ∧ (τ'.arrs "a").length = Alen ∧
        (∀ i, (i < a0 ∨ a0 + T.length ≤ i) → (τ'.arrs "a")[i]? = (τ.arrs "a")[i]?) ∧
        ∀ k (hk : k < T.length), (τ'.arrs "a")[a0 + k]? = some T[k])
      (18 * T.length + 4) := by
  rintro τ ⟨hbw, hcs, hcl, hck, hap, hal⟩
  let I : Env → Prop := fun ρ => BufWord T s ρ ∧ ρ.vars "cs" = s ∧ ρ.vars "cl" = T.length ∧
    ρ.vars "ck" ≤ T.length ∧ ρ.vars "ap" = a0 + ρ.vars "ck" ∧ (ρ.arrs "a").length = Alen ∧
    (∀ i, (i < a0 ∨ a0 + ρ.vars "ck" ≤ i) → (ρ.arrs "a")[i]? = (τ.arrs "a")[i]?) ∧
    ∀ k (hk : k < ρ.vars "ck"), (ρ.arrs "a")[a0 + k]? = T[k]?
  have hbody : Spec B (fun ρ => I ρ ∧ ρ.vars "ck" < T.length) exCopy
      (fun ρ ρ' => I ρ' ∧ ρ'.vars "ck" = ρ.vars "ck" + 1) 14 := by
    rintro ρ ⟨⟨hbw, hcs, hcl, hle, hap, hal, hold, hnew⟩, hlt⟩
    obtain ⟨k, hkd⟩ : ∃ k, ρ.vars "ck" = k := ⟨_, rfl⟩
    rw [hkd] at hle hap hold hnew hlt
    have hget : (ρ.arrs "b")[s + k]? = some T[k] := hbw k hlt
    have hTk : T[k] < B := hT _ (List.getElem_mem hlt)
    set ρ' := ((ρ.setArr "a" (a0 + k) T[k]).setVar "ap" (a0 + k + 1)).setVar "ck" (k + 1) with hρ'
    refine ⟨ρ', ?_, ⟨?_, by simp [hρ', hcs], by simp [hρ', hcl], by simp [hρ']; omega,
      by simp [hρ']; omega, by simp [hρ', hal], ?_, ?_⟩, by simp [hρ', hkd]⟩
    · unfold exCopy
      refine (Run.seq (Run.store ?_ ?_ ?_) (Run.seq (Run.assign ?_) (Run.assign ?_))).mono (by simp)
      · simp [hap]; omega
      · simp only [evalB_get_iff, evalB_bin_iff, evalB_var_iff]
        exact ⟨s + k, ⟨s, k, ⟨hcs.symm, by omega⟩, ⟨hkd.symm, by omega⟩, rfl, by omega⟩, hget, hTk⟩
      · rw [hal]; omega
      · simp [hap]; omega
      · simp [hkd]; omega
    · intro k' hk'; simp only [hρ', arrs_setVar, arrs_setArr, show ("b" : String) = "a" ↔ False by decide,
        if_false]; exact hbw k' hk'
    · intro i hi
      simp only [hρ', arrs_setVar, arrs_setArr, if_true, vars_setVar,
        show ("ck" : String) = "ap" ↔ False by decide] at hi ⊢
      rw [List.getElem?_set_ne (by omega)]; exact hold i (by omega)
    · intro k' hk'
      simp only [hρ', arrs_setVar, arrs_setArr, if_true, vars_setVar] at hk' ⊢
      rcases Nat.lt_or_ge k' k with h | h
      · rw [List.getElem?_set_ne (by omega)]; exact hnew k' h
      · obtain rfl : k' = k := by omega
        rw [List.getElem?_set_self (by omega), List.getElem?_eq_getElem hlt]
  obtain ⟨τ', hr, ⟨-, -, hcl', hle', hap', hal', hold', hnew'⟩, hend⟩ :=
    (Spec.forRange (B := B) (c := exCopy) (P := fun ρ => ρ = τ) "ck" "cl" I T.length 14
      (18 * T.length + 4) (fun ρ hI => by have := hI.2.2.2.1; omega)
      (fun ρ hI => by rw [hI.2.2.1]; omega) (fun ρ hI => hI.2.2.1) (fun ρ hI => hI.2.2.2.1) hbody
      (fun ρ h => by
        subst h
        exact ⟨hbw, hcs, hcl, by omega, by simp [hap, hck], hal, fun i _ => rfl,
          fun k hk => by rw [hck] at hk; omega⟩)
      (fun ρ h => by subst h; omega)).run rfl
  rw [hend] at hap' hold' hnew'
  exact ⟨τ', hr, hap', hal', hold', fun k hk => by rw [hnew' k hk, List.getElem?_eq_getElem hk]⟩

/-- Map one extension and keep it unless it is dropped. -/
def exFrame (grdCmd : Com) : Com :=
  .seq (.assign "gi" (.get "x" (.add (.var "y") (.lit 1))))
    (.seq grdCmd
      (.seq (.ite (.eq (.var "drp") (.lit 0))
          (.seq (.store "st" (.var "m") (.var "ap")) (.seq (.store "a" (.var "ap") (.var "ng"))
            (.seq (.assign "ap" (.add (.var "ap") (.lit 1)))
              (.seq (.assign "cs" (.get "bs" (.var "cc"))) (.seq (.assign "cl" (.get "bl" (.var "cc")))
                (.seq (.assign "ck" (.lit 0)) (.seq exCopies
                  (.seq (.store "ln" (.var "m") (.add (.var "cl") (.lit 1)))
                    (.assign "m" (.add (.var "m") (.lit 1)))))))))))
          .skip)
        (.seq (.assign "y" (.add (.add (.var "y") (.get "x" (.var "y"))) (.lit 1)))
          (.seq (.assign "e2" (.add (.var "e2") (.lit 1)))
            (.assign "cc" (.add (.var "cc") (.lit 1)))))))

/-- The candidates from the first `j` extensions of the list at `e`, the
transformed child of extension `i` being `T i`. -/
def exCands (gsub : ℕ → ℕ → Option ℕ) (d : ℕ) (X : List ℕ) (e : ℕ) (T : ℕ → List ℕ) (j : ℕ) :
    List (List ℕ) :=
  (List.range j).filterMap fun i => (gsub d (xg X (frPos X e i + 1))).map fun g => g :: T i

theorem exCands_succ (gsub : ℕ → ℕ → Option ℕ) (d : ℕ) (X : List ℕ) (e : ℕ) (T : ℕ → List ℕ)
    (j : ℕ) : exCands gsub d X e T (j + 1) = exCands gsub d X e T j ++
      ((gsub d (xg X (frPos X e j + 1))).map fun g => g :: T j).toList := by
  simp only [exCands, List.range_succ, List.filterMap_append, List.filterMap_cons, List.filterMap_nil]
  cases gsub d (xg X (frPos X e j + 1)) <;> simp

theorem exCands_le (gsub : ℕ → ℕ → Option ℕ) (d : ℕ) (X : List ℕ) (e : ℕ) (T : ℕ → List ℕ)
    (hT : ∀ i < xg X e, (T i).length + 1 ≤ xg X (frPos X e i)) :
    ∀ j ≤ xg X e, (exCands gsub d X e T j).length + total (exCands gsub d X e T j) + e + 1 ≤
      frPos X e j
  | 0, _ => by simp [exCands, total, frPos, skipFr]
  | j + 1, hj => by
    have ih := exCands_le gsub d X e T hT j (by omega)
    rw [exCands_succ]
    have h3 : frPos X e (j + 1) = frPos X e j + 1 + xg X (frPos X e j) := skipFr_succ' _ _ _
    have := hT j (by omega)
    cases hm : gsub d (xg X (frPos X e j + 1)) with
    | none => simp; omega
    | some g => simp [total_append, total_singleton]; omega

/-- The children of the extensions and their words in the buffer. -/
structure ChildBuf (X : List ℕ) (e FC : ℕ) (T : ℕ → List ℕ) (Bnd : ℕ) (τ : Env) : Prop where
  ln : ∀ i < xg X e, (τ.arrs "bl").getD (FC + i) 0 = (T i).length
  wd : ∀ i < xg X e, BufWord (T i) ((τ.arrs "bs").getD (FC + i) 0) τ
  idx : FC + xg X e ≤ (τ.arrs "bs").length ∧ FC + xg X e ≤ (τ.arrs "bl").length
  lt : ∀ i < xg X e, (τ.arrs "bs").getD (FC + i) 0 + (T i).length < Bnd

/-- The invariant of the loop over the extensions of the list at `e`. -/
def ExLInv (X : List ℕ) (e d FC : ℕ) (gsub : ℕ → ℕ → Option ℕ) (Dat : Env → Prop)
    (T : ℕ → List ℕ) (B Alen Slen : ℕ) (τ : Env) : Prop :=
  τ.arrs "x" = X ∧ τ.vars "dd" = d ∧ Dat τ ∧ τ.vars "e1" = xg X e ∧ τ.vars "e2" ≤ xg X e ∧
    τ.vars "y" = frPos X e (τ.vars "e2") ∧ τ.vars "cc" = FC + τ.vars "e2" ∧
    τ.vars "m" = (exCands gsub d X e T (τ.vars "e2")).length ∧
    τ.vars "ap" = total (exCands gsub d X e T (τ.vars "e2")) ∧
    WordsAt (exCands gsub d X e T (τ.vars "e2")) τ ∧ ChildBuf X e FC T B τ ∧
    (τ.arrs "a").length = Alen ∧ (τ.arrs "st").length = Slen ∧ (τ.arrs "ln").length = Slen

theorem exFrame_spec (grdCmd : Com) (gsub : ℕ → ℕ → Option ℕ) (Dat : Env → Prop)
    (B Kg : ℕ) (hF : HookFrame grdCmd) (hG : GrdOK grdCmd gsub Dat B Kg) (hD : DatOK Dat)
    (X : List ℕ) (e d FC : ℕ) (T : ℕ → List ℕ) (Alen Slen : ℕ) (hLF : ListFacts X e)
    (hfr : ∀ i < xg X e, 1 ≤ xg X (frPos X e i))
    (hT : ∀ i < xg X e, (T i).length + 1 ≤ xg X (frPos X e i))
    (hTB : ∀ i < xg X e, ∀ v ∈ T i, v < B)
    (hX : ∀ v ∈ X, v < B) (hXB : 2 * X.length + 2 < B) (hdB : d < B) (hFB : FC + X.length < B)
    (hA : X.length ≤ Alen) (hS' : X.length < Slen) :
    Spec B (fun τ => ExLInv X e d FC gsub Dat T B Alen Slen τ ∧ τ.vars "e2" < xg X e) (exFrame grdCmd)
      (fun τ τ' => ExLInv X e d FC gsub Dat T B Alen Slen τ' ∧ τ'.vars "e2" = τ.vars "e2" + 1)
      (Kg + 18 * X.length + 80) := by
  rintro τ ⟨⟨hxa, hdd, hdat, he1, he2le, hy, hcc, hm, hap, hwa, hcb, halen, hstl, hlnl⟩, hlt⟩
  obtain ⟨j, hjdef⟩ : ∃ j, τ.vars "e2" = j := ⟨_, rfl⟩
  rw [hjdef] at he2le hy hm hap hwa hlt hcc
  have hEle := exCands_le gsub d X e T hT j he2le
  have hsucc := exCands_succ gsub d X e T j
  obtain ⟨E, hE⟩ : ∃ E, exCands gsub d X e T j = E := ⟨_, rfl⟩
  rw [hE] at hm hap hwa hEle hsucc
  have hs1' : frPos X e (j + 1) = frPos X e j + 1 + xg X (frPos X e j) := skipFr_succ' _ _ _
  have hfr1 := hfr j hlt
  have hTj := hT j hlt
  have hTjB := hTB j hlt
  obtain ⟨f, hf⟩ : ∃ f, frPos X e j = f := ⟨_, rfl⟩
  rw [hf] at hy hEle hs1' hsucc hfr1 hTj
  obtain ⟨L, hL⟩ : ∃ L, xg X f = L := ⟨_, rfl⟩
  rw [hL] at hs1' hfr1 hTj
  have hle1 := (hLF.frPos_le (j + 1) (by omega)).2
  have hend := hLF.end_le
  have hc1 := hLF.frPos_le (xg X e) le_rfl
  have hfX : f + 1 + L ≤ X.length := by omega
  have hLB : L < B := by rw [← hL]; exact xg_lt hX (by omega)
  set g0 := xg X (f + 1) with hg0
  have hg0B : g0 < B := xg_lt hX (by omega)
  have hxf : (X.getD f 0) = L := hL
  -- gi := x[y + 1]
  set τ1 := τ.setVar "gi" g0 with hτ1
  have hev1 : (Expr.get "x" (.add (.var "y") (.lit 1))).evalB B τ = some g0 := by
    simp only [evalB_get_iff, evalB_bin_iff, evalB_var_iff, evalB_lit_iff, hxa, hy]
    refine ⟨f + 1, ⟨f, 1, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩, ?_, hg0B⟩
    simp only [hg0, xg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show f + 1 < X.length by omega),
      Option.getD_some]
  have hdat1 : Dat τ1 := hD τ τ1 (by simp [hτ1]) (by simp [hτ1]) (by simp [hτ1]) (by simp [hτ1])
    (by simp [hτ1]) hdat
  have h1gi : τ1.vars "gi" = g0 := by simp [hτ1]
  have h1dd : τ1.vars "dd" = d := by simp [hτ1, hdd]
  obtain ⟨τ2, hr2, hng, hngB, hdrp⟩ := hG τ1 ⟨hdat1, by rw [h1gi]; exact hg0B, by rw [h1dd]; exact hdB⟩
  rw [h1gi, h1dd] at hng hdrp
  have hv2 : ∀ y, y ∉ hookVars → τ2.vars y = τ1.vars y := hF.var hr2
  have ha2 : ∀ a, τ2.arrs a = τ1.arrs a := hF.arr hr2
  have hdat2 : Dat τ2 := hD τ τ2 (by rw [hv2 "g1" (by decide)]; simp [hτ1])
    (by rw [hv2 "g2" (by decide)]; simp [hτ1]) (by rw [hv2 "g3" (by decide)]; simp [hτ1])
    (by rw [hv2 "g4" (by decide)]; simp [hτ1]) (by rw [ha2]; simp [hτ1]) hdat
  have hx2 : τ2.arrs "x" = X := by rw [ha2]; simp [hτ1, hxa]
  have hy2 : τ2.vars "y" = f := by rw [hv2 "y" (by decide)]; simp [hτ1, hy]
  have hdd2 : τ2.vars "dd" = d := by rw [hv2 "dd" (by decide)]; simp [hτ1, hdd]
  have he12 : τ2.vars "e1" = xg X e := by rw [hv2 "e1" (by decide)]; simp [hτ1, he1]
  have he22 : τ2.vars "e2" = j := by rw [hv2 "e2" (by decide)]; simp [hτ1, hjdef]
  have hcc2 : τ2.vars "cc" = FC + j := by rw [hv2 "cc" (by decide)]; simp [hτ1, hcc]
  have hm2 : τ2.vars "m" = E.length := by rw [hv2 "m" (by decide)]; simp [hτ1, hm]
  have hap2 : τ2.vars "ap" = total E := by rw [hv2 "ap" (by decide)]; simp [hτ1, hap]
  have hcb2 : ChildBuf X e FC T B τ2 := by
    obtain ⟨c1, c2, c3, c4⟩ := hcb
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi; rw [ha2]; simpa [hτ1] using c1 i hi
    · intro i hi k hk; rw [ha2, ha2]; simpa [hτ1] using c2 i hi k hk
    · rw [ha2, ha2]; simpa [hτ1] using c3
    · intro i hi; rw [ha2]; simpa [hτ1] using c4 i hi
  have hfin : ∀ τ7 : Env, ∀ K7, Run B (.ite (.eq (.var "drp") (.lit 0))
          (.seq (.store "st" (.var "m") (.var "ap")) (.seq (.store "a" (.var "ap") (.var "ng"))
            (.seq (.assign "ap" (.add (.var "ap") (.lit 1)))
              (.seq (.assign "cs" (.get "bs" (.var "cc"))) (.seq (.assign "cl" (.get "bl" (.var "cc")))
                (.seq (.assign "ck" (.lit 0)) (.seq exCopies
                  (.seq (.store "ln" (.var "m") (.add (.var "cl") (.lit 1)))
                    (.assign "m" (.add (.var "m") (.lit 1)))))))))))
          .skip) τ2 τ7 K7 → K7 ≤ 18 * X.length + 50 →
      τ7.arrs "x" = X → τ7.vars "dd" = d → Dat τ7 → τ7.vars "e1" = xg X e →
      τ7.vars "y" = f → τ7.vars "e2" = j → τ7.vars "cc" = FC + j →
      τ7.vars "m" = (exCands gsub d X e T (j + 1)).length →
      τ7.vars "ap" = total (exCands gsub d X e T (j + 1)) →
      WordsAt (exCands gsub d X e T (j + 1)) τ7 → ChildBuf X e FC T B τ7 →
      (τ7.arrs "a").length = Alen → (τ7.arrs "st").length = Slen → (τ7.arrs "ln").length = Slen →
      ∃ τ', Run B (exFrame grdCmd) τ τ' (Kg + 18 * X.length + 80) ∧
        ExLInv X e d FC gsub Dat T B Alen Slen τ' ∧ τ'.vars "e2" = τ.vars "e2" + 1 := by
    intro τ7 K7 hr7 hK7 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14
    set τ10 := ((τ7.setVar "y" (f + L + 1)).setVar "e2" (j + 1)).setVar "cc" (FC + j + 1) with hτ10
    refine ⟨τ10, ?_, ?_, by simp [hτ10, hjdef]⟩
    · unfold exFrame
      refine (Run.seq (Run.assign hev1) (Run.seq hr2 (Run.seq hr7 (Run.seq (Run.assign ?_)
        (Run.seq (Run.assign (v := j + 1) ?_) (Run.assign (v := FC + j + 1) ?_)))))).mono ?_
      · simp only [evalB_bin_iff, evalB_get_iff, evalB_var_iff, evalB_lit_iff, h1, h5]
        refine ⟨f + L, 1, ⟨f, L, ⟨rfl, by omega⟩, ⟨f, ⟨rfl, by omega⟩, ?_, hLB⟩, rfl, by omega⟩,
          ⟨rfl, by omega⟩, rfl, by omega⟩
        rw [← hL]; simp only [xg, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem (show f < X.length by omega), Option.getD_some]
      · simp [h6]; exact ⟨by omega, by omega, by omega⟩
      · simp [h7]; omega
      · simp only [Expr.size]; omega
    · obtain ⟨c1, c2, c3, c4⟩ := h11
      refine ⟨by simp [hτ10, h1], by simp [hτ10, h2], hD τ7 τ10 (by simp [hτ10]) (by simp [hτ10])
        (by simp [hτ10]) (by simp [hτ10]) (by simp [hτ10]) h3, by simp [hτ10, h4], by simp [hτ10]; omega,
        by simp [hτ10, hs1']; omega, by simp [hτ10]; omega, by simp [hτ10, h8], by simp [hτ10, h9], ?_,
        ⟨fun i hi => by simpa [hτ10] using c1 i hi, fun i hi k hk => by simpa [hτ10] using c2 i hi k hk,
          by simpa [hτ10] using c3, fun i hi => by simpa [hτ10] using c4 i hi⟩, by simp [hτ10, h12],
        by simp [hτ10, h13], by simp [hτ10, h14]⟩
      simp only [hτ10, vars_setVar, if_true, show ("e2" : String) = "cc" ↔ False by decide, if_false]
      exact h10.of_arrs (by simp) (by simp) (by simp)
  have hwa2 : WordsAt E τ2 := hwa.of_arrs (by rw [ha2]; simp [hτ1]) (by rw [ha2]; simp [hτ1])
    (by rw [ha2]; simp [hτ1])
  have hal2 : (τ2.arrs "a").length = Alen := by rw [ha2]; simp [hτ1, halen]
  have hstl2 : (τ2.arrs "st").length = Slen := by rw [ha2]; simp [hτ1, hstl]
  have hlnl2 : (τ2.arrs "ln").length = Slen := by rw [ha2]; simp [hτ1, hlnl]
  cases hgs : gsub d g0 with
  | none =>
    have hdrp1 : τ2.vars "drp" = 1 := by rw [hdrp, hgs]; rfl
    rw [hgs] at hsucc
    simp only [Option.map_none, Option.toList_none, List.append_nil] at hsucc
    refine hfin τ2 5 ((Run.ite_false ?_ Run.skip).mono (by simp)) (by omega) hx2 hdd2 hdat2 he12 hy2
      he22 hcc2 (by rw [hsucc, hm2]) (by rw [hsucc, hap2]) (by rw [hsucc]; exact hwa2) hcb2 hal2
      hstl2 hlnl2
    simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff]
    exact ⟨1, 0, ⟨hdrp1.symm, by omega⟩, ⟨rfl, by omega⟩, by simp⟩
  | some g =>
    have hdrp0 : τ2.vars "drp" = 0 := by rw [hdrp, hgs]; rfl
    have hng' : τ2.vars "ng" = g := by rw [hng, hgs]; rfl
    rw [hgs] at hsucc
    simp only [Option.map_some, Option.toList_some] at hsucc
    obtain ⟨c1, c2, c3, c4⟩ := hcb2
    set S := (τ2.arrs "bs").getD (FC + j) 0 with hS
    have hSB : S + (T j).length < B := c4 j hlt
    have hbl : (τ2.arrs "bl").getD (FC + j) 0 = (T j).length := c1 j hlt
    have hst2 : τ2.arrs "st" = τ.arrs "st" := by rw [ha2]; simp [hτ1]
    have hln2 : τ2.arrs "ln" = τ.arrs "ln" := by rw [ha2]; simp [hτ1]
    have haa2 : τ2.arrs "a" = τ.arrs "a" := by rw [ha2]; simp [hτ1]
    set τ8 := (((((τ2.setArr "st" E.length (total E)).setArr "a" (total E) g).setVar "ap"
      (total E + 1)).setVar "cs" S).setVar "cl" (T j).length).setVar "ck" 0 with hτ8
    obtain ⟨τ9, hr9, hap9, hal9, hold9, hnew9⟩ := exCopies_spec B (T j) S (total E + 1) Alen hTjB
      (by omega) (by omega) hSB τ8 ⟨fun k hk => by rw [show τ8.arrs "b" = τ2.arrs "b" by simp [hτ8]]; exact c2 j hlt k hk, by simp [hτ8],
        by simp [hτ8], by simp [hτ8], by simp [hτ8], by simp [hτ8, haa2, halen]⟩
    have hv9 : ∀ y, y ∉ exCopies.wvars → τ9.vars y = τ8.vars y := fun y h => hr9.frame_var y h
    have ha9 : ∀ b, b ∉ exCopies.warrs → τ9.arrs b = τ8.arrs b := fun b h => hr9.frame_arr b h
    set τ11 := (τ9.setArr "ln" E.length ((T j).length + 1)).setVar "m" (E.length + 1) with hτ11
    have hr11 : Run B (.ite (.eq (.var "drp") (.lit 0))
          (.seq (.store "st" (.var "m") (.var "ap")) (.seq (.store "a" (.var "ap") (.var "ng"))
            (.seq (.assign "ap" (.add (.var "ap") (.lit 1)))
              (.seq (.assign "cs" (.get "bs" (.var "cc"))) (.seq (.assign "cl" (.get "bl" (.var "cc")))
                (.seq (.assign "ck" (.lit 0)) (.seq exCopies
                  (.seq (.store "ln" (.var "m") (.add (.var "cl") (.lit 1)))
                    (.assign "m" (.add (.var "m") (.lit 1)))))))))))
          .skip) τ2 τ11 (18 * (T j).length + 40) := by
      have hbs : (τ2.arrs "bs")[FC + j]? = some S := by
        rw [hS, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
      have hbl' : (τ2.arrs "bl")[FC + j]? = some (T j).length := by
        rw [← hbl, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]; rfl
      have hcl9 : τ9.vars "cl" = (T j).length := by rw [hv9 "cl" (by decide)]; simp [hτ8]
      have hm9 : τ9.vars "m" = E.length := by rw [hv9 "m" (by decide)]; simp [hτ8, hm2]
      have hln9 : (τ9.arrs "ln").length = Slen := by rw [ha9 "ln" (by decide)]; simp [hτ8, hlnl2]
      refine (Run.ite_true ?_ (Run.seq (Run.store ?_ ?_ ?_) (Run.seq (Run.store ?_ ?_ ?_)
        (Run.seq (Run.assign ?_) (Run.seq (Run.assign ?_) (Run.seq (Run.assign ?_)
          (Run.seq (Run.assign ?_) (Run.seq hr9 (Run.seq (Run.store ?_ ?_ ?_)
            (Run.assign ?_)))))))))).mono ?_
      · simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff]
        exact ⟨0, 0, ⟨hdrp0.symm, by omega⟩, ⟨rfl, by omega⟩, by simp⟩
      · simp [hm2]; omega
      · simp [hap2]; omega
      · rw [hstl2]; omega
      · simp [hap2]; omega
      · simp [hng']; omega
      · simp [hal2]; omega
      · simp [hap2]; omega
      · simp only [evalB_get_iff, evalB_var_iff, vars_setVar, arrs_setVar, arrs_setArr]
        refine ⟨FC + j, ⟨by simp [hcc2], by simp [hcc2]; omega⟩, by simpa using hbs, by omega⟩
      · simp only [evalB_get_iff, evalB_var_iff, vars_setVar, arrs_setVar, arrs_setArr]
        refine ⟨FC + j, ⟨by simp [hcc2], by simp [hcc2]; omega⟩, by simpa using hbl', by omega⟩
      · simp; omega
      · simp [hm9]; omega
      · simp [hcl9]; omega
      · rw [hln9]; omega
      · simp [hm9]; omega
      · simp only [Cond.size, Expr.size]; omega
    have hhold : ∀ i, i < total E + 1 → (τ9.arrs "a")[i]? = ((τ.arrs "a").set (total E) g)[i]? := by
      intro i hi
      rw [hold9 i (Or.inl hi)]; simp [hτ8, haa2]
    have hw11 : WordsAt (E ++ [g :: T j]) τ11 := by
      have h0 : WordsAt E τ11 := by
        refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi k hk => ?_⟩
        · simp only [hτ11, arrs_setVar, arrs_setArr, show ("st" : String) = "ln" ↔ False by decide,
            if_false]
          rw [ha9 "st" (by decide)]
          simp only [hτ8, arrs_setVar, arrs_setArr, if_true, show ("st" : String) = "a" ↔ False by decide,
            if_false]
          rw [List.getElem?_set_ne (by omega), hst2]; exact hwa.st i hi
        · simp only [hτ11, arrs_setVar, arrs_setArr, if_true]
          rw [List.getElem?_set_ne (by omega), ha9 "ln" (by decide)]
          simp only [hτ8, arrs_setVar, arrs_setArr, show ("ln" : String) = "a" ↔ False by decide,
            show ("ln" : String) = "st" ↔ False by decide, if_false, hln2]
          exact hwa.ln i hi
        · have := off_add_le hi
          simp only [hτ11, arrs_setVar, arrs_setArr, show ("a" : String) = "ln" ↔ False by decide,
            if_false]
          rw [hhold _ (by omega), List.getElem?_set_ne (by omega)]
          exact hwa.a i hi k hk
      refine h0.snoc ?_ ?_ ?_
      · simp only [hτ11, arrs_setVar, arrs_setArr, show ("st" : String) = "ln" ↔ False by decide,
          if_false]
        rw [ha9 "st" (by decide)]
        simp only [hτ8, arrs_setVar, arrs_setArr, if_true, show ("st" : String) = "a" ↔ False by decide,
          if_false]
        rw [List.getElem?_set_self (by rw [hst2, hstl]; omega)]
      · simp only [hτ11, arrs_setVar, arrs_setArr, if_true]
        rw [List.getElem?_set_self (by rw [ha9 "ln" (by decide)]; simp [hτ8]; omega)]; simp
      · intro k hk
        simp only [hτ11, arrs_setVar, arrs_setArr, show ("a" : String) = "ln" ↔ False by decide,
          if_false]
        cases k with
        | zero =>
          rw [Nat.add_zero, hhold _ (by omega), List.getElem?_set_self (by rw [halen]; omega)]; rfl
        | succ k =>
          simp only [List.getElem_cons_succ]
          rw [show total E + (k + 1) = total E + 1 + k by omega]
          exact hnew9 k (by simp at hk; omega)
    have hv11 : ∀ y, y ∉ ["ap", "ck", "m", "cs", "cl"] → τ11.vars y = τ2.vars y := by
      intro y hy
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp only [hτ11, vars_setVar, vars_setArr, if_neg hy.2.2.1]
      rw [hv9 y (by simp [exCopies, exCopy, Com.wvars]; exact ⟨hy.1, hy.2.1⟩)]
      simp [hτ8, hy.1, hy.2.1, hy.2.2.2.1, hy.2.2.2.2]
    have ha11 : ∀ b, b ≠ "a" → b ≠ "ln" → b ≠ "st" → τ11.arrs b = τ2.arrs b := by
      intro b h1 h2 h3
      simp only [hτ11, arrs_setVar, arrs_setArr, if_neg h2]
      rw [ha9 b (by simp [exCopies, exCopy, Com.warrs]; exact h1)]
      simp [hτ8, h1, h3]
    refine hfin τ11 _ hr11 (by omega) (by rw [ha11 "x" (by decide) (by decide) (by decide), hx2])
      (by rw [hv11 "dd" (by decide), hdd2])
      (hD τ2 τ11 (hv11 "g1" (by decide)) (hv11 "g2" (by decide)) (hv11 "g3" (by decide))
        (hv11 "g4" (by decide)) (ha11 "gt" (by decide) (by decide) (by decide)) hdat2)
      (by rw [hv11 "e1" (by decide), he12]) (by rw [hv11 "y" (by decide), hy2])
      (by rw [hv11 "e2" (by decide), he22]) (by rw [hv11 "cc" (by decide), hcc2])
      (by rw [hsucc]; simp [hτ11]) (by rw [hsucc, total_append, total_singleton]; simp [hτ11, hap9]; omega)
      (by rw [hsucc]; exact hw11) ?_ (by simp [hτ11, hal9])
      (by simp [hτ11]; rw [ha9 "st" (by decide)]; simp [hτ8, hstl2])
      (by simp [hτ11]; rw [ha9 "ln" (by decide)]; simp [hτ8, hlnl2])
    refine ⟨fun i hi => ?_, fun i hi k hk => ?_, ?_, fun i hi => ?_⟩
    · rw [ha11 "bl" (by decide) (by decide) (by decide)]; exact c1 i hi
    · rw [ha11 "bs" (by decide) (by decide) (by decide), ha11 "b" (by decide) (by decide) (by decide)]
      exact c2 i hi k hk
    · rw [ha11 "bs" (by decide) (by decide) (by decide), ha11 "bl" (by decide) (by decide) (by decide)]
      exact c3
    · rw [ha11 "bs" (by decide) (by decide) (by decide)]; exact c4 i hi

/-- The candidates for the extensions of the node whose list of extensions
is at `y`. -/
def exList (grdCmd : Com) : Com :=
  .seq (.assign "e1" (.get "x" (.var "y"))) (.seq (.assign "y" (.add (.var "y") (.lit 1)))
    (.seq (.assign "e2" (.lit 0)) (.seq (.assign "m" (.lit 0)) (.seq (.assign "ap" (.lit 0))
      (.seq (.assign "cc" (.get "fc" (.var "u")))
        (.while (.lt (.var "e2") (.var "e1")) (exFrame grdCmd)))))))

/-- **The extension candidates.** -/
theorem exList_spec (grdCmd : Com) (gsub : ℕ → ℕ → Option ℕ) (Dat : Env → Prop)
    (B Kg : ℕ) (hF : HookFrame grdCmd) (hG : GrdOK grdCmd gsub Dat B Kg) (hD : DatOK Dat)
    (X : List ℕ) (e d FC : ℕ) (T : ℕ → List ℕ) (Alen Slen : ℕ) (hLF : ListFacts X e)
    (hfr : ∀ i < xg X e, 1 ≤ xg X (frPos X e i))
    (hT : ∀ i < xg X e, (T i).length + 1 ≤ xg X (frPos X e i))
    (hTB : ∀ i < xg X e, ∀ v ∈ T i, v < B)
    (hX : ∀ v ∈ X, v < B) (hXB : 2 * X.length + 2 < B) (hdB : d < B) (hFB : FC + X.length < B)
    (hA : X.length ≤ Alen) (hS' : X.length < Slen) :
    Spec B (fun τ => τ.arrs "x" = X ∧ τ.vars "y" = e ∧ τ.vars "dd" = d ∧ Dat τ ∧
        τ.vars "u" < (τ.arrs "fc").length ∧ τ.vars "u" < B ∧ (τ.arrs "fc").getD (τ.vars "u") 0 = FC ∧
        ChildBuf X e FC T B τ ∧
        (τ.arrs "a").length = Alen ∧ (τ.arrs "st").length = Slen ∧ (τ.arrs "ln").length = Slen)
      (exList grdCmd)
      (fun _ τ' => τ'.arrs "x" = X ∧ τ'.vars "y" = listEnd X e ∧ τ'.vars "dd" = d ∧ Dat τ' ∧
        τ'.vars "m" = (exCands gsub d X e T (xg X e)).length ∧
        WordsAt (exCands gsub d X e T (xg X e)) τ' ∧ ChildBuf X e FC T B τ' ∧
        (τ'.arrs "a").length = Alen ∧ (τ'.arrs "st").length = Slen ∧ (τ'.arrs "ln").length = Slen)
      ((Kg + 18 * X.length + 84) * X.length + 40) := by
  rintro τ ⟨hxa, hy, hdd, hdat, hul, huB, hfc, hcb, hal, hstl, hlnl⟩
  have hc1 := hLF.frPos_le (xg X e) le_rfl
  have hend := hLF.end_le
  have hcB : xg X e < B := xg_lt hX (by omega)
  set τ0 := (((((τ.setVar "e1" (xg X e)).setVar "y" (e + 1)).setVar "e2" 0).setVar "m" 0).setVar
    "ap" 0).setVar "cc" FC with hτ0
  have hI0 : ExLInv X e d FC gsub Dat T B Alen Slen τ0 := by
    obtain ⟨c1, c2, c3, c4⟩ := hcb
    refine ⟨by simp [hτ0, hxa], by simp [hτ0, hdd],
      hD τ τ0 (by simp [hτ0]) (by simp [hτ0]) (by simp [hτ0]) (by simp [hτ0]) (by simp [hτ0]) hdat,
      by simp [hτ0], by simp [hτ0], by simp [hτ0, frPos, skipFr], by simp [hτ0],
      by simp [hτ0, exCands], by simp [hτ0, exCands, total], ?_,
      ⟨fun i hi => by simpa [hτ0] using c1 i hi, fun i hi k hk => by simpa [hτ0] using c2 i hi k hk,
        by simpa [hτ0] using c3, fun i hi => by simpa [hτ0] using c4 i hi⟩, by simp [hτ0, hal],
      by simp [hτ0, hstl], by simp [hτ0, hlnl]⟩
    have h0 : τ0.vars "e2" = 0 := by simp [hτ0]
    rw [h0]
    exact ⟨fun i hi => by simp [exCands] at hi, fun i hi => by simp [exCands] at hi,
      fun i hi => by simp [exCands] at hi⟩
  have hbody : Spec B (fun ρ => ExLInv X e d FC gsub Dat T B Alen Slen ρ ∧
      (Cond.lt (.var "e2") (.var "e1")).evalB B ρ = some true) (exFrame grdCmd)
      (fun ρ ρ' => ExLInv X e d FC gsub Dat T B Alen Slen ρ' ∧
        xg X e - ρ'.vars "e2" < xg X e - ρ.vars "e2")
      (Kg + 18 * X.length + 80) :=
    (exFrame_spec grdCmd gsub Dat B Kg hF hG hD X e d FC T Alen Slen hLF hfr hT hTB hX hXB hdB hFB
      hA hS').conseq
      (fun ρ ⟨hI, hc⟩ => ⟨hI, by have := lt_of_condLt_true hc; rwa [hI.2.2.2.1] at this⟩)
      (fun ρ ρ' ⟨hI, hc⟩ ⟨hI', he⟩ => ⟨hI', by
        have := lt_of_condLt_true hc; rw [hI.2.2.2.1] at this; omega⟩) le_rfl
  have hK : ∀ ρ, ρ = τ0 → (1 + (Cond.lt (.var "e2") (.var "e1")).size + (Kg + 18 * X.length + 80)) *
      (xg X e - ρ.vars "e2") + 1 + (Cond.lt (.var "e2") (.var "e1")).size ≤
      (Kg + 18 * X.length + 84) * X.length + 4 := by
    intro ρ h; subst h
    have h0 : τ0.vars "e2" = 0 := by simp [hτ0]
    simp only [h0, Cond.size, Expr.size, Nat.sub_zero]
    have h2 : 1 + (1 + 1 + 1) + (Kg + 18 * X.length + 80) = Kg + 18 * X.length + 84 := by ring
    rw [h2]
    have := Nat.mul_le_mul_left (Kg + 18 * X.length + 84) (show xg X e ≤ X.length by omega)
    omega
  obtain ⟨τ', hr, hI', hfalse⟩ := (Spec.while_count (B := B) (P := fun ρ => ρ = τ0)
    (b := .lt (.var "e2") (.var "e1")) (c := exFrame grdCmd)
    (K := (Kg + 18 * X.length + 84) * X.length + 4)
    (ExLInv X e d FC gsub Dat T B Alen Slen) (fun ρ => xg X e - ρ.vars "e2") (Kg + 18 * X.length + 80)
    (fun ρ hI => evalB_condLt_vars (by have := hI.2.2.2.2.1; omega) (by rw [hI.2.2.2.1]; omega))
    hbody (fun ρ h => h ▸ hI0) hK).run rfl
  obtain ⟨hx', hdd', hdat', he1', he2', hy', -, hm', -, hw', hcb', hal', hst', hln'⟩ := hI'
  have hend' : τ'.vars "e2" = xg X e := by
    have := le_of_condLt_false hfalse; rw [he1'] at this; omega
  rw [hend'] at hm' hw'
  refine ⟨τ', ?_, hx', by rw [hy', hend']; rfl, hdd', hdat', hm', hw', hcb', hal', hst', hln'⟩
  unfold exList
  refine (Run.seq (Run.assign (v := xg X e) ?_) (Run.seq (Run.assign (v := e + 1) ?_)
    (Run.seq (Run.assign (v := 0) ?_) (Run.seq (Run.assign (v := 0) ?_)
      (Run.seq (Run.assign (v := 0) ?_) (Run.seq (Run.assign (v := FC) ?_) hr)))))).mono ?_
  · simp only [evalB_get_iff, evalB_var_iff, hxa, hy]
    refine ⟨e, ⟨rfl, by omega⟩, ?_, hcB⟩
    simp only [xg, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show e < X.length by omega),
      Option.getD_some]
  · simp [hy]; omega
  · simp; omega
  · simp; omega
  · simp; omega
  · simp only [evalB_get_iff, evalB_var_iff, vars_setVar, arrs_setVar]
    refine ⟨τ.vars "u", ⟨by simp, by simp; exact huB⟩, ?_, by omega⟩
    rw [← hfc, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hul]; rfl
  · simp only [Expr.size]; omega

end Lax185574Proofs.Words
