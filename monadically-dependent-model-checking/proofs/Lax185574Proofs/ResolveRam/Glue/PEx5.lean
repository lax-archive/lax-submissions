import Lax185574Proofs.ResolveRam.Glue.PEx4

/-!
The second part of the expansion of lem:resolve-lift: the guards of the
old extensions.

For every extension word `ew = g :: toWord c` of the root, `part2` runs
the guard loop `gLoop` on the child word `childW k q ℓ ew`, whose atom
list is that of `c`, two entries after the frame of `ew` (`part2_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.EvalRam Lax185574Proofs.FarRam
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo

/-- The guards of one old extension. -/
def p2Body : Com :=
  .seq (.assign "tsS" (.add (.var "tf") (.lit 2))) (.seq (.assign "tsN" (.sub (.get "a" (.var "tf")) (.lit 1)))
    (.seq (.assign "tp1" (.add (.var "tf") (.lit 2))) (.seq (.assign "tp2" (.add (.var "tf") (.lit 2))) gLoop)))

/-- The guards of the old extensions. -/
def part2 : Com := frLoop p2Body

/-- The scalars that `part2` writes. -/
def p2V : List String := ["tsS", "tsN", "tp1", "tp2", "tf", "tz"] ++ gLV

/-- The words of the guards of an old extension. -/
def oldG (Dw : DW) (R i k q ℓ : ℕ) (ew : List ℕ) : List (List ℕ) :=
  (guardW Dw R ℓ (listWords (childW k q ℓ ew) 3) (childW k q ℓ ew)).map (i :: ·)

theorem childW_tree (k q ℓ g : ℕ) (c : Node q (ℓ + 1)) :
    childW k q ℓ (g :: toWord c) = toWord (⟨k + 1, q, ℓ + 1, c⟩ : TypeTree) := by
  rw [toWord_typeTree]; rfl

theorem exHopK_mono {L L' R : ℕ} (h : L ≤ L') : hopK L R ≤ hopK L' R := by
  unfold hopK; exact Nat.mul_le_mul_left _ (by omega)

theorem flatMap_take_succ {E : List (List ℕ)} {z : ℕ} (hz : z < E.length) (f : List ℕ → List (List ℕ)) :
    (E.take (z + 1)).flatMap f = (E.take z).flatMap f ++ f E[z] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hz, Option.toList_some, List.flatMap_append]
  simp

theorem length_guardW_le (Dw : DW) (R ℓ : ℕ) (A : List (List ℕ)) (cw : List ℕ) :
    (guardW Dw R ℓ A cw).length ≤ ℓ := by
  unfold guardW
  exact le_trans (List.length_filterMap_le _ _) (by simp)

theorem length_frames_oldG (Dw : DW) (R ℓ i : ℕ) (A : List (List ℕ)) (cw : List ℕ) :
    (frames ((guardW Dw R ℓ A cw).map (i :: ·))).length = (guardW Dw R ℓ A cw).length * (cw.length + 3) := by
  rw [← gWords_full]
  have := (length_frames_gWords Dw R ℓ A cw i ℓ).1
  rw [this, gWords_full, List.length_map]

/-- **The guards of the old extensions.** -/
theorem part2_run {W : ℕ} {X : List ℕ} {e : ℕ} {E : List (List ℕ)} {r : List ℕ} {pre : List ℕ}
    {Dw : DW} {R i k q ℓ c₀ : ℕ} {τ : Env}
    (ha : τ.arrs "a" = X) (hd : X.drop e = toWord E ++ r) (hte : τ.vars "te" = e)
    (hne : τ.vars "tne" = E.length)
    (hE : ∀ ew ∈ E, ∃ (g : ℕ) (c : Node q (ℓ + 1)), ew = g :: toWord c) (hi : τ.vars "ii" = i)
    (h0 : τ.vars "th0" = k + 1) (h1 : τ.vars "th1" = q) (h2 : τ.vars "th2" = ℓ + 1)
    (hP : τ.vars "tP" = Dw.P) (hQ : τ.vars "tQ" = Dw.Q) (hcP : τ.vars "tcP" = bv Dw.cP)
    (hcQ : τ.vars "tcQ" = bv Dw.cQ) (hi2 : τ.vars "ti2" = ℓ) (hs : τ.vars "ts" = R) (hL : τ.vars "tL" = ℓ)
    (hF : Filled "OB" "po" pre τ) (hpc : τ.vars "pc" = c₀) (hOB : (τ.arrs "OB").length = W + 1)
    (hal : (τ.arrs "a").length = W + 1)
    (hB : e + (toWord E).length + 8 < W + 1) (hv : ∀ v ∈ toWord E, v < W + 1)
    (hcap : pre.length + ℓ * (5 * (toWord E).length) ≤ W) (hik : i ≤ W ∧ k + 1 ≤ W ∧ q ≤ W ∧ ℓ + 1 ≤ W)
    (hc : c₀ + ℓ * (E.length + 1) + 1 ≤ W) (hPB : Dw.P < W + 1) (hQB : Dw.Q < W + 1)
    (hR : 2 * R + 4 < W + 1) :
    ∃ τ', Run (W + 1) part2 τ τ' (E.length * (ℓ * (hopK (2 * (toWord E).length) R + 20 * (toWord E).length +
        100) + 50) + 10) ∧
      Filled "OB" "po" (pre ++ frames (E.flatMap (oldG Dw R i k q ℓ))) τ' ∧
      τ'.vars "pc" = c₀ + (E.flatMap (oldG Dw R i k q ℓ)).length ∧ OFr τ τ' p2V := by
  set L := (toWord E).length
  have hL3 : (frames E).length + 1 = L := by simp only [L]; rw [toWord_words]; simp
  have hEl : E.length < L := by rw [← hL3, Words.length_frames]; omega
  set G := oldG Dw R i k q ℓ
  let I : ℕ → Env → Prop := fun z ρ =>
    Filled "OB" "po" (pre ++ frames ((E.take z).flatMap G)) ρ ∧
    ρ.vars "pc" = c₀ + ((E.take z).flatMap G).length ∧ ((E.take z).flatMap G).length ≤ ℓ * z ∧
    (frames ((E.take z).flatMap G)).length ≤ ℓ * ((frames (E.take z)).length + 4 * z) ∧ OFr τ ρ p2V
  have kP : ∀ y ∈ ["ii", "th0", "th1", "th2", "tP", "tQ", "tcP", "tcQ", "ti2", "ts", "tL"], y ∉ p2V := by decide
  obtain ⟨τ', r', ⟨F', c', -, -, o'⟩, -⟩ := frLoop_run (W := W) (body := p2Body) (X := X)
    (fun _ => ℓ * (hopK (2 * L) R + 20 * L + 100) + 34) I ha hd hte hne (by omega) hv
    (fun z ρ x ⟨h1, h2, h3, h4, h5⟩ => ⟨h1.setVar (by decide) _, by simp [h2], h3, h4,
      (h5.trans (OFr.setVar ρ "tf" x)).mono (by decide)⟩)
    (fun z ρ x ⟨h1, h2, h3, h4, h5⟩ => ⟨h1.setVar (by decide) _, by simp [h2], h3, h4,
      (h5.trans (OFr.setVar ρ "tz" x)).mono (by decide)⟩)
    ⟨by simpa [frames] using hF, by simp [hpc], by simp, by simp [frames], OFr.refl τ |>.mono (by simp)⟩
    (by
      rintro z hz ρ ⟨Fρ, cρ, nρ, fρ, oρ⟩ hzρ hfρ haρ hnρ
      have hds := frame_seg hd hz
      set f := e + 1 + (frames (E.take z)).length
      obtain ⟨g', c, hew⟩ := hE E[z] (List.getElem_mem hz)
      have hd2 : X.drop (f + 2) = toWord c ++ (frames (E.drop (z + 1)) ++ r) := by
        rw [show X.drop (f + 2) = (X.drop f).drop 2 by rw [List.drop_drop], hds, hew]; simp
      obtain ⟨r'', hd3⟩ := atoms_drop hd2
      set A := (Node.atoms c).words
      have hA : listWords (childW k q ℓ E[z]) 3 = A := by rw [hew, childW_tree, listWords_tree_root]
      have hcwd : childW k q ℓ E[z] = [k + 1, q, ℓ + 1] ++ E[z].tail := rfl
      have htl : E[z].tail = toWord c := by rw [hew]; rfl
      have hlen1 := frames_take_le E (z + 1)
      have hlen2 := length_frames_take_succ hz
      have hfl : f + 1 + E[z].length ≤ e + L := by simp only [f]; omega
      have hmem : ∀ v ∈ E[z].length :: E[z], v ∈ toWord E := frame_mem hz
      have hvew : ∀ v ∈ E[z], v < W + 1 := fun v h => hv v (hmem v (List.mem_cons_of_mem _ h))
      obtain ⟨r0, hr0⟩ := atoms_drop (X := toWord c) (y := 0) (t := c) (r := []) (by simp)
      simp only [List.drop_zero] at hr0
      have hAl : (toWord A).length ≤ (toWord c).length := by rw [hr0]; simp [A]
      have hwc : (toWord c).length + 1 = E[z].length := by rw [hew]; simp
      have hX0 : X[f]? = some E[z].length := by
        have := congrArg (·[0]?) hds; simpa [List.getElem?_drop] using this
      set ρ1 := ρ.setVar "tsS" (f + 2)
      set ρ2 := ρ1.setVar "tsN" (E[z].length - 1)
      set ρ3 := ρ2.setVar "tp1" (f + 2)
      set ρ4 := ρ3.setVar "tp2" (f + 2)
      have r1 : Run (W + 1) (.assign "tsS" (.add (.var "tf") (.lit 2))) ρ ρ1 4 :=
        (Run.assign (ev_add (ev_var hfρ (by omega)) (evalB_lit (by omega)) (by omega))).mono (by simp [Expr.size])
      have r2 : Run (W + 1) (.assign "tsN" (.sub (.get "a" (.var "tf")) (.lit 1))) ρ1 ρ2 5 :=
        (Run.assign (ev_sub (evalB_get (ev_var (v := f) (by simp [ρ1, hfρ]) (by omega))
          (by simp [ρ1, haρ, hX0]) (hv _ (hmem _ (List.mem_cons_self ..)))) (evalB_lit (by omega))
          (by omega))).mono (by simp [Expr.size])
      have r3 : Run (W + 1) (.assign "tp1" (.add (.var "tf") (.lit 2))) ρ2 ρ3 4 :=
        (Run.assign (ev_add (ev_var (by simp [ρ2, ρ1, hfρ]) (by omega)) (evalB_lit (by omega)) (by omega))).mono
          (by simp [Expr.size])
      have r4 : Run (W + 1) (.assign "tp2" (.add (.var "tf") (.lit 2))) ρ3 ρ4 4 :=
        (Run.assign (ev_add (ev_var (by simp [ρ3, ρ2, ρ1, hfρ]) (by omega)) (evalB_lit (by omega)) (by omega))).mono
          (by simp [Expr.size])
      have kv : ∀ y ∈ ["ii", "th0", "th1", "th2", "tP", "tQ", "tcP", "tcQ", "ti2", "ts", "tL"],
          ρ4.vars y = τ.vars y := fun y hy => by
        have h1 : y ≠ "tp2" := by intro h; subst h; simp at hy
        have h2 : y ≠ "tp1" := by intro h; subst h; simp at hy
        have h3 : y ≠ "tsN" := by intro h; subst h; simp at hy
        have h4 : y ≠ "tsS" := by intro h; subst h; simp at hy
        simp only [ρ4, ρ3, ρ2, ρ1, vars_setVar, h1, h2, h3, h4, if_false]; exact oρ.vars y (kP y hy)
      have a4 : ρ4.arrs "a" = X := by simp [ρ4, ρ3, ρ2, ρ1, haρ]
      have H4 : HopAt "a" "a" X X A A (f + 2) (f + 2) Dw (ρ4.vars "ti1") ℓ R ρ4 :=
        ⟨a4, a4, by simp [ρ4, ρ3], by simp [ρ4], by rw [kv "tP" (by simp), hP], by rw [kv "tQ" (by simp), hQ],
          by rw [kv "tcP" (by simp), hcP], by rw [kv "tcQ" (by simp), hcQ], rfl, by rw [kv "ti2" (by simp), hi2],
          by rw [kv "ts" (by simp), hs]⟩
      have hseg : seg (ρ4.arrs "a") (f + 2) E[z].tail.length = E[z].tail := by
        rw [a4, seg, hd2, htl]; simp
      have E4 : EmAt i (ρ4.vars "tG") (k + 1) q (ℓ + 1) (f + 2) E[z].tail ρ4 :=
        ⟨by rw [kv "ii" (by simp), hi], rfl, by rw [kv "th0" (by simp), h0], by rw [kv "th1" (by simp), h1],
          by rw [kv "th2" (by simp), h2], by simp [ρ4, ρ3, ρ2, ρ1], by simp [ρ4, ρ3, ρ2, List.length_tail], hseg⟩
      have hstepB : ℓ * ((frames (E.take z)).length + 4 * z) + ℓ * (E[z].length + 5) ≤ ℓ * (5 * L) := by
        rw [← Nat.mul_add]; apply Nat.mul_le_mul_left; omega
      obtain ⟨ρ5, r5, F5, c5, o5⟩ := gLoop_run (W := W) (c := c₀ + ((E.take z).flatMap G).length) H4 hd3 E4
        (by rw [kv "tL" (by simp), hL]) (Fρ.setVar (by decide) _ |>.setVar (by decide) _ |>.setVar (by decide) _
          |>.setVar (by decide) _) (by simp [ρ4, ρ3, ρ2, ρ1, cρ])
        (by simp only [ρ4, ρ3, ρ2, ρ1, arrs_setVar]; rw [oρ.len, hOB]) (by rw [a4, ← ha, hal]; simp only [List.length_tail]; omega)
        (by
          simp only [List.length_append, List.length_tail]
          have : ℓ * (E[z].length - 1 + 6) = ℓ * (E[z].length + 5) := by congr 1; omega
          rw [this]; omega)
        (by simp only [List.length_tail]; omega)
        (fun x hx => by
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | rfl | rfl | hx
          · exact hik.1
          · exact hik.2.1
          · exact hik.2.2.1
          · exact hik.2.2.2
          · have := hvew x (List.mem_of_mem_tail hx); omega)
        (by
          have : ℓ * z + ℓ ≤ ℓ * (E.length + 1) := by rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
          omega)
        (by omega) (fun v h => hvew v (by rw [hew]; exact List.mem_cons_of_mem _ (by
          rw [hr0]; exact List.mem_append_left _ h)))
        hPB hQB (by omega) hR
      have hG : G E[z] = (guardW Dw R ℓ A ([k + 1, q, ℓ + 1] ++ E[z].tail)).map (i :: ·) := by
        simp only [G, oldG]; rw [hA, hcwd]
      have hfs := flatMap_take_succ hz G
      have hgl := length_guardW_le Dw R ℓ A ([k + 1, q, ℓ + 1] ++ E[z].tail)
      have kz : ∀ y ∈ ["tz", "tf", "tne"], y ∉ gLV ∧ y ≠ "tsS" ∧ y ≠ "tsN" ∧ y ≠ "tp1" ∧ y ≠ "tp2" := by decide
      have k5 : ∀ y ∈ ["tz", "tf", "tne"], ρ5.vars y = ρ.vars y := fun y hy => by
        obtain ⟨a1, a2, a3, a4', a5⟩ := kz y hy
        rw [o5.vars y a1]; simp [ρ4, ρ3, ρ2, ρ1, a2, a3, a4', a5]
      refine ⟨ρ5, ?_, ⟨?_, ?_, ?_, ?_, ?_⟩, by rw [k5 "tz" (by simp), hzρ], k5 "tf" (by simp),
        by rw [o5.arrs _ (by decide), a4], by rw [k5 "tne" (by simp), hnρ]⟩
      · unfold p2Body
        refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 r5)))).mono ?_
        have h1 := exHopK_mono (L := A.length + A.length) (L' := 2 * L) (R := R) (by
          have : A.length < (toWord A).length := by
            rw [toWord_words, List.length_cons, Words.length_frames]; omega
          omega)
        have h2 : hopK (A.length + A.length) R + 20 * E[z].tail.length + 100 ≤ hopK (2 * L) R + 20 * L + 100 := by
          simp only [List.length_tail]; omega
        have := Nat.mul_le_mul_left ℓ h2
        omega
      · rw [hfs, frames_append, ← List.append_assoc, hG]; exact F5
      · rw [c5, hfs, List.length_append, hG, List.length_map]; omega
      · rw [hfs, List.length_append, hG, List.length_map, Nat.mul_succ]; omega
      · rw [hfs, frames_append, List.length_append, hG, length_frames_oldG]
        have h3 := Nat.mul_le_mul_right (([k + 1, q, ℓ + 1] ++ E[z].tail).length + 3) hgl
        have h4 : ([k + 1, q, ℓ + 1] ++ E[z].tail).length + 3 = E[z].length + 5 := by
          simp only [List.length_append, List.length_tail, List.length_cons, List.length_nil]; omega
        rw [h4] at h3 ⊢
        have h5 : ℓ * ((frames (E.take z)).length + 4 * z) + ℓ * (E[z].length + 5) =
            ℓ * ((frames (E.take (z + 1))).length + 4 * (z + 1)) := by rw [hlen2]; ring
        omega
      · exact (oρ.trans ((((((OFr.setVar ρ "tsS" _).trans (OFr.setVar ρ1 "tsN" _)).trans
          (OFr.setVar ρ2 "tp1" _)).trans (OFr.setVar ρ3 "tp2" _)).trans o5))).mono (by decide))
  refine ⟨τ', r'.mono ?_, by rwa [List.take_length] at F', by rwa [List.take_length] at c', o'⟩
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  rw [show ℓ * (hopK (2 * L) R + 20 * L + 100) + 34 + 16 = ℓ * (hopK (2 * L) R + 20 * L + 100) + 50 by omega]

end Lax185574Proofs.ResolveRam.Glue
