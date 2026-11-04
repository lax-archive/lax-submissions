import Lax185574Proofs.ResolveRam.Glue.PEx3

/-!
The first part of the expansion of lem:resolve-lift: the old extensions.

For every extension word `ew` of the root (the list at `te` of `a`),
`part1` appends the frame of `i :: ew.headD 0 :: childW k q ℓ ew`, the
word of the extension with the header `k + 1, q, ℓ + 1` of the child in
front of the child root (`part1_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.EvalRam Lax185574Proofs.FarRam
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo

/-- One old extension. -/
def p1Body : Com :=
  .seq (.assign "tG" (.get "a" (.add (.var "tf") (.lit 1)))) (.seq (.assign "tsS" (.add (.var "tf") (.lit 2)))
    (.seq (.assign "tsN" (.sub (.get "a" (.var "tf")) (.lit 1))) gEmit))

/-- The old extensions. -/
def part1 : Com := frLoop p1Body

/-- The scalars that `part1` writes. -/
def p1V : List String := ["tG", "tsS", "tsN", "po", "ci", "pc", "tf", "tz"]

/-- The word of an old extension. -/
def oldW (i k q ℓ : ℕ) (ew : List ℕ) : List ℕ := i :: (ew.headD 0 :: childW k q ℓ ew)

theorem frames_map_take_succ {E : List (List ℕ)} {z : ℕ} (hz : z < E.length) (f : List ℕ → List ℕ) :
    frames ((E.take (z + 1)).map f) = frames ((E.take z).map f) ++ frames [f E[z]] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hz, Option.toList_some, List.map_append, frames_append]
  rfl

/-- A frame of the list at `e` as a segment of `a`. -/
theorem frame_seg {X : List ℕ} {e : ℕ} {E : List (List ℕ)} {r : List ℕ} (hd : X.drop e = toWord E ++ r)
    {z : ℕ} (hz : z < E.length) :
    X.drop (e + 1 + (frames (E.take z)).length) = E[z].length :: (E[z] ++ (frames (E.drop (z + 1)) ++ r)) := by
  obtain ⟨-, hpos, -, -, -⟩ := listAt hd
  obtain ⟨hp1, hp2⟩ := hpos z hz.le
  rw [← hp1, hp2, frames_drop hz]; simp

/-- **The old extensions.** -/
theorem part1_run {W : ℕ} {X : List ℕ} {e : ℕ} {E : List (List ℕ)} {r : List ℕ} {pre : List ℕ}
    {i k q ℓ c₀ : ℕ} {τ : Env}
    (ha : τ.arrs "a" = X) (hd : X.drop e = toWord E ++ r) (hte : τ.vars "te" = e)
    (hne : τ.vars "tne" = E.length) (hE : ∀ ew ∈ E, 1 ≤ ew.length) (hi : τ.vars "ii" = i)
    (h0 : τ.vars "th0" = k + 1) (h1 : τ.vars "th1" = q) (h2 : τ.vars "th2" = ℓ + 1)
    (hF : Filled "OB" "po" pre τ) (hpc : τ.vars "pc" = c₀) (hOB : (τ.arrs "OB").length = W + 1)
    (hal : (τ.arrs "a").length = W + 1)
    (hB : e + (toWord E).length + 2 < W + 1) (hv : ∀ v ∈ toWord E, v < W + 1)
    (hcap : pre.length + 5 * (toWord E).length ≤ W) (hik : i ≤ W ∧ k + 1 ≤ W ∧ q ≤ W ∧ ℓ + 1 ≤ W)
    (hc : c₀ + E.length + 1 ≤ W) :
    ∃ τ', Run (W + 1) part1 τ τ' (E.length * (20 * (toWord E).length + 130) + 10) ∧
      Filled "OB" "po" (pre ++ frames (E.map (oldW i k q ℓ))) τ' ∧ τ'.vars "pc" = c₀ + E.length ∧
      OFr τ τ' p1V := by
  have hEl : E.length < (toWord E).length := by
    rw [toWord_words, List.length_cons, Words.length_frames]; omega
  let I : ℕ → Env → Prop := fun z ρ =>
    Filled "OB" "po" (pre ++ frames ((E.take z).map (oldW i k q ℓ))) ρ ∧ ρ.vars "pc" = c₀ + z ∧
    OFr τ ρ p1V
  have hfr : ∀ z, (frames ((E.take z).map (oldW i k q ℓ))).length = (frames (E.take z)).length + 4 * z ∧
      z ≤ E.length ∨ E.length < z := by
    intro z
    rcases Nat.lt_or_ge E.length z with h | h
    · exact Or.inr h
    · left
      induction z with
      | zero => simp [frames]
      | succ z ih =>
        obtain ⟨ih1, -⟩ := ih (by omega)
        refine ⟨?_, h⟩
        rw [frames_map_take_succ (by omega), List.length_append, ih1, frames_take_succ' (by omega)]
        simp [frames, oldW, childW]
        have := hE E[z] (List.getElem_mem (by omega))
        omega
  obtain ⟨τ', r', ⟨F', c', o'⟩, -⟩ := frLoop_run (W := W) (body := p1Body) (X := X)
    (fun _ => 20 * (toWord E).length + 110) I ha hd hte hne hB hv
    (fun z ρ x ⟨h1, h2, h3⟩ => ⟨h1.setVar (by decide) _, by simp [h2], (h3.trans (OFr.setVar ρ "tf" x)).mono
      (by decide)⟩)
    (fun z ρ x ⟨h1, h2, h3⟩ => ⟨h1.setVar (by decide) _, by simp [h2], (h3.trans (OFr.setVar ρ "tz" x)).mono
      (by decide)⟩)
    ⟨by simpa [frames] using hF, by simp [hpc], OFr.refl τ |>.mono (by simp)⟩
    (by
      rintro z hz ρ ⟨Fρ, cρ, oρ⟩ hzρ hfρ haρ hnρ
      have hds := frame_seg hd hz
      set f := e + 1 + (frames (E.take z)).length
      obtain ⟨a0, l0, hz0⟩ : ∃ a0 l0, E[z] = a0 :: l0 := by
        have := hE E[z] (List.getElem_mem hz)
        cases h : E[z] with
        | nil => rw [h] at this; simp at this
        | cons a l => exact ⟨a, l, rfl⟩
      set ew := E[z]
      have hew : 1 ≤ ew.length := hE ew (List.getElem_mem hz)
      have hX0 : X[f]? = some ew.length := by
        have := congrArg (·[0]?) hds; simpa [List.getElem?_drop] using this
      have hX1 : X[f + 1]? = some (ew.headD 0) := by
        have := congrArg (·[1]?) hds; simp only [List.getElem?_drop] at this; rw [this, hz0]; simp
      have hd2 : X.drop (f + 2) = ew.tail ++ (frames (E.drop (z + 1)) ++ r) := by
        rw [show X.drop (f + 2) = (X.drop f).drop 2 by rw [List.drop_drop], hds, hz0]
        simp
      have hfl : f + 1 + ew.length ≤ e + (toWord E).length := by
        have h1 := frames_take_le E (z + 1)
        have h2 := length_frames_take_succ hz
        have h3 : (toWord E).length = (frames E).length + 1 := by rw [toWord_words]; simp
        simp only [f, ew]; omega
      have hmem : ∀ v ∈ ew.length :: ew, v ∈ toWord E := frame_mem hz
      have hvew : ∀ v ∈ ew, v < W + 1 := fun v h => hv v (hmem v (List.mem_cons_of_mem _ h))
      set ρ1 := ρ.setVar "tG" (ew.headD 0)
      set ρ2 := ρ1.setVar "tsS" (f + 2)
      set ρ3 := ρ2.setVar "tsN" (ew.length - 1)
      have hhd : ew.headD 0 < W + 1 := by
        simp only [ew, hz0, List.headD_cons]; exact hvew a0 (by simp [ew, hz0])
      have r1 : Run (W + 1) (.assign "tG" (.get "a" (.add (.var "tf") (.lit 1)))) ρ ρ1 5 :=
        (Run.assign (evalB_get (ev_add (ev_var hfρ (by omega)) (evalB_lit (by omega)) (by omega))
          (by rw [haρ]; exact hX1) hhd)).mono (by simp [Expr.size])
      have r2 : Run (W + 1) (.assign "tsS" (.add (.var "tf") (.lit 2))) ρ1 ρ2 4 :=
        (Run.assign (ev_add (ev_var (by simp [ρ1, hfρ]) (by omega)) (evalB_lit (by omega)) (by omega))).mono
          (by simp [Expr.size])
      have r3 : Run (W + 1) (.assign "tsN" (.sub (.get "a" (.var "tf")) (.lit 1))) ρ2 ρ3 5 :=
        (Run.assign (ev_sub (evalB_get (ev_var (v := f) (by simp [ρ2, ρ1, hfρ]) (by omega))
          (by simp [ρ2, ρ1, haρ, hX0]) (hv _ (hmem _ (List.mem_cons_self ..)))) (evalB_lit (by omega))
          (by omega))).mono (by simp [Expr.size])
      have hseg : seg (ρ3.arrs "a") (f + 2) ew.tail.length = ew.tail := by
        simp only [ρ3, ρ2, ρ1, arrs_setVar, seg, haρ]
        rw [hd2]; simp
      have kv : ∀ y ∈ ["ii", "th0", "th1", "th2"], ρ3.vars y = τ.vars y := fun y hy => by
        have : y ∉ p1V := by simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> decide
        have h1 : y ≠ "tsN" := by simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> decide
        have h2 : y ≠ "tsS" := by simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> decide
        have h3 : y ≠ "tG" := by simp at hy; rcases hy with rfl | rfl | rfl | rfl <;> decide
        simp only [ρ3, ρ2, ρ1, vars_setVar, h1, h2, h3, if_false]; exact oρ.vars y this
      have E3 : EmAt i (ew.headD 0) (k + 1) q (ℓ + 1) (f + 2) ew.tail ρ3 :=
        ⟨by rw [kv "ii" (by simp), hi], by simp [ρ3, ρ2, ρ1], by rw [kv "th0" (by simp), h0],
          by rw [kv "th1" (by simp), h1], by rw [kv "th2" (by simp), h2], by simp [ρ3, ρ2],
          by simp [ρ3, List.length_tail], hseg⟩
      have hpre := hfr z
      rcases hpre with ⟨hpre, -⟩ | hpre
      swap; · omega
      obtain ⟨ρ4, r4, F4, c4, o4⟩ := gEmit_run (W := W) (c := c₀ + z) E3 (Fρ.setVar (by decide) _ |>.setVar (by decide) _
          |>.setVar (by decide) _) (by simp [ρ3, ρ2, ρ1, cρ])
        (by simp only [ρ3, ρ2, ρ1, arrs_setVar]; rw [oρ.len, hOB]) (by simp only [ρ3, ρ2, ρ1, arrs_setVar]; rw [haρ, ← ha, hal]; simp only [List.length_tail]; omega)
        (by simp only [List.length_append, List.length_tail]
            have h1 := frames_take_le E (z + 1)
            have h2 := length_frames_take_succ hz
            have h3 : (toWord E).length = (frames E).length + 1 := by rw [toWord_words]; simp
            simp only [ew] at *
            omega)
        (by simp only [List.length_tail]; omega)
        (fun x hx => by
          simp only [List.mem_cons] at hx
          rcases hx with rfl | rfl | rfl | rfl | rfl | hx
          · exact hik.1
          · omega
          · exact hik.2.1
          · exact hik.2.2.1
          · exact hik.2.2.2
          · have := hvew x (List.mem_of_mem_tail hx); omega)
        (by omega)
      refine ⟨ρ4, ?_, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩
      · unfold p1Body
        exact (Run.seq r1 (Run.seq r2 (Run.seq r3 r4))).mono (by simp only [List.length_tail]; omega)
      · rw [frames_map_take_succ hz, ← List.append_assoc]
        have : oldW i k q ℓ E[z] = i :: ew.headD 0 :: (k + 1) :: q :: (ℓ + 1) :: ew.tail := by
          simp [oldW, childW, ew]
        rw [this]; exact F4
      · rw [c4]; omega
      · exact (oρ.trans ((((OFr.setVar ρ "tG" _).trans (OFr.setVar ρ1 "tsS" _)).trans
          (OFr.setVar ρ2 "tsN" _)).trans o4)).mono (by decide)
      · rw [o4.vars _ (by decide)]; simp [ρ3, ρ2, ρ1, hzρ]
      · rw [o4.vars _ (by decide)]; simp [ρ3, ρ2, ρ1]
      · rw [o4.arrs _ (by decide)]; simp [ρ3, ρ2, ρ1, haρ]
      · rw [o4.vars _ (by decide)]; simp [ρ3, ρ2, ρ1, hnρ])
  refine ⟨τ', r'.mono ?_, by rwa [List.take_length] at F', c', o'⟩
  simp only [Finset.sum_const, Finset.card_range, smul_eq_mul]
  nlinarith

end Lax185574Proofs.ResolveRam.Glue
