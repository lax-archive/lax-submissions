import Lax185574Proofs.Words.Read
import Lax808846Proofs.Tactic

/-!
Copying a list of words verbatim from the input tape into the array `x`.

The command `cpList` reads a list of words, its length and then the
frames of the words, and stores every number it reads into `x` at the
pointer `xp`, which it advances. It uses the scalars `e1`, `e2`, `e3`,
`vv` and `ev`.
-/

namespace Lax185574Proofs.Words

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding

theorem frames_take_succ' {ws : List (List ℕ)} {j : ℕ} (h : j < ws.length) :
    frames (ws.take (j + 1)) = frames (ws.take j) ++ (ws[j].length :: ws[j]) := by
  rw [List.take_add_one, List.getElem?_eq_getElem h]
  simp only [frames, List.map_append, List.flatten_append, Option.toList_some, List.map_cons,
    List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]

theorem length_frames_take_succ {ws : List (List ℕ)} {j : ℕ} (h : j < ws.length) :
    (frames (ws.take (j + 1))).length = (frames (ws.take j)).length + 1 + ws[j].length := by
  rw [frames_take_succ' h]; simp; omega

theorem length_frames (ws : List (List ℕ)) : (frames ws).length = ws.length + total ws := by
  have := length_toWord_words ws
  rw [toWord_words] at this
  simp at this; omega

/-- Copy one number from the input to `x`. -/
def cpEntry : Com :=
  .seq (.read "ev") (.seq (.store "x" (.var "xp") (.var "ev"))
    (.seq (.assign "xp" (.add (.var "xp") (.lit 1))) (.assign "e3" (.add (.var "e3") (.lit 1)))))

/-- The array `x` holds `pre` followed by the rest of the original
contents `O`, and `xp` points after `pre`. -/
def XAt (O pre : List ℕ) (τ : Env) : Prop :=
  τ.vars "xp" = pre.length ∧ τ.arrs "x" = pre ++ O.drop pre.length

theorem XAt.store {O pre : List ℕ} {τ : Env} (h : XAt O pre τ) (hl : pre.length < O.length) (v : ℕ) :
    (τ.arrs "x").set (τ.vars "xp") v = (pre ++ [v]) ++ O.drop (pre ++ [v]).length := by
  rw [h.1, h.2, set_prefix hl]; simp

theorem cpEntry_spec (B : ℕ) (O pre u rest : List ℕ) (j : ℕ) (hj : j < u.length)
    (hfit : pre.length + 1 ≤ O.length) (hB : pre.length + 1 < B) (hu : u[j] < B) (hjB : j + 1 < B) :
    Spec B (fun τ => XAt O pre τ ∧ τ.inp = u.drop j ++ rest ∧ τ.vars "e3" = j) cpEntry
      (fun _ τ' => XAt O (pre ++ [u[j]]) τ' ∧ τ'.inp = u.drop (j + 1) ++ rest ∧
        τ'.vars "e3" = j + 1) 12 := by
  rintro τ ⟨hx, hinp, he3⟩
  have hinp' : τ.inp = u[j] :: (u.drop (j + 1) ++ rest) := by
    rw [hinp, List.drop_eq_getElem_cons hj]; rfl
  have hne : τ.inp ≠ [] := by rw [hinp']; simp
  have hxl : (τ.arrs "x").length = O.length := by rw [hx.2]; simp; omega
  obtain ⟨hxp, hxa⟩ := hx
  have hst : (τ.arrs "x").set pre.length u[j] = pre ++ u[j] :: O.drop (pre.length + 1) := by
    rw [hxa, set_prefix (by omega)]; simp
  unfold cpEntry
  run_vcg
  all_goals simp [XAt, hinp', hxp, he3, hst, hu]

/-- Copy `vv` numbers. -/
def cpEntries : Com := .while (.lt (.var "e3") (.var "vv")) cpEntry

theorem cpEntries_spec (B : ℕ) (O pre u rest : List ℕ)
    (hfit : pre.length + u.length ≤ O.length) (hB : pre.length + u.length < B)
    (hu : ∀ v ∈ u, v < B) :
    Spec B (fun τ => XAt O pre τ ∧ τ.inp = u ++ rest ∧ τ.vars "e3" = 0 ∧ τ.vars "vv" = u.length)
      cpEntries
      (fun _ τ' => XAt O (pre ++ u) τ' ∧ τ'.inp = rest ∧ τ'.vars "vv" = u.length)
      (16 * u.length + 4) := by
  rintro τ ⟨hx, hinp, he3, hvv⟩
  let I : Env → Prop := fun ρ => ρ.vars "e3" ≤ u.length ∧ ρ.vars "vv" = u.length ∧
    XAt O (pre ++ u.take (ρ.vars "e3")) ρ ∧ ρ.inp = u.drop (ρ.vars "e3") ++ rest
  have hbody : Spec B (fun ρ => I ρ ∧ ρ.vars "e3" < u.length) cpEntry
      (fun ρ ρ' => I ρ' ∧ ρ'.vars "e3" = ρ.vars "e3" + 1) 12 := by
    rintro ρ ⟨⟨hle, hvv, hx, hinp⟩, hlt⟩
    have hj : ρ.vars "e3" < u.length := hlt
    obtain ⟨ρ', hr', hx', hinp', he3'⟩ := cpEntry_spec B O (pre ++ u.take (ρ.vars "e3")) u rest
      (ρ.vars "e3") hj (by simp; omega) (by simp; omega) (hu _ (List.getElem_mem _)) (by omega) ρ
      ⟨hx, hinp, rfl⟩
    refine ⟨ρ', hr', ⟨by omega, ?_, ?_, ?_⟩, he3'⟩
    · rw [hr'.frame_var "vv" (by decide), hvv]
    · rw [he3', List.take_add_one, List.getElem?_eq_getElem hj]; simpa using hx'
    · rw [he3']; exact hinp'
  obtain ⟨τ', hr, ⟨hle, hvv', hx', hinp'⟩, he⟩ := (Spec.forRange (B := B) (c := cpEntry) "e3" "vv" I
    u.length 12 (16 * u.length + 4) (fun ρ hI => by omega) (fun ρ hI => by rw [hI.2.1]; omega)
    (fun ρ hI => hI.2.1) (fun ρ hI => hI.1) hbody (P := fun ρ => ρ = τ) (fun ρ h => by
      subst h; exact ⟨by omega, hvv, by simpa [he3] using hx, by simpa [he3] using hinp⟩)
    (fun ρ h => by subst h; omega)).run rfl
  refine ⟨τ', hr, ?_, by rw [hinp', he]; simp, hvv'⟩
  rw [he, List.take_length] at hx'
  exact hx'

/-- Copy one frame: its length, then its entries. -/
def cpFrame : Com :=
  .seq (.read "vv") (.seq (.store "x" (.var "xp") (.var "vv"))
    (.seq (.assign "xp" (.add (.var "xp") (.lit 1))) (.seq (.assign "e3" (.lit 0))
      (.seq cpEntries (.assign "e2" (.add (.var "e2") (.lit 1)))))))

theorem cpFrame_spec (B : ℕ) (O pre u rest : List ℕ) (j : ℕ)
    (hfit : pre.length + 1 + u.length ≤ O.length) (hB : pre.length + 1 + u.length < B)
    (hu : ∀ v ∈ u, v < B) (hlB : u.length < B) (hjB : j + 1 < B) :
    Spec B (fun τ => XAt O pre τ ∧ τ.inp = (u.length :: u) ++ rest ∧ τ.vars "e2" = j) cpFrame
      (fun _ τ' => XAt O (pre ++ (u.length :: u)) τ' ∧ τ'.inp = rest ∧ τ'.vars "e2" = j + 1)
      (16 * u.length + 20) := by
  rintro τ ⟨⟨hxp, hxa⟩, hinp, he2⟩
  have hinp' : τ.inp = u.length :: (u ++ rest) := by rw [hinp]; rfl
  have hne : τ.inp ≠ [] := by rw [hinp']; simp
  have hxl : (τ.arrs "x").length = O.length := by rw [hxa]; simp; omega
  have hst : (τ.arrs "x").set pre.length u.length = pre ++ u.length :: O.drop (pre.length + 1) := by
    rw [hxa, set_prefix (by omega)]; simp
  unfold cpFrame
  run_vcg [(cpEntries_spec B O (pre ++ [u.length]) u rest (by simp; omega) (by simp; omega) hu).frame]
  · rename_i ρ h
    obtain ⟨⟨⟨hx1, hx2⟩, hi, -⟩, hfv, -, -, -⟩ := h
    have he2' : ρ.vars "e2" = j := by rw [hfv "e2" (by decide)]; simp [he2]
    refine ⟨⟨by simp [hx1], by simp [hx2]⟩, by simp [hi], by simp [he2']⟩
  · simp [hinp', hlB]
  · refine ⟨⟨by simp [hxp], by simp [hxp, hst, hinp']⟩, by simp [hinp'], by simp, by simp [hinp']⟩
  all_goals
    rename_i ρ h1 h
    obtain ⟨-, hfv, -, -, -⟩ := h
    rw [hfv "e2" (by decide)]; simp [he2]; omega

/-- Copy a list of words. -/
def cpList : Com :=
  .seq (.read "e1") (.seq (.store "x" (.var "xp") (.var "e1"))
    (.seq (.assign "xp" (.add (.var "xp") (.lit 1))) (.seq (.assign "e2" (.lit 0))
      (.while (.lt (.var "e2") (.var "e1")) cpFrame))))

theorem length_frames_drop {ws : List (List ℕ)} {j : ℕ} (hj : j < ws.length) :
    (frames (ws.drop j)).length = ws[j].length + 1 + (frames (ws.drop (j + 1))).length := by
  rw [frames_drop hj]; simp; omega

theorem cpList_spec (B : ℕ) (O pre rest : List ℕ) (ws : List (List ℕ))
    (hfit : pre.length + (toWord ws).length ≤ O.length) (hB : pre.length + (toWord ws).length < B)
    (hv : ∀ v ∈ toWord ws, v < B) :
    Spec B (fun τ => XAt O pre τ ∧ τ.inp = toWord ws ++ rest) cpList
      (fun _ τ' => XAt O (pre ++ toWord ws) τ' ∧ τ'.inp = rest)
      (24 * (toWord ws).length + 12) := by
  rintro τ ⟨⟨hxp, hxa⟩, hinp⟩
  have hlw := length_toWord_words ws
  have hfl := length_frames ws
  rw [toWord_words] at hinp hfit hB hv ⊢
  have hinp' : τ.inp = ws.length :: (frames ws ++ rest) := by rw [hinp]; rfl
  have hxl : (τ.arrs "x").length = O.length := by rw [hxa]; simp; omega
  have hst : (τ.arrs "x").set pre.length ws.length = (pre ++ [ws.length]) ++ O.drop (pre.length + 1) := by
    rw [hxa, set_prefix (by simp at hfit; omega)]
  let P := pre ++ [ws.length]
  let I : Env → Prop := fun ρ => ρ.vars "e2" ≤ ws.length ∧ ρ.vars "e1" = ws.length ∧
    XAt O (P ++ frames (ws.take (ρ.vars "e2"))) ρ ∧ ρ.inp = frames (ws.drop (ρ.vars "e2")) ++ rest
  have hlenB : ws.length < B := by simp at hB; omega
  have hstep : ∀ ρ, I ρ → (Cond.lt (.var "e2") (.var "e1")).evalB B ρ = some true →
      ∃ ρ' K, Run B cpFrame ρ ρ' K ∧ I ρ' ∧
        1 + (Cond.lt (.var "e2") (.var "e1")).size + K +
          24 * (frames (ws.drop (ρ'.vars "e2"))).length ≤
          24 * (frames (ws.drop (ρ.vars "e2"))).length := by
    rintro ρ ⟨hle, he1, hx, hinp⟩ hc
    have hj : ρ.vars "e2" < ws.length := by
      have := lt_of_condLt_true hc; rwa [he1] at this
    generalize hjd : ρ.vars "e2" = j at *
    have hmem := mem_toWord_words hj
    rw [toWord_words] at hmem
    have hfd := length_frames_drop hj
    have htk := length_frames_take_succ hj
    have hfr : (frames (ws.take j)).length + (frames (ws.drop j)).length = (frames ws).length := by
      rw [← List.length_append]; congr 1
      simp only [frames, ← List.flatten_append, ← List.map_append, List.take_append_drop]
    obtain ⟨ρ', hr, hx', hinp', he2'⟩ := cpFrame_spec B O (P ++ frames (ws.take j)) ws[j]
      (frames (ws.drop (j + 1)) ++ rest) j (by simp [P] at hfit ⊢; omega)
      (by simp [P] at hB ⊢; omega)
      (fun v hv' => hv v (hmem.2 v hv'))
      (hv _ hmem.1) (by omega) ρ
      ⟨hx, by rw [hinp, frames_drop hj]; simp, hjd⟩
    refine ⟨ρ', _, hr, ⟨by omega, by rw [hr.frame_var "e1" (by decide), he1], ?_, ?_⟩, ?_⟩
    · rw [he2', frames_take_succ' hj]; simpa using hx'
    · rw [he2', hinp']
    · rw [he2']; simp; omega
  obtain ⟨τ', K, hr, ⟨hle, he1, hx, hinp2⟩, hfalse, hK⟩ := Run.while_potential (B := B)
    (b := .lt (.var "e2") (.var "e1")) (c := cpFrame) I
    (fun ρ => 24 * (frames (ws.drop (ρ.vars "e2"))).length)
    (fun ρ hI => evalB_condLt_vars (by have := hI.1; omega) (by rw [hI.2.1]; omega)) hstep
    (σ := (({ τ.setVar "e1" ws.length with inp := frames ws ++ rest }.setArr "x" pre.length
      ws.length).setVar "xp" (pre.length + 1)).setVar "e2" 0)
    ⟨by simp, by simp, ⟨by simp [P, frames], by simp [P, hst, frames]⟩, by simp⟩
  have hend : τ'.vars "e2" = ws.length := by
    have := le_of_condLt_false hfalse; rw [he1] at this; omega
  refine ⟨τ', ?_, ?_, ?_⟩
  · unfold cpList
    refine (Run.seq (Run.read hinp') (Run.seq (Run.store ?_ ?_ ?_) (Run.seq (Run.assign ?_)
      (Run.seq (Run.assign ?_) hr)))).mono ?_
    · simp [hxp]; simp at hB; omega
    · simp; omega
    · simp [hxl]; simp at hfit; omega
    · simp [hxp]; simp at hB; omega
    · simp; omega
    · simp at hK ⊢; omega
  · rw [hend, List.take_length] at hx; simpa [P] using hx
  · rw [hinp2, hend]; simp [frames]

end Lax185574Proofs.Words
