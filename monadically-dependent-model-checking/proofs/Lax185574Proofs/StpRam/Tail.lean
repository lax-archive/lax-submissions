import Lax185574Proofs.StpRam.Buffer
import Lax185574Proofs.ShiftRam.Glue

/-!
Writing the output of a round of the glue program of lem:compute-stp
that asks a query.

`cpMid` copies the state of a middle round into the buffer `x` and
appends the answer of the last call to the list of answers. `walk`
finds the position of a frame of a list of words in the buffer, `wFrame`
writes the word of that frame. `tail` writes the output of a round: the
tag, the length of the state and the length of the window of the input,
then the state, then the query.
-/

namespace Lax185574Proofs.StpRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574Proofs.ShiftRam

theorem toWord_snoc (A : List (List ℕ)) (b : List ℕ) :
    toWord (A ++ [b]) = (A.length + 1) :: (frames A ++ (b.length :: b)) := by
  rw [toWord_words]; simp [frames]

/-- Copy the state of a middle round and append the answer. -/
def cpMid : Com := .seq cpList (.seq (.assign "pa" (.var "xp")) (.seq cpList
  (.seq (.assign "e2" (.lit 0)) (.seq cpFrame
    (.store "x" (.var "pa") (.add (.get "x" (.var "pa")) (.lit 1)))))))

set_option maxHeartbeats 1000000 in
theorem cpMid_run {B : ℕ} {O pre rest : List ℕ} (F A : List (List ℕ)) (b : List ℕ) {τ : Env}
    (hx : XAt O pre τ) (hinp : τ.inp = toWord F ++ toWord A ++ (b.length :: b) ++ rest)
    (hfit : pre.length + (toWord F).length + (toWord (A ++ [b])).length ≤ O.length)
    (hB : pre.length + (toWord F).length + (toWord (A ++ [b])).length < B)
    (hv : ∀ v ∈ toWord F ++ toWord A ++ (b.length :: b), v < B) :
    ∃ τ', Run B cpMid τ τ' (24 * ((toWord F).length + (toWord (A ++ [b])).length) + 80) ∧
      XAt O (pre ++ toWord F ++ toWord (A ++ [b])) τ' ∧
      τ'.vars "pa" = pre.length + (toWord F).length ∧ τ'.inp = rest ∧ τ'.out = τ.out := by
  have hAl : (toWord (A ++ [b])).length = (toWord A).length + 1 + b.length := by
    rw [toWord_snoc, toWord_words]; simp; omega
  obtain ⟨τ1, r1, hx1, hi1⟩ := cpList_spec B O pre (toWord A ++ (b.length :: b) ++ rest) F
    (by omega) (by omega) (fun v h => hv v (by simp [h])) τ ⟨hx, by rw [hinp]; simp⟩
  have hp1 : τ1.vars "xp" = pre.length + (toWord F).length := by rw [hx1.1]; simp
  set τ2 := τ1.setVar "pa" (pre.length + (toWord F).length) with hτ2
  have r2 : Run B (.assign "pa" (.var "xp")) τ1 τ2 2 :=
    (Run.assign (by simp [hp1]; omega)).mono (by simp [Expr.size])
  obtain ⟨τ3, r3, hx3, hi3⟩ := cpList_spec B O (pre ++ toWord F) ((b.length :: b) ++ rest) A
    (by simp; omega) (by simp; omega) (fun v h => hv v (by simp [h])) τ2
    ⟨XAt.setVar hx1 (by decide) _, by simp [hτ2, hi1]⟩
  set τ4 := τ3.setVar "e2" 0 with hτ4
  have r4 : Run B (.assign "e2" (.lit 0)) τ3 τ4 2 := (Run.assign (by simp; omega)).mono (by simp [Expr.size])
  obtain ⟨τ5, r5, hx5, hi5, -⟩ := cpFrame_spec B O (pre ++ toWord F ++ toWord A) b rest 0
    (by simp; omega) (by simp; omega) (fun v h => hv v (by simp [h])) (by omega) (by omega) τ4
    ⟨XAt.setVar hx3 (by decide) _, by simp [hτ4, hi3], by simp [hτ4]⟩
  have hpa5 : τ5.vars "pa" = pre.length + (toWord F).length := by
    rw [r5.frame_var "pa" (by decide)]; simp [hτ4, r3.frame_var "pa" (by decide), hτ2]
  have hA : toWord A = A.length :: frames A := toWord_words A
  have hx5' : XAt O ((pre ++ toWord F) ++ A.length :: (frames A ++ (b.length :: b))) τ5 := by
    have : pre ++ toWord F ++ toWord A ++ (b.length :: b) =
        (pre ++ toWord F) ++ A.length :: (frames A ++ (b.length :: b)) := by rw [hA]; simp
    rw [← this]; exact hx5
  have hxl5 : (τ5.arrs "x").length = O.length := by
    have hl : (frames A).length + 1 + b.length + 1 = (toWord (A ++ [b])).length := by
      rw [toWord_snoc]; simp; omega
    rw [hx5'.2]; simp only [List.length_append, List.length_cons, List.length_drop]
    omega
  have hget : (τ5.arrs "x")[pre.length + (toWord F).length]? = some A.length := by
    rw [hx5'.2]
    have : pre.length + (toWord F).length = (pre ++ toWord F).length := by simp
    rw [this, List.append_assoc]; simp
  have hAB : A.length + 1 < B := by
    have := length_toWord_words A; omega
  have r6 : Run B (.store "x" (.var "pa") (.add (.get "x" (.var "pa")) (.lit 1))) τ5
      (τ5.setArr "x" (pre ++ toWord F).length (A.length + 1)) 10 := by
    refine (Run.store (idx := (pre ++ toWord F).length) (by simp [hpa5]; omega) ?_
      (by simp; omega)).mono (by simp [Expr.size])
    simp only [evalB_bin_iff, evalB_get_iff, evalB_var_iff, evalB_lit_iff, hpa5]
    exact ⟨A.length, 1, ⟨_, ⟨rfl, by omega⟩, hget, by omega⟩, ⟨rfl, by omega⟩, rfl, hAB⟩
  have hrun : Run B cpMid τ (τ5.setArr "x" (pre ++ toWord F).length (A.length + 1))
      (24 * ((toWord F).length + (toWord (A ++ [b])).length) + 80) := by
    unfold cpMid
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 r6))))).mono ?_
    omega
  refine ⟨_, hrun, ?_, by simp [hpa5], by simp [hi5], hrun.out_eq (by decide)⟩
  have := XAt.setBack hx5' (A.length + 1)
  rw [toWord_snoc]; simpa using this

/-! ### Finding and writing a frame -/

/-- Skip `wc` frames from position `ws0` on. -/
def walk : Com := .seq (.assign "y" (.var "ws0"))
  (forUp "e2" (.var "wc") (.assign "y" (.add (.add (.var "y") (.get "x" (.var "y"))) (.lit 1))))

theorem walk_run {B : ℕ} {X : List ℕ} {p j : ℕ} {ws : List (List ℕ)} {r : List ℕ} {τ : Env}
    (hX : τ.arrs "x" = X) (hp : τ.vars "ws0" = p) (hj : τ.vars "wc" = j) (hjl : j ≤ ws.length)
    (hdrop : X.drop p = frames ws ++ r) (hB : p + (frames ws).length + 1 < B) :
    ∃ τ', Run B walk τ τ' (20 * j + 10) ∧ τ'.vars "y" = p + (frames (ws.take j)).length ∧
      X.drop (τ'.vars "y") = frames (ws.drop j) ++ r ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out := by
  have hpos := fun k (hk : k ≤ ws.length) => skipFr_frames hdrop hk
  have hfa : ∀ k, (frames (ws.take k)).length ≤ (frames ws).length := fun k => by
    rw [← frames_take_drop ws k]; simp
  set τ1 := τ.setVar "y" p with hτ1
  have r1 : Run B (.assign "y" (.var "ws0")) τ τ1 2 :=
    (Run.assign (by simp [hp]; omega)).mono (by simp [Expr.size])
  have hjB : j < B := by
    have := length_frames ws
    have : j ≤ (frames ws).length := by omega
    omega
  obtain ⟨τ2, r2, ⟨hy2, -, ha2, ho2⟩, -⟩ := forUp_run (B := B) (i := "e2") (e := .var "wc")
    (body := .assign "y" (.add (.add (.var "y") (.get "x" (.var "y"))) (.lit 1))) (N := j) (K := 8)
    (fun k ρ => ρ.vars "y" = skipFr X p k ∧ ρ.vars "wc" = j ∧ ρ.arrs = τ.arrs ∧ ρ.out = τ.out)
    (σ := τ1) hjB
    (fun k _ ρ hI _ => by
      simp only [evalB_var_iff]; exact ⟨hI.2.1.symm, by rw [hI.2.1]; exact hjB⟩)
    ⟨by simp [hτ1, skipFr], by simp [hτ1, hj], by simp [hτ1], by simp [hτ1]⟩
    (by
      rintro k hk ρ ⟨hy, hwc, ha, ho⟩ he2
      obtain ⟨h1, h2⟩ := hpos k (by omega)
      have hkl : k < ws.length := by omega
      rw [frames_drop hkl] at h2
      have hxg : xg X (skipFr X p k) = ws[k].length := xg_of_drop (by rw [h2]; rfl)
      have hget : X[skipFr X p k]? = some ws[k].length := by
        have := congrArg (fun l => l[0]?) h2
        simpa using this
      have hS := skipFr_succ' X p k
      obtain ⟨h3, -⟩ := hpos (k + 1) (by omega)
      have hf1 := hfa (k + 1)
      refine ⟨ρ.setVar "y" (skipFr X p (k + 1)), (Run.assign ?_).mono (by simp [Expr.size]),
        by simp [he2], by simp, by simp [hwc], by simp [ha], by simp [ho]⟩
      simp only [evalB_bin_iff, evalB_get_iff, evalB_var_iff, evalB_lit_iff, hy, ha, hX]
      refine ⟨skipFr X p k + ws[k].length, 1, ⟨_, _, ⟨rfl, by omega⟩, ⟨_, ⟨rfl, by omega⟩, hget, ?_⟩,
        rfl, ?_⟩, ⟨rfl, by omega⟩, ?_, ?_⟩
      · omega
      · show _ + _ < B; omega
      · rw [hS, hxg]; simp [Bop.apply]; omega
      · omega)
  obtain ⟨h1, h2⟩ := hpos j hjl
  have hrun : Run B walk τ τ2 (20 * j + 10) := by
    unfold walk
    refine (Run.seq r1 r2).mono ?_
    simp only [Expr.size]; omega
  exact ⟨τ2, hrun, by rw [hy2, h1], by rw [hy2, h2], by rw [ha2], by rw [ho2]⟩

/-- Write the word of the frame at position `y`. -/
def wFrame : Com := .seq (.assign "fl2" (.get "x" (.var "y")))
  (forUp "i" (.var "fl2") (.write (.get "x" (.add (.add (.var "y") (.lit 1)) (.var "i")))))

theorem wFrame_run {B : ℕ} {X : List ℕ} {y : ℕ} {u r : List ℕ} {τ : Env} (hX : τ.arrs "x" = X)
    (hy : τ.vars "y" = y) (hd : X.drop y = (u.length :: u) ++ r) (hB : y + u.length + 2 < B)
    (hu : ∀ v ∈ u, v < B) :
    ∃ τ', Run B wFrame τ τ' (20 * u.length + 20) ∧ τ'.out = τ.out ++ u ∧ τ'.arrs = τ.arrs := by
  have hget : X[y]? = some u.length := by
    have := congrArg (fun l => l[0]?) hd
    simpa using this
  have hget' : ∀ i (hi : i < u.length), X[y + 1 + i]? = some u[i] := by
    intro i hi
    have := congrArg (fun l => l[1 + i]?) hd
    simp only [List.getElem?_drop] at this
    rw [show y + 1 + i = y + (1 + i) by omega, this]
    simp [List.getElem?_cons, hi]
    rw [List.getElem?_append_left hi]; simp
  set τ1 := τ.setVar "fl2" u.length with hτ1
  have r1 : Run B (.assign "fl2" (.get "x" (.var "y"))) τ τ1 3 := by
    refine (Run.assign ?_).mono (by simp [Expr.size])
    simp only [evalB_get_iff, evalB_var_iff, hy, hX]
    exact ⟨y, ⟨rfl, by omega⟩, hget, by omega⟩
  obtain ⟨τ2, r2, ⟨ha2, hy2, hf2⟩, ho2⟩ := writeLoop_run (B := B) (N := u.length) (m := "fl2")
    (e := .get "x" (.add (.add (.var "y") (.lit 1)) (.var "i"))) (fun i => u.getD i 0)
    (fun ρ => ρ.arrs "x" = X ∧ ρ.vars "y" = y ∧ ρ.vars "fl2" = u.length) (by omega) (by decide)
    (fun ρ o h => h) (fun ρ k h => ⟨by simp [h.1], by simp [h.2.1], by simp [h.2.2]⟩)
    (fun ρ h => h.2.2)
    (fun ρ h hi => by
      have hi' : ρ.vars "i" < u.length := hi
      simp only [evalB_get_iff, evalB_bin_iff, evalB_var_iff, evalB_lit_iff, h.1, h.2.1]
      refine ⟨y + 1 + ρ.vars "i", ⟨y + 1, ρ.vars "i", ⟨y, 1, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, rfl,
        by show _ + _ < B; omega⟩, ⟨rfl, by omega⟩, rfl, by show _ + _ < B; omega⟩, ?_, ?_⟩
      · rw [hget' _ hi']; simp [hi']
      · simp [hi']; exact hu _ (List.getElem_mem _))
    τ1 ⟨by simp [hτ1, hX], by simp [hτ1, hy], by simp [hτ1]⟩
  have hmap : (List.range u.length).map (fun i => u.getD i 0) = u := by
    apply List.ext_getElem (by simp)
    intro i h1 h2; simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1 : i < u.length)]
  have hrun : Run B wFrame τ τ2 (20 * u.length + 20) := by
    unfold wFrame
    refine (Run.seq r1 r2).mono ?_
    simp only [Expr.size]; omega
  refine ⟨τ2, hrun, by rw [ho2, hmap]; simp [hτ1], ?_⟩
  funext a; exact hrun.frame_arr a (by simp [wFrame, forUp, Com.warrs])

/-! ### The output of a round with a query -/

/-- Write the output of a round that asks a query: the tag, the length of
the state, the length of the window, the state, and frame `wc` of the
list of words whose frames start at `ws0`. -/
def tail : Com := .seq (.write (.var "otg")) (.seq (.write (.var "xp")) (.seq (.write (.var "owin"))
  (.seq (forUp "i" (.var "xp") (.write (.get "x" (.var "i")))) (.seq walk wFrame))))

set_option maxHeartbeats 1000000 in
theorem tail_run {B : ℕ} {S D : List ℕ} {p j tg win : ℕ} {ws : List (List ℕ)} {r : List ℕ} {τ : Env}
    (hX : τ.arrs "x" = S ++ D) (hxp : τ.vars "xp" = S.length) (htg : τ.vars "otg" = tg)
    (hwin : τ.vars "owin" = win) (hp : τ.vars "ws0" = p) (hj : τ.vars "wc" = j)
    (hjl : j < ws.length) (hdrop : S.drop p = frames ws ++ r) (hSB : S.length + 2 < B)
    (hvB : ∀ v ∈ S, v < B) (htgB : tg < B) (hwinB : win < B) :
    ∃ τ', Run B tail τ τ' (60 * S.length + 60) ∧
      τ'.out = τ.out ++ [tg, S.length, win] ++ S ++ ws[j] := by
  have hpS : p + (frames ws).length ≤ S.length := by
    have := congrArg List.length hdrop
    simp only [List.length_drop, List.length_append] at this
    have hne : (frames ws).length ≠ 0 := by
      have := length_frames ws; omega
    omega
  have hXd : (S ++ D).drop p = frames ws ++ (r ++ D) := by
    rw [List.drop_append_of_le_length (by omega), hdrop, List.append_assoc]
  set τ1 : Env := { τ with out := τ.out ++ [tg] } with hτ1
  have r1 : Run B (.write (.var "otg")) τ τ1 2 := (Run.write (by simp [htg]; omega)).mono (by simp [Expr.size])
  set τ2 : Env := { τ1 with out := τ1.out ++ [S.length] } with hτ2
  have r2 : Run B (.write (.var "xp")) τ1 τ2 2 :=
    (Run.write (by simp [hτ1, hxp]; omega)).mono (by simp [Expr.size])
  set τ3 : Env := { τ2 with out := τ2.out ++ [win] } with hτ3
  have r3 : Run B (.write (.var "owin")) τ2 τ3 2 :=
    (Run.write (by simp [hτ2, hτ1, hwin]; omega)).mono (by simp [Expr.size])
  obtain ⟨τ4, r4, ⟨ha4, -⟩, ho4⟩ := writeLoop_run (B := B) (N := S.length) (m := "xp")
    (e := .get "x" (.var "i")) (fun i => S.getD i 0)
    (fun ρ => ρ.arrs "x" = S ++ D ∧ ρ.vars "xp" = S.length) (by omega) (by decide)
    (fun ρ o h => h) (fun ρ k h => ⟨by simp [h.1], by simp [h.2]⟩) (fun ρ h => h.2)
    (fun ρ h hi => by
      simp only [evalB_get_iff, evalB_var_iff, h.1]
      refine ⟨ρ.vars "i", ⟨rfl, by omega⟩, ?_, ?_⟩
      · rw [List.getElem?_append_left hi, List.getElem?_eq_getElem hi]
        simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
      · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
        exact hvB _ (List.getElem_mem _))
    τ3 ⟨by simp [hτ3, hτ2, hτ1, hX], by simp [hτ3, hτ2, hτ1, hxp]⟩
  have hmap : (List.range S.length).map (fun i => S.getD i 0) = S := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using h1 : i < S.length)]
  have hv4 : ∀ x, x ∉ (forUp "i" (.var "xp") (.write (.get "x" (.var "i")))).wvars →
      τ4.vars x = τ3.vars x := fun x h => r4.frame_var x h
  obtain ⟨τ5, r5, hy5, hd5, ha5, ho5⟩ := walk_run (B := B) (X := S ++ D) (p := p) (j := j) (ws := ws)
    (r := r ++ D) (τ := τ4) ha4 (by rw [hv4 _ (by decide)]; simpa [hτ3, hτ2, hτ1] using hp)
    (by rw [hv4 _ (by decide)]; simpa [hτ3, hτ2, hτ1] using hj) hjl.le hXd (by omega)
  rw [frames_drop hjl] at hd5
  have hft : (frames (ws.take j)).length + 1 + ws[j].length ≤ (frames ws).length := by
    rw [← length_frames_take_succ hjl, ← frames_take_drop ws (j + 1)]; simp
  have hmem : ∀ v ∈ ws[j], v < B := by
    intro v hv
    apply hvB
    have h1 : v ∈ frames ws := List.mem_flatten.mpr
      ⟨ws[j].length :: ws[j], List.mem_map.mpr ⟨ws[j], List.getElem_mem hjl, rfl⟩,
        List.mem_cons_of_mem _ hv⟩
    have h2 : v ∈ S.drop p := by rw [hdrop]; exact List.mem_append_left _ h1
    exact List.mem_of_mem_drop h2
  obtain ⟨τ6, r6, ho6, -⟩ := wFrame_run (B := B) (X := S ++ D) (u := ws[j])
    (r := frames (ws.drop (j + 1)) ++ (r ++ D)) (τ := τ5) (by rw [ha5, ha4]) hy5
    (by rw [← hy5, hd5]; simp) (by omega) hmem
  have hrun : Run B tail τ τ6 (60 * S.length + 60) := by
    unfold tail
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 r6))))).mono ?_
    have : ws[j].length ≤ S.length := by omega
    have : j ≤ S.length := by have := length_frames ws; omega
    simp only [Expr.size]; omega
  refine ⟨τ6, hrun, ?_⟩
  rw [ho6, ho5, ho4, hmap]; simp [hτ3, hτ2, hτ1]

end Lax185574Proofs.StpRam
