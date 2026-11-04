import Lax185574Proofs.ResolveRam.Glue.Tail

/-!
Writing the query of the switch in a later round of the glue program of
lem:resolve-lift.

The query of the switch is `sw5In qA qB qC qE qF`: the lengths of
`swIn qA qB qC`, `qE` and `qF`, then `swIn qA qB qC` (the lengths of
`qA`, `qB`, `qC` and the three words), `qE` and `qF`. `wrQ cA cB cC cE`
writes six placeholders, then the four words by the commands `cA`, `cB`,
`cC`, `cE` and the fixed query of slot F, and then the six lengths from
the positions where the words start (`wrQ_run`). The commands of the
slots are given by their effect (`SlotRun`): from any state with the
invariant `P` they append their word and keep `P` and the positions.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574Proofs.ResolveRam

/-- The positions of the query. -/
def qN : List String := ["q0", "a0", "b0", "c0", "e0", "f0", "W"]

/-- A command that appends the word `w`, keeping `P`, the positions and
the length of the buffer, within `K` steps. -/
def SlotRun (W S Xm : ℕ) (c : Com) (w : List ℕ) (P P' : Env → Prop) (K : ℕ) : Prop :=
  ∀ (σ : Env) (X : List ℕ), P σ → Filled "OB" "po" X σ → (σ.arrs "OB").length = W + 1 →
    X.length + w.length + S + 1 ≤ W → X.length ≤ Xm →
    ∃ σ', Run (W + 1) c σ σ' K ∧ Filled "OB" "po" (X ++ w) σ' ∧ P' σ' ∧
      (∀ y ∈ qN, σ'.vars y = σ.vars y) ∧ (σ'.arrs "OB").length = (σ.arrs "OB").length ∧
      σ'.out = σ.out

/-- The fixed words are slots too. -/
theorem slot_lits {W S Xm : ℕ} {w : List ℕ} {P : Env → Prop} (hw : ∀ v ∈ w, v ≤ W)
    (hP : ∀ σ σ', P σ → OFr σ σ' ["po"] → P σ') :
    SlotRun W S Xm (pushLits w) w P P (1 + 8 * w.length) := by
  intro σ X hσ hF hc hl _
  obtain ⟨σ', r, F, o⟩ := pushLits_run (W := W) (l := w) hF hw (by omega) (by omega)
  exact ⟨σ', r, F, hP σ σ' hσ o, fun y hy => o.vars y (by intro h; simp at h; subst h; revert hy; decide),
    o.len, o.out⟩

/-- Write the query of the switch. -/
noncomputable def wrQ (cA cB cC cE : Com) : Com :=
  .seq (.assign "q0" (.var "po")) (.seq (pushLits [0, 0, 0, 0, 0, 0])
  (.seq (.assign "a0" (.var "po")) (.seq cA (.seq (.assign "b0" (.var "po")) (.seq cB
  (.seq (.assign "c0" (.var "po")) (.seq cC (.seq (.assign "e0" (.var "po")) (.seq cE
  (.seq (.assign "f0" (.var "po")) (.seq (pushLits qF0)
  (.seq (.store "OB" (.var "q0") (.sub (.var "e0") (.add (.var "q0") (.lit 3))))
  (.seq (.store "OB" (.add (.var "q0") (.lit 1)) (.sub (.var "f0") (.var "e0")))
  (.seq (.store "OB" (.add (.var "q0") (.lit 2)) (.sub (.var "po") (.var "f0")))
  (.seq (.store "OB" (.add (.var "q0") (.lit 3)) (.sub (.var "b0") (.var "a0")))
  (.seq (.store "OB" (.add (.var "q0") (.lit 4)) (.sub (.var "c0") (.var "b0")))
    (.store "OB" (.add (.var "q0") (.lit 5)) (.sub (.var "e0") (.var "c0")))))))))))))))))))

/-- A position assignment `x := po`, with the buffer kept. -/
theorem pos_run {W : ℕ} {x : String} {X : List ℕ} {σ : Env} (hx : x ≠ "po") (hF : Filled "OB" "po" X σ)
    (hl : X.length ≤ W) :
    ∃ σ', Run (W + 1) (.assign x (.var "po")) σ σ' 2 ∧ Only x X.length σ σ' ∧ Filled "OB" "po" X σ' := by
  obtain ⟨σ', r, o⟩ := asg_run (x := x) (ev_var (B := W + 1) hF.pos (by omega))
  exact ⟨σ', r, o, hF.congr (by rw [o.vars _ (Ne.symm hx)]) (by rw [o.arrs])⟩

theorem sw5In_eq (A B C E F : List ℕ) :
    sw5In A B C E F = [3 + A.length + B.length + C.length, E.length, F.length] ++
      ([A.length, B.length, C.length] ++ A ++ B ++ C) ++ E ++ F := by
  simp [sw5In, swIn]; omega

/-- A store at a position `q0 + i` with value `v`. -/
theorem qPatch_run {W : ℕ} {pre F : List ℕ} {x v q i : ℕ} {ie ve : Expr} {σ : Env}
    (hF : Filled "OB" "po" (pre ++ x :: F) σ) (hq : pre.length = q + i)
    (hi : ie.evalB (W + 1) σ = some (q + i)) (hv : ve.evalB (W + 1) σ = some v)
    (hc : q + i < (σ.arrs "OB").length) :
    ∃ σ', Run (W + 1) (.store "OB" ie ve) σ σ' (1 + ie.size + ve.size) ∧
      Filled "OB" "po" (pre ++ v :: F) σ' ∧ (∀ y, σ'.vars y = σ.vars y) ∧
      (σ'.arrs "OB").length = (σ.arrs "OB").length ∧ (∀ b, b ≠ "OB" → σ'.arrs b = σ.arrs b) ∧
      σ'.out = σ.out ∧ σ'.inp = σ.inp := by
  refine ⟨_, Run.store hi hv hc, ?_, fun _ => by simp, by simp, fun b hb => by simp [hb], by simp, by simp⟩
  have := hF.patch (v := v) (by rw [hq]; exact hc)
  rwa [hq] at this

/-- The scalars that the positions of `wrQ` change. -/
def qW : List String := ["po", "q0", "a0", "b0", "c0", "e0", "f0"]

set_option maxHeartbeats 1000000 in
/-- **Writing the query of the switch.** -/
theorem wrQ_run {W S Xm KA KB KC KE : ℕ} {cA cB cC cE : Com} {wA wB wC wE : List ℕ}
    {P0 P1 P2 P3 P : Env → Prop} {σ : Env} {pre : List ℕ}
    (hA : SlotRun W S Xm cA wA P0 P1 KA) (hB : SlotRun W S Xm cB wB P1 P2 KB) (hC : SlotRun W S Xm cC wC P2 P3 KC)
    (hE : SlotRun W S Xm cE wE P3 P KE) (hFl : ∀ v ∈ qF0, v ≤ W)
    (hP0 : ∀ σ σ', P0 σ → OFr σ σ' qW → P0 σ') (hP1 : ∀ σ σ', P1 σ → OFr σ σ' qW → P1 σ')
    (hP2 : ∀ σ σ', P2 σ → OFr σ σ' qW → P2 σ') (hP3 : ∀ σ σ', P3 σ → OFr σ σ' qW → P3 σ')
    (hP : ∀ σ σ', P σ → OFr σ σ' qW → P σ') (hσ : P0 σ) (hF : Filled "OB" "po" pre σ)
    (hcap : (σ.arrs "OB").length = W + 1)
    (hl : pre.length + 6 + wA.length + wB.length + wC.length + wE.length + qF0.length + S + 1 ≤ W)
    (hXm : pre.length + 6 + wA.length + wB.length + wC.length ≤ Xm) :
    ∃ σ', Run (W + 1) (wrQ cA cB cC cE) σ σ' (KA + KB + KC + KE + 8 * qF0.length + 200) ∧
      Filled "OB" "po" (pre ++ sw5In wA wB wC wE qF0) σ' ∧ P σ' ∧
      σ'.vars "a0" = pre.length + 6 ∧ σ'.vars "b0" = pre.length + 6 + wA.length ∧
      σ'.vars "c0" = pre.length + 6 + wA.length + wB.length ∧
      σ'.vars "e0" = pre.length + 6 + wA.length + wB.length + wC.length ∧
      (σ'.arrs "OB").length = W + 1 ∧ σ'.out = σ.out := by
  have mk : ∀ (Q : Env → Prop), (∀ σ σ', Q σ → OFr σ σ' qW → Q σ') →
      ∀ σ σ' (xs : List String), Q σ → OFr σ σ' xs → (∀ y ∈ xs, y ∈ qW) → Q σ' :=
    fun Q hQ σ σ' xs h o hs => hQ σ σ' h (o.mono hs)
  have only_ofr : ∀ {x v} {σ σ' : Env}, Only x v σ σ' → OFr σ σ' [x] := fun o =>
    ⟨fun y hy => o.vars y (by simpa using hy), fun b _ => by rw [o.arrs], by rw [o.arrs], o.out, o.inp⟩
  -- q0
  obtain ⟨σ1, r1, o1, F1⟩ := pos_run (W := W) (x := "q0") (by decide) hF (by omega)
  have H1 := mk P0 hP0 _ _ _ hσ (only_ofr o1) (by decide)
  obtain ⟨σ2, r2, F2, O2⟩ := pushLits_run (W := W) (l := [0, 0, 0, 0, 0, 0]) F1 (by simp)
    (by rw [o1.arrs, hcap]; simp; omega) (by simp; omega)
  have H2 := mk P0 hP0 _ _ _ H1 O2 (by decide)
  have c2 : (σ2.arrs "OB").length = W + 1 := by rw [O2.len, o1.arrs, hcap]
  -- a0 and slot A
  obtain ⟨σ3, r3, o3, F3⟩ := pos_run (W := W) (x := "a0") (by decide) F2 (by simp; omega)
  have H3 := mk P0 hP0 _ _ _ H2 (only_ofr o3) (by decide)
  obtain ⟨σ4, r4, F4, H4, q4, l4, su4⟩ := hA σ3 _ H3 F3 (by rw [o3.arrs, c2]) (by simp; omega) (by simp; omega)
  -- b0 and slot B
  obtain ⟨σ5, r5, o5, F5⟩ := pos_run (W := W) (x := "b0") (by decide) F4 (by simp; omega)
  have H5 := mk P1 hP1 _ _ _ H4 (only_ofr o5) (by decide)
  obtain ⟨σ6, r6, F6, H6, q6, l6, su6⟩ := hB σ5 _ H5 F5 (by rw [o5.arrs, l4, o3.arrs, c2]) (by simp; omega)
    (by simp; omega)
  -- c0 and slot C
  obtain ⟨σ7, r7, o7, F7⟩ := pos_run (W := W) (x := "c0") (by decide) F6 (by simp; omega)
  have H7 := mk P2 hP2 _ _ _ H6 (only_ofr o7) (by decide)
  obtain ⟨σ8, r8, F8, H8, q8, l8, su8⟩ := hC σ7 _ H7 F7 (by rw [o7.arrs, l6, o5.arrs, l4, o3.arrs, c2])
    (by simp; omega) (by simp; omega)
  -- e0 and slot E
  obtain ⟨σ9, r9, o9, F9⟩ := pos_run (W := W) (x := "e0") (by decide) F8 (by simp; omega)
  have H9 := mk P3 hP3 _ _ _ H8 (only_ofr o9) (by decide)
  obtain ⟨σ10, r10, F10, H10, q10, l10, su10⟩ := hE σ9 _ H9 F9
    (by rw [o9.arrs, l8, o7.arrs, l6, o5.arrs, l4, o3.arrs, c2]) (by simp; omega) (by simp; omega)
  have c10 : (σ10.arrs "OB").length = W + 1 := by rw [l10, o9.arrs, l8, o7.arrs, l6, o5.arrs, l4, o3.arrs, c2]
  -- f0 and slot F
  obtain ⟨σ11, r11, o11, F11⟩ := pos_run (W := W) (x := "f0") (by decide) F10 (by simp; omega)
  obtain ⟨σ12, r12, F12, O12⟩ := pushLits_run (W := W) (l := qF0) F11 hFl
    (by rw [o11.arrs, c10]; simp; omega) (by simp; omega)
  have H12 := mk P hP _ _ _ (mk P hP _ _ _ H10 (only_ofr o11) (by decide)) O12 (by decide)
  have c12 : (σ12.arrs "OB").length = W + 1 := by rw [O12.len, o11.arrs, c10]
  -- the positions
  set n := pre.length
  have v12 : ∀ y ∈ ["q0", "a0", "b0", "c0", "e0", "f0"], σ12.vars y = σ11.vars y := fun y hy =>
    O12.vars y (by intro h; simp at h; subst h; revert hy; decide)
  have hq0 : σ12.vars "q0" = n := by
    rw [v12 _ (by decide), o11.vars _ (by decide), q10 _ (by decide), o9.vars _ (by decide),
      q8 _ (by decide), o7.vars _ (by decide), q6 _ (by decide), o5.vars _ (by decide), q4 _ (by decide),
      o3.vars _ (by decide), O2.vars _ (by decide), o1.self]
  have ha0 : σ12.vars "a0" = n + 6 := by
    rw [v12 _ (by decide), o11.vars _ (by decide), q10 _ (by decide), o9.vars _ (by decide),
      q8 _ (by decide), o7.vars _ (by decide), q6 _ (by decide), o5.vars _ (by decide), q4 _ (by decide),
      o3.self]; simp [n]
  have hb0 : σ12.vars "b0" = n + 6 + wA.length := by
    rw [v12 _ (by decide), o11.vars _ (by decide), q10 _ (by decide), o9.vars _ (by decide),
      q8 _ (by decide), o7.vars _ (by decide), q6 _ (by decide), o5.self]; simp [n]; omega
  have hc0 : σ12.vars "c0" = n + 6 + wA.length + wB.length := by
    rw [v12 _ (by decide), o11.vars _ (by decide), q10 _ (by decide), o9.vars _ (by decide),
      q8 _ (by decide), o7.self]; simp [n]; omega
  have he0 : σ12.vars "e0" = n + 6 + wA.length + wB.length + wC.length := by
    rw [v12 _ (by decide), o11.vars _ (by decide), q10 _ (by decide), o9.self]; simp [n]; omega
  have hf0 : σ12.vars "f0" = n + 6 + wA.length + wB.length + wC.length + wE.length := by
    rw [v12 _ (by decide), o11.self]; simp [n]; omega
  have hpo : σ12.vars "po" = n + 6 + wA.length + wB.length + wC.length + wE.length + qF0.length := by
    rw [F12.pos]; simp [n]; omega
  set R := wA ++ wB ++ wC ++ wE ++ qF0
  have hR : R.length = wA.length + wB.length + wC.length + wE.length + qF0.length := by simp [R]; omega
  have hWn : n + 6 + R.length + 1 ≤ W := by omega
  have G0 : Filled "OB" "po" (pre ++ 0 :: ([0, 0, 0, 0, 0] ++ R)) σ12 := by simpa [R] using F12
  have ev : ∀ (ρ : Env) (i : ℕ), (∀ y, ρ.vars y = σ12.vars y) → i ≤ 5 →
      (Expr.add (.var "q0") (.lit i)).evalB (W + 1) ρ = some (n + i) := fun ρ i h hi =>
    ev_add (ev_var (by rw [h, hq0]) (by omega)) (evalB_lit (by omega)) (by omega)
  have evv : ∀ (ρ : Env) (x : String) (a : ℕ), (∀ y, ρ.vars y = σ12.vars y) → σ12.vars x = a →
      a ≤ n + 6 + R.length → (Expr.var x).evalB (W + 1) ρ = some a := fun ρ x a h ha hl =>
    ev_var (by rw [h, ha]) (by omega)
  set A := wA.length; set B := wB.length; set C := wC.length; set E := wE.length; set F := qF0.length
  -- six patches
  obtain ⟨ρ1, s1, G1, v1, l1, a1, u1, i1⟩ := qPatch_run (W := W) (q := n) (i := 0) (v := 3 + A + B + C) G0
    (by simp [n]) (by rw [Nat.add_zero]; exact evv σ12 "q0" n (fun _ => rfl) hq0 (by omega))
    (ev_sub (evv σ12 "e0" _ (fun _ => rfl) he0 (by omega))
      (ev_add (evv σ12 "q0" _ (fun _ => rfl) hq0 (by omega)) (evalB_lit (n := 3) (by omega)) (by omega))
      (by omega) |>.trans (by congr 1; omega)) (by rw [c12]; omega)
  have w1 : ∀ y, ρ1.vars y = σ12.vars y := v1
  have G1' : Filled "OB" "po" ((pre ++ [3 + A + B + C]) ++ 0 :: ([0, 0, 0, 0] ++ R)) ρ1 := by simpa using G1
  obtain ⟨ρ2, s2, G2, v2, l2, a2, u2, i2⟩ := qPatch_run (W := W) (q := n) (i := 1) (v := E) G1'
    (by simp [n]) (ev ρ1 1 w1 (by omega))
    (ev_sub (evv ρ1 "f0" _ w1 hf0 (by omega)) (evv ρ1 "e0" _ w1 he0 (by omega)) (by omega) |>.trans
      (by congr 1; omega)) (by rw [l1, c12]; omega)
  have w2 : ∀ y, ρ2.vars y = σ12.vars y := fun y => by rw [v2, w1]
  have G2' : Filled "OB" "po" ((pre ++ [3 + A + B + C, E]) ++ 0 :: ([0, 0, 0] ++ R)) ρ2 := by simpa using G2
  obtain ⟨ρ3, s3, G3, v3, l3, a3, u3, i3⟩ := qPatch_run (W := W) (q := n) (i := 2) (v := F) G2'
    (by simp [n]) (ev ρ2 2 w2 (by omega))
    (ev_sub (evv ρ2 "po" _ w2 hpo (by omega)) (evv ρ2 "f0" _ w2 hf0 (by omega)) (by omega) |>.trans
      (by congr 1; omega)) (by rw [l2, l1, c12]; omega)
  have w3 : ∀ y, ρ3.vars y = σ12.vars y := fun y => by rw [v3, w2]
  have G3' : Filled "OB" "po" ((pre ++ [3 + A + B + C, E, F]) ++ 0 :: ([0, 0] ++ R)) ρ3 := by simpa using G3
  obtain ⟨ρ4, s4, G4, v4, l4, a4, u4, i4⟩ := qPatch_run (W := W) (q := n) (i := 3) (v := A) G3'
    (by simp [n]) (ev ρ3 3 w3 (by omega))
    (ev_sub (evv ρ3 "b0" _ w3 hb0 (by omega)) (evv ρ3 "a0" _ w3 ha0 (by omega)) (by omega) |>.trans
      (by congr 1; omega)) (by rw [l3, l2, l1, c12]; omega)
  have w4 : ∀ y, ρ4.vars y = σ12.vars y := fun y => by rw [v4, w3]
  have G4' : Filled "OB" "po" ((pre ++ [3 + A + B + C, E, F, A]) ++ 0 :: ([0] ++ R)) ρ4 := by simpa using G4
  obtain ⟨ρ5, s5, G5, v5, l5, a5, u5, i5⟩ := qPatch_run (W := W) (q := n) (i := 4) (v := B) G4'
    (by simp [n]) (ev ρ4 4 w4 (by omega))
    (ev_sub (evv ρ4 "c0" _ w4 hc0 (by omega)) (evv ρ4 "b0" _ w4 hb0 (by omega)) (by omega) |>.trans
      (by congr 1; omega)) (by rw [l4, l3, l2, l1, c12]; omega)
  have w5 : ∀ y, ρ5.vars y = σ12.vars y := fun y => by rw [v5, w4]
  have G5' : Filled "OB" "po" ((pre ++ [3 + A + B + C, E, F, A, B]) ++ 0 :: R) ρ5 := by simpa using G5
  obtain ⟨ρ6, s6, G6, v6, l6, a6, u6, i6⟩ := qPatch_run (W := W) (q := n) (i := 5) (v := C) G5'
    (by simp [n]) (ev ρ5 5 w5 (by omega))
    (ev_sub (evv ρ5 "e0" _ w5 he0 (by omega)) (evv ρ5 "c0" _ w5 hc0 (by omega)) (by omega) |>.trans
      (by congr 1; omega)) (by rw [l5, l4, l3, l2, l1, c12]; omega)
  have w6 : ∀ y, ρ6.vars y = σ12.vars y := fun y => by rw [v6, w5]
  have hfin : (pre ++ [3 + A + B + C, E, F, A, B]) ++ C :: R = pre ++ sw5In wA wB wC wE qF0 := by
    rw [sw5In_eq]; simp [R, A, B, C, E, F]
  rw [hfin] at G6
  have ea6 : ∀ b, b ≠ "OB" → ρ6.arrs b = σ12.arrs b := fun b hb => by
    rw [a6 b hb, a5 b hb, a4 b hb, a3 b hb, a2 b hb, a1 b hb]
  refine ⟨ρ6, ?_, G6, ?_, by rw [w6, ha0], by rw [w6, hb0], by rw [w6, hc0], by rw [w6, he0],
    by rw [l6, l5, l4, l3, l2, l1, c12], ?_⟩
  · unfold wrQ
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7
      (Run.seq r8 (Run.seq r9 (Run.seq r10 (Run.seq r11 (Run.seq r12 (Run.seq s1 (Run.seq s2
      (Run.seq s3 (Run.seq s4 (Run.seq s5 s6))))))))))))))))).mono ?_
    simp only [Expr.size, List.length_cons, List.length_nil]
    omega
  · refine hP σ12 ρ6 H12 ⟨fun y _ => w6 y, ea6, by rw [l6, l5, l4, l3, l2, l1], ?_, ?_⟩
    · rw [u6, u5, u4, u3, u2, u1]
    · rw [i6, i5, i4, i3, i2, i1]
  · rw [u6, u5, u4, u3, u2, u1, O12.out, o11.out, su10, o9.out, su8, o7.out, su6, o5.out, su4, o3.out,
      O2.out, o1.out]

end Lax185574Proofs.ResolveRam.Glue
