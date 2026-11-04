import Lax185574Proofs.ResolveRam.Glue.CFEKit

/-!
The end of the last round of the glue program of lem:resolve-lift.

After the last call the round has the input `x` of the composite as its
window, the state at the last position and the answer of the last
canonical form. `fECmd` writes `0`, the word of the resolved graph and
the word of its distance matrix (the piece `hCmd`), `n`, the output words of level `0` that the state
holds (the last `ii` words of the library), the entries `k, q, ℓ` of the
tree of the last item of level `0`, the answer on its atom words (the
library word with index `2`) and the answer of the last canonical form,
and then checks the entries and writes the buffer (`finEnd`).
`fECmd_gen`: from the environment after the start of the round the
command writes `feOut` and sets `ovf` exactly when an entry is too big.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.ResolveLift Lax185574Proofs.ResolveRam

/-- The constant of the piece of the resolved graph. -/
noncomputable def cH : ℕ := Classical.choose hCmd_spec

theorem cH_spec : ∀ (W k₀ q₀ : ℕ) {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (τ : Env)
    (pre : List ℕ),
    τ.vars "W" = W → ArrW W τ → PreAt "x" (xIn G k₀ q₀ P Q s) τ →
    τ.vars "nx" = (xIn G k₀ q₀ P Q s).length → τ.vars "gn" = n → τ.vars "gP" = P →
    τ.vars "gQ" = Q → τ.vars "gS" = (if s then 1 else 0) → Filled "OB" "po" pre τ →
    Room W 0 (ySz (xIn G k₀ q₀ P Q s) + pre.length) →
    ∃ τ', Run (W + 1) hCmd τ τ' (cH * ((xIn G k₀ q₀ P Q s).length + 1)) ∧
      Filled "OB" "po" (pre ++ hWord G s P Q) τ' ∧ PFr hCV τ τ' :=
  Classical.choose_spec hCmd_spec

/-- The offset of the answer of a canonical form in the answer of the switch. -/
noncomputable def fePl : ℕ := preLen (.canon [])

/-- The number of fixed answers around the answer of a canonical form. -/
noncomputable def feDl : ℕ := dLen (.canon [])

theorem fePl_le : fePl ≤ feDl := by simp [fePl, feDl, preLen, dLen]; omega

/-- **The end of the last round.** -/
noncomputable def fECmd : Com :=
  .seq (push1 "OB" "po" (.lit 0)) (.seq hCmd (.seq (push1 "OB" "po" (.var "gn"))
    (.seq feOU (.seq feHd (.seq feAT (.seq (feY fePl feDl) finEnd))))))

/-- The output of the last round, from the word `H` of the resolved graph
and its distance matrix (`hWord`), `n`, the number `i` of output words
of level `0` in the library, the index `iw` of the word of the last item,
the library and the answer. -/
noncomputable def feOut (H : List ℕ) (n i iw : ℕ) (ws : List (List ℕ)) (b : List ℕ) : List ℕ :=
  0 :: H ++ n :: ((ws.drop (ws.length - i)).flatten ++ ((ws.getD iw []).drop 2).take 3 ++
    ws.getD 2 [] ++ (b.drop fePl).take (b.length - feDl))

/-- The cost of the end of the last round. -/
noncomputable def feK (n xl : ℕ) (ws : List (List ℕ)) (b o : List ℕ) : ℕ :=
  cH * (xl + 1) + 40 * total ws + 20 * b.length + 42 * o.length + 300

theorem filled_le {W : ℕ} {o : List ℕ} {τ : Env} (hF : Filled "OB" "po" o τ) (hlt : EnvLt (W + 1) τ) :
    ∀ v ∈ o, v ≤ W := by
  intro v hv
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hv
  have := hlt.arrs "OB" _ (List.mem_of_getElem? (hF.get i hi))
  omega

theorem ofr_arrW {W : ℕ} {τ τ' : Env} {xs : List String} (h : OFr τ τ' xs) (ha : ArrW W τ) : ArrW W τ' := by
  intro b
  by_cases hb : b = "OB"
  · subst hb; rw [h.len]; exact ha _
  · rw [h.arrs b hb]; exact ha b

theorem ofr_lib {ws : List (List ℕ)} {τ τ' : Env} {xs : List String} (h : OFr τ τ' xs) (hm : "m" ∉ xs)
    (hl : "lt" ∉ xs) (hL : Lib ws τ) : Lib ws τ' :=
  hL.of (h.vars _ hm) (h.vars _ hl) (h.arrs _ (by decide)) (h.arrs _ (by decide)) (h.arrs _ (by decide))

set_option maxHeartbeats 1600000 in
/-- **The end of the last round.** -/
theorem fECmd_gen {W R i iw : ℕ} {n : ℕ} {G : PartialGraph (Fin n)} {k₀ q₀ P Q : ℕ} {s : Bool}
    {sc b : List ℕ} {ws : List (List ℕ)} {τ : Env}
    (hP : PreR W R sc ws (xIn G k₀ q₀ P Q s) b τ) (hov : τ.vars "ovf" = 0) (hR1 : 1 ≤ R)
    (hs2 : sc.getD 2 0 = (xIn G k₀ q₀ P Q s).length) (hs3 : sc.getD 3 0 = n) (hs4 : sc.getD 4 0 = P)
    (hs5 : sc.getD 5 0 = Q) (hs6 : sc.getD 6 0 = if s then 1 else 0) (hs11 : sc.getD 11 0 = i)
    (hil : i ≤ ws.length) (hiw : 4 + sc.getD 13 0 + sc.getD 14 0 + sc.getD 15 0 + i = iw)
    (hiwl : iw < ws.length) (h5 : 5 ≤ (ws.getD iw []).length) (h3 : 3 ≤ ws.length)
    (hdl : feDl ≤ b.length) :
    ∃ τ' k, Run (W + 1) fECmd τ τ' k ∧
      k ≤ feK n (xIn G k₀ q₀ P Q s).length ws b (feOut (hWord G s P Q) n i iw ws b) ∧
      τ'.out = feOut (hWord G s P Q) n i iw ws b ∧
      τ'.vars "ovf" = if maxEntry (feOut (hWord G s P Q) n i iw ws b) < W / 32 / 32
        then 0 else 1 := by
  set x := xIn G k₀ q₀ P Q s with hx
  set H := hWord G s P Q with hH
  set o := feOut H n i iw ws b with ho
  have hroom : RoomOK W R τ ws b := by
    have := hP.hroom; rw [hov] at this; split_ifs at this with h; exact h
  have hsv := sOfV_ge (τ := τ) (ws := ws) (b := b)
  have hnx : τ.vars "nx" = x.length := (hP.hsc 2 (by omega)).trans hs2
  have hgn : τ.vars "gn" = n := (hP.hsc 3 (by omega)).trans hs3
  have hgP : τ.vars "gP" = P := (hP.hsc 4 (by omega)).trans hs4
  have hgQ : τ.vars "gQ" = Q := (hP.hsc 5 (by omega)).trans hs5
  have hgS : τ.vars "gS" = if s then 1 else 0 := (hP.hsc 6 (by omega)).trans hs6
  have hii : τ.vars "ii" = i := (hP.hsc 11 (by omega)).trans hs11
  have hSG : τ.vars "nSG" = sc.getD 13 0 := hP.hsc 13 (by omega)
  have hFA : τ.vars "nFA" = sc.getD 14 0 := hP.hsc 14 (by omega)
  have hCO : τ.vars "nCO" = sc.getD 15 0 := hP.hsc 15 (by omega)
  -- sizes
  set S := sOfV τ ws b
  have hSW : 2 ^ 24 * S * S < W := by
    have h1 : 1 ≤ R * R * R * R := Nat.one_le_iff_ne_zero.2 (by positivity)
    have : 2 ^ 24 * S * S ≤ 2 ^ 24 * R * R * R * R * S * S := by
      have := Nat.mul_le_mul_left (2 ^ 24 * S * S) h1
      calc 2 ^ 24 * S * S = 2 ^ 24 * S * S * 1 := by ring
        _ ≤ 2 ^ 24 * S * S * (R * R * R * R) := this
        _ = _ := by ring
    exact lt_of_le_of_lt this hroom
  have hxn : n + 1 ≤ x.length := by
    have := xIn_len (G := G) (k₀ := k₀) (q₀ := q₀) (P := P) (Q := Q) (s := s); rw [hx]; omega
  have hHl : H.length ≤ 6 * ((n + 1) * (n + 1)) := length_hWord_le G s P Q
  have hxS : x.length + 64 ≤ S := by rw [← hnx]; omega
  have hmS : maxEntry x ≤ S := by rw [← hP.hmw]; exact hsv.2.2.2
  have hnS : (n + 1) * (n + 1) ≤ S * S := Nat.mul_le_mul (by omega) (by omega)
  have h64 : 64 * S ≤ S * S := Nat.mul_le_mul_right _ (by omega)
  have hSb : 2 ^ 20 * S ≤ W := by nlinarith
  have hHW : 2 ^ 20 * H.length ≤ W := by nlinarith
  have hwsS : 2 * total ws + 2 * ws.length + b.length + 64 ≤ S := by omega
  have hlen2 : (ws.getD 2 []).length ≤ total ws := by
    have : ws.getD 2 [] = ws[2] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show 2 < ws.length by omega)]
    rw [this]; exact len_le_total (by omega)
  have hflat : ((ws.drop (ws.length - i)).flatten).length ≤ total ws := by
    have := total_le_of_sub (List.drop_sublist (ws.length - i) ws); exact this
  have hol : o.length ≤ H.length + total ws + total ws + b.length + 5 := by
    simp only [o, feOut, List.length_cons, List.length_append, List.length_take, List.length_drop]
    omega
  have hW64 : 2 ^ 10 * (o.length + 64) ≤ W := by omega
  -- step 1: push 0
  have hF0 : Filled "OB" "po" [] τ := ⟨by rw [hP.hpo]; rfl, fun i h => absurd h (by simp)⟩
  obtain ⟨τ1, r1, F1, O1⟩ := push1_ofr (W := W) (e := .lit 0) hF0 (evalB_lit (by omega))
    (by rw [hP.harr "OB"]; simp) (by simp; omega)
  have ar1 := ofr_arrW O1 hP.harr
  -- step 2: the resolved graph
  have hRm : Room W 0 (ySz x + ([] ++ [0]).length) := by
    refine room_of_ok hroom (by omega) ?_
    unfold ySz; simp; omega
  obtain ⟨τ2, r2, F2, P2⟩ := cH_spec W k₀ q₀ G P Q s τ1 ([] ++ [0])
    (by rw [O1.vars _ (by decide), hP.hW]) ar1
    (fun j hj => by rw [O1.arrs _ (by decide)]; exact hP.hx j hj)
    (by rw [O1.vars _ (by decide), hnx]) (by rw [O1.vars _ (by decide), hgn])
    (by rw [O1.vars _ (by decide), hgP]) (by rw [O1.vars _ (by decide), hgQ])
    (by rw [O1.vars _ (by decide), hgS]) F1 hRm
  rw [← hH] at F2
  rw [← hx] at r2
  have ar2 : ArrW W τ2 := fun b' => by rw [P2.len]; exact ar1 b'
  have hlt1 : EnvLt (W + 1) τ1 := Run.envLt r1 hP.hlt
  have hlt2 : EnvLt (W + 1) τ2 := Run.envLt r2 hlt1
  have v2 : ∀ y, y ∉ hCV → y ≠ "po" → τ2.vars y = τ.vars y := fun y hy hp => by
    rw [P2.vars y hy, O1.vars y (by simpa using hp)]
  have L2 : Lib ws τ2 := hP.hlib.of (by rw [v2 "m" (by decide) (by decide)])
    (by rw [v2 "lt" (by decide) (by decide)])
    (by rw [P2.arrs "a" (by decide), O1.arrs _ (by decide)]) (by rw [P2.arrs "st" (by decide), O1.arrs _ (by decide)])
    (by rw [P2.arrs "ln" (by decide), O1.arrs _ (by decide)])
  -- step 3: push n
  obtain ⟨τ3, r3, F3, O3⟩ := push1_ofr (W := W) (e := .var "gn") (v := n) F2
    (ev_var (by rw [v2 "gn" (by decide) (by decide), hgn]) (by omega))
    (by rw [ar2 "OB"]; simp; omega) (by simp; omega)
  -- step 4: the output words of level 0
  have hlt3 : EnvLt (W + 1) τ3 := Run.envLt r3 hlt2
  obtain ⟨τ4, r4, F4, O4⟩ := feOU_run (W := W) (i := i) (ofr_lib O3 (by decide) (by decide) L2)
    (by rw [O3.vars _ (by decide), v2 "ii" (by decide) (by decide), hii]) hil F3 hlt3 (ofr_arrW O3 ar2)
    (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  -- step 5: the head of the tree of the last item
  have O34 := O3.trans O4
  have hlt4 : EnvLt (W + 1) τ4 := Run.envLt r4 hlt3
  obtain ⟨τ5, r5, F5, O5⟩ := feHd_run (W := W) (iw := iw) (ofr_lib O34 (by decide) (by decide) L2)
    (by rw [O34.vars _ (by decide), v2 "nSG" (by decide) (by decide), hSG])
    (by rw [O34.vars _ (by decide), v2 "nFA" (by decide) (by decide), hFA])
    (by rw [O34.vars _ (by decide), v2 "nCO" (by decide) (by decide), hCO])
    (by rw [O34.vars _ (by decide), v2 "ii" (by decide) (by decide), hii]) hiw hiwl h5 F4 hlt4
    (ofr_arrW O34 ar2) (by simp only [List.length_append, List.length_cons, List.length_nil]; omega)
  -- step 6: the answer on the atom words
  have O35 := O34.trans O5
  have hlt5 : EnvLt (W + 1) τ5 := Run.envLt r5 hlt4
  obtain ⟨τ6, r6, F6, O6⟩ := feAT_run (W := W) (ofr_lib O35 (by decide) (by decide) L2) h3 F5 hlt5
    (ofr_arrW O35 ar2) (by simp only [List.length_append, List.length_cons, List.length_nil, List.length_take, List.length_drop]; omega)
  -- step 7: the answer of the last call
  have O36 := O35.trans O6
  have hlt6 : EnvLt (W + 1) τ6 := Run.envLt r6 hlt5
  have hy6 : SegAt "y" 0 b τ6 := fun j hj => by
    rw [O36.arrs _ (by decide), P2.arrs "y" (by decide), O1.arrs _ (by decide)]; exact hP.hy j hj
  obtain ⟨τ7, r7, F7, O7⟩ := feY_run (W := W) (b := b)
    (by rw [O36.vars _ (by decide), v2 "bl" (by decide) (by decide), hP.hbl]) hy6 fePl_le hdl F6 hlt6
    (ofr_arrW O36 ar2) (by simp only [List.length_append, List.length_cons, List.length_nil, List.length_take, List.length_drop]; omega)
  -- step 8: check and write
  have O37 := O36.trans O7
  have hlt7 : EnvLt (W + 1) τ7 := Run.envLt r7 hlt6
  have hoe : [] ++ [0] ++ H ++ [n] ++ (ws.drop (ws.length - i)).flatten ++ ((ws.getD iw []).drop 2).take 3 ++
      ws.getD 2 [] ++ (b.drop fePl).take (b.length - feDl) = o := by
    simp [o, feOut]
  rw [hoe] at F7
  obtain ⟨τ8, r8, o8, ov8⟩ := finEnd_run (W := W) (o := o)
    (by rw [O37.vars _ (by decide), v2 "W" (by decide) (by decide), hP.hW]) (by omega) F7 (by omega)
    (filled_le F7 hlt7) (by rw [O37.vars _ (by decide), v2 "ovf" (by decide) (by decide), hov])
  refine ⟨τ8, _, Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7 r8)))))),
    ?_, ?_, ov8⟩
  · have hfl := hflat
    simp only [feK, Expr.size]
    omega
  · rw [o8, O37.out, P2.out, O1.out, hP.hout]; rfl

end Lax185574Proofs.ResolveRam.Glue
