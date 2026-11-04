import Lax185574Proofs.ResolveRam.Glue.OkDisp
import Lax185574Proofs.ResolveRam.Glue.ClauseJ
import Lax185574Proofs.ResolveRam.Glue.CR1
import Lax185574Proofs.ResolveRam.Glue.CFinT
import Lax185574Proofs.ResolveRam.SizeGlue.Calls
import Lax185574Proofs.ResolveRam.SizeGlue.Graph
import Lax185574Proofs.ResolveRam.SizeGlue.State
import Lax185574Proofs.ResolveRam.LenBounds

/-!
Round `1` of the glue program of lem:resolve-lift: the round after the
scatter type.

The dispatcher runs the case `bR1` (one test of the phase), which builds
the library `libR1` and writes the state of the next position as a plan.
`round1`: the clause of round `1`, with a time bound that is linear in
`(n + 1)²` up to a power of `Y`. `two_le_rcalls`: a nonempty
graph has at least two calls.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574Proofs.Words Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.ResolveRam
open Lax185574Proofs.TypeTreeSizes Lax3.DistFO Lax808846Proofs.Compile

/-! ### Sizes of words -/

theorem r1_length_toWord_ws (ws : List (List ℕ)) : (toWord ws).length = total ws + ws.length + 1 := by
  rw [length_toWord_ws]
  induction ws with
  | nil => simp [tot, total]
  | cons w ws ih =>
    rw [tot_cons, total_cons, List.length_cons]
    have : (toWord ws).length = 1 + tot ws := length_toWord_ws ws
    omega

theorem r1_mem_toWord {ws : List (List ℕ)} {w : List ℕ} {e : ℕ} (hw : w ∈ ws) (he : e ∈ w) :
    e ∈ toWord ws := by
  change e ∈ ws.length :: (ws.map toWord).flatten
  refine List.mem_cons_of_mem _ (List.mem_flatten.2 ⟨toWord w, List.mem_map_of_mem hw, ?_⟩)
  rw [toWord_listNat]; exact List.mem_cons_of_mem _ he

/-- The size of the room check of a round, from a bound of the library
by the output. -/
theorem sBig_r1 {L : List (List ℕ)} {b o x u : List ℕ} {k : ℕ}
    (hlen : total L + L.length ≤ 3 * o.length + 10) (hent : ∀ w ∈ L, ∀ e ∈ w, e ≤ maxEntry o)
    (hb : b.length ≤ u.length) (hmb : maxEntry b ≤ maxEntry u) :
    sBig L b x.length (maxEntry (x.take k)) ≤ 100 * (ySz u + ySz o + ySz x) := by
  have hmL : maxEntry L.flatten ≤ maxEntry o := maxEntry_le fun v hv => by
    obtain ⟨w, hw, hv⟩ := List.mem_flatten.1 hv
    exact hent w hw v hv
  have hm3 : maxEntry (x.take k) ≤ maxEntry x := maxEntry_le fun v hv => le_maxEntry (List.mem_of_mem_take hv)
  unfold sBig sOf ySz
  have : max (max (maxEntry (x.take k)) (maxEntry L.flatten)) (maxEntry b) ≤
      maxEntry x + maxEntry o + maxEntry u := by omega
  omega

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-! ### The number of calls -/

theorem next_stp_ne_fin : next G P Q s k₀ q₀ .stp ≠ .fin := by
  by_cases hq : q₀ = 0
  · rw [next_stp_up G P Q s k₀ q₀ hq]; simp
  · rw [next_stp_dn G P Q s k₀ q₀ hq]; simp

/-- **A nonempty graph has at least two calls**: the scatter type and the
call of the position after it. -/
theorem two_le_rcalls (hn : 1 ≤ n) : 2 ≤ (rcalls G P Q s k₀ q₀).length := by
  have h0 : 0 < (rcalls G P Q s k₀ q₀).length := by
    simp [rcalls, show n ≠ 0 by omega]
  have h := cur_succ_fin G P Q s k₀ q₀ hn (j := 0) h0
  have hne : cur G P Q s k₀ q₀ (0 + 1) ≠ .fin := next_stp_ne_fin G P Q s k₀ q₀
  have : 0 + 1 ≠ (rcalls G P Q s k₀ q₀).length := fun h' => hne (h.2 h')
  omega

/-! ### The output of round `1` -/

theorem r1_hd_len (c : Cur) :
    total (swAt G P Q s k₀ q₀ c).ws + (swAt G P Q s k₀ q₀ c).ws.length + 1 ≤
      (hdOf G P Q s k₀ q₀ c).length := by
  have := r1_length_toWord_ws (swAt G P Q s k₀ q₀ c).ws
  simp only [hdOf, stOf, List.length_cons, List.length_append]; omega

theorem r1_hd_ent (c : Cur) {w : List ℕ} {e : ℕ} (hw : w ∈ (swAt G P Q s k₀ q₀ c).ws) (he : e ∈ w) :
    e ∈ hdOf G P Q s k₀ q₀ c := by
  have := r1_mem_toWord hw he
  simp only [hdOf, stOf, List.mem_cons, List.mem_append]; tauto

theorem r1_q_ent {c : RCall} (hc : c ≠ .stp) {h : List ℕ} :
    (realQ G k₀ q₀ c).length ≤ (h ++ rQ G k₀ q₀ c).length ∧
      ∀ e ∈ realQ G k₀ q₀ c, e ≤ maxEntry (h ++ rQ G k₀ q₀ c) := by
  obtain ⟨pre, post, hsp', -, -⟩ := kW_split (kindOf c) (realQ G k₀ q₀ c) (kindOf_le hc)
  rw [rQ_kind G k₀ q₀ _ hc, hsp']
  refine ⟨by simp only [List.length_append]; omega, fun e he => le_maxEntry ?_⟩
  simp [he]

/-- The words of the library of round `1` are empty or words of the next state. -/
theorem libR1_words (z : ℕ) {w : List ℕ} (hw : w ∈ libR1 G P Q s k₀ q₀ z) :
    w = [] ∨ w ∈ planW (libR1 G P Q s k₀ q₀ z ++ []) (psR1 n (Lax185574.ScatterTypes.stp G k₀ q₀).words.length) := by
  rw [planW_r1]
  simp only [libR1, midR1, ws_stp, List.mem_append, List.mem_cons, List.not_mem_nil] at hw ⊢
  tauto

theorem libR1_size (z : ℕ) :
    total (libR1 G P Q s k₀ q₀ z) + (libR1 G P Q s k₀ q₀ z).length =
      total (planW (libR1 G P Q s k₀ q₀ z ++ []) (psR1 n (Lax185574.ScatterTypes.stp G k₀ q₀).words.length)) +
      (planW (libR1 G P Q s k₀ q₀ z ++ []) (psR1 n (Lax185574.ScatterTypes.stp G k₀ q₀).words.length)).length +
        2 := by
  rw [planW_r1]
  simp only [libR1, midR1, ws_stp, total_append, total_cons, List.length_append, List.length_cons,
    List.length_nil]
  simp [total]
  omega

theorem eOf_le_sum (eS eF eC eK eT : ℕ) (c : RCall) : eOf eS eF eC eK eT c ≤ eS + eF + eC + eK + eT := by
  cases c <;> simp only [eOf] <;> omega

/-- The dispatcher runs `bR1` after the scatter type. -/
theorem disp_stp_r1 {W : ℕ} {L : List (List ℕ)} {ps : List (ℕ × ℕ)} {KB : ℕ}
    (h : BodyCall (bR1 atCmd) W (rhoPlus (k₀ + 1) q₀ + 2) (ySz (xIn G k₀ q₀ P Q s)) (scW G P Q s k₀ q₀ .stp)
      (swAt G P Q s k₀ q₀ .stp).ws ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ .stp))
      (rY G k₀ q₀ (callOf G P Q s k₀ q₀ .stp)) L ps
      (kindOf (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)))
      (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)))
      (tagOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)) (winOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp))
      (scW G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)) KB) :
    BodyCall (disp atCmd (bR1 atCmd)) W (rhoPlus (k₀ + 1) q₀ + 2) (ySz (xIn G k₀ q₀ P Q s))
      (scW G P Q s k₀ q₀ .stp)
      (swAt G P Q s k₀ q₀ .stp).ws ((xIn G k₀ q₀ P Q s).take (winOf G P Q s k₀ q₀ .stp))
      (rY G k₀ q₀ (callOf G P Q s k₀ q₀ .stp)) L ps
      (kindOf (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)))
      (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)))
      (tagOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)) (winOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp))
      (scW G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)) (KB + 10) := by
  refine bodyCall_mono (bodyCall_ite_true (fun τ P0 => ?_) h) ?_
  · have hv : (Expr.var "ph").evalB (W + 1) τ = some 0 := by
      have := preR_var P0 9 (by omega)
      simp only [scR, scW_stp, List.getElem_cons_succ, List.getElem_cons_zero, List.getD_cons_succ,
        List.getD_cons_zero] at this
      exact this
    rw [evalB_condEq hv (evalB_lit (by omega))]
    rfl
  · simp only [Cond.size, Expr.size]; omega

theorem r1_pow {n Y a A c : ℕ} (hY : 1 ≤ Y) (ha : a ≤ A) :
    c * (n + 1) * Y ^ a ≤ c * ((n + 1) * (n + 1) * Y ^ A) := by
  have h1 : Y ^ a ≤ Y ^ A := Nat.pow_le_pow_right hY ha
  have h2 : (n + 1) * Y ^ a ≤ (n + 1) * (n + 1) * Y ^ A := by
    calc (n + 1) * Y ^ a ≤ 1 * ((n + 1) * Y ^ A) := by rw [one_mul]; exact Nat.mul_le_mul_left _ h1
      _ ≤ (n + 1) * ((n + 1) * Y ^ A) := Nat.mul_le_mul_right _ (by omega)
      _ = _ := by ring
  rw [mul_assoc]; exact Nat.mul_le_mul_left _ h2

/-- The size of the library of round `1` and its entries, from the next state. -/
theorem libR1_out (z : ℕ) (hz : planW (libR1 G P Q s k₀ q₀ z ++ [])
      (psR1 n (Lax185574.ScatterTypes.stp G k₀ q₀).words.length) =
      (swAt G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)).ws) (r : List ℕ) :
    total (libR1 G P Q s k₀ q₀ z) + (libR1 G P Q s k₀ q₀ z).length ≤
        (hdOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)).length + 1 ∧
      ∀ w ∈ libR1 G P Q s k₀ q₀ z, ∀ e ∈ w, e ≤ maxEntry (hdOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp) ++ r) := by
  refine ⟨?_, fun w hw e he => ?_⟩
  · have h1 := libR1_size G P Q s k₀ q₀ z
    have h2 := r1_hd_len G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp)
    rw [hz] at h1
    omega
  · rcases libR1_words G P Q s k₀ q₀ z hw with rfl | h
    · simp at he
    · rw [hz] at h
      exact le_maxEntry (List.mem_append_left _ (r1_hd_ent G P Q s k₀ q₀ _ h he))

/-- The cost of the atom words of round `1`. -/
theorem kA_r1 (hk : 1 ≤ k₀) (hn : 1 ≤ n) {C4 A4 : ℕ}
    (hIt : ∀ x ∈ lvR G P Q s k₀ q₀ 0, wordLength x.2 ≤ C4 * (maxTreeSize G k₀ q₀ + 1) ^ A4) (c a : ℕ) :
    c * ((ctW G P Q).length + 1) *
        ((itemW (itm G P Q s k₀ q₀ 0 0)).length + (itm G P Q s k₀ q₀ 0 0).2.ℓ +
          rhoPlus (itm G P Q s k₀ q₀ 0 0).2.k (itm G P Q s k₀ q₀ 0 0).2.q + 1) ^ a ≤
      3 * c * (3 + k₀ + rhoPlus k₀ q₀ + C4) ^ a * ((n + 1) * (maxTreeSize G k₀ q₀ + 1) ^ (A4 * a)) := by
  have hi : 0 < (lvR G P Q s k₀ q₀ 0).length := by rw [lvR_zero_length]; omega
  have hx := itm_eq G P Q s k₀ q₀ hi
  have hmem : itm G P Q s k₀ q₀ 0 0 ∈ lvR G P Q s k₀ q₀ 0 := by rw [hx]; exact List.getElem_mem hi
  obtain ⟨ℓ, u, hu, -, hℓ⟩ := lvR_good G P Q s k₀ q₀ hk (Nat.zero_le _) hmem
  have hw := hIt _ hmem
  have hl := length_itemW (itm G P Q s k₀ q₀ 0 0)
  have hct := ctW_len G P Q
  set X := maxTreeSize G k₀ q₀ + 1 with hX
  have hX1 : 1 ≤ X ^ A4 := Nat.one_le_pow _ _ (by omega)
  have hb : (itemW (itm G P Q s k₀ q₀ 0 0)).length + (itm G P Q s k₀ q₀ 0 0).2.ℓ +
      rhoPlus (itm G P Q s k₀ q₀ 0 0).2.k (itm G P Q s k₀ q₀ 0 0).2.q + 1 ≤
      (3 + k₀ + rhoPlus k₀ q₀ + C4) * X ^ A4 := by
    rw [hu]
    simp only [tree, Nat.add_zero, Nat.sub_zero]
    rw [hu] at hw
    have : (3 + k₀ + rhoPlus k₀ q₀ + C4) * X ^ A4 =
        (3 + k₀ + rhoPlus k₀ q₀) * X ^ A4 + C4 * X ^ A4 := by ring
    have h3 : 3 + k₀ + rhoPlus k₀ q₀ ≤ (3 + k₀ + rhoPlus k₀ q₀) * X ^ A4 := Nat.le_mul_of_pos_right _ hX1
    rw [hu] at hl
    omega
  calc c * ((ctW G P Q).length + 1) * ((itemW (itm G P Q s k₀ q₀ 0 0)).length + (itm G P Q s k₀ q₀ 0 0).2.ℓ +
          rhoPlus (itm G P Q s k₀ q₀ 0 0).2.k (itm G P Q s k₀ q₀ 0 0).2.q + 1) ^ a
      ≤ c * (3 * (n + 1)) * ((3 + k₀ + rhoPlus k₀ q₀ + C4) * X ^ A4) ^ a :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega)) (Nat.pow_le_pow_left hb _)
    _ = _ := by rw [mul_pow, ← pow_mul]; ring

set_option maxHeartbeats 1600000 in
/-- **Round `1`.** The round after the scatter type runs the body `bR1`
through the dispatcher. -/
theorem round1 (k₀ q₀ : ℕ) (hk : 1 ≤ k₀) : ∃ Cs As cS : ℕ, ∀ (K eS eF eC eK eT sQ cG E : ℕ)
    (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool),
    kq0 ≤ K → guardBits glueLay + 11 ≤ sQ → 1 ≤ n →
    2 * 2 ^ (eS + eF + eC + eK + eT + 1) + K + 1 ≤ cG →
    2 ^ 24 * (rhoPlus (k₀ + 1) q₀ + 2) ^ 4 * cS ^ 2 ≤ cG →
    E = eS + eF + eC + eK + eT + 2 →
    ∃ t, ClauseAt G P Q s k₀ q₀
      (guardedProgram glueLay (glueTop K eT (sQ - guardBits glueLay + eT + 1)
        (roundJ (disp atCmd (bR1 atCmd)) fECmd eS eF eC eK (sQ - guardBits glueLay + eS + 1)
          (sQ - guardBits glueLay + eF + 1) (sQ - guardBits glueLay + eC + 1) (sQ - guardBits glueLay + eK + 1))))
      (guardBits glueLay + 6) sQ eS eF eC eK eT cG E t 1 ∧
    t ≤ glueLay.const * (Cs * (n + 1) * (n + 1) *
      (maxTreeSize G k₀ q₀ + treeCount G (resolveBy G s P Q) k₀ q₀ + 1) ^ As +
      100 * (K + 2 ^ (sQ + eS + eF + eC + eK + eT + 1))) + 5 := by
  obtain ⟨C1, A1, hSt⟩ := stOf_cur_len k₀ q₀ hk
  obtain ⟨C2, A2, hRc⟩ := rcall_le_nY (q₀ := q₀) hk
  obtain ⟨C3, A3, hYs⟩ := stp_ans_le (q₀ := q₀) hk
  obtain ⟨C4, A4, hIt⟩ := item_le_all k₀ q₀ hk
  obtain ⟨cA, hcA⟩ : ∃ v, v = cR1 atCmd_spec atKeep_atV := ⟨_, rfl⟩
  obtain ⟨aA, haA⟩ : ∃ v, v = aR1 atCmd_spec atKeep_atV := ⟨_, rfl⟩
  obtain ⟨As, hAs⟩ : ∃ v, v = A1 + A2 + A3 + A4 * aA + 1 := ⟨_, rfl⟩
  obtain ⟨CA, hCA⟩ : ∃ v, v = 12 * cCT + 12 * cLV + 60 * C3 + 60 * C1 + 3500 := ⟨_, rfl⟩
  obtain ⟨CK, hCK⟩ : ∃ v, v = 2 * CA + 120 * C1 + 60 * C3 + 18 * C2 +
      3 * cA * (3 + k₀ + rhoPlus k₀ q₀ + C4) ^ aA + 3000 := ⟨_, rfl⟩
  obtain ⟨CO, hCO⟩ : ∃ v, v = C1 + C2 + 3 := ⟨_, rfl⟩
  obtain ⟨Cst, hCst⟩ : ∃ v, v = 23 * ((k₀ + q₀ + 1) * (q₀ + 1)) + 1000 * qLen + 20000 := ⟨_, rfl⟩
  refine ⟨1000 * (C1 + C3 + 4 * CO + CK + 40) + Cst, As, 100, ?_⟩
  intro K eS eF eC eK eT sQ cG E n G P Q s hK hrs hn hcG1 hcG2 hE
  have hR2 := two_le_rcalls G P Q s k₀ q₀ hn
  obtain ⟨hv1, hc1⟩ := rcalls_get G P Q s k₀ q₀ hn (j := 1) (by omega)
  have ecur1 : cur G P Q s k₀ q₀ 1 = next G P Q s k₀ q₀ .stp := rfl
  rw [ecur1] at hv1 hc1
  have hne : callOf G P Q s k₀ q₀ (next G P Q s k₀ q₀ .stp) ≠ .stp :=
    callOf_ne_stp G P Q s k₀ q₀ hv1 (next_ne_stp G P Q s k₀ q₀ _)
  have rSt0 := hSt n G P Q s 0 (by omega)
  have rSt1 := hSt n G P Q s 1 (by omega)
  rw [ecur1] at rSt1
  have rRc := hRc n G P Q s _ (List.mem_of_getElem? hc1) hne
  have rYs := hYs n G
  have hxl := xIn_len_le' k₀ q₀ G P Q s
  set x := xIn G k₀ q₀ P Q s with hx
  set c' := next G P Q s k₀ q₀ .stp with hc'
  set M := maxTreeSize G k₀ q₀ with hM
  set T := treeCount G (resolveBy G s P Q) k₀ q₀ with hT
  set Y := M + T + 1 with hY
  set Z := (n + 1) * (n + 1) * Y ^ As with hZ
  have hY1 : 1 ≤ Y := by omega
  have hZ1 : 1 ≤ Z := Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (pow_pos hY1 _)
  have hzp : ∀ c a, a ≤ As → c * (n + 1) * Y ^ a ≤ c * Z := fun c a ha => r1_pow hY1 ha
  have hMY : ∀ a, (M + 1) ^ a ≤ Y ^ a := fun a => Nat.pow_le_pow_left (by omega) a
  set o := hdOf G P Q s k₀ q₀ c' ++ rQ G k₀ q₀ (callOf G P Q s k₀ q₀ c') with ho
  -- sizes
  have hx2 : x.length + 1 ≤ 12 * Z := by
    have h2 : M + 1 ≤ Y ^ As := le_trans (by omega : M + 1 ≤ Y) (Nat.le_self_pow (by omega) _)
    have h3 : 11 * (n + 1) * (n + 1) * (M + 1) ≤ 11 * Z := by
      calc 11 * (n + 1) * (n + 1) * (M + 1) = 11 * ((n + 1) * (n + 1) * (M + 1)) := by ring
        _ ≤ 11 * ((n + 1) * (n + 1) * Y ^ As) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ h2)
    omega
  have hst0 : (stOf G P Q s k₀ q₀ .stp).length ≤ C1 * Z :=
    le_trans rSt0 (hzp C1 A1 (by omega))
  have hst1 : (stOf G P Q s k₀ q₀ c').length ≤ C1 * Z :=
    le_trans rSt1 (hzp C1 A1 (by omega))
  have hrq : (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ c')).length +
      (rQ G k₀ q₀ (callOf G P Q s k₀ q₀ c')).length ≤ C2 * Z := by
    have := hzp C2 A2 (by omega)
    omega
  have hb : (rY G k₀ q₀ .stp).length ≤ C3 * Z := by
    have h2 : C3 * (n + 1) * (M + 1) ^ A3 ≤ C3 * (n + 1) * Y ^ A3 := Nat.mul_le_mul_left _ (hMY A3)
    have h3 := hzp C3 A3 (by omega)
    omega
  have hol : o.length ≤ 3 + C1 * Z + C2 * Z := by
    simp only [o, hdOf, List.length_append, List.length_cons]; omega
  have hkA : ∀ z, planW (libR1 G P Q s k₀ q₀ z ++ [])
      (psR1 n (Lax185574.ScatterTypes.stp G k₀ q₀).words.length) = (swAt G P Q s k₀ q₀ c').ws →
      kR1A G P Q s k₀ q₀ z ≤ CA * Z := by
    intro z hz
    have hL := (libR1_out G P Q s k₀ q₀ z hz []).1
    rw [← hc'] at hL
    have hhd : (hdOf G P Q s k₀ q₀ c').length = 3 + (stOf G P Q s k₀ q₀ c').length := by
      simp [hdOf]; omega
    unfold kR1A
    try rw [← hx]
    have e1 : cCT * (x.length + 1) ≤ 12 * (cCT * Z) := by
      calc _ ≤ cCT * (12 * Z) := Nat.mul_le_mul_left _ hx2
        _ = _ := by ring
    have e2 : cLV * (x.length + 1) ≤ 12 * (cLV * Z) := by
      calc _ ≤ cLV * (12 * Z) := Nat.mul_le_mul_left _ hx2
        _ = _ := by ring
    have e3 : CA * Z = 12 * (cCT * Z) + 12 * (cLV * Z) + 60 * (C3 * Z) + 60 * (C1 * Z) + 3500 * Z := by
      rw [hCA]; ring
    omega
  have hhd : (hdOf G P Q s k₀ q₀ c').length = 3 + (stOf G P Q s k₀ q₀ c').length := by
    simp [hdOf]; omega
  have hoL : (hdOf G P Q s k₀ q₀ c').length ≤ o.length := by simp [o]
  have hsz1 : (Cond.eq (.var "gq") (.lit 0)).size ≤ 10 := by simp [Cond.size, Expr.size]
  have key : ∃ (L : List (List ℕ)) (ps : List (ℕ × ℕ)) (KB : ℕ),
      (∀ W, BodyCall (bR1 atCmd) W (rhoPlus (k₀ + 1) q₀ + 2) (ySz x) (scW G P Q s k₀ q₀ .stp)
        (swAt G P Q s k₀ q₀ .stp).ws (x.take (winOf G P Q s k₀ q₀ .stp))
        (rY G k₀ q₀ (callOf G P Q s k₀ q₀ .stp)) L ps
        (kindOf (callOf G P Q s k₀ q₀ c')) (realQ G k₀ q₀ (callOf G P Q s k₀ q₀ c'))
        (tagOf G P Q s k₀ q₀ c') (winOf G P Q s k₀ q₀ c') (scW G P Q s k₀ q₀ c') KB) ∧
      planW L ps = (swAt G P Q s k₀ q₀ c').ws ∧ (swAt G P Q s k₀ q₀ .stp).ws.Sublist L ∧
      ps.length ≤ 12 ∧ total L + L.length ≤ 3 * o.length + 10 ∧
      (∀ w ∈ L, ∀ e ∈ w, e ≤ maxEntry o) ∧ KB ≤ CK * Z := by
    by_cases hq : q₀ = 0
    · have hpl := planW_r1up G P Q s k₀ q₀ hq
      have hz : planW (libR1 G P Q s k₀ q₀ 0 ++ []) (psR1 n (Lax185574.ScatterTypes.stp G k₀ q₀).words.length) =
          (swAt G P Q s k₀ q₀ c').ws := by
        rw [planW_r1]; rw [planW_r1] at hpl; exact hpl
      obtain ⟨hL1, hL2⟩ := libR1_out G P Q s k₀ q₀ 0 hz (rQ G k₀ q₀ (callOf G P Q s k₀ q₀ c'))
      rw [← hc'] at hL1 hL2
      have haq : aqR1 G P Q s k₀ q₀ = realQ G k₀ q₀ (callOf G P Q s k₀ q₀ c') := by
        rw [hc', next_stp_up G P Q s k₀ q₀ hq, callOf_up' (by rw [lvR_zero_length]; omega)
          (by unfold nUp; split_ifs <;> omega), if_pos rfl, realQ_canon]
        rfl
      obtain ⟨hq1, hq2⟩ := r1_q_ent G k₀ q₀ hne (h := hdOf G P Q s k₀ q₀ c')
      rw [← ho] at hq1 hq2
      have hKA := kA_r1 G P Q s k₀ q₀ hk hn (hIt 0 (Nat.zero_le _) n G P Q s) cA aA
      rw [← hM] at hKA
      refine ⟨libR1 G P Q s k₀ q₀ 0 ++ [aqR1 G P Q s k₀ q₀],
        psR1 n (Lax185574.ScatterTypes.stp G k₀ q₀).words.length,
        1 + cR1q.size + kR1up G P Q s k₀ q₀ atCmd_spec atKeep_atV,
        fun W => bR1_up_ok G P Q s k₀ q₀ atCmd_spec atKeep_atV hk hn hq, hpl,
        sub_libR1 G P Q s k₀ q₀ 0 _, by simp [psR1], ?_, ?_, ?_⟩
      · rw [total_append, List.length_append, total_single, List.length_singleton, haq]
        omega
      · intro w hw e he
        rcases List.mem_append.1 hw with h | h
        · exact hL2 w h e he
        · rw [List.mem_singleton] at h; subst h; rw [haq] at he; exact hq2 e he
      · have hk0 := hkA 0 hz
        unfold kR1up kAtT
        rw [← hcA, ← haA]
        have hKA' : 3 * cA * (3 + k₀ + rhoPlus k₀ q₀ + C4) ^ aA * ((n + 1) * (M + 1) ^ (A4 * aA)) ≤
            3 * cA * (3 + k₀ + rhoPlus k₀ q₀ + C4) ^ aA * Z := by
          rw [← mul_assoc]
          refine le_trans (Nat.mul_le_mul_left _ (hMY _)) ?_
          exact hzp _ _ (by omega)
        rw [haq]
        have e4 : CK * Z = 2 * (CA * Z) + 120 * (C1 * Z) + 60 * (C3 * Z) + 18 * (C2 * Z) +
            3 * cA * (3 + k₀ + rhoPlus k₀ q₀ + C4) ^ aA * Z + 3000 * Z := by rw [hCK]; ring
        simp only [cR1q] at hsz1 ⊢
        omega
    · have hpl := planW_r1dn G P Q s k₀ q₀ hq
      have hz : planW (libR1 G P Q s k₀ q₀ 1 ++ []) (psR1 n (Lax185574.ScatterTypes.stp G k₀ q₀).words.length) =
          (swAt G P Q s k₀ q₀ c').ws := by rw [List.append_nil]; exact hpl
      obtain ⟨hL1, hL2⟩ := libR1_out G P Q s k₀ q₀ 1 hz (rQ G k₀ q₀ (callOf G P Q s k₀ q₀ c'))
      rw [← hc'] at hL1 hL2
      refine ⟨libR1 G P Q s k₀ q₀ 1, psR1 n (Lax185574.ScatterTypes.stp G k₀ q₀).words.length,
        1 + cR1q.size + kR1dn G P Q s k₀ q₀, fun W => bR1_dn_ok G P Q s k₀ q₀ atCmd hn hq, hpl,
        by simpa using sub_libR1 G P Q s k₀ q₀ 1 [], by simp [psR1], by omega, hL2, ?_⟩
      have hk1 := hkA 1 hz
      unfold kR1dn
      have e4 : CK * Z = 2 * (CA * Z) + 120 * (C1 * Z) + 60 * (C3 * Z) + 18 * (C2 * Z) +
          3 * cA * (3 + k₀ + rhoPlus k₀ q₀ + C4) ^ aA * Z + 3000 * Z := by rw [hCK]; ring
      simp only [cR1q] at hsz1 ⊢
      omega
  obtain ⟨L, ps, KB, hbody, hpl, hsub, hps, hlen, hent, hKB⟩ := key
  obtain ⟨-, hc0⟩ := rcalls_get G P Q s k₀ q₀ hn (j := 0) (by omega)
  have hgu := gU_succ G P Q s k₀ q₀ (zOut G k₀ q₀ P Q s) hc0
  have hgo : gOut G k₀ q₀ (rcalls G P Q s k₀ q₀) (hdJ G P Q s k₀ q₀) (zOut G k₀ q₀ P Q s) (0 + 1) = o := by
    simp [gOut, hc1, hdJ, ecur1, o]
  have heS := eOf_le_sum eS eF eC eK eT (callOf G P Q s k₀ q₀ c')
  have hcl := clauseJ_call G P Q s k₀ q₀ (Lay := glueLay) (j := 0) (cS := 100) (KB := KB + 10)
    (disp atCmd (bR1 atCmd)) fECmd (L := L) (ps := ps)
    (glue_ok _ _ _ _ _ _ _ _ _ _ _) glueLay_W glueLay_ovf hK hrs hn (by omega)
    (fun W => disp_stp_r1 G P Q s k₀ q₀ (hbody W)) hpl hsub ?_ ?_ hcG2
    (show eOf eS eF eC eK eT (callOf G P Q s k₀ q₀ c') + 1 ≤ E by omega) (by omega)
  rotate_left
  · rw [hgu, hgo]
    refine sBig_r1 hlen hent ?_ ?_
    · simp only [List.length_append, List.length_cons]; omega
    · exact maxEntry_le fun v hv => le_maxEntry (by simp [hv])
  · have : 2 ^ (eOf eS eF eC eK eT (callOf G P Q s k₀ q₀ c') + 1) ≤ 2 ^ (eS + eF + eC + eK + eT + 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    show 2 * 2 ^ (eOf eS eF eC eK eT (callOf G P Q s k₀ q₀ c') + 1) + K + 1 ≤ cG
    omega
  rw [show (0 : ℕ) + 1 = 1 from rfl] at hcl
  refine ⟨_, hcl, ?_⟩
  refine le_trans (tJ_le glueLay K (KB + 10) _ _ _ k₀ q₀ _ L ps _ _ _ hps) ?_
  refine Nat.add_le_add_right (Nat.mul_le_mul_left _ ?_) 5
  have hwx : (x.take (winOf G P Q s k₀ q₀ .stp)).length ≤ x.length := List.length_take_le _ _
  have hws : total (swAt G P Q s k₀ q₀ .stp).ws = 0 := by rw [ws_stp]; rfl
  set e := eOf eS eF eC eK eT (callOf G P Q s k₀ q₀ c') with he
  set N := sQ + eS + eF + eC + eK + eT + 1 with hN
  have hd : 2 ^ (sQ - guardBits glueLay + e + 1) ≤ 2 ^ N := Nat.pow_le_pow_right (by omega) (by omega)
  have he1 : e + 1 ≤ 2 ^ N :=
    le_trans (Nat.lt_two_pow_self).le (Nat.pow_le_pow_right (by omega) (by omega))
  have e5 : (1000 * (C1 + C3 + 4 * CO + CK + 40) + Cst) * (n + 1) * (n + 1) * Y ^ As =
      1000 * (C1 * Z) + 1000 * (C3 * Z) + 4000 * (CO * Z) + 1000 * (CK * Z) + 40000 * Z + Cst * Z := by
    simp only [hZ]; ring
  have e6 : CO * Z = C1 * Z + C2 * Z + 3 * Z := by rw [hCO]; ring
  have e7 : Cst ≤ Cst * Z := Nat.le_mul_of_pos_right _ hZ1
  show 1000 * ((x.take (winOf G P Q s k₀ q₀ .stp)).length + (stOf G P Q s k₀ q₀ .stp).length +
      (rY G k₀ q₀ .stp).length + total (swAt G P Q s k₀ q₀ .stp).ws + total L + L.length + o.length +
      (KB + 10) + 1) + (30 * K + 23 * ((k₀ + q₀ + 1) * (q₀ + 1)) + 60 * (e + 1) +
      30 * 2 ^ (sQ - guardBits glueLay + e + 1) + 1000 * qLen + 20000) ≤
    (1000 * (C1 + C3 + 4 * CO + CK + 40) + Cst) * (n + 1) * (n + 1) * Y ^ As + 100 * (K + 2 ^ N)
  rw [e5]
  omega


end Lax185574Proofs.ResolveRam.Glue
