import Lax185574Proofs.ResolveRam.Glue.FinM

/-!
The output of a later round of the glue program of lem:resolve-lift that
issues a call.

After the case of the round has grown the library `L` and set the
scalars of the new state, the ranges of its words in `PR`, the kind `qk`
of the next call (`0` rank shift, `1` far tree, `2` composition, `3`
canonical form) and the scalars of its real query (`KindOK`), `tailC`
writes the head and the new state (`wrHS`), the query of the switch
(`wrQ` with the slots chosen by the kind), marks the real query and ends
the round with the guard of the exponent of the kind (`tailC_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Simulate
open Lax185574.WordEncoding Lax185574Proofs.ResolveRam

/-- The slots by kind. -/
noncomputable def sA : Com := .ite (.eq (.var "qk") (.lit 0)) slotA (pushLits qA0)
noncomputable def sB : Com := .ite (.eq (.var "qk") (.lit 1)) slotB (pushLits qB0)
noncomputable def sC : Com := .ite (.eq (.var "qk") (.lit 2)) slotC (pushLits qC0)
noncomputable def sE : Com := .ite (.eq (.var "qk") (.lit 3)) (cpPart "oe" 0) (pushLits qE0)

/-- Mark the real query. -/
noncomputable def setQ : Com :=
  .ite (.eq (.var "qk") (.lit 0))
    (.seq (.assign "qa" (.var "a0")) (.assign "ql" (.sub (.var "b0") (.var "a0"))))
  (.ite (.eq (.var "qk") (.lit 1))
    (.seq (.assign "qa" (.var "b0")) (.assign "ql" (.sub (.var "c0") (.var "b0"))))
  (.ite (.eq (.var "qk") (.lit 2))
    (.seq (.assign "qa" (.var "c0")) (.assign "ql" (.sub (.var "e0") (.var "c0"))))
    (.seq (.assign "qa" (.var "e0"))
      (.assign "ql" (.sub (.sub (.var "po") (.var "e0")) (.lit qF0.length))))))

/-- The end with the exponent of the kind. -/
def finSel (eS eF eC eK dS dF dC dK : ℕ) : Com :=
  .ite (.eq (.var "qk") (.lit 0)) (finCallM eS dS)
  (.ite (.eq (.var "qk") (.lit 1)) (finCallM eF dF)
  (.ite (.eq (.var "qk") (.lit 2)) (finCallM eC dC) (finCallM eK dK)))

/-- The output of a round with a call. -/
noncomputable def tailC (eS eF eC eK dS dF dC dK : ℕ) : Com :=
  .seq wrHS (.seq (wrQ sA sB sC sE) (.seq setQ (finSel eS eF eC eK dS dF dC dK)))

/-- The words of the slots for a call of kind `k` with real query `w`. -/
noncomputable def kW (k : ℕ) (w : List ℕ) : List ℕ :=
  sw5In (if k = 0 then w else qA0) (if k = 1 then w else qB0) (if k = 2 then w else qC0)
    (if k = 3 then w else qE0) qF0

/-- The exponent of the kind. -/
def kE (eS eF eC eK k : ℕ) : ℕ := if k = 0 then eS else if k = 1 then eF else if k = 2 then eC else eK

/-- The scalars of the real query of a call of kind `k`. -/
def KindOK (W : ℕ) (L : List (List ℕ)) (k : ℕ) (w : List ℕ) (τ : Env) : Prop :=
  (k = 0 → ∃ iw, ∃ h : iw < L.length, 2 ≤ L[iw].length ∧ τ.vars "ox" = iw ∧ w = L[iw].drop 2) ∧
  (k = 1 → ∃ iw, ∃ h : iw < L.length, ∃ lo N m, 2 ≤ L[iw].length ∧ lo + N ≤ L.length ∧ 1 ≤ m ∧
    m ≤ W ∧ τ.vars "ox" = iw ∧ τ.vars "flo" = lo ∧ τ.vars "fN" = N ∧ τ.vars "ck" = m ∧
    w = L[iw].drop 2 ++ toWord (selW L lo N (cutSel m))) ∧
  (k = 2 → ∃ is jf, ∃ h1 : is < L.length, ∃ h2 : jf < L.length, τ.vars "os" = is ∧
    τ.vars "of" = jf ∧ w = L[is] ++ L[jf]) ∧
  (k = 3 → ∃ ie, ∃ h : ie < L.length, τ.vars "oe" = ie ∧ w = L[ie]) ∧ k ≤ 3

theorem SlotRun.vac {W S Xm K : ℕ} {c : Com} {w : List ℕ} {P P' : Env → Prop} (h : ∀ σ, ¬ P σ) :
    SlotRun W S Xm c w P P' K := fun σ _ hP => absurd hP (h σ)

/-- The invariant of the query phase. -/
def QInv (W X k : ℕ) (L : List (List ℕ)) (w : List ℕ) (σ : Env) : Prop :=
  σ.vars "gX" = X ∧ σ.vars "ovf" = 0 ∧ LibOK W L σ ∧ KindOK W L k w σ ∧ σ.vars "qk" = k

theorem QInv.ofr {W X k : ℕ} {L : List (List ℕ)} {w : List ℕ} {σ σ' : Env} {xs : List String}
    (h : QInv W X k L w σ) (o : OFr σ σ' xs)
    (hxs : ∀ y ∈ xs, y ∉ ["gX", "ovf", "W", "qk", "ox", "flo", "fN", "ck", "os", "of", "oe"]) :
    QInv W X k L w σ' := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have v : ∀ y ∈ ["gX", "ovf", "W", "qk", "ox", "flo", "fN", "ck", "os", "of", "oe"], σ'.vars y = σ.vars y :=
    fun y hy => o.vars y (fun h => hxs y h hy)
  refine ⟨by rw [v "gX" (by simp), h1], by rw [v "ovf" (by simp), h2], h3.ofr o (fun h => hxs _ h (by simp)),
    ?_, by rw [v "qk" (by simp), h5]⟩
  obtain ⟨k0, k1, k2, k3, k4⟩ := h4
  refine ⟨fun hk => ?_, fun hk => ?_, fun hk => ?_, fun hk => ?_, k4⟩
  · obtain ⟨iw, hiw, h2', hox, hw⟩ := k0 hk; exact ⟨iw, hiw, h2', by rw [v "ox" (by simp), hox], hw⟩
  · obtain ⟨iw, hiw, lo, N, m, a1, a2, a3, a4, a5, a6, a7, a8, hw⟩ := k1 hk
    exact ⟨iw, hiw, lo, N, m, a1, a2, a3, a4, by rw [v "ox" (by simp), a5], by rw [v "flo" (by simp), a6],
      by rw [v "fN" (by simp), a7], by rw [v "ck" (by simp), a8], hw⟩
  · obtain ⟨is, jf, h1', h2', a1, a2, hw⟩ := k2 hk
    exact ⟨is, jf, h1', h2', by rw [v "os" (by simp), a1], by rw [v "of" (by simp), a2], hw⟩
  · obtain ⟨ie, hie, a1, hw⟩ := k3 hk; exact ⟨ie, hie, by rw [v "oe" (by simp), a1], hw⟩

theorem SlotRun.monoK {W S Xm K K' : ℕ} {c : Com} {w : List ℕ} {P P' : Env → Prop}
    (h : SlotRun W S Xm c w P P' K) (hK : K ≤ K') : SlotRun W S Xm c w P P' K' := by
  intro σ X hP hF hc hX hXm
  obtain ⟨σ', r, F, H, q, l, u⟩ := h σ X hP hF hc hX hXm
  exact ⟨σ', r.mono hK, F, H, q, l, u⟩

/-- The length of the fixed queries. -/
noncomputable def qLen : ℕ := qA0.length + qB0.length + qC0.length + qE0.length + qF0.length

/-- A bound on the cost of a slot, linear in the size of the library. -/
noncomputable def slotK (L : List (List ℕ)) : ℕ := 100 * (total L + L.length + qLen + 10)

theorem lits_slot {W S Xm X k j : ℕ} {L : List (List ℕ)} {w q : List ℕ} (hq : ∀ v ∈ q, v ≤ W)
    (hql : q.length ≤ qLen) :
    SlotRun W S Xm (pushLits q) q (fun σ => QInv W X k L w σ ∧ σ.vars "qk" ≠ j) (QInv W X k L w)
      (slotK L) := by
  refine ((slot_lits (P := QInv W X k L w) hq (fun σ σ' h o => h.ofr o (by decide))).pre
    (fun σ h => h.1)).monoK ?_
  unfold slotK; omega

theorem len_le_total {L : List (List ℕ)} {i : ℕ} (h : i < L.length) : L[i].length ≤ total L := by
  have := off_add_le h; have := off_le_total L (i + 1); rw [off_succ h] at this; omega

theorem slotK_ge (L : List (List ℕ)) : 100 * (total L + L.length + qLen + 10) ≤ slotK L := le_rfl

theorem sA_ok {W Xm X k : ℕ} {L : List (List ℕ)} {w : List ℕ} (hs : LibSmall W L)
    (hq : ∀ v ∈ qA0, v ≤ W) :
    SlotRun W (total L + L.length + 8) Xm sA (if k = 0 then w else qA0) (QInv W X k L w) (QInv W X k L w)
      (slotK L + slotK L + 5) := by
  have := slot_ite (W := W) (S := total L + L.length + 8) (Xm := Xm) (j := 0) (c := slotA)
    (c' := pushLits qA0) (w := w) (w' := qA0) (P := QInv W X k L w) (P' := QInv W X k L w)
    (K := slotK L) (K' := slotK L) ?_ (lits_slot hq (by unfold qLen; omega))
    (fun σ h => by have := hs.1; have := h.2.2.2.1.2.2.2.2; rw [h.2.2.2.2]; omega) (decide (k = 0))
    (fun σ h => by rw [h.2.2.2.2]; simp) (by have := hs.1; omega)
  · simpa [sA] using this
  · intro σ X' hP hF hc hX hXm
    have hk : k = 0 := by rw [← hP.1.2.2.2.2]; exact hP.2
    obtain ⟨iw, hiw, h2, hox, hw⟩ := hP.1.2.2.2.1.1 hk
    subst hw
    have := (slotA_ok (Xm := Xm) (B := QInv W X k L (L[iw].drop 2)) hiw h2 hs
      (fun σ σ' h o => h.ofr o (by decide))) σ X' ⟨hP.1, hP.1.2.2.1, hox⟩ hF hc hX hXm
    obtain ⟨σ', r, F, H, q, l, u⟩ := this
    exact ⟨σ', r.mono (by have := len_le_total hiw; have := slotK_ge L; omega), F, H, q, l, u⟩

theorem sB_ok {W Xm X k : ℕ} {L : List (List ℕ)} {w : List ℕ} (hs : LibSmall W L)
    (hq : ∀ v ∈ qB0, v ≤ W) :
    SlotRun W (total L + L.length + 8) Xm sB (if k = 1 then w else qB0) (QInv W X k L w) (QInv W X k L w)
      (slotK L + slotK L + 5) := by
  have := slot_ite (W := W) (S := total L + L.length + 8) (Xm := Xm) (j := 1) (c := slotB)
    (c' := pushLits qB0) (w := w) (w' := qB0) (P := QInv W X k L w) (P' := QInv W X k L w)
    (K := slotK L) (K' := slotK L) ?_ (lits_slot hq (by unfold qLen; omega))
    (fun σ h => by have := hs.1; have := h.2.2.2.1.2.2.2.2; rw [h.2.2.2.2]; omega) (decide (k = 1))
    (fun σ h => by rw [h.2.2.2.2]; simp) (by have := hs.1; omega)
  · simpa [sB] using this
  · intro σ X' hP hF hc hX hXm
    have hk : k = 1 := by rw [← hP.1.2.2.2.2]; exact hP.2
    obtain ⟨iw, hiw, lo, N, m, a1, a2, a3, a4, a5, a6, a7, a8, hw⟩ := hP.1.2.2.2.1.2.1 hk
    subst hw
    have := (slotB_ok (Xm := Xm) (B := QInv W X k L (L[iw].drop 2 ++ toWord (selW L lo N (cutSel m))))
      hiw a1 a2 a3 a4 hs (fun σ σ' h o => h.ofr o (by decide))) σ X' ⟨hP.1, hP.1.2.2.1, a5, a6, a7, a8⟩
      hF hc hX hXm
    obtain ⟨σ', r, F, H, q, l, u⟩ := this
    refine ⟨σ', r.mono ?_, F, H, q, l, u⟩
    have h1 := len_le_total hiw
    have h2 : total ((L.drop lo).take N) ≤ total L :=
      total_le_of_sub ((List.take_sublist _ _).trans (List.drop_sublist _ _))
    unfold slotK; omega

theorem sC_ok {W Xm X k : ℕ} {L : List (List ℕ)} {w : List ℕ} (hs : LibSmall W L)
    (hq : ∀ v ∈ qC0, v ≤ W) :
    SlotRun W (total L + L.length + 8) Xm sC (if k = 2 then w else qC0) (QInv W X k L w) (QInv W X k L w)
      (slotK L + slotK L + 5) := by
  have := slot_ite (W := W) (S := total L + L.length + 8) (Xm := Xm) (j := 2) (c := slotC)
    (c' := pushLits qC0) (w := w) (w' := qC0) (P := QInv W X k L w) (P' := QInv W X k L w)
    (K := slotK L) (K' := slotK L) ?_ (lits_slot hq (by unfold qLen; omega))
    (fun σ h => by have := hs.1; have := h.2.2.2.1.2.2.2.2; rw [h.2.2.2.2]; omega) (decide (k = 2))
    (fun σ h => by rw [h.2.2.2.2]; simp) (by have := hs.1; omega)
  · simpa [sC] using this
  · intro σ X' hP hF hc hX hXm
    have hk : k = 2 := by rw [← hP.1.2.2.2.2]; exact hP.2
    obtain ⟨is, jf, h1, h2, a1, a2, hw⟩ := hP.1.2.2.2.1.2.2.1 hk
    subst hw
    have := (slotC_ok (Xm := Xm) (B := QInv W X k L (L[is] ++ L[jf])) h1 h2 hs
      (fun σ σ' h o => h.ofr o (by decide))) σ X' ⟨hP.1, hP.1.2.2.1, a1, a2⟩ hF hc hX hXm
    obtain ⟨σ', r, F, H, q, l, u⟩ := this
    exact ⟨σ', r.mono (by have := len_le_total h1; have := len_le_total h2; have := slotK_ge L; omega),
      F, H, q, l, u⟩

theorem sE_ok {W Xm X k : ℕ} {L : List (List ℕ)} {w : List ℕ} (hs : LibSmall W L)
    (hq : ∀ v ∈ qE0, v ≤ W) :
    SlotRun W (total L + L.length + 8) Xm sE (if k = 3 then w else qE0) (QInv W X k L w) (QInv W X k L w)
      (slotK L + slotK L + 5) := by
  have := slot_ite (W := W) (S := total L + L.length + 8) (Xm := Xm) (j := 3) (c := cpPart "oe" 0)
    (c' := pushLits qE0) (w := w) (w' := qE0) (P := QInv W X k L w) (P' := QInv W X k L w)
    (K := slotK L) (K' := slotK L) ?_ (lits_slot hq (by unfold qLen; omega))
    (fun σ h => by have := hs.1; have := h.2.2.2.1.2.2.2.2; rw [h.2.2.2.2]; omega) (decide (k = 3))
    (fun σ h => by rw [h.2.2.2.2]; simp) (by have := hs.1; omega)
  · simpa [sE] using this
  · intro σ X' hP hF hc hX hXm
    have hk : k = 3 := by rw [← hP.1.2.2.2.2]; exact hP.2
    obtain ⟨ie, hie, a1, hw⟩ := hP.1.2.2.2.1.2.2.2.1 hk
    subst hw
    have := (slotP_ok (Xm := Xm) (ix := "oe") (d := 0) (B := QInv W X k L L[ie]) (by decide) (by decide)
      hie (by omega) (by omega) hs (fun σ σ' h o => h.ofr o (by decide))) σ X' ⟨hP.1, hP.1.2.2.1, a1⟩ hF hc
      (by simpa using hX) hXm
    obtain ⟨σ', r, F, H, q, l, u⟩ := this
    exact ⟨σ', r.mono (by have := len_le_total hie; have := slotK_ge L; omega), by simpa using F, H, q, l, u⟩

/-- The head and the new state. -/
noncomputable def hdW (τ : Env) (L : List (List ℕ)) (ps : List (ℕ × ℕ)) : List ℕ :=
  τ.vars "Nt" :: (17 + (toWord (planW L ps)).length) :: τ.vars "Nw" :: (hsV.map τ.vars ++ toWord (planW L ps))

/-- The split of the output at the real query. -/
theorem kW_split (k : ℕ) (w : List ℕ) (hk : k ≤ 3) :
    ∃ pre post, kW k w = pre ++ w ++ post ∧ post ≠ [] ∧
      pre.length = 6 + (if 1 ≤ k then qA0.length else 0) + (if 2 ≤ k then qB0.length else 0) +
        (if 3 ≤ k then qC0.length else 0) := by
  have hF : qF0 ≠ [] := by simp [qF0, word_simps]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · exact ⟨[3 + w.length + qB0.length + qC0.length, qE0.length, qF0.length, w.length, qB0.length,
      qC0.length], qB0 ++ qC0 ++ qE0 ++ qF0, by simp [kW, sw5In_eq], by simp [hF], by simp⟩
  · exact ⟨[3 + qA0.length + w.length + qC0.length, qE0.length, qF0.length, qA0.length, w.length,
      qC0.length] ++ qA0, qC0 ++ qE0 ++ qF0, by simp [kW, sw5In_eq], by simp [hF], by simp; omega⟩
  · exact ⟨[3 + qA0.length + qB0.length + w.length, qE0.length, qF0.length, qA0.length, qB0.length,
      w.length] ++ qA0 ++ qB0, qE0 ++ qF0, by simp [kW, sw5In_eq], by simp [hF], by simp; omega⟩
  · exact ⟨[3 + qA0.length + qB0.length + qC0.length, w.length, qF0.length, qA0.length, qB0.length,
      qC0.length] ++ qA0 ++ qB0 ++ qC0, qF0, by simp [kW, sw5In_eq], hF, by simp; omega⟩

/-- The exponents of the guard by kind. -/
def kD (dS dF dC dK k : ℕ) : ℕ := if k = 0 then dS else if k = 1 then dF else if k = 2 then dC else dK

theorem mem_toWord_bound {L : List (List ℕ)} {v W : ℕ} (hv : v ∈ toWord L) (h1 : total L + L.length ≤ W)
    (h2 : ∀ w ∈ L, ∀ x ∈ w, x ≤ W) : v ≤ W := by
  rw [toWord_words] at hv
  rcases List.mem_cons.1 hv with rfl | hv
  · omega
  · rcases mem_frames hv with ⟨w, hw, rfl⟩ | ⟨w, hw, hx⟩
    · have := len_le_total (L := L) (i := L.idxOf w) (List.idxOf_lt_length_of_mem hw)
      rw [List.getElem_idxOf] at this; omega
    · exact h2 w hw v hx

/-- The offset of the real query in the query of the switch. -/
noncomputable def kOff (k : ℕ) : ℕ := 6 + (if 1 ≤ k then qA0.length else 0) + (if 2 ≤ k then qB0.length else 0) +
  (if 3 ≤ k then qC0.length else 0)

theorem setQ_run {W k h wl : ℕ} {σ : Env} (hk : k ≤ 3) (hqk : σ.vars "qk" = k)
    (ha0 : σ.vars "a0" = h + 6) (hb0 : σ.vars "b0" = h + 6 + (if k = 0 then wl else qA0.length))
    (hc0 : σ.vars "c0" = h + 6 + (if k = 0 then wl else qA0.length) + (if k = 1 then wl else qB0.length))
    (he0 : σ.vars "e0" = h + 6 + (if k = 0 then wl else qA0.length) + (if k = 1 then wl else qB0.length) +
      (if k = 2 then wl else qC0.length))
    (hpo : σ.vars "po" = h + 6 + (if k = 0 then wl else qA0.length) + (if k = 1 then wl else qB0.length) +
      (if k = 2 then wl else qC0.length) + (if k = 3 then wl else qE0.length) + qF0.length)
    (hW : h + 6 + qLen + wl ≤ W) :
    ∃ σ', Run (W + 1) setQ σ σ' 30 ∧ σ'.vars "qa" = h + kOff k ∧ σ'.vars "ql" = wl ∧
      (∀ y, y ≠ "qa" → y ≠ "ql" → σ'.vars y = σ.vars y) ∧ σ'.arrs = σ.arrs ∧ σ'.out = σ.out := by
  have hq : qA0.length + qB0.length + qC0.length + qE0.length + qF0.length = qLen := rfl
  have ev : ∀ x v, σ.vars x = v → v ≤ W → (Expr.var x).evalB (W + 1) σ = some v := fun x v h hv =>
    ev_var h (by omega)
  have c : ∀ j, j ≤ 3 → (Cond.eq (.var "qk") (.lit j)).evalB (W + 1) σ = some (k == j) := fun j hj =>
    evalB_condEq (ev "qk" k hqk (by omega)) (evalB_lit (by omega))
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · simp only [ite_true] at hb0
    obtain ⟨σ1, r1, o1⟩ := asg_run (x := "qa") (ev "a0" _ ha0 (by omega))
    obtain ⟨σ2, r2, o2⟩ := asg_run (x := "ql") (B := W + 1) (σ := σ1)
      (ev_sub (ev_var (by rw [o1.vars "b0" (by decide), hb0]) (by omega))
        (ev_var (by rw [o1.vars "a0" (by decide), ha0]) (by omega)) (by omega))
    refine ⟨σ2, (Run.ite_true (by rw [c 0 (by omega)]; rfl) (Run.seq r1 r2)).mono (by simp [Cond.size, Expr.size]),
      by rw [o2.vars "qa" (by decide), o1.self]; simp [kOff], by rw [o2.self]; omega,
      fun y h1 h2 => by rw [o2.vars y h2, o1.vars y h1], by rw [o2.arrs, o1.arrs], by rw [o2.out, o1.out]⟩
  · simp only [ite_true, show (1 : ℕ) ≠ 0 by omega, ite_false] at hb0 hc0
    obtain ⟨σ1, r1, o1⟩ := asg_run (x := "qa") (ev "b0" _ hb0 (by omega))
    obtain ⟨σ2, r2, o2⟩ := asg_run (x := "ql") (B := W + 1) (σ := σ1)
      (ev_sub (ev_var (by rw [o1.vars "c0" (by decide), hc0]) (by omega))
        (ev_var (by rw [o1.vars "b0" (by decide), hb0]) (by omega)) (by omega))
    refine ⟨σ2, (Run.ite_false (by rw [c 0 (by omega)]; rfl) (Run.ite_true (by rw [c 1 (by omega)]; rfl)
      (Run.seq r1 r2))).mono (by simp [Cond.size, Expr.size]),
      by rw [o2.vars "qa" (by decide), o1.self]; simp [kOff]; omega, by rw [o2.self]; omega,
      fun y h1 h2 => by rw [o2.vars y h2, o1.vars y h1], by rw [o2.arrs, o1.arrs], by rw [o2.out, o1.out]⟩
  · simp only [ite_true, show (2 : ℕ) ≠ 0 by omega, show (2 : ℕ) ≠ 1 by omega, ite_false] at hc0 he0
    obtain ⟨σ1, r1, o1⟩ := asg_run (x := "qa") (ev "c0" _ hc0 (by omega))
    obtain ⟨σ2, r2, o2⟩ := asg_run (x := "ql") (B := W + 1) (σ := σ1)
      (ev_sub (ev_var (by rw [o1.vars "e0" (by decide), he0]) (by omega))
        (ev_var (by rw [o1.vars "c0" (by decide), hc0]) (by omega)) (by omega))
    refine ⟨σ2, (Run.ite_false (by rw [c 0 (by omega)]; rfl) (Run.ite_false (by rw [c 1 (by omega)]; rfl)
      (Run.ite_true (by rw [c 2 (by omega)]; rfl) (Run.seq r1 r2)))).mono (by simp [Cond.size, Expr.size]),
      by rw [o2.vars "qa" (by decide), o1.self]; simp [kOff]; omega, by rw [o2.self]; omega,
      fun y h1 h2 => by rw [o2.vars y h2, o1.vars y h1], by rw [o2.arrs, o1.arrs], by rw [o2.out, o1.out]⟩
  · simp only [show (3 : ℕ) ≠ 0 by omega, show (3 : ℕ) ≠ 1 by omega, show (3 : ℕ) ≠ 2 by omega,
      ite_false, ite_true] at he0 hpo
    obtain ⟨σ1, r1, o1⟩ := asg_run (x := "qa") (ev "e0" _ he0 (by omega))
    obtain ⟨σ2, r2, o2⟩ := asg_run (x := "ql") (B := W + 1) (σ := σ1)
      (ev_sub (ev_sub (ev_var (by rw [o1.vars "po" (by decide), hpo]) (by omega))
        (ev_var (by rw [o1.vars "e0" (by decide), he0]) (by omega)) (by omega))
        (evalB_lit (n := qF0.length) (by omega)) (by omega))
    refine ⟨σ2, (Run.ite_false (by rw [c 0 (by omega)]; rfl) (Run.ite_false (by rw [c 1 (by omega)]; rfl)
      (Run.ite_false (by rw [c 2 (by omega)]; rfl) (Run.seq r1 r2)))).mono (by simp [Cond.size, Expr.size]),
      by rw [o2.vars "qa" (by decide), o1.self]; simp [kOff]; omega, by rw [o2.self]; omega,
      fun y h1 h2 => by rw [o2.vars y h2, o1.vars y h1], by rw [o2.arrs, o1.arrs], by rw [o2.out, o1.out]⟩

theorem finSel_run {W k eS eF eC eK dS dF dC dK K : ℕ} {σ σ' : Env} (hk : k ≤ 3) (hqk : σ.vars "qk" = k)
    (hW : 3 ≤ W) (h : Run (W + 1) (finCallM (kE eS eF eC eK k) (kD dS dF dC dK k)) σ σ' K) :
    Run (W + 1) (finSel eS eF eC eK dS dF dC dK) σ σ' (K + 20) := by
  have c : ∀ j, j ≤ 3 → (Cond.eq (.var "qk") (.lit j)).evalB (W + 1) σ = some (k == j) := fun j hj =>
    evalB_condEq (ev_var hqk (by omega)) (evalB_lit (by omega))
  unfold finSel
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 by omega) with rfl | rfl | rfl | rfl
  · exact (Run.ite_true (by rw [c 0 (by omega)]; rfl) h).mono (by simp [Cond.size, Expr.size]; omega)
  · exact (Run.ite_false (by rw [c 0 (by omega)]; rfl) (Run.ite_true (by rw [c 1 (by omega)]; rfl) h)).mono
      (by simp [Cond.size, Expr.size]; omega)
  · exact (Run.ite_false (by rw [c 0 (by omega)]; rfl) (Run.ite_false (by rw [c 1 (by omega)]; rfl)
      (Run.ite_true (by rw [c 2 (by omega)]; rfl) h))).mono (by simp [Cond.size, Expr.size]; omega)
  · exact (Run.ite_false (by rw [c 0 (by omega)]; rfl) (Run.ite_false (by rw [c 1 (by omega)]; rfl)
      (Run.ite_false (by rw [c 2 (by omega)]; rfl) h))).mono (by simp [Cond.size, Expr.size]; omega)

theorem sw5In_le {W : ℕ} {A B C E F : List ℕ} (h : ∀ v ∈ A ++ B ++ C ++ E ++ F, v ≤ W)
    (hl : 3 + A.length + B.length + C.length + E.length + F.length ≤ W) :
    ∀ v ∈ sw5In A B C E F, v ≤ W := by
  intro v hv
  have e : sw5In A B C E F = [3 + A.length + B.length + C.length, E.length, F.length, A.length, B.length,
      C.length] ++ (A ++ B ++ C ++ E ++ F) := by rw [sw5In_eq]; simp
  rw [e, List.mem_append] at hv
  rcases hv with hv | hv
  · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  · exact h v hv

set_option maxRecDepth 20000 in
set_option maxHeartbeats 1000000 in
/-- **The output of a round with a call.** -/
theorem tailC_run {W X k eS eF eC eK dS dF dC dK : ℕ} {L : List (List ℕ)} {ps : List (ℕ × ℕ)}
    {w : List ℕ} {τ : Env}
    (hW : τ.vars "W" = W) (hW32 : 1024 ≤ W) (hq : QInv W X k L w τ) (hs : LibSmall W L)
    (hPR : PreAt "PR" (prW ps) τ) (hnp : τ.vars "np" = ps.length) (hps : ∀ p ∈ ps, p.1 + p.2 ≤ L.length)
    (hs17 : ∀ y ∈ "Nt" :: "Nw" :: hsV, τ.vars y ≤ W) (hX : X ≤ W)
    (hBig : 64 * ((ps.length + 4) * (total L + L.length + qLen + 64)) ≤ W)
    (hFv : ∀ v ∈ qA0 ++ qB0 ++ qC0 ++ qE0 ++ qF0, v ≤ W)
    (hwl : w.length ≤ 2 * total L + L.length + 8) (hwv : ∀ v ∈ w, v ≤ W) :
    ∃ σ' K, Run (W + 1) (tailC eS eF eC eK dS dF dC dK) τ σ' K ∧
      K ≤ 40 * (total (planW L ps) + (planW L ps).length) + 100 * ps.length + 8 * slotK L +
        72 * (hdW τ L ps ++ kW k w).length +
        60 * (kE eS eF eC eK k + 1) + 30 * 2 ^ kD dS dF dC dK k + 8 * qLen + 2000 ∧
      σ'.out = τ.out ++ (hdW τ L ps ++ kW k w) ∧
      σ'.vars "ovf" = (if guardOK W (kE eS eF eC eK k) (kD dS dF dC dK k) X w ∧
        maxEntry (hdW τ L ps ++ kW k w) < W / 32 / 32 then 0 else 1) := by
  obtain ⟨hgX, hov, hl, hK, hqk⟩ := hq
  have hk3 : k ≤ 3 := hK.2.2.2.2
  have hs1 := hs.1
  have hP1 : ps.length * (total L + L.length) ≤ (ps.length + 4) * (total L + L.length + qLen + 64) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hP2 : (ps.length + 1) * (total L + L.length + 1) ≤ (ps.length + 4) * (total L + L.length + qLen + 64) :=
    Nat.mul_le_mul (by omega) (by omega)
  have hP3 : ps.length ≤ (ps.length + 4) * (total L + L.length + qLen + 64) := by
    have := Nat.le_mul_of_pos_right (ps.length + 4) (show 0 < total L + L.length + qLen + 64 by omega); omega
  -- head and state
  obtain ⟨σ1, r1, F1, O1⟩ := wrHS_run (W := W) (L := L) (ps := ps) hl.at_ hPR hnp hps (hl.arr "OB")
    (by omega) (by omega) hs.2 (by rw [hl.arr]; omega) hs17
  have hq1 : QInv W X k L w σ1 := QInv.ofr ⟨hgX, hov, hl, hK, hqk⟩ O1 (by decide)
  set H := hdW τ L ps
  have hH : H = τ.vars "Nt" :: (17 + (toWord (planW L ps)).length) :: τ.vars "Nw" ::
      (hsV.map τ.vars ++ toWord (planW L ps)) := rfl
  rw [← hH] at F1
  have hpsz := planW_sub_size L ps
  have hlw := length_toWord_words (planW L ps)
  have hHl : H.length = 20 + (toWord (planW L ps)).length := by simp [hH, hsV]; omega
  have hHl' : H.length ≤ 21 + (ps.length + 4) * (total L + L.length + qLen + 64) := by
    rw [hHl, hlw]; omega
  have hqL : qA0.length + qB0.length + qC0.length + qE0.length + qF0.length = qLen := rfl
  -- the query
  have hA := sA_ok (Xm := H.length + 6 + qLen + 2 * total L + L.length + 8) (X := X) (k := k) (w := w) hs
    (fun v hv => hFv v (by simp [hv]))
  have hB := sB_ok (Xm := H.length + 6 + qLen + 2 * total L + L.length + 8) (X := X) (k := k) (w := w) hs
    (fun v hv => hFv v (by simp [hv]))
  have hC := sC_ok (Xm := H.length + 6 + qLen + 2 * total L + L.length + 8) (X := X) (k := k) (w := w) hs
    (fun v hv => hFv v (by simp [hv]))
  have hE := sE_ok (Xm := H.length + 6 + qLen + 2 * total L + L.length + 8) (X := X) (k := k) (w := w) hs
    (fun v hv => hFv v (by simp [hv]))
  have hst : ∀ σ σ', QInv W X k L w σ → OFr σ σ' qW → QInv W X k L w σ' :=
    fun σ σ' h o => h.ofr o (by decide)
  have hA0 : qA0.length ≤ qLen := by unfold qLen; omega
  have hB0 : qB0.length ≤ qLen := by unfold qLen; omega
  have hC0 : qC0.length ≤ qLen := by unfold qLen; omega
  have hE0 : qE0.length ≤ qLen := by unfold qLen; omega
  have l0 : (if k = 0 then w else qA0).length ≤ w.length + qLen := by split_ifs <;> omega
  have l1 : (if k = 1 then w else qB0).length ≤ w.length + qLen := by split_ifs <;> omega
  have l2 : (if k = 2 then w else qC0).length ≤ w.length + qLen := by split_ifs <;> omega
  have l3 : (if k = 3 then w else qE0).length ≤ w.length + qLen := by split_ifs <;> omega
  have hF0 : qF0.length ≤ qLen := by unfold qLen; omega
  have hc4 : 4 * (total L + L.length + qLen + 64) ≤ (ps.length + 4) * (total L + L.length + qLen + 64) :=
    Nat.mul_le_mul_right _ (by omega)
  have hl1 : H.length + 6 + (if k = 0 then w else qA0).length + (if k = 1 then w else qB0).length +
      (if k = 2 then w else qC0).length + (if k = 3 then w else qE0).length + qF0.length +
      (total L + L.length + 8) + 1 ≤ W := by omega
  have hl2 : H.length + 6 + (if k = 0 then w else qA0).length + (if k = 1 then w else qB0).length +
      (if k = 2 then w else qC0).length ≤ H.length + 6 + qLen + 2 * total L + L.length + 8 := by
    have : (if k = 0 then w else qA0).length + (if k = 1 then w else qB0).length +
        (if k = 2 then w else qC0).length ≤ w.length + qLen := by
      split_ifs <;> simp_all <;> omega
    omega
  obtain ⟨σ2, r2, F2, hq2, ha0, hb0, hc0, he0, c2, u2⟩ := wrQ_run (W := W) hA hB hC hE
    (fun v hv => hFv v (by simp [hv])) hst hst hst hst hst hq1 F1 (by rw [O1.len, hl.arr]) hl1 hl2
  -- marking the real query
  have hlenkW : (kW k w).length = 6 + (if k = 0 then w else qA0).length + (if k = 1 then w else qB0).length +
      (if k = 2 then w else qC0).length + (if k = 3 then w else qE0).length + qF0.length := by
    simp [kW, sw5In_eq]; omega
  have hli : ∀ (b : Bool) (q : List ℕ), (if b = true then w else q).length = (if b = true then w.length else q.length) :=
    fun b q => by cases b <;> rfl
  obtain ⟨σ3, r3, hqa3, hql3, v3, a3, u3⟩ := setQ_run (W := W) (k := k) (h := H.length) (wl := w.length) hk3
    hq2.2.2.2.2 ha0 (by rw [hb0]; split_ifs <;> rfl) (by rw [hc0]; split_ifs <;> rfl)
    (by rw [he0]; split_ifs <;> rfl)
    (by rw [F2.pos, List.length_append, show sw5In (if k = 0 then w else qA0) (if k = 1 then w else qB0)
        (if k = 2 then w else qC0) (if k = 3 then w else qE0) qF0 = kW k w from rfl, hlenkW]
        split_ifs <;> simp_all <;> omega)
    (by omega)
  -- the end
  obtain ⟨pk, post, hsplit, hpost, hpkl⟩ := kW_split k w hk3
  have hF3 : Filled "OB" "po" ((H ++ pk) ++ w ++ post) σ3 := by
    have := F2.congr (v3 "po" (by decide) (by decide)) (by rw [a3])
    rwa [show sw5In (if k = 0 then w else qA0) (if k = 1 then w else qB0) (if k = 2 then w else qC0)
      (if k = 3 then w else qE0) qF0 = kW k w from rfl, hsplit, ← List.append_assoc, ← List.append_assoc] at this
  have hoeq : (H ++ pk) ++ w ++ post = H ++ kW k w := by rw [hsplit]; simp
  have hol : (H ++ kW k w).length ≤ H.length + 6 + 4 * (w.length + qLen) + qLen := by
    rw [List.length_append, hlenkW]; omega
  have hFvals : ∀ v ∈ H ++ kW k w, v ≤ W := by
    intro v hv
    rcases List.mem_append.1 hv with hv | hv
    · rw [hH] at hv
      simp only [List.mem_cons, List.mem_append, List.mem_map] at hv
      rcases hv with rfl | rfl | rfl | ⟨y, hy, rfl⟩ | hv
      · exact hs17 "Nt" (by simp)
      · rw [hlw]; omega
      · exact hs17 "Nw" (by simp)
      · exact hs17 y (by simp [hy])
      · exact mem_toWord_bound hv (by omega) (fun w' hw' x hx => by
          obtain ⟨p, hp, hw''⟩ := List.mem_flatMap.1 hw'
          unfold rng at hw''
          exact hs.2 w' (List.mem_of_mem_drop (List.mem_of_mem_take hw'')) x hx)
    · refine sw5In_le (W := W) (fun v hv => ?_) ?_ v hv
      · simp only [List.mem_append] at hv
        rcases hv with (((hv | hv) | hv) | hv) | hv
        all_goals first
          | (split_ifs at hv
             · exact hwv v hv
             · exact hFv v (by simp [hv]))
          | exact hFv v (by simp [hv])
      · omega
  have hW3 : σ3.vars "W" = W := by rw [v3 "W" (by decide) (by decide), hq2.2.2.1.w]
  obtain ⟨σ4, r4, o4, ov4⟩ := finCallM_run (W := W) (e := kE eS eF eC eK k) (d := kD dS dF dC dK k) (X := X)
    (σ := σ3) (pre := H ++ pk) (q := w) (post := post) hW3 (by omega) hF3 hpost
    (by rw [hqa3, List.length_append, hpkl]; rfl) hql3
    (by rw [v3 "gX" (by decide) (by decide), hq2.1]) (by rw [a3, c2])
    (by rw [hoeq]; omega) (by rw [hoeq]; exact hFvals) hX
    (by rw [v3 "ovf" (by decide) (by decide), hq2.2.1])
  rw [hoeq] at o4 ov4
  refine ⟨σ4, _, Run.seq r1 (Run.seq r2 (Run.seq r3 (finSel_run hk3 (by rw [v3 "qk" (by decide) (by decide),
    hq2.2.2.2.2]) (by omega) r4))), ?_, ?_, ov4⟩
  · generalize 2 ^ kD dS dF dC dK k = P2
    generalize kE eS eF eC eK k = E2
    have e1 : ((H ++ pk) ++ w ++ post).length = (H ++ kW k w).length := by rw [hoeq]
    have e2 : qF0.length ≤ qLen := hF0
    omega
  · rw [o4, u3, u2, O1.out]

end Lax185574Proofs.ResolveRam.Glue
