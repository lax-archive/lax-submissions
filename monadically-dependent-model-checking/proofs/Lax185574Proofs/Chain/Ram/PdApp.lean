import Lax185574Proofs.Chain.Ram.PdState

/-!
One application of the predamping rules.

The command `pdApp` computes the types for the current `S` (`prepCom`),
looks for the first vertex of rule (R1), then of (R2) and of (R3) by the
pointer scans, and adds the vertex found to `S` (array `inS`, list `Sl`
of length `sc`), or sets `stop` if no rule applies. The vertex found is
the one of `pdStep` (`rules_val`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram Lax185574Proofs.Chain

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

/-- The list `sl` of length `sc` enumerates `S` without repetition. -/
structure SlOK (n : ℕ) (S : Finset (Fin n)) (sl : ℕ → ℕ) (sc : ℕ) : Prop where
  card : S.card = sc
  lt : ∀ j < sc, sl j < n
  mem : ∀ j < sc, inBN S (sl j)
  all : ∀ s : Fin n, s ∈ S → ∃ j < sc, sl j = s

theorem SlOK.empty : SlOK n ∅ (fun _ => 0) 0 :=
  ⟨by simp, fun _ h => absurd h (Nat.not_lt_zero _), fun _ h => absurd h (Nat.not_lt_zero _),
    fun s hs => absurd hs (notMem_empty s)⟩

theorem SlOK.insert {S : Finset (Fin n)} {sl : ℕ → ℕ} {sc : ℕ} (h : SlOK n S sl sc) {w : Fin n}
    (hw : w ∉ S) : SlOK n (insert w S) (fun j => if j = sc then w else sl j) (sc + 1) :=
  ⟨by rw [card_insert_of_notMem hw, h.card],
    fun j hj => by split_ifs with hjs; exact w.2; exact h.lt j (by omega),
    fun j hj => by
      split_ifs with hjs
      · exact ⟨w.2, mem_insert_self _ _⟩
      · obtain ⟨hl, hm⟩ := h.mem j (by omega); exact ⟨hl, mem_insert_of_mem hm⟩,
    fun s hs => by
      rcases mem_insert.1 hs with rfl | hs
      · exact ⟨sc, by omega, by simp⟩
      · obtain ⟨j, hj, hjs⟩ := h.all s hs
        exact ⟨j, by omega, by simp [show j ≠ sc by omega, hjs]⟩⟩

theorem SlOK.forall_iff {S : Finset (Fin n)} {sl : ℕ → ℕ} {sc : ℕ} (h : SlOK n S sl sc)
    (F : ℕ → Prop) : (∀ s : Fin n, s ∈ S → F s) ↔ ∀ j < sc, F (sl j) := by
  constructor
  · intro hF j hj
    obtain ⟨hl, hm⟩ := h.mem j hj
    exact hF ⟨sl j, hl⟩ hm
  · intro hF s hs
    obtain ⟨j, hj, hjs⟩ := h.all s hs
    rw [← hjs]; exact hF j hj

/-! ### The rules on numbers -/

variable (G) in
/-- Rule (R1) on numbers. -/
def r1N (L : ℕ → ℕ) (t1 w : ℕ) : Prop := t1 < crossN G L w

variable (G) in
/-- Rule (R2) on numbers. -/
def r2N (L sl : ℕ → ℕ) (sc t2 w : ℕ) : Prop := ∀ j < sc, t2 < hamN G L w (sl j)

/-- Rule (R3) on numbers. -/
def r3N (n : ℕ) (pf L sl : ℕ → ℕ) (sc t3 w : ℕ) : Prop := ∀ j < sc, t3 ≤ betwN n pf L w (sl j)

/-- **The step of the procedure, as computed.** -/
theorem rules_val (o : VOrder (Fin n)) (r : ℕ) (A : Finset (Fin n)) (q κ : ℕ)
    {S : Finset (Fin n)} {sl : ℕ → ℕ} {sc : ℕ} (hS : SlOK n S sl sc) :
    (pdStep G (tpP G r) o A q κ S).map Fin.val =
      ((firstN n (r1N G (lbl n (tpN G (A ∪ S) r)) (3 * (q + 1) * κ))) <|>
      ((firstN n (r2N G (lbl n (tpN G (A ∪ S) r)) sl sc (5 * (3 * (q + 1)) * κ * κ))) <|>
      (firstN n (r3N n (posN o) (lbl n (tpN G (A ∪ S) r)) sl sc (2 * (3 * (q + 1)) * κ))))) := by
  rw [pdStep_val]
  have e1 : (firstN n fun v => ∃ h : v < n, Rule1 G (tpP G r) o A q κ S ⟨v, h⟩) =
      firstN n (r1N G (lbl n (tpN G (A ∪ S) r)) (3 * (q + 1) * κ)) := by
    refine firstN_congr fun v hv => ?_
    unfold Rule1 r1N
    simp only [crossCnt_eq]
    exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hv, h⟩⟩
  have e2 : (firstN n fun v => ∃ h : v < n, Rule2 G (tpP G r) o A q κ S ⟨v, h⟩) =
      firstN n (r2N G (lbl n (tpN G (A ∪ S) r)) sl sc (5 * (3 * (q + 1)) * κ * κ)) := by
    refine firstN_congr fun v hv => ?_
    unfold Rule2 r2N
    constructor
    · rintro ⟨_, h⟩ j hj
      obtain ⟨hl, hm⟩ := hS.mem j hj
      have := h ⟨sl j, hl⟩ hm
      rwa [ham_eq] at this
    · intro h
      refine ⟨hv, fun s hs => ?_⟩
      obtain ⟨j, hj, hjs⟩ := hS.all s hs
      have := h j hj
      rw [hjs] at this
      rw [ham_eq]; exact this
  have e3 : (firstN n fun v => ∃ h : v < n, Rule3 (tpP G r) o A q κ S ⟨v, h⟩) =
      firstN n (r3N n (posN o) (lbl n (tpN G (A ∪ S) r)) sl sc (2 * (3 * (q + 1)) * κ)) := by
    refine firstN_congr fun v hv => ?_
    unfold Rule3 r3N
    constructor
    · rintro ⟨_, h⟩ j hj
      obtain ⟨hl, hm⟩ := hS.mem j hj
      have := h ⟨sl j, hl⟩ hm
      rwa [betw_eq] at this
    · intro h
      refine ⟨hv, fun s hs => ?_⟩
      obtain ⟨j, hj, hjs⟩ := hS.all s hs
      have := h j hj
      rw [hjs] at this
      rw [betw_eq]; exact this
  rw [e1, e2, e3]

/-- Pointers stay correct when the parameter set grows and a vertex is
appended to the list. -/
theorem PtrOK.grow {sc : ℕ} {F F' : ℕ → ℕ → Prop} {sl : ℕ → ℕ} {P : ℕ → ℕ}
    (h : PtrOK n sc F sl P) (hF : ∀ w s, w < n → s < n → F w s → F' w s)
    (hsl : ∀ j < sc, sl j < n) (w0 : ℕ) :
    PtrOK n (sc + 1) F' (fun j => if j = sc then w0 else sl j) P := fun w hw => by
  obtain ⟨h1, h2⟩ := h w hw
  refine ⟨by omega, fun j hj => ?_⟩
  have hjs : j ≠ sc := by omega
  simp only [hjs, if_false]
  exact hF w (sl j) hw (hsl j (by omega)) (h2 j hj)

/-! ### Rule (R1) -/

/-- Rule (R1) and clearing the counts. -/
def r1Phase : Com :=
  .seq (scanFirst r1Tst) (.seq (matFill "cnt" (.lit 0)) (rowFill "sz" (.var "b") (.lit 0)))

/-- The bound on values of the procedure. -/
def PdBound (n B' : ℕ) : Prop := n * (n + 4) + 3 * n + 10 < B'

variable {r : ℕ} {A : Finset (Fin n)} {pf : ℕ → ℕ} {t1 t2 t3 : ℕ}

theorem r1Phase_run {B' : ℕ} (hB' : PdBound n B') (ht1 : t1 < B') {L : ℕ → ℕ}
    (hL : IsLabels n L) {σ : Env} (hF : PdFix n r G A pf t1 t2 t3 σ)
    (hlab : Vec σ "lab" n L) (hcnt : Mat σ "cnt" n (fun u c => cntN G L u c))
    (hsz : Vec σ "sz" n (fun c => szN n L c)) :
    ∃ σ', Run B' r1Phase σ σ' (n * (n * 200 + 200) + 100) ∧ PdFix n r G A pf t1 t2 t3 σ' ∧
      σ'.vars "fw" = (firstN n (r1N G L t1)).getD n ∧
      (∀ a, a ∉ ["cnt", "sz"] → σ'.arrs a = σ.arrs a) ∧
      (∀ x, x ∉ r1Phase.wvars → σ'.vars x = σ.vars x) ∧
      Mat σ' "cnt" n (fun _ _ => 0) ∧ Vec σ' "sz" n (fun _ => 0) := by
  unfold PdBound at hB'
  have hnn : n * (n + 4) = n * n + 4 * n := by ring
  obtain ⟨σ1, K1, hr1, ⟨hF1, hk1⟩, hfw1, hK1⟩ :=
    scanFirst_run (B := B') (n := n) (Kt := n * 120 + 40) (tst := r1Tst)
      (fun τ => PdFix n r G A pf t1 t2 t3 τ ∧ Keep σ ["lab", "cnt", "sz"] τ) (fun _ => 0)
      (r1N G L t1) (by omega) (fun τ h => h.1.hn)
      (fun τ x h => ⟨h.1.setVar (by simp [fixVars]) _, h.2.setVar _ _⟩)
      (fun τ x h => ⟨h.1.setVar (by simp [fixVars]) _, h.2.setVar _ _⟩)
      (fun _ _ => rfl) (fun _ _ => rfl)
      (fun τ k h hwk hk => by
        obtain ⟨τ', hr, hC', hok, harr, hfr⟩ :=
          r1Tst_run (B := B') (t := t1) (G := G) (L := L) (pf := pf)
            (fun ρ => PdFix n r G A pf t1 t2 t3 ρ ∧ Keep σ ["lab", "cnt", "sz"] ρ) hL
            (by omega) ht1
            (fun ρ h => ⟨h.1.hn, h.1.hadj, hlab.of_eq (h.2 "lab" (by simp)), h.1.hpos,
              h.1.lvec "mark" (by simp)⟩)
            (fun ρ h => hcnt.of_eq (h.2 "cnt" (by simp)))
            (fun ρ h => hsz.of_eq (h.2 "sz" (by simp))) (fun ρ h => h.1.ht1)
            (fun ρ x v h hx => ⟨h.1.setVar (by
              simp at hx; simp [fixVars]; rcases hx with rfl | rfl | rfl <;> decide) _,
              h.2.setVar _ _⟩) h hwk hk
        exact ⟨τ', _, hr, hC', by rw [hfr "w" (by decide), hwk], hfr "fw" (by decide), hok,
          by simp⟩)
      ⟨hF, fun _ _ => rfl⟩
  obtain ⟨σ2, hr2, ⟨hF2, hk2⟩, hm2⟩ :=
    matFill_run (B := B') (n := n) (K := 7) (arr := "cnt") (e := .lit 0)
      (fun τ => PdFix n r G A pf t1 t2 t3 τ ∧ ∀ a, a ≠ "cnt" → τ.arrs a = σ1.arrs a)
      (fun _ _ => 0) (by omega) (fun τ h => h.1.hn)
      (fun τ x h => ⟨h.1.setVar (by simp [fixVars]) _, by simpa using h.2⟩)
      (fun τ x h => ⟨h.1.setVar (by simp [fixVars]) _, by simpa using h.2⟩)
      (fun τ i x h => ⟨h.1.setArr (by simp [fixArrs]) _ _, fun a ha => by
        simp only [arrs_setArr, if_neg ha]; exact h.2 a ha⟩)
      (fun τ i j h _ _ _ _ => by simp; omega) (by simp) ⟨hF1, fun _ _ => rfl⟩ hF1.lcnt
  obtain ⟨σ3, hr3, ⟨hF3, hk3⟩, hl3, hg3⟩ :=
    rowFill_run (B := B') (n := n) (base := 0) (K := 3) (arr := "sz") (ie := .var "b")
      (e := .lit 0) (fun τ => PdFix n r G A pf t1 t2 t3 τ ∧ ∀ a, a ≠ "sz" → τ.arrs a = σ2.arrs a)
      (fun _ => 0) (by omega) (fun τ h => h.1.hn)
      (fun τ x h => ⟨h.1.setVar (by simp [fixVars]) _, by simpa using h.2⟩)
      (fun τ i x h => ⟨h.1.setArr (by simp [fixArrs]) _ _, fun a ha => by
        simp only [arrs_setArr, if_neg ha]; exact h.2 a ha⟩)
      (fun τ k h hb hk => by simp [hb]; omega) (fun τ k h hb hk => by simp; omega) (by simp)
      ⟨hF2, fun _ _ => rfl⟩ (by rw [hF2.lvec "sz" (by simp)]; omega)
  have hrun : Run B' r1Phase σ σ3 (n * (n * 200 + 200) + 100) :=
    (Run.seq (hr1.mono (show K1 ≤ n * (n * 120 + 40 + 20) + 20 by simpa using hK1))
      (Run.seq hr2 hr3)).mono (by simp; nlinarith)
  have hfw3 : σ3.vars "fw" = σ1.vars "fw" := by
    rw [hr3.frame_var "fw" (by decide), hr2.frame_var "fw" (by decide)]
  refine ⟨σ3, hrun, hF3, hfw3.trans hfw1, fun a ha => ?_, fun x hx => hrun.frame_var x hx,
    hm2.of_eq (hk3 _ (by decide)), ⟨by rw [hl3, hF2.lvec "sz" (by simp)], fun u hu => by
      rw [hg3 u]; simp [hu]⟩⟩
  simp at ha
  rw [hk3 a ha.2, hk2 a ha.1]
  rw [hr1.frame_arr a (by
    have : ∀ b ∈ (scanFirst r1Tst).warrs, b ∈ ([] : List String) := by decide
    exact fun h => by simpa using this a h)]

/-! ### Rules (R2) and (R3) -/

/-- Rules (R2) and (R3), if (R1) found nothing. -/
def r23Phase : Com :=
  .ite (.lt (.var "fw") (.var "n")) .skip
    (.seq (scanFirst (ptrTst "p2" hamTst))
      (.ite (.lt (.var "fw") (.var "n")) .skip (scanFirst (ptrTst "p3" btTst))))

/-- The potential of the two pointer arrays. -/
noncomputable def pdPot (n : ℕ) (τ : Env) : ℕ :=
  (n * 300 + 80) * ptrPot n "p2" τ + (n * 80 + 80) * ptrPot n "p3" τ

theorem pdPot_setVar (n : ℕ) (τ : Env) (x : String) (v : ℕ) :
    pdPot n (τ.setVar x v) = pdPot n τ := rfl

theorem pdPot_of_arrs {τ τ' : Env} (h2 : τ'.arrs "p2" = τ.arrs "p2")
    (h3 : τ'.arrs "p3" = τ.arrs "p3") : pdPot n τ' = pdPot n τ := by
  unfold pdPot ptrPot; rw [h2, h3]

/-- What the pair tests read, besides the fixed state. -/
def pairKeep : List String := ["lab", "Sl", "rep"]

theorem r2Scan_run {B' : ℕ} (hB' : PdBound n B') (ht2 : t2 < B') {L sl : ℕ → ℕ} {sc : ℕ}
    (hL : IsLabels n L) (hsc : sc ≤ n) (hsln : ∀ j < sc, sl j < n)
    {σ : Env} (hF : PdFix n r G A pf t1 t2 t3 σ) (hlab : Vec σ "lab" n L)
    (hscv : σ.vars "sc" = sc) (hsl : ∀ j < sc, (σ.arrs "Sl")[j]? = some (sl j))
    (hmark : Vec σ "mark" n (fun _ => 0))
    (hP : PtrOK n sc (fun w s => t2 < hamN G L w s) sl (fun w => (σ.arrs "p2").getD w 0)) :
    ∃ σ' K, Run B' (scanFirst (ptrTst "p2" hamTst)) σ σ' K ∧ PdFix n r G A pf t1 t2 t3 σ' ∧
      σ'.vars "fw" = (firstN n (r2N G L sl sc t2)).getD n ∧
      PtrOK n sc (fun w s => t2 < hamN G L w s) sl (fun w => (σ'.arrs "p2").getD w 0) ∧
      Vec σ' "mark" n (fun _ => 0) ∧ (∀ a, a ∉ ["p2", "mark"] → σ'.arrs a = σ.arrs a) ∧
      σ'.vars "sc" = sc ∧
      K + (n * 300 + 80) * ptrPot n "p2" σ' ≤
        n * (2 * (n * 300 + 40) + 120) + 20 + (n * 300 + 80) * ptrPot n "p2" σ := by
  unfold PdBound at hB'
  have hnn : n * (n + 4) = n * n + 4 * n := by ring
  let C0 : Env → Prop := fun τ => PdFix n r G A pf t1 t2 t3 τ ∧
    (∀ a, a ∉ ["p2", "mark"] → τ.arrs a = σ.arrs a) ∧ τ.vars "sc" = sc
  let Ctx : Env → Prop := fun τ => C0 τ ∧ Vec τ "mark" n (fun _ => 0)
  obtain ⟨σ', K, hr, ⟨⟨hF', hk', hsc'⟩, hm'⟩, hfw, hP', hK⟩ :=
    ptrScan_run (B := B') (n := n) (sc := sc) (Kq := n * 300 + 40) (pa := "p2") (pt := hamTst)
      (sl := sl) (F := fun w s => t2 < hamN G L w s) Ctx (by decide) (by omega) hsc
      (fun τ h => ⟨h.1.1.hn, h.1.2.2, fun j hj => by
        rw [h.1.2.1 "Sl" (by decide)]; exact hsl j hj, hsln, h.1.1.lvec "p2" (by simp)⟩)
      (fun τ x v h hx => ⟨⟨h.1.1.setVar (by
          simp at hx; simp [fixVars]; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide) _,
          fun a ha => by simpa using h.1.2.1 a ha, by
            have : x ≠ "sc" := by simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
            simp [Ne.symm this, h.1.2.2]⟩, h.2.of_eq rfl⟩)
      (fun τ i v h => ⟨⟨h.1.1.setArr (by simp [fixArrs]) _ _, fun a ha => by
          have : a ≠ "p2" := by intro e; subst e; simp at ha
          simp only [arrs_setArr, if_neg this]; exact h.1.2.1 a ha, by simp [h.1.2.2]⟩,
        h.2.of_eq (by simp)⟩)
      (fun τ k s h hwk hkn hsv hs => by
        obtain ⟨τ', hr, hC', hok, hm', harr, hfr⟩ :=
          hamTst_run (B := B') (μ := t2) (G := G) (L := L) (pf := pf) C0 hL (by omega) ht2
            (fun ρ h => ⟨h.1.hn, h.1.hadj, hlab.of_eq (h.2.1 "lab" (by decide)), h.1.hpos,
              h.1.lvec "mark" (by simp)⟩)
            (fun ρ h => h.1.ht2)
            (fun ρ x v h hx => ⟨h.1.setVar (by
              simp at hx; simp [fixVars]; rcases hx with rfl | rfl | rfl <;> decide) _,
              fun a ha => by simpa using h.2.1 a ha, by
                have : x ≠ "sc" := by simp at hx; rcases hx with rfl | rfl | rfl <;> decide
                simp [Ne.symm this, h.2.2]⟩)
            (fun ρ i v h => ⟨h.1.setArr (by simp [fixArrs]) _ _, fun a ha => by
                have : a ≠ "mark" := by intro e; subst e; simp at ha
                simp only [arrs_setArr, if_neg this]; exact h.2.1 a ha, by simp [h.2.2]⟩)
            h.1 hwk hsv hkn hs h.2
        exact ⟨τ', hr, ⟨hC', hm'⟩, hok, by rw [hfr "w" (by decide), hwk],
          hfr "go" (by decide), hfr "fw" (by decide), harr "p2" (by decide)⟩)
      ⟨⟨hF, fun _ _ => rfl, hscv⟩, hmark⟩ hP
  exact ⟨σ', K, hr, hF', hfw, hP', hm', hk', hsc', hK⟩

theorem r3Scan_run {B' : ℕ} (hB' : PdBound n B') (ht3 : t3 < B') {L sl : ℕ → ℕ} {sc : ℕ}
    (hL : IsLabels n L) (hpf : ∀ z < n, pf z < n) (hsc : sc ≤ n) (hsln : ∀ j < sc, sl j < n)
    {σ : Env} (hF : PdFix n r G A pf t1 t2 t3 σ) (hlab : Vec σ "lab" n L)
    (hrep : Vec σ "rep" n (fun z => ind (isRepN n pf L z)))
    (hscv : σ.vars "sc" = sc) (hsl : ∀ j < sc, (σ.arrs "Sl")[j]? = some (sl j))
    (hP : PtrOK n sc (fun w s => t3 ≤ betwN n pf L w s) sl (fun w => (σ.arrs "p3").getD w 0)) :
    ∃ σ' K, Run B' (scanFirst (ptrTst "p3" btTst)) σ σ' K ∧ PdFix n r G A pf t1 t2 t3 σ' ∧
      σ'.vars "fw" = (firstN n (r3N n pf L sl sc t3)).getD n ∧
      PtrOK n sc (fun w s => t3 ≤ betwN n pf L w s) sl (fun w => (σ'.arrs "p3").getD w 0) ∧
      (∀ a, a ≠ "p3" → σ'.arrs a = σ.arrs a) ∧ σ'.vars "sc" = sc ∧
      K + (n * 80 + 80) * ptrPot n "p3" σ' ≤
        n * (2 * (n * 80 + 40) + 120) + 20 + (n * 80 + 80) * ptrPot n "p3" σ := by
  unfold PdBound at hB'
  let Ctx : Env → Prop := fun τ => PdFix n r G A pf t1 t2 t3 τ ∧
    (∀ a, a ≠ "p3" → τ.arrs a = σ.arrs a) ∧ τ.vars "sc" = sc
  obtain ⟨σ', K, hr, ⟨hF', hk', hsc'⟩, hfw, hP', hK⟩ :=
    ptrScan_run (B := B') (n := n) (sc := sc) (Kq := n * 80 + 40) (pa := "p3") (pt := btTst)
      (sl := sl) (F := fun w s => t3 ≤ betwN n pf L w s) Ctx (by decide) (by omega) hsc
      (fun τ h => ⟨h.1.hn, h.2.2, fun j hj => by
        rw [h.2.1 "Sl" (by decide)]; exact hsl j hj, hsln, h.1.lvec "p3" (by simp)⟩)
      (fun τ x v h hx => ⟨h.1.setVar (by
          simp at hx; simp [fixVars]; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide) _,
          fun a ha => by simpa using h.2.1 a ha, by
            have : x ≠ "sc" := by simp at hx; rcases hx with rfl | rfl | rfl | rfl | rfl <;> decide
            simp [Ne.symm this, h.2.2]⟩)
      (fun τ i v h => ⟨h.1.setArr (by simp [fixArrs]) _ _, fun a ha => by
          simp only [arrs_setArr, if_neg ha]; exact h.2.1 a ha, by simp [h.2.2]⟩)
      (fun τ k s h hwk hkn hsv hs => by
        obtain ⟨τ', hr, hC', hok, harr, hfr⟩ :=
          btTst_run (B := B') (ζ := t3) (G := G) (L := L) (pf := pf) Ctx hL hpf (by omega) ht3
            (fun ρ h => ⟨h.1.hn, h.1.hadj, hlab.of_eq (h.2.1 "lab" (by decide)), h.1.hpos,
              h.1.lvec "mark" (by simp)⟩)
            (fun ρ h => hrep.of_eq (h.2.1 "rep" (by decide)))
            (fun ρ h => h.1.ht3)
            (fun ρ x v h hx => ⟨h.1.setVar (by
              simp at hx; simp [fixVars]; rcases hx with rfl | rfl | rfl <;> decide) _,
              fun a ha => by simpa using h.2.1 a ha, by
                have : x ≠ "sc" := by simp at hx; rcases hx with rfl | rfl | rfl <;> decide
                simp [Ne.symm this, h.2.2]⟩)
            h hwk hsv hkn hs
        exact ⟨τ', hr, hC', hok, by rw [hfr "w" (by decide), hwk],
          hfr "go" (by decide), hfr "fw" (by decide), by rw [harr]⟩)
      ⟨hF, fun _ _ => rfl, hscv⟩ hP
  exact ⟨σ', K, hr, hF', hfw, hP', hk', hsc', hK⟩

theorem getD_lt_or {o : Option ℕ} (h : ∀ w, o = some w → w < n) :
    o.getD n < n ↔ o.isSome := by
  cases o with
  | none => simp
  | some w => simp [h w rfl]

theorem firstN_lt {p : ℕ → Prop} {w : ℕ} (h : firstN n p = some w) : w < n :=
  (firstN_eq_some.1 h).1

/-- The cost of rules (R2) and (R3), besides the potential. -/
def r23Cost (n : ℕ) : ℕ := n * (n * 800 + 400) + 100

theorem r23Phase_run {B' : ℕ} (hB' : PdBound n B') (ht2 : t2 < B') (ht3 : t3 < B')
    {L sl : ℕ → ℕ} {sc : ℕ} (hL : IsLabels n L) (hpf : ∀ z < n, pf z < n) (hsc : sc ≤ n)
    (hsln : ∀ j < sc, sl j < n)
    {σ : Env} (hF : PdFix n r G A pf t1 t2 t3 σ) (hlab : Vec σ "lab" n L)
    (hrep : Vec σ "rep" n (fun z => ind (isRepN n pf L z)))
    (hscv : σ.vars "sc" = sc) (hsl : ∀ j < sc, (σ.arrs "Sl")[j]? = some (sl j))
    (hmark : Vec σ "mark" n (fun _ => 0))
    (hP2 : PtrOK n sc (fun w s => t2 < hamN G L w s) sl (fun w => (σ.arrs "p2").getD w 0))
    (hP3 : PtrOK n sc (fun w s => t3 ≤ betwN n pf L w s) sl (fun w => (σ.arrs "p3").getD w 0))
    (hfw : σ.vars "fw" = (firstN n (r1N G L t1)).getD n) :
    ∃ σ' K, Run B' r23Phase σ σ' K ∧ PdFix n r G A pf t1 t2 t3 σ' ∧
      σ'.vars "fw" = ((firstN n (r1N G L t1)) <|> ((firstN n (r2N G L sl sc t2)) <|>
        (firstN n (r3N n pf L sl sc t3)))).getD n ∧
      PtrOK n sc (fun w s => t2 < hamN G L w s) sl (fun w => (σ'.arrs "p2").getD w 0) ∧
      PtrOK n sc (fun w s => t3 ≤ betwN n pf L w s) sl (fun w => (σ'.arrs "p3").getD w 0) ∧
      Vec σ' "mark" n (fun _ => 0) ∧
      (∀ a, a ∉ ["p2", "p3", "mark"] → σ'.arrs a = σ.arrs a) ∧ σ'.vars "sc" = sc ∧
      K + pdPot n σ' ≤ r23Cost n + pdPot n σ := by
  unfold PdBound at hB'
  have hfwB : σ.vars "fw" ≤ n := by
    rw [hfw]; cases h : firstN n (r1N G L t1) with
    | none => simp
    | some w => have := firstN_lt h; simp; omega
  have hev : (Cond.lt (.var "fw") (.var "n")).evalB B' σ =
      some (decide (σ.vars "fw" < n)) := by
    rw [evalB_condLt (evalB_var (by omega)) (evalB_var (by rw [hF.hn]; omega)), hF.hn]
  cases h1 : firstN n (r1N G L t1) with
  | some w =>
    have hw := firstN_lt h1
    rw [h1] at hfw
    refine ⟨σ, _, Run.ite_true (by rw [hev]; simp [hfw, hw]) Run.skip, hF, by simp [hfw],
      hP2, hP3, hmark, fun _ _ => rfl, hscv, ?_⟩
    simp [r23Cost]
  | none =>
    rw [h1] at hfw
    simp only [Option.getD_none] at hfw
    obtain ⟨σ1, K1, hr1, hF1, hfw1, hP21, hm1, hk1, hsc1, hK1⟩ :=
      r2Scan_run hB' ht2 hL hsc hsln hF hlab hscv hsl hmark hP2
    have hP31 : PtrOK n sc (fun w s => t3 ≤ betwN n pf L w s) sl
        (fun w => (σ1.arrs "p3").getD w 0) := by
      rw [hk1 "p3" (by decide)]; exact hP3
    have hpot1 : ptrPot n "p3" σ1 = ptrPot n "p3" σ := by
      unfold ptrPot; rw [hk1 "p3" (by decide)]
    have hev1 : (Cond.lt (.var "fw") (.var "n")).evalB B' σ1 =
        some (decide (σ1.vars "fw" < n)) := by
      have : σ1.vars "fw" ≤ n := by
        rw [hfw1]; cases h : firstN n (r2N G L sl sc t2) with
        | none => simp
        | some w => have := firstN_lt h; simp; omega
      rw [evalB_condLt (evalB_var (by omega)) (evalB_var (by rw [hF1.hn]; omega)), hF1.hn]
    cases h2 : firstN n (r2N G L sl sc t2) with
    | some w =>
      have hw := firstN_lt h2
      rw [h2] at hfw1
      refine ⟨σ1, _, Run.ite_false (by rw [hev]; simp [hfw]) (Run.seq hr1
        (Run.ite_true (by rw [hev1]; simp [hfw1, hw]) Run.skip)), hF1, by simp [hfw1],
        hP21, hP31, hm1, fun a ha => hk1 a (by simp at ha ⊢; tauto), hsc1, ?_⟩
      unfold pdPot r23Cost
      rw [hpot1]
      simp; nlinarith
    | none =>
      rw [h2] at hfw1
      simp only [Option.getD_none] at hfw1
      have hlab1 : Vec σ1 "lab" n L := hlab.of_eq (hk1 "lab" (by decide))
      have hrep1 : Vec σ1 "rep" n (fun z => ind (isRepN n pf L z)) :=
        hrep.of_eq (hk1 "rep" (by decide))
      have hsl1 : ∀ j < sc, (σ1.arrs "Sl")[j]? = some (sl j) := fun j hj => by
        rw [hk1 "Sl" (by decide)]; exact hsl j hj
      obtain ⟨σ2, K2, hr2, hF2, hfw2, hP32, hk2, hsc2, hK2⟩ :=
        r3Scan_run hB' ht3 hL hpf hsc hsln hF1 hlab1 hrep1 hsc1 hsl1 hP31
      have hpot2 : ptrPot n "p2" σ2 = ptrPot n "p2" σ1 := by
        unfold ptrPot; rw [hk2 "p2" (by decide)]
      refine ⟨σ2, _, Run.ite_false (by rw [hev]; simp [hfw]) (Run.seq hr1
        (Run.ite_false (by rw [hev1]; simp [hfw1]) hr2)), hF2, by simp [hfw2],
        by rw [hk2 "p2" (by decide)]; exact hP21, hP32, hm1.of_eq (hk2 "mark" (by decide)),
        fun a ha => by
          rw [hk2 a (by simp at ha ⊢; tauto), hk1 a (by simp at ha ⊢; tauto)], hsc2, ?_⟩
      unfold pdPot r23Cost
      rw [hpot1] at hK2
      rw [hpot2]
      simp; nlinarith

end Lax185574Proofs.Chain.Ram
