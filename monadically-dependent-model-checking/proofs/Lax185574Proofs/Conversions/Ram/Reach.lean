import Lax185574Proofs.Conversions.Ram.Atomic

/-!
Walks of length five between two parts, by layers.

For a vertex `u` with part `X` and every part `Y`, the program computes
which vertices of `Y` are reached from `u` by an alternating walk of
length five in the bipartite graph on `X` and `Y` with the edges `E`.
The layers are kept for all parts `Y` at once: a right layer is a set of
vertices `b` (each in its own part `Y = 𝒫(b)`), and a left layer is a
matrix `Lm` whose entry `(y, a)` says that `a ∈ X` is reached in the
bipartite graph on `X` and the part with label `y`.
-/

namespace Lax185574Proofs.Conversions.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words

/-- The left layer after the right layer `rin`: `a` lies in the part of
`u` and has an `E`-neighbor `b` in `rin` with label `y`. -/
def LStep (n : ℕ) (L : ℕ → ℕ) (E : ℕ → ℕ → Prop) (u : ℕ) (rin : ℕ → Prop) (y a : ℕ) : Prop :=
  L a = L u ∧ ∃ b < n, L b = y ∧ rin b ∧ E a b

/-- The right layer after the left layer `lin`: `b` has an `E`-neighbor
`a` in the part of `u` that is in `lin` for the label of `b`. -/
def RStep (n : ℕ) (L : ℕ → ℕ) (E : ℕ → ℕ → Prop) (u : ℕ) (lin : ℕ → ℕ → Prop) (b : ℕ) : Prop :=
  ∃ a < n, L a = L u ∧ lin (L b) a ∧ E a b

/-- The index `lab[b] · n + a` of `Lm`. -/
def lmIdx : Expr := .add (.mul (.get "lab" (.var "b")) (.var "n")) (.var "a")

/-- Clear `Lm`. -/
def resetLm : Com := forUp "j" (.mul (.var "n") (.var "n")) (.store "Lm" (.var "j") (.lit 0))

/-- One round of the scan over `b` of the left step. -/
def lbody (rin : String) : Com :=
  .ite (.eq (.get rin (.var "b")) (.lit 1))
    (.ite (.eq (.get "E" (rm "a" "b")) (.lit 1)) (.store "Lm" lmIdx (.lit 1)) .skip) .skip

/-- The left step from the right layer `rin` into `Lm`. -/
def lstepC (rin : String) : Com :=
  .seq resetLm (forUp "a" (.var "n")
    (.ite (.eq (.get "lab" (.var "a")) (.get "lab" (.var "u"))) (forUp "b" (.var "n") (lbody rin))
      .skip))

/-- One round of the scan over `a` of the right step. -/
def rbody (rout : String) : Com :=
  .ite (.eq (.get "lab" (.var "a")) (.get "lab" (.var "u")))
    (.ite (.eq (.get "Lm" lmIdx) (.lit 1))
      (.ite (.eq (.get "E" (rm "a" "b")) (.lit 1)) (.store rout (.var "b") (.lit 1)) .skip) .skip)
    .skip

/-- The right step from `Lm` into the right layer `rout`. -/
def rstepC (rout : String) : Com :=
  forUp "b" (.var "n") (.seq (.store rout (.var "b") (.lit 0)) (forUp "a" (.var "n") (rbody rout)))

theorem getElem?_set_rm {l : List ℕ} {n i j i' j' v : ℕ} (hj : j < n) (hj' : j' < n) :
    (l.set (i * n + j) v)[i' * n + j']? =
      if i' = i ∧ j' = j then (if i * n + j < l.length then some v else none)
      else l[i' * n + j']? := by
  rw [List.getElem?_set]
  by_cases h : i' = i ∧ j' = j
  · obtain ⟨rfl, rfl⟩ := h; simp
  · have : i * n + j ≠ i' * n + j' := fun he => h (by
      obtain ⟨h1, h2⟩ := rowMajor_inj hj hj' he; exact ⟨h1.symm, h2.symm⟩)
    simp [this, h]

theorem resetLm_run {B n : ℕ} {τ : Env} (hn : τ.vars "n" = n) (hlen : (τ.arrs "Lm").length = n * n)
    (hB : n * n + 1 < B) :
    ∃ τ', Run B resetLm τ τ' (13 * (n * n) + 9) ∧ Mat τ' "Lm" n (fun _ _ => 0) ∧
      τ'.vars "n" = n := by
  let I : ℕ → Env → Prop := fun k ρ => ρ.vars "n" = n ∧ (ρ.arrs "Lm").length = n * n ∧
    ∀ j < k, (ρ.arrs "Lm")[j]? = some 0
  have hnn : n ≤ n * n := by rcases Nat.eq_zero_or_pos n with h | h <;> [simp [h]; nlinarith]
  obtain ⟨ρ, hr, ⟨hn', hl', h0⟩, -⟩ :=
    forUp_run (B := B) (i := "j") (e := .mul (.var "n") (.var "n"))
      (body := .store "Lm" (.var "j") (.lit 0)) (N := n * n) (K := 3) I
      (by omega)
      (fun k _ ρ hI _ => by
        rw [evalB_bin (evalB_var (by rw [hI.1]; omega)) (evalB_var (by rw [hI.1]; omega))
          (by simp [hI.1]; omega)]
        simp [hI.1])
      (σ := τ) ⟨by simp [hn], by simp [hlen], fun j hj => absurd hj (Nat.not_lt_zero _)⟩
      (by
        rintro k hk ρ ⟨hnρ, hlρ, hρ⟩ hjk
        refine ⟨_, (Run.store (idx := k) (v := 0) (by simp [hjk]; omega) (by simp; omega)
          (by omega)).mono (by simp), by simp [hjk], by simp [hnρ], by simp [hlρ], ?_⟩
        intro j hj
        simp only [arrs_setVar, arrs_setArr, if_true, List.getElem?_set]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · simp [show k ≠ j by omega, hρ j hj]
        · simp [hlρ, hk])
  refine ⟨ρ, hr.mono (by simp; ring_nf; omega), ⟨hl', fun i hi j hj => h0 _ (rowMajor_lt hi hj)⟩, hn'⟩

/-- What the layer steps read: the size, the vertex `u`, the labels and
the edges. -/
structure ReachCtx (n : ℕ) (L : ℕ → ℕ) (E : ℕ → ℕ → Prop) (u : ℕ) (τ : Env) : Prop where
  hn : τ.vars "n" = n
  hu : τ.vars "u" = u
  hlab : LabAt n L τ
  hE : Mat τ "E" n fun a b => ind (E a b)

theorem ReachCtx.of_eq {n u : ℕ} {L : ℕ → ℕ} {E : ℕ → ℕ → Prop} {τ τ' : Env}
    (h : ReachCtx n L E u τ) (hn : τ'.vars "n" = τ.vars "n") (hu : τ'.vars "u" = τ.vars "u")
    (hl : τ'.arrs "lab" = τ.arrs "lab") (hE : τ'.arrs "E" = τ.arrs "E") : ReachCtx n L E u τ' :=
  ⟨by rw [hn, h.hn], by rw [hu, h.hu], by unfold LabAt; rw [hl]; exact h.hlab, h.hE.of_eq hE⟩

theorem evalB_lab {B n : ℕ} {L : ℕ → ℕ} {τ : Env} (hl : LabAt n L τ) (hL : ∀ z < n, L z < n)
    (hnB : n < B) {x : String} {i : ℕ} (hx : τ.vars x = i) (hi : i < n) :
    (Expr.get "lab" (.var x)).evalB B τ = some (L i) :=
  evalB_getVar hx (by omega) (hl i hi) (by have := hL i hi; omega)

theorem evalB_lmIdx {B n : ℕ} {L : ℕ → ℕ} {τ : Env} (hl : LabAt n L τ) (hL : ∀ z < n, L z < n)
    (hn : τ.vars "n" = n) (hB : n * n < B) {a b : ℕ} (ha : τ.vars "a" = a) (hb : τ.vars "b" = b)
    (han : a < n) (hbn : b < n) : lmIdx.evalB B τ = some (L b * n + a) := by
  have hLb := hL b hbn
  have h1 := rowMajor_lt hLb han
  have h2 : L b * n ≤ L b * n + a := Nat.le_add_right _ _
  have hnn : n ≤ n * n := Nat.le_mul_of_pos_left n (by omega)
  have := evalB_bin (op := .add) (evalB_bin (op := .mul) (evalB_lab hl hL (by omega) hb hbn)
    (evalB_var (B := B) (x := "n") (σ := τ) (by omega)) (by simp [hn]; omega))
    (evalB_var (x := "a") (by omega)) (by simp [hn, ha]; omega)
  simpa [lmIdx, hn, ha] using this

theorem evalB_eq_one_true {B : ℕ} {e : Expr} {τ : Env} {p : Prop}
    (h : e.evalB B τ = some (ind p)) (hB : 1 < B) (hp : p) :
    (Cond.eq e (.lit 1)).evalB B τ = some true := by
  rw [evalB_condEq' h (evalB_lit hB)]
  simp [ind_eq_one, hp]

theorem evalB_eq_one_false {B : ℕ} {e : Expr} {τ : Env} {p : Prop}
    (h : e.evalB B τ = some (ind p)) (hB : 1 < B) (hp : ¬ p) :
    (Cond.eq e (.lit 1)).evalB B τ = some false := by
  rw [evalB_condEq' h (evalB_lit hB)]
  simp [ind_eq_one, hp]

/-- **The left step.** -/
theorem lstepC_run {B n u : ℕ} {L : ℕ → ℕ} {E : ℕ → ℕ → Prop} {rin : ℕ → Prop} {τ : Env}
    {rinA : String} (hrA : rinA ≠ "Lm") (hc : ReachCtx n L E u τ) (hL : ∀ z < n, L z < n)
    (hun : u < n) (hrin : Vec τ rinA n fun b => ind (rin b))
    (hlm : (τ.arrs "Lm").length = n * n) (hB : n * n + n + 1 < B) :
    ∃ τ', Run B (lstepC rinA) τ τ' (60 * (n * n) + 30 * n + 20) ∧
      Mat τ' "Lm" n (fun y a => ind (LStep n L E u rin y a)) := by
  classical
  have hnB : n + 1 < B := by
    have : n ≤ n * n := Nat.le_mul_self n
    omega
  obtain ⟨τ0, hr0, hm0, hn0⟩ := resetLm_run (B := B) hc.hn hlm (by omega)
  have hc0 : ReachCtx n L E u τ0 :=
    hc.of_eq (hr0.frame_var "n" (by decide)) (hr0.frame_var "u" (by decide))
      (hr0.frame_arr "lab" (by decide)) (hr0.frame_arr "E" (by decide))
  have hrin0 : Vec τ0 rinA n fun b => ind (rin b) :=
    hrin.of_eq (hr0.frame_arr rinA (by simp [resetLm, forUp, Com.warrs]; exact hrA))
  -- the scan over a
  let IA : ℕ → Env → Prop := fun ka ρ => ReachCtx n L E u ρ ∧ Vec ρ rinA n (fun b => ind (rin b)) ∧
    Mat ρ "Lm" n (fun y a => ind (a < ka ∧ LStep n L E u rin y a))
  obtain ⟨ρ, hrA, ⟨-, -, hmρ⟩, -⟩ :=
    forUp_run (B := B) (i := "a") (e := .var "n")
      (body := .ite (.eq (.get "lab" (.var "a")) (.get "lab" (.var "u")))
        (forUp "b" (.var "n") (lbody rinA)) .skip) (N := n) (K := 40 * n + 20) IA (by omega)
      (fun k _ ρ hI _ => by rw [evalB_var (by rw [hI.1.hn]; omega), hI.1.hn])
      (σ := τ0) ⟨hc0.of_eq (by simp) (by simp) rfl rfl, hrin0.of_eq rfl,
        (hm0.congr (fun i _ j _ => by simp [ind])).of_eq (by simp)⟩
      (by
        rintro ka hka ρ ⟨hcρ, hrρ, hmρ⟩ hak
        have hla := evalB_lab (B := B) hcρ.hlab hL (by omega) hak hka
        have hlu := evalB_lab (B := B) hcρ.hlab hL (by omega) hcρ.hu hun
        have hfin : ∀ ρ' : Env, ρ'.vars "a" = ka → ReachCtx n L E u ρ' →
            Vec ρ' rinA n (fun b => ind (rin b)) →
            Mat ρ' "Lm" n (fun y a => ind (a < ka + 1 ∧ LStep n L E u rin y a)) →
            IA (ka + 1) (ρ'.setVar "a" (ka + 1)) := fun ρ' _ h1 h2 h3 =>
          ⟨h1.of_eq (by simp) (by simp) rfl rfl, h2.of_eq rfl, h3.of_eq rfl⟩
        by_cases hsame : L ka = L u
        swap
        · refine ⟨ρ, (Run.ite_false ?_ Run.skip).mono (by simp), hak, hfin ρ hak hcρ hrρ
            (hmρ.congr fun y _ a _ => ind_eq_iff.mpr ?_)⟩
          · rw [evalB_condEq' hla hlu]; simp [hsame]
          · constructor
            · rintro ⟨h1, h2⟩; exact ⟨by omega, h2⟩
            · rintro ⟨h1, h2⟩
              rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h1 | rfl
              · exact ⟨h1, h2⟩
              · exact absurd h2.1 hsame
        have hc1 : (Cond.eq (.get "lab" (.var "a")) (.get "lab" (.var "u"))).evalB B ρ =
            some true := by
          rw [evalB_condEq' hla hlu]; simp [hsame]
        let Q : ℕ → ℕ → ℕ → Prop := fun kb y a =>
          (a < ka ∧ LStep n L E u rin y a) ∨ (a = ka ∧ ∃ b < kb, L b = y ∧ rin b ∧ E ka b)
        let IB : ℕ → Env → Prop := fun kb ρ' => ReachCtx n L E u ρ' ∧ ρ'.vars "a" = ka ∧
          Vec ρ' rinA n (fun b => ind (rin b)) ∧ Mat ρ' "Lm" n (fun y a => ind (Q kb y a))
        obtain ⟨ρ', hrB, ⟨hc', ha', hr', hm'⟩, -⟩ :=
          forUp_run (B := B) (i := "b") (e := .var "n") (body := lbody rinA) (N := n) (K := 25) IB
            (by omega) (fun k _ ρ hI _ => by rw [evalB_var (by rw [hI.1.hn]; omega), hI.1.hn])
            (σ := ρ) ⟨hcρ.of_eq (by simp) (by simp) rfl rfl, by simp [hak], hrρ.of_eq rfl,
              (hmρ.congr fun y _ a _ => ind_eq_iff.mpr (by simp [Q])).of_eq (by simp)⟩
            (by
              rintro kb hkb ρ1 ⟨hc1', ha1, hr1, hm1⟩ hbk
              have hrb := hr1.evalB (B := B) hbk hkb (by omega) (by
                have := ind_le_one (rin kb); omega)
              have hEab := hc1'.hE.evalB (B := B) hc1'.hn ha1 hbk hka hkb (by omega) (by omega)
                (by have := ind_le_one (E ka kb); omega)
              have hfin2 : ∀ ρ2 : Env, ρ2.vars "b" = kb → ReachCtx n L E u ρ2 → ρ2.vars "a" = ka →
                  Vec ρ2 rinA n (fun b => ind (rin b)) →
                  Mat ρ2 "Lm" n (fun y a => ind (Q (kb + 1) y a)) →
                  IB (kb + 1) (ρ2.setVar "b" (kb + 1)) := fun ρ2 _ h1 h2 h3 h4 =>
                ⟨h1.of_eq (by simp) (by simp) rfl rfl, by simp [h2], h3.of_eq rfl, h4.of_eq rfl⟩
              have hQsame : ¬ (rin kb ∧ E ka kb) → ∀ y a, (Q (kb + 1) y a ↔ Q kb y a) := by
                intro hno y a
                simp only [Q]
                constructor
                · rintro (h | ⟨h1, b, hb, h2, h3, h4⟩)
                  · exact Or.inl h
                  · rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | rfl
                    · exact Or.inr ⟨h1, b, hb, h2, h3, h4⟩
                    · exact absurd ⟨h3, h4⟩ hno
                · rintro (h | ⟨h1, b, hb, h2, h3, h4⟩)
                  · exact Or.inl h
                  · exact Or.inr ⟨h1, b, by omega, h2, h3, h4⟩
              by_cases hR : rin kb
              swap
              · refine ⟨ρ1, (Run.ite_false ?_ Run.skip).mono (by simp), hbk,
                  hfin2 ρ1 hbk hc1' ha1 hr1 (hm1.congr fun y _ a _ => ind_eq_iff.mpr
                    (hQsame (fun h => hR h.1) y a).symm)⟩
                exact evalB_eq_one_false hrb (by omega) hR
              by_cases hEk : E ka kb
              swap
              · refine ⟨ρ1, (Run.ite_true ?_ (Run.ite_false ?_ Run.skip)).mono (by simp), hbk,
                  hfin2 ρ1 hbk hc1' ha1 hr1 (hm1.congr fun y _ a _ => ind_eq_iff.mpr
                    (hQsame (fun h => hEk h.2) y a).symm)⟩
                · exact evalB_eq_one_true hrb (by omega) hR
                · exact evalB_eq_one_false hEab (by omega) hEk
              have hidx := evalB_lmIdx (B := B) hc1'.hlab hL hc1'.hn (by omega) ha1 hbk hka hkb
              have hLkb := hL kb hkb
              have hlt := rowMajor_lt hLkb hka
              refine ⟨ρ1.setArr "Lm" (L kb * n + ka) 1, (Run.ite_true ?_ (Run.ite_true ?_
                (Run.store hidx (evalB_lit (by omega)) (by rw [hm1.len]; exact hlt)))).mono
                (by simp [lmIdx]), by simp [hbk], hfin2 _ (by simp [hbk])
                (hc1'.of_eq (by simp) (by simp) (by simp) (by simp)) (by simp [ha1])
                (hr1.of_eq (by simp [hrA])) ⟨by simp [hm1.len], fun y hy a ha => ?_⟩⟩
              · exact evalB_eq_one_true hrb (by omega) hR
              · exact evalB_eq_one_true hEab (by omega) hEk
              · simp only [arrs_setArr, if_true]
                rw [getElem?_set_rm hka ha]
                by_cases hya : y = L kb ∧ a = ka
                · obtain ⟨rfl, rfl⟩ := hya
                  rw [if_pos ⟨rfl, rfl⟩, if_pos (by rw [hm1.len]; exact hlt)]
                  congr 1
                  symm
                  exact ind_eq_one.mpr (Or.inr ⟨rfl, kb, by omega, rfl, hR, hEk⟩)
                · rw [if_neg hya, hm1.get y hy a ha]
                  congr 1
                  refine ind_eq_iff.mpr ?_
                  simp only [Q]
                  constructor
                  · rintro (h | ⟨h1, b, hb, h2, h3, h4⟩)
                    · exact Or.inl h
                    · exact Or.inr ⟨h1, b, by omega, h2, h3, h4⟩
                  · rintro (h | ⟨h1, b, hb, h2, h3, h4⟩)
                    · exact Or.inl h
                    · rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | rfl
                      · exact Or.inr ⟨h1, b, hb, h2, h3, h4⟩
                      · exact absurd ⟨h2.symm, h1⟩ hya)
        refine ⟨ρ', (Run.ite_true hc1 hrB).mono (by simp; ring_nf; omega), ha', hfin ρ' ha' hc' hr'
          (hm'.congr fun y _ a _ => ind_eq_iff.mpr ?_)⟩
        simp only [Q, LStep]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨rfl, h2⟩)
          · exact ⟨by omega, h2⟩
          · exact ⟨by omega, hsame, h2⟩
        · rintro ⟨h1, h2⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp h1 with h1 | rfl
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr ⟨rfl, h2.2⟩)
  refine ⟨ρ, (Run.seq hr0 hrA).mono (by simp; ring_nf; omega),
    hmρ.congr fun y _ a ha => ind_eq_iff.mpr ⟨fun h => h.2, fun h => ⟨ha, h⟩⟩⟩

/-- **The right step.** -/
theorem rstepC_run {B n u : ℕ} {L : ℕ → ℕ} {E : ℕ → ℕ → Prop} {lin : ℕ → ℕ → Prop} {τ : Env}
    {routA : String} (hro : routA ≠ "Lm") (hroE : routA ≠ "E") (hrol : routA ≠ "lab")
    (hc : ReachCtx n L E u τ) (hL : ∀ z < n, L z < n)
    (hun : u < n) (hlin : Mat τ "Lm" n fun y a => ind (lin y a))
    (hlen : (τ.arrs routA).length = n) (hB : n * n + n + 1 < B) :
    ∃ τ', Run B (rstepC routA) τ τ' (40 * (n * n) + 20 * n + 10) ∧
      Vec τ' routA n (fun b => ind (RStep n L E u lin b)) := by
  classical
  have hnB : n + 1 < B := by
    have : n ≤ n * n := Nat.le_mul_self n
    omega
  let OB : ℕ → Env → Prop := fun kb ρ => ReachCtx n L E u ρ ∧
    Mat ρ "Lm" n (fun y a => ind (lin y a)) ∧ (ρ.arrs routA).length = n ∧
    ∀ b < kb, (ρ.arrs routA)[b]? = some (ind (RStep n L E u lin b))
  obtain ⟨ρ, hrO, ⟨-, -, hlρ, hgρ⟩, -⟩ :=
    forUp_run (B := B) (i := "b") (e := .var "n")
      (body := .seq (.store routA (.var "b") (.lit 0)) (forUp "a" (.var "n") (rbody routA)))
      (N := n) (K := 38 * n + 9) OB (by omega)
      (fun k _ ρ hI _ => by rw [evalB_var (by rw [hI.1.hn]; omega), hI.1.hn])
      (σ := τ) ⟨hc.of_eq (by simp) (by simp) rfl rfl, hlin.of_eq (by simp), by simp [hlen],
        fun b hb => absurd hb (Nat.not_lt_zero _)⟩
      (by
        rintro kb hkb ρ ⟨hcρ, hmρ, hlρ, hgρ⟩ hbk
        set ρ0 := ρ.setArr routA kb 0 with hρ0
        have hr0 : Run B (.store routA (.var "b") (.lit 0)) ρ ρ0 3 :=
          (Run.store (idx := kb) (v := 0) (by simp [hbk]; omega) (by simp; omega)
            (by omega)).mono (by simp)
        let P : ℕ → Prop := fun ka => ∃ a < ka, L a = L u ∧ lin (L kb) a ∧ E a kb
        let IA : ℕ → Env → Prop := fun ka ρ' => ReachCtx n L E u ρ' ∧ ρ'.vars "b" = kb ∧
          Mat ρ' "Lm" n (fun y a => ind (lin y a)) ∧ (ρ'.arrs routA).length = n ∧
          (ρ'.arrs routA)[kb]? = some (ind (P ka)) ∧
          ∀ b < kb, (ρ'.arrs routA)[b]? = some (ind (RStep n L E u lin b))
        obtain ⟨ρ', hrA, ⟨hc', hb', hm', hl', hk', hg'⟩, -⟩ :=
          forUp_run (B := B) (i := "a") (e := .var "n") (body := rbody routA) (N := n) (K := 30)
            IA (by omega) (fun k _ ρ hI _ => by rw [evalB_var (by rw [hI.1.hn]; omega), hI.1.hn])
            (σ := ρ0) ⟨hcρ.of_eq (by simp [hρ0]) (by simp [hρ0]) (by simp [hρ0, Ne.symm hrol])
                (by simp [hρ0, Ne.symm hroE]),
              by simp [hρ0, hbk], hmρ.of_eq (by simp [hρ0, Ne.symm hro]), by simp [hρ0, hlρ],
              by simp [hρ0, hlρ, hkb, P, ind],
              fun b hb => by
                simp only [arrs_setVar, hρ0, arrs_setArr, if_true]
                rw [List.getElem?_set_ne (by omega)]; exact hgρ b hb⟩
            (by
              rintro ka hka ρ1 ⟨hc1, hb1, hm1, hl1, hk1, hg1⟩ hak
              have hla := evalB_lab (B := B) hc1.hlab hL (by omega) hak hka
              have hlu := evalB_lab (B := B) hc1.hlab hL (by omega) hc1.hu hun
              have hLkb := hL kb hkb
              have hidx := evalB_lmIdx (B := B) hc1.hlab hL hc1.hn (by omega) hak hb1 hka hkb
              have hlm : (Expr.get "Lm" lmIdx).evalB B ρ1 = some (ind (lin (L kb) ka)) :=
                evalB_get hidx (hm1.get _ hLkb _ hka) (by have := ind_le_one (lin (L kb) ka); omega)
              have hEab := hc1.hE.evalB (B := B) hc1.hn hak hb1 hka hkb (by omega) (by omega)
                (by have := ind_le_one (E ka kb); omega)
              have hsucc : P (ka + 1) ↔ (P ka ∨ (L ka = L u ∧ lin (L kb) ka ∧ E ka kb)) := by
                constructor
                · rintro ⟨a, ha, h⟩
                  rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha | rfl
                  · exact Or.inl ⟨a, ha, h⟩
                  · exact Or.inr h
                · rintro (⟨a, ha, h⟩ | h)
                  · exact ⟨a, by omega, h⟩
                  · exact ⟨ka, by omega, h⟩
              have hfin : ∀ ρ2 : Env, ρ2.vars "a" = ka → ReachCtx n L E u ρ2 → ρ2.vars "b" = kb →
                  Mat ρ2 "Lm" n (fun y a => ind (lin y a)) → (ρ2.arrs routA).length = n →
                  (ρ2.arrs routA)[kb]? = some (ind (P (ka + 1))) →
                  (∀ b < kb, (ρ2.arrs routA)[b]? = some (ind (RStep n L E u lin b))) →
                  IA (ka + 1) (ρ2.setVar "a" (ka + 1)) := fun ρ2 _ h1 h2 h3 h4 h5 h6 =>
                ⟨h1.of_eq (by simp) (by simp) rfl rfl, by simp [h2], h3.of_eq rfl, by simp [h4],
                  by simpa using h5, by simpa using h6⟩
              have hkeep : ¬ (L ka = L u ∧ lin (L kb) ka ∧ E ka kb) →
                  (ρ1.arrs routA)[kb]? = some (ind (P (ka + 1))) := fun h => by
                rw [hk1]; congr 1
                exact ind_eq_iff.mpr (by
                  rw [hsucc]; exact ⟨Or.inl, fun h' => h'.elim id (fun h'' => absurd h'' h)⟩)
              by_cases hs : L ka = L u
              swap
              · refine ⟨ρ1, (Run.ite_false ?_ Run.skip).mono (by simp), hak,
                  hfin ρ1 hak hc1 hb1 hm1 hl1 (hkeep fun h => hs h.1) hg1⟩
                rw [evalB_condEq' hla hlu]; simp [hs]
              have hc1' : (Cond.eq (.get "lab" (.var "a")) (.get "lab" (.var "u"))).evalB B ρ1 =
                  some true := by rw [evalB_condEq' hla hlu]; simp [hs]
              by_cases hli : lin (L kb) ka
              swap
              · exact ⟨ρ1, (Run.ite_true hc1' (Run.ite_false (evalB_eq_one_false hlm (by omega) hli)
                  Run.skip)).mono (by simp [lmIdx]), hak,
                  hfin ρ1 hak hc1 hb1 hm1 hl1 (hkeep fun h => hli h.2.1) hg1⟩
              by_cases hE : E ka kb
              swap
              · exact ⟨ρ1, (Run.ite_true hc1' (Run.ite_true (evalB_eq_one_true hlm (by omega) hli)
                  (Run.ite_false (evalB_eq_one_false hEab (by omega) hE) Run.skip))).mono
                  (by simp [lmIdx]), hak,
                  hfin ρ1 hak hc1 hb1 hm1 hl1 (hkeep fun h => hE h.2.2) hg1⟩
              refine ⟨ρ1.setArr routA kb 1, (Run.ite_true hc1' (Run.ite_true
                (evalB_eq_one_true hlm (by omega) hli)
                (Run.ite_true (evalB_eq_one_true hEab (by omega) hE)
                  (Run.store (idx := kb) (v := 1) (by simp [hb1]; omega) (by simp; omega)
                    (by omega))))).mono (by simp [lmIdx]), by simp [hak],
                hfin _ (by simp [hak]) (hc1.of_eq (by simp) (by simp) (by simp [Ne.symm hrol])
                  (by simp [Ne.symm hroE]))
                  (by simp [hb1]) (hm1.of_eq (by simp [Ne.symm hro])) (by simp [hl1]) ?_ ?_⟩
              · simp only [arrs_setArr, if_true]
                rw [List.getElem?_set_self (by omega)]
                congr 1
                exact (ind_eq_one.mpr (hsucc.mpr (Or.inr ⟨hs, hli, hE⟩))).symm
              · intro b hb
                simp only [arrs_setArr, if_true]
                rw [List.getElem?_set_ne (by omega)]
                exact hg1 b hb)
        refine ⟨ρ', (Run.seq hr0 hrA).mono (by simp; ring_nf; omega), hb', hc'.of_eq (by simp)
          (by simp) rfl rfl, hm'.of_eq (by simp), by simp [hl'], fun b hb => ?_⟩
        simp only [arrs_setVar]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | rfl
        · exact hg' b hb
        · rw [hk']; rfl)
  exact ⟨ρ, hrO.mono (by simp; ring_nf; omega), ⟨hlρ, hgρ⟩⟩

/-- The right layer reached by walks of length five from `u`. -/
def Reach5 (n : ℕ) (L : ℕ → ℕ) (E : ℕ → ℕ → Prop) (u b : ℕ) : Prop :=
  RStep n L E u (LStep n L E u (RStep n L E u (LStep n L E u (fun b => E u b)))) b

/-- The first right layer: the `E`-neighbors of `u`. -/
def fillR1 : Com := rowFill "R1" (.var "b") (.get "E" (rm "u" "b"))

/-- Copy the fifth right layer into row `u` of `D`. -/
def copyD (D : String) : Com := rowFill D (rm "u" "b") (.get "R5" (.var "b"))

/-- The five layers from `u`, stored into row `u` of `D`. -/
def bfsU (D : String) : Com :=
  .seq fillR1 (.seq (lstepC "R1") (.seq (rstepC "R3") (.seq (lstepC "R3")
    (.seq (rstepC "R5") (copyD D)))))

/-- The layers from every vertex. -/
def bfs (D : String) : Com := forUp "u" (.var "n") (bfsU D)

/-- What `bfs` needs: the size, the labels, the edges, and the work
arrays of the right sizes. -/
structure BfsCtx (n : ℕ) (L : ℕ → ℕ) (E : ℕ → ℕ → Prop) (D : String) (τ : Env) : Prop where
  hn : τ.vars "n" = n
  hlab : LabAt n L τ
  hE : Mat τ "E" n fun a b => ind (E a b)
  hR1 : (τ.arrs "R1").length = n
  hR3 : (τ.arrs "R3").length = n
  hR5 : (τ.arrs "R5").length = n
  hLm : (τ.arrs "Lm").length = n * n
  hD : (τ.arrs D).length = n * n

/-- The arrays `bfsU D` writes. -/
theorem warrs_bfsU (D : String) (b : String) (hb : b ∉ ["R1", "Lm", "R3", "R5", D]) :
    b ∉ (bfsU D).warrs := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hb
  simp [bfsU, fillR1, copyD, rowFill, lstepC, rstepC, resetLm, lbody, rbody, forUp, Com.warrs, hb.1,
    hb.2.1, hb.2.2.1, hb.2.2.2.1, hb.2.2.2.2]

theorem ReachCtx.of_run {n u : ℕ} {L : ℕ → ℕ} {E : ℕ → ℕ → Prop} {B K : ℕ} {c : Com}
    {τ τ' : Env} (h : ReachCtx n L E u τ) (hr : Run B c τ τ' K) (hn : "n" ∉ c.wvars)
    (hu : "u" ∉ c.wvars) (hl : "lab" ∉ c.warrs) (hE : "E" ∉ c.warrs) : ReachCtx n L E u τ' :=
  h.of_eq (hr.frame_var "n" hn) (hr.frame_var "u" hu) (hr.frame_arr "lab" hl) (hr.frame_arr "E" hE)

/-- **The layers from one vertex.** -/
theorem bfsU_run {B n k : ℕ} {L : ℕ → ℕ} {E : ℕ → ℕ → Prop} {D : String} {τ : Env}
    (hD : D ∉ ["R1", "Lm", "R3", "R5", "E", "lab"]) (hc : BfsCtx n L E D τ)
    (hu : τ.vars "u" = k) (hk : k < n) (hL : ∀ z < n, L z < n) (hB : n * n + n + 1 < B) :
    ∃ τ', Run B (bfsU D) τ τ' (200 * (n * n) + 150 * n + 100) ∧ BfsCtx n L E D τ' ∧
      τ'.vars "u" = k ∧
      ∀ j, (τ'.arrs D)[j]? = if k * n ≤ j ∧ j < k * n + n
        then some (ind (Reach5 n L E k (j - k * n))) else (τ.arrs D)[j]? := by
  classical
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hD
  obtain ⟨hD1, hD2, hD3, hD5, hDE, hDl⟩ := hD
  have hnn : n ≤ n * n := Nat.le_mul_self n
  have hrc : ReachCtx n L E k τ := ⟨hc.hn, hu, hc.hlab, hc.hE⟩
  -- the first layer
  obtain ⟨τ1, hr1, hc1, hl1, hg1⟩ := rowFill_run (B := B) (base := 0) (K := 8) (arr := "R1")
    (ie := .var "b") (e := .get "E" (rm "u" "b")) (ReachCtx n L E k) (fun b => ind (E k b))
    (by omega) (fun τ h => h.hn) (fun τ x h => h.of_eq (by simp) (by simp) rfl rfl)
    (fun τ i x h => h.of_eq (by simp) (by simp) (by simp) (by simp))
    (fun τ k' _ hb _ => by rw [evalB_var (by omega), hb]; simp)
    (fun τ k' h hb hk' => h.hE.evalB h.hn h.hu hb hk hk' (by omega) (by omega)
      (by have := ind_le_one (E k k'); omega))
    (by simp) hrc (by rw [hc.hR1]; omega)
  have hv1 : Vec τ1 "R1" n fun b => ind (E k b) :=
    ⟨by rw [hl1, hc.hR1], fun i hi => by rw [hg1 i, if_pos ⟨by omega, by omega⟩]; simp⟩
  -- the second layer
  obtain ⟨τ2, hr2, hm2⟩ := lstepC_run (B := B) (rinA := "R1") (by decide) hc1 hL hk hv1
    (by rw [run_length_arrs hr1, hc.hLm]) hB
  have hc2 := hc1.of_run hr2 (by decide) (by decide) (by decide) (by decide)
  -- the third layer
  obtain ⟨τ3, hr3, hv3⟩ := rstepC_run (B := B) (routA := "R3") (by decide) (by decide) (by decide)
    hc2 hL hk hm2 (by rw [run_length_arrs hr2, run_length_arrs hr1, hc.hR3]) hB
  have hc3 := hc2.of_run hr3 (by decide) (by decide) (by decide) (by decide)
  -- the fourth layer
  obtain ⟨τ4, hr4, hm4⟩ := lstepC_run (B := B) (rinA := "R3") (by decide) hc3 hL hk hv3
    (by rw [run_length_arrs hr3, hm2.len]) hB
  have hc4 := hc3.of_run hr4 (by decide) (by decide) (by decide) (by decide)
  -- the fifth layer
  obtain ⟨τ5, hr5, hv5⟩ := rstepC_run (B := B) (routA := "R5") (by decide) (by decide) (by decide)
    hc4 hL hk hm4 (by rw [run_length_arrs hr4, run_length_arrs hr3, run_length_arrs hr2, run_length_arrs hr1,
      hc.hR5]) hB
  have hc5 := hc4.of_run hr5 (by decide) (by decide) (by decide) (by decide)
  -- the copy
  have hlD : (τ5.arrs D).length = n * n := by
    rw [run_length_arrs hr5, run_length_arrs hr4, run_length_arrs hr3, run_length_arrs hr2, run_length_arrs hr1, hc.hD]
  obtain ⟨τ6, hr6, ⟨hc6, hv6⟩, hl6, hg6⟩ := rowFill_run (B := B) (base := k * n) (K := 8)
    (arr := D) (ie := rm "u" "b") (e := .get "R5" (.var "b"))
    (fun ρ => ReachCtx n L E k ρ ∧ Vec ρ "R5" n fun b => ind (Reach5 n L E k b))
    (fun b => ind (Reach5 n L E k b)) (by omega) (fun τ h => h.1.hn)
    (fun τ x h => ⟨h.1.of_eq (by simp) (by simp) rfl rfl, h.2.of_eq rfl⟩)
    (fun τ i x h => ⟨h.1.of_eq (by simp) (by simp) (by simp [Ne.symm hDl]) (by simp [Ne.symm hDE]),
      h.2.of_eq (by simp [Ne.symm hD5])⟩)
    (fun τ k' h hb hk' => evalB_rm h.1.hu h.1.hn hb hk' (by omega) (by
      have := rowMajor_lt hk hk'; omega))
    (fun τ k' h hb hk' => h.2.evalB hb hk' (by omega)
      (by have := ind_le_one (Reach5 n L E k k'); omega))
    (by simp) ⟨hc5, hv5⟩ (by
      have := Nat.mul_le_mul_right n (show k + 1 ≤ n by omega)
      rw [Nat.add_mul] at this; rw [hlD]; omega)
  refine ⟨τ6, (Run.seq hr1 (Run.seq hr2 (Run.seq hr3 (Run.seq hr4 (Run.seq hr5 hr6))))).mono ?_,
    ⟨hc6.hn, hc6.hlab, hc6.hE, ?_, ?_, ?_, ?_, by rw [hl6, hlD]⟩, hc6.hu, fun j => ?_⟩
  · nlinarith
  · rw [run_length_arrs hr6, run_length_arrs hr5, run_length_arrs hr4, run_length_arrs hr3, run_length_arrs hr2,
      run_length_arrs hr1, hc.hR1]
  · rw [run_length_arrs hr6, run_length_arrs hr5, run_length_arrs hr4, run_length_arrs hr3, run_length_arrs hr2,
      run_length_arrs hr1, hc.hR3]
  · rw [run_length_arrs hr6, run_length_arrs hr5, run_length_arrs hr4, run_length_arrs hr3, run_length_arrs hr2,
      run_length_arrs hr1, hc.hR5]
  · rw [run_length_arrs hr6, run_length_arrs hr5, run_length_arrs hr4, run_length_arrs hr3, run_length_arrs hr2,
      run_length_arrs hr1, hc.hLm]
  · rw [hg6 j]
    split
    · rfl
    · have h5 : τ5.arrs D = τ.arrs D := by
        rw [hr5.frame_arr D (by simp [rstepC, rbody, forUp, Com.warrs]; exact hD5),
          hr4.frame_arr D (by simp [lstepC, resetLm, lbody, forUp, Com.warrs]; exact hD2),
          hr3.frame_arr D (by simp [rstepC, rbody, forUp, Com.warrs]; exact hD3),
          hr2.frame_arr D (by simp [lstepC, resetLm, lbody, forUp, Com.warrs]; exact hD2),
          hr1.frame_arr D (by simp [rowFill, forUp, Com.warrs]; exact hD1)]
      rw [h5]

theorem BfsCtx.setVar {n : ℕ} {L : ℕ → ℕ} {E : ℕ → ℕ → Prop} {D : String} {τ : Env}
    (h : BfsCtx n L E D τ) (x : String) (hx : x ≠ "n") (v : ℕ) : BfsCtx n L E D (τ.setVar x v) :=
  ⟨by simp [Ne.symm hx, h.hn], by simpa [LabAt] using h.hlab, h.hE.of_eq (by simp),
    by simp [h.hR1], by simp [h.hR3], by simp [h.hR5], by simp [h.hLm], by simp [h.hD]⟩

/-- **The layers from every vertex.** Entry `(u, b)` of `D` says that
`b` is reached from `u` by an alternating walk of length five. -/
theorem bfs_run {B n : ℕ} {L : ℕ → ℕ} {E : ℕ → ℕ → Prop} {D : String} {τ : Env}
    (hD : D ∉ ["R1", "Lm", "R3", "R5", "E", "lab"]) (hc : BfsCtx n L E D τ)
    (hL : ∀ z < n, L z < n) (hB : n * n + n + 1 < B) :
    ∃ τ', Run B (bfs D) τ τ' (n * (200 * (n * n) + 150 * n + 110) + 6) ∧ BfsCtx n L E D τ' ∧
      Mat τ' D n (fun u b => ind (Reach5 n L E u b)) := by
  have hnn : n ≤ n * n := Nat.le_mul_self n
  let I : ℕ → Env → Prop := fun k ρ => BfsCtx n L E D ρ ∧
    ∀ u < k, ∀ b < n, (ρ.arrs D)[u * n + b]? = some (ind (Reach5 n L E u b))
  obtain ⟨ρ, hr, ⟨hcρ, hgρ⟩, -⟩ :=
    forUp_run (B := B) (i := "u") (e := .var "n") (body := bfsU D) (N := n)
      (K := 200 * (n * n) + 150 * n + 100) I (by omega)
      (fun k _ ρ hI _ => by rw [evalB_var (by rw [hI.1.hn]; omega), hI.1.hn])
      (σ := τ) ⟨hc.setVar "u" (by decide) 0, fun u hu => absurd hu (Nat.not_lt_zero _)⟩
      (by
        rintro k hk ρ ⟨hcρ, hgρ⟩ huk
        obtain ⟨ρ', hr', hc', hu', hg'⟩ := bfsU_run hD hcρ huk hk hL hB
        refine ⟨ρ', hr', hu', hc'.setVar "u" (by decide) _, fun u hu b hb => ?_⟩
        simp only [arrs_setVar]
        rw [hg' (u * n + b)]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
        · have : u * n + b < k * n := by
            have := Nat.mul_le_mul_right n (show u + 1 ≤ k by omega)
            rw [Nat.add_mul] at this; omega
          rw [if_neg (by omega)]
          exact hgρ u hu b hb
        · rw [if_pos ⟨by omega, by omega⟩]
          simp)
  exact ⟨ρ, hr.mono (by simp; exact Nat.mul_le_mul_left _ (by omega)), hcρ, ⟨hcρ.hD, hgρ⟩⟩

end Lax185574Proofs.Conversions.Ram
