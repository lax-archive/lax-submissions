import Lax185574Proofs.Conversions.Ram.Classify

/-!
Refining a labelling by a key.

The array `lab` holds a labelling `L` of the vertices `u < n` and the
array `key` holds a key `κ u < M`. The command `refine` replaces `lab`
by the labelling that maps `u` to the least `v < n` with `L v = L u` and
`κ v = κ u`. It uses the scratch array `lab2` and the table `tab` of
length at least `n · M`, which must be zero before and is zero again
afterwards. It runs in time linear in `n`: every `u` looks up the pair
`(L u, κ u)` in `tab`, which records the first vertex with that pair.
-/

namespace Lax185574Proofs.Chain.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram

/-! ### Least elements -/

theorem leastBelow_lt_of {p : ℕ → Prop} {k d : ℕ} (hd : k ≤ d) :
    leastBelow p k d ≤ d := by
  by_cases h : ∃ u, u < k ∧ p u
  · have := (leastBelow_spec (d := d) h).1; omega
  · rw [leastBelow_none h]

theorem leastBelow_mono_eq {p : ℕ → Prop} {k m d : ℕ} (hkm : k ≤ m) (h : ∃ u, u < k ∧ p u) :
    leastBelow p m d = leastBelow p k d := by
  obtain ⟨h1, h2, h3⟩ := leastBelow_spec (d := d) h
  have h' : ∃ u, u < m ∧ p u := ⟨_, by omega, h2⟩
  obtain ⟨g1, g2, g3⟩ := leastBelow_spec (d := d) h'
  rcases lt_trichotomy (leastBelow p m d) (leastBelow p k d) with hlt | heq | hgt
  · exact absurd g2 (h3 _ hlt)
  · exact heq
  · exact absurd h2 (g3 _ hgt)

/-- `leastBelow` of a property that holds at `u < n` is at most `u`. -/
theorem leastBelow_le_of {p : ℕ → Prop} {n d u : ℕ} (hu : u < n) (hp : p u) :
    leastBelow p n d ≤ u := by
  obtain ⟨-, -, h3⟩ := leastBelow_spec (d := d) ⟨u, hu, hp⟩
  by_contra hc; exact h3 u (by omega) hp

theorem leastBelow_congr {p q : ℕ → Prop} {k d : ℕ} (h : ∀ u < k, (p u ↔ q u)) :
    leastBelow p k d = leastBelow q k d := by
  classical
  by_cases hp : ∃ u, u < k ∧ p u
  · have hq : ∃ u, u < k ∧ q u := by
      obtain ⟨u, hu, h'⟩ := hp; exact ⟨u, hu, (h u hu).1 h'⟩
    obtain ⟨a1, a2, a3⟩ := leastBelow_spec (d := d) hp
    obtain ⟨b1, b2, b3⟩ := leastBelow_spec (d := d) hq
    rcases lt_trichotomy (leastBelow p k d) (leastBelow q k d) with hlt | heq | hgt
    · exact absurd ((h _ a1).1 a2) (b3 _ hlt)
    · exact heq
    · exact absurd ((h _ b1).2 b2) (a3 _ hgt)
  · have hq : ¬ ∃ u, u < k ∧ q u := by
      rintro ⟨u, hu, h'⟩; exact hp ⟨u, hu, (h u hu).2 h'⟩
    rw [leastBelow_none hp, leastBelow_none hq]

/-! ### The command -/

/-- The table position `L u · M + κ u` of the scalar `ru`. -/
def codeE : Expr := .add (.mul (.get "lab" (.var "ru")) (.var "M")) (.get "key" (.var "ru"))

/-- First pass: record the first vertex of every pair, label by it. -/
def refPass1 : Com :=
  forUp "ru" (.var "n") (.seq (.assign "rt" codeE)
    (.seq (.ite (.eq (.get "tab" (.var "rt")) (.lit 0))
        (.store "tab" (.var "rt") (.add (.var "ru") (.lit 1))) .skip)
      (.store "lab2" (.var "ru") (.sub (.get "tab" (.var "rt")) (.lit 1)))))

/-- Second pass: clear the table. -/
def refPass2 : Com := forUp "ru" (.var "n") (.store "tab" codeE (.lit 0))

/-- Third pass: copy the new labels. -/
def refPass3 : Com := forUp "ru" (.var "n") (.store "lab" (.var "ru") (.get "lab2" (.var "ru")))

/-- Refine the labelling `lab` by the key `key`. -/
def refine : Com := .seq refPass1 (.seq refPass2 refPass3)

/-- The array `arr` is zero everywhere. -/
def Zero (τ : Env) (arr : String) : Prop := ∀ t < (τ.arrs arr).length, (τ.arrs arr)[t]? = some 0

/-- The context of `refine`: the scalars `n` and `M`, the arrays `lab`
and `key`, and the lengths. -/
structure RefCtx (n M : ℕ) (L κ : ℕ → ℕ) (τ : Env) : Prop where
  hn : τ.vars "n" = n
  hM : τ.vars "M" = M
  hlab : Vec τ "lab" n L
  hkey : Vec τ "key" n κ
  hlab2 : (τ.arrs "lab2").length = n
  htab : n * M ≤ (τ.arrs "tab").length

theorem RefCtx.setVar {n M : ℕ} {L κ : ℕ → ℕ} {τ : Env} (h : RefCtx n M L κ τ) (x : String)
    (v : ℕ) (hx : x ≠ "n") (hM : x ≠ "M") : RefCtx n M L κ (τ.setVar x v) :=
  ⟨by simp [Ne.symm hx, h.hn], by simp [Ne.symm hM, h.hM], h.hlab.of_eq rfl, h.hkey.of_eq rfl,
    by simp [h.hlab2], by simpa using h.htab⟩

theorem RefCtx.setArr {n M : ℕ} {L κ : ℕ → ℕ} {τ : Env} (h : RefCtx n M L κ τ) (a : String)
    (i v : ℕ) (hl : a ≠ "lab") (hk : a ≠ "key") : RefCtx n M L κ (τ.setArr a i v) :=
  ⟨by simp [h.hn], by simp [h.hM], h.hlab.of_eq (by simp [Ne.symm hl]),
    h.hkey.of_eq (by simp [Ne.symm hk]), by rw [length_arrs_setArr]; exact h.hlab2,
    by rw [length_arrs_setArr]; exact h.htab⟩

theorem code_lt {n M u : ℕ} {L κ : ℕ → ℕ} (hL : ∀ u < n, L u < n) (hκ : ∀ u < n, κ u < M)
    (hu : u < n) : L u * M + κ u < n * M := by
  have h1 := hL u hu
  have h2 := hκ u hu
  have : (L u + 1) * M ≤ n * M := Nat.mul_le_mul_right _ h1
  rw [Nat.add_mul, one_mul] at this
  omega

theorem code_inj {M a b c d : ℕ} (hb : b < M) (hd : d < M) (h : a * M + b = c * M + d) :
    a = c ∧ b = d := by
  have := rowMajor_inj hb hd h; exact this

theorem evalB_codeE {B n M : ℕ} {L κ : ℕ → ℕ} {τ : Env} (h : RefCtx n M L κ τ)
    (hL : ∀ u < n, L u < n) (hκ : ∀ u < n, κ u < M) {u : ℕ} (hu : τ.vars "ru" = u)
    (hun : u < n) (hB : n * M < B) (hnB : n < B) (hMB : M < B) :
    codeE.evalB B τ = some (L u * M + κ u) := by
  have hc := code_lt hL hκ hun
  have hLu := hL u hun
  have hLM : L u * M ≤ L u * M + κ u := Nat.le_add_right _ _
  have e1 := h.hlab.evalB (B := B) hu hun hnB (by omega)
  have e2 := h.hkey.evalB (B := B) hu hun hnB (by have := hκ u hun; omega)
  have e3 := evalB_bin (op := .mul) e1 (evalB_var (x := "M") (σ := τ) (B := B) (by rw [h.hM]; omega))
    (by simp [h.hM]; omega)
  have e4 := evalB_bin (op := .add) e3 e2 (by simp [h.hM]; omega)
  simpa [codeE, h.hM] using e4

/-- The table after the first `k` rounds of the first pass. -/
noncomputable def tabAfter (n : ℕ) (code : ℕ → ℕ) (k t : ℕ) : ℕ :=
  open Classical in if ∃ v, v < k ∧ code v = t then leastBelow (fun v => code v = t) k n + 1 else 0

theorem tabAfter_succ {n : ℕ} {code : ℕ → ℕ} {k : ℕ} (hk : k < n) (t : ℕ) :
    tabAfter n code (k + 1) t =
      if t = code k ∧ tabAfter n code k t = 0 then k + 1 else tabAfter n code k t := by
  classical
  unfold tabAfter
  have hs := leastBelow_succ (fun v => code v = t) (d := n) (k := k) hk
  by_cases hex : ∃ v, v < k ∧ code v = t
  · have hex' : ∃ v, v < k + 1 ∧ code v = t := by
      obtain ⟨v, hv, h⟩ := hex; exact ⟨v, by omega, h⟩
    obtain ⟨h1, -, -⟩ := leastBelow_spec (d := n) hex
    rw [if_pos hex', if_pos hex, if_neg (by omega), hs, if_neg (by omega)]
  · rw [if_neg hex]
    by_cases ht : t = code k
    · have hex' : ∃ v, v < k + 1 ∧ code v = t := ⟨k, by omega, ht.symm⟩
      rw [if_pos hex', if_pos ⟨ht, rfl⟩, hs, leastBelow_none hex, if_pos ⟨ht.symm, hk⟩]
    · have hex' : ¬ ∃ v, v < k + 1 ∧ code v = t := by
        rintro ⟨v, hv, h⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hv with hv | rfl
        · exact hex ⟨v, hv, h⟩
        · exact ht h.symm
      rw [if_neg hex', if_neg (fun h => ht h.1)]

theorem tabAfter_code {n : ℕ} {code : ℕ → ℕ} {k : ℕ} (hk : k < n) :
    tabAfter n code (k + 1) (code k) = leastBelow (fun v => code v = code k) n n + 1 := by
  classical
  have hex : ∃ v, v < k + 1 ∧ code v = code k := ⟨k, by omega, rfl⟩
  unfold tabAfter
  rw [if_pos hex, leastBelow_mono_eq (m := n) (k := k + 1) (by omega) hex]

theorem tabAfter_le {n : ℕ} {code : ℕ → ℕ} {k t : ℕ} (hk : k ≤ n) : tabAfter n code k t ≤ n := by
  classical
  unfold tabAfter
  split_ifs with h
  · have := (leastBelow_spec (d := n) h).1; omega
  · omega

theorem tabAfter_ne_zero {n : ℕ} {code : ℕ → ℕ} {k t : ℕ} (h : tabAfter n code k t ≠ 0) :
    ∃ v, v < k ∧ code v = t := by
  classical
  unfold tabAfter at h
  split_ifs at h with hex
  · exact hex
  · exact absurd rfl h

theorem refPass1_run {B n M : ℕ} {L κ : ℕ → ℕ} (Ctx : Env → Prop)
    (hL : ∀ u < n, L u < n) (hκ : ∀ u < n, κ u < M) (hB : n * M + n + 2 < B) (hMB : M < B)
    (hC : ∀ τ, Ctx τ → RefCtx n M L κ τ)
    (hCv : ∀ τ v, Ctx τ → Ctx (τ.setVar "ru" v)) (hCt : ∀ τ v, Ctx τ → Ctx (τ.setVar "rt" v))
    (hCa : ∀ τ a i v, Ctx τ → a ∈ ["lab2", "tab"] → Ctx (τ.setArr a i v))
    {σ : Env} (hσ : Ctx σ) (hz : Zero σ "tab") :
    ∃ σ', Run B refPass1 σ σ' (n * 50 + 10) ∧ Ctx σ' ∧
      (σ'.arrs "tab").length = (σ.arrs "tab").length ∧
      (∀ t < (σ'.arrs "tab").length, (σ'.arrs "tab")[t]? = some 0 ∨
        ∃ v, v < n ∧ L v * M + κ v = t) ∧
      Vec σ' "lab2" n (fun u => leastBelow (fun v => L v * M + κ v = L u * M + κ u) n n) := by
  set code : ℕ → ℕ := fun v => L v * M + κ v with hcode
  have hcl : ∀ u < n, code u < n * M := fun u hu => code_lt hL hκ hu
  let I : ℕ → Env → Prop := fun k τ => Ctx τ ∧
    (τ.arrs "tab").length = (σ.arrs "tab").length ∧
    (∀ t < (τ.arrs "tab").length, (τ.arrs "tab")[t]? = some (tabAfter n code k t)) ∧
    (τ.arrs "lab2").length = n ∧
    ∀ u < k, (τ.arrs "lab2")[u]? = some (leastBelow (fun v => code v = code u) n n)
  have hσC := hC σ hσ
  obtain ⟨σ', hr, ⟨hC', hlen', htab', hl2', hlab2'⟩, -⟩ :=
    forUp_run (B := B) (i := "ru") (e := .var "n") (N := n) (K := 40) I (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [(hC τ hI.1).hn]; omega), (hC τ hI.1).hn])
      (σ := σ) ⟨hCv _ _ hσ, by simp,
        fun t ht => by
          have := hz t (by simpa using ht)
          simpa [tabAfter] using this,
        by simp [hσC.hlab2], fun u hu => absurd hu (Nat.not_lt_zero _)⟩
      (by
        rintro k hk τ ⟨hCτ, hlen, htab, hl2, hlab2⟩ hku
        have hR := hC τ hCτ
        have hck := hcl k hk
        have htl : n * M ≤ (τ.arrs "tab").length := hR.htab
        have hcB : code k < B := by omega
        set τ1 := τ.setVar "rt" (code k) with hτ1
        have hr1 : Run B (.assign "rt" codeE) τ τ1 (1 + codeE.size) :=
          Run.assign (evalB_codeE hR hL hκ hku hk (by omega) (by omega) hMB)
        have hR1 : RefCtx n M L κ τ1 := hR.setVar _ _ (by decide) (by decide)
        have hold : (τ1.arrs "tab")[code k]? = some (tabAfter n code k (code k)) := by
          simpa [hτ1] using htab (code k) (by omega)
        have holdB : tabAfter n code k (code k) < B := by
          have := tabAfter_le (code := code) (t := code k) (show k ≤ n by omega); omega
        -- the conditional store
        have hstep : ∃ τ2, Run B (.ite (.eq (.get "tab" (.var "rt")) (.lit 0))
            (.store "tab" (.var "rt") (.add (.var "ru") (.lit 1))) .skip) τ1 τ2 12 ∧
            Ctx τ2 ∧ τ2.vars "ru" = k ∧ τ2.vars "rt" = code k ∧
            (τ2.arrs "lab2") = (τ.arrs "lab2") ∧
            (τ2.arrs "tab").length = (σ.arrs "tab").length ∧
            ∀ t < (τ2.arrs "tab").length, (τ2.arrs "tab")[t]? = some (tabAfter n code (k + 1) t) := by
          have hev : (Cond.eq (.get "tab" (.var "rt")) (.lit 0)).evalB B τ1 =
              some (decide (tabAfter n code k (code k) = 0)) :=
            by rw [evalB_condEq' (evalB_get (evalB_var (by simp [hτ1]; omega))
                (by simpa [hτ1] using hold) holdB) (evalB_lit (by omega))]
          by_cases h0 : tabAfter n code k (code k) = 0
          · refine ⟨τ1.setArr "tab" (code k) (k + 1), (Run.ite_true (by rw [hev]; simp [h0])
              (Run.store (by simp [hτ1]; omega) (by simp [hτ1, hku]; omega)
                (by simp [hτ1]; omega))).mono (by simp), hCa _ _ _ _ (hCt _ _ hCτ) (by simp), by simp [hτ1, hku], by simp [hτ1],
                by simp [hτ1], by simp [hτ1, hlen], fun t ht => ?_⟩
            simp only [hτ1, arrs_setArr, arrs_setVar, if_true] at ht ⊢
            rw [List.length_set] at ht
            rw [tabAfter_succ hk t, List.getElem?_set]
            by_cases htk : code k = t
            · subst htk; simp [ht, h0]
            · rw [if_neg htk, if_neg (fun h => htk h.1.symm)]; exact htab t ht
          · refine ⟨τ1, (Run.ite_false (by rw [hev]; simp [h0]) Run.skip).mono (by simp),
              hCt _ _ hCτ, by simp [hτ1, hku], by simp [hτ1],
              by simp [hτ1], by simp [hτ1, hlen], fun t ht => ?_⟩
            simp only [hτ1, arrs_setVar] at ht ⊢
            rw [tabAfter_succ hk t, if_neg (show ¬ (t = code k ∧ tabAfter n code k t = 0) from
              fun h => h0 (h.1 ▸ h.2))]; exact htab t ht
        obtain ⟨τ2, hr2, hC2, hu2, ht2, hl2e, hlen2, htab2⟩ := hstep
        have hR2 := hC τ2 hC2
        have hnew : (τ2.arrs "tab")[code k]? =
            some (leastBelow (fun v => code v = code k) n n + 1) := by
          rw [htab2 _ (by have := hR2.htab; omega), tabAfter_code hk]
        have hlbB : leastBelow (fun v => code v = code k) n n + 1 < B := by
          have := leastBelow_lt_of (p := fun v => code v = code k) (le_refl n); omega
        refine ⟨τ2.setArr "lab2" k (leastBelow (fun v => code v = code k) n n),
          (Run.seq hr1 (Run.seq hr2 (Run.store (i := .var "ru") (e := .sub (.get "tab" (.var "rt")) (.lit 1)) (idx := k)
            (v := leastBelow (fun v => code v = code k) n n) (by simp [hu2]; omega)
            (by
              simp only [evalB_bin_iff, evalB_get_iff, evalB_var_iff, evalB_lit_iff]
              refine ⟨_, 1, ⟨_, ⟨rfl, by rw [ht2]; omega⟩, by rw [ht2]; exact hnew, hlbB⟩,
                ⟨rfl, by omega⟩, by simp, by omega⟩)
            (by rw [hl2e, hl2]; omega)))).mono (by simp [codeE]),
          by simp [hu2], ?_⟩
        refine ⟨hCv _ _ (hCa _ _ _ _ hC2 (by simp)),
          by simp [hlen2], fun t ht => by simpa using htab2 t (by simpa using ht),
          by simp [hl2e, hl2], fun u hu => ?_⟩
        simp only [arrs_setVar, arrs_setArr, if_true]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
        · rw [List.getElem?_set_ne (by omega), hl2e]; exact hlab2 u hu
        · rw [List.getElem?_set_self (by rw [hl2e, hl2]; omega)])
  refine ⟨σ', hr.mono (by simp; omega), hC', hlen', fun t ht => ?_, ⟨hl2', fun u hu => hlab2' u hu⟩⟩
  rw [htab' t ht]
  by_cases h0 : tabAfter n code n t = 0
  · left; rw [h0]
  · right; exact tabAfter_ne_zero h0

theorem refPass2_run {B n M : ℕ} {L κ : ℕ → ℕ} (Ctx : Env → Prop)
    (hL : ∀ u < n, L u < n) (hκ : ∀ u < n, κ u < M) (hB : n * M + n + 2 < B) (hMB : M < B)
    (hC : ∀ τ, Ctx τ → RefCtx n M L κ τ)
    (hCv : ∀ τ v, Ctx τ → Ctx (τ.setVar "ru" v)) (hCt : ∀ τ v, Ctx τ → Ctx (τ.setVar "rt" v))
    (hCa : ∀ τ a i v, Ctx τ → a ∈ ["lab2", "tab"] → Ctx (τ.setArr a i v))
    {σ : Env} (hσ : Ctx σ)
    (ht : ∀ t < (σ.arrs "tab").length, (σ.arrs "tab")[t]? = some 0 ∨
        ∃ v, v < n ∧ L v * M + κ v = t) :
    ∃ σ', Run B refPass2 σ σ' (n * 30 + 10) ∧ Ctx σ' ∧
      (σ'.arrs "tab").length = (σ.arrs "tab").length ∧ Zero σ' "tab" ∧
      σ'.arrs "lab2" = σ.arrs "lab2" := by
  let I : ℕ → Env → Prop := fun k τ => Ctx τ ∧
    (τ.arrs "tab").length = (σ.arrs "tab").length ∧ τ.arrs "lab2" = σ.arrs "lab2" ∧
    (∀ t < (τ.arrs "tab").length, (τ.arrs "tab")[t]? = some 0 ∨
        ∃ v, k ≤ v ∧ v < n ∧ L v * M + κ v = t)
  obtain ⟨σ', hr, ⟨hC', hlen', hl2', ht'⟩, -⟩ :=
    forUp_run (B := B) (i := "ru") (e := .var "n") (N := n) (K := 20) I (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [(hC τ hI.1).hn]; omega), (hC τ hI.1).hn])
      (σ := σ) ⟨hCv _ _ hσ, by simp, by simp,
        fun t htl => by
          rcases ht t (by simpa using htl) with h | ⟨v, hv, h⟩
          · left; simpa using h
          · right; exact ⟨v, Nat.zero_le _, hv, h⟩⟩
      (by
        rintro k hk τ ⟨hCτ, hlen, hl2, htz⟩ hku
        have hR := hC τ hCτ
        have hck := code_lt hL hκ hk
        refine ⟨τ.setArr "tab" (L k * M + κ k) 0, (Run.store (e := .lit 0)
          (evalB_codeE hR hL hκ hku hk (by omega) (by omega) hMB) (by simp; omega)
          (by have := hR.htab; omega)).mono (by simp [codeE]), by simp [hku],
          hCv _ _ (hCa _ _ _ _ hCτ (by simp)),
          by simp [hlen], by simp [hl2], fun t htl => ?_⟩
        simp only [arrs_setVar, arrs_setArr, if_true, List.length_set] at htl ⊢
        rw [List.getElem?_set]
        by_cases htk : L k * M + κ k = t
        · left; subst htk; simp [htl]
        · rw [if_neg htk]
          rcases htz t htl with h | ⟨v, hv, hvn, h⟩
          · left; exact h
          · right
            rcases Nat.lt_or_ge v (k + 1) with hv' | hv'
            · have : v = k := by omega
              subst this; exact absurd h htk
            · exact ⟨v, hv', hvn, h⟩)
  refine ⟨σ', hr.mono (by simp; omega), hC', hlen', fun t htl => ?_, hl2'⟩
  rcases ht' t htl with h | ⟨v, hv, hvn, -⟩
  · exact h
  · omega

theorem refPass3_run {B n : ℕ} {f : ℕ → ℕ} (Ctx : Env → Prop) (hnB : n + 1 < B)
    (hf : ∀ u < n, f u < B)
    (hCn : ∀ τ, Ctx τ → τ.vars "n" = n)
    (hCv : ∀ τ v, Ctx τ → Ctx (τ.setVar "ru" v))
    (hCa : ∀ τ i v, Ctx τ → Ctx (τ.setArr "lab" i v))
    {σ : Env} (hσ : Ctx σ) (h2 : Vec σ "lab2" n f) (hl : (σ.arrs "lab").length = n) :
    ∃ σ', Run B refPass3 σ σ' (n * 20 + 10) ∧ Ctx σ' ∧ Vec σ' "lab" n f ∧
      σ'.arrs "lab2" = σ.arrs "lab2" := by
  let I : ℕ → Env → Prop := fun k τ => Ctx τ ∧ τ.arrs "lab2" = σ.arrs "lab2" ∧
    (τ.arrs "lab").length = n ∧ ∀ u < k, (τ.arrs "lab")[u]? = some (f u)
  obtain ⟨σ', hr, ⟨hC', hl2', hl', hv'⟩, -⟩ :=
    forUp_run (B := B) (i := "ru") (e := .var "n") (N := n) (K := 10) I (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [hCn τ hI.1]; omega), hCn τ hI.1])
      (σ := σ) ⟨hCv _ _ hσ, by simp, by simp [hl], fun u hu => absurd hu (Nat.not_lt_zero _)⟩
      (by
        rintro k hk τ ⟨hCτ, hl2, hlen, hv⟩ hku
        have h2' : Vec τ "lab2" n f := h2.of_eq hl2
        refine ⟨τ.setArr "lab" k (f k), (Run.store (i := .var "ru") (by simp [hku]; omega)
          (h2'.evalB hku hk (by omega) (hf k hk)) (by omega)).mono (by simp), by simp [hku],
          hCv _ _ (hCa _ _ _ hCτ), by simp [hl2], by simp [hlen], fun u hu => ?_⟩
        simp only [arrs_setVar, arrs_setArr, if_true]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
        · rw [List.getElem?_set_ne (by omega)]; exact hv u hu
        · rw [List.getElem?_set_self (by omega)])
  exact ⟨σ', hr.mono (by simp; omega), hC', ⟨hl', hv'⟩, hl2'⟩

/-- **Refining a labelling.** Afterwards `lab` maps `u` to the least
`v < n` with `L v = L u` and `κ v = κ u`, and `tab` is zero again. -/
theorem refine_run {B n M : ℕ} {L κ : ℕ → ℕ} (Ctx : Env → Prop)
    (hL : ∀ u < n, L u < n) (hκ : ∀ u < n, κ u < M) (hB : n * M + n + 2 < B) (hMB : M < B)
    (hCn : ∀ τ, Ctx τ → τ.vars "n" = n) (hCM : ∀ τ, Ctx τ → τ.vars "M" = M)
    (hCk : ∀ τ, Ctx τ → Vec τ "key" n κ)
    (hCv : ∀ τ v, Ctx τ → Ctx ((τ.setVar "ru" v)))
    (hCt : ∀ τ v, Ctx τ → Ctx ((τ.setVar "rt" v)))
    (hCa : ∀ τ a i v, Ctx τ → a ∈ ["lab", "lab2", "tab"] → Ctx (τ.setArr a i v))
    {σ : Env} (hσ : Ctx σ) (hlab : Vec σ "lab" n L) (hz : Zero σ "tab")
    (htab : n * M ≤ (σ.arrs "tab").length) (hl2 : (σ.arrs "lab2").length = n) :
    ∃ σ', Run B refine σ σ' (n * 100 + 40) ∧ Ctx σ' ∧
      Vec σ' "lab" n (fun u => leastBelow (fun v => L v = L u ∧ κ v = κ u) n n) ∧
      Zero σ' "tab" ∧ (σ'.arrs "tab").length = (σ.arrs "tab").length ∧
      (σ'.arrs "lab2").length = n := by
  -- passes 1 and 2 keep `lab`
  let C1 : Env → Prop := fun τ => Ctx τ ∧ τ.arrs "lab" = σ.arrs "lab" ∧
    (τ.arrs "tab").length = (σ.arrs "tab").length ∧ (τ.arrs "lab2").length = n
  have hC1 : ∀ τ, C1 τ → RefCtx n M L κ τ := fun τ h =>
    ⟨hCn τ h.1, hCM τ h.1, hlab.of_eq h.2.1, hCk τ h.1, h.2.2.2, by rw [h.2.2.1]; exact htab⟩
  have hC1v : ∀ τ v, C1 τ → C1 (τ.setVar "ru" v) := fun τ v h =>
    ⟨hCv _ _ h.1, by simp [h.2.1], by simp [h.2.2.1], by simp [h.2.2.2]⟩
  have hC1t : ∀ τ v, C1 τ → C1 (τ.setVar "rt" v) := fun τ v h =>
    ⟨hCt _ _ h.1, by simp [h.2.1], by simp [h.2.2.1], by simp [h.2.2.2]⟩
  have hC1a : ∀ τ a i v, C1 τ → a ∈ ["lab2", "tab"] → C1 (τ.setArr a i v) := by
    intro τ a i v h ha
    have hal : a ≠ "lab" := by simp at ha; rcases ha with rfl | rfl <;> decide
    refine ⟨hCa _ _ _ _ h.1 (by simp at ha ⊢; tauto), by simp [Ne.symm hal, h.2.1], ?_, ?_⟩
    · simp only [length_arrs_setArr]; exact h.2.2.1
    · simp only [length_arrs_setArr]; exact h.2.2.2
  have hσ1 : C1 σ := ⟨hσ, rfl, rfl, hl2⟩
  obtain ⟨σ1, hr1, hC1', htl1, ht1, hv1⟩ :=
    refPass1_run C1 hL hκ hB hMB hC1 hC1v hC1t hC1a hσ1 hz
  obtain ⟨σ2, hr2, hC2, htl2, hz2, hl22⟩ :=
    refPass2_run C1 hL hκ hB hMB hC1 hC1v hC1t hC1a hC1' ht1
  -- the new labels
  set f : ℕ → ℕ := fun u => leastBelow (fun v => L v * M + κ v = L u * M + κ u) n n with hf
  have hfeq : ∀ u < n, f u = leastBelow (fun v => L v = L u ∧ κ v = κ u) n n := by
    intro u hu
    refine leastBelow_congr fun v hv => ⟨fun h => ?_, fun ⟨h1, h2⟩ => by rw [h1, h2]⟩
    exact code_inj (hκ v hv) (hκ u hu) h
  have hfB : ∀ u < n, f u < B := by
    intro u _; have := leastBelow_lt_of (p := fun v => L v * M + κ v = L u * M + κ u) (le_refl n)
    simp only [hf]; omega
  let C3 : Env → Prop := fun τ => Ctx τ ∧ (τ.arrs "tab") = (σ2.arrs "tab")
  obtain ⟨σ3, hr3, ⟨hC3, ht3⟩, hv3, hl23⟩ :=
    refPass3_run (f := f) C3 (by nlinarith) hfB (fun τ h => hCn τ h.1)
      (fun τ v h => ⟨hCv _ _ h.1, by simp [h.2]⟩)
      (fun τ i v h => ⟨hCa _ _ _ _ h.1 (by simp), by simp [h.2]⟩)
      ⟨hC2.1, rfl⟩ (hv1.of_eq hl22) (by rw [hC2.2.1, hlab.len])
  refine ⟨σ3, (Run.seq hr1 (Run.seq hr2 hr3)).mono (by omega), hC3,
    hv3.congr hfeq, fun t ht => ?_, by rw [ht3, htl2, htl1], ?_⟩
  · rw [ht3] at ht ⊢; exact hz2 t ht
  · rw [hl23]; exact hC2.2.2.2

end Lax185574Proofs.Chain.Ram
