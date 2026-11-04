import Lax185574Proofs.ResolveRam.Glue.PCT0
import Lax185574Proofs.Conversions.Ram.Classify

/-!
The sorted colors in a tape program.

The colors of the vertices are in the array `co`. Round `c` of `rounds`
scans the vertices for the least color at least `lo` (`scan`), and if
there is one it stores the color and its first vertex at position `cnt`
of the arrays `sy` and `su` and moves `lo` above it. For the strictly
increasing list `L` of the colors, round `c` finds `L[c]` while `c < |L|`
and nothing after (`round_some`, `round_none`), so after `n` rounds the
arrays hold `L` and the first vertices of its colors (`rounds_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.Conversions.Ram

/-! ### Sorted lists -/

/-- The lower bound after `c` rounds. -/
def loR (L : List ℕ) : ℕ → ℕ
  | 0 => 0
  | c + 1 => if h : c < L.length then L[c] + 1 else loR L c

theorem mem_drop_loR {L : List ℕ} (hL : L.Pairwise (· < ·)) :
    ∀ c y, (y ∈ L ∧ loR L c ≤ y) ↔ y ∈ L.drop c
  | 0, y => by simp [loR]
  | c + 1, y => by
    have hP := List.pairwise_iff_getElem.1 hL
    by_cases hc : c < L.length
    · simp only [loR, dif_pos hc, List.mem_drop_iff_getElem]
      constructor
      · rintro ⟨hy, hle⟩
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hy
        have hcj : c < j := by
          by_contra hn
          rcases Nat.lt_or_eq_of_le (Nat.le_of_not_lt hn) with h | h
          · have := hP j c hj hc h; omega
          · subst h; omega
        exact ⟨j - (c + 1), by omega, by congr 1; omega⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨List.getElem_mem _, by have := hP c (c + 1 + j) hc (by omega) (by omega); omega⟩
    · have h1 : L.drop (c + 1) = [] := List.drop_eq_nil_of_le (by omega)
      have h2 : L.drop c = [] := List.drop_eq_nil_of_le (by omega)
      simp only [loR, dif_neg hc, h1]
      have := mem_drop_loR hL c y
      rw [h2] at this
      simpa using this

/-- What a scan of the vertices below `k` found: nothing at least `lo`
(`fd = 0`), or the least color `m` at least `lo` and its first vertex `u`. -/
def ScanOK (col : ℕ → ℕ) (lo k fd m u : ℕ) : Prop :=
  (fd = 0 ∧ ∀ w < k, col w < lo) ∨
  (fd = 1 ∧ u < k ∧ lo ≤ col u ∧ m = col u ∧ ∀ w < k, lo ≤ col w → m ≤ col w ∧ (col w = m → u ≤ w))

theorem round_none {L : List ℕ} {col : ℕ → ℕ} {n : ℕ} (hL : L.Pairwise (· < ·))
    (hmem : ∀ y, y ∈ L ↔ ∃ w < n, col w = y) {c fd m u : ℕ} (hc : L.length ≤ c)
    (h : ScanOK col (loR L c) n fd m u) : fd = 0 := by
  have hno : ∀ w < n, ¬ loR L c ≤ col w := by
    intro w hw hle
    have := (mem_drop_loR hL c (col w)).1 ⟨(hmem _).2 ⟨w, hw, rfl⟩, hle⟩
    rw [List.drop_eq_nil_of_le hc] at this
    simp at this
  rcases h with ⟨h, -⟩ | ⟨-, hu, hle, -⟩
  · exact h
  · exact absurd hle (hno _ hu)

theorem round_some {L : List ℕ} {col : ℕ → ℕ} {n : ℕ} (hL : L.Pairwise (· < ·))
    (hmem : ∀ y, y ∈ L ↔ ∃ w < n, col w = y) {c fd m u : ℕ} (hc : c < L.length)
    (h : ScanOK col (loR L c) n fd m u) :
    fd = 1 ∧ m = L[c] ∧ u = leastBelow (fun w => col w = L[c]) n n := by
  have hP := List.pairwise_iff_getElem.1 hL
  have hLc : L[c] ∈ L.drop c := List.mem_drop_iff_getElem.2 ⟨0, by omega, by simp⟩
  obtain ⟨hLc1, hLc2⟩ := (mem_drop_loR hL c L[c]).2 hLc
  obtain ⟨w0, hw0, hcw0⟩ := (hmem _).1 hLc1
  rcases h with ⟨-, h⟩ | ⟨hfd, hu, hle, hm, hmin⟩
  · have := h w0 hw0; omega
  have hmL : m = L[c] := by
    have hmd : m ∈ L.drop c := (mem_drop_loR hL c m).1 ⟨(hmem _).2 ⟨u, hu, hm.symm⟩, by omega⟩
    obtain ⟨j, hj, hjm⟩ := List.mem_drop_iff_getElem.1 hmd
    have h1 : L[c] ≤ m := by
      rw [← hjm]
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · simp [h0]
      · exact le_of_lt (hP c (c + j) hc (by omega) (by omega))
    have h2 := (hmin w0 hw0 (by omega)).1
    omega
  refine ⟨hfd, hmL, ?_⟩
  have hex : ∃ w, w < n ∧ col w = L[c] := ⟨u, hu, by omega⟩
  obtain ⟨g1, g2, g3⟩ := leastBelow_spec (d := n) hex
  set lb := leastBelow (fun w => col w = L[c]) n n
  rcases lt_trichotomy lb u with h | h | h
  · have := (hmin lb g1 (by rw [g2]; omega)).2 (by omega); omega
  · exact h.symm
  · exact absurd (by omega : col u = L[c]) (g3 u h)

/-! ### The scan -/

/-- Keep vertex `w` as the best one. -/
def sSet : Com :=
  .seq (.assign "fd" (.lit 1)) (.seq (.assign "m" (.get "co" (.var "w"))) (.assign "u" (.var "w")))

/-- One vertex of the scan. -/
def sBody : Com :=
  .ite (.lt (.get "co" (.var "w")) (.var "lo")) .skip
    (.ite (.eq (.var "fd") (.lit 0)) sSet (.ite (.lt (.get "co" (.var "w")) (.var "m")) sSet .skip))

/-- **The scan for the least color at least `lo`.** -/
def scan : Com := .seq (.assign "fd" (.lit 0)) (forUp "w" (.var "n") sBody)

theorem sSet_run {B n k : ℕ} {col : ℕ → ℕ} {τ : Env} (hw : τ.vars "w" = k) (hk : k < n)
    (hco : τ.arrs "co" = arrOf n col) (hcolB : col k < B) (hnB : n < B) :
    Run B sSet τ (((τ.setVar "fd" 1).setVar "m" (col k)).setVar "u" k) 10 := by
  refine (Run.seq (Run.assign (by simp ; omega)) (Run.seq (Run.assign ?_) (Run.assign ?_))).mono (by simp)
  · simp [hw, hco, hk, hcolB] ; omega
  · simp [hw] ; omega

theorem sBody_run {B n lo k fd m u : ℕ} {col : ℕ → ℕ} {τ : Env} (hw : τ.vars "w" = k) (hk : k < n)
    (hco : τ.arrs "co" = arrOf n col) (hcolB : ∀ w < n, col w < B) (hnB : n < B) (hlo : τ.vars "lo" = lo)
    (hloB : lo < B) (hfd : τ.vars "fd" = fd) (hm : τ.vars "m" = m) (hu : τ.vars "u" = u)
    (hS : ScanOK col lo k fd m u) :
    ∃ τ', Run B sBody τ τ' 30 ∧ ScanOK col lo (k + 1) (τ'.vars "fd") (τ'.vars "m") (τ'.vars "u") ∧
      (∀ x, x ∉ ["fd", "m", "u"] → τ'.vars x = τ.vars x) ∧ τ'.arrs = τ.arrs := by
  have hck := hcolB k hk
  have hmB : fd = 1 → m < B := by
    intro h1
    rcases hS with ⟨h0, -⟩ | ⟨-, hu', -, hm', -⟩
    · omega
    · rw [hm']; exact hcolB u (by omega)
  have eco : (Expr.get "co" (.var "w")).evalB B τ = some (col k) := by simp [hw, hco, hk, hck]; omega
  have hset : ∀ τ0 : Env, τ0 = τ → ∃ τ', Run B sSet τ0 τ' 10 ∧ τ'.vars "fd" = 1 ∧ τ'.vars "m" = col k ∧
      τ'.vars "u" = k ∧ (∀ x, x ∉ ["fd", "m", "u"] → τ'.vars x = τ.vars x) ∧ τ'.arrs = τ.arrs := by
    rintro τ0 rfl
    refine ⟨_, sSet_run hw hk hco hck hnB, by simp, by simp, by simp, fun x hx => ?_, by simp⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    simp [hx.1, hx.2.1, hx.2.2]
  by_cases hlt : col k < lo
  · refine ⟨τ, (Run.ite_true (by simp [hw, hco, hk, hck, hlo]; omega) Run.skip).mono (by simp),
      ?_, fun _ _ => rfl, rfl⟩
    rw [hfd, hm, hu]
    rcases hS with ⟨h0, h⟩ | ⟨h1, hu', hle, hm', h⟩
    · exact Or.inl ⟨h0, fun w hw' => by
        rcases Nat.lt_succ_iff_lt_or_eq.1 hw' with h' | rfl
        · exact h w h'
        · exact hlt⟩
    · refine Or.inr ⟨h1, by omega, hle, hm', fun w hw' hlw => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hw' with h' | rfl
      · exact h w h' hlw
      · omega
  have hc1 : (Cond.lt (.get "co" (.var "w")) (.var "lo")).evalB B τ = some false := by
    simp [hw, hco, hk, hck, hlo]; omega
  by_cases hf0 : fd = 0
  · obtain ⟨τ', r', h1, h2, h3, hv, ha⟩ := hset τ rfl
    refine ⟨τ', (Run.ite_false hc1 (Run.ite_true (by simp [hfd, hf0] ; omega) r')).mono (by simp), ?_, hv, ha⟩
    rw [h1, h2, h3]
    rcases hS with ⟨-, h⟩ | ⟨h1', -⟩
    · refine Or.inr ⟨rfl, by omega, by omega, rfl, fun w hw' hlw => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hw' with h' | rfl
      · have := h w h'; omega
      · exact ⟨le_rfl, fun _ => le_rfl⟩
    · omega
  have hf1 : fd = 1 := by rcases hS with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  have hc2 : (Cond.eq (.var "fd") (.lit 0)).evalB B τ = some false := by
    simp [hfd, hf0]; omega
  obtain ⟨-, hu', hle, hm', hmin⟩ : fd = 1 ∧ u < k ∧ lo ≤ col u ∧ m = col u ∧
      ∀ w < k, lo ≤ col w → m ≤ col w ∧ (col w = m → u ≤ w) := by
    rcases hS with ⟨h, -⟩ | h
    · omega
    · exact h
  by_cases hlm : col k < m
  · obtain ⟨τ', r', h1, h2, h3, hv, ha⟩ := hset τ rfl
    refine ⟨τ', (Run.ite_false hc1 (Run.ite_false hc2 (Run.ite_true
      (by have := hmB hf1; simp [hw, hco, hk, hck, hm] ; omega) r'))).mono (by simp), ?_, hv, ha⟩
    rw [h1, h2, h3]
    refine Or.inr ⟨rfl, by omega, by omega, rfl, fun w hw' hlw => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hw' with h' | rfl
    · have := (hmin w h' hlw).1
      exact ⟨by omega, fun h => by omega⟩
    · exact ⟨le_rfl, fun _ => le_rfl⟩
  · refine ⟨τ, (Run.ite_false hc1 (Run.ite_false hc2 (Run.ite_false
      (by have := hmB hf1; simp [hw, hco, hk, hck, hm] ; omega) Run.skip))).mono (by simp), ?_,
      fun _ _ => rfl, rfl⟩
    rw [hfd, hm, hu]
    refine Or.inr ⟨hf1, by omega, hle, hm', fun w hw' hlw => ?_⟩
    rcases Nat.lt_succ_iff_lt_or_eq.1 hw' with h' | rfl
    · exact hmin w h' hlw
    · exact ⟨by omega, fun _ => by omega⟩

/-- **The scan.** -/
theorem scan_run {B n lo : ℕ} {col : ℕ → ℕ} {σ : Env} (hn : σ.vars "n" = n)
    (hco : σ.arrs "co" = arrOf n col) (hcolB : ∀ w < n, col w < B) (hnB : n + 1 < B) (hlo : σ.vars "lo" = lo)
    (hloB : lo < B) :
    ∃ σ', Run B scan σ σ' (n * 38 + 8) ∧ ScanOK col lo n (σ'.vars "fd") (σ'.vars "m") (σ'.vars "u") ∧
      (∀ x, x ∉ ["fd", "m", "u", "w"] → σ'.vars x = σ.vars x) ∧ σ'.arrs = σ.arrs := by
  set σ0 := σ.setVar "fd" 0
  have r0 : Run B (.assign "fd" (.lit 0)) σ σ0 2 := (Run.assign (by simp; omega)).mono (by simp)
  let I : ℕ → Env → Prop := fun k τ => ScanOK col lo k (τ.vars "fd") (τ.vars "m") (τ.vars "u") ∧
    (∀ x, x ∉ ["fd", "m", "u", "w"] → τ.vars x = σ.vars x) ∧ τ.arrs = σ.arrs
  obtain ⟨σ', r1, ⟨hS, hv, ha⟩, -⟩ := forUp_run (B := B) (i := "w") (e := .var "n") (body := sBody)
    (N := n) (K := 30) I (σ := σ0) (by omega)
    (fun k _ τ hI _ => by rw [evalB_var_iff]; rw [hI.2.1 "n" (by decide), hn]; omega)
    ⟨Or.inl ⟨by simp [σ0], fun w hw => absurd hw (Nat.not_lt_zero _)⟩,
      fun x hx => by simp only [List.mem_cons, not_or] at hx; simp [σ0, hx.1, hx.2.2.2.1], by simp [σ0]⟩
    (by
      rintro k hk τ ⟨hS, hv, ha⟩ hwk
      obtain ⟨τ', r', hS', hv', ha'⟩ := sBody_run (B := B) (n := n) (lo := lo) hwk hk (by rw [ha, hco])
        hcolB (by omega) (by rw [hv "lo" (by decide), hlo]) hloB rfl rfl rfl hS
      refine ⟨τ', r', by rw [hv' "w" (by decide), hwk], ?_, fun x hx => ?_, by simp [ha', ha]⟩
      · simpa using hS'
      · simp only [List.mem_cons, not_or] at hx
        simp only [vars_setVar, if_neg hx.2.2.2.1]
        rw [hv' x (by simp [hx.1, hx.2.1, hx.2.2.1]), hv x (by simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1])])
  refine ⟨σ', (Run.seq r0 r1).mono (by simp; omega), hS, hv, ha⟩

/-! ### The rounds -/

/-- Store the color found and its first vertex. -/
def rAct : Com :=
  .seq (.store "sy" (.var "cnt") (.var "m")) (.seq (.store "su" (.var "cnt") (.var "u"))
    (.seq (.assign "cnt" (.add (.var "cnt") (.lit 1))) (.assign "lo" (.add (.var "m") (.lit 1)))))

/-- One round. -/
def rBody : Com := .seq scan (.ite (.eq (.var "fd") (.lit 1)) rAct .skip)

/-- **The rounds.** -/
def rounds : Com := .seq (.assign "lo" (.lit 0)) (.seq (.assign "cnt" (.lit 0)) (forUp "c" (.var "n") rBody))

/-- The first vertex of color `y`. -/
noncomputable def fstV (col : ℕ → ℕ) (n y : ℕ) : ℕ := leastBelow (fun w => col w = y) n n

/-- The state after `c` rounds. -/
def RoundsAt (L : List ℕ) (col : ℕ → ℕ) (n c : ℕ) (τ : Env) : Prop :=
  τ.vars "lo" = loR L c ∧ τ.vars "cnt" = min c L.length ∧ (τ.arrs "sy").length = n ∧
    (τ.arrs "su").length = n ∧
    ∀ j (hj : j < min c L.length), (τ.arrs "sy")[j]? = some (L[j]'(by omega)) ∧
      (τ.arrs "su")[j]? = some (fstV col n (L[j]'(by omega)))

theorem loR_lt {L : List ℕ} {B : ℕ} (hB : 0 < B) (hLB : ∀ y ∈ L, y + 1 < B) : ∀ c, loR L c < B
  | 0 => by simpa [loR] using hB
  | c + 1 => by
    simp only [loR]
    split_ifs with h
    · exact hLB _ (List.getElem_mem h)
    · exact loR_lt hB hLB c

theorem rBody_run {B n c : ℕ} {L : List ℕ} {col : ℕ → ℕ} {τ : Env} (hL : L.Pairwise (· < ·))
    (hmem : ∀ y, y ∈ L ↔ ∃ w < n, col w = y) (hLn : L.length ≤ n) (hn : τ.vars "n" = n)
    (hco : τ.arrs "co" = arrOf n col) (hcolB : ∀ w < n, col w + 1 < B) (hnB : n + 1 < B)
    (hR : RoundsAt L col n c τ) :
    ∃ τ', Run B rBody τ τ' (n * 38 + 40) ∧ RoundsAt L col n (c + 1) τ' ∧
      (∀ x, x ∉ ["fd", "m", "u", "w", "cnt", "lo"] → τ'.vars x = τ.vars x) ∧
      τ'.arrs "co" = τ.arrs "co" := by
  obtain ⟨hlo, hcnt, hsyl, hsul, hj⟩ := hR
  have hLB : ∀ y ∈ L, y + 1 < B := by
    intro y hy; obtain ⟨w, hw, rfl⟩ := (hmem y).1 hy; exact hcolB w hw
  obtain ⟨τ1, r1, hS, hv1, ha1⟩ := scan_run (B := B) (lo := loR L c) hn hco
    (fun w hw => by have := hcolB w hw; omega) hnB hlo (loR_lt (by omega) hLB c)
  have hv1' : ∀ x ∈ ["n", "cnt", "lo", "c"], τ1.vars x = τ.vars x := by
    intro x hx; exact hv1 x (by simp at hx ⊢; rcases hx with h | h | h | h <;> subst h <;> decide)
  by_cases hc : c < L.length
  · obtain ⟨hfd, hm, hu⟩ := round_some hL hmem hc hS
    have hcn : c < n := by omega
    have hmin : min c L.length = c := by omega
    have hcnt1 : τ1.vars "cnt" = c := by rw [hv1' "cnt" (by simp), hcnt, hmin]
    have hLcB := hLB _ (List.getElem_mem hc)
    set τ2 := τ1.setArr "sy" c L[c]
    set τ3 := τ2.setArr "su" c (fstV col n L[c])
    set τ4 := τ3.setVar "cnt" (c + 1)
    set τ5 := τ4.setVar "lo" (L[c] + 1)
    have hufB : fstV col n L[c] < B := by
      have : fstV col n L[c] = τ1.vars "u" := hu.symm
      have hu' : τ1.vars "u" < n := by
        rcases hS with ⟨h, -⟩ | ⟨-, h, -⟩
        · omega
        · exact h
      omega
    have ract : Run B rAct τ1 τ5 22 := by
      refine (Run.seq (Run.store ?_ ?_ ?_) (Run.seq (Run.store ?_ ?_ ?_)
        (Run.seq (Run.assign ?_) (Run.assign ?_)))).mono (by simp)
      · simp [hcnt1]; omega
      · simp [hm]; omega
      · rw [ha1, hsyl]; omega
      · simp [hcnt1]; omega
      · have hu' : τ1.vars "u" = fstV col n L[c] := hu
        simp [hu']; omega
      · simp [ha1, hsul]; omega
      · simp [hcnt1]; omega
      · simp [hm]; omega
    refine ⟨τ5, (Run.seq r1 (Run.ite_true (by simp [hfd]; omega) ract)).mono (by simp), ?_, ?_, ?_⟩
    · refine ⟨by simp [τ5, loR, hc], by simp [τ5, τ4]; omega, by simp [τ5, τ4, τ3, τ2, ha1, hsyl],
        by simp [τ5, τ4, τ3, τ2, ha1, hsul], fun j hj' => ?_⟩
      simp only [τ5, τ4, τ3, τ2, arrs_setVar, arrs_setArr, if_true, ha1]
      simp only [show ("sy" = "su") = False by decide, show ("su" = "sy") = False by decide, if_false,
        List.getElem?_set]
      rcases Nat.lt_succ_iff_lt_or_eq.1 (show j < c + 1 by omega) with h | rfl
      · have := hj j (by omega)
        simp only [show ¬ c = j by omega, if_false]
        exact this
      · simp [hsyl, hsul, hcn]
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
      simp only [τ5, τ4, τ3, τ2, vars_setVar, vars_setArr, if_neg hx.2.2.2.2.2, if_neg hx.2.2.2.2.1]
      exact hv1 x (by simp [hx.1, hx.2.1, hx.2.2.1, hx.2.2.2.1])
    · simp [τ5, τ4, τ3, τ2, ha1]
  · have hfd := round_none hL hmem (by omega) hS
    refine ⟨τ1, (Run.seq r1 (Run.ite_false (by simp [hfd]; omega) Run.skip)).mono (by simp), ?_, ?_, ?_⟩
    · refine ⟨by rw [hv1' "lo" (by simp), hlo]; simp [loR, hc], by rw [hv1' "cnt" (by simp), hcnt]; omega,
        by rw [ha1, hsyl], by rw [ha1, hsul], fun j hj' => by rw [ha1]; exact hj j (by omega)⟩
    · intro x hx
      exact hv1 x (by simp at hx ⊢; tauto)
    · rw [ha1]

/-- **The rounds.** -/
theorem rounds_run {B n : ℕ} {L : List ℕ} {col : ℕ → ℕ} {σ : Env} (hL : L.Pairwise (· < ·))
    (hmem : ∀ y, y ∈ L ↔ ∃ w < n, col w = y) (hLn : L.length ≤ n) (hn : σ.vars "n" = n)
    (hco : σ.arrs "co" = arrOf n col) (hcolB : ∀ w < n, col w + 1 < B) (hnB : n + 1 < B)
    (hsy : (σ.arrs "sy").length = n) (hsu : (σ.arrs "su").length = n) :
    ∃ σ', Run B rounds σ σ' (n * (n * 38 + 50) + 20) ∧ RoundsAt L col n n σ' ∧
      (∀ x, x ∉ rounds.wvars → σ'.vars x = σ.vars x) ∧ σ'.arrs "co" = σ.arrs "co" := by
  set σ1 := (σ.setVar "lo" 0).setVar "cnt" 0
  have r0a : Run B (.assign "lo" (.lit 0)) σ (σ.setVar "lo" 0) 2 := (Run.assign (by simp; omega)).mono (by simp)
  have r0b : Run B (.assign "cnt" (.lit 0)) (σ.setVar "lo" 0) σ1 2 :=
    (Run.assign (by simp; omega)).mono (by simp)
  let I : ℕ → Env → Prop := fun c τ => RoundsAt L col n c τ ∧ τ.vars "n" = n ∧ τ.arrs "co" = σ.arrs "co"
  obtain ⟨σ', r1, ⟨hR, -, hco'⟩, -⟩ := forUp_run (B := B) (i := "c") (e := .var "n") (body := rBody)
    (N := n) (K := n * 38 + 40) I (σ := σ1) (by omega)
    (fun k _ τ hI _ => by rw [evalB_var_iff]; rw [hI.2.1]; omega)
    ⟨⟨by simp [σ1, loR], by simp [σ1], by simp [σ1, hsy], by simp [σ1, hsu],
      fun j hj => absurd hj (by simp)⟩, by simp [σ1, hn], by simp [σ1]⟩
    (by
      rintro k hk τ ⟨hR, hnτ, hcoτ⟩ hck
      obtain ⟨τ', r', hR', hv', ha'⟩ := rBody_run (B := B) hL hmem hLn hnτ (by rw [hcoτ, hco]) hcolB hnB hR
      refine ⟨τ', r', by rw [hv' "c" (by decide), hck], ?_, by simp [hv' "n" (by decide), hnτ],
        by simp [ha', hcoτ]⟩
      obtain ⟨a1, a2, a3, a4, a5⟩ := hR'
      exact ⟨by simp [a1], by simp [a2], by simp [a3], by simp [a4], by simpa using a5⟩)
  refine ⟨σ', ?_, hR, fun x hx => ?_, hco'⟩
  · unfold rounds
    exact (Run.seq r0a (Run.seq r0b r1)).mono (by simp; nlinarith)
  · unfold rounds at hx
    have := (Run.seq r0a (Run.seq r0b r1)).frame_var x hx
    exact this

end Lax185574Proofs.ResolveRam.Glue
