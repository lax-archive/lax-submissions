import Lax185574Proofs.MC.Ram.InitAtoms

/-!
The IMP+ command `buildInit` that writes the word of an initial tree
into the array `ta`. It builds the word level by level from the bottom
(`lvlWord`): level `d` is written into `tb` from the word of level
`d - 1` in `ta`, and then copied back into `ta`. The values of the run
are bounded by the length of the final word.
-/

namespace Lax185574Proofs.MC

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words

/-! ### Bounds on the levels -/

theorem lt_nine_pow (n : ℕ) : n < 9 ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ]; omega

theorem rmD_le (K q ℓ d : ℕ) (hd : d ≤ q) (hℓ : 1 ≤ ℓ) : rmD K d ≤ lvlLen K q ℓ d := by
  have ha : 1 ≤ ℓ + q - d := by omega
  have : rmD K d ≤ alen (ℓ + q - d) (rmD K d) (rpD K d) := by
    simp only [alen]; nlinarith [Nat.mul_le_mul ha ha]
  cases d with
  | zero => simpa [lvlLen] using this
  | succ d => simp only [lvlLen]; omega

theorem rpD_le (K q ℓ d : ℕ) (hd : d ≤ q) (hℓ : 1 ≤ ℓ) : rpD K d ≤ lvlLen K q ℓ d := by
  have ha : 1 ≤ ℓ + q - d := by omega
  have : rpD K d ≤ alen (ℓ + q - d) (rmD K d) (rpD K d) := by
    simp only [alen]; nlinarith [Nat.mul_le_mul ha ha]
  cases d with
  | zero => simpa [lvlLen] using this
  | succ d => simp only [lvlLen]; omega

theorem alen_le (K q ℓ d : ℕ) :
    alen (ℓ + q - d) (rmD K d) (rpD K d) ≤ lvlLen K q ℓ d := by
  cases d with
  | zero => simp [lvlLen]
  | succ d => simp only [lvlLen]; omega

theorem lvlLen_mono (K q ℓ : ℕ) (hℓ : 1 ≤ ℓ) : ∀ d e, d ≤ e → e ≤ q →
    lvlLen K q ℓ d ≤ lvlLen K q ℓ e := by
  intro d e hde heq
  induction e with
  | zero => obtain rfl : d = 0 := by omega
            exact le_rfl
  | succ e ih =>
      rcases Nat.lt_or_eq_of_le hde with h | rfl
      · have := ih (by omega) (by omega)
        have ha : 1 ≤ ℓ + q - (e + 1) := by omega
        simp only [lvlLen] at this ⊢
        nlinarith
      · exact le_rfl

/-! ### The commands -/

def cntE : Expr :=
  .add (.add (.add (.mul (.var "iwa") (.var "iwa")) (.var "iwa"))
    (.mul (.add (.var "iwrm") (.lit 1)) (.mul (.var "iwa") (.var "iwa"))))
    (.mul (.var "iwrp") (.var "iwa"))

/-- Append `ta[0], …, ta[iwn - 1]` to `tb`. -/
def copyTa : Com := forUp "iwj" (.var "iwn") (push1 "tb" "iwp" (.get "ta" (.var "iwj")))

/-- The extensions. -/
def wExts : Com :=
  forUp "iwi" (.var "iwa")
    (.seq (pushL "tb" "iwp" [.add (.var "iwn") (.lit 1), .var "iwi"]) copyTa)

/-- One level into `tb`. -/
def wLevel : Com :=
  .seq (.assign "iwp" (.lit 0)) (.seq (pushL "tb" "iwp" [cntE]) (.seq wAtoms
    (.ite (.eq (.var "iwd") (.lit 0)) .skip (.seq (pushL "tb" "iwp" [.var "iwa"]) wExts))))

/-- Copy `tb` back into `ta`. -/
def copyBack : Com :=
  .seq (.assign "iwn" (.lit 0)) (forUp "iwj" (.var "iwp") (push1 "ta" "iwn" (.get "tb" (.var "iwj"))))

/-- The bounds `ρ⁻` and `ρ⁺` of level `d`. -/
def powers : Com :=
  .seq (.assign "iwrm" (.lit 1))
    (.seq (forUp "iwe" (.mul (.add (.var "iwK") (.lit 1)) (.var "iwd"))
      (.assign "iwrm" (.mul (.var "iwrm") (.lit 9))))
    (.seq (.assign "iwrp" (.lit 1))
      (forUp "iwe" (.mul (.var "iwK") (.add (.var "iwd") (.lit 1)))
        (.assign "iwrp" (.mul (.var "iwrp") (.lit 9))))))

def levelBody : Com :=
  .seq (.assign "iwa" (.sub (.add (.var "iwl") (.var "iwq")) (.var "iwd")))
    (.seq powers (.seq wLevel copyBack))

/-- **The initial tree, into `ta`.** -/
def buildInit : Com := forUp "iwd" (.add (.var "iwq") (.lit 1)) levelBody

/-! ### Copying -/

theorem flatMap_getD (W : List ℕ) :
    (List.range W.length).flatMap (fun k => [W.getD k 0]) = W := by
  induction W using List.reverseRecOn with
  | nil => simp
  | append_singleton W x ih =>
      rw [List.length_append, List.length_singleton, flatMap_range_succ']
      conv_rhs => rw [← ih]
      congr 1
      · apply List.flatMap_congr; intro k hk
        rw [List.mem_range] at hk
        simp [List.getElem?_append_left hk]
      · simp

/-- Copy the array `src` (holding `W` in its first cells) to the end of
`dst`. -/
theorem copy_run {B : ℕ} {j src dst pv : String} (hj : j ≠ pv)
    {e : Expr} {W l : List ℕ} {σ : Env} (P : Env → Prop)
    (hPj : ∀ τ v, P τ → P (τ.setVar j v))
    (hPpush : ∀ τ τ', P τ → (∀ y, y ≠ pv → τ'.vars y = τ.vars y) →
      (∀ b, b ≠ dst → τ'.arrs b = τ.arrs b) →
      (τ'.arrs dst).length = (τ.arrs dst).length → P τ')
    (hsrc : ∀ τ, P τ → ∀ i (h : i < W.length), (τ.arrs src)[i]? = some W[i])
    (hcapP : ∀ τ, P τ → l.length + W.length ≤ (τ.arrs dst).length)
    (he : ∀ τ, P τ → e.evalB B τ = some W.length) (hP : P σ) (hF : Filled dst pv l σ)
    (hB : l.length + W.length + 1 < B) (hW : ∀ v ∈ W, v < B) :
    ∃ σ', Run B (forUp j e (push1 dst pv (.get src (.var j)))) σ σ'
      (W.length * (8 + e.size + 7) + e.size + 5) ∧ P σ' ∧ Filled dst pv (l ++ W) σ' := by
  obtain ⟨σ', r, ⟨hP', -⟩, -, F⟩ := forUp_append (B := B) (i := j) (e := e)
    (body := push1 dst pv (.get src (.var j))) (N := W.length) (K := 8) (a := dst) (pv := pv) hj
    (fun k => [W.getD k 0]) (fun τ => P τ ∧ True) (fun τ v h => ⟨hPj τ v h.1, trivial⟩)
    (by omega) ⟨hP, trivial⟩ hF (fun τ h => he τ h.1)
    (by
      rintro k hk τ ⟨hτ, -⟩ hτk hFk
      have hl : (l ++ (List.range k).flatMap fun k => [W.getD k 0]).length = l.length + k := by
        rw [List.length_append, length_flatMap_const (m := 1) (fun _ => rfl)]; ring
      have hval : (Expr.get src (.var j)).evalB B τ = some (W.getD k 0) := by
        refine evalB_get (evalB_var_of hτk (by omega)) ?_ ?_
        · rw [hsrc τ hτ k hk]; simp [hk]
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
          exact hW _ (List.getElem_mem hk)
      obtain ⟨τ', r', F', fv, fa, fl, -, -⟩ := push1_run hFk hval
        (by have := hcapP τ hτ; rw [hl]; omega) (by rw [hl]; omega)
      refine ⟨τ', r'.mono (by simp), by rw [fv _ hj, hτk], ⟨hPpush τ τ' hτ fv fa fl, trivial⟩, ?_⟩
      rw [flatMap_range_succ', ← List.append_assoc]; exact F')
  rw [flatMap_getD] at F
  exact ⟨σ', r, hP', F⟩

/-! ### Entries -/

theorem mem_flatMap_range {f : ℕ → List ℕ} {N v : ℕ} (h : v ∈ (List.range N).flatMap f) :
    ∃ k < N, v ∈ f k := by
  simp only [List.mem_flatMap, List.mem_range] at h; exact h

theorem atomsOut_entries {a rm rp c v : ℕ} (h : v ∈ atomsOut a rm rp c) :
    v ≤ a + rm + rp + c + 5 := by
  simp only [atomsOut, List.mem_append] at h
  rcases h with ((h | h) | h) | h
  · obtain ⟨i, hi, h⟩ := mem_flatMap_range h; obtain ⟨j, hj, h⟩ := mem_flatMap_range h
    simp at h; omega
  · obtain ⟨i, hi, h⟩ := mem_flatMap_range h; simp at h; omega
  · obtain ⟨r, hr, h⟩ := mem_flatMap_range h; obtain ⟨i, hi, h⟩ := mem_flatMap_range h
    obtain ⟨j, hj, h⟩ := mem_flatMap_range h; simp at h; omega
  · obtain ⟨r, hr, h⟩ := mem_flatMap_range h; obtain ⟨i, hi, h⟩ := mem_flatMap_range h
    simp at h; omega

theorem sum_le_alen {a rm rp : ℕ} (ha : 1 ≤ a) : a + rm + rp ≤ alen a rm rp := by
  simp only [alen]; nlinarith [Nat.mul_le_mul ha ha]

theorem lvlWord_entries (K q ℓ c : ℕ) (hℓ : 1 ≤ ℓ) :
    ∀ d, d ≤ q → ∀ v ∈ lvlWord K q ℓ c d, v ≤ lvlLen K q ℓ d + c + 5 := by
  intro d hd
  have hrm := rmD_le K q ℓ d hd hℓ
  have hrp := rpD_le K q ℓ d hd hℓ
  have hal := alen_le K q ℓ d
  have ha : ℓ + q - d ≤ alen (ℓ + q - d) (rmD K d) (rpD K d) := by
    simp only [alen]; nlinarith
  have hcnt : atomsCnt (ℓ + q - d) (rmD K d) (rpD K d) ≤ alen (ℓ + q - d) (rmD K d) (rpD K d) := by
    simp only [atomsCnt, alen]; nlinarith
  induction d with
  | zero =>
      intro v hv
      simp only [lvlWord, List.mem_cons] at hv
      rcases hv with rfl | hv
      · simp only [Nat.sub_zero] at hcnt hal; omega
      · have := atomsOut_entries hv
        have := sum_le_alen (a := ℓ + q) (rm := rmD K 0) (rp := rpD K 0) (by omega)
        simp only [Nat.sub_zero] at *; omega
  | succ d ih =>
      intro v hv
      have ih' := ih (by omega) (rmD_le K q ℓ d (by omega) hℓ) (rpD_le K q ℓ d (by omega) hℓ)
        (alen_le K q ℓ d) (by simp only [alen]; nlinarith) (by simp only [atomsCnt, alen]; nlinarith)
      have hlen := length_lvlWord K q ℓ c d
      have hmono : lvlLen K q ℓ d + 1 ≤ lvlLen K q ℓ (d + 1) := by
        have : 1 ≤ ℓ + q - (d + 1) := by omega
        simp only [lvlLen]; nlinarith
      simp only [lvlWord, levelWord, List.mem_cons, List.mem_append, extsOut] at hv
      have hs := sum_le_alen (a := ℓ + q - (d + 1)) (rm := rmD K (d + 1)) (rp := rpD K (d + 1))
        (by omega)
      rcases hv with (rfl | hv) | (rfl | hv)
      · omega
      · have := atomsOut_entries hv; omega
      · omega
      · obtain ⟨i, hi, hv⟩ := mem_flatMap_range hv
        simp only [List.mem_cons] at hv
        rcases hv with rfl | rfl | hv
        · rw [hlen]; omega
        · omega
        · have := ih' v hv; omega

/-! ### The context -/

structure BCtx (K q ℓ c cap : ℕ) (τ : Env) : Prop where
  hK : τ.vars "iwK" = K
  hq : τ.vars "iwq" = q
  hl : τ.vars "iwl" = ℓ
  hc : τ.vars "iwc" = c
  lta : (τ.arrs "ta").length = cap
  ltb : (τ.arrs "tb").length = cap

theorem BCtx.frame {K q ℓ c cap : ℕ} {τ τ' : Env} (h : BCtx K q ℓ c cap τ)
    (hv : ∀ y ∈ ["iwK", "iwq", "iwl", "iwc"], τ'.vars y = τ.vars y)
    (hta : (τ'.arrs "ta").length = (τ.arrs "ta").length)
    (htb : (τ'.arrs "tb").length = (τ.arrs "tb").length) : BCtx K q ℓ c cap τ' :=
  ⟨by rw [hv _ (by simp), h.hK], by rw [hv _ (by simp), h.hq], by rw [hv _ (by simp), h.hl],
    by rw [hv _ (by simp), h.hc], by rw [hta, h.lta], by rw [htb, h.ltb]⟩

theorem BCtx.setVar {K q ℓ c cap : ℕ} {τ : Env} (h : BCtx K q ℓ c cap τ) {y : String}
    (h1 : y ≠ "iwK") (h2 : y ≠ "iwq") (h3 : y ≠ "iwl") (h4 : y ≠ "iwc") (v : ℕ) :
    BCtx K q ℓ c cap (τ.setVar y v) :=
  ⟨by simp [Ne.symm h1, h.hK], by simp [Ne.symm h2, h.hq], by simp [Ne.symm h3, h.hl],
    by simp [Ne.symm h4, h.hc], by simp [h.lta], by simp [h.ltb]⟩

/-- The context survives an append to `tb` or to `ta`. -/
theorem BCtx.push {K q ℓ c cap : ℕ} {τ τ' : Env} (h : BCtx K q ℓ c cap τ) {pv dst : String}
    (h1 : pv ≠ "iwK") (h2 : pv ≠ "iwq") (h3 : pv ≠ "iwl") (h4 : pv ≠ "iwc")
    (hv : ∀ y, y ≠ pv → τ'.vars y = τ.vars y) (ha : ∀ b, b ≠ dst → τ'.arrs b = τ.arrs b)
    (hl : (τ'.arrs dst).length = (τ.arrs dst).length) : BCtx K q ℓ c cap τ' := by
  refine ⟨by rw [hv _ (Ne.symm h1), h.hK], by rw [hv _ (Ne.symm h2), h.hq],
    by rw [hv _ (Ne.symm h3), h.hl], by rw [hv _ (Ne.symm h4), h.hc], ?_, ?_⟩
  · by_cases hd : dst = "ta"
    · subst hd; rw [hl, h.lta]
    · rw [ha _ (Ne.symm hd), h.lta]
  · by_cases hd : dst = "tb"
    · subst hd; rw [hl, h.ltb]
    · rw [ha _ (Ne.symm hd), h.ltb]

/-! ### The runs -/

/-- A power loop: `x := 9 ^ E`. -/
theorem pow9_run {B : ℕ} {x i : String} (hxi : x ≠ i) {e : Expr} {E : ℕ} {σ : Env}
    (P : Env → Prop) (hPi : ∀ τ v, P τ → P (τ.setVar i v)) (hPx : ∀ τ v, P τ → P (τ.setVar x v))
    (he : ∀ τ, P τ → e.evalB B τ = some E) (hE : 9 ^ E < B) (h9B : 9 < B) (hP : P σ) :
    ∃ σ', Run B (forUp i e (.assign x (.mul (.var x) (.lit 9)))) (σ.setVar x 1) σ'
      (E * (5 + e.size + 7) + e.size + 5) ∧ P σ' ∧ σ'.vars x = 9 ^ E := by
  have hpw : ∀ k ≤ E, 9 ^ k ≤ 9 ^ E := fun k hk => Nat.pow_le_pow_right (by norm_num) hk
  obtain ⟨σ', r, ⟨h1, h2⟩, -⟩ := forUp_run (B := B) (i := i) (e := e)
    (body := .assign x (.mul (.var x) (.lit 9))) (N := E) (K := 5)
    (fun k τ => P τ ∧ τ.vars x = 9 ^ k)
    (by have := lt_nine_pow E; omega) (fun k _ τ h _ => he τ h.1)
    ⟨hPi _ 0 (hPx σ 1 hP), by simp [hxi]⟩
    (by
      rintro k hk τ ⟨hτ, hx⟩ hik
      have h9 : 9 ^ k * 9 = 9 ^ (k + 1) := by rw [pow_succ]
      have hlt : 9 ^ (k + 1) < B := lt_of_le_of_lt (hpw (k + 1) hk) hE
      refine ⟨τ.setVar x (9 ^ (k + 1)), (Run.assign ?_).mono (by simp), by simp [Ne.symm hxi, hik],
        hPi _ _ (hPx _ _ hτ), by simp [hxi]⟩
      rw [← h9]
      exact evalB_bin (evalB_var_of hx (by have := hpw k (by omega); omega)) (evalB_lit (by omega))
        (by rw [Bop.apply_mul, h9]; exact hlt))
  exact ⟨σ', r, h1, h2⟩

end Lax185574Proofs.MC
