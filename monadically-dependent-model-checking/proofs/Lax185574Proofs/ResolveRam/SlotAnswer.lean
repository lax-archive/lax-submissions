import Lax185574Proofs.ResolveRam.GlueSpec

/-!
The answers of the five slots to a call.

`cBig k₀ q₀` bounds the constants of all calls at the top rank
`(k₀, q₀)`. A real query of a call is an instance of its callee
(`callInst`), so every halting run of the slot program at a word length
at which the query is admissible for `cBig` gives the answer of the call
(`real_*`). `slots_answer`: under the guard of the call, with `X ≥ cBig`
or with room for a power of `cBig`, and with room for the fixed queries,
the five halting runs of the slots give `rY c`.
-/

namespace Lax185574Proofs.ResolveRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.FarTrees Lax185574.ResolveLift
open Lax185574.PartialGraphEncoding Lax185574Proofs.TreeAlgo Lax185574Proofs.Words
open Lax3.DistFO (rhoMinus rhoPlus)
open Lax185574.DistanceMatrix

/-- The constants of the calls at the top rank `(k₀, q₀)`. -/
noncomputable def cBig (k₀ q₀ : ℕ) : ℕ :=
  (∑ d ∈ Finset.range q₀, (cSh (k₀ + d) (q₀ - d - 1) + cFt (k₀ + d) (q₀ - d - 1) +
    cCo (k₀ + d + 1) (q₀ - d - 1))) + cCa + cSt k₀ q₀ + 1

theorem le_cBig {k₀ q₀ d : ℕ} (hd : d < q₀) :
    cSh (k₀ + d) (q₀ - d - 1) ≤ cBig k₀ q₀ ∧ cFt (k₀ + d) (q₀ - d - 1) ≤ cBig k₀ q₀ ∧
      cCo (k₀ + d + 1) (q₀ - d - 1) ≤ cBig k₀ q₀ := by
  have h := Finset.single_le_sum (f := fun d => cSh (k₀ + d) (q₀ - d - 1) + cFt (k₀ + d) (q₀ - d - 1) +
    cCo (k₀ + d + 1) (q₀ - d - 1)) (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 hd)
  unfold cBig
  omega

theorem one_le_cBig (k₀ q₀ : ℕ) : 1 ≤ cBig k₀ q₀ := by unfold cBig; omega

variable {n : ℕ} (G : PartialGraph (Fin n)) {k₀ q₀ : ℕ}

theorem real_shift {τ : TypeTree} (hc : CallInst G k₀ q₀ (.shift τ)) {v : ℕ}
    (ha : WordAdmissible eSh (cBig k₀ q₀) v (toWord τ)) {y : List ℕ} {t : ℕ}
    (hr : RunsTo v pSh (toWord τ) y t) : y = toWord (shOf G τ) := by
  obtain ⟨d, hd, ℓ, u, h1, hk, rfl⟩ := hc
  have hs := (soundOn_of (hSh' (k₀ + d) (q₀ - d - 1) n G ℓ u h1 hk)).mono (le_cBig hd).1
  rw [hs v ha y t hr, shOf_tree G u h1 hk]

theorem toWord_faOf {k q ℓ : ℕ} (u : Fin ℓ → Fin n) (h1 : 1 ≤ ℓ) (hk : ℓ ≤ k) :
    toWord ((faOf G (tree G k (q + 1) u)).map toWord) = toWord (ftree G k (q + 1) u) := by
  have := Lax185574Proofs.EncodingInjectivity.prefixFree_typeTree
  show toWord ((elems (farMapOf G k q ℓ (node G k (q + 1) u) ∅)).map toWord) = _
  have e : farMapOf G k q ℓ (node G k (q + 1) u) ∅ = ftree G k (q + 1) u :=
    farSpec_farMapOf G k q ℓ u h1 hk
  rw [map_elems, e]
  rfl

theorem real_ftree {τ : TypeTree} (hc : CallInst G k₀ q₀ (.ftree τ)) {v : ℕ}
    (ha : WordAdmissible eFt (cBig k₀ q₀) v (toWord (τ, stpCut (τ.k + 1) (stp G k₀ q₀))))
    {y : List ℕ} {t : ℕ} (hr : RunsTo v pFt (toWord (τ, stpCut (τ.k + 1) (stp G k₀ q₀))) y t) :
    y = toWord ((faOf G τ).map toWord) := by
  obtain ⟨d, hd, ℓ, u, h1, hk, rfl⟩ := hc
  have hst : stpCut ((tree G (k₀ + d) (q₀ - d - 1 + 1) u).k + 1) (stp G k₀ q₀) =
      stp G (k₀ + d) (q₀ - d - 1 + 1) := stpCut_stp' G (by simp [tree]) (by simp [tree]; omega)
  rw [hst] at ha hr
  have hs := (soundOn_of (hFt' (k₀ + d) (q₀ - d - 1) n G ℓ u h1 hk)).mono (le_cBig hd).2.1
  rw [hs v ha y t hr, toWord_faOf G u h1 hk]

theorem real_compose {σ ν : TypeTree} (hc : CallInst G k₀ q₀ (.compose σ ν)) {v : ℕ}
    (ha : WordAdmissible eCo (cBig k₀ q₀) v (toWord (σ, ν))) {y : List ℕ} {t : ℕ}
    (hr : RunsTo v pCo (toWord (σ, ν)) y t) : y = toWord (coOf G σ ν) := by
  obtain ⟨d, hd, ℓ, u, b, h1, hk, hb, rfl, rfl⟩ := hc
  have hs := (soundOn_of (hCo' (k₀ + d + 1) (q₀ - d - 1) n G ℓ 1 u ![b] h1 le_rfl (by omega)
    (fun i j => by rw [Fin.fin_one_eq_zero j]; exact hb i))).mono (le_cBig hd).2.2
  rw [hs v ha y t hr, coOf_tree G u b h1 hk hb, Fin.append_right_eq_snoc]
  rfl

theorem real_canon (ws : List (List ℕ)) {v : ℕ} (ha : WordAdmissible eCa (cBig k₀ q₀) v (toWord ws))
    {y : List ℕ} {t : ℕ} (hr : RunsTo v pCa (toWord ws) y t) : y = canonW ws := by
  obtain ⟨h1, h2⟩ := canonW_raw ws
  have hs := (soundOn_of (hCa RawW (ws.map RawW.mk))).mono (show cCa ≤ cBig k₀ q₀ by unfold cBig; omega)
  rw [h2] at hs
  rw [hs v ha y t hr, h1]

theorem real_stp (hk : 1 ≤ k₀) (hn : 1 ≤ n) {v : ℕ}
    (ha : WordAdmissible eSt (cBig k₀ q₀) v (toWord (G, k₀, q₀, distMatrix G, family G k₀ q₀))) {y : List ℕ}
    {t : ℕ} (hr : RunsTo v pSt (toWord (G, k₀, q₀, distMatrix G, family G k₀ q₀)) y t) :
    y = toWord (stp G k₀ q₀) :=
  (soundOn_of (hSt' k₀ q₀ n G hk hn)).mono (show cSt k₀ q₀ ≤ cBig k₀ q₀ by unfold cBig; omega)
    v ha y t hr

/-- The sum of the literal exponents. -/
noncomputable def eSum : ℕ := eSh + eFt + eCo + eCa + eSt

theorem eOf_le (c : RCall) : eOf eSh eFt eCo eCa eSt c ≤ eSum := by
  cases c <;> simp [eOf, eSum] <;> omega

/-- The condition on `cBig` under which the guard gives admissibility. -/
def BigOK (k₀ q₀ X w : ℕ) : Prop := cBig k₀ q₀ ≤ X ∨ cBig k₀ q₀ ^ (eSum + 1) ≤ 2 ^ w

theorem adm_real {c : RCall} {X v sQ w : ℕ}
    (hg : RGuard G k₀ q₀ eSh eFt eCo eCa eSt X v sQ c) (hw : v - sQ ≤ w) (hB : BigOK k₀ q₀ X w) :
    WordAdmissible (eOf eSh eFt eCo eCa eSt c) (cBig k₀ q₀) w (realQ G k₀ q₀ c) := by
  refine adm_of_guardX (X := X) (le_trans hg (Nat.pow_le_pow_right (by norm_num) hw)) ?_
  rcases hB with h | h
  · exact Or.inl h
  · exact Or.inr (le_trans (Nat.pow_le_pow_right (one_le_cBig k₀ q₀) (by have := eOf_le c; omega)) h)

/-- **The answer of the switch.** -/
theorem slots_answer (hk : 1 ≤ k₀) {P Q : ℕ} {s : Bool} {c : RCall}
    (hc : c ∈ rcalls G P Q s k₀ q₀) {X v sQ : ℕ}
    (hg : RGuard G k₀ q₀ eSh eFt eCo eCa eSt X v sQ c) {wA wB wC wE wF : ℕ}
    (hwA : v - sQ ≤ wA) (hwB : v - sQ ≤ wB) (hwC : v - sQ ≤ wC) (hwE : v - sQ ≤ wE)
    (hwF : v - sQ ≤ wF) (hB : BigOK k₀ q₀ X (v - sQ)) (hfix : fixBig ≤ 2 ^ (v - sQ))
    {yA' yB' yC' yE' yF' : List ℕ} {tA tB tC tE tF : ℕ}
    (hA : RunsTo wA pSh (qA c) yA' tA) (hB' : RunsTo wB pFt (qB G k₀ q₀ c) yB' tB)
    (hC : RunsTo wC pCo (qC c) yC' tC) (hE : RunsTo wE pCa (qE c) yE' tE)
    (hF : RunsTo wF pSt (qF G k₀ q₀ c) yF' tF) :
    yA' ++ yB' ++ yC' ++ yE' ++ yF' = rY G k₀ q₀ c := by
  have hci := callInst G P Q s k₀ q₀ hk c hc
  have hf : ∀ w, v - sQ ≤ w → fixBig ≤ 2 ^ w := fun w hw =>
    le_trans hfix (Nat.pow_le_pow_right (by norm_num) hw)
  have hBw : ∀ w, v - sQ ≤ w → BigOK k₀ q₀ X w := fun w hw => by
    rcases hB with h | h
    · exact Or.inl h
    · exact Or.inr (le_trans h (Nat.pow_le_pow_right (by norm_num) hw))
  cases c with
  | stp =>
    have hn : 1 ≤ n := hci
    have e5 := real_stp G hk hn (adm_real G hg hwF (hBw _ hwF)) hF
    rw [soundA0 (hf _ hwA) hA, soundB0 (hf _ hwB) hB', soundC0 (hf _ hwC) hC,
      soundE0 (hf _ hwE) hE, e5]
    rfl
  | shift τ =>
    have e1 := real_shift G hci (adm_real G hg hwA (hBw _ hwA)) hA
    rw [e1, soundB0 (hf _ hwB) hB', soundC0 (hf _ hwC) hC, soundE0 (hf _ hwE) hE,
      soundF0 (hf _ hwF) hF]
    rfl
  | ftree τ =>
    have e2 := real_ftree G hci (adm_real G hg hwB (hBw _ hwB)) hB'
    rw [soundA0 (hf _ hwA) hA, e2, soundC0 (hf _ hwC) hC, soundE0 (hf _ hwE) hE,
      soundF0 (hf _ hwF) hF]
    rfl
  | compose σ ν =>
    have e3 := real_compose G hci (adm_real G hg hwC (hBw _ hwC)) hC
    rw [soundA0 (hf _ hwA) hA, soundB0 (hf _ hwB) hB', e3, soundE0 (hf _ hwE) hE,
      soundF0 (hf _ hwF) hF]
    rfl
  | canon ws =>
    have e4 := real_canon (k₀ := k₀) (q₀ := q₀) ws (adm_real G hg hwE (hBw _ hwE)) hE
    rw [soundA0 (hf _ hwA) hA, soundB0 (hf _ hwB) hB', soundC0 (hf _ hwC) hC, e4,
      soundF0 (hf _ hwF) hF]
    rfl

end Lax185574Proofs.ResolveRam
