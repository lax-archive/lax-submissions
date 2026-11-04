import Lax185574Proofs.Chain.Ram.WTree4

/-!
The greedy procedure of the Welzl ordering as a program (`wtCom`).

The command computes `welzlTree G` for a graph on `Fin n` given by its
adjacency matrix `adj`. It sets the scalar `D` to `2n + 2`, the number
of bits of every value `ξ(u,v)`. Then it makes all vertices active, sets
all weight exponents in `wc` to `0`, and computes all values `ξ(u,v)`
with weights one, as `n` passes of the update for one vertex. Finally it
runs the greedy steps while at least two vertices are active. Each step
scans for the first candidate pair of minimum value, records it in `su`
and `sv` at position `ns`, deactivates its first vertex, and doubles the
weights of the vertices crossing it.

The result is the final active set in `act`, and the steps in order of
time in `su` and `sv`, `ns` of them (`wtCom_run`). The arrays `xb` and
`xt` of the values must be zero at the start, with room for the `n * n`
numbers of `2n + 2` bits.

The cost is `O(n^3 (K + 1) (K + log₂ n + 2))`, where `K` is the largest
number of steps crossed by one vertex. A step costs `O(n^2 (K + log₂ n))`
for the scan, and `O(n^2 (K + log₂ n))` more for every vertex crossing
it, and there are at most `n K` such crossings over all steps.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram Lax185574Proofs.Chain

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

/-! ### The initialization -/

/-- All vertices active, all exponents `0`. -/
def initFill : Com :=
  forUp "wx" (.var "n") (.seq (.store "act" (.var "wx") (.lit 1)) (.store "wc" (.var "wx") (.lit 0)))

/-- All values with weights one. -/
def initXi : Com := forUp "wx" (.var "n") updX

/-- The initialization. -/
def initCom : Com :=
  .seq (.assign "D" (.add (.mul (.lit 2) (.var "n")) (.lit 2)))
    (.seq initFill (.seq initXi (.seq (.assign "ns" (.lit 0)) (.assign "wcnt" (.var "n")))))

/-- The greedy procedure of the Welzl ordering. -/
def wtCom : Com := .seq initCom mainLoop

theorem initFill_run {B : ℕ} {σ : Env} (hB : WB n B) (hn : σ.vars "n" = n)
    (hact : (σ.arrs "act").length = n) (hwc : (σ.arrs "wc").length = n) :
    ∃ σ', Run B initFill σ σ' (n * 14 + 6) ∧ Vec σ' "act" n (fun _ => 1) ∧
      Vec σ' "wc" n (fun _ => 0) ∧ Fr ["wx"] ["act", "wc"] σ σ' := by
  have hs := hB.small
  let I : ℕ → Env → Prop := fun k τ => Fr ["wx"] ["act", "wc"] σ τ ∧
    (τ.arrs "act").length = n ∧ (τ.arrs "wc").length = n ∧
    ∀ x < k, (τ.arrs "act")[x]? = some 1 ∧ (τ.arrs "wc")[x]? = some 0
  have hnτ : ∀ τ, Fr ["wx"] ["act", "wc"] σ τ → τ.vars "n" = n := fun τ hF => by
    rw [hF.vars _ (by decide), hn]
  obtain ⟨σ', hr, ⟨hF', ha', hw', hv'⟩, -⟩ :=
    forUp_run (B := B) (i := "wx") (e := .var "n")
      (body := .seq (.store "act" (.var "wx") (.lit 1)) (.store "wc" (.var "wx") (.lit 0)))
      (N := n) (K := 6) I (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [hnτ τ hI.1]; omega), hnτ τ hI.1])
      (σ := σ) ⟨(Fr.refl _ _ σ).setVar (by simp) 0, by simp [hact], by simp [hwc],
        fun x hx => by omega⟩
      (by
        rintro k hk τ ⟨hFτ, haτ, hwτ, hvτ⟩ hwx
        have hr := Run.seq
          (Run.store (B := B) (σ := τ) (a := "act") (i := .var "wx") (e := .lit 1) (idx := k)
            (v := 1) (by rw [evalB_var (by omega), hwx]) (evalB_lit (by omega)) (by omega))
          (Run.store (B := B) (σ := τ.setArr "act" k 1) (a := "wc") (i := .var "wx")
            (e := .lit 0) (idx := k) (v := 0) (by rw [evalB_var (by simp [hwx]; omega)]; simp [hwx])
            (evalB_lit (by omega)) (by simp [hwτ]; omega))
        refine ⟨_, hr.mono (by simp), by simp [hwx], ?_⟩
        refine ⟨(((hFτ.setArr (by simp) _ _).setArr (by simp) _ _).setVar (by simp) _),
          by simp [haτ], by simp [hwτ], fun x hx => ?_⟩
        simp only [arrs_setVar, arrs_setArr, if_true]
        simp only [show ("act" : String) ≠ "wc" by decide, if_false]
        rw [List.getElem?_set, List.getElem?_set]
        by_cases hxk : k = x
        · subst hxk; simp [haτ, hwτ, hk]
        · rw [if_neg hxk, if_neg hxk]; exact hvτ x (by omega))
  exact ⟨σ', hr.mono (by simp), ⟨ha', fun x hx => (hv' x hx).1⟩, ⟨hw', fun x hx => (hv' x hx).2⟩,
    hF'⟩

theorem initXi_run {B : ℕ} {σ : Env} (hB : WB n B) (hC : WCtx n G σ)
    (hwc : Vec σ "wc" n (fun _ => 0)) (hrep : XiRep n (fun _ _ => 0) σ) :
    ∃ σ', Run B initXi σ σ' (n * (uxC n (20 * lgW G + 30) + 8) + 6) ∧
      XiRep n (xiP G (fun _ => 0) n) σ' ∧ Fr xW ["xb", "xt"] σ σ' := by
  have hs := hB.small
  let I : ℕ → Env → Prop := fun k τ => Fr xW ["xb", "xt"] σ τ ∧
    XiRep n (xiP G (fun _ => 0) k) τ
  have hCτ : ∀ τ, Fr xW ["xb", "xt"] σ τ → WCtx n G τ := fun τ hF => hC.fr hF (by decide)
    (by decide) (by decide)
  obtain ⟨σ', hr, ⟨hF', hR'⟩, -⟩ :=
    forUp_run (B := B) (i := "wx") (e := .var "n") (body := updX) (N := n)
      (K := uxC n (20 * lgW G + 30)) I (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [(hCτ τ hI.1).hn]; omega), (hCτ τ hI.1).hn])
      (σ := σ) ⟨(Fr.refl _ _ σ).setVar (by simp [xW]) 0,
        XiRep.mk' hrep rfl rfl fun u _ v _ => by simp [xiP_zero]⟩
      (by
        rintro k hk τ ⟨hFτ, hRτ⟩ hwx
        have hle : ∀ u v, xiP G (fun _ => 0) (k + 1) u v ≤ n * 2 ^ Kw G := fun u v =>
          (xiP_le (K := 0) (fun _ _ => le_rfl) u v).trans (by
            have := Nat.one_le_two_pow (n := Kw G)
            simp only [pow_zero, mul_one]; nlinarith)
        obtain ⟨τ', hr', hR', hF'⟩ := updX_run (B := B) (G := G) (x := k) (j := 0)
          (P := 20 * lgW G + 30) hB (hCτ τ hFτ) hwx hk
          (by rw [hFτ.arrs _ (by decide), hwc.get k hk]) (by omega) hRτ
          (fun u _ v _ h => by
            have := xiP_succ (G := G) (fun _ => 0) k u v
            rw [ind_eq_one.2 h] at this
            simp only [pow_zero, mul_one] at this ⊢
            rw [← this]
            exact (hle u v).trans_lt (mul_two_pow_lt Kw_le))
          (fun u _ v _ h => by
            have := xiP_succ (G := G) (fun _ => 0) k u v
            rw [ind_eq_one.2 h] at this
            simp only [pow_zero, mul_one] at this ⊢
            rw [← this]
            have := log_le_of_le (hle u v)
            simp only [lgW]; omega)
        refine ⟨τ', hr', by rw [hF'.vars _ (by decide), hwx], ?_, ?_⟩
        · exact (hFτ.trans (hF'.mono (by simp [xW]) (by simp))).setVar (by simp [xW]) _
        · exact XiRep.mk' hR' rfl rfl fun u _ v _ => by
            rw [xiP_succ])
  exact ⟨σ', hr.mono (by simp), hR', hF'⟩

/-- **The initialization.** It establishes the invariant of the main
loop for the state before the first step. -/
theorem initCom_run {B : ℕ} {σ : Env} (hB : WB n B) (hn : σ.vars "n" = n)
    (hadj : Mat σ "adj" n (fun u v => ind (gA G u v)))
    (hact : (σ.arrs "act").length = n) (hwc : (σ.arrs "wc").length = n)
    (hsu : (σ.arrs "su").length = n) (hsv : (σ.arrs "sv").length = n)
    (hxb : n * n * (2 * n + 2) ≤ (σ.arrs "xb").length) (hxt : n * n ≤ (σ.arrs "xt").length)
    (hxb0 : ∀ i < n * n * (2 * n + 2), (σ.arrs "xb")[i]? = some 0)
    (hxt0 : ∀ i < n * n, (σ.arrs "xt")[i]? = some 0) :
    ∃ σ', Run B initCom σ σ' (n * 14 + n * (uxC n (20 * lgW G + 30) + 8) + 22) ∧
      MInv G σ σ' ∧ σ'.vars "ns" = 0 := by
  have hs := hB.small
  have hD := Run.assign (B := B) (σ := σ) (x := "D") (e := .add (.mul (.lit 2) (.var "n")) (.lit 2))
    (v := 2 * n + 2) (by
      have := evalB_bin (op := .add) (evalB_bin (op := .mul) (evalB_lit (n := 2) (B := B) (σ := σ)
        (by omega)) (evalB_var (x := "n") (by rw [hn]; omega)) (by simp [hn]; omega))
        (evalB_lit (n := 2) (by omega)) (by simp [hn]; omega)
      simpa [hn] using this)
  let σ0 := σ.setVar "D" (2 * n + 2)
  obtain ⟨σ1, hr1, hA1, hW1, hF1⟩ := initFill_run (B := B) (σ := σ0) hB (by simp [σ0, hn])
    (by simpa [σ0] using hact) (by simpa [σ0] using hwc)
  have hC1 : WCtx n G σ1 := ⟨by rw [hF1.vars _ (by decide)]; simp [σ0, hn],
    by rw [hF1.vars _ (by decide)]; simp [σ0], hadj.of_eq (by rw [hF1.arrs _ (by decide)]; rfl)⟩
  have hxb1 : σ1.arrs "xb" = σ.arrs "xb" := by rw [hF1.arrs _ (by decide)]; rfl
  have hxt1 : σ1.arrs "xt" = σ.arrs "xt" := by rw [hF1.arrs _ (by decide)]; rfl
  have hz : XiRep n (fun _ _ => 0) σ1 := fun u hu v hv => by
    have ht := rm_lt hu hv
    have h1 : (u * n + v) * (2 * n + 2) + (2 * n + 2) ≤ n * n * (2 * n + 2) := by
      have := Nat.mul_le_mul_right (2 * n + 2) (show u * n + v + 1 ≤ n * n by omega)
      rw [Nat.add_mul, one_mul] at this; exact this
    refine bigRep_zero (by rw [hxb1]; omega) (by rw [hxt1]; omega) (fun k hk => ?_)
      (by rw [hxt1]; exact hxt0 _ ht)
    rw [hxb1]; exact hxb0 _ (by omega)
  obtain ⟨σ2, hr2, hR2, hF2⟩ := initXi_run (G := G) (B := B) hB hC1 hW1 hz
  have hC2 : WCtx n G σ2 := hC1.fr hF2 (by decide) (by decide) (by decide)
  let σ3 := (σ2.setVar "ns" 0).setVar "wcnt" n
  have hr3 : Run B (.seq (.assign "ns" (.lit 0)) (.assign "wcnt" (.var "n"))) σ2 σ3 4 :=
    (Run.seq (Run.assign (v := 0) (by simp; omega))
      (Run.assign (v := n) (by simp [hC2.hn]; omega))).mono (by simp)
  refine ⟨σ3, (Run.seq hD (Run.seq hr1 (Run.seq hr2 hr3))).mono (by simp; omega), ?_, by simp [σ3]⟩
  have hns : σ3.vars "ns" = 0 := by simp [σ3]
  have hF3 : Fr ["ns", "wcnt"] [] σ2 σ3 := ((Fr.refl _ _ σ2).setVar (by simp) _).setVar (by simp) _
  have hFall : Fr allW allA σ σ3 :=
    (((((Fr.refl allW allA σ).setVar (by simp [allW]) _).trans
      (hF1.mono (by simp [allW]) (by simp [allA]))).trans
      (hF2.mono (by simp [xW, allW]) (by simp [allA]))).trans (hF3.mono (by simp [allW]) (by simp)))
  have ha2 : ∀ a, a ∉ ["xb", "xt"] → σ3.arrs a = σ1.arrs a := fun a ha => by
    simp only [σ3, arrs_setVar]; exact hF2.arrs a ha
  have hst : wSt G 0 = ⟨univ, fun _ => 1, []⟩ := wSt_zero
  refine ⟨hC2.fr hF3 (by decide) (by decide) (by decide), by simp [σ3], ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, hFall⟩
  · simp [σ3, hst]
  · rw [hns]; simp [hst]
  · rw [hns]
    refine (hA1.of_eq (ha2 _ (by decide))).congr fun u hu => ?_
    rw [hst]; symm; exact ind_eq_one.2 ⟨hu, mem_univ _⟩
  · rw [hns]
    exact (hW1.of_eq (ha2 _ (by decide))).congr fun x _ => (wExp_zero x).symm
  · rw [ha2 _ (by decide), hF1.arrs _ (by decide)]; simpa [σ0] using hsu
  · rw [ha2 _ (by decide), hF1.arrs _ (by decide)]; simpa [σ0] using hsv
  · rw [hns]; intro j hj; omega
  · rw [hns]; intro j hj; omega
  · rw [hns]
    exact XiRep.mk' hR2 rfl rfl fun u _ v _ => xiP_congr (fun x _ => (wExp_zero x).symm) u v

/-! ### The cost -/

theorem wt_cost (n L R S : ℕ) (hS : S ≤ n * R) :
    n * 14 + n * (uxC n (20 * L + 30) + 8) + 22 +
      (n * (scanC n (40 * L + 70) + n * 45 + 23 + 4) + S * (uxC n (20 * L + 30) + 5) + 4) ≤
    300 * (n + 1) ^ 3 * (R + 1) * (L + 2) := by
  let X := (n + 1) ^ 2 * (L + 2)
  have hX : (n + 1) ^ 2 * (L + 2) = X := rfl
  have hnL : 0 ≤ n * n * L := Nat.zero_le _
  have hu : uxC n (20 * L + 30) + 8 ≤ 62 * X := by
    simp only [uxC, X]; nlinarith [Nat.zero_le (n * L), Nat.zero_le (n * n)]
  have hsc : scanC n (40 * L + 70) + n * 45 + 23 + 4 ≤ 158 * X := by
    simp only [scanC, X]; nlinarith [Nat.zero_le (n * L), Nat.zero_le (n * n)]
  have h1 : n * 14 + 22 + 4 ≤ 40 * X := by
    simp only [X]; nlinarith [Nat.zero_le (n * L), Nat.zero_le (n * n)]
  have hY : (n + 1) ^ 3 * (L + 2) = (n + 1) * X := by simp only [X]; ring
  have e1 : n * (uxC n (20 * L + 30) + 8) ≤ (n + 1) * (62 * X) :=
    Nat.mul_le_mul (by omega) hu
  have e2 : n * (scanC n (40 * L + 70) + n * 45 + 23 + 4) ≤ (n + 1) * (158 * X) :=
    Nat.mul_le_mul (by omega) hsc
  have e3 : S * (uxC n (20 * L + 30) + 5) ≤ ((n + 1) * R) * (62 * X) :=
    Nat.mul_le_mul (hS.trans (Nat.mul_le_mul_right _ (by omega))) (by omega)
  have e4 : X ≤ (n + 1) * X := Nat.le_mul_of_pos_left _ (by omega)
  have : 300 * (n + 1) ^ 3 * (R + 1) * (L + 2) = 300 * (R * ((n + 1) * X)) + 300 * ((n + 1) * X) := by
    rw [show 300 * (n + 1) ^ 3 * (R + 1) * (L + 2) = 300 * (R + 1) * ((n + 1) ^ 3 * (L + 2)) by ring,
      hY]
    ring
  rw [this]
  have e5 : (n + 1) * R * (62 * X) = 62 * (R * ((n + 1) * X)) := by ring
  have e6 : (n + 1) * (62 * X) = 62 * ((n + 1) * X) := by ring
  have e7 : (n + 1) * (158 * X) = 158 * ((n + 1) * X) := by ring
  omega

/-! ### The whole program -/

/-- **The greedy procedure of the Welzl ordering.** Started with the
adjacency matrix of `G` in `adj`, arrays `act`, `wc`, `su`, `sv` of
length `n` and zero arrays `xb`, `xt` with room for `n * n` numbers of
`2n + 2` bits, the command `wtCom` leaves the final active set of
`welzlTree G` in `act` and its steps in order of time in `su` and `sv`,
`ns` of them. It sets `D` to `2n + 2`. The cost is
`O(n^3 (K + 1) (K + log₂ n + 2))`, where `K` is the largest number of
steps crossed by one vertex. -/
theorem wtCom_run {B n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hB : (n + 2) ^ 3 * 8 < B) {σ : Env}
    (hn : σ.vars "n" = n) (hadj : Mat σ "adj" n (fun u v => ind (gA G u v)))
    (hact : (σ.arrs "act").length = n) (hwc : (σ.arrs "wc").length = n)
    (hsu : (σ.arrs "su").length = n) (hsv : (σ.arrs "sv").length = n)
    (hxb : n * n * (2 * n + 2) ≤ (σ.arrs "xb").length) (hxt : n * n ≤ (σ.arrs "xt").length)
    (hxb0 : ∀ i < n * n * (2 * n + 2), (σ.arrs "xb")[i]? = some 0)
    (hxt0 : ∀ i < n * n, (σ.arrs "xt")[i]? = some 0) :
    ∃ σ' K, Run B wtCom σ σ' K ∧
      Vec σ' "act" n (fun u => ind (inBN (welzlTree G).active u)) ∧
      σ'.vars "ns" = (welzlTree G).steps.length ∧
      (∀ j (h : j < (welzlTree G).steps.length), (σ'.arrs "su")[j]? =
        some (((welzlTree G).steps.map fun p => ((p.1 : ℕ), (p.2 : ℕ)))[
          (welzlTree G).steps.length - 1 - j]'(by simp; omega)).1) ∧
      (∀ j (h : j < (welzlTree G).steps.length), (σ'.arrs "sv")[j]? =
        some (((welzlTree G).steps.map fun p => ((p.1 : ℕ), (p.2 : ℕ)))[
          (welzlTree G).steps.length - 1 - j]'(by simp; omega)).2) ∧
      (∀ x, x ∉ ["D", "wx", "wa", "wb", "bt", "bj", "bk", "wbf", "wbu", "wbv", "ca1", "ca2",
        "blt", "wu", "wv", "ns", "wcnt"] → σ'.vars x = σ.vars x) ∧
      (∀ a, a ∉ ["act", "wc", "su", "sv", "xb", "xt"] → σ'.arrs a = σ.arrs a) ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out ∧
      K ≤ 300 * (n + 1) ^ 3 * (Finset.univ.sup (fun x => stepCross G x (welzlTree G).steps) + 1) *
        (Finset.univ.sup (fun x => stepCross G x (welzlTree G).steps) + Nat.log 2 n + 2) := by
  have hB' : WB n B := hB
  obtain ⟨σ1, hr1, hI1, h01⟩ := initCom_run (G := G) hB' hn hadj hact hwc hsu hsv hxb hxt hxb0 hxt0
  obtain ⟨σ', K2, hr2, hI', hc', hK2⟩ := mainLoop_run hB' hI1 h01
  obtain ⟨k, hk⟩ : ∃ k, σ'.vars "ns" = k := ⟨_, rfl⟩
  have hsum := hI'.sum
  have hcnt := hI'.cnt
  rw [hk] at hsum hcnt
  have hT : welzlTree G = wSt G k := by
    have e : wSt G n = welzlRun G (n - k) (wSt G k) := by
      unfold wSt; rw [← welzlRun_add]; congr 1; omega
    rw [welzlTree_eq, e]
    exact welzlRun_of_card _ (by omega)
  have hlen := hI'.len
  rw [hk, ← hT] at hlen
  refine ⟨σ', _, Run.seq hr1 hr2, ?_, by rw [hk, hlen], ?_, ?_, hI'.fr.vars, hI'.fr.arrs,
    hI'.fr.inp, hI'.fr.out, ?_⟩
  · have := hI'.act; rwa [hk, ← hT] at this
  · intro j hj
    have := hI'.su j (by omega)
    rw [hk, ← hT] at this
    rw [this, List.getElem?_map, List.getElem?_reverse hj, List.getElem?_eq_getElem (by omega)]
    simp
  · intro j hj
    have := hI'.sv j (by omega)
    rw [hk, ← hT] at this
    rw [this, List.getElem?_map, List.getElem?_reverse hj, List.getElem?_eq_getElem (by omega)]
    simp
  · have h := wt_cost n (lgW G) (Kw G) (sExp G n) sExp_le
    simp only [cSt, cUp] at hK2
    simp only [lgW, Kw] at h hK2 ⊢
    omega

end Lax185574Proofs.Chain.Ram
