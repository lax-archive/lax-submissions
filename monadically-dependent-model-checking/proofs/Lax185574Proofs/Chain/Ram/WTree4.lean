import Lax185574Proofs.Chain.Ram.WTree3

/-!
The greedy procedure of the Welzl ordering as a program, fourth part:
one greedy step and the loop of all steps.

The invariant `MInv` says that the environment represents the state
`wSt G k` after `k = ns` greedy steps: the number of active vertices in
`wcnt`, the active vertices in `act`, the weight exponents in `wc`, the
steps in order of time in `su` and `sv`, and all values `ξ(u,v)` as big
numbers. One round of `mainLoop` scans for the pair of the next step,
records it, deactivates its first vertex and doubles the weights of the
vertices crossing it (`stepBody_run`). The loop runs while at least two
vertices are active (`mainLoop_run`). A round costs a scan and a pass over
all vertices, plus an update of all values for every vertex crossing the
step. The latter is paid for by the potential: the total of the weight
exponents still to come.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram Lax185574Proofs.Chain

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

/-! ### The program of one step -/

/-- Record the step `wbu wbv`, deactivate `wbu`. -/
def recStep : Com :=
  .seq (.store "su" (.var "ns") (.var "wbu")) (.seq (.store "sv" (.var "ns") (.var "wbv"))
    (.seq (.assign "ns" (.add (.var "ns") (.lit 1))) (.seq (.store "act" (.var "wbu") (.lit 0))
      (.assign "wcnt" (.sub (.var "wcnt") (.lit 1))))))

/-- One greedy step. -/
def stepBody : Com := .seq scan (.seq recStep xLoop)

/-- All greedy steps. -/
def mainLoop : Com := .while (.lt (.lit 1) (.var "wcnt")) stepBody

/-- The scalars the whole program may change. -/
def allW : List String :=
  ["D", "wx", "wa", "wb", "bt", "bj", "bk", "wbf", "wbu", "wbv", "ca1", "ca2", "blt", "wu", "wv",
    "ns", "wcnt"]

/-- The arrays the whole program may change. -/
def allA : List String := ["act", "wc", "su", "sv", "xb", "xt"]

theorem recStep_run {B k a b c : ℕ} {τ : Env} (hk : τ.vars "ns" = k) (ha : τ.vars "wbu" = a)
    (hb : τ.vars "wbv" = b) (hc : τ.vars "wcnt" = c) (hkB : k + 1 < B) (haB : a < B)
    (hbB : b < B) (hcB : c < B) (hsu : k < (τ.arrs "su").length)
    (hsv : k < (τ.arrs "sv").length) (hact : a < (τ.arrs "act").length) :
    Run B recStep τ (((((τ.setArr "su" k a).setArr "sv" k b).setVar "ns" (k + 1)).setArr
      "act" a 0).setVar "wcnt" (c - 1)) 17 :=
  (Run.seq (Run.store (idx := k) (v := a) (by simp [hk]; omega) (by simp [ha]; omega) hsu)
    (Run.seq (Run.store (idx := k) (v := b) (by simp [hk]; omega) (by simp [hb]; omega)
      (by simpa using hsv))
      (Run.seq (Run.assign (v := k + 1) (by simp [hk]; omega))
        (Run.seq (Run.store (idx := a) (v := 0) (by simp [ha]; omega) (by simp; omega)
          (by simpa using hact))
          (Run.assign (v := c - 1) (by simp [hc]; omega)))))).mono (by simp)

/-! ### The invariant -/

variable (G) in
/-- The environment represents the state after `ns` greedy steps. -/
structure MInv (σ0 τ : Env) : Prop where
  ctx : WCtx n G τ
  sum : τ.vars "wcnt" + τ.vars "ns" = n
  cnt : τ.vars "wcnt" = (wSt G (τ.vars "ns")).active.card
  len : (wSt G (τ.vars "ns")).steps.length = τ.vars "ns"
  act : Vec τ "act" n (fun u => ind (inBN (wSt G (τ.vars "ns")).active u))
  wc : Vec τ "wc" n (wExp G (wSt G (τ.vars "ns")))
  sulen : (τ.arrs "su").length = n
  svlen : (τ.arrs "sv").length = n
  su : ∀ j < τ.vars "ns",
    (τ.arrs "su")[j]? = ((wSt G (τ.vars "ns")).steps.reverse.map fun p => (p.1 : ℕ))[j]?
  sv : ∀ j < τ.vars "ns",
    (τ.arrs "sv")[j]? = ((wSt G (τ.vars "ns")).steps.reverse.map fun p => (p.2 : ℕ))[j]?
  xi : XiRep n (xiP G (wExp G (wSt G (τ.vars "ns"))) n) τ
  fr : Fr allW allA σ0 τ

theorem push_get {l L : List ℕ} {k v : ℕ} (hk : k < l.length) (hL : L.length = k)
    (h : ∀ j < k, l[j]? = L[j]?) : ∀ j < k + 1, (l.set k v)[j]? = (L ++ [v])[j]? := by
  intro j hj
  rw [List.getElem?_set]
  by_cases hjk : k = j
  · subst hjk
    subst hL
    simp [hk]
  · rw [if_neg hjk, h j (by omega), List.getElem?_append_left (by omega)]

theorem inBN_erase {A : Finset (Fin n)} {x : Fin n} {u : ℕ} :
    inBN (A.erase x) u ↔ u ≠ x ∧ inBN A u := by
  constructor
  · rintro ⟨hu, h⟩
    rw [Finset.mem_erase] at h
    exact ⟨fun e => h.1 (Fin.ext e), hu, h.2⟩
  · rintro ⟨hne, hu, h⟩
    exact ⟨hu, Finset.mem_erase.2 ⟨fun e => hne (congrArg Fin.val e), h⟩⟩

/-- The weight exponents after a step. -/
theorem wExp_step {k : ℕ} {p : Fin n × Fin n} {st' : WState (Fin n)}
    (h : st' = ⟨(wSt G k).active.erase p.1,
      fun x => if CrossesPair G x p.1 p.2 then 2 * (wSt G k).w x else (wSt G k).w x,
      p :: (wSt G k).steps⟩) (x : ℕ) :
    wExp G st' x = wExp G (wSt G k) x + ind (crN G x p.1 p.2) := by
  unfold wExp
  split
  · rename_i hx
    rw [h]
    simp only
    rw [stepCross_cons]
    have := ind_crN_fin (G := G) ⟨x, hx⟩ p.1 p.2
    simp only at this
    rw [this]
  · rename_i hx
    have : ¬ crN G x p.1 p.2 := fun h' => hx (crN_lt h').1
    simp [ind, this]

/-! ### One step -/

/-- The bound on the logarithm of all values: `Kw G + log₂ n`. -/
noncomputable def lgW (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ := Kw G + Nat.log 2 n

/-- The cost of an update of all values. -/
noncomputable def cUp (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ :=
  uxC n (20 * lgW G + 30) + 5

/-- The cost of a step without the updates. -/
noncomputable def cSt (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : ℕ :=
  scanC n (40 * lgW G + 70) + n * 45 + 23

/-- The total weight exponent after `k` steps. -/
noncomputable def sExp (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (k : ℕ) : ℕ :=
  ∑ x ∈ range n, wExp G (wSt G k) x

theorem sExp_mono {k : ℕ} (hk : k ≤ n) : sExp G k ≤ sExp G n :=
  sum_le_sum fun x _ => wExp_le_final hk x

theorem sExp_zero : sExp G 0 = 0 := by simp [sExp, wExp_zero]

theorem sExp_le : sExp G n ≤ n * Kw G := by
  have := sum_le_card_nsmul (range n) (fun x => wExp G (wSt G n) x) (Kw G)
    (fun x _ => wExp_final_le x)
  simpa [sExp] using this

/-- **One greedy step.** -/
theorem stepBody_run {B : ℕ} {σ0 τ : Env} (hB : WB n B) (hI : MInv G σ0 τ)
    (h2 : 1 < τ.vars "wcnt") :
    ∃ τ' K, Run B stepBody τ τ' K ∧ MInv G σ0 τ' ∧ τ'.vars "ns" = τ.vars "ns" + 1 ∧
      K + sExp G (τ.vars "ns") * cUp G ≤ cSt G + sExp G (τ.vars "ns" + 1) * cUp G := by
  have hs := hB.small
  obtain ⟨k, hk⟩ : ∃ k, τ.vars "ns" = k := ⟨_, rfl⟩
  have hsum := hI.sum
  have hcnt := hI.cnt
  have hact := hI.act
  have hwc := hI.wc
  have hxi := hI.xi
  have hsu := hI.su
  have hsv := hI.sv
  have hlen := hI.len
  rw [hk] at hsum hcnt hact hwc hxi hsu hsv hlen ⊢
  have hkn : k + 1 < n := by omega
  have hwinv := wSt_inv (G := G) k
  obtain ⟨st, hst⟩ : ∃ st, wSt G k = st := ⟨_, rfl⟩
  rw [hst] at hcnt hact hwc hxi hsu hsv hlen hwinv
  -- the scan
  have hval : ∀ u v, xiP G (wExp G st) n u v ≤ n * 2 ^ Kw G := fun u v =>
    xiP_le (fun x _ => by rw [← hst]; exact wExp_le_Kw (by omega) x) u v
  have hSC : ScanCtx n st.active (fun p => xi G st.w p.1 p.2) τ :=
    ⟨hI.ctx.hn, hI.ctx.hD, hact, fun u hu v hv => by
      simp only
      rw [xi_eq_xiP hwinv.weight hu hv]; exact hxi u hu v hv⟩
  obtain ⟨τ1, hr1, hb1, hF1⟩ := scan_run (B := B) (Q := 40 * lgW G + 70) hB hSC
    (fun u hu v hv => by
      simp only
      rw [xi_eq_xiP hwinv.weight hu hv]
      have := log_le_of_le (hval u v)
      simp only [lgW]; omega)
  cases hp : (candPairs st.active).argmin (fun p => xi G st.w p.1 p.2) with
  | none =>
    exfalso
    have := argmin_candPairs_none hp
    omega
  | some p =>
  rw [hp] at hb1
  obtain ⟨hf1, hu1, hv1⟩ := hb1
  obtain ⟨hvu, hpu, hpv, -⟩ := argmin_candPairs hp
  have hnext : wSt G (k + 1) = ⟨st.active.erase p.1,
      fun x => if CrossesPair G x p.1 p.2 then 2 * st.w x else st.w x, p :: st.steps⟩ := by
    rw [wSt_succ, hst]; unfold welzlStep; rw [hp]
  have hnext' : wSt G (k + 1) = ⟨(wSt G k).active.erase p.1,
      fun x => if CrossesPair G x p.1 p.2 then 2 * (wSt G k).w x else (wSt G k).w x,
      p :: (wSt G k).steps⟩ := by rw [hnext, hst]
  -- recording the step
  have h1v : ∀ y, y ∉ scanW → τ1.vars y = τ.vars y := hF1.vars
  have h1a : ∀ a, τ1.arrs a = τ.arrs a := fun a => hF1.arrs a (by simp)
  have hk1 : τ1.vars "ns" = k := by rw [h1v _ (by decide), hk]
  have hc1 : τ1.vars "wcnt" = st.active.card := by rw [h1v _ (by decide), hcnt]
  have hp1n := p.1.2
  have hp2n := p.2.2
  have hr2 := recStep_run (B := B) (τ := τ1) hk1 hu1 hv1 hc1 (by omega) (by omega) (by omega)
    (by have := Finset.card_le_univ st.active; simp at this; omega)
    (by rw [h1a, hI.sulen]; omega) (by rw [h1a, hI.svlen]; omega)
    (by rw [h1a, hact.len]; exact hp1n)
  let τ2 := ((((τ1.setArr "su" k p.1).setArr "sv" k p.2).setVar "ns" (k + 1)).setArr
      "act" p.1 0).setVar "wcnt" (st.active.card - 1)
  have hF2 : Fr ["ns", "wcnt"] ["su", "sv", "act"] τ1 τ2 :=
    (((((Fr.refl _ _ τ1).setArr (by simp) _ _).setArr (by simp) _ _).setVar
      (by simp) _).setArr (by simp) _ _).setVar (by simp) _
  have hC2 : WCtx n G τ2 := (hI.ctx.fr hF1 (by decide) (by decide) (by decide)).fr hF2
    (by decide) (by decide) (by decide)
  have hwc2 : Vec τ2 "wc" n (wExp G st) := hwc.of_eq (by simp [τ2, h1a])
  have hxi2 : XiRep n (xiP G (wExp G st) n) τ2 := XiRep.mk' hxi (by simp [τ2, h1a])
    (by simp [τ2, h1a]) fun _ _ _ _ => rfl
  -- doubling the weights
  have hexp : ∀ x, wExp G (wSt G (k + 1)) x = wExp G st x + ind (crN G x p.1 p.2) := fun x => by
    rw [wExp_step hnext' x, hst]
  obtain ⟨τ3, hr3, hW3, hR3, hF3⟩ := xLoop_run (B := B) (G := G) (K := Kw G) (p1 := p.1)
    (p2 := p.2) (c0 := wExp G st) hB hC2 Kw_le
    (fun x _ => by rw [← hexp]; exact wExp_le_Kw (by omega) x) (by simp [τ2, hu1])
    (by simp [τ2, hv1]) hp1n hp2n hwc2 hxi2
  have h3v : ∀ y, y ∉ xW → τ3.vars y = τ2.vars y := hF3.vars
  have h3a : ∀ a, a ∉ xA → τ3.arrs a = τ2.arrs a := hF3.arrs
  have hns3 : τ3.vars "ns" = k + 1 := by rw [h3v _ (by decide)]; simp [τ2]
  have hsu3 : τ3.arrs "su" = (τ.arrs "su").set k p.1 := by
    rw [h3a _ (by decide)]; simp [τ2, h1a]
  have hsv3 : τ3.arrs "sv" = (τ.arrs "sv").set k p.2 := by
    rw [h3a _ (by decide)]; simp [τ2, h1a]
  have hact3 : τ3.arrs "act" = (τ.arrs "act").set p.1 0 := by
    rw [h3a _ (by decide)]; simp [τ2, h1a]
  have hS : sExp G (k + 1) = sExp G k + ∑ x ∈ range n, ind (crN G x p.1 p.2) := by
    simp only [sExp, hexp, sum_add_distrib, hst]
  refine ⟨τ3, _, Run.seq hr1 (Run.seq hr2 hr3), ?_, hns3, ?_⟩
  · refine ⟨hC2.fr hF3 (by decide) (by decide) (by decide), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · rw [hns3, h3v _ (by decide)]; simp [τ2]; omega
    · rw [hns3, h3v _ (by decide), hnext]
      simp only [τ2, vars_setVar, if_true]
      rw [card_erase_of_mem hpu]
    · rw [hns3, hnext]; simp [hlen]
    · rw [hns3]
      refine ⟨by rw [hact3]; simp [hact.len], fun u hu => ?_⟩
      rw [hact3, List.getElem?_set, hnext]
      by_cases hue : (p.1 : ℕ) = u
      · subst hue
        simp [hact.len, ind, inBN_erase]
      · rw [if_neg hue, hact.get u hu]
        congr 1
        exact ind_eq_iff.2 (by rw [inBN_erase]; exact ⟨fun h => ⟨fun e => hue e.symm, h⟩,
          fun h => h.2⟩)
    · rw [hns3]; exact hW3.congr fun x _ => (hexp x).symm
    · rw [hsu3]; simp [hI.sulen]
    · rw [hsv3]; simp [hI.svlen]
    · rw [hns3, hnext, hsu3]
      intro j hj
      rw [push_get (by rw [hI.sulen]; omega) (by simp [hlen]) hsu j hj]
      simp
    · rw [hns3, hnext, hsv3]
      intro j hj
      rw [push_get (by rw [hI.svlen]; omega) (by simp [hlen]) hsv j hj]
      simp
    · rw [hns3]; exact XiRep.mk' hR3 rfl rfl fun u _ v _ => xiP_congr (fun x _ => (hexp x).symm) u v
    · exact (((hI.fr.trans (hF1.mono (by simp [scanW, allW]) (by simp))).trans
        (hF2.mono (by simp [allW]) (by simp [allA]))).trans
        (hF3.mono (by simp [xW, allW]) (by simp [xA, allA])))
  · have e : uxC n (20 * (Kw G + Nat.log 2 n) + 30) + 5 = cUp G := rfl
    rw [e, hS, add_mul]
    simp only [cSt]
    omega

theorem wExp_mono {k k' : ℕ} (hk : k ≤ k') (x : ℕ) : wExp G (wSt G k) x ≤ wExp G (wSt G k') x := by
  unfold wExp
  split
  · obtain ⟨l, h, -⟩ := steps_welzlRun (G := G) (k' - k) (wSt G k)
    have e : wSt G k' = welzlRun G (k' - k) (wSt G k) := by
      unfold wSt; rw [← welzlRun_add]; congr 1; omega
    rw [e, h, stepCross_append]
    omega
  · exact le_rfl

/-- **All greedy steps.** The loop runs while at least two vertices are
active. -/
theorem mainLoop_run {B : ℕ} {σ0 τ : Env} (hB : WB n B) (hI : MInv G σ0 τ)
    (h0 : τ.vars "ns" = 0) :
    ∃ τ' K, Run B mainLoop τ τ' K ∧ MInv G σ0 τ' ∧ τ'.vars "wcnt" ≤ 1 ∧
      K ≤ n * (cSt G + 4) + sExp G n * cUp G + 4 := by
  have hs := hB.small
  let Φ : Env → ℕ := fun τ =>
    (n - τ.vars "ns") * (cSt G + 4) + (sExp G n - sExp G (τ.vars "ns")) * cUp G
  have hev : ∀ τ, MInv G σ0 τ → (Cond.lt (.lit 1) (.var "wcnt")).evalB B τ =
      some (decide (1 < τ.vars "wcnt")) := fun τ hI =>
    evalB_condLt (evalB_lit (by omega)) (evalB_var (by have := hI.sum; omega))
  obtain ⟨τ', K, hr, hI', hf, hK⟩ := Run.while_potential (B := B)
    (b := .lt (.lit 1) (.var "wcnt")) (c := stepBody) (MInv G σ0) Φ
    (fun τ hI => ⟨_, hev τ hI⟩)
    (by
      intro τ hI hc
      have h2 : 1 < τ.vars "wcnt" := by rw [hev τ hI] at hc; simpa using hc
      obtain ⟨τ', K, hr, hI', hns, hK⟩ := stepBody_run hB hI h2
      refine ⟨τ', K, hr, hI', ?_⟩
      have hsum := hI.sum
      have hk : τ.vars "ns" + 1 ≤ n := by omega
      have m1 := Nat.mul_le_mul_right (cUp G) (sExp_mono (G := G) hk)
      have m0 := Nat.mul_le_mul_right (cUp G)
        (show sExp G (τ.vars "ns") ≤ sExp G (τ.vars "ns" + 1) from
          sum_le_sum fun x _ => wExp_mono (by omega) x)
      simp only [Φ, hns, size_condLt, size_lit, size_var]
      obtain ⟨a, ha⟩ : ∃ a, n - (τ.vars "ns" + 1) = a := ⟨_, rfl⟩
      rw [show n - τ.vars "ns" = a + 1 by omega, ha, add_mul, one_mul, Nat.sub_mul, Nat.sub_mul]
      omega)
    hI
  refine ⟨τ', K, hr, hI', ?_, ?_⟩
  · rw [hev τ' hI'] at hf; simpa using hf
  · simp only [Φ, h0, sExp_zero, Nat.sub_zero, size_condLt, size_lit, size_var] at hK
    omega

end Lax185574Proofs.Chain.Ram
