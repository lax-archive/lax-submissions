import Lax235315Proofs.Construction.MarkingMath
import Lax235315Proofs.Construction.WelzlStraight
import Mathlib.Tactic

/-! Source-level verification of the duplicate-tolerant neighborhood
collection loop used by the batched near-twin check. -/

namespace Lax235315Proofs.Construction.NearCollectSource

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.MarkingMath
open Lax235315Proofs.Construction.NeighborScan
open Lax235315Proofs.Construction.WelzlProgram

/-- The occupied prefix of `neighbors` is exactly the set of distinct active
targets encountered in the current CSR interval. -/
def NeighborInv (B n targetCap lo hi token : ℕ)
    (active target : ℕ → ℕ) (τ : Env) : Prop :=
  ∃ stamp neighbors : ℕ → ℕ,
    lo ≤ τ.vars "j" ∧ τ.vars "j" ≤ hi ∧ τ.vars "jend" = hi ∧
    τ.vars "token" = token ∧ τ.vars "n" = n ∧ hi ≤ targetCap ∧
    τ.arrs "activeB" = arrOf n active ∧
    τ.arrs "tgt" = arrOf targetCap target ∧
    τ.arrs "stamp" = arrOf n stamp ∧
    Stack "neighbors" "neighborLen" n n
      (activeTargets target active lo (τ.vars "j")).card neighbors τ ∧
    PrefixEnumerates
      (activeTargets target active lo (τ.vars "j")).card neighbors
      (activeTargets target active lo (τ.vars "j")) ∧
    (∀ v < n, stamp v = token ↔
      v ∈ activeTargets target active lo (τ.vars "j")) ∧
    (∀ v < n, stamp v ≤ token) ∧
    ∀ v < n, stamp v < B

lemma neighborInv_initial
    {B n targetCap lo hi token : ℕ} {active target : ℕ → ℕ}
    {σ : Env} {stamp neighbors : ℕ → ℕ}
    (hj : σ.vars "j" = lo) (hjend : σ.vars "jend" = hi)
    (htoken : σ.vars "token" = token) (hn : σ.vars "n" = n)
    (hlohi : lo ≤ hi) (hhi : hi ≤ targetCap)
    (hactive : σ.arrs "activeB" = arrOf n active)
    (htarget : σ.arrs "tgt" = arrOf targetCap target)
    (hstamp : σ.arrs "stamp" = arrOf n stamp)
    (hneighbors : σ.arrs "neighbors" = arrOf n neighbors)
    (hlen : σ.vars "neighborLen" = 0)
    (hstampNe : ∀ v < n, stamp v ≠ token)
    (hstampLe : ∀ v < n, stamp v ≤ token)
    (hstampB : ∀ v < n, stamp v < B) :
    NeighborInv B n targetCap lo hi token active target σ := by
  refine ⟨stamp, neighbors, by omega, by omega, hjend, htoken, hn, hhi,
    hactive, htarget, hstamp, ?_, ?_, ?_, hstampLe, hstampB⟩
  · simpa [hj] using
      (show Stack "neighbors" "neighborLen" n n 0 neighbors σ from
        ⟨hneighbors, hlen, by omega, by intro i hi; omega⟩)
  · simpa [hj] using prefixEnumerates_zero neighbors
  · intro v hv
    simp [hj, hstampNe v hv]

private lemma NeighborInv.advanceSame
    {B n targetCap lo hi token : ℕ} {active target : ℕ → ℕ}
    {σ : Env}
    (hI : NeighborInv B n targetCap lo hi token active target σ)
    (hjlt : σ.vars "j" < hi)
    (hsame : activeTargets target active lo (σ.vars "j" + 1) =
      activeTargets target active lo (σ.vars "j")) (b : ℕ) :
    NeighborInv B n targetCap lo hi token active target
      ((σ.setVar "b" b).setVar "j" (σ.vars "j" + 1)) := by
  rcases hI with ⟨stamp, neighbors, hlo, hjhi, hjend, htoken, hn, hhi,
    hactive, htarget, hstamp, hstack, henum, hstampMem, hstampLe, hstampB⟩
  let σ' := (σ.setVar "b" b).setVar "j" (σ.vars "j" + 1)
  refine ⟨stamp, neighbors, by simp [σ']; omega, by simp [σ']; omega,
    by simp [σ', hjend], by simp [σ', htoken], by simp [σ', hn], hhi,
    by simp [σ', hactive], by simp [σ', htarget], by simp [σ', hstamp],
    ?_, ?_, ?_, hstampLe, hstampB⟩
  · simpa [σ', hsame] using hstack
  · simpa [σ', hsame] using henum
  · intro v hv
    simpa [σ', hsame] using hstampMem v hv

private lemma NeighborInv.advanceFresh
    {B n targetCap lo hi token : ℕ} {active target : ℕ → ℕ}
    {σ σ' : Env}
    (hI : NeighborInv B n targetCap lo hi token active target σ)
    (hjlt : σ.vars "j" < hi)
    (htargetRange : ∀ j, lo ≤ j → j < hi → target j < n)
    (hactiveAt : active (target (σ.vars "j")) = 1)
    (hfresh : (σ.arrs "stamp").getD (target (σ.vars "j")) 0 ≠ token)
    (htokenB : token < B)
    (hj' : σ'.vars "j" = σ.vars "j" + 1)
    (hjend' : σ'.vars "jend" = hi)
    (htoken' : σ'.vars "token" = token) (hn' : σ'.vars "n" = n)
    (hlen' : σ'.vars "neighborLen" =
      (activeTargets target active lo (σ.vars "j")).card + 1)
    (hactive' : σ'.arrs "activeB" = arrOf n active)
    (htarget' : σ'.arrs "tgt" = arrOf targetCap target)
    (hstamp' : σ'.arrs "stamp" =
      (σ.arrs "stamp").set (target (σ.vars "j")) token)
    (hneighbors' : σ'.arrs "neighbors" =
      (σ.arrs "neighbors").set
        (activeTargets target active lo (σ.vars "j")).card
        (target (σ.vars "j"))) :
    NeighborInv B n targetCap lo hi token active target σ' := by
  rcases hI with ⟨stamp, neighbors, hlo, hjhi, hjend, htoken, hn, hhi,
    hactive, htarget, hstamp, hstack, henum, hstampMem, hstampLe, hstampB⟩
  let M := activeTargets target active lo (σ.vars "j")
  let v := target (σ.vars "j")
  have hvn : v < n := htargetRange _ hlo hjlt
  have hstampv : stamp v ≠ token := by
    intro heq
    apply hfresh
    rw [hstamp, getD_arrOf stamp hvn, heq]
  have hvM : v ∉ M := by
    intro hv
    exact hstampv ((hstampMem v hvn).mpr hv)
  have hMnext : activeTargets target active lo (σ.vars "j" + 1) =
      insert v M := by
    rw [activeTargets_succ hlo, if_pos hactiveAt]
  let stamp' := upd stamp v token
  let neighbors' := upd neighbors M.card v
  have hstampArr' : σ'.arrs "stamp" = arrOf n stamp' := by
    rw [hstamp', hstamp, set_arrOf_eq_upd]
  have hneighborsArr' : σ'.arrs "neighbors" = arrOf n neighbors' := by
    rw [hneighbors', hstack.arr, set_arrOf_eq_upd]
  have henum' : PrefixEnumerates (insert v M).card neighbors'
      (insert v M) := by
    rw [Finset.card_insert_of_notMem hvM]
    exact henum.push hvM
  have hstack' : Stack "neighbors" "neighborLen" n n
      (insert v M).card neighbors' σ' := by
    refine ⟨hneighborsArr', ?_, ?_, ?_⟩
    · rw [Finset.card_insert_of_notMem hvM, hlen']
    · calc
        (insert v M).card ≤ (Finset.range n).card := Finset.card_le_card (by
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl | hu
          · exact Finset.mem_range.mpr hvn
          · rw [mem_activeTargets] at hu
            obtain ⟨-, k, hlk, hkj, rfl⟩ := hu
            exact Finset.mem_range.mpr (htargetRange k hlk (hkj.trans hjlt)))
        _ = n := Finset.card_range n
    · intro i hiEntry
      have hmem : neighbors' i ∈ Stack.toList (insert v M).card neighbors' := by
        simp [Stack.toList, arrOf]
        exact ⟨i, hiEntry, rfl⟩
      have := (henum'.2 _).mp hmem
      rcases Finset.mem_insert.mp this with huv | hu
      · rw [huv]
        exact hvn
      · rw [mem_activeTargets] at hu
        obtain ⟨-, k, hlk, hkj, hku⟩ := hu
        rw [← hku]
        exact htargetRange k hlk (hkj.trans hjlt)
  refine ⟨stamp', neighbors', by rw [hj']; omega,
    by rw [hj']; omega, hjend', htoken', hn', hhi,
    hactive', htarget', hstampArr', by simpa [hj', hMnext] using hstack',
    by simpa [hj', hMnext] using henum', ?_, ?_, ?_⟩
  · intro u hu
    rw [hj', hMnext]
    exact upd_eq_token_iff_insert (hstampMem u hu)
  · intro u hu
    simp only [stamp', upd]
    split
    · exact le_rfl
    · exact hstampLe u hu
  · intro u hu
    simp only [stamp', upd]
    split
    · exact htokenB
    · exact hstampB u hu

/-- One collection step preserves `NeighborInv` and advances the CSR index. -/
lemma collectNeighborBody_spec
    {B n targetCap lo hi token : ℕ} {active target : ℕ → ℕ}
    (htargetRange : ∀ j, lo ≤ j → j < hi → target j < n)
    (hactiveB : ∀ v < n, active v < B)
    (hnB : n < B) (htargetCapB : targetCap < B)
    (htokenB : token < B) (honeB : 1 < B) :
    Spec B
      (fun τ => NeighborInv B n targetCap lo hi token active target τ ∧
        τ.vars "j" < hi)
      collectNeighborBody
      (fun τ τ' => NeighborInv B n targetCap lo hi token active target τ' ∧
        τ'.vars "j" = τ.vars "j" + 1) 50 := by
  intro σ hσ
  rcases hσ with ⟨hI, hjlt⟩
  rcases hI with ⟨stamp, neighbors, hlo, hjhi, hjend, htoken, hn, hhi,
    hactive, htarget, hstamp, hstack, henum, hstampMem, hstampLe, hstampB⟩
  have hI₀ : NeighborInv B n targetCap lo hi token active target σ :=
    ⟨stamp, neighbors, hlo, hjhi, hjend, htoken, hn, hhi, hactive,
      htarget, hstamp, hstack, henum, hstampMem, hstampLe, hstampB⟩
  let v := target (σ.vars "j")
  have hvn : v < n := htargetRange _ hlo hjlt
  have hvB : v < B := hvn.trans hnB
  have hjB : σ.vars "j" < B :=
    lt_of_lt_of_le hjlt (hhi.trans htargetCapB.le)
  have hget : (σ.arrs "tgt")[σ.vars "j"]? = some v := by
    rw [htarget, getElem?_arrOf target (hjlt.trans_le hhi)]
  have heval : (Expr.get "tgt" (.var "j")).evalB B σ = some v :=
    evalB_get (evalB_var hjB) hget hvB
  let σ₁ := σ.setVar "b" v
  have rb : Run B (.assign "b" (.get "tgt" (.var "j"))) σ σ₁ 6 := by
    exact (Run.assign heval).mono (by norm_num [Expr.size])
  have hactiveEval : (Expr.get "activeB" (.var "b")).evalB B σ₁ =
      some (active v) := by
    apply evalB_get
    · exact evalB_var (by simp [σ₁]; exact hvB)
    · simp [σ₁, hactive, getElem?_arrOf active hvn]
    · exact hactiveB _ hvn
  by_cases hav : active v = 1
  · have hactiveTest :
        (Cond.eq (.get "activeB" (.var "b")) (.lit 1)).evalB B σ₁ =
          some true := by
      simpa [hav] using evalB_condEq hactiveEval (evalB_lit honeB)
    have hstampEval : (Expr.get "stamp" (.var "b")).evalB B σ₁ =
        some (stamp v) := by
      apply evalB_get
      · exact evalB_var (by simp [σ₁]; exact hvB)
      · simp [σ₁, hstamp, getElem?_arrOf stamp hvn]
      · exact hstampB _ hvn
    have htokenEval : (Expr.var "token").evalB B σ₁ = some token := by
      rw [show (Expr.var "token").evalB B σ₁ = some (σ₁.vars "token") from
        evalB_var (by simp [σ₁, htoken]; exact htokenB)]
      simp [σ₁, htoken]
    by_cases hdup : (σ.arrs "stamp").getD v 0 = token
    · have hdup' : stamp v = token := by
        rw [← getD_arrOf stamp hvn, ← hstamp]
        exact hdup
      have hstampTest :
          (Cond.eq (.get "stamp" (.var "b")) (.var "token")).evalB B σ₁ =
            some true := by
        simpa [hdup'] using evalB_condEq hstampEval htokenEval
      let σ₂ := σ₁.setVar "j" (σ.vars "j" + 1)
      have hj1B : σ.vars "j" + 1 < B := by
        exact lt_of_le_of_lt ((Nat.succ_le_of_lt hjlt).trans hhi) htargetCapB
      have rj : Run B (inc "j") σ₁ σ₂ 4 := by
        apply Run.assign
        exact evalB_bin (by simpa [σ₁] using evalB_var hjB)
          (evalB_lit honeB) hj1B
      have hvM : v ∈ activeTargets target active lo (σ.vars "j") :=
        (hstampMem v hvn).mp hdup'
      have hsame : activeTargets target active lo (σ.vars "j" + 1) =
          activeTargets target active lo (σ.vars "j") := by
        rw [activeTargets_succ hlo, if_pos hav,
          Finset.insert_eq_self.mpr hvM]
      refine ⟨σ₂, ?_, hI₀.advanceSame hjlt hsame v, by simp [σ₂]⟩
      exact (rb.seq ((Run.ite_true hactiveTest
        (Run.ite_true hstampTest Run.skip)).seq rj)).mono (by
          norm_num [collectNeighborBody, seqs, Cond.size, Expr.size])
    · have hstampv : stamp v ≠ token := by
        intro heq
        apply hdup
        rw [hstamp, getD_arrOf stamp hvn, heq]
      have hstampTest :
          (Cond.eq (.get "stamp" (.var "b")) (.var "token")).evalB B σ₁ =
            some false := by
        simpa [hstampv] using evalB_condEq hstampEval htokenEval
      let M := activeTargets target active lo (σ.vars "j")
      have hvM : v ∉ M := by
        intro hv
        exact hstampv ((hstampMem v hvn).mpr hv)
      have hMsub : insert v M ⊆ Finset.range n := by
        intro u hu
        rcases Finset.mem_insert.mp hu with rfl | hu
        · exact Finset.mem_range.mpr hvn
        · rw [mem_activeTargets] at hu
          obtain ⟨-, k, hlk, hkj, rfl⟩ := hu
          exact Finset.mem_range.mpr (htargetRange k hlk (hkj.trans hjlt))
      have hMcard : M.card < n := by
        have hc := Finset.card_le_card hMsub
        rw [Finset.card_insert_of_notMem hvM, Finset.card_range] at hc
        omega
      have hMcardB : M.card < B := hMcard.trans hnB
      let σ₂ := σ₁.setArr "stamp" v token
      have rstamp : Run B (.store "stamp" (.var "b") (.var "token"))
          σ₁ σ₂ 3 := by
        apply Run.store
        · exact evalB_var (by simp [σ₁]; exact hvB)
        · exact htokenEval
        · rw [show σ₁.arrs "stamp" = σ.arrs "stamp" by simp [σ₁],
            hstamp, length_arrOf]
          exact hvn
      let σ₃ := σ₂.setArr "neighbors" M.card v
      have rstore : Run B
          (.store "neighbors" (.var "neighborLen") (.var "b")) σ₂ σ₃ 3 := by
        have hlen : σ₂.vars "neighborLen" = M.card := by
          simp [σ₂, σ₁, hstack.height, M]
        apply Run.store
        · rw [show (Expr.var "neighborLen").evalB B σ₂ =
              some (σ₂.vars "neighborLen") from evalB_var (by
                rw [hlen]; exact hMcardB), hlen]
        · exact evalB_var (by simp [σ₂, σ₁]; exact hvB)
        · rw [show σ₂.arrs "neighbors" = σ.arrs "neighbors" by
              simp [σ₂, σ₁], hstack.arr, length_arrOf]
          exact hMcard
      let σ₄ := σ₃.setVar "neighborLen" (M.card + 1)
      have rlen : Run B (inc "neighborLen") σ₃ σ₄ 4 := by
        have hlen : σ₃.vars "neighborLen" = M.card := by
          simp [σ₃, σ₂, σ₁, hstack.height, M]
        apply Run.assign
        exact evalB_bin (by rw [show (Expr.var "neighborLen").evalB B σ₃ =
          some (σ₃.vars "neighborLen") from evalB_var (by
            rw [hlen]; exact hMcardB), hlen]) (evalB_lit honeB)
          (by simpa using (show M.card + 1 < B by omega))
      let σ₅ := σ₄.setVar "j" (σ.vars "j" + 1)
      have hj1B : σ.vars "j" + 1 < B := by
        exact lt_of_le_of_lt ((Nat.succ_le_of_lt hjlt).trans hhi) htargetCapB
      have rj : Run B (inc "j") σ₄ σ₅ 4 := by
        apply Run.assign
        exact evalB_bin (by simpa [σ₄, σ₃, σ₂, σ₁] using evalB_var hjB)
          (evalB_lit honeB) hj1B
      have rfresh : Run B
          (seqs [.store "stamp" (.var "b") (.var "token"),
            .store "neighbors" (.var "neighborLen") (.var "b"),
            inc "neighborLen"]) σ₁ σ₄ 10 := by
        simpa [seqs] using (rstamp.seq (rstore.seq rlen)).mono (by omega)
      have hrun : Run B collectNeighborBody σ σ₅ 50 := by
        exact (rb.seq ((Run.ite_true hactiveTest
          (Run.ite_false hstampTest rfresh)).seq rj)).mono (by
            norm_num [collectNeighborBody, seqs, Cond.size, Expr.size])
      have hpost : NeighborInv B n targetCap lo hi token active target σ₅ := by
        apply NeighborInv.advanceFresh hI₀ hjlt htargetRange hav hdup htokenB
        · simp [σ₅, σ₄]
        · simp [σ₅, σ₄, σ₃, σ₂, σ₁, hjend]
        · simp [σ₅, σ₄, σ₃, σ₂, σ₁, htoken]
        · simp [σ₅, σ₄, σ₃, σ₂, σ₁, hn]
        · simp [σ₅, σ₄, σ₃, σ₂, σ₁, hstack.height, M]
        · simp [σ₅, σ₄, σ₃, σ₂, σ₁, hactive]
        · simp [σ₅, σ₄, σ₃, σ₂, σ₁, htarget]
        · simp [σ₅, σ₄, σ₃, σ₂, σ₁, v]
        · simp [σ₅, σ₄, σ₃, σ₂, σ₁, hstack.height, M, v]
      exact ⟨σ₅, hrun, hpost, by simp [σ₅, σ₄]⟩
  · have hactiveTest :
        (Cond.eq (.get "activeB" (.var "b")) (.lit 1)).evalB B σ₁ =
          some false := by
      simpa [hav] using evalB_condEq hactiveEval (evalB_lit honeB)
    let σ₂ := σ₁.setVar "j" (σ.vars "j" + 1)
    have hj1B : σ.vars "j" + 1 < B := by
      exact lt_of_le_of_lt ((Nat.succ_le_of_lt hjlt).trans hhi) htargetCapB
    have rj : Run B (inc "j") σ₁ σ₂ 4 := by
      apply Run.assign
      exact evalB_bin (by simpa [σ₁] using evalB_var hjB)
        (evalB_lit honeB) hj1B
    have hsame : activeTargets target active lo (σ.vars "j" + 1) =
        activeTargets target active lo (σ.vars "j") := by
      rw [activeTargets_succ hlo, if_neg hav]
    refine ⟨σ₂, ?_, hI₀.advanceSame hjlt hsame v, by simp [σ₂]⟩
    exact (rb.seq ((Run.ite_false hactiveTest Run.skip).seq rj)).mono (by
      norm_num [collectNeighborBody, seqs, Cond.size, Expr.size])

/-- The complete interval scan produces a duplicate-free enumeration of its
active targets. -/
lemma collectNeighborLoop_run
    {B n targetCap lo hi token : ℕ} {active target : ℕ → ℕ} {σ : Env}
    (hI : NeighborInv B n targetCap lo hi token active target σ)
    (htargetRange : ∀ j, lo ≤ j → j < hi → target j < n)
    (hactiveB : ∀ v < n, active v < B)
    (hnB : n < B) (htargetCapB : targetCap < B)
    (htokenB : token < B) (honeB : 1 < B) :
    ∃ σ', Run B (.while (.lt (.var "j") (.var "jend"))
        collectNeighborBody) σ σ' (54 * (hi - lo) + 4) ∧
      NeighborInv B n targetCap lo hi token active target σ' ∧
      σ'.vars "j" = hi := by
  let I := NeighborInv B n targetCap lo hi token active target
  have hbody : Spec B (fun τ => I τ ∧ τ.vars "j" < hi)
      collectNeighborBody
      (fun τ τ' => I τ' ∧ τ'.vars "j" = τ.vars "j" + 1) 50 :=
    collectNeighborBody_spec htargetRange hactiveB hnB htargetCapB htokenB honeB
  exact (Spec.forRange "j" "jend" I hi 50 (54 * (hi - lo) + 4)
    (fun _ h => by
      rcases h with ⟨_, _, _, hjhi, _, _, _, hcap, -⟩
      exact lt_of_le_of_lt (hjhi.trans hcap) htargetCapB)
    (fun _ h => by
      rcases h with ⟨_, _, _, _, hjend, _, _, hcap, -⟩
      rw [hjend]
      exact lt_of_le_of_lt hcap htargetCapB)
    (fun _ h => by
      rcases h with ⟨_, _, _, _, hjend, -⟩
      exact hjend)
    (fun _ h => by
      rcases h with ⟨_, _, _, hjhi, -⟩
      exact hjhi)
    hbody (fun _ h => h)
    (fun _ h => by
      rcases h with ⟨_, _, hlo, -⟩
      omega)).run hI

end Lax235315Proofs.Construction.NearCollectSource
