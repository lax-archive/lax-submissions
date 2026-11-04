import Lax185574Proofs.Chain.Ram.ChainOut
import Lax185574Proofs.Chain.Ram.InputRam

/-!
The second half of the program: from the ordering and `q` to the
output. `tailCom` sets up the damping state for `V`, runs the damping
sequence, computes the suffix unions and writes the chain. Its output is
the word of `chainAlg` for graphs with at least two vertices
(`tailCom_run`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram Lax185574Proofs.Chain Lax185574.WordEncoding

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

/-- Start the damping sequence at `V`. -/
def seqInit : Com :=
  .seq (.assign "M" (.add (.var "n") (.lit 4)))
    (.seq (rowFill "inA" (.var "b") (.lit 1)) (.seq (.assign "ca" (.var "n")) (.assign "m" (.lit 0))))

/-- Everything after the ordering. -/
def tailCom : Com := .seq seqInit (.seq seqLoop (.seq lstCom outCom))

/-- The word of the chain for at least two vertices. -/
theorem toWord_chainAlg {r : ℕ} {ε : ℚ} (hn : 2 ≤ n) (hε : 0 < ε) :
    toWord (chainAlg G r ε) =
      let o := welzlVOrder G
      let q := qOf n r ε
      (dLen G r o q + 1) :: (List.range (dLen G r o q + 1)).flatMap fun i =>
        (below n (inSuf (dIter G r o q) (dLen G r o q) i)).length ::
          elemFrames (below n (inSuf (dIter G r o q) (dLen G r o q) i)) := by
  have hq := (qOf_spec (r := r) hn hε).1
  unfold chainAlg chainSeq
  rw [if_neg (by rw [Fintype.card_fin]; omega), Fintype.card_fin, dampSeq_eq r _ hq]
  exact toWord_suffix _ _

/-- What the second half reads. -/
structure TailPre (n r : ℕ) (G : SimpleGraph (Fin n)) (o : VOrder (Fin n)) (q : ℕ) (τ : Env) :
    Prop where
  hn : τ.vars "n" = n
  htr : τ.vars "tr" = r
  hq : τ.vars "q" = q
  hadj : Mat τ "adj" n (fun u v => ind (gA G u v))
  hpos : Vec τ "pos" n (posN o)
  lvec : ∀ a ∈ ["inA", "inB", "inS", "Sl", "p2", "p3", "mark", "rep", "lab", "key", "lab2", "labk",
    "sz", "lst"], (τ.arrs a).length = n
  ltab : n * (n + 4) ≤ (τ.arrs "tab").length
  lcnt : (τ.arrs "cnt").length = n * n
  lch : (τ.arrs "ch").length = (n + 1) * n
  ztab : Zero τ "tab"
  zcnt : Mat τ "cnt" n (fun _ _ => 0)
  zsz : Vec τ "sz" n (fun _ => 0)
  zmark : Vec τ "mark" n (fun _ => 0)

theorem seqInit_run {B r q : ℕ} {o : VOrder (Fin n)} (hB : n + 6 < B) {σ : Env}
    (h : TailPre n r G o q σ) :
    ∃ σ', Run B seqInit σ σ' (n * 11 + 20) ∧ SeqSt n r G o q (posN o) 0 σ' ∧
      σ'.out = σ.out := by
  obtain ⟨σ1, hr1, hv1, ha1, hl1, hg1⟩ :=
    fillKeep_run (n := n) (B' := B) (arr := "inA") (e := .lit 1) (f := fun _ => 1) (base := 0) (K := 3)
      (σ := σ.setVar "M" (n + 4)) (by omega) (by simp [h.hn]) (by simp [h.lvec "inA" (by simp)])
      (.var "b") (fun τ k hv ha hb hk => by simp [hb]; omega)
      (fun τ k hv ha hb hk => by simp; omega) (by simp)
  set σ2 := (σ1.setVar "ca" n).setVar "m" 0 with hσ2
  have hrun : Run B seqInit σ σ2 (n * 11 + 20) :=
    (Run.seq (Run.assign (v := n + 4) (by simp [h.hn]; omega)) (Run.seq hr1
      (Run.seq (Run.assign (by simp [hv1 "n" (by decide), h.hn]; omega))
        (Run.assign (v := 0) (by simp; omega))))).mono (by simp; omega)
  have hA : ∀ a, a ≠ "inA" → σ2.arrs a = σ.arrs a := fun a ha => by simp [hσ2, ha1 a ha]
  have hV : ∀ x, x ∉ ["b", "ca", "m", "M"] → σ2.vars x = σ.vars x := fun x hx => by
    simp at hx; simp [hσ2, hx.2.1, hx.2.2.1, hv1 x hx.1, hx.2.2.2]
  refine ⟨σ2, hrun, ⟨⟨⟨σ.vars "t1", σ.vars "t2", σ.vars "t3", ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    fun a ha => ?_, ?_, ?_⟩⟩, ?_, ?_, fun t ht => ?_, ?_, ?_, ?_⟩, by simp [hσ2], ?_,
    fun j hj => absurd hj (Nat.not_lt_zero _)⟩, ?_⟩
  · rw [hV _ (by decide), h.hn]
  · simp [hσ2, hv1 "M" (by decide)]
  · rw [hV _ (by decide), h.htr]
  · rw [hV _ (by decide)]
  · rw [hV _ (by decide)]
  · rw [hV _ (by decide)]
  · exact h.hadj.of_eq (hA _ (by decide))
  · exact h.hpos.of_eq (hA _ (by decide))
  · refine ⟨by simp [hσ2, hl1, h.lvec "inA" (by simp)], fun u hu => ?_⟩
    simp only [hσ2, arrs_setVar, hg1 u]
    simp [hu, ind, inBN, dIter]
  · rw [hA a (by simp at ha ⊢; rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl <;> decide)]
    exact h.lvec a (by simp at ha ⊢; tauto)
  · rw [hA _ (by decide)]; exact h.ltab
  · rw [hA _ (by decide)]; exact h.lcnt
  · rw [hV _ (by decide), h.hq]
  · simp [hσ2, dIter]
  · rw [hA _ (by decide)] at ht ⊢; exact h.ztab t ht
  · exact h.zcnt.of_eq (hA _ (by decide))
  · exact h.zsz.of_eq (hA _ (by decide))
  · exact h.zmark.of_eq (hA _ (by decide))
  · rw [hA _ (by decide)]; exact h.lch
  · rw [hrun.out_eq (by decide)]

/-- The cost of the second half. -/
noncomputable def tailCost (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ)
    (o : VOrder (Fin n)) (q : ℕ) : ℕ :=
  ∑ j ∈ range (dLen G r o q), sCost G r o q j + (n + 1) * (n * 100 + 200) + 100

theorem tailCom_run {B r : ℕ} {ε : ℚ} (hε : 0 < ε) (hn2 : 2 ≤ n) (hB : DampBound n B)
    (hrB : r < B) {σ : Env} (h : TailPre n r G (welzlVOrder G) (qOf n r ε) σ) :
    ∃ σ', Run B tailCom σ σ' (tailCost G r (welzlVOrder G) (qOf n r ε)) ∧
      σ'.out = σ.out ++ toWord (chainAlg G r ε) := by
  have hB1 := hB.1
  unfold PdBound at hB1
  obtain ⟨hq2, hqn, -⟩ := qOf_spec (r := r) hn2 hε
  obtain ⟨σ1, hr1, hst1, ho1⟩ := seqInit_run (B := B) (r := r) (q := qOf n r ε) (o := welzlVOrder G)
    (by omega) h
  obtain ⟨σ2, K2, hr2, hst2, hK2, hv2⟩ := seqLoop_run hB hrB (welzlVOrder G) rfl hq2 hqn hst1
  have hMn := dLen_le (G := G) r (welzlVOrder G) hq2
  have hl2 : (σ2.arrs "lst").length = n := by
    rw [hr2.frame_arr "lst" (by decide), hr1.frame_arr "lst" (by decide)]
    exact h.lvec "lst" (by simp)
  obtain ⟨t1, t2, t3, hF2⟩ := hst2.dst.fix
  obtain ⟨σ3, hr3, hv3, ha3, hl3, hok3⟩ :=
    lstCom_run (B := B) (M := dLen G r (welzlVOrder G) (qOf n r ε))
      (D := dIter G r (welzlVOrder G) (qOf n r ε)) hMn (by nlinarith) hF2.hn hst2.hm hst2.hch hl2
  obtain ⟨σ4, hr4, ho4⟩ :=
    outCom_run (B := B) (M := dLen G r (welzlVOrder G) (qOf n r ε))
      (D := dIter G r (welzlVOrder G) (qOf n r ε)) hMn (by omega)
      (by rw [hv3 "n" (by decide), hF2.hn]) (by rw [hv3 "m" (by decide), hst2.hm]) hl3 hok3
  refine ⟨σ4, ?_, ?_⟩
  · exact (Run.seq hr1 (Run.seq (hr2.mono hK2) (Run.seq hr3 hr4))).mono (by
      unfold tailCost; nlinarith)
  · rw [ho4, toWord_chainAlg hn2 hε, hr3.out_eq (by decide), hr2.out_eq (by decide), ho1]

end Lax185574Proofs.Chain.Ram
