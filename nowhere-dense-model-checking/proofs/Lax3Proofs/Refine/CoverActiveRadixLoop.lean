import Lax3Proofs.Refine.CoverActiveRadixPass
import Lax3Proofs.Refine.CoverActiveLoop
import Lax3Proofs.Refine.SigmaLoop
import Lax3Proofs.Refine.MassMath

/-!
# Sorting every active-cover block

This file lifts the verified single-block radix sorter over the compressed
active-cover arena.  The outer loop reads only consecutive offsets, sorts
exactly that half-open block, and advances to the next active centre.
-/

namespace Lax3Proofs.Refine.CoverActiveRadixLoop

open Finset
open Lax3.ColoredGraphs
open Lax3Proofs.RamCover
open Lax3Proofs.Refine.MassMath (blockSize)
open Lax3Proofs.Refine.CoverActiveRadixMath
open Lax3Proofs.Refine.CoverActiveRadixPass
open Lax13Proofs.Imp Lax13Proofs.Reasoning

/-! ## Offset and segment lemmas -/

variable {n q xp r : ℕ} {G : SimpleGraph (Fin n)}
variable {A₀ centre Xoff Xmem asg : ℕ → ℕ}
variable {π : Equiv.Perm (Fin n)}

theorem rawOff_mono (h : RawCoverOutA G A₀ π centre r q xp Xoff Xmem asg)
    {i j : ℕ} (hij : i ≤ j) (hj : j ≤ q) : Xoff i ≤ Xoff j := by
  induction j with
  | zero =>
      have : i = 0 := by omega
      subst i
      exact le_rfl
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with hlt | hge
      · exact le_trans (ih (by omega) (by omega)) (h.mono j (by omega))
      · have : i = j + 1 := by omega
        subst i
        exact le_rfl

theorem rawOff_le (h : RawCoverOutA G A₀ π centre r q xp Xoff Xmem asg)
    {k : ℕ} (hk : k ≤ q) : Xoff k ≤ xp := by
  rw [← h.last]
  exact rawOff_mono h hk le_rfl

theorem add_blockSize (h : RawCoverOutA G A₀ π centre r q xp Xoff Xmem asg)
    {k : ℕ} (hk : k < q) : Xoff k + blockSize Xoff k = Xoff (k + 1) := by
  exact Nat.add_sub_of_le (h.mono k hk)

theorem raw_blockSize_le (h : RawCoverOutA G A₀ π centre r q xp Xoff Xmem asg)
    {k : ℕ} (hk : k < q) : blockSize Xoff k ≤ n := by
  let f : Fin (blockSize Xoff k) → Fin n := fun i =>
    ⟨Xmem (Xoff k + i), h.mem_lt _ (by
      have hip : Xoff k + i < Xoff (k + 1) := by
        rw [← add_blockSize h hk]
        omega
      exact lt_of_lt_of_le hip (rawOff_le h (by omega)))⟩
  have hf : Function.Injective f := by
    intro i j hij
    apply Fin.ext
    have hp := h.block_inj k hk (Xoff k + i) (Xoff k + j)
      (by omega) (by rw [← add_blockSize h hk]; omega)
      (by omega) (by rw [← add_blockSize h hk]; omega)
      (by simpa [f] using congrArg Fin.val hij)
    omega
  simpa [f] using Fintype.card_le_of_injective f hf

theorem raw_sum_blockSize (h : RawCoverOutA G A₀ π centre r q xp Xoff Xmem asg) :
    ∀ t ≤ q, ∑ k ∈ range t, blockSize Xoff k = Xoff t := by
  intro t ht
  induction t with
  | zero => simp [h.zero]
  | succ t ih =>
      rw [sum_range_succ, ih (by omega), blockSize]
      have := h.mono t (by omega)
      omega

theorem raw_arena_le (h : RawCoverOutA G A₀ π centre r q xp Xoff Xmem asg) :
    xp ≤ n * n := by
  calc
    xp = ∑ k ∈ range q, blockSize Xoff k := by
      rw [raw_sum_blockSize h q le_rfl, h.last]
    _ ≤ ∑ _k ∈ range q, n := by
      exact sum_le_sum fun k hk => raw_blockSize_le h (mem_range.mp hk)
    _ = q * n := by simp
    _ ≤ n * n := Nat.mul_le_mul_right n h.count_le

theorem raw_segment_nodup
    (h : RawCoverOutA G A₀ π centre r q xp Xoff Xmem asg)
    {k : ℕ} (hk : k < q) :
    (segment (Xoff k) (blockSize Xoff k) Xmem).Nodup := by
  rw [CoverActiveRadixPass.segment, List.nodup_ofFn]
  intro i j hij
  apply Fin.ext
  have hp := h.block_inj k hk (Xoff k + i) (Xoff k + j)
    (by omega) (by rw [← add_blockSize h hk]; omega)
    (by omega) (by rw [← add_blockSize h hk]; omega) hij
  omega

theorem mem_segment_block_iff {lo hi w : ℕ} {X : ℕ → ℕ} (hlo : lo ≤ hi) :
    w ∈ segment lo (hi - lo) X ↔
      ∃ p, lo ≤ p ∧ p < hi ∧ X p = w := by
  rw [mem_segment_iff]
  constructor
  · rintro ⟨i, hi', heq⟩
    exact ⟨lo + i, by omega, by omega, heq⟩
  · rintro ⟨p, hp, hp', heq⟩
    refine ⟨p - lo, by omega, ?_⟩
    simpa [Nat.add_sub_of_le hp] using heq

theorem segment_eq_of_eq_on {lo m : ℕ} {X Y : ℕ → ℕ}
    (h : ∀ i < m, X (lo + i) = Y (lo + i)) :
    segment lo m X = segment lo m Y := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    rw [segment_getElem lo m X i hi, segment_getElem lo m Y i hi']
    exact h i (by simpa using hi)

theorem pairwise_segment_to_block {lo hi : ℕ} {X : ℕ → ℕ}
    (hlo : lo ≤ hi) (hpair : (segment lo (hi - lo) X).Pairwise (fun x y => x < y)) :
    ∀ p p', lo ≤ p → p < p' → p' < hi → X p < X p' := by
  intro p p' hp hpp' hp'end
  have h := (pairwise_segment_iff.mp hpair) (p - lo) (p' - lo) (by omega) (by omega)
  simpa [Nat.add_sub_of_le hp, Nat.add_sub_of_le (le_trans hp hpp'.le)] using h

/-! ## Outer program and invariant -/

/-- Load the current block bounds, run its radix sorter, and advance the
outer block counter. -/
def radixCoverTurn : Com :=
  .seq (.assign "rslo" (.get "xoff" (.var "rsc")))
    (.seq (.assign "rsnext" (.get "xoff" (.add (.var "rsc") (.lit 1))))
      (.seq (.assign "rsn" (.sub (.var "rsnext") (.var "rslo")))
        (.seq radixBlockCom
          (.assign "rsc" (.add (.var "rsc") (.lit 1))))))

/-- Set the common bit count once, then sort every active block. -/
def radixCoverCom (bits : ℕ) : Com :=
  .seq (.assign "rsbits" (.lit bits))
    (.seq (.assign "rsc" (.lit 0))
      (.while (.lt (.var "rsc") (.var "qn")) radixCoverTurn))

def radixCoverTurnCost (bits : ℕ) (Xoff : ℕ → ℕ) (k : ℕ) : ℕ :=
  radixBlockCost bits (blockSize Xoff k) + 16

def radixCoverCost (bits q : ℕ) (Xoff : ℕ → ℕ) : ℕ :=
  2 + ((∑ k ∈ range q, (radixCoverTurnCost bits Xoff k + 4)) + 6)

/-- Processed blocks have their exact radix result; the unprocessed suffix
is still byte-for-byte the entering arena. -/
def CoverRadixInv (n q xp bits : ℕ) (Xoff Xmem asg : ℕ → ℕ)
    (σ : Env) : Prop :=
  σ.vars "rsc" ≤ q ∧ σ.vars "qn" = q ∧ σ.vars "rsbits" = bits ∧
  σ.arrs "xoff" = arrOf (n + 1) Xoff ∧ σ.arrs "asg" = arrOf n asg ∧
  ∃ X' Q : ℕ → ℕ,
    σ.arrs "xmem" = arrOf (n * n) X' ∧ σ.arrs "q" = arrOf n Q ∧
    (∀ p < xp, X' p < n) ∧
    (∀ k < σ.vars "rsc",
      segment (Xoff k) (blockSize Xoff k) X' =
        radixRounds bits (segment (Xoff k) (blockSize Xoff k) Xmem)) ∧
    (∀ p, Xoff (σ.vars "rsc") ≤ p → p < xp → X' p = Xmem p)

/-! ## One outer turn -/

theorem radixCoverTurn_spec {B bits : ℕ}
    (hraw : RawCoverOutA G A₀ π centre r q xp Xoff Xmem asg)
    (hB : 1 < B) (hnB : n < B) (hnnB : n * n < B) (hbitsB : bits < B)
    {k : ℕ} (hk : k < q) :
    Spec B
      (fun σ => CoverRadixInv n q xp bits Xoff Xmem asg σ ∧ σ.vars "rsc" = k)
      radixCoverTurn
      (fun _ σ' => CoverRadixInv n q xp bits Xoff Xmem asg σ' ∧
        σ'.vars "rsc" = k + 1)
      (radixCoverTurnCost bits Xoff k) := by
  intro σ hσ
  obtain ⟨⟨hrscle, hqn, hbits, hxoff, hasg, Xc, Q, hxmem, hq, hmem,
      hdone, hsuffix⟩, hrsc⟩ := hσ
  let lo := Xoff k
  let hi := Xoff (k + 1)
  let m := blockSize Xoff k
  have hkN : k < n := lt_of_lt_of_le hk hraw.count_le
  have hkB : k < B := lt_trans hkN hnB
  have hk1N : k + 1 < n + 1 := by omega
  have hk1B : k + 1 < B := by
    have : k + 1 ≤ q := by omega
    omega
  have hlohi : lo ≤ hi := hraw.mono k hk
  have hhim : lo + m = hi := add_blockSize hraw hk
  have hhiXp : hi ≤ xp := rawOff_le hraw (by omega)
  have hxpnn : xp ≤ n * n := raw_arena_le hraw
  have hloB : lo < B := lt_of_le_of_lt (le_trans hlohi (le_trans hhiXp hxpnn)) hnnB
  have hhiB : hi < B := lt_of_le_of_lt (le_trans hhiXp hxpnn) hnnB
  have hmN : m ≤ n := raw_blockSize_le hraw hk
  have hmB : m < B := lt_of_le_of_lt hmN hnB
  have ersc : (Expr.var "rsc").evalB B σ = some k := by
    have hv := evalB_var (B := B) (x := "rsc") (show σ.vars "rsc" < B by
      rw [hrsc]
      exact hkB)
    simpa only [hrsc] using hv
  have elo : (Expr.get "xoff" (.var "rsc")).evalB B σ = some lo := by
    apply evalB_get ersc
    · rw [hxoff, getElem?_arrOf Xoff (show k < n + 1 by omega)]
    · exact hloB
  let σ₁ := σ.setVar "rslo" lo
  have r₁ : Run B (.assign "rslo" (.get "xoff" (.var "rsc"))) σ σ₁ 3 :=
    Run.assign elo
  have eidx : (Expr.add (.var "rsc") (.lit 1)).evalB B σ₁ = some (k + 1) := by
    apply evalB_bin (op := .add)
    · have hrsc₁ : σ₁.vars "rsc" = k := by simp [σ₁, hrsc]
      have hv := evalB_var (B := B) (x := "rsc")
        (show σ₁.vars "rsc" < B by rw [hrsc₁]; exact hkB)
      simpa only [hrsc₁] using hv
    · exact evalB_lit hB
    · simp only [Bop.apply_add]
      exact hk1B
  have ehi : (Expr.get "xoff" (.add (.var "rsc") (.lit 1))).evalB B σ₁ = some hi := by
    apply evalB_get eidx
    · rw [show σ₁.arrs "xoff" = arrOf (n + 1) Xoff by simpa [σ₁] using hxoff,
        getElem?_arrOf Xoff hk1N]
    · exact hhiB
  let σ₂ := σ₁.setVar "rsnext" hi
  have r₂ : Run B
      (.assign "rsnext" (.get "xoff" (.add (.var "rsc") (.lit 1)))) σ₁ σ₂ 5 :=
    Run.assign ehi
  have em : (Expr.sub (.var "rsnext") (.var "rslo")).evalB B σ₂ = some m := by
    apply evalB_bin (op := .sub)
    · apply evalB_var
      simp [σ₂, hhiB]
    · apply evalB_var
      simp [σ₂, σ₁, hloB]
    · simpa only [Bop.apply_sub, m, lo, hi] using hmB
  let σ₃ := σ₂.setVar "rsn" m
  have r₃ : Run B (.assign "rsn" (.sub (.var "rsnext") (.var "rslo"))) σ₂ σ₃ 4 :=
    Run.assign em
  have hXcB : ∀ i < m, Xc (lo + i) < B := by
    intro i hi'
    apply lt_trans (hmem (lo + i) (by omega)) hnB
  obtain ⟨σb, rb, hb⟩ :=
    (radixBlockCom_spec (X := Xc) (Q₀ := Q) hB hnB hmN hbitsB
      (by rw [hhim]; exact le_trans hhiXp hxpnn)
      (by rw [hhim]; exact hhiB) hXcB).run (show
        σ₃.vars "rslo" = lo ∧ σ₃.vars "rsn" = m ∧
          σ₃.vars "rsbits" = bits ∧
          σ₃.arrs "xmem" = arrOf (n * n) Xc ∧ σ₃.arrs "q" = arrOf n Q from by
        refine ⟨by simp [σ₃, σ₂, σ₁], by simp [σ₃], ?_, ?_, ?_⟩
        · simp [σ₃, σ₂, σ₁, hbits]
        · simp [σ₃, σ₂, σ₁, hxmem]
        · simp [σ₃, σ₂, σ₁, hq])
  obtain ⟨hblo, hblen, hbbits, -, Xn, Qn, hbxmem, hbq, hbseg, hboutside⟩ := hb
  have hbrsc : σb.vars "rsc" = k := by
    rw [rb.frame_var "rsc" (by
      simp [radixBlockCom, radixRoundCom, radixPassCom, stableScatterCom,
        selectDigitCom, selectDigitSlot, copyBackCom, copyBackSlot, Com.wvars])]
    simp [σ₃, σ₂, σ₁, hrsc]
  have hbqn : σb.vars "qn" = q := by
    rw [rb.frame_var "qn" (by
      simp [radixBlockCom, radixRoundCom, radixPassCom, stableScatterCom,
        selectDigitCom, selectDigitSlot, copyBackCom, copyBackSlot, Com.wvars])]
    simp [σ₃, σ₂, σ₁, hqn]
  have hbxoff : σb.arrs "xoff" = arrOf (n + 1) Xoff := by
    rw [rb.frame_arr "xoff" (by
      simp [radixBlockCom, radixRoundCom, radixPassCom, stableScatterCom,
        selectDigitCom, selectDigitSlot, copyBackCom, copyBackSlot, Com.warrs])]
    simp [σ₃, σ₂, σ₁, hxoff]
  have hbasg : σb.arrs "asg" = arrOf n asg := by
    rw [rb.frame_arr "asg" (by
      simp [radixBlockCom, radixRoundCom, radixPassCom, stableScatterCom,
        selectDigitCom, selectDigitSlot, copyBackCom, copyBackSlot, Com.warrs])]
    simp [σ₃, σ₂, σ₁, hasg]
  have einc : (Expr.add (.var "rsc") (.lit 1)).evalB B σb = some (k + 1) := by
    apply evalB_bin (op := .add)
    · have hv := evalB_var (B := B) (x := "rsc")
        (show σb.vars "rsc" < B by rw [hbrsc]; exact hkB)
      simpa only [hbrsc] using hv
    · exact evalB_lit hB
    · simp only [Bop.apply_add]
      exact hk1B
  let σ' := σb.setVar "rsc" (k + 1)
  have rinc : Run B (.assign "rsc" (.add (.var "rsc") (.lit 1))) σb σ' 4 :=
    Run.assign einc
  have hcurOrig : segment lo m Xc = segment lo m Xmem := by
    apply segment_eq_of_eq_on
    intro i hi'
    exact hsuffix (lo + i) (by simpa [hrsc, lo] using Nat.le_add_right lo i)
      (by omega)
  have hmemn : ∀ p < xp, Xn p < n := by
    intro p hp
    by_cases hout : p < lo ∨ lo + m ≤ p
    · rw [hboutside p hout]
      exact hmem p hp
    · have hplo : lo ≤ p := by omega
      have hip : p - lo < m := by omega
      have hw := radixRounds_segment_words (B := n)
        (lo := lo) (m := m) (b := bits) (X := Xc) (X' := Xn)
        (fun i hi' => hmem (lo + i) (by omega)) hbseg (p - lo) hip
      simpa [Nat.add_sub_of_le hplo] using hw
  have hdone' : ∀ j < k + 1,
      segment (Xoff j) (blockSize Xoff j) Xn =
        radixRounds bits (segment (Xoff j) (blockSize Xoff j) Xmem) := by
    intro j hj
    rcases lt_or_eq_of_le (show j ≤ k by omega) with hjk | rfl
    · calc
        segment (Xoff j) (blockSize Xoff j) Xn =
            segment (Xoff j) (blockSize Xoff j) Xc := by
          apply segment_eq_of_eq_on
          intro i hi'
          apply hboutside
          left
          have hend : Xoff j + blockSize Xoff j = Xoff (j + 1) :=
            add_blockSize hraw (lt_trans hjk hk)
          have hbefore : Xoff (j + 1) ≤ lo := by
            exact rawOff_mono hraw (by omega) (by omega)
          omega
        _ = radixRounds bits (segment (Xoff j) (blockSize Xoff j) Xmem) :=
          hdone j (by simpa [hrsc] using hjk)
    · simpa [lo, m] using hbseg.trans (congrArg (radixRounds bits) hcurOrig)
  have hsuffix' : ∀ p, Xoff (k + 1) ≤ p → p < xp → Xn p = Xmem p := by
    intro p hp hp'
    rw [hboutside p (Or.inr (by simpa [hhim] using hp))]
    exact hsuffix p (by simpa [hrsc, lo] using le_trans hlohi hp) hp'
  refine ⟨σ', ?_, ?_⟩
  · have hrun := r₁.seq (r₂.seq (r₃.seq (rb.seq rinc)))
    have hcost : 3 + (5 + (4 + (radixBlockCost bits m + 4))) ≤
        radixCoverTurnCost bits Xoff k := by
      simp [radixCoverTurnCost, m]
      omega
    simpa only [radixCoverTurn] using hrun.mono hcost
  · refine ⟨⟨?_, ?_, ?_, ?_, ?_, Xn, Qn, ?_, ?_, hmemn, ?_, ?_⟩, ?_⟩
    · simp [σ']
      omega
    · simp [σ', hbqn]
    · simp [σ', hbbits]
    · simp [σ', hbxoff]
    · simp [σ', hbasg]
    · simp [σ', hbxmem]
    · simp [σ', hbq]
    · intro j hj
      exact hdone' j (by simpa [σ'] using hj)
    · intro p hp hp'
      exact hsuffix' p (by simpa [σ'] using hp) hp'
    · simp [σ']

/-! ## Complete arena sort -/

/-- The outer loop turns the raw active cover into the exact sorted
consumer contract. -/
theorem radixCoverCom_spec {B bits : ℕ} {Q₀ : ℕ → ℕ}
    (hraw : RawCoverOutA G A₀ π centre r q xp Xoff Xmem asg)
    (hB : 1 < B) (hnB : n < B) (hnnB : n * n < B) (hbitsB : bits < B)
    (hpow : n ≤ 2 ^ bits) :
    Spec B
      (fun σ => σ.vars "qn" = q ∧
        σ.arrs "xoff" = arrOf (n + 1) Xoff ∧
        σ.arrs "xmem" = arrOf (n * n) Xmem ∧
        σ.arrs "asg" = arrOf n asg ∧ σ.arrs "q" = arrOf n Q₀)
      (radixCoverCom bits)
      (fun _ σ' => ∃ Xmem' Q : ℕ → ℕ,
        σ'.arrs "xoff" = arrOf (n + 1) Xoff ∧
        σ'.arrs "xmem" = arrOf (n * n) Xmem' ∧
        σ'.arrs "asg" = arrOf n asg ∧ σ'.arrs "q" = arrOf n Q ∧
        CoverOutA G A₀ π centre r q xp Xoff Xmem' asg)
      (radixCoverCost bits q Xoff) := by
  intro σ hσ
  obtain ⟨hqn, hxoff, hxmem, hasg, hq⟩ := hσ
  let σb := σ.setVar "rsbits" bits
  have rb : Run B (.assign "rsbits" (.lit bits)) σ σb 2 :=
    Run.assign (evalB_lit hbitsB)
  let I := CoverRadixInv n q xp bits Xoff Xmem asg
  have hqB : q < B := lt_of_le_of_lt hraw.count_le hnB
  have hbody : ∀ k, k < q → Spec B (fun τ => I τ ∧ τ.vars "rsc" = k)
      radixCoverTurn (fun _ τ' => I τ' ∧ τ'.vars "rsc" = k + 1)
      (radixCoverTurnCost bits Xoff k) := by
    intro k hk
    exact radixCoverTurn_spec hraw hB hnB hnnB hbitsB hk
  have hloop := Lax3Proofs.Refine.SigmaLoop.forRangeZeroSum
    (B := B) "rsc" "qn" I q (radixCoverTurnCost bits Xoff) hqB
    (fun _ h => h.1) (fun _ h => h.2.1) hbody
  have hI₀ : I (σb.setVar "rsc" 0) := by
    refine ⟨by simp, by simp [σb, hqn], by simp [σb],
      by simp [σb, hxoff], by simp [σb, hasg], Xmem, Q₀,
      by simp [σb, hxmem], by simp [σb, hq], hraw.mem_lt, ?_, ?_⟩
    · intro k hk
      simp at hk
    · intro p hp hp'
      rfl
  obtain ⟨σ', rloop, hI', hrsc⟩ := hloop.run (show I (σb.setVar "rsc" 0) from hI₀)
  obtain ⟨-, -, -, hxoff', hasg', Xmem', Q, hxmem', hq', hmem', hdone', -⟩ := hI'
  have hdone : ∀ k < q,
      segment (Xoff k) (blockSize Xoff k) Xmem' =
        radixRounds bits (segment (Xoff k) (blockSize Xoff k) Xmem) := by
    intro k hk
    exact hdone' k (by simpa [hrsc] using hk)
  have hblock : ∀ k < q, ∀ w,
      (∃ p, Xoff k ≤ p ∧ p < Xoff (k + 1) ∧ Xmem' p = w) ↔
        (∃ p, Xoff k ≤ p ∧ p < Xoff (k + 1) ∧ Xmem p = w) := by
    intro k hk w
    have hoff := hraw.mono k hk
    rw [← mem_segment_block_iff (X := Xmem') hoff,
      ← mem_segment_block_iff (X := Xmem) hoff]
    change (w ∈ segment (Xoff k) (blockSize Xoff k) Xmem') ↔
      w ∈ segment (Xoff k) (blockSize Xoff k) Xmem
    rw [hdone k hk]
    exact mem_radixRounds_iff
  have hmono : ∀ k < q, ∀ p p', Xoff k ≤ p → p < p' →
      p' < Xoff (k + 1) → Xmem' p < Xmem' p' := by
    intro k hk
    apply pairwise_segment_to_block (hraw.mono k hk)
    change List.Pairwise (fun x y => x < y)
      (segment (Xoff k) (blockSize Xoff k) Xmem')
    rw [hdone k hk]
    apply radixRounds_strict hpow
    · intro x hx
      obtain ⟨i, hi, heq⟩ := mem_segment_iff.mp hx
      rw [← heq]
      have hiend : Xoff k + i < Xoff (k + 1) := by
        rw [← add_blockSize hraw hk]
        omega
      exact hraw.mem_lt (Xoff k + i)
        (lt_of_lt_of_le hiend (rawOff_le hraw (k := k + 1) (by omega)))
    · exact raw_segment_nodup hraw hk
  have hsorted : CoverOutA G A₀ π centre r q xp Xoff Xmem' asg :=
    hraw.sorted hmem' hblock hmono
  refine ⟨σ', ?_, Xmem', Q, hxoff', hxmem', hasg', hq', hsorted⟩
  simpa [radixCoverCom, radixCoverCost] using rb.seq rloop

/-! ## Axiom audit -/

#print axioms radixCoverTurn_spec
#print axioms radixCoverCom_spec

end Lax3Proofs.Refine.CoverActiveRadixLoop
