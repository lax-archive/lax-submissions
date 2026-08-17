import Lax3Proofs.RamDriverMemberPhases

/-!
# Block-driven batch enumeration

The landed cluster turn pads its splitter batch by scanning every carrier
vertex.  The active cover already retains an injective, increasing row for
the current cluster.  This file enumerates the same marked set by walking
that row instead.  Its cost is therefore a function of the current block
size and the formula-sized padding width, never of the carrier.
-/

namespace Lax3Proofs.Refine.ActiveEnum

open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster
open Lax3Proofs.RamDriverDescend
open Lax3Proofs.RamDriverMember
open Lax3Proofs.RamDriverClusterMember
open Lax3Proofs.RamDriverFrames
open Lax3Proofs.Refine.MassMath (blockSize clusterAt)
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-- The batch marker pulled back from vertices to positions of one block.
Positions before the block are deliberately unmarked, so
`markedBelow ... p₀` is empty and the existing counting lemmas apply at a
nonzero row offset. -/
def blockMarker (p₀ : ℕ) (Xmem Wa Xa : ℕ → ℕ) (p : ℕ) : ℕ :=
  if p₀ ≤ p then Wa (Xmem p) * Xa (Xmem p) else 0

@[simp] theorem blockMarker_of_lt {p₀ p : ℕ} (h : p < p₀) (Xmem Wa Xa : ℕ → ℕ) :
    blockMarker p₀ Xmem Wa Xa p = 0 := by
  simp [blockMarker, Nat.not_le.mpr h]

theorem blockMarker_ne_zero_iff {p₀ p : ℕ} (Xmem Wa Xa : ℕ → ℕ) :
    blockMarker p₀ Xmem Wa Xa p ≠ 0 ↔
      p₀ ≤ p ∧ Wa (Xmem p) * Xa (Xmem p) ≠ 0 := by
  by_cases h : p₀ ≤ p
  · simp [blockMarker, h]
  · simp [blockMarker, h]

/-- Before the first block position, the pulled-back marker is empty. -/
theorem ncard_markedBelow_blockMarker_start (e p₀ : ℕ) (Xmem Wa Xa : ℕ → ℕ) :
    (markedBelow e (blockMarker p₀ Xmem Wa Xa) p₀).ncard = 0 := by
  have hset : markedBelow e (blockMarker p₀ Xmem Wa Xa) p₀ = ∅ := by
    ext p
    simp only [markedBelow, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun hp => hp.2 (blockMarker_of_lt hp.1 Xmem Wa Xa)
  rw [hset, Set.ncard_empty]

/-- Injectivity of a retained cover row transfers the batch-cardinality
bound from vertices to the positions the block walk scans. -/
theorem blockMarker_ncard_le {n m e p₀ : ℕ} {Xmem Wa Xa : ℕ → ℕ}
    (he : e ≤ m)
    (hmem : ∀ p < m, Xmem p < n)
    (hinj : ∀ p p', p₀ ≤ p → p < e → p₀ ≤ p' → p' < e →
      Xmem p = Xmem p' → p = p') :
    (markSet e (blockMarker p₀ Xmem Wa Xa)).ncard ≤
      (markSet n (fun v => Wa v * Xa v)).ncard := by
  let f : Fin e → Fin n := fun p =>
    ⟨Xmem (p : ℕ), hmem (p : ℕ) (lt_of_lt_of_le p.isLt he)⟩
  have hf : Set.InjOn f (markSet e (blockMarker p₀ Xmem Wa Xa)) := by
    intro p hp p' hp' heq
    apply Fin.ext
    apply hinj (p : ℕ) (p' : ℕ)
    · exact (blockMarker_ne_zero_iff Xmem Wa Xa).mp hp |>.1
    · exact p.isLt
    · exact (blockMarker_ne_zero_iff Xmem Wa Xa).mp hp' |>.1
    · exact p'.isLt
    · exact congrArg Fin.val heq
  have hsub : f '' markSet e (blockMarker p₀ Xmem Wa Xa) ⊆
      markSet n (fun v => Wa v * Xa v) := by
    rintro v ⟨p, hp, rfl⟩
    exact (blockMarker_ne_zero_iff Xmem Wa Xa).mp hp |>.2
  calc
    (markSet e (blockMarker p₀ Xmem Wa Xa)).ncard =
        (f '' markSet e (blockMarker p₀ Xmem Wa Xa)).ncard :=
      (Set.InjOn.ncard_image hf).symm
    _ ≤ (markSet n (fun v => Wa v * Xa v)).ncard :=
      Set.ncard_le_ncard hsub (Set.toFinite _)

/-! ## Executable -/

/-- One slot of the block-driven collector. -/
def enumBlockBody (idx bat clu : String) : Com :=
  .seq (.assign "z" (.get idx (.var "p")))
    (.seq
      (.ite (.lt (.lit 0) (.mul (.get bat (.var "z")) (.get clu (.var "z"))))
        (.seq (.store "wa" (.var "bc") (.var "z"))
          (.assign "bc" (.add (.var "bc") (.lit 1))))
        .skip)
      (.assign "p" (.add (.var "p") (.lit 1))))

/-- Enumerate the batch through the current retained-cover row and pad it
to `mb`, exactly as the landed `enumBatch` pads its carrier enumeration. -/
def enumBlockCom (j mb : ℕ) : Com :=
  .seq (.assign "bc" (.lit 0))
    (.seq (Csr.loadRow (xofName j) (curName j) "p" "pend")
      (.seq (.while (.lt (.var "p") (.var "pend"))
          (enumBlockBody (xmmName j) (batName j) (cluName j)))
        (.seq (.assign "k" (.var "bc"))
          (.while (.lt (.var "k") (.lit mb))
            (.seq (.store "wa" (.var "k") (.get "wa" (.lit 0)))
              (.assign "k" (.add (.var "k") (.lit 1))))))))

/-- The intended affine charge of the block collector and formula-sized
padding.  Slack is deliberate: the semantic gate is the important part of
this leaf, and the final turn coefficient absorbs constants. -/
def enumBlockCost (bs mb : ℕ) : ℕ := 30 * bs + 12 * mb + 40

/-! ## The collecting loop -/

/-- What the block collector has produced before position `p`.  The
buffer stores vertices, while the counting set is over injective cover
positions. -/
def BlockCollectAt (n m e p₀ mb : ℕ) (Xmem Wa Xa : ℕ → ℕ)
    (idx bat clu : String) (p : ℕ) ( σ : Env) : Prop :=
  σ.arrs idx = arrOf m Xmem ∧ σ.arrs bat = arrOf n Wa ∧
    σ.arrs clu = arrOf n Xa ∧
    σ.vars "bc" ≤ (markedBelow e (blockMarker p₀ Xmem Wa Xa) p).ncard ∧
    ∃ E : ℕ → ℕ, σ.arrs "wa" = arrOf mb E ∧
      (∀ i, i < σ.vars "bc" → E i < n ∧ Wa (E i) * Xa (E i) ≠ 0) ∧
      (∀ q, p₀ ≤ q → q < p → Wa (Xmem q) * Xa (Xmem q) ≠ 0 →
        ∃ i, i < σ.vars "bc" ∧ E i = Xmem q)

/-- The interval collector carries both loaded row bounds. -/
def BlockCollectInv (n m e p₀ mb : ℕ) (Xmem Wa Xa : ℕ → ℕ)
    (idx bat clu : String) (σ : Env) : Prop :=
  p₀ ≤ σ.vars "p" ∧ σ.vars "p" ≤ e ∧ σ.vars "pend" = e ∧
    BlockCollectAt n m e p₀ mb Xmem Wa Xa idx bat clu (σ.vars "p") σ

/-- One retained-cover position is read, tested at its vertex, and
appended when both masks mark it. -/
theorem enumBlockBody_spec (B n m e p₀ mb : ℕ) (Xmem Wa Xa : ℕ → ℕ)
    (idx bat clu : String) (hidx : idx ≠ "wa") (hbat : bat ≠ "wa")
    (hclu : clu ≠ "wa") (heM : e ≤ m) (heB : e < B) (hB : 1 < B) (hnB : n < B)
    (hmbB : mb < B)
    (hmem : ∀ q, p₀ ≤ q → q < e → Xmem q < n)
    (hcard : (markSet e (blockMarker p₀ Xmem Wa Xa)).ncard ≤ mb)
    (hWB : ∀ v, v < n → Wa v < B) (hX1 : ∀ v, v < n → Xa v ≤ 1) :
    Spec B
      (fun σ => BlockCollectInv n m e p₀ mb Xmem Wa Xa idx bat clu σ ∧
        σ.vars "p" < e)
      (enumBlockBody idx bat clu)
      (fun σ σ' => BlockCollectInv n m e p₀ mb Xmem Wa Xa idx bat clu σ' ∧
        σ'.vars "p" = σ.vars "p" + 1) 22 := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨⟨hp₀, hpe, hpend, hidxσ, hbatσ, hcluσ, hbc, E, hwa, hlt, hcov⟩, hp⟩ := hσ
  have hpM : σ.vars "p" < m := lt_of_lt_of_le hp heM
  have hpB : σ.vars "p" < B := lt_trans hp heB
  have hxpn : Xmem (σ.vars "p") < n := hmem _ hp₀ hp
  have hxpB : Xmem (σ.vars "p") < B := lt_trans hxpn hnB
  have hget : (Expr.get idx (.var "p")).evalB B σ = some (Xmem (σ.vars "p")) :=
    evalB_get (evalB_var hpB) (by rw [hidxσ, getElem?_arrOf Xmem hpM]) hxpB
  let ρ := σ.setVar "z" (Xmem (σ.vars "p"))
  have hrz : Run B (.assign "z" (.get idx (.var "p"))) σ ρ 3 :=
    (Run.assign hget).mono (by simp)
  have hzρ : ρ.vars "z" = Xmem (σ.vars "p") := by simp [ρ]
  have hpρ : ρ.vars "p" = σ.vars "p" := by simp [ρ]
  have hbatρ : ρ.arrs bat = arrOf n Wa := by simpa [ρ] using hbatσ
  have hcluρ : ρ.arrs clu = arrOf n Xa := by simpa [ρ] using hcluσ
  have hWaB : Wa (Xmem (σ.vars "p")) < B := hWB _ hxpn
  have hXa1 : Xa (Xmem (σ.vars "p")) ≤ 1 := hX1 _ hxpn
  have hprodB : Wa (Xmem (σ.vars "p")) * Xa (Xmem (σ.vars "p")) < B :=
    lt_of_le_of_lt (le_trans (Nat.mul_le_mul_left _ hXa1) (by omega)) hWaB
  have hcond : (Cond.lt (.lit 0)
      (.mul (.get bat (.var "z")) (.get clu (.var "z")))).evalB B ρ =
      some (decide (0 < Wa (Xmem (σ.vars "p")) * Xa (Xmem (σ.vars "p")))) := by
    refine evalB_condLt (evalB_lit (by omega)) (evalB_bin ?_ ?_ ?_)
    · exact evalB_get (evalB_var (by rw [hzρ]; exact hxpB))
        (by rw [hbatρ, hzρ, getElem?_arrOf Wa hxpn]) hWaB
    · exact evalB_get (evalB_var (by rw [hzρ]; exact hxpB))
        (by rw [hcluρ, hzρ, getElem?_arrOf Xa hxpn]) (by omega)
    · simpa only [Bop.apply_mul] using hprodB
  by_cases hm : Wa (Xmem (σ.vars "p")) * Xa (Xmem (σ.vars "p")) = 0
  · let τ := ρ.setVar "p" (σ.vars "p" + 1)
    have hpτ : τ.vars "p" = σ.vars "p" + 1 := by simp [τ]
    have hbcτ : τ.vars "bc" = σ.vars "bc" := by simp [τ, ρ]
    have hmark : blockMarker p₀ Xmem Wa Xa (σ.vars "p") = 0 := by
      simp [blockMarker, hp₀, hm]
    have hpadd : (.add (.var "p") (.lit 1) : Expr).evalB B ρ =
        some (σ.vars "p" + 1) :=
      evalB_bin (evalB_var (by rw [hpρ]; exact hpB)) (evalB_lit (by omega))
        (by simp only [Bop.apply_add]; omega)
    have hrbranch : Run B
        (.seq (.ite (.lt (.lit 0) (.mul (.get bat (.var "z")) (.get clu (.var "z"))))
          (.seq (.store "wa" (.var "bc") (.var "z"))
            (.assign "bc" (.add (.var "bc") (.lit 1)))) .skip)
          (.assign "p" (.add (.var "p") (.lit 1)))) ρ τ 13 :=
      ((Run.ite_false (by rw [hcond, hm]; simp) Run.skip).seq
        (Run.assign hpadd)).mono (by simp)
    refine ⟨τ, 22, ?_, le_rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, E, ?_, ?_, ?_⟩, hpτ⟩
    · simpa [enumBlockBody] using (hrz.seq hrbranch).mono (by omega)
    · rw [hpτ]; omega
    · rw [hpτ]; omega
    · simpa [τ, ρ] using hpend
    · simpa [τ, ρ] using hidxσ
    · simpa [τ, ρ] using hbatσ
    · simpa [τ, ρ] using hcluσ
    · rw [hbcτ, hpτ, markedBelow_succ_of_unmarked hmark]
      exact hbc
    · simpa [τ, ρ] using hwa
    · intro i hi
      rw [hbcτ] at hi
      exact hlt i hi
    · intro q hq₀ hq hwq
      rw [hpτ] at hq
      by_cases hqp : q = σ.vars "p"
      · subst q
        exact False.elim (hwq hm)
      · exact hcov q hq₀ (by omega) hwq
  · have hmark : blockMarker p₀ Xmem Wa Xa (σ.vars "p") ≠ 0 :=
      (blockMarker_ne_zero_iff Xmem Wa Xa).2 ⟨hp₀, hm⟩
    have hbclt : σ.vars "bc" < mb :=
      count_lt_of_mark (n := e) hp hmark hbc hcard
    have hwalen : σ.vars "bc" < (ρ.arrs "wa").length := by
      rw [show ρ.arrs "wa" = σ.arrs "wa" by simp [ρ], hwa, length_arrOf]
      exact hbclt
    let ρw := ρ.setArr "wa" (σ.vars "bc") (Xmem (σ.vars "p"))
    let ρb := ρw.setVar "bc" (σ.vars "bc" + 1)
    let τ := ρb.setVar "p" (σ.vars "p" + 1)
    have hpτ : τ.vars "p" = σ.vars "p" + 1 := by simp [τ]
    have hbcτ : τ.vars "bc" = σ.vars "bc" + 1 := by simp [τ, ρb]
    have hwaτ : τ.arrs "wa" =
        arrOf mb (upd E (σ.vars "bc") (Xmem (σ.vars "p"))) := by
      simp [τ, ρb, ρw, ρ, hwa, set_arrOf_eq_upd]
    have htrue : (Cond.lt (.lit 0)
        (.mul (.get bat (.var "z")) (.get clu (.var "z")))).evalB B ρ = some true := by
      rw [hcond]
      simp [Nat.pos_of_ne_zero hm]
    have hbcB : ρ.vars "bc" < B := by simp [ρ]; omega
    have hbcadd : (.add (.var "bc") (.lit 1) : Expr).evalB B ρw =
        some (σ.vars "bc" + 1) := by
      refine evalB_bin (evalB_var ?_) (evalB_lit (by omega)) ?_
      · simpa [ρw, ρ] using hbcB
      · simp only [Bop.apply_add]
        omega
    have hpadd : (.add (.var "p") (.lit 1) : Expr).evalB B ρb =
        some (σ.vars "p" + 1) := by
      refine evalB_bin (evalB_var ?_) (evalB_lit (by omega)) ?_
      · simpa [ρb, ρw, ρ] using hpB
      · simp only [Bop.apply_add]
        omega
    have hrbranch : Run B
        (.seq (.ite (.lt (.lit 0) (.mul (.get bat (.var "z")) (.get clu (.var "z"))))
          (.seq (.store "wa" (.var "bc") (.var "z"))
            (.assign "bc" (.add (.var "bc") (.lit 1)))) .skip)
          (.assign "p" (.add (.var "p") (.lit 1)))) ρ τ 19 := by
      refine ((Run.ite_true htrue
        ((Run.store (evalB_var hbcB) (evalB_var (by rw [hzρ]; exact hxpB)) hwalen).seq
          (Run.assign hbcadd))).seq (Run.assign hpadd)).mono ?_
      simp
    refine ⟨τ, 22, ?_, le_rfl, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
      upd E (σ.vars "bc") (Xmem (σ.vars "p")), hwaτ, ?_, ?_⟩, hpτ⟩
    · simpa [enumBlockBody] using hrz.seq hrbranch
    · rw [hpτ]; omega
    · rw [hpτ]; omega
    · simpa [τ, ρb, ρw, ρ] using hpend
    · simp only [τ, ρb, ρw, arrs_setVar, arrs_setArr, if_neg hidx]
      simpa [ρ] using hidxσ
    · simp only [τ, ρb, ρw, arrs_setVar, arrs_setArr, if_neg hbat]
      simpa [ρ] using hbatσ
    · simp only [τ, ρb, ρw, arrs_setVar, arrs_setArr, if_neg hclu]
      simpa [ρ] using hcluσ
    · rw [hbcτ, hpτ, ncard_markedBelow_succ_of_mark hp hmark]
      omega
    · intro i hi
      rw [hbcτ] at hi
      by_cases hie : i = σ.vars "bc"
      · subst i
        rw [upd_self]
        exact ⟨hxpn, hm⟩
      · rw [upd_of_ne _ hie]
        exact hlt i (by omega)
    · intro q hq₀ hq hwq
      rw [hpτ] at hq
      by_cases hqp : q = σ.vars "p"
      · subst q
        exact ⟨σ.vars "bc", by rw [hbcτ]; omega, by rw [upd_self]⟩
      · obtain ⟨i, hi, hEi⟩ := hcov q hq₀ (by omega) hwq
        exact ⟨i, by rw [hbcτ]; omega, by rw [upd_of_ne _ (by omega), hEi]⟩

/-- The collector traverses exactly the loaded cover interval.  The
coefficient `30` pays the 22-step body and the loop guard with slack. -/
theorem enumBlockLoop_spec (B n m e p₀ mb : ℕ) (Xmem Wa Xa : ℕ → ℕ)
    (idx bat clu : String) (hidx : idx ≠ "wa") (hbat : bat ≠ "wa")
    (hclu : clu ≠ "wa") (heM : e ≤ m) (heB : e < B) (hB : 1 < B)
    (hnB : n < B) (hmbB : mb < B)
    (hmem : ∀ q, p₀ ≤ q → q < e → Xmem q < n)
    (hcard : (markSet e (blockMarker p₀ Xmem Wa Xa)).ncard ≤ mb)
    (hWB : ∀ v, v < n → Wa v < B) (hX1 : ∀ v, v < n → Xa v ≤ 1) :
    Spec B (BlockCollectInv n m e p₀ mb Xmem Wa Xa idx bat clu)
      (.while (.lt (.var "p") (.var "pend")) (enumBlockBody idx bat clu))
      (fun _ σ' => BlockCollectInv n m e p₀ mb Xmem Wa Xa idx bat clu σ' ∧
        σ'.vars "p" = e)
      (30 * (e - p₀) + 4) := by
  let I := BlockCollectInv n m e p₀ mb Xmem Wa Xa idx bat clu
  let Φ : Env → ℕ := fun σ => 26 * (e - σ.vars "p")
  refine ((Spec.while_potential (b := .lt (.var "p") (.var "pend"))
    (c := enumBlockBody idx bat clu) I Φ (fun σ hσ =>
      evalB_condLt_vars (by have := hσ.2.1; omega) (by rw [hσ.2.2.1]; exact heB))
    ?_ (fun _ h => h) ?_).pre (fun _ h => h)).post ?_
  · intro σ hI hb
    have hp : σ.vars "p" < e := by
      have hlt := lt_of_condLt_true hb
      rw [hI.2.2.1] at hlt
      exact hlt
    obtain ⟨σ', hr, hI', hp'⟩ :=
      (enumBlockBody_spec B n m e p₀ mb Xmem Wa Xa idx bat clu hidx hbat hclu
        heM heB hB hnB hmbB hmem hcard hWB hX1).run ⟨hI, hp⟩
    refine ⟨σ', 22, hr, hI', ?_⟩
    change 1 + (Cond.lt (Expr.var "p") (Expr.var "pend")).size + 22 + Φ σ' ≤ Φ σ
    simp only [Cond.size, Expr.size, Φ]
    rw [hp']
    omega
  · intro σ hI
    have hsub : e - σ.vars "p" ≤ e - p₀ := Nat.sub_le_sub_left hI.1 e
    have hmul := Nat.mul_le_mul_left 26 hsub
    change Φ σ + 1 + (Cond.lt (Expr.var "p") (Expr.var "pend")).size ≤
      30 * (e - p₀) + 4
    simp only [Cond.size, Expr.size, Φ]
    omega
  · intro σ σ' _ hpost
    refine ⟨hpost.1, ?_⟩
    have hge := le_of_condLt_false hpost.2
    have hle := hpost.1.2.1
    have heq := hpost.1.2.2.1
    omega

/-! ## Padding -/

/-- Padding preserves the collected interval coverage while repeating
the first collected vertex to the fixed formula width. -/
def BlockPadInv (n mb bc v₀ p₀ e : ℕ) (Xmem Mark : ℕ → ℕ) (σ : Env) : Prop :=
  bc ≤ σ.vars "k" ∧ σ.vars "k" ≤ mb ∧
    ∃ E : ℕ → ℕ, σ.arrs "wa" = arrOf mb E ∧ E 0 = v₀ ∧
      (∀ i, i < σ.vars "k" → E i < n ∧ Mark (E i) ≠ 0) ∧
      (∀ q, p₀ ≤ q → q < e → Mark (Xmem q) ≠ 0 →
        ∃ i, i < bc ∧ E i = Xmem q)

/-- One padding write, with interval coverage framed. -/
theorem enumBlockPadBody_spec (B n mb bc v₀ p₀ e : ℕ) (Xmem Mark : ℕ → ℕ)
    (hB : 1 < B) (hnB : n < B) (hmbB : mb < B) (hbcpos : 1 ≤ bc) :
    Spec B (fun σ => BlockPadInv n mb bc v₀ p₀ e Xmem Mark σ ∧
        (Cond.lt (.var "k") (.lit mb)).evalB B σ = some true)
      (.seq (.store "wa" (.var "k") (.get "wa" (.lit 0)))
        (.assign "k" (.add (.var "k") (.lit 1))))
      (fun σ σ' => BlockPadInv n mb bc v₀ p₀ e Xmem Mark σ' ∧
        mb - σ'.vars "k" < mb - σ.vars "k") 8 := by
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨⟨hkbc, hkmb, E, hwa, hE0, hlt, hcov⟩, hcond⟩ := hσ
  have hkB : σ.vars "k" < B := by omega
  have hk : σ.vars "k" < mb := by
    rw [evalB_condLt (evalB_var hkB) (evalB_lit hmbB)] at hcond
    simpa using hcond
  have hE0n : E 0 < n := (hlt 0 (by omega)).1
  have hE0B : E 0 < B := lt_trans hE0n hnB
  have hget : (Expr.get "wa" (.lit 0)).evalB B σ = some (E 0) :=
    evalB_get (evalB_lit (by omega)) (by rw [hwa, getElem?_arrOf E (by omega)]) hE0B
  have hwalen : σ.vars "k" < (σ.arrs "wa").length := by
    rw [hwa, length_arrOf]
    exact hk
  let ρ := σ.setArr "wa" (σ.vars "k") (E 0)
  let τ := ρ.setVar "k" (σ.vars "k" + 1)
  have hkτ : τ.vars "k" = σ.vars "k" + 1 := by simp [τ]
  have hwaτ : τ.arrs "wa" = arrOf mb (upd E (σ.vars "k") (E 0)) := by
    simp [τ, ρ, hwa, set_arrOf_eq_upd]
  have hkadd : (.add (.var "k") (.lit 1) : Expr).evalB B ρ =
      some (σ.vars "k" + 1) := by
    refine evalB_bin (evalB_var ?_) (evalB_lit (by omega)) ?_
    · simpa using hkB
    · simp only [Bop.apply_add]
      omega
  refine ⟨τ, 8, ((Run.store (evalB_var hkB) hget hwalen).seq
      (Run.assign hkadd)).mono (by simp), le_rfl,
    ⟨?_, ?_, upd E (σ.vars "k") (E 0), hwaτ, ?_, ?_, ?_⟩, ?_⟩
  · rw [hkτ]
    omega
  · rw [hkτ]
    omega
  · rw [upd_of_ne _ (by omega), hE0]
  · intro i hi
    rw [hkτ] at hi
    by_cases hie : i = σ.vars "k"
    · subst i
      rw [upd_self]
      exact ⟨hE0n, (hlt 0 (by omega)).2⟩
    · rw [upd_of_ne _ hie]
      exact hlt i (by omega)
  · intro q hq₀ hqe hq
    obtain ⟨i, hi, hEi⟩ := hcov q hq₀ hqe hq
    exact ⟨i, hi, by rw [upd_of_ne _ (by omega), hEi]⟩
  · rw [hkτ]
    omega

/-- The complete padding loop. -/
theorem enumBlockPadLoop_spec (B n mb bc v₀ p₀ e : ℕ) (Xmem Mark : ℕ → ℕ)
    (hB : 1 < B) (hnB : n < B) (hmbB : mb < B) (hbcpos : 1 ≤ bc) :
    Spec B (BlockPadInv n mb bc v₀ p₀ e Xmem Mark)
      (.while (.lt (.var "k") (.lit mb))
        (.seq (.store "wa" (.var "k") (.get "wa" (.lit 0)))
          (.assign "k" (.add (.var "k") (.lit 1)))))
      (fun _ σ' => BlockPadInv n mb bc v₀ p₀ e Xmem Mark σ' ∧
        σ'.vars "k" = mb) (12 * mb + 4) := by
  refine (Spec.while_count (B := B)
    (P := BlockPadInv n mb bc v₀ p₀ e Xmem Mark) (K := 12 * mb + 4)
    (BlockPadInv n mb bc v₀ p₀ e Xmem Mark) (fun σ => mb - σ.vars "k") 8
    (fun σ hσ => evalB_condLt_var_lit (by have := hσ.2.1; omega) hmbB)
    (enumBlockPadBody_spec B n mb bc v₀ p₀ e Xmem Mark hB hnB hmbB hbcpos)
    (fun _ hσ => hσ) ?_).post ?_
  · intro σ _
    have hmul : 12 * (mb - σ.vars "k") ≤ 12 * mb :=
      Nat.mul_le_mul_left 12 (Nat.sub_le mb (σ.vars "k"))
    simp only [size_condLt, size_var, size_lit]
    omega
  · intro σ σ' _ hpost
    refine ⟨hpost.1, ?_⟩
    have hkmb : σ'.vars "k" ≤ mb := hpost.1.2.1
    have hkB : σ'.vars "k" < B := by omega
    have hfalse := hpost.2
    rw [evalB_condLt (evalB_var hkB) (evalB_lit hmbB)] at hfalse
    simp only [Option.some.injEq, decide_eq_false_iff_not, not_lt] at hfalse
    omega

/-! ## Complete low-level pass -/

/-- Enumerating one loaded active-cover row produces exactly its marked
vertices, padded to `mb`.  The bound contains the row length, not `n`. -/
theorem enumBlockCom_spec {B n m w c j mb : ℕ} {Xoff Xmem Wa Xa : ℕ → ℕ}
    (hB : 1 < B) (hnB : n < B) (hmB : m < B) (hmbB : mb < B)
    (hc : c < n) (hp₀e : Xoff c ≤ Xoff (c + 1))
    (heM : Xoff (c + 1) ≤ m) (hmw : m ≤ w)
    (hmemAll : ∀ p, p < m → Xmem p < n)
    (hinj : ∀ p p', Xoff c ≤ p → p < Xoff (c + 1) →
      Xoff c ≤ p' → p' < Xoff (c + 1) → Xmem p = Xmem p' → p = p')
    (hcard : (markSet n (fun v => Wa v * Xa v)).ncard ≤ mb)
    (hne : ∃ q, Xoff c ≤ q ∧ q < Xoff (c + 1) ∧
      Wa (Xmem q) * Xa (Xmem q) ≠ 0)
    (hWB : ∀ v, v < n → Wa v < B) (hX1 : ∀ v, v < n → Xa v ≤ 1) :
    Spec B
      (fun σ => σ.arrs (xofName j) = arrOf (n + 1) Xoff ∧
        σ.arrs (xmmName j) = arrOf w Xmem ∧ σ.vars (curName j) = c ∧
        σ.arrs (batName j) = arrOf n Wa ∧ σ.arrs (cluName j) = arrOf n Xa ∧
        ∃ g, σ.arrs "wa" = arrOf mb g)
      (enumBlockCom j mb)
      (fun _ σ' => ∃ E : ℕ → ℕ, σ'.arrs "wa" = arrOf mb E ∧
        (∀ i, i < mb → E i < n ∧ Wa (E i) * Xa (E i) ≠ 0) ∧
        (∀ q, Xoff c ≤ q → q < Xoff (c + 1) →
          Wa (Xmem q) * Xa (Xmem q) ≠ 0 → ∃ i, i < mb ∧ E i = Xmem q))
      (enumBlockCost (Xoff (c + 1) - Xoff c) mb) := by
  classical
  refine Spec.of_exists (fun σ hσ => ?_)
  obtain ⟨hxoffσ, hxmemσ, hcur, hbatσ, hcluσ, g₀, hwaσ⟩ := hσ
  have heB : Xoff (c + 1) < B := lt_of_le_of_lt heM hmB
  have heW : Xoff (c + 1) ≤ w := heM.trans hmw
  have hcardBlock :
      (markSet (Xoff (c + 1)) (blockMarker (Xoff c) Xmem Wa Xa)).ncard ≤ mb :=
    (blockMarker_ncard_le heM hmemAll hinj).trans hcard
  have hidxwa : xmmName j ≠ "wa" := by simp [xmmName, String.ext_iff]
  have hbatwa : batName j ≠ "wa" := by simp [batName, String.ext_iff]
  have hcluwa : cluName j ≠ "wa" := by simp [cluName, String.ext_iff]
  let σ₀ := σ.setVar "bc" 0
  have hr₀ : Run B (.assign "bc" (.lit 0)) σ σ₀ 2 :=
    (Run.assign (evalB_lit (by omega))).mono (by simp)
  have hcur₀ : σ₀.vars (curName j) = c := by
    simpa [σ₀, curName, String.ext_iff] using hcur
  have hcB : c < B := hc.trans hnB
  have hc1B : c + 1 < B := by omega
  have hp₀B : Xoff c < B := lt_of_le_of_lt hp₀e heB
  have hxoff₀ : σ₀.arrs (xofName j) = arrOf (n + 1) Xoff := by
    simpa [σ₀] using hxoffσ
  have hcurEval₀ : (Expr.var (curName j)).evalB B σ₀ = some c := by
    have hv := evalB_var (B := B) (x := curName j) (σ := σ₀)
      (by rw [hcur₀]; exact hcB)
    rw [hcur₀] at hv
    exact hv
  have e₁ : (Expr.get (xofName j) (.var (curName j))).evalB B σ₀ = some (Xoff c) :=
    evalB_get hcurEval₀
      (by rw [hxoff₀, getElem?_arrOf Xoff (by omega)]) hp₀B
  let σp := σ₀.setVar "p" (Xoff c)
  have hcurp : σp.vars (curName j) = c := by
    rw [show σp.vars (curName j) = σ₀.vars (curName j) by
      simp [σp, curName, String.ext_iff]]
    exact hcur₀
  have hxoffp : σp.arrs (xofName j) = arrOf (n + 1) Xoff := by
    simpa [σp] using hxoff₀
  have hcurEvalp : (Expr.var (curName j)).evalB B σp = some c := by
    have hv := evalB_var (B := B) (x := curName j) (σ := σp)
      (by rw [hcurp]; exact hcB)
    rw [hcurp] at hv
    exact hv
  have haddp : (.add (.var (curName j)) (.lit 1) : Expr).evalB B σp = some (c + 1) :=
    evalB_bin hcurEvalp (evalB_lit (by omega)) (by simp only [Bop.apply_add]; omega)
  have e₂ : (Expr.get (xofName j) (.add (.var (curName j)) (.lit 1))).evalB B σp =
      some (Xoff (c + 1)) := by
    refine evalB_get haddp ?_ heB
    rw [hxoffp, getElem?_arrOf Xoff (by omega)]
  let σ₁ := σp.setVar "pend" (Xoff (c + 1))
  have hr₁ : Run B (Csr.loadRow (xofName j) (curName j) "p" "pend") σ₀ σ₁ 8 :=
    ((Run.assign e₁).seq (Run.assign e₂)).mono (by simp)
  have hp₁ : σ₁.vars "p" = Xoff c := by simp [σ₁, σp]
  have he₁ : σ₁.vars "pend" = Xoff (c + 1) := by simp [σ₁]
  have hI₁ : BlockCollectInv n w (Xoff (c + 1)) (Xoff c) mb Xmem Wa Xa
      (xmmName j) (batName j) (cluName j) σ₁ := by
    refine ⟨by rw [hp₁], by rw [hp₁]; exact hp₀e, he₁,
      ?_, ?_, ?_, ?_, g₀, ?_, ?_, ?_⟩
    · simpa [σ₁, σp, σ₀] using hxmemσ
    · simpa [σ₁, σp, σ₀] using hbatσ
    · simpa [σ₁, σp, σ₀] using hcluσ
    · have hbc₁ : σ₁.vars "bc" = 0 := by
        simp [σ₁, σp, σ₀]
      rw [hbc₁, hp₁, ncard_markedBelow_blockMarker_start]
    · simpa [σ₁, σp, σ₀] using hwaσ
    · intro i hi
      simp [σ₁, σp, σ₀] at hi
    · intro q hqc hqp _
      rw [hp₁] at hqp
      omega
  obtain ⟨σ₂, hr₂, hI₂, hp₂⟩ :=
    (enumBlockLoop_spec B n w (Xoff (c + 1)) (Xoff c) mb Xmem Wa Xa
      (xmmName j) (batName j) (cluName j) hidxwa hbatwa hcluwa heW heB hB hnB
      hmbB (fun q _ hq => hmemAll q (lt_of_lt_of_le hq heM)) hcardBlock hWB hX1).run hI₁
  obtain ⟨-, -, -, -, -, -, hbc₂, E₂, hwa₂, hlt₂, hcov₂⟩ := hI₂
  obtain ⟨q₀, hq₀c, hq₀e, hq₀m⟩ := hne
  obtain ⟨i₀, hi₀, -⟩ := hcov₂ q₀ hq₀c (by simpa [hp₂] using hq₀e) hq₀m
  have hbcpos : 1 ≤ σ₂.vars "bc" := by omega
  have hbcmb : σ₂.vars "bc" ≤ mb :=
    le_trans hbc₂ (le_trans
      (Set.ncard_le_ncard (markedBelow_subset (Xoff (c + 1)) _ _) (Set.toFinite _))
      hcardBlock)
  let σ₃ := σ₂.setVar "k" (σ₂.vars "bc")
  have hr₃ : Run B (.assign "k" (.var "bc")) σ₂ σ₃ 2 :=
    (Run.assign (evalB_var (by omega))).mono (by simp)
  have hk₃ : σ₃.vars "k" = σ₂.vars "bc" := by simp [σ₃]
  have hP₃ : BlockPadInv n mb (σ₂.vars "bc") (E₂ 0) (Xoff c) (Xoff (c + 1))
      Xmem (fun v => Wa v * Xa v) σ₃ := by
    refine ⟨by rw [hk₃], by rw [hk₃]; exact hbcmb, E₂,
      by simpa [σ₃] using hwa₂, rfl, ?_, ?_⟩
    · intro i hi
      rw [hk₃] at hi
      exact hlt₂ i hi
    · intro q hqc hqe hqm
      obtain ⟨i, hi, hEi⟩ := hcov₂ q hqc (by simpa [hp₂] using hqe) hqm
      exact ⟨i, hi, hEi⟩
  obtain ⟨σ₄, hr₄, hP₄, hk₄⟩ :=
    (enumBlockPadLoop_spec B n mb (σ₂.vars "bc") (E₂ 0) (Xoff c)
      (Xoff (c + 1)) Xmem (fun v => Wa v * Xa v) hB hnB hmbB hbcpos).run hP₃
  obtain ⟨-, -, E₄, hwa₄, -, hlt₄, hcov₄⟩ := hP₄
  rw [hk₄] at hlt₄
  refine ⟨σ₄,
    2 + (8 + ((30 * (Xoff (c + 1) - Xoff c) + 4) + (2 + (12 * mb + 4)))),
    hr₀.seq (hr₁.seq (hr₂.seq (hr₃.seq hr₄))), ?_, E₄, hwa₄, hlt₄, ?_⟩
  · simp only [enumBlockCost]
    omega
  · intro q hqc hqe hqm
    obtain ⟨i, hi, hEi⟩ := hcov₄ q hqc hqe hqm
    exact ⟨i, by omega, hEi⟩

/-! ## Frames -/

theorem not_mem_wvars_enumBlockCom {j mb : ℕ} {y : String}
    (hbc : y ≠ "bc") (hp : y ≠ "p") (he : y ≠ "pend")
    (hz : y ≠ "z") (hk : y ≠ "k") : y ∉ (enumBlockCom j mb).wvars := by
  simp [enumBlockCom, enumBlockBody, Csr.loadRow, Com.wvars, hbc, hp, he, hz, hk]

theorem not_mem_warrs_enumBlockCom {j mb : ℕ} {a : String} (h : a ≠ "wa") :
    a ∉ (enumBlockCom j mb).warrs := by
  simp [enumBlockCom, enumBlockBody, Csr.loadRow, Com.warrs, h]

theorem noWrite_enumBlockCom (j mb : ℕ) : (enumBlockCom j mb).NoWrite := by
  simp [enumBlockCom, enumBlockBody, Csr.loadRow, Com.NoWrite]

/-! ## Active-driver adapter -/

/-- The active cluster contract for the block enumerator.  The two
additional clauses relative to the carrier enumerator are exactly what
the sparse walk uses: the current active row is named by `k`, and `X`
is contained in that row's mathematical cluster. -/
def EnumBlockStepA {n : ℕ} (B q cap mb ns Ws j : ℕ) (G : SimpleGraph (Fin n))
    (O T M Gm : ℕ → ℕ) (C : ℕ → ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre Xoff Xmem asg : ℕ → ℕ) (m k : ℕ) (X W : Set (Fin n))
    (Alv' Gam' : ℕ → ℕ) (K : ℕ) : Prop :=
  Spec B (fun σ => TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
      Xoff Xmem asg m σ ∧ σ.vars (curName j) = k ∧
      BatchData n j B G M X W Alv' Gam' σ ∧
      PlayRec B cap G (j + 1) Alv' Gam' σ ∧ (W ∩ X).Nonempty ∧
      W.ncard ≤ mb ∧ (∀ v : Fin n, v ∈ X → v ∈ clusterAt G M π centre cap k) ∧
      ∃ g, σ.arrs "wa" = arrOf mb g)
    (enumBlockCom j mb)
    (fun σ σ' => TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
        Xoff Xmem asg m σ' ∧ PlayRec B cap G (j + 1) Alv' Gam' σ' ∧
      σ'.out = σ.out ∧ σ'.vars (curName j) = σ.vars (curName j) ∧
      ∃ w : Fin mb → Fin n, ClusterData n mb j B G M X W w Alv' Gam' σ' ∧
        ClusterWa mb w σ') K

/-- The retained active-cover row discharges the block enumerator. -/
theorem enumBlockStepA {n B q cap mb ns Ws j k K : ℕ} {G : SimpleGraph (Fin n)}
    {O T M Gm : ℕ → ℕ} {C : ℕ → ℕ → ℕ} {π : Equiv.Perm (Fin n)}
    {centre Xoff Xmem asg : ℕ → ℕ} {m : ℕ} {X W : Set (Fin n)}
    {Alv' Gam' : ℕ → ℕ} {d : ℕ} (hk : k < q)
    (hB : WordBoundK B n d ns cap mb)
    (hK : enumBlockCost (blockSize Xoff k) mb ≤ K) :
    EnumBlockStepA B q cap mb ns Ws j G O T M Gm C π centre Xoff Xmem asg m k
      X W Alv' Gam' K := by
  intro σ hσ
  obtain ⟨⟨hlev, hplayrec, hheld⟩, hcur, hbat, hplay', hne, hcard, hXcl,
      ⟨gwa, hwa⟩⟩ := hσ
  obtain ⟨Xa, hXaarr, hXs, hXa1⟩ := hbat.1
  obtain ⟨Wa, hWaarr, hWs, hWaB⟩ := hbat.2.1
  have hbatwa : batName j ≠ "wa" := by simp [batName, String.ext_iff]
  have hkn : k < n := lt_of_lt_of_le hk hheld.cover.count_le
  have hoffle : ∀ t ≤ q, Xoff t ≤ m := by
    intro t ht
    have key : ∀ r t, t + r = q → Xoff t ≤ Xoff q := by
      intro r
      induction r with
      | zero =>
          intro u hu
          rw [show u = q by omega]
      | succ r ihr =>
          intro u hu
          exact (hheld.cover.mono u (by omega)).trans (ihr (u + 1) (by omega))
    rw [← hheld.cover.last]
    exact key (q - t) t (by omega)
  have heM : Xoff (k + 1) ≤ m := hoffle (k + 1) (by omega)
  have hprod : markSet n (fun v => Wa v * Xa v) = W ∩ X := by
    ext v
    show Wa (v : ℕ) * Xa (v : ℕ) ≠ 0 ↔ _
    rw [← hWs, ← hXs]
    exact ⟨fun h => ⟨fun hc => h (by rw [hc]; ring),
        fun hc => h (by rw [hc]; ring)⟩,
      fun h => Nat.mul_ne_zero h.1 h.2⟩
  have hprodCard : (markSet n (fun v => Wa v * Xa v)).ncard ≤ mb := by
    rw [hprod]
    exact (Set.ncard_le_ncard Set.inter_subset_left (Set.toFinite _)).trans hcard
  have hrowne : ∃ p, Xoff k ≤ p ∧ p < Xoff (k + 1) ∧
      Wa (Xmem p) * Xa (Xmem p) ≠ 0 := by
    obtain ⟨v, hvW, hvX⟩ := hne
    have hvprod : Wa (v : ℕ) * Xa (v : ℕ) ≠ 0 := by
      apply Nat.mul_ne_zero
      · change v ∈ markSet n Wa
        rw [hWs]
        exact hvW
      · change v ∈ markSet n Xa
        rw [hXs]
        exact hvX
    obtain ⟨p, hp₀, hpe, hpv⟩ :=
      (hheld.cover.block k hk (v : ℕ)).mpr (hXcl v hvX)
    exact ⟨p, hp₀, hpe, by simpa [hpv] using hvprod⟩
  obtain ⟨σ', hr, ⟨E, hwa', hltE, hcovE⟩, hfv, hfa, -, hout⟩ :=
    ((enumBlockCom_spec (B := B) (n := n) (m := m) (w := n * n) (c := k)
      (j := j) (mb := mb) hB.one_lt hB.n_lt hheld.pointer_lt hB.mb_lt hkn
      (hheld.cover.mono k hk) heM hheld.alloc hheld.cover.mem_lt
      (hheld.cover.block_inj k hk) hprodCard hrowne hWaB hXa1).frame).run
      ⟨hheld.off_arr, hheld.mem_arr, hcur, hWaarr, hXaarr, gwa, hwa⟩
  have hav : ∀ a : String, a ≠ "wa" → σ'.arrs a = σ.arrs a :=
    fun a ha => hfa a (not_mem_warrs_enumBlockCom ha)
  have hvv : ∀ y : String, y ≠ "bc" → y ≠ "p" → y ≠ "pend" →
      y ≠ "z" → y ≠ "k" → σ'.vars y = σ.vars y :=
    fun y hbc hp he hz hkv => hfv y (not_mem_wvars_enumBlockCom hbc hp he hz hkv)
  have hturn' : TurnPreA B n q cap mb ns Ws j G O T M Gm C π centre
      Xoff Xmem asg m σ' := by
    refine ⟨levelPre_congr hlev hr
        (hvv "n" (by decide) (by decide) (by decide) (by decide) (by decide))
        (hvv "m" (by decide) (by decide) (by decide) (by decide) (by decide))
        (hvv "lw" (by decide) (by decide) (by decide) (by decide) (by decide))
        (hav "off" (by decide)) (hav "tgt" (by decide))
        (hav _ (by simp [alvName, String.ext_iff]))
        (hav _ (by simp [gamName, String.ext_iff]))
        (fun c' _ => hav _ (by simp [colName, String.ext_iff]))
        (fun a ha => hav a (by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
          rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
        (hav _ (by simp [memName, String.ext_iff]))
        (hvv _ (by simp [mnumName, String.ext_iff])
          (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff])
          (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff])),
      hplayrec.congr
        (fun a _ => hvv (ctrName a) (by simp [ctrName, String.ext_iff])
          (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff])
          (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff]))
        (fun a _ => hav (resName a) (by simp [resName, String.ext_iff]))
        (fun a _ => hav (gamName a) (by simp [gamName, String.ext_iff]))
        (fun a _ => hav (parName a) (by simp [parName, balName, String.ext_iff])),
      hheld.congr (hav _ (by simp [ordName, String.ext_iff]))
        (hav _ (by simp [xofName, String.ext_iff]))
        (hav _ (by simp [xmmName, String.ext_iff]))
        (hav _ (by simp [asgName, String.ext_iff]))
        (hvv _ (by simp [xpName, String.ext_iff]) (by simp [xpName, String.ext_iff])
          (by simp [xpName, String.ext_iff]) (by simp [xpName, String.ext_iff])
          (by simp [xpName, String.ext_iff]))⟩
  have hplay'' : PlayRec B cap G (j + 1) Alv' Gam' σ' :=
    hplay'.congr
      (fun a _ => hvv (ctrName a) (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff])
        (by simp [ctrName, String.ext_iff]) (by simp [ctrName, String.ext_iff]))
      (fun a _ => hav (resName a) (by simp [resName, String.ext_iff]))
      (fun a _ => hav (gamName a) (by simp [gamName, String.ext_iff]))
      (fun a _ => hav (parName a) (by simp [parName, balName, String.ext_iff]))
  refine ⟨σ', hr.mono hK, hturn', hplay'', hout (noWrite_enumBlockCom j mb),
    hvv _ (by simp [curName, String.ext_iff]) (by simp [curName, String.ext_iff])
      (by simp [curName, String.ext_iff]) (by simp [curName, String.ext_iff])
      (by simp [curName, String.ext_iff]),
    fun i => ⟨E (i : ℕ), (hltE (i : ℕ) i.isLt).1⟩, ⟨?_, ?_⟩, ?_⟩
  · exact RamDriverDescend.batchData_congr hbat
      (hav _ (by simp [cluName, String.ext_iff])) (hav _ hbatwa)
      (hav _ (by simp [resName, String.ext_iff]))
      (hav _ (by simp [alvName, String.ext_iff]))
      (hav _ (by simp [gamName, String.ext_iff]))
      (hav _ (by simp [memName, String.ext_iff]))
      (hvv _ (by simp [mnumName, String.ext_iff])
        (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff])
        (by simp [mnumName, String.ext_iff]) (by simp [mnumName, String.ext_iff]))
  · apply Set.eq_of_subset_of_subset
    · rintro v ⟨i, rfl⟩
      rw [← hprod]
      exact (hltE (i : ℕ) i.isLt).2
    · intro v hv
      have hvX : v ∈ X := hv.2
      obtain ⟨p, hp₀, hpe, hpv⟩ :=
        (hheld.cover.block k hk (v : ℕ)).mpr (hXcl v hvX)
      have hvprod : Wa (v : ℕ) * Xa (v : ℕ) ≠ 0 := by
        apply Nat.mul_ne_zero
        · change v ∈ markSet n Wa
          rw [hWs]
          exact hv.1
        · change v ∈ markSet n Xa
          rw [hXs]
          exact hv.2
      obtain ⟨i, hi, hEi⟩ := hcovE p hp₀ hpe (by simpa [hpv] using hvprod)
      refine ⟨⟨i, hi⟩, Fin.ext ?_⟩
      change E i = (v : ℕ)
      exact hEi.trans hpv
  · rw [ClusterWa, hwa']
    exact arrOf_congr (fun i hi => by rw [dif_pos hi])

#print axioms enumBlockCom_spec
#print axioms enumBlockStepA

end Lax3Proofs.Refine.ActiveEnum
