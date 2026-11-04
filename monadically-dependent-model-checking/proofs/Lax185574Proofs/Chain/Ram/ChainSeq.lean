import Lax185574Proofs.Chain.Ram.DampLoop

/-!
The damping sequence `V, damp V, damp (damp V), …` until the empty set.

`dIter i` is the `i`-th set of the sequence and `dLen` the index of the
first empty one. The damping sequence of `chainSeq` is the list of the
`dIter i` for `i < dLen` (`dampSeq_eq`). The command `seqLoop` records
them as the rows of the matrix `ch` and leaves their number in `m`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram Lax185574Proofs.Chain

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

variable (G) in
/-- The `i`-th set of the damping sequence. -/
def dIter (r : ℕ) (o : VOrder (Fin n)) (q : ℕ) (i : ℕ) : Finset (Fin n) :=
  (damp G r o q)^[i] univ

theorem dIter_succ (r : ℕ) (o : VOrder (Fin n)) (q i : ℕ) :
    dIter G r o q (i + 1) = damp G r o q (dIter G r o q i) := by
  unfold dIter; rw [Function.iterate_succ_apply']

theorem dIter_card (r : ℕ) (o : VOrder (Fin n)) {q : ℕ} (hq : 2 ≤ q) (i : ℕ) :
    (dIter G r o q i).card + i ≤ n ∨ dIter G r o q i = ∅ := by
  induction i with
  | zero => left; simp [dIter]
  | succ i ih =>
    rw [dIter_succ]
    by_cases he : dIter G r o q i = ∅
    · right
      rw [he]
      unfold damp; simp
    · rcases ih with ih | ih
      · left
        have := damp_lt (G := G) r o hq (nonempty_iff_ne_empty.2 he)
        omega
      · exact absurd ih he

theorem exists_dIter_empty (r : ℕ) (o : VOrder (Fin n)) {q : ℕ} (hq : 2 ≤ q) :
    ∃ i, dIter G r o q i = ∅ := by
  rcases dIter_card (G := G) r o hq (n + 1) with h | h
  · omega
  · exact ⟨_, h⟩

open Classical in
variable (G) in
/-- The index of the first empty set of the damping sequence. -/
noncomputable def dLen (r : ℕ) (o : VOrder (Fin n)) (q : ℕ) : ℕ :=
  if h : ∃ i, dIter G r o q i = ∅ then Nat.find h else 0

theorem dLen_spec (r : ℕ) (o : VOrder (Fin n)) {q : ℕ} (hq : 2 ≤ q) :
    dIter G r o q (dLen G r o q) = ∅ ∧ ∀ i < dLen G r o q, dIter G r o q i ≠ ∅ := by
  classical
  have h := exists_dIter_empty (G := G) r o hq
  unfold dLen; rw [dif_pos h]
  exact ⟨Nat.find_spec h, fun i hi => Nat.find_min h hi⟩

theorem dLen_le (r : ℕ) (o : VOrder (Fin n)) {q : ℕ} (hq : 2 ≤ q) : dLen G r o q ≤ n := by
  classical
  obtain ⟨h1, h2⟩ := dLen_spec (G := G) r o hq
  by_contra hc
  have := h2 n (by omega)
  rcases dIter_card (G := G) r o hq n with h | h
  · have : (dIter G r o q n).card = 0 := by omega
    exact (h2 n (by omega)) (card_eq_zero.1 this)
  · exact this h

theorem dampSeq_iter (r : ℕ) (o : VOrder (Fin n)) (q : ℕ) :
    ∀ (k f : ℕ) (A : Finset (Fin n)), k ≤ f → (∀ i < k, (damp G r o q)^[i] A ≠ ∅) →
      (damp G r o q)^[k] A = ∅ →
      dampSeq G r o q f A = (List.range k).map fun i => (damp G r o q)^[i] A
  | 0, f, A, _, _, hk => by
    simp only [Function.iterate_zero, id] at hk
    subst hk
    cases f <;> simp [dampSeq]
  | k + 1, f + 1, A, hf, hne, hk => by
    have hA : A ≠ ∅ := by simpa using hne 0 (by omega)
    simp only [dampSeq, if_neg hA]
    rw [dampSeq_iter r o q k f (damp G r o q A) (by omega)
      (fun i hi => by
        have := hne (i + 1) (by omega)
        rwa [Function.iterate_succ_apply] at this)
      (by rwa [Function.iterate_succ_apply] at hk)]
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    congr 1

/-- **The damping sequence of the chain.** -/
theorem dampSeq_eq (r : ℕ) (o : VOrder (Fin n)) {q : ℕ} (hq : 2 ≤ q) :
    dampSeq G r o q (n + 1) univ = (List.range (dLen G r o q)).map (dIter G r o q) := by
  obtain ⟨h1, h2⟩ := dLen_spec (G := G) r o hq
  exact dampSeq_iter r o q _ _ _ (by have := dLen_le (G := G) r o hq; omega) h2 h1

/-! ### The loop -/

/-- Fill `arr` (of length at least `n`) from `e`, keeping everything but
`arr` and `b`. -/
theorem fillKeep_run {B' : ℕ} {arr : String} {e : Expr} {f : ℕ → ℕ} {base K : ℕ} (hnB : n < B')
    {σ : Env} (hn : σ.vars "n" = n) (hlen : base + n ≤ (σ.arrs arr).length)
    (ie : Expr) (hie' : ∀ τ k, (∀ x, x ≠ "b" → τ.vars x = σ.vars x) →
      (∀ a, a ≠ arr → τ.arrs a = σ.arrs a) → τ.vars "b" = k → k < n → ie.evalB B' τ = some (base + k))
    (he : ∀ τ k, (∀ x, x ≠ "b" → τ.vars x = σ.vars x) → (∀ a, a ≠ arr → τ.arrs a = σ.arrs a) →
      τ.vars "b" = k → k < n → e.evalB B' τ = some (f k)) (hsz : 1 + ie.size + e.size ≤ K) :
    ∃ σ', Run B' (rowFill arr ie e) σ σ' (n * (K + 8) + 6) ∧
      (∀ x, x ≠ "b" → σ'.vars x = σ.vars x) ∧ (∀ a, a ≠ arr → σ'.arrs a = σ.arrs a) ∧
      (σ'.arrs arr).length = (σ.arrs arr).length ∧
      ∀ j, (σ'.arrs arr)[j]? = if base ≤ j ∧ j < base + n then some (f (j - base))
        else (σ.arrs arr)[j]? := by
  obtain ⟨σ', hr, ⟨hv, ha⟩, hl, hg⟩ :=
    rowFill_run (B := B') (n := n) (base := base) (K := K) (arr := arr) (ie := ie) (e := e)
      (fun τ => (∀ x, x ≠ "b" → τ.vars x = σ.vars x) ∧ (∀ a, a ≠ arr → τ.arrs a = σ.arrs a))
      f hnB (fun τ h => by rw [h.1 "n" (by decide), hn])
      (fun τ x h => ⟨fun y hy => by simp [hy, h.1 y hy], fun a ha => by simpa using h.2 a ha⟩)
      (fun τ i x h => ⟨fun y hy => by simp [h.1 y hy], fun a ha => by
        simp only [arrs_setArr, if_neg ha]; exact h.2 a ha⟩)
      (fun τ k h hb hk => hie' τ k h.1 h.2 hb hk) (fun τ k h hb hk => he τ k h.1 h.2 hb hk) hsz
      ⟨fun _ _ => rfl, fun _ _ => rfl⟩ hlen
  exact ⟨σ', hr, hv, ha, hl, hg⟩

theorem PdFix.setInA {r : ℕ} {A A' : Finset (Fin n)} {pf : ℕ → ℕ} {t1 t2 t3 : ℕ} {τ τ' : Env}
    (h : PdFix n r G A pf t1 t2 t3 τ) (hv : ∀ x, x ≠ "b" → τ'.vars x = τ.vars x)
    (ha : ∀ a, a ≠ "inA" → τ'.arrs a = τ.arrs a)
    (hA : Vec τ' "inA" n (fun u => ind (inBN A' u))) : PdFix n r G A' pf t1 t2 t3 τ' :=
  ⟨by rw [hv _ (by decide), h.hn], by rw [hv _ (by decide), h.hM], by rw [hv _ (by decide), h.htr],
    by rw [hv _ (by decide), h.ht1], by rw [hv _ (by decide), h.ht2],
    by rw [hv _ (by decide), h.ht3], h.hadj.of_eq (ha _ (by decide)),
    h.hpos.of_eq (ha _ (by decide)), hA, fun a hm => by
      rw [ha a (by simp at hm; rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> decide)]; exact h.lvec a hm,
    by rw [ha _ (by decide)]; exact h.ltab, by rw [ha _ (by decide)]; exact h.lcnt⟩

/-- The arrays the damping state reads. -/
def dstArrs : List String := ["adj", "pos", "inA", "inB", "inS", "Sl", "p2", "p3", "mark", "rep",
  "lab", "key", "lab2", "labk", "sz", "tab", "cnt"]

/-- The scalars the damping state reads. -/
def dstVars : List String := ["n", "M", "tr", "t1", "t2", "t3", "q", "ca"]

theorem DampSt.transfer {r : ℕ} {A : Finset (Fin n)} {pf : ℕ → ℕ} {q : ℕ} {τ τ' : Env}
    (h : DampSt n r G A pf q τ) (hv : ∀ x ∈ dstVars, τ'.vars x = τ.vars x)
    (ha : ∀ a ∈ dstArrs, τ'.arrs a = τ.arrs a) : DampSt n r G A pf q τ' := by
  obtain ⟨⟨t1, t2, t3, hF⟩, hq, hca, hz, hc, hs, hm⟩ := h
  have v : ∀ x, x ∈ dstVars → τ'.vars x = τ.vars x := hv
  have a : ∀ x, x ∈ dstArrs → τ'.arrs x = τ.arrs x := ha
  refine ⟨⟨t1, t2, t3, ⟨?_, ?_, ?_, ?_, ?_, ?_, hF.hadj.of_eq (a _ (by decide)),
    hF.hpos.of_eq (a _ (by decide)), hF.hinA.of_eq (a _ (by decide)), fun b hb => ?_, ?_, ?_⟩⟩,
    ?_, ?_, fun t ht => ?_, hc.of_eq (a _ (by decide)), hs.of_eq (a _ (by decide)),
    hm.of_eq (a _ (by decide))⟩
  · rw [v _ (by decide)]; exact hF.hn
  · rw [v _ (by decide)]; exact hF.hM
  · rw [v _ (by decide)]; exact hF.htr
  · rw [v _ (by decide)]; exact hF.ht1
  · rw [v _ (by decide)]; exact hF.ht2
  · rw [v _ (by decide)]; exact hF.ht3
  · rw [a b (by simp at hb; simp [dstArrs]; tauto)]; exact hF.lvec b hb
  · rw [a _ (by decide)]; exact hF.ltab
  · rw [a _ (by decide)]; exact hF.lcnt
  · rw [v _ (by decide)]; exact hq
  · rw [v _ (by decide)]; exact hca
  · rw [a _ (by decide)] at ht ⊢; exact hz t ht

/-- The state of the loop after recording `i` sets. -/
structure SeqSt (n r : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (o : VOrder (Fin n))
    (q : ℕ) (pf : ℕ → ℕ) (i : ℕ) (τ : Env) : Prop where
  dst : DampSt n r G (dIter G r o q i) pf q τ
  hm : τ.vars "m" = i
  lch : (τ.arrs "ch").length = (n + 1) * n
  hch : ∀ j < i, ∀ u < n, (τ.arrs "ch")[j * n + u]? = some (ind (inBN (dIter G r o q j) u))

/-- Record the set, damp it. -/
def seqBody : Com :=
  .seq (rowFill "ch" (.add (.mul (.var "m") (.var "n")) (.var "b")) (.get "inA" (.var "b")))
    (.seq (.assign "m" (.add (.var "m") (.lit 1)))
      (.seq dampCom (.seq (rowFill "inA" (.var "b") (.get "inS" (.var "b")))
        (.assign "ca" (.var "sc")))))

theorem seqBody_run {B' r : ℕ} {pf : ℕ → ℕ} (hB' : DampBound n B') (hrB : r < B')
    (o : VOrder (Fin n)) (hpfo : pf = posN o) {q : ℕ} (hq : q ≤ n + 1) {i : ℕ} (hi : i < n)
    {σ : Env} (hst : SeqSt n r G o q pf i σ) :
    ∃ σ' K, Run B' seqBody σ σ' K ∧ SeqSt n r G o q pf (i + 1) σ' ∧
      K ≤ dampCost G r o q (dIter G r o q i) + n * 40 + 100 ∧
      (∀ x, x ∉ seqBody.wvars → σ'.vars x = σ.vars x) := by
  have hB1 := hB'.1
  unfold PdBound at hB1
  obtain ⟨hD, hm, hlch, hch⟩ := hst
  obtain ⟨t1, t2, t3, hF⟩ := hD.fix
  have hnn : (i + 1) * n ≤ (n + 1) * n := Nat.mul_le_mul_right _ (by omega)
  have hnn' : (n + 1) * n ≤ n * (n + 4) := by nlinarith
  have hin : i * n + n = (i + 1) * n := by ring
  -- record
  obtain ⟨σ1, hr1, hv1, ha1, hl1, hg1⟩ :=
    fillKeep_run (B' := B') (arr := "ch") (e := .get "inA" (.var "b"))
      (f := fun u => ind (inBN (dIter G r o q i) u)) (base := i * n) (K := 12) (by omega) hF.hn
      (by rw [hlch]; nlinarith) (.add (.mul (.var "m") (.var "n")) (.var "b"))
      (fun τ k hv ha hb hk => by
        simp [hb, hv "m" (by decide), hv "n" (by decide), hm, hF.hn]
        constructor <;> omega)
      (fun τ k hv ha hb hk => by
        have := (hF.hinA.of_eq (ha "inA" (by decide))).evalB (B := B') hb hk (by omega)
          (by have := ind_le_one (inBN (dIter G r o q i) k); omega)
        exact this) (by simp)
  have hD1 : DampSt n r G (dIter G r o q i) pf q σ1 :=
    hD.transfer (fun x hx => hv1 x (by intro e; subst e; simp [dstVars] at hx))
      (fun a ha => ha1 a (by intro e; subst e; simp [dstArrs] at ha))
  set σ2 := σ1.setVar "m" (i + 1) with hσ2
  have hr2 : Run B' (.assign "m" (.add (.var "m") (.lit 1))) σ1 σ2 4 :=
    (Run.assign (by simp [hv1 "m" (by decide), hm]; omega)).mono (by simp)
  have hD2 : DampSt n r G (dIter G r o q i) pf q σ2 :=
    hD1.transfer (fun x hx => by
      have : x ≠ "m" := by intro e; subst e; simp [dstVars] at hx
      simp [hσ2, this]) (fun a _ => rfl)
  obtain ⟨σ3, K3, hr3, hD3, hK3, hx3, hS3, hsc3⟩ := dampCom_run hB' hrB o hpfo hq hD2
  have ha3 : ∀ a, a ∉ dampCom.warrs → σ3.arrs a = σ2.arrs a := fun a ha => hr3.frame_arr a ha
  obtain ⟨t1', t2', t3', hF3⟩ := hD3.fix
  -- copy back
  obtain ⟨σ4, hr4, hv4, ha4, hl4, hg4⟩ :=
    fillKeep_run (B' := B') (arr := "inA") (e := .get "inS" (.var "b"))
      (f := fun u => ind (inBN (damp G r o q (dIter G r o q i)) u)) (base := 0) (K := 4)
      (by omega) hF3.hn (by rw [hF3.hinA.len]; omega) (.var "b")
      (fun τ k hv ha hb hk => by simp [hb]; omega)
      (fun τ k hv ha hb hk => by
        have := (hS3.of_eq (ha "inS" (by decide))).evalB (B := B') hb hk (by omega)
          (by have := ind_le_one (inBN (damp G r o q (dIter G r o q i)) k); omega)
        exact this) (by simp)
  have hA4 : Vec σ4 "inA" n (fun u => ind (inBN (dIter G r o q (i + 1)) u)) := by
    rw [dIter_succ]
    exact ⟨by rw [hl4, hF3.hinA.len], fun u hu => by rw [hg4 u]; simp [hu]⟩
  have hF4 : PdFix n r G (dIter G r o q (i + 1)) pf t1' t2' t3' σ4 := hF3.setInA hv4 ha4 hA4
  set σ5 := σ4.setVar "ca" (dIter G r o q (i + 1)).card with hσ5
  have hr5 : Run B' (.assign "ca" (.var "sc")) σ4 σ5 2 := by
    have hscn : (damp G r o q (dIter G r o q i)).card ≤ n := by
      have := card_le_univ (damp G r o q (dIter G r o q i)); simpa using this
    refine Run.assign (by simp [hv4 "sc" (by decide), hsc3, dIter_succ]; omega)
  have hD5 : DampSt n r G (dIter G r o q (i + 1)) pf q σ5 := by
    obtain ⟨-, hq3, hca3, hz3, hc3, hs3, hm3⟩ := hD3
    exact ⟨⟨t1', t2', t3', hF4.setVar (by simp [fixVars]) _⟩,
      by simp [hσ5, hv4 "q" (by decide), hq3], by simp [hσ5],
      fun t ht => by
        have e : σ5.arrs "tab" = σ3.arrs "tab" := by
          simp only [hσ5, arrs_setVar]; exact ha4 _ (by decide)
        rw [e] at ht ⊢; exact hz3 t ht,
      (hc3.of_eq (ha4 _ (by decide))).of_eq rfl, (hs3.of_eq (ha4 _ (by decide))).of_eq rfl,
      (hm3.of_eq (ha4 _ (by decide))).of_eq rfl⟩
  have hrun : Run B' seqBody σ σ5 (n * 20 + 6 + (4 + (K3 + (n * 12 + 6 + 2)))) :=
    Run.seq hr1 (Run.seq hr2 (Run.seq hr3 (Run.seq hr4 hr5)))
  have hchk : σ5.arrs "ch" = σ1.arrs "ch" := by
    simp only [hσ5, arrs_setVar]
    rw [ha4 _ (by decide), ha3 _ (by decide)]; rfl
  refine ⟨σ5, _, hrun, ⟨hD5, ?_, ?_, fun j hj u hu => ?_⟩, by omega,
    fun x hx => hrun.frame_var x hx⟩
  · have : "m" ∉ dampCom.wvars := by decide
    simp [hσ5, hv4 "m" (by decide), hx3 "m" this, hσ2]
  · rw [hchk, hl1, hlch]
  · rw [hchk, hg1]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · have : j * n + u < i * n := by
        have := Nat.mul_le_mul_right n (show j + 1 ≤ i by omega); rw [Nat.add_mul] at this; omega
      rw [if_neg (by omega)]; exact hch j hj u hu
    · rw [if_pos ⟨by omega, by omega⟩]; simp

/-- Record and damp until the set is empty. -/
def seqLoop : Com := .while (.lt (.lit 0) (.var "ca")) seqBody

/-- The cost of one round of the loop. -/
noncomputable def sCost (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (r : ℕ)
    (o : VOrder (Fin n)) (q j : ℕ) : ℕ :=
  dampCost G r o q (dIter G r o q j) + n * 40 + 110

/-- **The damping sequence.** -/
theorem seqLoop_run {B' r : ℕ} {pf : ℕ → ℕ} (hB' : DampBound n B') (hrB : r < B')
    (o : VOrder (Fin n)) (hpfo : pf = posN o) {q : ℕ} (hq2 : 2 ≤ q) (hq : q ≤ n + 1)
    {σ : Env} (hst : SeqSt n r G o q pf 0 σ) :
    ∃ σ' K, Run B' seqLoop σ σ' K ∧ SeqSt n r G o q pf (dLen G r o q) σ' ∧
      K ≤ ∑ j ∈ range (dLen G r o q), sCost G r o q j + 10 ∧
      (∀ x, x ∉ seqLoop.wvars → σ'.vars x = σ.vars x) := by
  have hB1 := hB'.1
  unfold PdBound at hB1
  set M := dLen G r o q with hM
  obtain ⟨hMe, hMne⟩ := dLen_spec (G := G) r o hq2
  have hMn : M ≤ n := dLen_le (G := G) r o hq2
  let J : Env → Prop := fun τ => ∃ i, SeqSt n r G o q pf i τ ∧ i ≤ M ∧
    ∀ x, x ∉ seqLoop.wvars → τ.vars x = σ.vars x
  let Ψ : Env → ℕ := fun τ => ∑ j ∈ Ico (τ.vars "m") M, sCost G r o q j
  have hca : ∀ τ i, SeqSt n r G o q pf i τ → τ.vars "ca" = (dIter G r o q i).card :=
    fun τ i h => h.dst.hca
  obtain ⟨σ', K, hr, ⟨i, hst', hiM, hfr'⟩, hfalse, hK⟩ :=
    Run.while_potential (B := B') (b := .lt (.lit 0) (.var "ca")) (c := seqBody) J Ψ
      (fun τ ⟨i, h, _, _⟩ => ⟨_, evalB_condLt (evalB_lit (by omega)) (evalB_var (by
        rw [hca τ i h]; have := card_le_univ (dIter G r o q i); simp at this; omega))⟩)
      (by
        rintro τ ⟨i, hstτ, hiM, hfr⟩ hc
        have hne : dIter G r o q i ≠ ∅ := by
          intro he
          rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (by
            rw [hca τ i hstτ]; have := card_le_univ (dIter G r o q i); simp at this; omega)),
            hca τ i hstτ, he] at hc
          simp at hc
        have hiM' : i < M := by
          rcases Nat.lt_or_ge i M with h | h
          · exact h
          · have : i = M := by omega
            rw [this] at hne; exact absurd hMe hne
        obtain ⟨τ', K, hr, hst', hK, hx⟩ := seqBody_run hB' hrB o hpfo hq (by omega) hstτ
        refine ⟨τ', K, hr, ⟨i + 1, hst', by omega, fun x hx' => ?_⟩, ?_⟩
        · rw [hx x (fun h => hx' h), hfr x hx']
        · simp only [Ψ, hst'.hm, hstτ.hm, Cond.size, Expr.size]
          rw [← Finset.sum_Ico_consecutive _ (show i ≤ i + 1 by omega) (show i + 1 ≤ M by omega)]
          simp only [Nat.Ico_succ_singleton, sum_singleton]
          unfold sCost at *
          omega)
      ⟨0, hst, by omega, fun _ _ => rfl⟩
  have hiM' : i = M := by
    rcases Nat.lt_or_ge i M with h | h
    · exfalso
      have hne := hMne i h
      rw [evalB_condLt (evalB_lit (by omega)) (evalB_var (by
        rw [hca σ' i hst']; have := card_le_univ (dIter G r o q i); simp at this; omega)),
        hca σ' i hst'] at hfalse
      simp at hfalse
      exact hne hfalse
    · omega
  subst hiM'
  refine ⟨σ', K, hr, hst', ?_, hfr'⟩
  simp only [Ψ, hst.hm, Cond.size, Expr.size] at hK
  rw [Nat.Ico_zero_eq_range] at hK
  omega

end Lax185574Proofs.Chain.Ram
