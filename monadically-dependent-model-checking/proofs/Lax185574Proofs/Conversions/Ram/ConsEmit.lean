import Lax185574Proofs.Conversions.Ram.Buffer
import Lax185574Proofs.Conversions.Ram.FlagScan

/-!
Emitting the steps of one stage of the construction script into the
buffer: first the resolves of the pairs of parts in lexicographic order
of their least vertices, then the merges in increasing order.
-/

namespace Lax185574Proofs.Conversions.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words

theorem length_flatMap_le {α : Type*} (l : List α) (f : α → List ℕ) (c : ℕ)
    (h : ∀ a ∈ l, (f a).length ≤ c) : (l.flatMap f).length ≤ c * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons]
    have h1 := h a (List.mem_cons_self ..)
    have h2 := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
    rw [Nat.mul_succ]; omega

/-- The resolve triples of a stage, in lexicographic order of `(a, b)`. -/
noncomputable def resTriples (n : ℕ) (lab : ℕ → ℕ) (Bad Unr Pos : ℕ → ℕ → Prop) : List ℕ :=
  (List.range n).flatMap fun a => (List.range n).flatMap fun b =>
    open Classical in
    if a ≤ b ∧ lab a = a ∧ lab b = b ∧ ¬ Bad a b ∧ Unr a b then [2 - ind (Pos a b), a, b] else []

/-- The merge triples of a stage. -/
noncomputable def mrgTriples (n : ℕ) (lab lab' : ℕ → ℕ) : List ℕ :=
  (List.range n).flatMap fun v =>
    open Classical in if lab v = v ∧ lab' v ≠ v then [0, lab' v, v] else []

/-- One pair of parts. -/
def resBody : Com :=
  .ite (.lt (.var "b") (.var "a")) .skip
    (.ite (.eq (.get "cur" (.var "a")) (.var "a"))
      (.ite (.eq (.get "cur" (.var "b")) (.var "b"))
        (.ite (.eq (.get "bad" (rm "a" "b")) (.lit 0))
          (.ite (.eq (.get "unr" (rm "a" "b")) (.lit 1))
            (.seq (.assign "s1" (.sub (.lit 2) (.get "pos" (rm "a" "b"))))
              (.seq (.assign "s2" (.var "a")) (.seq (.assign "s3" (.var "b")) pushVars)))
            .skip) .skip) .skip) .skip)

/-- The resolves of a stage. -/
def emitResolves : Com := forUp "a" (.var "n") (forUp "b" (.var "n") resBody)

/-- What `emitResolves` reads. -/
structure ResCtx (n : ℕ) (lab : ℕ → ℕ) (Bad Unr Pos : ℕ → ℕ → Prop) (τ : Env) : Prop where
  hn : τ.vars "n" = n
  hcur : Vec τ "cur" n lab
  hbad : Mat τ "bad" n fun a b => ind (Bad a b)
  hunr : Mat τ "unr" n fun a b => ind (Unr a b)
  hpos : Mat τ "pos" n fun a b => ind (Pos a b)

theorem ResCtx.of_eq {n : ℕ} {lab : ℕ → ℕ} {Bad Unr Pos : ℕ → ℕ → Prop} {τ τ' : Env}
    (h : ResCtx n lab Bad Unr Pos τ) (hn : τ'.vars "n" = τ.vars "n")
    (ha : ∀ a, a ≠ "buf" → τ'.arrs a = τ.arrs a) : ResCtx n lab Bad Unr Pos τ' :=
  ⟨by rw [hn, h.hn], h.hcur.of_eq (ha _ (by decide)), h.hbad.of_eq (ha _ (by decide)),
    h.hunr.of_eq (ha _ (by decide)), h.hpos.of_eq (ha _ (by decide))⟩

open Classical in
theorem resBody_run {B n cap : ℕ} {lab : ℕ → ℕ} {Bad Unr Pos : ℕ → ℕ → Prop} {l : List ℕ}
    {τ : Env} (hc : ResCtx n lab Bad Unr Pos τ) (hlab : ∀ z < n, lab z < n) (hbuf : BufAt cap l τ)
    (hcap : l.length + 3 ≤ cap) (hB : n * n + cap + 3 < B) {a b : ℕ} (ha : τ.vars "a" = a)
    (hb : τ.vars "b" = b) (han : a < n) (hbn : b < n) :
    ∃ τ', Run B resBody τ τ' 80 ∧ ResCtx n lab Bad Unr Pos τ' ∧ τ'.vars "a" = a ∧
      τ'.vars "b" = b ∧
      BufAt cap (l ++ if a ≤ b ∧ lab a = a ∧ lab b = b ∧ ¬ Bad a b ∧ Unr a b then
        [2 - ind (Pos a b), a, b] else []) τ' := by
  have hnn : n ≤ n * n := Nat.le_mul_self n
  have hle : ∀ p : Prop, ind p < B := fun p => by have := ind_le_one p; omega
  have hba : (Cond.lt (.var "b") (.var "a")).evalB B τ = some (decide (b < a)) := by
    rw [evalB_condLt (evalB_var (by omega)) (evalB_var (by omega)), ha, hb]
  by_cases h1 : b < a
  · exact ⟨τ, (Run.ite_true (by rw [hba]; simp [h1]) Run.skip).mono (by simp), hc, ha, hb,
      by simpa [show ¬ a ≤ b by omega] using hbuf⟩
  have hba' : (Cond.lt (.var "b") (.var "a")).evalB B τ = some false := by rw [hba]; simp [h1]
  have hca : (Cond.eq (.get "cur" (.var "a")) (.var "a")).evalB B τ = some (decide (lab a = a)) := by
    rw [evalB_condEq' (hc.hcur.evalB ha han (by omega) (by have := hlab a han; omega))
      (by rw [evalB_var (by omega), ha])]
  by_cases h2 : lab a = a
  swap
  · exact ⟨τ, (Run.ite_false hba' (Run.ite_false (by rw [hca]; simp [h2]) Run.skip)).mono
      (by simp), hc, ha, hb, by simpa [h2] using hbuf⟩
  have hcb : (Cond.eq (.get "cur" (.var "b")) (.var "b")).evalB B τ = some (decide (lab b = b)) := by
    rw [evalB_condEq' (hc.hcur.evalB hb hbn (by omega) (by have := hlab b hbn; omega))
      (by rw [evalB_var (by omega), hb])]
  have hca' : (Cond.eq (.get "cur" (.var "a")) (.var "a")).evalB B τ = some true := by
    rw [hca]; simp [h2]
  by_cases h3 : lab b = b
  swap
  · exact ⟨τ, (Run.ite_false hba' (Run.ite_true hca' (Run.ite_false (by rw [hcb]; simp [h3])
      Run.skip))).mono (by simp), hc, ha, hb, by simpa [h3] using hbuf⟩
  have hcb' : (Cond.eq (.get "cur" (.var "b")) (.var "b")).evalB B τ = some true := by
    rw [hcb]; simp [h3]
  have hbad := hc.hbad.evalB (B := B) hc.hn ha hb han hbn (by omega) (by omega) (hle _)
  have hunr := hc.hunr.evalB (B := B) hc.hn ha hb han hbn (by omega) (by omega) (hle _)
  have hpos := hc.hpos.evalB (B := B) hc.hn ha hb han hbn (by omega) (by omega) (hle _)
  by_cases h4 : Bad a b
  · exact ⟨τ, (Run.ite_false hba' (Run.ite_true hca' (Run.ite_true hcb' (Run.ite_false
      (by rw [evalB_condEq' hbad (evalB_lit (by omega))]; simp [ind, h4]) Run.skip)))).mono
      (by simp), hc, ha, hb, by simpa [h4] using hbuf⟩
  have hbad' : (Cond.eq (.get "bad" (rm "a" "b")) (.lit 0)).evalB B τ = some true := by
    rw [evalB_condEq' hbad (evalB_lit (by omega))]; simp [ind, h4]
  by_cases h5 : Unr a b
  swap
  · exact ⟨τ, (Run.ite_false hba' (Run.ite_true hca' (Run.ite_true hcb' (Run.ite_true hbad'
      (Run.ite_false (by rw [evalB_condEq' hunr (evalB_lit (by omega))]; simp [ind, h5])
        Run.skip))))).mono (by simp), hc, ha, hb, by simpa [h5] using hbuf⟩
  have hunr' : (Cond.eq (.get "unr" (rm "a" "b")) (.lit 1)).evalB B τ = some true := by
    rw [evalB_condEq' hunr (evalB_lit (by omega))]; simp [ind, h5]
  set τ1 := τ.setVar "s1" (2 - ind (Pos a b)) with hτ1
  set τ2 := τ1.setVar "s2" a with hτ2
  set τ3 := τ2.setVar "s3" b with hτ3
  have hs1 : Run B (.assign "s1" (.sub (.lit 2) (.get "pos" (rm "a" "b")))) τ τ1 9 :=
    (Run.assign (evalB_bin (evalB_lit (by omega)) hpos (by simp; omega))).mono (by simp)
  have hs2 : Run B (.assign "s2" (.var "a")) τ1 τ2 2 :=
    Run.assign (by simp [hτ1, ha]; omega)
  have hs3 : Run B (.assign "s3" (.var "b")) τ2 τ3 2 :=
    Run.assign (by simp [hτ2, hτ1, hb]; omega)
  have hpb : (τ3.vars "s1") < B := by simp [hτ3, hτ2, hτ1]; omega
  obtain ⟨τ4, hr4, hbuf4, hv4, ha4, ho4, hi4⟩ := pushVars_run (B := B) (τ := τ3)
    (hbuf.of_eq (by simp [hτ3, hτ2, hτ1]) (by simp [hτ3, hτ2, hτ1])) hcap (by omega) hpb
    (by simp [hτ3, hτ2, hτ1]; omega) (by simp [hτ3, hτ2, hτ1]; omega)
  refine ⟨τ4, (Run.ite_false hba' (Run.ite_true hca' (Run.ite_true hcb' (Run.ite_true hbad'
    (Run.ite_true hunr' (Run.seq hs1 (Run.seq hs2 (Run.seq hs3 hr4)))))))).mono (by simp),
    hc.of_eq (by rw [hv4 "n" (by decide)]; simp [hτ3, hτ2, hτ1])
      (fun x hx => by rw [ha4 x hx]; simp [hτ3, hτ2, hτ1]),
    by rw [hv4 "a" (by decide)]; simp [hτ3, hτ2, hτ1, ha],
    by rw [hv4 "b" (by decide)]; simp [hτ3, hτ2, hτ1, hb], ?_⟩
  simpa [h1, h2, h3, h4, h5, show a ≤ b by omega, hτ3, hτ2, hτ1] using hbuf4

theorem length_ite_le {p : Prop} [Decidable p] (l : List ℕ) (hl : l.length ≤ 3) :
    (if p then l else []).length ≤ 3 := by
  split <;> simp_all

open Classical in
/-- **The resolves of a stage.** -/
theorem emitResolves_run {B n cap : ℕ} {lab : ℕ → ℕ} {Bad Unr Pos : ℕ → ℕ → Prop} {l : List ℕ}
    {τ : Env} (hc : ResCtx n lab Bad Unr Pos τ) (hlab : ∀ z < n, lab z < n)
    (hbuf : BufAt cap l τ) (hcap : l.length + 3 * (n * n) ≤ cap) (hB : n * n + cap + 3 < B) :
    ∃ τ', Run B emitResolves τ τ' (n * (n * 88 + 14) + 6) ∧ ResCtx n lab Bad Unr Pos τ' ∧
      BufAt cap (l ++ resTriples n lab Bad Unr Pos) τ' := by
  have hnn : n ≤ n * n := Nat.le_mul_self n
  let cell : ℕ → ℕ → List ℕ := fun a b =>
    if a ≤ b ∧ lab a = a ∧ lab b = b ∧ ¬ Bad a b ∧ Unr a b then [2 - ind (Pos a b), a, b] else []
  have hcell : ∀ a b, (cell a b).length ≤ 3 := fun a b => length_ite_le _ (by simp)
  let row : ℕ → List ℕ := fun a => (List.range n).flatMap (cell a)
  have hrow : ∀ a, (row a).length ≤ 3 * n := fun a => by
    have := length_flatMap_le (List.range n) (cell a) 3 (fun b _ => hcell a b)
    rw [List.length_range] at this; exact this
  have hlenk : ∀ k, ((List.range k).flatMap row).length ≤ 3 * n * k := fun k => by
    have := length_flatMap_le (List.range k) row (3 * n) (fun a _ => hrow a)
    rw [List.length_range] at this; exact this
  let IA : ℕ → Env → Prop := fun k ρ => ResCtx n lab Bad Unr Pos ρ ∧
    BufAt cap (l ++ (List.range k).flatMap row) ρ
  obtain ⟨ρ, hr, ⟨hcρ, hbρ⟩, -⟩ :=
    forUp_run (B := B) (i := "a") (e := .var "n") (body := forUp "b" (.var "n") resBody) (N := n)
      (K := n * 88 + 6) IA (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [hI.1.hn]; omega), hI.1.hn])
      (σ := τ) ⟨hc.of_eq (by simp) (fun _ _ => by simp), by
        simpa using hbuf.of_eq (τ' := τ.setVar "a" 0) (by simp) (by simp)⟩
      (by
        rintro k hk ρ ⟨hcρ, hbρ⟩ hak
        have hk3 : 3 * n * k + 3 * n ≤ 3 * (n * n) := by
          have := Nat.mul_le_mul_left (3 * n) (show k + 1 ≤ n by omega); rw [Nat.mul_succ] at this
          nlinarith
        let IB : ℕ → Env → Prop := fun k2 ρ' => ResCtx n lab Bad Unr Pos ρ' ∧ ρ'.vars "a" = k ∧
          BufAt cap (l ++ (List.range k).flatMap row ++ (List.range k2).flatMap (cell k)) ρ'
        obtain ⟨ρ', hrB, ⟨hc', ha', hb'⟩, -⟩ :=
          forUp_run (B := B) (i := "b") (e := .var "n") (body := resBody) (N := n) (K := 80) IB
            (by omega) (fun k _ τ hI _ => by rw [evalB_var (by rw [hI.1.hn]; omega), hI.1.hn])
            (σ := ρ) ⟨hcρ.of_eq (by simp) (fun _ _ => by simp), by simp [hak], by
              simpa using hbρ.of_eq (τ' := ρ.setVar "b" 0) (by simp) (by simp)⟩
            (by
              rintro k2 hk2 ρ1 ⟨hc1, ha1, hb1⟩ hbk
              have hl1 := length_flatMap_le (List.range k2) (cell k) 3 (fun b _ => hcell k b)
              simp only [List.length_range] at hl1
              obtain ⟨ρ2, hr2, hc2, ha2, hb2, hbuf2⟩ := resBody_run hc1 hlab hb1
                (by simp only [List.length_append]; have := hlenk k; omega) hB ha1 hbk hk hk2
              refine ⟨ρ2, hr2, hb2, ⟨hc2.of_eq (by simp) (fun _ _ => by simp), by simp [ha2], ?_⟩⟩
              have := hbuf2.of_eq (τ' := ρ2.setVar "b" (k2 + 1)) (by simp) (by simp)
              simpa [List.range_succ, List.flatMap_append, List.append_assoc] using this)
        refine ⟨ρ', hrB.mono (by simp), ha', hc'.of_eq (by simp) (fun _ _ => by simp), ?_⟩
        have := hb'.of_eq (τ' := ρ'.setVar "a" (k + 1)) (by simp) (by simp)
        simpa [List.range_succ, List.flatMap_append, List.append_assoc] using this)
  exact ⟨ρ, hr.mono (by simp), hcρ, hbρ⟩

/-- One vertex of the merges. -/
def mrgBody : Com :=
  .ite (.eq (.get "cur" (.var "v")) (.var "v"))
    (.ite (.eq (.get "nxt" (.var "v")) (.var "v")) .skip
      (.seq (.assign "s1" (.lit 0)) (.seq (.assign "s2" (.get "nxt" (.var "v")))
        (.seq (.assign "s3" (.var "v")) pushVars))))
    .skip

/-- The merges of a stage. -/
def emitMerges : Com := forUp "v" (.var "n") mrgBody

/-- What `emitMerges` reads. -/
structure MrgCtx (n : ℕ) (lab lab' : ℕ → ℕ) (τ : Env) : Prop where
  hn : τ.vars "n" = n
  hcur : Vec τ "cur" n lab
  hnxt : Vec τ "nxt" n lab'

theorem MrgCtx.of_eq {n : ℕ} {lab lab' : ℕ → ℕ} {τ τ' : Env} (h : MrgCtx n lab lab' τ)
    (hn : τ'.vars "n" = τ.vars "n") (ha : ∀ a, a ≠ "buf" → τ'.arrs a = τ.arrs a) :
    MrgCtx n lab lab' τ' :=
  ⟨by rw [hn, h.hn], h.hcur.of_eq (ha _ (by decide)), h.hnxt.of_eq (ha _ (by decide))⟩

open Classical in
/-- **The merges of a stage.** -/
theorem emitMerges_run {B n cap : ℕ} {lab lab' : ℕ → ℕ} {l : List ℕ} {τ : Env}
    (hc : MrgCtx n lab lab' τ) (hlab : ∀ z < n, lab z < n) (hlab' : ∀ z < n, lab' z < n)
    (hbuf : BufAt cap l τ) (hcap : l.length + 3 * n ≤ cap) (hB : n + cap + 3 < B) :
    ∃ τ', Run B emitMerges τ τ' (n * 60 + 6) ∧ MrgCtx n lab lab' τ' ∧
      BufAt cap (l ++ mrgTriples n lab lab') τ' := by
  let cell : ℕ → List ℕ := fun v => if lab v = v ∧ lab' v ≠ v then [0, lab' v, v] else []
  let I : ℕ → Env → Prop := fun k ρ => MrgCtx n lab lab' ρ ∧
    BufAt cap (l ++ (List.range k).flatMap cell) ρ
  obtain ⟨ρ, hr, ⟨hcρ, hbρ⟩, -⟩ :=
    forUp_run (B := B) (i := "v") (e := .var "n") (body := mrgBody) (N := n) (K := 52) I
      (by omega) (fun k _ τ hI _ => by rw [evalB_var (by rw [hI.1.hn]; omega), hI.1.hn])
      (σ := τ) ⟨hc.of_eq (by simp) (fun _ _ => by simp), by
        simpa using hbuf.of_eq (τ' := τ.setVar "v" 0) (by simp) (by simp)⟩
      (by
        rintro k hk ρ ⟨hcρ, hbρ⟩ hvk
        have hlk := length_flatMap_le (List.range k) cell 3 (fun v _ => length_ite_le _ (by simp))
        rw [List.length_range] at hlk
        have hfin : ∀ ρ2 : Env, ρ2.vars "v" = k → MrgCtx n lab lab' ρ2 →
            BufAt cap (l ++ (List.range k).flatMap cell ++ cell k) ρ2 →
            I (k + 1) (ρ2.setVar "v" (k + 1)) := fun ρ2 _ h1 h2 => by
          refine ⟨h1.of_eq (by simp) (fun _ _ => by simp), ?_⟩
          have := h2.of_eq (τ' := ρ2.setVar "v" (k + 1)) (by simp) (by simp)
          simpa [List.range_succ, List.flatMap_append, List.append_assoc] using this
        have hc1 : (Cond.eq (.get "cur" (.var "v")) (.var "v")).evalB B ρ =
            some (decide (lab k = k)) := by
          rw [evalB_condEq' (hcρ.hcur.evalB hvk hk (by omega) (by have := hlab k hk; omega))
            (by rw [evalB_var (by omega), hvk])]
        by_cases h1 : lab k = k
        swap
        · exact ⟨ρ, (Run.ite_false (by rw [hc1]; simp [h1]) Run.skip).mono (by simp), hvk,
            hfin ρ hvk hcρ (by simpa [cell, h1] using hbρ)⟩
        have hc1' : (Cond.eq (.get "cur" (.var "v")) (.var "v")).evalB B ρ = some true := by
          rw [hc1]; simp [h1]
        have hnx := hcρ.hnxt.evalB (B := B) hvk hk (by omega) (by have := hlab' k hk; omega)
        have hc2 : (Cond.eq (.get "nxt" (.var "v")) (.var "v")).evalB B ρ =
            some (decide (lab' k = k)) := by
          rw [evalB_condEq' hnx (by rw [evalB_var (by omega), hvk])]
        by_cases h2 : lab' k = k
        · exact ⟨ρ, (Run.ite_true hc1' (Run.ite_true (by rw [hc2]; simp [h2]) Run.skip)).mono
            (by simp), hvk, hfin ρ hvk hcρ (by simpa [cell, h2] using hbρ)⟩
        set τ1 := ρ.setVar "s1" 0 with hτ1
        set τ2 := τ1.setVar "s2" (lab' k) with hτ2
        set τ3 := τ2.setVar "s3" k with hτ3
        have hs1 : Run B (.assign "s1" (.lit 0)) ρ τ1 2 := Run.assign (by simp; omega)
        have hs2 : Run B (.assign "s2" (.get "nxt" (.var "v"))) τ1 τ2 3 :=
          Run.assign (Vec.evalB (hcρ.hnxt.of_eq (by simp [hτ1])) (by simp [hτ1, hvk]) hk
            (by omega) (by have := hlab' k hk; omega))
        have hs3 : Run B (.assign "s3" (.var "v")) τ2 τ3 2 :=
          Run.assign (by simp [hτ2, hτ1, hvk]; omega)
        obtain ⟨τ4, hr4, hbuf4, hv4, ha4, -, -⟩ := pushVars_run (B := B) (τ := τ3)
          (hbρ.of_eq (by simp [hτ3, hτ2, hτ1]) (by simp [hτ3, hτ2, hτ1]))
          (by simp only [List.length_append]; omega) (by omega)
          (by simp [hτ3, hτ2, hτ1]; omega) (by simp [hτ3, hτ2, hτ1]; have := hlab' k hk; omega)
          (by simp [hτ3, hτ2, hτ1]; omega)
        refine ⟨τ4, (Run.ite_true hc1' (Run.ite_false (by rw [hc2]; simp [h2])
          (Run.seq hs1 (Run.seq hs2 (Run.seq hs3 hr4))))).mono (by simp),
          by rw [hv4 "v" (by decide)]; simp [hτ3, hτ2, hτ1, hvk],
          hfin τ4 (by rw [hv4 "v" (by decide)]; simp [hτ3, hτ2, hτ1, hvk])
            (hcρ.of_eq (by rw [hv4 "n" (by decide)]; simp [hτ3, hτ2, hτ1])
              (fun x hx => by rw [ha4 x hx]; simp [hτ3, hτ2, hτ1])) ?_⟩
        simpa [cell, h1, h2, hτ3, hτ2, hτ1] using hbuf4)
  exact ⟨ρ, hr.mono (by simp), hcρ, hbρ⟩

end Lax185574Proofs.Conversions.Ram
