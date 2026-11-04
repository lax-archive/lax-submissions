import Lax185574Proofs.Chain.Ram.WTree1

/-!
The greedy procedure of the Welzl ordering as a program, second part:
the scan for the candidate pair of minimum weight.

The command `scan` visits the pairs `(u, v)` with `u, v < n` in
lexicographic order and keeps the first pair of strictly smaller value
among the candidates, those with `v < u` and both active. Its best pair
is in the scalars `wbu` and `wbv`, and `wbf` is `1` once a candidate was
seen (`BestRep`). This is exactly `List.argmin` over `candPairs`, which
grows by one candidate at a time in the same order (`candPairs_eq`), so
`scan` computes the pair chosen by `welzlStep` (`scan_run`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram Lax185574Proofs.Chain

variable {n : ℕ}

/-! ### The candidate pairs, one at a time -/

/-- The pair `(u, v)` if it is a candidate, as a list. -/
def candAt (A : Finset (Fin n)) (u v : ℕ) : List (Fin n × Fin n) :=
  if h : u < n ∧ v < n then
    if v < u ∧ (⟨u, h.1⟩ : Fin n) ∈ A ∧ (⟨v, h.2⟩ : Fin n) ∈ A then [(⟨u, h.1⟩, ⟨v, h.2⟩)]
    else []
  else []

/-- The candidates `(u, v')` with `v' < v`. -/
def rowPre (A : Finset (Fin n)) (u : ℕ) : ℕ → List (Fin n × Fin n)
  | 0 => []
  | v + 1 => rowPre A u v ++ candAt A u v

/-- The candidates `(u', v)` with `u' < u`. -/
def rowsPre (A : Finset (Fin n)) : ℕ → List (Fin n × Fin n)
  | 0 => []
  | u + 1 => rowsPre A u ++ rowPre A u n

theorem filterMap_take_eq (A : Finset (Fin n)) (u : Fin n) {m : ℕ} (hm : m ≤ n) :
    ((List.finRange n).take m).filterMap
      (fun v => if v < u ∧ u ∈ A ∧ v ∈ A then some (u, v) else none) = rowPre A u m := by
  induction m with
  | zero => simp [rowPre]
  | succ m ih =>
    have hm' : m < n := by omega
    rw [List.take_add_one, List.filterMap_append, ih (by omega), rowPre]
    congr 1
    rw [List.getElem?_eq_getElem (by simpa using hm')]
    simp only [List.getElem_finRange, Option.toList_some, candAt, hm', u.2, and_self, dif_pos]
    simp only [Fin.cast_mk, List.filterMap_cons, List.filterMap_nil]
    by_cases h : (⟨m, hm'⟩ : Fin n) < u ∧ u ∈ A ∧ (⟨m, hm'⟩ : Fin n) ∈ A
    · have h' : m < (u : ℕ) ∧ (⟨u, u.2⟩ : Fin n) ∈ A ∧ (⟨m, hm'⟩ : Fin n) ∈ A :=
        ⟨h.1, by simpa using h.2.1, h.2.2⟩
      rw [if_pos h, if_pos h']
    · have h' : ¬ (m < (u : ℕ) ∧ (⟨u, u.2⟩ : Fin n) ∈ A ∧ (⟨m, hm'⟩ : Fin n) ∈ A) :=
        fun h' => h ⟨h'.1, by simpa using h'.2.1, h'.2.2⟩
      rw [if_neg h, if_neg h']

/-- **The candidate pairs, grown one at a time.** -/
theorem candPairs_eq (A : Finset (Fin n)) : candPairs A = rowsPre A n := by
  have key : ∀ m ≤ n, ((List.finRange n).take m).flatMap (fun u => (List.finRange n).filterMap
      (fun v => if v < u ∧ u ∈ A ∧ v ∈ A then some (u, v) else none)) = rowsPre A m := by
    intro m hm
    induction m with
    | zero => simp [rowsPre]
    | succ m ih =>
      have hm' : m < n := by omega
      rw [List.take_add_one, List.flatMap_append, ih (by omega), rowsPre]
      congr 1
      rw [List.getElem?_eq_getElem (by simpa using hm')]
      simp only [List.getElem_finRange, Option.toList_some, Fin.cast_mk, List.flatMap_cons,
        List.flatMap_nil, List.append_nil]
      have := filterMap_take_eq A ⟨m, hm'⟩ (le_refl n)
      rwa [List.take_of_length_le (by simp)] at this
  unfold candPairs
  rw [Fin.sort_univ, ← key n le_rfl, List.take_of_length_le (by simp)]

instance (A : Finset (Fin n)) (u : ℕ) : Decidable (inBN A u) := by
  unfold inBN; infer_instance

theorem candAt_of {A : Finset (Fin n)} {u v : ℕ} (hu : u < n) (hv : v < n) :
    candAt A u v = if v < u ∧ inBN A u ∧ inBN A v then [(⟨u, hu⟩, ⟨v, hv⟩)] else [] := by
  have e1 : inBN A u ↔ (⟨u, hu⟩ : Fin n) ∈ A := ⟨fun ⟨_, h⟩ => h, fun h => ⟨hu, h⟩⟩
  have e2 : inBN A v ↔ (⟨v, hv⟩ : Fin n) ∈ A := ⟨fun ⟨_, h⟩ => h, fun h => ⟨hv, h⟩⟩
  simp only [candAt, hu, hv, and_self, dif_pos, e1, e2]

/-! ### The best pair so far -/

/-- The scalars `wbf`, `wbu`, `wbv` hold the pair `o`. -/
def BestRep : Option (Fin n × Fin n) → Env → Prop
  | none, τ => τ.vars "wbf" = 0
  | some p, τ => τ.vars "wbf" = 1 ∧ τ.vars "wbu" = p.1 ∧ τ.vars "wbv" = p.2

theorem BestRep.congr {o : Option (Fin n × Fin n)} {σ τ : Env} (h : BestRep o σ)
    (h1 : τ.vars "wbf" = σ.vars "wbf") (h2 : τ.vars "wbu" = σ.vars "wbu")
    (h3 : τ.vars "wbv" = σ.vars "wbv") : BestRep o τ := by
  cases o with
  | none => simp only [BestRep] at h ⊢; rw [h1, h]
  | some p => simp only [BestRep] at h ⊢; rw [h1, h2, h3]; exact h

theorem BestRep.fr {o : Option (Fin n × Fin n)} {W Wa : List String} {σ τ : Env}
    (h : BestRep o σ) (F : Fr W Wa σ τ) (h1 : "wbf" ∉ W) (h2 : "wbu" ∉ W) (h3 : "wbv" ∉ W) :
    BestRep o τ := h.congr (F.vars _ h1) (F.vars _ h2) (F.vars _ h3)

/-! ### The scan -/

/-- `1` if `wv < wu` and both are active, else `0`. -/
def candE : Expr :=
  .mul (ltX (.var "wv") (.var "wu")) (.mul (.get "act" (.var "wu")) (.get "act" (.var "wv")))

@[simp] theorem size_candE : candE.size = 13 := rfl

/-- Visit the pair `wu wv`. -/
def scanBody : Com :=
  .ite (.eq candE (.lit 1))
    (.ite (.eq (.var "wbf") (.lit 0))
      (.seq (.assign "wbf" (.lit 1)) (.seq (.assign "wbu" (.var "wu")) (.assign "wbv" (.var "wv"))))
      (.seq (.assign "ca1" (rm "wu" "wv")) (.seq (.assign "ca2" (rm "wbu" "wbv"))
        (.seq bigCmp (.ite (.eq (.var "blt") (.lit 1))
          (.seq (.assign "wbu" (.var "wu")) (.assign "wbv" (.var "wv"))) .skip)))))
    .skip

/-- Find the first candidate pair of minimum value. -/
def scan : Com :=
  .seq (.assign "wbf" (.lit 0)) (forUp "wu" (.var "n") (forUp "wv" (.var "n") scanBody))

/-- The scalars the scan may change. -/
def scanW : List String := ["wbf", "wbu", "wbv", "ca1", "ca2", "blt", "bk", "wu", "wv"]

/-- The cost of the scan when every comparison costs at most `Q`. -/
def scanC (n Q : ℕ) : ℕ := n * (n * (Q + 58) + 14) + 8

/-- What the scan needs of the environment: the active vertices, and the
values `f (u, v)` of all pairs. -/
structure ScanCtx (n : ℕ) (A : Finset (Fin n)) (f : Fin n × Fin n → ℕ) (τ : Env) : Prop where
  hn : τ.vars "n" = n
  hD : τ.vars "D" = 2 * n + 2
  hact : Vec τ "act" n (fun u => ind (inBN A u))
  hrep : ∀ u (hu : u < n) v (hv : v < n), BigRep (2 * n + 2) τ (u * n + v) (f (⟨u, hu⟩, ⟨v, hv⟩))

theorem ScanCtx.fr {A : Finset (Fin n)} {f : Fin n × Fin n → ℕ} {W : List String} {σ τ : Env}
    (h : ScanCtx n A f σ) (F : Fr W [] σ τ) (h1 : "n" ∉ W) (h2 : "D" ∉ W) : ScanCtx n A f τ := by
  have ha : τ.arrs = σ.arrs := funext fun a => F.arrs a (by simp)
  exact ⟨by rw [F.vars _ h1, h.hn], by rw [F.vars _ h2, h.hD], h.hact.of_eq (by rw [ha]),
    fun u hu v hv => (h.hrep u hu v hv).of_arrs ha⟩

theorem scanBody_run {B Q U V : ℕ} {A : Finset (Fin n)} {f : Fin n × Fin n → ℕ}
    {l : List (Fin n × Fin n)} {τ : Env} (hB : WB n B) (hC : ScanCtx n A f τ)
    (hQ : ∀ u (hu : u < n) v (hv : v < n), 40 * Nat.log 2 (f (⟨u, hu⟩, ⟨v, hv⟩)) + 70 ≤ Q)
    (hu : τ.vars "wu" = U) (hv : τ.vars "wv" = V) (hU : U < n) (hV : V < n)
    (hbest : BestRep (l.argmin f) τ) :
    ∃ τ', Run B scanBody τ τ' (Q + 50) ∧ BestRep ((l ++ candAt A U V).argmin f) τ' ∧
      Fr ["wbf", "wbu", "wbv", "ca1", "ca2", "blt", "bk"] [] τ τ' := by
  have hs := hB.small
  have hnn : n ≤ n * n := Nat.le_mul_self n
  have g1 := evalB_ltX (B := B) (σ := τ) (e := .var "wv") (f := .var "wu")
    (evalB_var (by rw [hv]; omega)) (evalB_var (by rw [hu]; omega)) (by rw [hv]; omega)
    (by rw [hu]; omega) (by omega)
  rw [hu, hv] at g1
  have g2 := hC.hact.evalB (B := B) (x := "wu") hu hU (by omega) (by
    have := ind_le_one (inBN A U); omega)
  have g3 := hC.hact.evalB (B := B) (x := "wv") hv hV (by omega) (by
    have := ind_le_one (inBN A V); omega)
  have g4 := evalB_and01 g1 (evalB_and01 g2 g3 (by omega)) (by omega)
  have hcond : (Cond.eq candE (.lit 1)).evalB B τ =
      some (decide (V < U ∧ inBN A U ∧ inBN A V)) := by
    unfold candE
    rw [evalB_condEq' g4 (evalB_lit (by omega))]
    simp [ind_eq_one]
  rw [candAt_of hU hV]
  by_cases hc : V < U ∧ inBN A U ∧ inBN A V
  · rw [if_pos hc, List.argmin_concat]
    cases hl : l.argmin f with
    | none =>
      rw [hl] at hbest
      simp only [BestRep] at hbest
      have hc0 : (Cond.eq (.var "wbf") (.lit 0)).evalB B τ = some true := by
        rw [eq_lit_evalB (by rw [hbest]; omega) (by omega)]; simp [hbest]
      have hrun : Run B scanBody τ (((τ.setVar "wbf" 1).setVar "wbu" U).setVar "wbv" V)
          (Q + 50) :=
        (Run.ite_true (by rw [hcond]; simp [hc]) (Run.ite_true hc0
          (Run.seq (Run.assign (v := 1) (by simp; omega)) (Run.seq
            (Run.assign (v := U) (by simp [hu]; omega))
            (Run.assign (v := V) (by simp [hv]; omega)))))).mono (by simp)
      refine ⟨_, hrun, by simp [BestRep], ?_⟩
      exact (((Fr.refl _ _ τ).setVar (by simp) _).setVar (by simp) _).setVar (by simp) _
    | some c =>
      rw [hl] at hbest
      simp only [BestRep] at hbest
      obtain ⟨hb1, hb2, hb3⟩ := hbest
      have hc0 : (Cond.eq (.var "wbf") (.lit 0)).evalB B τ = some false := by
        rw [eq_lit_evalB (by rw [hb1]; omega) (by omega)]; simp [hb1]
      have ht1 := rm_lt hU hV
      have ht2 := rm_lt c.1.2 c.2.2
      have hr1 := Run.assign (B := B) (σ := τ) (x := "ca1") (e := rm "wu" "wv") (v := U * n + V)
        (evalB_rm hu hC.hn hv hV (by omega) (by omega))
      have hr2 := Run.assign (B := B) (σ := τ.setVar "ca1" (U * n + V)) (x := "ca2")
        (e := rm "wbu" "wbv") (v := c.1 * n + c.2)
        (evalB_rm (by simp [hb2]) (by simp [hC.hn]) (by simp [hb3]) c.2.2 (by omega) (by omega))
      let τ2 := (τ.setVar "ca1" (U * n + V)).setVar "ca2" (c.1 * n + c.2)
      have hr3e : τ2.arrs = τ.arrs := rfl
      obtain ⟨τ3, K3, hr3, hblt, hv3, ha3, hi3, ho3, hK3⟩ := bigCmp_run (B := B) (σ := τ2)
        ((hC.hrep U hU V hV).of_arrs hr3e) ((hC.hrep c.1 c.1.2 c.2 c.2.2).of_arrs hr3e)
        (by simp [τ2]) (by simp [τ2]) (by simp [τ2, hC.hD]) (hB.big ht1) (hB.big ht2)
        (by omega) (by omega)
      have hv3' : ∀ y, y ≠ "blt" → y ≠ "bk" → y ≠ "ca1" → y ≠ "ca2" → τ3.vars y = τ.vars y :=
        fun y h1 h2 h3 h4 => by rw [hv3 y h1 h2]; simp [τ2, h3, h4]
      have hF3 : Fr ["wbf", "wbu", "wbv", "ca1", "ca2", "blt", "bk"] [] τ τ3 :=
        ⟨fun y hy => hv3' y (by intro e; simp [e] at hy) (by intro e; simp [e] at hy)
          (by intro e; simp [e] at hy) (by intro e; simp [e] at hy),
          fun a _ => by rw [ha3]; rfl, hi3, ho3⟩
      have hQ1 := hQ U hU V hV
      have hblt' : τ3.vars "blt" = ind (f (⟨U, hU⟩, ⟨V, hV⟩) < f c) := hblt
      have hcmp : (Cond.eq (.var "blt") (.lit 1)).evalB B τ3 =
          some (decide (f (⟨U, hU⟩, ⟨V, hV⟩) < f c)) := by
        rw [eq_lit_evalB (by rw [hblt']; have := ind_le_one (f (⟨U, hU⟩, ⟨V, hV⟩) < f c); omega)
          (by omega), hblt']
        simp [ind_eq_one]
      have hu3 : τ3.vars "wu" = U := by rw [hv3' "wu" (by decide) (by decide) (by decide)
        (by decide), hu]
      have hv3 : τ3.vars "wv" = V := by rw [hv3' "wv" (by decide) (by decide) (by decide)
        (by decide), hv]
      by_cases hlt : f (⟨U, hU⟩, ⟨V, hV⟩) < f c
      · have hrun : Run B scanBody τ ((τ3.setVar "wbu" U).setVar "wbv" V) (Q + 50) :=
          (Run.ite_true (by rw [hcond]; simp [hc]) (Run.ite_false hc0 (Run.seq hr1 (Run.seq hr2
            (Run.seq hr3 (Run.ite_true (by rw [hcmp]; simp [hlt])
              (Run.seq (Run.assign (v := U) (by simp [hu3]; omega))
                (Run.assign (v := V) (by simp [hv3]; omega))))))))).mono
            (by simp only [Cond.size, Expr.size, size_candE, size_rm] at *; omega)
        refine ⟨_, hrun, ?_, (hF3.setVar (by simp) _).setVar (by simp) _⟩
        simp only [if_pos hlt, BestRep, vars_setVar]
        simp [hv3' "wbf" (by decide) (by decide) (by decide) (by decide), hb1]
      · have hrun : Run B scanBody τ τ3 (Q + 50) :=
          (Run.ite_true (by rw [hcond]; simp [hc]) (Run.ite_false hc0 (Run.seq hr1 (Run.seq hr2
            (Run.seq hr3 (Run.ite_false (by rw [hcmp]; simp [hlt]) Run.skip)))))).mono
            (by simp only [Cond.size, Expr.size, size_candE, size_rm] at *; omega)
        refine ⟨τ3, hrun, ?_, hF3⟩
        simp only [if_neg hlt, BestRep]
        refine ⟨by rw [hv3' "wbf" (by decide) (by decide) (by decide) (by decide), hb1],
          by rw [hv3' "wbu" (by decide) (by decide) (by decide) (by decide), hb2],
          by rw [hv3' "wbv" (by decide) (by decide) (by decide) (by decide), hb3]⟩
  · rw [if_neg hc, List.append_nil]
    exact ⟨τ, (Run.ite_false (by rw [hcond]; simp [hc]) Run.skip).mono (by simp), hbest,
      Fr.refl _ _ τ⟩

/-- **The scan.** It leaves in `wbf`, `wbu`, `wbv` the first candidate
pair of minimum value. -/
theorem scan_run {B Q : ℕ} {A : Finset (Fin n)} {f : Fin n × Fin n → ℕ} {σ : Env}
    (hB : WB n B) (hC : ScanCtx n A f σ)
    (hQ : ∀ u (hu : u < n) v (hv : v < n), 40 * Nat.log 2 (f (⟨u, hu⟩, ⟨v, hv⟩)) + 70 ≤ Q) :
    ∃ σ', Run B scan σ σ' (scanC n Q) ∧ BestRep ((candPairs A).argmin f) σ' ∧
      Fr scanW [] σ σ' := by
  have hs := hB.small
  let I : ℕ → Env → Prop := fun U τ => Fr scanW [] σ τ ∧ BestRep ((rowsPre A U).argmin f) τ
  have hCτ : ∀ τ, Fr scanW [] σ τ → ScanCtx n A f τ := fun τ hF =>
    hC.fr hF (by decide) (by decide)
  obtain ⟨σ', hr, ⟨hF', hR'⟩, -⟩ :=
    forUp_run (B := B) (i := "wu") (e := .var "n") (body := forUp "wv" (.var "n") scanBody)
      (N := n) (K := n * (Q + 58) + 6) I (by omega)
      (fun k _ τ hI _ => by rw [evalB_var (by rw [(hCτ τ hI.1).hn]; omega), (hCτ τ hI.1).hn])
      (σ := σ.setVar "wbf" 0)
      ⟨((Fr.refl scanW [] σ).setVar (by simp [scanW]) 0).setVar (by simp [scanW]) 0,
        by simp [BestRep, rowsPre]⟩
      (by
        rintro U hU τ ⟨hFτ, hRτ⟩ hwu
        let J : ℕ → Env → Prop := fun V ρ => Fr scanW [] σ ρ ∧ ρ.vars "wu" = U ∧
          BestRep ((rowsPre A U ++ rowPre A U V).argmin f) ρ
        obtain ⟨ρ, hrI, ⟨hFρ, huρ, hRρ⟩, -⟩ :=
          forUp_run (B := B) (i := "wv") (e := .var "n") (body := scanBody) (N := n)
            (K := Q + 50) J (by omega)
            (fun k _ ρ hI _ => by
              rw [evalB_var (by rw [(hCτ ρ hI.1).hn]; omega), (hCτ ρ hI.1).hn])
            (σ := τ) ⟨hFτ.setVar (by simp [scanW]) 0, by simp [hwu],
              by simpa [rowPre] using hRτ.congr (by simp) (by simp) (by simp)⟩
            (by
              rintro V hV ρ ⟨hFρ, huρ, hRρ⟩ hwv
              obtain ⟨ρ', hr', hR', hF'⟩ := scanBody_run (B := B) (Q := Q) (A := A) (f := f)
                hB (hCτ ρ hFρ) hQ huρ hwv hU hV hRρ
              refine ⟨ρ', hr', by rw [hF'.vars _ (by decide), hwv], ?_, ?_, ?_⟩
              · exact (hFρ.trans (hF'.mono (by simp [scanW]) (by simp))).setVar
                  (by simp [scanW]) _
              · simp [hF'.vars _ (by decide : "wu" ∉ ["wbf", "wbu", "wbv", "ca1", "ca2", "blt",
                  "bk"]), huρ]
              · rw [rowPre, ← List.append_assoc]
                exact hR'.congr (by simp) (by simp) (by simp))
        refine ⟨ρ, hrI.mono (by simp), huρ, hFρ.setVar (by simp [scanW]) _, ?_⟩
        rw [rowsPre]
        exact hRρ.congr (by simp) (by simp) (by simp))
  refine ⟨σ', (Run.seq (Run.assign (v := 0) (by simp; omega)) hr).mono (by simp [scanC]; ring_nf; omega),
    ?_, ?_⟩
  · rw [candPairs_eq]; exact hR'
  · exact hF'

end Lax185574Proofs.Chain.Ram
