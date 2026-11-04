import Lax185574Proofs.Chain.Ram.ChainOut

/-!
The Welzl ordering from the steps of the greedy procedure.

The ordering is built from the list of the remaining active vertices by
inserting, for the steps from the last to the first, the vertex `u`
right after `v`. On numbers this is `insAfterN`. The command `ordCom`
does it in the array `ol` (of current length `olen`), from the steps in
order of time in the arrays `su` and `sv` (`ns` of them), and then
stores the position of every vertex in `pos`.
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.Conversions.Ram Lax185574Proofs.Chain

/-- Insert `u` right after the first occurrence of `v`, on numbers. -/
def insAfterN (v u : ℕ) : List ℕ → List ℕ
  | [] => [u]
  | a :: l => if a = v then a :: u :: l else a :: insAfterN v u l

theorem map_insertAfter {n : ℕ} (v u : Fin n) (l : List (Fin n)) :
    (insertAfter v u l).map Fin.val = insAfterN v u (l.map Fin.val) := by
  induction l with
  | nil => simp [insertAfter, insAfterN]
  | cons a l ih =>
    simp only [insertAfter, insAfterN, List.map_cons]
    by_cases h : a = v
    · simp [h]
    · have : (a : ℕ) ≠ v := fun e => h (Fin.ext e)
      simp [h, this, ih]

/-- `insAfterN` as a split of the list: `u` goes to position `idx + 1`
if `v` is at `idx`, and to the end otherwise. -/
theorem insAfterN_eq (v u : ℕ) (l : List ℕ) :
    insAfterN v u l = l.take (min (l.idxOf v + 1) l.length) ++ u ::
      l.drop (min (l.idxOf v + 1) l.length) := by
  induction l with
  | nil => simp [insAfterN]
  | cons a l ih =>
    simp only [insAfterN, List.idxOf_cons, List.length_cons]
    by_cases h : a = v
    · simp [h]
    · have : (a == v) = false := by simp [h]
      simp only [h, if_false, this, cond_false]
      rw [ih]
      have : min (l.idxOf v + 1 + 1) (l.length + 1) = min (l.idxOf v + 1) l.length + 1 := by omega
      rw [this]; simp

/-! ### The list in an array -/

/-- The array `ol` starts with the list `l`, and `olen` is its length. -/
structure OlAt (n : ℕ) (l : List ℕ) (τ : Env) : Prop where
  len : τ.vars "olen" = l.length
  room : l.length ≤ n
  arr : (τ.arrs "ol").length = n
  get : ∀ k (h : k < l.length), (τ.arrs "ol")[k]? = some l[k]
  lt : ∀ x ∈ l, x < n

/-- Find the position after `v` (scalar `ov`): `op = min (idx v + 1) olen`. -/
def findPos : Com :=
  .seq (.assign "op" (.var "olen")) (.seq (.assign "oi" (.lit 0))
    (.while (.lt (.var "oi") (.var "olen"))
      (.ite (.eq (.get "ol" (.var "oi")) (.var "ov"))
        (.seq (.assign "op" (.add (.var "oi") (.lit 1))) (.assign "oi" (.var "olen")))
        (.assign "oi" (.add (.var "oi") (.lit 1))))))

theorem idxOf_first : ∀ (l : List ℕ) (v k : ℕ), (∀ j (h : j < l.length), j < k → l[j] ≠ v) →
    (∀ h : k < l.length, l[k] = v) → k ≤ l.length → l.idxOf v = k
  | [], v, k, _, _, hk => by simp at hk; simp [hk]
  | a :: l, v, 0, _, h, _ => by
    have := h (by simp); simp at this; simp [List.idxOf_cons, this]
  | a :: l, v, k + 1, hb, h, hk => by
    have ha : a ≠ v := hb 0 (by simp) (by omega)
    have hav : (a == v) = false := by simp [ha]
    rw [List.idxOf_cons, hav, cond_false,
      idxOf_first l v k (fun j hj hjk => hb (j + 1) (by simp; omega) (by omega))
        (fun hk' => h (by simp; omega)) (by simp at hk; omega)]

theorem findPos_run {B n : ℕ} {l : List ℕ} {v : ℕ} (Ctx : Env → Prop) (hnB : n + 2 < B)
    (hvn : v < n)
    (hC : ∀ τ, Ctx τ → OlAt n l τ ∧ τ.vars "ov" = v)
    (hCv : ∀ τ x u, Ctx τ → x ∈ ["op", "oi"] → Ctx (τ.setVar x u))
    {σ : Env} (hσ : Ctx σ) :
    ∃ σ', Run B findPos σ σ' (n * 20 + 20) ∧ Ctx σ' ∧
      σ'.vars "op" = min (l.idxOf v + 1) l.length := by
  have hO := (hC σ hσ).1
  set L := l.length with hL
  let J : Env → Prop := fun τ => Ctx τ ∧ τ.vars "oi" ≤ L ∧
    ((τ.vars "oi" < L ∧ τ.vars "op" = L ∧ ∀ j (h : j < L), j < τ.vars "oi" → l[j] ≠ v) ∨
     (τ.vars "oi" = L ∧ τ.vars "op" = min (l.idxOf v + 1) L))
  have hJ0 : J ((σ.setVar "op" L).setVar "oi" 0) := by
    refine ⟨hCv _ _ _ (hCv _ _ _ hσ (by simp)) (by simp), by simp, ?_⟩
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · right; simp [h0]
    · left; simp [h0]
  obtain ⟨σ', K, hr, ⟨hC', hle', hst'⟩, hf', hK⟩ :=
    Run.while_potential (B := B) (b := .lt (.var "oi") (.var "olen"))
      (c := .ite (.eq (.get "ol" (.var "oi")) (.var "ov"))
        (.seq (.assign "op" (.add (.var "oi") (.lit 1))) (.assign "oi" (.var "olen")))
        (.assign "oi" (.add (.var "oi") (.lit 1)))) J (fun τ => (L - τ.vars "oi") * 20)
      (fun τ hJ => evalB_condLt_vars (by have := hJ.2.1; have := (hC τ hJ.1).1.room; omega)
        (by rw [(hC τ hJ.1).1.len]; have := (hC τ hJ.1).1.room; omega))
      (by
        rintro τ ⟨hCτ, hle, hst⟩ hc
        obtain ⟨hOτ, hvτ⟩ := hC τ hCτ
        have hlt : τ.vars "oi" < L := by
          have := lt_of_condLt_true hc; rwa [hOτ.len] at this
        have hst2 : τ.vars "op" = L ∧ ∀ j (h : j < L), j < τ.vars "oi" → l[j] ≠ v := by
          rcases hst with ⟨-, a, b⟩ | ⟨a, -⟩
          · exact ⟨a, b⟩
          · omega
        obtain ⟨k, hk⟩ : ∃ k, τ.vars "oi" = k := ⟨_, rfl⟩
        rw [hk] at hlt hst2
        have hLn := hOτ.room
        have hget := hOτ.get k hlt
        have hlk := hOτ.lt _ (List.getElem_mem hlt)
        have hev : (Cond.eq (.get "ol" (.var "oi")) (.var "ov")).evalB B τ =
            some (decide (l[k] = v)) := by
          rw [evalB_condEq' (evalB_get (evalB_var (by rw [hk]; omega)) (by rw [hk]; exact hget)
            (by omega)) (evalB_var (by rw [hvτ]; omega)), hvτ]
        by_cases hkv : l[k] = v
        · have hidx : l.idxOf v = k := idxOf_first l v k (fun j hj hjk => hst2.2 j hj hjk)
            (fun _ => hkv) (by omega)
          refine ⟨(τ.setVar "op" (k + 1)).setVar "oi" L, _, Run.ite_true (by rw [hev]; simp [hkv])
            (Run.seq (Run.assign (v := k + 1) (by simp [hk]; omega))
              (Run.assign (v := L) (by simp [hOτ.len]; omega))),
            ⟨hCv _ _ _ (hCv _ _ _ hCτ (by simp)) (by simp), by simp,
              Or.inr ⟨by simp, by simp [hidx]; omega⟩⟩, ?_⟩
          simp only [Cond.size, Expr.size, vars_setVar, if_true, hk, Nat.sub_self, zero_mul]
          have : (L - k) * 20 ≥ 20 := Nat.le_mul_of_pos_left 20 (by omega)
          omega
        · refine ⟨τ.setVar "oi" (k + 1), _, Run.ite_false (by rw [hev]; simp [hkv])
            (Run.assign (v := k + 1) (by simp [hk]; omega)),
            ⟨hCv _ _ _ hCτ (by simp), by simp; omega, ?_⟩, ?_⟩
          · have hall : ∀ j (h : j < L), j < k + 1 → l[j] ≠ v := fun j h hj => by
              rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
              · exact hst2.2 j h hj
              · exact hkv
            rcases Nat.lt_or_ge (k + 1) L with h' | h'
            · left; refine ⟨by simp; omega, by simp [hst2.1], by simpa using hall⟩
            · right
              have hidx : l.idxOf v = L := idxOf_first l v L (fun j hj _ => hall j hj (by omega))
                (fun h => absurd h (lt_irrefl _)) le_rfl
              refine ⟨by simp; omega, by simp [hst2.1, hidx]⟩
          · simp only [Cond.size, Expr.size, vars_setVar, if_true, hk]
            have : L - k = (L - (k + 1)) + 1 := by omega
            rw [this, Nat.add_mul]; omega)
      hJ0
  have hoi : σ'.vars "oi" = L := by
    have := le_of_condLt_false hf'; rw [(hC σ' hC').1.len] at this; omega
  have hop : σ'.vars "op" = min (l.idxOf v + 1) L := by
    rcases hst' with ⟨h, -⟩ | ⟨-, h⟩
    · omega
    · exact h
  have hLn0 : L ≤ n := hO.room
  refine ⟨σ', (Run.seq (Run.assign (v := L) (by simp [hO.len]; omega))
    (Run.seq (Run.assign (v := 0) (by simp; omega)) hr)).mono ?_, hC', hop⟩
  simp only [Cond.size, Expr.size, vars_setVar, if_true] at hK ⊢
  have : (L - 0) * 20 ≤ n * 20 := by have := hO.room; simp; omega
  omega

/-- Shift the list from `op` on by one and put `ou` at `op`. -/
def insAt : Com :=
  .seq (forUp "ot" (.sub (.var "olen") (.var "op"))
      (.store "ol" (.sub (.var "olen") (.var "ot"))
        (.get "ol" (.sub (.sub (.var "olen") (.var "ot")) (.lit 1)))))
    (.seq (.store "ol" (.var "op") (.var "ou")) (.assign "olen" (.add (.var "olen") (.lit 1))))

theorem insAt_run {B n : ℕ} {l : List ℕ} {p u : ℕ} (Ctx : Env → Prop) (hnB : n + 2 < B)
    (hun : u < n) (hp : p ≤ l.length) (hroom : l.length < n)
    (hCv : ∀ τ x v, Ctx τ → x ∈ ["ot", "olen"] → Ctx (τ.setVar x v))
    (hCa : ∀ τ i v, Ctx τ → Ctx (τ.setArr "ol" i v))
    {σ : Env} (hσ : Ctx σ) (hO : OlAt n l σ) (hop : σ.vars "op" = p) (hou : σ.vars "ou" = u) :
    ∃ σ', Run B insAt σ σ' (n * 30 + 30) ∧ Ctx σ' ∧
      OlAt n (l.take p ++ u :: l.drop p) σ' ∧
      (∀ x, x ∉ ["ot", "olen"] → σ'.vars x = σ.vars x) ∧
      (∀ a, a ≠ "ol" → σ'.arrs a = σ.arrs a) := by
  have hlen := hO.len
  -- the old contents
  let old : ℕ → Option ℕ := fun j => (σ.arrs "ol")[j]?
  let I : ℕ → Env → Prop := fun k τ => Ctx τ ∧ (∀ x, x ≠ "ot" → τ.vars x = σ.vars x) ∧
    (∀ a, a ≠ "ol" → τ.arrs a = σ.arrs a) ∧ (τ.arrs "ol").length = n ∧
    ∀ j, (τ.arrs "ol")[j]? = if l.length - k < j ∧ j ≤ l.length then old (j - 1) else old j
  obtain ⟨σ1, hr1, ⟨hC1, hv1, ha1, hl1, hg1⟩, -⟩ :=
    forUp_run (B := B) (i := "ot") (e := .sub (.var "olen") (.var "op"))
      (body := .store "ol" (.sub (.var "olen") (.var "ot"))
        (.get "ol" (.sub (.sub (.var "olen") (.var "ot")) (.lit 1)))) (N := l.length - p) (K := 20) I
      (by omega)
      (fun k _ τ hI _ => by
        have h1 := hI.2.1 "olen" (by decide)
        have h2 := hI.2.1 "op" (by decide)
        have := evalB_bin (op := .sub) (evalB_var (x := "olen") (σ := τ) (B := B)
          (by rw [h1, hlen]; omega)) (evalB_var (x := "op") (by rw [h2, hop]; omega))
          (by simp [h1, h2, hlen, hop]; omega)
        simpa [h1, h2, hlen, hop] using this)
      (σ := σ) ⟨hCv σ "ot" 0 hσ (by simp), fun x hx => by simp [hx], fun _ _ => rfl,
        by simp [hO.arr], fun j => by simp [old]⟩
      (by
        rintro k hk τ ⟨hCτ, hvτ, haτ, hlτ, hgτ⟩ hot
        have h1 := hvτ "olen" (by decide)
        have hj0 : p + 1 ≤ l.length - k := by omega
        have hidx : (Expr.sub (.var "olen") (.var "ot")).evalB B τ = some (l.length - k) := by
          have := evalB_bin (op := .sub) (evalB_var (x := "olen") (σ := τ) (B := B)
            (by rw [h1, hlen]; omega)) (evalB_var (x := "ot") (by rw [hot]; omega))
            (by simp [h1, hlen, hot]; omega)
          simpa [h1, hlen, hot] using this
        have hidx2 : (Expr.sub (.sub (.var "olen") (.var "ot")) (.lit 1)).evalB B τ =
            some (l.length - k - 1) := by
          have := evalB_bin (op := .sub) hidx (evalB_lit (n := 1) (by omega)) (by simp; omega)
          simpa using this
        have hget : (τ.arrs "ol")[l.length - k - 1]? = old (l.length - k - 1) := by
          rw [hgτ, if_neg (by omega)]
        have hold : ∃ x, old (l.length - k - 1) = some x ∧ x < n := by
          by_cases hpk : l.length - k - 1 < l.length
          · refine ⟨l[l.length - k - 1], hO.get _ hpk, hO.lt _ (List.getElem_mem _)⟩
          · omega
        obtain ⟨x, hx, hxn⟩ := hold
        refine ⟨τ.setArr "ol" (l.length - k) x, (Run.store hidx (evalB_get hidx2 (by rw [hget, hx])
          (by omega)) (by rw [hlτ]; omega)).mono (by simp), by simp [hot], ?_⟩
        refine ⟨hCv _ _ _ (hCa _ _ _ hCτ) (by simp), fun y hy => by simp [hy, hvτ y hy],
          fun a ha => by simp only [arrs_setVar, arrs_setArr, if_neg ha]; exact haτ a ha,
          by simp [hlτ], fun j => ?_⟩
        simp only [arrs_setVar, arrs_setArr, if_true, List.getElem?_set]
        by_cases hjk : l.length - k = j
        · subst hjk
          rw [if_pos rfl, if_pos (by rw [hlτ]; omega), if_pos ⟨by omega, by omega⟩, hx]
        · rw [if_neg hjk, hgτ]
          by_cases hj : l.length - k < j ∧ j ≤ l.length
          · rw [if_pos hj, if_pos ⟨by omega, hj.2⟩]
          · rw [if_neg hj, if_neg (by omega)])
  have hpv : σ1.vars "op" = p := by rw [hv1 "op" (by decide), hop]
  have huv : σ1.vars "ou" = u := by rw [hv1 "ou" (by decide), hou]
  have hlv : σ1.vars "olen" = l.length := by rw [hv1 "olen" (by decide), hlen]
  set σ2 := (σ1.setArr "ol" p u).setVar "olen" (l.length + 1) with hσ2
  have hr2 : Run B (.seq (.store "ol" (.var "op") (.var "ou"))
      (.assign "olen" (.add (.var "olen") (.lit 1)))) σ1 σ2 8 :=
    (Run.seq (Run.store (i := .var "op") (e := .var "ou") (idx := p) (v := u)
      (by simp [hpv]; omega) (by simp [huv]; omega) (by rw [hl1]; omega))
      (Run.assign (by simp [hlv]; omega))).mono (by simp)
  have hrun : Run B insAt σ σ2 (n * 30 + 30) := by
    refine (Run.seq hr1 hr2).mono ?_
    have : (l.length - p) * (20 + (Expr.sub (.var "olen") (.var "op")).size + 7) ≤ n * 30 := by
      simp; nlinarith
    simp at this ⊢; omega
  have hlen' : (l.take p ++ u :: l.drop p).length = l.length + 1 := by simp; omega
  refine ⟨σ2, hrun, hCv _ _ _ (hCa _ _ _ hC1) (by simp), ⟨by simp [hσ2, hlen'],
    by rw [hlen']; omega, by simp [hσ2, hl1], fun j hj => ?_, fun x hx => ?_⟩,
    fun x hx => ?_, fun a ha => ?_⟩
  · simp only [hσ2, arrs_setVar, arrs_setArr, if_true, List.getElem?_set]
    rw [hlen'] at hj
    by_cases hjp : p = j
    · subst hjp
      rw [if_pos rfl, if_pos (by rw [hl1]; omega)]
      simp [List.getElem_append_right (show (l.take p).length ≤ p by simp), min_eq_left hp]
    · rw [if_neg hjp, hg1]
      rcases Nat.lt_or_ge j p with hjp' | hjp'
      · rw [if_neg (by omega)]
        simp only [old]
        rw [hO.get j (by omega), List.getElem_append_left (by simp; omega)]
        simp [List.getElem_take]
      · rw [if_pos ⟨by omega, by omega⟩]
        simp only [old]
        rw [hO.get (j - 1) (by omega), List.getElem_append_right (by simp; omega)]
        simp only [List.length_take, min_eq_left hp]
        rw [List.getElem_cons, dif_neg (by omega), List.getElem_drop]
        simp only [show p + (j - p - 1) = j - 1 by omega]
  · simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | hx
    · exact hO.lt x (List.mem_of_mem_take hx)
    · exact hun
    · exact hO.lt x (List.mem_of_mem_drop hx)
  · simp at hx
    simp only [hσ2, vars_setVar, if_neg hx.2, vars_setArr]; exact hv1 x hx.1
  · simp only [hσ2, arrs_setVar, arrs_setArr, if_neg ha]; exact ha1 a ha

/-- One insertion: the step at `ns - 1 - oz`. -/
def insStep : Com :=
  .seq (.assign "ov" (.get "sv" (.sub (.sub (.var "ns") (.lit 1)) (.var "oz"))))
    (.seq (.assign "ou" (.get "su" (.sub (.sub (.var "ns") (.lit 1)) (.var "oz"))))
      (.seq findPos insAt))

/-- All insertions. -/
def insLoop : Com := forUp "oz" (.var "ns") insStep

/-- The insertion of the steps `Sn`, the most recent first. -/
def insAll (l : List ℕ) (Sn : List (ℕ × ℕ)) : List ℕ :=
  Sn.foldl (fun l p => insAfterN p.2 p.1 l) l

theorem insAll_take_succ (l : List ℕ) (Sn : List (ℕ × ℕ)) {k : ℕ} (hk : k < Sn.length) :
    insAll l (Sn.take (k + 1)) = insAfterN Sn[k].2 Sn[k].1 (insAll l (Sn.take k)) := by
  unfold insAll
  rw [List.take_succ_eq_append_getElem hk, List.foldl_append]
  rfl

theorem length_insAfterN (v u : ℕ) (l : List ℕ) : (insAfterN v u l).length = l.length + 1 := by
  induction l with
  | nil => simp [insAfterN]
  | cons a l ih => simp only [insAfterN]; split_ifs <;> simp [ih]

theorem length_insAll (l : List ℕ) (Sn : List (ℕ × ℕ)) :
    (insAll l Sn).length = l.length + Sn.length := by
  induction Sn generalizing l with
  | nil => simp [insAll]
  | cons p Sn ih =>
    simp only [insAll, List.foldl_cons] at ih ⊢
    rw [ih, length_insAfterN]; simp; ring

theorem OlAt.setVar {n : ℕ} {l : List ℕ} {τ : Env} (h : OlAt n l τ) {x : String}
    (hx : x ≠ "olen") (v : ℕ) : OlAt n l (τ.setVar x v) :=
  ⟨by simp [Ne.symm hx, h.len], h.room, by simp [h.arr], fun k hk => by simpa using h.get k hk,
    h.lt⟩

theorem OlAt.of_arr {n : ℕ} {l : List ℕ} {τ τ' : Env} (h : OlAt n l τ)
    (hv : τ'.vars "olen" = τ.vars "olen") (ha : τ'.arrs "ol" = τ.arrs "ol") : OlAt n l τ' :=
  ⟨by rw [hv, h.len], h.room, by rw [ha, h.arr], fun k hk => by rw [ha]; exact h.get k hk, h.lt⟩

theorem insStep_body {B n : ℕ} {l0 : List ℕ} {Sn : List (ℕ × ℕ)} {Ctx : Env → Prop}
    (hnB : n + 2 < B) (hlen : l0.length + Sn.length ≤ n)
    (hSn : ∀ p ∈ Sn, p.1 < n ∧ p.2 < n)
    (hCv : ∀ τ x v, Ctx τ → x ∈ ["oz", "ov", "ou", "op", "oi", "ot", "olen"] → Ctx (τ.setVar x v))
    (hCa : ∀ τ i v, Ctx τ → Ctx (τ.setArr "ol" i v)) {k : ℕ} (hk : k < Sn.length) {σ τ : Env}
    (hCτ : Ctx τ) (hOτ : OlAt n (insAll l0 (Sn.take k)) τ)
    (hvτ : ∀ x, x ∉ ["oz", "ov", "ou", "op", "oi", "ot", "olen"] → τ.vars x = σ.vars x)
    (haτ : ∀ a, a ≠ "ol" → τ.arrs a = σ.arrs a) (hoz : τ.vars "oz" = k)
    (hns : σ.vars "ns" = Sn.length)
    (hsu : ∀ j (h : j < Sn.length), (σ.arrs "su")[j]? = some (Sn[Sn.length - 1 - j]'(by omega)).1)
    (hsv : ∀ j (h : j < Sn.length), (σ.arrs "sv")[j]? = some (Sn[Sn.length - 1 - j]'(by omega)).2) :
    ∃ τ', Run B insStep τ τ' (n * 50 + 100) ∧ τ'.vars "oz" = k ∧
      Ctx (τ'.setVar "oz" (k + 1)) ∧ OlAt n (insAll l0 (Sn.take (k + 1))) (τ'.setVar "oz" (k + 1)) ∧
      (∀ x, x ∉ ["oz", "ov", "ou", "op", "oi", "ot", "olen"] →
        (τ'.setVar "oz" (k + 1)).vars x = σ.vars x) ∧
      (∀ a, a ≠ "ol" → (τ'.setVar "oz" (k + 1)).arrs a = σ.arrs a) := by
  set N := Sn.length with hN
  set l := insAll l0 (Sn.take k) with hl
  have hlenl : l.length = l0.length + k := by
    rw [hl, length_insAll, List.length_take, min_eq_left (by omega)]
  have hnsτ : τ.vars "ns" = N := by rw [hvτ "ns" (by simp), hns]
  have hj : N - 1 - k < N := by omega
  have hjj : N - 1 - (N - 1 - k) = k := by omega
  have hidx : ∀ ρ : Env, ρ.vars "ns" = N → ρ.vars "oz" = k →
      (Expr.sub (.sub (.var "ns") (.lit 1)) (.var "oz")).evalB B ρ = some (N - 1 - k) := by
    intro ρ h1 h2
    have := evalB_bin (op := .sub) (evalB_bin (op := .sub) (evalB_var (x := "ns") (σ := ρ)
      (B := B) (by rw [h1]; omega)) (evalB_lit (n := 1) (by omega)) (by simp [h1]; omega))
      (evalB_var (x := "oz") (by rw [h2]; omega)) (by simp [h1, h2]; omega)
    simpa [h1, h2] using this
  have hSk := hSn Sn[k] (List.getElem_mem hk)
  have hsv' : (τ.arrs "sv")[N - 1 - k]? = some Sn[k].2 := by
    rw [haτ "sv" (by decide), hsv _ hj]; congr 2; exact getElem_congr_idx hjj
  have hsu' : (τ.arrs "su")[N - 1 - k]? = some Sn[k].1 := by
    rw [haτ "su" (by decide), hsu _ hj]; congr 2; exact getElem_congr_idx hjj
  have hr1 : Run B (.assign "ov" (.get "sv" (.sub (.sub (.var "ns") (.lit 1)) (.var "oz"))))
      τ (τ.setVar "ov" Sn[k].2) 9 :=
    (Run.assign (evalB_get (hidx τ hnsτ hoz) hsv' (by omega))).mono (by simp)
  have hr2 : Run B (.assign "ou" (.get "su" (.sub (.sub (.var "ns") (.lit 1)) (.var "oz"))))
      (τ.setVar "ov" Sn[k].2) ((τ.setVar "ov" Sn[k].2).setVar "ou" Sn[k].1) 9 :=
    (Run.assign (evalB_get (hidx _ (by simp [hnsτ]) (by simp [hoz])) (by simpa using hsu')
      (by omega))).mono (by simp)
  set τ2 := (τ.setVar "ov" Sn[k].2).setVar "ou" Sn[k].1 with hτ2
  have hO2 : OlAt n l τ2 := (hOτ.setVar (by decide) _).setVar (by decide) _
  have hCf : ∀ ρ x u, (Ctx ρ ∧ OlAt n l ρ ∧ (∀ x, x ∉ ["op", "oi"] → ρ.vars x = τ2.vars x) ∧
      ρ.arrs = τ2.arrs) → x ∈ ["op", "oi"] → (Ctx (ρ.setVar x u) ∧ OlAt n l (ρ.setVar x u) ∧
      (∀ y, y ∉ ["op", "oi"] → (ρ.setVar x u).vars y = τ2.vars y) ∧ (ρ.setVar x u).arrs = τ2.arrs) := by
    intro ρ x u h hx
    have hx' : x ≠ "olen" := by simp at hx; rcases hx with rfl | rfl <;> decide
    refine ⟨hCv _ _ _ h.1 (by simp at hx ⊢; tauto), h.2.1.setVar hx' u, fun y hy => ?_, h.2.2.2⟩
    have : y ≠ x := by intro e; subst e; exact hy hx
    simp [this, h.2.2.1 y hy]
  obtain ⟨τ3, hr3, ⟨hC3, hO3, hv3, ha3⟩, hop3⟩ :=
    findPos_run (B := B) (n := n) (l := l) (v := Sn[k].2)
      (fun ρ => Ctx ρ ∧ OlAt n l ρ ∧ (∀ x, x ∉ ["op", "oi"] → ρ.vars x = τ2.vars x) ∧
        ρ.arrs = τ2.arrs) hnB hSk.2
      (fun ρ h => ⟨h.2.1, by rw [h.2.2.1 "ov" (by decide)]; simp [hτ2]⟩) hCf
      ⟨hCv _ _ _ (hCv _ _ _ hCτ (by simp)) (by simp), hO2, fun _ _ => rfl, rfl⟩
  obtain ⟨τ4, hr4, hC4, hO4, hv4, ha4⟩ :=
    insAt_run (B := B) (n := n) (l := l) (p := min (l.idxOf Sn[k].2 + 1) l.length)
      (u := Sn[k].1) Ctx hnB hSk.1 (by omega) (by omega)
      (fun ρ x v h hx => hCv _ _ _ h (by simp at hx ⊢; tauto)) hCa hC3 hO3 hop3
      (by rw [hv3 "ou" (by decide)]; simp [hτ2])
  rw [← insAfterN_eq] at hO4
  refine ⟨τ4, (Run.seq hr1 (Run.seq hr2 (Run.seq hr3 hr4))).mono (by omega), ?_,
    hCv _ _ _ hC4 (by simp), ?_, fun x hx => ?_, fun a ha => ?_⟩
  · rw [hv4 "oz" (by decide), hv3 "oz" (by decide)]; simp [hτ2, hoz]
  · rw [insAll_take_succ l0 Sn hk, ← hl]
    exact hO4.setVar (by decide) _
  · have h1 : x ∉ ["ot", "olen"] := fun h => hx (by simp at h ⊢; tauto)
    have h2 : x ∉ ["op", "oi"] := fun h => hx (by simp at h ⊢; tauto)
    have h3 : x ≠ "oz" := fun h => hx (by simp [h])
    have h4 : x ≠ "ou" := fun h => hx (by simp [h])
    have h5 : x ≠ "ov" := fun h => hx (by simp [h])
    simp only [vars_setVar, if_neg h3]
    rw [hv4 x h1, hv3 x h2]
    simp [hτ2, h4, h5, hvτ x hx]
  · simp only [arrs_setVar]
    rw [ha4 a ha, ha3]; simp [hτ2, haτ a ha]

theorem insLoop_run {B n : ℕ} {l0 : List ℕ} {Sn : List (ℕ × ℕ)} (Ctx : Env → Prop)
    (hnB : n + 2 < B) (hlen : l0.length + Sn.length ≤ n)
    (hSn : ∀ p ∈ Sn, p.1 < n ∧ p.2 < n)
    (hCv : ∀ τ x v, Ctx τ → x ∈ ["oz", "ov", "ou", "op", "oi", "ot", "olen"] → Ctx (τ.setVar x v))
    (hCa : ∀ τ i v, Ctx τ → Ctx (τ.setArr "ol" i v))
    {σ : Env} (hσ : Ctx σ) (hO : OlAt n l0 σ) (hns : σ.vars "ns" = Sn.length)
    (hsu : ∀ j (h : j < Sn.length), (σ.arrs "su")[j]? = some (Sn[Sn.length - 1 - j]'(by omega)).1)
    (hsv : ∀ j (h : j < Sn.length), (σ.arrs "sv")[j]? = some (Sn[Sn.length - 1 - j]'(by omega)).2) :
    ∃ σ', Run B insLoop σ σ' (n * (n * 60 + 120) + 10) ∧ Ctx σ' ∧ OlAt n (insAll l0 Sn) σ' ∧
      (∀ a, a ≠ "ol" → σ'.arrs a = σ.arrs a) := by
  set N := Sn.length with hN
  let W : List String := ["oz", "ov", "ou", "op", "oi", "ot", "olen"]
  let I : ℕ → Env → Prop := fun k τ => Ctx τ ∧ OlAt n (insAll l0 (Sn.take k)) τ ∧
    (∀ x, x ∉ W → τ.vars x = σ.vars x) ∧ (∀ a, a ≠ "ol" → τ.arrs a = σ.arrs a)
  have hI0 : I 0 (σ.setVar "oz" 0) := by
    refine ⟨hCv _ _ _ hσ (by simp), ?_, fun x hx => ?_, fun a _ => rfl⟩
    · rw [show insAll l0 (Sn.take 0) = l0 by simp [insAll]]
      exact hO.setVar (by decide) 0
    · have : x ≠ "oz" := by intro e; subst e; simp [W] at hx
      simp [this]
  obtain ⟨σ', hr, ⟨hC', hO', hv', ha'⟩, -⟩ :=
    forUp_run (B := B) (i := "oz") (e := .var "ns") (body := insStep) (N := N)
      (K := n * 50 + 100) I (by omega)
      (fun k _ τ hI _ => by
        have := hI.2.2.1 "ns" (by simp [W])
        rw [evalB_var (by rw [this, hns]; omega), this, hns])
      hI0
      (by
        rintro k hk τ ⟨hCτ, hOτ, hvτ, haτ⟩ hoz
        exact insStep_body hnB hlen hSn hCv hCa hk hCτ hOτ hvτ haτ hoz hns hsu hsv)
  refine ⟨σ', hr.mono ?_, hC', ?_, ha'⟩
  · have : N * (n * 50 + 100 + 1 + 7) ≤ n * (n * 50 + 108) := Nat.mul_le_mul_right _ (by omega)
    simp only [Expr.size] at this ⊢; nlinarith
  · rw [show Sn.take N = Sn from List.take_length] at hO'; exact hO'

/-! ### From the steps to the positions -/

theorem foldl_map_val {n : ℕ} (steps : List (Fin n × Fin n)) (l : List (Fin n)) :
    (steps.foldl (fun l p => insertAfter p.2 p.1 l) l).map Fin.val =
      insAll (l.map Fin.val) (steps.map fun p => ((p.1 : ℕ), (p.2 : ℕ))) := by
  induction steps generalizing l with
  | nil => simp [insAll]
  | cons p steps ih =>
    simp only [List.foldl_cons, List.map_cons, insAll] at ih ⊢
    rw [ih, map_insertAfter]

/-- **The Welzl ordering on numbers.** -/
theorem welzlOrder_val {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    (welzlOrder G).map Fin.val = insAll (below n fun u => inBN (welzlTree G).active u)
      ((welzlTree G).steps.map fun p => ((p.1 : ℕ), (p.2 : ℕ))) := by
  unfold welzlOrder
  rw [foldl_map_val]
  congr 1
  exact sortedVals_eq_below _ _ fun u => ⟨fun h => ⟨u.2, h⟩, fun ⟨_, h⟩ => h⟩

theorem idxOf_map_val {n : ℕ} (l : List (Fin n)) (x : Fin n) :
    (l.map Fin.val).idxOf (x : ℕ) = l.idxOf x := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.idxOf_cons]
    by_cases h : a = x
    · subst h; simp
    · have h1 : ((a : ℕ) == (x : ℕ)) = false := by simp [Fin.val_ne_of_ne h]
      have h2 : (a == x) = false := by simp [h]
      rw [h1, h2]; simp [ih]

theorem posN_welzl {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] {z : ℕ} (hz : z < n) :
    posN (welzlVOrder G) z = ((welzlOrder G).map Fin.val).idxOf z := by
  simp only [posN, dif_pos hz, welzlVOrder, listOrder]
  exact (idxOf_map_val (welzlOrder G) ⟨z, hz⟩).symm

/-! ### The first list and the positions -/

/-- The list of the vertices `u` with `act[u] = 1`, in increasing order. -/
def initOl : Com :=
  .seq (.assign "olen" (.lit 0)) (forUp "ou" (.var "n")
    (.ite (.eq (.get "act" (.var "ou")) (.lit 1))
      (.seq (.store "ol" (.var "olen") (.var "ou")) (.assign "olen" (.add (.var "olen") (.lit 1))))
      .skip))

theorem initOl_run {B n : ℕ} {Act : Finset (Fin n)} (hnB : n + 2 < B) {σ : Env}
    (hn : σ.vars "n" = n) (hact : Vec σ "act" n (fun u => ind (inBN Act u)))
    (hol : (σ.arrs "ol").length = n) :
    ∃ σ', Run B initOl σ σ' (n * 30 + 10) ∧ OlAt n (below n fun u => inBN Act u) σ' ∧
      (∀ x, x ∉ ["olen", "ou"] → σ'.vars x = σ.vars x) ∧
      (∀ a, a ≠ "ol" → σ'.arrs a = σ.arrs a) := by
  classical
  let I : ℕ → Env → Prop := fun k τ => OlAt n (below k fun u => inBN Act u) τ ∧
    (∀ x, x ∉ ["olen", "ou"] → τ.vars x = σ.vars x) ∧ (∀ a, a ≠ "ol" → τ.arrs a = σ.arrs a)
  have hbl : ∀ k, k ≤ n → (below k fun u => inBN Act u).length ≤ k := fun k _ => length_below_le k _
  obtain ⟨σ', hr, hI', -⟩ :=
    forUp_run (B := B) (i := "ou") (e := .var "n")
      (body := .ite (.eq (.get "act" (.var "ou")) (.lit 1))
        (.seq (.store "ol" (.var "olen") (.var "ou")) (.assign "olen" (.add (.var "olen") (.lit 1))))
        .skip) (N := n) (K := 20) I (by omega)
      (fun k _ τ hI _ => by
        rw [evalB_var (by rw [hI.2.1 "n" (by decide), hn]; omega), hI.2.1 "n" (by decide), hn])
      (σ := σ.setVar "olen" 0)
      ⟨⟨by simp [below], by simp [below], by simp [hol], fun k hk => by simp [below] at hk,
        fun x hx => by simp [below] at hx⟩, fun x hx => by
          have h1 : x ≠ "olen" := by intro e; subst e; simp at hx
          have h2 : x ≠ "ou" := by intro e; subst e; simp at hx
          simp [h1, h2], fun a _ => rfl⟩
      (by
        rintro k hk τ ⟨hO, hv, ha⟩ hou
        have hbs := below_succ k (fun u => inBN Act u)
        have hlk := hbl k (by omega)
        have hev : (Cond.eq (.get "act" (.var "ou")) (.lit 1)).evalB B τ =
            some (decide (ind (inBN Act k) = 1)) :=
          evalB_condEq' ((hact.of_eq (ha "act" (by decide))).evalB hou hk (by omega)
            (by have := ind_le_one (inBN Act k); omega)) (evalB_lit (by omega))
        by_cases hin : inBN Act k
        · refine ⟨(τ.setArr "ol" (below k fun u => inBN Act u).length k).setVar "olen"
            ((below k fun u => inBN Act u).length + 1), (Run.ite_true (by rw [hev]; simp [ind, hin])
            (Run.seq (Run.store (i := .var "olen") (e := .var "ou") (by simp [hO.len]; omega)
              (by simp [hou]; omega) (by rw [hO.arr]; omega))
              (Run.assign (by simp [hO.len]; omega)))).mono (by simp), by simp [hou], ?_⟩
          refine ⟨⟨by simp [hbs, hin], by simp [hbs, hin]; omega, by simp [hO.arr], fun j hj => ?_,
            fun x hx => ?_⟩, fun x hx => ?_, fun a ha' => ?_⟩
          · simp only [hbs, if_pos hin, List.length_append, List.length_singleton] at hj
            simp only [arrs_setVar, arrs_setArr, if_true, List.getElem?_set, hbs, if_pos hin]
            by_cases hjl : (below k fun u => inBN Act u).length = j
            · subst hjl; simp [hO.arr, show (below k fun u => inBN Act u).length < n by omega]
            · rw [if_neg hjl, hO.get j (by omega), List.getElem_append_left (by omega)]
          · simp only [hbs, if_pos hin, List.mem_append, List.mem_singleton] at hx
            rcases hx with hx | rfl
            · exact hO.lt x hx
            · exact hk
          · simp at hx
            simp [hx.1, hx.2, hv x (by simp [hx.1, hx.2])]
          · simp only [arrs_setVar, arrs_setArr, if_neg ha']; exact ha a ha'
        · refine ⟨τ, (Run.ite_false (by rw [hev]; simp [ind, hin]) Run.skip).mono (by simp),
            hou, ?_⟩
          refine ⟨⟨by simp [hbs, hin, hO.len], by simp [hbs, hin]; omega, by simp [hO.arr],
            fun j hj => by simpa [hbs, hin] using hO.get j (by simpa [hbs, hin] using hj),
            fun x hx => hO.lt x (by simpa [hbs, hin] using hx)⟩, fun x hx => ?_, fun a ha' => ?_⟩
          · simp at hx; simp [hx.2, hv x (by simp [hx.1, hx.2])]
          · simpa using ha a ha')
  obtain ⟨hO', hv', ha'⟩ := hI'
  refine ⟨σ', (Run.seq (Run.assign (v := 0) (by simp; omega)) hr).mono (by simp; omega), hO',
    fun x hx => ?_, ha'⟩
  rw [hv' x hx]

/-- The positions of the list. -/
def posFill : Com := forUp "ok" (.var "olen") (.store "pos" (.get "ol" (.var "ok")) (.var "ok"))

theorem posFill_run {B n : ℕ} {l : List ℕ} (hnB : n + 2 < B) (hnd : l.Nodup) {σ : Env}
    (hO : OlAt n l σ) (hpos : (σ.arrs "pos").length = n) :
    ∃ σ', Run B posFill σ σ' (n * 20 + 10) ∧
      (∀ j (h : j < l.length), (σ'.arrs "pos")[l[j]]? = some j) ∧
      (σ'.arrs "pos").length = n ∧
      (∀ x, x ≠ "ok" → σ'.vars x = σ.vars x) ∧ (∀ a, a ≠ "pos" → σ'.arrs a = σ.arrs a) := by
  let I : ℕ → Env → Prop := fun k τ => (∀ x, x ≠ "ok" → τ.vars x = σ.vars x) ∧
    (∀ a, a ≠ "pos" → τ.arrs a = σ.arrs a) ∧ (τ.arrs "pos").length = n ∧
    ∀ j (h : j < l.length), j < k → (τ.arrs "pos")[l[j]]? = some j
  obtain ⟨σ', hr, ⟨hv, ha, hl, hg⟩, -⟩ :=
    forUp_run (B := B) (i := "ok") (e := .var "olen")
      (body := .store "pos" (.get "ol" (.var "ok")) (.var "ok")) (N := l.length) (K := 10) I
      (by have := hO.room; omega)
      (fun k _ τ hI _ => by
        rw [evalB_var (by rw [hI.1 "olen" (by decide), hO.len]; have := hO.room; omega),
          hI.1 "olen" (by decide), hO.len])
      (σ := σ) ⟨fun x hx => by simp [hx], fun _ _ => rfl, by simp [hpos],
        fun j _ hj => absurd hj (Nat.not_lt_zero _)⟩
      (by
        rintro k hk τ ⟨hv, ha, hl, hg⟩ hok
        have hroom := hO.room
        have hlk := hO.lt _ (List.getElem_mem hk)
        have hgk : (τ.arrs "ol")[k]? = some l[k] := by rw [ha "ol" (by decide)]; exact hO.get k hk
        have hev : (Expr.get "ol" (.var "ok")).evalB B τ = some l[k] :=
          evalB_get (evalB_var (by rw [hok]; omega)) (by rw [hok]; exact hgk) (by omega)
        refine ⟨τ.setArr "pos" l[k] k, (Run.store (i := .get "ol" (.var "ok")) (e := .var "ok")
          hev (by simp [hok]; omega) (by rw [hl]; exact hlk)).mono
          (by simp), by simp [hok], fun x hx => by simp [hx, hv x hx],
          fun a ha' => by simp only [arrs_setVar, arrs_setArr, if_neg ha']; exact ha a ha',
          by simp [hl], fun j hj hjk => ?_⟩
        simp only [arrs_setVar, arrs_setArr, if_true, List.getElem?_set]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hjk with hjk | rfl
        · have hne : l[k] ≠ l[j] := fun e => by
            have := (List.Nodup.getElem_inj_iff hnd).1 e; omega
          rw [if_neg hne]; exact hg j hj hjk
        · simp [hl, hlk])
  exact ⟨σ', hr.mono (by have := hO.room; simp; nlinarith), fun j hj => hg j hj hj, hl, hv, ha⟩

/-- The steps of the greedy procedure on numbers, the most recent first. -/
def wSteps {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] : List (ℕ × ℕ) :=
  (welzlTree G).steps.map fun p => ((p.1 : ℕ), (p.2 : ℕ))

/-- **The ordering.** -/
def ordCom : Com := .seq initOl (.seq insLoop posFill)

theorem ordCom_run {B n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hnB : n + 2 < B)
    {σ : Env} (hn : σ.vars "n" = n)
    (hact : Vec σ "act" n (fun u => ind (inBN (welzlTree G).active u)))
    (hns : σ.vars "ns" = (wSteps G).length)
    (hsu : ∀ j (h : j < (wSteps G).length), (σ.arrs "su")[j]? =
      some ((wSteps G)[(wSteps G).length - 1 - j]'(by omega)).1)
    (hsv : ∀ j (h : j < (wSteps G).length), (σ.arrs "sv")[j]? =
      some ((wSteps G)[(wSteps G).length - 1 - j]'(by omega)).2)
    (hol : (σ.arrs "ol").length = n) (hpos : (σ.arrs "pos").length = n) :
    ∃ σ', Run B ordCom σ σ' (n * (n * 60 + 200) + 40) ∧
      Vec σ' "pos" n (posN (welzlVOrder G)) ∧
      (∀ x, x ∉ ["olen", "ou", "oz", "ov", "op", "oi", "ot", "ok"] → σ'.vars x = σ.vars x) ∧
      (∀ a, a ∉ ["ol", "pos"] → σ'.arrs a = σ.arrs a) := by
  set Sn := wSteps G with hSn
  set l0 := below n fun u => inBN (welzlTree G).active u with hl0
  have hfinal : insAll l0 Sn = (welzlOrder G).map Fin.val := (welzlOrder_val G).symm
  have hlen : l0.length + Sn.length = n := by
    have := congrArg List.length hfinal
    rw [length_insAll] at this
    simp only [List.length_map] at this
    rw [this]
    have := (welzlOrder_spec (G := G)).1
    have h2 := List.toFinset_card_of_nodup this
    rw [show (welzlOrder G).toFinset = univ from
      Finset.eq_univ_of_forall fun x => List.mem_toFinset.2 (mem_welzlOrder x)] at h2
    simpa using h2.symm
  obtain ⟨σ1, hr1, hO1, hv1, ha1⟩ := initOl_run (B := B) (Act := (welzlTree G).active) hnB hn hact hol
  obtain ⟨σ2, hr2, hC2, hO2, ha2⟩ :=
    insLoop_run (B := B) (n := n) (l0 := l0) (Sn := Sn)
      (fun τ => ∀ x, x ∉ ["olen", "ou", "oz", "ov", "op", "oi", "ot", "ok"] → τ.vars x = σ.vars x)
      hnB (by omega)
      (fun p hp => by
        simp only [hSn, wSteps, List.mem_map] at hp
        obtain ⟨q, -, rfl⟩ := hp; exact ⟨q.1.2, q.2.2⟩)
      (fun τ x v h hx y hy => by
        have : y ≠ x := by intro e; subst e; simp at hx hy; tauto
        simp [this, h y hy])
      (fun τ i v h => h) (fun x hx => hv1 x (by simp at hx ⊢; tauto)) hO1
      (by rw [hv1 "ns" (by decide), hns])
      (fun j hj => by rw [ha1 "su" (by decide)]; exact hsu j hj)
      (fun j hj => by rw [ha1 "sv" (by decide)]; exact hsv j hj)
  rw [hfinal] at hO2
  obtain ⟨σ3, hr3, hp3, hl3, hv3, ha3⟩ :=
    posFill_run (B := B) hnB ((List.nodup_map_iff Fin.val_injective).2 welzlOrder_nodup) hO2
      (by rw [ha2 "pos" (by decide), ha1 "pos" (by decide), hpos])
  refine ⟨σ3, (Run.seq hr1 (Run.seq hr2 hr3)).mono (by nlinarith), ⟨hl3, fun z hz => ?_⟩,
    fun x hx => ?_, fun a ha => ?_⟩
  · have hmem : z ∈ (welzlOrder G).map Fin.val := by
      simp only [List.mem_map]; exact ⟨⟨z, hz⟩, mem_welzlOrder _, rfl⟩
    have hidx := List.idxOf_lt_length_of_mem hmem
    have := hp3 _ hidx
    rw [List.getElem_idxOf hidx] at this
    rw [this, posN_welzl G hz]
  · rw [hv3 x (by intro e; subst e; simp at hx)]
    exact hC2 x hx
  · rw [ha3 a (by intro e; subst e; simp at ha), ha2 a (by intro e; subst e; simp at ha),
      ha1 a (by intro e; subst e; simp at ha)]

end Lax185574Proofs.Chain.Ram
