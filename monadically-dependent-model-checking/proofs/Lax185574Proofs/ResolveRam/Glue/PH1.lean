import Lax185574Proofs.ResolveRam.Glue.PH0
import Lax185574Proofs.ResolveRam.Glue.PCT4
import Lax185574Proofs.Words.FinsetRead

/-!
The word of the resolved graph as a tape program.

`hIn` reads the input of the composite: it writes `n` and the colors as
it reads them (`rdCoW`), reads the edges and the non-edges into the
`n × n` matrices `E` and `N` (`rdG`), reads `P`, `Q` and the sign, fills
the matrix `Rm` of the edges after the resolve (`rsE`) and writes it
with Conversions `writeGraph`, and then the same for the non-edges
(`hIn_run`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.Conversions.Ram
open Lax185574Proofs.StpRam Lax185574.PartialGraphs Lax185574.WordEncoding Lax185574Proofs.ResolveRam
open Lax185574.PartialGraphEncoding Finset

variable {n : ℕ}

/-! ### Reading the colors -/

/-- Read the colors into `co` and write them. -/
def rdCoW : Com :=
  forUp "v" (.var "n") (.seq (.read "cx") (.seq (.store "co" (.var "v") (.var "cx")) (.write (.var "cx"))))

theorem rdCoW_run {B : ℕ} (G : PartialGraph (Fin n)) {σ : Env} {rest : List ℕ}
    (hinp : σ.inp = List.ofFn G.color ++ rest) (hn : σ.vars "n" = n) (hco : (σ.arrs "co").length = n)
    (hnB : n < B) (hcB : ∀ v < n, colN G v < B) :
    ∃ σ', Run B rdCoW σ σ' (n * 19 + 6) ∧ σ'.inp = rest ∧ σ'.arrs "co" = arrOf n (colN G) ∧
      (∀ x, x ∉ ["v", "cx"] → σ'.vars x = σ.vars x) ∧ (∀ a, a ≠ "co" → σ'.arrs a = σ.arrs a) ∧
      σ'.out = σ.out ++ List.ofFn G.color := by
  have hcol : ∀ k (hk : k < n), (List.ofFn G.color)[k]'(by simpa using hk) = colN G k := by
    intro k hk; simp [colN, hk]
  let I : ℕ → Env → Prop := fun k τ => τ.inp = (List.ofFn G.color).drop k ++ rest ∧
    (τ.arrs "co").length = n ∧ (∀ j < k, (τ.arrs "co")[j]? = some (colN G j)) ∧
    (∀ x, x ∉ ["v", "cx"] → τ.vars x = σ.vars x) ∧ (∀ a, a ≠ "co" → τ.arrs a = σ.arrs a) ∧
    τ.out = σ.out ++ (List.ofFn G.color).take k
  obtain ⟨σ', r, ⟨h1, h2, h3, h4, h5, h6⟩, -⟩ := forUp_run (B := B) (i := "v") (e := .var "n")
    (body := .seq (.read "cx") (.seq (.store "co" (.var "v") (.var "cx")) (.write (.var "cx")))) (N := n)
    (K := 11) I (σ := σ) hnB
    (fun k _ τ hI _ => by rw [evalB_var_iff, hI.2.2.2.1 "n" (by decide), hn]; omega)
    ⟨by simp [hinp], by simp [hco], fun j hj => absurd hj (Nat.not_lt_zero _),
      fun x hx => by simp at hx; simp [hx.1], fun a _ => by simp, by simp⟩
    (by
      rintro k hk τ ⟨hin, hl, hg, hv, ha, ho⟩ hvk
      have hkl : k < (List.ofFn G.color).length := by simpa using hk
      have hd : (List.ofFn G.color).drop k = colN G k :: (List.ofFn G.color).drop (k + 1) := by
        rw [List.drop_eq_getElem_cons hkl, hcol k hk]
      set τ1 : Env := { τ.setVar "cx" (colN G k) with inp := (List.ofFn G.color).drop (k + 1) ++ rest }
      have r1 : Run B (.read "cx") τ τ1 1 := Run.read (by rw [hin, hd]; rfl)
      set τ2 := τ1.setArr "co" k (colN G k)
      have r2 : Run B (.store "co" (.var "v") (.var "cx")) τ1 τ2 3 :=
        (Run.store (by simp [τ1, hvk]; omega) (by simp [τ1]; exact hcB k hk) (by simp [τ1, hl, hk])).mono
          (by simp)
      have r3 : Run B (.write (.var "cx")) τ2 { τ2 with out := τ2.out ++ [colN G k] } 2 :=
        (Run.write (by simp [τ2, τ1]; exact hcB k hk)).mono (by simp)
      refine ⟨_, (Run.seq r1 (Run.seq r2 r3)).mono (by omega), by simp [τ2, τ1, hvk], by simp [τ2, τ1],
        by simp [τ2, τ1, hl], fun j hj => ?_, fun x hx => ?_, fun a ha' => by simp [τ2, τ1, ha', ha a ha'], ?_⟩
      · simp only [arrs_setVar, arrs_setArr, if_true, τ2, τ1]
        rw [List.getElem?_set]
        rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
        · simp [show k ≠ j by omega, hg j h]
        · simp [hl, hk]
      · simp at hx; simp [τ2, τ1, hx.1, hx.2, hv x (by simp [hx.1, hx.2])]
      · simp only [τ2, τ1, out_setVar, out_setArr, ho, List.take_add_one, List.getElem?_eq_getElem hkl,
          Option.toList_some, List.append_assoc, hcol k hk])
  refine ⟨σ', r.mono (by simp only [Expr.size]; omega), by rw [h1, List.drop_eq_nil_of_le (by simp)]; rfl,
    ?_, h4, h5, by rw [h6, List.take_of_length_le (by simp)]⟩
  refine List.ext_getElem (by rw [h2]; simp) fun j hj _ => ?_
  have := h3 j (by omega)
  rw [List.getElem?_eq_getElem hj] at this
  simp only [Option.some.injEq] at this
  rw [this]; simp [arrOf]

/-! ### Reading a graph into a matrix -/

open Classical in
/-- The neighborhoods of a graph, as its word lists them. -/
noncomputable def nbhs (H : SimpleGraph (Fin n)) : List (Finset (Fin n)) :=
  List.ofFn fun v : Fin n => univ.filter (H.Adj v)

theorem matZ_eq {τ : Env} {a : String} (h : Mat τ a n fun _ _ => 0) :
    τ.arrs a = List.replicate (n * n) 0 := by
  refine List.ext_getElem (by rw [h.len]; simp) fun k h1 h2 => ?_
  rw [List.getElem_replicate]
  have hk : k < n * n := by rw [h.len] at h1; exact h1
  have hn : 0 < n := by rcases Nat.eq_zero_or_pos n with h0 | h0 <;> [simp [h0] at hk; exact h0]
  have := h.get (k / n) (by rw [Nat.div_lt_iff_lt_mul hn]; exact hk) (k % n) (Nat.mod_lt _ hn)
  rw [Nat.div_add_mod' k n] at this
  rw [List.getElem?_eq_getElem h1] at this
  exact Option.some.inj this

/-- Read the word of a graph into the matrix `arr`. -/
def rdG (arr : String) : Com := .seq (.read "c0") (.seq (matFill arr (.lit 0)) (readRows arr "n"))

theorem rdG_run {B : ℕ} (H : SimpleGraph (Fin n)) {arr : String} {σ : Env}
    {rest : List ℕ} (hinp : σ.inp = toWord H ++ rest) (hn : σ.vars "n" = n)
    (hl : (σ.arrs arr).length = n * n) (hB : n * n + n + 1 < B) :
    ∃ σ', Run B (rdG arr) σ σ' (n * (n * 15 + 14) + n * (17 * n + 15) + 20) ∧ σ'.inp = rest ∧
      Mat σ' arr n (fun u v => ind (Conversions.Ram.gA H u v)) ∧ (∀ a, a ≠ arr → σ'.arrs a = σ.arrs a) ∧
      (∀ x, x ∉ (rdG arr).wvars → σ'.vars x = σ.vars x) ∧ σ'.out = σ.out := by
  classical
  have hL : (nbhs H).length = n := by simp [nbhs]
  have hw : toWord H = (nbhs H).length :: ((nbhs H).map toWord).flatten := rfl
  rw [hw, hL] at hinp
  set σ1 : Env := { σ.setVar "c0" n with inp := ((nbhs H).map toWord).flatten ++ rest }
  have r1 : Run B (.read "c0") σ σ1 1 := Run.read (by rw [hinp]; rfl)
  obtain ⟨σ2, r2, hn2, hm2⟩ := matFill_run (B := B) (n := n) (K := 7) (arr := arr) (e := .lit 0)
    (fun τ => τ.vars "n" = n) (fun _ _ => 0) hB (fun τ h => h) (fun τ x h => by simp [h])
    (fun τ x h => by simp [h]) (fun τ i x h => by simp [h]) (fun τ i j _ _ _ _ _ => by simp; omega)
    (by simp) (σ := σ1) (by simp [σ1, hn]) (by simp [σ1, hl])
  have hz := matZ_eq hm2
  have hin2 : σ2.inp = ((nbhs H).map toWord).flatten ++ rest := by
    rw [r2.frame_inp (by simp [matFill, rowFill, forUp, Com.reads])]
  obtain ⟨σ3, r3, hin3, hl3, he3⟩ := readRows_run (B := B) (n := n) (L := nbhs H) (rest := rest) (σ := σ2)
    (arr := arr) (cnt := "n") (by simp [readRow, readElem, forUp, Com.wvars]) (by decide) hin2 (by rw [hn2, hL]) hn2 (by rw [hz, hL])
    (by rw [hL]; omega) (by rw [hL]; omega)
  have hrun : Run B (rdG arr) σ σ3 (n * (n * 15 + 14) + n * (17 * n + 15) + 20) :=
    (Run.seq r1 (Run.seq r2 r3)).mono (by rw [hL]; ring_nf; omega)
  refine ⟨σ3, hrun, hin3, ⟨by rw [hl3, hL], fun u hu v hv' => ?_⟩, fun a ha => ?_,
    fun x hx => hrun.frame_var x hx, hrun.out_eq (by simp [rdG, matFill, rowFill, forUp, readRows, readRow,
      readElem, Com.NoWrite])⟩
  · rw [he3 u (by rw [hL]; exact hu) v hv']
    congr 1
    unfold ind
    have : v ∈ sortedVals (nbhs H)[u] ↔ Conversions.Ram.gA H u v := by
      rw [mem_sortedVals]
      simp only [nbhs, List.getElem_ofFn, mem_filter, mem_univ, true_and]
      exact ⟨fun ⟨h, hadj⟩ => ⟨hu, h, hadj⟩, fun ⟨_, h, hadj⟩ => ⟨h, hadj⟩⟩
    by_cases h : Conversions.Ram.gA H u v <;> simp [h, this]
  · exact hrun.frame_arr a (by simp [rdG, matFill, rowFill, forUp, readRows, readRow, readElem, Com.warrs]; exact ha)

end Lax185574Proofs.ResolveRam.Glue
