import Lax185574Proofs.Words.ForLoop
import Lax185574Proofs.Words.FinsetWords

/-!
Reading lists of finite sets of vertices into a membership matrix.

A list `L` of finite sets of vertices of `Fin n` is read row by row into
an array of width `n`: entry `t · n + u` becomes `1` if `u` lies in the
`t`-th set. The command `readRows arr cnt` expects the number of sets in
the scalar `cnt` and the word of the sets on the input tape. It uses
the scalars `r`, `d`, `k`, `x1` and `x`. A graph on `Fin n` is the list
of its neighborhoods, so the same command reads an adjacency matrix.
-/

namespace Lax185574Proofs.Words

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding

/-- Set the entries `b + u` for `u` in `us` to `1`. -/
def setOnes (l : List ℕ) (b : ℕ) (us : List ℕ) : List ℕ := us.foldl (fun l u => l.set (b + u) 1) l

theorem length_setOnes (l : List ℕ) (b : ℕ) (us : List ℕ) : (setOnes l b us).length = l.length := by
  induction us generalizing l with
  | nil => rfl
  | cons a us ih => simp only [setOnes, List.foldl_cons] at ih ⊢; rw [ih]; simp

theorem setOnes_append (l : List ℕ) (b : ℕ) (us vs : List ℕ) :
    setOnes l b (us ++ vs) = setOnes (setOnes l b us) b vs := by
  simp [setOnes, List.foldl_append]

theorem getElem?_setOnes (l : List ℕ) (b : ℕ) (us : List ℕ) (j : ℕ) :
    (setOnes l b us)[j]? = if j < l.length ∧ ∃ u ∈ us, j = b + u then some 1 else l[j]? := by
  by_cases hj : j < l.length
  · simp only [hj, true_and]
    induction us generalizing l with
    | nil => simp [setOnes]
    | cons a us ih =>
      simp only [setOnes, List.foldl_cons] at ih ⊢
      rw [ih _ (by simpa using hj), List.getElem?_set]
      by_cases h1 : ∃ u ∈ us, j = b + u
      · have h1' : ∃ u ∈ a :: us, j = b + u := by
          obtain ⟨u, hu, rfl⟩ := h1; exact ⟨u, List.mem_cons_of_mem _ hu, rfl⟩
        simp only [h1, h1', if_true]
      · by_cases h2 : b + a = j
        · have h1' : ∃ u ∈ a :: us, j = b + u := ⟨a, List.mem_cons_self .., h2.symm⟩
          simp only [h1, h1', h2, if_true, if_false, hj]
        · have h3 : ¬ ∃ u ∈ a :: us, j = b + u := by
            rintro ⟨u, hu, rfl⟩
            rcases List.mem_cons.mp hu with rfl | hu
            · exact h2 rfl
            · exact h1 ⟨u, hu, rfl⟩
          simp only [h1, h2, h3, if_false]
  · rw [List.getElem?_eq_none (by rw [length_setOnes]; omega), List.getElem?_eq_none (by omega)]
    simp [hj]

theorem evalB_rowIdx {B : ℕ} {σ : Env} {r n x : ℕ} (hr : σ.vars "r" = r) (hn : σ.vars "n" = n)
    (hx : σ.vars "x" = x) (hxn : x < n) (hnB : n < B) (h : r * n + x < B) :
    (Expr.add (.mul (.var "r") (.var "n")) (.var "x")).evalB B σ = some (r * n + x) := by
  have hr' : r ≤ r * n := Nat.le_mul_of_pos_right _ (by omega)
  have := evalB_bin (op := .add) (evalB_bin (op := .mul) (evalB_var (B := B) (x := "r") (σ := σ)
    (by omega)) (evalB_var (x := "n") (by omega)) (by simp [hr, hn]; omega))
    (evalB_var (x := "x") (by omega)) (by simp [hr, hn, hx]; omega)
  simpa [hr, hn, hx] using this

/-- Read the frame `1, u` of an element and mark entry `r · n + u`. -/
def readElem (arr : String) : Com :=
  .seq (.read "x1") (.seq (.read "x")
    (.store arr (.add (.mul (.var "r") (.var "n")) (.var "x")) (.lit 1)))

/-- Read the word of a finite set into row `r` of `arr`. -/
def readRow (arr : String) : Com := .seq (.read "d") (forUp "k" (.var "d") (readElem arr))

/-- Read `cnt` finite sets into the rows of `arr`. -/
def readRows (arr cnt : String) : Com := forUp "r" (.var cnt) (readRow arr)

theorem readRow_run {B n r : ℕ} {A : Finset (Fin n)} {rest : List ℕ} {τ : Env} {arr : String}
    (hinp : τ.inp = toWord A ++ rest) (hr : τ.vars "r" = r) (hn : τ.vars "n" = n)
    (hlen : r * n + n ≤ (τ.arrs arr).length) (hB : r * n + n < B) (hcB : A.card < B) :
    ∃ τ', Run B (readRow arr) τ τ' (17 * A.card + 7) ∧ τ'.inp = rest ∧
      τ'.arrs arr = setOnes (τ.arrs arr) (r * n) (sortedVals A) := by
  set us := sortedVals A with hus
  have husl : us.length = A.card := length_sortedVals A
  have husn : ∀ u ∈ us, u < n := fun u hu => sortedVals_lt hu
  rw [toWord_finset_fin] at hinp
  set τ0 : Env := { τ.setVar "d" A.card with inp := elemFrames us ++ rest } with hτ0
  have hrd : Run B (.read "d") τ τ0 1 := Run.read (by rw [hinp]; rfl)
  let I : ℕ → Env → Prop := fun k τ' =>
    τ'.inp = elemFrames (us.drop k) ++ rest ∧ τ'.vars "d" = A.card ∧ τ'.vars "r" = r ∧
      τ'.vars "n" = n ∧ τ'.arrs arr = setOnes (τ.arrs arr) (r * n) (us.take k)
  obtain ⟨τ', hrun, ⟨hinp', -, -, -, ha'⟩, -⟩ :=
    forUp_run (B := B) (i := "k") (e := .var "d") (body := readElem arr) (N := A.card) (K := 9)
      I hcB
      (fun k _ τ' hI _ => by rw [evalB_var (by rw [hI.2.1]; exact hcB), hI.2.1])
      (σ := τ0) ⟨by simp [hτ0], by simp [hτ0], by simp [hτ0, hr], by simp [hτ0, hn], by simp [hτ0, setOnes]⟩
      (by
        rintro k hk τ1 ⟨hi1, hd1, hr1, hn1, ha1⟩ hk1
        have hkl : k < us.length := by omega
        have hu := husn _ (List.getElem_mem hkl)
        have hinp1 : τ1.inp = 1 :: us[k] :: (elemFrames (us.drop (k + 1)) ++ rest) := by
          rw [hi1, List.drop_eq_getElem_cons hkl, elemFrames_cons]; rfl
        have hlen1 : (τ1.arrs arr).length = (τ.arrs arr).length := by
          rw [ha1, length_setOnes]
        refine ⟨_, (Run.seq (Run.read hinp1) (Run.seq (Run.read rfl) (Run.store
          (idx := r * n + us[k]) (v := 1) ?_ ?_ ?_))).mono (by simp), ?_, ?_⟩
        · exact evalB_rowIdx (by simp [hr1]) (by simp [hn1]) (by simp) hu (by omega) (by omega)
        · simp; omega
        · simp; omega
        · simp [hk1]
        · refine ⟨by simp, by simp [hd1], by simp [hr1], by simp [hn1], ?_⟩
          simp only [arrs_setVar, arrs_setArr, if_true, ha1, List.take_add_one,
            List.getElem?_eq_getElem hkl, Option.toList_some, setOnes_append]
          simp [setOnes])
  refine ⟨τ', (Run.seq hrd hrun).mono (by simp; omega), by rw [hinp', ← husl, List.drop_length]; rfl, ?_⟩
  rw [ha', ← husl, List.take_length]

theorem card_lt_of {n B : ℕ} (A : Finset (Fin n)) (h : n < B) : A.card < B :=
  lt_of_le_of_lt (by simpa using Finset.card_le_univ A) h

/-- **Reading a list of finite sets.** With the number of sets in `cnt`
and an array of zeros of the right size, `readRows arr cnt` leaves the
membership matrix of the sets in `arr`, in time `O(|L| · n)`. -/
theorem readRows_run {B n : ℕ} {L : List (Finset (Fin n))} {rest : List ℕ} {σ : Env}
    {arr cnt : String} (hcnt : cnt ∉ (readRow arr).wvars) (hcr : cnt ≠ "r")
    (hinp : σ.inp = (L.map toWord).flatten ++ rest)
    (hc : σ.vars cnt = L.length) (hn : σ.vars "n" = n)
    (harr : σ.arrs arr = List.replicate (L.length * n) 0) (hB : L.length * n + n < B)
    (hLB : L.length < B) :
    ∃ σ', Run B (readRows arr cnt) σ σ' (L.length * (17 * n + 15) + 6) ∧ σ'.inp = rest ∧
      (σ'.arrs arr).length = L.length * n ∧
      ∀ t (ht : t < L.length), ∀ u < n,
        (σ'.arrs arr)[t * n + u]? = some (if u ∈ sortedVals L[t] then 1 else 0) := by
  have hnB : n < B := by omega
  let J : ℕ → Env → Prop := fun r τ =>
    τ.inp = ((L.drop r).map toWord).flatten ++ rest ∧ τ.vars cnt = L.length ∧
      τ.vars "n" = n ∧ (τ.arrs arr).length = L.length * n ∧
      ∀ t (ht : t < L.length), ∀ u < n,
        (τ.arrs arr)[t * n + u]? = some (if t < r ∧ u ∈ sortedVals L[t] then 1 else 0)
  obtain ⟨σ', hrun, ⟨hinp', -, -, hlen', hent'⟩, -⟩ :=
    forUp_run (B := B) (i := "r") (e := .var cnt) (body := readRow arr) (N := L.length)
      (K := 17 * n + 7) J hLB
      (fun k _ τ hI _ => by rw [evalB_var (by rw [hI.2.1]; exact hLB), hI.2.1])
      (σ := σ) ⟨by simp [hinp], by simp [hcr, hc], by simp [hn], by simp [harr],
        fun t ht u hu => by
          simp only [arrs_setVar, harr]
          rw [List.getElem?_replicate_of_lt (rowMajor_lt ht hu)]
          simp⟩
      (by
        rintro k hk τ ⟨hi, hc1, hn1, hl1, he1⟩ hk1
        have hinpk : τ.inp = toWord L[k] ++ (((L.drop (k + 1)).map toWord).flatten ++ rest) := by
          rw [hi, List.drop_eq_getElem_cons hk]
          simp only [List.map_cons, List.flatten_cons, List.append_assoc]
        have hrn : k * n + n ≤ L.length * n := by
          have := Nat.mul_le_mul_right n hk; rw [Nat.succ_mul] at this; exact this
        obtain ⟨τ', hr', hinp', ha'⟩ := readRow_run (B := B) (arr := arr) hinpk hk1 hn1
          (by omega) (by omega) (card_lt_of _ hnB)
        refine ⟨τ', hr'.mono (by
            have : L[k].card ≤ n := by simpa using Finset.card_le_univ L[k]
            omega), ?_, ?_⟩
        · rw [hr'.frame_var "r" (by simp [readRow, readElem, forUp, Com.wvars]), hk1]
        · refine ⟨by simp [hinp'], ?_, ?_, ?_, ?_⟩
          · simp [hcr, hr'.frame_var cnt hcnt, hc1]
          · simp [hr'.frame_var "n" (by simp [readRow, readElem, forUp, Com.wvars]), hn1]
          · simp [ha', length_setOnes, hl1]
          · intro t ht u hu
            simp only [arrs_setVar, ha', getElem?_setOnes, he1 t ht u hu, hl1]
            have hiff : (t * n + u < L.length * n ∧ ∃ u' ∈ sortedVals L[k], t * n + u = k * n + u') ↔
                t = k ∧ u ∈ sortedVals L[k] := by
              constructor
              · rintro ⟨-, u', hu', he⟩
                obtain ⟨rfl, rfl⟩ := rowMajor_inj hu (sortedVals_lt hu') he
                exact ⟨rfl, hu'⟩
              · rintro ⟨rfl, hu'⟩
                exact ⟨rowMajor_lt ht hu, u, hu', rfl⟩
            by_cases h1 : t = k ∧ u ∈ sortedVals L[k]
            · obtain ⟨rfl, h2⟩ := h1
              rw [if_pos (hiff.mpr ⟨rfl, h2⟩)]
              simp [h2]
            · rw [if_neg (fun h => h1 (hiff.mp h))]
              by_cases htk : t = k
              · subst htk
                simp_all
              · have : (t < k + 1) ↔ (t < k) := by omega
                simp [this])
  refine ⟨σ', hrun.mono (by simp only [size_var]; nlinarith), by simpa using hinp', hlen',
    fun t ht u hu => ?_⟩
  rw [hent' t ht u hu]
  simp [ht]

end Lax185574Proofs.Words
