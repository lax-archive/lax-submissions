import Lax3Proofs.SolveBlocks
import Lax3Proofs.ImplBot

/-!
# F6c/2 — block 0's evaluator: the candidate table (§6.4's machine
schedule, abstract half)

`Impl.botEval` (block 0's live route) evaluates a formula over an
edgeless arena's color rows; its unrestricted quantifier searches
`candidates colB m = ofFn m ++ reps colB m`, and `reps` — the first
off-environment representative of each realized row — is *defined* by
a scan of the whole carrier per quantifier. A machine that ran that
scan per quantifier would pay `Θ(N)` per node of the formula tree per
table entry — `Θ(N²)` per arena — where `botC` allows `O(‖A‖)` for
the whole table. §6.4's schedule is: **build a representative table
once per arena, then evaluate every table entry against the table in
schedule-constant time.** This file is that schedule's abstract half,
discharged:

* `rowCode` — the packed row bits of a vertex (`codeAux`), with the
  injectivity that makes a row code stand for a row
  (`rowCode_eq_iff`);
* `firsts colB K ρ` — the first `K+1` vertices of row code `ρ`, in
  ascending order: the table one `O(N·L)` scan builds, of size
  `≤ 2^L·(K+1)` (schedule-constant × carrier-free);
* `tableReps colB K m` — the per-quantifier candidate completion read
  *off the table*: for each row code, the first table entry off the
  environment. **`mem_tableReps_iff`**: at any environment of size
  `k ≤ K` this is exactly `Impl.FirstRep` — the table is sound *and
  complete*, because an off-environment representative has all its
  earlier same-row vertices in the environment, so it sits among the
  first `k+1 ≤ K+1` of its row;
* `botEvalT` — `botEval` with the table-completed candidate list, and
  **`botEvalT_eq_botEval`**: at every environment within the depth
  budget (`k + qdepth φ ≤ K + 1`) the two evaluators agree — so
  `botEvalT_eq_sat`: the table-scheduled evaluator still decides
  satisfaction on the edgeless arena (`Impl.botEval_eq_sat`
  composed).

The IMP+ compilation of block 0 (continuation) consumes `botEvalT`
verbatim: the table build is one pass over the color-bit region
(`ArenaSt`'s `ColBits`, rows read at stride `Λ`), each `exU` is one
loop over the `≤ k + 2^L·(K+1)` candidates with the `find?` filter
inlined (`≤ K+1` environment tests per row code), and every other
clause is a constant block — `botC`'s `(1 + |ℱ_j|)·‖A‖` shape, with
the per-entry constant a function of `(L, K, φ)` alone. `K` is
instantiated at `qdepth β` over the level's family (`k = 1` at a
table entry, so `1 + qdepth β ≤ K + 1` wants `K ≥ qdepth β`).
-/

namespace Lax3Proofs.Prog

open Lax3.DistFO

variable {L n : ℕ}

/-! ## §1 The row code -/

/-- The packed bits of `f` below `l`. -/
def codeAux (f : ℕ → Bool) : ℕ → ℕ
  | 0 => 0
  | c + 1 => codeAux f c + (if f c then 2 ^ c else 0)

theorem codeAux_lt (f : ℕ → Bool) (l : ℕ) : codeAux f l < 2 ^ l := by
  induction l with
  | zero => simp [codeAux]
  | succ l ih =>
    have h2 : (2 : ℕ) ^ (l + 1) = 2 ^ l + 2 ^ l := by ring
    rw [codeAux, h2]
    by_cases hf : f l
    · rw [if_pos hf]; omega
    · rw [if_neg hf]; omega

/-- The code determines every bit below the width. -/
theorem codeAux_inj {f g : ℕ → Bool} :
    ∀ l, codeAux f l = codeAux g l → ∀ c, c < l → f c = g c := by
  intro l
  induction l with
  | zero => intro _ c hc; omega
  | succ l ih =>
    intro h c hc
    have hfl := codeAux_lt f l
    have hgl := codeAux_lt g l
    rw [codeAux, codeAux] at h
    have hbit : f l = g l := by
      by_cases hf : f l = true <;> by_cases hg : g l = true
      · rw [hf, hg]
      · exfalso
        rw [if_pos hf, if_neg hg] at h
        omega
      · exfalso
        rw [if_neg hf, if_pos hg] at h
        omega
      · rw [Bool.not_eq_true] at hf hg
        rw [hf, hg]

    have hrest : codeAux f l = codeAux g l := by
      rw [hbit] at h
      omega
    rcases Nat.lt_or_ge c l with hcl | hcl
    · exact ih hrest c hcl
    · have hceq : c = l := by omega
      subst hceq
      exact hbit

/-- The row of `v`, as a `ℕ`-indexed bit function. -/
def rowBit (colB : Fin n → Fin L → Bool) (v : Fin n) (c : ℕ) : Bool :=
  if h : c < L then colB v ⟨c, h⟩ else false

theorem rowBit_of_lt (colB : Fin n → Fin L → Bool) (v : Fin n) {c : ℕ}
    (hc : c < L) : rowBit colB v c = colB v ⟨c, hc⟩ :=
  dif_pos hc

/-- **The row code**: the packed color row. -/
def rowCode (colB : Fin n → Fin L → Bool) (v : Fin n) : ℕ :=
  codeAux (rowBit colB v) L

theorem rowCode_lt (colB : Fin n → Fin L → Bool) (v : Fin n) :
    rowCode colB v < 2 ^ L :=
  codeAux_lt _ _

/-- **A code stands for a row**: two vertices carry the same code iff
they carry the same colors. -/
theorem rowCode_eq_iff (colB : Fin n → Fin L → Bool) (v w : Fin n) :
    rowCode colB v = rowCode colB w ↔ ∀ c, colB v c = colB w c := by
  constructor
  · intro h c
    have hbit := codeAux_inj L h (c : ℕ) c.2
    rwa [rowBit_of_lt colB v c.2, rowBit_of_lt colB w c.2] at hbit
  · intro h
    unfold rowCode
    congr 1
    funext c
    unfold rowBit
    by_cases hc : c < L
    · rw [dif_pos hc, dif_pos hc, h ⟨c, hc⟩]
    · rw [dif_neg hc, dif_neg hc]

/-! ## §2 The table -/

/-- The environment test of the candidate scan, as the `Bool` the
machine computes: `v` is off the environment. -/
def offEnv {k : ℕ} (m : Fin k → Fin n) (v : Fin n) : Bool :=
  decide (∀ i, m i ≠ v)

theorem offEnv_eq_true_iff {k : ℕ} (m : Fin k → Fin n) (v : Fin n) :
    offEnv m v = true ↔ ¬ ∃ i, m i = v := by
  simp [offEnv]

/-- **The representative table**: for each row code, the first `K+1`
vertices carrying it, in ascending order — built by one scan of the
carrier. -/
def firsts (colB : Fin n → Fin L → Bool) (K ρ : ℕ) : List (Fin n) :=
  (((List.finRange n).filter fun v => rowCode colB v == ρ)).take (K + 1)

/-- **The candidate completion, read off the table**: for each row
code, the first table entry off the environment. -/
def tableReps (colB : Fin n → Fin L → Bool) (K : ℕ) {k : ℕ}
    (m : Fin k → Fin n) : List (Fin n) :=
  (List.range (2 ^ L)).flatMap fun ρ =>
    ((firsts colB K ρ).find? (offEnv m)).toList

/-! The row lists' order facts, once. -/

private theorem filterRow_pairwise (colB : Fin n → Fin L → Bool) (ρ : ℕ) :
    ((List.finRange n).filter fun v => rowCode colB v == ρ).Pairwise (· < ·) :=
  (List.sortedLT_iff_pairwise.mp (List.sortedLT_finRange n)).filter _

private theorem mem_filterRow_iff (colB : Fin n → Fin L → Bool) (ρ : ℕ)
    (v : Fin n) :
    v ∈ (List.finRange n).filter (fun v => rowCode colB v == ρ) ↔
      rowCode colB v = ρ := by
  simp [List.mem_filter]

private theorem firsts_pairwise (colB : Fin n → Fin L → Bool) (K ρ : ℕ) :
    (firsts colB K ρ).Pairwise (· < ·) :=
  (filterRow_pairwise colB ρ).sublist (List.take_sublist _ _)

private theorem mem_firsts_row (colB : Fin n → Fin L → Bool) {K ρ : ℕ}
    {v : Fin n} (h : v ∈ firsts colB K ρ) : rowCode colB v = ρ :=
  (mem_filterRow_iff colB ρ v).mp
    (List.Sublist.subset (List.take_sublist _ _) h)

/-- A row member below a table entry is itself a table entry: the
elements the `take` dropped all lie above everything kept. -/
private theorem mem_firsts_of_lt (colB : Fin n → Fin L → Bool) {K ρ : ℕ}
    {v u : Fin n} (hv : v ∈ firsts colB K ρ) (hu : rowCode colB u = ρ)
    (hlt : u < v) : u ∈ firsts colB K ρ := by
  set fl := (List.finRange n).filter fun v => rowCode colB v == ρ with hfl
  have hufl : u ∈ fl := (mem_filterRow_iff colB ρ u).mpr hu
  rw [← List.take_append_drop (K + 1) fl] at hufl
  rcases List.mem_append.mp hufl with h | h
  · exact h
  · -- everything dropped lies above the kept entry `v`
    exfalso
    have hsplit := (List.take_append_drop (K + 1) fl).symm
    have hpw : (fl.take (K + 1) ++ fl.drop (K + 1)).Pairwise (· < ·) := by
      rw [← hsplit]
      exact filterRow_pairwise colB ρ
    have := (List.pairwise_append.mp hpw).2.2 v hv u h
    exact absurd hlt (asymm this)

/-- Skipping a failing prefix: `find?` lands on the first success. -/
private theorem find?_of_prefix {α : Type*} {p : α → Bool} :
    ∀ (as : List α) (v : α) (bs : List α),
      (∀ a ∈ as, p a = false) → p v = true →
      List.find? p (as ++ v :: bs) = some v := by
  intro as
  induction as with
  | nil =>
    intro v bs _ hv
    simpa using List.find?_cons_of_pos hv
  | cons a as ih =>
    intro v bs hfail hv
    rw [List.cons_append, List.find?_cons_of_neg]
    · exact ih v bs (fun x hx => hfail x (List.mem_cons_of_mem a hx)) hv
    · simp [hfail a List.mem_cons_self]

open Classical in
/-- **The table is the representative system** (§6.4): at any
environment of size `k ≤ K`, the per-row `find?` over the table finds
exactly the first off-environment representatives — `Impl.FirstRep`,
the set `Impl.reps` realizes. Soundness is the `find?` decomposition
(everything the scan skipped is on the environment, and everything
earlier in the row than a table entry is in the table); completeness
is the counting fact that a first representative has all its earlier
row-mates on the environment, hence at most `k ≤ K` of them, hence a
seat among the row's first `K+1`. -/
theorem mem_tableReps_iff (colB : Fin n → Fin L → Bool) {K k : ℕ}
    (hk : k ≤ K) (m : Fin k → Fin n) (v : Fin n) :
    v ∈ tableReps colB K m ↔ Impl.FirstRep colB m v := by
  constructor
  · -- soundness
    intro hv
    rw [tableReps, List.mem_flatMap] at hv
    obtain ⟨ρ, hρ, hv⟩ := hv
    have hfind : (firsts colB K ρ).find? (offEnv m) = some v := by
      cases hcase : (firsts colB K ρ).find? (offEnv m) with
      | none => rw [hcase] at hv; simp at hv
      | some w =>
        rw [hcase] at hv
        simp only [Option.toList_some, List.mem_singleton] at hv
        rw [hv]
    obtain ⟨hoff, as, bs, hsplit, hfail⟩ :=
      List.find?_eq_some_iff_append.mp hfind
    have hvfirsts : v ∈ firsts colB K ρ := by
      rw [hsplit]
      exact List.mem_append.mpr (Or.inr (List.mem_cons_self))
    have hρv : rowCode colB v = ρ := mem_firsts_row colB hvfirsts
    refine ⟨(offEnv_eq_true_iff m v).mp hoff, fun u hu hrow => ?_⟩
    -- an earlier same-row vertex is in the table, before `v`, so the
    -- scan skipped it: it is on the environment
    have huρ : rowCode colB u = ρ := by
      rw [← hρv]
      exact (rowCode_eq_iff colB u v).mpr hrow
    have hufirsts : u ∈ firsts colB K ρ := mem_firsts_of_lt colB hvfirsts huρ hu
    have huas : u ∈ as := by
      rw [hsplit] at hufirsts
      rcases List.mem_append.mp hufirsts with h | h
      · exact h
      · rcases List.mem_cons.mp h with heq | h
        · exact absurd (heq ▸ hu) (lt_irrefl v)
        · exfalso
          have hpw : (as ++ v :: bs).Pairwise (· < ·) := by
            rw [← hsplit]
            exact firsts_pairwise colB K ρ
          have hvblt := (List.pairwise_cons.mp (List.pairwise_append.mp hpw).2.1).1
          exact absurd hu (asymm (hvblt u h))
    have h2 := hfail u huas
    have h3 : ¬ (∀ i, m i ≠ u) := by
      intro hall
      rw [show offEnv m u = true from by simp [offEnv]; exact hall] at h2
      simp at h2
    rw [not_forall] at h3
    obtain ⟨i, hi⟩ := h3
    rw [not_not] at hi
    exact ⟨i, hi⟩
  · -- completeness
    intro hFR
    obtain ⟨hoff, hbefore⟩ := hFR
    set ρ := rowCode colB v with hρ
    set fl := (List.finRange n).filter fun w => rowCode colB w == ρ with hfl
    have hvfl : v ∈ fl := (mem_filterRow_iff colB ρ v).mpr rfl
    obtain ⟨as, bs, hsplit⟩ := List.append_of_mem hvfl
    have hpwfl : fl.Pairwise (· < ·) := filterRow_pairwise colB ρ
    have hpw : (as ++ v :: bs).Pairwise (· < ·) := by rw [← hsplit]; exact hpwfl
    -- the prefix consists of earlier row-mates, all on the environment
    have has_env : ∀ u ∈ as, ∃ i, m i = u := by
      intro u hu
      have hult : u < v := (List.pairwise_append.mp hpw).2.2 u hu v
        List.mem_cons_self
      have hufl : u ∈ fl := by
        rw [hsplit]
        exact List.mem_append.mpr (Or.inl hu)
      have hurow := (mem_filterRow_iff colB ρ u).mp hufl
      exact hbefore u hult ((rowCode_eq_iff colB u v).mp (hρ ▸ hurow))
    -- so the prefix is short: it embeds in the environment's range
    have has_nodup : as.Nodup := by
      have hnd : (as ++ v :: bs).Nodup := by
        rw [← hsplit]
        exact hpwfl.imp ne_of_lt
      exact (List.nodup_append.mp hnd).1
    have has_len : as.length ≤ k := by
      classical
      have hsub : as.toFinset ⊆ Finset.univ.image m := by
        intro u hu
        obtain ⟨i, hi⟩ := has_env u (List.mem_toFinset.mp hu)
        exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩
      calc as.length = as.toFinset.card :=
            (List.toFinset_card_of_nodup has_nodup).symm
        _ ≤ (Finset.univ.image m).card := Finset.card_le_card hsub
        _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
        _ = k := by simp
    -- hence `v` keeps its seat in the truncated table
    have hfirsts_eq : firsts colB K ρ
        = as ++ v :: (bs.take (K + 1 - as.length - 1)) := by
      rw [firsts, ← hfl, hsplit, List.take_append,
        List.take_of_length_le (by omega), List.take_cons (by omega)]
    -- and the scan lands on it
    rw [tableReps, List.mem_flatMap]
    refine ⟨ρ, List.mem_range.mpr (rowCode_lt colB v), ?_⟩
    have hfind : (firsts colB K ρ).find? (offEnv m) = some v := by
      rw [hfirsts_eq]
      refine find?_of_prefix as v _ (fun a ha => ?_) ?_
      · obtain ⟨i, hi⟩ := has_env a ha
        simp only [offEnv, decide_eq_false_iff_not]
        intro hall
        exact hall i hi
      · exact (offEnv_eq_true_iff m v).mpr hoff
    rw [hfind]
    simp

/-! ## §3 The table-scheduled evaluator -/

/-- Any over membership-equal lists agrees. -/
private theorem any_congr_mem {α : Type*} {l l' : List α}
    (h : ∀ x, x ∈ l ↔ x ∈ l') (f : α → Bool) : l.any f = l'.any f := by
  by_cases hl : l.any f = true
  · rw [hl]
    symm
    rw [List.any_eq_true] at hl ⊢
    obtain ⟨x, hx, hfx⟩ := hl
    exact ⟨x, (h x).mp hx, hfx⟩
  · have hl' : ¬ l'.any f = true := by
      intro hc
      apply hl
      rw [List.any_eq_true] at hc ⊢
      obtain ⟨x, hx, hfx⟩ := hc
      exact ⟨x, (h x).mpr hx, hfx⟩
    rw [Bool.not_eq_true] at hl hl'
    rw [hl, hl']

/-- The nesting depth of the quantifiers — what the table's width `K`
must cover. -/
def qdepth : {k : ℕ} → DistFO L k → ℕ
  | _, .adj _ _ => 0
  | _, .eq _ _ => 0
  | _, .color _ _ => 0
  | _, .distLe _ _ _ => 0
  | _, .distColorLt _ _ _ => 0
  | _, .not φ => qdepth φ
  | _, .and φ ψ => max (qdepth φ) (qdepth ψ)
  | _, .exU φ => qdepth φ + 1
  | _, .exL _ _ φ => qdepth φ + 1

/-- **`botEval`, on the machine's schedule**: the same evaluator with
the per-quantifier carrier scan replaced by the table read. -/
def botEvalT (colB : Fin n → Fin L → Bool) (K : ℕ) :
    {k : ℕ} → (Fin k → Fin n) → DistFO L k → Bool
  | _, _, .adj _ _ => false
  | _, m, .eq i j => decide (m i = m j)
  | _, m, .color c i => colB (m i) c
  | _, m, .distLe _ i j => decide (m i = m j)
  | _, m, .distColorLt r c i => decide (0 < r) && colB (m i) c
  | _, m, .not φ => ! botEvalT colB K m φ
  | _, m, .and φ ψ => botEvalT colB K m φ && botEvalT colB K m ψ
  | _, m, .exU φ =>
      (List.ofFn m ++ tableReps colB K m).any fun w =>
        botEvalT colB K (Fin.snoc m w) φ
  | _, m, .exL _ g φ => decide (∃ i ∈ g, botEvalT colB K (Fin.snoc m (m i)) φ = true)

/-- **The schedule computes the evaluator**: within the depth budget,
the table-scheduled evaluator agrees with `Impl.botEval` — clause by
clause, the quantifier case through `mem_tableReps_iff` and
`Impl.mem_reps_iff`. -/
theorem botEvalT_eq_botEval (colB : Fin n → Fin L → Bool) {K : ℕ} :
    ∀ {k : ℕ} (φ : DistFO L k) (m : Fin k → Fin n),
      k + qdepth φ ≤ K + 1 →
      botEvalT colB K m φ = Impl.botEval colB m φ := by
  intro k φ
  induction φ with
  | adj i j => intro m _; rfl
  | eq i j => intro m _; rfl
  | color c i => intro m _; rfl
  | distLe r i j => intro m _; rfl
  | distColorLt r c i => intro m _; rfl
  | not φ ih =>
    intro m hd
    show (! botEvalT colB K m φ) = (! Impl.botEval colB m φ)
    rw [ih m (by simpa [qdepth] using hd)]
  | and φ ψ ih₁ ih₂ =>
    intro m hd
    simp only [qdepth] at hd
    show (botEvalT colB K m φ && botEvalT colB K m ψ)
        = (Impl.botEval colB m φ && Impl.botEval colB m ψ)
    rw [ih₁ m (by omega), ih₂ m (by omega)]
  | exU φ ih =>
    intro m hd
    simp only [qdepth] at hd
    show ((List.ofFn m ++ tableReps colB K m).any fun w =>
        botEvalT colB K (Fin.snoc m w) φ)
      = ((Impl.candidates colB m).any fun w =>
        Impl.botEval colB (Fin.snoc m w) φ)
    have hbody : ∀ w, botEvalT colB K (Fin.snoc m w) φ
        = Impl.botEval colB (Fin.snoc m w) φ :=
      fun w => ih (Fin.snoc m w) (by omega)
    calc ((List.ofFn m ++ tableReps colB K m).any fun w =>
          botEvalT colB K (Fin.snoc m w) φ)
        = ((List.ofFn m ++ tableReps colB K m).any fun w =>
          Impl.botEval colB (Fin.snoc m w) φ) := by
          simp only [hbody]
      _ = ((Impl.candidates colB m).any fun w =>
          Impl.botEval colB (Fin.snoc m w) φ) := by
          refine any_congr_mem (fun x => ?_) _
          simp only [Impl.candidates, List.mem_append]
          rw [mem_tableReps_iff colB (by omega) m x, ← Impl.mem_reps_iff colB]
  | exL r g φ ih =>
    intro m hd
    simp only [qdepth] at hd
    show decide (∃ i ∈ g, botEvalT colB K (Fin.snoc m (m i)) φ = true)
        = decide (∃ i ∈ g, Impl.botEval colB (Fin.snoc m (m i)) φ = true)
    rw [decide_eq_decide]
    constructor
    · rintro ⟨i, hi, h⟩
      exact ⟨i, hi, by rw [← ih (Fin.snoc m (m i)) (by omega)]; exact h⟩
    · rintro ⟨i, hi, h⟩
      exact ⟨i, hi, by rw [ih (Fin.snoc m (m i)) (by omega)]; exact h⟩

open Lax3.ColoredGraphs in
/-- **The headline of the schedule**: within the depth budget and
against rows matching the coloring, the table-scheduled evaluator
decides satisfaction on the edgeless arena — `botEval_eq_sat` composed
with the schedule identity. Block 0's IMP+ `Spec` lands here: its
table region holds `botEvalT`'s bits, and this is what makes them
`Unroll.botFrame`'s truth values. -/
theorem botEvalT_eq_sat (colB : Fin n → Fin L → Bool) {K : ℕ}
    (col : Coloring n L)
    (hcol : ∀ v c, colB v c = true ↔ v ∈ col c)
    {k : ℕ} (φ : DistFO L k) (m : Fin k → Fin n)
    (hd : k + qdepth φ ≤ K + 1) :
    botEvalT colB K m φ = true ↔ Sat (⊥ : SimpleGraph (Fin n)) col m φ := by
  rw [botEvalT_eq_botEval colB φ m hd]
  exact Impl.botEval_eq_sat colB col hcol φ m

end Lax3Proofs.Prog
