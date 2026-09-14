/-
Part D: for-transducers -- the prenex normal form, Lemma `lemma:prenex-normal-form`.

The translation `Transducers.trFor` turns a for-program into a single nest of loops with a
loop-free body, correct on inputs of length at least two.  It follows the proof of the book: a
sequential composition `I;J` is simulated by a loop whose first iteration runs `I` and whose last
iteration runs `J` (this is `Transducers.exec_merge`), and a conditional is simulated by first
storing the value of the test in a fresh Boolean variable and then running the two branches,
guarded, one after the other.  Fresh variables are taken from a counter that is threaded through
the translation.
-/
import Lax194892Proofs.Source.PartD.ForMerge

namespace Lax194892Proofs.Transducers

open scoped Classical

variable {A B : Type}

/-- The translation of a for-program into a nest of loops, using the fresh variables `k`, `k+1`,
… ; the designated position variables `zv` and `lv` are assumed to hold the first and the last
position of the input.  The result is the list of loops, the body of the nest, and the first
unused fresh variable. -/
def trFor (zv lv : ℕ) : ForProg A B → ℕ → List (Bool × ℕ) × ForProg A B × ℕ
  | ForProg.skip, k => ([], ForProg.skip, k)
  | ForProg.output c, k => ([], ForProg.output c, k)
  | ForProg.assign i v, k => ([], ForProg.assign i v, k)
  | ForProg.seq P Q, k =>
      let r₁ := trFor zv lv P (k + 1)
      let r₂ := trFor zv lv Q r₁.2.2
      (mergeLoops k r₁.1 r₂.1, mergeBody zv lv k r₁.1 r₂.1 r₁.2.1 r₂.2.1, r₂.2.2)
  | ForProg.ite t P Q, k =>
      let r₁ := trFor zv lv P (k + 3)
      let r₂ := trFor zv lv Q r₁.2.2
      let b₀ : ForProg A B :=
        ForProg.ite t (ForProg.assign (k + 1) true) (ForProg.assign (k + 1) false)
      let b₁ := ForProg.ite (ForTest.boolVar (k + 1)) r₁.2.1 ForProg.skip
      let b₂ := ForProg.ite (ForTest.not (ForTest.boolVar (k + 1))) r₂.2.1 ForProg.skip
      (mergeLoops k (mergeLoops (k + 2) [] r₁.1) r₂.1,
        mergeBody zv lv k (mergeLoops (k + 2) [] r₁.1) r₂.1
          (mergeBody zv lv (k + 2) [] r₁.1 b₀ b₁) b₂,
        r₂.2.2)
  | ForProg.loop d x P, k =>
      let r := trFor zv lv P (k + 1)
      ((d, k) :: r.1, ForProg.renamePos (fun i => if i = x then k else i) r.2.1, r.2.2)

/-- The syntactic invariant of the translation `Transducers.trFor`: the loop variables are fresh
and pairwise distinct, the body is loop-free, produces at most one letter, and only mentions the
variables of the source program, the two designated variables and the fresh ones. -/
structure TrOk (zv lv : ℕ) (P : ForProg A B) (k : ℕ)
    (L : List (Bool × ℕ)) (b : ForProg A B) (k' : ℕ) : Prop where
  /-- The counter only grows. -/
  mono : k ≤ k'
  /-- The loop variables are fresh. -/
  loopRange : ∀ y ∈ L.map Prod.snd, k ≤ y ∧ y < k'
  /-- The loop variables are pairwise distinct. -/
  nodup : (L.map Prod.snd).Nodup
  /-- The position variables of the body. -/
  posOk : ∀ i ∈ b.posVars, i ∈ P.posVars ∨ i = zv ∨ i = lv ∨ (k ≤ i ∧ i < k')
  /-- The Boolean variables of the body. -/
  boolOk : ∀ i ∈ b.boolVars, i ∈ P.boolVars ∨ (k ≤ i ∧ i < k')
  /-- The body contains no loop. -/
  loopFree : b.LoopFree
  /-- The body produces at most one letter. -/
  out1 : b.OutputsAtMostOne

theorem trFor_ok (zv lv : ℕ) : ∀ (P : ForProg A B) (k : ℕ) (L : List (Bool × ℕ))
    (b : ForProg A B) (k' : ℕ), trFor zv lv P k = (L, b, k') → TrOk zv lv P k L b k' := by
  intro P
  induction P with
  | skip =>
      rintro k L b k' heq
      simp only [trFor, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact
        { mono := le_rfl
          loopRange := by simp
          nodup := by simp
          posOk := by simp [ForProg.posVars]
          boolOk := by simp [ForProg.boolVars]
          loopFree := trivial
          out1 := ForProg.outputsAtMostOne_skip }
  | output c =>
      rintro k L b k' heq
      simp only [trFor, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact
        { mono := le_rfl
          loopRange := by simp
          nodup := by simp
          posOk := by simp [ForProg.posVars]
          boolOk := by simp [ForProg.boolVars]
          loopFree := trivial
          out1 := ForProg.outputsAtMostOne_output c }
  | assign i v =>
      rintro k L b k' heq
      simp only [trFor, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact
        { mono := le_rfl
          loopRange := by simp
          nodup := by simp
          posOk := by simp [ForProg.posVars]
          boolOk := by
            intro j hj
            simp only [ForProg.boolVars, List.mem_singleton] at hj
            exact Or.inl (by simp [ForProg.boolVars, hj])
          loopFree := trivial
          out1 := ForProg.outputsAtMostOne_assign i v }
  | seq P Q ihP ihQ =>
      rintro k L b k' heq
      rcases hr₁ : trFor zv lv P (k + 1) with ⟨L₁, b₁, k₁⟩
      rcases hr₂ : trFor zv lv Q k₁ with ⟨L₂, b₂, k₂⟩
      have h₁ := ihP _ _ _ _ hr₁
      have h₂ := ihQ _ _ _ _ hr₂
      simp only [trFor, hr₁, hr₂, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      have hL₁ := h₁.loopRange
      have hL₂ := h₂.loopRange
      have hm₁ : k + 1 ≤ k₁ := h₁.mono
      have hm₂ : k₁ ≤ k₂ := h₂.mono
      refine
        { mono := by omega
          loopRange := ?_
          nodup := ?_
          posOk := ?_
          boolOk := ?_
          loopFree := loopFree_mergeBody _ _ _ _ _ _ _ h₁.loopFree h₂.loopFree
          out1 := outputsAtMostOne_mergeBody _ _ _ _ _ _ _ h₁.out1 h₂.out1 }
      · intro y hy
        simp only [mergeLoops, List.map_cons, List.map_append, List.mem_cons,
          List.mem_append] at hy
        rcases hy with rfl | hy | hy
        · omega
        · have := hL₁ y hy; omega
        · have := hL₂ y hy; omega
      · simp only [mergeLoops, List.map_cons, List.map_append]
        refine List.nodup_cons.mpr ⟨?_, ?_⟩
        · intro hk
          rcases List.mem_append.mp hk with h | h
          · have := hL₁ k h; omega
          · have := hL₂ k h; omega
        · refine List.nodup_append.mpr ⟨h₁.nodup, h₂.nodup, ?_⟩
          intro a ha c hc
          have := hL₁ a ha
          have := hL₂ c hc
          omega
      · intro i hi
        have hmem := posVars_mergeBody zv lv k L₁ L₂ b₁ b₂ hi
        simp only [List.mem_cons, List.append_assoc, List.mem_append] at hmem
        simp only [ForProg.posVars, List.mem_append]
        rcases hmem with rfl | rfl | rfl | h | h | h | h
        · exact Or.inr (Or.inr (Or.inr ⟨le_rfl, by omega⟩))
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · have := hL₁ i h; exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
        · have := hL₂ i h; exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
        · rcases h₁.posOk i h with h' | h' | h' | h'
          · exact Or.inl (Or.inl h')
          · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inr (Or.inl h'))
          · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
        · rcases h₂.posOk i h with h' | h' | h' | h'
          · exact Or.inl (Or.inr h')
          · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inr (Or.inl h'))
          · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
      · intro i hi
        rw [boolVars_mergeBody] at hi
        simp only [List.mem_append] at hi
        simp only [ForProg.boolVars, List.mem_append]
        rcases hi with h | h
        · rcases h₁.boolOk i h with h' | h'
          · exact Or.inl (Or.inl h')
          · exact Or.inr ⟨by omega, by omega⟩
        · rcases h₂.boolOk i h with h' | h'
          · exact Or.inl (Or.inr h')
          · exact Or.inr ⟨by omega, by omega⟩
  | ite t P Q ihP ihQ =>
      rintro k L b k' heq
      rcases hr₁ : trFor zv lv P (k + 3) with ⟨L₁, b₁, k₁⟩
      rcases hr₂ : trFor zv lv Q k₁ with ⟨L₂, b₂, k₂⟩
      have h₁ := ihP _ _ _ _ hr₁
      have h₂ := ihQ _ _ _ _ hr₂
      simp only [trFor, hr₁, hr₂, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      have hL₁ := h₁.loopRange
      have hL₂ := h₂.loopRange
      have hm₁ : k + 3 ≤ k₁ := h₁.mono
      have hm₂ : k₁ ≤ k₂ := h₂.mono
      set c₀ : ForProg A B :=
        ForProg.ite t (ForProg.assign (k + 1) true) (ForProg.assign (k + 1) false) with hc₀
      set c₁ : ForProg A B := ForProg.ite (ForTest.boolVar (k + 1)) b₁ ForProg.skip with hc₁
      set c₂ : ForProg A B := ForProg.ite (ForTest.not (ForTest.boolVar (k + 1))) b₂ ForProg.skip
        with hc₂
      have hinnerPos : ∀ j ∈ (mergeBody zv lv (k + 2) ([] : List (Bool × ℕ)) L₁ c₀ c₁).posVars,
          j ∈ (ForProg.ite t P Q).posVars ∨ j = zv ∨ j = lv ∨ (k ≤ j ∧ j < k₂) := by
        intro j hj
        have hmem := posVars_mergeBody zv lv (k + 2) ([] : List (Bool × ℕ)) L₁ c₀ c₁ hj
        simp only [List.mem_cons, List.map_nil, List.append_assoc, List.mem_append,
          List.not_mem_nil, false_or] at hmem
        rcases hmem with rfl | rfl | rfl | h | h | h
        · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · have := hL₁ j h; exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
        · simp only [hc₀, ForProg.posVars, List.append_nil, 
            ] at h
          exact Or.inl (by simp [ForProg.posVars, h])
        · simp only [hc₁, ForProg.posVars, ForTest.posVars, List.nil_append, List.append_nil,
            ] at h
          rcases h₁.posOk j h with h' | h' | h' | h'
          · exact Or.inl (by simp [ForProg.posVars, h'])
          · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inr (Or.inl h'))
          · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
      refine
        { mono := by omega
          loopRange := ?_
          nodup := ?_
          posOk := ?_
          boolOk := ?_
          loopFree := loopFree_mergeBody _ _ _ _ _ _ _
            (loopFree_mergeBody _ _ _ _ _ _ _ ⟨trivial, trivial⟩
              ⟨h₁.loopFree, trivial⟩)
            ⟨h₂.loopFree, trivial⟩
          out1 := outputsAtMostOne_mergeBody _ _ _ _ _ _ _
            (outputsAtMostOne_mergeBody _ _ _ _ _ _ _
              (ForProg.outputsAtMostOne_ite _ _ _ (ForProg.outputsAtMostOne_assign _ _)
                (ForProg.outputsAtMostOne_assign _ _))
              (ForProg.outputsAtMostOne_ite _ _ _ h₁.out1 ForProg.outputsAtMostOne_skip))
            (ForProg.outputsAtMostOne_ite _ _ _ h₂.out1 ForProg.outputsAtMostOne_skip) }
      · intro y hy
        simp only [mergeLoops, List.map_cons, List.map_append, List.nil_append,
          List.cons_append, List.mem_cons, List.mem_append] at hy
        rcases hy with h | h | hy | hy
        · omega
        · omega
        · have := hL₁ y hy; omega
        · have := hL₂ y hy; omega
      · simp only [mergeLoops, List.map_cons, List.map_append, List.nil_append,
          List.cons_append]
        refine List.nodup_cons.mpr ⟨?_, List.nodup_cons.mpr ⟨?_, ?_⟩⟩
        · simp only [List.mem_cons, List.mem_append]
          rintro (h | h | h)
          · omega
          · have := hL₁ k h; omega
          · have := hL₂ k h; omega
        · simp only [List.mem_append]
          rintro (h | h)
          · have := hL₁ (k + 2) h; omega
          · have := hL₂ (k + 2) h; omega
        · refine List.nodup_append.mpr ⟨h₁.nodup, h₂.nodup, ?_⟩
          intro a ha c hc
          have := hL₁ a ha
          have := hL₂ c hc
          omega
      · intro i hi
        have hmem := posVars_mergeBody zv lv k (mergeLoops (k + 2) [] L₁) L₂
          (mergeBody zv lv (k + 2) [] L₁ c₀ c₁) c₂ hi
        simp only [List.mem_cons, List.append_assoc, List.mem_append] at hmem
        rcases hmem with rfl | rfl | rfl | h | h | h | h
        · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr (Or.inl rfl))
        · simp only [mergeLoops, List.map_cons, List.nil_append,
            List.mem_cons] at h
          rcases h with rfl | h
          · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
          · have := hL₁ i h; exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
        · have := hL₂ i h; exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
        · exact hinnerPos i h
        · simp only [hc₂, ForProg.posVars, ForTest.posVars, List.nil_append, List.append_nil,
            ] at h
          rcases h₂.posOk i h with h' | h' | h' | h'
          · exact Or.inl (by simp [ForProg.posVars, h'])
          · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inr (Or.inl h'))
          · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
      · intro i hi
        by_cases hik : i = k + 1
        · exact Or.inr ⟨by omega, by omega⟩
        by_cases ht : i ∈ t.boolVars
        · exact Or.inl (by simp [ForProg.boolVars, ht])
        by_cases hb1 : i ∈ b₁.boolVars
        · rcases h₁.boolOk i hb1 with h' | h'
          · exact Or.inl (by simp [ForProg.boolVars, h'])
          · exact Or.inr ⟨by omega, by omega⟩
        by_cases hb2 : i ∈ b₂.boolVars
        · rcases h₂.boolOk i hb2 with h' | h'
          · exact Or.inl (by simp [ForProg.boolVars, h'])
          · exact Or.inr ⟨by omega, by omega⟩
        exfalso
        rw [boolVars_mergeBody, boolVars_mergeBody] at hi
        simp only [hc₀, hc₁, hc₂, ForProg.boolVars, ForTest.boolVars, 
          List.append_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hi
        tauto
  | loop d x P ih =>
      rintro k L b k' heq
      rcases hr : trFor zv lv P (k + 1) with ⟨L₁, b₁, k₁⟩
      have h₁ := ih _ _ _ _ hr
      simp only [trFor, hr, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      have hL := h₁.loopRange
      have hm : k + 1 ≤ k₁ := h₁.mono
      refine
        { mono := by omega
          loopRange := ?_
          nodup := ?_
          posOk := ?_
          boolOk := ?_
          loopFree := ForProg.loopFree_renamePos _ _ h₁.loopFree
          out1 := ForProg.outputsAtMostOne_renamePos _ _ h₁.loopFree h₁.out1 }
      · intro y hy
        simp only [List.map_cons, List.mem_cons] at hy
        rcases hy with rfl | hy
        · omega
        · have := hL y hy; omega
      · simp only [List.map_cons]
        refine List.nodup_cons.mpr ⟨?_, h₁.nodup⟩
        intro hk
        have := hL k hk
        omega
      · intro i hi
        rw [ForProg.posVars_renamePos] at hi
        simp only [List.mem_map] at hi
        obtain ⟨j, hj, rfl⟩ := hi
        by_cases hjx : j = x
        · rw [if_pos hjx]
          exact Or.inr (Or.inr (Or.inr ⟨le_rfl, by omega⟩))
        · rw [if_neg hjx]
          rcases h₁.posOk j hj with h' | h' | h' | h'
          · exact Or.inl (by simp [ForProg.posVars, h'])
          · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inr (Or.inl h'))
          · exact Or.inr (Or.inr (Or.inr ⟨by omega, by omega⟩))
      · intro i hi
        rw [ForProg.boolVars_renamePos] at hi
        rcases h₁.boolOk i hi with h' | h'
        · exact Or.inl (by simpa [ForProg.boolVars] using h')
        · exact Or.inr ⟨by omega, by omega⟩

/-! ## Freshness bookkeeping -/

/-- `FreshNest a lo hi L b` says that the nest of loops `L` with body `b` uses, as position
variables, only "old" ones -- those below `a` -- and fresh ones taken from the interval
`[lo, hi)`, and that its loop variables are fresh and pairwise distinct. -/
structure FreshNest (a lo hi : ℕ) (L : List (Bool × ℕ)) (b : ForProg A B) : Prop where
  /-- The loop variables are fresh. -/
  loopRange : ∀ y ∈ L.map Prod.snd, lo ≤ y ∧ y < hi
  /-- The loop variables are pairwise distinct. -/
  nodup : (L.map Prod.snd).Nodup
  /-- The position variables of the body are either old or fresh. -/
  posOk : ∀ i ∈ b.posVars, i < a ∨ (lo ≤ i ∧ i < hi)

lemma FreshNest.mono {a lo hi lo' hi' : ℕ} {L : List (Bool × ℕ)} {b : ForProg A B}
    (h : FreshNest a lo hi L b) (h1 : lo' ≤ lo) (h2 : hi ≤ hi') : FreshNest a lo' hi' L b where
  loopRange y hy := ⟨by have := (h.loopRange y hy).1; omega, by have := (h.loopRange y hy).2; omega⟩
  nodup := h.nodup
  posOk i hi' := by
    rcases h.posOk i hi' with h' | h'
    · exact Or.inl h'
    · exact Or.inr ⟨by omega, by omega⟩

/-- The translation produces a fresh nest. -/
lemma TrOk.toFresh {zv lv : ℕ} {P : ForProg A B} {k : ℕ} {L : List (Bool × ℕ)} {b : ForProg A B}
    {k' a : ℕ} (h : TrOk zv lv P k L b k') (hzv : zv < a) (hlv : lv < a)
    (hP : ∀ i ∈ P.posVars, i < a) : FreshNest a k k' L b where
  loopRange := h.loopRange
  nodup := h.nodup
  posOk i hi := by
    rcases h.posOk i hi with h' | h' | h' | h'
    · exact Or.inl (hP i h')
    · exact Or.inl (by omega)
    · exact Or.inl (by omega)
    · exact Or.inr h'

/-- Merging two fresh nests gives a fresh nest. -/
lemma FreshNest.merge {a lo₁ hi₁ lo₂ hi₂ pi zv lv : ℕ} {L₁ L₂ : List (Bool × ℕ)}
    {b₁ b₂ : ForProg A B} (h₁ : FreshNest a lo₁ hi₁ L₁ b₁) (h₂ : FreshNest a lo₂ hi₂ L₂ b₂)
    (hzv : zv < a) (hlv : lv < a) (hpa : a ≤ pi) (hpl : pi < lo₁) (hle₁ : lo₁ ≤ hi₁)
    (hmid : hi₁ ≤ lo₂) (hle₂ : lo₂ ≤ hi₂) :
    FreshNest a pi hi₂ (mergeLoops pi L₁ L₂) (mergeBody zv lv pi L₁ L₂ b₁ b₂) where
  loopRange y hy := by
    simp only [mergeLoops, List.map_cons, List.map_append, List.mem_cons, List.mem_append] at hy
    rcases hy with rfl | hy | hy
    · omega
    · have := h₁.loopRange y hy; omega
    · have := h₂.loopRange y hy; omega
  nodup := by
    simp only [mergeLoops, List.map_cons, List.map_append]
    refine List.nodup_cons.mpr ⟨?_, List.nodup_append.mpr ⟨h₁.nodup, h₂.nodup, ?_⟩⟩
    · intro hk
      rcases List.mem_append.mp hk with h | h
      · have := h₁.loopRange _ h; omega
      · have := h₂.loopRange _ h; omega
    · intro c hc e he
      have := h₁.loopRange c hc
      have := h₂.loopRange e he
      omega
  posOk i hi := by
    have hmem := posVars_mergeBody zv lv pi L₁ L₂ b₁ b₂ hi
    simp only [List.mem_cons, List.append_assoc, List.mem_append] at hmem
    rcases hmem with rfl | rfl | rfl | h | h | h | h
    · exact Or.inr ⟨le_rfl, by omega⟩
    · exact Or.inl hzv
    · exact Or.inl hlv
    · have := h₁.loopRange i h; exact Or.inr ⟨by omega, by omega⟩
    · have := h₂.loopRange i h; exact Or.inr ⟨by omega, by omega⟩
    · rcases h₁.posOk i h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨by omega, by omega⟩
    · rcases h₂.posOk i h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨by omega, by omega⟩

/-- `Transducers.exec_merge`, with the freshness hypotheses packaged as `FreshNest`. -/
lemma exec_merge_fresh (w : List A) (zv lv a : ℕ) (hzv : zv < a) (hlv : lv < a)
    (pos : ℕ → ℕ) (hposz : pos zv < pos lv) (hposl : pos lv < w.length)
    (bv : ℕ → Bool) (pi lo₁ hi₁ lo₂ hi₂ : ℕ) (L₁ L₂ : List (Bool × ℕ)) (b₁ b₂ : ForProg A B)
    (h₁ : FreshNest a lo₁ hi₁ L₁ b₁) (h₂ : FreshNest a lo₂ hi₂ L₂ b₂)
    (hpa : a ≤ pi) (hpl : pi < lo₁) (hle₁ : lo₁ ≤ hi₁) (hmid : hi₁ ≤ lo₂) (hle₂ : lo₂ ≤ hi₂) :
    ForProg.exec w (ForProg.nestLoops (mergeLoops pi L₁ L₂) (mergeBody zv lv pi L₁ L₂ b₁ b₂))
        pos bv
      = ForProg.exec w (ForProg.seq (ForProg.nestLoops L₁ b₁) (ForProg.nestLoops L₂ b₂))
        pos bv := by
  have hmem : ∀ y ∈ (L₁ ++ L₂).map Prod.snd, lo₁ ≤ y ∧ y < hi₂ := by
    intro y hy
    rw [List.map_append, List.mem_append] at hy
    rcases hy with hy | hy
    · have := h₁.loopRange y hy; omega
    · have := h₂.loopRange y hy; omega
  refine exec_merge w zv lv pi L₁ L₂ b₁ b₂ pos bv hposz hposl (by omega) (by omega)
    (fun h => by have := hmem pi h; omega)
    (fun h => by rcases h₁.posOk pi h with h' | h' <;> omega)
    (fun h => by rcases h₂.posOk pi h with h' | h' <;> omega)
    (fun h => by have := hmem zv h; omega) (fun h => by have := hmem lv h; omega)
    h₁.nodup h₂.nodup (fun y hy hb => ?_) (fun y hy => ⟨fun hb => ?_, fun hb => ?_⟩)
  · have := h₂.loopRange y hy
    rcases h₁.posOk y hb with h' | h' <;> omega
  · have := h₁.loopRange y hy
    have := h₂.loopRange y hb
    omega
  · have := h₁.loopRange y hy
    rcases h₂.posOk y hb with h' | h' <;> omega

/-! ## Auxiliary facts about tuples and folds -/

lemma runList_congr_mem {α S C : Type} (step₁ step₂ : S → α → S × List C) (as : List α) (s : S)
    (h : ∀ (t : S) (a : α), a ∈ as → step₁ t a = step₂ t a) :
    runList step₁ as s = runList step₂ as s := by
  induction as generalizing s with
  | nil => rfl
  | cons a as ih =>
      rw [runList_cons, runList_cons, h s a (by simp),
        ih _ (fun t c hc => h t c (by simp [hc]))]

lemma length_of_mem_tuplesOf : ∀ (L : List (Bool × ℕ)) (n : ℕ) {t : List ℕ},
    t ∈ tuplesOf L n → t.length = L.length := by
  intro L
  induction L with
  | nil => intro n t ht; simp only [tuplesOf_nil, List.mem_singleton] at ht; simp [ht]
  | cons a L ih =>
      obtain ⟨d, x⟩ := a
      intro n t ht
      rw [tuplesOf_cons] at ht
      simp only [List.mem_flatMap, List.mem_map] at ht
      obtain ⟨p, -, t', ht', rfl⟩ := ht
      simp [ih n ht']

/-- The value that a tuple gives to one of the loop variables does not depend on the ambient
valuation. -/
lemma setTuple_mem_eq : ∀ (L : List (Bool × ℕ)) (t : List ℕ), t.length = L.length →
    ∀ (pos pos' : ℕ → ℕ) {i : ℕ}, i ∈ L.map Prod.snd →
      setTuple L t pos i = setTuple L t pos' i := by
  intro L
  induction L with
  | nil => intro t _ pos pos' i hi; simp at hi
  | cons a L ih =>
      obtain ⟨d, x⟩ := a
      intro t ht pos pos' i hi
      cases t with
      | nil => simp at ht
      | cons p t =>
          simp only [setTuple_cons]
          simp only [List.map_cons, List.mem_cons] at hi
          by_cases hiL : i ∈ L.map Prod.snd
          · exact ih t (by simpa using ht) _ _ hiL
          · have hix : i = x := by rcases hi with h | h; · exact h
                                   · exact absurd h hiL
            subst hix
            rw [setTuple_of_not_mem L t _ hiL, setTuple_of_not_mem L t _ hiL,
              Function.update_self, Function.update_self]

/-- A nest of loops whose body never changes a Boolean variable does not change it either. -/
lemma nest_bv_fix (w : List A) (L : List (Bool × ℕ)) (body : ForProg A B) (pos : ℕ → ℕ)
    (bv : ℕ → Bool) (i : ℕ)
    (h : ∀ (t : List ℕ) (s : ℕ → Bool), (ForProg.exec w body (setTuple L t pos) s).1 i = s i) :
    (ForProg.exec w (ForProg.nestLoops L body) pos bv).1 i = bv i := by
  rw [exec_nestLoops]
  exact runList_fix _ _ _ (fun s => s i) (fun s t => h t s)

/-! ## The correctness of the translation -/

/-- **The translation is correct.**  If `zv` and `lv` hold two positions of the input, the first
strictly before the second, then the nest of loops produced by `Transducers.trFor` produces the
same output as the source program, and leaves the same values in the variables of the source
program.  In the prenex form of the book `zv` and `lv` hold the first and the last position; the
forward prenex form of Exercise `exer:forward-for-transducer` uses the first and the second one
instead, which is why only the order of the two positions is assumed here. -/
theorem trFor_spec (zv lv k₀ : ℕ) (hzv : zv < k₀) (hlv : lv < k₀) (w : List A) :
    ∀ (P : ForProg A B), (∀ i ∈ P.posVars, i < k₀) → (∀ i ∈ P.boolVars, i < k₀) →
      zv ∉ P.posVars → lv ∉ P.posVars →
      ∀ (k : ℕ) (L : List (Bool × ℕ)) (b : ForProg A B) (k' : ℕ),
        trFor zv lv P k = (L, b, k') → k₀ ≤ k →
        ∀ pos : ℕ → ℕ, pos zv < pos lv → pos lv < w.length →
        ∀ bv₁ bv₂ : ℕ → Bool, (∀ i, i < k₀ → bv₁ i = bv₂ i) →
          (ForProg.exec w (ForProg.nestLoops L b) pos bv₁).2 = (ForProg.exec w P pos bv₂).2 ∧
            ∀ i, i < k₀ → (ForProg.exec w (ForProg.nestLoops L b) pos bv₁).1 i
              = (ForProg.exec w P pos bv₂).1 i := by
  intro P
  induction P with
  | skip =>
      rintro - - - - k L b k' heq hk pos hpz hpl bv₁ bv₂ hbv
      simp only [trFor, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact ⟨rfl, fun i hi => hbv i hi⟩
  | output c =>
      rintro - - - - k L b k' heq hk pos hpz hpl bv₁ bv₂ hbv
      simp only [trFor, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      exact ⟨rfl, fun i hi => hbv i hi⟩
  | assign j v =>
      rintro - - - - k L b k' heq hk pos hpz hpl bv₁ bv₂ hbv
      simp only [trFor, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      refine ⟨rfl, fun i hi => ?_⟩
      show Function.update bv₁ j v i = Function.update bv₂ j v i
      by_cases hij : i = j
      · subst hij; simp
      · simp [Function.update_of_ne hij, hbv i hi]
  | seq P Q ihP ihQ =>
      intro hpos hbool hzvP hlvP k L b k' heq hk pos hpz hpl bv₁ bv₂ hbv
      have hPpos : ∀ i ∈ P.posVars, i < k₀ := fun i hi => hpos i (by simp [ForProg.posVars, hi])
      have hQpos : ∀ i ∈ Q.posVars, i < k₀ := fun i hi => hpos i (by simp [ForProg.posVars, hi])
      have hPbool : ∀ i ∈ P.boolVars, i < k₀ :=
        fun i hi => hbool i (by simp [ForProg.boolVars, hi])
      have hQbool : ∀ i ∈ Q.boolVars, i < k₀ :=
        fun i hi => hbool i (by simp [ForProg.boolVars, hi])
      have hzvP' : zv ∉ P.posVars := fun h => hzvP (by simp [ForProg.posVars, h])
      have hzvQ' : zv ∉ Q.posVars := fun h => hzvP (by simp [ForProg.posVars, h])
      have hlvP' : lv ∉ P.posVars := fun h => hlvP (by simp [ForProg.posVars, h])
      have hlvQ' : lv ∉ Q.posVars := fun h => hlvP (by simp [ForProg.posVars, h])
      rcases hr₁ : trFor zv lv P (k + 1) with ⟨L₁, b₁, k₁⟩
      rcases hr₂ : trFor zv lv Q k₁ with ⟨L₂, b₂, k₂⟩
      have o₁ := trFor_ok zv lv P (k + 1) L₁ b₁ k₁ hr₁
      have o₂ := trFor_ok zv lv Q k₁ L₂ b₂ k₂ hr₂
      simp only [trFor, hr₁, hr₂, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      have hm₁ : k + 1 ≤ k₁ := o₁.mono
      have hf₁ : FreshNest k₀ (k + 1) k₁ L₁ b₁ := o₁.toFresh hzv hlv hPpos
      have hf₂ : FreshNest k₀ k₁ k₂ L₂ b₂ := o₂.toFresh hzv hlv hQpos
      rw [exec_merge_fresh w zv lv k₀ hzv hlv pos hpz hpl bv₁ k (k + 1) k₁ k₁ k₂ L₁ L₂ b₁ b₂
        hf₁ hf₂ (by omega) (by omega) (by omega) le_rfl (by have := o₂.mono; omega)]
      obtain ⟨e₁, e₂⟩ := ihP hPpos hPbool hzvP' hlvP' (k + 1) L₁ b₁ k₁ hr₁ (by omega) pos hpz hpl
        bv₁ bv₂ hbv
      obtain ⟨f₁, f₂⟩ := ihQ hQpos hQbool hzvQ' hlvQ' k₁ L₂ b₂ k₂ hr₂ (by omega) pos hpz hpl
        _ _ e₂
      refine ⟨?_, ?_⟩
      · show _ ++ _ = _ ++ _
        rw [e₁, f₁]
      · exact f₂
  | ite t P Q ihP ihQ =>
      intro hpos hbool hzvP hlvP k L b k' heq hk pos hpz hpl bv₁ bv₂ hbv
      have hPpos : ∀ i ∈ P.posVars, i < k₀ := fun i hi => hpos i (by simp [ForProg.posVars, hi])
      have hQpos : ∀ i ∈ Q.posVars, i < k₀ := fun i hi => hpos i (by simp [ForProg.posVars, hi])
      have hPbool : ∀ i ∈ P.boolVars, i < k₀ :=
        fun i hi => hbool i (by simp [ForProg.boolVars, hi])
      have hQbool : ∀ i ∈ Q.boolVars, i < k₀ :=
        fun i hi => hbool i (by simp [ForProg.boolVars, hi])
      have htbool : ∀ i ∈ t.boolVars, i < k₀ :=
        fun i hi => hbool i (by simp [ForProg.boolVars, hi])
      have htpos : ∀ i ∈ t.posVars, i < k₀ := fun i hi => hpos i (by simp [ForProg.posVars, hi])
      have hzvP' : zv ∉ P.posVars := fun h => hzvP (by simp [ForProg.posVars, h])
      have hzvQ' : zv ∉ Q.posVars := fun h => hzvP (by simp [ForProg.posVars, h])
      have hlvP' : lv ∉ P.posVars := fun h => hlvP (by simp [ForProg.posVars, h])
      have hlvQ' : lv ∉ Q.posVars := fun h => hlvP (by simp [ForProg.posVars, h])
      rcases hr₁ : trFor zv lv P (k + 3) with ⟨L₁, b₁, k₁⟩
      rcases hr₂ : trFor zv lv Q k₁ with ⟨L₂, b₂, k₂⟩
      have o₁ := trFor_ok zv lv P (k + 3) L₁ b₁ k₁ hr₁
      have o₂ := trFor_ok zv lv Q k₁ L₂ b₂ k₂ hr₂
      simp only [trFor, hr₁, hr₂, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      have hm₁ : k + 3 ≤ k₁ := o₁.mono
      have hm₂ : k₁ ≤ k₂ := o₂.mono
      set b₀ : ForProg A B :=
        ForProg.ite t (ForProg.assign (k + 1) true) (ForProg.assign (k + 1) false) with hb₀
      set c₁ : ForProg A B := ForProg.ite (ForTest.boolVar (k + 1)) b₁ ForProg.skip with hc₁
      set c₂ : ForProg A B := ForProg.ite (ForTest.not (ForTest.boolVar (k + 1))) b₂ ForProg.skip
        with hc₂
      -- freshness of the three nests that are merged
      have hf₀ : FreshNest k₀ (k + 3) (k + 3) ([] : List (Bool × ℕ)) b₀ := by
        refine ⟨by simp, by simp, fun i hi => ?_⟩
        simp only [hb₀, ForProg.posVars, List.append_nil, 
          ] at hi
        exact Or.inl (htpos i hi)
      have hf₁ : FreshNest k₀ (k + 3) k₁ L₁ c₁ := by
        refine ⟨o₁.loopRange, o₁.nodup, fun i hi => ?_⟩
        simp only [hc₁, ForProg.posVars, ForTest.posVars, List.nil_append, List.append_nil,
          ] at hi
        exact (o₁.toFresh (a := k₀) hzv hlv hPpos).posOk i hi
      have hf₂ : FreshNest k₀ k₁ k₂ L₂ c₂ := by
        refine ⟨o₂.loopRange, o₂.nodup, fun i hi => ?_⟩
        simp only [hc₂, ForProg.posVars, ForTest.posVars, List.nil_append, List.append_nil,
          ] at hi
        exact (o₂.toFresh (a := k₀) hzv hlv hQpos).posOk i hi
      have hfM : FreshNest k₀ (k + 2) k₁ (mergeLoops (k + 2) [] L₁)
          (mergeBody zv lv (k + 2) [] L₁ b₀ c₁) :=
        FreshNest.merge hf₀ hf₁ hzv hlv (by omega) (by omega) le_rfl le_rfl (by omega)
      -- unfold the two merges
      rw [exec_merge_fresh w zv lv k₀ hzv hlv pos hpz hpl bv₁ k (k + 2) k₁ k₁ k₂
        (mergeLoops (k + 2) [] L₁) L₂ _ c₂ hfM hf₂ (by omega) (by omega) (by omega) le_rfl
        (by omega)]
      have hinner : ForProg.exec w (ForProg.nestLoops (mergeLoops (k + 2) [] L₁)
            (mergeBody zv lv (k + 2) [] L₁ b₀ c₁)) pos bv₁
          = ForProg.exec w (ForProg.seq b₀ (ForProg.nestLoops L₁ c₁)) pos bv₁ :=
        exec_merge_fresh w zv lv k₀ hzv hlv pos hpz hpl bv₁ (k + 2) (k + 3) (k + 3) (k + 3) k₁
          [] L₁ b₀ c₁ hf₀ hf₁ (by omega) (by omega) le_rfl le_rfl (by omega)
      rw [show ForProg.exec w (ForProg.seq (ForProg.nestLoops (mergeLoops (k + 2) [] L₁)
              (mergeBody zv lv (k + 2) [] L₁ b₀ c₁)) (ForProg.nestLoops L₂ c₂)) pos bv₁
            = ForProg.exec w (ForProg.seq (ForProg.seq b₀ (ForProg.nestLoops L₁ c₁))
              (ForProg.nestLoops L₂ c₂)) pos bv₁ from by
          simp only [ForProg.exec, hinner]]
      -- the value of the test
      have hT : ForTest.Holds w pos bv₁ t ↔ ForTest.Holds w pos bv₂ t :=
        ForTest.holds_congr w t pos pos bv₁ bv₂ (fun _ _ => rfl)
          (fun i hi => hbv i (htbool i hi))
      have hb₁bool : (k + 1) ∉ b₁.boolVars := by
        intro h
        rcases o₁.boolOk (k + 1) h with h' | h'
        · have := hPbool (k + 1) h'; omega
        · omega
      have hb₂bool : (k + 1) ∉ b₂.boolVars := by
        intro h
        rcases o₂.boolOk (k + 1) h with h' | h'
        · have := hQbool (k + 1) h'; omega
        · omega
      by_cases hTv : ForTest.Holds w pos bv₂ t
      · -- the first branch is taken
        have hexec₀ : ForProg.exec w b₀ pos bv₁ = (Function.update bv₁ (k + 1) true, []) := by
          simp only [hb₀, ForProg.exec, if_pos (hT.mpr hTv)]
        set s₀ := Function.update bv₁ (k + 1) true with hs₀
        have hs₀true : s₀ (k + 1) = true := by simp [hs₀]
        have hs₀bv : ∀ i, i < k₀ → s₀ i = bv₂ i := by
          intro i hi
          rw [hs₀, Function.update_of_ne (by omega), hbv i hi]
        have hguard : ForProg.exec w (ForProg.nestLoops L₁ c₁) pos s₀
            = ForProg.exec w (ForProg.nestLoops L₁ b₁) pos s₀ := by
          refine nest_congr w L₁ c₁ b₁ pos s₀ (fun s => s (k + 1) = true) hs₀true
            (fun tt s hs => ?_) (fun tt s hs => ?_)
          · simp only [hc₁, ForProg.exec, ForTest.Holds, if_pos hs]
          · simp only [hc₁, ForProg.exec, ForTest.Holds, if_pos hs]
            exact (ForProg.exec_bv_unchanged w b₁ _ s hb₁bool).trans hs
        obtain ⟨e₁, e₂⟩ := ihP hPpos hPbool hzvP' hlvP' (k + 3) L₁ b₁ k₁ hr₁ (by omega) pos hpz hpl
          s₀ bv₂ hs₀bv
        have hs₁true : (ForProg.exec w (ForProg.nestLoops L₁ b₁) pos s₀).1 (k + 1) = true := by
          rw [nest_bv_fix w L₁ b₁ pos s₀ (k + 1)
            (fun tt s => ForProg.exec_bv_unchanged w b₁ _ s hb₁bool)]
          exact hs₀true
        have hkill : ForProg.exec w (ForProg.nestLoops L₂ c₂) pos
            (ForProg.exec w (ForProg.nestLoops L₁ b₁) pos s₀).1
            = ((ForProg.exec w (ForProg.nestLoops L₁ b₁) pos s₀).1, []) := by
          refine nest_noop w L₂ c₂ pos _ (fun tt => ?_)
          simp only [hc₂, ForProg.exec, ForTest.Holds, hs₁true]
          rw [if_neg (by simp)]
        have hval : ForProg.exec w (ForProg.seq (ForProg.seq b₀ (ForProg.nestLoops L₁ c₁))
              (ForProg.nestLoops L₂ c₂)) pos bv₁
            = ForProg.exec w (ForProg.nestLoops L₁ b₁) pos s₀ := by
          simp only [ForProg.exec, hexec₀]
          rw [hguard, hkill]
          simp
        rw [hval]
        simp only [ForProg.exec]
        rw [if_pos hTv]
        exact ⟨e₁, e₂⟩
      · -- the second branch is taken
        have hexec₀ : ForProg.exec w b₀ pos bv₁ = (Function.update bv₁ (k + 1) false, []) := by
          simp only [hb₀, ForProg.exec, if_neg (fun h => hTv (hT.mp h))]
        set s₀ := Function.update bv₁ (k + 1) false with hs₀
        have hs₀false : s₀ (k + 1) = false := by simp [hs₀]
        have hs₀bv : ∀ i, i < k₀ → s₀ i = bv₂ i := by
          intro i hi
          rw [hs₀, Function.update_of_ne (by omega), hbv i hi]
        have hskip : ForProg.exec w (ForProg.nestLoops L₁ c₁) pos s₀ = (s₀, []) := by
          refine nest_noop w L₁ c₁ pos s₀ (fun tt => ?_)
          simp only [hc₁, ForProg.exec, ForTest.Holds, hs₀false]
          rw [if_neg (by simp)]
        have hguard : ForProg.exec w (ForProg.nestLoops L₂ c₂) pos s₀
            = ForProg.exec w (ForProg.nestLoops L₂ b₂) pos s₀ := by
          refine nest_congr w L₂ c₂ b₂ pos s₀ (fun s => s (k + 1) = false) hs₀false
            (fun tt s hs => ?_) (fun tt s hs => ?_)
          · simp only [hc₂, ForProg.exec, ForTest.Holds, hs]
            rw [if_pos (by simp)]
          · simp only [hc₂, ForProg.exec, ForTest.Holds, hs]
            rw [if_pos (by simp)]
            exact (ForProg.exec_bv_unchanged w b₂ _ s hb₂bool).trans hs
        obtain ⟨e₁, e₂⟩ := ihQ hQpos hQbool hzvQ' hlvQ' k₁ L₂ b₂ k₂ hr₂ (by omega) pos hpz hpl
          s₀ bv₂ hs₀bv
        have hval : ForProg.exec w (ForProg.seq (ForProg.seq b₀ (ForProg.nestLoops L₁ c₁))
              (ForProg.nestLoops L₂ c₂)) pos bv₁
            = ForProg.exec w (ForProg.nestLoops L₂ b₂) pos s₀ := by
          simp only [ForProg.exec, hexec₀, hskip]
          rw [hguard]
          simp
        rw [hval]
        simp only [ForProg.exec]
        rw [if_neg hTv]
        exact ⟨e₁, e₂⟩
  | loop d x P ih =>
      intro hpos hbool hzvP hlvP k L b k' heq hk pos hpz hpl bv₁ bv₂ hbv
      have hPpos : ∀ i ∈ P.posVars, i < k₀ := fun i hi => hpos i (by simp [ForProg.posVars, hi])
      have hPbool : ∀ i ∈ P.boolVars, i < k₀ := fun i hi => hbool i (by simp [ForProg.boolVars, hi])
      have hzvP' : zv ∉ P.posVars := fun h => hzvP (by simp [ForProg.posVars, h])
      have hlvP' : lv ∉ P.posVars := fun h => hlvP (by simp [ForProg.posVars, h])
      have hzx : zv ≠ x := fun h => hzvP (by simp [ForProg.posVars, h])
      have hlx : lv ≠ x := fun h => hlvP (by simp [ForProg.posVars, h])
      have hxk : x < k₀ := hpos x (by simp [ForProg.posVars])
      rcases hr : trFor zv lv P (k + 1) with ⟨L₁, b₁, k₁⟩
      have o₁ := trFor_ok zv lv P (k + 1) L₁ b₁ k₁ hr
      simp only [trFor, hr, Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl, rfl⟩ := heq
      have hm : k + 1 ≤ k₁ := o₁.mono
      have hf₁ : FreshNest k₀ (k + 1) k₁ L₁ b₁ := o₁.toFresh hzv hlv hPpos
      have hkb : k ∉ b₁.posVars := by
        intro h
        rcases hf₁.posOk k h with h' | h' <;> omega
      have hxL : x ∉ L₁.map Prod.snd := by
        intro h
        have := hf₁.loopRange x h
        omega
      have hkL : k ∉ L₁.map Prod.snd := by
        intro h
        have := hf₁.loopRange k h
        omega
      -- renaming the loop variable
      have hren : ∀ (s : ℕ → Bool) (p : ℕ),
          ForProg.exec w (ForProg.nestLoops L₁
              (ForProg.renamePos (fun i => if i = x then k else i) b₁))
              (Function.update pos k p) s
            = ForProg.exec w (ForProg.nestLoops L₁ b₁) (Function.update pos x p) s := by
        intro s p
        rw [exec_nestLoops, exec_nestLoops]
        refine runList_congr_mem _ _ _ _ (fun s' tt htt => ?_)
        have hlen := length_of_mem_tuplesOf L₁ w.length htt
        rw [ForProg.exec_renamePos w _ b₁ o₁.loopFree]
        refine ForProg.exec_congr_pos w b₁ _ _ _ (fun i hi => ?_)
        by_cases hix : i = x
        · subst hix
          rw [if_pos rfl, setTuple_of_not_mem L₁ tt _ hkL,
            setTuple_of_not_mem L₁ tt _ hxL, Function.update_self, Function.update_self]
        · rw [if_neg hix]
          by_cases hiL : i ∈ L₁.map Prod.snd
          · exact setTuple_mem_eq L₁ tt hlen _ _ hiL
          · rw [setTuple_of_not_mem L₁ tt _ hiL, setTuple_of_not_mem L₁ tt _ hiL,
              Function.update_of_ne (by rintro rfl; exact hkb hi),
              Function.update_of_ne hix]
      have hLeft : ForProg.exec w (ForProg.nestLoops ((d, k) :: L₁)
            (ForProg.renamePos (fun i => if i = x then k else i) b₁)) pos bv₁
          = runList (fun s p => ForProg.exec w (ForProg.nestLoops L₁ b₁)
              (Function.update pos x p) s) (loopRange d w.length) bv₁ := by
        show ForProg.exec w (ForProg.loop d k _) pos bv₁ = _
        rw [ForProg.exec, forLoopRun_eq_runList,
          show (if d then List.range w.length else (List.range w.length).reverse)
            = loopRange d w.length from by cases d <;> rfl]
        exact runList_congr_mem _ _ _ _ (fun s p _ => hren s p)
      have hRight : ForProg.exec w (ForProg.loop d x P) pos bv₂
          = runList (fun s p => ForProg.exec w P (Function.update pos x p) s)
              (loopRange d w.length) bv₂ := by
        rw [ForProg.exec, forLoopRun_eq_runList,
          show (if d then List.range w.length else (List.range w.length).reverse)
            = loopRange d w.length from by cases d <;> rfl]
      rw [hLeft, hRight]
      refine runList_sim _ _ (fun s₁ s₂ => ∀ i, i < k₀ → s₁ i = s₂ i) _ bv₁ bv₂ hbv
        (fun t₁ t₂ p _ hR => ?_)
      exact ih hPpos hPbool hzvP' hlvP' (k + 1) L₁ b₁ k₁ hr (by omega) (Function.update pos x p)
        (by rw [Function.update_of_ne hzx, Function.update_of_ne hlx]; exact hpz)
        (by rw [Function.update_of_ne hlx]; exact hpl) t₁ t₂ hR

end Lax194892Proofs.Transducers
