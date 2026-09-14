/-
Part D: for-transducers -- the translation used for the composition of two for-transducers.

Let `f` be computed, on the inputs of length at least two, by the nest of loops `L` with loop-free
body `p` producing at most one letter per iteration, and let `Q` be a for-transducer computing `g`.
This file defines the program `Transducers.tr` translating `Q` into a for-transducer over the input
of `f`: a position of the string `f w` is represented by the tuple of positions of `w` at which the
inner nest produces the corresponding letter, so a position variable of `Q` is represented by a
block of position variables of the translation, one for each loop of the inner nest.  A block is
attached to the nesting depth of the loop of `Q` that binds the variable, so that the blocks of the
enclosing loops are left untouched; the environment `env` records, for every position variable of
`Q`, the depth of its block.

The order and equality tests of `Q` become the lexicographic comparison and the equality of tuples;
its label tests are answered by the re-simulation `Transducers.resim` of the inner nest, which
places the answer in the flag `flQ`; and its loops become nests of loops over the tuples, guarded
by the test -- again answered by a re-simulation -- that the tuple is one at which the inner nest
produces a letter.
-/
import Lax194892Proofs.Source.PartD.ForEvents

namespace Lax194892Proofs.Transducers

open scoped Classical

variable {A B C : Type}

/-! ## The blocks of position variables -/

/-- The block of position variables representing, at the nesting depth `lvl`, a position variable
of the translated program: one variable for each loop of the inner nest. -/
def blk (L : List (Bool × ℕ)) (base lvl : ℕ) : List ℕ :=
  (List.range L.length).map (fun j => base + 2 * (lvl * (L.length + 1) + j))

/-- The Boolean variable representing a Boolean variable of the translated program. -/
def qbv (base i : ℕ) : ℕ := base + 2 * i + 1

@[simp] lemma blk_length (L : List (Bool × ℕ)) (base lvl : ℕ) :
    (blk L base lvl).length = L.length := by simp [blk]

lemma mem_blk_iff (L : List (Bool × ℕ)) (base lvl z : ℕ) :
    z ∈ blk L base lvl ↔ ∃ j, j < L.length ∧ z = base + 2 * (lvl * (L.length + 1) + j) := by
  simp only [blk, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩

lemma blk_nodup (L : List (Bool × ℕ)) (base lvl : ℕ) : (blk L base lvl).Nodup := by
  refine (List.nodup_range).map_on (fun a _ b _ h => ?_)
  omega

lemma le_of_mem_blk {L : List (Bool × ℕ)} {base lvl z : ℕ} (hz : z ∈ blk L base lvl) :
    base ≤ z := by
  obtain ⟨j, -, rfl⟩ := (mem_blk_iff L base lvl z).mp hz
  omega

lemma blk_disjoint {L : List (Bool × ℕ)} {base lvl lvl' z : ℕ} (h : lvl ≠ lvl')
    (hz : z ∈ blk L base lvl) : z ∉ blk L base lvl' := by
  obtain ⟨j, hj, rfl⟩ := (mem_blk_iff L base lvl z).mp hz
  intro hc
  obtain ⟨j', hj', he⟩ := (mem_blk_iff L base lvl' _).mp hc
  have h1 : lvl * (L.length + 1) + j = lvl' * (L.length + 1) + j' := by omega
  have h2 : lvl ≠ lvl' → False := by
    intro _
    rcases Nat.lt_or_ge lvl lvl' with hlt | hge
    · have : (lvl + 1) * (L.length + 1) ≤ lvl' * (L.length + 1) :=
        Nat.mul_le_mul_right _ hlt
      have : lvl * (L.length + 1) + (L.length + 1) ≤ lvl' * (L.length + 1) := by
        rw [Nat.succ_mul] at this; omega
      omega
    · have hlt' : lvl' < lvl := by omega
      have : (lvl' + 1) * (L.length + 1) ≤ lvl * (L.length + 1) :=
        Nat.mul_le_mul_right _ hlt'
      have : lvl' * (L.length + 1) + (L.length + 1) ≤ lvl * (L.length + 1) := by
        rw [Nat.succ_mul] at this; omega
      omega
  exact h2 h

lemma qbv_not_mem_blk (L : List (Bool × ℕ)) (base lvl i : ℕ) : qbv base i ∉ blk L base lvl := by
  intro hc
  obtain ⟨j, -, he⟩ := (mem_blk_iff L base lvl _).mp hc
  rw [qbv] at he
  omega

lemma le_qbv (base i : ℕ) : base ≤ qbv base i := by rw [qbv]; omega

lemma not_mem_blk_of_lt {L : List (Bool × ℕ)} {base lvl z : ℕ} (h : z < base) :
    z ∉ blk L base lvl := fun hc => by have := le_of_mem_blk hc; omega

/-! ## The nest of loops that binds a block -/

/-- The tuples visited by a nest of loops only depend on the directions of its loops. -/
lemma tuplesOf_congr_dirs : ∀ (L₁ L₂ : List (Bool × ℕ)) (n : ℕ),
    L₁.map Prod.fst = L₂.map Prod.fst → tuplesOf L₁ n = tuplesOf L₂ n := by
  intro L₁
  induction L₁ with
  | nil => intro L₂ n h; cases L₂ with
    | nil => rfl
    | cons a L => simp at h
  | cons a L₁ ih =>
      intro L₂ n h
      cases L₂ with
      | nil => simp at h
      | cons b L₂ =>
          simp only [List.map_cons, List.cons.injEq] at h
          obtain ⟨d, x⟩ := a
          obtain ⟨d', x'⟩ := b
          simp only at h
          rw [tuplesOf_cons, tuplesOf_cons, h.1, ih L₂ n h.2]

/-- The nest of loops binding the block of depth `lvl`, in the direction `d`. -/
def loopNest (L : List (Bool × ℕ)) (base lvl : ℕ) (d : Bool) : List (Bool × ℕ) :=
  if d then (L.map Prod.fst).zip (blk L base lvl)
  else negDirs ((L.map Prod.fst).zip (blk L base lvl))

@[simp] lemma map_snd_loopNest (L : List (Bool × ℕ)) (base lvl : ℕ) (d : Bool) :
    (loopNest L base lvl d).map Prod.snd = blk L base lvl := by
  have h : ((L.map Prod.fst).zip (blk L base lvl)).map Prod.snd = blk L base lvl := by
    rw [List.map_snd_zip]
    simp
  cases d <;> simp [loopNest, h]

@[simp] lemma map_fst_loopNest_true (L : List (Bool × ℕ)) (base lvl : ℕ) :
    (loopNest L base lvl true).map Prod.fst = L.map Prod.fst := by
  rw [loopNest, if_pos rfl, List.map_fst_zip]
  simp

@[simp] lemma length_loopNest (L : List (Bool × ℕ)) (base lvl : ℕ) (d : Bool) :
    (loopNest L base lvl d).length = L.length := by
  rw [← blk_length L base lvl, ← map_snd_loopNest L base lvl d, List.length_map]

lemma tuplesOf_loopNest (L : List (Bool × ℕ)) (base lvl : ℕ) (d : Bool) (n : ℕ) :
    tuplesOf (loopNest L base lvl d) n
      = if d then tuplesOf L n else (tuplesOf L n).reverse := by
  cases d
  · show tuplesOf (negDirs ((L.map Prod.fst).zip (blk L base lvl))) n = _
    rw [tuplesOf_negDirs, if_neg (by simp)]
    refine congrArg List.reverse (tuplesOf_congr_dirs _ _ n ?_)
    rw [List.map_fst_zip]
    simp
  · rw [if_pos rfl]
    exact tuplesOf_congr_dirs _ _ n (map_fst_loopNest_true L base lvl)

/-! ## The translation -/

/-- The program computing, in the flag `flQ`, the answer to the label test of a conditional. -/
noncomputable def preTest (L : List (Bool × ℕ)) (p : ForProg A B) (base flQ flS : ℕ) (env : ℕ → ℕ) :
    ForTest B → ForProg A C
  | ForTest.label y b => resim L p (blk L base (env y)) flQ flS (fun c => decide (c = b))
  | _ => ForProg.skip

/-- The translation of a test: a Boolean variable becomes its representative, an equality or order
test becomes a comparison of the corresponding tuples of position variables, and a label test is
read off the flag `flQ` computed by `Transducers.preTest`. -/
def trTest (L : List (Bool × ℕ)) (base flQ : ℕ) (env : ℕ → ℕ) : ForTest B → ForTest A
  | ForTest.boolVar i => ForTest.boolVar (qbv base i)
  | ForTest.eqPos y y' => eqTupleTest (blk L base (env y)) (blk L base (env y'))
  | ForTest.lePos y y' =>
      ForTest.not (lexLtTest (L.map Prod.fst) (blk L base (env y')) (blk L base (env y)))
  | _ => ForTest.boolVar flQ

/-- **The translation of the outer for-transducer.**  A position variable of `Q` is represented by
the block of position variables attached to the depth `env y`; a loop of `Q` becomes a nest of
loops over the tuples of positions of the input of the inner transducer, guarded by the test that
the tuple is one at which the inner transducer produces a letter. -/
noncomputable def tr (L : List (Bool × ℕ)) (p : ForProg A B) (base flQ flS : ℕ) :
    (ℕ → ℕ) → ℕ → ForProg B C → ForProg A C
  | _, _, ForProg.skip => ForProg.skip
  | _, _, ForProg.output c => ForProg.output c
  | _, _, ForProg.assign i b => ForProg.assign (qbv base i) b
  | env, lvl, ForProg.seq S T =>
      ForProg.seq (tr L p base flQ flS env lvl S) (tr L p base flQ flS env lvl T)
  | env, lvl, ForProg.ite t S T =>
      ForProg.seq (preTest L p base flQ flS env t)
        (ForProg.ite (trTest L base flQ env t) (tr L p base flQ flS env lvl S)
          (tr L p base flQ flS env lvl T))
  | env, lvl, ForProg.loop d y S =>
      ForProg.nestLoops (loopNest L base lvl d)
        (ForProg.seq (resim L p (blk L base lvl) flQ flS (fun _ => true))
          (ForProg.ite (ForTest.boolVar flQ)
            (tr L p base flQ flS (Function.update env y lvl) (lvl + 1) S) ForProg.skip))

end Lax194892Proofs.Transducers
