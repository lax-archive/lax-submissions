/-
The transducers of the easy direction of Theorem `thm:regular-terms` of *Transducers*
(M. Bojańczyk).

Every atomic term of Definition `def:regular-terms`, except for reverse, is implemented under
string representation by a machine of the following shape: it reads the input from left to right,
it keeps a *mode* from a finite set together with the current bracket depth, and at every letter,
and once more at the end of the input, it writes a block that depends on the mode, on the depth and
on the letter.  Such a machine is a sequential rewriting with a final output, hence a rational
function (`Transducers.isRationalFun_seqFinEval`), hence a regular one.

The depth is kept as an element of `Fin (N+1)`, that is, it is capped at `N`; the cap is never
reached on a well-formed input, because the depth of a representation is at most the height of its
type (`Transducers.Comb.repr_depth_le`), and `N` is chosen larger than that.  Nothing has to be
proved about the behaviour of a machine on an input that is not a representation: Definition
`def:regular-functions-on-types-under-string-representation` only constrains it on the
representations.

The work of the file is `Transducers.Comb.Mach.runFrom_repr`: a machine that copies -- or, more
generally, that applies a fixed letter-to-block map `g` and does not change its mode -- at every
letter of depth greater than the current one, and at every *transparent* letter of the current
depth, runs through a whole sub-representation without changing its mode and comes back to the
depth it started at.  This is the simulation lemma that lets the correctness proof of each atomic
term skip over the sub-representations of the input and look only at the delimiters that separate
them.
-/
import Lax709149Proofs.Source.PartC.CombDepth
import Lax916827Proofs.Source.PartC.RatSeq
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax709149Proofs.Transducers
namespace Comb

variable {M O : Type}

/-- The blocks of a copying machine reassemble the string. -/
@[simp] lemma flatten_map_single (l : List Sym8) : (l.map (fun c => [c])).flatten = l := by
  induction l with
  | nil => rfl
  | cons c l ih => simp [ih]

/-- The blocks of an erasing machine are empty. -/
@[simp] lemma flatten_map_nil (l : List Sym8) :
    (l.map (fun _ => ([] : List Sym8))).flatten = [] := by
  induction l with
  | nil => rfl
  | cons c l ih => simp

/-! ## The capped bracket counter -/

/-- One step of the bracket counter, capped at `N`. -/
def dstep {N : ℕ} (d : Fin (N + 1)) (c : Sym8) : Fin (N + 1) :=
  if wt c = 1 then ⟨min (d.1 + 1) N, by omega⟩
  else if wt c = -1 then ⟨d.1 - 1, by omega⟩
  else d

/-- The bracket counter after reading a string. -/
def dfold {N : ℕ} (d : Fin (N + 1)) (w : List Sym8) : Fin (N + 1) := w.foldl dstep d

@[simp] lemma dfold_nil {N : ℕ} (d : Fin (N + 1)) : dfold d [] = d := rfl

@[simp] lemma dfold_cons {N : ℕ} (d : Fin (N + 1)) (c : Sym8) (w : List Sym8) :
    dfold d (c :: w) = dfold (dstep d c) w := rfl

lemma dstep_open {N : ℕ} {d : Fin (N + 1)} {c : Sym8} (hc : wt c = 1) (hd : d.1 + 1 ≤ N) :
    (dstep d c).1 = d.1 + 1 := by
  rw [dstep, if_pos hc]
  simp only []
  omega

lemma dstep_close {N : ℕ} {d : Fin (N + 1)} {c : Sym8} (hc : wt c = -1) :
    (dstep d c).1 = d.1 - 1 := by
  have h1 : ¬ (wt c = 1) := by rw [hc]; decide
  rw [dstep, if_neg h1, if_pos hc]

lemma dstep_neutral {N : ℕ} {d : Fin (N + 1)} {c : Sym8} (hc : wt c = 0) : dstep d c = d := by
  have h1 : ¬ (wt c = 1) := by rw [hc]; decide
  have h2 : ¬ (wt c = -1) := by rw [hc]; decide
  rw [dstep, if_neg h1, if_neg h2]

lemma wt_cases (c : Sym8) : wt c = 1 ∨ wt c = -1 ∨ wt c = 0 := by
  cases c <;> simp

/-- On a string all of whose prefixes have depth between `0` and `N`, the capped counter is the
true bracket depth. -/
lemma dfold_val {N : ℕ} : ∀ (w : List Sym8) (d : Fin (N + 1)),
    (∀ u v, w = u ++ v → 0 ≤ (d.1 : ℤ) + depth u) →
    (∀ u v, w = u ++ v → (d.1 : ℤ) + depth u ≤ N) →
    ((dfold d w).1 : ℤ) = (d.1 : ℤ) + depth w := by
  intro w
  induction w with
  | nil => intro d _ _; simp
  | cons c w ih =>
      intro d h0 hN
      have hc0 : 0 ≤ (d.1 : ℤ) + wt c := by
        have := h0 [c] w rfl
        simpa using this
      have hcN : (d.1 : ℤ) + wt c ≤ N := by
        have := hN [c] w rfl
        simpa using this
      have hval : ((dstep d c).1 : ℤ) = (d.1 : ℤ) + wt c := by
        rcases wt_cases c with h | h | h
        · rw [dstep, if_pos h]
          simp only [h]
          have : min (d.1 + 1) N = d.1 + 1 := by
            rw [h] at hcN
            omega
          rw [this]
          push_cast
          ring
        · have h1 : ¬ (wt c = 1) := by rw [h]; decide
          rw [dstep, if_neg h1, if_pos h]
          rw [h] at hc0 ⊢
          have : 1 ≤ d.1 := by omega
          push_cast [Nat.cast_sub this]
          ring
        · have h1 : ¬ (wt c = 1) := by rw [h]; decide
          have h2 : ¬ (wt c = -1) := by rw [h]; decide
          rw [dstep, if_neg h1, if_neg h2, h]
          ring
      rw [dfold_cons, ih (dstep d c) ?_ ?_, hval, depth_cons]
      · ring
      · intro u v huv
        have := h0 (c :: u) v (by rw [huv]; rfl)
        rw [hval]
        simp only [depth_cons] at this
        omega
      · intro u v huv
        have := hN (c :: u) v (by rw [huv]; rfl)
        rw [hval]
        simp only [depth_cons] at this
        omega

/-! ## The machines -/

/-- A machine reading the string representation: a mode, and at every letter (and once at the end
of the input) a block of output, both depending on the mode and on the current bracket depth. -/
structure Mach (M : Type) (O : Type) where
  /-- The next mode, given the mode, the depth before the letter, and the letter. -/
  step : M → ℕ → Sym8 → M
  /-- The block written at a letter. -/
  out : M → ℕ → Sym8 → List O
  /-- The block written at the end of the input. -/
  fin : M → ℕ → List O

variable (T : Mach M O) (N : ℕ)

/-- The transition function of the machine on pairs (mode, capped depth). -/
def Mach.st : M × Fin (N + 1) → Sym8 → M × Fin (N + 1) :=
  fun s c => (T.step s.1 s.2.1 c, dstep s.2 c)

/-- The function computed by the machine, started in a given state. -/
def Mach.runFrom (s : M × Fin (N + 1)) (w : List Sym8) : List O :=
  seqFinEval (T.st N) (fun s c => T.out s.1 s.2.1 c) (fun s => T.fin s.1 s.2.1) s w

/-- The function computed by the machine, started in the mode `m₀` at depth `0`. -/
def Mach.run (m₀ : M) : List Sym8 → List O := fun w => T.runFrom N (m₀, 0) w

@[simp] lemma Mach.runFrom_nil (s : M × Fin (N + 1)) : T.runFrom N s [] = T.fin s.1 s.2.1 := rfl

@[simp] lemma Mach.runFrom_cons (s : M × Fin (N + 1)) (c : Sym8) (w : List Sym8) :
    T.runFrom N s (c :: w)
      = T.out s.1 s.2.1 c ++ T.runFrom N (T.step s.1 s.2.1 c, dstep s.2 c) w := rfl

lemma Mach.run_eq (m₀ : M) (w : List Sym8) : T.run N m₀ w = T.runFrom N (m₀, 0) w := rfl

/-- **The function computed by such a machine is regular** -- indeed rational. -/
theorem Mach.isRationalFun_run [Finite M] [Finite O] (m₀ : M) : IsRationalFun (T.run N m₀) :=
  isRationalFun_seqFinEval (T.st N) (m₀, 0) (fun s c => T.out s.1 s.2.1 c)
    (fun s => T.fin s.1 s.2.1)

theorem Mach.isRegularFun_run [Finite M] [Finite O] (m₀ : M) : IsRegularFun (T.run N m₀) :=
  IsRegularFun.of_rational (T.isRationalFun_run N m₀)

/-! ## Running through a sub-representation -/

/-- A machine that does not change its mode, and applies the fixed map `g` to every letter, as
long as the depth stays above the depth `d₀` it started at (and at `d₀` itself, for a transparent
letter), runs through such a string writing `g` of it, and ends where it started. -/
theorem Mach.runFrom_copy (m : M) (d₀ : ℕ) (g : Sym8 → List O)
    (hcopy : ∀ e c, d₀ ≤ e → (e = d₀ → transparent c = true) →
      T.step m e c = m ∧ T.out m e c = g c) :
    ∀ (w : List Sym8) (d : Fin (N + 1)) (rest : List Sym8),
      (∀ u c v, w = u ++ c :: v →
        d₀ ≤ (dfold d u).1 ∧ ((dfold d u).1 = d₀ → transparent c = true)) →
      T.runFrom N (m, d) (w ++ rest) = (w.map g).flatten ++ T.runFrom N (m, dfold d w) rest := by
  intro w
  induction w with
  | nil => intro d rest _; simp
  | cons c w ih =>
      intro d rest hw
      have h0 := hw [] c w rfl
      obtain ⟨hstep, hout⟩ := hcopy d.1 c (by simpa using h0.1) (by simpa using h0.2)
      have hrec : T.runFrom N (m, dstep d c) (w ++ rest)
          = (w.map g).flatten ++ T.runFrom N (m, dfold (dstep d c) w) rest := by
        refine ih (dstep d c) rest ?_
        intro u c' v huv
        have := hw (c :: u) c' v (by rw [huv]; rfl)
        simpa using this
      rw [List.cons_append, Mach.runFrom_cons]
      simp only [hout, hstep]
      rw [hrec, dfold_cons]
      simp

/-- The machine copies, through `g`, in mode `m`: it does not change its mode and writes `g c` at
every letter `c` of depth above `d₀`, and at every transparent letter of depth `d₀`. -/
def Mach.Copies (m : M) (d₀ : ℕ) (g : Sym8 → List O) : Prop :=
  ∀ e c, d₀ ≤ e → (e = d₀ → transparent c = true) → T.step m e c = m ∧ T.out m e c = g c

/-- The machine also copies the separators of a list at depth `d₀`. -/
def Mach.CopiesComma (m : M) (d₀ : ℕ) (g : Sym8 → List O) : Prop :=
  T.step m d₀ Sym8.comma = m ∧ T.out m d₀ Sym8.comma = g Sym8.comma

/-- The counter is the true depth on every prefix of a representation, provided the cap `N` is
larger than the height of the type. -/
lemma dfold_repr {N : ℕ} (t : Ty) (x : t.Elt) (d : Fin (N + 1))
    (hcap : (d.1 : ℤ) + (t.height : ℤ) ≤ N) :
    ∀ u v, t.repr x = u ++ v → ((dfold d u).1 : ℤ) = (d.1 : ℤ) + depth u := by
  intro u v huv
  refine dfold_val u d ?_ ?_
  · intro u' v' hu'
    have hsplit : t.repr x = u' ++ (v' ++ v) := by rw [huv, hu', List.append_assoc]
    have h1 : 0 ≤ depth u' := (repr_balanced t x).prefix_nonneg hsplit
    have h2 : (0 : ℤ) ≤ (d.1 : ℤ) := Int.natCast_nonneg _
    omega
  · intro u' v' hu'
    have hsplit : t.repr x = u' ++ (v' ++ v) := by rw [huv, hu', List.append_assoc]
    have h1 : depth u' ≤ (t.height : ℤ) := repr_depth_le t x u' (v' ++ v) hsplit
    omega

/-- The counter comes back to where it started after a whole representation. -/
lemma dfold_repr_full {N : ℕ} (t : Ty) (x : t.Elt) (d : Fin (N + 1))
    (hcap : (d.1 : ℤ) + (t.height : ℤ) ≤ N) : dfold d (t.repr x) = d := by
  have h := dfold_repr t x d hcap (t.repr x) [] (by simp)
  refine Fin.ext ?_
  have : ((dfold d (t.repr x)).1 : ℤ) = (d.1 : ℤ) := by rw [h, depth_repr]; ring
  exact_mod_cast this

/-- The hypothesis of `Mach.runFrom_copy`, for a representation read from the depth `d`. -/
lemma repr_run_cond {N : ℕ} (t : Ty) (x : t.Elt) (d : Fin (N + 1))
    (hcap : (d.1 : ℤ) + (t.height : ℤ) ≤ N) :
    ∀ u c v, t.repr x = u ++ c :: v →
      d.1 ≤ (dfold d u).1 ∧ ((dfold d u).1 = d.1 → transparent c = true) := by
  intro u c v huv
  have hu : ((dfold d u).1 : ℤ) = (d.1 : ℤ) + depth u := dfold_repr t x d hcap u (c :: v) huv
  have h1 : 0 ≤ depth u := (repr_balanced t x).2 u c v huv
  refine ⟨by omega, fun heq => ?_⟩
  have hzero : depth u = 0 := by rw [heq] at hu; omega
  exact ((repr_shape t x).2 u c v huv).2 hzero

/-- **Running through a string while the mode evolves.**  A machine whose mode is updated by
`upd`, and which writes nothing, at every letter of depth above `d₀` and at every transparent
letter of depth `d₀`, runs through such a string writing nothing and comes back to the depth it
started at, its mode having been updated by every letter.  This is the version of
`Mach.runFrom_copy` for a machine that reads a sub-representation in order to identify it. -/
theorem Mach.runFrom_scan (P : M → Prop) (upd : M → Sym8 → M) (d₀ : ℕ)
    (hstep : ∀ m e c, P m → d₀ ≤ e → (e = d₀ → transparent c = true) →
      T.step m e c = upd m c ∧ T.out m e c = [] ∧ P (upd m c)) :
    ∀ (w : List Sym8) (m : M) (d : Fin (N + 1)) (rest : List Sym8), P m →
      (∀ u c v, w = u ++ c :: v →
        d₀ ≤ (dfold d u).1 ∧ ((dfold d u).1 = d₀ → transparent c = true)) →
      T.runFrom N (m, d) (w ++ rest) = T.runFrom N (w.foldl upd m, dfold d w) rest := by
  intro w
  induction w with
  | nil => intro m d rest _ _; simp
  | cons c w ih =>
      intro m d rest hP hw
      have h0 := hw [] c w rfl
      obtain ⟨hs, ho, hP'⟩ := hstep m d.1 c hP (by simpa using h0.1) (by simpa using h0.2)
      rw [List.cons_append, Mach.runFrom_cons, hs, ho, List.nil_append]
      rw [ih (upd m c) (dstep d c) rest hP' ?_]
      · simp
      · intro u c' v huv
        have := hw (c :: u) c' v (by rw [huv]; rfl)
        simpa using this

/-- **Running through a sub-representation while the mode evolves.** -/
theorem Mach.runFrom_repr_scan (P : M → Prop) (upd : M → Sym8 → M) (m : M) (t : Ty) (x : t.Elt)
    (d : Fin (N + 1)) (rest : List Sym8) (hcap : (d.1 : ℤ) + (t.height : ℤ) ≤ N) (hP : P m)
    (hstep : ∀ m e c, P m → d.1 ≤ e → (e = d.1 → transparent c = true) →
      T.step m e c = upd m c ∧ T.out m e c = [] ∧ P (upd m c)) :
    T.runFrom N (m, d) (t.repr x ++ rest) = T.runFrom N ((t.repr x).foldl upd m, d) rest := by
  rw [T.runFrom_scan N P upd d.1 hstep (t.repr x) m d rest hP (repr_run_cond t x d hcap),
    dfold_repr_full t x d hcap]

/-- **Running through a sub-representation.**  A machine that copies in its mode at the depth it
starts at reads a whole representation without changing its mode, comes back to that depth, and
writes `g` of the representation. -/
theorem Mach.runFrom_repr (m : M) (g : Sym8 → List O) (t : Ty) (x : t.Elt) (d : Fin (N + 1))
    (rest : List Sym8) (hcap : (d.1 : ℤ) + (t.height : ℤ) ≤ N) (hcopy : T.Copies m d.1 g) :
    T.runFrom N (m, d) (t.repr x ++ rest)
      = ((t.repr x).map g).flatten ++ T.runFrom N (m, d) rest := by
  have h := T.runFrom_copy N m d.1 g hcopy (t.repr x) d rest (repr_run_cond t x d hcap)
  rw [h, dfold_repr_full t x d hcap]

/-- **Running through a sub-representation whose first letter is read in another mode.**  The
machine commits at the first letter of the representation -- it writes whatever it writes there and
switches to a mode that copies -- and then runs through the rest of the representation. -/
theorem Mach.runFrom_repr_cons (m m' : M) (g : Sym8 → List O) (t : Ty) (x : t.Elt) (c : Sym8)
    (w : List Sym8) (hx : t.repr x = c :: w) (d : Fin (N + 1)) (rest : List Sym8)
    (hcap : (d.1 : ℤ) + (t.height : ℤ) ≤ N) (hstep : T.step m d.1 c = m')
    (hcopy : T.Copies m' d.1 g) :
    T.runFrom N (m, d) (t.repr x ++ rest)
      = T.out m d.1 c ++ ((w.map g).flatten ++ T.runFrom N (m', d) rest) := by
  have hcond := repr_run_cond t x d hcap
  have hd : dfold d (t.repr x) = d := dfold_repr_full t x d hcap
  rw [hx] at hd
  rw [hx, List.cons_append, Mach.runFrom_cons, hstep]
  have h := T.runFrom_copy N m' d.1 g hcopy w (dstep d c) rest ?_
  · rw [h]
    rw [show dfold (dstep d c) w = d from hd]
  · intro u c' v huv
    have := hcond (c :: u) c' v (by rw [hx, huv]; rfl)
    simpa using this

/-- A machine in a mode that writes nothing and never leaves that mode writes nothing. -/
theorem Mach.runFrom_dead (m : M) (hstep : ∀ e c, T.step m e c = m)
    (hout : ∀ e c, T.out m e c = []) (hfin : ∀ e, T.fin m e = []) :
    ∀ (w : List Sym8) (d : Fin (N + 1)), T.runFrom N (m, d) w = [] := by
  intro w
  induction w with
  | nil => intro d; simpa using hfin d.1
  | cons c w ih => intro d; rw [Mach.runFrom_cons, hout, hstep, ih]; rfl

/-- **Running through the entries of a list that follow the first one.** -/
theorem Mach.runFrom_joinSepTail (m : M) (g : Sym8 → List O) (A : Ty) (d : Fin (N + 1))
    (hcap : (d.1 : ℤ) + (A.height : ℤ) ≤ N) (hcopy : T.Copies m d.1 g)
    (hcomma : T.CopiesComma m d.1 g) :
    ∀ (l : List A.Elt) (rest : List Sym8),
      T.runFrom N (m, d) (joinSepTail A l ++ rest)
        = ((joinSepTail A l).map g).flatten ++ T.runFrom N (m, d) rest := by
  intro l
  induction l with
  | nil => intro rest; simp
  | cons a l ih =>
      intro rest
      rw [joinSepTail_cons, joinSep_cons, List.cons_append, Mach.runFrom_cons, hcomma.1,
        hcomma.2, dstep_neutral (by simp : wt Sym8.comma = 0), List.append_assoc,
        T.runFrom_repr N m g A a d _ hcap hcopy, ih rest]
      simp

/-- **Running through the whole body of a list representation.** -/
theorem Mach.runFrom_joinSep (m : M) (g : Sym8 → List O) (A : Ty) (d : Fin (N + 1))
    (hcap : (d.1 : ℤ) + (A.height : ℤ) ≤ N) (hcopy : T.Copies m d.1 g)
    (hcomma : T.CopiesComma m d.1 g) (l : List A.Elt) (rest : List Sym8) :
    T.runFrom N (m, d) (joinSep (l.map A.repr) ++ rest)
      = ((joinSep (l.map A.repr)).map g).flatten ++ T.runFrom N (m, d) rest := by
  cases l with
  | nil => simp
  | cons a l =>
      rw [joinSep_cons, List.append_assoc, T.runFrom_repr N m g A a d _ hcap hcopy,
        T.runFrom_joinSepTail N m g A d hcap hcopy hcomma l rest]
      simp

end Comb
end Lax709149Proofs.Transducers
