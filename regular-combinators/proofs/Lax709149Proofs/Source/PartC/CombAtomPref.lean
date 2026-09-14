/-
Group prefix multiplication is regular under string representation.  Part of the easy direction of
Theorem `thm:regular-terms` of *Transducers* (M. Bojańczyk).

Group prefix multiplication `G* → G*` maps `g₁ ⋯ gₙ` to the list of the products
`g₁, g₁g₂, …, g₁⋯gₙ`, where `G` is a type whose set of elements is finite and carries a group
structure.  A machine reading the input from left to right computes it, provided that it can
recover the element of `G` from the string that represents it -- and this is where the finiteness
of `G` is used: the machine remembers the part of the current entry that it has read so far, which
is a *prefix of the representation of an element*, and there are only finitely many of those.

At the delimiter that closes an entry the machine has the whole representation of that entry in its
mode, and `Transducers.Comb.repr_injective` turns it into the element; the machine multiplies its
running product by it and writes the representation of the product, preceded by a comma.  The
leading comma is removed, and the brackets are put back, by the machine `dropFirstMach` of
`CombAtomConcat.lean`, exactly as for concatenation.
-/
import Lax709149Proofs.Source.PartC.CombAtomConcat
import Lax709149Proofs.Source.PartC.CombInj
import Lax709149Proofs.Source.PartC.CombTerms
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax709149Proofs.Transducers
namespace Comb

open scoped Classical

/-! ## Recovering an element from its representation -/

/-- The element represented by a string, if there is one. -/
noncomputable def elemOfRepr (G : Ty) (u : List Sym8) : G.Elt :=
  if h : ∃ g : G.Elt, G.repr g = u then h.choose else default

lemma elemOfRepr_repr (G : Ty) (g : G.Elt) : elemOfRepr G (G.repr g) = g := by
  have h : ∃ g' : G.Elt, G.repr g' = G.repr g := ⟨g, rfl⟩
  rw [elemOfRepr, dif_pos h]
  exact repr_injective G h.choose_spec

section Pref

variable (G : Ty) [Group G.Elt] [Finite G.Elt]

/-! ## The prefixes of the representations -/

omit [Group G.Elt] in
lemma pfxSet_finite : {u : List Sym8 | ∃ g : G.Elt, u <+: G.repr g}.Finite := by
  have h : {u : List Sym8 | ∃ g : G.Elt, u <+: G.repr g}
      = ⋃ g : G.Elt, {u : List Sym8 | u <+: G.repr g} := by
    ext u; simp
  rw [h]
  refine Set.finite_iUnion (fun g => ?_)
  refine Set.Finite.subset (Finset.finite_toSet ((G.repr g).inits.toFinset)) ?_
  intro u hu
  simpa [List.mem_inits] using hu

/-- A prefix of the representation of an element of `G`.  These are the states in which the machine
reads an entry of its input. -/
def Pfx : Type := {u : List Sym8 // ∃ g : G.Elt, u <+: G.repr g}

noncomputable instance : Finite (Pfx G) := (pfxSet_finite G).to_subtype

/-- The empty prefix. -/
def pfxNil : Pfx G := ⟨[], ⟨default, by simp⟩⟩

/-- Reading one more letter of an entry. -/
noncomputable def pstep : Option (Pfx G) → Sym8 → Option (Pfx G)
  | none, _ => none
  | some u, c =>
      if h : ∃ g : G.Elt, (u.val ++ [c]) <+: G.repr g then some ⟨u.val ++ [c], h⟩ else none

/-- The part of the current entry that has been read. -/
def pval : Option (Pfx G) → List Sym8
  | none => []
  | some u => u.val

/-- The element of `G` that the current entry represents. -/
noncomputable def pelem : Option (Pfx G) → G.Elt := fun p => elemOfRepr G (pval G p)

omit [Group G.Elt] [Finite G.Elt] in
lemma pfold : ∀ (w : List Sym8) (u : Pfx G), (∃ g : G.Elt, u.val ++ w <+: G.repr g) →
    pval G (w.foldl (pstep G) (some u)) = u.val ++ w := by
  intro w
  induction w with
  | nil => intro u _; simp [pval]
  | cons c w ih =>
      intro u hu
      obtain ⟨g, hg⟩ := hu
      have hpre : (u.val ++ [c]) <+: G.repr g := by
        refine List.IsPrefix.trans ?_ hg
        exact (List.prefix_append_right_inj (l := u.val)).2 ⟨w, rfl⟩
      have hstep : pstep G (some u) c = some ⟨u.val ++ [c], ⟨g, hpre⟩⟩ := by
        rw [pstep, dif_pos ⟨g, hpre⟩]
      rw [List.foldl_cons, hstep, ih ⟨u.val ++ [c], ⟨g, hpre⟩⟩ ⟨g, by
        rw [List.append_assoc]
        simpa using hg⟩]
      simp

/-! ## The machine -/

/-- The part of the input that the machine of group prefix multiplication is inside of. -/
inductive PrefPhase | start | blk | done
  deriving DecidableEq, Fintype

/-- The mode of the machine: the part of the input, the product of the entries that are already
written, and the part of the current entry that has been read. -/
abbrev PrefMode (G : Ty) [Group G.Elt] [Finite G.Elt] : Type :=
  PrefPhase × G.Elt × Option (Pfx G)

/-- The machine of group prefix multiplication: it writes, at the delimiter that closes an entry,
a comma and the representation of the product of the entries up to and including that one. -/
noncomputable def prefMach : Mach (PrefMode G) Sym8 where
  step := fun m e c =>
    match m with
    | (.start, h, p) => (.blk, h, p)
    | (.blk, h, p) =>
        if e = 1 ∧ c = Sym8.comma then (.blk, h * pelem G p, some (pfxNil G))
        else if e = 1 ∧ c = Sym8.rbrack then (.done, h, p)
        else (.blk, h, pstep G p c)
    | (.done, h, p) => (.done, h, p)
  out := fun m e c =>
    match m with
    | (.start, _, _) => []
    | (.blk, h, p) =>
        if e = 1 ∧ c = Sym8.comma then Sym8.comma :: G.repr (h * pelem G p)
        else if e = 1 ∧ c = Sym8.rbrack then
          (if pval G p = [] then [] else Sym8.comma :: G.repr (h * pelem G p))
        else []
    | (.done, _, _) => []
  fin := fun _ _ => []

@[simp] lemma prefMach_out_start (h : G.Elt) (p : Option (Pfx G)) (e : ℕ) (c : Sym8) :
    (prefMach G).out (PrefPhase.start, h, p) e c = [] := rfl

@[simp] lemma prefMach_step_start (h : G.Elt) (p : Option (Pfx G)) (e : ℕ) (c : Sym8) :
    (prefMach G).step (PrefPhase.start, h, p) e c = (PrefPhase.blk, h, p) := rfl

@[simp] lemma prefMach_out_blk_comma (h : G.Elt) (p : Option (Pfx G)) :
    (prefMach G).out (PrefPhase.blk, h, p) 1 Sym8.comma
      = Sym8.comma :: G.repr (h * pelem G p) := rfl

@[simp] lemma prefMach_step_blk_comma (h : G.Elt) (p : Option (Pfx G)) :
    (prefMach G).step (PrefPhase.blk, h, p) 1 Sym8.comma
      = (PrefPhase.blk, h * pelem G p, some (pfxNil G)) := rfl

@[simp] lemma prefMach_out_blk_rbrack (h : G.Elt) (p : Option (Pfx G)) :
    (prefMach G).out (PrefPhase.blk, h, p) 1 Sym8.rbrack
      = (if pval G p = [] then [] else Sym8.comma :: G.repr (h * pelem G p)) := rfl

@[simp] lemma prefMach_step_blk_rbrack (h : G.Elt) (p : Option (Pfx G)) :
    (prefMach G).step (PrefPhase.blk, h, p) 1 Sym8.rbrack = (PrefPhase.done, h, p) := rfl

@[simp] lemma prefMach_out_done (h : G.Elt) (p : Option (Pfx G)) (e : ℕ) (c : Sym8) :
    (prefMach G).out (PrefPhase.done, h, p) e c = [] := rfl

@[simp] lemma prefMach_step_done (h : G.Elt) (p : Option (Pfx G)) (e : ℕ) (c : Sym8) :
    (prefMach G).step (PrefPhase.done, h, p) e c = (PrefPhase.done, h, p) := rfl

@[simp] lemma prefMach_fin (m : PrefMode G) (e : ℕ) : (prefMach G).fin m e = [] := rfl

/-! ## The run of the machine -/

/-- The domain of group prefix multiplication. -/
def prefDom : Ty := Ty.list G

omit [Group G.Elt] [Finite G.Elt] in
lemma prefDom_height : (prefDom G).height = 1 + G.height := rfl

/-- The counter at depth `1`, inside the list. -/
def p1 : Fin ((prefDom G).height + 1) := ⟨1, by rw [prefDom_height]; omega⟩

omit [Group G.Elt] [Finite G.Elt] in
@[simp] lemma p1_val : (p1 G).1 = 1 := rfl

omit [Group G.Elt] [Finite G.Elt] in
lemma dstep_p0_lbrack : dstep (0 : Fin ((prefDom G).height + 1)) Sym8.lbrack = p1 G := by
  refine Fin.ext ?_
  rw [dstep_open (by simp) (by simp only [Fin.val_zero]; rw [prefDom_height]; omega)]
  rfl

omit [Group G.Elt] [Finite G.Elt] in
lemma prefCap : (1 : ℤ) + (G.height : ℤ) ≤ ((prefDom G).height : ℤ) := by
  rw [prefDom_height]; push_cast; omega

/-- The mode update while an entry is being read. -/
noncomputable def pupd : PrefMode G → Sym8 → PrefMode G :=
  fun m c => (PrefPhase.blk, m.2.1, pstep G m.2.2 c)

private lemma pref_scan_step :
    ∀ (m : PrefMode G) (e : ℕ) (c : Sym8), (∃ h p, m = (PrefPhase.blk, h, p)) →
      (p1 G).1 ≤ e → (e = (p1 G).1 → transparent c = true) →
      (prefMach G).step m e c = pupd G m c ∧ (prefMach G).out m e c = []
        ∧ (∃ h p, pupd G m c = (PrefPhase.blk, h, p)) := by
  rintro m e c ⟨h, p, rfl⟩ he htr
  simp only [p1_val] at he htr
  have h1 : ¬ (e = 1 ∧ c = Sym8.comma) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  have h2 : ¬ (e = 1 ∧ c = Sym8.rbrack) := by
    rintro ⟨rfl, rfl⟩
    exact absurd (htr rfl) (by simp [transparent])
  refine ⟨?_, ?_, ⟨h, pstep G p c, rfl⟩⟩
  · simp only [prefMach, h1, h2, if_false]
    rfl
  · simp only [prefMach, h1, h2, if_false]

lemma pupd_foldl (h : G.Elt) (p : Option (Pfx G)) (w : List Sym8) :
    w.foldl (pupd G) (PrefPhase.blk, h, p) = (PrefPhase.blk, h, w.foldl (pstep G) p) := by
  induction w generalizing p with
  | nil => rfl
  | cons c w ih => rw [List.foldl_cons, List.foldl_cons, ← ih]; rfl

/-- The prefix products of a list, from a given starting value. -/
def prefixProdFrom (h : G.Elt) (l : List G.Elt) : List G.Elt := (l.scanl (· * ·) h).tail

omit [Finite G.Elt] in
@[simp] lemma prefixProdFrom_nil (h : G.Elt) : prefixProdFrom G h [] = [] := rfl

omit [Finite G.Elt] in
lemma prefixProdFrom_cons (h g : G.Elt) (l : List G.Elt) :
    prefixProdFrom G h (g :: l) = (h * g) :: prefixProdFrom G (h * g) l := by
  cases l with
  | nil => simp [prefixProdFrom]
  | cons g' l' => simp [prefixProdFrom]

/-- **The machine writes the prefix products, each preceded by a comma.** -/
theorem prefMach_body :
    ∀ (l : List G.Elt) (h : G.Elt),
      (prefMach G).runFrom ((prefDom G).height) ((PrefPhase.blk, h, some (pfxNil G)), p1 G)
          (joinSep (l.map G.repr) ++ [Sym8.rbrack])
        = commaBlocks G (prefixProdFrom G h l) := by
  intro l
  induction l with
  | nil =>
      intro h
      rw [List.map_nil, joinSep_nil, List.nil_append, Mach.runFrom_cons]
      simp only [p1_val, prefMach_out_blk_rbrack, prefMach_step_blk_rbrack]
      rw [if_pos (by rfl : pval G (some (pfxNil G)) = [])]
      rw [Mach.runFrom_nil]
      simp only [prefMach_fin, List.nil_append, prefixProdFrom_nil, commaBlocks_nil]
  | cons g l ih =>
      intro h
      rw [joinSep_cons, List.append_assoc]
      rw [(prefMach G).runFrom_repr_scan ((prefDom G).height)
        (fun m => ∃ h' p, m = (PrefPhase.blk, h', p)) (pupd G) _ G g (p1 G) _
        (by simpa using prefCap G) ⟨h, some (pfxNil G), rfl⟩ (pref_scan_step G)]
      rw [pupd_foldl]
      have hp : pval G ((G.repr g).foldl (pstep G) (some (pfxNil G))) = G.repr g := by
        have := pfold G (G.repr g) (pfxNil G) ⟨g, by simp [pfxNil]⟩
        simpa [pfxNil] using this
      have helem : pelem G ((G.repr g).foldl (pstep G) (some (pfxNil G))) = g := by
        rw [pelem, hp, elemOfRepr_repr]
      have hne : ¬ (pval G ((G.repr g).foldl (pstep G) (some (pfxNil G))) = []) := by
        rw [hp]
        obtain ⟨c, w, hcw, -⟩ := repr_eq_cons G g
        rw [hcw]
        simp
      cases l with
      | nil =>
          rw [joinSepTail_nil, List.nil_append, Mach.runFrom_cons]
          simp only [p1_val, prefMach_out_blk_rbrack, prefMach_step_blk_rbrack]
          rw [if_neg hne, helem, Mach.runFrom_nil]
          simp only [prefMach_fin, List.append_nil]
          rw [prefixProdFrom_cons, commaBlocks_cons]
          simp
      | cons g' l' =>
          rw [joinSepTail_cons, List.cons_append, Mach.runFrom_cons]
          simp only [p1_val, prefMach_out_blk_comma, prefMach_step_blk_comma,
            dstep_neutral (by simp : wt Sym8.comma = 0)]
          rw [helem, ih (h * g), prefixProdFrom_cons G h g (g' :: l'), commaBlocks_cons]
          simp

/-- **The run of the machine of group prefix multiplication.** -/
theorem prefMach_run (l : List G.Elt) :
    (prefMach G).run ((prefDom G).height) (PrefPhase.start, 1, some (pfxNil G))
        ((prefDom G).repr l)
      = commaBlocks G (prefixProdFrom G 1 l) := by
  show (prefMach G).runFrom ((prefDom G).height)
      ((PrefPhase.start, 1, some (pfxNil G)), 0)
      (Sym8.lbrack :: (joinSep (l.map G.repr) ++ [Sym8.rbrack])) = _
  rw [Mach.runFrom_cons]
  simp only [prefMach_out_start, prefMach_step_start, dstep_p0_lbrack, List.nil_append]
  rw [prefMach_body]

omit [Finite G.Elt] in
lemma prefixProdFrom_one (l : List G.Elt) : prefixProdFrom G 1 l = prefixProd l := rfl

/-- **Group prefix multiplication is regular under string representation.** -/
theorem isRegularUnderRepr_pref :
    IsRegularUnderRepr (A := Ty.list G) (B := Ty.list G) (fun l => prefixProd l) := by
  refine ⟨fun w => dropFirstMach.run ((prefDom G).height) .first
      ((prefMach G).run ((prefDom G).height) (PrefPhase.start, 1, some (pfxNil G)) w),
    ((prefMach G).isRegularFun_run _ _).comp' (dropFirstMach.isRegularFun_run _ _)
      (fun _ => rfl),
    fun l => ?_⟩
  show dropFirstMach.run ((prefDom G).height) DropMode.first
      ((prefMach G).run ((prefDom G).height) (PrefPhase.start, 1, some (pfxNil G))
        ((prefDom G).repr l)) = (Ty.list G).repr (prefixProd l)
  rw [prefMach_run, dropFirstMach_run, commaBlocks_tail, prefixProdFrom_one]
  rfl

end Pref

end Comb
end Lax709149Proofs.Transducers
