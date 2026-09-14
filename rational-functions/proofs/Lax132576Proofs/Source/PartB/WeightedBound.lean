/-
An *effective* Schützenberger bound for coded weighted automata over `ℚ`
(Section *Rational relations and weighted automata* of *Transducers*, M. Bojańczyk).

`RequestProject/PartB/WeightedZero.lean` proves Schützenberger's criterion: two
functions given by linear representations of dimensions `d₁` and `d₂` are equal
as soon as they agree on all inputs of length at most `d₁ + d₂`
(`linRep_eq_of_short`).  In order to turn this into a decision procedure one
needs the bound as an *explicit arithmetic function of the code*, which is what
this file provides.

The linear representation of a weighted automaton `M` built in
`WeightedNF.lean`/`WeightedLinRep.lean` has one dimension per useful state of
`atom (initCopy M)`, and `WNF.useful_finite` shows that a useful state is either
an initial state or the target of a transition.  Both are read off the
description of `atom (initCopy M)`: its initial states are the copies of the
initial states of `M` together with the extra state `phi`, and the targets of
its transitions are the states `cfg t x` where `t` is a transition of
`initCopy M` (so a lifted or a copied transition of `M`) and `x` is a suffix of
the input string of `t`.  Listing these states gives the bound

  `1 + (number of initial states) + Σ over the transitions of 2 * (|input| + 1)`,

which for a code is a primitive recursive function of the code
(`wcodeBound`).  The result is `Transducers.effectiveWeightedBound`, which
discharges the hypothesis `EffectiveWeightedBound` of
`RequestProject/PartB/Effective.lean`.
-/
import Lax132576Proofs.Source.PartB.Effective
import Lax132576Proofs.Source.PartB.WeightedZero
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

namespace WBound

open LabAut WNF

variable {B S : Type}

/-! ## Counting a set through a list covering it -/

/-- A set whose elements all occur in a list has at most as many elements as the
list has entries. -/
lemma ncard_le_of_list {α : Type} {T : Set α} {L : List α} (h : ∀ x ∈ T, x ∈ L) :
    T.ncard ≤ L.length := by
  classical
  have hsub : T ⊆ (L.toFinset : Set α) := fun x hx => by simpa using h x hx
  calc T.ncard ≤ (L.toFinset : Set α).ncard := Set.ncard_le_ncard hsub (L.toFinset.finite_toSet)
    _ = L.toFinset.card := Set.ncard_coe_finset _
    _ ≤ L.length := List.toFinset_card_le _

/-! ## A list covering the useful states of the normalised automaton -/

/-- A list containing every useful state of `atom (initCopy M)`, computed from a
list `Iₗ` covering the initial states and a list `Dₗ` covering the transitions
of `M`. -/
def coverList {Q : Type} (Iₗ : List Q) (Dₗ : List (Q × List B × S × Q)) :
    List (ASt (ISt Q) B S) :=
  (Sum.inl (phi : ISt Q)) :: (Iₗ.map (fun q => Sum.inl (cop q)) ++
    Dₗ.flatMap (fun t => t.2.1.tails.flatMap (fun x => [cfg (liftTr t) x, cfg (copTr t) x])))

lemma coverList_length {Q : Type} (Iₗ : List Q) (Dₗ : List (Q × List B × S × Q)) :
    (coverList Iₗ Dₗ).length
      = 1 + Iₗ.length + (Dₗ.map (fun t => 2 * (t.2.1.length + 1))).sum := by
  have hin : ∀ t : Q × List B × S × Q,
      (t.2.1.tails.flatMap (fun x => [cfg (liftTr t) x, cfg (copTr t) x])).length
        = 2 * (t.2.1.length + 1) := by
    intro t
    rw [List.length_flatMap]
    simp [List.map_const', List.sum_replicate, List.length_tails, Nat.mul_comm]
  have hflat : (Dₗ.flatMap
      (fun t => t.2.1.tails.flatMap (fun x => [cfg (liftTr t) x, cfg (copTr t) x]))).length
      = (Dₗ.map (fun t => 2 * (t.2.1.length + 1))).sum := by
    rw [List.length_flatMap]
    exact congrArg List.sum (List.map_congr_left (fun t _ => hin t))
  rw [coverList, List.length_cons, List.length_append, List.length_map, hflat]
  omega

variable [Semiring S]

/-- Every useful state of `atom (initCopy M)` occurs in `coverList`. -/
lemma useful_mem_coverList {Q : Type} (M : LabAut B S Q)
    {Iₗ : List Q} (hI : ∀ q ∈ M.init, q ∈ Iₗ)
    {Dₗ : List (Q × List B × S × Q)} (hD : ∀ t ∈ M.δ, t ∈ Dₗ)
    {q : ASt (ISt Q) B S} (hq : Useful (atom (initCopy M)) q) :
    q ∈ coverList Iₗ Dₗ := by
  -- the states of the flatMap part of `coverList`
  have hcfg : ∀ (t : Q × List B × S × Q), t ∈ M.δ → ∀ x : List B, x <:+ t.2.1 →
      (cfg (liftTr t) x ∈ coverList Iₗ Dₗ ∧ cfg (copTr t) x ∈ coverList Iₗ Dₗ) := by
    intro t ht x hx
    have hx' : x ∈ t.2.1.tails := (List.mem_tails x t.2.1).2 hx
    constructor <;>
      exact List.mem_cons_of_mem _ (List.mem_append_right _
        (List.mem_flatMap.2 ⟨t, hD t ht, List.mem_flatMap.2 ⟨x, hx', by simp⟩⟩))
  -- an initial state of `atom (initCopy M)` occurs in `coverList`
  have hinit : ∀ x : ASt (ISt Q) B S, x ∈ (atom (initCopy M)).init → x ∈ coverList Iₗ Dₗ := by
    rintro x ⟨y, hy, rfl⟩
    rcases hy with ⟨q', hq', rfl⟩ | ⟨rfl, -⟩
    · exact List.mem_cons_of_mem _ (List.mem_append_left _
        (List.mem_map.2 ⟨q', hI q' hq', rfl⟩))
    · exact List.mem_cons_self
  obtain ⟨q₀, hq₀, p, -, ts₁, ts₂, hts₁, -⟩ := hq
  rcases WNF.path_target_mem (atom (initCopy M)) hts₁ with rfl | ⟨tr, htr, rfl⟩
  · exact hinit _ hq₀
  -- otherwise the state is the target of a transition of the atomised automaton
  have key : ∀ (t : ISt Q × List B × S × ISt Q), t ∈ (initCopy M).δ → ∀ x : List B,
      x <:+ t.2.1 → cfg t x ∈ coverList Iₗ Dₗ := by
    rintro t (⟨t₀, ht₀, rfl⟩ | ⟨t₀, ⟨ht₀, -⟩, rfl⟩) x hx
    · exact (hcfg t₀ ht₀ x hx).1
    · exact (hcfg t₀ ht₀ x hx).2
  rcases htr with ⟨t, ht, rfl⟩ | ⟨t, ht, b, y, hsuf, rfl⟩
  · exact key t ht t.2.1 (List.suffix_refl _)
  · exact key t ht y ((List.suffix_cons b y).trans hsuf)

/-- The number of useful states of `atom (initCopy M)` is bounded by an explicit
function of a list of initial states and a list of transitions of `M`. -/
lemma card_useful_le {Q : Type} (M : LabAut B S Q)
    {Iₗ : List Q} (hI : ∀ q ∈ M.init, q ∈ Iₗ)
    {Dₗ : List (Q × List B × S × Q)} (hD : ∀ t ∈ M.δ, t ∈ Dₗ) :
    Nat.card {q : ASt (ISt Q) B S // Useful (atom (initCopy M)) q}
      ≤ 1 + Iₗ.length + (Dₗ.map (fun t => 2 * (t.2.1.length + 1))).sum := by
  have h1 : Nat.card {q : ASt (ISt Q) B S // Useful (atom (initCopy M)) q}
      = {q : ASt (ISt Q) B S | Useful (atom (initCopy M)) q}.ncard :=
    Nat.card_coe_set_eq _
  rw [h1, ← coverList_length (S := S) Iₗ Dₗ]
  exact ncard_le_of_list (fun x hx => useful_mem_coverList M hI hD hx)

/-! ## A linear representation of explicitly bounded dimension -/

/-- Every weighted automaton with finitely many initial states has a linear
representation whose dimension is bounded by an explicit function of a list of
its initial states and a list of its transitions.  This is `WNF.exists_linRep`
with the dimension made explicit. -/
theorem exists_linRep_bounded {Q : Type} (M : LabAut B S Q)
    (hfin : M.FinitelyManyRuns) (hinit : M.init.Finite)
    {Iₗ : List Q} (hI : ∀ q ∈ M.init, q ∈ Iₗ)
    {Dₗ : List (Q × List B × S × Q)} (hD : ∀ t ∈ M.δ, t ∈ Dₗ) :
    ∃ (Q' : Type) (_ : Fintype Q') (_ : DecidableEq Q') (I : Finset Q')
      (m : B → Matrix Q' Q' S) (bta : Q' → S),
      Fintype.card Q' ≤ 1 + Iₗ.length + (Dₗ.map (fun t => 2 * (t.2.1.length + 1))).sum ∧
      ∀ v : List B, M.wEval v = ∑ q ∈ I, ∑ q' : Q', ((v.map m).prod) q q' * bta q' := by
  classical
  -- make the empty run unique
  set M₁ := initCopy M with hM₁
  have hfin₁ : M₁.FinitelyManyRuns := finitelyManyRuns_initCopy M hfin
  have hue₁ : UniqueEmptyRun M₁ := uniqueEmptyRun_initCopy M
  have hinit₁ : M₁.init.Finite := by
    refine (hinit.image cop).union ((Set.finite_singleton (phi : ISt Q)).subset ?_)
    rintro x ⟨rfl, -⟩
    exact rfl
  -- atomise
  set M₂ := atom M₁ with hM₂
  have hfin₂ : M₂.FinitelyManyRuns := finitelyManyRuns_atom M₁ hfin₁
  have hue₂ : UniqueEmptyRun M₂ := uniqueEmptyRun_atom M₁ hue₁
  have hat₂ : Atomic M₂ := atomic_atom M₁
  have hinit₂ : M₂.init.Finite := init_atom_finite M₁ hinit₁
  -- restrict to the useful states
  set M₃ := restrict M₂ with hM₃
  have hfin₃ : M₃.FinitelyManyRuns := finitelyManyRuns_restrict M₂ hfin₂
  have hue₃ : UniqueEmptyRun M₃ := uniqueEmptyRun_restrict M₂ hue₂
  have hat₃ : Atomic M₃ := atomic_restrict M₂ hat₂
  have hall₃ : AllUseful M₃ := allUseful_restrict M₂
  have hinit₃ : M₃.init.Finite := init_restrict_finite M₂ hinit₂
  have hQ₃ : Finite {q // Useful M₂ q} := instFiniteUseful M₂ hinit₂
  letI : Fintype {q // Useful M₂ q} := Fintype.ofFinite _
  refine ⟨{q // Useful M₂ q}, inferInstance, inferInstance, hinit₃.toFinset, mu M₃,
    beta M₃, ?_, fun v => ?_⟩
  · rw [Fintype.card_eq_nat_card]
    exact card_useful_le M hI hD
  · have hcoe : ∑ᶠ q ∈ M₃.init, (∑ q' : {q // Useful M₂ q},
        muStr M₃ v q q' * beta M₃ q')
        = ∑ q ∈ hinit₃.toFinset, ∑ q' : {q // Useful M₂ q},
          muStr M₃ v q q' * beta M₃ q' := by
      rw [← finsum_mem_coe_finset (fun q => ∑ q' : {q // Useful M₂ q},
        muStr M₃ v q q' * beta M₃ q') hinit₃.toFinset, hinit₃.coe_toFinset]
    have hval : M₃.wEval v = M.wEval v := by
      rw [wEval_restrict M₂ v, wEval_atom M₁ v, wEval_initCopy M v]
    rw [← hval, wEval_eq_linRep M₃ hue₃ (paths_finite M₃ hall₃ hfin₃) hfin₃ hat₃ v,
      hcoe]
    rfl

end WBound

/-! ## The bound of a code -/

/-- The Schützenberger bound computed from the code of a weighted automaton over
`ℚ`: one more than the number of its initial states, plus twice the sum over its
transitions of the length of the input string plus one. -/
def wcodeBound (c : WCode) : ℕ :=
  1 + c.2.1.length + (c.1.map (fun t => 2 * (t.2.1.length + 1))).sum

/-- **The effective Schützenberger criterion for codes.**  Two valid coded
weighted automata over `ℚ` that agree on all strings of length at most the sum
of their bounds compute the same function. -/
theorem wcodeEval_eq_of_short {c₁ c₂ : WCode} (h₁ : WCodeValid c₁) (h₂ : WCodeValid c₂)
    (hagree : ∀ v : List ℕ, v.length ≤ wcodeBound c₁ + wcodeBound c₂ →
      wcodeEval c₁ v = wcodeEval c₂ v) :
    wcodeEval c₁ = wcodeEval c₂ := by
  classical
  -- the data read off a code
  have hinit : ∀ c : WCode, (wcodeAut c).init.Finite := by
    intro c
    exact List.finite_toSet c.2.1
  have hI : ∀ (c : WCode), ∀ q ∈ (wcodeAut c).init, q ∈ c.2.1 := fun _ _ hq => hq
  have hD : ∀ (c : WCode), ∀ t ∈ (wcodeAut c).δ,
      t ∈ c.1.map (fun s => (s.1, s.2.1, ((s.2.2.1.1 : ℚ) / (s.2.2.1.2 : ℚ)), s.2.2.2)) := by
    rintro c t ⟨s, hs, rfl⟩
    exact List.mem_map.2 ⟨s, hs, rfl⟩
  have hsum : ∀ c : WCode,
      ((c.1.map (fun s => ((s.1, s.2.1, ((s.2.2.1.1 : ℚ) / (s.2.2.1.2 : ℚ)), s.2.2.2) :
        ℕ × List ℕ × ℚ × ℕ))).map (fun t => 2 * (t.2.1.length + 1))).sum
        = (c.1.map (fun t => 2 * (t.2.1.length + 1))).sum := by
    intro c
    simp [List.map_map, Function.comp_def]
  obtain ⟨Q₁, hfQ₁, hdQ₁, I₁, m₁, bta₁, hcard₁, hrep₁⟩ :=
    WBound.exists_linRep_bounded (wcodeAut c₁) h₁ (hinit c₁) (hI c₁) (hD c₁)
  obtain ⟨Q₂, hfQ₂, hdQ₂, I₂, m₂, bta₂, hcard₂, hrep₂⟩ :=
    WBound.exists_linRep_bounded (wcodeAut c₂) h₂ (hinit c₂) (hI c₂) (hD c₂)
  rw [hsum c₁] at hcard₁
  rw [hsum c₂] at hcard₂
  refine linRep_eq_of_short (h₁ := wcodeEval c₁) (h₂ := wcodeEval c₂)
    I₁ m₁ bta₁ I₂ m₂ bta₂ hrep₁ hrep₂ (fun v hv => hagree v ?_)
  have : Fintype.card Q₁ + Fintype.card Q₂ ≤ wcodeBound c₁ + wcodeBound c₂ := by
    have e₁ : wcodeBound c₁ = 1 + c₁.2.1.length + (c₁.1.map (fun t => 2 * (t.2.1.length + 1))).sum :=
      rfl
    have e₂ : wcodeBound c₂ = 1 + c₂.2.1.length + (c₂.1.map (fun t => 2 * (t.2.1.length + 1))).sum :=
      rfl
    omega
  omega

/-- Summing a list of natural numbers is primitive recursive.  (Mathlib's
`Primrec` API has no combinator for folding over a list, so the sum is written
as an explicit `List.foldr`.) -/
lemma primrec_listSum : Primrec (fun l : List ℕ => l.sum) := by
  have h : Primrec (fun l : List ℕ =>
      l.foldr (fun b s => (fun (_ : List ℕ) (p : ℕ × ℕ) => p.1 + p.2) l (b, s)) 0) := by
    refine Primrec.list_foldr (f := fun l : List ℕ => l) (g := fun _ => (0 : ℕ))
      (h := fun (_ : List ℕ) (p : ℕ × ℕ) => p.1 + p.2) Primrec.id (Primrec.const 0) ?_
    exact Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  refine h.of_eq (fun l => ?_)
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- The bound is a primitive recursive function of the code. -/
lemma primrec_wcodeBound : Primrec wcodeBound := by
  have hlen : Primrec (fun c : WCode => c.2.1.length) :=
    Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)
  have hmap : Primrec (fun c : WCode => c.1.map (fun t => 2 * (t.2.1.length + 1))) := by
    refine Primrec.list_map Primrec.fst ?_
    show Primrec fun z : WCode × (ℕ × List ℕ × (ℤ × ℕ) × ℕ) => 2 * (z.2.2.1.length + 1)
    exact Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec.succ.comp (Primrec.list_length.comp (Primrec.fst.comp (Primrec.snd.comp
        Primrec.snd))))
  have hsum : Primrec (fun c : WCode => (c.1.map (fun t => 2 * (t.2.1.length + 1))).sum) :=
    primrec_listSum.comp hmap
  exact (Primrec.nat_add.comp
    (Primrec.nat_add.comp (Primrec.const 1) hlen) hsum).of_eq (fun c => rfl)

/-- **The effective Schützenberger bound stated in `RequestProject/PartB/Effective.lean`
is a theorem.**  A Schützenberger bound can be computed from the two codes. -/
theorem effectiveWeightedBound : EffectiveWeightedBound := by
  have hprim : Primrec₂ (fun c₁ c₂ : WCode => wcodeBound c₁ + wcodeBound c₂) :=
    Primrec.nat_add.comp (primrec_wcodeBound.comp Primrec.fst)
      (primrec_wcodeBound.comp Primrec.snd)
  exact ⟨fun c₁ c₂ => wcodeBound c₁ + wcodeBound c₂, hprim.to_comp,
    fun _ _ h₁ h₂ hagree => wcodeEval_eq_of_short h₁ h₂ hagree⟩

end Lax132576Proofs.Transducers
