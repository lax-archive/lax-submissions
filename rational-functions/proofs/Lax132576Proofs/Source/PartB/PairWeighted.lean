/-
The weighted automaton over `ℚ` used in the proof of Theorem `thm:equivalence-rational-functions` of
*Transducers* (M. Bojańczyk): the product of two letter-atomic codes, weighted
by the numerical encoding `iota` of the output of the first one.

Given two codes `M` and `N` in the letter-atomic normal form of
`RequestProject/PartB/CodeMerge.lean`, the weighted automaton `pairW K M N` has
states `(p, q, i)` with `p` a state of `M`, `q` a state of `N` and `i ∈ {0,1}`,
and the transitions

  `(p, q, 0) --a / K ^ |x|--> (p', q', 0)`,
  `(p, q, 0) --a / iota K x--> (p', q', 1)`,
  `(p, q, 1) --a / 1--> (p', q', 1)`,

one for each pair of transitions `p --a/x--> p'` of `M` and `q --a/y--> q'` of
`N` reading the same letter `a`.  Its runs over a string `w` are therefore the
triples consisting of a run of `M` over `w`, a run of `N` over `w` and a
position at which the bit switches from `0` to `1`, and the weight of such a
triple is `K ^ |x₁ ⋯ x_{i-1}| * iota K xᵢ`.  Summing over the switching position
and using `iota_append`, the value of the automaton on `w` is

  `∑_{ρ run of M} iota K (output of ρ) * (number of runs of N)`,

which is the content of `pairW_eval` in
`RequestProject/PartB/PairWeightedEval.lean`: when all the runs of `M` over `w`
produce the same output `v` -- which is the case when the coded relation is a
function -- the value is `(number of runs of M) * (number of runs of N) *
iota K v`.  The symmetric expression obtained by exchanging `M` and `N` has the
same two factors in front, so the two weighted automata are equivalent exactly
when the two coded functions are equal.

This file sets up the construction and its basic combinatorics; the evaluation
is in `RequestProject/PartB/PairWeightedEval.lean`.
-/
import Lax132576Proofs.Source.PartB.CodeMerge
import Lax132576Proofs.Source.PartB.Iota
import Lax132576Proofs.Source.PartB.WCodes
import Lax132576Proofs.Source.PartB.RunList
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers
namespace PairWeighted

open LabAut CodeMerge Iota RunList

/-! ## The states of the product -/

/-- The state `(p, q, i)` of the product automaton, coded by a natural number.
-/
def st (p q b : ℕ) : ℕ := 2 * Nat.pair p q + b

lemma st_inj {p q b p' q' b' : ℕ} (hb : b < 2) (hb' : b' < 2)
    (h : st p q b = st p' q' b') : p = p' ∧ q = q' ∧ b = b' := by
  have h' : 2 * Nat.pair p q + b = 2 * Nat.pair p' q' + b' := h
  have h1 : Nat.pair p q = Nat.pair p' q' := by omega
  have h2 : b = b' := by omega
  obtain ⟨hp, hq⟩ := Nat.pair_eq_pair.1 h1
  exact ⟨hp, hq, h2⟩

lemma st_ne {p q p' q' : ℕ} {b b' : ℕ} (hb : b < 2) (hb' : b' < 2) (hne : b ≠ b') :
    st p q b ≠ st p' q' b' := fun h => hne (st_inj hb hb' h).2.2

/-! ## The transitions of the product -/

/-- The pair of bits (source, target) of the `i`-th kind of transition. -/
def bits (i : ℕ) : ℕ × ℕ := if i = 0 then (0, 0) else if i = 1 then (0, 1) else (1, 1)

lemma bits_fst_lt (i : ℕ) : (bits i).1 < 2 := by unfold bits; split_ifs <;> simp
lemma bits_snd_lt (i : ℕ) : (bits i).2 < 2 := by unfold bits; split_ifs <;> simp

lemma bits_injOn {i i' : ℕ} (hi : i ∈ [0, 1, 2]) (hi' : i' ∈ [0, 1, 2])
    (h : bits i = bits i') : i = i' := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hi'
  rcases hi with rfl | rfl | rfl <;> rcases hi' with rfl | rfl | rfl <;>
    first
      | rfl
      | (exfalso; simp [bits] at h)

/-- The `i`-th transition of the product attached to a pair of transitions,
with rational weights. -/
def sel (K : ℕ) (z : CodeMerge.Tr × CodeMerge.Tr) (i : ℕ) : RunList.T ℚ :=
  (st z.1.1 z.2.1 (bits i).1, z.1.2.1,
    (if i = 0 then ((K ^ z.1.2.2.1.length : ℕ) : ℚ)
      else if i = 1 then ((iota K z.1.2.2.1 : ℕ) : ℚ) else (1 : ℚ)),
    st z.1.2.2.2 z.2.2.2.2 (bits i).2)

/-- The `i`-th transition of the product attached to a pair of transitions, as
it is stored in a code (with weights written as fractions of integers). -/
def selZ (K : ℕ) (z : CodeMerge.Tr × CodeMerge.Tr) (i : ℕ) : ℕ × List ℕ × (ℤ × ℕ) × ℕ :=
  (st z.1.1 z.2.1 (bits i).1, z.1.2.1,
    ((if i = 0 then ((K ^ z.1.2.2.1.length : ℕ) : ℤ)
      else if i = 1 then ((iota K z.1.2.2.1 : ℕ) : ℤ) else (1 : ℤ)), 1),
    st z.1.2.2.2 z.2.2.2.2 (bits i).2)

/-- The pairs of transitions reading the same letter, each with the index of one
of the three kinds of product transition. -/
def pairBase (M N : RelCode) : List ((CodeMerge.Tr × CodeMerge.Tr) × ℕ) :=
  ((M.1 ×ˢ N.1).filter (fun z => decide (z.1.2.1 = z.2.2.1))) ×ˢ [0, 1, 2]

lemma mem_pairBase {M N : RelCode} {s t : CodeMerge.Tr} {i : ℕ} :
    ((s, t), i) ∈ pairBase M N ↔
      (s ∈ M.1 ∧ t ∈ N.1 ∧ s.2.1 = t.2.1) ∧ (i = 0 ∨ i = 1 ∨ i = 2) := by
  simp [pairBase, List.mem_product, List.mem_filter, and_assoc]

/-- The transitions of the product automaton. -/
def pairTrans (K : ℕ) (M N : RelCode) : List (ℕ × List ℕ × (ℤ × ℕ) × ℕ) :=
  (pairBase M N).map (fun zi => selZ K zi.1 zi.2)

/-- The initial states of the product automaton. -/
def pairInit (M N : RelCode) : List ℕ := (M.2.1 ×ˢ N.2.1).map (fun z => st z.1 z.2 0)

/-- The final states of the product automaton. -/
def pairFin (M N : RelCode) : List ℕ := (M.2.2 ×ˢ N.2.2).map (fun z => st z.1 z.2 1)

/-- The product automaton of two letter-atomic codes, weighted by the numerical
encoding of the output of the first one. -/
def pairW (K : ℕ) (M N : RelCode) : WCode :=
  (pairTrans K M N, pairInit M N, pairFin M N)

/-- The transitions of the product automaton, with their rational weights. -/
def qTrans (K : ℕ) (M N : RelCode) : List (RunList.T ℚ) :=
  (pairBase M N).map (fun zi => sel K zi.1 zi.2)

lemma sel_eq_selZ (K : ℕ) (z : CodeMerge.Tr × CodeMerge.Tr) (i : ℕ) :
    sel K z i = ((selZ K z i).1, (selZ K z i).2.1,
      (((selZ K z i).2.2.1.1 : ℚ) / ((selZ K z i).2.2.1.2 : ℚ)), (selZ K z i).2.2.2) := by
  simp only [selZ, sel]
  split_ifs <;> simp

/-- The transitions of the automaton described by the code are exactly the
members of `qTrans`. -/
lemma delta_pairW (K : ℕ) (M N : RelCode) :
    ∀ t, t ∈ (wcodeAut (pairW K M N)).δ ↔ t ∈ qTrans K M N := by
  intro t
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨zi, hzi, rfl⟩ := List.mem_map.1 (show s ∈ pairTrans K M N from hs)
    exact List.mem_map.2 ⟨zi, hzi, (sel_eq_selZ K zi.1 zi.2)⟩
  · intro ht
    obtain ⟨zi, hzi, rfl⟩ := List.mem_map.1 ht
    exact ⟨selZ K zi.1 zi.2, List.mem_map.2 ⟨zi, hzi, rfl⟩, sel_eq_selZ K zi.1 zi.2⟩

lemma init_pairW {K : ℕ} (M N : RelCode) :
    ∀ q, q ∈ (wcodeAut (pairW K M N)).init ↔ q ∈ pairInit M N := fun _ => Iff.rfl

lemma final_pairW {K : ℕ} (M N : RelCode) :
    ∀ p, p ∈ (wcodeAut (pairW K M N)).final ↔ p ∈ pairFin M N := fun _ => Iff.rfl

/-! ## Membership in the state lists -/

lemma mem_pairInit {M N : RelCode} {p q : ℕ} :
    st p q 0 ∈ pairInit M N ↔ p ∈ M.2.1 ∧ q ∈ N.2.1 := by
  simp only [pairInit, List.mem_map]
  constructor
  · rintro ⟨⟨p', q'⟩, hz, hz'⟩
    obtain ⟨h1, h2, -⟩ := st_inj (by norm_num) (by norm_num) hz'.symm
    exact ⟨h1 ▸ (List.mem_product.1 hz).1, h2 ▸ (List.mem_product.1 hz).2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(p, q), List.mem_product.2 ⟨h1, h2⟩, rfl⟩

lemma mem_pairFin {M N : RelCode} {p q : ℕ} :
    st p q 1 ∈ pairFin M N ↔ p ∈ M.2.2 ∧ q ∈ N.2.2 := by
  simp only [pairFin, List.mem_map]
  constructor
  · rintro ⟨⟨p', q'⟩, hz, hz'⟩
    obtain ⟨h1, h2, -⟩ := st_inj (by norm_num) (by norm_num) hz'.symm
    exact ⟨h1 ▸ (List.mem_product.1 hz).1, h2 ▸ (List.mem_product.1 hz).2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(p, q), List.mem_product.2 ⟨h1, h2⟩, rfl⟩

lemma not_mem_pairFin_zero {M N : RelCode} {p q : ℕ} : st p q 0 ∉ pairFin M N := by
  simp only [pairFin, List.mem_map, not_exists]
  rintro ⟨p', q'⟩ ⟨-, hz⟩
  exact absurd hz.symm (st_ne (by norm_num) (by norm_num) (by norm_num))

/-! ## The product automaton is letter-atomic, with pairwise distinct
transitions -/

lemma qTrans_atomic {K : ℕ} {M N : RelCode} (hMa : LetterAtomic M) :
    RunList.Atomic (qTrans K M N) := by
  rintro u hu
  obtain ⟨⟨⟨s, t⟩, i⟩, hzi, rfl⟩ := List.mem_map.1 hu
  obtain ⟨⟨hs, -, -⟩, -⟩ := mem_pairBase.1 hzi
  obtain ⟨a, ha⟩ := hMa s hs
  exact ⟨a, by simpa [sel] using ha⟩

lemma pairBase_nodup {M N : RelCode} (hM : M.1.Nodup) (hN : N.1.Nodup) :
    (pairBase M N).Nodup :=
  List.Nodup.product ((hM.product hN).filter _) (by decide)

lemma sel_injOn {K : ℕ} {M N : RelCode} (hMc : Canonical M) (hNc : Canonical N) :
    ∀ zi ∈ pairBase M N, ∀ zi' ∈ pairBase M N,
      sel K zi.1 zi.2 = sel K zi'.1 zi'.2 → zi = zi' := by
  rintro ⟨⟨s, t⟩, i⟩ hzi ⟨⟨s', t'⟩, i'⟩ hzi' heq
  obtain ⟨⟨hs, ht, hst⟩, hi⟩ := mem_pairBase.1 hzi
  obtain ⟨⟨hs', ht', hst'⟩, hi'⟩ := mem_pairBase.1 hzi'
  simp only [sel, Prod.mk.injEq] at heq
  obtain ⟨hsrc, hin, -, htgt⟩ := heq
  obtain ⟨h1, h2, hb1⟩ := st_inj (bits_fst_lt i) (bits_fst_lt i') hsrc
  obtain ⟨h3, h4, hb2⟩ := st_inj (bits_snd_lt i) (bits_snd_lt i') htgt
  have hii : i = i' := bits_injOn (by simpa using hi) (by simpa using hi') (Prod.ext hb1 hb2)
  have hss : s = s' := hMc s hs s' hs' (by simp only [key, Prod.mk.injEq]; exact ⟨h1, hin, h3⟩)
  have htt : t = t' := by
    refine hNc t ht t' ht' ?_
    simp only [key, Prod.mk.injEq]
    exact ⟨h2, by rw [← hst, ← hst', hin], h4⟩
  simp [hss, htt, hii]

lemma qTrans_nodup {K : ℕ} {M N : RelCode} (hM : M.1.Nodup) (hN : N.1.Nodup)
    (hMc : Canonical M) (hNc : Canonical N) : (qTrans K M N).Nodup :=
  List.Nodup.map_on (sel_injOn hMc hNc) (pairBase_nodup hM hN)

lemma pairInit_nodup {M N : RelCode} (hM : M.2.1.Nodup) (hN : N.2.1.Nodup) :
    (pairInit M N).Nodup := by
  refine List.Nodup.map_on ?_ (hM.product hN)
  rintro ⟨p, q⟩ - ⟨p', q'⟩ - h
  obtain ⟨h1, h2, -⟩ := st_inj (by norm_num) (by norm_num) h
  exact Prod.ext h1 h2

/-- The product automaton is a genuine weighted automaton: every string has
finitely many accepting runs. -/
theorem pairW_valid (K : ℕ) (M N : RelCode) (hMa : LetterAtomic M) :
    WCodeValid (pairW K M N) := fun w =>
  RunList.finite_acceptingOn (delta_pairW K M N) (init_pairW M N) (final_pairW M N)
    (qTrans_atomic hMa) w

/-! ## Counting the runs of a code -/

/-- The number of accepting runs of a code from a given state. -/
def nRun (M : RelCode) (p : ℕ) (w : List ℕ) : ℕ :=
  (RunList.accRuns M.1 M.2.2 p w).length

/-- The sum, over the accepting runs of a code from a given state, of the number
representing the output of the run. -/
def iRun (K : ℕ) (M : RelCode) (p : ℕ) (w : List ℕ) : ℕ :=
  ((RunList.accRuns M.1 M.2.2 p w).map (fun ρ => iota K (NFAO.outputOf ρ))).sum

/-- The total number of accepting runs of a code over a string. -/
def nAll (M : RelCode) (w : List ℕ) : ℕ := (M.2.1.map (fun p => nRun M p w)).sum

/-- The sum, over all the accepting runs of a code over a string, of the number
representing the output of the run. -/
def iAll (K : ℕ) (M : RelCode) (w : List ℕ) : ℕ :=
  (M.2.1.map (fun p => iRun K M p w)).sum

lemma nRun_nil (M : RelCode) (p : ℕ) : nRun M p [] = if p ∈ M.2.2 then 1 else 0 := by
  rw [nRun, RunList.accRuns_nil']
  by_cases h : p ∈ M.2.2 <;> simp [h]

lemma iRun_nil (K : ℕ) (M : RelCode) (p : ℕ) : iRun K M p [] = 0 := by
  rw [iRun, RunList.accRuns_nil']
  by_cases h : p ∈ M.2.2 <;> simp [h, NFAO.outputOf, LabAut.labelsOf]

lemma sum_map_affine {α : Type} (l : List α) (c d : ℕ) (g : α → ℕ) :
    (l.map (fun x => c + d * g x)).sum = l.length * c + d * (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
      simp only [List.map_cons, List.sum_cons, ih, List.length_cons]
      ring

lemma nRun_cons (M : RelCode) (p a : ℕ) (w : List ℕ) :
    nRun M p (a :: w) =
      (M.1.map (fun s => if s.1 = p ∧ s.2.1 = [a] then nRun M s.2.2.2 w else 0)).sum := by
  rw [nRun, ← RunList.length_map_one, RunList.sum_map_accRuns_cons]
  refine congrArg List.sum (List.map_congr_left (fun s _ => ?_))
  by_cases hc : s.1 = p ∧ s.2.1 = [a]
  · rw [if_pos hc, if_pos hc, nRun, RunList.length_map_one]
  · rw [if_neg hc, if_neg hc]

lemma iRun_cons (K : ℕ) (M : RelCode) (p a : ℕ) (w : List ℕ) :
    iRun K M p (a :: w) =
      (M.1.map (fun s => if s.1 = p ∧ s.2.1 = [a] then
        nRun M s.2.2.2 w * iota K s.2.2.1 + K ^ s.2.2.1.length * iRun K M s.2.2.2 w
        else 0)).sum := by
  rw [iRun, RunList.sum_map_accRuns_cons]
  refine congrArg List.sum (List.map_congr_left (fun s _ => ?_))
  by_cases hc : s.1 = p ∧ s.2.1 = [a]
  · rw [if_pos hc, if_pos hc]
    have hout : ∀ ρ : List CodeMerge.Tr,
        iota K (NFAO.outputOf (s :: ρ)) = iota K s.2.2.1 + K ^ s.2.2.1.length *
          iota K (NFAO.outputOf ρ) := by
      intro ρ
      rw [NFAO.outputOf_cons, iota_append]
    rw [List.map_congr_left (fun ρ _ => hout ρ), sum_map_affine]
    rfl
  · rw [if_neg hc, if_neg hc]

/-! ## The accepting runs of a code and the relation that it describes -/

lemma codeRel_of_mem_accRuns {M : RelCode} (hMa : LetterAtomic M) {p : ℕ} (hp : p ∈ M.2.1)
    {w : List ℕ} {ρ : List CodeMerge.Tr} (h : ρ ∈ RunList.accRuns M.1 M.2.2 p w) :
    codeRel M w (NFAO.outputOf ρ) := by
  obtain ⟨hruns, hfin⟩ := RunList.mem_accRuns.1 h
  obtain ⟨hpath, hin⟩ :=
    (RunList.mem_runs (M := codeAut M) (fun _ => Iff.rfl) hMa).1 hruns
  rw [codeRel, NFAO.rel_iff_relFrom]
  exact ⟨p, hp, RunList.tgt p ρ, hfin, ρ, hpath, hin, rfl⟩

lemma exists_mem_accRuns {M : RelCode} (hMa : LetterAtomic M) {w v : List ℕ}
    (h : codeRel M w v) : ∃ p ∈ M.2.1, ∃ ρ ∈ RunList.accRuns M.1 M.2.2 p w,
      NFAO.outputOf ρ = v := by
  rw [codeRel, NFAO.rel_iff_relFrom] at h
  obtain ⟨p, hp, r, hr, ρ, hpath, hin, hout⟩ := h
  refine ⟨p, hp, ρ, RunList.mem_accRuns.2 ⟨?_, ?_⟩, hout⟩
  · exact (RunList.mem_runs (M := codeAut M) (fun _ => Iff.rfl) hMa).2
      ⟨(RunList.tgt_eq_of_path hpath) ▸ hpath, hin⟩
  · exact (RunList.tgt_eq_of_path hpath) ▸ hr

lemma nAll_pos {M : RelCode} (hMa : LetterAtomic M) {w v : List ℕ} (h : codeRel M w v) :
    0 < nAll M w := by
  obtain ⟨p, hp, ρ, hρ, -⟩ := exists_mem_accRuns hMa h
  have hlen : 0 < nRun M p w := by
    rw [nRun, List.length_pos_iff_ne_nil]
    intro hnil
    rw [hnil] at hρ
    exact absurd hρ (by simp)
  rw [nAll]
  have hmem : nRun M p w ∈ M.2.1.map (fun p => nRun M p w) := List.mem_map_of_mem hp
  exact lt_of_lt_of_le hlen (List.single_le_sum (fun _ _ => Nat.zero_le _) _ hmem)

lemma nAll_eq_zero {M : RelCode} (hMa : LetterAtomic M) {w : List ℕ}
    (h : ∀ v, ¬ codeRel M w v) : nAll M w = 0 := by
  rw [nAll]
  refine List.sum_eq_zero (fun x hx => ?_)
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  rw [nRun, List.length_eq_zero_iff]
  by_contra hne
  obtain ⟨ρ, hρ⟩ := List.exists_mem_of_ne_nil _ hne
  exact h _ (codeRel_of_mem_accRuns hMa hp hρ)

lemma sum_map_const {α : Type} (l : List α) (c : ℕ) :
    (l.map (fun _ => c)).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih, List.length_cons]; ring

lemma sum_map_mul_const {α : Type} (l : List α) (g : α → ℕ) (c : ℕ) :
    (l.map (fun x => g x * c)).sum = (l.map g).sum * c := by
  induction l with
  | nil => simp
  | cons x l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

lemma iRun_eq_of_unique {K : ℕ} {M : RelCode} (hMa : LetterAtomic M) {p : ℕ}
    (hp : p ∈ M.2.1) {w v : List ℕ} (hv : ∀ v', codeRel M w v' → v' = v) :
    iRun K M p w = nRun M p w * iota K v := by
  rw [iRun, List.map_congr_left
      (fun ρ hρ => congrArg (iota K) (hv _ (codeRel_of_mem_accRuns hMa hp hρ))),
    sum_map_const, nRun]

lemma iAll_eq_of_unique {K : ℕ} {M : RelCode} (hMa : LetterAtomic M) {w v : List ℕ}
    (hv : ∀ v', codeRel M w v' → v' = v) : iAll K M w = nAll M w * iota K v := by
  rw [iAll, List.map_congr_left (fun p hp => iRun_eq_of_unique hMa hp hv),
    sum_map_mul_const, nAll]

end PairWeighted
end Lax132576Proofs.Transducers
