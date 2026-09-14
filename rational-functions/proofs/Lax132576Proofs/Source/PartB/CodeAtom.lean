/-
Atomisation of the input of a coded nfa with output.

The decision procedures of Theorems `thm:equivalence-rational-functions` and `thm:decide-if-mealy`
need a normal form of a code in which every transition reads exactly one letter.  The first step
towards it, carried out here, splits every transition into a chain of transitions each of which
reads at most one letter: the transition `p --u/v--> q` with `u = a₁ ⋯ a_k` becomes

  `p --a₁/ε--> m₀ --a₂/ε--> ⋯ --a_k/ε--> m_{k-1} --ε/v--> q`,

where the intermediate states `m₀, …, m_{k-1}` are fresh.  The states of the
original code are renamed `q ↦ 2 * q`, and the fresh state used after reading
`j + 1` letters of the transition `t` is the odd number
`2 * ⟨code of t, j⟩ + 1`.  Coding the *whole* transition into the fresh state,
rather than only its position in the code, is what makes the analysis of the
atomised automaton easy: a fresh state determines the transition that it belongs
to and the number of letters that have already been read, hence also the unique
transition of the atomised code that leaves it.

The relation described by the code is unchanged (`atomCode_rel`).
-/
import Lax132576Proofs.Source.PartB.Codes
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers
namespace CodeAtom

open LabAut

/-- The type of coded transitions. -/
abbrev Tr := ℕ × List ℕ × List ℕ × ℕ

/-- The renaming of the states of the original code. -/
def orig (q : ℕ) : ℕ := 2 * q

/-- The fresh state reached after reading `j + 1` letters of the transition
`t`. -/
def midS (t : Tr) (j : ℕ) : ℕ := 2 * Nat.pair (Encodable.encode t) j + 1

/-- The source of the transition of the chain of `t` that reads the `k`-th
letter of the input of `t`. -/
def srcS (t : Tr) (k : ℕ) : ℕ := if k = 0 then orig t.1 else midS t (k - 1)

lemma orig_ne_midS (q : ℕ) (t : Tr) (j : ℕ) : orig q ≠ midS t j := by
  simp only [orig, midS]; omega

lemma orig_injective : Function.Injective orig := by
  intro a b h; simpa [orig] using h

lemma midS_inj {t t' : Tr} {j j' : ℕ} (h : midS t j = midS t' j') : t = t' ∧ j = j' := by
  have h' : Nat.pair (Encodable.encode t) j = Nat.pair (Encodable.encode t') j' := by
    simp only [midS] at h; omega
  have := Nat.pair_eq_pair.1 h'
  exact ⟨Encodable.encode_injective this.1, this.2⟩

@[simp] lemma srcS_zero (t : Tr) : srcS t 0 = orig t.1 := rfl

@[simp] lemma srcS_succ (t : Tr) (k : ℕ) : srcS t (k + 1) = midS t k := by
  simp [srcS]

/-- The chain of transitions replacing a transition. -/
def chain (t : Tr) : List Tr :=
  (List.range t.2.1.length).map
      (fun k => (srcS t k, [t.2.1.getD k 0], ([] : List ℕ), midS t k)) ++
    [(srcS t t.2.1.length, [], t.2.2.1, orig t.2.2.2)]

lemma mem_chain {t tr : Tr} :
    tr ∈ chain t ↔
      (∃ k < t.2.1.length, tr = (srcS t k, [t.2.1.getD k 0], ([] : List ℕ), midS t k)) ∨
        tr = (srcS t t.2.1.length, [], t.2.2.1, orig t.2.2.2) := by
  simp only [chain, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton]
  constructor
  · rintro (⟨k, hk, rfl⟩ | h)
    · exact Or.inl ⟨k, hk, rfl⟩
    · exact Or.inr h
  · rintro (⟨k, hk, rfl⟩ | h)
    · exact Or.inl ⟨k, hk, rfl⟩
    · exact Or.inr h

/-- The code in which every transition reads at most one letter. -/
def atomCode (c : RelCode) : RelCode :=
  (c.1.flatMap chain, c.2.1.map orig, c.2.2.map orig)

/-- Every transition of the atomised code reads at most one letter. -/
lemma atomCode_atomic (c : RelCode) :
    ∀ t ∈ (atomCode c).1, t.2.1 = [] ∨ ∃ a, t.2.1 = [a] := by
  intro tr htr
  obtain ⟨t, -, htr⟩ := List.mem_flatMap.1 htr
  rcases mem_chain.1 htr with ⟨k, -, rfl⟩ | rfl
  · exact Or.inr ⟨_, rfl⟩
  · exact Or.inl rfl

/-! ## The transitions leaving a state of the atomised code -/

lemma srcS_eq_orig {t' : Tr} {k p : ℕ} (h : srcS t' k = orig p) : k = 0 ∧ t'.1 = p := by
  rcases k with _ | k
  · exact ⟨rfl, orig_injective h⟩
  · rw [srcS_succ] at h
    exact absurd h.symm (orig_ne_midS p t' k)

lemma srcS_eq_midS {t' t : Tr} {k j : ℕ} (h : srcS t' k = midS t j) : t' = t ∧ k = j + 1 := by
  rcases k with _ | k
  · exact absurd h (orig_ne_midS t'.1 t j)
  · rw [srcS_succ] at h
    obtain ⟨h1, h2⟩ := midS_inj h
    exact ⟨h1, by omega⟩

lemma atom_out_orig {c : RelCode} {tr : Tr} (htr : tr ∈ (atomCode c).1) {p : ℕ}
    (hp : tr.1 = orig p) :
    ∃ t ∈ c.1, t.1 = p ∧
      ((∃ a u, t.2.1 = a :: u ∧ tr = (orig p, [a], [], midS t 0)) ∨
        (t.2.1 = [] ∧ tr = (orig p, [], t.2.2.1, orig t.2.2.2))) := by
  obtain ⟨t, ht, htr⟩ := List.mem_flatMap.1 htr
  rcases mem_chain.1 htr with ⟨k, hk, rfl⟩ | rfl
  · obtain ⟨rfl, hp1⟩ := srcS_eq_orig hp
    refine ⟨t, ht, hp1, Or.inl ⟨t.2.1.getD 0 0, t.2.1.drop 1, ?_, ?_⟩⟩
    · rcases hu : t.2.1 with _ | ⟨a, u⟩
      · rw [hu] at hk; simp at hk
      · simp
    · simp [hp1]
  · obtain ⟨hk0, hp1⟩ := srcS_eq_orig hp
    refine ⟨t, ht, hp1, Or.inr ⟨List.eq_nil_of_length_eq_zero hk0, ?_⟩⟩
    rw [hk0]
    simp [hp1]

lemma atom_out_mid {c : RelCode} {tr : Tr} (htr : tr ∈ (atomCode c).1) {t : Tr}
    (ht : t ∈ c.1) {j : ℕ} (hj : j < t.2.1.length) (hp : tr.1 = midS t j) :
    (j + 1 < t.2.1.length ∧
        tr = (midS t j, [t.2.1.getD (j + 1) 0], [], midS t (j + 1))) ∨
      (j + 1 = t.2.1.length ∧ tr = (midS t j, [], t.2.2.1, orig t.2.2.2)) := by
  obtain ⟨t', ht', htr⟩ := List.mem_flatMap.1 htr
  rcases mem_chain.1 htr with ⟨k, hk, rfl⟩ | rfl
  · obtain ⟨rfl, rfl⟩ := srcS_eq_midS hp
    exact Or.inl ⟨hk, by simp⟩
  · obtain ⟨rfl, hlen⟩ := srcS_eq_midS hp
    refine Or.inr ⟨hlen.symm, ?_⟩
    rw [hlen]
    simp

/-! ## Completeness: every run of the code is a run of the atomised code -/

lemma chain_subset {c : RelCode} {t : Tr} (ht : t ∈ c.1) : ∀ tr ∈ chain t, tr ∈ (atomCode c).1 :=
  fun _ htr => List.mem_flatMap.2 ⟨t, ht, htr⟩

lemma chain_relFrom {c : RelCode} {t : Tr} (ht : t ∈ c.1) :
    ∀ (n k : ℕ), t.2.1.length - k = n → k ≤ t.2.1.length →
      NFAO.relFrom (codeAut (atomCode c)) (srcS t k) (t.2.1.drop k) t.2.2.1
        (orig t.2.2.2) := by
  intro n
  induction n with
  | zero =>
      intro k hn hk
      have hk' : k = t.2.1.length := by omega
      subst hk'
      have : ((srcS t t.2.1.length, ([] : List ℕ), t.2.2.1, orig t.2.2.2) : Tr) ∈
          (codeAut (atomCode c)).δ :=
        chain_subset ht _ (mem_chain.2 (Or.inr rfl))
      simpa using NFAO.relFrom_single this
  | succ n ih =>
      intro k hn hk
      have hklt : k < t.2.1.length := by omega
      have hstep : ((srcS t k, [t.2.1.getD k 0], ([] : List ℕ), midS t k) : Tr) ∈
          (codeAut (atomCode c)).δ :=
        chain_subset ht _ (mem_chain.2 (Or.inl ⟨k, hklt, rfl⟩))
      have hrec := ih (k + 1) (by omega) (by omega)
      rw [← srcS_succ t k] at hstep
      have := NFAO.relFrom_step hstep hrec
      have hdrop : t.2.1.drop k = t.2.1.getD k 0 :: t.2.1.drop (k + 1) := by
        rw [List.drop_eq_getElem_cons hklt]
        congr 1
        exact (List.getD_eq_getElem _ _ hklt).symm
      rw [hdrop]
      simpa using this

lemma trans_relFrom {c : RelCode} {t : Tr} (ht : t ∈ c.1) :
    NFAO.relFrom (codeAut (atomCode c)) (orig t.1) t.2.1 t.2.2.1 (orig t.2.2.2) := by
  have := chain_relFrom ht t.2.1.length 0 (by omega) (by omega)
  simpa using this

lemma relFrom_atom {c : RelCode} {p : ℕ} {w x : List ℕ} {r : ℕ}
    (h : NFAO.relFrom (codeAut c) p w x r) :
    NFAO.relFrom (codeAut (atomCode c)) (orig p) w x (orig r) := by
  refine NFAO.relFrom_induction (motive := fun q w x =>
    NFAO.relFrom (codeAut (atomCode c)) (orig q) w x (orig r)) ?_ ?_ h
  · exact NFAO.relFrom_nil _ _
  · intro q q' u y w' v' hδ _ hrec
    have ht : ((q, u, y, q') : Tr) ∈ c.1 := hδ
    exact NFAO.relFrom_trans (trans_relFrom ht) hrec

/-! ## Soundness: every run of the atomised code is a run of the code -/

lemma sound_aux (c : RelCode) : ∀ n : ℕ,
    (∀ (ts : List Tr) (p r : ℕ), ts.length ≤ n →
        (codeAut (atomCode c)).Path (orig p) ts (orig r) →
        NFAO.relFrom (codeAut c) p (inputOf ts) (NFAO.outputOf ts) r) ∧
    (∀ (ts : List Tr) (t : Tr) (j r : ℕ), ts.length ≤ n → t ∈ c.1 → j < t.2.1.length →
        (codeAut (atomCode c)).Path (midS t j) ts (orig r) →
        ∃ w' x', inputOf ts = t.2.1.drop (j + 1) ++ w' ∧
          NFAO.outputOf ts = t.2.2.1 ++ x' ∧ NFAO.relFrom (codeAut c) t.2.2.2 w' x' r) := by
  intro n
  induction n with
  | zero =>
      constructor
      · intro ts p r hlen hpath
        have : ts = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst this
        rw [orig_injective (Path.eq_of_nil hpath)]
        exact NFAO.relFrom_nil _ _
      · intro ts t j r hlen _ _ hpath
        have : ts = [] := List.eq_nil_of_length_eq_zero (by omega)
        subst this
        exact absurd (Path.eq_of_nil hpath).symm (orig_ne_midS r t j)
  | succ n ih =>
      obtain ⟨ihO, ihM⟩ := ih
      constructor
      · intro ts p r hlen hpath
        rcases ts with _ | ⟨tr, ts'⟩
        · rw [orig_injective (Path.eq_of_nil hpath)]
          exact NFAO.relFrom_nil _ _
        obtain ⟨hsrc, hmem, hrest⟩ := Path.cons_inv hpath
        obtain ⟨t, ht, hp, hcase⟩ := atom_out_orig (c := c) hmem hsrc
        have htδ : ((t.1, t.2.1, t.2.2.1, t.2.2.2) : Tr) ∈ (codeAut c).δ := ht
        rcases hcase with ⟨a, u, hu, rfl⟩ | ⟨hu, rfl⟩
        · have hj : (0 : ℕ) < t.2.1.length := by rw [hu]; simp
          obtain ⟨w', x', hin, hout, hrel⟩ :=
            ihM ts' t 0 r (by simpa using hlen) ht hj hrest
          have := NFAO.relFrom_step htδ hrel
          rw [hp] at this
          rw [inputOf_cons, NFAO.outputOf_cons, hin, hout]
          simpa [hu] using this
        · obtain hrec := ihO ts' t.2.2.2 r (by simpa using hlen) hrest
          have := NFAO.relFrom_step htδ hrec
          rw [hp] at this
          rw [inputOf_cons, NFAO.outputOf_cons]
          simpa [hu] using this
      · intro ts t j r hlen ht hj hpath
        rcases ts with _ | ⟨tr, ts'⟩
        · exact absurd (Path.eq_of_nil hpath).symm (orig_ne_midS r t j)
        obtain ⟨hsrc, hmem, hrest⟩ := Path.cons_inv hpath
        rcases atom_out_mid (c := c) hmem ht hj hsrc with ⟨hlt, rfl⟩ | ⟨heq, rfl⟩
        · obtain ⟨w', x', hin, hout, hrel⟩ :=
            ihM ts' t (j + 1) r (by simpa using hlen) ht hlt hrest
          refine ⟨w', x', ?_, by simpa using hout, hrel⟩
          rw [inputOf_cons, hin]
          have hdrop : t.2.1.drop (j + 1) = t.2.1.getD (j + 1) 0 :: t.2.1.drop (j + 2) := by
            rw [List.drop_eq_getElem_cons hlt]
            congr 1
            exact (List.getD_eq_getElem _ _ hlt).symm
          rw [hdrop]
          simp
        · obtain hrec := ihO ts' t.2.2.2 r (by simpa using hlen) hrest
          refine ⟨inputOf ts', NFAO.outputOf ts', ?_, by simp, hrec⟩
          rw [inputOf_cons]
          have : t.2.1.drop (j + 1) = [] := List.drop_eq_nil_of_le (by omega)
          simp [this]

lemma sound_orig {c : RelCode} {ts : List Tr} {p r : ℕ}
    (hpath : (codeAut (atomCode c)).Path (orig p) ts (orig r)) :
    NFAO.relFrom (codeAut c) p (inputOf ts) (NFAO.outputOf ts) r :=
  (sound_aux c ts.length).1 ts p r le_rfl hpath

/-- Atomisation does not change the relation described by the code. -/
lemma atomCode_rel (c : RelCode) : codeRel (atomCode c) = codeRel c := by
  funext w v
  simp only [codeRel, eq_iff_iff]
  rw [NFAO.rel_iff_relFrom, NFAO.rel_iff_relFrom]
  constructor
  · rintro ⟨q, hq, p, hp, ts, hpath, rfl, rfl⟩
    obtain ⟨q₀, hq₀, rfl⟩ : ∃ q₀ ∈ c.2.1, orig q₀ = q := by
      simpa [atomCode, codeAut, eq_comm] using hq
    obtain ⟨p₀, hp₀, rfl⟩ : ∃ p₀ ∈ c.2.2, orig p₀ = p := by
      simpa [atomCode, codeAut, eq_comm] using hp
    exact ⟨q₀, hq₀, p₀, hp₀, sound_orig hpath⟩
  · rintro ⟨q, hq, p, hp, hrel⟩
    refine ⟨orig q, ?_, orig p, ?_, relFrom_atom hrel⟩
    · show orig q ∈ c.2.1.map orig
      exact List.mem_map_of_mem hq
    · show orig p ∈ c.2.2.map orig
      exact List.mem_map_of_mem hp

/-! ## Effectivity -/

set_option maxHeartbeats 1000000 in
lemma primrec_midS : Primrec (fun z : Tr × ℕ => midS z.1 z.2) :=
  Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 2)
      (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst) Primrec.snd))
    (Primrec.const 1)

set_option maxHeartbeats 1000000 in
lemma primrec_srcS : Primrec (fun z : Tr × ℕ => srcS z.1 z.2) := by
  have hmid : Primrec (fun z : Tr × ℕ => midS z.1 (z.2 - 1)) :=
    Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2)
        (Primrec₂.natPair.comp (Primrec.encode.comp Primrec.fst)
          (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))))
      (Primrec.const 1)
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.fst)) hmid

set_option maxHeartbeats 1000000 in
lemma primrec_chain : Primrec chain := by
  have h1 : Primrec (fun t : Tr =>
      (List.range t.2.1.length).map
        (fun k => (srcS t k, [t.2.1.getD k 0], ([] : List ℕ), midS t k))) := by
    refine Primrec.list_map (Primrec.list_range.comp
      (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd))) ?_
    have hlet : Primrec (fun z : Tr × ℕ => [z.1.2.1.getD z.2 0]) :=
      Primrec.list_cons.comp
        ((Primrec.list_getD 0).comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd)
        (Primrec.const [])
    exact Primrec.pair primrec_srcS
      (Primrec.pair hlet (Primrec.pair (Primrec.const []) primrec_midS))
  have h2 : Primrec (fun t : Tr =>
      [((srcS t t.2.1.length, ([] : List ℕ), t.2.2.1, orig t.2.2.2) : Tr)]) := by
    have hsrc : Primrec (fun t : Tr => srcS t t.2.1.length) :=
      primrec_srcS.comp (Primrec.pair Primrec.id
        (Primrec.list_length.comp (Primrec.fst.comp Primrec.snd)))
    exact Primrec.list_cons.comp
      (Primrec.pair hsrc (Primrec.pair (Primrec.const [])
        (Primrec.pair (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
          (Primrec.nat_mul.comp (Primrec.const 2)
            (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))))
      (Primrec.const [])
  exact Primrec.list_append.comp h1 h2

set_option maxHeartbeats 1000000 in
lemma primrec_atomCode : Primrec atomCode := by
  refine Primrec.pair (Primrec.list_flatMap Primrec.fst (primrec_chain.comp Primrec.snd).to₂) ?_
  exact Primrec.pair
    (Primrec.list_map (Primrec.fst.comp Primrec.snd)
      ((Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)).to₂)
    (Primrec.list_map (Primrec.snd.comp Primrec.snd)
      ((Primrec.nat_mul.comp (Primrec.const 2) Primrec.snd)).to₂)

end CodeAtom
end Lax132576Proofs.Transducers
