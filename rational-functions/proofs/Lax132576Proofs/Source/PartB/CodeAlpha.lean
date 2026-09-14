/- The alphabets of a code, and the elementary facts about them that the decision procedures of
Sections *Rational relations and weighted automata* and *Machine independent characterisations* of
*Transducers* (M. Bojańczyk) need.

A code has finitely many transitions, so the automaton that it describes reads
only the letters occurring in the input strings of its transitions
(`codeAlphabet`, defined in `RequestProject/PartB/Codes.lean`) and writes only
the letters occurring in their output strings (`codeOutAlphabet`, defined here).
Both facts are used to reduce a statement about all strings over `ℕ` to a
statement about the finitely many letters that the code can see.

The file also contains the boolean test `sameAlpha` deciding whether two codes
read the same letters -- under the promise that both codes describe a total
function on the strings over their alphabet, this is exactly the statement that
the two relations have the same domain.
-/
import Lax132576Proofs.Source.PartB.CodeMerge
open Lax765601Proofs Lax765601Proofs.Transducers

namespace Lax132576Proofs.Transducers

open LabAut LenDec

/-! ## The output alphabet -/

/-- The letters that the automaton described by a code can write: those
occurring in the output strings of its transitions. -/
def codeOutAlphabet (c : RelCode) : List ℕ := c.1.flatMap (fun t => t.2.2.1)

lemma mem_codeOutAlphabet_of_mem_output {c : RelCode} {ts : List (ℕ × List ℕ × List ℕ × ℕ)}
    (hts : ∀ t ∈ ts, t ∈ c.1) {x : ℕ} (hx : x ∈ NFAO.outputOf ts) :
    x ∈ codeOutAlphabet c := by
  simp only [NFAO.outputOf, labelsOf, List.mem_flatten, List.mem_map] at hx
  obtain ⟨u, ⟨t, ht, rfl⟩, hxu⟩ := hx
  exact List.mem_flatMap.2 ⟨t, hts t ht, hxu⟩

/-- Every letter of an output of the relation described by a code occurs in the
output strings of its transitions. -/
lemma codeRel_output_mem {c : RelCode} {w v : List ℕ} (h : codeRel c w v) {x : ℕ}
    (hx : x ∈ v) : x ∈ codeOutAlphabet c := by
  obtain ⟨ts, ⟨q, -, p, -, hpath⟩, -, rfl⟩ := h
  exact mem_codeOutAlphabet_of_mem_output (fun t ht => Path.mem_delta hpath t ht) hx

/-- Every letter of an input of the relation described by a code occurs in the
input strings of its transitions. -/
lemma codeRel_codeWord {c : RelCode} {w v : List ℕ} (h : codeRel c w v) : CodeWord c w := by
  obtain ⟨ts, ⟨q, -, p, -, hpath⟩, rfl, -⟩ := h
  exact fun x hx =>
    mem_codeAlphabet_of_mem_input (fun t ht => Path.mem_delta hpath t ht) hx

/-- A string using a letter that the code cannot read is not in the domain of
the relation described by the code. -/
lemma not_codeRel_of_foreign {c : RelCode} {w : List ℕ} {x : ℕ} (hxw : x ∈ w)
    (hx : x ∉ codeAlphabet c) : ∀ v, ¬ codeRel c w v :=
  fun _ h => hx (codeRel_codeWord h x hxw)

/-! ## Deciding whether two codes read the same letters -/

lemma allB_eq_isEmpty {α : Type} (l : List α) (p : α → Bool) :
    allB l p = (l.filter (fun x => !p x)).isEmpty := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases h : p a = true
      · simp [allB, h] at *
        simpa using ih
      · simp only [Bool.not_eq_true] at h
        simp [allB, h]

/-- The two codes read the same letters. -/
def sameAlpha (c₁ c₂ : RelCode) : Bool :=
  allB (codeAlphabet c₁) (memB (codeAlphabet c₂)) &&
    allB (codeAlphabet c₂) (memB (codeAlphabet c₁))

lemma sameAlpha_iff (c₁ c₂ : RelCode) :
    sameAlpha c₁ c₂ = true ↔ ∀ x, x ∈ codeAlphabet c₁ ↔ x ∈ codeAlphabet c₂ := by
  simp only [sameAlpha, Bool.and_eq_true, allB_iff, memB_iff]
  constructor
  · rintro ⟨h1, h2⟩ x
    exact ⟨fun h => h1 x h, fun h => h2 x h⟩
  · intro h
    exact ⟨fun x hx => (h x).1 hx, fun x hx => (h x).2 hx⟩

/-! ## Computability -/

lemma primrec_codeAlphabet : Primrec codeAlphabet := by
  refine Primrec.list_flatMap Primrec.fst ?_
  show Primrec fun z : RelCode × (ℕ × List ℕ × List ℕ × ℕ) => z.2.2.1
  exact Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

lemma primrec_codeOutAlphabet : Primrec codeOutAlphabet := by
  refine Primrec.list_flatMap Primrec.fst ?_
  show Primrec fun z : RelCode × (ℕ × List ℕ × List ℕ × ℕ) => z.2.2.2.1
  exact Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

/-- A bounded universal quantifier over a computable list is primitive
recursive. -/
lemma primrec_allB {α β : Type} [Primcodable α] [Primcodable β] {f : α → List β}
    {p : α → β → Bool} (hf : Primrec f) (hp : Primrec₂ p) :
    Primrec (fun a => allB (f a) (p a)) := by
  have hnot : Primrec₂ (fun (a : α) (x : β) => !p a x) :=
    (Primrec.cond hp (Primrec.const false) (Primrec.const true)).to₂
  have hfil : Primrec (fun a => (f a).filter (fun x => !p a x)) :=
    CodeMerge.primrec_filter hf hnot
  have h : Primrec (fun a => decide (((f a).filter (fun x => !p a x)).length = 0)) :=
    primrec_decEq (Primrec.list_length.comp hfil) (Primrec.const 0)
  refine h.of_eq (fun a => ?_)
  rw [allB_eq_isEmpty]
  cases ((f a).filter (fun x => !p a x)) <;> simp

lemma primrec_sameAlpha : Primrec (fun p : RelCode × RelCode => sameAlpha p.1 p.2) := by
  have h1 : Primrec (fun p : RelCode × RelCode =>
      allB (codeAlphabet p.1) (memB (codeAlphabet p.2))) :=
    primrec_allB (primrec_codeAlphabet.comp Primrec.fst)
      (primrec_memB.comp (primrec_codeAlphabet.comp (Primrec.snd.comp Primrec.fst))
        Primrec.snd)
  have h2 : Primrec (fun p : RelCode × RelCode =>
      allB (codeAlphabet p.2) (memB (codeAlphabet p.1))) :=
    primrec_allB (primrec_codeAlphabet.comp Primrec.snd)
      (primrec_memB.comp (primrec_codeAlphabet.comp (Primrec.fst.comp Primrec.fst))
        Primrec.snd)
  exact (Primrec.and.comp h1 h2).of_eq (fun _ => rfl)

end Lax132576Proofs.Transducers
