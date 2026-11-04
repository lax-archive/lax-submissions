import Lax185574Proofs.Words.TreeWord
import Lax185574Proofs.TreeAlgo.Evaluation

/-!
Evaluation of a formula on a type tree read by position.

`evalW X φ p h` evaluates the formula `φ` on the node of height `h` whose
word starts at position `p` of the word `X`, in the way the program does:
an atom is looked up among the atom codes of the node, the Boolean
connectives are evaluated directly, and `∃ y (dist(xᵢ, y) ≤ s ∧ ψ)` holds
if some frame of the extensions of the node has guard `i` and its child
satisfies `ψ`. On the word of a node this is the semantic core
`Lax185574Proofs.TreeAlgo.evalNode`.
-/

namespace Lax185574Proofs.EvalRam

open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo Lax185574Proofs.Words
open Lax185574.DistanceLogic Lax185574.DistanceLogic.DistFO

/-- A Boolean as a number. -/
def bv (b : Bool) : ℕ := if b then 1 else 0

@[simp] theorem bv_true : bv true = 1 := rfl
@[simp] theorem bv_false : bv false = 0 := rfl

theorem bv_le (b : Bool) : bv b ≤ 1 := by cases b <;> simp

theorem bv_eq_one {b : Bool} : bv b = 1 ↔ b = true := by cases b <;> simp

/-- Evaluation of a formula on the node of height `h` at position `p`
of `X`. -/
def evalW (X : List ℕ) : {ℓ : ℕ} → DistFO ℓ → ℕ → ℕ → Bool
  | _, .not φ, p, h => !evalW X φ p h
  | _, .and φ ψ, p, h => evalW X φ p h && evalW X ψ p h
  | _, .exLocal i _ φ, p, h =>
      match h with
      | 0 => false
      | h + 1 => decide (∃ j < xg X (listEnd X p),
          xg X (frPos X (listEnd X p) j + 1) = i.val ∧
            evalW X φ (frPos X (listEnd X p) j + 2) h = true)
  | _, φ, p, _ => decide (code φ ∈ listWords X p)

theorem code_inj {ℓ : ℕ} (φ : DistFO ℓ) :
    ∀ (ψ : DistFO ℓ) (r s : List ℕ), code φ ++ r = code ψ ++ s → φ = ψ ∧ r = s := by
  induction φ with
  | not φ ih =>
    intro ψ r s h
    cases ψ <;> simp only [code, List.cons_append, List.cons.injEq] at h <;>
      first | omega | skip
    obtain ⟨h1, h2⟩ := ih _ _ _ h.2
    exact ⟨by rw [h1], h2⟩
  | and φ φ' ih ih' =>
    intro ψ r s h
    cases ψ <;> simp only [code, List.cons_append, List.cons.injEq,
      List.append_assoc] at h <;> first | omega | skip
    obtain ⟨h1, h'⟩ := ih _ _ _ h.2
    obtain ⟨h2, h3⟩ := ih' _ _ _ h'
    exact ⟨by rw [h1, h2], h3⟩
  | exLocal i t φ ih =>
    intro ψ r s h
    cases ψ <;> simp only [code, List.cons_append, List.cons.injEq] at h <;>
      first | omega | skip
    obtain ⟨h1, h2⟩ := ih _ _ _ h.2.2.2
    obtain rfl : i = _ := Fin.ext h.2.1
    obtain rfl := h.2.2.1
    exact ⟨by rw [h1], h2⟩
  | _ =>
    intro ψ r s h
    cases ψ <;> simp only [code, List.cons_append, List.cons.injEq, List.nil_append] at h <;>
      first | omega | skip
    all_goals simp_all [Fin.val_inj]

theorem code_injective {ℓ : ℕ} {φ ψ : DistFO ℓ} (h : code φ = code ψ) : φ = ψ :=
  (code_inj φ ψ [] [] (by simpa using h)).1

theorem code_mem_words {ℓ : ℕ} {S : Finset (DistFO ℓ)} {φ : DistFO ℓ} :
    code φ ∈ S.words ↔ φ ∈ S := by
  rw [mem_words]
  constructor
  · rintro ⟨a, ha, h⟩
    rwa [code_injective ((Lax185574Proofs.Legacy.encode_eq_code a).symm.trans h :
      code a = code φ)] at ha
  · intro h; exact ⟨φ, h, Lax185574Proofs.Legacy.encode_eq_code φ⟩

/-- The atoms of a node, read by position. -/
theorem atoms_listWords {h ℓ : ℕ} {X : List ℕ} {p : ℕ} {t : Node h ℓ} {r : List ℕ}
    (hx : X.drop p = toWord t ++ r) : listWords X p = (Node.atoms t).words := by
  cases h with
  | zero => rw [toWord_node_zero] at hx; exact listWords_eq hx
  | succ h => exact listWords_eq (nodeSplit hx).1

theorem evalW_atom {h ℓ : ℕ} {X : List ℕ} {p : ℕ} {t : Node h ℓ} {r : List ℕ}
    (hx : X.drop p = toWord t ++ r) (φ : DistFO ℓ) :
    decide (code φ ∈ listWords X p) = decide (φ ∈ Node.atoms t) := by
  rw [atoms_listWords hx]
  exact decide_eq_decide.mpr code_mem_words

/-- **Evaluation by position.** On the word of a node, `evalW` is the
semantic core `evalNode`. -/
theorem evalW_eq (X : List ℕ) {ℓ : ℕ} (φ : DistFO ℓ) :
    ∀ {h : ℕ} (t : Node h ℓ) (p : ℕ) (r : List ℕ), X.drop p = toWord t ++ r →
      evalW X φ p h = evalNode t φ := by
  induction φ with
  | not φ ih => intro h t p r hx; simp [evalW, evalNode, ih t p r hx]
  | and φ ψ ih ih' => intro h t p r hx; simp [evalW, evalNode, ih t p r hx, ih' t p r hx]
  | exLocal i s φ ih =>
    intro h t p r hx
    cases h with
    | zero => rfl
    | succ h =>
      simp only [evalW, evalNode]
      obtain ⟨-, h2⟩ := nodeSplit hx
      have h0 := (listAt h2).1
      refine decide_eq_decide.mpr ⟨?_, ?_⟩
      · rintro ⟨j, hj, hg, hev⟩
        rw [h0] at hj
        obtain ⟨a, ha, haw⟩ := getElem_words hj
        obtain ⟨hga, r', hr'⟩ := extFrame h2 hj haw
        refine ⟨a, ha, Fin.ext (by rw [← hga, hg]), ?_⟩
        rwa [ih a.2 _ r' hr'] at hev
      · rintro ⟨a, ha, rfl, hev⟩
        have hmem : toWord a ∈ (Node.exts t).words := mem_words.mpr ⟨a, ha, rfl⟩
        obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem hmem
        obtain ⟨hga, r', hr'⟩ := extFrame h2 hj hjw.symm
        refine ⟨j, by rw [h0]; exact hj, hga, ?_⟩
        rwa [ih a.2 _ r' hr']
  | eq i j => intro h t p r hx; exact evalW_atom hx _
  | edge i j => intro h t p r hx; exact evalW_atom hx _
  | nonEdge i j => intro h t p r hx; exact evalW_atom hx _
  | color Y i => intro h t p r hx; exact evalW_atom hx _
  | distLe s i j => intro h t p r hx; exact evalW_atom hx _
  | distColorLt s Y i => intro h t p r hx; exact evalW_atom hx _

end Lax185574Proofs.EvalRam
