/-
The crossing decomposition of a run of a two-way transducer at a cut of the
input, used by the effective equivalence bound of Theorem
`thm:decidable-equivalence-regular` (`RequestProject/PartC/RegEffBound.lean`).

Fix a cut `n₀` of the input `w = u ++ v`.  A halting run of a two-way transducer
on `w` breaks into maximal pieces (`Transducers.RegPos.Reg`,
`RequestProject/PartC/RegBlock.lean`) that stay on one side of the cut,
alternately on the left and on the right.  The states in which the run crosses
the cut form the *crossing sequence* `cs : List Q`, and
`Transducers.RegPos.Alt` is the assertion that the output of the run splits
accordingly.

Three facts are proved here.

* `Transducers.RegPos.alt_of_runP`: every halting run has such a decomposition,
  with the left pieces read as runs on `u ++ v.take 1` and the right pieces as
  runs on `v` with the cuts shifted by `n₀` -- this is where locality is used.
* `Transducers.RegPos.Alt.det`: the decomposition is unique, because a two-way
  transducer is deterministic.
* `Transducers.RegPos.Alt.length_le`: the crossing sequence has length at most
  `2 * Fintype.card Q`.  A crossing is determined by the side of the cut it
  leaves from and by the state, so two equal crossings would start two
  sub-decompositions from the same place; uniqueness then forces the two
  crossings to be the same one.

The last fact is what makes the index set of the Hankel decomposition of
`RequestProject/PartC/RegHankel.lean` finite of an explicitly bounded size.
-/
import Lax916827Proofs.Source.PartC.RegBlock
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

namespace RegPos

open TwoWay

variable {A B Q : Type}

/-! ## The two kinds of piece -/

/-- A piece of the run: on the left of the cut (`side = true`) it is a run on
the word `z`, ending with the step at the cut `n₀` that moves right; on the
right (`side = false`) it is a run on the word `v`, ending with the step at the
cut `1` of `v` that moves left. -/
def Blk (M : TwoWay A B Q) (z v : List A) (n₀ : ℕ) : Bool → ℕ × Q → List B → Option Q → Prop
  | true => Reg M z n₀ true
  | false => Reg M v 1 false

@[simp] lemma Blk_true (M : TwoWay A B Q) (z v : List A) (n₀ : ℕ) :
    Blk M z v n₀ true = Reg M z n₀ true := rfl

@[simp] lemma Blk_false (M : TwoWay A B Q) (z v : List A) (n₀ : ℕ) :
    Blk M z v n₀ false = Reg M v 1 false := rfl

lemma Blk.det {M : TwoWay A B Q} {z v : List A} {n₀ : ℕ} {side : Bool} {x : ℕ × Q}
    {o o' : List B} {r r' : Option Q} (h : Blk M z v n₀ side x o r)
    (h' : Blk M z v n₀ side x o' r') : o = o' ∧ r = r' := by
  cases side with
  | true => exact Reg.det h h'
  | false => exact Reg.det h h'

/-- Where the run enters the other side of the cut after a crossing. -/
def nxt (n₀ : ℕ) (side : Bool) (q : Q) : ℕ × Q := if side then (1, q) else (n₀, q)

@[simp] lemma nxt_true (n₀ : ℕ) (q : Q) : nxt n₀ true q = (1, q) := rfl

@[simp] lemma nxt_false (n₀ : ℕ) (q : Q) : nxt n₀ false q = (n₀, q) := rfl

/-- The side of the `j`-th piece of a decomposition that starts on the side
`side`. -/
def flipn (side : Bool) : ℕ → Bool
  | 0 => side
  | j + 1 => !(flipn side j)

@[simp] lemma flipn_zero (side : Bool) : flipn side 0 = side := rfl

@[simp] lemma flipn_succ (side : Bool) (j : ℕ) : flipn side (j + 1) = !(flipn side j) := rfl

lemma flipn_not (side : Bool) (j : ℕ) : flipn (!side) j = !(flipn side j) := by
  induction j with
  | zero => rfl
  | succ j ih => simp [ih]

/-! ## The decomposition -/

/-- The output `o` of a run starting on the side `side` at `x` splits along the
crossing sequence `cs`. -/
inductive Alt (M : TwoWay A B Q) (z v : List A) (n₀ : ℕ) :
    Bool → ℕ × Q → List Q → List B → Prop
  | halt {side : Bool} {x : ℕ × Q} {o : List B} :
      Blk M z v n₀ side x o none → Alt M z v n₀ side x [] o
  | cont {side : Bool} {x : ℕ × Q} {o o' : List B} {q' : Q} {cs : List Q} :
      Blk M z v n₀ side x o (some q') →
      Alt M z v n₀ (!side) (nxt n₀ side q') cs o' →
      Alt M z v n₀ side x (q' :: cs) (o ++ o')

/-- Prepending a step to the first piece of a decomposition. -/
lemma Alt.prepend {M : TwoWay A B Q} {z v : List A} {n₀ : ℕ} {side : Bool} {x x' : ℕ × Q}
    {o₁ : List B} {cs : List Q} {o : List B}
    (hmv : ∀ (ob : List B) (r : Option Q), Blk M z v n₀ side x' ob r →
      Blk M z v n₀ side x (o₁ ++ ob) r)
    (h : Alt M z v n₀ side x' cs o) : Alt M z v n₀ side x cs (o₁ ++ o) := by
  cases h with
  | halt hb => exact Alt.halt (hmv _ _ hb)
  | cont hb hrest =>
      rw [← List.append_assoc]
      exact Alt.cont (hmv _ _ hb) hrest

/-! ## Existence of the decomposition -/

/-- **The crossing decomposition of a halting run.**  A halting run of `M` on
`w` decomposes at the cut `n₀` into pieces that alternate between the two sides,
the pieces on the left read on the word `z` and the pieces on the right read on
the word `v` with the cuts shifted by `n₀`.

The hypotheses are exactly the locality of a step: a step at the cut `p` reads
the letters at the positions `p - 1` and `p`. -/
theorem alt_of_runP {M : TwoWay A B Q} {w z v : List A} {n₀ : ℕ}
    (hzl : ∀ p ≤ n₀, leftLet z p = leftLet w p)
    (hzr : ∀ p ≤ n₀, z[p]? = w[p]?)
    (hzlen : ∀ p < n₀, p < z.length)
    (hvl : ∀ p, 1 ≤ p → leftLet v p = leftLet w (n₀ + p))
    (hvr : ∀ p, v[p]? = w[n₀ + p]?)
    (hvlen : ∀ p, p < v.length ↔ n₀ + p < w.length) :
    ∀ (n : ℕ) (x : ℕ × Q) (o : List B), RunP M w n (some x) o none →
      (x.1 ≤ n₀ → ∃ cs, Alt M z v n₀ true x cs o) ∧
      (n₀ + 1 ≤ x.1 → ∃ cs, Alt M z v n₀ false (x.1 - n₀, x.2) cs o) := by
  intro n
  induction n with
  | zero => intro x o h; cases h
  | succ n ih =>
      rintro ⟨p, q⟩ o h
      cases h with
      | @step _ _ o₁ o₂ y _ hs hrest =>
      rcases hst : M.step (leftLet w p) q w[p]? with ob | ⟨q', ob, d⟩
      · -- the run halts
        simp only [stepP, hst] at hs
        obtain ⟨rfl, rfl⟩ : ob = o₁ ∧ (none : Option (ℕ × Q)) = y := by
          simpa [Prod.ext_iff] using hs
        obtain ⟨rfl, -⟩ := RunP.of_none hrest
        constructor
        · intro hple
          refine ⟨[], ?_⟩
          refine Alt.halt ?_
          rw [Blk_true, List.append_nil]
          exact Reg.halt (by rw [hzl p hple, hzr p hple]; exact hst)
        · intro hpge
          refine ⟨[], ?_⟩
          refine Alt.halt ?_
          rw [Blk_false, List.append_nil]
          refine Reg.halt ?_
          have h1 : leftLet v (p - n₀) = leftLet w p := by
            rw [hvl (p - n₀) (by omega)]
            congr 1
            omega
          have h2 : v[p - n₀]? = w[p]? := by
            rw [hvr (p - n₀)]
            congr 1
            omega
          rw [h1, h2]
          exact hst
      · cases d with
        | true =>
            simp only [stepP, hst] at hs
            by_cases hlt : p < w.length
            · rw [if_pos hlt] at hs
              obtain ⟨rfl, rfl⟩ : ob = o₁ ∧ (some (p + 1, q') : Option (ℕ × Q)) = y := by
                simpa [Prod.ext_iff] using hs
              constructor
              · intro hple
                by_cases hpn : p = n₀
                · subst hpn
                  obtain ⟨cs, hcs⟩ := (ih (p + 1, q') o₂ hrest).2 (by omega)
                  refine ⟨q' :: cs, Alt.cont ?_ ?_⟩
                  · rw [Blk_true]
                    exact Reg.exit (by rw [hzl p le_rfl, hzr p le_rfl]; exact hst)
                  · simpa using hcs
                · obtain ⟨cs, hcs⟩ := (ih (p + 1, q') o₂ hrest).1 (by simp; omega)
                  refine ⟨cs, Alt.prepend (fun oc r hb => ?_) hcs⟩
                  rw [Blk_true] at hb ⊢
                  exact Reg.moveR (by simp [hpn]) (hzlen p (by omega))
                    (by rw [hzl p hple, hzr p hple]; exact hst) hb
              · intro hpge
                have h1 : leftLet v (p - n₀) = leftLet w p := by
                  rw [hvl (p - n₀) (by omega)]; congr 1; omega
                have h2 : v[p - n₀]? = w[p]? := by
                  rw [hvr (p - n₀)]; congr 1; omega
                obtain ⟨cs, hcs⟩ := (ih (p + 1, q') o₂ hrest).2 (by simp; omega)
                have he : ((p + 1 : ℕ), q').1 - n₀ = (p - n₀) + 1 := by
                  show p + 1 - n₀ = (p - n₀) + 1
                  omega
                rw [he] at hcs
                refine ⟨cs, Alt.prepend (fun oc r hb => ?_) hcs⟩
                rw [Blk_false] at hb ⊢
                exact Reg.moveR (by simp) ((hvlen (p - n₀)).2 (by omega))
                  (by rw [h1, h2]; exact hst) hb
            · rw [if_neg hlt] at hs; exact absurd hs (by simp)
        | false =>
            simp only [stepP, hst] at hs
            by_cases hpos : 0 < p
            · rw [if_pos hpos] at hs
              obtain ⟨rfl, rfl⟩ : ob = o₁ ∧ (some (p - 1, q') : Option (ℕ × Q)) = y := by
                simpa [Prod.ext_iff] using hs
              constructor
              · intro hple
                obtain ⟨cs, hcs⟩ := (ih (p - 1, q') o₂ hrest).1 (by simp; omega)
                refine ⟨cs, Alt.prepend (fun oc r hb => ?_) hcs⟩
                rw [Blk_true] at hb ⊢
                exact Reg.moveL (by simp) hpos
                  (by rw [hzl p hple, hzr p hple]; exact hst) hb
              · intro hpge
                have h1 : leftLet v (p - n₀) = leftLet w p := by
                  rw [hvl (p - n₀) (by omega)]; congr 1; omega
                have h2 : v[p - n₀]? = w[p]? := by
                  rw [hvr (p - n₀)]; congr 1; omega
                by_cases hpn : p = n₀ + 1
                · subst hpn
                  obtain ⟨cs, hcs⟩ := (ih (n₀ + 1 - 1, q') o₂ hrest).1 (by simp)
                  have hblk : Blk M z v n₀ false (1, q) ob (some q') := by
                    rw [Blk_false]
                    exact Reg.exit (by rw [hvl 1 le_rfl, hvr 1]; exact hst)
                  refine ⟨q' :: cs, ?_⟩
                  have := Alt.cont hblk (by simpa using hcs)
                  simpa using this
                · obtain ⟨cs, hcs⟩ := (ih (p - 1, q') o₂ hrest).2 (by simp; omega)
                  have he : ((p - 1 : ℕ), q').1 - n₀ = (p - n₀) - 1 := by
                    show p - 1 - n₀ = (p - n₀) - 1
                    omega
                  rw [he] at hcs
                  refine ⟨cs, Alt.prepend (fun oc r hb => ?_) hcs⟩
                  rw [Blk_false] at hb ⊢
                  exact Reg.moveL (by simp; omega) (by omega) (by rw [h1, h2]; exact hst) hb
            · rw [if_neg hpos] at hs; exact absurd hs (by simp)

/-! ## Uniqueness of the decomposition, and the length of a crossing sequence -/

/-- The crossing decomposition is unique. -/
lemma Alt.det {M : TwoWay A B Q} {z v : List A} {n₀ : ℕ} {side : Bool} {x : ℕ × Q}
    {cs cs' : List Q} {o o' : List B}
    (h : Alt M z v n₀ side x cs o) (h' : Alt M z v n₀ side x cs' o') : cs = cs' ∧ o = o' := by
  induction h generalizing cs' o' with
  | @halt side x o hb =>
      cases h' with
      | halt hb' => exact ⟨rfl, (Blk.det hb hb').1⟩
      | cont hb' _ =>
          obtain ⟨-, hr⟩ := Blk.det hb hb'
          exact absurd hr.symm (by simp)
  | @cont side x o o₂ q' cs hb _ ih =>
      cases h' with
      | halt hb' =>
          obtain ⟨-, hr⟩ := Blk.det hb hb'
          exact absurd hr (by simp)
      | @cont _ _ ob' o₃ q'' cs'' hb' hrest' =>
          obtain ⟨ho, hr⟩ := Blk.det hb hb'
          obtain rfl : q' = q'' := by simpa using hr
          obtain ⟨h1, h2⟩ := ih hrest'
          exact ⟨by rw [h1], by rw [ho, h2]⟩

/-- Each crossing of the cut starts a sub-decomposition. -/
lemma Alt.sub {M : TwoWay A B Q} {z v : List A} {n₀ : ℕ} {side : Bool} {x : ℕ × Q}
    {cs : List Q} {o : List B} (h : Alt M z v n₀ side x cs o) :
    ∀ (j : ℕ) (hj : j < cs.length), ∃ o',
      Alt M z v n₀ (flipn side (j + 1)) (nxt n₀ (flipn side j) cs[j]) (cs.drop (j + 1)) o' := by
  induction h with
  | halt hb => intro j hj; simp at hj
  | @cont side x o o₂ q' cs hb hrest ih =>
      intro j hj
      cases j with
      | zero => exact ⟨o₂, by simpa using hrest⟩
      | succ k =>
          have hk : k < cs.length := by simpa using hj
          obtain ⟨o', ho'⟩ := ih k hk
          refine ⟨o', ?_⟩
          rw [flipn_not] at ho'
          simpa [flipn_not] using ho'

variable [Fintype Q]

/-- **The crossing sequence is short.**  It has at most `2 * Fintype.card Q`
entries: a crossing is determined by the side of the cut that it leaves and by
the state, and two crossings with the same data would start, by uniqueness, two
sub-decompositions of the same length. -/
lemma Alt.length_le {M : TwoWay A B Q} {z v : List A} {n₀ : ℕ} {side : Bool} {x : ℕ × Q}
    {cs : List Q} {o : List B} (h : Alt M z v n₀ side x cs o) :
    cs.length ≤ 2 * Fintype.card Q := by
  classical
  have hinj : Function.Injective (fun j : Fin cs.length => (flipn side (j : ℕ), cs[(j : ℕ)])) := by
    intro j j' hjj
    simp only [Prod.mk.injEq] at hjj
    obtain ⟨hside, hst⟩ := hjj
    obtain ⟨o₁, h₁⟩ := h.sub j j.isLt
    obtain ⟨o₂, h₂⟩ := h.sub j' j'.isLt
    rw [hside, hst] at h₁
    have hs1 : flipn side ((j : ℕ) + 1) = flipn side ((j' : ℕ) + 1) := by
      simp [hside]
    rw [hs1] at h₁
    have := (Alt.det h₁ h₂).1
    have hlen : cs.length - ((j : ℕ) + 1) = cs.length - ((j' : ℕ) + 1) := by
      simpa using congrArg List.length this
    have := j.isLt
    have := j'.isLt
    exact Fin.ext (by omega)
  have := Fintype.card_le_of_injective _ hinj
  simpa [Fintype.card_bool, mul_comm] using this

end RegPos

end Lax916827Proofs.Transducers
