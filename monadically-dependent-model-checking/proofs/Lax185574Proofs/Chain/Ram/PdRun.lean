import Lax185574Proofs.Chain.Ram.PdSpec

/-!
The predamping procedure on numbers.

The rule chosen by `pdStep` is the first vertex passing the first
applicable rule. On numbers this is `firstN` of the three rules
(`pdStep_val`). The quantities `hamN` and `betwN` only grow with the
parameter set (`hamN_mono`, `betwN_mono`), which is what lets the
program keep, for every vertex, a pointer into the list of chosen
vertices up to which the vertex is known to be far. The procedure stops
after at most `n` additions (`pdRun_stable`, `predamp_eq`).
-/

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Lax185574Proofs.Chain.Ram

open Finset Lax185574Proofs.Conversions.Ram Lax185574Proofs.Chain

variable {n : ℕ}

open Classical in
/-- The least `v < n` with `p v`, if there is one. -/
noncomputable def firstN (n : ℕ) (p : ℕ → Prop) : Option ℕ :=
  if ∃ v < n, p v then some (leastBelow p n n) else none

theorem firstN_eq_some {p : ℕ → Prop} {w : ℕ} :
    firstN n p = some w ↔ w < n ∧ p w ∧ ∀ v < w, ¬ p v := by
  classical
  unfold firstN
  split_ifs with h
  · obtain ⟨h1, h2, h3⟩ := leastBelow_spec (d := n) h
    simp only [Option.some.injEq]
    constructor
    · rintro rfl; exact ⟨h1, h2, h3⟩
    · rintro ⟨hw, hpw, hmin⟩
      rcases lt_trichotomy (leastBelow p n n) w with hlt | heq | hgt
      · exact absurd h2 (hmin _ hlt)
      · exact heq
      · exact absurd hpw (h3 _ hgt)
  · simp only [false_iff]
    rintro ⟨hw, hpw, -⟩; exact h ⟨w, hw, hpw⟩

theorem firstN_eq_none {p : ℕ → Prop} : firstN n p = none ↔ ∀ v < n, ¬ p v := by
  classical
  unfold firstN
  split_ifs with h
  · simp only [false_iff, not_forall, not_not]
    obtain ⟨v, hv, hp⟩ := h; exact ⟨v, hv, hp⟩
  · simp only [true_iff]; intro v hv hp; exact h ⟨v, hv, hp⟩

theorem firstN_congr {p p' : ℕ → Prop} (h : ∀ v < n, (p v ↔ p' v)) : firstN n p = firstN n p' := by
  classical
  unfold firstN
  have he : (∃ v < n, p v) ↔ (∃ v < n, p' v) :=
    ⟨fun ⟨v, hv, hp⟩ => ⟨v, hv, (h v hv).1 hp⟩, fun ⟨v, hv, hp⟩ => ⟨v, hv, (h v hv).2 hp⟩⟩
  by_cases hp : ∃ v < n, p v
  · rw [if_pos hp, if_pos (he.1 hp), leastBelow_congr h]
  · rw [if_neg hp, if_neg (fun h' => hp (he.2 h'))]

theorem map_find?_finRange' (p : Fin n → Prop) [DecidablePred p] :
    ((List.finRange n).find? fun w => decide (p w)).map Fin.val =
      firstN n (fun v => ∃ h : v < n, p ⟨v, h⟩) := by
  rw [map_find?_finRange]; unfold firstN; split_ifs <;> rfl

variable (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (o : VOrder (Fin n)) (r : ℕ)
  (A : Finset (Fin n)) (q κ : ℕ)

/-- The step of the procedure, on numbers. -/
theorem pdStep_val (S : Finset (Fin n)) :
    (pdStep G (tpP G r) o A q κ S).map Fin.val =
      ((firstN n (fun v => ∃ h : v < n, Rule1 G (tpP G r) o A q κ S ⟨v, h⟩)) <|>
      ((firstN n (fun v => ∃ h : v < n, Rule2 G (tpP G r) o A q κ S ⟨v, h⟩)) <|>
      (firstN n (fun v => ∃ h : v < n, Rule3 (tpP G r) o A q κ S ⟨v, h⟩)))) := by
  unfold pdStep
  rw [Fin.sort_univ, ← map_find?_finRange', ← map_find?_finRange', ← map_find?_finRange']
  cases (List.finRange n).find? fun w => decide (Rule1 G (tpP G r) o A q κ S w) <;>
    cases (List.finRange n).find? fun w => decide (Rule2 G (tpP G r) o A q κ S w) <;>
    cases (List.finRange n).find? fun w => decide (Rule3 (tpP G r) o A q κ S w) <;> rfl

variable {G o r A q κ}

theorem pdRun_stable {T : Finset (Fin n)} (h : pdStep G (tpP G r) o A q κ T = none) (f : ℕ) :
    pdRun G (tpP G r) o A q κ f T = T := by
  cases f with
  | zero => rfl
  | succ f => unfold pdRun; rw [h]

theorem pdRun_add (a b : ℕ) (S : Finset (Fin n)) :
    pdRun G (tpP G r) o A q κ (a + b) S =
      pdRun G (tpP G r) o A q κ b (pdRun G (tpP G r) o A q κ a S) := by
  induction a generalizing S with
  | zero => simp only [Nat.zero_add]; rfl
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    cases h : pdStep G (tpP G r) o A q κ S with
    | none =>
      have e1 : pdRun G (tpP G r) o A q κ (a + b + 1) S = S := pdRun_stable h _
      have e2 : pdRun G (tpP G r) o A q κ (a + 1) S = S := pdRun_stable h _
      rw [e1, e2, pdRun_stable h]
    | some w =>
      have e1 : pdRun G (tpP G r) o A q κ (a + b + 1) S =
          pdRun G (tpP G r) o A q κ (a + b) (insert w S) := by
        conv_lhs => unfold pdRun
        rw [h]
      have e2 : pdRun G (tpP G r) o A q κ (a + 1) S =
          pdRun G (tpP G r) o A q κ a (insert w S) := by
        conv_lhs => unfold pdRun
        rw [h]
      rw [e1, e2, ih]

theorem pdRun_succ_of_some {j : ℕ} {w : Fin n}
    (h : pdStep G (tpP G r) o A q κ (pdRun G (tpP G r) o A q κ j ∅) = some w) :
    pdRun G (tpP G r) o A q κ (j + 1) ∅ = insert w (pdRun G (tpP G r) o A q κ j ∅) := by
  rw [pdRun_add j 1]
  generalize pdRun G (tpP G r) o A q κ j ∅ = T at h ⊢
  conv_lhs => unfold pdRun
  rw [h]; rfl

/-- The output of the procedure is any run that stops, with at most
`n + 1` applications. -/
theorem predamp_eq {j : ℕ} (hj : j ≤ n + 1)
    (h : pdStep G (tpP G r) o A q κ (pdRun G (tpP G r) o A q κ j ∅) = none) :
    predamp G (tpP G r) o A q κ = pdRun G (tpP G r) o A q κ j ∅ := by
  unfold predamp
  rw [Fintype.card_fin, show n + 1 = j + (n + 1 - j) by omega, pdRun_add, pdRun_stable h]

/-! ### Monotonicity -/

theorem ham_mono {B B' : Finset (Fin n)} (hBB : B ⊆ B') (w s : Fin n) :
    ham G (tpP G r) o B w s ≤ ham G (tpP G r) o B' w s := by
  have hP := tpP_selector G r
  rw [ham_eq_numCls hP, ham_eq_numCls hP]
  exact numCls_le_of_le (hP.equiv B) (hP.equiv B') fun x _ y _ h => hP.anti hBB x y h

theorem hamN_mono (o : VOrder (Fin n)) {B B' : Finset (Fin n)} (hBB : B ⊆ B') {w s : ℕ} (hw : w < n) (hs : s < n) :
    hamN G (lbl n (tpN G B r)) w s ≤ hamN G (lbl n (tpN G B' r)) w s := by
  have := ham_mono (G := G) (o := o) (r := r) hBB ⟨w, hw⟩ ⟨s, hs⟩
  rwa [ham_eq, ham_eq] at this

theorem betwN_mono (o : VOrder (Fin n)) {B B' : Finset (Fin n)} (hBB : B ⊆ B') {w s : ℕ} (hw : w < n) (hs : s < n) :
    betwN n (posN o) (lbl n (tpN G B r)) w s ≤ betwN n (posN o) (lbl n (tpN G B' r)) w s := by
  have := betw_mono (tpP_selector G r) (o := o) hBB ⟨w, hw⟩ ⟨s, hs⟩
  rwa [betw_eq, betw_eq] at this

end Lax185574Proofs.Chain.Ram
