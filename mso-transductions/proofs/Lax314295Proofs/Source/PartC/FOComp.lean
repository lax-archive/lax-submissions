/- Claim `claim:fo-composition-quantifier-rank`: compositionality of first-order logic over strings,
which is the left-to-right implication of Lemma `lem:k-types-fo-equivalence` in
*Transducers* (M. Bojańczyk).

The book's claim reads: whether a first-order formula `φ(x₁, …, xₙ)` of
quantifier rank `k` holds in a string with distinguished positions
`x₁ < ⋯ < xₙ` depends only on the labels of the distinguished positions and on
the `k`-types of the factors between them.

It is formalised here by the relation `KEquiv k V w fo v go`: the strings `w`
and `v`, with the positions of the variables of the finite set `V` given by the
valuations `fo` and `go`, carry the same information at level `k`.  Rather than
sorting the marked positions, the relation records, for every pair of bounds
(a marked variable, or the beginning/end of the string), the `k`-type of the
factor between them; the factors are the `segP` of
`RequestProject/PartC/FOSeg.lean`.

The main statement is `Transducers.sat_iff_of_kEquiv`, proved by induction on
the formula; the quantifier step is `Transducers.exists_mark`, where the new
marked position of `w` is matched with a position of `v` by transferring the
split of the factor that contains it (`exists_split_of_tp_succ_eq`).
-/
import Lax314295Proofs.Source.PartC.FOSeg
import Lax916827Proofs.Source.PartC.MSODef
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax314295Proofs.Transducers

variable {A : Type}

/-- Membership in `some i` is equality (a convenience for `Option` bounds). -/
private lemma eq_of_mem_some {i j : ℕ} (h : j ∈ (some i : Option ℕ)) : j = i :=
  (Option.mem_some_iff.mp h).symm

/-- Concatenation of two factors around a common letter is compatible with
`k`-types (Lemma `lem:k-types-properties`, congruence). -/
lemma tp_congr_cons (k : ℕ) {x₁ x₂ y₁ y₂ : List A} (a : A)
    (h1 : tp k x₁ = tp k x₂) (h2 : tp k y₁ = tp k y₂) :
    tp k (x₁ ++ a :: y₁) = tp k (x₂ ++ a :: y₂) :=
  tp_congr k _ _ _ _ h1 (tp_congr k [a] [a] y₁ y₂ rfl h2)

/-- Two strings with marked positions carry the same information at level `k`:
the marked positions have the same labels and the same relative order, and the
factors between any two bounds (marked positions or the ends of the string)
have the same `k`-types. -/
structure KEquiv (k : ℕ) (V : Finset ℕ) (w : List A) (fo : ℕ → ℕ)
    (v : List A) (go : ℕ → ℕ) : Prop where
  /-- The marked positions of `w` are positions of `w`. -/
  lt_w : ∀ i ∈ V, fo i < w.length
  /-- The marked positions of `v` are positions of `v`. -/
  lt_v : ∀ i ∈ V, go i < v.length
  /-- Corresponding marked positions carry the same letter. -/
  lab : ∀ i ∈ V, w[fo i]? = v[go i]?
  /-- Corresponding marked positions are in the same relative order. -/
  ord : ∀ i ∈ V, ∀ j ∈ V, (fo i ≤ fo j ↔ go i ≤ go j)
  /-- Corresponding factors have the same `k`-type. -/
  seg : ∀ b c : Option ℕ, (∀ i ∈ b, i ∈ V) → (∀ j ∈ c, j ∈ V) →
    (∀ i ∈ b, ∀ j ∈ c, fo i ≤ fo j) →
    tp k (segP w (b.map fo) (c.map fo)) = tp k (segP v (b.map go) (c.map go))

namespace KEquiv

variable {k : ℕ} {V W : Finset ℕ} {w v : List A} {fo go : ℕ → ℕ}

/-- The relation is symmetric. -/
lemma symm (H : KEquiv k V w fo v go) : KEquiv k V v go w fo where
  lt_w := H.lt_v
  lt_v := H.lt_w
  lab := fun i hi => (H.lab i hi).symm
  ord := fun i hi j hj => (H.ord i hi j hj).symm
  seg := fun b c hb hc hord =>
    (H.seg b c hb hc (fun i hi j hj => (H.ord i (hb i hi) j (hc j hj)).mpr (hord i hi j hj))).symm

/-- The relation only speaks about the variables of `V`. -/
lemma mono (H : KEquiv k V w fo v go) (hW : W ⊆ V) : KEquiv k W w fo v go where
  lt_w := fun i hi => H.lt_w i (hW hi)
  lt_v := fun i hi => H.lt_v i (hW hi)
  lab := fun i hi => H.lab i (hW hi)
  ord := fun i hi j hj => H.ord i (hW hi) j (hW hj)
  seg := fun b c hb hc hord =>
    H.seg b c (fun i hi => hW (hb i hi)) (fun j hj => hW (hc j hj)) hord

/-- Level `k + 1` implies level `k` (refinement, Lemma `lem:k-types-properties`). -/
lemma refine (H : KEquiv (k + 1) V w fo v go) : KEquiv k V w fo v go where
  lt_w := H.lt_w
  lt_v := H.lt_v
  lab := H.lab
  ord := H.ord
  seg := fun b c hb hc hord => tp_refine k _ _ (H.seg b c hb hc hord)

/-- The whole strings have the same `k`-type. -/
lemma tp_eq (H : KEquiv k V w fo v go) : tp k w = tp k v := by
  simpa using H.seg none none (by simp) (by simp) (by simp)

end KEquiv

/-- Bookkeeping for the quantifier step: the conditions to be checked when a new
marked position is added. -/
lemma kEquiv_insert {k : ℕ} {V : Finset ℕ} {w v : List A} {fo go : ℕ → ℕ}
    (H : KEquiv (k + 1) V w fo v go) {x : ℕ} (hx : x ∉ V) {p q : ℕ}
    (hpw : p < w.length) (hqv : q < v.length) (hlab : w[p]? = v[q]?)
    (hord : ∀ i ∈ V, (fo i ≤ p ↔ go i ≤ q) ∧ (p ≤ fo i ↔ q ≤ go i))
    (hleft : ∀ b : Option ℕ, (∀ i ∈ b, i ∈ V) → (∀ i ∈ b, fo i ≤ p) →
      tp k (segP w (b.map fo) (some p)) = tp k (segP v (b.map go) (some q)))
    (hright : ∀ c : Option ℕ, (∀ j ∈ c, j ∈ V) → (∀ j ∈ c, p ≤ fo j) →
      tp k (segP w (some p) (c.map fo)) = tp k (segP v (some q) (c.map go))) :
    KEquiv k (insert x V) w (Function.update fo x p) v (Function.update go x q) := by
  set fo' := Function.update fo x p with hfo'def
  set go' := Function.update go x q with hgo'def
  have hfoV : ∀ i, i ∈ V → fo' i = fo i := by
    intro i hi
    have hne : i ≠ x := by rintro rfl; exact hx hi
    simp [hfo'def, Function.update_of_ne hne]
  have hgoV : ∀ i, i ∈ V → go' i = go i := by
    intro i hi
    have hne : i ≠ x := by rintro rfl; exact hx hi
    simp [hgo'def, Function.update_of_ne hne]
  have hfox : fo' x = p := by simp [hfo'def]
  have hgox : go' x = q := by simp [hgo'def]
  have hcase : ∀ i ∈ insert x V,
      (fo' i = p ∧ go' i = q) ∨ (i ∈ V ∧ fo' i = fo i ∧ go' i = go i) := by
    intro i hi
    by_cases hiV : i ∈ V
    · exact Or.inr ⟨hiV, hfoV i hiV, hgoV i hiV⟩
    · have hix : i = x := by
        rcases Finset.mem_insert.mp hi with h | h
        · exact h
        · exact absurd h hiV
      subst hix
      exact Or.inl ⟨hfox, hgox⟩
  have hdcase : ∀ d : Option ℕ, (∀ i ∈ d, i ∈ insert x V) →
      (d = some x ∧ d.map fo' = some p ∧ d.map go' = some q) ∨
        ((∀ i ∈ d, i ∈ V) ∧ d.map fo' = d.map fo ∧ d.map go' = d.map go) := by
    intro d hd
    cases d with
    | none => exact Or.inr ⟨by simp, rfl, rfl⟩
    | some i =>
        by_cases hiV : i ∈ V
        · refine Or.inr ⟨?_, ?_, ?_⟩
          · intro j hj
            obtain rfl := Option.mem_some_iff.mp hj
            assumption
          · simp [hfoV i hiV]
          · simp [hgoV i hiV]
        · have hix : i = x := by
            rcases Finset.mem_insert.mp (hd i rfl) with h | h
            · exact h
            · exact absurd h hiV
          subst hix
          exact Or.inl ⟨rfl, by simp [hfox], by simp [hgox]⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rcases hcase i hi with ⟨h1, _⟩ | ⟨hiV, h1, _⟩
    · rw [h1]; exact hpw
    · rw [h1]; exact H.lt_w i hiV
  · intro i hi
    rcases hcase i hi with ⟨_, h2⟩ | ⟨hiV, _, h2⟩
    · rw [h2]; exact hqv
    · rw [h2]; exact H.lt_v i hiV
  · intro i hi
    rcases hcase i hi with ⟨h1, h2⟩ | ⟨hiV, h1, h2⟩
    · rw [h1, h2]; exact hlab
    · rw [h1, h2]; exact H.lab i hiV
  · intro i hi j hj
    rcases hcase i hi with ⟨hi1, hi2⟩ | ⟨hiV, hi1, hi2⟩ <;>
      rcases hcase j hj with ⟨hj1, hj2⟩ | ⟨hjV, hj1, hj2⟩ <;>
        rw [hi1, hi2, hj1, hj2]
    · simp
    · exact (hord j hjV).2
    · exact (hord i hiV).1
    · exact H.ord i hiV j hjV
  · intro b c hb hc hbc
    rcases hdcase b hb with ⟨rfl, hb1, hb2⟩ | ⟨hbV, hb1, hb2⟩
    · rcases hdcase c hc with ⟨rfl, hc1, hc2⟩ | ⟨hcV, hc1, hc2⟩
      · simp only [hb1, hb2, segP_self]
      · rw [hb1, hb2, hc1, hc2]
        refine hright c hcV (fun j hj => ?_)
        have hle := hbc x rfl j hj
        rwa [hfox, hfoV j (hcV j hj)] at hle
    · rcases hdcase c hc with ⟨rfl, hc1, hc2⟩ | ⟨hcV, hc1, hc2⟩
      · rw [hb1, hb2, hc1, hc2]
        refine hleft b hbV (fun i hi => ?_)
        have hle := hbc i hi x rfl
        rwa [hfox, hfoV i (hbV i hi)] at hle
      · rw [hb1, hb2, hc1, hc2]
        refine tp_refine k _ _ (H.seg b c hbV hcV (fun i hi j hj => ?_))
        have hle := hbc i hi j hj
        rwa [hfoV i (hbV i hi), hfoV j (hcV j hj)] at hle

/-- The quantifier step of Claim `claim:fo-composition-quantifier-rank`: a new marked position of `w`
can be matched by a marked position of `v`, at the cost of decreasing the level by one. -/
theorem exists_mark {k : ℕ} {V : Finset ℕ} {w v : List A} {fo go : ℕ → ℕ}
    (H : KEquiv (k + 1) V w fo v go) {x : ℕ} (hx : x ∉ V) {p : ℕ} (hp : p < w.length) :
    ∃ q, q < v.length ∧
      KEquiv k (insert x V) w (Function.update fo x p) v (Function.update go x q) := by
  by_cases hmark : ∃ i ∈ V, fo i = p
  · -- the new position is already marked
    obtain ⟨i₀, hi₀, hfi₀⟩ := hmark
    refine ⟨go i₀, H.lt_v i₀ hi₀, kEquiv_insert H hx hp (H.lt_v i₀ hi₀) ?_ ?_ ?_ ?_⟩
    · rw [← hfi₀]; exact H.lab i₀ hi₀
    · intro i hi
      constructor
      · rw [← hfi₀]; exact H.ord i hi i₀ hi₀
      · rw [← hfi₀]; exact H.ord i₀ hi₀ i hi
    · intro b hb hbp
      have h1 : (some i₀).map fo = some p := by simp [hfi₀]
      have h2 : (some i₀).map go = some (go i₀) := by simp
      rw [← h1, ← h2]
      refine tp_refine k _ _ (H.seg b (some i₀) hb
        (by intro j hj; obtain rfl := eq_of_mem_some hj; exact hi₀) ?_)
      intro i hi j hj
      obtain rfl := eq_of_mem_some hj
      rw [hfi₀]; exact hbp i hi
    · intro c hc hpc
      have h1 : (some i₀).map fo = some p := by simp [hfi₀]
      have h2 : (some i₀).map go = some (go i₀) := by simp
      rw [← h1, ← h2]
      refine tp_refine k _ _ (H.seg (some i₀) c
        (by intro j hj; obtain rfl := eq_of_mem_some hj; exact hi₀) hc ?_)
      intro i hi j hj
      obtain rfl := eq_of_mem_some hi
      rw [hfi₀]; exact hpc j hj
  · push_neg at hmark
    -- the bound to the left of the new position
    obtain ⟨l, hlV, hlp, hlmax⟩ : ∃ l : Option ℕ, (∀ i ∈ l, i ∈ V) ∧ (∀ i ∈ l, fo i < p) ∧
        (∀ i ∈ V, fo i < p → ∃ i₀ ∈ l, fo i ≤ fo i₀) := by
      rcases Finset.eq_empty_or_nonempty (V.filter (fun i => fo i < p)) with hL | hL
      · refine ⟨none, by simp, by simp, fun i hi hlt => ?_⟩
        have : i ∈ V.filter (fun i => fo i < p) := Finset.mem_filter.mpr ⟨hi, hlt⟩
        rw [hL] at this
        exact absurd this (Finset.notMem_empty i)
      · obtain ⟨i₀, hi₀, hmax⟩ := Finset.exists_max_image _ fo hL
        rw [Finset.mem_filter] at hi₀
        exact ⟨some i₀, by intro i hi; obtain rfl := eq_of_mem_some hi; exact hi₀.1,
          by intro i hi; obtain rfl := eq_of_mem_some hi; exact hi₀.2,
          fun i hi hlt => ⟨i₀, rfl, hmax i (Finset.mem_filter.mpr ⟨hi, hlt⟩)⟩⟩
    -- the bound to the right of the new position
    obtain ⟨r, hrV, hrp, hrmin⟩ : ∃ r : Option ℕ, (∀ j ∈ r, j ∈ V) ∧ (∀ j ∈ r, p < fo j) ∧
        (∀ j ∈ V, p < fo j → ∃ j₀ ∈ r, fo j₀ ≤ fo j) := by
      rcases Finset.eq_empty_or_nonempty (V.filter (fun j => p < fo j)) with hR | hR
      · refine ⟨none, by simp, by simp, fun j hj hlt => ?_⟩
        have : j ∈ V.filter (fun j => p < fo j) := Finset.mem_filter.mpr ⟨hj, hlt⟩
        rw [hR] at this
        exact absurd this (Finset.notMem_empty j)
      · obtain ⟨j₀, hj₀, hmin⟩ := Finset.exists_min_image _ fo hR
        rw [Finset.mem_filter] at hj₀
        exact ⟨some j₀, by intro j hj; obtain rfl := eq_of_mem_some hj; exact hj₀.1,
          by intro j hj; obtain rfl := eq_of_mem_some hj; exact hj₀.2,
          fun j hj hlt => ⟨j₀, rfl, hmin j (Finset.mem_filter.mpr ⟨hj, hlt⟩)⟩⟩
    -- the factor of `w` containing the new position, and its counterpart in `v`
    have hlo_w : loB (l.map fo) ≤ p := by
      cases l with
      | none => exact Nat.zero_le p
      | some i₀ => exact hlp i₀ rfl
    have hhi_w : p < hiB w (r.map fo) := by
      cases r with
      | none => exact hp
      | some j₀ => exact hrp j₀ rfl
    have hhi_w_le : hiB w (r.map fo) ≤ w.length := by
      cases r with
      | none => exact le_rfl
      | some j₀ => exact le_of_lt (H.lt_w j₀ (hrV j₀ rfl))
    have hhi_v_le : hiB v (r.map go) ≤ v.length := by
      cases r with
      | none => exact le_rfl
      | some j₀ => exact le_of_lt (H.lt_v j₀ (hrV j₀ rfl))
    set g := segP w (l.map fo) (r.map fo) with hg
    set g' := segP v (l.map go) (r.map go) with hg'
    have hgg' : tp (k + 1) g = tp (k + 1) g' :=
      H.seg l r hlV hrV (fun i hi j hj => le_of_lt (lt_trans (hlp i hi) (hrp j hj)))
    have hglen : g.length = hiB w (r.map fo) - loB (l.map fo) := segP_length w _ _ hhi_w_le
    have hp' : p - loB (l.map fo) < g.length := by rw [hglen]; omega
    obtain ⟨q', hq'len, hq'lab, hq'take, hq'drop⟩ :=
      exists_split_of_tp_succ_eq k g g' hgg' (p - loB (l.map fo)) hp'
    have hg'len : g'.length = hiB v (r.map go) - loB (l.map go) := segP_length v _ _ hhi_v_le
    set q := loB (l.map go) + q' with hq
    have hq_hi : q < hiB v (r.map go) := by rw [hg'len] at hq'len; omega
    have hqv : q < v.length := lt_of_lt_of_le hq_hi hhi_v_le
    have hlo_v : loB (l.map go) ≤ q := by omega
    -- the letters agree
    have hlab : w[p]? = v[q]? := by
      have h1 : g[p - loB (l.map fo)]? = w[p]? := by
        rw [segP_getElem? w _ _ _ hp']
        congr 1
        omega
      have h2 : g'[q']? = v[q]? := by
        rw [segP_getElem? v _ _ _ hq'len]
      rw [← h1, ← h2, hq'lab]
    -- the two halves of the factor
    have hkeyL : tp k (segP w (l.map fo) (some p)) = tp k (segP v (l.map go) (some q)) := by
      have e1 : g.take (p - loB (l.map fo)) = segP w (l.map fo) (some p) := by
        rw [segP_take w _ _ _ (le_of_lt hp')]
        congr 2
        omega
      have e2 : g'.take q' = segP v (l.map go) (some q) := by
        rw [segP_take v _ _ _ (le_of_lt hq'len)]
      rw [← e1, ← e2]; exact hq'take
    have hkeyR : tp k (segP w (some p) (r.map fo)) = tp k (segP v (some q) (r.map go)) := by
      have e1 : g.drop (p - loB (l.map fo) + 1) = segP w (some p) (r.map fo) := by
        rw [segP_drop w _ _ (p - loB (l.map fo))]
        congr 2
        omega
      have e2 : g'.drop (q' + 1) = segP v (some q) (r.map go) := by
        rw [segP_drop v _ _ q']
      rw [← e1, ← e2]; exact hq'drop
    -- the order of the marks
    have hordL : ∀ i ∈ V, fo i < p → go i < q := by
      intro i hi hlt
      obtain ⟨i₀, hi₀l, hle⟩ := hlmax i hi hlt
      have h1 : go i ≤ go i₀ := (H.ord i hi i₀ (hlV i₀ hi₀l)).mp hle
      have h2 : loB (l.map go) = go i₀ + 1 := by
        cases l with
        | none => exact absurd hi₀l (by simp)
        | some j => cases hi₀l; simp [loB]
      omega
    have hordR : ∀ j ∈ V, p < fo j → q < go j := by
      intro j hj hlt
      obtain ⟨j₀, hj₀r, hle⟩ := hrmin j hj hlt
      have h1 : go j₀ ≤ go j := (H.ord j₀ (hrV j₀ hj₀r) j hj).mp hle
      have h2 : hiB v (r.map go) = go j₀ := by
        cases r with
        | none => exact absurd hj₀r (by simp)
        | some j' => cases hj₀r; simp [hiB]
      omega
    have hord : ∀ i ∈ V, (fo i ≤ p ↔ go i ≤ q) ∧ (p ≤ fo i ↔ q ≤ go i) := by
      intro i hi
      rcases lt_trichotomy (fo i) p with hlt | heq | hgt
      · have := hordL i hi hlt
        exact ⟨by omega, by omega⟩
      · exact absurd heq (hmark i hi)
      · have := hordR i hi hgt
        exact ⟨by omega, by omega⟩
    -- the factor to the left of the new position
    have hleft : ∀ b : Option ℕ, (∀ i ∈ b, i ∈ V) → (∀ i ∈ b, fo i ≤ p) →
        tp k (segP w (b.map fo) (some p)) = tp k (segP v (b.map go) (some q)) := by
      intro b hbV hbp
      cases l with
      | none =>
          have hbnone : b = none := by
            cases b with
            | none => rfl
            | some i =>
                have hlt : fo i < p := lt_of_le_of_ne (hbp i rfl) (hmark i (hbV i rfl))
                obtain ⟨i₀, hi₀, _⟩ := hlmax i (hbV i rfl) hlt
                exact absurd hi₀ (by simp)
          subst hbnone
          exact hkeyL
      | some i₀ =>
          have hi₀V : i₀ ∈ V := hlV i₀ rfl
          have hi₀p : fo i₀ < p := hlp i₀ rfl
          have hi₀q : go i₀ < q := hordL i₀ hi₀V hi₀p
          have hb_le : ∀ i ∈ b, fo i ≤ fo i₀ := by
            intro i hi
            have hlt : fo i < p := lt_of_le_of_ne (hbp i hi) (hmark i (hbV i hi))
            obtain ⟨i₁, hi₁, hle⟩ := hlmax i (hbV i hi) hlt
            obtain rfl : i₁ = i₀ := (Option.mem_some_iff.mp hi₁).symm
            exact hle
          by_cases hsame : ∃ i, b = some i ∧ fo i = fo i₀
          · obtain ⟨i, rfl, hfi⟩ := hsame
            have hgi : go i = go i₀ := by
              have h1 : go i ≤ go i₀ := (H.ord i (hbV i rfl) i₀ hi₀V).mp (le_of_eq hfi)
              have h2 : go i₀ ≤ go i := (H.ord i₀ hi₀V i (hbV i rfl)).mp (le_of_eq hfi.symm)
              omega
            simp only [Option.map_some, hfi, hgi]
            exact hkeyL
          · have hbfo : loB (b.map fo) ≤ fo i₀ := by
              cases b with
              | none => exact Nat.zero_le _
              | some i =>
                  have hne : fo i ≠ fo i₀ := fun h => hsame ⟨i, rfl, h⟩
                  have := hb_le i rfl
                  simp only [Option.map_some, loB]
                  omega
            have hbgo : loB (b.map go) ≤ go i₀ := by
              cases b with
              | none => exact Nat.zero_le _
              | some i =>
                  have hne : fo i ≠ fo i₀ := fun h => hsame ⟨i, rfl, h⟩
                  have hle := hb_le i rfl
                  have h1 : go i ≤ go i₀ := (H.ord i (hbV i rfl) i₀ hi₀V).mp hle
                  have hne' : go i ≠ go i₀ := by
                    intro h
                    exact hne (le_antisymm hle
                      ((H.ord i₀ hi₀V i (hbV i rfl)).mpr (le_of_eq h.symm)))
                  simp only [Option.map_some, loB]
                  omega
            obtain ⟨a, ha⟩ : ∃ a : A, w[fo i₀]? = some a :=
              ⟨w[fo i₀]'(H.lt_w i₀ hi₀V), List.getElem?_eq_getElem (H.lt_w i₀ hi₀V)⟩
            have ha' : v[go i₀]? = some a := by rw [← H.lab i₀ hi₀V]; exact ha
            have hsplit_w : segP w (b.map fo) (some p)
                = segP w (b.map fo) (some (fo i₀)) ++ a :: segP w (some (fo i₀)) (some p) :=
              segP_split ha hbfo (by simpa [hiB] using hi₀p)
            have hsplit_v : segP v (b.map go) (some q)
                = segP v (b.map go) (some (go i₀)) ++ a :: segP v (some (go i₀)) (some q) :=
              segP_split ha' hbgo (by simpa [hiB] using hi₀q)
            rw [hsplit_w, hsplit_v]
            refine tp_congr_cons k a ?_ hkeyL
            have hseg := H.seg b (some i₀) hbV (fun j hj => by
              obtain rfl : j = i₀ := (Option.mem_some_iff.mp hj).symm
              exact hi₀V) (fun i hi j hj => by
              obtain rfl : j = i₀ := (Option.mem_some_iff.mp hj).symm
              exact hb_le i hi)
            simpa using tp_refine k _ _ hseg
    -- the factor to the right of the new position
    have hright : ∀ c : Option ℕ, (∀ j ∈ c, j ∈ V) → (∀ j ∈ c, p ≤ fo j) →
        tp k (segP w (some p) (c.map fo)) = tp k (segP v (some q) (c.map go)) := by
      intro c hcV hpc
      cases r with
      | none =>
          have hcnone : c = none := by
            cases c with
            | none => rfl
            | some j =>
                have hlt : p < fo j :=
                  lt_of_le_of_ne (hpc j rfl) (fun h => hmark j (hcV j rfl) h.symm)
                obtain ⟨j₀, hj₀, _⟩ := hrmin j (hcV j rfl) hlt
                exact absurd hj₀ (by simp)
          subst hcnone
          exact hkeyR
      | some j₀ =>
          have hj₀V : j₀ ∈ V := hrV j₀ rfl
          have hj₀p : p < fo j₀ := hrp j₀ rfl
          have hj₀q : q < go j₀ := hordR j₀ hj₀V hj₀p
          have hc_le : ∀ j ∈ c, fo j₀ ≤ fo j := by
            intro j hj
            have hlt : p < fo j := lt_of_le_of_ne (hpc j hj) (fun h => hmark j (hcV j hj) h.symm)
            obtain ⟨j₁, hj₁, hle⟩ := hrmin j (hcV j hj) hlt
            obtain rfl : j₁ = j₀ := (Option.mem_some_iff.mp hj₁).symm
            exact hle
          by_cases hsame : ∃ j, c = some j ∧ fo j = fo j₀
          · obtain ⟨j, rfl, hfj⟩ := hsame
            have hgj : go j = go j₀ := by
              have h1 : go j ≤ go j₀ := (H.ord j (hcV j rfl) j₀ hj₀V).mp (le_of_eq hfj)
              have h2 : go j₀ ≤ go j := (H.ord j₀ hj₀V j (hcV j rfl)).mp (le_of_eq hfj.symm)
              omega
            simp only [Option.map_some, hfj, hgj]
            exact hkeyR
          · have hcfo : fo j₀ < hiB w (c.map fo) := by
              cases c with
              | none => simpa [hiB] using H.lt_w j₀ hj₀V
              | some j =>
                  have hne : fo j ≠ fo j₀ := fun h => hsame ⟨j, rfl, h⟩
                  have := hc_le j rfl
                  simp only [Option.map_some, hiB]
                  omega
            have hcgo : go j₀ < hiB v (c.map go) := by
              cases c with
              | none => simpa [hiB] using H.lt_v j₀ hj₀V
              | some j =>
                  have hne : fo j ≠ fo j₀ := fun h => hsame ⟨j, rfl, h⟩
                  have hle := hc_le j rfl
                  have h1 : go j₀ ≤ go j := (H.ord j₀ hj₀V j (hcV j rfl)).mp hle
                  have hne' : go j ≠ go j₀ := by
                    intro h
                    exact hne (le_antisymm ((H.ord j (hcV j rfl) j₀ hj₀V).mpr (le_of_eq h)) hle)
                  simp only [Option.map_some, hiB]
                  omega
            obtain ⟨a, ha⟩ : ∃ a : A, w[fo j₀]? = some a :=
              ⟨w[fo j₀]'(H.lt_w j₀ hj₀V), List.getElem?_eq_getElem (H.lt_w j₀ hj₀V)⟩
            have ha' : v[go j₀]? = some a := by rw [← H.lab j₀ hj₀V]; exact ha
            have hsplit_w : segP w (some p) (c.map fo)
                = segP w (some p) (some (fo j₀)) ++ a :: segP w (some (fo j₀)) (c.map fo) :=
              segP_split ha (by simpa [loB] using hj₀p) hcfo
            have hsplit_v : segP v (some q) (c.map go)
                = segP v (some q) (some (go j₀)) ++ a :: segP v (some (go j₀)) (c.map go) :=
              segP_split ha' (by simpa [loB] using hj₀q) hcgo
            rw [hsplit_w, hsplit_v]
            refine tp_congr_cons k a hkeyR ?_
            have hseg := H.seg (some j₀) c (fun j hj => by
              obtain rfl : j = j₀ := (Option.mem_some_iff.mp hj).symm
              exact hj₀V) hcV (fun i hi j hj => by
              obtain rfl : i = j₀ := (Option.mem_some_iff.mp hi).symm
              exact hc_le j hj)
            simpa using tp_refine k _ _ hseg
    exact ⟨q, hqv, kEquiv_insert H hx hp hqv hlab hord hleft hright⟩

/-- **Claim `claim:fo-composition-quantifier-rank`.**  Whether a first-order formula of quantifier rank
at most `k` holds in a string with marked positions depends only on the level-`k` information about
the marked positions. -/
theorem sat_iff_of_kEquiv : ∀ (φ : MSO A) {k : ℕ} {V : Finset ℕ} {w v : List A}
    {fo go : ℕ → ℕ} {so so' : ℕ → Set ℕ}, φ.IsFO → φ.qrank ≤ k → φ.freeFO ⊆ (V : Set ℕ) →
    KEquiv k V w fo v go → (MSO.Sat w fo so φ ↔ MSO.Sat v go so' φ) := by
  intro φ
  induction φ with
  | le i j =>
      intro k V w v fo go so so' _ _ hfree H
      exact H.ord i (Finset.mem_coe.mp (hfree (Or.inl rfl))) j
        (Finset.mem_coe.mp (hfree (Or.inr rfl)))
  | lab a i =>
      intro k V w v fo go so so' _ _ hfree H
      show (w[fo i]? = some a) ↔ (v[go i]? = some a)
      rw [H.lab i (Finset.mem_coe.mp (hfree rfl))]
  | mem i j => intro k V w v fo go so so' h; exact h.elim
  | not φ ih =>
      intro k V w v fo go so so' hfo hq hfree H
      show ¬ MSO.Sat w fo so φ ↔ ¬ MSO.Sat v go so' φ
      rw [ih hfo hq hfree H]
  | and φ ψ ihφ ihψ =>
      intro k V w v fo go so so' hfo hq hfree H
      show (MSO.Sat w fo so φ ∧ MSO.Sat w fo so ψ) ↔ (MSO.Sat v go so' φ ∧ MSO.Sat v go so' ψ)
      rw [ihφ hfo.1 (le_trans (le_max_left _ _) hq) (fun i hi => hfree (Or.inl hi)) H,
        ihψ hfo.2 (le_trans (le_max_right _ _) hq) (fun i hi => hfree (Or.inr hi)) H]
  | or φ ψ ihφ ihψ =>
      intro k V w v fo go so so' hfo hq hfree H
      show (MSO.Sat w fo so φ ∨ MSO.Sat w fo so ψ) ↔ (MSO.Sat v go so' φ ∨ MSO.Sat v go so' ψ)
      rw [ihφ hfo.1 (le_trans (le_max_left _ _) hq) (fun i hi => hfree (Or.inl hi)) H,
        ihψ hfo.2 (le_trans (le_max_right _ _) hq) (fun i hi => hfree (Or.inr hi)) H]
  | exFO i ψ ih =>
      intro k V w v fo go so so' hfo hq hfree H
      have hk : ψ.qrank + 1 ≤ k := hq
      obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
      have hqψ : ψ.qrank ≤ k' := by omega
      have H₀ : KEquiv (k' + 1) (V.erase i) w fo v go := H.mono (Finset.erase_subset _ _)
      have hfree' : ψ.freeFO ⊆ ((insert i (V.erase i) : Finset ℕ) : Set ℕ) := by
        intro j hj
        by_cases hji : j = i
        · subst hji; simp
        · have hjV : j ∈ V := Finset.mem_coe.mp (hfree ⟨hj, hji⟩)
          simp [hjV, hji]
      show (∃ p < w.length, MSO.Sat w (Function.update fo i p) so ψ) ↔
        (∃ q < v.length, MSO.Sat v (Function.update go i q) so' ψ)
      constructor
      · rintro ⟨p, hp, hsat⟩
        obtain ⟨q, hqv, HK⟩ := exists_mark H₀ (Finset.notMem_erase i V) hp
        exact ⟨q, hqv, (ih hfo hqψ hfree' HK).mp hsat⟩
      · rintro ⟨q, hq', hsat⟩
        obtain ⟨p, hpw, HK⟩ := exists_mark H₀.symm (Finset.notMem_erase i V) hq'
        exact ⟨p, hpw, (ih hfo hqψ hfree' HK.symm).mpr hsat⟩
  | exSO i φ _ => intro k V w v fo go so so' h; exact h.elim

/-- Strings with the same `k`-type satisfy the same first-order sentences of
quantifier rank at most `k`.  This is the left-to-right implication of
Lemma `lem:k-types-fo-equivalence`. -/
theorem sat_iff_of_tp_eq {k : ℕ} {w v : List A} (h : tp k w = tp k v) (φ : MSO A)
    (hfo : φ.IsFO) (hq : φ.qrank ≤ k) (hfree : φ.freeFO = ∅)
    (fo go : ℕ → ℕ) (so so' : ℕ → Set ℕ) : MSO.Sat w fo so φ ↔ MSO.Sat v go so' φ := by
  refine sat_iff_of_kEquiv φ (V := (∅ : Finset ℕ)) hfo hq (by rw [hfree]; exact Set.empty_subset _)
    ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Finset.notMem_empty, IsEmpty.forall_iff, imp_false, forall_const]
  intro b c hb hc _
  have hbn : b = none := by cases b with
    | none => rfl
    | some i => exact absurd (hb i rfl) (by simp)
  have hcn : c = none := by cases c with
    | none => rfl
    | some j => exact absurd (hc j rfl) (by simp)
  subst hbn; subst hcn
  simpa using h

end Lax314295Proofs.Transducers
