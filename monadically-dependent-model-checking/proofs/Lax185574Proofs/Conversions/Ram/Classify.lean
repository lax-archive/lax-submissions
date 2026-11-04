import Lax185574Proofs.Conversions.Ram.Basic

/-!
Labelling every vertex by the least vertex related to it.

`classify arr eqc` stores, for every `v < n`, the least `u < n` with
`R u v` into entry `v` of `arr`, or `n` if there is none. The command
`eqc` tests the relation for the scalars `u` and `v` and leaves `1` or
`0` in `ok`. This is how the programs of the conversions compute the
least vertex of the part of every vertex of a partition: `R` is the
equivalence relation of the partition.
-/

namespace Lax185574Proofs.Conversions.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words

/-- The least `u < k` with `p u`, or `d` if there is none. -/
noncomputable def leastBelow (p : ℕ → Prop) (k d : ℕ) : ℕ :=
  open Classical in if h : ∃ u, u < k ∧ p u then Nat.find h else d

theorem leastBelow_zero (p : ℕ → Prop) (d : ℕ) : leastBelow p 0 d = d := by
  simp [leastBelow]

theorem leastBelow_spec {p : ℕ → Prop} {k d : ℕ} (h : ∃ u, u < k ∧ p u) :
    leastBelow p k d < k ∧ p (leastBelow p k d) ∧ ∀ u < leastBelow p k d, ¬ p u := by
  classical
  simp only [leastBelow, dif_pos h]
  refine ⟨(Nat.find_spec h).1, (Nat.find_spec h).2, fun u hu hpu => ?_⟩
  exact Nat.find_min h hu ⟨by have := (Nat.find_spec h).1; omega, hpu⟩

theorem leastBelow_none {p : ℕ → Prop} {k d : ℕ} (h : ¬ ∃ u, u < k ∧ p u) :
    leastBelow p k d = d := by
  simp [leastBelow, h]

open Classical in
theorem leastBelow_succ (p : ℕ → Prop) {k d : ℕ} (hk : k < d) :
    leastBelow p (k + 1) d =
      if p k ∧ k < leastBelow p k d then k else leastBelow p k d := by
  by_cases h : ∃ u, u < k ∧ p u
  · obtain ⟨h1, h2, h3⟩ := leastBelow_spec (d := d) h
    have h' : ∃ u, u < k + 1 ∧ p u := by obtain ⟨u, hu, hp⟩ := h; exact ⟨u, by omega, hp⟩
    obtain ⟨g1, g2, g3⟩ := leastBelow_spec (d := d) h'
    rw [if_neg (by omega)]
    rcases lt_trichotomy (leastBelow p (k + 1) d) (leastBelow p k d) with hlt | heq | hgt
    · exact absurd g2 (h3 _ hlt)
    · exact heq
    · exact absurd h2 (g3 _ hgt)
  · rw [leastBelow_none h]
    by_cases hp : p k
    · rw [if_pos ⟨hp, hk⟩]
      have h' : ∃ u, u < k + 1 ∧ p u := ⟨k, by omega, hp⟩
      obtain ⟨g1, g2, g3⟩ := leastBelow_spec (d := d) h'
      rcases Nat.lt_succ_iff_lt_or_eq.mp g1 with hlt | heq
      · exact absurd ⟨_, hlt, g2⟩ h
      · exact heq
    · rw [if_neg (fun h => hp h.1)]
      apply leastBelow_none
      rintro ⟨u, hu, hpu⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | rfl
      · exact h ⟨u, hu, hpu⟩
      · exact hp hpu

/-- One round of the inner loop: test `R u v` and keep `u` if it is the
first related vertex. -/
def classifyStep (arr : String) (eqc : Com) : Com :=
  .seq eqc (.ite (.eq (.var "ok") (.lit 1))
    (.ite (.lt (.var "u") (.get arr (.var "v"))) (.store arr (.var "v") (.var "u")) .skip) .skip)

/-- For every `v < n`, store the least `u < n` related to `v` into
entry `v` of `arr`. -/
def classify (arr : String) (eqc : Com) : Com :=
  forUp "v" (.var "n") (.seq (.store arr (.var "v") (.var "n"))
    (forUp "u" (.var "n") (classifyStep arr eqc)))

open Classical in
/-- **Labelling by the least related vertex.** `Ctx` is what `eqc`
needs. It must survive setting `u` and `v` and storing into `arr`. -/
theorem classify_run {B n Ke : ℕ} {arr : String} {eqc : Com} (Ctx : Env → Prop)
    (R : ℕ → ℕ → Prop) (hnB : n + 1 < B)
    (hCn : ∀ τ, Ctx τ → τ.vars "n" = n)
    (hCu : ∀ τ x, Ctx τ → Ctx (τ.setVar "u" x)) (hCv : ∀ τ x, Ctx τ → Ctx (τ.setVar "v" x))
    (hCa : ∀ τ i x, Ctx τ → Ctx (τ.setArr arr i x))
    (heqc : ∀ τ, Ctx τ → τ.vars "u" < n → τ.vars "v" < n →
      ∃ τ', Run B eqc τ τ' Ke ∧ Ctx τ' ∧
        τ'.vars "ok" = ind (R (τ.vars "u") (τ.vars "v")) ∧
        τ'.vars "u" = τ.vars "u" ∧ τ'.vars "v" = τ.vars "v" ∧ τ'.arrs arr = τ.arrs arr)
    {σ : Env} (hσ : Ctx σ) (hlen : (σ.arrs arr).length = n) :
    ∃ σ', Run B (classify arr eqc) σ σ' (n * (n * (Ke + 20) + 17) + 6) ∧ Ctx σ' ∧
      (σ'.arrs arr).length = n ∧
      ∀ v < n, (σ'.arrs arr)[v]? = some (leastBelow (fun u => R u v) n n) := by
  classical
  let O : ℕ → Env → Prop := fun v τ => Ctx τ ∧ (τ.arrs arr).length = n ∧
    ∀ w < v, (τ.arrs arr)[w]? = some (leastBelow (fun u => R u w) n n)
  obtain ⟨σ', hrun, ⟨hC', hl', he'⟩, -⟩ :=
    forUp_run (B := B) (i := "v") (e := .var "n") (N := n) (K := n * (Ke + 20) + 9) O
      (by omega) (fun k _ τ hI _ => by rw [evalB_var (by rw [hCn τ hI.1]; omega), hCn τ hI.1])
      (σ := σ) ⟨hCv _ _ hσ, by simp [hlen], fun w hw => absurd hw (Nat.not_lt_zero _)⟩
      (by
        rintro v hv τ ⟨hC, hl, he⟩ hvv
        have hnτ := hCn τ hC
        set τ0 := τ.setArr arr v n with hτ0
        have hr0 : Run B (.store arr (.var "v") (.var "n")) τ τ0 3 :=
          (Run.store (idx := v) (v := n) (by simp [hvv]; omega) (by simp [hnτ]; omega)
            (by omega)).mono (by simp)
        let I : ℕ → Env → Prop := fun k ρ => Ctx ρ ∧ ρ.vars "v" = v ∧
          (ρ.arrs arr).length = n ∧
          (ρ.arrs arr)[v]? = some (leastBelow (fun u => R u v) k n) ∧
          ∀ w < v, (ρ.arrs arr)[w]? = some (leastBelow (fun u => R u w) n n)
        obtain ⟨ρ, hrunI, ⟨hCρ, hvρ, hlρ, hvρ', hwρ⟩, -⟩ :=
          forUp_run (B := B) (i := "u") (e := .var "n") (N := n) (K := Ke + 12) I
            (by omega) (fun k _ ρ hI _ => by rw [evalB_var (by rw [hCn ρ hI.1]; omega), hCn ρ hI.1])
            (σ := τ0) ⟨hCu _ _ (hCa _ _ _ hC), by simp [hτ0, hvv], by simp [hτ0, hl],
              by simp [hτ0, hl, hv, leastBelow_zero],
              fun w hw => by
                simp only [arrs_setVar, hτ0, arrs_setArr, if_true]
                rw [List.getElem?_set_ne (by omega)]; exact he w hw⟩
            (by
              rintro k hk ρ ⟨hCρ, hvρ, hlρ, hvρ', hwρ⟩ hku
              obtain ⟨ρ1, hr1, hC1, hok1, hu1, hv1, ha1⟩ :=
                heqc ρ hCρ (by omega) (by omega)
              rw [hku, hvρ] at hok1
              have hn1 := hCn ρ1 hC1
              have hget : (ρ1.arrs arr)[v]? = some (leastBelow (fun u => R u v) k n) := by
                rw [ha1]; exact hvρ'
              have hlbB : leastBelow (fun u => R u v) k n < B := by
                by_cases hex : ∃ u, u < k ∧ R u v
                · have := (leastBelow_spec (d := n) hex).1; omega
                · rw [leastBelow_none hex]; omega
              have hsucc := leastBelow_succ (fun u => R u v) (d := n) (k := k) hk
              have hstep : ∃ ρ2, Run B (.ite (.eq (.var "ok") (.lit 1))
                  (.ite (.lt (.var "u") (.get arr (.var "v"))) (.store arr (.var "v") (.var "u"))
                    .skip) .skip) ρ1 ρ2 12 ∧ Ctx ρ2 ∧ ρ2.vars "u" = k ∧
                  ρ2.vars "v" = v ∧ (ρ2.arrs arr).length = n ∧
                  (ρ2.arrs arr)[v]? = some (leastBelow (fun u => R u v) (k + 1) n) ∧
                  ∀ w ≠ v, (ρ2.arrs arr)[w]? = (ρ1.arrs arr)[w]? := by
                by_cases hR : R k v
                · have hok : ρ1.vars "ok" = 1 := by simp [hok1, ind, hR]
                  by_cases hlt : k < leastBelow (fun u => R u v) k n
                  · refine ⟨ρ1.setArr arr v k, (Run.ite_true ?_ (Run.ite_true ?_
                      (Run.store (idx := v) (v := k) ?_ ?_ ?_))).mono (by simp), hCa _ _ _ hC1,
                      by simp [hu1, hku], by simp [hv1, hvρ], by simp [ha1, hlρ], ?_, ?_⟩
                    · rw [eq_lit_evalB (by omega) (by omega)]; simp [hok]
                    · rw [evalB_condLt (evalB_var (by omega))
                        (evalB_get (evalB_var (by omega)) (by rw [hv1, hvρ]; exact hget) hlbB)]
                      simp [hu1, hku, hlt]
                    · simp [hv1, hvρ]; omega
                    · simp [hu1, hku]; omega
                    · rw [ha1, hlρ]; omega
                    · simp only [arrs_setArr, if_true]
                      rw [List.getElem?_set_self (by rw [ha1, hlρ]; omega), hsucc, if_pos ⟨hR, hlt⟩]
                    · intro w hw
                      simp only [arrs_setArr, if_true]
                      rw [List.getElem?_set_ne (Ne.symm hw)]
                  · refine ⟨ρ1, (Run.ite_true ?_ (Run.ite_false ?_ Run.skip)).mono (by simp), hC1,
                      by simp [hu1, hku], by simp [hv1, hvρ], by simp [ha1, hlρ], ?_,
                      fun _ _ => rfl⟩
                    · rw [eq_lit_evalB (by omega) (by omega)]; simp [hok]
                    · rw [evalB_condLt (evalB_var (by omega))
                        (evalB_get (evalB_var (by omega)) (by rw [hv1, hvρ]; exact hget) hlbB)]
                      simp [hu1, hku, hlt]
                    · rw [hget, hsucc, if_neg (fun h => hlt h.2)]
                · have hok : ρ1.vars "ok" = 0 := by simp [hok1, ind, hR]
                  refine ⟨ρ1, (Run.ite_false ?_ Run.skip).mono (by simp), hC1,
                    by simp [hu1, hku], by simp [hv1, hvρ], by simp [ha1, hlρ], ?_,
                    fun _ _ => rfl⟩
                  · rw [eq_lit_evalB (by omega) (by omega)]; simp [hok]
                  · rw [hget, hsucc, if_neg (fun h => hR h.1)]
              obtain ⟨ρ2, hr2, hC2, hu2, hv2, hl2, hvv2, hw2⟩ := hstep
              refine ⟨ρ2, (Run.seq hr1 hr2).mono (by omega), hu2, hCu _ _ hC2, by simp [hv2],
                by simp [hl2], by simpa using hvv2, fun w hw => ?_⟩
              simp only [arrs_setVar]
              rw [hw2 w (by omega), ha1]; exact hwρ w hw)
        refine ⟨ρ, (Run.seq hr0 hrunI).mono (by simp only [size_var]; ring_nf; omega), hvρ,
          hCv _ _ hCρ, by simp [hlρ], fun w hw => ?_⟩
        simp only [arrs_setVar]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hw with hw | rfl
        · exact hwρ w hw
        · exact hvρ')
  exact ⟨σ', hrun.mono (by simp only [size_var]; ring_nf; omega), hC', hl', he'⟩

end Lax185574Proofs.Conversions.Ram
