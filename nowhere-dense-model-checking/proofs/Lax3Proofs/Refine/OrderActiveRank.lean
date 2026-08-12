import Lax3Proofs.RamDriverOrder
import Lax3Proofs.Refine.OrderActiveMath

/-!
# Inverting a compact rank array into active carrier centres

The final compact elimination ranks the member indices `0, ..., mm - 1`.
The active cover, however, reads arena vertices from the level's physical
order array.  This pass performs exactly that seam: for every compact member
`k`, it writes `mem[k]` at compact position `rnk[k]`.  It touches `mm` cells
and leaves the physical tail of the carrier-sized destination alone.
-/

namespace Lax3Proofs.Refine.OrderActiveRank

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib
open Lax3Proofs.RamCover (OrdersBy rankPerm ordersBy_rankPerm)
open Lax3Proofs.RamDriverOrder (exists_preimage_of_inj)
open Lax3Proofs.Refine.OrderActiveMath (activeCentre activeCentre_of_lt)

/-- Invert compact ranks while translating compact member indices back to
arena vertices.  The loop bound is the active count, never the carrier size. -/
def memberOrdCom (dst : String) : Com :=
  .seq (.assign "z" (.lit 0))
    (.while (.lt (.var "z") (.var "mm"))
      (.seq (.store dst (.get "rnk" (.var "z")) (.get "mem" (.var "z")))
        (.assign "z" (.add (.var "z") (.lit 1)))))

/-- The member inversion materializes precisely the compact order lifted
through `Mem`.  Only its first `mm` cells are specified; the destination is
still carrier-sized, so the pass composes directly with the active cover. -/
theorem memberOrdCom_spec {B n mm : ℕ} {R Mem : ℕ → ℕ} (dst : String)
    (hdr : dst ≠ "rnk") (hdm : dst ≠ "mem") (hmn : mm ≤ n) (hnB : n < B)
    (hR : ∀ v < mm, R v < mm)
    (hinj : ∀ v < mm, ∀ w < mm, R v = R w → v = w)
    (hMem : ∀ v < mm, Mem v < n) :
    Spec B
      (fun σ => σ.vars "mm" = mm ∧ σ.arrs "rnk" = arrOf n R ∧
        σ.arrs "mem" = arrOf n Mem ∧ (∃ g, σ.arrs dst = arrOf n g))
      (memberOrdCom dst)
      (fun _ σ' => σ'.vars "mm" = mm ∧ σ'.arrs "rnk" = arrOf n R ∧
        σ'.arrs "mem" = arrOf n Mem ∧
        ∃ (πm : Equiv.Perm (Fin mm)) (centre : ℕ → ℕ),
          σ'.arrs dst = arrOf n centre ∧
          (∀ k < mm, centre k = activeCentre mm Mem πm k) ∧
          (∀ v : Fin mm, ((πm v : Fin mm) : ℕ) = R (v : ℕ)))
      (13 * mm + 6) := by
  classical
  have hbody : Spec B
      (fun σ => (∃ g, σ.vars "mm" = mm ∧ σ.arrs "rnk" = arrOf n R ∧
        σ.arrs "mem" = arrOf n Mem ∧ σ.arrs dst = arrOf n g ∧
        σ.vars "z" ≤ mm ∧ ∀ v < σ.vars "z", g (R v) = Mem v) ∧
        σ.vars "z" < mm)
      (.seq (.store dst (.get "rnk" (.var "z")) (.get "mem" (.var "z")))
        (.assign "z" (.add (.var "z") (.lit 1))))
      (fun σ σ' => (∃ g, σ'.vars "mm" = mm ∧ σ'.arrs "rnk" = arrOf n R ∧
        σ'.arrs "mem" = arrOf n Mem ∧ σ'.arrs dst = arrOf n g ∧
        σ'.vars "z" ≤ mm ∧ ∀ v < σ'.vars "z", g (R v) = Mem v) ∧
        σ'.vars "z" = σ.vars "z" + 1) 9 := by
    refine Spec.of_exists fun σ hσ => ?_
    obtain ⟨⟨g, hmm, hrnk, hmem, hord, -, hinv⟩, hz⟩ := hσ
    have hzN : σ.vars "z" < n := lt_of_lt_of_le hz hmn
    have hRz : R (σ.vars "z") < mm := hR _ hz
    have hRzN : R (σ.vars "z") < n := lt_of_lt_of_le hRz hmn
    have hMz : Mem (σ.vars "z") < n := hMem _ hz
    have h1 : Run B
        (.store dst (.get "rnk" (.var "z")) (.get "mem" (.var "z"))) σ
        (σ.setArr dst (R (σ.vars "z")) (Mem (σ.vars "z"))) (1 + 2 + 2) := by
      have h := Run.store (B := B) (σ := σ) (a := dst)
        (i := .get "rnk" (.var "z")) (e := .get "mem" (.var "z"))
        (evalB_get (evalB_var (by omega))
          (by rw [hrnk, getElem?_arrOf R hzN]) (by omega))
        (evalB_get (evalB_var (by omega))
          (by rw [hmem, getElem?_arrOf Mem hzN]) (by omega))
        (by rw [hord, length_arrOf]; exact hRzN)
      simpa using h
    have h2 : Run B (.assign "z" (.add (.var "z") (.lit 1)))
        (σ.setArr dst (R (σ.vars "z")) (Mem (σ.vars "z")))
        ((σ.setArr dst (R (σ.vars "z")) (Mem (σ.vars "z"))).setVar
          "z" (σ.vars "z" + 1)) (1 + 3) := by
      have h := Run.assign
        (B := B) (σ := σ.setArr dst (R (σ.vars "z")) (Mem (σ.vars "z")))
        (x := "z") (e := .add (.var "z") (.lit 1))
        (evalB_bin (evalB_var (by rw [vars_setArr]; omega))
          (evalB_lit (by omega))
          (by simp only [Bop.apply_add, vars_setArr]; omega))
      rw [Bop.apply_add, vars_setArr] at h
      simpa using h
    refine ⟨_, _, h1.seq h2, by omega,
      ⟨upd g (R (σ.vars "z")) (Mem (σ.vars "z")), by simp [hmm],
        by rw [arrs_setVar, arrs_setArr, if_neg (Ne.symm hdr)]; exact hrnk,
        by rw [arrs_setVar, arrs_setArr, if_neg (Ne.symm hdm)]; exact hmem,
        ?_, by simp; omega, ?_⟩, by simp⟩
    · rw [arrs_setVar, arrs_setArr, if_pos rfl, hord, set_arrOf_eq_upd]
    · intro v hv
      rw [vars_setVar, if_pos rfl] at hv
      rcases Nat.lt_or_ge v (σ.vars "z") with hlt | hge
      · rw [upd_of_ne _ (fun hc =>
          absurd (hinj v (by omega) _ hz hc) (by omega))]
        exact hinv v hlt
      · have : v = σ.vars "z" := by omega
        rw [this, upd_self]
  refine ((Spec.forRangeZero (B := B) "z" "mm"
    (fun σ => ∃ g, σ.vars "mm" = mm ∧ σ.arrs "rnk" = arrOf n R ∧
      σ.arrs "mem" = arrOf n Mem ∧ σ.arrs dst = arrOf n g ∧
      σ.vars "z" ≤ mm ∧ ∀ v < σ.vars "z", g (R v) = Mem v) mm 9 (by omega)
    (fun _ h => by obtain ⟨-, -, -, -, -, hzz, -⟩ := h; exact hzz)
    (fun _ h => by obtain ⟨-, hmm', -⟩ := h; exact hmm') hbody).pre ?_).post ?_
  · rintro σ ⟨hmm, hrnk, hmem, ⟨g, hord⟩⟩
    exact ⟨g, by simp [hmm], by simp [hrnk], by simp [hmem], by simp [hord], by simp,
      fun v hv => absurd hv (by simp)⟩
  · rintro σ σ' - ⟨⟨g, hmm, hrnk, hmem, hord, -, hinv⟩, hzm⟩
    rw [hzm] at hinv
    let inv : ℕ → ℕ := fun c =>
      if hc : c < mm then Classical.choose (exists_preimage_of_inj hR hinj hc) else 0
    have hinvSpec : ∀ c < mm, inv c < mm ∧ R (inv c) = c := by
      intro c hc
      simp only [inv, dif_pos hc]
      exact Classical.choose_spec (exists_preimage_of_inj hR hinj hc)
    have hinvLt : ∀ c < mm, inv c < mm := fun c hc => (hinvSpec c hc).1
    have hRinv : ∀ c < mm, R (inv c) = c := fun c hc => (hinvSpec c hc).2
    have hinvR : ∀ v < mm, inv (R v) = v := by
      intro v hv
      exact hinj _ (hinvLt _ (hR v hv)) v hv (hRinv _ (hR v hv))
    let πm : Equiv.Perm (Fin mm) := rankPerm mm R inv hR hinvLt hRinv hinvR
    have hordInv : OrdersBy mm πm inv :=
      ordersBy_rankPerm mm R inv hR hinvLt hRinv hinvR
    refine ⟨hmm, hrnk, hmem, πm, g, hord, ?_, ?_⟩
    · intro k hk
      rw [activeCentre_of_lt πm hk]
      calc
        g k = g (R (inv k)) := congrArg g (hRinv k hk).symm
        _ = Mem (inv k) := hinv _ (hinvLt k hk)
        _ = Mem (((πm.symm ⟨k, hk⟩ : Fin mm) : ℕ)) := by
          exact congrArg Mem (hordInv.eq_symm hk)
    · intro v
      rfl

/-! ## Axioms -/

#print axioms memberOrdCom_spec

end Lax3Proofs.Refine.OrderActiveRank
