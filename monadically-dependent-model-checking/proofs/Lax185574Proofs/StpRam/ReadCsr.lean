import Lax185574Proofs.StpRam.CsrPure

/-!
Reading the word of a graph on `Fin n` into compressed-row form.

`readCsr o t` reads `n`, and for every vertex the number of its
neighbors and the words `1, z` of the neighbors. It stores the offset of
every vertex into `o` and the neighbors into `t`.
-/

namespace Lax185574Proofs.StpRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib
open Lax185574.WordEncoding Lax185574Proofs.Words

def slotRd (t : String) : Com :=
  .seq (.read "cx") (.seq (.read "cy") (.seq (.store t (.var "cp") (.var "cy"))
    (.assign "cp" (.add (.var "cp") (.lit 1)))))

def vtxRd (o t : String) : Com :=
  .seq (.store o (.var "cv") (.var "cp")) (.seq (.read "cd") (forUp "ck" (.var "cd") (slotRd t)))

def readCsr (o t : String) : Com :=
  .seq (.read "cn") (.seq (.assign "cp" (.lit 0)) (.seq (forUp "cv" (.var "cn") (vtxRd o t))
    (.store o (.var "cn") (.var "cp"))))

theorem length_nbrL_le {n : ℕ} (H : SimpleGraph (Fin n)) (v : ℕ) : (nbrL H v).length ≤ n := by
  unfold nbrL; exact le_trans (List.length_filter_le _ _) (by simp)

theorem pairs_drop (l : List ℕ) {j : ℕ} (hj : j < l.length) :
    ((l.drop j).map fun z => [1, z]).flatten = 1 :: l[j] :: ((l.drop (j + 1)).map fun z => [1, z]).flatten := by
  rw [List.drop_eq_getElem_cons hj, List.map_cons, List.flatten_cons]; rfl

/-- **Reading a graph.** -/
theorem readCsr_run {B n : ℕ} (H : SimpleGraph (Fin n)) {o t : String} (hot : o ≠ t) {rest : List ℕ}
    {σ : Env} (hinp : σ.inp = toWord H ++ rest) (ho : (σ.arrs o).length = n + 1)
    (ht : (σ.arrs t).length = offL H n) (hnB : n + 1 < B) (hsB : offL H n + 1 < B) :
    ∃ σ', Run B (readCsr o t) σ σ' (n * (17 * n + 18) + 12) ∧
      Csr o t n (offL H n) n (offL H) (tgtL H) σ' ∧ σ'.inp = rest ∧ σ'.vars "cn" = n := by
  rw [toWord_graph_blocks] at hinp
  set ns := offL H n with hns
  set σ1 : Env := { σ.setVar "cn" n with inp := blocksFrom H 0 ++ rest } with hσ1
  have r1 : Run B (.read "cn") σ σ1 1 := Run.read (by rw [hinp]; rfl)
  set σ2 := σ1.setVar "cp" 0 with hσ2
  have r2 : Run B (.assign "cp" (.lit 0)) σ1 σ2 2 := (Run.assign (by simp; omega)).mono (by simp)
  let I : ℕ → Env → Prop := fun v τ => τ.inp = blocksFrom H v ++ rest ∧ τ.vars "cp" = offL H v ∧
    τ.vars "cn" = n ∧ (τ.arrs o).length = n + 1 ∧ (τ.arrs t).length = ns ∧
    (∀ i < v, (τ.arrs o)[i]? = some (offL H i)) ∧ (∀ p < offL H v, (τ.arrs t)[p]? = some (tgtL H p))
  obtain ⟨σ3, r3, ⟨hin3, hcp3, hcn3, hlo3, hlt3, ho3, ht3⟩, -⟩ := forUp_run (B := B) (i := "cv")
    (e := .var "cn") (body := vtxRd o t) (N := n) (K := 17 * n + 10) I (σ := σ2) (by omega)
    (fun v _ τ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.2.2.1.symm, by rw [hI.2.2.1]; omega⟩)
    ⟨by simp [hσ2, hσ1], by simp [hσ2, offL], by simp [hσ2, hσ1], by simp [hσ2, hσ1, ho],
      by simp [hσ2, hσ1, ht], fun i hi => absurd hi (Nat.not_lt_zero _),
      fun p hp => absurd hp (by simp [offL])⟩
    (by
      rintro v hv τ ⟨hin, hcp, hcn, hlo, hlt, hoτ, htτ⟩ hcv
      have hsv : offL H (v + 1) ≤ ns := offL_mono H (by omega)
      have hov : offL H v ≤ offL H (v + 1) := offL_mono H (by omega)
      set d := (nbrL H v).length with hd
      have hdn : d ≤ n := length_nbrL_le H v
      have hof := offL_succ H v
      -- store the offset
      set τ1 := τ.setArr o v (offL H v) with hτ1
      have q1 : Run B (.store o (.var "cv") (.var "cp")) τ τ1 3 :=
        (Run.store (by simp [hcv]; omega) (by simp [hcp]; omega) (by omega)).mono (by simp)
      -- read the number of neighbors
      have hin' : τ1.inp = d :: (((nbrL H v).map fun z => [1, z]).flatten ++
          blocksFrom H (v + 1) ++ rest) := by
        simp [hτ1, hin, blocksFrom_succ H hv, vblk, hd]
      set τ2 : Env := { τ1.setVar "cd" d with
        inp := (((nbrL H v).map fun z => [1, z]).flatten ++ blocksFrom H (v + 1) ++ rest) } with hτ2
      have q2 : Run B (.read "cd") τ1 τ2 1 := Run.read hin'
      -- the slots
      let J : ℕ → Env → Prop := fun j ρ =>
        ρ.inp = (((nbrL H v).drop j).map fun z => [1, z]).flatten ++ blocksFrom H (v + 1) ++ rest ∧
        ρ.vars "cp" = offL H v + j ∧ ρ.vars "cd" = d ∧ ρ.vars "cn" = n ∧ ρ.vars "cv" = v ∧
        (ρ.arrs o).length = n + 1 ∧ (ρ.arrs t).length = ns ∧
        (∀ i < v + 1, (ρ.arrs o)[i]? = some (offL H i)) ∧
        (∀ p < offL H v + j, (ρ.arrs t)[p]? = some (tgtL H p))
      obtain ⟨τ3, q3, ⟨hin3, hcp3, -, hcn3, hcv3, hlo3, hlt3, ho3, ht3⟩, -⟩ := forUp_run (B := B)
        (i := "ck") (e := .var "cd") (body := slotRd t) (N := d) (K := 9) J (σ := τ2) (by omega)
        (fun j _ ρ hI _ => by simp only [evalB_var_iff]; exact ⟨hI.2.2.1.symm, by rw [hI.2.2.1]; omega⟩)
        ⟨by simp [hτ2], by simp [hτ2, hτ1, hcp], by simp [hτ2], by simp [hτ2, hτ1, hcn],
          by simp [hτ2, hτ1, hcv], by simp [hτ2, hτ1, hlo], by simp [hτ2, hτ1, Ne.symm hot, hlt],
          fun i hi => by
            simp only [hτ2, hτ1, arrs_setVar, arrs_setArr, if_true]
            by_cases hiv : v = i
            · subst hiv; rw [List.getElem?_set_self (by rw [hlo]; omega)]
            · rw [List.getElem?_set_ne hiv]; exact hoτ i (by omega),
          fun p hp => by simp only [hτ2, hτ1, arrs_setVar, arrs_setArr, if_neg (Ne.symm hot)]; exact htτ p hp⟩
        (by
          rintro j hj ρ ⟨hinρ, hcpρ, hcdρ, hcnρ, hcvρ, hloρ, hltρ, hoρ, htρ⟩ hck
          have hpj : offL H v + j < ns := by omega
          have hy : (nbrL H v)[j] < n := lt_of_mem_nbrL (List.getElem_mem hj)
          rw [pairs_drop _ hj] at hinρ
          set ρ1 : Env := { ρ.setVar "cx" 1 with
            inp := ((nbrL H v)[j] :: ((((nbrL H v).drop (j + 1)).map fun z => [1, z]).flatten ++
              blocksFrom H (v + 1) ++ rest)) } with hρ1
          have s1 : Run B (.read "cx") ρ ρ1 1 := Run.read (by rw [hinρ]; simp)
          set ρ2 : Env := { ρ1.setVar "cy" (nbrL H v)[j] with
            inp := ((((nbrL H v).drop (j + 1)).map fun z => [1, z]).flatten ++ blocksFrom H (v + 1) ++
              rest) } with hρ2
          have s2 : Run B (.read "cy") ρ1 ρ2 1 := Run.read rfl
          set ρ3 := ρ2.setArr t (offL H v + j) (nbrL H v)[j] with hρ3
          have s3 : Run B (.store t (.var "cp") (.var "cy")) ρ2 ρ3 3 :=
            (Run.store (by simp [hρ2, hρ1, hcpρ]; omega) (by simp [hρ2]; omega)
              (by simp [hρ2, hρ1, hltρ]; omega)).mono (by simp)
          have s4 : Run B (.assign "cp" (.add (.var "cp") (.lit 1))) ρ3 (ρ3.setVar "cp" (offL H v + j + 1))
              4 := by
            refine (Run.assign ?_).mono (by simp)
            simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
            exact ⟨offL H v + j, 1, ⟨by simp [hρ3, hρ2, hρ1, hcpρ], by simp [hρ3, hρ2, hρ1, hcpρ]; omega⟩,
              ⟨rfl, by omega⟩, by simp [Bop.apply], by omega⟩
          refine ⟨ρ3.setVar "cp" (offL H v + j + 1), (Run.seq s1 (Run.seq s2 (Run.seq s3 s4))).mono
            (by omega), by simp [hρ3, hρ2, hρ1, hck], by simp [hρ3, hρ2, hρ1], by simp [hρ3, hρ2, hρ1]; omega,
            by simp [hρ3, hρ2, hρ1, hcdρ], by simp [hρ3, hρ2, hρ1, hcnρ], by simp [hρ3, hρ2, hρ1, hcvρ],
            by simp [hρ3, hρ2, hρ1, hot, hloρ], by simp [hρ3, hρ2, hρ1, hltρ],
            fun i hi => by simp only [hρ3, hρ2, hρ1, arrs_setVar, arrs_setArr, if_neg hot]; exact hoρ i hi,
            fun p hp => ?_⟩
          simp only [hρ3, hρ2, hρ1, arrs_setVar, arrs_setArr, if_true]
          by_cases hpe : offL H v + j = p
          · subst hpe; rw [List.getElem?_set_self (by simp [hltρ]; omega), tgtL_row H hv hj]
          · rw [List.getElem?_set_ne hpe]; exact htρ p (by omega))
      refine ⟨τ3, (Run.seq q1 (Run.seq q2 q3)).mono ?_, hcv3, ⟨?_, by simp [hcp3, hof, hd],
        by simp [hcn3], by simp [hlo3], by simp [hlt3], by simpa using ho3,
        fun p hp => by simpa using ht3 p (by rw [hof] at hp; exact hp)⟩⟩
      · have := Nat.mul_le_mul_right 17 hdn
        simp only [Expr.size]; omega
      · simp [hin3, List.drop_of_length_le (show d ≤ d by omega)])
  -- the last offset
  have r4 : Run B (.store o (.var "cn") (.var "cp")) σ3 (σ3.setArr o n ns) 3 :=
    (Run.store (by simp [hcn3]; omega) (by simp [hcp3]; omega) (by omega)).mono (by simp)
  refine ⟨σ3.setArr o n ns, (Run.seq r1 (Run.seq r2 (Run.seq r3 r4))).mono (by simp only [Expr.size]; nlinarith),
    ⟨?_, ?_, fun i _ => offL_mono H (by omega), rfl, fun p hp => tgtL_lt H hp⟩, by
      simp [hin3, blocksFrom_n], by simp [hcn3]⟩
  · refine List.ext_getElem? fun i => ?_
    simp only [arrs_setArr, if_true]
    by_cases hi : n = i
    · subst hi; rw [List.getElem?_set_self (by rw [hlo3]; omega), getElem?_arrOf _ (show n < n + 1 by omega)]
    · rw [List.getElem?_set_ne hi]
      by_cases hi' : i < n
      · rw [ho3 i hi', getElem?_arrOf _ (by omega)]
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
  · refine List.ext_getElem? fun p => ?_
    simp only [arrs_setArr, if_neg (Ne.symm hot)]
    by_cases hp : p < ns
    · rw [ht3 p hp, getElem?_arrOf _ hp]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]

end Lax185574Proofs.StpRam
