import Lax185574Proofs.CompRam.Callee

/-!
The runs of the callee of the glue of lem:compose within time.

`CRun`: the three programs compute their answers at all ranks up to `K`
with one constant `C` and one degree `A` (from the three concepts by
`cRun_of`, with `C` and `A` sums over the ranks). `cSound_of_cRun`
gives the soundness facts `CSound` of `Callee.lean` with the constant
`crunBig`. `callee_run`: if the question has an answer, its rank is at
most `K`, the guard holds at `v`, and the word lengths of the three runs
are at least `v` with `crunBig ≤ 2^v` and room for the time bound of the
real part, then the three programs halt with the answer `ansWord q b`
within `C (|realQ q| + 1)^A + crunBig` steps in total.
-/

namespace Lax185574Proofs.CompRam

open Lax808846.Ram Lax808846.RamComputes Lax185574.Computing Lax185574.WordEncoding
open Lax185574Proofs.Words Lax185574.TypeTrees Lax185574.PartialGraphs Lax185574Proofs.TreeAlgo
open Lax185574Proofs.MC (SoundOn soundOn_of fixCst adm_of_fix adm_of_guard two_pow_mono)

/-- **Weakening a `Computes` statement.** A larger constant and a larger
time bound. -/
theorem computes_mono {α β : Type*} [WordEncoding α] [WordEncoding β] {p : Program} {e c c' : ℕ}
    {a : α} {b : β} {T T' : ℕ → ℕ} (h : Computes p e c a b T) (hc : c ≤ c')
    (hT : ∀ m, T m ≤ T' m) : Computes p e c' a b T' := by
  intro w hw
  have hw' : WordAdmissible e c w (toWord a) := fun v hv =>
    le_trans (Nat.mul_le_mul_right _ hc) (hw v hv)
  obtain ⟨h1, h2⟩ := h w hw'
  refine ⟨h1, fun hT' x hx => ?_⟩
  obtain ⟨t, ht, hr⟩ := h2 (le_trans (hT _) hT') x hx
  exact ⟨t, le_trans ht (hT _), hr⟩

/-- The three programs compute their answers at the ranks up to `K`
with the constant `C` and the degree `A`. -/
structure CRun (pR pS pC : Program) (eR eS eC K C A : ℕ) : Prop where
  re : ∀ kk d, kk ≤ K → d ≤ K →
    ∀ (n : ℕ) (G : PartialGraph (Fin n)) (l : ℕ) (u : Fin l → Fin n) (J : List (Fin l)),
      l ≤ kk → J.Nodup → Computes pR eR C (tree G kk d u, J) (tree G kk d (fun i => u (J.get i)))
        (fun m => C * (m + 1) ^ A)
  sh : ∀ kk d, kk ≤ K → d ≤ K →
    ∀ (n : ℕ) (G : PartialGraph (Fin n)) (l : ℕ) (u : Fin l → Fin n), 1 ≤ l → l ≤ kk →
      Computes pS eS C (tree G kk (d + 1) u) (tree G (kk + 1) d u) (fun m => C * (m + 1) ^ A)
  ca : ∀ ws : List (List ℕ),
    Computes pC eC C ((ws.map Raw.mk).map toWord) (finsetOf {x | x ∈ ws.map Raw.mk})
      (fun m => C * (m + 1) ^ A)

theorem pow_le_pow_of {m a A : ℕ} (h : a ≤ A) : (m + 1) ^ a ≤ (m + 1) ^ A :=
  Nat.pow_le_pow_right (by omega) h

open Classical in
/-- **The runs from the three concepts.** -/
theorem cRun_of {pR pS pC : Program} {eR eS eC cC aC : ℕ}
    (hR : ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n)
        (J : List (Fin ℓ)), ℓ ≤ k → J.Nodup →
        Computes pR eR c (tree G k q u, J) (tree G k q (fun i => u (J.get i)))
          (fun m => c * (m + 1) ^ a))
    (hS : ∀ k q : ℕ, ∃ c a : ℕ,
      ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n),
        1 ≤ ℓ → ℓ ≤ k →
        Computes pS eS c (tree G k (q + 1) u) (tree G (k + 1) q u)
          (fun m => c * (m + 1) ^ a))
    (hC : ∀ (α : Type) [WordEncoding α] (l : List α),
        Computes pC eC cC (l.map toWord) (finsetOf {x | x ∈ l}) (fun m => cC * (m + 1) ^ aC))
    (K : ℕ) : ∃ C A, CRun pR pS pC eR eS eC K C A := by
  let cR : ℕ → ℕ → ℕ := fun k q => (hR k q).choose
  let cS : ℕ → ℕ → ℕ := fun k q => (hS k q).choose
  let aR : ℕ → ℕ → ℕ := fun k q => (hR k q).choose_spec.choose
  let aS : ℕ → ℕ → ℕ := fun k q => (hS k q).choose_spec.choose
  have hR' : ∀ k q, ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n)
      (J : List (Fin ℓ)), ℓ ≤ k → J.Nodup →
      Computes pR eR (cR k q) (tree G k q u, J) (tree G k q (fun i => u (J.get i)))
        (fun m => cR k q * (m + 1) ^ aR k q) := fun k q => (hR k q).choose_spec.choose_spec
  have hS' : ∀ k q, ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n),
      1 ≤ ℓ → ℓ ≤ k → Computes pS eS (cS k q) (tree G k (q + 1) u) (tree G (k + 1) q u)
        (fun m => cS k q * (m + 1) ^ aS k q) := fun k q => (hS k q).choose_spec.choose_spec
  set C := dsum cR K + dsum cS K + cC with hCdef
  set A := dsum aR K + dsum aS K + aC with hAdef
  refine ⟨C, A, fun kk d hk hd n G l u J hl hJ => ?_, fun kk d hk hd n G l u h1 hl => ?_,
    fun ws => ?_⟩
  · have h1 := le_dsum cR hk hd
    have h2 := le_dsum aR hk hd
    exact computes_mono (hR' kk d n G l u J hl hJ) (by omega)
      (fun m => Nat.mul_le_mul (by omega) (pow_le_pow_of (by omega)))
  · have h1' := le_dsum cS hk hd
    have h2 := le_dsum aS hk hd
    exact computes_mono (hS' kk d n G l u h1 hl) (by omega)
      (fun m => Nat.mul_le_mul (by omega) (pow_le_pow_of (by omega)))
  · exact computes_mono (hC Raw (ws.map Raw.mk)) (by omega)
      (fun m => Nat.mul_le_mul (by omega) (pow_le_pow_of (by omega)))

/-- The constant that the word lengths of the runs must exceed. -/
noncomputable def crunBig (eR eS eC C A : ℕ) : ℕ :=
  C ^ (eR + 1) + C ^ (eS + 1) + C ^ (eC + 1) + fixCst eR C dRq + fixCst eS C dSq + fixCst eC C [0] +
    C * (dRq.length + 1) ^ A + C * (dSq.length + 1) ^ A + C * ([0].length + 1) ^ A

theorem rank_dRq : dRq = toWord (tree G0 0 0 (Fin.elim0 : Fin 0 → Fin 0), ([] : List (Fin 0))) := rfl

/-- **Soundness from the runs.** -/
theorem cSound_of_cRun {pR pS pC : Program} {eR eS eC K C A : ℕ} (h : CRun pR pS pC eR eS eC K C A)
    (hK : 1 ≤ K) : CSound pR pS pC eR eS eC K (crunBig eR eS eC C A) := by
  refine ⟨fun kk d hk hd => ⟨C, ?_, fun n G l u J hl hJ => soundOn_of (h.re kk d hk hd n G l u J hl hJ)⟩,
    fun kk d hk hd => ⟨C, ?_, fun n G l u h1 hl => soundOn_of (h.sh kk d hk hd n G l u h1 hl)⟩,
    ⟨C, ?_, fun ws => soundOn_of (h.ca ws)⟩, ?_, ?_, ?_⟩
  · unfold crunBig; omega
  · unfold crunBig; omega
  · unfold crunBig; omega
  · intro y t w hw hr
    have hs := soundOn_of (h.re 0 0 (Nat.zero_le _) (Nat.zero_le _) 0 G0 0 Fin.elim0 [] le_rfl
      List.nodup_nil)
    exact hs w (adm_of_fix (u := dRq) (by unfold crunBig at hw; omega)) y t hr
  · intro y t w hw hr
    have hs := soundOn_of (h.sh 1 0 hK (Nat.zero_le _) 1 G1 1 ![0] le_rfl le_rfl)
    exact hs w (adm_of_fix (u := dSq) (by unfold crunBig at hw; omega)) y t hr
  · intro y t w hw hr
    have hs := soundOn_of (h.ca [])
    have e1 : toWord ((([] : List (List ℕ)).map Raw.mk).map toWord) = [0] := rfl
    have e2 : toWord (finsetOf {x | x ∈ ([] : List (List ℕ)).map Raw.mk}) = [0] := by
      rw [raw_output, show sortedDistinct ([] : List (List ℕ)) = [] by simp [sortedDistinct]]; rfl
    unfold SoundOn at hs
    rw [e1, e2] at hs
    exact hs w (adm_of_fix (by unfold crunBig at hw; omega)) y t hr

/-- The time bound of the real part of a question. -/
def realT (C A : ℕ) (q : Qry) : ℕ := C * ((realQ q).length + 1) ^ A

theorem run_dRq {pR pS pC : Program} {eR eS eC K C A : ℕ} (hC : CRun pR pS pC eR eS eC K C A)
    {w : ℕ} (hw : fixCst eR C dRq + C * (dRq.length + 1) ^ A ≤ 2 ^ w) :
    ∃ t ≤ C * (dRq.length + 1) ^ A, RunsTo w pR dRq dRa t :=
  ((hC.re 0 0 (Nat.zero_le _) (Nat.zero_le _) 0 G0 0 Fin.elim0 [] le_rfl List.nodup_nil) w
    (adm_of_fix (u := dRq) (by omega))).2 (by show C * (dRq.length + 1) ^ A ≤ 2 ^ w; omega) _ rfl

theorem run_dSq {pR pS pC : Program} {eR eS eC K C A : ℕ} (hC : CRun pR pS pC eR eS eC K C A)
    (hK : 1 ≤ K) {w : ℕ} (hw : fixCst eS C dSq + C * (dSq.length + 1) ^ A ≤ 2 ^ w) :
    ∃ t ≤ C * (dSq.length + 1) ^ A, RunsTo w pS dSq dSa t :=
  ((hC.sh 1 0 hK (Nat.zero_le _) 1 G1 1 ![0] le_rfl le_rfl) w
    (adm_of_fix (u := dSq) (by omega))).2 (by show C * (dSq.length + 1) ^ A ≤ 2 ^ w; omega) _ rfl

theorem run_c0 {pR pS pC : Program} {eR eS eC K C A : ℕ} (hC : CRun pR pS pC eR eS eC K C A)
    {w : ℕ} (hw : fixCst eC C [0] + C * ([0].length + 1) ^ A ≤ 2 ^ w) :
    ∃ t ≤ C * ([0].length + 1) ^ A, RunsTo w pC [0] [0] t := by
  have hs := hC.ca []
  have e1 : toWord ((([] : List (List ℕ)).map Raw.mk).map toWord) = [0] := rfl
  have e2 : toWord (finsetOf {x | x ∈ ([] : List (List ℕ)).map Raw.mk}) = [0] := by
    rw [raw_output, show sortedDistinct ([] : List (List ℕ)) = [] by simp [sortedDistinct]]; rfl
  obtain ⟨t, ht, hr⟩ := (hs w (by rw [e1]; exact adm_of_fix (by omega))).2
    (by show C * ((toWord ((([] : List (List ℕ)).map Raw.mk).map toWord)).length + 1) ^ A ≤ 2 ^ w
        rw [e1]; omega) _ rfl
  rw [e1, e2] at hr
  exact ⟨t, by rw [e1] at ht; exact ht, hr⟩

/-- **The runs of the callee.** -/
theorem callee_run {pR pS pC : Program} {eR eS eC K C A : ℕ} (hC : CRun pR pS pC eR eS eC K C A)
    (hK1 : 1 ≤ K) {n : ℕ} {G : PartialGraph (Fin n)} {q : Qry} {b : List ℕ} (hA : Ans G q b)
    (hK : RankLe K q) {v wR wS wC : ℕ} (hg : CGuard eR eS eC v q)
    (hbig : crunBig eR eS eC C A + realT C A q ≤ 2 ^ v) (hR : v ≤ wR) (hS' : v ≤ wS)
    (hC' : v ≤ wC) :
    ∃ y z u tA tB tC, RunsTo wR pR (qR q) y tA ∧ RunsTo wS pS (qS q) z tB ∧
      RunsTo wC pC (qC q) u tC ∧ y ++ z ++ u = ansWord q b ∧
      tA + tB + tC ≤ realT C A q + crunBig eR eS eC C A := by
  have pR := two_pow_mono hR
  have pS := two_pow_mono hS'
  have pC := two_pow_mono hC'
  unfold crunBig at hbig ⊢
  cases q with
  | re w =>
    obtain ⟨kk, d, l, u', J, hl, hJ, rfl, rfl⟩ := hA
    obtain ⟨e0, e1⟩ := getD_tree_word G kk d u' (toWord J)
    simp only [RankLe] at hK
    have hw : toWord (tree G kk d u', J) = toWord (tree G kk d u') ++ toWord J := rfl
    rw [hw, e0, e1] at hK
    simp only [CGuard, realQ, expQ] at hg
    simp only [realT, realQ] at hbig ⊢
    obtain ⟨t1, ht1, r1⟩ := ((hC.re kk d hK.1 hK.2 n G l u' J hl hJ) wR
      (adm_of_guard (by omega) (by omega))).2 (by simp only [wordLength]; omega) _ rfl
    obtain ⟨t2, ht2, r2⟩ := run_dSq hC hK1 (w := wS) (by omega)
    obtain ⟨t3, ht3, r3⟩ := run_c0 hC (w := wC) (by omega)
    refine ⟨_, _, _, _, _, _, r1, r2, r3, rfl, ?_⟩
    simp only [wordLength] at ht1
    omega
  | sh w =>
    obtain ⟨kk, d, l, u', h1, hl, rfl, rfl⟩ := hA
    obtain ⟨e0, e1⟩ := getD_tree_word G kk (d + 1) u' []
    rw [List.append_nil] at e0 e1
    simp only [RankLe, e0, e1] at hK
    simp only [CGuard, realQ, expQ] at hg
    simp only [realT, realQ] at hbig ⊢
    obtain ⟨t1, ht1, r1⟩ := run_dRq hC (w := wR) (by omega)
    obtain ⟨t2, ht2, r2⟩ := ((hC.sh kk d hK.1 (by omega) n G l u' h1 hl) wS
      (adm_of_guard (by omega) (by omega))).2 (by simp only [wordLength]; omega) _ rfl
    obtain ⟨t3, ht3, r3⟩ := run_c0 hC (w := wC) (by omega)
    refine ⟨_, _, _, _, _, _, r1, r2, r3, rfl, ?_⟩
    simp only [wordLength] at ht2
    omega
  | ca ws =>
    simp only [Ans] at hA
    subst hA
    simp only [CGuard, realQ, expQ] at hg
    simp only [realT, realQ] at hbig ⊢
    obtain ⟨t1, ht1, r1⟩ := run_dRq hC (w := wR) (by omega)
    obtain ⟨t2, ht2, r2⟩ := run_dSq hC hK1 (w := wS) (by omega)
    have hs := hC.ca ws
    have e1 : toWord ((ws.map Raw.mk).map toWord) = toWord ws := by rw [raw_input]
    obtain ⟨t3, ht3, r3⟩ := (hs wC (by rw [e1]; exact adm_of_guard (by omega) (by omega))).2
      (by simp only [wordLength]; rw [e1]; omega) _ rfl
    rw [e1, raw_output] at r3
    refine ⟨_, _, _, _, _, _, r1, r2, r3, rfl, ?_⟩
    simp only [wordLength] at ht3
    rw [e1] at ht3
    omega

end Lax185574Proofs.CompRam
