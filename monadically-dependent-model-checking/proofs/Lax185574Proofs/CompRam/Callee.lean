import Lax185574Proofs.CompRam.Fixed
import Lax185574Proofs.MC.Asm.Callees
import Lax185574.Restriction
import Lax185574.RankShift
import Lax185574.CanonicalForm

/-!
The answers of the callee of the glue of lem:compose.

The callee `switch R S C` runs the restriction, the rank shift and the
canonical form on the three parts `qR q`, `qS q`, `qC q` of the query
`qWord q` of a question `q`. One part does real work, the other two are
the fixed questions. The real part is a question about a tree of rank
`(kk, d)`, and the constants of the programs depend on the rank. If both
entries of the rank are at most `K` (`RankLe K q`), the constants are
bounded by one number `C` (`CSound`, from the three concepts by
`cSound_of`). If the glue program has checked the guard `CGuard` of the
real part at a word length `v`, and the three programs run at word
lengths at least `v` with `C ≤ 2^v`, then every halting run of the three
programs gives the answer `ansWord q b` (`callee_ans`).

The canonical form is called on words encoded by themselves (`Raw`), so
that its input is the word of a list of words and its output the word
of their sorted list of distinct words.
-/

namespace Lax185574Proofs.CompRam

open Lax808846.Ram Lax185574.Computing Lax185574.WordEncoding Lax185574Proofs.Words
open Lax185574.TypeTrees Lax185574.PartialGraphs Lax185574Proofs.TreeAlgo
open Lax185574Proofs.MC (SoundOn soundOn_of fixCst adm_of_fix adm_of_guard two_pow_mono)
open Lax185574Proofs.Simulate (swIn)

/-! ### Words encoded by themselves -/

/-- A word, encoded by itself. -/
structure Raw where
  /-- The word. -/
  w : List ℕ

instance : WordEncoding Raw := ⟨Raw.w⟩

theorem raw_input (ws : List (List ℕ)) : ((ws.map Raw.mk).map toWord) = ws := by
  rw [List.map_map]
  exact List.map_id' _

theorem raw_output (ws : List (List ℕ)) :
    toWord (finsetOf {x | x ∈ ws.map Raw.mk}) = toWord (sortedDistinct ws) := by
  have hfin : {x | x ∈ ws.map Raw.mk}.Finite := (ws.map Raw.mk).finite_toSet
  show toWord (finsetOf {x | x ∈ ws.map Raw.mk}).words = _
  have h := sortedDistinct_eq_words (finsetOf {x | x ∈ ws.map Raw.mk}) ws fun u => by
    constructor
    · intro hu; exact ⟨⟨u⟩, (mem_finsetOf hfin).2 (List.mem_map.2 ⟨u, hu, rfl⟩), rfl⟩
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨v, hv, rfl⟩ := List.mem_map.1 ((mem_finsetOf hfin).1 ha)
      exact hv
  rw [h]

/-! ### The parts of the query -/

/-- The part of the query for the restriction. -/
noncomputable def qR : Qry → List ℕ
  | .re w => w
  | _ => dRq

/-- The part of the query for the rank shift. -/
noncomputable def qS : Qry → List ℕ
  | .sh w => w
  | _ => dSq

/-- The part of the query for the canonical form. -/
def qC : Qry → List ℕ
  | .ca ws => toWord ws
  | _ => [0]

theorem qWord_parts (q : Qry) : qWord q = swIn (qR q) (qS q) (qC q) := by
  cases q <;> rfl

/-- The part of the query that does real work. -/
def realQ : Qry → List ℕ
  | .re w => w
  | .sh w => w
  | .ca ws => toWord ws

/-- The literal exponent of the guard of a question. -/
def expQ (eR eS eC : ℕ) : Qry → ℕ
  | .re _ => eR
  | .sh _ => eS
  | .ca _ => eC

/-- The guard of a question at word length `v`. -/
def CGuard (eR eS eC v : ℕ) (q : Qry) : Prop :=
  ((realQ q).length + maxEntry (realQ q) + 1) ^ (expQ eR eS eC q + 1) ≤ 2 ^ v

/-- Both entries of the rank of the tree of a question are at most `K`. -/
def RankLe (K : ℕ) : Qry → Prop
  | .re w => w.getD 0 0 ≤ K ∧ w.getD 1 0 ≤ K
  | .sh w => w.getD 0 0 ≤ K ∧ w.getD 1 0 ≤ K
  | .ca _ => True

/-! ### Soundness of the three programs -/

/-- The soundness facts of the three programs at the ranks up to `K`,
with all constants bounded by `C`. -/
structure CSound (pR pS pC : Program) (eR eS eC K C : ℕ) : Prop where
  re : ∀ kk d, kk ≤ K → d ≤ K → ∃ c, c ^ (eR + 1) ≤ C ∧
    ∀ (n : ℕ) (G : PartialGraph (Fin n)) (l : ℕ) (u : Fin l → Fin n) (J : List (Fin l)),
      l ≤ kk → J.Nodup → SoundOn pR eR c (tree G kk d u, J) (tree G kk d (fun i => u (J.get i)))
  sh : ∀ kk d, kk ≤ K → d ≤ K → ∃ c, c ^ (eS + 1) ≤ C ∧
    ∀ (n : ℕ) (G : PartialGraph (Fin n)) (l : ℕ) (u : Fin l → Fin n), 1 ≤ l → l ≤ kk →
      SoundOn pS eS c (tree G kk (d + 1) u) (tree G (kk + 1) d u)
  ca : ∃ c, c ^ (eC + 1) ≤ C ∧ ∀ ws : List (List ℕ),
    SoundOn pC eC c ((ws.map Raw.mk).map toWord) (finsetOf {x | x ∈ ws.map Raw.mk})
  re0 : ∀ y t w, C ≤ 2 ^ w → RunsTo w pR dRq y t → y = dRa
  sh0 : ∀ y t w, C ≤ 2 ^ w → RunsTo w pS dSq y t → y = dSa
  ca0 : ∀ y t w, C ≤ 2 ^ w → RunsTo w pC [0] y t → y = [0]

/-- The sum of a function over the pairs below `K + 1`. -/
def dsum (f : ℕ → ℕ → ℕ) (K : ℕ) : ℕ := ∑ i ∈ Finset.range (K + 1), ∑ j ∈ Finset.range (K + 1), f i j

theorem le_dsum (f : ℕ → ℕ → ℕ) {K a b : ℕ} (ha : a ≤ K) (hb : b ≤ K) : f a b ≤ dsum f K := by
  unfold dsum
  refine le_trans ?_ (Finset.single_le_sum (f := fun i => ∑ j ∈ Finset.range (K + 1), f i j)
    (fun _ _ => Nat.zero_le _) (Finset.mem_range.2 (Nat.lt_succ_of_le ha)))
  exact Finset.single_le_sum (f := f a) (fun _ _ => Nat.zero_le _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hb))

theorem words_nil {α : Type*} [WordEncoding α] : (∅ : Finset α).words = [] := by
  simp [Finset.words]

open Classical in
/-- **The soundness facts from the three concepts.** -/
theorem cSound_of {pR pS pC : Program} {eR eS eC cC aC : ℕ}
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
    (K : ℕ) : ∃ C, CSound pR pS pC eR eS eC K C := by
  let cR : ℕ → ℕ → ℕ := fun k q => (hR k q).choose
  let cS : ℕ → ℕ → ℕ := fun k q => (hS k q).choose
  have hR' : ∀ k q, ∃ a : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n)
      (J : List (Fin ℓ)), ℓ ≤ k → J.Nodup →
      Computes pR eR (cR k q) (tree G k q u, J) (tree G k q (fun i => u (J.get i)))
        (fun m => cR k q * (m + 1) ^ a) := fun k q => (hR k q).choose_spec
  have hS' : ∀ k q, ∃ a : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n),
      1 ≤ ℓ → ℓ ≤ k → Computes pS eS (cS k q) (tree G k (q + 1) u) (tree G (k + 1) q u)
        (fun m => cS k q * (m + 1) ^ a) := fun k q => (hS k q).choose_spec
  refine ⟨dsum (fun i j => cR i j ^ (eR + 1)) K + dsum (fun i j => cS i j ^ (eS + 1)) K +
    cC ^ (eC + 1) + fixCst eR (cR 0 0) dRq + fixCst eS (cS 1 0) dSq + fixCst eC cC [0], ?_⟩
  refine ⟨fun kk d hk hd => ⟨cR kk d, ?_, fun n G l u J hl hJ => ?_⟩,
    fun kk d hk hd => ⟨cS kk d, ?_, fun n G l u h1 hl => ?_⟩,
    ⟨cC, by omega, fun ws => soundOn_of (hC Raw (ws.map Raw.mk))⟩, ?_, ?_, ?_⟩
  · have : cR kk d ^ (eR + 1) ≤ dsum (fun i j => cR i j ^ (eR + 1)) K :=
      le_dsum (fun i j => cR i j ^ (eR + 1)) hk hd
    omega
  · obtain ⟨a, ha⟩ := hR' kk d; exact soundOn_of (ha n G l u J hl hJ)
  · have : cS kk d ^ (eS + 1) ≤ dsum (fun i j => cS i j ^ (eS + 1)) K :=
      le_dsum (fun i j => cS i j ^ (eS + 1)) hk hd
    omega
  · obtain ⟨a, ha⟩ := hS' kk d; exact soundOn_of (ha n G l u h1 hl)
  · intro y t w hw h
    obtain ⟨a, ha⟩ := hR' 0 0
    exact soundOn_of (ha 0 G0 0 Fin.elim0 [] le_rfl List.nodup_nil) w
      (adm_of_fix (u := dRq) (by omega)) y t h
  · intro y t w hw h
    obtain ⟨a, ha⟩ := hS' 1 0
    exact soundOn_of (ha 1 G1 1 ![0] le_rfl le_rfl) w (adm_of_fix (u := dSq) (by omega)) y t h
  · intro y t w hw h
    have hs := soundOn_of (hC Raw ([] : List Raw)) w
    have e1 : toWord (([] : List Raw).map toWord) = [0] := rfl
    have e2 : toWord (finsetOf {x | x ∈ ([] : List Raw)}) = [0] := by
      have : finsetOf {x | x ∈ ([] : List Raw)} = ∅ := by
        ext x; rw [mem_finsetOf ([] : List Raw).finite_toSet]; simp
      rw [this]; show toWord (∅ : Finset Raw).words = _; rw [words_nil]; rfl
    rw [e1, e2] at hs
    exact hs (adm_of_fix (by omega)) y t h

/-! ### The answers of the callee -/

theorem getD_tree_word {n : ℕ} (G : PartialGraph (Fin n)) (kk d : ℕ) {l : ℕ} (u : Fin l → Fin n)
    (r : List ℕ) : (toWord (tree G kk d u) ++ r).getD 0 0 = kk ∧
      (toWord (tree G kk d u) ++ r).getD 1 0 = d := by
  rw [Lax185574Proofs.CompRam.toWord_tree_eq]
  simp

/-- **The answers of the callee.** If the question has an answer `b` of
the three programs on trees of `G`, its rank is at most `K`, the guard
holds at `v`, and the three runs are at word lengths at least `v` with
`C ≤ 2^v`, then the three outputs together are `ansWord q b`. -/
theorem callee_ans {pR pS pC : Program} {eR eS eC K C : ℕ} (hS : CSound pR pS pC eR eS eC K C)
    {n : ℕ} {G : PartialGraph (Fin n)} {q : Qry} {b : List ℕ} (hA : Ans G q b) (hK : RankLe K q)
    {v wR wS wC : ℕ} (hg : CGuard eR eS eC v q) (hC : C ≤ 2 ^ v) (hR : v ≤ wR) (hS' : v ≤ wS)
    (hC' : v ≤ wC) {y z u : List ℕ} {tA tB tC : ℕ} (hy : RunsTo wR pR (qR q) y tA)
    (hz : RunsTo wS pS (qS q) z tB) (hu : RunsTo wC pC (qC q) u tC) :
    y ++ z ++ u = ansWord q b := by
  have pR := two_pow_mono hR
  have pS := two_pow_mono hS'
  have pC := two_pow_mono hC'
  cases q with
  | re w =>
    obtain ⟨kk, d, l, u', J, hl, hJ, rfl, rfl⟩ := hA
    obtain ⟨e0, e1⟩ := getD_tree_word G kk d u' (toWord J)
    simp only [RankLe] at hK
    have hw : toWord (tree G kk d u', J) = toWord (tree G kk d u') ++ toWord J := rfl
    rw [hw, e0, e1] at hK
    obtain ⟨c, hc, hs⟩ := hS.re kk d hK.1 hK.2
    simp only [CGuard, realQ, expQ] at hg
    simp only [qR, qS, qC] at hy hz hu
    have e2 := hS.sh0 _ _ _ (by omega) hz
    have e3 := hS.ca0 _ _ _ (by omega) hu
    have e1' := hs n G l u' J hl hJ wR (adm_of_guard (by omega) (by omega)) _ _ hy
    rw [e1', e2, e3]; rfl
  | sh w =>
    obtain ⟨kk, d, l, u', h1, hl, rfl, rfl⟩ := hA
    obtain ⟨e0, e1⟩ := getD_tree_word G kk (d + 1) u' []
    rw [List.append_nil] at e0 e1
    simp only [RankLe, e0, e1] at hK
    obtain ⟨c, hc, hs⟩ := hS.sh kk d hK.1 (by omega)
    simp only [CGuard, realQ, expQ] at hg
    simp only [qR, qS, qC] at hy hz hu
    have e2 := hS.re0 _ _ _ (by omega) hy
    have e3 := hS.ca0 _ _ _ (by omega) hu
    have e1' := hs n G l u' h1 hl wS (adm_of_guard (by omega) (by omega)) _ _ hz
    rw [e1', e2, e3]; rfl
  | ca ws =>
    simp only [Ans] at hA
    subst hA
    obtain ⟨c, hc, hs⟩ := hS.ca
    simp only [CGuard, realQ, expQ] at hg
    simp only [qR, qS, qC] at hy hz hu
    have e2 := hS.re0 _ _ _ (by omega) hy
    have e3 := hS.sh0 _ _ _ (by omega) hz
    have hs' := hs ws wC
    rw [raw_input, raw_output] at hs'
    have e1' := hs' (adm_of_guard (by omega) (by omega)) _ _ hu
    rw [e1', e2, e3]; rfl

/-- The back clause of `switch R S C D` with constant `K₀`: every halting
run comes from halting runs of the three programs. -/
def SwBack (p pR pS pC : Program) (K₀ D : ℕ) : Prop :=
  ∀ (w : ℕ) (qA qB qC : List ℕ), K₀ ≤ 2 ^ (w - 8 - D) →
    (swIn qA qB qC).length < 2 ^ (w - 10 - D) → D + 14 ≤ w →
    ∀ o T, RunsTo w p (swIn qA qB qC) o T →
      ∃ y z u tA tB tC, RunsTo (w - 4 - D) pR qA y tA ∧ RunsTo (w - 6 - D) pS qB z tB ∧
        RunsTo (w - 8 - D) pC qC u tC ∧ o = y ++ z ++ u

/-- **The answer of the switch.** Every halting run of the switch on the
query of a question with an answer, checked by the guard at a word
length `v` at most `w - 8 - D`, outputs `ansWord q b`. -/
theorem switch_ans {p pR pS pC : Program} {K₀ D eR eS eC K C : ℕ} (hsw : SwBack p pR pS pC K₀ D)
    (hS : CSound pR pS pC eR eS eC K C) {n : ℕ} {G : PartialGraph (Fin n)} {q : Qry}
    {b : List ℕ} (hA : Ans G q b) (hK : RankLe K q) {v w : ℕ} (hg : CGuard eR eS eC v q)
    (hC : C ≤ 2 ^ v) (hv : v ≤ w - 8 - D) (hK₀ : K₀ ≤ 2 ^ (w - 8 - D))
    (hl : (qWord q).length < 2 ^ (w - 10 - D)) (hw : D + 14 ≤ w) :
    ∀ o T, RunsTo w p (qWord q) o T → o = ansWord q b := by
  intro o T h
  rw [qWord_parts] at h hl
  obtain ⟨y, z, u, tA, tB, tC, hy, hz, hu, rfl⟩ := hsw w _ _ _ hK₀ hl hw o T h
  exact callee_ans hS hA hK hg hC (by omega) (by omega) hv hy hz hu

theorem swBack_of {p pR pS pC : Program} {K₀ D : ℕ}
    (h : ∀ (w : ℕ) (qA qB qC : List ℕ), K₀ ≤ 2 ^ (w - 8 - D) →
      (swIn qA qB qC).length < 2 ^ (w - 10 - D) → D + 14 ≤ w →
      (∀ y z u tA tB tC, RunsTo (w - 4 - D) pR qA y tA → RunsTo (w - 6 - D) pS qB z tB →
        RunsTo (w - 8 - D) pC qC u tC → y.length ≤ Lax185574Proofs.RamCat.catLim (w - 4) (D + 2) →
        z.length ≤ Lax185574Proofs.RamCat.catLim (w - 6) (D + 2) →
        u.length ≤ Lax185574Proofs.RamCat.catLim (w - 8) (D + 2) →
        ∃ t ≤ K₀ * (tA + tB + tC + y.length + z.length + u.length + 1),
          RunsTo w p (swIn qA qB qC) (y ++ z ++ u) t) ∧
      (∀ o T, RunsTo w p (swIn qA qB qC) o T →
        ∃ y z u tA tB tC, RunsTo (w - 4 - D) pR qA y tA ∧ RunsTo (w - 6 - D) pS qB z tB ∧
          RunsTo (w - 8 - D) pC qC u tC ∧ o = y ++ z ++ u ∧
          y.length ≤ Lax185574Proofs.RamCat.catLim (w - 4) (D + 2) ∧
          z.length ≤ Lax185574Proofs.RamCat.catLim (w - 6) (D + 2) ∧
          u.length ≤ Lax185574Proofs.RamCat.catLim (w - 8) (D + 2))) :
    SwBack p pR pS pC K₀ D := by
  intro w qA qB qC h1 h2 h3 o T hr
  obtain ⟨y, z, u, tA, tB, tC, hy, hz, hu, ho, -⟩ := (h w qA qB qC h1 h2 h3).2 o T hr
  exact ⟨y, z, u, tA, tB, tC, hy, hz, hu, ho⟩

end Lax185574Proofs.CompRam
