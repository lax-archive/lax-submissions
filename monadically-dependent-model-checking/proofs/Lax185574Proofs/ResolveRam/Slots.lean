import Lax185574Proofs.ResolveRam.CallList
import Lax185574Proofs.ResolveRam.Switch5
import Lax185574.ComputeScatterType
import Lax185574.CanonicalForm
import Lax185574Proofs.Interface.Shim.CanonicalForm
import Lax185574Proofs.Interface.Shim.ComputeScatterType
import Lax185574Proofs.Interface.Shim.FarComposition
import Lax185574Proofs.Interface.Shim.RankShift
import Lax185574Proofs.Interface.Shim.ToFarTree

/-!
The five callees of the program of lem:resolve-lift and their answers.

The callee of the loop driver is `switch5` of the rank shift (slot A),
the far tree (slot B), the composition (slot C), the canonical form
(slot E) and the scatter type (slot F). A call gives its query to its
slot and fixed small queries of real instances to the other four
(`qA0`, …, `qF0`), as in thm:mc. The answer of the switch is the
concatenation of the five answers (`rY`).

The programs and constants of the callees are fixed by choice from the
concept statements. The glue program checks the guard `RGuard` of a
call before it asks: the size of the real query plus the size `X` of
the input of the composite, to the power of the exponent of the slot
plus one, fits into the word length. If `X` is at least the constants of
the calls, or the constants fit into the word length, then the real
query is admissible for its callee (`adm_of_guardX`). Then every
halting run of the slot programs gives the answer of the call
(`slots_answer`).
-/

namespace Lax185574Proofs.ResolveRam

open Lax808846.Ram Lax185574.WordEncoding Lax185574.Computing
open Lax185574.PartialGraphs Lax185574.GaifmanGraph Lax185574.TypeTrees
open Lax185574.ScatterTypes Lax185574.FarTrees Lax185574.ResolveLift
open Lax185574.PartialGraphEncoding Lax185574.ConstructionSequences Lax185574.SequenceEncoding
open Lax185574Proofs.TreeAlgo Lax185574Proofs.Words Lax185574Proofs.Simulate
open Lax185574.DistanceMatrix
open Lax3.DistFO (rhoMinus rhoPlus)

/-! ### Admissibility -/

/-- Clause 1 of `Computes`: every halting run at an admissible word
length outputs the answer. -/
def SoundOn {α β : Type*} [WordEncoding α] [WordEncoding β] (p : Program) (e c : ℕ) (a : α)
    (b : β) : Prop :=
  ∀ w : ℕ, WordAdmissible e c w (toWord a) → ∀ (y : List ℕ) (t : ℕ), RunsTo w p (toWord a) y t →
    y = toWord b

theorem soundOn_of {α β : Type*} [WordEncoding α] [WordEncoding β] {p : Program}
    {e c : ℕ} {a : α} {b : β} {T : ℕ → ℕ} (h : Computes p e c a b T) : SoundOn p e c a b :=
  fun w hw => (h w hw).1

theorem SoundOn.mono {α β : Type*} [WordEncoding α] [WordEncoding β] {p : Program}
    {e c c' : ℕ} {a : α} {b : β} (h : SoundOn p e c a b) (hc : c ≤ c') : SoundOn p e c' a b :=
  fun w hw => h w fun v hv => le_trans (Nat.mul_le_mul_right _ hc) (hw v hv)

/-- The constant of a fixed word for a constant `c` and an exponent `e`. -/
def fixCst (e c : ℕ) (u : List ℕ) : ℕ := c * (u.length + maxEntry u + 1) ^ e

theorem adm_of_fix {e c v : ℕ} {u : List ℕ} (h : fixCst e c u ≤ 2 ^ v) :
    WordAdmissible e c v u := by
  intro x hx
  refine le_trans ?_ h
  unfold fixCst
  have := le_maxEntry hx
  gcongr

/-- **Admissibility from the guard.** -/
theorem adm_of_guardX {e c v X : ℕ} {u : List ℕ}
    (hg : (u.length + maxEntry u + 1 + X) ^ (e + 1) ≤ 2 ^ v) (hc : c ≤ X ∨ c ^ (e + 1) ≤ 2 ^ v) :
    WordAdmissible e c v u := by
  intro x hx
  have hxm := le_maxEntry hx
  rcases hc with hc | hc
  · refine le_trans ?_ hg
    rw [pow_succ']
    exact Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) _)
  · rcases le_total c (u.length + maxEntry u + 1 + X) with h | h
    · refine le_trans ?_ hg
      rw [pow_succ']
      exact Nat.mul_le_mul h (Nat.pow_le_pow_left (by omega) _)
    · refine le_trans ?_ hc
      rw [pow_succ']
      exact Nat.mul_le_mul le_rfl (Nat.pow_le_pow_left (by omega) _)

/-! ### The programs of the callees -/

/-- The rank shift. -/
noncomputable def pSh : Program := Lax185574Proofs.Shim.RankShift.exists_program_shift.choose
noncomputable def eSh : ℕ := Lax185574Proofs.Shim.RankShift.exists_program_shift.choose_spec.choose
theorem hSh : ∀ k q : ℕ, ∃ c a : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ)
    (u : Fin ℓ → Fin n), 1 ≤ ℓ → ℓ ≤ k →
      Computes pSh eSh c (tree G k (q + 1) u) (tree G (k + 1) q u) (fun m => c * (m + 1) ^ a) :=
  Lax185574Proofs.Shim.RankShift.exists_program_shift.choose_spec.choose_spec
noncomputable def cSh (k q : ℕ) : ℕ := (hSh k q).choose
noncomputable def aSh (k q : ℕ) : ℕ := (hSh k q).choose_spec.choose
theorem hSh' (k q : ℕ) : ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n),
    1 ≤ ℓ → ℓ ≤ k → Computes pSh eSh (cSh k q) (tree G k (q + 1) u) (tree G (k + 1) q u)
      (fun m => cSh k q * (m + 1) ^ aSh k q) :=
  (hSh k q).choose_spec.choose_spec

/-- The far tree. -/
noncomputable def pFt : Program := Lax185574Proofs.Shim.ToFarTree.exists_program_ftree.choose
noncomputable def eFt : ℕ := Lax185574Proofs.Shim.ToFarTree.exists_program_ftree.choose_spec.choose
theorem hFt : ∀ k q : ℕ, ∃ c a : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ)
    (u : Fin ℓ → Fin n), 1 ≤ ℓ → ℓ ≤ k →
      Computes pFt eFt c (tree G k (q + 1) u, stp G k (q + 1)) (ftree G k (q + 1) u)
        (fun _ => c * (wordLength (stp G k (q + 1)) + 1) * (wordLength (tree G k (q + 1) u) + 1) ^ a) :=
  Lax185574Proofs.Shim.ToFarTree.exists_program_ftree.choose_spec.choose_spec
noncomputable def cFt (k q : ℕ) : ℕ := (hFt k q).choose
noncomputable def aFt (k q : ℕ) : ℕ := (hFt k q).choose_spec.choose
theorem hFt' (k q : ℕ) : ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ : ℕ) (u : Fin ℓ → Fin n),
    1 ≤ ℓ → ℓ ≤ k → Computes pFt eFt (cFt k q) (tree G k (q + 1) u, stp G k (q + 1)) (ftree G k (q + 1) u)
      (fun _ => cFt k q * (wordLength (stp G k (q + 1)) + 1) *
        (wordLength (tree G k (q + 1) u) + 1) ^ aFt k q) :=
  (hFt k q).choose_spec.choose_spec

/-- The composition. -/
noncomputable def pCo : Program := Lax185574Proofs.Shim.FarComposition.exists_program_compose.choose
noncomputable def eCo : ℕ := Lax185574Proofs.Shim.FarComposition.exists_program_compose.choose_spec.choose
theorem hCo : ∀ k q : ℕ, ∃ c a : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ₁ ℓ₂ : ℕ)
    (u₁ : Fin ℓ₁ → Fin n) (u₂ : Fin ℓ₂ → Fin n), 1 ≤ ℓ₁ → 1 ≤ ℓ₂ → ℓ₁ + ℓ₂ ≤ k →
      (∀ i j, ¬ WithinDist G.resolved (rhoMinus k q) (u₁ i) (u₂ j)) →
      Computes pCo eCo c (tree G k q u₁, tree G k q u₂) (tree G k q (Fin.append u₁ u₂))
        (fun m => c * (m + 1) ^ a) :=
  Lax185574Proofs.Shim.FarComposition.exists_program_compose.choose_spec.choose_spec
noncomputable def cCo (k q : ℕ) : ℕ := (hCo k q).choose
noncomputable def aCo (k q : ℕ) : ℕ := (hCo k q).choose_spec.choose
theorem hCo' (k q : ℕ) : ∀ (n : ℕ) (G : PartialGraph (Fin n)) (ℓ₁ ℓ₂ : ℕ)
    (u₁ : Fin ℓ₁ → Fin n) (u₂ : Fin ℓ₂ → Fin n), 1 ≤ ℓ₁ → 1 ≤ ℓ₂ → ℓ₁ + ℓ₂ ≤ k →
      (∀ i j, ¬ WithinDist G.resolved (rhoMinus k q) (u₁ i) (u₂ j)) →
      Computes pCo eCo (cCo k q) (tree G k q u₁, tree G k q u₂) (tree G k q (Fin.append u₁ u₂))
        (fun m => cCo k q * (m + 1) ^ aCo k q) :=
  (hCo k q).choose_spec.choose_spec

/-- The canonical form. -/
noncomputable def pCa : Program := Lax185574Proofs.Shim.CanonicalForm.exists_program_canonical.choose
noncomputable def eCa : ℕ := Lax185574Proofs.Shim.CanonicalForm.exists_program_canonical.choose_spec.choose
noncomputable def cCa : ℕ :=
  Lax185574Proofs.Shim.CanonicalForm.exists_program_canonical.choose_spec.choose_spec.choose
noncomputable def aCa : ℕ :=
  Lax185574Proofs.Shim.CanonicalForm.exists_program_canonical.choose_spec.choose_spec.choose_spec.choose
theorem hCa : ∀ (α : Type) [WordEncoding α] (l : List α),
    Computes pCa eCa cCa (l.map toWord) (finsetOf {x | x ∈ l}) (fun m => cCa * (m + 1) ^ aCa) :=
  Lax185574Proofs.Shim.CanonicalForm.exists_program_canonical.choose_spec.choose_spec.choose_spec.choose_spec

/-- The scatter type. -/
noncomputable def pSt : Program := Lax185574Proofs.Shim.ComputeScatterType.exists_program_stp.choose
noncomputable def eSt : ℕ := Lax185574Proofs.Shim.ComputeScatterType.exists_program_stp.choose_spec.choose
theorem hSt : ∀ k q : ℕ, ∃ c a : ℕ, ∀ (n : ℕ) (G : PartialGraph (Fin n)), 1 ≤ k → 1 ≤ n →
    Computes pSt eSt c (G, k, q, distMatrix G, family G k q) (stp G k q)
      (fun _ => c * (n + 1) ^ 2 * (maxTreeSize G k q + 1) ^ a) :=
  Lax185574Proofs.Shim.ComputeScatterType.exists_program_stp.choose_spec.choose_spec
noncomputable def cSt (k q : ℕ) : ℕ := (hSt k q).choose
noncomputable def aSt (k q : ℕ) : ℕ := (hSt k q).choose_spec.choose
theorem hSt' (k q : ℕ) : ∀ (n : ℕ) (G : PartialGraph (Fin n)), 1 ≤ k → 1 ≤ n →
    Computes pSt eSt (cSt k q) (G, k, q, distMatrix G, family G k q) (stp G k q)
      (fun _ => cSt k q * (n + 1) ^ 2 * (maxTreeSize G k q + 1) ^ aSt k q) :=
  (hSt k q).choose_spec.choose_spec

/-! ### Fixed small queries -/

/-- The partial graph on one vertex of color `0`. -/
def G1 : PartialGraph (Fin 1) := unresolved fun _ => 0

/-- The partial graph on two vertices of color `0`, with no resolved pairs. -/
def G2 : PartialGraph (Fin 2) := unresolved fun _ => 0

theorem g2_far (r : ℕ) : ¬ WithinDist G2.resolved r 0 1 := by
  rintro ⟨p, -⟩
  cases p with
  | cons h _ =>
    simp [G2, unresolved, PartialGraph.resolved] at h

noncomputable def qA0 : List ℕ := toWord (tree G1 1 (0 + 1) ![(0 : Fin 1)])
noncomputable def yA0 : List ℕ := toWord (tree G1 (1 + 1) 0 ![(0 : Fin 1)])
noncomputable def qB0 : List ℕ := toWord (tree G1 1 (0 + 1) ![(0 : Fin 1)], stp G1 1 (0 + 1))
noncomputable def yB0 : List ℕ := toWord (ftree G1 1 (0 + 1) ![(0 : Fin 1)])
noncomputable def qC0 : List ℕ := toWord (tree G2 2 0 ![(0 : Fin 2)], tree G2 2 0 ![(1 : Fin 2)])
noncomputable def yC0 : List ℕ :=
  toWord (tree G2 2 0 (Fin.append ![(0 : Fin 2)] ![(1 : Fin 2)]))
def qE0 : List ℕ := toWord ([] : List (List ℕ))
def yE0 : List ℕ := canonW []
noncomputable def qF0 : List ℕ := toWord (G1, (1 : ℕ), (0 : ℕ), distMatrix G1, family G1 1 0)
noncomputable def yF0 : List ℕ := toWord (stp G1 1 0)

/-- The constant that the word lengths must exceed for the fixed queries. -/
noncomputable def fixBig : ℕ :=
  fixCst eSh (cSh 1 0) qA0 + fixCst eFt (cFt 1 0) qB0 + fixCst eCo (cCo 2 0) qC0 +
    fixCst eCa cCa qE0 + fixCst eSt (cSt 1 0) qF0

theorem soundA0 {v : ℕ} (h : fixBig ≤ 2 ^ v) {y : List ℕ} {t : ℕ} (hr : RunsTo v pSh qA0 y t) :
    y = yA0 := by
  have h' : fixCst eSh (cSh 1 0) qA0 ≤ 2 ^ v := by unfold fixBig at h; omega
  exact soundOn_of (hSh' 1 0 1 G1 1 ![0] le_rfl le_rfl) v (adm_of_fix h') y t hr

theorem soundB0 {v : ℕ} (h : fixBig ≤ 2 ^ v) {y : List ℕ} {t : ℕ} (hr : RunsTo v pFt qB0 y t) :
    y = yB0 := by
  have h' : fixCst eFt (cFt 1 0) qB0 ≤ 2 ^ v := by unfold fixBig at h; omega
  exact soundOn_of (hFt' 1 0 1 G1 1 ![0] le_rfl le_rfl) v (adm_of_fix h') y t hr

theorem soundC0 {v : ℕ} (h : fixBig ≤ 2 ^ v) {y : List ℕ} {t : ℕ} (hr : RunsTo v pCo qC0 y t) :
    y = yC0 := by
  have h' : fixCst eCo (cCo 2 0) qC0 ≤ 2 ^ v := by unfold fixBig at h; omega
  exact soundOn_of (hCo' 2 0 2 G2 1 1 ![0] ![1] le_rfl le_rfl le_rfl
    (fun i j => by rw [Fin.fin_one_eq_zero i, Fin.fin_one_eq_zero j]; exact g2_far _)) v
    (adm_of_fix h') y t hr

theorem soundE0 {v : ℕ} (h : fixBig ≤ 2 ^ v) {y : List ℕ} {t : ℕ} (hr : RunsTo v pCa qE0 y t) :
    y = yE0 := by
  have h' : fixCst eCa cCa qE0 ≤ 2 ^ v := by unfold fixBig at h; omega
  have hc := soundOn_of (hCa RawW ([] : List RawW)) v (adm_of_fix h') y t hr
  rw [hc]; exact (canonW_raw []).1

theorem soundF0 {v : ℕ} (h : fixBig ≤ 2 ^ v) {y : List ℕ} {t : ℕ} (hr : RunsTo v pSt qF0 y t) :
    y = yF0 := by
  have h' : fixCst eSt (cSt 1 0) qF0 ≤ 2 ^ v := by unfold fixBig at h; omega
  exact soundOn_of (hSt' 1 0 1 G1 le_rfl le_rfl) v (adm_of_fix h') y t hr

end Lax185574Proofs.ResolveRam
