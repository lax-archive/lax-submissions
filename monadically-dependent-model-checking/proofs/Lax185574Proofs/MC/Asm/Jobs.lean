import Lax185574Proofs.MC.Asm.Defs
import Lax185574Proofs.JobMap.Main
import Lax185574Proofs.Interface.Shim.MergeLift

/-!
The batched merge lift of the pipeline of thm:mc.

One call of the pipeline per merge step runs the merge lift on the
trees of all vertices. `mergeJobs` builds this callee from the program
of lem:merge-lift with `jobMap`: for every rank `q` there are constants
`c` and `a` such that on the list of jobs `mjobs G q P Q` (the tree of
every vertex with the colors `P ≠ Q`) the program computes the list of
the answers `mans G q P Q` in time `c (n + 1)² (maxLen + 1)^a`, and on
the empty list of jobs the empty list of answers in time `c`.

Two vertices may have the same job word. The answers are then equal,
since both are outputs of the merge-lift program on the same input at a
large word length.
-/

namespace Lax185574Proofs.MC

open Lax185574Proofs.Words.Fast (maxLen)
open Lax808846Proofs.Machine (runsTo_unique)

open Lax808846.Ram Lax808846.RamComputes Lax185574.Computing Lax185574.WordEncoding
open Lax185574.PartialGraphs Lax185574.ConstructionSequences Lax185574.TypeTrees
open Lax185574Proofs.Words

theorem two_pow_ge (N : ℕ) : N ≤ 2 ^ N := (Nat.lt_two_pow_self).le

/-- Two inputs with the same word have the same answer under `Computes`. -/
theorem computes_word_eq {α β : Type*} [WordEncoding α] [WordEncoding β] {p : Program}
    {e c : ℕ} {T : ℕ → ℕ} {a a' : α} {b b' : β} (h : Computes p e c a b T)
    (h' : Computes p e c a' b' T) (ha : toWord a = toWord a') : toWord b = toWord b' := by
  set u := toWord a with hu
  set w := c * (u.length + maxEntry u + 1) ^ e + T (wordLength a) with hw
  have hadm : WordAdmissible e c w u := by
    intro x hx
    refine le_trans ?_ (two_pow_ge w)
    have := le_maxEntry hx
    have : c * (u.length + x + 1) ^ e ≤ c * (u.length + maxEntry u + 1) ^ e := by gcongr
    omega
  have hT : T (wordLength a) ≤ 2 ^ w := le_trans (by omega) (two_pow_ge w)
  have hl : wordLength a' = wordLength a := by simp only [wordLength]; rw [← ha]
  obtain ⟨t, -, hr⟩ := (h w hadm).2 hT u rfl
  have hadm' : WordAdmissible e c w (toWord a') := by rw [← ha]; exact hadm
  obtain ⟨t', -, hr'⟩ := (h' w hadm').2 (by rw [hl]; exact hT) (toWord a') rfl
  rw [← ha] at hr'
  exact (runsTo_unique hr hr').1

/-- What the pipeline needs of the batched merge lift `pJ` with exponent `eJ`. -/
def MJSpec (pJ : Program) (eJ : ℕ) : Prop :=
  ∀ q : ℕ, ∃ c a : ℕ,
    (∀ (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ), P ≠ Q →
      Computes pJ eJ c (mjobs G q P Q) (mans G q P Q)
        (fun _ => c * (n + 1) ^ 2 * (maxLen (mjobs G q P Q) + 1) ^ a)) ∧
    Computes pJ eJ c ([] : List (List ℕ)) ([] : List (List ℕ)) (fun _ => c)

/-- **The batched merge lift.** -/
theorem mergeJobs : ∃ (pJ : Program) (eJ : ℕ), MJSpec pJ eJ := by
  obtain ⟨p, e, hM⟩ := Lax185574Proofs.Shim.MergeLift.exists_program_mergeLift
  obtain ⟨pJ, eJ, hJ⟩ := Lax185574Proofs.JobMap.jobMap (p := p) (e := e)
  refine ⟨pJ, eJ, fun q => ?_⟩
  obtain ⟨c, a, hc⟩ := hM 1 q
  obtain ⟨cJ, aJ, hJc⟩ := hJ c a
  refine ⟨cJ, aJ, fun n G P Q hPQ => ?_, ?_⟩
  · set js := mjobs G q P Q with hjs
    let job : Fin n → List ℕ := fun v => toWord (tree G 1 q ![v], P, Q)
    let ans : Fin n → List ℕ := fun v => toWord (tree (merge G P Q) 1 q ![v])
    have hcv : ∀ v : Fin n, Computes p e c (tree G 1 q ![v], P, Q) (tree (merge G P Q) 1 q ![v])
        (fun m => c * (m + 1) ^ a) := fun v => hc n G 1 ![v] P Q le_rfl hPQ
    classical
    let f : List ℕ → List ℕ := fun j => if h : ∃ v : Fin n, j = job v then ans h.choose else []
    have hf : ∀ v, f (job v) = ans v := by
      intro v
      have h : ∃ v' : Fin n, job v = job v' := ⟨v, rfl⟩
      simp only [f, dif_pos h]
      exact computes_word_eq (hcv h.choose) (hcv v) h.choose_spec.symm
    have hmap : js.map f = mans G q P Q := by
      simp only [hjs, mjobs, mans, List.map_ofFn]
      congr 1; funext v; exact hf v
    have hjob : ∀ j ∈ js, ∀ w, WordAdmissible e c w j → (∀ y t, RunsTo w p j y t → y = f j) ∧
        (c * (j.length + 1) ^ a ≤ 2 ^ w → ∃ t ≤ c * (j.length + 1) ^ a, RunsTo w p j (f j) t) := by
      intro j hj w hw
      obtain ⟨v, rfl⟩ : ∃ v, job v = j := by
        simp only [hjs, mjobs, List.mem_ofFn] at hj; exact hj
      rw [hf v]
      exact ⟨(hcv v w hw).1, fun ht => (hcv v w hw).2 ht _ rfl⟩
    have hlen : js.length = n := by simp [hjs, mjobs]
    intro w hw
    obtain ⟨h1, h2⟩ := hJc js f hjob w hw
    refine ⟨fun y t hr => by rw [h1 y t hr, hmap], fun hT x hx => ?_⟩
    rw [Set.mem_singleton_iff.1 hx]
    rw [hlen] at h2
    obtain ⟨t, ht, hr⟩ := h2 hT
    exact ⟨t, ht, by rw [← hmap]; exact hr⟩
  · intro w hw
    obtain ⟨h1, h2⟩ := hJc [] (fun _ => []) (by simp) w hw
    refine ⟨fun y t hr => by rw [h1 y t hr]; rfl, fun hT x hx => ?_⟩
    rw [Set.mem_singleton_iff.1 hx]
    have e1 : cJ * (([] : List (List ℕ)).length + 1) ^ 2 * (maxLen [] + 1) ^ aJ = cJ := by
      simp [maxLen]
    rw [e1] at h2
    obtain ⟨t, ht, hr⟩ := h2 hT
    exact ⟨t, ht, hr⟩

open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574.DistanceMatrix in
/-- The statement of lem:resolve-lift for the program `pR` with exponent `eR`. -/
def RLSpec (pR : Program) (eR : ℕ) : Prop :=
  ∀ k q : ℕ, ∃ c a : ℕ,
    ∀ (n : ℕ) (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool), 1 ≤ k →
      Computes pR eR c (G, distMatrix G, P, Q, s, family G k q)
        (resolveBy G s P Q, distMatrix (resolveBy G s P Q), family (resolveBy G s P Q) k q)
        (fun _ => c * (n + 1) ^ 2 *
          (maxTreeSize G k q + treeCount G (resolveBy G s P Q) k q + 1) ^ a) ∧
      ∀ b : Fin n, wordLength (tree (resolveBy G s P Q) k q ![b]) ≤
        c * (treeCount G (resolveBy G s P Q) k q + 1) ^ a

end Lax185574Proofs.MC
