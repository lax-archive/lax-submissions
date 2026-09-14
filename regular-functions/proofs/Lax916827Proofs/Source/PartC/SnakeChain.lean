/-
**Telescoping a chain of pieces.**

Stage 1 of the induction step of the book's snake lemma produces an annotation
of the input which describes the run of `M` as a chain of pieces: the first
piece starts in the initial configuration, every piece leads from one
configuration of the run to the next one, and the last piece ends when the run
halts.  This file contains the purely combinatorial step that turns such a chain
into the statement that the concatenation of the outputs of the pieces is the
output of the run (`TwoWay.runOut_of_chain`), and the reindexing of a doubly
indexed family of pieces -- one index for the pair of neighbouring blocks, one
for the slot inside the pair -- as a single chain (`Transducers.flatMap_range_mul`).
-/
import Lax916827Proofs.Source.PartC.SnakeWinRun
open Lax765601Proofs Lax765601Proofs.Transducers Lax132576Proofs Lax132576Proofs.Transducers

namespace Lax916827Proofs.Transducers

/-- A doubly indexed concatenation, read as a single one. -/
lemma flatMap_range_mul {C : Type} (f : ℕ → ℕ → List C) (R : ℕ) (hR : 0 < R) :
    ∀ m : ℕ, (List.range m).flatMap (fun i => (List.range R).flatMap (fun r => f i r))
      = (List.range (m * R)).flatMap (fun j => f (j / R) (j % R)) := by
  intro m
  induction m with
  | zero => simp
  | succ m ih =>
      have hsplit : List.range ((m + 1) * R) = List.range (m * R) ++ List.range' (m * R) R := by
        rw [show (m + 1) * R = m * R + R by ring, List.range_eq_range',
          List.range_eq_range', ← List.range'_append_1]
        simp
      rw [List.range_succ, List.flatMap_append, ih, hsplit, List.flatMap_append]
      congr 1
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [show List.range' (m * R) R = (List.range R).map (fun r => m * R + r) by
        rw [List.range_eq_range', List.map_add_range']; simp]
      rw [List.flatMap_map]
      refine List.flatMap_congr ?_
      intro r hr
      have hrR : r < R := List.mem_range.1 hr
      have h1 : (m * R + r) / R = m := by
        rw [Nat.mul_comm, Nat.mul_add_div hR, Nat.div_eq_of_lt hrR, Nat.add_zero]
      have h2 : (m * R + r) % R = r := by
        rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hrR]
      simp only [h1, h2]

namespace TwoWay

variable {A B Q : Type}

/-- **The chain of the pieces**: from a configuration of the run, the pieces
`j, j+1, …, n-1` lead to the halting configuration, and their outputs
concatenate to the output produced from that configuration on. -/
lemma outRange_of_chain (M : TwoWay A B Q) (w : List A) (n : ℕ) (g : ℕ → List B)
    (c : ℕ → ℕ) (st : ℕ → Q)
    (hchain : ∀ j < n, ∀ t, cfgAt M w t = some (Cfg.conf (w.take (c j)) (st j) (w.drop (c j))) →
      ∃ d, outRange M w t (t + d) = g j ∧
        (if j + 1 = n then cfgAt M w (t + d) = some Cfg.halt
          else cfgAt M w (t + d)
            = some (Cfg.conf (w.take (c (j + 1))) (st (j + 1)) (w.drop (c (j + 1)))))) :
    ∀ (D j : ℕ), n - j ≤ D → ∀ t, j < n →
      cfgAt M w t = some (Cfg.conf (w.take (c j)) (st j) (w.drop (c j))) →
      ∃ T, cfgAt M w T = some Cfg.halt ∧
        outRange M w t T = ((List.range' j (n - j)).map g).flatten := by
  intro D
  induction D with
  | zero => intro j hD t hjn _; omega
  | succ D ih =>
      intro j hD t hjn ht
      obtain ⟨d, hout, hnext⟩ := hchain j hjn t ht
      by_cases hlast : j + 1 = n
      · rw [if_pos hlast] at hnext
        refine ⟨t + d, hnext, ?_⟩
        rw [show n - j = 1 by omega]
        simpa using hout
      · rw [if_neg hlast] at hnext
        obtain ⟨T, hT, hrest⟩ := ih (j + 1) (by omega) (t + d) (by omega) hnext
        refine ⟨T, hT, ?_⟩
        have hle : t + d ≤ T := by
          by_contra hcon
          have hnone : cfgAt M w (t + d) = none :=
            cfgAt_none_mono M w (by omega) (cfgAt_halt_succ M w hT)
          rw [hnext] at hnone; simp at hnone
        rw [outRange_split M w (show t ≤ t + d by omega) hle, hout, hrest,
          show n - j = (n - (j + 1)) + 1 by omega, List.range'_succ]
        simp

/-- **The output of the run is the concatenation of the outputs of a chain of
pieces** that starts in the initial configuration. -/
theorem runOut_of_chain (M : TwoWay A B Q) (w : List A) (n : ℕ) (hn : 0 < n) (g : ℕ → List B)
    (c : ℕ → ℕ) (st : ℕ → Q) (hc0 : c 0 = 0) (hst0 : st 0 = M.init)
    (hchain : ∀ j < n, ∀ t, cfgAt M w t = some (Cfg.conf (w.take (c j)) (st j) (w.drop (c j))) →
      ∃ d, outRange M w t (t + d) = g j ∧
        (if j + 1 = n then cfgAt M w (t + d) = some Cfg.halt
          else cfgAt M w (t + d)
            = some (Cfg.conf (w.take (c (j + 1))) (st (j + 1)) (w.drop (c (j + 1)))))) :
    runOut M w = (List.range n).flatMap g := by
  classical
  have hstart : cfgAt M w 0 = some (Cfg.conf (w.take (c 0)) (st 0) (w.drop (c 0))) := by
    rw [hc0, hst0]; simp
  obtain ⟨T, hT, hout⟩ :=
    outRange_of_chain M w n g c st hchain n 0 (by omega) 0 hn hstart
  have hex : ∃ T, cfgAt M w T = some Cfg.halt := ⟨T, hT⟩
  rw [runOut, dif_pos hex, halt_time_unique M w hex.choose_spec hT, hout,
    List.flatMap_def, List.range_eq_range']
  simp

end TwoWay

end Lax916827Proofs.Transducers
