import Lax185574Proofs.ShiftRam.Glue
import Lax185574Proofs.ShiftRam.Answer

/-!
The two rounds of the glue program of the rank shift, compiled, at the
word lengths of the loop driver.
-/

namespace Lax185574Proofs.ShiftRam

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax185574Proofs.Words Lax185574Proofs.Simulate Lax185574Proofs.RamSim
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo

/-- The scalars and arrays of the glue program. -/
def layout : Layout :=
  ⟨["tg", "sl", "m", "w", "i", "hk", "hq", "hl", "xp", "e1", "e2", "e3", "vv", "ev", "y", "ne", "fr",
    "fd", "cf", "j", "ln"], ["x"], 6⟩

theorem glue_ok : Com.Ok layout glue := by
  simp [glue, round0, round1, copyLoop, readTree, cpList, cpFrame, cpEntries, cpEntry, findCmd,
    skipList, skipBody, findBody, forUp, wHead, wChild, wJ, layout, Com.Ok, Cond.Ok, condExpr, Expr.Ok]

/-- The compiled glue program. -/
def glueProg : Program := compileProgram layout glue

/-- The size factor of the layout. -/
def lsz : ℕ := layout.temps + 2 + layout.scalars.length + layout.arrays.length + 1

theorem lsz_eq : lsz = 31 := rfl

theorem lpU_first (x : List ℕ) : lpU x (lpA0 x) [] = [0, x.length] ++ x ++ [0] := by
  simp [lpU, lpA0]

theorem lpU_second (x a : List ℕ) (b : List ℕ) (ha1 : a.getD 1 0 = 0) (ha2 : a.getD 2 0 = 0)
    (ha0 : a.getD 0 0 = 1) : lpU x a b = [1, 0, b.length] ++ b := by
  simp only [List.getD_eq_getElem?_getD] at ha0 ha1 ha2
  simp [lpU, ha1, ha2, ha0]

theorem child_infix {h ℓ : ℕ} {t : Node (h + 1) ℓ} {a : Fin ℓ × Node h (ℓ + 1)}
    (ha : a ∈ Node.exts t) : toWord a.2 <:+: toWord t := by
  have h1 : toWord a ∈ (Node.exts t).words := mem_words.mpr ⟨a, ha, rfl⟩
  have h2 : (toWord a).length :: toWord a <:+: frames (Node.exts t).words :=
    List.infix_of_mem_flatten (List.mem_map.mpr ⟨_, h1, rfl⟩)
  have h3 : toWord a.2 <:+: (toWord a).length :: toWord a := by
    rw [toWord_ext]
    exact (List.suffix_cons _ _).isInfix.trans (List.suffix_cons _ _).isInfix
  have h4 : frames (Node.exts t).words <:+: toWord t := by
    rw [toWord_node_succ, toWord_words (Finset.words (Node.exts t))]
    exact (List.suffix_cons _ _).isInfix.trans (List.suffix_append _ _).isInfix
  exact h3.trans (h2.trans h4)

/-- **The first round, compiled.** -/
theorem shift_g0 {v : ℕ} (k q ℓ : ℕ) (t : Node (q + 1) ℓ) (hex : ∃ a ∈ Node.exts t, a.1.val = 0)
    (Bv : ℕ) (hv : ∀ y ∈ [k, q + 1, ℓ] ++ toWord t, y + 1 < Bv)
    (hB : 4 * (toWord t).length + 30 < Bv) (hS : lsz * Bv ≤ 2 ^ v) :
    ∃ a ∈ Node.exts t, a.1.val = 0 ∧
      (∃ tm ≤ 3100 * ((toWord t).length + 3) + 200 * ℓ + 3001,
        RunsTo v glueProg (lpU ([k, q + 1, ℓ] ++ toWord t) (lpA0 ([k, q + 1, ℓ] ++ toWord t)) [])
          ([1, 0, 0, k + 1, q, ℓ + 1] ++ toWord a.2 ++ (ℓ :: List.range ℓ)) tm) ∧
      ∀ o tm, RunsTo v glueProg (lpU ([k, q + 1, ℓ] ++ toWord t) (lpA0 ([k, q + 1, ℓ] ++ toWord t)) [])
        o tm → o = [1, 0, 0, k + 1, q, ℓ + 1] ++ toWord a.2 ++ (ℓ :: List.range ℓ) := by
  set ext : String → ℕ := fun s => if s = "x" then (toWord t).length + 3 else 0 with hext
  obtain ⟨σ', hr, a, ha, ha0, hout⟩ := glue_round0 Bv ext k q ℓ t hex (by simp [hext])
    hv (by simp [hext] <;> omega)
  have hlen : ([k, q + 1, ℓ] ++ toWord t).length = (toWord t).length + 3 := by simp <;> omega
  rw [lpU_first, hlen]
  obtain ⟨h1, h2⟩ := glue_runsTo glue_ok (B := Bv) (v := v) (ext := ext) (by omega) hS
    (fun y hy => by
      rcases List.mem_append.mp hy with h | h
      · rcases List.mem_append.mp h with h | h
        · simp at h; omega
        · have := hv y h; omega
      · simp at h; omega)
    hr
  rw [hout] at h1 h2
  refine ⟨a, ha, ha0, ?_, h2⟩
  obtain ⟨tm, htm, hrun⟩ := h1
  refine ⟨tm, le_trans htm ?_, hrun⟩
  simp only [Layout.const, hext, if_true]
  omega

/-- **The second round, compiled.** -/
theorem shift_g1 {v : ℕ} (x a b : List ℕ) (ha1 : a.getD 1 0 = 0) (ha2 : a.getD 2 0 = 0)
    (ha0 : a.getD 0 0 = 1) (Bv : ℕ) (hb : ∀ y ∈ b, y < Bv) (hbB : b.length + 2 < Bv)
    (hS : lsz * Bv ≤ 2 ^ v) :
    (∃ tm ≤ 140 * b.length + 301, RunsTo v glueProg (lpU x a b) (0 :: b) tm) ∧
      ∀ o tm, RunsTo v glueProg (lpU x a b) o tm → o = 0 :: b := by
  rw [lpU_second x a b ha1 ha2 ha0]
  obtain ⟨σ', hr, hout⟩ := glue_round1 Bv (fun _ => 0) b hb hbB
  obtain ⟨h1, h2⟩ := glue_runsTo glue_ok (B := Bv) (v := v) (ext := fun _ => 0) (by omega) hS
    (fun y hy => by
      rcases List.mem_append.mp hy with h | h
      · simp at h; omega
      · exact hb y h) hr
  rw [hout] at h1 h2
  obtain ⟨tm, htm, hrun⟩ := h1
  exact ⟨⟨tm, le_trans htm (by simp only [Layout.const]; omega), hrun⟩, h2⟩

end Lax185574Proofs.ShiftRam
