import Lax235315Proofs.Construction.WelzlLog
import Lax235315Proofs.Construction.WelzlStraight
import Lax11Proofs.CCGraph
import Mathlib.Tactic

/-! Reading the CSR prefix and initializing the Welzl driver. -/

namespace Lax235315Proofs.Construction.WelzlSetup

open Lax11.GraphEncoding
open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax235315Proofs.Construction.WelzlProgram
open Lax235315Proofs.Construction.WelzlStraight
open Lax235315Proofs.Construction.WelzlLog

private lemma getD_take {l : List ℕ} {k i : ℕ} (h : i < k) :
    (l.take k).getD i 0 = l.getD i 0 := by
  simp [List.getD_eq_getElem?_getD, h]

private lemma getD_drop {l : List ℕ} {k i : ℕ} :
    (l.drop k).getD i 0 = l.getD (k + i) 0 := by
  simp [List.getD_eq_getElem?_getD]

private lemma getD_cons_cons (a b : ℕ) (l : List ℕ) (i : ℕ) :
    (a :: b :: l).getD (2 + i) 0 = l.getD i 0 := by
  have h : 2 + i = i + 1 + 1 := by omega
  rw [h]
  simp [List.getD_eq_getElem?_getD]

/-- Array extents used by the source-level run. -/
def welzlExt (n m qpow : ℕ) (a : String) : ℕ :=
  if a = "off" then n + 1 else if a = "tgt" then 2 * m else
    if a = "count" then qpow else n

@[simp] lemma welzlExt_off (n m q : ℕ) : welzlExt n m q "off" = n + 1 := by
  simp [welzlExt]

@[simp] lemma welzlExt_tgt (n m q : ℕ) : welzlExt n m q "tgt" = 2 * m := by
  simp [welzlExt]

@[simp] lemma welzlExt_count (n m q : ℕ) : welzlExt n m q "count" = q := by
  simp [welzlExt]

@[simp] lemma welzlExt_other (n m q : ℕ) {a : String}
    (hoff : a ≠ "off") (htgt : a ≠ "tgt") (hcount : a ≠ "count") :
    welzlExt n m q a = n := by
  simp [welzlExt, hoff, htgt, hcount]

/-- Split an encoded word into its header, offset block, and target block. -/
lemma encodesGraph_split {x : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)}
    (hx : EncodesGraph x n G) :
    ∃ (m : ℕ) (ys zs : List ℕ),
      edgeCount x = m ∧ x = n :: m :: (ys ++ zs) ∧
      ys.length = n + 1 ∧ zs.length = 2 * m ∧
      (∀ i < n + 1, ys.getD i 0 = offset x i) ∧
      (∀ j < 2 * m, zs.getD j 0 = target x j) := by
  let m := edgeCount x
  have hlen := hx.length_eq
  obtain ⟨rest, hxr⟩ : ∃ rest, x = n :: m :: rest := by
    rcases x with _ | ⟨a, _ | ⟨b, rest⟩⟩
    · simp at hlen
      omega
    · simp at hlen
      omega
    · have ha : a = n := by simpa [vertexCount] using hx.vertexCount_eq
      have hb : b = m := by rfl
      exact ⟨rest, by rw [ha, hb]⟩
  have hrest : rest.length = 1 + n + 2 * m := by
    have hxlen : x.length = rest.length + 2 := by rw [hxr]; simp
    dsimp [m]
    omega
  let ys := rest.take (n + 1)
  let zs := rest.drop (n + 1)
  refine ⟨m, ys, zs, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hxr]
    simp [ys, zs]
  · simp [ys, hrest]
    omega
  · simp [zs, hrest]
    omega
  · intro i hi
    change (rest.take (n + 1)).getD i 0 = offset x i
    rw [getD_take hi, offset, hxr, getD_cons_cons]
  · intro j hj
    change (rest.drop (n + 1)).getD j 0 = target x j
    rw [getD_drop, target, hx.vertexCount_eq, hxr]
    rw [show 3 + n + j = 2 + (n + 1 + j) by omega,
      getD_cons_cons]

/-- The graph-reading phase copies the CSR blocks literally and leaves the
random suffix untouched. -/
lemma readGraph_run {B c n m qpow : ℕ} {x bits : List ℕ}
    {G : SimpleGraph (Fin n)} (hx : EncodesGraph x n G)
    (hm : edgeCount x = m)
    {ys zs : List ℕ}
    (hxsplit : x = n :: m :: (ys ++ zs))
    (hys : ys.length = n + 1) (hzs : zs.length = 2 * m)
    (hysval : ∀ i < n + 1, ys.getD i 0 = offset x i)
    (hzsval : ∀ j < 2 * m, zs.getD j 0 = target x j)
    (hB : x.length ≤ B) :
    ∃ σ' O T, Run B readGraph
        (initEnv (welzlExt n m qpow) ((c :: x) ++ bits)) σ'
        (12 * n + 24 * m + 35) ∧
      σ'.vars "c" = c ∧ σ'.vars "n" = n ∧ σ'.vars "m" = m ∧
      σ'.arrs "off" = arrOf (n + 1) O ∧
      σ'.arrs "tgt" = arrOf (2 * m) T ∧
      (∀ i < n + 1, O i = offset x i) ∧
      (∀ j < 2 * m, T j = target x j) ∧
      σ'.inp = bits ∧ σ'.out = [] := by
  have hlen := hx.length_eq
  rw [hm] at hlen
  have hnB : n < B := by omega
  have hmB : m < B := by omega
  have hn1B : n + 1 < B := by omega
  have h2mB : 2 * m < B := by omega
  have hysB : ∀ v ∈ ys, v < B := by
    intro v hv
    apply lt_of_lt_of_le (Lax11Proofs.CC.mem_lt_length hx (by
      rw [hxsplit]
      simp only [List.mem_cons]
      exact Or.inr (Or.inr (List.mem_append_left _ hv)))) hB
  have hzsB : ∀ v ∈ zs, v < B := by
    intro v hv
    apply lt_of_lt_of_le (Lax11Proofs.CC.mem_lt_length hx (by
      rw [hxsplit]
      simp only [List.mem_cons]
      exact Or.inr (Or.inr (List.mem_append_right _ hv)))) hB
  let σ₀ := initEnv (welzlExt n m qpow) ((c :: x) ++ bits)
  let σ₁ := { σ₀.setVar "c" c with inp := n :: m :: (ys ++ zs) ++ bits }
  let σ₂ := { σ₁.setVar "n" n with inp := m :: (ys ++ zs) ++ bits }
  let σ₃ := { σ₂.setVar "m" m with inp := (ys ++ zs) ++ bits }
  let σ₄ := σ₃.setVar "len" (n + 1)
  have rinp : σ₀.inp = c :: n :: m :: (ys ++ zs) ++ bits := by
    simp [σ₀, initEnv, hxsplit]
  have r₁ : Run B (.read "c") σ₀ σ₁ 1 := by
    apply Run.read
    simpa [σ₁] using rinp
  have r₂ : Run B (.read "n") σ₁ σ₂ 1 := by
    apply Run.read
    simp [σ₁]
  have r₃ : Run B (.read "m") σ₂ σ₃ 1 := by
    apply Run.read
    simp [σ₂]
  have r₄ : Run B (.assign "len" (.add (.var "n") (.lit 1))) σ₃ σ₄ 4 := by
    apply Run.assign
    exact evalB_bin (evalB_var (by simp [σ₃, σ₂, σ₁]; exact hnB))
      (evalB_lit (by omega)) hn1B
  have hoff₄ : σ₄.arrs "off" = arrOf (n + 1) (fun _ => 0) := by
    simp [σ₄, σ₃, σ₂, σ₁, σ₀, initEnv, replicate_eq_arrOf]
  obtain ⟨σ₅, O, r₅, hoff₅, hO, hinp₅⟩ :=
    readArray_run (B := B) (a := "off") (lim := "len")
      (ys := ys) (rest := zs ++ bits)
      (by decide) (by decide) hoff₄ (by simp [σ₄]) hys
      (by simp [σ₄, σ₃, σ₂, σ₁, List.append_assoc]) hn1B hysB
  let σ₆ := σ₅.setVar "len" (2 * m)
  have hm₅ : σ₅.vars "m" = m := by
    rw [r₅.frame_var "m" (by decide)]
    simp [σ₄, σ₃, σ₂, σ₁]
  have r₆ : Run B (.assign "len" (.mul (.lit 2) (.var "m"))) σ₅ σ₆ 4 := by
    apply Run.assign
    exact evalB_bin (evalB_lit (by omega))
      (show (Expr.var "m").evalB B σ₅ = some m from by
        rw [evalB_var_iff]
        exact ⟨hm₅.symm, by rw [hm₅]; exact hmB⟩)
      (by simpa [Nat.mul_comm] using h2mB)
  have htgt₆ : σ₆.arrs "tgt" = arrOf (2 * m) (fun _ => 0) := by
    simp [σ₆, r₅.frame_arr "tgt" (by decide), σ₄, σ₃, σ₂, σ₁, σ₀,
      initEnv, replicate_eq_arrOf]
  obtain ⟨σ₇, T, r₇, htgt₇, hT, hinp₇⟩ :=
    readArray_run (B := B) (a := "tgt") (lim := "len")
      (ys := zs) (rest := bits)
      (by decide) (by decide) htgt₆ (by simp [σ₆]) hzs
      (by simp [σ₆, hinp₅]) h2mB hzsB
  refine ⟨σ₇, O, T, ?_, ?_⟩
  · have rr := r₁.seq (r₂.seq (r₃.seq (r₄.seq (r₅.seq (r₆.seq r₇)))))
    change Run B readGraph σ₀ σ₇ (12 * n + 24 * m + 35)
    simpa [readGraph, seqs] using rr.mono (by omega)
  · refine ⟨?_, ?_, ?_, ?_, htgt₇, ?_, ?_, hinp₇, ?_⟩
    · rw [r₇.frame_var "c" (by decide), r₆.frame_var "c" (by decide),
        r₅.frame_var "c" (by decide)]
      simp [σ₄, σ₃, σ₂, σ₁]
    · rw [r₇.frame_var "n" (by decide), r₆.frame_var "n" (by decide),
        r₅.frame_var "n" (by decide)]
      simp [σ₄, σ₃, σ₂, σ₁]
    · rw [r₇.frame_var "m" (by decide), r₆.frame_var "m" (by decide),
        r₅.frame_var "m" (by decide)]
      simp [σ₄, σ₃, σ₂, σ₁]
    · rw [r₇.frame_arr "off" (by decide), r₆.frame_arr "off" (by decide)]
      exact hoff₅
    · intro i hi
      rw [hO i hi, hysval i hi]
    · intro j hj
      rw [hT j hj, hzsval j hj]
    · rw [r₇.out_eq (by decide), r₆.out_eq (by decide), r₅.out_eq (by decide),
        r₄.out_eq (by decide), r₃.out_eq (by decide), r₂.out_eq (by decide),
        r₁.out_eq (by decide)]
      rfl

/-- The deterministic initialization phase computes the exact logarithm,
fills both active sides, and zeros the reconstruction counters. -/
lemma initializeWelzl_run {B n : ℕ} {σ : Env} {fA fB : ℕ → ℕ}
    (hn : σ.vars "n" = n)
    (hA : σ.arrs "activeA" = arrOf n fA)
    (hBside : σ.arrs "activeB" = arrOf n fB)
    (hpowB : 2 ^ Nat.clog 2 n < B)
    (hlogB : Nat.clog 2 n + 1 < B)
    (hnB : n < B) (honeB : 1 < B) :
    ∃ σ' gA gB, Run B initializeWelzl σ σ'
        (12 * Nat.clog 2 n + 20 * n + 34) ∧
      σ'.vars "n" = n ∧ σ'.vars "L" = Nat.clog 2 n ∧
      σ'.vars "qpow" = 2 ^ Nat.clog 2 n ∧
      σ'.vars "acount" = n ∧ σ'.vars "good" = 1 ∧
      σ'.vars "round" = 0 ∧ σ'.vars "removedCount" = 0 ∧
      σ'.arrs "activeA" = arrOf n gA ∧
      σ'.arrs "activeB" = arrOf n gB ∧
      (∀ i < n, gA i = 1) ∧ (∀ i < n, gB i = 1) ∧
      σ'.arrs "off" = σ.arrs "off" ∧
      σ'.arrs "tgt" = σ.arrs "tgt" ∧
      σ'.inp = σ.inp ∧ σ'.out = σ.out := by
  obtain ⟨σ₁, r₁, hn₁, hL₁, hq₁⟩ :=
    computeLog_run hn hpowB hlogB
  have hA₁ : σ₁.arrs "activeA" = arrOf n fA := by
    rw [r₁.frame_arr "activeA" (by decide), hA]
  have hB₁ : σ₁.arrs "activeB" = arrOf n fB := by
    rw [r₁.frame_arr "activeB" (by decide), hBside]
  obtain ⟨σ₂, gA, gB, r₂, hA₂, hB₂, hgA, hgB, hac₂, hn₂⟩ :=
    initActive_run hA₁ hB₁ hn₁ hnB honeB
  let σ₃ := σ₂.setVar "good" 1
  let σ₄ := σ₃.setVar "round" 0
  let σ₅ := σ₄.setVar "removedCount" 0
  have r₃ : Run B (.assign "good" (.lit 1)) σ₂ σ₃ 2 :=
    Run.assign (evalB_lit honeB)
  have r₄ : Run B (.assign "round" (.lit 0)) σ₃ σ₄ 2 :=
    Run.assign (evalB_lit (by omega))
  have r₅ : Run B (.assign "removedCount" (.lit 0)) σ₄ σ₅ 2 :=
    Run.assign (evalB_lit (by omega))
  refine ⟨σ₅, gA, gB, ?_, ?_⟩
  · change Run B (seqs [computeLog, initActive,
      .assign "good" (.lit 1), .assign "round" (.lit 0),
      .assign "removedCount" (.lit 0)]) σ σ₅ _
    exact (r₁.seq (r₂.seq (r₃.seq (r₄.seq r₅)))).mono (by omega)
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hgA, hgB,
        ?_, ?_, ?_, ?_⟩
    · simpa [σ₅, σ₄, σ₃] using hn₂
    · rw [show σ₅.vars "L" = σ₁.vars "L" by
          simp [σ₅, σ₄, σ₃, r₂.frame_var "L" (by decide)]]
      exact hL₁
    · rw [show σ₅.vars "qpow" = σ₁.vars "qpow" by
          simp [σ₅, σ₄, σ₃, r₂.frame_var "qpow" (by decide)]]
      exact hq₁
    · simpa [σ₅, σ₄, σ₃] using hac₂
    · simp [σ₅, σ₄, σ₃]
    · simp [σ₅, σ₄, σ₃]
    · simp [σ₅, σ₄, σ₃]
    · simpa [σ₅, σ₄, σ₃] using hA₂
    · simpa [σ₅, σ₄, σ₃] using hB₂
    · rw [r₅.frame_arr "off" (by decide), r₄.frame_arr "off" (by decide),
        r₃.frame_arr "off" (by decide), r₂.frame_arr "off" (by decide),
        r₁.frame_arr "off" (by decide)]
    · rw [r₅.frame_arr "tgt" (by decide), r₄.frame_arr "tgt" (by decide),
        r₃.frame_arr "tgt" (by decide), r₂.frame_arr "tgt" (by decide),
        r₁.frame_arr "tgt" (by decide)]
    · rw [r₅.frame_inp (by decide), r₄.frame_inp (by decide),
        r₃.frame_inp (by decide), r₂.frame_inp (by decide),
        r₁.frame_inp (by decide)]
    · rw [r₅.out_eq (by decide), r₄.out_eq (by decide),
        r₃.out_eq (by decide), r₂.out_eq (by decide),
        r₁.out_eq (by decide)]

end Lax235315Proofs.Construction.WelzlSetup
