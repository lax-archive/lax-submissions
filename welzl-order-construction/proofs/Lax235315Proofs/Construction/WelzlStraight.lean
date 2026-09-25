import Lax235315Proofs.Construction.WelzlProgram
import Lax808846Proofs.Lib.Fill

/-!
Verified straight-line passes of the concrete Welzl IMP+ program.
-/

namespace Lax235315Proofs.Construction.WelzlStraight

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax808846Proofs.Reasoning.Lib
open Lax235315Proofs.Construction.WelzlProgram

/-- Clearing an array is the standard verified fill pass. -/
lemma clearArray_run {B n : ℕ} {a lim : String} {σ : Env} {g : ℕ → ℕ}
    (harr : σ.arrs a = arrOf n g) (hlim : σ.vars lim = n)
    (hilim : "i" ≠ lim) (hnB : n < B) :
    ∃ σ' g', Run B (clearArray a lim) σ σ' (11 * n + 6) ∧
      σ'.arrs a = arrOf n g' ∧ ∀ i < n, g' i = 0 := by
  have hshape : clearArray a lim =
      .seq (.assign "i" (.lit 0))
        (.while (.lt (.var "i") (.var lim))
          (Fill.put a "i" (.lit 0))) := by
    simp [clearArray, Fill.put, inc, seqs]
  rw [hshape]
  obtain ⟨σ', hrun, ⟨g', harr', hg'⟩, -⟩ :=
    (Fill.loop_spec B n a "i" lim (.lit 0) (fun _ => 0) hilim hnB
      (fun _ _ _ _ => evalB_lit (by omega))).run ⟨⟨g, harr⟩, hlim⟩
  exact ⟨σ', g', hrun, harr', hg'⟩

/-- Invariant for copying a finite prefix of the input tape. -/
def ReadInv (a lim : String) (k : ℕ) (ys rest : List ℕ) (τ : Env) : Prop :=
  τ.vars lim = k ∧ τ.inp = ys.drop (τ.vars "i") ++ rest ∧
    Fill.Below a "i" k (fun i => ys.getD i 0) τ

/-- Reading one CSR block copies it literally and consumes exactly that input
prefix. -/
lemma readArray_run {B : ℕ} {a lim : String}
    (hi : lim ≠ "i") (htmp : lim ≠ "tmp")
    {σ : Env} {g : ℕ → ℕ} {k : ℕ} {ys rest : List ℕ}
    (harr : σ.arrs a = arrOf k g) (hlim : σ.vars lim = k)
    (hys : ys.length = k) (hinp : σ.inp = ys ++ rest)
    (hkB : k < B) (hyB : ∀ v ∈ ys, v < B) :
    ∃ (σ' : Env) (g' : ℕ → ℕ),
      Run B (readArray a lim) σ σ' (12 * k + 6) ∧
      σ'.arrs a = arrOf k g' ∧
      (∀ i < k, g' i = ys.getD i 0) ∧ σ'.inp = rest := by
  have hshape : readArray a lim =
      .seq (.assign "i" (.lit 0))
        (.while (.lt (.var "i") (.var lim))
          (.seq (.read "tmp") (Fill.put a "i" (.var "tmp")))) := by
    simp [readArray, Fill.put, inc, seqs]
  rw [hshape]
  have hbody : Spec B (fun τ => ReadInv a lim k ys rest τ ∧ τ.vars "i" < k)
      (.seq (.read "tmp") (Fill.put a "i" (.var "tmp")))
      (fun τ τ' => ReadInv a lim k ys rest τ' ∧
        τ'.vars "i" = τ.vars "i" + 1) 8 := by
    rintro τ ⟨⟨hl, hinp', hbel⟩, hlt⟩
    have hylen : τ.vars "i" < ys.length := by omega
    have hhead : τ.inp = ys.getD (τ.vars "i") 0 ::
        (ys.drop (τ.vars "i" + 1) ++ rest) := by
      rw [hinp', List.drop_eq_getElem_cons hylen,
        List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hylen]
      rfl
    have hv : τ.inp.headD 0 = ys.getD (τ.vars "i") 0 := by
      rw [hhead]
      simp
    have hvB : τ.inp.headD 0 < B := by
      rw [hv, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hylen]
      exact hyB _ (List.getElem_mem hylen)
    have hlen : τ.vars "i" < (τ.arrs a).length := by
      rw [hbel.length]
      omega
    run_vcg
    · refine ⟨⟨by simp [hi, htmp, hl], by simp [hhead], ?_⟩, by simp⟩
      exact (hbel.step hlt hv).of_eq (by simp) (by simp)
    · simpa using hvB
  obtain ⟨σ', hrun, ⟨-, hinp', hbel⟩, hik⟩ :=
    (Spec.forRangeZero "i" lim (ReadInv a lim k ys rest) k 8 hkB
      (fun _ h => h.2.2.le) (fun _ h => h.1) hbody).run (σ := σ)
      ⟨by simp [hi, hlim], by simp [hinp],
        Fill.below_zero (g := g) (by simp [harr]) (by simp)⟩
  obtain ⟨g', harr', hg'⟩ := hbel.done hik
  exact ⟨σ', g', hrun, harr', hg', by
    rw [hik] at hinp'
    rw [hinp', List.drop_eq_nil_of_le (by omega)]
    simp⟩

/-- Output invariant for the deterministic small-instance branch. -/
def NaturalOutInv (n : ℕ) (o : List ℕ) (τ : Env) : Prop :=
  τ.vars "v" ≤ n ∧ τ.vars "n" = n ∧
    τ.out = o ++ List.range (τ.vars "v")

lemma writeNaturalOrder_run {B n : ℕ} {σ : Env}
    (hn : σ.vars "n" = n) (hnB : n < B) :
    ∃ σ', Run B writeNaturalOrder σ σ' (10 * n + 6) ∧
      σ'.out = σ.out ++ List.range n := by
  have hbody : Spec B
      (fun τ => NaturalOutInv n σ.out τ ∧ τ.vars "v" < n)
      (.seq (.write (.var "v")) (inc "v"))
      (fun τ τ' => NaturalOutInv n σ.out τ' ∧
        τ'.vars "v" = τ.vars "v" + 1) 6 := by
    rintro τ ⟨⟨hle, hnn, hout⟩, hlt⟩
    run_vcg
    exact ⟨⟨by simp; omega, by simp [hnn],
      by simp [hout, List.range_succ]⟩, by simp⟩
  have hshape : writeNaturalOrder =
      .seq (.assign "v" (.lit 0))
        (.while (.lt (.var "v") (.var "n"))
          (.seq (.write (.var "v")) (inc "v"))) := by
    simp [writeNaturalOrder, seqs]
  rw [hshape]
  obtain ⟨σ', hrun, ⟨-, -, hout⟩, hvn⟩ :=
    (Spec.forRangeZero "v" "n" (NaturalOutInv n σ.out) n 6 hnB
      (fun _ h => h.1) (fun _ h => h.2.1) hbody).run (σ := σ)
      ⟨by simp, by simp [hn], by simp⟩
  rw [hvn] at hout
  exact ⟨σ', hrun, hout⟩

/-- Invariant while the two active-side arrays are initialized. -/
def InitActiveInv (n : ℕ) (τ : Env) : Prop :=
  ∃ fA fB : ℕ → ℕ,
    τ.arrs "activeA" = arrOf n fA ∧
    τ.arrs "activeB" = arrOf n fB ∧
    τ.vars "v" ≤ n ∧ τ.vars "n" = n ∧
    (∀ i < τ.vars "v", fA i = 1) ∧
    (∀ i < τ.vars "v", fB i = 1)

/-- Both graph sides start as the full vertex set. -/
lemma initActive_run {B n : ℕ} {σ : Env} {fA fB : ℕ → ℕ}
    (hA : σ.arrs "activeA" = arrOf n fA)
    (hB : σ.arrs "activeB" = arrOf n fB)
    (hn : σ.vars "n" = n) (hnB : n < B) (honeB : 1 < B) :
    ∃ σ' fA' fB', Run B initActive σ σ' (20 * (n + 1)) ∧
      σ'.arrs "activeA" = arrOf n fA' ∧
      σ'.arrs "activeB" = arrOf n fB' ∧
      (∀ i < n, fA' i = 1) ∧ (∀ i < n, fB' i = 1) ∧
      σ'.vars "acount" = n ∧ σ'.vars "n" = n := by
  let loopBody : Com := seqs [
    .store "activeA" (.var "v") (.lit 1),
    .store "activeB" (.var "v") (.lit 1), inc "v"]
  have hbody : Spec B
      (fun τ => InitActiveInv n τ ∧ τ.vars "v" < n)
      loopBody
      (fun τ τ' => InitActiveInv n τ' ∧
        τ'.vars "v" = τ.vars "v" + 1) 10 := by
    rintro τ ⟨⟨gA, gB, hgA, hgB, hv, hnn, hfillA, hfillB⟩, hlt⟩
    have hlenA : τ.vars "v" < (τ.arrs "activeA").length := by
      rw [hgA, length_arrOf]
      exact hlt
    have hlenB : τ.vars "v" < (τ.arrs "activeB").length := by
      rw [hgB, length_arrOf]
      exact hlt
    run_vcg
    refine ⟨⟨upd gA (τ.vars "v") 1, upd gB (τ.vars "v") 1,
      ?_, ?_, by simp; omega, by simp [hnn], ?_, ?_⟩, by simp⟩
    · simp [hgA, set_arrOf_eq_upd]
    · simp [hgB, set_arrOf_eq_upd]
    · intro i hi
      exact upd_below_succ rfl hfillA i (by simpa using hi)
    · intro i hi
      exact upd_below_succ rfl hfillB i (by simpa using hi)
  have hloopShape : initActive =
      .seq
        (.seq (.assign "v" (.lit 0))
          (.while (.lt (.var "v") (.var "n")) loopBody))
        (.assign "acount" (.var "n")) := by
    simp [initActive, loopBody, inc, seqs]
  rw [hloopShape]
  obtain ⟨τ, hphase, hinv, hvn⟩ :=
    (Spec.forRangeZero "v" "n" (InitActiveInv n) n 10 hnB
      (fun _ h => by obtain ⟨_, _, _, _, hv, _, _, _⟩ := h; exact hv)
      (fun _ h => by obtain ⟨_, _, _, _, _, hnn, _, _⟩ := h; exact hnn)
      hbody).run (σ := σ)
      ⟨fA, fB, by simp [hA], by simp [hB], by simp,
        by simp [hn], by intro i hi; simp at hi,
        by intro i hi; simp at hi⟩
  obtain ⟨gA, gB, hgA, hgB, -, hnn, hfillA, hfillB⟩ := hinv
  have hacEval : (Expr.var "n").evalB B τ = some n := by
    rw [evalB_var (by rw [hnn]; exact hnB), hnn]
  let τ' := τ.setVar "acount" n
  have hassign : Run B (.assign "acount" (.var "n")) τ τ' 2 :=
    Run.assign hacEval
  refine ⟨τ', gA, gB, (Run.seq hphase hassign).mono ?_, ?_⟩
  · omega
  · refine ⟨by simp [τ', hgA], by simp [τ', hgB], ?_, ?_, by simp [τ'],
      by simp [τ', hnn]⟩
    · intro i hi
      apply hfillA i
      simpa [hvn] using hi
    · intro i hi
      apply hfillB i
      simpa [hvn] using hi

end Lax235315Proofs.Construction.WelzlStraight
