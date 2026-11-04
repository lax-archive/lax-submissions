import Lax185574Proofs.MainRam.ValidSem
import Lax185574Proofs.Compose.CsrToGraph

/-!
The validation program, part one: reading the input
`|y|, |x| + 1, y, x` with `x = g ++ code φ` into arrays. The script goes
to `Y`, the offsets and targets of the graph to `of` and `tg`, and the
formula to `F`.
-/

namespace Lax185574Proofs.MainRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax271696.GraphEncoding Lax185574Proofs.Compose

/-- The offsets of a graph word. -/
def ofL (g : List ℕ) (n : ℕ) : List ℕ := (g.drop 2).take (n + 1)

/-- The targets of a graph word. -/
def tgL (g : List ℕ) (n : ℕ) : List ℕ := g.drop (3 + n)

theorem graph_split {g : List ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} (hg : EncodesGraph g n G) :
    g = n :: edgeCount g :: (ofL g n ++ tgL g n) ∧ (ofL g n).length = n + 1 ∧
      (tgL g n).length = 2 * edgeCount g := by
  have hl := hg.length_eq
  have h0 : g.getD 0 0 = n := hg.vertexCount_eq
  refine ⟨?_, by simp [ofL]; omega, by simp [tgL]; omega⟩
  obtain ⟨a, b, r, rfl⟩ : ∃ a b r, g = a :: b :: r := by
    rcases g with _ | ⟨a, _ | ⟨b, r⟩⟩
    · simp at hl; omega
    · simp at hl; omega
    · exact ⟨a, b, r, rfl⟩
  simp only [List.getD_cons_zero] at h0
  subst h0
  simp only [ofL, tgL, edgeCount, List.getD_cons_succ, List.getD_cons_zero, List.drop_succ_cons,
    List.drop_zero]
  congr 2
  rw [show 3 + a = (a + 1) + 2 by omega, List.drop_succ_cons, List.drop_succ_cons]
  exact (List.take_append_drop (a + 1) r).symm

/-- A read, with its effect named. -/
theorem read_step {B : ℕ} {σ : Env} (x : String) {v : ℕ} {rest : List ℕ} (h : σ.inp = v :: rest) :
    ∃ σ', Run B (.read x) σ σ' 1 ∧ σ'.vars x = v ∧ (∀ z, z ≠ x → σ'.vars z = σ.vars z) ∧
      σ'.arrs = σ.arrs ∧ σ'.inp = rest ∧ σ'.out = σ.out :=
  ⟨_, Run.read h, by simp, fun z hz => by simp [hz], rfl, rfl, rfl⟩

/-- An assignment, with its effect named. -/
theorem assign_step {B : ℕ} {σ : Env} (x : String) {e : Expr} {v : ℕ} (h : e.evalB B σ = some v) :
    ∃ σ', Run B (.assign x e) σ σ' (1 + e.size) ∧ σ'.vars x = v ∧
      (∀ z, z ≠ x → σ'.vars z = σ.vars z) ∧ σ'.arrs = σ.arrs ∧ σ'.inp = σ.inp ∧ σ'.out = σ.out :=
  ⟨_, Run.assign h, by simp, fun z hz => by simp [hz], rfl, rfl, rfl⟩

/-- Read the input into arrays. -/
def readPh : Com :=
  .seq (.read "L") (.seq (.read "X1") (.seq (.assign "cnt" (.var "L")) (.seq (readArr "Y")
  (.seq (.read "n") (.seq (.read "E") (.seq (.assign "cnt" (.add (.var "n") (.lit 1)))
  (.seq (readArr "of") (.seq (.assign "cnt" (.add (.var "E") (.var "E"))) (.seq (readArr "tg")
  (.seq (.assign "nF" (.sub (.var "X1") (.add (.add (.var "n") (.lit 4)) (.add (.var "E") (.var "E")))))
  (.seq (.assign "cnt" (.var "nF")) (readArr "F"))))))))))))

theorem readArr_wvars (a : String) : (readArr a).wvars = ["i", "v", "i"] := rfl
theorem readArr_warrs (a : String) : (readArr a).warrs = [a] := rfl

theorem readPh_run {B : ℕ} {n : ℕ} {G : SimpleGraph (Fin n)} {g φw y : List ℕ}
    (hg : EncodesGraph g n G) {σ : Env}
    (hinp : σ.inp = y.length :: ((g ++ φw).length + 1) :: (y ++ (g ++ φw)))
    (hB : y.length + (g ++ φw).length + 2 < B) (hyB : ∀ a ∈ y, a < B) (hxB : ∀ a ∈ g ++ φw, a < B)
    (hY : σ.arrs "Y" = arrOf y.length (fun _ => 0))
    (hof : σ.arrs "of" = arrOf (n + 1) (fun _ => 0))
    (htg : σ.arrs "tg" = arrOf (2 * edgeCount g) (fun _ => 0))
    (hF : σ.arrs "F" = arrOf φw.length (fun _ => 0)) :
    ∃ σ', Run B readPh σ σ' (12 * (y.length + (g ++ φw).length) + 80) ∧
      σ'.vars "L" = y.length ∧ σ'.vars "n" = n ∧ σ'.vars "E" = edgeCount g ∧
      σ'.vars "nF" = φw.length ∧
      σ'.arrs "Y" = y ∧ σ'.arrs "of" = ofL g n ∧ σ'.arrs "tg" = tgL g n ∧ σ'.arrs "F" = φw ∧
      (∀ a, a ≠ "Y" → a ≠ "of" → a ≠ "tg" → a ≠ "F" → σ'.arrs a = σ.arrs a) ∧
      σ'.out = σ.out := by
  obtain ⟨hgs, hofl, htgl⟩ := graph_split hg
  set E := edgeCount g
  have hgl : g.length = 3 + n + 2 * E := by rw [hg.length_eq]
  have hxl : (g ++ φw).length = g.length + φw.length := List.length_append
  have hofB : ∀ a ∈ ofL g n, a < B := fun a ha => hxB a (by
    have : a ∈ g := by rw [hgs]; simp [ha]
    simp [this])
  have htgB : ∀ a ∈ tgL g n, a < B := fun a ha => hxB a (by
    have : a ∈ g := by rw [hgs]; simp [ha]
    simp [this])
  have hφB : ∀ a ∈ φw, a < B := fun a ha => hxB a (by simp [ha])
  obtain ⟨σ1, r1, a1, f1, ar1, i1, o1⟩ := read_step (B := B) "L" hinp
  obtain ⟨σ2, r2, a2, f2, ar2, i2, o2⟩ := read_step (B := B) (σ := σ1) "X1" i1
  obtain ⟨σ3, r3, a3, f3, ar3, i3, o3⟩ := assign_step (B := B) (σ := σ2) "cnt" (e := .var "L")
    (evalB_var (by rw [f2 _ (by decide), a1]; omega))
  rw [f2 _ (by decide), a1] at a3
  obtain ⟨σ4, r4, hi4, ha4, hv4, hb4, ho4⟩ := readArr_spec (B := B) "Y" y (g ++ φw) (by omega)
    hyB (σ := σ3) a3 (by rw [i3, i2]) (by rw [ar3, ar2, ar1, hY])
  have hin4 : σ4.inp = n :: E :: (ofL g n ++ tgL g n ++ φw) := by
    rw [hi4]; conv_lhs => rw [hgs]
    simp
  obtain ⟨σ5, r5, a5, f5, ar5, i5, o5⟩ := read_step (B := B) (σ := σ4) "n" hin4
  obtain ⟨σ6, r6, a6, f6, ar6, i6, o6⟩ := read_step (B := B) (σ := σ5) "E" i5
  have hn6 : σ6.vars "n" = n := by rw [f6 _ (by decide), a5]
  obtain ⟨σ7, r7, a7, f7, ar7, i7, o7⟩ := assign_step (B := B) (σ := σ6) "cnt"
    (e := .add (.var "n") (.lit 1))
    (evalB_bin (evalB_var (by rw [hn6]; omega)) (evalB_lit (by omega)) (by simp [hn6]; omega))
  simp only [Bop.apply_add, hn6] at a7
  obtain ⟨σ8, r8, hi8, ha8, hv8, hb8, ho8⟩ := readArr_spec (B := B) "of" (ofL g n) (tgL g n ++ φw)
    (by omega) hofB (σ := σ7) (by rw [a7, hofl]) (by rw [i7, i6, List.append_assoc])
    (by rw [ar7, ar6, ar5, hb4 "of" (by rw [readArr_warrs]; decide), ar3, ar2, ar1, hof, hofl])
  have hn8 : σ8.vars "n" = n := by
    rw [hv8 "n" (by rw [readArr_wvars]; decide), f7 _ (by decide), hn6]
  have hE8 : σ8.vars "E" = E := by
    rw [hv8 "E" (by rw [readArr_wvars]; decide), f7 _ (by decide), a6]
  obtain ⟨σ9, r9, a9, f9, ar9, i9, o9⟩ := assign_step (B := B) (σ := σ8) "cnt"
    (e := .add (.var "E") (.var "E"))
    (evalB_bin (evalB_var (by rw [hE8]; omega)) (evalB_var (by rw [hE8]; omega))
      (by simp [hE8]; omega))
  simp only [Bop.apply_add, hE8] at a9
  obtain ⟨σ10, r10, hi10, ha10, hv10, hb10, ho10⟩ := readArr_spec (B := B) "tg" (tgL g n) φw
    (by omega) htgB (σ := σ9) (by rw [a9, htgl]; omega) (by rw [i9, hi8])
    (by rw [ar9, hb8 "tg" (by rw [readArr_warrs]; decide), ar7, ar6, ar5,
      hb4 "tg" (by rw [readArr_warrs]; decide), ar3, ar2, ar1, htg, htgl])
  have hfr10 : ∀ z, z ≠ "i" → z ≠ "v" → z ≠ "cnt" → σ10.vars z = σ8.vars z := by
    intro z h1 h2 h3
    rw [hv10 z (by rw [readArr_wvars]; simp [h1, h2]), f9 z h3]
  have hn10 : σ10.vars "n" = n := by rw [hfr10 _ (by decide) (by decide) (by decide), hn8]
  have hE10 : σ10.vars "E" = E := by rw [hfr10 _ (by decide) (by decide) (by decide), hE8]
  have hX10 : σ10.vars "X1" = (g ++ φw).length + 1 := by
    rw [hfr10 _ (by decide) (by decide) (by decide), hv8 "X1" (by rw [readArr_wvars]; decide),
      f7 _ (by decide), f6 _ (by decide), f5 _ (by decide),
      hv4 "X1" (by rw [readArr_wvars]; decide), f3 _ (by decide), a2]
  have hL10 : σ10.vars "L" = y.length := by
    rw [hfr10 _ (by decide) (by decide) (by decide), hv8 "L" (by rw [readArr_wvars]; decide),
      f7 _ (by decide), f6 _ (by decide), f5 _ (by decide),
      hv4 "L" (by rw [readArr_wvars]; decide), f3 _ (by decide), f2 _ (by decide), a1]
  obtain ⟨σ11, r11, a11, f11, ar11, i11, o11⟩ := assign_step (B := B) (σ := σ10) "nF"
    (e := .sub (.var "X1") (.add (.add (.var "n") (.lit 4)) (.add (.var "E") (.var "E"))))
    (evalB_bin (evalB_var (by rw [hX10]; omega)) (evalB_bin (evalB_bin
      (evalB_var (by rw [hn10]; omega)) (evalB_lit (by omega)) (by simp [hn10]; omega))
      (evalB_bin (evalB_var (by rw [hE10]; omega)) (evalB_var (by rw [hE10]; omega))
        (by simp [hE10]; omega)) (by simp [hn10, hE10]; omega)) (by simp; omega))
  simp only [Bop.apply_sub, Bop.apply_add, hX10, hn10, hE10] at a11
  rw [show (g ++ φw).length + 1 - (n + 4 + (E + E)) = φw.length by omega] at a11
  obtain ⟨σ12, r12, a12, f12, ar12, i12, o12⟩ := assign_step (B := B) (σ := σ11) "cnt"
    (e := .var "nF") (evalB_var (by rw [a11]; omega))
  rw [a11] at a12
  obtain ⟨σ13, r13, hi13, ha13, hv13, hb13, ho13⟩ := readArr_spec (B := B) "F" φw []
    (by omega) hφB (σ := σ12) a12 (by rw [i12, i11, hi10]; simp)
    (by rw [ar12, ar11, hb10 "F" (by rw [readArr_warrs]; decide), ar9,
      hb8 "F" (by rw [readArr_warrs]; decide), ar7, ar6, ar5,
      hb4 "F" (by rw [readArr_warrs]; decide), ar3, ar2, ar1, hF])
  have hfr13 : ∀ z, z ≠ "i" → z ≠ "v" → z ≠ "cnt" → z ≠ "nF" → σ13.vars z = σ10.vars z := by
    intro z h1 h2 h3 h4
    rw [hv13 z (by rw [readArr_wvars]; simp [h1, h2]), f12 z h3, f11 z h4]
  refine ⟨σ13, (r1.seq (r2.seq (r3.seq (r4.seq (r5.seq (r6.seq (r7.seq (r8.seq (r9.seq (r10.seq
    (r11.seq (r12.seq r13)))))))))))).mono ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ha13, ?_, ?_⟩
  · simp only [Expr.size]; rw [hxl, hgl, hofl, htgl] at *; omega
  · rw [hfr13 _ (by decide) (by decide) (by decide) (by decide), hL10]
  · rw [hfr13 _ (by decide) (by decide) (by decide) (by decide), hn10]
  · rw [hfr13 _ (by decide) (by decide) (by decide) (by decide), hE10]
  · rw [hv13 "nF" (by rw [readArr_wvars]; decide), f12 _ (by decide), a11]
  · rw [hb13 "Y" (by rw [readArr_warrs]; decide), ar12, ar11,
      hb10 "Y" (by rw [readArr_warrs]; decide), ar9, hb8 "Y" (by rw [readArr_warrs]; decide),
      ar7, ar6, ar5, ha4]
  · rw [hb13 "of" (by rw [readArr_warrs]; decide), ar12, ar11,
      hb10 "of" (by rw [readArr_warrs]; decide), ar9, ha8]
  · rw [hb13 "tg" (by rw [readArr_warrs]; decide), ar12, ar11, ha10]
  · intro a h1 h2 h3 h4
    rw [hb13 a (by rw [readArr_warrs]; simp [h4]), ar12, ar11,
      hb10 a (by rw [readArr_warrs]; simp [h3]), ar9, hb8 a (by rw [readArr_warrs]; simp [h2]),
      ar7, ar6, ar5, hb4 a (by rw [readArr_warrs]; simp [h1]), ar3, ar2, ar1]
  · rw [ho13, o12, o11, ho10, o9, ho8, o7, o6, o5, ho4, o3, o2, o1]

end Lax185574Proofs.MainRam
