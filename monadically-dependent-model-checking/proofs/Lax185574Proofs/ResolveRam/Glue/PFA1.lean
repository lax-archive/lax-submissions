import Lax185574Proofs.ResolveRam.Glue.PCt
import Lax185574Proofs.ResolveRam.Glue.ExpW

/-!
The test of one member of the far tree, for the filter of lem:resolve-lift.

`passC` decides `passW` for a member of the far tree whose frame is at
`tf` of the array `y`, against the shifted tree whose atom list is at
`tp1` of the array `a`, with arity `tL` and radius `ts` (`passC_run`): if
the arity of the member is `1` it runs `hop2C` for every position of the
shifted tree. The answer is in `tF`.

Also the facts on words found at a position that the pieces use: a word
of the library is a prefix of the array `a` from its offset (`drop_off`),
and the atom list of a tree word starts three entries after the tree
(`tree_atoms`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.FarRam Lax185574Proofs.EvalRam
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo
open Lax3.DistFO (rhoPlus)

/-! ### Words at a position -/

/-- A word of the library from its offset in `a`. -/
theorem drop_off {ws : List (List ℕ)} {τ : Env} (hw : WordsAt ws τ) {i : ℕ} (hi : i < ws.length) :
    (τ.arrs "a").drop (off ws i) = ws[i] ++ (τ.arrs "a").drop (off ws i + ws[i].length) := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_drop]
  rcases Nat.lt_or_ge j ws[i].length with h | h
  · rw [List.getElem?_append_left h, hw.a i hi j h, List.getElem?_eq_getElem h]
  · rw [List.getElem?_append_right h, List.getElem?_drop]
    congr 1; omega

/-- A word held in `y` from an offset. -/
theorem drop_yAt {w : List ℕ} {yo : ℕ} {τ : Env} (h : YAt w yo τ) :
    (τ.arrs "y").drop yo = w ++ (τ.arrs "y").drop (yo + w.length) := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_drop]
  rcases Nat.lt_or_ge j w.length with h' | h'
  · rw [List.getElem?_append_left h', h j h', List.getElem?_eq_getElem h']
  · rw [List.getElem?_append_right h', List.getElem?_drop]
    congr 1; omega

/-- The atom list of a tree word starts three entries after it. -/
theorem tree_atoms {X : List ℕ} {p : ℕ} {σ : TypeTree} {r : List ℕ} (h : X.drop p = toWord σ ++ r) :
    ∃ r', X.drop (p + 3) = toWord (Node.atoms σ.root).words ++ r' ∧
      (toWord (Node.atoms σ.root).words).length + 3 ≤ (toWord σ).length ∧
      (∀ v ∈ toWord (Node.atoms σ.root).words, v ∈ toWord σ) := by
  obtain ⟨r'', hr''⟩ := atoms_drop (X := toWord σ.root) (y := 0) (t := σ.root) (r := []) (by simp)
  simp only [List.drop_zero] at hr''
  have h3 : X.drop (p + 3) = toWord σ.root ++ r := by
    rw [← List.drop_drop, h, toWord_typeTree]; simp
  refine ⟨r'' ++ r, by rw [h3, hr'', List.append_assoc], ?_, fun v hv => ?_⟩
  · rw [toWord_typeTree, List.length_cons, List.length_cons, List.length_cons, hr'',
      List.length_append]; omega
  · rw [toWord_typeTree, hr'']; simp [hv]

/-! ### The test of a member -/

/-- The loop over the positions of the shifted tree. -/
def posLoop : Com := anyLoop "tI" "tL" "tF" "tw" (.seq (.assign "ti1" (.var "tI")) (hop2C "a" "y"))

/-- The test of the member at `tf` of `y`. -/
def passC : Com :=
  .seq (.assign "tF" (.lit 0)) (.ite (.eq (.get "y" (.add (.var "tf") (.lit 3))) (.lit 1))
    (.seq (.assign "tp2" (.add (.var "tf") (.lit 4))) (.seq (.assign "ti2" (.lit 0)) posLoop)) .skip)

/-- The scalars that `passC` writes. -/
def passV : List String := hV ++ ["tF", "tp2", "ti2", "tI", "ti1"]

theorem passC_wvars : ∀ y ∈ passC.wvars, y ∈ passV := by
  have := hop2C_wvars "a" "y"
  intro y hy
  by_cases hp : y ∈ (hop2C "a" "y").wvars
  · exact List.mem_append_left _ (this y hp)
  · simp only [passC, posLoop, anyLoop, forUp, Com.wvars, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.append_nil, hp, false_or] at hy
    simp only [passV, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto

theorem passC_warrs : passC.warrs = [] := by
  simp [passC, posLoop, anyLoop, forUp, Com.warrs, hop2C_warrs]

theorem passC_reads : ¬ passC.reads := by
  have := hop2C_reads "a" "y"
  simp_all [passC, posLoop, anyLoop, forUp, Com.reads]

theorem passC_noWrite : passC.NoWrite := by
  have := hop2C_noWrite "a" "y"
  simp_all [passC, posLoop, anyLoop, forUp, Com.NoWrite]

/-- The data of a member test: the shifted tree, the colors, the flags,
the arity and the radius. -/
structure PassAt (Xa Y : List ℕ) (p₁ : ℕ) (Dw : DW) (ℓσ R : ℕ) (τ : Env) : Prop where
  a : τ.arrs "a" = Xa
  y : τ.arrs "y" = Y
  p1 : τ.vars "tp1" = p₁
  P : τ.vars "tP" = Dw.P
  Q : τ.vars "tQ" = Dw.Q
  cP : τ.vars "tcP" = bv Dw.cP
  cQ : τ.vars "tcQ" = bv Dw.cQ
  L : τ.vars "tL" = ℓσ
  s : τ.vars "ts" = R

/-- The scalars that `PassAt` reads. -/
def paN : List String := ["tp1", "tP", "tQ", "tcP", "tcQ", "tL", "ts"]

theorem PassAt.congr {Xa Y : List ℕ} {p₁ : ℕ} {Dw : DW} {ℓσ R : ℕ} {τ τ' : Env}
    (h : PassAt Xa Y p₁ Dw ℓσ R τ) (hv : ∀ y ∈ paN, τ'.vars y = τ.vars y) (ha : τ'.arrs = τ.arrs) :
    PassAt Xa Y p₁ Dw ℓσ R τ' := by
  obtain ⟨a, y, p1, P, Q, cP, cQ, L, s⟩ := h
  exact ⟨by rw [ha, a], by rw [ha, y], by rw [hv _ (by simp [paN]), p1], by rw [hv _ (by simp [paN]), P],
    by rw [hv _ (by simp [paN]), Q], by rw [hv _ (by simp [paN]), cP], by rw [hv _ (by simp [paN]), cQ],
    by rw [hv _ (by simp [paN]), L], by rw [hv _ (by simp [paN]), s]⟩

theorem hopAt_i1 {A₁ A₂ : String} {X₁ X₂ : List ℕ} {ws₁ ws₂ : List (List ℕ)} {p₁ p₂ : ℕ}
    {Dw : DW} {i j s : ℕ} {τ : Env} (h : HopAt A₁ A₂ X₁ X₂ ws₁ ws₂ p₁ p₂ Dw i j s τ) (c : ℕ) :
    HopAt A₁ A₂ X₁ X₂ ws₁ ws₂ p₁ p₂ Dw c j s (τ.setVar "ti1" c) := by
  obtain ⟨a1, a2, p1, p2, P, Q, cP, cQ, -, i2, s'⟩ := h
  exact ⟨by simp [a1], by simp [a2], by simp [p1], by simp [p2], by simp [P], by simp [Q], by simp [cP],
    by simp [cQ], by simp, by simp [i2], by simp [s']⟩

/-- The cost of a member test. -/
def passK (ℓσ L R : ℕ) : ℕ := ℓσ * (hopK L R + 30) + 40

/-- **The test of a member.** -/
theorem passC_run {B : ℕ} {Xa Y : List ℕ} {p₁ tf : ℕ} {Aσ : List (List ℕ)} {r₁ r : List ℕ}
    {Dw : DW} {ℓσ R : ℕ} {ν : TypeTree} {τ : Env} (hP : PassAt Xa Y p₁ Dw ℓσ R τ)
    (hd₁ : Xa.drop p₁ = toWord Aσ ++ r₁) (htf : τ.vars "tf" = tf)
    (hdr : Y.drop tf = (toWord ν).length :: (toWord ν ++ r))
    (hB₁ : p₁ + (toWord Aσ).length + 6 < B) (hv₁ : ∀ v ∈ toWord Aσ, v < B)
    (hB₂ : tf + (toWord ν).length + 8 < B) (hv₂ : ∀ v ∈ toWord ν, v < B)
    (hPB : Dw.P < B) (hQB : Dw.Q < B) (hℓ : ℓσ + 1 < B) (hR : 2 * R + 4 < B) :
    ∃ τ', Run B passC τ τ' (passK ℓσ (Aσ.length + (toWord ν).length) R) ∧
      τ'.vars "tF" = bv ((ν.ℓ == 1) && (List.range ℓσ).any fun i =>
        hop2W Dw Aσ i (Node.atoms ν.root).words 0 R) ∧
      (∀ y, y ∉ passV → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧
      τ'.inp = τ.inp := by
  set Aν := (Node.atoms ν.root).words
  -- the member as a tree word at `tf + 1`
  have hd1 : Y.drop (tf + 1) = toWord ν ++ r := by
    rw [← List.drop_drop, hdr]; simp
  obtain ⟨r₂, hd₂, hl₂, hm₂⟩ := tree_atoms (X := Y) (σ := ν) hd1
  have hAν : Aν.length < (toWord Aν).length := by
    rw [toWord_words, List.length_cons, length_frames]; omega
  have hw3 : Y[tf + 3]? = some ν.ℓ := by
    have h := congrArg (·[2]?) hd1
    simp only [List.getElem?_drop] at h
    rw [show tf + 3 = tf + 1 + 2 by omega, h, toWord_typeTree]; rfl
  have hℓν : ν.ℓ < B := hv₂ _ (by rw [toWord_typeTree]; simp)
  set τ1 := τ.setVar "tF" 0
  have r1 : Run B (.assign "tF" (.lit 0)) τ τ1 2 := Run.assign (evalB_lit (by omega))
  have c1 : (Cond.eq (.get "y" (.add (.var "tf") (.lit 3))) (.lit 1)).evalB B τ1 = some (ν.ℓ == 1) :=
    evalB_condEq (evalB_get (ev_add (ev_var (v := tf) (by simp [τ1, htf]) (by omega)) (evalB_lit (by omega))
      (by omega)) (by simp [τ1, hP.y, hw3]) hℓν) (evalB_lit (by omega))
  have frP : ∀ y, y ∈ paN → y ∉ passV := by decide
  by_cases hν : ν.ℓ = 1
  · set τ2 := (τ1.setVar "tp2" (tf + 4)).setVar "ti2" 0
    have r2a : Run B (.assign "tp2" (.add (.var "tf") (.lit 4))) τ1 (τ1.setVar "tp2" (tf + 4)) 4 :=
      (Run.assign (ev_add (ev_var (v := tf) (by simp [τ1, htf]) (by omega)) (evalB_lit (by omega))
        (by omega))).mono (by simp [Expr.size])
    have r2b : Run B (.assign "ti2" (.lit 0)) (τ1.setVar "tp2" (tf + 4)) τ2 2 :=
      Run.assign (evalB_lit (by omega))
    -- the loop over the positions
    let C : Env → Prop := fun ρ => HopAt "a" "y" Xa Y Aσ Aν p₁ (tf + 4) Dw (ρ.vars "ti1") 0 R ρ
    have hC2 : C τ2 := ⟨by simp [τ2, τ1, hP.a], by simp [τ2, τ1, hP.y], by simp [τ2, τ1, hP.p1],
      by simp [τ2], by simp [τ2, τ1, hP.P], by simp [τ2, τ1, hP.Q], by simp [τ2, τ1, hP.cP],
      by simp [τ2, τ1, hP.cQ], rfl, by simp [τ2], by simp [τ2, τ1, hP.s]⟩
    have hCs : ∀ ρ (z : String) x, z ∉ rN → C ρ → C (ρ.setVar z x) := by
      intro ρ z x hz hC
      have : (ρ.setVar z x).vars "ti1" = ρ.vars "ti1" := by
        have : "ti1" ≠ z := fun h => hz (h ▸ by simp [rN])
        simp [this]
      show HopAt _ _ _ _ _ _ _ _ _ ((ρ.setVar z x).vars "ti1") _ _ _
      rw [this]; exact hopAt_setVar hC hz x
    have hL2 : τ2.vars "tL" = ℓσ := by simp [τ2, τ1, hP.L]
    obtain ⟨τ3, r3, C3, f3, n3⟩ := anyLoop_run (B := B) (i := "tI") (n := "tL") (flag := "tF")
      (v := "tw") (body := .seq (.assign "ti1" (.var "tI")) (hop2C "a" "y")) C
      (fun c => hop2W Dw Aσ c Aν 0 R) ℓσ (hopK (Aσ.length + Aν.length) R + 2) hℓ (by decide)
      (by decide) (by decide) (fun ρ x h => hCs ρ "tI" x (by decide) h)
      (fun ρ x h => hCs ρ "tF" x (by decide) h)
      (by
        rintro c hc ρ ⟨hC, hI, hn, -⟩
        set ρ1 := ρ.setVar "ti1" c
        have r1' : Run B (.assign "ti1" (.var "tI")) ρ ρ1 2 := Run.assign (ev_var hI (by omega))
        have H1 : HopAt "a" "y" Xa Y Aσ Aν p₁ (tf + 4) Dw c 0 R ρ1 := hopAt_i1 hC c
        obtain ⟨ρ2, r2', w2, f2, a2, -, -⟩ := hop2C_run H1 hd₁ (by rw [show tf + 4 = tf + 1 + 3 by omega]; exact hd₂)
          ⟨hB₁, by have := hl₂; simp only [Aν]; omega, hv₁, fun v hv => hv₂ v (hm₂ v hv), hPB, hQB, by omega, by omega, hR⟩
        have k : ∀ y ∈ rN ++ ["tI", "tL", "tF"], y ∉ hV := by decide
        have H2 : HopAt "a" "y" Xa Y Aσ Aν p₁ (tf + 4) Dw c 0 R ρ2 :=
          H1.congr (fun y hy => f2 y (k y (List.mem_append_left _ hy))) a2
        have hi2 : ρ2.vars "ti1" = c := H2.i1
        refine ⟨ρ2, (Run.seq r1' r2').mono (by omega), ?_, ?_, ?_, ?_, w2⟩
        · show HopAt _ _ _ _ _ _ _ _ _ (ρ2.vars "ti1") _ _ _
          rw [hi2]; exact H2
        · rw [f2 _ (k _ (by simp)), show ρ1.vars "tI" = ρ.vars "tI" by simp [ρ1], hI]
        · rw [f2 _ (k _ (by simp)), show ρ1.vars "tL" = ρ.vars "tL" by simp [ρ1], hn]
        · rw [f2 _ (k _ (by simp))]; simp [ρ1])
      τ2 ⟨hC2, hL2, by simp [τ2, τ1]⟩
    have hrun : Run B passC τ τ3 (passK ℓσ (Aσ.length + (toWord ν).length) R) := by
      unfold passC
      refine (Run.seq r1 (Run.ite_true (by rw [c1]; simp [hν]) (Run.seq r2a (Run.seq r2b r3)))).mono ?_
      have hm : hopK (Aσ.length + Aν.length) R ≤ hopK (Aσ.length + (toWord ν).length) R := by
        unfold hopK; apply Nat.mul_le_mul_left; have := hl₂; have := hAν; simp only [Aν] at *; omega
      simp only [passK, Cond.size, Expr.size]
      nlinarith
    obtain ⟨fa, fo, fi⟩ := run_frame hrun passC_warrs passC_reads passC_noWrite
    refine ⟨τ3, hrun, by rw [f3]; simp [hν], fun y hy => hrun.frame_var y
      (fun h => hy (passC_wvars y h)), fa, fo, fi⟩
  · refine ⟨τ1, ?_, ?_, fun y hy => ?_, by simp [τ1], by simp [τ1], by simp [τ1]⟩
    · unfold passC
      refine (Run.seq r1 (Run.ite_false (by rw [c1]; simp [hν]) Run.skip)).mono ?_
      simp only [passK, Cond.size, Expr.size]; omega
    · rw [show (ν.ℓ == 1) = false by simpa using hν]; simp [τ1]
    · have : y ≠ "tF" := by rintro rfl; simp [passV] at hy
      simp [τ1, this]

end Lax185574Proofs.ResolveRam.Glue
