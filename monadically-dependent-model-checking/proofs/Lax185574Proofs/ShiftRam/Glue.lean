import Lax185574Proofs.LoopGlue
import Lax185574Proofs.Words.TreeMap
import Lax185574Proofs.EvalRam.Table

/-!
The glue program of the rank shift.

In its first round the program reads the tree, finds the first
extension with guard `0` and asks for the restriction of its child to
the first `ℓ` positions. In its second round it outputs the answer.
-/

namespace Lax185574Proofs.ShiftRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo

/-! ### Writing loops -/

/-- A loop that writes the values `f 0, …, f (N − 1)`. -/
theorem writeLoop_run {B N : ℕ} {m : String} {e : Expr} (f : ℕ → ℕ) (P : Env → Prop)
    (hNB : N < B) (hm : m ≠ "i")
    (hPw : ∀ τ (o : List ℕ), P τ → P { τ with out := o })
    (hPi : ∀ τ k, P τ → P (τ.setVar "i" k))
    (hmN : ∀ τ, P τ → τ.vars m = N)
    (he : ∀ τ, P τ → τ.vars "i" < N → e.evalB B τ = some (f (τ.vars "i"))) (σ : Env) (hσ : P σ) :
    ∃ σ', Run B (forUp "i" (.var m) (.write e)) σ σ' (N * (e.size + 9) + 6) ∧ P σ' ∧
      σ'.out = σ.out ++ (List.range N).map f := by
  obtain ⟨σ', hr, ⟨hP, hout⟩, -⟩ := forUp_run (B := B) (i := "i") (e := .var m) (body := .write e)
    (N := N) (K := 1 + e.size) (fun k τ => P τ ∧ τ.out = σ.out ++ (List.range k).map f) hNB
    (fun k _ τ hI _ => by
      simp only [evalB_var_iff]; exact ⟨(hmN τ hI.1).symm, by rw [hmN τ hI.1]; exact hNB⟩)
    ⟨hPi σ 0 hσ, by simp⟩
    (fun k hk τ hI hik => by
      refine ⟨{ τ with out := τ.out ++ [f k] }, Run.write ?_, by simpa using hik, ?_, ?_⟩
      · rw [← hik]; exact he τ hI.1 (by omega)
      · exact hPi _ _ (hPw τ _ hI.1)
      · simp [hI.2, List.range_succ])
  exact ⟨σ', hr.mono (by simp only [Expr.size]; ring_nf; omega), hP, hout⟩

/-- A loop that copies `N` numbers from the input to the output. -/
def copyLoop : Com := forUp "i" (.var "m") (.seq (.read "w") (.write (.var "w")))

theorem copyLoop_run {B : ℕ} (b rest : List ℕ) (hb : ∀ v ∈ b, v < B) (hbB : b.length < B)
    (σ : Env) (hm : σ.vars "m" = b.length) (hinp : σ.inp = b ++ rest) :
    ∃ σ', Run B copyLoop σ σ' (b.length * 13 + 6) ∧ σ'.out = σ.out ++ b ∧ σ'.inp = rest := by
  obtain ⟨σ', hr, ⟨-, hout, hin⟩, -⟩ := forUp_run (B := B) (i := "i") (e := .var "m")
    (body := .seq (.read "w") (.write (.var "w"))) (N := b.length) (K := 4)
    (fun k τ => τ.vars "m" = b.length ∧ τ.out = σ.out ++ b.take k ∧ τ.inp = b.drop k ++ rest)
    (σ := σ) hbB
    (fun k _ τ hI _ => by
      simp only [evalB_var_iff]; exact ⟨hI.1.symm, by rw [hI.1]; exact hbB⟩)
    ⟨by simp [hm], by simp, by simp [hinp]⟩
    (fun k hk τ ⟨hm', hout, hin⟩ hik => by
      have hin' : τ.inp = b[k] :: (b.drop (k + 1) ++ rest) := by
        rw [hin, List.drop_eq_getElem_cons hk]; rfl
      have hbk : b[k] < B := hb _ (List.getElem_mem hk)
      refine ⟨{ ({ τ.setVar "w" b[k] with inp := b.drop (k + 1) ++ rest } : Env) with
        out := τ.out ++ [b[k]] }, (Run.seq (Run.read hin') (Run.write (v := b[k]) ?_)).mono (by simp),
        by simp [hik], by simp [hm'], ?_, by simp⟩
      · simp only [evalB_var_iff, vars_setVar, if_true]; exact ⟨trivial, hbk⟩
      · simp only [out_setVar]
        rw [hout, List.take_add_one, List.getElem?_eq_getElem hk]; simp)
  exact ⟨σ', hr.mono (by simp; omega), by simpa using hout, by simpa using hin⟩

/-! ### Finding the first extension with guard `0` -/

/-- Frame `j` of the list at `e` has guard `0`. -/
def gz (X : List ℕ) (e j : ℕ) : Bool := xg X (frPos X e j + 1) == 0

/-- The first of the first `n` frames with guard `0`. -/
def fz (X : List ℕ) (e n : ℕ) : Option ℕ := (List.range n).find? (gz X e)

theorem fz_succ (X : List ℕ) (e n : ℕ) :
    fz X e (n + 1) = (fz X e n).or (if gz X e n then some n else none) := by
  simp only [fz, List.range_succ, List.find?_append, List.find?_cons, List.find?_nil]
  cases gz X e n <;> rfl

def findBody : Com :=
  .seq (.ite (.eq (.var "fd") (.lit 0))
      (.ite (.eq (.get "x" (.add (.var "fr") (.lit 1))) (.lit 0))
        (.seq (.assign "fd" (.lit 1)) (.assign "cf" (.var "fr"))) .skip) .skip)
    (.assign "fr" (.add (.add (.var "fr") (.get "x" (.var "fr"))) (.lit 1)))

/-- Skip the atoms of the root and look for the first extension with
guard `0`. -/
def findCmd : Com :=
  .seq (.assign "y" (.lit 0)) (.seq skipList (.seq (.assign "ne" (.get "x" (.var "y")))
    (.seq (.assign "fr" (.add (.var "y") (.lit 1))) (.seq (.assign "fd" (.lit 0))
      (.seq (.assign "cf" (.lit 0)) (forUp "j" (.var "ne") findBody))))))

theorem findBody_spec (B : ℕ) (X : List ℕ) (fr fd cf : ℕ) (hfr : fr + 1 + xg X fr ≤ X.length)
    (h1 : 1 ≤ xg X fr) (hX : ∀ v ∈ X, v < B) (hXB : X.length + 1 < B) (hfd : fd ≤ 1)
    (hcf : cf < B) :
    Spec B (fun τ => τ.arrs "x" = X ∧ τ.vars "fr" = fr ∧ τ.vars "fd" = fd ∧ τ.vars "cf" = cf)
      findBody (fun _ τ' => τ'.vars "fr" = fr + 1 + xg X fr ∧
        τ'.vars "fd" = (if fd = 0 ∧ xg X (fr + 1) = 0 then 1 else fd) ∧
        τ'.vars "cf" = (if fd = 0 ∧ xg X (fr + 1) = 0 then fr else cf)) 40 := by
  rintro τ ⟨hx, hfr', hfd', hcf'⟩
  subst hx hfr' hfd' hcf'
  have h0 : (τ.arrs "x").getD (τ.vars "fr") 0 < B := xg_lt hX (by omega)
  have h1' : (τ.arrs "x").getD (τ.vars "fr" + 1) 0 < B := xg_lt hX (by omega)
  have hfr3 : τ.vars "fr" + (τ.arrs "x").getD (τ.vars "fr") 0 + 1 ≤ (τ.arrs "x").length := by
    unfold xg at hfr; omega
  have hfr4 : τ.vars "fr" + 1 < (τ.arrs "x").length := by unfold xg at hfr h1; omega
  unfold findBody
  run_vcg
  all_goals (try (simp; omega))
  all_goals (simp [xg] at *)
  all_goals (try split_ifs) <;> simp_all <;> omega

/-- The position of the first frame with guard `0`, `0` if there is none. -/
def fzPos (X : List ℕ) (e n : ℕ) : ℕ := ((fz X e n).map (frPos X e)).getD 0

theorem findCmd_spec (B : ℕ) (X : List ℕ) {h ℓ : ℕ} (t : Node (h + 1) ℓ) (r : List ℕ)
    (hXt : X.drop 0 = toWord t ++ r) (hX : ∀ v ∈ X, v < B) (hXB : X.length + 5 < B) :
    Spec B (fun τ => τ.arrs "x" = X) findCmd
      (fun _ τ' => τ'.vars "cf" = fzPos X (listEnd X 0) (xg X (listEnd X 0)))
      (100 * X.length + 60) := by
  intro τ hx
  have hn : NodeAt X 0 (h + 1) := ⟨ℓ, t, r, hXt⟩
  obtain ⟨hfr1, -, -⟩ := hn.exts
  obtain ⟨-, h2⟩ := nodeSplit hXt
  have hE := listFacts_of h2
  obtain ⟨ws, r0, hws⟩ := hn.atomList
  have hA := listFacts_of hws
  set e := listEnd X 0 with he
  set N := xg X e with hN
  have heX : e < X.length := by have := hE.frPos_le 0 (Nat.zero_le _); have := hE.end_le; omega
  have hNX : N ≤ X.length := by have := hE.frPos_le _ le_rfl; have := hE.end_le; omega
  have ra : Run B (.assign "y" (.lit 0)) τ (τ.setVar "y" 0) 2 :=
    (Run.assign (by simp; omega)).mono (by simp)
  obtain ⟨τ1, r1, hy1⟩ := skipList_spec B X 0 hA (by omega) hX (τ.setVar "y" 0) ⟨by simp [hx], by simp⟩
  rw [← he] at hy1
  have hx1 : τ1.arrs "x" = X := by rw [r1.frame_arr "x" (by decide)]; simp [hx]
  set τ2 := ((((τ1.setVar "ne" N).setVar "fr" (e + 1)).setVar "fd" 0).setVar "cf" 0) with hτ2
  have rne : Run B (.assign "ne" (.get "x" (.var "y"))) τ1 (τ1.setVar "ne" N) 4 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_get_iff, evalB_var_iff]
    refine ⟨e, ⟨hy1.symm, by omega⟩, ?_, xg_lt hX (by omega)⟩
    rw [hx1, List.getElem?_eq_getElem heX, hN, xg_of_lt heX]
  have rfr : Run B (.assign "fr" (.add (.var "y") (.lit 1))) (τ1.setVar "ne" N)
      ((τ1.setVar "ne" N).setVar "fr" (e + 1)) 4 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff, vars_setVar]
    exact ⟨e, 1, ⟨by simp [hy1], by simp [hy1]; omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩
  have rfd : Run B (.assign "fd" (.lit 0)) ((τ1.setVar "ne" N).setVar "fr" (e + 1))
      (((τ1.setVar "ne" N).setVar "fr" (e + 1)).setVar "fd" 0) 2 :=
    (Run.assign (by simp; omega)).mono (by simp)
  have rcf : Run B (.assign "cf" (.lit 0)) (((τ1.setVar "ne" N).setVar "fr" (e + 1)).setVar "fd" 0)
      τ2 2 := (Run.assign (by simp; omega)).mono (by simp)
  obtain ⟨τ3, r3, hI3, -⟩ := forUp_run (B := B) (i := "j") (e := .var "ne") (body := findBody) (N := N)
    (K := 40) (fun j ρ => ρ.arrs "x" = X ∧ ρ.vars "ne" = N ∧ ρ.vars "fr" = frPos X e j ∧
      ρ.vars "fd" = (if (fz X e j).isSome then 1 else 0) ∧ ρ.vars "cf" = fzPos X e j)
    (σ := τ2) (by omega)
    (fun j _ ρ hI _ => by
      simp only [evalB_var_iff]; exact ⟨hI.2.1.symm, by rw [hI.2.1]; omega⟩)
    ⟨by simp [hτ2, hx1], by simp [hτ2], by simp [hτ2, frPos, skipFr],
      by simp [hτ2, fz], by simp [hτ2, fzPos, fz]⟩
    (fun j hj ρ ⟨hx', hne', hfr', hfd', hcf'⟩ hjv => by
      have hs := skipFr_succ' X (e + 1) j
      obtain ⟨-, hle1⟩ := hE.frPos_le (j + 1) (by omega)
      have hle2 := hE.end_le
      have hfrB : fzPos X e j < B := by
        unfold fzPos
        cases hf : fz X e j with
        | none => simp; omega
        | some j' =>
          have : j' < j := by
            have := List.mem_of_find?_eq_some hf; simpa using this
          obtain ⟨-, h3⟩ := hE.frPos_le j' (by omega)
          simp; omega
      obtain ⟨ρ', hr', hfr2, hfd2, hcf2⟩ := findBody_spec B X (frPos X e j)
        (if (fz X e j).isSome then 1 else 0) (fzPos X e j) (by unfold frPos at hle1 ⊢; omega)
        (hfr1 j hj).2.2 hX (by omega) (by split_ifs <;> omega) hfrB ρ ⟨hx', hfr', hfd', hcf'⟩
      have hfv : ∀ z, z ∉ findBody.wvars → ρ'.vars z = ρ.vars z := fun z h => hr'.frame_var z h
      refine ⟨ρ', hr', by rw [hfv "j" (by decide), hjv], ?_, ?_, ?_, ?_, ?_⟩
      · simp only [arrs_setVar]; rw [hr'.frame_arr "x" (by decide)]; exact hx'
      · simp [hfv "ne" (by decide), hne']
      · simp only [vars_setVar, show ("fr" : String) = "j" ↔ False by decide, if_false, hfr2]
        unfold frPos; rw [hs]
      · simp only [vars_setVar, show ("fd" : String) = "j" ↔ False by decide, if_false, hfd2, fz_succ]
        cases hf : fz X e j <;> simp [gz] <;> split_ifs <;> simp_all
      · simp only [vars_setVar, show ("cf" : String) = "j" ↔ False by decide, if_false, hcf2, fzPos,
          fz_succ]
        cases hf : fz X e j <;> simp [gz] <;> split_ifs <;> simp_all)
  refine ⟨τ3, ?_, hI3.2.2.2.2⟩
  unfold findCmd
  refine (Run.seq ra (Run.seq r1 (Run.seq rne (Run.seq rfr (Run.seq rfd (Run.seq rcf r3)))))).mono ?_
  simp only [Expr.size]
  nlinarith

/-- **The first extension with guard `0`.** If the root has an extension
with guard `0`, the first frame with guard `0` holds such an extension. -/
theorem first_guard {X : List ℕ} {h ℓ : ℕ} {t : Node (h + 1) ℓ} {r : List ℕ}
    (hXt : X.drop 0 = toWord t ++ r) (hex : ∃ a ∈ Node.exts t, a.1.val = 0) :
    ∃ a ∈ Node.exts t, a.1.val = 0 ∧
      xg X (fzPos X (listEnd X 0) (xg X (listEnd X 0))) = (toWord a.2).length + 1 ∧
      ∃ r', X.drop (fzPos X (listEnd X 0) (xg X (listEnd X 0)) + 2) = toWord a.2 ++ r' := by
  obtain ⟨-, h2⟩ := nodeSplit hXt
  obtain ⟨h0, -, hfr, -⟩ := listAt h2
  set e := listEnd X 0
  obtain ⟨a, ha, ha0⟩ := hex
  have hmem : toWord a ∈ (Node.exts t).words := mem_words.mpr ⟨a, ha, rfl⟩
  obtain ⟨j, hj, hjw⟩ := List.getElem_of_mem hmem
  obtain ⟨hg, -⟩ := extFrame h2 hj hjw.symm
  have hgz : gz X e j = true := by simp [gz, hg, ha0]
  have hsome : (fz X e (xg X e)).isSome := by
    unfold fz
    rw [List.find?_isSome]
    exact ⟨j, by rw [List.mem_range, h0]; exact hj, hgz⟩
  obtain ⟨j0, hj0⟩ := Option.isSome_iff_exists.mp hsome
  have hj0m := List.mem_of_find?_eq_some hj0
  have hj0g := List.find?_some hj0
  rw [List.mem_range, h0] at hj0m
  obtain ⟨a0, ha0m, ha0w⟩ := getElem_words hj0m
  obtain ⟨hg0, r', hr'⟩ := extFrame h2 hj0m ha0w
  have hpos : fzPos X e (xg X e) = frPos X e j0 := by simp [fzPos, hj0]
  refine ⟨a0, ha0m, ?_, ?_, r', by rw [hpos]; exact hr'⟩
  · simp only [gz, beq_iff_eq] at hj0g; rw [← hg0, hj0g]
  · rw [hpos, (hfr j0 hj0m).1, ← ha0w, toWord_ext]; simp

def wHead : Com :=
  .seq (.write (.lit 1)) (.seq (.write (.lit 0)) (.seq (.write (.lit 0))
    (.seq (.write (.add (.var "hk") (.lit 1))) (.seq (.write (.sub (.var "hq") (.lit 1)))
      (.write (.add (.var "hl") (.lit 1)))))))

def wChild : Com :=
  .seq (.assign "ln" (.sub (.get "x" (.var "cf")) (.lit 1)))
    (forUp "i" (.var "ln") (.write (.get "x" (.add (.add (.var "cf") (.lit 2)) (.var "i")))))

def wJ : Com := .seq (.write (.var "hl")) (forUp "i" (.var "hl") (.write (.var "i")))

/-- The first round: the query. -/
def round0 : Com := .seq readTree (.seq findCmd (.seq wHead (.seq wChild wJ)))

/-- The second round: the answer. -/
def round1 : Com := .seq (.read "m") (.seq (.write (.lit 0)) copyLoop)

/-- The glue program. -/
def glue : Com :=
  .seq (.read "tg") (.seq (.read "sl") (.ite (.eq (.var "tg") (.lit 0)) round0 round1))

theorem condEq_var {B : ℕ} {ρ : Env} {x : String} {a n : ℕ} (h : ρ.vars x = a) (ha : a < B)
    (hn : n < B) : (Cond.eq (.var x) (.lit n)).evalB B ρ = some (a == n) := by
  simp only [evalB_condEq_iff, evalB_var_iff, evalB_lit_iff]
  exact ⟨a, n, ⟨h.symm, by omega⟩, ⟨rfl, hn⟩, rfl⟩

/-- **The second round.** -/
theorem glue_round1 (B : ℕ) (ext : String → ℕ) (b : List ℕ) (hb : ∀ v ∈ b, v < B)
    (hbB : b.length + 2 < B) :
    ∃ σ', Run B glue (initEnv ext ([1, 0, b.length] ++ b)) σ' (14 * b.length + 30) ∧
      σ'.out = 0 :: b := by
  set σ0 := initEnv ext ([1, 0, b.length] ++ b)
  set σ1 : Env := { σ0.setVar "tg" 1 with inp := 0 :: b.length :: b }
  set σ2 : Env := { σ1.setVar "sl" 0 with inp := b.length :: b }
  set σ3 : Env := { σ2.setVar "m" b.length with inp := b }
  set σ4 : Env := { σ3 with out := σ3.out ++ [0] }
  obtain ⟨σ5, r5, hout5, -⟩ := copyLoop_run (B := B) b [] hb (by omega) σ4 (by simp [σ4, σ3])
    (by simp [σ4, σ3])
  refine ⟨σ5, ?_, by rw [hout5]; simp [σ4, σ3, σ2, σ1, σ0, initEnv]⟩
  unfold glue round1
  refine (Run.seq (Run.read (by simp [σ0, initEnv])) (Run.seq (Run.read rfl)
    (Run.ite_false (condEq_var (a := 1) (by simp [σ2, σ1]) (by omega) (by omega))
      (Run.seq (Run.read rfl) (Run.seq (Run.write (v := 0) (by simp; omega)) r5))))).mono ?_
  simp only [Cond.size, Expr.size]; omega

theorem map_xg_drop {X : List ℕ} {s : ℕ} {w r : List ℕ} (h : X.drop s = w ++ r) :
    (List.range w.length).map (fun i => xg X (s + i)) = w := by
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range]
  exact Lax185574Proofs.EvalRam.xg_drop h (by simpa using h1)

set_option maxHeartbeats 1000000 in
/-- **The first round.** -/
theorem glue_round0 (B : ℕ) (ext : String → ℕ) (k q ℓ : ℕ) (t : Node (q + 1) ℓ)
    (hex : ∃ a ∈ Node.exts t, a.1.val = 0) (hext : (toWord t).length ≤ ext "x")
    (hv : ∀ v ∈ [k, q + 1, ℓ] ++ toWord t, v + 1 < B) (hB : ext "x" + 3 * (toWord t).length + 20 < B) :
    ∃ σ', Run B glue (initEnv ext ([0, (toWord t).length + 3] ++ ([k, q + 1, ℓ] ++ toWord t) ++ [0])) σ'
        (300 * ext "x" + 20 * ℓ + 300) ∧
      ∃ a ∈ Node.exts t, a.1.val = 0 ∧
        σ'.out = [1, 0, 0, k + 1, q, ℓ + 1] ++ toWord a.2 ++ (ℓ :: List.range ℓ) := by
  set n := (toWord t).length + 3 with hn
  set σ0 := initEnv ext ([0, n] ++ ([k, q + 1, ℓ] ++ toWord t) ++ [0]) with hσ0
  set σ1 : Env := { σ0.setVar "tg" 0 with inp := n :: ([k, q + 1, ℓ] ++ toWord t ++ [0]) } with hσ1
  set σ2 : Env := { σ1.setVar "sl" n with inp := [k, q + 1, ℓ] ++ toWord t ++ [0] } with hσ2
  have hkB : k + 1 < B := hv k (by simp)
  have hqB : q + 1 + 1 < B := hv (q + 1) (by simp)
  have hℓB : ℓ + 1 < B := hv ℓ (by simp)
  have htv : ∀ v ∈ toWord t, v < B := fun v h => by have := hv v (by simp [h]); omega
  set O := List.replicate (ext "x") 0 with hO
  obtain ⟨σ3, r3, hk3, hq3, hl3, hx3, -⟩ := readTree_spec B k (q + 1) ℓ t [0] O
    (by simp [hO]; omega) (by omega) htv (by omega) σ2 ⟨by simp [hσ2], by simp [hσ2, hσ1, hσ0, initEnv, hO]⟩
  set X := toWord t ++ O.drop (toWord t).length with hX
  have hXl : X.length = ext "x" := by simp [hX, hO]; omega
  have hXv : ∀ v ∈ X, v < B := by
    intro v hv'
    rcases List.mem_append.mp hv' with h | h
    · exact htv v h
    · rw [hO, List.drop_replicate] at h; rw [List.eq_of_mem_replicate h]; omega
  have hXt : X.drop 0 = toWord t ++ O.drop (toWord t).length := by simp [hX]
  obtain ⟨σ4, r4, hcf4⟩ := findCmd_spec B X t _ hXt hXv (by omega) σ3 hx3
  set cf := fzPos X (listEnd X 0) (xg X (listEnd X 0)) with hcf
  obtain ⟨a, ha, ha0, hlen, r', hdrop⟩ := first_guard hXt hex
  rw [← hcf] at hlen hdrop
  set L := (toWord a.2).length with hL
  have hcfX : cf + 2 + L ≤ X.length := by
    have h1 := congrArg List.length hdrop
    have := List.length_pos_iff.mpr (toWord_node_ne_nil a.2)
    simp at h1; omega
  have hv4 : ∀ z, z ∉ findCmd.wvars → σ4.vars z = σ3.vars z := fun z h => r4.frame_var z h
  have hx4 : σ4.arrs "x" = X := by rw [r4.frame_arr "x" (by decide), hx3]
  -- the head
  set σ5 : Env := { σ4 with out := σ4.out ++ [1, 0, 0, k + 1, q, ℓ + 1] } with hσ5
  have r5 : Run B wHead σ4 σ5 30 := by
    unfold wHead
    have hk4 : σ4.vars "hk" = k := by rw [hv4 "hk" (by decide)]; exact hk3
    have hq4 : σ4.vars "hq" = q + 1 := by rw [hv4 "hq" (by decide)]; exact hq3
    have hl4 : σ4.vars "hl" = ℓ := by rw [hv4 "hl" (by decide)]; exact hl3
    refine (Run.congr (Run.seq (Run.write (v := 1) (by simp; omega)) (Run.seq (Run.write (v := 0)
      (by simp; omega)) (Run.seq (Run.write (v := 0) (by simp; omega)) (Run.seq (Run.write (v := k + 1)
        ?_) (Run.seq (Run.write (v := q) ?_) (Run.write (v := ℓ + 1) ?_)))))) ?_).mono (by simp)
    · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
      exact ⟨k, 1, ⟨hk4.symm, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩
    · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
      exact ⟨q + 1, 1, ⟨hq4.symm, by omega⟩, ⟨rfl, by omega⟩, by simp, by omega⟩
    · simp only [evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
      exact ⟨ℓ, 1, ⟨hl4.symm, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩
    · simp [hσ5]
  -- the child
  have hcfx : xg X cf = L + 1 := hlen
  have hcfl : cf < X.length := by omega
  set σ6 := σ5.setVar "ln" L with hσ6
  have r6a : Run B (.assign "ln" (.sub (.get "x" (.var "cf")) (.lit 1))) σ5 σ6 5 := by
    refine (Run.assign ?_).mono (by simp)
    simp only [evalB_bin_iff, evalB_get_iff, evalB_var_iff, evalB_lit_iff]
    have hcf5 : σ5.vars "cf" = cf := by simp [hσ5, hcf4]
    refine ⟨L + 1, 1, ⟨cf, ⟨hcf5.symm, by omega⟩, ?_, by omega⟩, ⟨rfl, by omega⟩, by simp, by omega⟩
    simp only [hσ5, hx4]
    rw [List.getElem?_eq_getElem hcfl, ← xg_of_lt hcfl, hcfx]
  obtain ⟨σ7, r7, ⟨hx7, hcf7, -⟩, hout7⟩ := writeLoop_run (B := B) (N := L) (m := "ln")
    (e := .get "x" (.add (.add (.var "cf") (.lit 2)) (.var "i"))) (fun i => xg X (cf + 2 + i))
    (fun τ => τ.arrs "x" = X ∧ τ.vars "cf" = cf ∧ τ.vars "ln" = L) (by omega) (by decide)
    (fun τ o h => h) (fun τ k' h => ⟨by simpa using h.1, by simpa using h.2.1, by simpa using h.2.2⟩)
    (fun τ h => h.2.2)
    (fun τ h hi => by
      simp only [evalB_get_iff, evalB_bin_iff, evalB_var_iff, evalB_lit_iff]
      refine ⟨cf + 2 + τ.vars "i", ⟨cf + 2, τ.vars "i", ⟨cf, 2, ⟨h.2.1.symm, by omega⟩, ⟨rfl, by omega⟩,
        rfl, by omega⟩, ⟨rfl, by omega⟩, rfl, by omega⟩, ?_, xg_lt hXv (by omega)⟩
      rw [h.1, List.getElem?_eq_getElem (by omega), ← xg_of_lt (by omega)])
    σ6 ⟨by simp [hσ6, hσ5, hx4], by simp [hσ6, hσ5, hcf4], by simp [hσ6]⟩
  rw [map_xg_drop hdrop] at hout7
  -- the list of positions
  have hl7 : σ7.vars "hl" = ℓ := by
    rw [r7.frame_var "hl" (by decide)]; simp [hσ6, hσ5, hv4 "hl" (by decide), hl3]
  set σ8 : Env := { σ7 with out := σ7.out ++ [ℓ] } with hσ8
  obtain ⟨σ9, r9, -, hout9⟩ := writeLoop_run (B := B) (N := ℓ) (m := "hl") (e := .var "i") id
    (fun τ => τ.vars "hl" = ℓ) (by omega) (by decide) (fun τ o h => h)
    (fun τ k' h => by simpa using h) (fun τ h => h)
    (fun τ h hi => by simp only [evalB_var_iff]; exact ⟨rfl, by omega⟩) σ8 (by simp [hσ8, hl7])
  refine ⟨σ9, ?_, a, ha, ha0, ?_⟩
  · unfold glue round0 wChild wJ
    refine (Run.seq (Run.read (by simp [hσ0, initEnv])) (Run.seq (Run.read rfl)
      (Run.ite_true (condEq_var (a := 0) (by simp [hσ2, hσ1]) (by omega) (by omega))
        (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq (Run.seq r6a r7)
          (Run.seq (Run.write (v := ℓ) (by simp [hl7]; omega)) r9)))))))).mono ?_
    simp only [Cond.size, Expr.size]
    have : L ≤ ext "x" := by omega
    nlinarith
  · rw [hout9, hσ8, hout7, hσ6, hσ5]
    have h4 : σ4.out = [] := by
      rw [r4.out_eq (by simp [findCmd, skipList, skipBody, findBody, forUp, Com.NoWrite]),
        r3.out_eq readTree_noWrite]
      simp [hσ2, hσ1, hσ0, initEnv]
    simp [h4, List.map_id]

end Lax185574Proofs.ShiftRam
