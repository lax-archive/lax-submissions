import Lax194892.MarkedSquaring
import Lax194892.PolyregularFunctions
import Lax194892.ForTransducers
import Lax194892.PebbleTransducers
import Lax194892.PebbleConfigurationEncoding
import Lax194892.ChildConfigurationGraphs
import Lax765601Proofs.Bridge
import Lax916827Proofs.Bridge
import Lax916827Proofs.Source.PartC.RatBuild
import Lax194892Proofs.Source.PartD.Statements
import Lax194892Proofs.Source.PartD.PebReach
import Lax194892Proofs.Source.PartD.CGFor
import Lax194892Proofs.Source.PartD.ChildGraphFor

/-!
The bridge between the concept package of Part D and the ported source
development: every concept definition is shown equal or equivalent to its
source counterpart. Marked squaring and the polyregular family are defined by
the same formulas, so the polyregular functions go through Part A's
`compClosure_iff` and Part C's `isRegularFun_iff`; the syntax of
for-transducers and the actions of pebble transducers are distinct inductive
types on the concept side, related by `toSrc`/`ofSrc` pairs with their
semantics transported by induction (`exec_toSrcProg`, `reaches_toSrcPeb`); the
encodings of configurations unfold identically; the letters of child
configuration graphs are a distinct structure, and the graphs, their local
consistency test and their output are transported along the bijection
`cgLetterToSrc` of the alphabets.
-/

namespace Lax194892Proofs.Bridge

open Lax765601Proofs Lax132576Proofs Lax916827Proofs
open Lax765601.Continuity Lax765601.CompositionClosure
open Lax916827.RegularFunctions
open Lax194892.MarkedSquaring Lax194892.PolyregularFunctions Lax194892.ForTransducers
  Lax194892.PebbleTransducers Lax194892.PebbleConfigurationEncoding
  Lax194892.ChildConfigurationGraphs

/-! ## Polyregular functions -/

section Polyregular

variable {A B : Type}

lemma markedSquare_eq (A : Type) (w : List A) :
    markedSquare A w = Transducers.markedSquare A w := rfl

lemma polyregularFam_iff (A B : Type) (f : List A → List B) :
    PolyregularFam A B f ↔ Transducers.PolyregularFam A B f := by
  simp only [PolyregularFam, Transducers.PolyregularFam, Lax916827Proofs.Bridge.isRegularFun_iff,
    markedSquare_eq]

lemma isPolyregular_iff (f : List A → List B) : IsPolyregular f ↔ Transducers.IsPolyregular f :=
  Lax765601Proofs.Bridge.compClosure_iff polyregularFam_iff

end Polyregular

/-! ## For-transducers -/

section ForTransducers

variable {A B : Type}

/-- A concept test as a source test. -/
def toSrcTest : ForTest A → Transducers.ForTest A
  | ForTest.boolVar i => Transducers.ForTest.boolVar i
  | ForTest.eqPos i j => Transducers.ForTest.eqPos i j
  | ForTest.lePos i j => Transducers.ForTest.lePos i j
  | ForTest.label i a => Transducers.ForTest.label i a
  | ForTest.not t => Transducers.ForTest.not (toSrcTest t)
  | ForTest.and t s => Transducers.ForTest.and (toSrcTest t) (toSrcTest s)
  | ForTest.or t s => Transducers.ForTest.or (toSrcTest t) (toSrcTest s)

/-- A source test as a concept test. -/
def ofSrcTest : Transducers.ForTest A → ForTest A
  | Transducers.ForTest.boolVar i => ForTest.boolVar i
  | Transducers.ForTest.eqPos i j => ForTest.eqPos i j
  | Transducers.ForTest.lePos i j => ForTest.lePos i j
  | Transducers.ForTest.label i a => ForTest.label i a
  | Transducers.ForTest.not t => ForTest.not (ofSrcTest t)
  | Transducers.ForTest.and t s => ForTest.and (ofSrcTest t) (ofSrcTest s)
  | Transducers.ForTest.or t s => ForTest.or (ofSrcTest t) (ofSrcTest s)

@[simp] lemma toSrcTest_ofSrcTest (t : Transducers.ForTest A) : toSrcTest (ofSrcTest t) = t := by
  induction t <;> simp [toSrcTest, ofSrcTest, *]

@[simp] lemma ofSrcTest_toSrcTest (t : ForTest A) : ofSrcTest (toSrcTest t) = t := by
  induction t <;> simp [toSrcTest, ofSrcTest, *]

/-- A concept program as a source program. -/
def toSrcProg : ForProg A B → Transducers.ForProg A B
  | ForProg.skip => Transducers.ForProg.skip
  | ForProg.output b => Transducers.ForProg.output b
  | ForProg.assign i v => Transducers.ForProg.assign i v
  | ForProg.seq P Q => Transducers.ForProg.seq (toSrcProg P) (toSrcProg Q)
  | ForProg.ite t P Q => Transducers.ForProg.ite (toSrcTest t) (toSrcProg P) (toSrcProg Q)
  | ForProg.loop d x P => Transducers.ForProg.loop d x (toSrcProg P)

/-- A source program as a concept program. -/
def ofSrcProg : Transducers.ForProg A B → ForProg A B
  | Transducers.ForProg.skip => ForProg.skip
  | Transducers.ForProg.output b => ForProg.output b
  | Transducers.ForProg.assign i v => ForProg.assign i v
  | Transducers.ForProg.seq P Q => ForProg.seq (ofSrcProg P) (ofSrcProg Q)
  | Transducers.ForProg.ite t P Q => ForProg.ite (ofSrcTest t) (ofSrcProg P) (ofSrcProg Q)
  | Transducers.ForProg.loop d x P => ForProg.loop d x (ofSrcProg P)

@[simp] lemma toSrcProg_ofSrcProg (P : Transducers.ForProg A B) : toSrcProg (ofSrcProg P) = P := by
  induction P <;> simp [toSrcProg, ofSrcProg, *]

@[simp] lemma ofSrcProg_toSrcProg (P : ForProg A B) : ofSrcProg (toSrcProg P) = P := by
  induction P <;> simp [toSrcProg, ofSrcProg, *]

lemma holds_toSrcTest (w : List A) (pos : ℕ → ℕ) (bv : ℕ → Bool) (t : ForTest A) :
    Transducers.ForTest.Holds w pos bv (toSrcTest t) = ForTest.Holds w pos bv t := by
  induction t <;> simp [toSrcTest, Transducers.ForTest.Holds, ForTest.Holds, *]

lemma forLoopRun_eq (body : (ℕ → Bool) → ℕ → (ℕ → Bool) × List B) (l : List ℕ) (bv : ℕ → Bool) :
    forLoopRun body l bv = Transducers.forLoopRun body l bv := by
  induction l generalizing bv with
  | nil => rfl
  | cons p ps ih => simp [forLoopRun, Transducers.forLoopRun, ih]

/-- The semantics of a program is preserved by `toSrcProg`. -/
lemma exec_toSrcProg (w : List A) (P : ForProg A B) (pos : ℕ → ℕ) (bv : ℕ → Bool) :
    Transducers.ForProg.exec w (toSrcProg P) pos bv = ForProg.exec w P pos bv := by
  induction P generalizing pos bv with
  | skip => rfl
  | output b => rfl
  | assign i v => rfl
  | seq P Q ihP ihQ => simp [toSrcProg, Transducers.ForProg.exec, ForProg.exec, ihP, ihQ]
  | ite t P Q ihP ihQ =>
      simp only [toSrcProg, Transducers.ForProg.exec, ForProg.exec, ihP, ihQ]
      rw [holds_toSrcTest]
  | loop d x P ih =>
      simp only [toSrcProg, Transducers.ForProg.exec, ForProg.exec, ih, ← forLoopRun_eq]

lemma eval_toSrcProg (P : ForProg A B) (w : List A) :
    Transducers.ForProg.eval (toSrcProg P) w = ForProg.eval P w := by
  simp only [Transducers.ForProg.eval, ForProg.eval, exec_toSrcProg]

lemma eval_ofSrcProg (P : Transducers.ForProg A B) (w : List A) :
    ForProg.eval (ofSrcProg P) w = Transducers.ForProg.eval P w := by
  rw [← eval_toSrcProg, toSrcProg_ofSrcProg]

lemma isForTransducer_iff (f : List A → List B) :
    IsForTransducer f ↔ Transducers.IsForTransducer f := by
  constructor
  · rintro ⟨P, hP⟩
    exact ⟨toSrcProg P, fun w => by rw [eval_toSrcProg]; exact hP w⟩
  · rintro ⟨P, hP⟩
    exact ⟨ofSrcProg P, fun w => by rw [eval_ofSrcProg]; exact hP w⟩

lemma loopFree_toSrcProg (P : ForProg A B) :
    Transducers.ForProg.LoopFree (toSrcProg P) ↔ ForProg.LoopFree P := by
  induction P <;> simp [toSrcProg, Transducers.ForProg.LoopFree, ForProg.LoopFree, *]

lemma nestLoops_toSrcProg (ls : List (Bool × ℕ)) (body : ForProg A B) :
    Transducers.ForProg.nestLoops ls (toSrcProg body) = toSrcProg (ForProg.nestLoops ls body) := by
  induction ls with
  | nil => rfl
  | cons dx rest ih =>
      obtain ⟨d, x⟩ := dx
      simp [Transducers.ForProg.nestLoops, ForProg.nestLoops, toSrcProg, ih]

lemma outputsAtMostOne_toSrcProg (P : ForProg A B) :
    Transducers.ForProg.OutputsAtMostOne (toSrcProg P) ↔ ForProg.OutputsAtMostOne P := by
  simp only [Transducers.ForProg.OutputsAtMostOne, ForProg.OutputsAtMostOne, exec_toSrcProg]

lemma prenexForm_toSrcProg (P : ForProg A B) :
    Transducers.ForProg.PrenexForm (toSrcProg P) ↔ ForProg.PrenexForm P := by
  constructor
  · rintro ⟨ls, body, epi, hb, he, ho, hP⟩
    refine ⟨ls, ofSrcProg body, ofSrcProg epi, ?_, ?_, ?_, ?_⟩
    · rw [← loopFree_toSrcProg, toSrcProg_ofSrcProg]; exact hb
    · rw [← loopFree_toSrcProg, toSrcProg_ofSrcProg]; exact he
    · rw [← outputsAtMostOne_toSrcProg, toSrcProg_ofSrcProg]; exact ho
    · have h := congrArg ofSrcProg hP
      rw [ofSrcProg_toSrcProg] at h
      rw [h, ← toSrcProg_ofSrcProg body, nestLoops_toSrcProg]
      simp [ofSrcProg]
  · rintro ⟨ls, body, epi, hb, he, ho, hP⟩
    refine ⟨ls, toSrcProg body, toSrcProg epi, (loopFree_toSrcProg body).2 hb,
      (loopFree_toSrcProg epi).2 he, (outputsAtMostOne_toSrcProg body).2 ho, ?_⟩
    rw [hP, nestLoops_toSrcProg]
    rfl

end ForTransducers

/-! ## Pebble transducers -/

section Pebble

variable {A B Q : Type} {k : ℕ}

/-- A concept action as a source action. -/
def toSrcAct : PebbleAction B → Transducers.PebbleAction B
  | PebbleAction.out b => Transducers.PebbleAction.out b
  | PebbleAction.move d => Transducers.PebbleAction.move d
  | PebbleAction.push => Transducers.PebbleAction.push
  | PebbleAction.pop => Transducers.PebbleAction.pop
  | PebbleAction.terminate => Transducers.PebbleAction.terminate

/-- A source action as a concept action. -/
def ofSrcAct : Transducers.PebbleAction B → PebbleAction B
  | Transducers.PebbleAction.out b => PebbleAction.out b
  | Transducers.PebbleAction.move d => PebbleAction.move d
  | Transducers.PebbleAction.push => PebbleAction.push
  | Transducers.PebbleAction.pop => PebbleAction.pop
  | Transducers.PebbleAction.terminate => PebbleAction.terminate

@[simp] lemma toSrcAct_ofSrcAct (a : Transducers.PebbleAction B) : toSrcAct (ofSrcAct a) = a := by
  cases a <;> rfl

@[simp] lemma ofSrcAct_toSrcAct (a : PebbleAction B) : ofSrcAct (toSrcAct a) = a := by
  cases a <;> rfl

/-- A concept pebble transducer as a source one. -/
def toSrcPeb (M : Pebble A B Q k) : Transducers.Pebble A B Q k :=
  ⟨M.init, fun q v => ((M.step q v).1, toSrcAct (M.step q v).2)⟩

/-- A source pebble transducer as a concept one. -/
def ofSrcPeb (M : Transducers.Pebble A B Q k) : Pebble A B Q k :=
  ⟨M.init, fun q v => ((M.step q v).1, ofSrcAct (M.step q v).2)⟩

@[simp] lemma toSrcPeb_ofSrcPeb (M : Transducers.Pebble A B Q k) : toSrcPeb (ofSrcPeb M) = M := by
  cases M; simp [toSrcPeb, ofSrcPeb]

@[simp] lemma ofSrcPeb_toSrcPeb (M : Pebble A B Q k) : ofSrcPeb (toSrcPeb M) = M := by
  cases M; simp [toSrcPeb, ofSrcPeb]

lemma viewOf_eq (w : List A) (st : List ℕ) : viewOf w st = Transducers.viewOf w st := rfl

/-- A concept configuration as a source configuration. -/
def cfgToSrc : PebbleCfg Q → Transducers.PebbleCfg Q
  | PebbleCfg.conf q st => Transducers.PebbleCfg.conf q st
  | PebbleCfg.halt => Transducers.PebbleCfg.halt

/-- A source configuration as a concept configuration. -/
def cfgOfSrc : Transducers.PebbleCfg Q → PebbleCfg Q
  | Transducers.PebbleCfg.conf q st => PebbleCfg.conf q st
  | Transducers.PebbleCfg.halt => PebbleCfg.halt

@[simp] lemma cfgToSrc_conf (q : Q) (st : List ℕ) :
    cfgToSrc (PebbleCfg.conf q st) = Transducers.PebbleCfg.conf q st := rfl

@[simp] lemma cfgToSrc_halt : cfgToSrc (PebbleCfg.halt : PebbleCfg Q) = Transducers.PebbleCfg.halt :=
  rfl

@[simp] lemma cfgToSrc_cfgOfSrc (c : Transducers.PebbleCfg Q) : cfgToSrc (cfgOfSrc c) = c := by
  cases c <;> rfl

@[simp] lemma cfgOfSrc_cfgToSrc (c : PebbleCfg Q) : cfgOfSrc (cfgToSrc c) = c := by
  cases c <;> rfl

lemma cfgToSrc_injective : Function.Injective (cfgToSrc : PebbleCfg Q → Transducers.PebbleCfg Q) :=
  Function.LeftInverse.injective cfgOfSrc_cfgToSrc

lemma cfgToSrc_eq_conf {c : PebbleCfg Q} {q : Q} {st : List ℕ} :
    cfgToSrc c = Transducers.PebbleCfg.conf q st ↔ c = PebbleCfg.conf q st := by
  cases c <;> simp

/-- One step of the source transducer `toSrcPeb M` is one step of `M`. -/
lemma stepCfg_toSrcPeb (M : Pebble A B Q k) (w : List A) (c : PebbleCfg Q) :
    (toSrcPeb M).stepCfg w (cfgToSrc c) = (M.stepCfg w c).map (fun p => (p.1, cfgToSrc p.2)) := by
  cases c with
  | halt => rfl
  | conf q st =>
      simp only [cfgToSrc_conf, Transducers.Pebble.stepCfg, Pebble.stepCfg, toSrcPeb, ← viewOf_eq]
      generalize M.step q (viewOf w st) = r
      obtain ⟨q', a⟩ := r
      cases a with
      | out b => rfl
      | terminate => rfl
      | push => simp only [toSrcAct]; split_ifs <;> rfl
      | pop => simp only [toSrcAct]; split_ifs <;> rfl
      | move dir =>
          simp only [toSrcAct]
          cases st.getLast? with
          | none => rfl
          | some p => cases dir <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> split_ifs <;> rfl

lemma stepCfg_toSrcPeb_eq_some {M : Pebble A B Q k} {w : List A} {c : PebbleCfg Q} {o : List B}
    {c' : Transducers.PebbleCfg Q} (h : (toSrcPeb M).stepCfg w (cfgToSrc c) = some (o, c')) :
    ∃ d, M.stepCfg w c = some (o, d) ∧ cfgToSrc d = c' := by
  rw [stepCfg_toSrcPeb, Option.map_eq_some_iff] at h
  obtain ⟨⟨o', d⟩, hd, he⟩ := h
  simp only [Prod.mk.injEq] at he
  exact ⟨d, he.1 ▸ hd, he.2⟩

lemma stepCfg_toSrcPeb_of_eq {M : Pebble A B Q k} {w : List A} {c d : PebbleCfg Q} {o : List B}
    (h : M.stepCfg w c = some (o, d)) :
    (toSrcPeb M).stepCfg w (cfgToSrc c) = some (o, cfgToSrc d) := by
  rw [stepCfg_toSrcPeb, h]; rfl

/-- Reachability in the configuration graph is preserved by `toSrcPeb`. -/
lemma reaches_toSrcPeb (M : Pebble A B Q k) (w : List A) (c : PebbleCfg Q) (v : List B)
    (c' : PebbleCfg Q) :
    (toSrcPeb M).Reaches w (cfgToSrc c) v (cfgToSrc c') ↔ M.Reaches w c v c' := by
  constructor
  · suffices h : ∀ {c₁ : Transducers.PebbleCfg Q} {v : List B} {c₂ : Transducers.PebbleCfg Q},
        (toSrcPeb M).Reaches w c₁ v c₂ → ∀ c c' : PebbleCfg Q, c₁ = cfgToSrc c → c₂ = cfgToSrc c' →
          M.Reaches w c v c' from fun hr => h hr c c' rfl rfl
    intro c₁ v c₂ hr
    induction hr with
    | refl c₁ =>
        intro c c' h1 h2
        rw [cfgToSrc_injective (h1.symm.trans h2)]
        exact Pebble.Reaches.refl _
    | step hs _ ih =>
        intro c c' h1 h2
        subst h1
        obtain ⟨d, hd, rfl⟩ := stepCfg_toSrcPeb_eq_some hs
        exact Pebble.Reaches.step hd (ih d c' rfl h2)
  · intro hr
    induction hr with
    | refl c => exact Transducers.Pebble.Reaches.refl _
    | step hs _ ih => exact Transducers.Pebble.Reaches.step (stepCfg_toSrcPeb_of_eq hs) ih

lemma computes_toSrcPeb (M : Pebble A B Q k) (w : List A) (v : List B) :
    (toSrcPeb M).Computes w v ↔ M.Computes w v :=
  reaches_toSrcPeb M w (PebbleCfg.conf M.init []) v PebbleCfg.halt

lemma isPebbleTransducer_iff (f : List A → List B) :
    IsPebbleTransducer f ↔ Transducers.IsPebbleTransducer f := by
  constructor
  · rintro ⟨k, Q, hQ, M, hM⟩
    exact ⟨k, Q, hQ, toSrcPeb M, fun w => (computes_toSrcPeb M w _).2 (hM w)⟩
  · rintro ⟨k, Q, hQ, M, hM⟩
    refine ⟨k, Q, hQ, ofSrcPeb M, fun w => (computes_toSrcPeb _ w _).1 ?_⟩
    rw [toSrcPeb_ofSrcPeb]
    exact hM w

/-! ### Encodings of configurations and balanced runs -/

/-- Restricted reachability is preserved by `toSrcPeb`. -/
lemma restrReaches_toSrcPeb (M : Pebble A B Q k) (w : List A) (ℓ : ℕ) (c c' : PebbleCfg Q) :
    (toSrcPeb M).RestrReaches w ℓ (cfgToSrc c) (cfgToSrc c') ↔ RestrReaches M w ℓ c c' := by
  constructor
  · suffices h : ∀ {c₁ c₂ : Transducers.PebbleCfg Q},
        (toSrcPeb M).RestrReaches w ℓ c₁ c₂ → ∀ c c' : PebbleCfg Q, c₁ = cfgToSrc c →
          c₂ = cfgToSrc c' → RestrReaches M w ℓ c c' from fun hr => h hr c c' rfl rfl
    intro c₁ c₂ hr
    induction hr with
    | refl q st h =>
        intro c c' h1 h2
        rw [eq_comm, cfgToSrc_eq_conf] at h1 h2
        subst h1; subst h2
        exact RestrReaches.refl q st h
    | step h hs _ ih =>
        intro c c' h1 h2
        rw [eq_comm, cfgToSrc_eq_conf] at h1
        subst h1
        obtain ⟨d, hd, rfl⟩ := stepCfg_toSrcPeb_eq_some (c := PebbleCfg.conf _ _) hs
        exact RestrReaches.step h hd (ih d c' rfl h2)
  · intro hr
    induction hr with
    | refl q st h => exact Transducers.Pebble.RestrReaches.refl q st h
    | step h hs _ ih => exact Transducers.Pebble.RestrReaches.step h (stepCfg_toSrcPeb_of_eq hs) ih

lemma balancedRun_toSrcPeb (M : Pebble A B Q k) (w : List A) (ℓ : ℕ) (c c' : PebbleCfg Q) :
    (toSrcPeb M).BalancedRun w ℓ (cfgToSrc c) (cfgToSrc c') ↔ BalancedRun M w ℓ c c' :=
  restrReaches_toSrcPeb M w ℓ c c'

lemma ann_eq (k : ℕ) (st : List ℕ) (p : ℕ) : ann k st p = Transducers.PebEnc.ann k st p := rfl

lemma pairEnc_eq (q₁ q₂ : Q) (sts stt : List ℕ) (w : List A) :
    pairEnc (k := k) q₁ q₂ sts stt w = Transducers.PebEnc.pairEnc (k := k) q₁ q₂ sts stt w := rfl

end Pebble

/-! ## Child configuration graphs -/

section ChildGraph

variable {A B Q : Type} {k : ℕ}

/-! ### The children of a configuration -/

lemma heightGe_cfgToSrc (h : ℕ) (c : PebbleCfg Q) :
    Transducers.Pebble.HeightGe h (cfgToSrc c) ↔ HeightGe h c := by
  cases c <;> exact Iff.rfl

/-- Runs staying above a height are preserved by `toSrcPeb`. -/
lemma strictAbove_toSrcPeb (M : Pebble A B Q k) (w : List A) (h : ℕ) (c c' : PebbleCfg Q) :
    (toSrcPeb M).StrictAbove w h (cfgToSrc c) (cfgToSrc c') ↔ StrictAbove M w h c c' := by
  constructor
  · suffices hh : ∀ {c₁ c₂ : Transducers.PebbleCfg Q},
        (toSrcPeb M).StrictAbove w h c₁ c₂ → ∀ c c' : PebbleCfg Q, c₁ = cfgToSrc c →
          c₂ = cfgToSrc c' → StrictAbove M w h c c' from fun hr => hh hr c c' rfl rfl
    intro c₁ c₂ hr
    induction hr with
    | one hs =>
        intro c c' h1 h2
        subst h1; subst h2
        obtain ⟨d, hd, hdc⟩ := stepCfg_toSrcPeb_eq_some hs
        rw [cfgToSrc_injective hdc] at hd
        exact StrictAbove.one hd
    | cons hs hge _ ih =>
        intro c c' h1 h2
        subst h1
        obtain ⟨d, hd, rfl⟩ := stepCfg_toSrcPeb_eq_some hs
        exact StrictAbove.cons hd ((heightGe_cfgToSrc h d).1 hge) (ih d c' rfl h2)
  · intro hr
    induction hr with
    | one hs => exact Transducers.Pebble.StrictAbove.one (stepCfg_toSrcPeb_of_eq hs)
    | cons hs hge _ ih =>
        exact Transducers.Pebble.StrictAbove.cons (stepCfg_toSrcPeb_of_eq hs)
          ((heightGe_cfgToSrc h _).2 hge) ih

lemma cfgOf_toSrc (st : List ℕ) (v : Vtx Q) : cfgToSrc (cfgOf st v) = Transducers.CG.cfgOf st v := rfl

lemma nextChild_toSrcPeb (M : Pebble A B Q k) (w : List A) (st : List ℕ) (v v' : Vtx Q) :
    Transducers.CG.NextChild (toSrcPeb M) w st v v' ↔ NextChild M w st v v' :=
  strictAbove_toSrcPeb M w _ (cfgOf st v) (cfgOf st v')

lemma firstChild_toSrcPeb (M : Pebble A B Q k) (w : List A) (q : Q) (st : List ℕ) (v : Vtx Q) :
    Transducers.CG.FirstChild (toSrcPeb M) w q st v ↔ FirstChild M w q st v :=
  strictAbove_toSrcPeb M w _ (PebbleCfg.conf q st) (cfgOf st v)

lemma isChildSeq_toSrcPeb (M : Pebble A B Q k) (w : List A) (q : Q) (st : List ℕ) (ch : ℕ → Vtx Q)
    (m : ℕ) : Transducers.CG.IsChildSeq (toSrcPeb M) w q st ch m ↔ IsChildSeq M w q st ch m := by
  constructor
  · intro h
    exact ⟨(firstChild_toSrcPeb M w q st _).1 h.first,
      fun t ht => (nextChild_toSrcPeb M w st _ _).1 (h.next t ht),
      fun v hv => h.stop v ((nextChild_toSrcPeb M w st _ _).2 hv)⟩
  · intro h
    exact ⟨(firstChild_toSrcPeb M w q st _).2 h.first,
      fun t ht => (nextChild_toSrcPeb M w st _ _).2 (h.next t ht),
      fun v hv => h.stop v ((nextChild_toSrcPeb M w st _ _).1 hv)⟩

/-! ### String representations -/

lemma confEnc_eq (q : Q) (st : List ℕ) (w : List A) :
    confEnc (k := k) q st w = Transducers.CG.confEnc (k := k) q st w := rfl

/-- A concept letter of a child configuration graph as a source letter. -/
def cgLetterToSrc (c : CGLetter A Q k) : Transducers.CG.CGLetter A Q k :=
  ⟨c.lett, c.peb, c.nid, c.src, c.nxt, c.prv⟩

/-- A source letter of a child configuration graph as a concept letter. -/
def cgLetterOfSrc (c : Transducers.CG.CGLetter A Q k) : CGLetter A Q k :=
  ⟨c.lett, c.peb, c.nid, c.src, c.nxt, c.prv⟩

@[simp] lemma cgLetterToSrc_lett (c : CGLetter A Q k) : (cgLetterToSrc c).lett = c.lett := rfl
@[simp] lemma cgLetterToSrc_peb (c : CGLetter A Q k) : (cgLetterToSrc c).peb = c.peb := rfl
@[simp] lemma cgLetterToSrc_nid (c : CGLetter A Q k) : (cgLetterToSrc c).nid = c.nid := rfl
@[simp] lemma cgLetterToSrc_src (c : CGLetter A Q k) : (cgLetterToSrc c).src = c.src := rfl
@[simp] lemma cgLetterToSrc_nxt (c : CGLetter A Q k) : (cgLetterToSrc c).nxt = c.nxt := rfl
@[simp] lemma cgLetterToSrc_prv (c : CGLetter A Q k) : (cgLetterToSrc c).prv = c.prv := rfl

@[simp] lemma cgLetterToSrc_ofSrc (c : Transducers.CG.CGLetter A Q k) :
    cgLetterToSrc (cgLetterOfSrc c) = c := rfl

@[simp] lemma cgLetterOfSrc_toSrc (c : CGLetter A Q k) : cgLetterOfSrc (cgLetterToSrc c) = c := rfl

/-- The bijection between the two alphabets of child configuration graphs. -/
def cgLetterEquiv : CGLetter A Q k ≃ Transducers.CG.CGLetter A Q k :=
  ⟨cgLetterToSrc, cgLetterOfSrc, cgLetterOfSrc_toSrc, cgLetterToSrc_ofSrc⟩

/-- The concept's alphabet of child configuration graphs is finite, as the source's is. -/
instance instFiniteCGLetter [Finite A] [Finite Q] : Finite (CGLetter A Q k) :=
  Finite.of_equiv _ (cgLetterEquiv (A := A) (Q := Q) (k := k)).symm

@[simp] lemma map_cgLetterOfSrc_map_toSrc (u : List (CGLetter A Q k)) :
    (u.map cgLetterToSrc).map cgLetterOfSrc = u := by
  simp [List.map_map, Function.comp_def]

@[simp] lemma map_cgLetterToSrc_map_ofSrc (u : List (Transducers.CG.CGLetter A Q k)) :
    (u.map cgLetterOfSrc).map cgLetterToSrc = u := by
  simp [List.map_map, Function.comp_def]

lemma dest_eq (p : ℕ) (d : Dir) : dest p d = Transducers.CG.dest p d := rfl

lemma dirOf_eq (a b : ℕ) : dirOf a b = Transducers.CG.dirOf a b := rfl

lemma idxAt_eq (ch : ℕ → Vtx Q) (m : ℕ) (v : Vtx Q) : idxAt ch m v = Transducers.CG.idxAt ch m v := rfl

lemma idxSuccAt_eq (ch : ℕ → Vtx Q) (m : ℕ) (v : Vtx Q) :
    idxSuccAt ch m v = Transducers.CG.idxSuccAt ch m v := rfl

/-- The representation of a child configuration graph, transported to the source's alphabet. -/
lemma cgOfPath_toSrc (lett : ℕ → Option A) (peb : ℕ → Fin k → Bool) (nid : Fin k) (n : ℕ)
    (ch : ℕ → Vtx Q) (m : ℕ) :
    (cgOfPath lett peb nid n ch m).map cgLetterToSrc = Transducers.CG.cgOfPath lett peb nid n ch m := by
  simp only [cgOfPath, Transducers.CG.cgOfPath, List.map_map]
  rfl

lemma cgOfChildren_toSrc (w : List A) (st : List ℕ) (nid : Fin k) (ch : ℕ → Vtx Q) (m : ℕ) :
    (cgOfChildren w st nid ch m).map cgLetterToSrc = Transducers.CG.cgOfChildren w st nid ch m :=
  cgOfPath_toSrc _ _ _ _ _ _

lemma cgOfChildren_eq_map_ofSrc (w : List A) (st : List ℕ) (nid : Fin k) (ch : ℕ → Vtx Q) (m : ℕ) :
    cgOfChildren w st nid ch m = (Transducers.CG.cgOfChildren w st nid ch m).map cgLetterOfSrc := by
  rw [← cgOfChildren_toSrc, map_cgLetterOfSrc_map_toSrc]

/-! ### Reading the children off a represented graph -/

variable (u : List (CGLetter A Q k))

lemma succOf_map_toSrc (v : Vtx Q) : Transducers.CG.succOf (u.map cgLetterToSrc) v = succOf u v := by
  simp only [Transducers.CG.succOf, succOf, List.getElem?_map]
  cases u[v.2]? <;> rfl

lemma isSrc_map_toSrc (v : Vtx Q) : Transducers.CG.IsSrc (u.map cgLetterToSrc) v ↔ IsSrc u v := by
  simp only [Transducers.CG.IsSrc, IsSrc, List.getElem?_map]
  cases u[v.2]? <;> simp

lemma confAt_map_toSrc (v : Vtx Q) : Transducers.CG.confAt (u.map cgLetterToSrc) v = confAt u v := by
  apply List.ext_getElem
  · simp [Transducers.CG.confAt, confAt]
  · intro i h₁ h₂
    simp [Transducers.CG.confAt, confAt]

lemma leftLet_map_toSrc (i : ℕ) :
    Transducers.CG.leftLet (u.map cgLetterToSrc) i = (leftLet u i).map cgLetterToSrc := by
  simp only [Transducers.CG.leftLet, leftLet, List.getElem?_map]
  split_ifs <;> rfl

lemma pairOK_map_toSrc (a b : Option (CGLetter A Q k)) :
    Transducers.CG.pairOK (a.map cgLetterToSrc) (b.map cgLetterToSrc) = pairOK a b := by
  simp only [Transducers.CG.pairOK, pairOK, decide_eq_decide]
  cases a <;> cases b <;> simp

lemma chk_map_toSrc : Transducers.CG.Chk (u.map cgLetterToSrc) ↔ Chk u := by
  simp only [Transducers.CG.Chk, Chk, List.length_map, leftLet_map_toSrc, List.getElem?_map,
    pairOK_map_toSrc]

lemma cgPath_map_toSrc (m : ℕ) (p : ℕ → Vtx Q) :
    Transducers.CG.CGPath (u.map cgLetterToSrc) m p ↔ CGPath u m p := by
  constructor
  · intro h
    exact ⟨(chk_map_toSrc u).1 h.chk, fun v => (isSrc_map_toSrc u v).symm.trans (h.srcEq v),
      fun t ht => by simpa [List.getElem?_map] using h.inRange t ht,
      fun t ht => (succOf_map_toSrc u _).symm.trans (h.step t ht),
      (succOf_map_toSrc u _).symm.trans h.last⟩
  · intro h
    exact ⟨(chk_map_toSrc u).2 h.chk, fun v => (isSrc_map_toSrc u v).trans (h.srcEq v),
      fun t ht => by simpa [List.getElem?_map] using h.inRange t ht,
      fun t ht => (succOf_map_toSrc u _).trans (h.step t ht),
      (succOf_map_toSrc u _).trans h.last⟩

lemma cgOut_map_toSrc (m : ℕ) (p : ℕ → Vtx Q) :
    Transducers.CG.cgOut (u.map cgLetterToSrc) m p = cgOut u m p := by
  simp only [Transducers.CG.cgOut, cgOut, confAt_map_toSrc]

lemma cgOutIs_map_toSrc (v : List (ConfLetter A Q k)) :
    Transducers.CG.CGOutIs (u.map cgLetterToSrc) v ↔ CGOutIs u v := by
  simp only [Transducers.CG.CGOutIs, CGOutIs, cgPath_map_toSrc, cgOut_map_toSrc]

/-! ### Letter-to-letter maps are for-transducers -/

/-- A letter-to-letter map between finite alphabets is computed by a for-transducer (through
the rational functions of Part B and Theorem D.1.1). -/
lemma isForTransducer_map {C D : Type} [Finite C] [Finite D] (e : C → D) :
    Transducers.IsForTransducer (fun w : List C => w.map e) :=
  (Transducers.polyregular_iff_forTransducer _).1
    (Transducers.IsPolyregular.of_regular
      (Transducers.IsRegularFun.of_rational (Transducers.isRationalFun_map e)))

end ChildGraph

end Lax194892Proofs.Bridge
