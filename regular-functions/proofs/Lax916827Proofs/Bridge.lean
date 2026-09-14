import Lax916827.RegularFunctions
import Lax916827.TwoWayTransducers
import Lax916827.ConfigurationGraphs
import Lax916827.TwoWayCodes
import Lax916827.StreamingStringTransducers
import Lax916827.SnakeGraphs
import Lax765601Proofs.Bridge
import Lax132576Proofs.Bridge
import Lax916827Proofs.Source.PartC.Statements
import Lax916827Proofs.Source.PartC.SnakeAlphReg

/-!
The bridge between the concept package of Part C §1–3 and the ported source
development: every concept definition is shown equal or equivalent to its
source counterpart. The regular functions go through Part A's bridge for the
composition closure and the map lifting and Part B's for the rational
functions; two-way transducers and streaming string transducers are related
by `toSrc`/`ofSrc` with their semantics; the alphabet `C` of configuration
graphs is a distinct inductive type on the concept side, so its
representation and the path-walking transducer are transported along an
explicit bijection of the alphabets; the snake graphs and the codes of two-way
transducers are defined by the same formulas and are related by `Iff.rfl`.
-/

namespace Lax916827Proofs.Bridge

open Lax765601Proofs Lax132576Proofs
open Lax765601.Continuity Lax765601.MapLifting Lax765601.CompositionClosure
  Lax765601.MealyMachine
open Lax132576.RationalFunctions Lax132576.TransducerCodes
open Lax916827.RegularFunctions Lax916827.TwoWayTransducers Lax916827.ConfigurationGraphs
  Lax916827.TwoWayCodes Lax916827.StreamingStringTransducers Lax916827.SnakeGraphs

/-! ## Continuity and the regular functions -/

section Regular

variable {A B : Type}

lemma continuous_iff (f : List A → List B) :
    Continuous f ↔ Lax765601Proofs.Transducers.Continuous f := Iff.rfl

lemma mapReverse_eq (A : Type) : mapReverse A = Transducers.mapReverse A :=
  Lax765601Proofs.Bridge.mapLift_eq _

lemma mapDuplicate_eq (A : Type) : mapDuplicate A = Transducers.mapDuplicate A :=
  Lax765601Proofs.Bridge.mapLift_eq _

lemma regularFam_iff (A B : Type) (f : List A → List B) :
    RegularFam A B f ↔ Transducers.RegularFam A B f := by
  simp only [RegularFam, Transducers.RegularFam, Lax132576Proofs.Bridge.isRationalFun_iff,
    mapReverse_eq, mapDuplicate_eq]

lemma isRegularFun_iff (f : List A → List B) : IsRegularFun f ↔ Transducers.IsRegularFun f :=
  Lax765601Proofs.Bridge.compClosure_iff regularFam_iff

end Regular

/-! ## Two-way transducers -/

section TwoWay

variable {A A' B Q : Type}

/-- A concept two-way transducer as a source one. -/
def toSrcTW (M : TwoWay A B Q) : Transducers.TwoWay A B Q := ⟨M.init, M.step⟩

/-- A source two-way transducer as a concept one. -/
def ofSrcTW (M : Transducers.TwoWay A B Q) : TwoWay A B Q := ⟨M.init, M.step⟩

@[simp] lemma toSrcTW_ofSrcTW (M : Transducers.TwoWay A B Q) : toSrcTW (ofSrcTW M) = M := rfl

@[simp] lemma ofSrcTW_toSrcTW (M : TwoWay A B Q) : ofSrcTW (toSrcTW M) = M := rfl

@[simp] lemma toSrcTW_init (M : TwoWay A B Q) : (toSrcTW M).init = M.init := rfl

@[simp] lemma toSrcTW_step (M : TwoWay A B Q) (l : Option A) (q : Q) (r : Option A) :
    (toSrcTW M).step l q r = M.step l q r := rfl

/-- A concept configuration as a source configuration, the input letters renamed by `e`. -/
def cfgMap (e : A → A') : Cfg A Q → Transducers.Cfg A' Q
  | Cfg.conf u q v => Transducers.Cfg.conf (u.map e) q (v.map e)
  | Cfg.halt => Transducers.Cfg.halt

/-- A concept configuration as a source configuration. -/
def cfgToSrc : Cfg A Q → Transducers.Cfg A Q
  | Cfg.conf u q v => Transducers.Cfg.conf u q v
  | Cfg.halt => Transducers.Cfg.halt

@[simp] lemma cfgMap_conf (e : A → A') (u : List A) (q : Q) (v : List A) :
    cfgMap e (Cfg.conf u q v) = Transducers.Cfg.conf (u.map e) q (v.map e) := rfl

@[simp] lemma cfgMap_halt (e : A → A') : cfgMap e (Cfg.halt : Cfg A Q) = Transducers.Cfg.halt := rfl

@[simp] lemma cfgToSrc_conf (u : List A) (q : Q) (v : List A) :
    cfgToSrc (Cfg.conf u q v) = Transducers.Cfg.conf u q v := rfl

@[simp] lemma cfgToSrc_halt : cfgToSrc (Cfg.halt : Cfg A Q) = Transducers.Cfg.halt := rfl

lemma cfgMap_id (c : Cfg A Q) : cfgMap id c = cfgToSrc c := by
  cases c <;> simp

lemma cfgMap_eq_halt {e : A → A'} {c : Cfg A Q} :
    cfgMap e c = Transducers.Cfg.halt ↔ c = Cfg.halt := by
  cases c <;> simp

lemma cfgToSrc_injective : Function.Injective (cfgToSrc : Cfg A Q → Transducers.Cfg A Q) := by
  intro c c' h
  cases c <;> cases c' <;> simp_all

variable {M : TwoWay A B Q} {M' : Transducers.TwoWay A' B Q} {e : A → A'}

/-- One step of a source transducer whose transition function is that of `M` with the
letters renamed by `e`. -/
lemma stepCfg_cfgMap (hstep : ∀ l q r, M'.step (l.map e) q (r.map e) = M.step l q r) (c : Cfg A Q) :
    M'.stepCfg (cfgMap e c) = (M.stepCfg c).map (fun p => (p.1, cfgMap e p.2)) := by
  cases c with
  | halt => rfl
  | conf u q v =>
    simp only [cfgMap_conf, Transducers.TwoWay.stepCfg, TwoWay.stepCfg, List.getLast?_map,
      List.head?_map, hstep]
    rcases M.step u.getLast? q v.head? with o | ⟨q', o, _ | _⟩
    · rfl
    · cases hu : u.getLast? with
      | none => simp
      | some a => simp [List.map_dropLast]
    · cases v with
      | nil => rfl
      | cons a v' => simp

lemma reaches_cfgMap (hstep : ∀ l q r, M'.step (l.map e) q (r.map e) = M.step l q r)
    {c c' : Cfg A Q} {o : List B} (h : M.Reaches c o c') :
    M'.Reaches (cfgMap e c) o (cfgMap e c') := by
  induction h with
  | refl c => exact Transducers.TwoWay.Reaches.refl _
  | step hs _ ih =>
    exact Transducers.TwoWay.Reaches.step (by rw [stepCfg_cfgMap hstep, hs]; rfl) ih

lemma reaches_of_cfgMap (hstep : ∀ l q r, M'.step (l.map e) q (r.map e) = M.step l q r)
    {c : Cfg A Q} {o : List B} {c'' : Transducers.Cfg A' Q}
    (h : M'.Reaches (cfgMap e c) o c'') : ∃ c', c'' = cfgMap e c' ∧ M.Reaches c o c' := by
  generalize hx : cfgMap e c = x at h
  induction h generalizing c with
  | refl d => exact ⟨c, hx.symm, TwoWay.Reaches.refl c⟩
  | step hs _ ih =>
    subst hx
    rw [stepCfg_cfgMap hstep] at hs
    obtain ⟨⟨o₁, c₁⟩, h1, h2⟩ := Option.map_eq_some_iff.1 hs
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    obtain ⟨c₂, rfl, hr⟩ := ih rfl
    exact ⟨c₂, rfl, TwoWay.Reaches.step h1 hr⟩

/-- The computed relation of a source transducer whose transition function is that of `M`
with the letters renamed by `e`. -/
lemma computes_iff_of_step (hinit : M'.init = M.init)
    (hstep : ∀ l q r, M'.step (l.map e) q (r.map e) = M.step l q r) (w : List A) (v : List B) :
    M.Computes w v ↔ M'.Computes (w.map e) v := by
  constructor
  · intro h
    have := reaches_cfgMap hstep h
    simpa [TwoWay.Computes, Transducers.TwoWay.Computes, hinit] using this
  · intro h
    have h' : M'.Reaches (cfgMap e (Cfg.conf [] M.init w)) v Transducers.Cfg.halt := by
      simpa [Transducers.TwoWay.Computes, hinit] using h
    obtain ⟨c', hc', hr⟩ := reaches_of_cfgMap hstep h'
    rw [eq_comm, cfgMap_eq_halt] at hc'
    subst hc'
    exact hr

lemma toSrcTW_step_map (M : TwoWay A B Q) (l : Option A) (q : Q) (r : Option A) :
    (toSrcTW M).step (l.map id) q (r.map id) = M.step l q r := by
  cases l <;> cases r <;> rfl

lemma computes_toSrc (M : TwoWay A B Q) (w : List A) (v : List B) :
    M.Computes w v ↔ (toSrcTW M).Computes w v := by
  have := computes_iff_of_step (M := M) (M' := toSrcTW M) rfl (toSrcTW_step_map M) w v
  simpa using this

lemma isTwoWay_iff (f : List A → List B) : IsTwoWay f ↔ Transducers.IsTwoWay f := by
  constructor
  · rintro ⟨Q, hQ, M, hM⟩
    exact ⟨Q, hQ, toSrcTW M, fun w => (computes_toSrc M w _).1 (hM w)⟩
  · rintro ⟨Q, hQ, M, hM⟩
    exact ⟨Q, hQ, ofSrcTW M, fun w => (computes_toSrc (ofSrcTW M) w _).2 (hM w)⟩

lemma stepCfg_toSrc (M : TwoWay A B Q) (c : Cfg A Q) :
    (toSrcTW M).stepCfg (cfgToSrc c) = (M.stepCfg c).map (fun p => (p.1, cfgToSrc p.2)) := by
  have := stepCfg_cfgMap (M := M) (M' := toSrcTW M) (toSrcTW_step_map M) c
  simpa [cfgMap_id] using this

lemma cfgAt_toSrc (M : TwoWay A B Q) (w : List A) (n : ℕ) :
    (toSrcTW M).cfgAt w n = (M.cfgAt w n).map cfgToSrc := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Transducers.TwoWay.cfgAt, TwoWay.cfgAt, ih]
    cases M.cfgAt w n with
    | none => rfl
    | some c => simp [stepCfg_toSrc, Option.map_map, Function.comp_def]

lemma visits_toSrc (M : TwoWay A B Q) (w : List A) (c : Cfg A Q) :
    M.Visits w c ↔ (toSrcTW M).Visits w (cfgToSrc c) := by
  simp only [TwoWay.Visits, Transducers.TwoWay.Visits, cfgAt_toSrc, Option.map_eq_some_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨n, c, hn, rfl⟩
  · rintro ⟨n, c', hn, hc⟩
    obtain rfl := cfgToSrc_injective hc
    exact ⟨n, hn⟩

end TwoWay

/-! ## Configuration graphs -/

section ConfGraph

variable {A B Q L L' : Type}

/-- The outgoing edge of a vertex, the labels renamed by `g`. -/
def voutMap (g : L → L') : VOut Q L → Transducers.VOut Q L'
  | VOut.nil => Transducers.VOut.nil
  | VOut.move q l => Transducers.VOut.move q (g l)
  | VOut.halt l => Transducers.VOut.halt (g l)

/-- The inverse direction of `voutMap`. -/
def voutMapInv (g : L' → L) : Transducers.VOut Q L' → VOut Q L
  | Transducers.VOut.nil => VOut.nil
  | Transducers.VOut.move q l => VOut.move q (g l)
  | Transducers.VOut.halt l => VOut.halt (g l)

/-- The bijection between the concept's and the source's outgoing edges, along a
bijection of the labels. -/
def voutEquiv (g : L ≃ L') : VOut Q L ≃ Transducers.VOut Q L' where
  toFun := voutMap g
  invFun := voutMapInv g.symm
  left_inv := by rintro (_ | _ | _) <;> simp [voutMap, voutMapInv]
  right_inv := by rintro (_ | _ | _) <;> simp [voutMap, voutMapInv]

instance [Finite Q] [Finite L] : Finite (VOut Q L) :=
  Finite.of_equiv _ (voutEquiv (Equiv.refl L)).symm

variable (M : TwoWay A B Q)

lemma transOut_toSrc (l : Option A) (q : Q) (r : Option A) :
    Transducers.TwoWay.transOut (toSrcTW M) l q r = TwoWay.transOut M l q r := rfl

lemma outLabels_toSrc : Transducers.TwoWay.OutLabels (toSrcTW M) = TwoWay.OutLabels M := rfl

/-- A concept label as a source label. -/
def labToSrc (x : TwoWay.Lab M) : Transducers.TwoWay.Lab (toSrcTW M) := ⟨x.1, x.2⟩

/-- A source label as a concept label. -/
def labOfSrc (x : Transducers.TwoWay.Lab (toSrcTW M)) : TwoWay.Lab M := ⟨x.1, x.2⟩

@[simp] lemma labToSrc_val (x : TwoWay.Lab M) : (labToSrc M x).val = x.val := rfl

/-- The bijection of the labels. -/
def labEquiv : TwoWay.Lab M ≃ Transducers.TwoWay.Lab (toSrcTW M) where
  toFun := labToSrc M
  invFun := labOfSrc M
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite A] [Finite Q] : Finite (TwoWay.Lab M) := Finite.of_equiv _ (labEquiv M).symm

/-- A concept letter of the alphabet `C` as a source letter. -/
def cletToSrc : CLet Q (TwoWay.Lab M) → Transducers.CLet Q (Transducers.TwoWay.Lab (toSrcTW M))
  | Sum.inl s => Sum.inl (fun x => voutMap (labToSrc M) (s x))
  | Sum.inr l => Sum.inr (l.map (labToSrc M))

/-- A source letter of the alphabet `C` as a concept letter. -/
def cletOfSrc : Transducers.CLet Q (Transducers.TwoWay.Lab (toSrcTW M)) → CLet Q (TwoWay.Lab M)
  | Sum.inl s => Sum.inl (fun x => voutMapInv (labOfSrc M) (s x))
  | Sum.inr l => Sum.inr (l.map (labOfSrc M))

/-- The bijection of the alphabets `C`. -/
def cletEquiv : CLet Q (TwoWay.Lab M) ≃ Transducers.CLet Q (Transducers.TwoWay.Lab (toSrcTW M)) where
  toFun := cletToSrc M
  invFun := cletOfSrc M
  left_inv := by
    rintro (s | l)
    · simp only [cletToSrc, cletOfSrc, Sum.inl.injEq]
      funext x
      cases s x <;> rfl
    · cases l <;> rfl
  right_inv := by
    rintro (s | l)
    · simp only [cletToSrc, cletOfSrc, Sum.inl.injEq]
      funext x
      cases s x <;> rfl
    · cases l <;> rfl

@[simp] lemma cletEquiv_apply (x : CLet Q (TwoWay.Lab M)) : cletEquiv M x = cletToSrc M x := rfl

@[simp] lemma cletEquiv_symm_cletToSrc (x : CLet Q (TwoWay.Lab M)) :
    (cletEquiv M).symm (cletToSrc M x) = x := (cletEquiv M).symm_apply_apply x

lemma cletToSrc_injective : Function.Injective (cletToSrc M) := (cletEquiv M).injective

lemma labOf_toSrc (l : Option A) (q : Q) (r : Option A) :
    Transducers.TwoWay.labOf (toSrcTW M) l q r = labToSrc M (TwoWay.labOf M l q r) := rfl

lemma edgeOf_toSrc (l : Option A) (q : Q) (r : Option A) (d : Bool) :
    Transducers.TwoWay.edgeOf (toSrcTW M) l q r d = voutMap (labToSrc M) (TwoWay.edgeOf M l q r d) := by
  unfold Transducers.TwoWay.edgeOf TwoWay.edgeOf
  rw [toSrcTW_step]
  rcases M.step l q r with o | ⟨q', o, dir⟩
  · rfl
  · by_cases h : dir = d
    · simp [h, voutMap, labOf_toSrc]
    · simp [h, voutMap]

lemma prevAt_eq (w : List A) (j : ℕ) : TwoWay.prevAt w j = Transducers.TwoWay.prevAt w j := rfl

lemma cutV_toSrc (w : List A) (j : ℕ) (q : Q) (d : Bool) :
    Transducers.TwoWay.cutV (toSrcTW M) w j q d = voutMap (labToSrc M) (TwoWay.cutV M w j q d) := by
  unfold Transducers.TwoWay.cutV TwoWay.cutV
  by_cases h : M.Visits w (Cfg.conf (w.take j) q (w.drop j))
  · have h' : (toSrcTW M).Visits w (Transducers.Cfg.conf (w.take j) q (w.drop j)) :=
      (visits_toSrc M w _).1 h
    rw [if_pos h, if_pos h', edgeOf_toSrc, prevAt_eq]
  · have h' : ¬ (toSrcTW M).Visits w (Transducers.Cfg.conf (w.take j) q (w.drop j)) :=
      fun h' => h ((visits_toSrc M w _).2 h')
    rw [if_neg h, if_neg h']
    rfl

lemma encSlice_toSrc (w : List A) (i : ℕ) :
    Transducers.TwoWay.encSlice (toSrcTW M) w i =
      fun x => voutMap (labToSrc M) (TwoWay.encSlice M w i x) := by
  funext x
  simp only [Transducers.TwoWay.encSlice, TwoWay.encSlice, cutV_toSrc]

lemma emptyOut_toSrc :
    Transducers.TwoWay.emptyOut (toSrcTW M) = (TwoWay.emptyOut M).map (labToSrc M) := by
  unfold Transducers.TwoWay.emptyOut TwoWay.emptyOut
  rw [toSrcTW_step, toSrcTW_init]
  rcases M.step none M.init none with o | ⟨q', o, dir⟩ <;> rfl

/-- The representation of the reachable configuration graph, transported to the source's
alphabet. -/
lemma enc_toSrc (w : List A) :
    Transducers.TwoWay.enc (toSrcTW M) w = (TwoWay.enc M w).map (cletToSrc M) := by
  unfold Transducers.TwoWay.enc TwoWay.enc
  by_cases hw : w.isEmpty
  · rw [if_pos hw, if_pos hw]
    simp [cletToSrc, emptyOut_toSrc]
  · rw [if_neg hw, if_neg hw]
    simp only [List.map_map, Function.comp_def, cletToSrc, encSlice_toSrc]

lemma readR_toSrc (r : Option (CLet Q (TwoWay.Lab M))) (q : Q) :
    Transducers.TwoWay.readR (r.map (cletToSrc M)) q = voutMap (labToSrc M) (TwoWay.readR r q) := by
  rcases r with _ | (s | (_ | lab)) <;> rfl

lemma readL_toSrc (l : Option (CLet Q (TwoWay.Lab M))) (q : Q) :
    Transducers.TwoWay.readL (l.map (cletToSrc M)) q = voutMap (labToSrc M) (TwoWay.readL l q) := by
  rcases l with _ | (s | (_ | lab)) <;> rfl

lemma pathTrans_step (l : Option (CLet Q (TwoWay.Lab M))) (q : Q)
    (r : Option (CLet Q (TwoWay.Lab M))) :
    (TwoWay.pathTrans M).step l q r =
      match TwoWay.readR r q with
      | VOut.move q' lab => Sum.inr (q', lab.val, true)
      | VOut.halt lab => Sum.inl lab.val
      | VOut.nil =>
        match TwoWay.readL l q with
        | VOut.move q' lab => Sum.inr (q', lab.val, false)
        | VOut.halt lab => Sum.inl lab.val
        | VOut.nil => Sum.inl [] := rfl

lemma pathTrans_step_toSrc (l : Option (CLet Q (TwoWay.Lab M))) (q : Q)
    (r : Option (CLet Q (TwoWay.Lab M))) :
    (Transducers.TwoWay.pathTrans (toSrcTW M)).step (l.map (cletToSrc M)) q (r.map (cletToSrc M)) =
      (TwoWay.pathTrans M).step l q r := by
  rw [Transducers.TwoWay.pathTrans_step, pathTrans_step, readR_toSrc, readL_toSrc]
  cases TwoWay.readR r q <;> cases TwoWay.readL l q <;> rfl

/-- The output read off a representation, transported to the source's alphabet. -/
lemma computes_pathTrans (u : List (CLet Q (TwoWay.Lab M))) (v : List B) :
    (TwoWay.pathTrans M).Computes u v ↔
      (Transducers.TwoWay.pathTrans (toSrcTW M)).Computes (u.map (cletToSrc M)) v :=
  computes_iff_of_step rfl (pathTrans_step_toSrc M) u v

/-- The inverse image of a regular language under a letter-to-letter map is regular. -/
lemma isRegular_map {C C' : Type} (e : C → C') {L : Language C'} (hL : L.IsRegular) :
    Language.IsRegular ({u : List C | u.map e ∈ L} : Language C) :=
  Transducers.continuous_map e L hL

end ConfGraph

/-! ## Codes of two-way transducers -/

section Codes

lemma decidableUnderPromise_iff {α : Type} [Primcodable α] (promise P : α → Prop) :
    DecidableUnderPromise promise P ↔ Transducers.DecidableUnderPromise promise P := Iff.rfl

lemma twoWayCodeAut_toSrc (c : TwoWayCode) : toSrcTW (twoWayCodeAut c) = Transducers.twoWayCodeAut c :=
  rfl

lemma twoWayCodeRel_eq (c : TwoWayCode) : twoWayCodeRel c = Transducers.twoWayCodeRel c := by
  funext w v
  exact propext ((computes_toSrc _ w v).trans (by rw [twoWayCodeAut_toSrc]; exact Iff.rfl))

lemma twoWayCodeTotal_iff (c : TwoWayCode) : TwoWayCodeTotal c ↔ Transducers.TwoWayCodeTotal c := by
  simp only [TwoWayCodeTotal, Transducers.TwoWayCodeTotal, twoWayCodeRel_eq]

end Codes

/-! ## Streaming string transducers -/

section SST

variable {A B Q X : Type} [Fintype X]

/-- A concept streaming string transducer as a source one. -/
def toSrcSST (T : SST A B Q X) : Transducers.SST A B Q X :=
  ⟨T.init, T.step, T.step_copyless, T.final⟩

/-- A source streaming string transducer as a concept one. -/
def ofSrcSST (T : Transducers.SST A B Q X) : SST A B Q X :=
  ⟨T.init, T.step, T.step_copyless, T.final⟩

omit [Fintype X] in
lemma subst_eq (η : X → List B) (s : List (X ⊕ B)) : SST.subst η s = Transducers.SST.subst η s := rfl

lemma eval_toSrcSST (T : SST A B Q X) : (toSrcSST T).eval = T.eval := rfl

lemma isSST_iff (f : List A → List B) : IsSST f ↔ Transducers.IsSST f := by
  constructor
  · rintro ⟨Q, X, hQ, instX, T, hT⟩
    exact ⟨Q, X, hQ, instX, toSrcSST T, by rw [eval_toSrcSST, hT]⟩
  · rintro ⟨Q, X, hQ, instX, T, hT⟩
    exact ⟨Q, X, hQ, instX, ofSrcSST T, hT⟩

end SST

/-! ## Snake graphs -/

section Snake

variable {Q B : Type}

lemma edge_iff (w : List (SnakeLetter Q B)) (v v' : Vtx Q) (o : Option B) :
    Edge w v v' o ↔ Transducers.SnakeGraph.Edge w v v' o := Iff.rfl

lemma incident_iff (w : List (SnakeLetter Q B)) (v : Vtx Q) :
    Incident w v ↔ Transducers.SnakeGraph.Incident w v := Iff.rfl

lemma isSnakePath_iff (w : List (SnakeLetter Q B)) (m : ℕ) (p : ℕ → Vtx Q) (lab : ℕ → Option B) :
    IsSnakePath w m p lab ↔ Transducers.SnakeGraph.IsSnakePath w m p lab :=
  ⟨fun h => ⟨h.edge, h.inj, h.covers⟩, fun h => ⟨h.edge, h.inj, h.covers⟩⟩

lemma pathOut_eq (lab : ℕ → Option B) (m : ℕ) : pathOut lab m = Transducers.SnakeGraph.pathOut lab m :=
  rfl

lemma snakeOutIs_iff (w : List (SnakeLetter Q B)) (v : List B) :
    SnakeOutIs w v ↔ Transducers.SnakeGraph.SnakeOutIs w v := by
  simp only [SnakeOutIs, Transducers.SnakeGraph.SnakeOutIs, isSnakePath_iff, pathOut_eq]

lemma colVisits_eq (w : List (SnakeLetter Q B)) (i : ℕ) :
    colVisits w i = Transducers.SnakeGraph.colVisits w i := rfl

lemma snakeWidthLe_iff (w : List (SnakeLetter Q B)) (k : ℕ) :
    SnakeWidthLe w k ↔ Transducers.SnakeGraph.SnakeWidthLe w k := Iff.rfl

lemma snakeOut_eq (k : ℕ) (w : List (SnakeLetter Q B)) :
    snakeOut k w = Transducers.SnakeGraph.snakeOut k w := by
  classical
  by_cases h : SnakeWidthLe w k ∧ ∃ v, SnakeOutIs w v
  · obtain ⟨hk, v, hv⟩ := h
    have h1 : snakeOut k w = v := by
      have h' : SnakeWidthLe w k ∧ ∃ v, SnakeOutIs w v := ⟨hk, v, hv⟩
      rw [snakeOut, dif_pos h']
      exact Transducers.SnakeGraph.snakeOutIs_unique ((snakeOutIs_iff w _).1 h'.2.choose_spec)
        ((snakeOutIs_iff w v).1 hv)
    rw [h1, Transducers.SnakeGraph.snakeOut_eq ((snakeWidthLe_iff w k).1 hk)
      ((snakeOutIs_iff w v).1 hv)]
  · rw [snakeOut, dif_neg h, Transducers.SnakeGraph.snakeOut_of_not]
    rintro ⟨hk, v, hv⟩
    exact h ⟨(snakeWidthLe_iff w k).2 hk, v, (snakeOutIs_iff w v).2 hv⟩

lemma snakeOut_eq' (k : ℕ) :
    (snakeOut k : List (SnakeLetter Q B) → List B) = Transducers.SnakeGraph.snakeOut k :=
  funext (snakeOut_eq k)

end Snake

end Lax916827Proofs.Bridge
