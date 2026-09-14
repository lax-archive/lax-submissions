/-
# Effectiveness of the reduction

Sipser's proof of Theorem 5.15 constructs, from a Turing machine `M` and an input `w`,
a PCP instance `sipserPCP M w`.  Here we check the part of the argument that Sipser
takes for granted: the construction is *effective*.  Concretely, we show that
`fun (M, w) ↦ sipserPCP M w` is a primitive recursive (hence computable) function.
-/
import Lax251941Proofs.Source.PCP.Reduction

namespace Lax251941Proofs.PCP

/-! ## Encodings -/

/-- The symbols of `Sym` are encoded as `ℕ ⊕ ℕ ⊕ Fin 4`. -/
def symEquiv : Sym ≃ ℕ ⊕ ℕ ⊕ Fin 4 where
  toFun
    | .tape n => .inl n
    | .state n => .inr (.inl n)
    | .hash => .inr (.inr 0)
    | .start => .inr (.inr 1)
    | .star => .inr (.inr 2)
    | .diamond => .inr (.inr 3)
  invFun
    | .inl n => .tape n
    | .inr (.inl n) => .state n
    | .inr (.inr ⟨0, _⟩) => .hash
    | .inr (.inr ⟨1, _⟩) => .start
    | .inr (.inr ⟨2, _⟩) => .star
    | .inr (.inr ⟨_, _⟩) => .diamond
  left_inv := by rintro (n | n | _ | _ | _ | _) <;> rfl
  right_inv := by
    rintro (n | n | i)
    · rfl
    · rfl
    · fin_cases i <;> rfl

instance : Primcodable Sym := Primcodable.ofEquiv _ symEquiv

/-- A Turing machine is encoded by its transition table together with its two
distinguished states. -/
def tmEquiv : TM ≃ List (ℕ × ℕ × ℕ × ℕ × Bool) × ℕ × ℕ where
  toFun M := (M.trans, M.q0, M.qacc)
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv := by rintro ⟨t, a, b⟩; rfl
  right_inv := by rintro ⟨t, a, b⟩; rfl

instance : Primcodable TM := Primcodable.ofEquiv _ tmEquiv

lemma primrec_tape : Primrec Sym.tape :=
  ((Primrec.of_equiv_symm_iff symEquiv).2 Primrec.sumInl).of_eq fun _ => rfl

lemma primrec_state : Primrec Sym.state :=
  ((Primrec.of_equiv_symm_iff symEquiv).2
    (Primrec.sumInr.comp Primrec.sumInl)).of_eq fun _ => rfl

lemma primrec_trans : Primrec TM.trans :=
  (Primrec.fst.comp (Primrec.of_equiv (e := tmEquiv))).of_eq fun _ => rfl

lemma primrec_q0 : Primrec TM.q0 :=
  (Primrec.fst.comp (Primrec.snd.comp (Primrec.of_equiv (e := tmEquiv)))).of_eq fun _ => rfl

lemma primrec_qacc : Primrec TM.qacc :=
  (Primrec.snd.comp (Primrec.snd.comp (Primrec.of_equiv (e := tmEquiv)))).of_eq fun _ => rfl

/-! ## The pieces of the construction are primitive recursive -/

/-- The argument of the reduction: a machine together with an input word. -/
abbrev Arg := TM × List ℕ

lemma primrec_argTrans : Primrec fun p : Arg => p.1.trans :=
  primrec_trans.comp Primrec.fst

lemma primrec_tapeSyms : Primrec fun p : Arg => p.1.tapeSyms p.2 := by
  have hm1 : Primrec fun p : Arg => p.1.trans.map (fun x => x.2.1) :=
    Primrec.list_map primrec_argTrans
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd (α := Arg)))).to₂
  have hm2 : Primrec fun p : Arg => p.1.trans.map (fun x => x.2.2.2.1) :=
    Primrec.list_map primrec_argTrans
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp
        (Primrec.snd.comp (Primrec.snd (α := Arg)))))).to₂
  exact Primrec.list_cons.comp (Primrec.const 0)
    (Primrec.list_append.comp (Primrec.list_append.comp Primrec.snd hm1) hm2)

lemma primrec_states : Primrec fun p : Arg => p.1.states := by
  have hm1 : Primrec fun p : Arg => p.1.trans.map (fun x => x.1) :=
    Primrec.list_map primrec_argTrans (Primrec.fst.comp (Primrec.snd (α := Arg))).to₂
  have hm2 : Primrec fun p : Arg => p.1.trans.map (fun x => x.2.2.1) :=
    Primrec.list_map primrec_argTrans
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd (α := Arg))))).to₂
  exact Primrec.list_cons.comp (primrec_q0.comp Primrec.fst)
    (Primrec.list_cons.comp (primrec_qacc.comp Primrec.fst)
      (Primrec.list_append.comp hm1 hm2))

lemma primrec_alphabet : Primrec fun p : Arg => p.1.alphabet p.2 :=
  Primrec.list_append.comp
    (Primrec.list_map primrec_tapeSyms (primrec_tape.comp Primrec.snd).to₂)
    (Primrec.list_map primrec_states (primrec_state.comp Primrec.snd).to₂)

/-- An entry of a transition table. -/
abbrev Entry := ℕ × ℕ × ℕ × ℕ × Bool

lemma primrec_rightRules : Primrec fun p : Arg => p.1.rightRules := by
  have hb : Primrec fun q : Arg × Entry => q.2.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hc : PrimrecPred fun q : Arg × Entry => q.2.2.2.2.2 = true := by
    simpa [PrimrecPred] using hb
  have hq : Primrec fun q : Arg × Entry => q.2.1 := Primrec.fst.comp Primrec.snd
  have ha : Primrec fun q : Arg × Entry => q.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hr : Primrec fun q : Arg × Entry => q.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hbb : Primrec fun q : Arg × Entry => q.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have htop : Primrec fun q : Arg × Entry => [Sym.state q.2.1, Sym.tape q.2.2.1] :=
    Primrec.list_cons.comp (primrec_state.comp hq)
      (Primrec.list_cons.comp (primrec_tape.comp ha) (Primrec.const []))
  have hbot : Primrec fun q : Arg × Entry => [Sym.tape q.2.2.2.2.1, Sym.state q.2.2.2.1] :=
    Primrec.list_cons.comp (primrec_tape.comp hbb)
      (Primrec.list_cons.comp (primrec_state.comp hr) (Primrec.const []))
  exact Primrec.listFilterMap primrec_argTrans
    (Primrec.ite hc (Primrec.option_some.comp (Primrec.pair htop hbot))
      (Primrec.const none)).to₂

lemma primrec_leftRules : Primrec fun p : Arg => p.1.leftRules p.2 := by
  have hb : Primrec fun q : (Arg × ℕ) × Entry => q.2.2.2.2.2 :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have hc : PrimrecPred fun q : (Arg × ℕ) × Entry => q.2.2.2.2.2 = true := by
    simpa [PrimrecPred] using hb
  have hcc : Primrec fun q : (Arg × ℕ) × Entry => q.1.2 := Primrec.snd.comp Primrec.fst
  have hq : Primrec fun q : (Arg × ℕ) × Entry => q.2.1 := Primrec.fst.comp Primrec.snd
  have ha : Primrec fun q : (Arg × ℕ) × Entry => q.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hr : Primrec fun q : (Arg × ℕ) × Entry => q.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hbb : Primrec fun q : (Arg × ℕ) × Entry => q.2.2.2.2.1 :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
  have htop : Primrec fun q : (Arg × ℕ) × Entry =>
      [Sym.tape q.1.2, Sym.state q.2.1, Sym.tape q.2.2.1] :=
    Primrec.list_cons.comp (primrec_tape.comp hcc)
      (Primrec.list_cons.comp (primrec_state.comp hq)
        (Primrec.list_cons.comp (primrec_tape.comp ha) (Primrec.const [])))
  have hbot : Primrec fun q : (Arg × ℕ) × Entry =>
      [Sym.state q.2.2.2.1, Sym.tape q.1.2, Sym.tape q.2.2.2.2.1] :=
    Primrec.list_cons.comp (primrec_state.comp hr)
      (Primrec.list_cons.comp (primrec_tape.comp hcc)
        (Primrec.list_cons.comp (primrec_tape.comp hbb) (Primrec.const [])))
  refine Primrec.list_flatMap primrec_tapeSyms (Primrec.listFilterMap
    (primrec_argTrans.comp Primrec.fst)
    (Primrec.ite hc (Primrec.const none)
      (Primrec.option_some.comp (Primrec.pair htop hbot))).to₂).to₂

lemma primrec_transRules : Primrec fun p : Arg => p.1.transRules p.2 :=
  Primrec.list_append.comp primrec_rightRules primrec_leftRules

lemma primrec_eatRules : Primrec fun p : Arg => p.1.eatRules p.2 := by
  have hqacc : Primrec fun q : Arg × Sym => Sym.state q.1.1.qacc :=
    primrec_state.comp (primrec_qacc.comp (Primrec.fst.comp Primrec.fst))
  have hx : Primrec fun q : Arg × Sym => q.2 := Primrec.snd
  have h1 : Primrec fun q : Arg × Sym =>
      ([q.2, Sym.state q.1.1.qacc], [Sym.state q.1.1.qacc]) :=
    Primrec.pair (Primrec.list_cons.comp hx
        (Primrec.list_cons.comp hqacc (Primrec.const [])))
      (Primrec.list_cons.comp hqacc (Primrec.const []))
  have h2 : Primrec fun q : Arg × Sym =>
      ([Sym.state q.1.1.qacc, q.2], [Sym.state q.1.1.qacc]) :=
    Primrec.pair (Primrec.list_cons.comp hqacc
        (Primrec.list_cons.comp hx (Primrec.const [])))
      (Primrec.list_cons.comp hqacc (Primrec.const []))
  exact Primrec.list_flatMap primrec_alphabet
    (Primrec.list_cons.comp h1 (Primrec.list_cons.comp h2 (Primrec.const []))).to₂

lemma primrec_startCfg : Primrec fun p : Arg => p.1.startCfg p.2 :=
  Primrec.list_cons.comp (primrec_state.comp (primrec_q0.comp Primrec.fst))
    (Primrec.list_map Primrec.snd (primrec_tape.comp Primrec.snd).to₂)

lemma primrec_fullRules : Primrec fun p : Arg => (p.1.fullSRS p.2).rules :=
  Primrec.list_append.comp primrec_transRules primrec_eatRules

lemma primrec_sipserMPCP : Primrec fun p : Arg => sipserMPCP p.1 p.2 := by
  have hfirst : Primrec fun p : Arg =>
      (([Sym.start] : List Sym), Sym.start :: (p.1.startCfg p.2 ++ [Sym.hash])) :=
    Primrec.pair (Primrec.const _)
      (Primrec.list_cons.comp (Primrec.const _)
        (Primrec.list_append.comp primrec_startCfg (Primrec.const _)))
  have hcopy : Primrec fun p : Arg => (p.1.alphabet p.2).map (fun a => ([a], [a])) :=
    Primrec.list_map primrec_alphabet
      (Primrec.pair (Primrec.list_cons.comp Primrec.snd (Primrec.const []))
        (Primrec.list_cons.comp Primrec.snd (Primrec.const []))).to₂
  have hext : Primrec fun p : Arg =>
      (p.1.fullSRS p.2).ext.map (fun x => ([Sym.hash], [x, Sym.hash])) :=
    (Primrec.const [(([Sym.hash] : List Sym), [Sym.tape 0, Sym.hash])]).of_eq fun _ => rfl
  have hfinal : Primrec fun p : Arg =>
      [(([Sym.state p.1.qacc] ++ [Sym.hash, Sym.hash] : List Sym), ([Sym.hash] : List Sym))] :=
    Primrec.list_cons.comp
      (Primrec.pair
        (Primrec.list_cons.comp (primrec_state.comp (primrec_qacc.comp Primrec.fst))
          (Primrec.const _))
        (Primrec.const _))
      (Primrec.const [])
  exact Primrec.list_cons.comp hfirst
    (Primrec.list_append.comp
      (Primrec.list_append.comp
        (Primrec.list_append.comp
          (Primrec.list_append.comp primrec_fullRules hcopy) (Primrec.const _)) hext)
      hfinal)

/-! ## The `⋆` trick is primitive recursive -/

variable {α : Type*}

lemma starTop_eq_flatMap (star : α) (u : List α) :
    starTop star u = u.flatMap (fun a => [star, a]) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp [starTop, ih]

lemma starBot_eq_flatMap (star : α) (u : List α) :
    starBot star u = u.flatMap (fun a => [a, star]) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp [starBot, ih]

lemma primrec_starTop {γ : Type} [Primcodable γ] {f : γ → List Sym} (hf : Primrec f) :
    Primrec fun a => starTop Sym.star (f a) :=
  (Primrec.list_flatMap hf
    (Primrec.list_cons.comp (Primrec.const Sym.star)
      (Primrec.list_cons.comp Primrec.snd (Primrec.const []))).to₂).of_eq fun a => by
    simp [starTop_eq_flatMap]

lemma primrec_starBot {γ : Type} [Primcodable γ] {f : γ → List Sym} (hf : Primrec f) :
    Primrec fun a => starBot Sym.star (f a) :=
  (Primrec.list_flatMap hf
    (Primrec.list_cons.comp Primrec.snd
      (Primrec.list_cons.comp (Primrec.const Sym.star) (Primrec.const []))).to₂).of_eq fun a => by
    simp [starBot_eq_flatMap]

/-- Sipser's `⋆` trick applied to the MPCP instance, written out explicitly. -/
lemma sipserPCP_eq (M : TM) (w : List ℕ) :
    sipserPCP M w =
      (starTop Sym.star [Sym.start],
          Sym.star :: starBot Sym.star (Sym.start :: (M.startCfg w ++ [Sym.hash])))
        :: ((sipserMPCP M w).map fun e => (starTop Sym.star e.1, starBot Sym.star e.2))
          ++ [([Sym.star, Sym.diamond], [Sym.diamond])] := rfl

/-- **The reduction is effective**: the map sending a machine and an input word to the
associated PCP instance is primitive recursive. -/
theorem primrec_sipserPCP : Primrec fun p : Arg => sipserPCP p.1 p.2 := by
  have hhead : Primrec fun p : Arg =>
      ((starTop Sym.star [Sym.start] : List Sym),
        Sym.star :: starBot Sym.star (Sym.start :: (p.1.startCfg p.2 ++ [Sym.hash]))) :=
    Primrec.pair (Primrec.const _)
      (Primrec.list_cons.comp (Primrec.const _)
        (primrec_starBot (Primrec.list_cons.comp (Primrec.const _)
          (Primrec.list_append.comp primrec_startCfg (Primrec.const _)))))
  have hmap : Primrec fun p : Arg =>
      (sipserMPCP p.1 p.2).map fun e => (starTop Sym.star e.1, starBot Sym.star e.2) :=
    Primrec.list_map primrec_sipserMPCP
      (Primrec.pair (primrec_starTop (Primrec.fst.comp Primrec.snd))
        (primrec_starBot (Primrec.snd.comp Primrec.snd))).to₂
  exact (Primrec.list_cons.comp hhead
    (Primrec.list_append.comp hmap (Primrec.const _))).of_eq fun p => (sipserPCP_eq p.1 p.2).symm

/-- The reduction is computable. -/
theorem computable_sipserPCP : Computable fun p : Arg => sipserPCP p.1 p.2 :=
  primrec_sipserPCP.to_comp

end Lax251941Proofs.PCP
