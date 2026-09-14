/-
Part D: for-transducers -- the correctness of the translation, and the composition.

This file proves that the translation `Transducers.tr` of the outer for-transducer is correct, and
assembles from it the proof of Lemma `lem:for-closed-under-composition`.
-/
import Lax194892Proofs.Source.PartD.ForCompDef
import Lax194892Proofs.Source.PartD.ForFree

namespace Lax194892Proofs.Transducers

open scoped Classical

variable {A B C : Type}

/-! ## The output of the inner nest and its events -/

lemma getD_getElem? {α : Type} (l : List α) (dflt : α) (q : ℕ) (h : q < l.length) :
    l[q]?.getD dflt = l[q] := by
  rw [List.getElem?_eq_getElem h]
  rfl

lemma getElem_congr_idx {α : Type} (l : List α) {i j : ℕ} (hi : i < l.length)
    (hj : j < l.length) (h : i = j) : l[i] = l[j] := by
  subst h; rfl

lemma exec_seq_out (w : List A) (P Q : ForProg A B) (pos : ℕ → ℕ) (bv : ℕ → Bool) :
    (ForProg.exec w (ForProg.seq P Q) pos bv).2
      = (ForProg.exec w P pos bv).2 ++ (ForProg.exec w Q pos (ForProg.exec w P pos bv).1).2 := rfl

lemma exec_seq_bv (w : List A) (P Q : ForProg A B) (pos : ℕ → ℕ) (bv : ℕ → Bool) :
    (ForProg.exec w (ForProg.seq P Q) pos bv).1
      = (ForProg.exec w Q pos (ForProg.exec w P pos bv).1).1 := rfl


/-- The output of the inner nest of loops on the input `w`. -/
noncomputable def innerOut (w : List A) (L : List (Bool × ℕ)) (p : ForProg A B) : List B :=
  (ForProg.exec w (ForProg.nestLoops L p) (fun _ => 0) (fun _ => false)).2

/-- The tuples at which the inner nest of loops produces a letter. -/
noncomputable def innerEvents (w : List A) (L : List (Bool × ℕ)) (p : ForProg A B) :
    List (List ℕ) := events w L p (fun _ => 0) (fun _ => false)

/-- What the inner nest of loops produces at a tuple. -/
noncomputable def innerAt (w : List A) (L : List (Bool × ℕ)) (p : ForProg A B) (z : List ℕ) :
    List B := outAt w L p (fun _ => 0) (fun _ => false) z

lemma innerOut_def (w : List A) (L : List (Bool × ℕ)) (p : ForProg A B) :
    innerOut w L p = (ForProg.exec w (ForProg.nestLoops L p) (fun _ => 0) (fun _ => false)).2 :=
  rfl

lemma innerEvents_def (w : List A) (L : List (Bool × ℕ)) (p : ForProg A B) :
    innerEvents w L p = events w L p (fun _ => 0) (fun _ => false) := rfl

lemma innerAt_def (w : List A) (L : List (Bool × ℕ)) (p : ForProg A B) (z : List ℕ) :
    innerAt w L p z = outAt w L p (fun _ => 0) (fun _ => false) z := rfl

/-- The data of the inner nest of loops, of the scratch flags and of the base of the block of
variables used by the translation. -/
structure CompOk (L : List (Bool × ℕ)) (p : ForProg A B) (base flQ flS : ℕ) : Prop where
  /-- The body of the inner nest is loop-free. -/
  loopFree : p.LoopFree
  /-- The body of the inner nest produces at most one letter per iteration. -/
  out1 : p.OutputsAtMostOne
  /-- The loop variables of the inner nest are pairwise distinct. -/
  nodup : (L.map Prod.snd).Nodup
  /-- The loop variables of the inner nest are below the scratch flags. -/
  xlt : ∀ x ∈ L.map Prod.snd, x < flQ
  /-- The position variables of the body are below the scratch flags. -/
  poslt : ∀ i ∈ p.posVars, i < flQ
  /-- The Boolean variables of the body are below the scratch flags. -/
  boollt : ∀ i ∈ p.boolVars, i < flQ
  /-- The two scratch flags are distinct. -/
  flQS : flQ < flS
  /-- The variables of the translated program are above the scratch flags. -/
  flSbase : flS < base

namespace CompOk

variable {L : List (Bool × ℕ)} {p : ForProg A B} {base flQ flS : ℕ}

lemma flQ_not_mem (hok : CompOk L p base flQ flS) : flQ ∉ p.boolVars :=
  fun h => absurd (hok.boollt _ h) (lt_irrefl _)

lemma flS_not_mem (hok : CompOk L p base flQ flS) : flS ∉ p.boolVars :=
  fun h => by have := hok.boollt _ h; have := hok.flQS; omega

lemma xbase (hok : CompOk L p base flQ flS) : ∀ x ∈ L.map Prod.snd, x < base :=
  fun x hx => by have := hok.xlt x hx; have := hok.flQS; have := hok.flSbase; omega

lemma posbase (hok : CompOk L p base flQ flS) : ∀ i ∈ p.posVars, i < base :=
  fun x hx => by have := hok.poslt x hx; have := hok.flQS; have := hok.flSbase; omega

end CompOk

/-! ## The correctness of the translation -/

section

variable (w : List A) (L : List (Bool × ℕ)) (p : ForProg A B) (base flQ flS : ℕ)

/-- The re-simulation answers the question asked at a tuple held in a block of position
variables. -/
lemma resim_block_spec (hok : CompOk L p base flQ flS) (lvl : ℕ) (q : B → Bool)
    (posR : ℕ → ℕ) (bvR : ℕ → Bool) (hpos0 : ∀ i, i < base → posR i = 0) :
    (ForProg.exec w (resim (C := C) L p (blk L base lvl) flQ flS q) posR bvR).2 = [] ∧
      (∀ i, i ≠ flQ → i ≠ flS → i ∉ p.boolVars →
        (ForProg.exec w (resim (C := C) L p (blk L base lvl) flQ flS q) posR bvR).1 i = bvR i) ∧
      (ForProg.exec w (resim (C := C) L p (blk L base lvl) flQ flS q) posR bvR).1 flQ
        = lastFlag false q (innerAt w L p ((blk L base lvl).map posR)) := by
  refine resim_spec w L p _ flQ flS q hok.loopFree hok.nodup (by simp) hok.flQ_not_mem
    hok.flS_not_mem (by have := hok.flQS; omega) (fun y hy hc => ?_) posR bvR (fun i hi hi' => ?_)
  · have h1 := le_of_mem_blk hy
    have h2 := hok.xbase y hc
    omega
  · exact hpos0 i (by have := hok.posbase i hi'; omega)


lemma innerEvents_sorted : (innerEvents w L p).Pairwise (LexLt (L.map Prod.fst)) :=
  events_sorted w L p _ _

lemma innerEvents_length (hout1 : p.OutputsAtMostOne) :
    (innerEvents w L p).length = (innerOut w L p).length :=
  events_length w L p hout1

lemma innerAt_getElem (hout1 : p.OutputsAtMostOne) (q : ℕ)
    (hq : q < (innerEvents w L p).length) :
    ∃ c, innerAt w L p (innerEvents w L p)[q] = [c] ∧ (innerOut w L p)[q]? = some c := by
  have hq' : q < (innerOut w L p).length := by rw [← innerEvents_length w L p hout1]; exact hq
  refine ⟨(innerOut w L p)[q], events_outAt_getElem w L p hout1 q hq, ?_⟩
  exact List.getElem?_eq_getElem hq'


lemma lastFlag_const : ∀ (l : List B) (init : Bool),
    lastFlag init (fun _ => true) l = if l = [] then init else true := by
  intro l
  induction l with
  | nil => intro init; rfl
  | cons c l ih =>
      intro init
      show lastFlag true (fun _ => true) l = _
      rw [ih true]
      cases l <;> simp

lemma map_getD_range {α : Type} (l : List α) (dflt : α) :
    (List.range l.length).map (fun q => l[q]?.getD dflt) = l := by
  refine List.ext_getElem (by simp) (fun q h1 h2 => ?_)
  rw [List.getElem_map, List.getElem_range, List.getElem?_eq_getElem h2]
  rfl

/-- **The translation of the outer for-transducer is correct.** -/
theorem tr_spec (hok : CompOk L p base flQ flS) :
    ∀ (S : ForProg B C) (env : ℕ → ℕ) (lvl : ℕ), S.AllAtomic →
      ∀ (posQ : ℕ → ℕ) (bvQ : ℕ → Bool) (posR : ℕ → ℕ) (bvR : ℕ → Bool),
        (∀ y ∈ S.freePos, env y < lvl) →
        (∀ i, i < base → posR i = 0) →
        (∀ y ∈ S.freePos, posQ y < (innerEvents w L p).length ∧
          (blk L base (env y)).map posR = (innerEvents w L p)[posQ y]?.getD []) →
        (∀ i, bvR (qbv base i) = bvQ i) →
        (ForProg.exec w (tr L p base flQ flS env lvl S) posR bvR).2
            = (ForProg.exec (innerOut w L p) S posQ bvQ).2 ∧
          (∀ i, (ForProg.exec w (tr L p base flQ flS env lvl S) posR bvR).1 (qbv base i)
            = (ForProg.exec (innerOut w L p) S posQ bvQ).1 i) ∧
          (∀ i, i ∉ p.boolVars → i ≠ flQ → i ≠ flS → (∀ j, i ≠ qbv base j) →
            (ForProg.exec w (tr L p base flQ flS env lvl S) posR bvR).1 i = bvR i) := by
  intro S
  induction S with
  | skip =>
      intro env lvl _ posQ bvQ posR bvR _ _ _ hbv
      exact ⟨rfl, fun i => hbv i, fun i _ _ _ _ => rfl⟩
  | output c =>
      intro env lvl _ posQ bvQ posR bvR _ _ _ hbv
      exact ⟨rfl, fun i => hbv i, fun i _ _ _ _ => rfl⟩
  | assign i b =>
      intro env lvl _ posQ bvQ posR bvR _ _ _ hbv
      refine ⟨rfl, fun j => ?_, fun j _ _ _ hj => ?_⟩
      · show Function.update bvR (qbv base i) b (qbv base j) = Function.update bvQ i b j
        by_cases hij : j = i
        · subst hij; simp
        · rw [Function.update_of_ne hij, Function.update_of_ne (by
            intro hc; exact hij (by rw [qbv, qbv] at hc; omega)), hbv]
      · show Function.update bvR (qbv base i) b j = bvR j
        exact Function.update_of_ne (hj i) _ _
  | seq S T ihS ihT =>
      intro env lvl hatom posQ bvQ posR bvR henv hpos0 hEv hbv
      obtain ⟨o1, b1, k1⟩ := ihS env lvl hatom.1 posQ bvQ posR bvR
        (fun y hy => henv y (by simp [hy]))
        hpos0 (fun y hy => hEv y (by simp [hy])) hbv
      obtain ⟨o2, b2, k2⟩ := ihT env lvl hatom.2 posQ
        (ForProg.exec (innerOut w L p) S posQ bvQ).1 posR
        (ForProg.exec w (tr L p base flQ flS env lvl S) posR bvR).1
        (fun y hy => henv y (by simp [hy]))
        hpos0 (fun y hy => hEv y (by simp [hy])) b1
      refine ⟨?_, ?_, ?_⟩
      · show (ForProg.exec w (ForProg.seq (tr L p base flQ flS env lvl S)
            (tr L p base flQ flS env lvl T)) posR bvR).2 = _
        rw [exec_seq, exec_seq, o1, o2]
      · intro i
        show (ForProg.exec w (ForProg.seq (tr L p base flQ flS env lvl S)
            (tr L p base flQ flS env lvl T)) posR bvR).1 (qbv base i) = _
        rw [exec_seq, exec_seq]
        exact b2 i
      · intro i h1 h2 h3 h4
        show (ForProg.exec w (ForProg.seq (tr L p base flQ flS env lvl S)
            (tr L p base flQ flS env lvl T)) posR bvR).1 i = _
        rw [exec_seq]
        exact (k2 i h1 h2 h3 h4).trans (k1 i h1 h2 h3 h4)
  | ite t S T ihS ihT =>
      intro env lvl hatom posQ bvQ posR bvR henv hpos0 hEv hbv
      have hSsub : ∀ y ∈ S.freePos, y ∈ (ForProg.ite t S T).freePos := by
        intro y hy; simp [hy]
      have hTsub : ∀ y ∈ T.freePos, y ∈ (ForProg.ite t S T).freePos := by
        intro y hy; simp [hy]
      have key : ∀ (pre : ForProg A C) (tt : ForTest A),
          (ForProg.exec w pre posR bvR).2 = [] →
          (∀ i, (ForProg.exec w pre posR bvR).1 (qbv base i) = bvQ i) →
          (∀ i, i ∉ p.boolVars → i ≠ flQ → i ≠ flS → (∀ j, i ≠ qbv base j) →
            (ForProg.exec w pre posR bvR).1 i = bvR i) →
          (ForTest.Holds w posR (ForProg.exec w pre posR bvR).1 tt
            ↔ ForTest.Holds (innerOut w L p) posQ bvQ t) →
          ((ForProg.exec w (ForProg.seq pre (ForProg.ite tt
              (tr L p base flQ flS env lvl S) (tr L p base flQ flS env lvl T))) posR bvR).2
                = (ForProg.exec (innerOut w L p) (ForProg.ite t S T) posQ bvQ).2 ∧
            (∀ i, (ForProg.exec w (ForProg.seq pre (ForProg.ite tt
                (tr L p base flQ flS env lvl S) (tr L p base flQ flS env lvl T))) posR bvR).1
                  (qbv base i)
                = (ForProg.exec (innerOut w L p) (ForProg.ite t S T) posQ bvQ).1 i) ∧
            (∀ i, i ∉ p.boolVars → i ≠ flQ → i ≠ flS → (∀ j, i ≠ qbv base j) →
              (ForProg.exec w (ForProg.seq pre (ForProg.ite tt
                (tr L p base flQ flS env lvl S) (tr L p base flQ flS env lvl T))) posR bvR).1 i
                  = bvR i)) := by
        intro pre tt h1 h2 h3 h4
        by_cases hT : ForTest.Holds (innerOut w L p) posQ bvQ t
        · obtain ⟨o, b, k⟩ := ihS env lvl hatom.2.1 posQ bvQ posR
            (ForProg.exec w pre posR bvR).1 (fun y hy => henv y (hSsub y hy)) hpos0
            (fun y hy => hEv y (hSsub y hy)) h2
          refine ⟨?_, fun i => ?_, fun i c1 c2 c3 c4 => ?_⟩
          · rw [exec_seq_out, h1, List.nil_append, exec_ite_pos _ _ _ _ _ _ (h4.mpr hT),
              exec_ite_pos _ _ _ _ _ _ hT, o]
          · rw [exec_seq_bv, exec_ite_pos _ _ _ _ _ _ (h4.mpr hT), exec_ite_pos _ _ _ _ _ _ hT]
            exact b i
          · rw [exec_seq_bv, exec_ite_pos _ _ _ _ _ _ (h4.mpr hT)]
            exact (k i c1 c2 c3 c4).trans (h3 i c1 c2 c3 c4)
        · obtain ⟨o, b, k⟩ := ihT env lvl hatom.2.2 posQ bvQ posR
            (ForProg.exec w pre posR bvR).1 (fun y hy => henv y (hTsub y hy)) hpos0
            (fun y hy => hEv y (hTsub y hy)) h2
          have hT' : ¬ ForTest.Holds w posR (ForProg.exec w pre posR bvR).1 tt :=
            fun hc => hT (h4.mp hc)
          refine ⟨?_, fun i => ?_, fun i c1 c2 c3 c4 => ?_⟩
          · rw [exec_seq_out, h1, List.nil_append, exec_ite_neg _ _ _ _ _ _ hT',
              exec_ite_neg _ _ _ _ _ _ hT, o]
          · rw [exec_seq_bv, exec_ite_neg _ _ _ _ _ _ hT', exec_ite_neg _ _ _ _ _ _ hT]
            exact b i
          · rw [exec_seq_bv, exec_ite_neg _ _ _ _ _ _ hT']
            exact (k i c1 c2 c3 c4).trans (h3 i c1 c2 c3 c4)
      cases t with
      | boolVar i =>
          exact key ForProg.skip (ForTest.boolVar (qbv base i)) rfl hbv (fun _ _ _ _ _ => rfl)
            (by show bvR (qbv base i) = true ↔ bvQ i = true; rw [hbv])
      | eqPos y y' =>
          obtain ⟨hy1, hy2⟩ := hEv y (by simp [ForTest.posVars])
          obtain ⟨hz1, hz2⟩ := hEv y' (by simp [ForTest.posVars])
          refine key ForProg.skip (eqTupleTest (blk L base (env y)) (blk L base (env y'))) rfl hbv
            (fun _ _ _ _ _ => rfl) ?_
          rw [holds_eqTupleTest w posR _ _ _ (by simp), hy2, hz2,
            getD_getElem? _ _ _ hy1, getD_getElem? _ _ _ hz1]
          show _ ↔ posQ y = posQ y'
          constructor
          · intro h
            exact lexLt_getElem_inj (L.map Prod.fst) (innerEvents w L p)
              (innerEvents_sorted w L p) _ _ hy1 hz1 h
          · intro h; exact getElem_congr_idx _ hy1 hz1 h
      | lePos y y' =>
          obtain ⟨hy1, hy2⟩ := hEv y (by simp [ForTest.posVars])
          obtain ⟨hz1, hz2⟩ := hEv y' (by simp [ForTest.posVars])
          refine key ForProg.skip (ForTest.not (lexLtTest (L.map Prod.fst)
            (blk L base (env y')) (blk L base (env y)))) rfl hbv (fun _ _ _ _ _ => rfl) ?_
          show (¬ ForTest.Holds w posR bvR (lexLtTest (L.map Prod.fst) _ _)) ↔ posQ y ≤ posQ y'
          rw [holds_lexLtTest, hy2, hz2, getD_getElem? _ _ _ hy1, getD_getElem? _ _ _ hz1]
          exact (lexLt_getElem_le_iff (L.map Prod.fst) (innerEvents w L p)
            (innerEvents_sorted w L p) _ _ hy1 hz1).symm
      | label y b =>
          obtain ⟨hy1, hy2⟩ := hEv y (by simp [ForTest.posVars])
          obtain ⟨hr1, hr2, hr3⟩ := resim_block_spec (C := C) w L p base flQ flS hok (env y)
            (fun c => decide (c = b)) posR bvR hpos0
          obtain ⟨c, hc1, hc2⟩ := innerAt_getElem w L p hok.out1 (posQ y) hy1
          refine key (resim L p (blk L base (env y)) flQ flS (fun c => decide (c = b)))
            (ForTest.boolVar flQ) hr1 (fun i => ?_) (fun i c1 c2 c3 _ => hr2 i c2 c3 c1) ?_
          · rw [hr2 (qbv base i) (by have := hok.flSbase; have := hok.flQS
                                     have := le_qbv base i; omega)
              (by have := hok.flSbase; have := le_qbv base i; omega)
              (fun hcc => by have := hok.boollt _ hcc
                             have := hok.flQS; have := hok.flSbase
                             have := le_qbv base i; omega)]
            exact hbv i
          · show _ = true ↔ ForTest.Holds (innerOut w L p) posQ bvQ (ForTest.label y b)
            rw [hr3, hy2, getD_getElem? _ _ _ hy1, hc1]
            show (decide (c = b) = true) ↔ (innerOut w L p)[posQ y]? = some b
            rw [hc2]
            simp
      | not t => exact absurd hatom.1 (by exact fun h => h)
      | and t s => exact absurd hatom.1 (by exact fun h => h)
      | or t s => exact absurd hatom.1 (by exact fun h => h)
  | loop d y S ih =>
      intro env lvl hatom posQ bvQ posR bvR henv hpos0 hEv hbv
      have hSsub : ∀ y' ∈ S.freePos, y' ≠ y → y' ∈ (ForProg.loop d y S).freePos :=
        fun y' hy' hne => ForProg.mem_freePos_loop hy' hne
      have hqne1 : ∀ i, qbv base i ≠ flQ := fun i hc => by
        have := le_qbv base i; have := hok.flQS; have := hok.flSbase; omega
      have hqne2 : ∀ i, qbv base i ≠ flS := fun i hc => by
        have := le_qbv base i; have := hok.flSbase; omega
      have hqne3 : ∀ i, qbv base i ∉ p.boolVars := fun i hc => by
        have := hok.boollt _ hc; have := le_qbv base i
        have := hok.flQS; have := hok.flSbase; omega
      set X : ForProg A C := tr L p base flQ flS (Function.update env y lvl) (lvl + 1) S with hX
      set LN : List (Bool × ℕ) := loopNest L base lvl d with hLN
      set body : ForProg A C := ForProg.seq (resim L p (blk L base lvl) flQ flS (fun _ => true))
        (ForProg.ite (ForTest.boolVar flQ) X ForProg.skip) with hbody
      have hunfold : tr L p base flQ flS env lvl (ForProg.loop d y S)
          = ForProg.nestLoops LN body := rfl
      have hQunfold : ForProg.exec (innerOut w L p) (ForProg.loop d y S) posQ bvQ
          = runList (fun s q => ForProg.exec (innerOut w L p) S (Function.update posQ y q) s)
              (loopRange d (innerOut w L p).length) bvQ := by
        show forLoopRun (fun s q => ForProg.exec (innerOut w L p) S
          (Function.update posQ y q) s) _ bvQ = _
        rw [forLoopRun_eq_runList]
        rfl
      have key : ∀ (T : List (List ℕ)) (qs : List ℕ),
          (∀ t ∈ T, t ∈ tuplesOf L w.length) →
          (∀ q ∈ qs, q < (innerEvents w L p).length) →
          T.filter (fun t => decide (innerAt w L p t ≠ []))
            = qs.map (fun q => (innerEvents w L p)[q]?.getD []) →
          ∀ (sR : ℕ → Bool) (sQ : ℕ → Bool), (∀ i, sR (qbv base i) = sQ i) →
            (runList (fun s t => ForProg.exec w body (setTuple LN t posR) s) T sR).2
                = (runList (fun s q => ForProg.exec (innerOut w L p) S
                    (Function.update posQ y q) s) qs sQ).2 ∧
              (∀ i, (runList (fun s t => ForProg.exec w body (setTuple LN t posR) s) T sR).1
                  (qbv base i)
                = (runList (fun s q => ForProg.exec (innerOut w L p) S
                    (Function.update posQ y q) s) qs sQ).1 i) ∧
              (∀ i, i ∉ p.boolVars → i ≠ flQ → i ≠ flS → (∀ j, i ≠ qbv base j) →
                (runList (fun s t => ForProg.exec w body (setTuple LN t posR) s) T sR).1 i
                  = sR i) := by
        intro T
        induction T with
        | nil =>
            intro qs _ _ hm sR sQ hrel
            have hqs : qs = [] := by
              cases qs with
              | nil => rfl
              | cons q qs => simp at hm
            subst hqs
            exact ⟨rfl, fun i => hrel i, fun i _ _ _ _ => rfl⟩
        | cons t T' ihT =>
            intro qs hT hq hm sR sQ hrel
            have htmem : t ∈ tuplesOf L w.length := hT t (by simp)
            have hposR' : ∀ i, i < base → setTuple LN t posR i = 0 := by
              intro i hi
              rw [setTuple_of_not_mem LN t posR
                (by rw [map_snd_loopNest]; exact not_mem_blk_of_lt hi)]
              exact hpos0 i hi
            have hblkt : (blk L base lvl).map (setTuple LN t posR) = t := by
              have h1 := map_setTuple LN t (by rw [map_snd_loopNest]; exact blk_nodup L base lvl)
                (by rw [length_loopNest]; exact length_of_mem_tuplesOf L w.length htmem) posR
              rwa [map_snd_loopNest] at h1
            obtain ⟨hr1, hr2, hr3⟩ := resim_block_spec (C := C) w L p base flQ flS hok lvl
              (fun _ => true) (setTuple LN t posR) sR hposR'
            rw [hblkt] at hr3
            set s₁ : ℕ → Bool := (ForProg.exec w (resim L p (blk L base lvl) flQ flS
              (fun _ => true) : ForProg A C) (setTuple LN t posR) sR).1 with hs₁
            have hs₁qbv : ∀ i, s₁ (qbv base i) = sQ i := by
              intro i
              rw [hr2 (qbv base i) (hqne1 i) (hqne2 i) (hqne3 i)]
              exact hrel i
            have hflQval : s₁ flQ = decide (innerAt w L p t ≠ []) := by
              rw [hr3, lastFlag_const]
              by_cases h : innerAt w L p t = [] <;> simp [h]
            by_cases hev : innerAt w L p t = []
            · -- the tuple is not an event
              have hnh : ¬ ForTest.Holds w (setTuple LN t posR) s₁ (ForTest.boolVar flQ) := by
                show ¬ (s₁ flQ = true)
                rw [hflQval]; simp [hev]
              have hstep1 : (ForProg.exec w body (setTuple LN t posR) sR).1 = s₁ := by
                rw [hbody, exec_seq_bv, exec_ite_neg _ _ _ _ _ _ hnh]
                rfl
              have hstep2 : (ForProg.exec w body (setTuple LN t posR) sR).2 = [] := by
                rw [hbody, exec_seq_out, exec_ite_neg _ _ _ _ _ _ hnh, hr1]
                rfl
              have hm' : T'.filter (fun t => decide (innerAt w L p t ≠ []))
                  = qs.map (fun q => (innerEvents w L p)[q]?.getD []) := by
                rw [← hm, List.filter_cons_of_neg (by simp [hev])]
              obtain ⟨o, b, k⟩ := ihT qs (fun z hz => hT z (by simp [hz])) hq hm' s₁ sQ hs₁qbv
              refine ⟨?_, fun i => ?_, fun i c1 c2 c3 c4 => ?_⟩
              · rw [runList_cons, hstep1, hstep2, List.nil_append, o]
              · rw [runList_cons, hstep1]
                exact b i
              · rw [runList_cons, hstep1]
                rw [k i c1 c2 c3 c4]
                exact hr2 i c2 c3 c1
            · -- the tuple is an event
              have hh : ForTest.Holds w (setTuple LN t posR) s₁ (ForTest.boolVar flQ) := by
                show s₁ flQ = true
                rw [hflQval]; simp [hev]
              have hstep1 : (ForProg.exec w body (setTuple LN t posR) sR).1
                  = (ForProg.exec w X (setTuple LN t posR) s₁).1 := by
                rw [hbody, exec_seq_bv, exec_ite_pos _ _ _ _ _ _ hh]
              have hstep2 : (ForProg.exec w body (setTuple LN t posR) sR).2
                  = (ForProg.exec w X (setTuple LN t posR) s₁).2 := by
                rw [hbody, exec_seq_out, exec_ite_pos _ _ _ _ _ _ hh, hr1, List.nil_append]
              rw [List.filter_cons_of_pos (by simp [hev])] at hm
              cases qs with
              | nil => simp at hm
              | cons q qs' =>
                  rw [List.map_cons, List.cons.injEq] at hm
                  have hqlt : q < (innerEvents w L p).length := hq q (by simp)
                  have hgq : (innerEvents w L p)[q] = t := by
                    rw [← getD_getElem? _ ([] : List ℕ) _ hqlt]
                    exact hm.1.symm
                  have henv' : ∀ y' ∈ S.freePos, (Function.update env y lvl) y' < lvl + 1 := by
                    intro y' hy'
                    by_cases hyy : y' = y
                    · subst hyy; rw [Function.update_self]; omega
                    · rw [Function.update_of_ne hyy]
                      have := henv y' (hSsub y' hy' hyy); omega
                  have hEv' : ∀ y' ∈ S.freePos,
                      (Function.update posQ y q) y' < (innerEvents w L p).length ∧
                      (blk L base ((Function.update env y lvl) y')).map (setTuple LN t posR)
                        = (innerEvents w L p)[(Function.update posQ y q) y']?.getD [] := by
                    intro y' hy'
                    by_cases hyy : y' = y
                    · subst hyy
                      rw [Function.update_self, Function.update_self]
                      exact ⟨hqlt, by rw [hblkt, ← hm.1]⟩
                    · rw [Function.update_of_ne hyy, Function.update_of_ne hyy]
                      obtain ⟨c1, c2⟩ := hEv y' (hSsub y' hy' hyy)
                      refine ⟨c1, ?_⟩
                      rw [← c2]
                      refine List.map_congr_left (fun z hz => ?_)
                      refine setTuple_of_not_mem LN t posR ?_
                      rw [map_snd_loopNest]
                      exact blk_disjoint (by have := henv y' (hSsub y' hy' hyy); omega) hz
                  obtain ⟨o, b, k⟩ := ih (Function.update env y lvl) (lvl + 1) hatom
                    (Function.update posQ y q) sQ (setTuple LN t posR) s₁ henv' hposR' hEv'
                    hs₁qbv
                  obtain ⟨o', b', k'⟩ := ihT qs' (fun z hz => hT z (by simp [hz]))
                    (fun z hz => hq z (by simp [hz])) hm.2
                    (ForProg.exec w X (setTuple LN t posR) s₁).1
                    (ForProg.exec (innerOut w L p) S (Function.update posQ y q) sQ).1 b
                  refine ⟨?_, fun i => ?_, fun i c1 c2 c3 c4 => ?_⟩
                  · rw [runList_cons, runList_cons, hstep1, hstep2, o, o']
                  · rw [runList_cons, runList_cons, hstep1]
                    exact b' i
                  · rw [runList_cons, hstep1, k' i c1 c2 c3 c4, k i c1 c2 c3 c4]
                    exact hr2 i c2 c3 c1
      rw [hunfold, exec_nestLoops, hQunfold, hLN, tuplesOf_loopNest]
      have hlen : (innerOut w L p).length = (innerEvents w L p).length :=
        (innerEvents_length w L p hok.out1).symm
      cases d
      · rw [if_neg (by simp), show loopRange false (innerOut w L p).length
          = (List.range (innerOut w L p).length).reverse from rfl]
        refine key _ _ (fun z hz => by simpa using hz)
          (fun z hz => by rw [← hlen]; simpa using List.mem_range.mp (by simpa using hz)) ?_
          bvR bvQ hbv
        rw [List.filter_reverse, List.map_reverse, hlen, map_getD_range]
        rfl
      · rw [if_pos rfl, show loopRange true (innerOut w L p).length
          = List.range (innerOut w L p).length from rfl]
        refine key _ _ (fun z hz => hz)
          (fun z hz => by rw [← hlen]; exact List.mem_range.mp hz) ?_ bvR bvQ hbv
        rw [hlen, map_getD_range]
        rfl

end

end Lax194892Proofs.Transducers
