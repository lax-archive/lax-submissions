import Lax185574Proofs.Conversions.Ram.ConsSpec
import Lax185574Proofs.Conversions.Ram.ReadPartition
import Lax185574Proofs.Conversions.Ram.MergeProgram

/-!
One stage of the program of cl:from-merge-to-construction.

At the start of stage `j` the array `cur` holds the labels of `𝒫_j`,
`res` the pairs resolved before the stage, and the input tape the words
of the stages from `j + 1` on. The stage reads `𝒫_{j+1}` and `R_{j+1}`
(or uses `{V}` and all pairs after the last stage), computes the flags of
the pairs of parts, emits the resolves and the merges into the buffer,
updates `res`, and moves the labels of `𝒫_{j+1}` into `cur`.
-/

namespace Lax185574Proofs.Conversions.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574.WordEncoding Lax185574.SequenceEncoding
open Lax185574Proofs.Conversions.MergeConstruction

/-- Read the next partition and relation, or use `{V}` and all pairs. -/
def loadNext : Com :=
  .ite (.lt (.add (.var "j") (.lit 1)) (.var "m"))
    (.seq (readPartition "nxt") (.seq (.read "c") (.seq (matFill "rel" (.lit 0))
      (readRows "rel" "c"))))
    (.seq (rowFill "nxt" (.var "b") (.lit 0)) (matFill "rel" (.sub (.lit 1) (eqE "a" "b"))))

variable {n : ℕ} (G : SimpleGraph (Fin n)) (ms : List (Setoid (Fin n) × SimpleGraph (Fin n)))

/-- The steps of the stages before `j`, encoded. -/
noncomputable def codesBefore (j : ℕ) : List ℕ :=
  ((List.range j).flatMap (stageSteps G ms)).flatMap stepCode

/-- The state between stages. -/
structure ConsBase (cap : ℕ) (j : ℕ) (τ : Env) : Prop where
  hn : τ.vars "n" = n
  hm : τ.vars "m" = ms.length
  hadj : Mat τ "adj" n fun x y => ind (gA G x y)
  hres : Mat τ "res" n fun x y => ind (gA (resolvedAt ms j) x y)
  hcur : Vec τ "cur" n (labJ ms j)
  hbuf : BufAt cap (codesBefore G ms j) τ
  hnxt : (τ.arrs "nxt").length = n
  hrel : (τ.arrs "rel").length = n * n
  hbad : (τ.arrs "bad").length = n * n
  hunr : (τ.arrs "unr").length = n * n
  hpos : (τ.arrs "pos").length = n * n
  hinp : τ.inp = ((ms.drop (j + 1)).map fun p => toWord p.1 ++ toWord p.2).flatten

theorem mat_zero_eq {τ : Env} {a : String} (h : Mat τ a n fun _ _ => 0) :
    τ.arrs a = List.replicate (n * n) 0 := by
  refine List.ext_getElem (by rw [h.len]; simp) fun k h1 h2 => ?_
  rw [List.getElem_replicate]
  have hk : k < n * n := by rw [h.len] at h1; exact h1
  have hn : 0 < n := by rcases Nat.eq_zero_or_pos n with h0 | h0 <;> [simp [h0] at hk; exact h0]
  have := h.get (k / n) (by rw [Nat.div_lt_iff_lt_mul hn]; exact hk) (k % n) (Nat.mod_lt _ hn)
  rw [Nat.div_add_mod' k n] at this
  rw [List.getElem?_eq_getElem h1] at this
  exact Option.some.inj this

theorem labJ_last {v : ℕ} (hv : v < n) :
    labJ ms ms.length v = 0 := by
  have hpart : part ms ms.length = ⊤ := by simp [part]
  simp only [labJ, hpart, repN, dif_pos hv]
  have := rep_le (⊤ : Setoid (Fin n)) (u := ⟨0, by omega⟩) (x := ⟨v, hv⟩) trivial
  have h0 : ((rep ⊤ (⟨v, hv⟩ : Fin n)) : ℕ) ≤ 0 := this
  omega

theorem gA_rel_last {x y : ℕ} (hx : x < n) (hy : y < n) :
    gA (rel ms ms.length) x y ↔ x ≠ y := by
  have hrel : rel ms ms.length = ⊤ := by simp [rel]
  rw [hrel]
  constructor
  · rintro ⟨_, _, h⟩ he
    subst he; exact h.ne rfl
  · intro h
    exact ⟨hx, hy, by simpa using h⟩

theorem labJ_of_lt {j : ℕ} (hj : j < ms.length) : labJ ms j = repN ms[j].1 := by
  simp [labJ, part, hj]

theorem rel_of_lt {j : ℕ} (hj : j < ms.length) : rel ms j = ms[j].2 := by
  simp [rel, hj]

/-- What `loadNext` leaves for the stage `j`. -/
theorem loadNext_run {B cap j : ℕ} {τ : Env} (hb : ConsBase G ms cap j τ) (hj : j < ms.length)
    (hj' : τ.vars "j" = j) (hB : n * n + ms.length + 2 * n + 3 < B) :
    ∃ τ', Run B loadNext τ τ' (100 * (n + 1) * (n + 1)) ∧
      Vec τ' "nxt" n (labJ ms (j + 1)) ∧ Mat τ' "rel" n (fun x y => ind (gA (rel ms (j + 1)) x y)) ∧
      τ'.inp = ((ms.drop (j + 2)).map fun p => toWord p.1 ++ toWord p.2).flatten ∧
      (∀ y, y ∈ ["n", "m", "j", "p"] → τ'.vars y = τ.vars y) ∧
      (∀ a, a ∈ ["adj", "res", "cur", "buf", "bad", "unr", "pos"] → τ'.arrs a = τ.arrs a) ∧
      τ'.out = τ.out := by
  have hnn : n ≤ n * n := Nat.le_mul_self n
  have hc : (Cond.lt (.add (.var "j") (.lit 1)) (.var "m")).evalB B τ =
      some (decide (j + 1 < ms.length)) := by
    rw [evalB_condLt (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp [hj']; omega))
      (evalB_var (by rw [hb.hm]; omega)), hj', hb.hm]
    rfl
  by_cases hlast : j + 1 < ms.length
  · -- read the next stage
    have hinp : τ.inp = toWord ms[j + 1].1 ++ (toWord ms[j + 1].2 ++
        ((ms.drop (j + 2)).map fun p => toWord p.1 ++ toWord p.2).flatten) := by
      rw [hb.hinp, List.drop_eq_getElem_cons hlast]
      simp only [List.map_cons, List.flatten_cons, List.append_assoc]
    obtain ⟨τ1, hr1, hinp1, hv1⟩ := readPartition_run (B := B) ms[j + 1].1 hinp hb.hnxt (by omega)
    set R := ms[j + 1].2
    have hinp1' : τ1.inp = n :: (((nbhds R).map toWord).flatten ++
        ((ms.drop (j + 2)).map fun p => toWord p.1 ++ toWord p.2).flatten) := by
      rw [hinp1, toWord_graph_nbhds]; rfl
    set τ2 : Env := { τ1.setVar "c" n with inp := ((nbhds R).map toWord).flatten ++
        ((ms.drop (j + 2)).map fun p => toWord p.1 ++ toWord p.2).flatten } with hτ2
    have hr2 : Run B (.read "c") τ1 τ2 1 := Run.read hinp1'
    have hfr1 : ∀ y, y ∈ ["n", "m", "j", "p", "c"] → τ1.vars y = τ.vars y := by
      intro y hy
      refine hr1.frame_var y ?_
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl <;>
        simp [readPartition, readPart, readPartElem, forUp, Com.wvars]
    have hn2 : τ2.vars "n" = n := by simp [hτ2, hfr1 "n" (by decide), hb.hn]
    obtain ⟨τ3, hr3, -, hm3⟩ := matFill_run (B := B) (K := 8) (arr := "rel") (e := .lit 0)
      (fun ρ => ρ.vars "n" = n) (fun _ _ => 0) (by omega) (fun ρ h => h)
      (fun ρ x h => by simp [h]) (fun ρ x h => by simp [h]) (fun ρ i x h => by simp [h])
      (fun ρ i j h _ _ _ _ => evalB_lit (by omega)) (by simp) hn2
      (by rw [show τ2.arrs "rel" = τ.arrs "rel" by
            simp only [hτ2, arrs_setVar]
            exact hr1.frame_arr "rel" (by simp [readPartition, readPart, readPartElem, forUp,
              Com.warrs])]
          exact hb.hrel)
    have hn3 : τ3.vars "n" = n := by rw [hr3.frame_var "n" (by decide), hn2]
    have hc3 : τ3.vars "c" = (nbhds R).length := by
      rw [hr3.frame_var "c" (by decide), length_nbhds]; simp [hτ2]
    obtain ⟨τ4, hr4, hinp4, hlen4, hrel4⟩ := readRows_run (B := B) (arr := "rel") (cnt := "c")
      (L := nbhds R) (σ := τ3) (by decide) (by decide)
      (by rw [hr3.frame_inp (by decide)]) hc3 hn3
      (by rw [mat_zero_eq hm3, length_nbhds]) (by rw [length_nbhds]; nlinarith)
      (by rw [length_nbhds]; omega)
    refine ⟨τ4, (Run.ite_true (by rw [hc]; simp [hlast]) (Run.seq hr1 (Run.seq hr2
      (Run.seq hr3 hr4)))).mono ?_, ?_, ⟨by rw [hlen4, length_nbhds], fun x hx y hy => ?_⟩,
      hinp4, fun y hy => ?_, fun a ha => ?_, ?_⟩
    · simp only [size_bin, size_var, size_lit, Cond.size, length_nbhds]
      nlinarith
    · rw [labJ_of_lt ms hlast]
      refine hv1.of_eq ?_
      rw [hr4.frame_arr "nxt" (by decide), hr3.frame_arr "nxt" (by decide)]
      simp [hτ2]
    · rw [hrel4 x (by rw [length_nbhds]; exact hx) y hy, rel_of_lt ms hlast]
      exact congrArg some (ite_eq_ind (mem_nbhds (by rw [length_nbhds]; exact hx)))
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rw [hr4.frame_var y (by rcases hy with rfl | rfl | rfl | rfl <;> decide),
        hr3.frame_var y (by rcases hy with rfl | rfl | rfl | rfl <;> decide)]
      have := hfr1 y (by simp only [List.mem_cons, List.not_mem_nil, or_false]; tauto)
      rcases hy with rfl | rfl | rfl | rfl <;> simp [hτ2, this]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rw [hr4.frame_arr a (by rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
        hr3.frame_arr a (by rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
      simp only [hτ2, arrs_setVar]
      exact hr1.frame_arr a (by
        rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp [readPartition, readPart, readPartElem, forUp, Com.warrs])
    · rw [hr4.out_eq (by decide), hr3.out_eq (by decide)]
      simp only [hτ2, out_setVar]
      rw [hr1.out_eq (by simp [readPartition, readPart, readPartElem, forUp, Com.NoWrite])]
  · -- the last stage
    have hjm : j + 1 = ms.length := by omega
    obtain ⟨τ1, hr1, hn1, hl1, hg1⟩ := rowFill_run (B := B) (base := 0) (K := 8) (arr := "nxt")
      (ie := .var "b") (e := .lit 0) (fun ρ => ρ.vars "n" = n) (fun _ => 0) (by omega)
      (fun ρ h => h) (fun ρ x h => by simp [h]) (fun ρ i x h => by simp [h])
      (fun ρ k _ hb' _ => by rw [evalB_var (by omega), hb']; simp)
      (fun ρ k _ _ _ => evalB_lit (by omega)) (by simp) hb.hn (by rw [hb.hnxt]; omega)
    obtain ⟨τ2, hr2, hn2, hm2⟩ := matFill_run (B := B) (K := 20) (arr := "rel")
      (e := .sub (.lit 1) (eqE "a" "b"))
      (fun ρ => ρ.vars "n" = n) (fun x y => ind (gA (rel ms (j + 1)) x y)) (by omega) (fun ρ h => h)
      (fun ρ x h => by simp [h]) (fun ρ x h => by simp [h]) (fun ρ i x h => by simp [h])
      (fun ρ i k h ha hb' hi hk => by
        have := evalB_bin (op := .sub) (evalB_lit (n := 1) (B := B) (σ := ρ) (by omega))
          (evalB_eqE (B := B) (σ := ρ) (x := "a") (y := "b") (by omega) (by omega) (by omega))
          (by simp; omega)
        rw [this, ha, hb', Bop.apply_sub, one_sub_ind]
        congr 1
        exact ind_eq_iff.mpr (by rw [hjm, gA_rel_last ms hi hk]))
      (by simp) hn1 (by rw [hr1.frame_arr "rel" (by decide)]; exact hb.hrel)
    refine ⟨τ2, (Run.ite_false (by rw [hc]; simp [hlast]) (Run.seq hr1 hr2)).mono ?_,
      ⟨by rw [hr2.frame_arr "nxt" (by decide), hl1, hb.hnxt], fun v hv => ?_⟩, hm2, ?_,
      fun y hy => ?_, fun a ha => ?_, ?_⟩
    · simp only [size_bin, size_var, size_lit, Cond.size]
      nlinarith
    · rw [hr2.frame_arr "nxt" (by decide), hg1 v, if_pos ⟨by omega, by omega⟩, hjm,
        labJ_last ms hv]
    · rw [hr2.frame_inp (by decide), hr1.frame_inp (by decide), hb.hinp]
      simp [List.drop_eq_nil_of_le (show ms.length ≤ j + 1 by omega),
        List.drop_eq_nil_of_le (show ms.length ≤ j + 2 by omega)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rw [hr2.frame_var y (by rcases hy with rfl | rfl | rfl | rfl <;> decide),
        hr1.frame_var y (by rcases hy with rfl | rfl | rfl | rfl <;> decide)]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rw [hr2.frame_arr a (by rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide),
        hr1.frame_arr a (by rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    · rw [hr2.out_eq (by decide), hr1.out_eq (by decide)]

/-- The state within a stage. -/
structure SCtx (cap : ℕ) (l : List ℕ) (lab lab' : ℕ → ℕ) (Rel Old : ℕ → ℕ → Prop) (τ : Env) :
    Prop where
  hn : τ.vars "n" = n
  hadj : Mat τ "adj" n fun x y => ind (gA G x y)
  hcur : Vec τ "cur" n lab
  hnxt : Vec τ "nxt" n lab'
  hrel : Mat τ "rel" n fun x y => ind (Rel x y)
  hres : Mat τ "res" n fun x y => ind (Old x y)
  hbuf : BufAt cap l τ
  hbad : (τ.arrs "bad").length = n * n
  hunr : (τ.arrs "unr").length = n * n
  hpos : (τ.arrs "pos").length = n * n

variable {G} in
theorem SCtx.of_frame {cap : ℕ} {l : List ℕ} {lab lab' : ℕ → ℕ} {Rel Old : ℕ → ℕ → Prop}
    {τ τ' : Env} (h : SCtx G cap l lab lab' Rel Old τ)
    (hv : ∀ y, y ∈ ["n", "p"] → τ'.vars y = τ.vars y)
    (ha : ∀ a, a ∈ ["adj", "cur", "nxt", "rel", "res", "buf"] → τ'.arrs a = τ.arrs a)
    (hl : ∀ a, (τ'.arrs a).length = (τ.arrs a).length) : SCtx G cap l lab lab' Rel Old τ' :=
  ⟨by rw [hv "n" (by decide), h.hn], h.hadj.of_eq (ha _ (by decide)), h.hcur.of_eq (ha _ (by decide)),
    h.hnxt.of_eq (ha _ (by decide)), h.hrel.of_eq (ha _ (by decide)), h.hres.of_eq (ha _ (by decide)),
    h.hbuf.of_eq (hv _ (by decide)) (ha _ (by decide)), by rw [hl, h.hbad], by rw [hl, h.hunr],
    by rw [hl, h.hpos]⟩

variable {G} in
theorem SCtx.of_run {cap : ℕ} {l : List ℕ} {lab lab' : ℕ → ℕ} {Rel Old : ℕ → ℕ → Prop}
    {τ τ' : Env} {B K : ℕ} {c : Com} (h : SCtx G cap l lab lab' Rel Old τ) (hr : Run B c τ τ' K)
    (hv : ∀ y, y ∈ ["n", "p"] → y ∉ c.wvars)
    (ha : ∀ a, a ∈ ["adj", "cur", "nxt", "rel", "res", "buf"] → a ∉ c.warrs) :
    SCtx G cap l lab lab' Rel Old τ' :=
  h.of_frame (fun y hy => hr.frame_var y (hv y hy)) (fun a hai => hr.frame_arr a (ha a hai))
    (fun a => run_length_arrs hr a)

/-- One flag: clear it, then scan the pairs. -/
def flagPhase (F : String) (c : Cond) : Com := .seq (matFill F (.lit 0)) (flagScan F c)

variable {G} in
/-- **One flag matrix.** -/
theorem flagPhase_run {B cap : ℕ} {l : List ℕ} {lab lab' : ℕ → ℕ} {Rel Old : ℕ → ℕ → Prop}
    {τ : Env} {F : String} {c : Cond} (P : ℕ → ℕ → Prop)
    (hF : F ∈ ["bad", "unr", "pos"]) (h : SCtx G cap l lab lab' Rel Old τ)
    (hlab : ∀ z < n, lab z < n) (hB : n * n + n + 1 < B)
    (hc : ∀ τ i j, SCtx G cap l lab lab' Rel Old τ → τ.vars "x" = i → τ.vars "y" = j →
      i < n → j < n → ∃ bv, c.evalB B τ = some bv ∧ (bv = true ↔ P i j)) :
    ∃ τ', Run B (flagPhase F c) τ τ' (n * (n * (c.size + 70) + 30) + 20) ∧
      SCtx G cap l lab lab' Rel Old τ' ∧ Mat τ' F n (fun lo hi => ind (FlagP n lab P lo hi)) ∧
      (∀ a, a ∈ ["bad", "unr", "pos"] → a ≠ F → τ'.arrs a = τ.arrs a) ∧ τ'.out = τ.out ∧
      τ'.inp = τ.inp ∧ (∀ y, y ∈ ["n", "m", "j", "p"] → τ'.vars y = τ.vars y) := by
  have hlenF : (τ.arrs F).length = n * n := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
    rcases hF with rfl | rfl | rfl
    exacts [h.hbad, h.hunr, h.hpos]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hF
  have hFn : ∀ a, a ∈ ["adj", "cur", "nxt", "rel", "res", "buf"] → F ≠ a := by
    intro a ha hFa
    subst hFa
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases hF with rfl | rfl | rfl <;> rcases ha with h | h | h | h | h | h <;> exact absurd h (by decide)
  have hCs : ∀ ρ i v, SCtx G cap l lab lab' Rel Old ρ → SCtx G cap l lab lab' Rel Old (ρ.setArr F i v) :=
    fun ρ i v hρ => hρ.of_frame (fun y _ => by simp) (fun a ha => by simp [Ne.symm (hFn a ha)])
      (fun a => length_arrs_setArr ρ F i v a)
  obtain ⟨τ1, hr1, hc1, hm1⟩ := matFill_run (B := B) (K := 8) (arr := F) (e := .lit 0)
    (SCtx G cap l lab lab' Rel Old) (fun _ _ => 0) hB (fun ρ h => h.hn)
    (fun ρ x hρ => hρ.of_frame (fun y hy => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> simp) (fun a _ => by simp) (fun a => by simp))
    (fun ρ x hρ => hρ.of_frame (fun y hy => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> simp) (fun a _ => by simp) (fun a => by simp))
    hCs (fun ρ i j _ _ _ _ _ => evalB_lit (by omega)) (by simp) h hlenF
  obtain ⟨τ2, hr2, hc2, hm2⟩ := flagScan_run (B := B) (F := F) (c := c)
    (SCtx G cap l lab lab' Rel Old) lab P hB hlab (fun ρ h => h.hn) (fun ρ h => h.hcur)
    (fun ρ x v hx hρ => hρ.of_frame (fun y hy => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
        rcases hy with rfl | rfl <;> rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
      (fun a _ => by simp) (fun a => by simp))
    (fun ρ ρ' hρ ha hi ho hv => hρ.of_frame (fun y hy => hv y (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> decide)) (fun a _ => by rw [ha]) (fun a => by rw [ha]))
    hCs hc hc1 hm1
  have hwv : ∀ y, y ∈ ["n", "m", "j", "p"] → y ∉ (flagPhase F c).wvars := by
    intro y hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl <;>
      simp [flagPhase, matFill, rowFill, flagScan, flagStep, lohi, forUp, Com.wvars]
  have hr : Run B (flagPhase F c) τ τ2 _ := Run.seq hr1 hr2
  refine ⟨τ2, hr.mono ?_, hc2, hm2, fun a ha haF => hr.frame_arr a ?_, hr.out_eq ?_,
    hr.frame_inp ?_, fun y hy => hr.frame_var y (hwv y hy)⟩
  · ring_nf
    nlinarith [Nat.zero_le (n * n * c.size), Nat.zero_le (n * c.size)]
  · simp [flagPhase, matFill, rowFill, flagScan, flagStep, lohi, forUp, Com.warrs]
    exact haF
  · simp [flagPhase, matFill, rowFill, flagScan, flagStep, lohi, forUp, Com.NoWrite]
  · simp [flagPhase, matFill, rowFill, flagScan, flagStep, lohi, forUp, Com.reads]

/-- The conditions of the three flags and of the update of `res`. -/
def cBad : Cond := .eq (.get "rel" (rm "x" "y")) (.lit 0)
def cUnr : Cond := .eq (.get "res" (rm "x" "y")) (.lit 0)
def cPos : Cond := .eq (.sub (.get "adj" (rm "x" "y")) (.get "res" (rm "x" "y"))) (.lit 1)
def cRes : Cond := .eq (.get "bad" (rm "lo" "hi")) (.lit 0)

/-- Move the labels of the next partition into `cur`. -/
def copyCur : Com := rowFill "cur" (.var "b") (.get "nxt" (.var "b"))

/-- One stage. -/
def stageM : Com :=
  .seq loadNext (.seq (flagPhase "bad" cBad) (.seq (flagPhase "unr" cUnr)
    (.seq (flagPhase "pos" cPos) (.seq emitResolves (.seq (pairSet "res" cRes)
      (.seq emitMerges copyCur))))))

theorem length_resTriples (lab : ℕ → ℕ) (Bad Unr Pos : ℕ → ℕ → Prop) :
    (resTriples n lab Bad Unr Pos).length ≤ 3 * (n * n) := by
  unfold resTriples
  refine (length_flatMap_le _ _ (3 * n) fun a _ => ?_).trans (by simp; nlinarith)
  refine (length_flatMap_le _ _ 3 fun b _ => ?_).trans (by simp)
  split <;> simp

theorem length_mrgTriples (lab lab' : ℕ → ℕ) : (mrgTriples n lab lab').length ≤ 3 * n := by
  unfold mrgTriples
  refine (length_flatMap_le _ _ 3 fun v _ => ?_).trans (by simp)
  split <;> simp

theorem codesBefore_succ (j : ℕ) : codesBefore G ms (j + 1) = codesBefore G ms j ++
    (resTriples n (labJ ms j) (BadJ ms j) (UnrJ ms j) (PosJ G ms j) ++
      mrgTriples n (labJ ms j) (labJ ms (j + 1))) := by
  rw [resTriples_eq, mrgTriples_eq, codesBefore, codesBefore, List.range_succ, List.flatMap_append,
    List.flatMap_append, List.flatMap_singleton]
  unfold stageSteps
  rw [List.flatMap_append]

theorem length_codesBefore (j : ℕ) : (codesBefore G ms j).length ≤ 3 * j * (n * n + n) := by
  induction j with
  | zero => simp [codesBefore]
  | succ j ih =>
    rw [codesBefore_succ, List.length_append, List.length_append]
    have h1 := length_resTriples (n := n) (labJ ms j) (BadJ ms j) (UnrJ ms j) (PosJ G ms j)
    have h2 := length_mrgTriples (n := n) (labJ ms j) (labJ ms (j + 1))
    nlinarith

theorem labJ_lt (j : ℕ) {v : ℕ} (hv : v < n) : labJ ms j v < n := repN_lt _ hv

theorem eval_mat_eq {B : ℕ} {τ : Env} {arr x y : String} {i j : ℕ} {P : ℕ → ℕ → Prop}
    (h : Mat τ arr n fun a b => ind (P a b)) (hn : τ.vars "n" = n) (hx : τ.vars x = i)
    (hy : τ.vars y = j) (hi : i < n) (hj : j < n) (hB : n * n + n + 1 < B) (v : ℕ) (hv : v ≤ 1) :
    ∃ bv, (Cond.eq (.get arr (rm x y)) (.lit v)).evalB B τ = some bv ∧
      (bv = true ↔ ind (P i j) = v) := by
  have hnn : n ≤ n * n := Nat.le_mul_self n
  refine ⟨_, evalB_condEq' (h.evalB hn hx hy hi hj (by omega) (by omega)
    (by have := ind_le_one (P i j); omega)) (evalB_lit (by omega)), by simp⟩

/-- **One stage of the program.** -/
theorem stageM_run {B cap j : ℕ} {τ : Env} (hb : ConsBase G ms cap j τ) (hj : j < ms.length)
    (hj' : τ.vars "j" = j) (hcap : 3 * ms.length * (n * n + n) ≤ cap)
    (hB : n * n + cap + ms.length + 2 * n + 3 < B) :
    ∃ τ', Run B stageM τ τ' (1000 * (n + 1) * (n + 1)) ∧ ConsBase G ms cap (j + 1) τ' ∧
      τ'.vars "j" = j := by
  classical
  have hnn : n ≤ n * n := Nat.le_mul_self n
  have hlab := fun v (hv : v < n) => labJ_lt ms j hv
  have hlab' := fun v (hv : v < n) => labJ_lt ms (j + 1) hv
  have hlc := length_codesBefore G ms j
  have hlcap : (codesBefore G ms j).length + 3 * (n * n) + 3 * n ≤ cap := by
    have : 3 * j * (n * n + n) + 3 * (n * n + n) ≤ 3 * ms.length * (n * n + n) := by
      have := Nat.mul_le_mul_right (n * n + n) (show 3 * j + 3 ≤ 3 * ms.length by omega)
      nlinarith
    nlinarith
  -- load the next stage
  obtain ⟨τ1, hr1, hnxt1, hrel1, hinp1, hv1, ha1, ho1⟩ := loadNext_run (B := B) G ms hb hj hj' (by omega)
  have hS1 : SCtx G cap (codesBefore G ms j) (labJ ms j) (labJ ms (j + 1))
      (gA (rel ms (j + 1))) (gA (resolvedAt ms j)) τ1 :=
    ⟨by rw [hv1 "n" (by decide), hb.hn], hb.hadj.of_eq (ha1 _ (by decide)),
      hb.hcur.of_eq (ha1 _ (by decide)), hnxt1, hrel1, hb.hres.of_eq (ha1 _ (by decide)),
      hb.hbuf.of_eq (hv1 "p" (by decide)) (ha1 _ (by decide)),
      (run_length_arrs hr1 "bad").trans hb.hbad, (run_length_arrs hr1 "unr").trans hb.hunr,
      (run_length_arrs hr1 "pos").trans hb.hpos⟩
  -- the three flags
  obtain ⟨τ2, hr2, hS2, hbad2, -, ho2, hi2, hv2⟩ := flagPhase_run (B := B) (F := "bad") (c := cBad)
    (fun x y => ¬ gA (rel ms (j + 1)) x y) (by decide) hS1 hlab (by omega)
    (fun ρ i k h hx hy hi hk => by
      obtain ⟨bv, hbv, hiff⟩ := eval_mat_eq (B := B) h.hrel h.hn hx hy hi hk (by omega) 0 (by omega)
      exact ⟨bv, hbv, by rw [hiff]; simp [ind]⟩)
  obtain ⟨τ3, hr3, hS3, hunr3, hk3, ho3, hi3, hv3⟩ := flagPhase_run (B := B) (F := "unr") (c := cUnr)
    (fun x y => ¬ gA (resolvedAt ms j) x y) (by decide) hS2 hlab (by omega)
    (fun ρ i k h hx hy hi hk => by
      obtain ⟨bv, hbv, hiff⟩ := eval_mat_eq (B := B) h.hres h.hn hx hy hi hk (by omega) 0 (by omega)
      exact ⟨bv, hbv, by rw [hiff]; simp [ind]⟩)
  have hbad3 : Mat τ3 "bad" n _ := hbad2.of_eq (hk3 "bad" (by decide) (by decide))
  obtain ⟨τ4, hr4, hS4, hpos4, hk4, ho4, hi4, hv4⟩ := flagPhase_run (B := B) (F := "pos") (c := cPos)
    (fun x y => ¬ gA (resolvedAt ms j) x y ∧ gA G x y) (by decide) hS3 hlab (by omega)
    (fun ρ i k h hx hy hi hk => by
      have e1 := h.hadj.evalB (B := B) h.hn hx hy hi hk (by omega) (by omega)
        (by have := ind_le_one (gA G i k); omega)
      have e2 := h.hres.evalB (B := B) h.hn hx hy hi hk (by omega) (by omega)
        (by have := ind_le_one (gA (resolvedAt ms j) i k); omega)
      refine ⟨_, evalB_condEq' (evalB_bin (op := .sub) e1 e2 (by
        simp only [Bop.apply_sub]; have := ind_le_one (gA G i k); omega)) (evalB_lit (by omega)), ?_⟩
      simp only [Bop.apply_sub]
      unfold ind
      by_cases h1 : gA G i k <;> by_cases h2 : gA (resolvedAt ms j) i k <;> simp [h1, h2])
  have hbad4 : Mat τ4 "bad" n _ := hbad3.of_eq (hk4 "bad" (by decide) (by decide))
  have hunr4 : Mat τ4 "unr" n _ := hunr3.of_eq (hk4 "unr" (by decide) (by decide))
  -- the resolves
  obtain ⟨τ5, hr5, hc5, hbuf5⟩ := emitResolves_run (B := B) (n := n) (cap := cap)
    (lab := labJ ms j) (Bad := BadJ ms j) (Unr := UnrJ ms j) (Pos := PosJ G ms j)
    ⟨hS4.hn, hS4.hcur, hbad4, hunr4, hpos4⟩ hlab hS4.hbuf (by omega) (by omega)
  have hr5' := hr5
  have hS5 : SCtx G cap (codesBefore G ms j ++ resTriples n (labJ ms j) (BadJ ms j) (UnrJ ms j)
      (PosJ G ms j)) (labJ ms j) (labJ ms (j + 1)) (gA (rel ms (j + 1))) (gA (resolvedAt ms j)) τ5 :=
    ⟨hc5.hn, hS4.hadj.of_eq (hr5.frame_arr "adj" (by decide)), hc5.hcur,
      hS4.hnxt.of_eq (hr5.frame_arr "nxt" (by decide)), hS4.hrel.of_eq (hr5.frame_arr "rel" (by decide)),
      hS4.hres.of_eq (hr5.frame_arr "res" (by decide)), hbuf5,
      (run_length_arrs hr5 "bad").trans hS4.hbad, (run_length_arrs hr5 "unr").trans hS4.hunr,
      (run_length_arrs hr5 "pos").trans hS4.hpos⟩
  -- the update of the resolved pairs
  set l5 := codesBefore G ms j ++ resTriples n (labJ ms j) (BadJ ms j) (UnrJ ms j) (PosJ G ms j)
    with hl5
  let C6 : Env → Prop := fun ρ => ρ.vars "n" = n ∧ Vec ρ "cur" n (labJ ms j) ∧
    Vec ρ "nxt" n (labJ ms (j + 1)) ∧ BufAt cap l5 ρ ∧ Mat ρ "bad" n fun lo hi => ind (BadJ ms j lo hi)
  have hC6 : ∀ ρ ρ' : Env, C6 ρ → (∀ y, y ∈ ["n", "p"] → ρ'.vars y = ρ.vars y) →
      (∀ a, a ∈ ["cur", "nxt", "buf", "bad"] → ρ'.arrs a = ρ.arrs a) → C6 ρ' :=
    fun ρ ρ' h hv ha => ⟨by rw [hv "n" (by decide), h.1], h.2.1.of_eq (ha _ (by decide)),
      h.2.2.1.of_eq (ha _ (by decide)), h.2.2.2.1.of_eq (hv _ (by decide)) (ha _ (by decide)),
      h.2.2.2.2.of_eq (ha _ (by decide))⟩
  obtain ⟨τ6, hr6, hC6', hres6⟩ := pairSet_run (B := B) (D := "res") (c := cRes) C6
    (labJ ms j) (gA (resolvedAt ms j))
    (fun x y => ¬ BadJ ms j (min (labJ ms j x) (labJ ms j y)) (max (labJ ms j x) (labJ ms j y)))
    (by omega) hlab (fun ρ h => h.1) (fun ρ h => h.2.1)
    (fun ρ x v hx h => hC6 ρ _ h (fun y hy => by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
        rcases hy with rfl | rfl <;> rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> simp)
      (fun a _ => by simp))
    (fun ρ ρ' h ha hi ho hv => hC6 ρ ρ' h (fun y hy => hv y (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl <;> decide)) (fun a _ => by rw [ha]))
    (fun ρ i v h => hC6 ρ _ h (fun y _ => by simp) (fun a ha => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> simp))
    (fun ρ i k h hx hy hi hk hlo hhi => by
      have hlo' : min (labJ ms j i) (labJ ms j k) < n := by have := hlab i hi; omega
      have hhi' : max (labJ ms j i) (labJ ms j k) < n := by
        have := hlab k hk; have := hlab i hi; omega
      obtain ⟨bv, hbv, hiff⟩ := eval_mat_eq (B := B) h.2.2.2.2 h.1 hlo hhi hlo' hhi' (by omega) 0
        (by omega)
      exact ⟨bv, hbv, by rw [hiff]; simp [ind]⟩)
    ⟨hS5.hn, hS5.hcur, hS5.hnxt, hS5.hbuf, hbad4.of_eq (hr5.frame_arr "bad" (by decide))⟩ hS5.hres
  obtain ⟨hn6, hcur6, hnxt6, hbuf6, -⟩ := hC6'
  have hres6' : Mat τ6 "res" n fun x y => ind (gA (resolvedAt ms (j + 1)) x y) :=
    hres6.congr fun x hx y hy => ind_eq_iff.mpr
      ((resolvedAt_succ_iff ms j ⟨x, hx⟩ ⟨y, hy⟩).symm)
  -- the merges
  have hrt := length_resTriples (n := n) (labJ ms j) (BadJ ms j) (UnrJ ms j) (PosJ G ms j)
  obtain ⟨τ7, hr7, hc7, hbuf7⟩ := emitMerges_run (B := B) (cap := cap) ⟨hn6, hcur6, hnxt6⟩ hlab
    hlab' hbuf6 (by rw [hl5, List.length_append]; omega) (by omega)
  -- the new labels
  obtain ⟨τ8, hr8, ⟨hn8, hnxt8⟩, hlen8, hg8⟩ := rowFill_run (B := B) (base := 0) (K := 8)
    (arr := "cur") (ie := .var "b") (e := .get "nxt" (.var "b"))
    (fun ρ => ρ.vars "n" = n ∧ Vec ρ "nxt" n (labJ ms (j + 1))) (labJ ms (j + 1)) (by omega)
    (fun ρ h => h.1) (fun ρ x h => ⟨by simp [h.1], h.2.of_eq (by simp)⟩)
    (fun ρ i x h => ⟨by simp [h.1], h.2.of_eq (by simp)⟩)
    (fun ρ k _ hb' _ => by rw [evalB_var (by omega), hb']; simp)
    (fun ρ k h hb' hk => h.2.evalB hb' hk (by omega) (by have := hlab' k hk; omega))
    (by simp) ⟨hc7.hn, hc7.hnxt⟩ (by rw [hc7.hcur.len]; omega)
  have hrA : Run B (.seq (flagPhase "pos" cPos) (.seq emitResolves (.seq (pairSet "res" cRes)
      (.seq emitMerges copyCur)))) τ3 τ8 _ := Run.seq hr4 (Run.seq hr5 (Run.seq hr6 (Run.seq hr7 hr8)))
  have hrS : Run B stageM τ τ8 _ := Run.seq hr1 (Run.seq hr2 (Run.seq hr3 hrA))
  refine ⟨τ8, hrS.mono ?_, ⟨hn8, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [cBad, cUnr, cPos, cRes, Cond.size, size_get, size_rm, size_lit, size_bin]
    ring_nf
    nlinarith
  · rw [hrS.frame_var "m" (by decide), hb.hm]
  · exact hb.hadj.of_eq (hrS.frame_arr "adj" (by decide))
  · refine hres6'.of_eq ?_
    rw [hr8.frame_arr "res" (by decide), hr7.frame_arr "res" (by decide)]
  · exact ⟨by rw [hlen8, hc7.hcur.len], fun v hv => by
      rw [hg8 v, if_pos ⟨by omega, by omega⟩]; simp⟩
  · have := hbuf7.of_eq (hr8.frame_var "p" (by decide)) (hr8.frame_arr "buf" (by decide))
    rw [codesBefore_succ, ← List.append_assoc, ← hl5]
    exact this
  · rw [run_length_arrs hrS, hb.hnxt]
  · rw [run_length_arrs hrS, hb.hrel]
  · rw [run_length_arrs hrS, hb.hbad]
  · rw [run_length_arrs hrS, hb.hunr]
  · rw [run_length_arrs hrS, hb.hpos]
  · rw [hr8.frame_inp (by decide), hr7.frame_inp (by decide), hr6.frame_inp (by decide),
      hr5.frame_inp (by decide), hi4, hi3, hi2, hinp1]
  · rw [hrS.frame_var "j" (by decide), hj']

end Lax185574Proofs.Conversions.Ram
