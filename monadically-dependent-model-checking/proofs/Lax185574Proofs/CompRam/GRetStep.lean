import Lax185574Proofs.CompRam.GAdv

/-!
The steps by phase of round `j ≥ 1` of the glue command of lem:compose.

`Top W M j f S' b σ` describes the scalars before the step by the phase of
the top frame `f` of the stack `f :: S'`: the frame in the scalars `g…`,
the part `b` of the answer at `bs`, `bl`, the rest of the stack at `rS`,
`rL`, and the positions of the frames of the first words of the stack in
`wp`. The lemmas give the output of the step for every phase
(`ph0_run`, `ph1_run`, `ph2_run`, `ph4_run`, `ph5_run`, with `ret_run`
for the step that hands a result down), and `roundJ_run` the output of
the whole round.
-/

namespace Lax185574Proofs.CompRam

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words Lax185574Proofs.MC
open Lax185574Proofs.MC.Glue Lax185574.WordEncoding Lax185574.TypeTrees Lax185574Proofs.TreeAlgo

/-! ### Sequences and frames -/

theorem Run.seqs_app2 {B : ℕ} : ∀ {a b : List Com} {σ σ1 σ2 : Env} {K1 K2 : ℕ}, a ≠ [] → b ≠ [] →
    Run B (seqs a) σ σ1 K1 → Run B (seqs b) σ1 σ2 K2 → Run B (seqs (a ++ b)) σ σ2 (K1 + K2)
  | [c], b, _, _, _, _, _, _, hb, h1, h2 => Run.seqs_cons hb h1 h2
  | c :: d :: a, b, _, _, _, K1, K2, _, hb, h1, h2 => by
    obtain ⟨k, hk, hbs⟩ := h1
    cases hbs with
    | seq h1' h2' =>
      rename_i σm k1 k2
      have := Run.seqs_app2 (a := d :: a) (by simp) hb ⟨k2, le_refl _, h2'⟩ h2
      have r := Run.seqs_cons (cs := d :: a ++ b) (by simp) ⟨k1, le_refl _, h1'⟩ this
      exact r.mono (by omega)

theorem Keep.refl (σ : Env) : Keep σ σ := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem Keep.trans {σ σ' σ'' : Env} (h : Keep σ σ') (h' : Keep σ' σ'') : Keep σ σ'' :=
  ⟨h'.W.trans h.W, h'.jr.trans h.jr, h'.ovf.trans h.ovf, h'.x.trans h.x, h'.wp.trans h.wp,
    h'.ob.trans h.ob, h'.out.trans h.out, h'.inp.trans h.inp⟩

theorem Keep.of_ofr {σ σ' : Env} {xs : List String} (h : OFr σ σ' xs) (hW : "W" ∉ xs)
    (hj : "jr" ∉ xs) (ho : "ovf" ∉ xs) : Keep σ σ' :=
  ⟨h.vars _ hW, h.vars _ hj, h.vars _ ho, h.arrs _ (by decide), h.arrs _ (by decide), h.len, h.out, h.inp⟩

theorem Keep.setVar (σ : Env) {y : String} (h1 : y ≠ "W") (h2 : y ≠ "jr") (h3 : y ≠ "ovf") (v : ℕ) :
    Keep σ (σ.setVar y v) := Keep.of_ofr (OFr.setVar σ y v) (by simpa using Ne.symm h1)
      (by simpa using Ne.symm h2) (by simpa using Ne.symm h3)

theorem ExIs.of_vars {M : ℕ} {σ σ' : Env} {EX : List (List ℕ)} (h : ExIs M σ EX)
    (hv : ∀ y ∈ exVars, σ'.vars y = σ.vars y) (hx : σ'.arrs "x" = σ.arrs "x") : ExIs M σ' EX := by
  have hs : ∀ s l, s ∈ exVars → l ∈ exVars → ∀ w, SegIs M σ s l w → SegIs M σ' s l w :=
    fun s l hs hl w h => h.of_eq (hv s hs) (hv l hl) hx
  rcases h with ⟨h0, hE⟩ | ⟨h0, hg, E0, R1, R2, hEX, hE, h1, h2⟩
  · exact Or.inl ⟨by rw [hv "gx" (by decide)]; exact h0, hs _ _ (by decide) (by decide) _ hE⟩
  · refine Or.inr ⟨by rw [hv "gx" (by decide)]; exact h0, by rw [hv "gg" (by decide)]; exact hg,
      E0, R1, R2, by rw [hv "gg" (by decide)]; exact hEX, hs _ _ (by decide) (by decide) _ hE,
      hs _ _ (by decide) (by decide) _ h1, hs _ _ (by decide) (by decide) _ h2⟩

/-- A frame description after a change of some of its scalars: `g` agrees
with `f` up to the fields whose scalars changed, which the caller proves. -/
theorem SlotIs.upd {M : ℕ} {σ σ' : Env} {f g : Fr} (h : SlotIs M σ f) (xs : List String)
    (hv : ∀ y ∈ slotVars, y ∉ xs → σ'.vars y = σ.vars y) (hx : σ'.arrs "x" = σ.arrs "x")
    (hd : "gd" ∈ xs ∨ g.d = f.d) (hk : "gk" ∈ xs ∨ g.kk = f.kk) (h1 : "g1" ∈ xs ∨ g.l1 = f.l1)
    (h2 : "g2" ∈ xs ∨ g.l2 = f.l2) (hp : "gp" ∈ xs ∨ g.ph = f.ph) (hi : "gi" ∈ xs ∨ g.i = f.i)
    (hA : ("gAs" ∈ xs ∨ "gAl" ∈ xs) ∨ g.A = f.A) (hB : ("gBs" ∈ xs ∨ "gBl" ∈ xs) ∨ g.B = f.B)
    (hSA : ("gSs" ∈ xs ∨ "gSl" ∈ xs) ∨ g.SA = f.SA) (hSB : ("gTs" ∈ xs ∨ "gTl" ∈ xs) ∨ g.SB = f.SB)
    (hAT : ("gUs" ∈ xs ∨ "gUl" ∈ xs) ∨ g.AT = f.AT)
    (hEX : (∃ y ∈ exVars, y ∈ xs) ∨ g.EX = f.EX)
    (nd : "gd" ∈ xs → σ'.vars "gd" = g.d) (nk : "gk" ∈ xs → σ'.vars "gk" = g.kk)
    (n1 : "g1" ∈ xs → σ'.vars "g1" = g.l1) (n2 : "g2" ∈ xs → σ'.vars "g2" = g.l2)
    (np : "gp" ∈ xs → σ'.vars "gp" = g.ph) (ni : "gi" ∈ xs → σ'.vars "gi" = g.i)
    (nums : g.d < 2 * M ∧ g.kk < 2 * M ∧ g.l1 < 2 * M ∧ g.l2 < 2 * M ∧ g.ph < 2 * M ∧ g.i < 2 * M)
    (sA : ("gAs" ∈ xs ∨ "gAl" ∈ xs) → SegIs M σ' "gAs" "gAl" g.A)
    (sB : ("gBs" ∈ xs ∨ "gBl" ∈ xs) → SegIs M σ' "gBs" "gBl" g.B)
    (sSA : ("gSs" ∈ xs ∨ "gSl" ∈ xs) → SegIs M σ' "gSs" "gSl" g.SA)
    (sSB : ("gTs" ∈ xs ∨ "gTl" ∈ xs) → SegIs M σ' "gTs" "gTl" g.SB)
    (sAT : ("gUs" ∈ xs ∨ "gUl" ∈ xs) → SegIs M σ' "gUs" "gUl" g.AT)
    (sEX : (∃ y ∈ exVars, y ∈ xs) → ExIs M σ' g.EX) : SlotIs M σ' g := by
  have num : ∀ y ∈ slotVars, ∀ v, (y ∈ xs → σ'.vars y = v) → (y ∈ xs ∨ v = σ.vars y) →
      σ'.vars y = v := by
    intro y hy v h1 h2
    by_cases hyx : y ∈ xs
    · exact h1 hyx
    · rcases h2 with h2 | h2
      · exact absurd h2 hyx
      · rw [hv y hy hyx, h2]
  have seg : ∀ s l w w', s ∈ slotVars → l ∈ slotVars → SegIs M σ s l w' →
      ((s ∈ xs ∨ l ∈ xs) → SegIs M σ' s l w) → ((s ∈ xs ∨ l ∈ xs) ∨ w = w') → SegIs M σ' s l w := by
    intro s l w w' hs hl h0 h1 h2
    by_cases hx' : s ∈ xs ∨ l ∈ xs
    · exact h1 hx'
    · rcases h2 with h2 | h2
      · exact absurd h2 hx'
      · rw [h2]; rw [not_or] at hx'
        exact h0.of_eq (hv s hs hx'.1) (hv l hl hx'.2) hx
  refine ⟨num "gd" (by decide) _ nd (hd.imp id fun e => by rw [e, h.d]),
    num "gk" (by decide) _ nk (hk.imp id fun e => by rw [e, h.kk]),
    num "g1" (by decide) _ n1 (h1.imp id fun e => by rw [e, h.l1]),
    num "g2" (by decide) _ n2 (h2.imp id fun e => by rw [e, h.l2]),
    num "gp" (by decide) _ np (hp.imp id fun e => by rw [e, h.ph]),
    num "gi" (by decide) _ ni (hi.imp id fun e => by rw [e, h.i]), nums,
    seg _ _ _ _ (by decide) (by decide) h.A sA hA, seg _ _ _ _ (by decide) (by decide) h.B sB hB,
    seg _ _ _ _ (by decide) (by decide) h.SA sSA hSA, seg _ _ _ _ (by decide) (by decide) h.SB sSB hSB,
    seg _ _ _ _ (by decide) (by decide) h.AT sAT hAT, ?_⟩
  by_cases hE : ∃ y ∈ exVars, y ∈ xs
  · exact sEX hE
  · rcases hEX with hEX | hEX
    · exact absurd hEX hE
    · rw [hEX]; simp only [not_exists, not_and] at hE
      exact h.EX.of_vars (fun y hy => hv y (by
        simp only [exVars, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) (hE y hy)) hx


theorem length_le_frames (ws : List (List ℕ)) : ws.length ≤ (frames ws).length := by
  have h1 := count_lt_toWord ws
  rw [toWord_words] at h1
  simp at h1; omega

theorem hd0_cons2 (j : ℕ) (g : Fr) (Sr : List Fr) :
    hd0 j (g :: Sr) = [1, 0, 0, 0, j, (stWords (g :: Sr)).length] ++ frames (frWords g) ++
      frames (stWords Sr) := by
  rw [hd0, stWords_cons, frames_append, List.append_assoc]

/-- The head of a call and the frames of the stack `g :: Sr`. -/
theorem frameOut_run {W M j : ℕ} {σ : Env} {g : Fr} {Sr : List Fr} (hC : Ctx W M σ)
    (hF : Filled "OB" "po" [] σ) (hg : SlotIs M σ g)
    (hrest : SegIs M σ "rS" "rL" (frames (stWords Sr)))
    (hcnt : σ.vars "cnt" = (stWords (g :: Sr)).length) (hj1 : σ.vars "j1" = j) (hjM : j < M) :
    ∃ σ' K, Run (W + 1) (seqs [emHd, emFr, emRest, patchL]) σ σ' K ∧
      Filled "OB" "po" (hdS j (g :: Sr)) σ' ∧ (hdS j (g :: Sr)).length ≤ 20 * M ∧
      K ≤ 20 * (hdS j (g :: Sr)).length + 600 ∧ OFr σ σ' ["po", "ci", "u1", "u2", "gEL"] := by
  have hR := hC.room
  have hm := hC.m16
  have hrl := hrest.2.1
  have hsw : (stWords (g :: Sr)).length = 7 + (stWords Sr).length := by
    rw [stWords_cons]; simp [frWords]; omega
  have hfl := length_le_frames (stWords Sr)
  obtain ⟨σ1, r1, F1, fr1⟩ := emHd_run hC hF (by omega) (by omega) (by simp; omega)
  have hC1 := hC.ofr fr1 (by decide)
  obtain ⟨σ2, r2, F2, hl2, fr2⟩ := emFr_run hC1 F1 (hg.ofr fr1 (by decide)) (by simp; omega)
  have hC2 := hC1.ofr fr2 (by decide)
  obtain ⟨σ3, r3, F3, fr3⟩ := emRest_run hC2 F2
    ((hrest.ofr fr1 (by decide) (by decide)).ofr fr2 (by decide) (by decide)) (by simp; omega)
  have e : [] ++ [1, 0, 0, 0, σ.vars "j1", σ.vars "cnt"] ++ frames (frWords g) ++ frames (stWords Sr) =
      hd0 j (g :: Sr) := by rw [hd0_cons2, hj1, hcnt]; simp
  rw [e] at F3
  have hlen : (hd0 j (g :: Sr)).length = 6 + (frames (frWords g)).length + (frames (stWords Sr)).length := by
    rw [hd0_cons2]; simp only [List.length_append, List.length_cons, List.length_nil]
  obtain ⟨σ4, r4, F4, fr4⟩ := patchL_run (W := W) (l := hd0 j (g :: Sr)) F3 (by omega) (by omega)
  refine ⟨σ4, _, Run.seqs_cons (by simp) r1 (Run.seqs_cons (by simp) r2 (Run.seqs_cons (by simp) r3
    (Run.seqs_one r4))), F4, by rw [length_hdS]; omega, by rw [length_hdS]; omega, ?_⟩
  exact (((fr1.trans fr2).trans fr3).trans fr4).mono (by decide)


/-- A segment from three cells behind the start of the segment of `b`. -/
theorem segIs_drop3 {M : ℕ} {σ σ' : Env} {b : List ℕ} {s l : String} (hb : SegIs M σ "bs" "bl" b)
    (h3 : σ.vars "bs" + 3 ≤ M) (hs : σ'.vars s = σ.vars "bs" + 3) (hl : σ'.vars l = σ.vars "bl" - 3)
    (hx : σ'.arrs "x" = σ.arrs "x") : SegIs M σ' s l (b.drop 3) := by
  obtain ⟨h1, h2, h4⟩ := hb
  refine segIs_of (a := σ.vars "bs" + 3) hs (by rw [hl, h1]; simp) (by simp; omega) ?_
  rw [hx, List.length_drop]; exact seg_drop_front h4

/-- The query of a rank shift ends the output of a call. -/
theorem emSh_built {W M j : ℕ} {σ : Env} {S : List Fr} {Wd : List ℕ} (hC : Ctx W M σ)
    (hF : Filled "OB" "po" (hdS j S) σ) (hk : σ.vars "hk" < 2 * M) (hd : σ.vars "hd" < 2 * M)
    (hl : σ.vars "hl" < 2 * M) (hs : SegIs M σ "hs" "hw" Wd) (hpre : (hdS j S).length + 4 * M ≤ W) :
    ∃ σ' K, Run (W + 1) emSh σ σ' K ∧
      Built j (.call S (.sh ([σ.vars "hk", σ.vars "hd", σ.vars "hl"] ++ Wd)))
        (hdS j S ++ [5, Wd.length + 3, 1, 0, 0, 0, 0, 0] ++
          ([σ.vars "hk", σ.vars "hd", σ.vars "hl"] ++ Wd) ++ [0]) σ' ∧
      K ≤ 20 * Wd.length + 200 ∧ OFr σ σ' ["ci", "po", "qa", "ql", "sp", "dq", "qk"] := by
  obtain ⟨σ', r, F, hqa, hql, hsp, hdq, hqk, fr⟩ := emSh_run hC hF hk hd hl hs hpre
  have hw : ([σ.vars "hk", σ.vars "hd", σ.vars "hl"] ++ Wd).length = Wd.length + 3 := by simp
  refine ⟨σ', _, r, ?_, le_refl _, fr⟩
  have := built_sh (j := j) (S := S) (w := [σ.vars "hk", σ.vars "hd", σ.vars "hl"] ++ Wd) (σ := σ')
    (by rw [hw]; exact F) (by rw [hsp, hw]; omega) hdq hqk hqa (by rw [hql, hw])
  rw [hw] at this
  exact this

/-- The scalars before the step by the phase of the top frame `f` of the
stack `f :: S'` in round `j`, with the part `b` of the answer. -/
structure Top (W M j : ℕ) (f : Fr) (S' : List Fr) (b : List ℕ) (σ : Env) : Prop where
  ctx : Ctx W M σ
  x4 : ∀ v ∈ σ.arrs "x", 4 * v + 4 < M
  hx : ∃ r, (σ.arrs "x").drop 2 = toWord (stWords (f :: S')) ++ r
  hp : 2 + (toWord (stWords (f :: S'))).length ≤ M
  F : Filled "OB" "po" [] σ
  slot : SlotIs M σ f
  bseg : SegIs M σ "bs" "bl" b
  bs3 : σ.vars "bs" + 3 ≤ M
  rest : SegIs M σ "rS" "rL" (frames (stWords S'))
  cnt : σ.vars "cnt" = (stWords S').length
  j1 : σ.vars "j1" = j + 1
  jM : j + 1 < M
  n : σ.vars "n" = (stWords (f :: S')).length
  L : σ.vars "L" = 2 + (toWord (stWords (f :: S'))).length
  wp : ∀ i < min (stWords (f :: S')).length 14,
    (σ.arrs "wp").getD i 0 = frPos (σ.arrs "x") 2 i
  td : σ.vars "td" = f.d
  tp : σ.vars "tp" = f.ph
  gx : σ.vars "gx" = 0

/-- The phase `1`. -/
theorem ph1_run {W M j : ℕ} {σ : Env} {f : Fr} {S' : List Fr} {b : List ℕ}
    (h : Top W M j f S' b σ) (hph : f.ph = 1) :
    ∃ σ' ob K, Run (W + 1) ph1Cmd σ σ' K ∧ Built (j + 1) (round (f :: S') b) ob σ' ∧
      ob.length ≤ 64 * M ∧ K ≤ 20 * ob.length + 1000 ∧ Keep σ σ' := by
  have hC := h.ctx
  have hR := hC.room
  have hg := h.slot
  have hm := hC.m16
  obtain ⟨hn1, hn2, hn3, hn4, hn5, hn6⟩ := hg.nums
  set σ1 := σ.setVar "gp" 2
  set σ2 := σ1.setVar "gTs" (σ.vars "bs" + 3)
  set σ3 := σ2.setVar "gTl" (σ.vars "bl" - 3)
  set σ4 := σ3.setVar "cnt" (σ.vars "cnt" + 7)
  have hbs := h.bseg
  obtain ⟨hbl, hbM, -⟩ := hbs
  have r1 : Run (W + 1) (seqs [asg "gp" (N 2), asg "gTs" (.add (V "bs") (N 3)),
      asg "gTl" (.sub (V "bl") (N 3)), asg "cnt" (.add (V "cnt") (N 7))]) σ σ4 16 := by
    have hc := h.cnt
    have := (h.rest).2.1
    have := length_le_frames (stWords S')
    refine (Run.seqs_cons (by simp) (Run.assign (by simp; omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ1]; omega)) (Run.seqs_cons (by simp) (Run.assign (by simp [σ2, σ1]; omega))
      (Run.seqs_one (Run.assign (by simp [σ3, σ2, σ1]; omega)))))).mono (by simp)
  have hx4 : σ4.arrs "x" = σ.arrs "x" := by simp [σ4, σ3, σ2, σ1]
  have hg4 : SlotIs M σ4 { f with ph := 2, SB := b.drop 3 } := by
    refine hg.upd ["gp", "gTs", "gTl"] (fun y hy hy' => ?_) hx4 (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
      (Or.inr rfl) (Or.inl (by decide)) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
      (Or.inl (Or.inl (by decide))) (Or.inr rfl) (Or.inr rfl) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun _ => by simp [σ4, σ3, σ2, σ1, ])
      (fun h => absurd h (by decide)) ?_ (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) ?_ (fun h => absurd h (by decide))
      (fun ⟨y, hy, hy'⟩ => absurd hy' (by
        simp only [exVars, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
    · have : y ≠ "gp" ∧ y ≠ "gTs" ∧ y ≠ "gTl" := by simpa using hy'
      have hyc : y ≠ "cnt" := fun e => by subst e; exact absurd hy (by decide)
      simp [σ4, σ3, σ2, σ1, this.1, this.2.1, this.2.2, hyc]
    · exact ⟨hn1, hn2, hn3, hn4, show (2 : ℕ) < 2 * M by omega, hn6⟩
    · intro _
      exact segIs_drop3 h.bseg h.bs3 (by simp [σ4, σ3, σ2]) (by simp [σ4, σ3]) hx4
  have hC4 : Ctx W M σ4 := (((hC.setVar (by decide) _).setVar (by decide) _).setVar (by decide) _).setVar
    (by decide) _
  have hF4 : Filled "OB" "po" [] σ4 := h.F.congr (by simp [σ4, σ3, σ2, σ1]) (by simp [σ4, σ3, σ2, σ1])
  have hrest4 : SegIs M σ4 "rS" "rL" (frames (stWords S')) :=
    h.rest.of_eq (by simp [σ4, σ3, σ2, σ1]) (by simp [σ4, σ3, σ2, σ1]) hx4
  have hcnt4 : σ4.vars "cnt" = (stWords (({ f with ph := 2, SB := b.drop 3 } : Fr) :: S')).length := by
    simp only [σ4, Env.setVar, if_pos rfl]; rw [h.cnt, stWords_cons]; simp [frWords] <;> omega
  obtain ⟨σ5, K5, r5, F5, hl5, hK5, fr5⟩ := frameOut_run (j := j + 1) hC4 hF4 hg4 hrest4 hcnt4
    (by simp [σ4, σ3, σ2, σ1, h.j1]) h.jM
  have hC5 := hC4.ofr fr5 (by decide)
  have hg5 := hg4.ofr fr5 (by decide)
  set σ6 := σ5.setVar "hk" f.kk
  set σ7 := σ6.setVar "hd" f.d
  set σ8 := σ7.setVar "hl" f.l1
  set σ9 := σ8.setVar "hs" (σ5.vars "gAs")
  set σ10 := σ9.setVar "hw" (σ5.vars "gAl")
  have r6 : Run (W + 1) (seqs [asg "hk" (V "gk"), asg "hd" (V "gd"), asg "hl" (V "g1"),
      asg "hs" (V "gAs"), asg "hw" (V "gAl")]) σ5 σ10 10 := by
    have := hg5.A.2.1
    refine (Run.seqs_cons (by simp) (Run.assign (by simp [hg5.kk]; omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ6, hg5.d]; omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ7, σ6, hg5.l1]; omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ8, σ7, σ6]; omega))
      (Run.seqs_one (Run.assign (by simp [σ9, σ8, σ7, σ6]; rw [hg5.A.1]; omega))))))).mono (by simp)
  have hC10 : Ctx W M σ10 := ((((hC5.setVar (by decide) _).setVar (by decide) _).setVar (by decide) _).setVar
    (by decide) _).setVar (by decide) _
  have hF10 : Filled "OB" "po" (hdS (j + 1) (({ f with ph := 2, SB := b.drop 3 } : Fr) :: S')) σ10 :=
    F5.congr (by simp [σ10, σ9, σ8, σ7, σ6]) (by simp [σ10, σ9, σ8, σ7, σ6])
  have hA10 : SegIs M σ10 "hs" "hw" f.A := by
    obtain ⟨a1, a2, a3⟩ := hg5.A
    exact segIs_of (a := σ5.vars "gAs") (by simp [σ10, σ9]) (by simpa [σ10, σ9] using a1) a2
      (by simpa [σ10, σ9, σ8, σ7, σ6] using a3)
  obtain ⟨σ11, K11, r11, B11, hK11, fr11⟩ := emSh_built hC10 hF10 (by simp [σ10, σ9, σ8, σ7, σ6]; omega)
    (by simp [σ10, σ9, σ8, σ7, σ6]; omega) (by simp [σ10, σ9, σ8, σ7, σ6]; omega) hA10
    (by have := hA10.2.1; omega)
  have e1 : [σ10.vars "hk", σ10.vars "hd", σ10.vars "hl"] = [f.kk, f.d, f.l1] := by
    simp [σ10, σ9, σ8, σ7, σ6]
  rw [e1] at B11
  refine ⟨σ11, hdS (j + 1) (({ f with ph := 2, SB := b.drop 3 } : Fr) :: S') ++
    [5, f.A.length + 3, 1, 0, 0, 0, 0, 0] ++ ([f.kk, f.d, f.l1] ++ f.A) ++ [0], 16 + (K5 + (10 + K11)),
    ?_, ?_, ?_, ?_, ?_⟩
  · have := Run.seqs_app2 (a := [asg "gp" (N 2), asg "gTs" (.add (V "bs") (N 3)),
      asg "gTl" (.sub (V "bl") (N 3)), asg "cnt" (.add (V "cnt") (N 7))])
      (b := [emHd, emFr, emRest, patchL] ++ ([asg "hk" (V "gk"), asg "hd" (V "gd"), asg "hl" (V "g1"),
      asg "hs" (V "gAs"), asg "hw" (V "gAl")] ++ [emSh])) (by simp) (by simp) r1
      (Run.seqs_app2 (by simp) (by simp) r5 (Run.seqs_app2 (by simp) (by simp) r6 (Run.seqs_one r11)))
    exact this
  · rw [round_ph1 f S' b hph]; exact B11
  · have := hA10.2.1; simp; omega
  · simp; omega
  · refine (Keep.setVar σ (by decide) (by decide) (by decide) _).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      ((Keep.of_ofr fr5 (by decide) (by decide) (by decide)).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      (Keep.of_ofr fr11 (by decide) (by decide) (by decide)))))))))))


/-! ### Handing a result down -/

/-- The query of a restriction of the result `R₁ ++ R₂` to the parent `p`. -/
theorem retRe_run {W M j : ℕ} {σ : Env} {p : Fr} {S'' : List Fr} {R1 R2 : List ℕ} (hC : Ctx W M σ)
    (hF : Filled "OB" "po" [] σ) (hg : SlotIs M σ p)
    (hrest : SegIs M σ "rS" "rL" (frames (stWords S''))) (hcnt : σ.vars "cnt" = (stWords S'').length)
    (hj1 : σ.vars "j1" = j) (hjM : j < M) (hpk : σ.vars "pk" = p.kk) (hpd : σ.vars "pd" = p.d)
    (hp1 : σ.vars "p1" = p.l1) (hp2 : σ.vars "p2" = p.l2) (hnum : p.kk + p.d + p.l1 + p.l2 < M)
    (h1 : SegIs M σ "r1s" "r1l" R1) (h2 : SegIs M σ "r2s" "r2l" R2) (h3 : 3 + 1 < M) :
    ∃ σ' ob K, Run (W + 1) (seqs [asg "gp" (N 4), asg "cnt" (.add (V "cnt") (N 7)), emHd, emFr, emRest,
        patchL, emRe]) σ σ' K ∧
      Built j (.call ({ p with ph := 4 } :: S'') (.re (reQuery p (R1 ++ R2)))) ob σ' ∧
      ob.length ≤ 64 * M ∧ K ≤ 40 * ob.length + 1100 ∧ Keep σ σ' := by
  have hR := hC.room
  have hm := hC.m16
  obtain ⟨hn1, hn2, hn3, hn4, hn5, hn6⟩ := hg.nums
  set σ1 := σ.setVar "gp" 4
  set σ2 := σ1.setVar "cnt" (σ.vars "cnt" + 7)
  have hfl := length_le_frames (stWords S'')
  have hrl := hrest.2.1
  have r1 : Run (W + 1) (seqs [asg "gp" (N 4), asg "cnt" (.add (V "cnt") (N 7))]) σ σ2 8 :=
    (Run.seqs_cons (by simp) (Run.assign (by simp; omega))
      (Run.seqs_one (Run.assign (by simp [σ1]; omega)))).mono (by simp)
  have hx2 : σ2.arrs "x" = σ.arrs "x" := by simp [σ2, σ1]
  have hg2 : SlotIs M σ2 { p with ph := 4 } :=
    (hg.set_ph (show 4 < 2 * M by omega)).ofr (OFr.setVar σ1 "cnt" _) (by decide)
  have hC2 : Ctx W M σ2 := (hC.setVar (by decide) _).setVar (by decide) _
  have hF2 : Filled "OB" "po" [] σ2 := hF.congr (by simp [σ2, σ1]) (by simp [σ2, σ1])
  have hcnt2 : σ2.vars "cnt" = (stWords (({ p with ph := 4 } : Fr) :: S'')).length := by
    simp only [σ2, Env.setVar, if_pos rfl]; rw [hcnt, stWords_cons]; simp [frWords] <;> omega
  obtain ⟨σ3, K3, r3, F3, hl3, hK3, fr3⟩ := frameOut_run hC2 hF2 hg2
    (hrest.of_eq (by simp [σ2, σ1]) (by simp [σ2, σ1]) hx2) hcnt2 (by simp [σ2, σ1, hj1]) hjM
  have hC3 := hC2.ofr fr3 (by decide)
  have hv3 : ∀ y ∈ ["pk", "pd", "p1", "p2", "r1s", "r1l", "r2s", "r2l"], σ3.vars y = σ.vars y := by
    intro y hy
    rw [fr3.vars y (by simp at hy ⊢; rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    simp at hy
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [σ2, σ1]
  have hx3 : σ3.arrs "x" = σ.arrs "x" := by rw [fr3.arrs "x" (by decide), hx2]
  have h13 : SegIs M σ3 "r1s" "r1l" R1 := h1.of_eq (hv3 _ (by simp)) (hv3 _ (by simp)) hx3
  have h23 : SegIs M σ3 "r2s" "r2l" R2 := h2.of_eq (hv3 _ (by simp)) (hv3 _ (by simp)) hx3
  obtain ⟨σ4, r4, F4, hqa, hql, hsp, hdq, hqk, fr4⟩ := emRe_run hC3 F3
    (by rw [hv3 _ (by simp), hpk]; omega) (by rw [hv3 _ (by simp), hpd]; omega)
    (by rw [hv3 _ (by simp), hv3 _ (by simp), hp1, hp2]; omega) h13 h23 (by omega)
  have e : reW (σ3.vars "pk") (σ3.vars "pd") (σ3.vars "p1") (σ3.vars "p2") (R1 ++ R2) =
      reQuery { p with ph := 4 } (R1 ++ R2) := by
    rw [hv3 _ (by simp), hv3 _ (by simp), hv3 _ (by simp), hv3 _ (by simp), hpk, hpd, hp1, hp2]; rfl
  rw [e] at F4 hql hsp
  have hB := built_re (j := j) (S := ({ p with ph := 4 } : Fr) :: S'')
    (w := reQuery { p with ph := 4 } (R1 ++ R2)) F4 hsp hdq hqk hqa hql
  have hrq : reQuery { p with ph := 4 } (R1 ++ R2) = reQuery p (R1 ++ R2) := rfl
  rw [hrq] at hB
  have hwl : (reQuery p (R1 ++ R2)).length = 3 + R1.length + R2.length + 1 + (p.l1 + p.l2 + 1) := by
    simp [reQuery, jList]; omega
  have hR1 := h1.2.1
  have hR2 := h2.2.1
  refine ⟨σ4, _, 8 + (K3 + _), Run.seqs_app2 (a := [asg "gp" (N 4), asg "cnt" (.add (V "cnt") (N 7))])
    (by simp) (by simp) r1 (Run.seqs_app2 (a := [emHd, emFr, emRest, patchL]) (by simp) (by simp) r3
    (Run.seqs_one r4)), hB, ?_, ?_, ?_⟩
  · simp only [List.length_append, List.length_cons, List.length_nil]; omega
  · have hpp : σ3.vars "p1" + σ3.vars "p2" = p.l1 + p.l2 := by
      rw [hv3 "p1" (by simp), hv3 "p2" (by simp), hp1, hp2]
    generalize σ3.vars "p1" = a1 at hpp ⊢
    generalize σ3.vars "p2" = a2 at hpp ⊢
    simp only [List.length_append, List.length_cons, List.length_nil]
    generalize (hdS j (({ p with ph := 4 } : Fr) :: S'')).length = H at hK3 ⊢
    generalize (reQuery p (R1 ++ R2)).length = Q at hwl ⊢
    clear * - hK3 hwl hpp
    omega
  · exact (Keep.setVar σ (by decide) (by decide) (by decide) _).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      ((Keep.of_ofr fr3 (by decide) (by decide) (by decide)).trans
      (Keep.of_ofr fr4 (by decide) (by decide) (by decide))))


theorem ExIs.seg0 {M : ℕ} {σ : Env} {EX : List (List ℕ)} (h : ExIs M σ EX) (h0 : σ.vars "gx" = 0) :
    SegIs M σ "gEs" "gEl" (toWord EX) := by
  rcases h with ⟨-, h⟩ | ⟨h1, -⟩
  · exact h
  · omega

theorem getElem_of_drop_cons {X r : List ℕ} {y a : ℕ} {e : List ℕ} (h : X.drop y = (a :: e) ++ r) :
    X[y]? = some a := by
  have := congrArg (fun l => l[0]?) h
  simpa using this

/-- Advancing the parent `p` past its current extension of `B`, with the
result `R₁ ++ R₂` as its new last extension. -/
theorem retAdv_run {W M j h T : ℕ} {σ : Env} {p : Fr} {S'' : List Fr} {R1 R2 : List ℕ}
    (hC : Ctx W M σ) (hF : Filled "OB" "po" [] σ) (hg : SlotIs M σ p) (hgx : σ.vars "gx" = 0)
    (hrest : SegIs M σ "rS" "rL" (frames (stWords S''))) (hcnt : σ.vars "cnt" = (stWords S'').length)
    (hj1 : σ.vars "j1" = j) (hjM : j < M) (hnA : σ.vars "nA" = nA p) (hi : ¬ p.i < nA p)
    (hi2 : p.i < nA p + nB p) (hdh : p.d = h + 1) (tA : Node (h + 1) p.l1) (tB : Node (h + 1) p.l2)
    (hA : p.A = toWord tA) (hB : p.B = toWord tB) (hSA : NW h p.l1 p.SA)
    (hnum : p.kk + p.l1 + p.l2 + 2 < M) (hpi : p.i + 1 < 2 * M) (hT : (toWord tB).length ≤ T)
    (h1 : SegIs M σ "r1s" "r1l" R1) (h2 : SegIs M σ "r2s" "r2l" R2) :
    ∃ σ' ob K, Run (W + 1) (seqs [extsAt "gBs" "nB", asg "u" (.sub (V "gi") (V "nA")), extFr "u",
        asg "gg" (.add (V "g1") (X (.add (V "y") (N 1)))), asg "gx" (N 1),
        asg "gi" (.add (V "gi") (N 1)), advCmd]) σ σ' K ∧
      Built j (ret (R1 ++ R2) [σ.vars "hk", σ.vars "hd", σ.vars "hl"] (p :: S'')) ob σ' ∧
      ob.length ≤ 64 * M ∧ K ≤ 300 * ob.length + 60 * T + 5300 ∧ Keep σ σ' := by
  have hR := hC.room
  have hm := hC.m16
  obtain ⟨hn1, hn2, hn3, hn4, hn5, hn6⟩ := hg.nums
  have hBs := hg.B
  rw [hB] at hBs
  obtain ⟨σ1, r1, hy1, hnB1, hx1, fr1⟩ := extsAt_run (s := "gBs") (cnt := "nB") (by decide) hC tB
    (hBs.drop_eq) hBs.2.1
  set ws := (Node.exts tB).words with hws
  have hnBp : nB p = ws.length := by simp [nB, hB, extsOf_node, hws]
  have hu : p.i - nA p < ws.length := by omega
  have hv1 : ∀ z ∈ slotVars, σ1.vars z = σ.vars z := fun z hz => fr1.vars z (by
    intro hz'; simp at hz'; rcases hz' with rfl | rfl | rfl | rfl <;> exact absurd hz (by decide))
  have hx1' : σ1.arrs "x" = σ.arrs "x" := fr1.arrs "x" (by decide)
  set σ2 := σ1.setVar "u" (p.i - nA p)
  have r2 : Run (W + 1) (asg "u" (.sub (V "gi") (V "nA"))) σ1 σ2 4 := by
    have e1 : σ1.vars "gi" = p.i := by rw [hv1 _ (by decide), hg.i]
    have e2 : σ1.vars "nA" = nA p := by rw [fr1.vars _ (by decide), hnA]
    exact (Run.assign (by simp [e1, e2]; omega)).mono (by simp)
  have hC2 : Ctx W M σ2 := (hC.ofr fr1 (by decide)).setVar (by decide) _
  have htB : (toWord tB).length = (toWord (Node.atoms tB).words).length + (toWord ws).length := by
    rw [toWord_node_succ, List.length_append]
  obtain ⟨σ3, r3, hy3, hxg3, hdrop3, hle3, fr3⟩ := extFr_run (k := "u") (by decide) hC2 (ws := ws)
    (r := (σ.arrs "x").drop (σ.vars "gBs" + (toWord tB).length))
    (by simp only [σ2, Env.setVar]; rw [hx1']; simpa using hx1)
    (by simp [σ2]; exact hu) (by simp [σ2]; have := hBs.2.1; omega)
  have hu2 : σ2.vars "u" = p.i - nA p := by simp [σ2]
  simp only [hu2] at hxg3 hdrop3 hle3
  set e := ws[p.i - nA p]'hu with he
  obtain ⟨ε, -, hε⟩ := extsOf_getD tB (j := p.i - nA p) hu
  have hge : (extsOf p.B).getD (p.i - nA p) [] = e := by
    rw [hB, extsOf_node, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu]; rfl
  have hee : e = ε.1.val :: toWord ε.2 := by rw [← hge, hB, hε]
  have hx3 : σ3.arrs "x" = σ.arrs "x" := by rw [fr3.arrs "x" (by decide)]; simp [σ2, hx1']
  set y3 := σ3.vars "y"
  have hget : (σ.arrs "x")[y3 + 1]? = some ε.1.val := by
    have hd : (σ.arrs "x").drop (y3 + 1) = (ε.1.val :: toWord ε.2) ++
        (frames (ws.drop (p.i - nA p + 1)) ++ (σ.arrs "x").drop (σ.vars "gBs" + (toWord tB).length)) := by
      rw [← hee]; simpa [σ2, hx1'] using hdrop3
    exact getElem_of_drop_cons hd
  have hεM : ε.1.val < M := hC.xv _ (List.mem_of_getElem? hget)
  have hy3M : y3 + 1 < W + 1 := by
    have e2 : σ2.vars "y" = σ1.vars "y" := by simp [σ2]
    have := hBs.2.1
    clear * - hle3 e2 hy1 htB this hR
    omega
  set gg := p.l1 + ε.1.val
  set σ4 := σ3.setVar "gg" gg
  set σ5 := σ4.setVar "gx" 1
  set σ6 := σ5.setVar "gi" (p.i + 1)
  have hv3 : ∀ z ∈ slotVars, σ3.vars z = σ.vars z := fun z hz => by
    rw [fr3.vars z (by intro hz'; simp at hz'; rcases hz' with rfl | rfl <;> exact absurd hz (by decide))]
    have : z ≠ "u" := fun e => by subst e; exact absurd hz (by decide)
    simp [σ2, this, hv1 z hz]
  have r4 : Run (W + 1) (seqs [asg "gg" (.add (V "g1") (X (.add (V "y") (N 1)))), asg "gx" (N 1),
      asg "gi" (.add (V "gi") (N 1))]) σ3 σ6 16 := by
    have e1 : σ3.vars "g1" = p.l1 := by rw [hv3 _ (by decide), hg.l1]
    have hgetE : (Expr.get "x" (.add (V "y") (N 1))).evalB (W + 1) σ3 = some ε.1.val :=
      evalB_get (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega))
        (by rw [hx3]; simpa using hget) (by omega)
    have hgg : (Expr.add (V "g1") (X (.add (V "y") (N 1)))).evalB (W + 1) σ3 = some gg := by
      rw [show gg = Bop.add.apply (σ3.vars "g1") ε.1.val by simp [e1, gg]]
      exact evalB_bin (evalB_var (by rw [e1]; omega)) hgetE (by simp [e1]; omega)
    refine (Run.seqs_cons (by simp) (Run.assign hgg) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ4]; omega)) (Run.seqs_one (Run.assign (by
        simp [σ5, σ4, hv3 "gi" (by decide), hg.i]; omega))))).mono (by simp)
  set g : Fr := { p with i := p.i + 1, EX := p.EX ++ [gg :: (R1 ++ R2)] } with hgdef
  have hx6 : σ6.arrs "x" = σ.arrs "x" := by simp [σ6, σ5, σ4, hx3]
  have hv6 : ∀ z ∈ slotVars, z ∉ ["gg", "gx", "gi"] → σ6.vars z = σ.vars z := by
    intro z hz hz'
    have : z ≠ "gg" ∧ z ≠ "gx" ∧ z ≠ "gi" := by simpa using hz'
    simp [σ6, σ5, σ4, this.1, this.2.1, this.2.2, hv3 z hz]
  have hg6 : SlotIs M σ6 g := by
    refine hg.upd ["gg", "gx", "gi"] hv6 hx6 (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
      (Or.inr rfl) (Or.inl (by decide)) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
      (Or.inl ⟨"gx", by decide, by decide⟩) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun _ => by simp [σ6, hgdef]) ⟨hn1, hn2, hn3, hn4, hn5, hpi⟩
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun _ => ?_)
    have hE0 := (hg.EX.seg0 hgx).of_eq (hv6 _ (by decide) (by decide)) (hv6 _ (by decide) (by decide)) hx6
    refine Or.inr ⟨by simp [σ6, σ5], by simp [σ6, σ5, σ4]; omega, p.EX, R1, R2,
      by simp [σ6, σ5, σ4, hgdef], hE0,
      h1.of_eq (hv6 _ (by decide) (by decide)) (hv6 _ (by decide) (by decide)) hx6,
      h2.of_eq (hv6 _ (by decide) (by decide)) (hv6 _ (by decide) (by decide)) hx6⟩
  have hfr6 : ∀ z ∉ ["y", "sn", "sk", "nB", "u", "gg", "gx", "gi"], σ6.vars z = σ.vars z := by
    intro z hz
    have : z ≠ "gg" ∧ z ≠ "gx" ∧ z ≠ "gi" ∧ z ≠ "u" ∧ z ≠ "y" ∧ z ≠ "sk" := by simp at hz; tauto
    simp only [σ6, σ5, σ4, Env.setVar, if_neg this.1, if_neg this.2.1, if_neg this.2.2.1]
    rw [fr3.vars z (by simp; tauto)]
    simp only [σ2, Env.setVar, if_neg this.2.2.2.1]
    exact fr1.vars z (by simp at hz ⊢; tauto)
  have hC6 : Ctx W M σ6 :=
    (((((hC.ofr fr1 (by decide)).setVar (by decide) _).ofr fr3 (by decide)).setVar (by decide) _).setVar
      (by decide) _).setVar (by decide) _
  have hF6 : Filled "OB" "po" [] σ6 :=
    ⟨by rw [hfr6 _ (by decide), hF.pos], fun i h => absurd h (by simp)⟩
  obtain ⟨σ7, ob, K7, r7, B7, hl7, hK7, kp7⟩ := advCmd_run (g := g) (Sr := S'') (j := j) (h := h) hC6 hF6
    hg6 (hrest.of_eq (hfr6 _ (by decide)) (hfr6 _ (by decide)) hx6)
    (by rw [hfr6 _ (by decide), hcnt]) (by rw [hfr6 _ (by decide), hj1]) hjM hdh tA tB hA hB
    (fun hlt => (hi (by have : g.i = p.i + 1 := rfl; have : nA g = nA p := rfl; omega)).elim)
    (fun _ _ => hSA) hnum
  have hret : ret (R1 ++ R2) [σ.vars "hk", σ.vars "hd", σ.vars "hl"] (p :: S'') = advance g S'' := by
    rw [ret_ge _ _ _ _ hi, hge, hee]; rfl
  have hwsl : ws.length < (toWord ws).length := count_lt_toWord ws
  refine ⟨σ7, ob, _, Run.seqs_cons (by simp) r1 (Run.seqs_cons (by simp) r2 (Run.seqs_cons (by simp) r3
    (Run.seqs_app2 (a := [asg "gg" (.add (V "g1") (X (.add (V "y") (N 1)))), asg "gx" (N 1),
      asg "gi" (.add (V "gi") (N 1))]) (by simp) (by simp) r4 (Run.seqs_one r7)))), by rw [hret]; exact B7,
    hl7, by omega, ?_⟩
  exact (Keep.of_ofr fr1 (by decide) (by decide) (by decide)).trans
    ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
    ((Keep.of_ofr fr3 (by decide) (by decide) (by decide)).trans
    ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
    ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
    ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans kp7)))))


/-- The scalars that `ret_run` needs. -/
structure TopR (W M j : ℕ) (f : Fr) (S' : List Fr) (σ : Env) : Prop where
  ctx : Ctx W M σ
  x4 : ∀ v ∈ σ.arrs "x", 4 * v + 4 < M
  hx : ∃ r, (σ.arrs "x").drop 2 = toWord (stWords (f :: S')) ++ r
  hp : 2 + (toWord (stWords (f :: S'))).length ≤ M
  F : Filled "OB" "po" [] σ
  j1 : σ.vars "j1" = j + 1
  jM : j + 1 < M
  n : σ.vars "n" = (stWords (f :: S')).length
  L : σ.vars "L" = 2 + (toWord (stWords (f :: S'))).length
  wp : ∀ i < min (stWords (f :: S')).length 14,
    (σ.arrs "wp").getD i 0 = frPos (σ.arrs "x") 2 i

theorem TopR.setVar {W M j : ℕ} {f : Fr} {S' : List Fr} {σ : Env} (h : TopR W M j f S' σ) {y : String}
    (hy : y ∉ ["W", "po", "j1", "n", "L"]) (v : ℕ) : TopR W M j f S' (σ.setVar y v) := by
  have h1 : y ≠ "W" ∧ y ≠ "po" ∧ y ≠ "j1" ∧ y ≠ "n" ∧ y ≠ "L" := by simpa using hy
  exact ⟨h.ctx.setVar h1.1 v, by simpa using h.x4, by simpa using h.hx, h.hp,
    h.F.setVar h1.2.1 v, by simp [Ne.symm h1.2.2.1, h.j1], h.jM, by simp [Ne.symm h1.2.2.2.1, h.n],
    by simp [Ne.symm h1.2.2.2.2, h.L], by simpa using h.wp⟩

theorem Top.toR {W M j : ℕ} {f : Fr} {S' : List Fr} {b : List ℕ} {σ : Env} (h : Top W M j f S' b σ) :
    TopR W M j f S' σ := ⟨h.ctx, h.x4, h.hx, h.hp, h.F, h.j1, h.jM, h.n, h.L, h.wp⟩

/-- The numbers of a frame of the stack are entries of `x`. -/
theorem nums_mem {X r : List ℕ} {S : List Fr} (hx : X.drop 2 = toWord (stWords S) ++ r) {g : Fr}
    (hg : g ∈ S) : ∀ v ∈ [g.d, g.kk, g.l1, g.l2, g.ph, g.i], v ∈ X := by
  intro v hv
  have h1 : [g.d, g.kk, g.l1, g.l2, g.ph, g.i] ∈ stWords S := by
    simp only [stWords, List.mem_flatten, List.mem_map]
    exact ⟨_, ⟨g, hg, rfl⟩, by simp [frWords]⟩
  have h2 := mem_toWord_of_mem h1 hv
  have h3 : v ∈ X.drop 2 := by rw [hx]; exact List.mem_append_left _ h2
  exact List.mem_of_mem_drop h3

theorem condEq_var_lit {B : ℕ} {σ : Env} {x : String} {a n : ℕ} (hx : σ.vars x = a) (ha : a < B)
    (hn : n < B) : (Cond.eq (V x) (N n)).evalB B σ = some (a == n) := by
  rw [← hx]; exact evalB_condEq (evalB_var (by omega)) (evalB_lit hn)

theorem condLt_var_var {B : ℕ} {σ : Env} {x y : String} {a c : ℕ} (hx : σ.vars x = a)
    (hy : σ.vars y = c) (ha : a < B) (hc : c < B) :
    (Cond.lt (V x) (V y)).evalB B σ = some (decide (a < c)) := by
  rw [← hx, ← hy]; exact evalB_condLt (evalB_var (by omega)) (evalB_var (by omega))

/-- The facts after loading the parent `p` in `retCmd`. -/
structure PreOut (W M j : ℕ) (p : Fr) (S'' : List Fr) (R1 R2 : List ℕ) (σ σ7 : Env) : Prop where
  ctx : Ctx W M σ7
  F : Filled "OB" "po" [] σ7
  slot : SlotIs M σ7 p
  gx : σ7.vars "gx" = 0
  rest : SegIs M σ7 "rS" "rL" (frames (stWords S''))
  cnt : σ7.vars "cnt" = (stWords S'').length
  j1 : σ7.vars "j1" = j + 1
  nA : σ7.vars "nA" = nA p
  pk : σ7.vars "pk" = p.kk
  pd : σ7.vars "pd" = p.d
  p1 : σ7.vars "p1" = p.l1
  p2 : σ7.vars "p2" = p.l2
  r1 : SegIs M σ7 "r1s" "r1l" R1
  r2 : SegIs M σ7 "r2s" "r2l" R2
  hk : [σ7.vars "hk", σ7.vars "hd", σ7.vars "hl"] = [σ.vars "hk", σ.vars "hd", σ.vars "hl"]
  keep : Keep σ σ7

/-- Loading the parent `p` in `retCmd`. -/
theorem retPre_run {W M j hh : ℕ} {σ : Env} {f p : Fr} {S'' : List Fr} {R1 R2 : List ℕ}
    (h : TopR W M j f (p :: S'') σ) (hdh : p.d = hh + 1) (tA : Node (hh + 1) p.l1) (hA : p.A = toWord tA)
    (h1 : SegIs M σ "r1s" "r1l" R1) (h2 : SegIs M σ "r2s" "r2l" R2) :
    ∃ σ7, Run (W + 1) (seqs [ldG 7, asg "pk" (V "gk"), asg "pd" (V "gd"), asg "p1" (V "g1"),
        asg "p2" (V "g2"), ldRest 2, extsAt "gAs" "nA"]) σ σ7
        (300 + (8 + (50 + (40 * (toWord tA).length + 80)))) ∧ PreOut W M j p S'' R1 R2 σ σ7 := by
  have hC := h.ctx
  have hR := hC.room
  have hm := hC.m16
  obtain ⟨r, hx⟩ := h.hx
  have hn := h.n
  have hlw : (stWords (f :: p :: S'')).length = 14 + (stWords S'').length := by
    rw [stWords_cons, stWords_cons]; simp [frWords]; omega
  have hpn := nums_mem hx (g := p) (by simp)
  have hx4 := h.x4
  have q1 := hx4 _ (hpn p.d (by simp)); have q2 := hx4 _ (hpn p.kk (by simp))
  have q3 := hx4 _ (hpn p.l1 (by simp)); have q4 := hx4 _ (hpn p.l2 (by simp))
  obtain ⟨σ1, r1, hg1, hgx1, fr1⟩ := ldG_run hC hx h.hp 7 p (by omega)
    (by rw [stWords_drop7, stWords_take7])
    (fun i hi => h.wp i (by omega))
  set σ2 := σ1.setVar "pk" p.kk
  set σ3 := σ2.setVar "pd" p.d
  set σ4 := σ3.setVar "p1" p.l1
  set σ5 := σ4.setVar "p2" p.l2
  have ra : Run (W + 1) (seqs [asg "pk" (V "gk"), asg "pd" (V "gd"), asg "p1" (V "g1"),
      asg "p2" (V "g2")]) σ1 σ5 8 :=
    (Run.seqs_cons (by simp) (Run.assign (by simp [hg1.kk]; omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ2, hg1.d]; omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ3, σ2, hg1.l1]; omega))
      (Run.seqs_one (Run.assign (by simp [σ4, σ3, σ2, hg1.l2]; omega)))))).mono (by simp)
  have fr5 : OFr σ1 σ5 ["pk", "pd", "p1", "p2"] :=
    ((((OFr.setVar σ1 "pk" _).trans (OFr.setVar σ2 "pd" _)).trans
      (OFr.setVar σ3 "p1" _)).trans (OFr.setVar σ4 "p2" _))
  have fr15 := fr1.trans fr5
  have hx5 : σ5.arrs "x" = σ.arrs "x" := fr15.arrs "x" (by decide)
  have hwp5 : σ5.arrs "wp" = σ.arrs "wp" := fr15.arrs "wp" (by decide)
  have hC5 : Ctx W M σ5 := hC.ofr fr15 (by decide)
  have hg5 : SlotIs M σ5 p := hg1.ofr fr5 (by decide)
  obtain ⟨σ6, r6, hrest6, hcnt6, fr6⟩ := ldRest_run hC5 (by rw [hx5]; exact hx) h.hp 2 (by omega)
    (by omega) (by rw [fr15.vars "L" (by decide), h.L]) (by rw [fr15.vars "n" (by decide), hn])
    (by rw [hwp5, hx5]; exact h.wp 13 (by omega))
  have hdrop : (stWords (f :: p :: S'')).drop (7 * 2) = stWords S'' := by
    rw [show 7 * 2 = 7 + 7 by rfl, ← List.drop_drop, stWords_drop7, stWords_drop7]
  rw [hdrop] at hrest6
  have hC6 := hC5.ofr fr6 (by decide)
  have hg6 := hg5.ofr fr6 (by decide)
  have hAs := hg6.A
  rw [hA] at hAs
  obtain ⟨σ7, r7, -, hnA7, -, fr7⟩ := extsAt_run (s := "gAs") (cnt := "nA") (by decide) hC6 tA
    hAs.drop_eq hAs.2.1
  have fr := (fr15.trans fr6).trans fr7
  have hnAp : nA p = (Node.exts tA).words.length := by simp [nA, hA, extsOf_node]
  have hx7 : σ7.arrs "x" = σ.arrs "x" := fr.arrs "x" (by decide)
  refine ⟨σ7, Run.seqs_cons (by simp) r1 (Run.seqs_app2 (a := [asg "pk" (V "gk"), asg "pd" (V "gd"),
      asg "p1" (V "g1"), asg "p2" (V "g2")]) (by simp) (by simp) ra
      (Run.seqs_cons (by simp) r6 (Run.seqs_one r7))), hC6.ofr fr7 (by decide),
    ⟨by rw [fr.vars "po" (by decide), h.F.pos], fun i hi => absurd hi (by simp)⟩,
    hg6.ofr fr7 (by decide), by rw [fr7.vars "gx" (by decide), fr6.vars "gx" (by decide),
      fr5.vars "gx" (by decide), hgx1],
    hrest6.ofr fr7 (by decide) (by decide), by rw [fr7.vars "cnt" (by decide), hcnt6]; omega,
    by rw [fr.vars "j1" (by decide), h.j1], by rw [hnA7, hnAp],
    by rw [fr7.vars "pk" (by decide), fr6.vars "pk" (by decide)]; simp [σ5, σ4, σ3, σ2],
    by rw [fr7.vars "pd" (by decide), fr6.vars "pd" (by decide)]; simp [σ5, σ4, σ3],
    by rw [fr7.vars "p1" (by decide), fr6.vars "p1" (by decide)]; simp [σ5, σ4],
    by rw [fr7.vars "p2" (by decide), fr6.vars "p2" (by decide)]; simp [σ5],
    h1.of_eq (fr.vars "r1s" (by decide)) (fr.vars "r1l" (by decide)) hx7,
    h2.of_eq (fr.vars "r2s" (by decide)) (fr.vars "r2l" (by decide)) hx7,
    by rw [fr.vars "hk" (by decide), fr.vars "hd" (by decide), fr.vars "hl" (by decide)],
    Keep.of_ofr fr (by decide) (by decide) (by decide)⟩

/-- Handing the result down to the parent `p`. -/
theorem retPar_run {W M j : ℕ} {σ : Env} {f p : Fr} {S'' : List Fr} {R1 R2 : List ℕ} (P : SzP)
    (h : TopR W M j f (p :: S'') σ) (hfok : FOK P p) (hph3 : p.ph = 3)
    (h1 : SegIs M σ "r1s" "r1l" R1) (h2 : SegIs M σ "r2s" "r2l" R2) :
    ∃ σ' ob K, Run (W + 1) retCmd σ σ' K ∧
      Built (j + 1) (ret (R1 ++ R2) [σ.vars "hk", σ.vars "hd", σ.vars "hl"] (p :: S'')) ob σ' ∧
      ob.length ≤ 64 * M ∧
      K ≤ 300 * ob.length + 500 * (toWord (stWords (f :: p :: S''))).length + 7000 ∧ Keep σ σ' := by
  have hC := h.ctx
  have hR := hC.room
  have hm := hC.m16
  obtain ⟨r, hx⟩ := h.hx
  have hn := h.n
  have hdp : 1 ≤ p.d := hfok.hd (by omega)
  obtain ⟨hh, hdh⟩ : ∃ hh, p.d = hh + 1 := ⟨p.d - 1, by omega⟩
  have hNA := hfok.A.1
  have hNB := hfok.B.1
  rw [hdh] at hNA hNB
  obtain ⟨tA, hA⟩ := hNA
  obtain ⟨tB, hB⟩ := hNB
  have hSA := (hfok.SA (by omega)).1
  rw [hdh, show hh + 1 - 1 = hh by omega] at hSA
  have hi34 := hfok.i34 (Or.inl hph3)
  have hlw : (stWords (f :: p :: S'')).length = 14 + (stWords S'').length := by
    rw [stWords_cons, stWords_cons]; simp [frWords]; omega
  have hcw := count_lt_toWord (stWords (f :: p :: S''))
  have hhp := h.hp
  have hpn := nums_mem hx (g := p) (by simp)
  have hx4 := h.x4
  have q1 := hx4 _ (hpn p.d (by simp)); have q2 := hx4 _ (hpn p.kk (by simp))
  have q3 := hx4 _ (hpn p.l1 (by simp)); have q4 := hx4 _ (hpn p.l2 (by simp))
  have q6 := hx4 _ (hpn p.i (by simp))
  have hpA : p.A ∈ stWords (f :: p :: S'') := by rw [stWords_cons, stWords_cons]; simp [frWords]
  have hpB : p.B ∈ stWords (f :: p :: S'') := by rw [stWords_cons, stWords_cons]; simp [frWords]
  have lA := length_le_toWord hpA
  have lB := length_le_toWord hpB
  obtain ⟨σ7, hpre, ho⟩ := retPre_run h hdh tA hA h1 h2
  have hgi7 : σ7.vars "gi" = p.i := ho.slot.i
  have hnA_le : nA p < W + 1 := by
    have hAs := ho.slot.A
    have := extsOf_count (show NW (hh + 1) p.l1 p.A from ⟨tA, hA⟩)
    have := hAs.2.1
    simp only [nA]; omega
  have hn7 : ¬ ((stWords (f :: p :: S'')).length == 7) = true := by simp; omega
  have htA : (toWord tA).length = p.A.length := by rw [hA]
  by_cases hi : p.i < nA p
  · obtain ⟨σ8, ob, K8, r8, B8, hl8, hK8, kp8⟩ := retRe_run ho.ctx ho.F ho.slot ho.rest ho.cnt ho.j1 h.jM
      ho.pk ho.pd ho.p1 ho.p2 (by omega) ho.r1 ho.r2 (by omega)
    refine ⟨σ8, ob, _, Run.ite_false (by rw [condEq_var_lit hn (by omega) (by omega)]; simpa using hn7)
      (Run.seqs_app2 (a := [ldG 7, asg "pk" (V "gk"), asg "pd" (V "gd"), asg "p1" (V "g1"),
        asg "p2" (V "g2"), ldRest 2, extsAt "gAs" "nA"]) (by simp) (by simp) hpre
        (Run.seqs_one (Run.ite_true (by rw [condLt_var_var hgi7 ho.nA (by omega) hnA_le]; simpa using hi)
          r8))), by rw [ret_lt _ _ _ _ hi]; exact B8, hl8, ?_, ho.keep.trans kp8⟩
    simp only [Cond.size, Expr.size]
    clear * - hK8 htA lA
    omega
  · obtain ⟨σ8, ob, K8, r8, B8, hl8, hK8, kp8⟩ := retAdv_run (j := j + 1) (h := hh)
      (T := (toWord (stWords (f :: p :: S''))).length) ho.ctx ho.F ho.slot ho.gx ho.rest ho.cnt ho.j1
      h.jM ho.nA hi hi34 hdh tA tB hA hB hSA (by omega) (by omega) (by rw [← hB]; exact le_of_lt lB)
      ho.r1 ho.r2
    rw [ho.hk] at B8
    refine ⟨σ8, ob, _, Run.ite_false (by rw [condEq_var_lit hn (by omega) (by omega)]; simpa using hn7)
      (Run.seqs_app2 (a := [ldG 7, asg "pk" (V "gk"), asg "pd" (V "gd"), asg "p1" (V "g1"),
        asg "p2" (V "g2"), ldRest 2, extsAt "gAs" "nA"]) (by simp) (by simp) hpre
        (Run.seqs_one (Run.ite_false (by rw [condLt_var_var hgi7 ho.nA (by omega) hnA_le]; simpa using hi)
          r8))), B8, hl8, ?_, ho.keep.trans kp8⟩
    simp only [Cond.size, Expr.size]
    clear * - hK8 htA lA
    omega

theorem condLt_var_lit_eq {B : ℕ} {σ : Env} {x : String} {a n : ℕ} (hx : σ.vars x = a) (ha : a < B)
    (hn : n < B) : (Cond.lt (V x) (N n)).evalB B σ = some (decide (a < n)) := by
  rw [← hx]; exact evalB_condLt (evalB_var (by omega)) (evalB_lit hn)

/-- **Handing the result down.** -/
theorem ret_run {W M j : ℕ} {σ : Env} {f : Fr} {S' : List Fr} {R1 R2 : List ℕ} (P : SzP)
    (h : TopR W M j f S' σ) (hpar : ∀ p S'', S' = p :: S'' → FOK P p ∧ p.ph = 3)
    (h1 : SegIs M σ "r1s" "r1l" R1) (h2 : SegIs M σ "r2s" "r2l" R2) (hk : σ.vars "hk" < 2 * M)
    (hd : σ.vars "hd" < 2 * M) (hl : σ.vars "hl" < 2 * M) :
    ∃ σ' ob K, Run (W + 1) retCmd σ σ' K ∧
      Built (j + 1) (ret (R1 ++ R2) [σ.vars "hk", σ.vars "hd", σ.vars "hl"] S') ob σ' ∧
      ob.length ≤ 64 * M ∧ K ≤ 300 * ob.length + 500 * (toWord (stWords (f :: S'))).length + 7000 ∧
      Keep σ σ' := by
  have hC := h.ctx
  have hR := hC.room
  have hm := hC.m16
  obtain ⟨r, hx⟩ := h.hx
  set ws := stWords (f :: S') with hws
  have hn := h.n
  cases S' with
  | nil =>
    have h7 : ws.length = 7 := by rw [hws, length_stWords]; rfl
    obtain ⟨σ', r1, F1, hsp, hdq, hqk, fr1⟩ := emDone_run hC h.F hk hd hl h1 h2 (by simp; omega)
    have e : [] ++ [0, σ.vars "hk", σ.vars "hd", σ.vars "hl"] ++ R1 ++ R2 =
        0 :: ([σ.vars "hk", σ.vars "hd", σ.vars "hl"] ++ R1 ++ R2) := by simp
    rw [e] at F1
    have hB := built_done (j := j + 1) F1 (by rw [hsp]; simp; omega) hdq hqk
    have hR1 := h1.2.1
    have hR2 := h2.2.1
    refine ⟨σ', _, _, Run.ite_true (by rw [condEq_var_lit (a := 7) (by rw [hn]; exact h7) (by omega) (by omega)]; rfl)
      r1, by simpa [ret] using hB, by simp; omega, by simp; omega,
      Keep.of_ofr fr1 (by decide) (by decide) (by decide)⟩
  | cons p S'' =>
    exact retPar_run P h (hpar p S'' rfl).1 (hpar p S'' rfl).2 h1 h2


/-- The phase `5`: hand `AT ++ b` down. -/
theorem ph5_run {W M j : ℕ} {σ : Env} {f : Fr} {S' : List Fr} {b : List ℕ} (P : SzP)
    (h : Top W M j f S' b σ) (hph : f.ph = 5) (hpar : ∀ p S'', S' = p :: S'' → FOK P p ∧ p.ph = 3) :
    ∃ σ' ob K, Run (W + 1) ph5Cmd σ σ' K ∧ Built (j + 1) (round (f :: S') b) ob σ' ∧
      ob.length ≤ 64 * M ∧ K ≤ 300 * ob.length + 500 * (toWord (stWords (f :: S'))).length + 7100 ∧
      Keep σ σ' := by
  have hC := h.ctx
  have hR := hC.room
  have hm := hC.m16
  have hg := h.slot
  obtain ⟨r, hx⟩ := h.hx
  have hpn := nums_mem hx (g := f) (by simp)
  have q2 := h.x4 _ (hpn f.kk (by simp)); have q1 := h.x4 _ (hpn f.d (by simp))
  have q3 := h.x4 _ (hpn f.l1 (by simp)); have q4 := h.x4 _ (hpn f.l2 (by simp))
  obtain ⟨u1, u2, -⟩ := hg.AT
  obtain ⟨b1, b2, -⟩ := h.bseg
  set σ1 := σ.setVar "hk" f.kk
  set σ2 := σ1.setVar "hd" f.d
  set σ3 := σ2.setVar "hl" (f.l1 + f.l2)
  set σ4 := σ3.setVar "r1s" (σ.vars "gUs")
  set σ5 := σ4.setVar "r1l" (σ.vars "gUl")
  set σ6 := σ5.setVar "r2s" (σ.vars "bs")
  set σ7 := σ6.setVar "r2l" (σ.vars "bl")
  have ra : Run (W + 1) (seqs [asg "hk" (V "gk"), asg "hd" (V "gd"), asg "hl" (.add (V "g1") (V "g2")),
      asg "r1s" (V "gUs"), asg "r1l" (V "gUl"), asg "r2s" (V "bs"), asg "r2l" (V "bl")]) σ σ7 16 :=
    (Run.seqs_cons (by simp) (Run.assign (by simp [hg.kk]; omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ1, hg.d]; omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ2, σ1, hg.l1, hg.l2]; omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ3, σ2, σ1]; omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ4, σ3, σ2, σ1]; omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ5, σ4, σ3, σ2, σ1]; omega))
      (Run.seqs_one (Run.assign (by simp [σ6, σ5, σ4, σ3, σ2, σ1]; omega))))))))).mono (by simp)
  have hx7 : σ7.arrs "x" = σ.arrs "x" := by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1]
  have hR7 : TopR W M j f S' σ7 :=
    ((((((h.toR.setVar (by decide) _).setVar (by decide) _).setVar (by decide) _).setVar (by decide) _).setVar
      (by decide) _).setVar (by decide) _).setVar (by decide) _
  have h17 : SegIs M σ7 "r1s" "r1l" f.AT := by
    obtain ⟨a1, a2, a3⟩ := hg.AT
    exact segIs_of (a := σ.vars "gUs") (by simp [σ7, σ6, σ5, σ4]) (by simp [σ7, σ6, σ5, a1]) a2
      (by rw [hx7]; exact a3)
  have h27 : SegIs M σ7 "r2s" "r2l" b := by
    obtain ⟨a1, a2, a3⟩ := h.bseg
    exact segIs_of (a := σ.vars "bs") (by simp [σ7, σ6]) (by simp [σ7, a1]) a2 (by rw [hx7]; exact a3)
  obtain ⟨σ8, ob, K8, r8, B8, hl8, hK8, kp8⟩ := ret_run P hR7 hpar h17 h27
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1]; omega) (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1]; omega)
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1]; omega)
  have e : [σ7.vars "hk", σ7.vars "hd", σ7.vars "hl"] = [f.kk, f.d, f.l1 + f.l2] := by
    simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1]
  rw [e] at B8
  refine ⟨σ8, ob, _, Run.seqs_app2 (a := [asg "hk" (V "gk"), asg "hd" (V "gd"),
      asg "hl" (.add (V "g1") (V "g2")), asg "r1s" (V "gUs"), asg "r1l" (V "gUl"), asg "r2s" (V "bs"),
      asg "r2l" (V "bl")]) (by simp) (by simp) ra (Run.seqs_one r8),
    by rw [round_ph5 f S' b hph]; exact B8, hl8, by omega, ?_⟩
  exact (Keep.setVar σ (by decide) (by decide) (by decide) _).trans
    ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
    ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
    ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
    ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
    ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
    ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans kp8))))))

/-- The phase `0` at positive depth: ask for the rank shift of `B`. -/
theorem ph0s_run {W M j : ℕ} {σ : Env} {f : Fr} {S' : List Fr} {b : List ℕ}
    (h : Top W M j f S' b σ) (hph : f.ph = 0) (hd0 : f.d ≠ 0) :
    ∃ σ' ob K, Run (W + 1) (seqs [asg "gp" (N 1), asg "gUs" (V "bs"), asg "gUl" (V "bl"),
      asg "cnt" (.add (V "cnt") (N 7)), emHd, emFr, emRest, patchL, asg "hk" (V "gk"), asg "hd" (V "gd"),
      asg "hl" (V "g2"), asg "hs" (V "gBs"), asg "hw" (V "gBl"), emSh]) σ σ' K ∧ Built (j + 1) (round (f :: S') b) ob σ' ∧
      ob.length ≤ 64 * M ∧ K ≤ 20 * ob.length + 1000 ∧ Keep σ σ' := by
  have hC := h.ctx
  have hR := hC.room
  have hg := h.slot
  have hm := hC.m16
  obtain ⟨hn1, hn2, hn3, hn4, hn5, hn6⟩ := hg.nums
  set σ1 := σ.setVar "gp" 1
  set σ2 := σ1.setVar "gUs" (σ.vars "bs")
  set σ3 := σ2.setVar "gUl" (σ.vars "bl")
  set σ4 := σ3.setVar "cnt" (σ.vars "cnt" + 7)
  have hbs := h.bseg
  obtain ⟨hbl, hbM, -⟩ := hbs
  have r1 : Run (W + 1) (seqs [asg "gp" (N 1), asg "gUs" (V "bs"),
      asg "gUl" (V "bl"), asg "cnt" (.add (V "cnt") (N 7))]) σ σ4 16 := by
    have hc := h.cnt
    have := (h.rest).2.1
    have := length_le_frames (stWords S')
    refine (Run.seqs_cons (by simp) (Run.assign (by simp; omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ1]; omega)) (Run.seqs_cons (by simp) (Run.assign (by simp [σ2, σ1]; omega))
      (Run.seqs_one (Run.assign (by simp [σ3, σ2, σ1]; omega)))))).mono (by simp)
  have hx4 : σ4.arrs "x" = σ.arrs "x" := by simp [σ4, σ3, σ2, σ1]
  have hg4 : SlotIs M σ4 { f with ph := 1, AT := b } := by
    refine hg.upd ["gp", "gUs", "gUl"] (fun y hy hy' => ?_) hx4 (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
      (Or.inr rfl) (Or.inl (by decide)) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
      (Or.inr rfl) (Or.inl (Or.inl (by decide))) (Or.inr rfl) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun _ => by simp [σ4, σ3, σ2, σ1, ])
      (fun h => absurd h (by decide)) ?_ (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) ?_
      (fun ⟨y, hy, hy'⟩ => absurd hy' (by
        simp only [exVars, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
    · have : y ≠ "gp" ∧ y ≠ "gUs" ∧ y ≠ "gUl" := by simpa using hy'
      have hyc : y ≠ "cnt" := fun e => by subst e; exact absurd hy (by decide)
      simp [σ4, σ3, σ2, σ1, this.1, this.2.1, this.2.2, hyc]
    · exact ⟨hn1, hn2, hn3, hn4, show (1 : ℕ) < 2 * M by omega, hn6⟩
    · intro _
      obtain ⟨a1, a2, a3⟩ := h.bseg
      exact segIs_of (a := σ.vars "bs") (by simp [σ4, σ3, σ2]) (by simp [σ4, σ3, a1]) a2
        (by rw [hx4]; exact a3)
  have hC4 : Ctx W M σ4 := (((hC.setVar (by decide) _).setVar (by decide) _).setVar (by decide) _).setVar
    (by decide) _
  have hF4 : Filled "OB" "po" [] σ4 := h.F.congr (by simp [σ4, σ3, σ2, σ1]) (by simp [σ4, σ3, σ2, σ1])
  have hrest4 : SegIs M σ4 "rS" "rL" (frames (stWords S')) :=
    h.rest.of_eq (by simp [σ4, σ3, σ2, σ1]) (by simp [σ4, σ3, σ2, σ1]) hx4
  have hcnt4 : σ4.vars "cnt" = (stWords (({ f with ph := 1, AT := b } : Fr) :: S')).length := by
    simp only [σ4, Env.setVar, if_pos rfl]; rw [h.cnt, stWords_cons]; simp [frWords] <;> omega
  obtain ⟨σ5, K5, r5, F5, hl5, hK5, fr5⟩ := frameOut_run (j := j + 1) hC4 hF4 hg4 hrest4 hcnt4
    (by simp [σ4, σ3, σ2, σ1, h.j1]) h.jM
  have hC5 := hC4.ofr fr5 (by decide)
  have hg5 := hg4.ofr fr5 (by decide)
  set σ6 := σ5.setVar "hk" f.kk
  set σ7 := σ6.setVar "hd" f.d
  set σ8 := σ7.setVar "hl" f.l2
  set σ9 := σ8.setVar "hs" (σ5.vars "gBs")
  set σ10 := σ9.setVar "hw" (σ5.vars "gBl")
  have r6 : Run (W + 1) (seqs [asg "hk" (V "gk"), asg "hd" (V "gd"), asg "hl" (V "g2"),
      asg "hs" (V "gBs"), asg "hw" (V "gBl")]) σ5 σ10 10 := by
    have := hg5.B.2.1
    refine (Run.seqs_cons (by simp) (Run.assign (by simp [hg5.kk]; omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ6, hg5.d]; omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ7, σ6, hg5.l2]; omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ8, σ7, σ6]; omega))
      (Run.seqs_one (Run.assign (by simp [σ9, σ8, σ7, σ6]; rw [hg5.B.1]; omega))))))).mono (by simp)
  have hC10 : Ctx W M σ10 := ((((hC5.setVar (by decide) _).setVar (by decide) _).setVar (by decide) _).setVar
    (by decide) _).setVar (by decide) _
  have hF10 : Filled "OB" "po" (hdS (j + 1) (({ f with ph := 1, AT := b } : Fr) :: S')) σ10 :=
    F5.congr (by simp [σ10, σ9, σ8, σ7, σ6]) (by simp [σ10, σ9, σ8, σ7, σ6])
  have hA10 : SegIs M σ10 "hs" "hw" f.B := by
    obtain ⟨a1, a2, a3⟩ := hg5.B
    exact segIs_of (a := σ5.vars "gBs") (by simp [σ10, σ9]) (by simpa [σ10, σ9] using a1) a2
      (by simpa [σ10, σ9, σ8, σ7, σ6] using a3)
  obtain ⟨σ11, K11, r11, B11, hK11, fr11⟩ := emSh_built hC10 hF10 (by simp [σ10, σ9, σ8, σ7, σ6]; omega)
    (by simp [σ10, σ9, σ8, σ7, σ6]; omega) (by simp [σ10, σ9, σ8, σ7, σ6]; omega) hA10
    (by have := hA10.2.1; omega)
  have e1 : [σ10.vars "hk", σ10.vars "hd", σ10.vars "hl"] = [f.kk, f.d, f.l2] := by
    simp [σ10, σ9, σ8, σ7, σ6]
  rw [e1] at B11
  refine ⟨σ11, hdS (j + 1) (({ f with ph := 1, AT := b } : Fr) :: S') ++
    [5, f.B.length + 3, 1, 0, 0, 0, 0, 0] ++ ([f.kk, f.d, f.l2] ++ f.B) ++ [0], 16 + (K5 + (10 + K11)),
    ?_, ?_, ?_, ?_, ?_⟩
  · have := Run.seqs_app2 (a := [asg "gp" (N 1), asg "gUs" (V "bs"),
      asg "gUl" (V "bl"), asg "cnt" (.add (V "cnt") (N 7))])
      (b := [emHd, emFr, emRest, patchL] ++ ([asg "hk" (V "gk"), asg "hd" (V "gd"), asg "hl" (V "g2"),
      asg "hs" (V "gBs"), asg "hw" (V "gBl")] ++ [emSh])) (by simp) (by simp) r1
      (Run.seqs_app2 (by simp) (by simp) r5 (Run.seqs_app2 (by simp) (by simp) r6 (Run.seqs_one r11)))
    exact this
  · rw [round_ph0_succ f S' b hph hd0]; exact B11
  · have := hA10.2.1; simp; omega
  · simp; omega
  · refine (Keep.setVar σ (by decide) (by decide) (by decide) _).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      ((Keep.of_ofr fr5 (by decide) (by decide) (by decide)).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      (Keep.of_ofr fr11 (by decide) (by decide) (by decide)))))))))))


/-- The phase `0` at depth `0`: hand `b` down. -/
theorem ph0z_run {W M j : ℕ} {σ : Env} {f : Fr} {S' : List Fr} {b : List ℕ} (P : SzP)
    (h : Top W M j f S' b σ) (hph : f.ph = 0) (hd0 : f.d = 0) (hpar : ∀ p S'', S' = p :: S'' → FOK P p ∧ p.ph = 3) :
    ∃ σ' ob K, Run (W + 1) (seqs [asg "hk" (V "gk"), asg "hd" (N 0),
        asg "hl" (.add (V "g1") (V "g2")), asg "r1s" (N 0), asg "r1l" (N 0), asg "r2s" (V "bs"),
        asg "r2l" (V "bl"), retCmd]) σ σ' K ∧ Built (j + 1) (round (f :: S') b) ob σ' ∧
      ob.length ≤ 64 * M ∧ K ≤ 300 * ob.length + 500 * (toWord (stWords (f :: S'))).length + 7100 ∧
      Keep σ σ' := by
  have hC := h.ctx
  have hR := hC.room
  have hm := hC.m16
  have hg := h.slot
  obtain ⟨r, hx⟩ := h.hx
  have hpn := nums_mem hx (g := f) (by simp)
  have q2 := h.x4 _ (hpn f.kk (by simp)); have q1 := h.x4 _ (hpn f.d (by simp))
  have q3 := h.x4 _ (hpn f.l1 (by simp)); have q4 := h.x4 _ (hpn f.l2 (by simp))
  obtain ⟨u1, u2, -⟩ := hg.AT
  obtain ⟨b1, b2, -⟩ := h.bseg
  set σ1 := σ.setVar "hk" f.kk
  set σ2 := σ1.setVar "hd" 0
  set σ3 := σ2.setVar "hl" (f.l1 + f.l2)
  set σ4 := σ3.setVar "r1s" 0
  set σ5 := σ4.setVar "r1l" 0
  set σ6 := σ5.setVar "r2s" (σ.vars "bs")
  set σ7 := σ6.setVar "r2l" (σ.vars "bl")
  have ra : Run (W + 1) (seqs [asg "hk" (V "gk"), asg "hd" (N 0), asg "hl" (.add (V "g1") (V "g2")),
      asg "r1s" (N 0), asg "r1l" (N 0), asg "r2s" (V "bs"), asg "r2l" (V "bl")]) σ σ7 16 :=
    (Run.seqs_cons (by simp) (Run.assign (by simp [hg.kk]; omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ1, hg.d] <;> omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ2, σ1, hg.l1, hg.l2]; omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ3, σ2, σ1] <;> omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ4, σ3, σ2, σ1] <;> omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ5, σ4, σ3, σ2, σ1]; omega))
      (Run.seqs_one (Run.assign (by simp [σ6, σ5, σ4, σ3, σ2, σ1]; omega))))))))).mono (by simp)
  have hx7 : σ7.arrs "x" = σ.arrs "x" := by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1]
  have hR7 : TopR W M j f S' σ7 :=
    ((((((h.toR.setVar (by decide) _).setVar (by decide) _).setVar (by decide) _).setVar (by decide) _).setVar
      (by decide) _).setVar (by decide) _).setVar (by decide) _
  have h17 : SegIs M σ7 "r1s" "r1l" [] :=
    segIs_of (a := 0) (by simp [σ7, σ6, σ5, σ4]) (by simp [σ7, σ6, σ5]) (by simp) (by simp [seg])
  have h27 : SegIs M σ7 "r2s" "r2l" b := by
    obtain ⟨a1, a2, a3⟩ := h.bseg
    exact segIs_of (a := σ.vars "bs") (by simp [σ7, σ6]) (by simp [σ7, a1]) a2 (by rw [hx7]; exact a3)
  obtain ⟨σ8, ob, K8, r8, B8, hl8, hK8, kp8⟩ := ret_run P hR7 hpar h17 h27
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1]; omega) (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1]; omega)
    (by simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1]; omega)
  have e : [σ7.vars "hk", σ7.vars "hd", σ7.vars "hl"] = [f.kk, 0, f.l1 + f.l2] := by
    simp [σ7, σ6, σ5, σ4, σ3, σ2, σ1]
  rw [e] at B8
  refine ⟨σ8, ob, _, Run.seqs_app2 (a := [asg "hk" (V "gk"), asg "hd" (N 0),
      asg "hl" (.add (V "g1") (V "g2")), asg "r1s" (N 0), asg "r1l" (N 0), asg "r2s" (V "bs"),
      asg "r2l" (V "bl")]) (by simp) (by simp) ra (Run.seqs_one r8),
    by rw [round_ph0_zero f S' b hph hd0]; simpa using B8, hl8, by omega, ?_⟩
  exact (Keep.setVar σ (by decide) (by decide) (by decide) _).trans
    ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
    ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
    ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
    ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
    ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
    ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans kp8))))))


/-! ### Advancing the top frame -/

/-- In a good state after `advance g S` that opens a child, the shifted
first node of `g` is a node word. -/
theorem adv_SA {P : SzP} {g : Fr} {S : List Fr} (h : ROKs P (advance g S)) (hi : g.i < nA g + nB g) :
    NW (g.d - 1) g.l1 g.SA := by
  rw [advance_lt g S hi] at h
  have := (h.1.2.1 { g with ph := 3 } (by simp)).SA (by simp)
  exact this.1

/-- The frame `f` of a good stack: its nodes as node words of depth `d + 1`. -/
theorem fok_nodes {P : SzP} {f : Fr} (hf : FOK P f) (hd : 1 ≤ f.d) :
    ∃ hh, f.d = hh + 1 ∧ (∃ tA : Node (hh + 1) f.l1, f.A = toWord tA) ∧
      ∃ tB : Node (hh + 1) f.l2, f.B = toWord tB := by
  obtain ⟨hh, hdh⟩ : ∃ hh, f.d = hh + 1 := ⟨f.d - 1, by omega⟩
  have hA := hf.A.1
  have hB := hf.B.1
  rw [hdh] at hA hB
  exact ⟨hh, hdh, hA, hB⟩

/-- The phase `2`: the shift of `A` is in, advance. -/
theorem ph2_run {W M j : ℕ} {σ : Env} {f : Fr} {S' : List Fr} {b : List ℕ} (P : SzP)
    (h : Top W M j f S' b σ) (hph : f.ph = 2) (hf : FOK P f)
    (hnext : ROKs P (round (f :: S') b)) :
    ∃ σ' ob K, Run (W + 1) ph2Cmd σ σ' K ∧ Built (j + 1) (round (f :: S') b) ob σ' ∧
      ob.length ≤ 64 * M ∧ K ≤ 300 * ob.length + 5100 ∧ Keep σ σ' := by
  have hC := h.ctx
  have hR := hC.room
  have hm := hC.m16
  have hg := h.slot
  obtain ⟨hn1, hn2, hn3, hn4, hn5, hn6⟩ := hg.nums
  obtain ⟨r, hx⟩ := h.hx
  have hpn := nums_mem hx (g := f) (by simp)
  have q2 := h.x4 _ (hpn f.kk (by simp))
  have q3 := h.x4 _ (hpn f.l1 (by simp)); have q4 := h.x4 _ (hpn f.l2 (by simp))
  obtain ⟨b1, b2, -⟩ := h.bseg
  set σ1 := σ.setVar "gSs" (σ.vars "bs" + 3)
  set σ2 := σ1.setVar "gSl" (σ.vars "bl" - 3)
  set σ3 := σ2.setVar "gi" 0
  have ra : Run (W + 1) (seqs [asg "gSs" (.add (V "bs") (N 3)), asg "gSl" (.sub (V "bl") (N 3)),
      asg "gi" (N 0)]) σ σ3 12 :=
    (Run.seqs_cons (by simp) (Run.assign (by simp; omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ1]; omega)) (Run.seqs_one (Run.assign (by simp <;> omega))))).mono (by simp)
  have hx3 : σ3.arrs "x" = σ.arrs "x" := by simp [σ3, σ2, σ1]
  have hg3 : SlotIs M σ3 { f with SA := b.drop 3, i := 0 } := by
    refine hg.upd ["gSs", "gSl", "gi"] (fun y hy hy' => ?_) hx3 (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
      (Or.inr rfl) (Or.inr rfl) (Or.inl (by decide)) (Or.inr rfl) (Or.inr rfl)
      (Or.inl (Or.inl (by decide))) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun _ => by simp [σ3])
      ⟨hn1, hn2, hn3, hn4, hn5, show (0 : ℕ) < 2 * M by omega⟩
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun _ => segIs_drop3 h.bseg h.bs3 (by simp [σ3, σ2, σ1]) (by simp [σ3, σ2]) hx3)
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun ⟨y, hy, hy'⟩ => absurd hy' (by
        simp only [exVars, List.mem_cons, List.not_mem_nil, or_false] at hy
        rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide))
    have : y ≠ "gSs" ∧ y ≠ "gSl" ∧ y ≠ "gi" := by simpa using hy'
    simp [σ3, σ2, σ1, this.1, this.2.1, this.2.2]
  have hv3 : ∀ z, z ∉ ["gSs", "gSl", "gi"] → σ3.vars z = σ.vars z := by
    intro z hz
    have : z ≠ "gSs" ∧ z ≠ "gSl" ∧ z ≠ "gi" := by simpa using hz
    simp [σ3, σ2, σ1, this.1, this.2.1, this.2.2]
  have hC3 : Ctx W M σ3 := ((hC.setVar (by decide) _).setVar (by decide) _).setVar (by decide) _
  obtain ⟨hh, hdh, ⟨tA, hA⟩, ⟨tB, hB⟩⟩ := fok_nodes hf (hf.hd (by omega))
  have hSB := (hf.SB (by omega)).1
  rw [hdh, show hh + 1 - 1 = hh by omega] at hSB
  have hround : round (f :: S') b = advance { f with SA := b.drop 3, i := 0 } S' := round_ph2 f S' b hph
  obtain ⟨σ4, ob, K4, r4, B4, hl4, hK4, kp4⟩ := advCmd_run (g := { f with SA := b.drop 3, i := 0 })
    (Sr := S') (j := j + 1) (h := hh) hC3
    (⟨by rw [hv3 "po" (by decide), h.F.pos], fun i hi => absurd hi (by simp)⟩) hg3
    (h.rest.of_eq (hv3 "rS" (by decide)) (hv3 "rL" (by decide)) hx3) (by rw [hv3 "cnt" (by decide), h.cnt])
    (by rw [hv3 "j1" (by decide), h.j1]) h.jM hdh tA tB hA hB (fun _ => hSB)
    (fun _ hi => by
      have := adv_SA (by rw [← hround]; exact hnext) hi
      rw [show ({ f with SA := b.drop 3, i := 0 } : Fr).d = hh + 1 from hdh] at this
      simpa using this) (by show f.kk + f.l1 + f.l2 + 2 < M; omega)
  refine ⟨σ4, ob, _, Run.seqs_app2 (a := [asg "gSs" (.add (V "bs") (N 3)), asg "gSl" (.sub (V "bl") (N 3)),
      asg "gi" (N 0)]) (by simp) (by simp) ra (Run.seqs_one r4), by rw [hround]; exact B4, hl4,
    by omega, ?_⟩
  exact (Keep.setVar σ (by decide) (by decide) (by decide) _).trans
    ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
    ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans kp4))


/-- The phase `4`: the restriction of the child is in, add it to `EX` and advance. -/
theorem ph4_run {W M j : ℕ} {σ : Env} {f : Fr} {S' : List Fr} {b : List ℕ} (P : SzP)
    (h : Top W M j f S' b σ) (hph : f.ph = 4) (hf : FOK P f) :
    ∃ σ' ob K, Run (W + 1) ph4Cmd σ σ' K ∧ Built (j + 1) (round (f :: S') b) ob σ' ∧
      ob.length ≤ 64 * M ∧ K ≤ 300 * ob.length + 60 * (toWord (stWords (f :: S'))).length + 5300 ∧
      Keep σ σ' := by
  have hC := h.ctx
  have hR := hC.room
  have hm := hC.m16
  have hg := h.slot
  obtain ⟨hn1, hn2, hn3, hn4, hn5, hn6⟩ := hg.nums
  obtain ⟨r, hx⟩ := h.hx
  have hpn := nums_mem hx (g := f) (by simp)
  have q2 := h.x4 _ (hpn f.kk (by simp))
  have q3 := h.x4 _ (hpn f.l1 (by simp)); have q4 := h.x4 _ (hpn f.l2 (by simp))
  have q6 := h.x4 _ (hpn f.i (by simp))
  have hfA : f.A ∈ stWords (f :: S') := by rw [stWords_cons]; simp [frWords]
  have lA := length_le_toWord hfA
  obtain ⟨hh, hdh, ⟨tA, hA⟩, ⟨tB, hB⟩⟩ := fok_nodes hf (hf.hd (by omega))
  have hSB := (hf.SB (by omega)).1
  rw [hdh, show hh + 1 - 1 = hh by omega] at hSB
  have hSA := (hf.SA (by omega)).1
  rw [hdh, show hh + 1 - 1 = hh by omega] at hSA
  have hi4 := hf.i4 hph
  have hAs := hg.A
  rw [hA] at hAs
  obtain ⟨σ1, r1, hy1, -, hx1, fr1⟩ := extsAt_run (s := "gAs") (cnt := "nA") (by decide) hC tA
    (hAs.drop_eq) hAs.2.1
  set ws := (Node.exts tA).words with hws
  have hnAp : nA f = ws.length := by simp [nA, hA, extsOf_node, hws]
  have hu : f.i < ws.length := by omega
  have hx1' : σ1.arrs "x" = σ.arrs "x" := fr1.arrs "x" (by decide)
  have hC1 : Ctx W M σ1 := hC.ofr fr1 (by decide)
  have htA : (toWord tA).length = (toWord (Node.atoms tA).words).length + (toWord ws).length := by
    rw [toWord_node_succ, List.length_append]
  have hgi1 : σ1.vars "gi" = f.i := by rw [fr1.vars "gi" (by decide), hg.i]
  obtain ⟨σ2, r2, hy2, hxg2, hdrop2, hle2, fr2⟩ := extFr_run (k := "gi") (by decide) hC1 (ws := ws)
    (r := (σ.arrs "x").drop (σ.vars "gAs" + (toWord tA).length))
    (by rw [hx1']; simpa using hx1) (by rw [hgi1]; exact hu) (by have := hAs.2.1; omega)
  simp only [hgi1] at hxg2 hdrop2 hle2
  set e := ws[f.i]'hu with he
  obtain ⟨ε, -, hε⟩ := extsOf_getD tA (j := f.i) hu
  have hge : (extsOf f.A).getD f.i [] = e := by
    rw [hA, extsOf_node, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu]; rfl
  have hee : e = ε.1.val :: toWord ε.2 := by rw [← hge, hA, hε]
  have hx2 : σ2.arrs "x" = σ.arrs "x" := by rw [fr2.arrs "x" (by decide), hx1']
  set y2 := σ2.vars "y"
  have hget : (σ.arrs "x")[y2 + 1]? = some ε.1.val := by
    have hd : (σ.arrs "x").drop (y2 + 1) = (ε.1.val :: toWord ε.2) ++
        (frames (ws.drop (f.i + 1)) ++ (σ.arrs "x").drop (σ.vars "gAs" + (toWord tA).length)) := by
      rw [← hee]; simpa [hx1'] using hdrop2
    exact getElem_of_drop_cons hd
  have hεM : ε.1.val < M := hC.xv _ (List.mem_of_getElem? hget)
  have hy2M : y2 + 1 < W + 1 := by
    have := hAs.2.1
    clear * - hle2 hy1 htA this hR
    omega
  obtain ⟨b1, b2, -⟩ := h.bseg
  set σ3 := σ2.setVar "gg" ε.1.val
  set σ4 := σ3.setVar "gx" 1
  set σ5 := σ4.setVar "r1s" (σ.vars "bs" + 3)
  set σ6 := σ5.setVar "r1l" (σ.vars "bl" - 3)
  set σ7 := σ6.setVar "r2s" 0
  set σ8 := σ7.setVar "r2l" 0
  set σ9 := σ8.setVar "gi" (f.i + 1)
  have fr12 := fr1.trans fr2
  have hv2 : ∀ z, z ∉ ["y", "sn", "sk", "nA", "y", "sk"] → σ2.vars z = σ.vars z := fun z hz => fr12.vars z hz
  have ra : Run (W + 1) (seqs [asg "gg" (X (.add (V "y") (N 1))), asg "gx" (N 1),
      asg "r1s" (.add (V "bs") (N 3)), asg "r1l" (.sub (V "bl") (N 3)), asg "r2s" (N 0), asg "r2l" (N 0),
      asg "gi" (.add (V "gi") (N 1))]) σ2 σ9 30 := by
    have hgetE : (X (.add (V "y") (N 1))).evalB (W + 1) σ2 = some ε.1.val :=
      evalB_get (evalB_bin (evalB_var (by omega)) (evalB_lit (by omega)) (by simp; omega))
        (by rw [hx2]; simpa using hget) (by omega)
    have e1 : σ2.vars "bs" = σ.vars "bs" := hv2 "bs" (by decide)
    have e2 : σ2.vars "bl" = σ.vars "bl" := hv2 "bl" (by decide)
    have e3 : σ2.vars "gi" = f.i := by rw [hv2 "gi" (by decide), hg.i]
    refine (Run.seqs_cons (by simp) (Run.assign hgetE) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ3] <;> omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ4, σ3, e1]; omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp [σ5, σ4, σ3, e2]; omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp <;> omega)) (Run.seqs_cons (by simp)
      (Run.assign (by simp <;> omega))
      (Run.seqs_one (Run.assign (by simp [σ8, σ7, σ6, σ5, σ4, σ3, e3]; omega))))))))).mono (by simp)
  set g : Fr := { f with i := f.i + 1, EX := f.EX ++ [ε.1.val :: b.drop 3] } with hgdef
  have hx9 : σ9.arrs "x" = σ.arrs "x" := by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, hx2]
  have hv9 : ∀ z, z ∉ ["gg", "gx", "r1s", "r1l", "r2s", "r2l", "gi", "y", "sn", "sk", "nA"] →
      σ9.vars z = σ.vars z := by
    intro z hz
    have : z ≠ "gg" ∧ z ≠ "gx" ∧ z ≠ "r1s" ∧ z ≠ "r1l" ∧ z ≠ "r2s" ∧ z ≠ "r2l" ∧ z ≠ "gi" := by
      simp at hz; tauto
    simp only [σ9, σ8, σ7, σ6, σ5, σ4, σ3, Env.setVar, if_neg this.1, if_neg this.2.1, if_neg this.2.2.1,
      if_neg this.2.2.2.1, if_neg this.2.2.2.2.1, if_neg this.2.2.2.2.2.1, if_neg this.2.2.2.2.2.2]
    exact hv2 z (by simp at hz ⊢; tauto)
  have hg9 : SlotIs M σ9 g := by
    refine hg.upd ["gg", "gx", "r1s", "r1l", "r2s", "r2l", "gi"]
      (fun z hz hz' => hv9 z (by
        intro hh'; simp at hh' hz'
        rcases hh' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | exact absurd hz (by decide) | simp_all))
      hx9 (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
      (Or.inr rfl) (Or.inl (by decide)) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl) (Or.inr rfl)
      (Or.inl ⟨"gx", by decide, by decide⟩) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun _ => by simp [σ9, hgdef]) ⟨hn1, hn2, hn3, hn4, hn5, show f.i + 1 < 2 * M by omega⟩
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun h => absurd h (by decide))
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) (fun _ => ?_)
    have hE0 := (hg.EX.seg0 h.gx).of_eq (hv9 "gEs" (by decide)) (hv9 "gEl" (by decide)) hx9
    refine Or.inr ⟨by simp [σ9, σ8, σ7, σ6, σ5, σ4], by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3]; omega,
      f.EX, b.drop 3, [], by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, hgdef], hE0,
      segIs_drop3 h.bseg h.bs3 (by simp [σ9, σ8, σ7, σ6, σ5]) (by simp [σ9, σ8, σ7, σ6]) hx9,
      segIs_of (a := 0) (by simp [σ9, σ8, σ7]) (by simp [σ9, σ8]) (by simp) (by simp [seg])⟩
  have hF9 : Filled "OB" "po" [] σ9 :=
    ⟨by rw [hv9 "po" (by decide), h.F.pos], fun i hi => absurd hi (by simp)⟩
  have hC9 : Ctx W M σ9 :=
    hC.of_frame (hv9 "W" (by decide)) hx9 (by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, fr12.arrs "wp" (by decide)])
      (by simp [σ9, σ8, σ7, σ6, σ5, σ4, σ3, fr12.len])
  have hround : round (f :: S') b = advance g S' := by rw [round_ph4 f S' b hph, hge, hee]; rfl
  obtain ⟨σ10, ob, K10, r10, B10, hl10, hK10, kp10⟩ := advCmd_run (g := g) (Sr := S') (j := j + 1) (h := hh)
    hC9 hF9 hg9 (h.rest.of_eq (hv9 "rS" (by decide)) (hv9 "rL" (by decide)) hx9)
    (by rw [hv9 "cnt" (by decide), h.cnt]) (by rw [hv9 "j1" (by decide), h.j1]) h.jM hdh tA tB hA hB
    (fun _ => hSB) (fun _ _ => hSA) (by show f.kk + f.l1 + f.l2 + 2 < M; omega)
  have hwsl : ws.length < (toWord ws).length := count_lt_toWord ws
  have htA' : (toWord tA).length = f.A.length := by rw [hA]
  refine ⟨σ10, ob, _, Run.seqs_cons (by simp) r1 (Run.seqs_cons (by simp) r2
    (Run.seqs_app2 (a := [asg "gg" (X (.add (V "y") (N 1))), asg "gx" (N 1),
      asg "r1s" (.add (V "bs") (N 3)), asg "r1l" (.sub (V "bl") (N 3)), asg "r2s" (N 0), asg "r2l" (N 0),
      asg "gi" (.add (V "gi") (N 1))]) (by simp) (by simp) ra (Run.seqs_one r10))),
    by rw [hround]; exact B10, hl10, ?_, ?_⟩
  · clear * - hK10 htA htA' lA hwsl
    omega
  · exact (Keep.of_ofr fr12 (by decide) (by decide) (by decide)).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans
      ((Keep.setVar _ (by decide) (by decide) (by decide) _).trans kp10)))))))


/-! ### The part of the answer and the dispatch -/

theorem seg_o {X o rest : List ℕ} {a0 a n : ℕ} (hxo : X.drop a0 = o ++ rest) (hn : n ≤ o.length - a) :
    seg X (a0 + a) n = (o.drop a).take n := by
  simp only [seg]
  rw [← List.drop_drop, hxo]
  by_cases ha : a ≤ o.length
  · rw [List.drop_append_of_le_length ha, List.take_append_of_le_length (by simp; omega)]
  · have : n = 0 := by omega
    subst this; simp

theorem pick_seg {M : ℕ} {σ σ' : Env} {o rest : List ℕ} {a0 a n : ℕ}
    (hxo : (σ.arrs "x").drop a0 = o ++ rest) (hM : a0 + o.length + 512 ≤ M) (ha : a ≤ 431)
    (hs : σ'.vars "bs" = a0 + a)
    (hl : σ'.vars "bl" = n) (hx : σ'.arrs "x" = σ.arrs "x") (hn' : n ≤ o.length - a) :
    SegIs M σ' "bs" "bl" ((o.drop a).take n) := by
  have hlen : ((o.drop a).take n).length = n := by simp; omega
  refine segIs_of (a := a0 + a) hs (by rw [hl, hlen]) (by rw [hlen]; omega) ?_
  rw [hx, hlen]; exact seg_o hxo hn'

/-- **The part of the answer of the phase.** -/
theorem pick_run {W M : ℕ} {σ : Env} {ph a0 : ℕ} {o rest : List ℕ} (hC : Ctx W M σ)
    (htp : σ.vars "tp" = ph) (hph : ph < 2 * M) (hoS : σ.vars "oS" = a0) (hoL : σ.vars "oL" = o.length)
    (hxo : (σ.arrs "x").drop a0 = o ++ rest) (hM : a0 + o.length + 512 ≤ M) :
    ∃ σ', Run (W + 1) pickCmd σ σ' 40 ∧ SegIs M σ' "bs" "bl" (pick ph o) ∧ σ'.vars "bs" + 3 ≤ M ∧
      OFr σ σ' ["bs", "bl"] := by
  have hR := hC.room
  have hm := hC.m16
  have c4 := condEq_var_lit (B := W + 1) (n := 4) htp (by omega) (by omega)
  have c1 := condEq_var_lit (B := W + 1) (n := 1) htp (by omega) (by omega)
  have c2 := condEq_var_lit (B := W + 1) (n := 2) htp (by omega) (by omega)
  have fr : ∀ v1 v2, OFr σ ((σ.setVar "bs" v1).setVar "bl" v2) ["bs", "bl"] :=
    fun v1 v2 => ((OFr.setVar σ "bs" v1).trans (OFr.setVar _ "bl" v2)).mono (by decide)
  by_cases h4 : ph = 4
  · subst h4
    refine ⟨(σ.setVar "bs" a0).setVar "bl" (o.length - 428), (Run.ite_true (by rw [c4]; rfl)
      (Run.seq (Run.assign (by simp [hoS]; omega)) (Run.assign (by simp [hoL]; omega)))).mono
      (by simp [Cond.size, Expr.size]), ?_, by simp; omega, fr _ _⟩
    rw [pick_re]
    exact pick_seg (a := 0) hxo hM (by omega) (by simp) (by simp) (by simp) (by omega)
  by_cases h1 : ph = 1
  · subst h1
    refine ⟨(σ.setVar "bs" (a0 + 4)).setVar "bl" (o.length - 5), (Run.ite_false (by rw [c4]; rfl)
      (Run.ite_true (by rw [c1]; rfl)
      (Run.seq (Run.assign (by simp [hoS]; omega)) (Run.assign (by simp [hoL]; omega))))).mono
      (by simp [Cond.size, Expr.size]), ?_, by simp; omega, fr _ _⟩
    rw [pick_sh (Or.inl rfl)]
    exact pick_seg (a := 4) hxo hM (by omega) (by simp) (by simp) (by simp) (by omega)
  by_cases h2 : ph = 2
  · subst h2
    refine ⟨(σ.setVar "bs" (a0 + 4)).setVar "bl" (o.length - 5), (Run.ite_false (by rw [c4]; rfl)
      (Run.ite_false (by rw [c1]; rfl) (Run.ite_true (by rw [c2]; rfl)
      (Run.seq (Run.assign (by simp [hoS]; omega)) (Run.assign (by simp [hoL]; omega)))))).mono
      (by simp [Cond.size, Expr.size]), ?_, by simp; omega, fr _ _⟩
    rw [pick_sh (Or.inr rfl)]
    exact pick_seg (a := 4) hxo hM (by omega) (by simp) (by simp) (by simp) (by omega)
  · refine ⟨(σ.setVar "bs" (a0 + 431)).setVar "bl" (o.length - 431), (Run.ite_false (by rw [c4]; simpa using h4)
      (Run.ite_false (by rw [c1]; simpa using h1) (Run.ite_false (by rw [c2]; simpa using h2)
      (Run.seq (Run.assign (by simp [hoS]; omega)) (Run.assign (by simp [hoL]; omega)))))).mono
      (by simp [Cond.size, Expr.size]), ?_, by simp; omega, fr _ _⟩
    rw [pick_ca h4 h1 h2]
    exact pick_seg (a := 431) hxo hM (by omega) (by simp) (by simp) (by simp) (by omega)


/-- The phase `0`. -/
theorem ph0_run {W M j : ℕ} {σ : Env} {f : Fr} {S' : List Fr} {b : List ℕ} (P : SzP)
    (h : Top W M j f S' b σ) (hph : f.ph = 0) (hpar : ∀ p S'', S' = p :: S'' → FOK P p ∧ p.ph = 3) :
    ∃ σ' ob K, Run (W + 1) ph0Cmd σ σ' K ∧ Built (j + 1) (round (f :: S') b) ob σ' ∧
      ob.length ≤ 64 * M ∧ K ≤ 300 * ob.length + 500 * (toWord (stWords (f :: S'))).length + 7200 ∧
      Keep σ σ' := by
  have hR := h.ctx.room
  have hm := h.ctx.m16
  have hd := h.slot.nums.1
  have c0 := condEq_var_lit (B := W + 1) (n := 0) h.td (by omega) (by omega)
  by_cases hd0 : f.d = 0
  · obtain ⟨σ', ob, K, r, B, hl, hK, kp⟩ := ph0z_run P h hph hd0 hpar
    exact ⟨σ', ob, _, Run.ite_true (by rw [c0]; simpa using hd0) r, B, hl, by
      simp only [Cond.size, Expr.size]; omega, kp⟩
  · obtain ⟨σ', ob, K, r, B, hl, hK, kp⟩ := ph0s_run h hph hd0
    exact ⟨σ', ob, _, Run.ite_false (by rw [c0]; simpa using hd0) r, B, hl, by
      simp only [Cond.size, Expr.size]; omega, kp⟩

/-- The command that dispatches on the phase. -/
def dispCmd : Com :=
  .ite (.eq (V "tp") (N 0)) ph0Cmd (.ite (.eq (V "tp") (N 1)) ph1Cmd
    (.ite (.eq (V "tp") (N 2)) ph2Cmd (.ite (.eq (V "tp") (N 4)) ph4Cmd ph5Cmd)))

/-- **The step by the phase of the top frame.** -/
theorem disp_run {W M j : ℕ} {σ : Env} {f : Fr} {S' : List Fr} {b : List ℕ} (P : SzP)
    (h : Top W M j f S' b σ) (hf : FOK P f) (hq : f.ph = 0 ∨ f.ph = 1 ∨ f.ph = 2 ∨ f.ph = 4 ∨ f.ph = 5)
    (hpar : ∀ p S'', S' = p :: S'' → FOK P p ∧ p.ph = 3) (hnext : ROKs P (round (f :: S') b)) :
    ∃ σ' ob K, Run (W + 1) dispCmd σ σ' K ∧ Built (j + 1) (round (f :: S') b) ob σ' ∧
      ob.length ≤ 64 * M ∧ K ≤ 300 * ob.length + 500 * (toWord (stWords (f :: S'))).length + 7300 ∧
      Keep σ σ' := by
  have hR := h.ctx.room
  have hm := h.ctx.m16
  have hp5 := hf.ph
  have c := fun n (hn : n < 8) => condEq_var_lit (B := W + 1) (n := n) h.tp (by omega) (by omega)
  rcases hq with hq | hq | hq | hq | hq
  · obtain ⟨σ', ob, K, r, B, hl, hK, kp⟩ := ph0_run P h hq hpar
    exact ⟨σ', ob, _, Run.ite_true (by rw [c 0 (by omega)]; simpa using hq) r, B, hl, by
      simp only [Cond.size, Expr.size]; omega, kp⟩
  · obtain ⟨σ', ob, K, r, B, hl, hK, kp⟩ := ph1_run h hq
    exact ⟨σ', ob, _, Run.ite_false (by rw [c 0 (by omega)]; simp [hq])
      (Run.ite_true (by rw [c 1 (by omega)]; simpa using hq) r), B, hl, by
      simp only [Cond.size, Expr.size]; omega, kp⟩
  · obtain ⟨σ', ob, K, r, B, hl, hK, kp⟩ := ph2_run P h hq hf hnext
    exact ⟨σ', ob, _, Run.ite_false (by rw [c 0 (by omega)]; simp [hq])
      (Run.ite_false (by rw [c 1 (by omega)]; simp [hq])
      (Run.ite_true (by rw [c 2 (by omega)]; simpa using hq) r)), B, hl, by
      simp only [Cond.size, Expr.size]; omega, kp⟩
  · obtain ⟨σ', ob, K, r, B, hl, hK, kp⟩ := ph4_run P h hq hf
    exact ⟨σ', ob, _, Run.ite_false (by rw [c 0 (by omega)]; simp [hq])
      (Run.ite_false (by rw [c 1 (by omega)]; simp [hq]) (Run.ite_false (by rw [c 2 (by omega)]; simp [hq])
      (Run.ite_true (by rw [c 4 (by omega)]; simpa using hq) r))), B, hl, by
      simp only [Cond.size, Expr.size]; omega, kp⟩
  · obtain ⟨σ', ob, K, r, B, hl, hK, kp⟩ := ph5_run P h hq hpar
    exact ⟨σ', ob, _, Run.ite_false (by rw [c 0 (by omega)]; simp [hq])
      (Run.ite_false (by rw [c 1 (by omega)]; simp [hq]) (Run.ite_false (by rw [c 2 (by omega)]; simp [hq])
      (Run.ite_false (by rw [c 4 (by omega)]; simp [hq]) r))), B, hl, by
      simp only [Cond.size, Expr.size]; omega, kp⟩


end Lax185574Proofs.CompRam
