/-
**What the atoms say about a genuine configuration.**

`RequestProject/PartD/CGAtom.lean` builds a finite family of regular languages of marked strings
over the alphabet of configuration letters.  This file computes what each of them says when the
string is the *genuine* string representation `Transducers.CG.confEnc q₀ st w` of a configuration
of a pebble transducer, with one gap marked.  The answers are exactly the fields of the letter that
the child configuration graph of that configuration attaches to that gap, and this is what
`RequestProject/PartD/CGFor.lean` turns into a for-transducer.
-/
import Lax194892Proofs.Source.PartD.CGAtom
open Lax765601Proofs Lax765601Proofs.Transducers
open Lax132576Proofs Lax132576Proofs.Transducers
open Lax916827Proofs Lax916827Proofs.Transducers

namespace Lax194892Proofs.Transducers

namespace CGL

open MarkStr RegAut Pebble

open scoped Classical

variable {A B Q : Type} {k : ℕ}
variable {q₀ : Q} {st : List ℕ} {w : List A} {x r : ℕ}

/-! ## Reading off the letters and the windows of a genuine marked string -/

lemma mem_mark_confEnc {c : MLetter A Q k} :
    c ∈ markAt2 (CG.confEnc (k := k) q₀ st w) x r ↔
      ∃ j ≤ w.length, c = ((q₀, w[j]?, PebEnc.ann k st j), decide (j = x), decide (j = r)) := by
  rw [List.mem_iff_getElem?]
  constructor
  · rintro ⟨j, hj⟩
    have hjlen : j < (markAt2 (CG.confEnc (k := k) q₀ st w) x r).length :=
      (List.getElem?_eq_some_iff.1 hj).1
    rw [mark_confEnc_length] at hjlen
    refine ⟨j, by omega, ?_⟩
    rw [mark_confEnc_getElem?, if_pos (by omega : j ≤ w.length)] at hj
    exact (Option.some.inj hj).symm
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by rw [mark_confEnc_getElem?, if_pos hj]⟩

/-- The window of the gap `j` of a genuine marked string. -/
def winAt (q₀ : Q) (st : List ℕ) (w : List A) (x r j : ℕ) : Win (MLetter A Q k) :=
  ((if j = 0 then none
      else some ((q₀, w[j - 1]?, PebEnc.ann k st (j - 1)),
        decide (j - 1 = x), decide (j - 1 = r))),
    ((q₀, w[j]?, PebEnc.ann k st j), decide (j = x), decide (j = r)),
    (if j + 1 ≤ w.length
      then some ((q₀, w[j + 1]?, PebEnc.ann k st (j + 1)),
        decide (j + 1 = x), decide (j + 1 = r))
      else none))

lemma mem_winMap_confEnc {t : Win (MLetter A Q k)} :
    t ∈ winMap (markAt2 (CG.confEnc (k := k) q₀ st w) x r) ↔
      ∃ j ≤ w.length, t = winAt q₀ st w x r j := by
  rw [List.mem_iff_getElem?]
  constructor
  · rintro ⟨j, hj⟩
    have hjlen : j < (winMap (markAt2 (CG.confEnc (k := k) q₀ st w) x r)).length :=
      (List.getElem?_eq_some_iff.1 hj).1
    rw [winMap_length, mark_confEnc_length] at hjlen
    refine ⟨j, by omega, ?_⟩
    rw [winMap_mark_confEnc_getElem? (by omega : j ≤ w.length)] at hj
    exact (Option.some.inj hj).symm
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, winMap_mark_confEnc_getElem? hj⟩

lemma spotBit_winAt {j : ℕ} (hj : j ≤ w.length) (hx : x ≤ w.length) {sp : Spot}
    (hok : SpotOk sp x w.length) :
    spotBit sp (winAt (k := k) q₀ st w x r j) = decide (spotPos sp x r = some j) :=
  spotBit_window hj hx hok

/-! ## The simple atoms -/

lemma mem_hgtL_iff (i : Fin k) (hstb : ∀ p ∈ st, p ≤ w.length) :
    markAt2 (CG.confEnc (k := k) q₀ st w) x r ∈ hgtL i ↔ (i : ℕ) < st.length := by
  constructor
  · rintro ⟨c, hc, hb⟩
    obtain ⟨j, -, rfl⟩ := mem_mark_confEnc.1 hc
    simp only [PebEnc.ann, decide_eq_true_eq] at hb
    exact (List.getElem?_eq_some_iff.1 hb).1
  · intro hi
    refine ⟨((q₀, w[st[i]]?, PebEnc.ann k st st[i]),
      decide (st[(i : ℕ)] = x), decide (st[(i : ℕ)] = r)), ?_, ?_⟩
    · exact mem_mark_confEnc.2 ⟨st[(i : ℕ)], hstb _ (List.getElem_mem hi), rfl⟩
    · simp only [PebEnc.ann, decide_eq_true_eq]
      exact List.getElem?_eq_getElem hi

lemma mem_stateL_iff (q : Q) :
    markAt2 (CG.confEnc (k := k) q₀ st w) x r ∈ stateL q ↔ q = q₀ := by
  constructor
  · intro h
    have h0 := h ((q₀, w[0]?, PebEnc.ann k st 0), decide ((0 : ℕ) = x), decide ((0 : ℕ) = r))
      (mem_mark_confEnc.2 ⟨0, Nat.zero_le _, rfl⟩)
    exact h0.symm
  · rintro rfl c hc
    obtain ⟨j, -, rfl⟩ := mem_mark_confEnc.1 hc
    rfl

lemma mem_lettL_iff (a : Option A) (hx : x ≤ w.length) :
    markAt2 (CG.confEnc (k := k) q₀ st w) x r ∈ lettL a ↔ a = w[x]? := by
  constructor
  · rintro ⟨c, hc, h1, h2⟩
    obtain ⟨j, -, rfl⟩ := mem_mark_confEnc.1 hc
    simp only [decide_eq_true_eq] at h1
    subst h1
    exact h2.symm
  · rintro rfl
    exact ⟨_, mem_mark_confEnc.2 ⟨x, hx, rfl⟩, by simp, rfl⟩

lemma mem_pebL_iff (i : Fin k) (hx : x ≤ w.length) :
    markAt2 (CG.confEnc (k := k) q₀ st w) x r ∈ pebL i ↔ PebEnc.ann k st x i = true := by
  constructor
  · rintro ⟨c, hc, h1, h2⟩
    obtain ⟨j, -, rfl⟩ := mem_mark_confEnc.1 hc
    simp only [decide_eq_true_eq] at h1
    subst h1
    exact h2
  · intro h
    exact ⟨_, mem_mark_confEnc.2 ⟨x, hx, rfl⟩, by simp, h⟩

lemma mem_zeroL_iff (hx : x ≤ w.length) :
    markAt2 (CG.confEnc (k := k) q₀ st w) x r ∈ zeroL ↔ x = 0 := by
  constructor
  · intro h
    have h0 := h (winAt q₀ st w x r 0) (mem_winMap_confEnc.2 ⟨0, Nat.zero_le _, rfl⟩)
    have hz : spotBit (A := A) (Q := Q) (k := k) Spot.zero (winAt q₀ st w x r 0) = true := by
      rw [spotBit_winAt (Nat.zero_le _) hx (by trivial)]
      simp [spotPos]
    have := h0 hz
    have hm : spotBit (A := A) (Q := Q) (k := k) Spot.mark (winAt q₀ st w x r 0) = true := this
    rw [spotBit_winAt (Nat.zero_le _) hx (by trivial)] at hm
    simp only [spotPos, Option.some.injEq, decide_eq_true_eq] at hm
    exact hm
  · rintro rfl t ht
    obtain ⟨j, hj, rfl⟩ := mem_winMap_confEnc.1 ht
    intro hz
    have hz' : spotBit (A := A) (Q := Q) (k := k) Spot.zero (winAt q₀ st w 0 r j) = true := hz
    rw [spotBit_winAt hj (Nat.zero_le _) (by trivial)] at hz'
    simp only [spotPos, Option.some.injEq, decide_eq_true_eq] at hz'
    show spotBit (A := A) (Q := Q) (k := k) Spot.mark (winAt q₀ st w 0 r j) = true
    rw [spotBit_winAt hj (Nat.zero_le _) (by trivial)]
    simp only [spotPos, Option.some.injEq, decide_eq_true_eq]
    omega

lemma mem_neqSpotL_iff {sp : Spot} (hx : x ≤ w.length) (hr : r ≤ w.length)
    (hok : SpotOk sp x w.length) :
    markAt2 (CG.confEnc (k := k) q₀ st w) x r ∈ neqSpotL sp ↔ spotPos sp x r ≠ some r := by
  constructor
  · intro h hc
    refine h (winAt q₀ st w x r r) (mem_winMap_confEnc.2 ⟨r, hr, rfl⟩) ⟨?_, ?_⟩
    · show spotBit (A := A) (Q := Q) (k := k) Spot.extra (winAt q₀ st w x r r) = true
      rw [spotBit_winAt hr hx (by trivial)]
      simp [spotPos]
    · rw [spotBit_winAt hr hx hok, hc]
      simp
  · intro h t ht
    obtain ⟨j, hj, rfl⟩ := mem_winMap_confEnc.1 ht
    rintro ⟨h1, h2⟩
    have h1' : spotBit (A := A) (Q := Q) (k := k) Spot.extra (winAt q₀ st w x r j) = true := h1
    rw [spotBit_winAt hj hx (by trivial)] at h1'
    simp only [spotPos, Option.some.injEq, decide_eq_true_eq] at h1'
    rw [spotBit_winAt hj hx hok] at h2
    simp only [decide_eq_true_eq] at h2
    exact h (by rw [h2, h1'])

lemma mem_okL_iff (sp : Spot) (hx : x ≤ w.length) :
    markAt2 (CG.confEnc (k := k) q₀ st w) x r ∈ okL sp ↔ SpotOk sp x w.length := by
  cases sp with
  | markL =>
      show (markAt2 (CG.confEnc (k := k) q₀ st w) x r ∉ zeroL) ↔ 1 ≤ x
      rw [mem_zeroL_iff hx]
      omega
  | markR =>
      show (markAt2 (CG.confEnc (k := k) q₀ st w) x r ∉ lettL none) ↔ x + 1 ≤ w.length
      rw [mem_lettL_iff none hx]
      constructor
      · intro h
        by_contra hc
        exact h (by rw [List.getElem?_eq_none (by omega)])
      · intro h hc
        rw [List.getElem?_eq_some_iff.2 ⟨by omega, rfl⟩] at hc
        exact absurd hc.symm (by simp)
  | nop => exact ⟨fun _ => trivial, fun _ => Set.mem_univ _⟩
  | zero => exact ⟨fun _ => trivial, fun _ => Set.mem_univ _⟩
  | mark => exact ⟨fun _ => trivial, fun _ => Set.mem_univ _⟩
  | extra => exact ⟨fun _ => trivial, fun _ => Set.mem_univ _⟩

/-! ## Reachability -/

@[simp] lemma spotStack_spotOfDir (d : CG.Dir) (x r : ℕ) :
    spotStack (spotOfDir d) x r = [colOf x d] := by
  rw [spotStack, spotPos_spotOfDir]
  rfl

@[simp] lemma spotStack_nop (x r : ℕ) : spotStack Spot.nop x r = [] := rfl

@[simp] lemma spotStack_zero (x r : ℕ) : spotStack Spot.zero x r = [0] := rfl

lemma stack_bounds {sp : Spot} (hstb : ∀ p ∈ st, p ≤ w.length) (hx : x ≤ w.length)
    (hr : r ≤ w.length) (hok : SpotOk sp x w.length) :
    ∀ p ∈ st ++ spotStack sp x r, p ≤ w.length := by
  intro p hp
  rcases List.mem_append.1 hp with hp | hp
  · exact hstb p hp
  · exact spotStack_le hx hr hok p hp

lemma stack_length_le (sp : Spot) (hstk : st.length < k) :
    (st ++ spotStack sp x r).length ≤ k := by
  have := spotStack_length_le sp x r
  simp only [List.length_append]
  omega

variable [Finite A] [Finite Q]

omit [Finite A] [Finite Q] in
/-- **The reachability atom, on a genuine marked string representation of a configuration.** -/
lemma mem_reachL_iff (M : Pebble A B Q k) {ell : ℕ} {nid : Fin k} {q₁ q₂ : Q} {sp₁ sp₂ : Spot}
    (hnid : (nid : ℕ) = st.length) (hstk : st.length < k) (hstb : ∀ p ∈ st, p ≤ w.length)
    (hx : x ≤ w.length) (hr : r ≤ w.length)
    (h₁ : SpotOk sp₁ x w.length) (h₂ : SpotOk sp₂ x w.length)
    (hl : ell ≤ (st ++ spotStack sp₁ x r).length) :
    markAt2 (CG.confEnc (k := k) q₀ st w) x r ∈ reachL M ell nid q₁ q₂ sp₁ sp₂ ↔
      M.RestrReaches w ell (PebbleCfg.conf q₁ (st ++ spotStack sp₁ x r))
        (PebbleCfg.conf q₂ (st ++ spotStack sp₂ x r)) := by
  rw [reachL]; erw [Set.mem_setOf_eq]; rw [pairMap_confEnc hnid q₁ q₂ hx h₁ h₂]
  exact PebEnc.mem_reachLang_iff M ell q₁ q₂ _ _ w (stack_bounds hstb hx hr h₁)
    (stack_bounds hstb hx hr h₂) (stack_length_le _ hstk) (stack_length_le _ hstk) hl

omit [Finite A] [Finite Q] in
/-- **The single-step atom, on a genuine marked string representation of a configuration.** -/
lemma mem_stepL_iff (M : Pebble A B Q k) {nid : Fin k} {q₁ q₂ : Q} {sp₁ sp₂ : Spot}
    (hnid : (nid : ℕ) = st.length) (hstk : st.length < k) (hstb : ∀ p ∈ st, p ≤ w.length)
    (hx : x ≤ w.length) (hr : r ≤ w.length)
    (h₁ : SpotOk sp₁ x w.length) (h₂ : SpotOk sp₂ x w.length) :
    markAt2 (CG.confEnc (k := k) q₀ st w) x r ∈ stepL M nid q₁ q₂ sp₁ sp₂ ↔
      ∃ o, M.stepCfg w (PebbleCfg.conf q₁ (st ++ spotStack sp₁ x r))
        = some (o, PebbleCfg.conf q₂ (st ++ spotStack sp₂ x r)) := by
  rw [stepL]; erw [Set.mem_setOf_eq]; rw [pairMap_confEnc hnid (q₁, false) (q₂, true) hx h₁ h₂]
  rw [PebEnc.mem_reachLang_iff (Pebble.stepMach M) 0 (q₁, false) (q₂, true) _ _ w
    (stack_bounds hstb hx hr h₁) (stack_bounds hstb hx hr h₂) (stack_length_le _ hstk)
    (stack_length_le _ hstk) (Nat.zero_le _)]
  exact Pebble.restrReaches_stepMach_iff q₁ q₂ _ _

/-! ## Children -/

lemma spotStack_eq_singleton {sp : Spot} {c : ℕ} (hc : spotPos sp x r = some c) :
    spotStack sp x r = [c] := by
  rw [spotStack, hc]
  rfl

omit [Finite A] [Finite Q] in
/-- **The reachability atom describes chains of children.** -/
lemma mem_reachL_childStar_iff (M : Pebble A B Q k) {nid : Fin k} {qa qb : Q} {sp₁ sp₂ : Spot}
    {c₁ c₂ : ℕ} (hnid : (nid : ℕ) = st.length) (hstk : st.length < k)
    (hstb : ∀ p ∈ st, p ≤ w.length) (hx : x ≤ w.length) (hr : r ≤ w.length)
    (h₁ : SpotOk sp₁ x w.length) (h₂ : SpotOk sp₂ x w.length)
    (hc₁ : spotPos sp₁ x r = some c₁) (hc₂ : spotPos sp₂ x r = some c₂) :
    markAt2 (CG.confEnc (k := k) q₀ st w) x r ∈ reachL M ((nid : ℕ) + 1) nid qa qb sp₁ sp₂ ↔
      CG.ChildStar M w st (qa, c₁) (qb, c₂) := by
  have hs₁ := spotStack_eq_singleton hc₁
  have hs₂ := spotStack_eq_singleton hc₂
  rw [mem_reachL_iff M hnid hstk hstb hx hr h₁ h₂ (by rw [hs₁]; simp; omega)]
  rw [CG.childStar_iff_restrReaches, hs₁, hs₂, hnid]
  exact Iff.rfl

omit [Finite A] [Finite Q] in
/-- **The single-step atom to the first gap describes the first child.** -/
lemma mem_firstL_iff (M : Pebble A B Q k) {nid : Fin k} {q q' : Q}
    (hnid : (nid : ℕ) = st.length) (hstk : st.length < k) (hstb : ∀ p ∈ st, p ≤ w.length)
    (hx : x ≤ w.length) (hr : r ≤ w.length) :
    markAt2 (CG.confEnc (k := k) q₀ st w) x r ∈ firstL M nid q q' ↔
      CG.FirstChild M w q st (q', 0) := by
  rw [firstL, mem_stepL_iff M (sp₁ := Spot.nop) (sp₂ := Spot.zero) hnid hstk hstb hx hr
    trivial trivial]
  rw [CG.firstChild_iff_step]
  simp only [spotStack_nop, spotStack_zero, List.append_nil, CG.cfgOf_eq_conf]

omit [Finite A] [Finite Q] in
/-- **The child atom describes the children reached from the first one.** -/
lemma mem_childL_iff (M : Pebble A B Q k) {nid : Fin k} {qa : Q} {sp : Spot} {c : ℕ}
    {ch : ℕ → CG.Vtx Q} {m : ℕ} (hseq : CG.IsChildSeq M w q₀ st ch m)
    (hnid : (nid : ℕ) = st.length) (hstk : st.length < k)
    (hstb : ∀ p ∈ st, p ≤ w.length) (hx : x ≤ w.length) (hr : r ≤ w.length)
    (hok : SpotOk sp x w.length) (hc : spotPos sp x r = some c) :
    markAt2 (CG.confEnc (k := k) q₀ st w) x r ∈ childL M nid qa sp ↔
      CG.ChildStar M w st (ch 0) (qa, c) := by
  constructor
  · rintro ⟨⟨p₁, p₂⟩, hst, hfst, hre⟩
    have hp₁ : p₁ = q₀ := (mem_stateL_iff (r := r) (x := x) (w := w) (st := st) p₁).1 hst
    subst hp₁
    have hfc := (mem_firstL_iff M hnid hstk hstb hx hr).1 hfst
    have h0 : (p₂, 0) = ch 0 := hfc.unique hseq.first
    have hcs := (mem_reachL_childStar_iff M (sp₁ := Spot.zero) (c₁ := 0) hnid hstk hstb hx hr
      trivial hok rfl hc).1 hre
    rw [← h0]
    exact hcs
  · intro h
    refine ⟨((q₀, (ch 0).1) : Q × Q), (mem_stateL_iff q₀).2 rfl, ?_, ?_⟩
    · refine (mem_firstL_iff M hnid hstk hstb hx hr).2 ?_
      have h0 : ((ch 0).1, (0 : ℕ)) = ch 0 := by
        refine Prod.ext rfl ?_
        exact (hseq.first.column_zero).symm
      rw [h0]
      exact hseq.first
    · refine (mem_reachL_childStar_iff M (sp₁ := Spot.zero) (c₁ := 0) hnid hstk hstb hx hr
        trivial hok rfl hc).2 ?_
      have h0 : ((ch 0).1, (0 : ℕ)) = ch 0 := by
        refine Prod.ext rfl ?_
        exact (hseq.first.column_zero).symm
      rw [h0]
      exact h

/-! ## The second mark, quantified away -/

omit [Finite A] [Finite Q] in
lemma dropExtra_markAt2 (z : List (CG.ConfLetter A Q k)) (x p : ℕ) :
    (markAt2 z x p).map dropExtra = (markAt2 z x x).map dropExtra := by
  refine List.ext_getElem? (fun j => ?_)
  simp [List.getElem?_map, markAt2_getElem?, dropExtra, Option.map_map, Function.comp_def]

omit [Finite A] [Finite Q] in
lemma marksOnce_markAt2 {z : List (CG.ConfLetter A Q k)} {p : ℕ} (hp : p < z.length) :
    MarksOnce (fun c : MLetter A Q k => c.2.2) (markAt2 z x p) := by
  refine ⟨p, fun j => ?_⟩
  constructor
  · rintro ⟨c, hc, hb⟩
    rw [markAt2_getElem?] at hc
    obtain ⟨a, -, rfl⟩ := Option.map_eq_some_iff.1 hc
    simpa using hb
  · rintro rfl
    refine ⟨(z[j]'hp, decide (j = x), decide (j = j)), ?_, ?_⟩
    · rw [markAt2_getElem?, List.getElem?_eq_getElem hp]
      rfl
    · simp

omit [Finite A] [Finite Q] in
/-- A marked string that agrees with a genuine one away from the second mark, and carries exactly
one second mark, is a genuine one. -/
lemma eq_markAt2_of_dropExtra {z : List (CG.ConfLetter A Q k)} {v : List (MLetter A Q k)}
    (hmap : v.map dropExtra = (markAt2 z x x).map dropExtra)
    (hm : MarksOnce (fun c : MLetter A Q k => c.2.2) v) :
    ∃ p, p < z.length ∧ v = markAt2 z x p := by
  obtain ⟨p, hp⟩ := hm
  have hlen : v.length = z.length := by
    have h := congrArg List.length hmap
    simpa using h
  have hplt : p < z.length := by rw [← hlen]; exact marksOnce_lt_length hp
  refine ⟨p, hplt, ?_⟩
  refine List.ext_getElem (by rw [hlen, markAt2_length]) (fun j hj1 hj2 => ?_)
  have hz : j < z.length := by omega
  have hz' : j < (markAt2 z x x).length := by simpa using hz
  have hdrop : dropExtra v[j] = dropExtra ((markAt2 z x x)[j]'hz') := by
    have h := congrArg (fun l => l[j]?) hmap
    simp only [List.getElem?_map] at h
    rw [List.getElem?_eq_getElem hj1, List.getElem?_eq_getElem hz'] at h
    exact Option.some.inj h
  have hxx : (markAt2 z x x)[j]'hz' = (z[j], decide (j = x), decide (j = x)) := by
    have h := markAt2_getElem? z x x j
    rw [List.getElem?_eq_getElem hz', List.getElem?_eq_getElem hz] at h
    exact Option.some.inj h
  have hb : v[j].2.2 = decide (j = p) := by
    by_cases hjp : j = p
    · subst hjp
      obtain ⟨c, hc, hcb⟩ := (hp j).2 rfl
      rw [List.getElem?_eq_getElem hj1] at hc
      rw [← Option.some.inj hc] at hcb
      simp [hcb]
    · have hnm : ¬ MarkedAt (fun c : MLetter A Q k => c.2.2) v j := fun h => hjp ((hp j).1 h)
      have hnb : v[j].2.2 ≠ true := fun hb' =>
        hnm ⟨v[j], List.getElem?_eq_getElem hj1, hb'⟩
      simp only [Bool.not_eq_true] at hnb
      simp [hnb, hjp]
  have hmk : (markAt2 z x p)[j]'hj2 = (z[j], decide (j = x), decide (j = p)) := by
    have h := markAt2_getElem? z x p j
    rw [List.getElem?_eq_getElem hj2, List.getElem?_eq_getElem hz] at h
    exact Option.some.inj h
  rw [hmk]
  rw [hxx] at hdrop
  simp only [dropExtra, Prod.mk.injEq] at hdrop
  exact Prod.ext hdrop.1 (Prod.ext hdrop.2 hb)

omit [Finite A] [Finite Q] in
/-- **Quantifying the second mark away, on a genuine marked string.** -/
lemma mem_existsExtraL_iff {L : Language (MLetter A Q k)} {z : List (CG.ConfLetter A Q k)} :
    markAt2 z x x ∈ existsExtraL L ↔ ∃ p, p < z.length ∧ markAt2 z x p ∈ L := by
  constructor
  · rintro ⟨v, hv, hm, he⟩
    obtain ⟨p, hp, rfl⟩ := eq_markAt2_of_dropExtra he hm
    exact ⟨p, hp, hv⟩
  · rintro ⟨p, hp, hL⟩
    exact ⟨markAt2 z x p, hL, marksOnce_markAt2 hp, dropExtra_markAt2 z x p⟩

/-! ## The successor of a child -/

omit [Finite A] [Finite Q] in
lemma neq_vtx_iff {q₃ qa : Q} {c : ℕ} :
    ((q₃, r) ≠ ((qa, c) : CG.Vtx Q)) ↔ (q₃ = qa → c ≠ r) := by
  simp only [ne_eq, Prod.mk.injEq, not_and]
  constructor
  · intro h hq hc
    exact h hq hc.symm
  · intro h hq hc
    exact h hq hc.symm

omit [Finite A] [Finite Q] in
/-- **The intermediate-child atom, on a genuine marked string representation.** -/
lemma mem_midL_iff (M : Pebble A B Q k) {nid : Fin k} {qa qb : Q} {da db : CG.Dir}
    (hnid : (nid : ℕ) = st.length) (hstk : st.length < k) (hstb : ∀ p ∈ st, p ≤ w.length)
    (hx : x ≤ w.length) (hr : r ≤ w.length)
    (h₁ : SpotOk (spotOfDir da) x w.length) (h₂ : SpotOk (spotOfDir db) x w.length) :
    markAt2 (CG.confEnc (k := k) q₀ st w) x r ∈ midL M nid qa da qb db ↔
      ∃ q₃ : Q, CG.ChildStar M w st (qa, colOf x da) (q₃, r) ∧
        CG.ChildStar M w st (q₃, r) (qb, colOf x db) ∧
        (q₃, r) ≠ ((qa, colOf x da) : CG.Vtx Q) ∧
        (q₃, r) ≠ ((qb, colOf x db) : CG.Vtx Q) := by
  rw [midL]; erw [Set.mem_setOf_eq]
  refine exists_congr (fun q₃ => ?_)
  rw [mem_reachL_childStar_iff M (sp₂ := Spot.extra) (c₂ := r) hnid hstk hstb hx hr h₁ trivial
      (spotPos_spotOfDir da x r) rfl,
    mem_reachL_childStar_iff M (sp₁ := Spot.extra) (c₁ := r) hnid hstk hstb hx hr trivial h₂
      rfl (spotPos_spotOfDir db x r)]
  refine and_congr_right (fun _ => and_congr_right (fun _ => and_congr ?_ ?_))
  · rw [mem_neqSpotL_iff hx hr h₁, neq_vtx_iff]
    simp only [spotPos_spotOfDir, ne_eq, Option.some.injEq]
  · rw [mem_neqSpotL_iff hx hr h₂, neq_vtx_iff]
    simp only [spotPos_spotOfDir, ne_eq, Option.some.injEq]

omit [Finite A] [Finite Q] in
/-- **No child strictly in between**, on a genuine marked string representation. -/
lemma mem_existsExtra_midL_iff (M : Pebble A B Q k) {nid : Fin k} {qa qb : Q} {da db : CG.Dir}
    {ch : ℕ → CG.Vtx Q} {m s : ℕ} (hseq : CG.IsChildSeq M w q₀ st ch m) (hs : s ≤ m)
    (hchs : ch s = (qa, colOf x da))
    (hnid : (nid : ℕ) = st.length) (hstk : st.length < k) (hstb : ∀ p ∈ st, p ≤ w.length)
    (hx : x ≤ w.length)
    (h₁ : SpotOk (spotOfDir da) x w.length) (h₂ : SpotOk (spotOfDir db) x w.length) :
    markAt2 (CG.confEnc (k := k) q₀ st w) x x ∈ existsExtraL (midL M nid qa da qb db) ↔
      ∃ u : CG.Vtx Q, CG.ChildStar M w st (qa, colOf x da) u ∧
        CG.ChildStar M w st u (qb, colOf x db) ∧ u ≠ (qa, colOf x da) ∧
        u ≠ (qb, colOf x db) := by
  rw [mem_existsExtraL_iff]
  constructor
  · rintro ⟨p, hp, hmid⟩
    have hple : p ≤ w.length := by
      rw [confEnc_length] at hp
      omega
    obtain ⟨q₃, ha, hb, hc, hd⟩ := (mem_midL_iff M hnid hstk hstb hx hple h₁ h₂).1 hmid
    exact ⟨(q₃, p), ha, hb, hc, hd⟩
  · rintro ⟨⟨q₃, c⟩, ha, hb, hc, hd⟩
    have hcle : c ≤ w.length := by
      rw [← hchs] at ha
      obtain ⟨t, -, htm, hct⟩ := (CG.childStar_from_iff_mem hseq hs _).1 ha
      have hcol := hseq.column_le t htm
      rw [hct] at hcol
      exact hcol
    refine ⟨c, by rw [confEnc_length]; omega, ?_⟩
    exact (mem_midL_iff M hnid hstk hstb hx hcle h₁ h₂).2 ⟨q₃, ha, hb, hc, hd⟩

omit [Finite A] [Finite Q] in
/-- Under the side conditions, the column reached by a direction determines the direction. -/
lemma colOf_inj {n : ℕ} {da db : CG.Dir} (h₁ : SpotOk (spotOfDir da) x n)
    (h₂ : SpotOk (spotOfDir db) x n) (h : colOf x da = colOf x db) : da = db := by
  cases da with
  | none =>
      cases db with
      | none => rfl
      | some b =>
          exfalso
          cases b with
          | true => exact absurd (show x = x + 1 from h) (by omega)
          | false =>
              have hxx : 1 ≤ x := h₂
              exact absurd (show x = x - 1 from h) (by omega)
  | some a =>
      cases db with
      | none =>
          exfalso
          cases a with
          | true => exact absurd (show x + 1 = x from h) (by omega)
          | false =>
              have hxx : 1 ≤ x := h₁
              exact absurd (show x - 1 = x from h) (by omega)
      | some b =>
          cases a with
          | true =>
              cases b with
              | true => rfl
              | false =>
                  exfalso
                  have hxx : 1 ≤ x := h₂
                  exact absurd (show x + 1 = x - 1 from h) (by omega)
          | false =>
              cases b with
              | true =>
                  exfalso
                  have hxx : 1 ≤ x := h₁
                  exact absurd (show x - 1 = x + 1 from h) (by omega)
              | false => rfl

omit [Finite A] [Finite Q] in
/-- **The edge atom, on a genuine marked string representation of a configuration**: the vertex in
the column that `da` leads to is a child, and the vertex in the column that `db` leads to is its
successor. -/
theorem mem_edgeL_iff (M : Pebble A B Q k) {nid : Fin k} {qa qb : Q} {da db : CG.Dir}
    {ch : ℕ → CG.Vtx Q} {m : ℕ} (hseq : CG.IsChildSeq M w q₀ st ch m)
    (hnid : (nid : ℕ) = st.length) (hstk : st.length < k) (hstb : ∀ p ∈ st, p ≤ w.length)
    (hx : x ≤ w.length) :
    markAt2 (CG.confEnc (k := k) q₀ st w) x x ∈ edgeL M nid qa da qb db ↔
      SpotOk (spotOfDir da) x w.length ∧ SpotOk (spotOfDir db) x w.length ∧
        CG.ChildStar M w st (ch 0) (qa, colOf x da) ∧
        CG.NextChild M w st (qa, colOf x da) (qb, colOf x db) := by
  rw [edgeL]
  split
  · rename_i heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [mem_emptyL]
    constructor
    · exact False.elim
    · rintro ⟨-, -, hcs, hnc⟩
      obtain ⟨t, ht, hct⟩ := (CG.childStar_iff_mem hseq _).1 hcs
      rw [← hct] at hnc
      have htm : t < m := by
        by_contra hc
        have hmt : t = m := by omega
        subst hmt
        exact hseq.stop _ hnc
      have h1 := hnc.unique (hseq.next t htm)
      have h2 := hseq.distinct t (t + 1) (by omega) (by omega) h1
      omega
  · rename_i hne
    erw [Set.mem_setOf_eq]
    constructor
    · rintro ⟨ho1, ho2, hch, hre, hnm⟩
      have h1 := (mem_okL_iff (spotOfDir da) hx).1 ho1
      have h2 := (mem_okL_iff (spotOfDir db) hx).1 ho2
      have hcs := (mem_childL_iff M hseq hnid hstk hstb hx hx h1
        (spotPos_spotOfDir da x x)).1 hch
      refine ⟨h1, h2, hcs, ?_⟩
      obtain ⟨s, hsm, hchs⟩ := (CG.childStar_iff_mem hseq _).1 hcs
      rw [← hchs, CG.nextChild_iff_no_mid hseq hsm]
      refine ⟨?_, ?_, ?_⟩
      · rw [hchs]
        exact (mem_reachL_childStar_iff M hnid hstk hstb hx hx h1 h2
          (spotPos_spotOfDir da x x) (spotPos_spotOfDir db x x)).1 hre
      · rw [hchs]
        intro hc
        rw [Prod.mk.injEq] at hc
        exact hne ⟨hc.1, colOf_inj h1 h2 hc.2⟩
      · rw [hchs]
        intro hmid
        exact hnm ((mem_existsExtra_midL_iff M hseq hsm hchs hnid hstk hstb hx h1 h2).2 hmid)
    · rintro ⟨h1, h2, hcs, hnc⟩
      refine ⟨(mem_okL_iff _ hx).2 h1, (mem_okL_iff _ hx).2 h2,
        (mem_childL_iff M hseq hnid hstk hstb hx hx h1 (spotPos_spotOfDir da x x)).2 hcs,
        (mem_reachL_childStar_iff M hnid hstk hstb hx hx h1 h2 (spotPos_spotOfDir da x x)
          (spotPos_spotOfDir db x x)).2 (CG.ChildStar.cons hnc (CG.ChildStar.refl _)), ?_⟩
      intro hex
      obtain ⟨s, hsm, hchs⟩ := (CG.childStar_iff_mem hseq _).1 hcs
      have hmid := (mem_existsExtra_midL_iff M hseq hsm hchs hnid hstk hstb hx h1 h2).1 hex
      rw [← hchs] at hnc hmid
      exact ((CG.nextChild_iff_no_mid hseq hsm _).1 hnc).2.2 hmid

end CGL

end Lax194892Proofs.Transducers
