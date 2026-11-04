import Lax185574Proofs.Words.TreeWord

/-!
The nodes of a tree word, found by a breadth-first scan.

The word of the root of a type tree of height `q` is in the array `x`.
The command `bfs` lists all nodes of the tree in the arrays `pos` (the
position of the word of the node), `dep` (its depth) and `fc` (the index
of its first child). Node `0` is the root. The nodes are listed in the
order of a breadth-first search, so that the children of a node are
listed after it, one after the other. The scalar `nn` holds the number of
nodes.

The scan keeps a queue, the nodes listed but not yet scanned. Scanning a
node skips its atom codes and, below height `q`, lists one child for
every frame of its extensions. The number of nodes and the total length of
the words of the queue together never exceed the length of the root word,
since the frames of the children lie strictly inside the word of their
parent.
-/

namespace Lax185574Proofs.Words

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning
open Lax185574.WordEncoding

/-- Skip one frame. -/
def skipBody : Com :=
  .seq (.assign "y" (.add (.add (.var "y") (.get "x" (.var "y"))) (.lit 1)))
    (.assign "e2" (.add (.var "e2") (.lit 1)))

/-- Skip a list of words at `y`. -/
def skipList : Com :=
  .seq (.assign "e1" (.get "x" (.var "y"))) (.seq (.assign "y" (.add (.var "y") (.lit 1)))
    (.seq (.assign "e2" (.lit 0)) (.while (.lt (.var "e2") (.var "e1")) skipBody)))

/-- Facts about a list of words at `p` in `X` that the scans use. -/
structure ListFacts (X : List ℕ) (p : ℕ) : Prop where
  frPos_le : ∀ j ≤ xg X p, p + 1 + j ≤ frPos X p j ∧ frPos X p j ≤ listEnd X p
  end_le : listEnd X p ≤ X.length

theorem listFacts_of {X : List ℕ} {p : ℕ} {ws : List (List ℕ)} {r : List ℕ}
    (hx : X.drop p = toWord ws ++ r) : ListFacts X p where
  frPos_le j hj := ⟨(frPos_le_listEnd hx hj).1, (frPos_le_listEnd hx hj).2.1⟩
  end_le := by
    rw [(listAt hx).2.2.2.1]
    exact le_of_drop_eq hx (by rw [toWord_words]; simp)

theorem xg_lt {X : List ℕ} {B i : ℕ} (hX : ∀ v ∈ X, v < B) (hB : 0 < B) : xg X i < B := by
  unfold xg
  rw [List.getD_eq_getElem?_getD]
  cases h : X[i]? with
  | none => simpa
  | some v => exact hX v (List.mem_of_getElem? h)

theorem getD_eq_xg (X : List ℕ) (i : ℕ) : X.getD i 0 = xg X i := rfl

theorem xg_of_lt {X : List ℕ} {i : ℕ} (h : i < X.length) : xg X i = X[i] := by
  simp [xg, List.getElem?_eq_getElem h]

theorem skipList_spec (B : ℕ) (X : List ℕ) (p : ℕ) (hL : ListFacts X p)
    (hXB : X.length + 1 < B) (hX : ∀ v ∈ X, v < B) :
    Spec B (fun τ => τ.arrs "x" = X ∧ τ.vars "y" = p) skipList
      (fun _ τ' => τ'.vars "y" = listEnd X p) (24 * X.length + 20) := by
  rintro τ ⟨hxa, hy⟩
  have hpl : p < X.length := by have := hL.frPos_le 0 (Nat.zero_le _); have := hL.end_le; omega
  have hN : xg X p ≤ X.length := by have := hL.frPos_le _ le_rfl; have := hL.end_le; omega
  let I : Env → Prop := fun ρ => ρ.arrs "x" = X ∧ ρ.vars "e1" = xg X p ∧ ρ.vars "e2" ≤ xg X p ∧
    ρ.vars "y" = frPos X p (ρ.vars "e2")
  have hbody : Spec B (fun ρ => I ρ ∧ ρ.vars "e2" < xg X p) skipBody
      (fun ρ ρ' => I ρ' ∧ ρ'.vars "e2" = ρ.vars "e2" + 1) 20 := by
    rintro ρ ⟨⟨hxa, he1, hle, hy⟩, hlt⟩
    obtain ⟨-, h1⟩ := hL.frPos_le (ρ.vars "e2" + 1) (by omega)
    have h2 := hL.end_le
    have hs : frPos X p (ρ.vars "e2" + 1) = frPos X p (ρ.vars "e2") + 1 + xg X (frPos X p (ρ.vars "e2")) :=
      skipFr_succ' _ _ _
    have hyl : frPos X p (ρ.vars "e2") < X.length := by have := hL.end_le; omega
    have hv := xg_of_lt hyl
    unfold skipBody
    run_vcg
    all_goals (try simp only [I])
    all_goals simp_all
    all_goals omega
  have hloop := Spec.forRange (B := B) (P := I) "e2" "e1" I (xg X p) 20 (24 * X.length + 4)
    (fun ρ hI => by have := hI.2.2.1; omega) (fun ρ hI => by rw [hI.2.1]; omega)
    (fun ρ hI => hI.2.1) (fun ρ hI => hI.2.2.1) hbody (fun _ h => h)
    (fun ρ hI => by have := Nat.sub_le (xg X p) (ρ.vars "e2"); nlinarith)
  unfold skipList
  run_vcg [hloop]
  · rename_i w h
    obtain ⟨⟨-, -, -, hy'⟩, he⟩ := h
    rw [hy', he]; rfl
  · rw [hxa, hy]; exact hpl
  · rw [hxa, hy]; exact xg_lt hX (by omega)
  · refine ⟨by simp [hxa], by simp [hxa, hy, xg, List.getD_eq_getElem?_getD], by simp, by simp [hy, frPos, skipFr]⟩

theorem getD_set_of_lt {l : List ℕ} {i : ℕ} (hi : i < l.length) (v j : ℕ) :
    (l.set i v).getD j 0 = if j = i then v else l.getD j 0 := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h
  · subst h; rw [List.getElem?_set_self hi]; rfl
  · rw [List.getElem?_set_ne (Ne.symm h)]

/-- List one child for every frame of the list of extensions at `y`. -/
def pushBody : Com :=
  .seq (.store "pos" (.var "nn") (.add (.var "y") (.lit 2)))
    (.seq (.store "dep" (.var "nn") (.add (.var "dd") (.lit 1)))
      (.seq (.assign "nn" (.add (.var "nn") (.lit 1)))
        (.seq (.assign "y" (.add (.add (.var "y") (.get "x" (.var "y"))) (.lit 1)))
          (.assign "e2" (.add (.var "e2") (.lit 1))))))

/-- List the children of the extensions at `y`. -/
def pushList : Com :=
  .seq (.assign "e1" (.get "x" (.var "y"))) (.seq (.assign "y" (.add (.var "y") (.lit 1)))
    (.seq (.assign "e2" (.lit 0)) (.while (.lt (.var "e2") (.var "e1")) pushBody)))

/-- What `pushList` leaves in the arrays: old entries below `n0` are
kept, and entry `n0 + j` describes the child of frame `j`. -/
def Pushed (X : List ℕ) (e n0 d k : ℕ) (PS DS : List ℕ) (ρ : Env) : Prop :=
  (ρ.arrs "pos").length = PS.length ∧ (ρ.arrs "dep").length = DS.length ∧
    (∀ c < n0, (ρ.arrs "pos").getD c 0 = PS.getD c 0 ∧ (ρ.arrs "dep").getD c 0 = DS.getD c 0) ∧
    (∀ j < k, (ρ.arrs "pos").getD (n0 + j) 0 = frPos X e j + 2 ∧
      (ρ.arrs "dep").getD (n0 + j) 0 = d + 1)

theorem pushList_spec (B : ℕ) (X : List ℕ) (e n0 d : ℕ) (PS DS : List ℕ) (hL : ListFacts X e)
    (hXB : X.length + 2 < B) (hX : ∀ v ∈ X, v < B) (hdB : d + 1 < B) (hnB : n0 + xg X e < B)
    (hPS : n0 + xg X e ≤ PS.length) (hDS : n0 + xg X e ≤ DS.length) :
    Spec B (fun τ => τ.arrs "x" = X ∧ τ.vars "y" = e ∧ τ.vars "nn" = n0 ∧ τ.vars "dd" = d ∧
        τ.arrs "pos" = PS ∧ τ.arrs "dep" = DS) pushList
      (fun _ τ' => τ'.arrs "x" = X ∧ τ'.vars "y" = listEnd X e ∧ τ'.vars "nn" = n0 + xg X e ∧
        τ'.vars "dd" = d ∧ Pushed X e n0 d (xg X e) PS DS τ') (32 * X.length + 20) := by
  rintro τ ⟨hxa, hy, hnn, hdd, hpa, hda⟩
  have hpl : e < X.length := by have := hL.frPos_le 0 (Nat.zero_le _); have := hL.end_le; omega
  have hN : xg X e ≤ X.length := by have := hL.frPos_le _ le_rfl; have := hL.end_le; omega
  let I : Env → Prop := fun ρ => ρ.arrs "x" = X ∧ ρ.vars "e1" = xg X e ∧ ρ.vars "e2" ≤ xg X e ∧
    ρ.vars "y" = frPos X e (ρ.vars "e2") ∧ ρ.vars "nn" = n0 + ρ.vars "e2" ∧ ρ.vars "dd" = d ∧
    Pushed X e n0 d (ρ.vars "e2") PS DS ρ
  have hbody : Spec B (fun ρ => I ρ ∧ ρ.vars "e2" < xg X e) pushBody
      (fun ρ ρ' => I ρ' ∧ ρ'.vars "e2" = ρ.vars "e2" + 1) 28 := by
    rintro ρ ⟨⟨hxa, he1, hle, hy, hnn, hdd, hpl, hdl, hold, hnew⟩, hlt⟩
    obtain ⟨-, h1⟩ := hL.frPos_le (ρ.vars "e2" + 1) (by omega)
    have h2 := hL.end_le
    have hs : frPos X e (ρ.vars "e2" + 1) = frPos X e (ρ.vars "e2") + 1 + xg X (frPos X e (ρ.vars "e2")) :=
      skipFr_succ' _ _ _
    have hyl : frPos X e (ρ.vars "e2") < X.length := by omega
    have hv := xg_of_lt hyl
    have hp1 : ρ.vars "nn" < (ρ.arrs "pos").length := by omega
    have hd1 : ρ.vars "nn" < (ρ.arrs "dep").length := by omega
    unfold pushBody
    run_vcg
    all_goals (try simp only [I])
    · simp only [vars_setVar, arrs_setVar, arrs_setArr, vars_setArr, if_true, if_false,
        show ("e2" : String) = "y" ↔ False by decide, show ("e2" : String) = "nn" ↔ False by decide,
        show ("y" : String) = "nn" ↔ False by decide, show ("y" : String) = "e2" ↔ False by decide,
        show ("nn" : String) = "y" ↔ False by decide, show ("nn" : String) = "e2" ↔ False by decide,
        show ("e1" : String) = "y" ↔ False by decide, show ("e1" : String) = "nn" ↔ False by decide,
        show ("e1" : String) = "e2" ↔ False by decide, show ("dd" : String) = "y" ↔ False by decide,
        show ("dd" : String) = "nn" ↔ False by decide, show ("dd" : String) = "e2" ↔ False by decide,
        show ("x" : String) = "pos" ↔ False by decide, show ("x" : String) = "dep" ↔ False by decide,
        show ("pos" : String) = "dep" ↔ False by decide, show ("dep" : String) = "pos" ↔ False by decide,
        Pushed]
      refine ⟨⟨hxa, he1, by omega, ?_, by omega, hdd, ?_, ?_, ?_, ?_⟩, trivial⟩
      · rw [hs, hy, hxa, getD_eq_xg]; omega
      · simp [hpl]
      · simp [hdl]
      · intro c hc
        rw [getD_set_of_lt hp1, getD_set_of_lt (by simpa using hd1), if_neg (by omega),
          if_neg (by omega)]
        exact hold c hc
      · intro j hj
        rw [getD_set_of_lt hp1, getD_set_of_lt (by simpa using hd1)]
        by_cases hje : j = ρ.vars "e2"
        · subst hje; rw [if_pos (by omega), if_pos (by omega), hy]; exact ⟨rfl, by rw [hdd]⟩
        · rw [if_neg (by omega), if_neg (by omega)]; exact hnew j (by omega)
    all_goals simp_all
    all_goals omega
  have hloop := Spec.forRange (B := B) (P := I) "e2" "e1" I (xg X e) 28 (32 * X.length + 4)
    (fun ρ hI => by have := hI.2.2.1; omega) (fun ρ hI => by rw [hI.2.1]; omega)
    (fun ρ hI => hI.2.1) (fun ρ hI => hI.2.2.1) hbody (fun _ h => h)
    (fun ρ hI => by have := Nat.sub_le (xg X e) (ρ.vars "e2"); nlinarith)
  unfold pushList
  run_vcg [hloop]
  · rename_i w h
    obtain ⟨⟨hx', -, -, hy', hnn', hdd', hpu⟩, he⟩ := h
    refine ⟨hx', by rw [hy', he]; rfl, by rw [hnn', he], hdd', ?_⟩
    rw [he] at hpu; exact hpu
  · rw [hxa, hy]; exact hpl
  · rw [hxa, hy]; exact xg_lt hX (by omega)
  · refine ⟨by simp [hxa], by simp [hxa, hy, xg, List.getD_eq_getElem?_getD], by simp,
      by simp [hy, frPos, skipFr], by simp [hnn], by simp [hdd], ?_⟩
    refine ⟨by simp [hpa], by simp [hda], fun c _ => by simp [hpa, hda], fun j hj => by simp at hj⟩

/-! ### The scan -/

/-- The length of the word of the node of height `h` at `p`. -/
def nlen (X : List ℕ) (p h : ℕ) : ℕ := nodeEnd X p h - p

/-- The total length of the words of the listed nodes `a, …, b - 1`. -/
def qsum (X : List ℕ) (q : ℕ) (PA DA : List ℕ) (a b : ℕ) : ℕ :=
  ∑ c ∈ Finset.Ico a b, nlen X (PA.getD c 0) (q - DA.getD c 0)

theorem qsum_congr {X : List ℕ} {q : ℕ} {PA DA PA' DA' : List ℕ} {a b : ℕ}
    (h : ∀ c, a ≤ c → c < b → PA'.getD c 0 = PA.getD c 0 ∧ DA'.getD c 0 = DA.getD c 0) :
    qsum X q PA' DA' a b = qsum X q PA DA a b := by
  unfold qsum
  refine Finset.sum_congr rfl fun c hc => ?_
  rw [Finset.mem_Ico] at hc
  rw [(h c hc.1 hc.2).1, (h c hc.1 hc.2).2]

theorem qsum_succ_bot {X : List ℕ} {q : ℕ} {PA DA : List ℕ} {a b : ℕ} (h : a < b) :
    qsum X q PA DA a b = nlen X (PA.getD a 0) (q - DA.getD a 0) + qsum X q PA DA (a + 1) b := by
  unfold qsum; rw [Finset.sum_eq_sum_Ico_succ_bot h]

theorem qsum_split {X : List ℕ} {q : ℕ} {PA DA : List ℕ} {a b c : ℕ} (h1 : a ≤ b) (h2 : b ≤ c) :
    qsum X q PA DA a c = qsum X q PA DA a b + qsum X q PA DA b c := by
  unfold qsum; rw [Finset.sum_Ico_consecutive _ h1 h2]

/-- The children listed for the frames of a list of extensions have a
total length of `listEnd - (e + 1) - 2 m`. -/
theorem qsum_children {X : List ℕ} {q : ℕ} {PA DA : List ℕ} {n0 e d h : ℕ}
    (hq : q - (d + 1) = h)
    (hP : ∀ j < xg X e, PA.getD (n0 + j) 0 = frPos X e j + 2 ∧ DA.getD (n0 + j) 0 = d + 1)
    (hE : ∀ j < xg X e, nodeEnd X (frPos X e j + 2) h = frPos X e (j + 1) ∧
      1 ≤ xg X (frPos X e j)) :
    ∀ m ≤ xg X e, qsum X q PA DA n0 (n0 + m) + e + 1 + 2 * m = frPos X e m := by
  intro m
  induction m with
  | zero => intro _; simp [qsum, frPos, skipFr]
  | succ m ih =>
    intro hm
    have ih' := ih (by omega)
    rw [show n0 + (m + 1) = n0 + m + 1 by omega, qsum, Finset.sum_Ico_succ_top (by omega), ← qsum]
    rw [(hP m (by omega)).1, (hP m (by omega)).2, hq, nlen, (hE m (by omega)).1]
    have h3 : frPos X e (m + 1) = frPos X e m + 1 + xg X (frPos X e m) := skipFr_succ' _ _ _
    have := (hE m (by omega)).2
    omega

/-- Scan node `u`: skip its atoms, record its first child, and list its
children. -/
def bfsBody : Com :=
  .seq (.assign "y" (.get "pos" (.var "u"))) (.seq (.assign "dd" (.get "dep" (.var "u")))
    (.seq skipList (.seq (.store "fc" (.var "u") (.var "nn"))
      (.seq (.ite (.lt (.var "dd") (.var "hq")) pushList .skip)
        (.assign "u" (.add (.var "u") (.lit 1)))))))

/-- List all nodes, from the root at position `0`. -/
def bfs : Com :=
  .seq (.store "pos" (.lit 0) (.lit 0)) (.seq (.store "dep" (.lit 0) (.lit 0))
    (.seq (.assign "nn" (.lit 1)) (.seq (.assign "u" (.lit 0))
      (.while (.lt (.var "u") (.var "nn")) bfsBody))))

/-- The listed nodes are nodes of the tree. -/
def NodesOK (X : List ℕ) (q n : ℕ) (PA DA : List ℕ) : Prop :=
  ∀ c < n, DA.getD c 0 ≤ q ∧ NodeAt X (PA.getD c 0) (q - DA.getD c 0)

/-- The scanned nodes have their children listed. -/
def ScannedOK (X : List ℕ) (q u n : ℕ) (PA DA FA : List ℕ) : Prop :=
  ∀ c < u, c < FA.getD c 0 ∧ FA.getD c 0 ≤ n ∧ (DA.getD c 0 < q →
    ∀ j < xg X (listEnd X (PA.getD c 0)), FA.getD c 0 + j < n ∧
      PA.getD (FA.getD c 0 + j) 0 = frPos X (listEnd X (PA.getD c 0)) j + 2 ∧
      DA.getD (FA.getD c 0 + j) 0 = DA.getD c 0 + 1)

/-- The invariant of the scan. -/
def BfsInv (X : List ℕ) (q PL : ℕ) (τ : Env) : Prop :=
  τ.arrs "x" = X ∧ τ.vars "hq" = q ∧ τ.vars "u" ≤ τ.vars "nn" ∧ 1 ≤ τ.vars "nn" ∧
    τ.vars "nn" + qsum X q (τ.arrs "pos") (τ.arrs "dep") (τ.vars "u") (τ.vars "nn") ≤
      nodeEnd X 0 q + 1 ∧
    (τ.arrs "pos").length = PL ∧ (τ.arrs "dep").length = PL ∧ (τ.arrs "fc").length = PL ∧
    NodesOK X q (τ.vars "nn") (τ.arrs "pos") (τ.arrs "dep") ∧
    ScannedOK X q (τ.vars "u") (τ.vars "nn") (τ.arrs "pos") (τ.arrs "dep") (τ.arrs "fc") ∧
    (τ.arrs "pos").getD 0 0 = 0 ∧ (τ.arrs "dep").getD 0 0 = 0

theorem bfsBody_spec (B : ℕ) (X : List ℕ) (q PL : ℕ) (hXB : X.length + 2 < B)
    (hX : ∀ v ∈ X, v < B) (hqB : q + 1 < B) (hPL : nodeEnd X 0 q + 1 ≤ PL)
    (hL0X : nodeEnd X 0 q ≤ X.length) :
    Spec B (fun τ => BfsInv X q PL τ ∧ τ.vars "u" < τ.vars "nn") bfsBody
      (fun τ τ' => BfsInv X q PL τ' ∧ τ'.vars "u" = τ.vars "u" + 1) (60 * X.length + 80) := by
  rintro τ ⟨⟨hxa, hhq, hun, hn1, hsum, hpl, hdl, hfl, hnodes, hscan, hr0, hd0⟩, hlt⟩
  set u := τ.vars "u" with hu
  set n := τ.vars "nn" with hn
  set PA := τ.arrs "pos" with hPA
  set DA := τ.arrs "dep" with hDA
  set FA := τ.arrs "fc" with hFA
  set L0 := nodeEnd X 0 q with hL0
  set p := PA.getD u 0 with hp
  set d := DA.getD u 0 with hd
  obtain ⟨hdq, hN⟩ := hnodes u hlt
  have hsplit := qsum_succ_bot (X := X) (q := q) (PA := PA) (DA := DA) hlt
  rw [← hp, ← hd] at hsplit
  have hnL : n ≤ L0 + 1 := by omega
  have huPL : u < PL := by omega
  obtain ⟨-, hpe, hen, hnx⟩ := hN.atoms
  obtain ⟨ws, r, hws⟩ := hN.atomList
  have hLF : ListFacts X p := listFacts_of hws
  have hpB : p < B := by omega
  have hdB : d < B := by omega
  -- the first two assignments and the skip
  set τ1 := (τ.setVar "y" p).setVar "dd" d with hτ1
  have hev1 : (Expr.get "pos" (.var "u")).evalB B τ = some p := by
    · simp only [evalB_get_iff, evalB_var_iff]
      refine ⟨u, ⟨rfl, by omega⟩, ?_, hpB⟩
      rw [← hPA, List.getElem?_eq_getElem (by omega)]; simp [hp, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show u < PA.length by omega)]
  have hev2 : (Expr.get "dep" (.var "u")).evalB B (τ.setVar "y" p) = some d := by
    · simp only [evalB_get_iff, evalB_var_iff, vars_setVar, arrs_setVar]
      refine ⟨u, ⟨by simp [hu], by simp; omega⟩, ?_, hdB⟩
      rw [← hDA, List.getElem?_eq_getElem (by omega)]; simp [hd, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show u < DA.length by omega)]
  obtain ⟨τ2, hr2, hy2⟩ := skipList_spec B X p hLF (by omega) hX τ1 ⟨by simp [hτ1, hxa], by simp [hτ1]⟩
  have hv2 : ∀ y, y ∉ skipList.wvars → τ2.vars y = τ1.vars y := fun y h => hr2.frame_var y h
  have ha2 : ∀ a, a ∉ skipList.warrs → τ2.arrs a = τ1.arrs a := fun a h => hr2.frame_arr a h
  have hn2 : τ2.vars "nn" = n := by rw [hv2 "nn" (by decide)]; simp [hτ1, hn]
  have hu2 : τ2.vars "u" = u := by rw [hv2 "u" (by decide)]; simp [hτ1, hu]
  have hdd2 : τ2.vars "dd" = d := by rw [hv2 "dd" (by decide)]; simp [hτ1]
  have hq2 : τ2.vars "hq" = q := by rw [hv2 "hq" (by decide)]; simp [hτ1, hhq]
  have hfa2 : τ2.arrs "fc" = FA := by rw [ha2 "fc" (by decide)]; simp [hτ1, hFA]
  have hpa2 : τ2.arrs "pos" = PA := by rw [ha2 "pos" (by decide)]; simp [hτ1, hPA]
  have hda2 : τ2.arrs "dep" = DA := by rw [ha2 "dep" (by decide)]; simp [hτ1, hDA]
  have hxa2 : τ2.arrs "x" = X := by rw [ha2 "x" (by decide)]; simp [hτ1, hxa]
  set τ3 := τ2.setArr "fc" u n with hτ3
  have hr3 : Run B (.store "fc" (.var "u") (.var "nn")) τ2 τ3 3 := by
    refine (Run.store ?_ ?_ ?_).mono (by simp)
    · simp [hu2]; omega
    · simp [hn2]; omega
    · rw [hfa2]; omega
  have hfa3 : τ3.arrs "fc" = FA.set u n := by simp [hτ3, hfa2]
  have hfc_old : ∀ c, c ≠ u → (FA.set u n).getD c 0 = FA.getD c 0 := fun c hc => by
    rw [getD_set_of_lt (by omega), if_neg hc]
  have hfc_new : (FA.set u n).getD u 0 = n := by rw [getD_set_of_lt (by omega), if_pos rfl]
  by_cases hdq' : d < q
  · -- an inner node: list its children
    have hN' : NodeAt X p (q - d - 1 + 1) := by rwa [show q - d - 1 + 1 = q - d by omega]
    obtain ⟨hch, -, hend⟩ := hN'.exts
    set e := listEnd X p with he
    set m := xg X e with hm
    have hLe : ListFacts X e := by
      obtain ⟨ℓ, t, r, hx⟩ := hN'
      exact listFacts_of (nodeSplit hx).2
    have hme : e + 1 + m ≤ listEnd X e := by
      have := hLe.frPos_le m le_rfl; omega
    have hnlen : nlen X p (q - d) = listEnd X e - p := by
      rw [nlen, show q - d = q - d - 1 + 1 by omega, hend]
    have hpe' : p + 1 ≤ e := by omega
    obtain ⟨τ4, hr4, hxa4, hy4, hn4, hdd4, hpu⟩ := pushList_spec B X e n d PA DA hLe (by omega) hX
      (by omega) (by have := hLe.end_le; omega) (by omega) (by omega) τ3
      ⟨by simp [hτ3, hxa2], by simp [hτ3, hy2], by simp [hτ3, hn2], by simp [hτ3, hdd2],
        by simp [hτ3, hpa2], by simp [hτ3, hda2]⟩
    obtain ⟨hpl4, hdl4, hold4, hnew4⟩ := hpu
    have hv4 : ∀ y, y ∉ pushList.wvars → τ4.vars y = τ3.vars y := fun y h => hr4.frame_var y h
    have ha4 : ∀ a, a ∉ pushList.warrs → τ4.arrs a = τ3.arrs a := fun a h => hr4.frame_arr a h
    have hu4 : τ4.vars "u" = u := by rw [hv4 "u" (by decide)]; simp [hτ3, hu2]
    have hq4 : τ4.vars "hq" = q := by rw [hv4 "hq" (by decide)]; simp [hτ3, hq2]
    have hfa4 : τ4.arrs "fc" = FA.set u n := by rw [ha4 "fc" (by decide)]; exact hfa3
    set PA' := τ4.arrs "pos" with hPA'
    set DA' := τ4.arrs "dep" with hDA'
    have hold' : ∀ c, c < n → PA'.getD c 0 = PA.getD c 0 ∧ DA'.getD c 0 = DA.getD c 0 := hold4
    refine ⟨τ4.setVar "u" (u + 1), ?_, ?_, by simp [hu]⟩
    · have hc : (Cond.lt (.var "dd") (.var "hq")).evalB B τ3 = some true := by
        have h1 : τ3.vars "dd" = d := by simp [hτ3, hdd2]
        have h2 : τ3.vars "hq" = q := by simp [hτ3, hq2]
        simp only [evalB_condLt_iff, evalB_var_iff, h1, h2]
        exact ⟨d, q, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, by simp [hdq']⟩
      unfold bfsBody
      refine (Run.seq (Run.assign hev1) (Run.seq (Run.assign hev2) (Run.seq hr2 (Run.seq hr3
        (Run.seq (Run.ite_true hc hr4) (Run.assign (v := u + 1) ?_)))))).mono ?_
      · simp [hu4]; omega
      · simp; omega
    · have hqs1 := qsum_congr (X := X) (q := q) (a := u + 1) (b := n) (PA := PA) (DA := DA)
        (PA' := PA') (DA' := DA') (fun c _ hc => hold' c hc)
      have hqs2 := qsum_children (X := X) (q := q) (PA := PA') (DA := DA') (n0 := n) (e := e)
        (d := d) (h := q - d - 1) (by omega) (fun j hj => hnew4 j hj)
        (fun j hj => ⟨(hch j hj).2.1, (hch j hj).2.2⟩) m le_rfl
      have hsp := qsum_split (X := X) (q := q) (PA := PA') (DA := DA')
        (show u + 1 ≤ n by omega) (show n ≤ n + m by omega)
      have hfm : frPos X e m = listEnd X e := rfl
      refine ⟨by simp [hxa4], by simp [hq4], by simp [hn4]; omega, by simp [hn4]; omega, ?_,
        by simp only [arrs_setVar]; rw [← hPA', hpl4, hpl],
        by simp only [arrs_setVar]; rw [← hDA', hdl4, hdl],
        by simp only [arrs_setVar, hfa4, List.length_set, hfl], ?_, ?_, ?_, ?_⟩
      · simp only [vars_setVar, arrs_setVar, if_true, hn4,
          show ("nn" : String) = "u" ↔ False by decide, if_false]
        rw [← hPA', ← hDA', hsp, hqs1]
        omega
      · intro c hc
        simp only [vars_setVar, arrs_setVar, hn4, show ("nn" : String) = "u" ↔ False by decide,
          if_false] at hc ⊢
        rw [← hPA', ← hDA']
        by_cases hcn : c < n
        · rw [(hold' c hcn).1, (hold' c hcn).2]; exact hnodes c hcn
        · obtain ⟨j, rfl⟩ : ∃ j, c = n + j := ⟨c - n, by omega⟩
          rw [(hnew4 j (by omega)).1, (hnew4 j (by omega)).2]
          refine ⟨by omega, ?_⟩
          rw [show q - (d + 1) = q - d - 1 by omega]
          exact (hch j (by omega)).1
      · intro c hc
        simp only [vars_setVar, arrs_setVar, hn4, if_true, show ("nn" : String) = "u" ↔ False by decide,
          if_false, hfa4] at hc ⊢
        rw [← hPA', ← hDA']
        by_cases hcu : c = u
        · subst hcu
          rw [hfc_new]
          refine ⟨by omega, by omega, fun _ j hj => ?_⟩
          rw [(hold' u hlt).1] at hj ⊢
          rw [(hold' u hlt).2]
          change j < m at hj
          exact ⟨by omega, (hnew4 j hj).1, (hnew4 j hj).2⟩
        · have hcu' : c < u := by omega
          rw [hfc_old c hcu]
          obtain ⟨h1, h2, h3⟩ := hscan c hcu'
          have hcn : c < n := by omega
          refine ⟨h1, by omega, fun hdc j hj => ?_⟩
          rw [(hold' c hcn).1, (hold' c hcn).2] at *
          obtain ⟨h4, h5, h6⟩ := h3 hdc j hj
          rw [(hold' _ h4).1, (hold' _ h4).2]
          exact ⟨by omega, h5, h6⟩
      · simp only [arrs_setVar]; rw [← hPA', (hold' 0 (by omega)).1]; exact hr0
      · simp only [arrs_setVar]; rw [← hDA', (hold' 0 (by omega)).2]; exact hd0
  · -- a leaf
    have hc : (Cond.lt (.var "dd") (.var "hq")).evalB B τ3 = some false := by
      have h1 : τ3.vars "dd" = d := by simp [hτ3, hdd2]
      have h2 : τ3.vars "hq" = q := by simp [hτ3, hq2]
      simp only [evalB_condLt_iff, evalB_var_iff, h1, h2]
      exact ⟨d, q, ⟨rfl, by omega⟩, ⟨rfl, by omega⟩, by simp [hdq']⟩
    have hu3 : τ3.vars "u" = u := by simp [hτ3, hu2]
    refine ⟨τ3.setVar "u" (u + 1), ?_, ?_, by simp [hu]⟩
    · unfold bfsBody
      refine (Run.seq (Run.assign hev1) (Run.seq (Run.assign hev2) (Run.seq hr2 (Run.seq hr3
        (Run.seq (Run.ite_false hc Run.skip) (Run.assign (v := u + 1) ?_)))))).mono ?_
      · simp [hu3]; omega
      · simp; omega
    · have hpa3 : τ3.arrs "pos" = PA := by simp [hτ3, hpa2]
      have hda3 : τ3.arrs "dep" = DA := by simp [hτ3, hda2]
      have hn3 : τ3.vars "nn" = n := by simp [hτ3, hn2]
      refine ⟨by simp [hτ3, hxa2], by simp [hτ3, hq2], by simp [hn3]; omega, by simp [hn3]; omega,
        ?_, by simp [hpa3, hpl], by simp [hda3, hdl], by simp [hfa3, hfl], ?_, ?_, ?_, ?_⟩
      · simp only [vars_setVar, arrs_setVar, if_true, hn3, hpa3, hda3,
          show ("nn" : String) = "u" ↔ False by decide, if_false]
        omega
      · simp only [vars_setVar, arrs_setVar, hn3, hpa3, hda3,
          show ("nn" : String) = "u" ↔ False by decide, if_false]
        exact hnodes
      · intro c hc
        simp only [vars_setVar, arrs_setVar, hn3, hpa3, hda3, hfa3, if_true,
          show ("nn" : String) = "u" ↔ False by decide, if_false] at hc ⊢
        by_cases hcu : c = u
        · subst hcu
          rw [hfc_new]
          exact ⟨by omega, le_rfl, fun h => absurd h hdq'⟩
        · rw [hfc_old c hcu]
          obtain ⟨h1, h2, h3⟩ := hscan c (by omega)
          exact ⟨h1, h2, h3⟩
      · simp only [arrs_setVar, hpa3]; exact hr0
      · simp only [arrs_setVar, hda3]; exact hd0

/-- **The scan.** Started on the word of a tree of height `q` at the
front of `x`, `bfs` lists all nodes. -/
theorem bfs_spec (B : ℕ) (X : List ℕ) (q PL : ℕ) (hXB : X.length + 2 < B)
    (hX : ∀ v ∈ X, v < B) (hqB : q + 1 < B) (hroot : NodeAt X 0 q)
    (hPL : nodeEnd X 0 q + 1 ≤ PL) :
    Spec B (fun τ => τ.arrs "x" = X ∧ τ.vars "hq" = q ∧ (τ.arrs "pos").length = PL ∧
        (τ.arrs "dep").length = PL ∧ (τ.arrs "fc").length = PL) bfs
      (fun _ τ' => BfsInv X q PL τ' ∧ τ'.vars "u" = τ'.vars "nn")
      ((60 * X.length + 84) * (X.length + 1) + 30) := by
  rintro τ ⟨hxa, hhq, hpl, hdl, hfl⟩
  have hL0X : nodeEnd X 0 q ≤ X.length := hroot.listEnd_le.2
  have h0e : 0 < nodeEnd X 0 q := by have := hroot.atoms.2.1; have := hroot.atoms.2.2.1; omega
  set τ0 := (((τ.setArr "pos" 0 0).setArr "dep" 0 0).setVar "nn" 1).setVar "u" 0 with hτ0
  have hI0 : BfsInv X q PL τ0 := by
    have hp0 : (τ0.arrs "pos").getD 0 0 = 0 := by
      simp [hτ0, List.getD_eq_getElem?_getD, List.getElem?_set_self (show 0 < (τ.arrs "pos").length by omega)]
    have hd0 : (τ0.arrs "dep").getD 0 0 = 0 := by
      simp [hτ0, List.getD_eq_getElem?_getD, List.getElem?_set_self (show 0 < (τ.arrs "dep").length by omega)]
    refine ⟨by simp [hτ0, hxa], by simp [hτ0, hhq], by simp [hτ0], by simp [hτ0], ?_,
      by simp [hτ0, hpl], by simp [hτ0, hdl], by simp [hτ0, hfl], ?_, fun c hc => by simp [hτ0] at hc,
      hp0, hd0⟩
    · have : qsum X q (τ0.arrs "pos") (τ0.arrs "dep") 0 1 = nodeEnd X 0 q := by
        simp only [qsum, Nat.Ico_zero_eq_range, Finset.range_one, Finset.sum_singleton, hp0, hd0,
          nlen, Nat.sub_zero]
      simp only [hτ0, vars_setVar, if_true, show ("nn" : String) = "u" ↔ False by decide, if_false]
      rw [← hτ0, this]; omega
    · intro c hc
      simp only [hτ0, vars_setVar, show ("nn" : String) = "u" ↔ False by decide, if_false, if_true] at hc
      obtain rfl : c = 0 := by omega
      rw [hp0, hd0]; exact ⟨by omega, by simpa using hroot⟩
  have hbody : Spec B (fun ρ => BfsInv X q PL ρ ∧
      (Cond.lt (.var "u") (.var "nn")).evalB B ρ = some true) bfsBody
      (fun ρ ρ' => BfsInv X q PL ρ' ∧
        nodeEnd X 0 q + 1 - ρ'.vars "u" < nodeEnd X 0 q + 1 - ρ.vars "u") (60 * X.length + 80) :=
    (bfsBody_spec B X q PL hXB hX hqB hPL hL0X).conseq
      (fun ρ ⟨hI, hc⟩ => ⟨hI, lt_of_condLt_true hc⟩)
      (fun ρ ρ' ⟨hI, hc⟩ ⟨hI', hu'⟩ => ⟨hI', by
        have := lt_of_condLt_true hc; have := hI.2.2.2.2.1; omega⟩) le_rfl
  have hK : ∀ σ, σ = τ0 → (1 + (Cond.lt (.var "u") (.var "nn")).size + (60 * X.length + 80)) *
      (nodeEnd X 0 q + 1 - σ.vars "u") + 1 + (Cond.lt (.var "u") (.var "nn")).size ≤
      (60 * X.length + 84) * (X.length + 1) + 4 := by
    intro ρ h; subst h
    simp only [hτ0, vars_setVar, if_true, Cond.size, Expr.size, Nat.sub_zero]
    have := Nat.mul_le_mul_left (60 * X.length + 84) (show nodeEnd X 0 q + 1 ≤ X.length + 1 by omega)
    have h2 : 1 + (1 + 1 + 1) + (60 * X.length + 80) = 60 * X.length + 84 := by ring
    rw [h2]; omega
  obtain ⟨τ', hr, hI', hfalse⟩ := (Spec.while_count (B := B) (P := fun ρ => ρ = τ0)
    (b := .lt (.var "u") (.var "nn")) (c := bfsBody) (K := (60 * X.length + 84) * (X.length + 1) + 4)
    (BfsInv X q PL) (fun ρ => nodeEnd X 0 q + 1 - ρ.vars "u") (60 * X.length + 80)
    (fun ρ hI => evalB_condLt_vars (by have := hI.2.2.1; have := hI.2.2.2.2.1; omega)
      (by have := hI.2.2.2.2.1; omega))
    hbody (fun ρ h => h ▸ hI0) hK).run rfl
  · refine ⟨τ', ?_, hI', ?_⟩
    · unfold bfs
      refine (Run.seq (Run.store (idx := 0) (v := 0) (by simp; omega) (by simp; omega) (by omega))
        (Run.seq (Run.store (idx := 0) (v := 0) (by simp; omega) (by simp; omega) (by simp; omega))
          (Run.seq (Run.assign (v := 1) (by simp; omega)) (Run.seq (Run.assign (v := 0)
            (by simp; omega)) hr)))).mono (by simp; omega)
    · have := le_of_condLt_false hfalse
      have := hI'.2.2.1
      omega

end Lax185574Proofs.Words
