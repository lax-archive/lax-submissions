import Lax185574Proofs.ResolveRam.Glue.PLv1
import Lax185574Proofs.ResolveRam.Glue.R0

/-!
The specification of the item words of level `0` of lem:resolve-lift
(`lv0Cmd_spec`), and a layout for the command (`lv0Cmd_ok`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.FarRam
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574.ResolveLift Lax185574Proofs.ResolveRam

/-- The step of `tu` over the word of the distance matrix, `P`, `Q`, the
sign and the length of the family. -/
def tuE : Expr := .add (.add (.var "tu") (.mul (.var "gn") (.add (.var "gn") (.lit 1)))) (.lit 5)

/-- **The item words of level `0`.** -/
def lv0Cmd : Com :=
  .seq (.assign "tu" (.add (.var "gn") (.lit 1))) (.seq tskG (.seq tskG
    (.seq (.assign "tu" tuE) (.seq (forUp "tb" (.var "gn") lvTree)
      (.assign "pc" (.var "gn"))))))

/-- The scalars that `lv0Cmd` writes. -/
def lv0V : List String := ["tu", "tgc", "tcv", "tb", "pc", "ts", "tq", "tf", "tn", "tz", "tl", "po", "ci"]

theorem lv0Cmd_wvars : ∀ y ∈ lv0Cmd.wvars, y ∈ lv0V := by decide

/-- An array that holds `X` as a prefix, from a position. -/
theorem preAt_drop {a : String} {X : List ℕ} {τ : Env} (h : PreAt a X τ) {p : ℕ} (hp : p ≤ X.length) :
    (τ.arrs a).drop p = X.drop p ++ (τ.arrs a).drop X.length := by
  apply List.ext_getElem?
  intro j
  rw [List.getElem?_drop]
  rcases Nat.lt_or_ge (p + j) X.length with h' | h'
  · rw [List.getElem?_append_left (by simp; omega), List.getElem?_drop, h.get h',
      List.getElem?_eq_getElem h']
  · rw [List.getElem?_append_right (by simp; omega), List.getElem?_drop]
    congr 1; simp; omega

theorem length_frames_item (L : List (List ℕ)) :
    (frames (L.map fun w => 0 :: 0 :: w)).length = L.flatten.length + 3 * L.length := by
  induction L with
  | nil => simp [frames]
  | cons a L ih =>
    simp only [frames, List.map_cons, List.flatten_cons, List.length_append, List.length_cons] at ih ⊢
    rw [ih]; ring

theorem flatten_split (L : List (List ℕ)) {b : ℕ} (hb : b < L.length) :
    L.flatten = (L.take b).flatten ++ (L[b] ++ (L.drop (b + 1)).flatten) := by
  calc L.flatten = (L.take b ++ L.drop b).flatten := by rw [List.take_append_drop]
    _ = _ := by rw [List.drop_eq_getElem_cons hb, List.flatten_append, List.flatten_cons]

/-- **The specification of the item words of level `0`.** -/
theorem lv0Cmd_spec : LV0Spec lv0Cmd lv0V := by
  refine ⟨500, ?_⟩
  intro W k₀ q₀ n G P Q s τ pre hW hA hX hnx hgn hF hRoom
  set X := xIn G k₀ q₀ P Q s with hXdef
  have hRS := room_ge hRoom
  have hSW : 65536 * (ySz X + pre.length + 1) ≤ W := by simpa using hRS
  have hyX : X.length + maxEntry X + 1 = ySz X := rfl
  have hvX : ∀ v ∈ X, v < W + 1 := fun v hv => by have := le_maxEntry hv; omega
  -- the parts of the input
  set FW : List (List ℕ) := List.ofFn fun b => toWord (family G k₀ q₀ b) with hFWdef
  have hFW : FW.length = n := by simp [FW]
  have hG := StpRam.toWord_pg G
  have hXs : X = toWord G ++ (toWord (Lax185574.DistanceMatrix.distMatrix G) ++
      ([P, Q, if s then 1 else 0] ++ (n :: FW.flatten))) := by
    rw [hXdef, xIn_split, toWord_family]
  set pd := (toWord (Lax185574.DistanceMatrix.distMatrix G)).length with hpddef
  have hpd : pd = 1 + n * (n + 1) := Lax185574Proofs.DistMatrix.length_toWord_distMatrix G
  set pg := (toWord G).length with hpgdef
  have hpg : pg = n + 1 + (toWord G.edge).length + (toWord G.nonEdge).length := by
    rw [hpgdef, hG]; simp; omega
  have hbase : X.drop (pg + pd + 4) = FW.flatten := by
    rw [hXs, show pg + pd + 4 = (toWord G).length +
      ((toWord (Lax185574.DistanceMatrix.distMatrix G)).length + 4) by simp only [pg, pd]; omega,
      ← List.drop_drop, List.drop_left, ← List.drop_drop, List.drop_left]; rfl
  have hXl : X.length = pg + pd + 4 + FW.flatten.length := by
    rw [hXs]; simp [pg, pd]; omega
  have hAx : (τ.arrs "x").length = W + 1 := hA "x"
  -- the word of the graph
  have hn1 : n + 1 < W + 1 := by omega
  set τ1 := τ.setVar "tu" (n + 1)
  have r1 : Run (W + 1) (.assign "tu" (.add (.var "gn") (.lit 1))) τ τ1 4 :=
    (Run.assign (ev_add (ev_var hgn (by omega)) (evalB_lit (by omega)) (by omega))).mono
      (by simp [Expr.size])
  have hX1 : PreAt "x" X τ1 := fun i h => by simpa [τ1] using hX i h
  have hd1 : X.drop (n + 1) = toWord G.edge ++ (toWord G.nonEdge ++
      (toWord (Lax185574.DistanceMatrix.distMatrix G) ++ ([P, Q, if s then 1 else 0] ++ (n :: FW.flatten)))) := by
    rw [hXs, hG]; simp
  obtain ⟨τ2, r2, hp2, ha2, ho2, hi2, hv2⟩ := tskG_run G.edge hX1 hd1 (by simp [τ1]) (by omega) hvX
  have hX2 : PreAt "x" X τ2 := fun i h => by rw [ha2]; exact hX1 i h
  have hd2 : X.drop (n + 1 + (toWord G.edge).length) = toWord G.nonEdge ++
      (toWord (Lax185574.DistanceMatrix.distMatrix G) ++ ([P, Q, if s then 1 else 0] ++ (n :: FW.flatten))) := by
    rw [← List.drop_drop, hd1, List.drop_left]
  obtain ⟨τ3, r3, hp3, ha3, ho3, hi3, hv3⟩ := tskG_run G.nonEdge hX2 hd2 hp2 (by omega) hvX
  have o3 : OFr τ τ3 ["tu", "tgc", "tcv", "tu", "tgc", "tcv"] := by
    have o1 : OFr τ τ1 ["tu"] := OFr.setVar τ "tu" _
    have o2 : OFr τ1 τ2 ["tu", "tgc", "tcv"] := ⟨hv2, fun b _ => by rw [ha2], by rw [ha2], ho2, hi2⟩
    have o3' : OFr τ2 τ3 ["tu", "tgc", "tcv"] := ⟨hv3, fun b _ => by rw [ha3], by rw [ha3], ho3, hi3⟩
    exact ((o1.trans o2).trans o3').mono (by decide)
  have hgn3 : τ3.vars "gn" = n := by rw [o3.vars "gn" (by decide), hgn]
  set τ4 := τ3.setVar "tu" (pg + pd + 4)
  have hpp : n + 1 + (toWord G.edge).length + (toWord G.nonEdge).length + n * (n + 1) + 5 = pg + pd + 4 := by
    omega
  have hnn : n * (n + 1) ≤ X.length := by omega
  have r4 : Run (W + 1) (.assign "tu" tuE) τ3 τ4 (1 + tuE.size) := by
    have e : tuE.evalB (W + 1) τ3 = some (pg + pd + 4) := by
      rw [← hpp]
      exact ev_add (ev_add (ev_var hp3 (by omega)) (ev_mul (ev_var hgn3 (by omega))
        (ev_add (ev_var hgn3 (by omega)) (evalB_lit (by omega)) (by omega)) (by omega)) (by omega))
        (evalB_lit (by omega)) (by omega)
    exact Run.assign e
  have o4 : OFr τ τ4 ["tu", "tgc", "tcv"] := (o3.trans (OFr.setVar τ3 "tu" _)).mono (by decide)
  have ha4 : τ4.arrs = τ.arrs := by simp [τ4, ha3, ha2, τ1]
  have F4 : Filled "OB" "po" pre τ4 := hF.congr (o4.vars "po" (by decide)) (by rw [ha4])
  -- the trees
  set Xa := τ.arrs "x"
  have hdrop : ∀ b (hb : b < n), Xa.drop (pg + pd + 4 + ((FW.take b).flatten).length) =
      FW[b]'(by omega) ++ ((FW.drop (b + 1)).flatten ++ Xa.drop X.length) := by
    intro b hb
    have hle : pg + pd + 4 + ((FW.take b).flatten).length ≤ X.length := by
      rw [hXl, flatten_split FW (b := b) (by omega)]; simp
    rw [preAt_drop hX hle, ← List.drop_drop, hbase, flatten_split FW (b := b) (by omega), List.drop_left,
      List.append_assoc]
  have hFWb : ∀ b (hb : b < n), FW[b]'(by omega) = toWord (family G k₀ q₀ ⟨b, hb⟩) := by
    intro b hb; simp [FW]
  let I : ℕ → Env → Prop := fun b ρ => ρ.vars "tu" = pg + pd + 4 + ((FW.take b).flatten).length ∧
    Filled "OB" "po" (pre ++ frames ((FW.take b).map fun w => 0 :: 0 :: w)) ρ ∧
    OFr τ4 ρ (lvV0 ++ ["tb"])
  obtain ⟨τ5, r5, ⟨-, F5, o5⟩, -⟩ := forUp_run_sum (B := W + 1) (i := "tb") (e := .var "gn")
    (body := lvTree) (N := n) (fun b => 60 * (FW.getD b []).length + 200) I (σ := τ4) (by omega)
    (fun b _ ρ hI _ => ev_var (by rw [hI.2.2.vars "gn" (by decide), o4.vars "gn" (by decide), hgn])
      (by omega))
    ⟨by simp [τ4], by simpa [frames] using F4.setVar (y := "tb") (by decide) 0,
      (OFr.setVar τ4 "tb" 0).mono (by decide)⟩
    (by
      rintro b hb ρ ⟨uρ, Fρ, oρ⟩ hbρ
      have hxρ : ρ.arrs "x" = Xa := by rw [oρ.arrs "x" (by decide), ha4]
      have hd := hdrop b hb
      rw [hFWb b hb] at hd
      have hsub : (FW.take b).flatten.length + (FW[b]'(by omega)).length ≤ FW.flatten.length := by
        rw [flatten_split FW (b := b) (by omega)]; simp
      rw [hFWb b hb] at hsub
      have hfl : (frames ((FW.take b).map fun w => 0 :: 0 :: w)).length ≤ FW.flatten.length + 3 * n := by
        rw [length_frames_item]
        have : (FW.take b).length ≤ n := by simp; omega
        have h2 : (FW.take b).flatten.length ≤ FW.flatten.length := by
          rw [flatten_split FW (b := b) (by omega)]; simp
        omega
      obtain ⟨ρ', r', F', u', o'⟩ := lvTree_run (W := W) (τ := ρ) hxρ hd uρ Fρ
        (by rw [oρ.len, ha4, hA "OB"]) (by omega) (by simp only [List.length_append]; omega)
        (fun v hv => by
          have : v ∈ Xa.drop (pg + pd + 4 + ((FW.take b).flatten).length) := by rw [hd]; simp [hv]
          have hvm := List.mem_of_mem_drop this
          have hle : pg + pd + 4 + ((FW.take b).flatten).length + (toWord (family G k₀ q₀ ⟨b, hb⟩)).length ≤
              X.length := by omega
          have hd' : X.drop (pg + pd + 4 + ((FW.take b).flatten).length) = toWord (family G k₀ q₀ ⟨b, hb⟩) ++
              (FW.drop (b + 1)).flatten := by
            rw [← List.drop_drop, hbase, flatten_split FW (b := b) (by omega), List.drop_left, hFWb b hb]
          have : v ∈ X.drop (pg + pd + 4 + ((FW.take b).flatten).length) := by rw [hd']; simp [hv]
          exact hvX v (List.mem_of_mem_drop this))
      refine ⟨ρ', ?_, by rw [o'.vars "tb" (by decide), hbρ], ?_, ?_, ?_⟩
      · rw [List.getD_eq_getElem _ _ (by omega), hFWb b hb]; exact r'
      · rw [vars_setVar, if_neg (by decide), u', List.take_add_one, List.getElem?_eq_getElem (by omega)]
        simp [hFWb b hb]; omega
      · rw [List.take_add_one, List.getElem?_eq_getElem (by omega), hFWb b hb]
        simpa [frames_append, List.append_assoc] using F'.setVar (y := "tb") (by decide) (b + 1)
      · exact ((oρ.trans o').trans (OFr.setVar ρ' "tb" _)).mono (by decide))
  have hgn5 : τ5.vars "gn" = n := by rw [o5.vars "gn" (by decide), o4.vars "gn" (by decide), hgn]
  set τ6 := τ5.setVar "pc" n
  have r6 : Run (W + 1) (.assign "pc" (.var "gn")) τ5 τ6 2 := Run.assign (ev_var hgn5 (by omega))
  have hsum := sum_len_drop (ws := FW) (ol := 0) n (by omega)
  simp only [zero_add, List.drop_zero, List.take_of_length_le (le_of_eq hFW)] at hsum
  have htot : total FW = FW.flatten.length := rfl
  refine ⟨τ6, ?_, ?_, by simp [τ6], ?_⟩
  · unfold lv0Cmd
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 r6))))).mono ?_
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hsum]
    simp only [Finset.sum_const, Finset.card_range, smul_eq_mul, Expr.size, tuE]
    have : n ≤ X.length := by omega
    rw [htot]
    omega
  · rw [List.take_of_length_le (le_of_eq hFW)] at F5
    have e : (FW.map fun w => 0 :: 0 :: w) =
        (List.finRange n).map fun b => itemW ((0, 0), family G k₀ q₀ b) := by
      rw [hFWdef, List.map_ofFn, List.ofFn_eq_map]; rfl
    rw [← e]
    exact F5.setVar (by decide) n
  · have oall := (o4.trans o5).trans (OFr.setVar τ5 "pc" n)
    have hsub : ∀ y ∈ ["tu", "tgc", "tcv"] ++ (lvV0 ++ ["tb"]) ++ ["pc"], y ∈ lv0V := by decide
    refine ⟨fun y hy => oall.vars y (fun h => hy (hsub y h)), fun b hb => oall.arrs b
      (by intro h; subst h; simp [keepA] at hb), fun b => ?_, oall.out, oall.inp⟩
    by_cases hb : b = "OB"
    · subst hb; exact oall.len
    · rw [oall.arrs b hb]

/-- A layout for the item words of level `0`. -/
def lv0Layout : Lax808846Proofs.Compile.Layout :=
  ⟨lv0V ++ ["gn"], ["x", "OB"], 6⟩

theorem lv0Cmd_ok : Lax808846Proofs.Compile.Com.Ok lv0Layout lv0Cmd :=
  StpRam.comOkB_sound _ _ (by decide)

end Lax185574Proofs.ResolveRam.Glue
