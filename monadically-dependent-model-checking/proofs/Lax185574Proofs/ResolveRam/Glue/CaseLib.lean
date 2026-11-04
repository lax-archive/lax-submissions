import Lax185574Proofs.ResolveRam.Glue.Asg
import Lax185574Proofs.ResolveRam.Glue.Ans

/-!
Steps shared by the cases of a later round.

* `room_bound`: a passed room check bounds the library, the answer and
  the scalars it reads.
* `apE`, `apY`: append the empty word, or the segment of the answer from
  a literal offset with a literal number of entries cut at the end, to
  the library (`apE_run`, `apY_run`).
* `ev_wd`: the expression `a[st[x] + j]` reads entry `j` of the library
  word with index `x`.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue

theorem room_bound {W R : ℕ} {τ : Env} {ws : List (List ℕ)} {b : List ℕ} (h : RoomOK W R τ ws b)
    (hR : 1 ≤ R) : 2 ^ 30 * sOfV τ ws b ≤ W := by
  set S := sOfV τ ws b
  have hS : 64 ≤ S := by simp only [S, sOfV, sOf]; omega
  have hSS : 2 ^ 24 * S * S < W := by
    have h1 : 1 ≤ R * R * R * R := Nat.one_le_iff_ne_zero.2 (by positivity)
    have : 2 ^ 24 * S * S ≤ 2 ^ 24 * R * R * R * R * S * S := by
      have := Nat.mul_le_mul_left (2 ^ 24 * S * S) h1
      calc 2 ^ 24 * S * S = 2 ^ 24 * S * S * 1 := by ring
        _ ≤ 2 ^ 24 * S * S * (R * R * R * R) := this
        _ = _ := by ring
    exact lt_of_le_of_lt this h
  have : 64 * S ≤ S * S := Nat.mul_le_mul_right _ hS
  have : 2 ^ 30 * S ≤ 2 ^ 24 * S * S := by
    calc 2 ^ 30 * S = 2 ^ 24 * (64 * S) := by ring
      _ ≤ 2 ^ 24 * (S * S) := Nat.mul_le_mul_left _ this
      _ = _ := by ring
  omega

theorem sOfV_ge {τ : Env} {ws : List (List ℕ)} {b : List ℕ} :
    2 * total ws + 2 * ws.length + b.length + τ.vars "po" + τ.vars "nx" + 64 ≤ sOfV τ ws b ∧
      maxEntry ws.flatten ≤ sOfV τ ws b ∧ maxEntry b ≤ sOfV τ ws b ∧ τ.vars "mw" ≤ sOfV τ ws b := by
  simp only [sOfV, sOf]; omega

/-- Append the empty word to the library. -/
def apE : Com := .seq (asgs [("ls", .lit 0), ("lL", .lit 0)]) (lbApp "y")

/-- Append the segment of the answer from `pl`, without its last `dl` entries. -/
def apY (pl dl : ℕ) : Com := .seq (asgs [("ls", .lit pl), ("lL", .sub (.var "bl") (.lit dl))]) (lbApp "y")

/-- The scalars that `apE` and `apY` write. -/
def apV : List String := ["ls", "lL", "ci", "lt", "m"]

theorem apY_run {W pl dl : ℕ} {ws : List (List ℕ)} {b : List ℕ} {τ : Env} (hL : Lib ws τ) (harr : ArrW W τ)
    (hbl : τ.vars "bl" = b.length) (hy : SegAt "y" 0 b τ) (hdl : dl ≤ b.length) (hpd : pl ≤ dl)
    (hB : total ws + ws.length + b.length + pl + 2 ≤ W) (hv : ∀ v ∈ b, v ≤ W) :
    ∃ τ', Run (W + 1) (apY pl dl) τ τ' (b.length * 18 + 50) ∧ Lib (ws ++ [(b.drop pl).take (b.length - dl)]) τ' ∧
      (∀ y, y ∉ apV → τ'.vars y = τ.vars y) ∧
      (∀ b', b' ∉ ["a", "st", "ln"] → τ'.arrs b' = τ.arrs b') ∧ ArrW W τ' ∧ τ'.out = τ.out ∧
      τ'.inp = τ.inp := by
  set w := (b.drop pl).take (b.length - dl)
  have hwl : w.length = b.length - dl := by simp [w]; omega
  obtain ⟨τ1, r1, s1, f1, a1, o1, i1⟩ := asgs_run (B := W + 1) (τ := τ)
    (l := [("ls", .lit pl), ("lL", .sub (.var "bl") (.lit dl))])
    (f := fun y => if y = "ls" then pl else b.length - dl)
    (by
      intro p hp
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl
      · rw [if_pos rfl]; exact evalB_lit (by omega)
      · rw [if_neg (show ("lL" : String) ≠ "ls" by decide)]
        exact ev_sub (ev_var hbl (by omega)) (evalB_lit (by omega)) (by omega))
    (by intro p hp q hq; simp at hp hq; rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp [exRv])
  have hls : τ1.vars "ls" = pl := by rw [s1 "ls" (by simp)]; simp
  have hlL : τ1.vars "lL" = w.length := by rw [s1 "lL" (by simp), hwl]; simp
  have L1 : Lib ws τ1 := hL.of (by rw [f1 "m" (by simp)]) (by rw [f1 "lt" (by simp)]) (by rw [a1]) (by rw [a1])
    (by rw [a1])
  have hseg : SegAt "y" pl w τ1 := by
    intro j hj
    rw [a1]
    have hj' : pl + j < b.length := by simp [w] at hj; omega
    have := hy (pl + j) hj'
    simp only [Nat.zero_add] at this
    rw [this]; simp [w]
  obtain ⟨τ2, r2, L2, f2, a2, l2, o2, i2⟩ := lbApp_run (W := W) (src := "y") (w := w) (s := pl) L1 hls hlL hseg
    (by decide) (by simp) (by rw [a1, harr "a"]; omega) (by rw [a1, harr "st"]; omega)
    (by rw [a1, harr "ln"]; omega) (by omega) (by omega)
    (fun v hv' => hv v (List.mem_of_mem_drop (List.mem_of_mem_take hv')))
  refine ⟨τ2, (Run.seq r1 r2).mono ?_, L2, fun y hy => ?_, fun b' hb => by rw [a2 b' hb, a1], fun b' => by
    rw [l2, a1]; exact harr b', by rw [o2, o1], by rw [i2, i1]⟩
  · simp [asgK, Expr.size]; omega
  · simp only [apV, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [f2 y (by simp; tauto), f1 y (by simp; tauto)]

theorem apE_run {W : ℕ} {ws : List (List ℕ)} {τ : Env} (hL : Lib ws τ) (harr : ArrW W τ)
    (hB : total ws + ws.length + 2 ≤ W) :
    ∃ τ', Run (W + 1) apE τ τ' 50 ∧ Lib (ws ++ [[]]) τ' ∧
      (∀ y, y ∉ apV → τ'.vars y = τ.vars y) ∧
      (∀ b, b ∉ ["a", "st", "ln"] → τ'.arrs b = τ.arrs b) ∧ ArrW W τ' ∧ τ'.out = τ.out ∧ τ'.inp = τ.inp := by
  obtain ⟨τ1, r1, s1, f1, a1, o1, i1⟩ := asgs_run (B := W + 1) (τ := τ)
    (l := [("ls", .lit 0), ("lL", .lit 0)]) (f := fun _ => 0)
    (by intro p hp; simp at hp; rcases hp with rfl | rfl <;> exact evalB_lit (by omega)) (by decide)
  have L1 : Lib ws τ1 := hL.of (by rw [f1 "m" (by simp)]) (by rw [f1 "lt" (by simp)]) (by rw [a1]) (by rw [a1])
    (by rw [a1])
  obtain ⟨τ2, r2, L2, f2, a2, l2, o2, i2⟩ := lbApp_run (W := W) (src := "y") (w := []) (s := 0) L1
    (s1 "ls" (by simp)) (s1 "lL" (by simp)) (fun j hj => by simp at hj)
    (by decide) (by simp) (by rw [a1, harr "a"]; simp; omega) (by rw [a1, harr "st"]; omega)
    (by rw [a1, harr "ln"]; omega) (by simp; omega) (by simp) (by simp)
  refine ⟨τ2, (Run.seq r1 r2).mono ?_, L2, fun y hy => ?_, fun b' hb => by rw [a2 b' hb, a1], fun b' => by
    rw [l2, a1]; exact harr b', by rw [o2, o1], by rw [i2, i1]⟩
  · simp [asgK, Expr.size]
  · simp only [apV, List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
    rw [f2 y (by simp; tauto), f1 y (by simp; tauto)]

/-- **Reading an entry of a library word.** -/
theorem ev_wd {W : ℕ} {L : List (List ℕ)} {τ : Env} {x : String} {i j : ℕ} (hw : WordsAt L τ)
    (hx : τ.vars x = i) (hi : i < L.length) (hj : j < L[i].length) (he : EnvLt (W + 1) τ)
    (harr : ArrW W τ) :
    (Expr.get "a" (.add (.get "st" (.var x)) (.lit j))).evalB (W + 1) τ = some L[i][j] := by
  have hv := he.vars x
  have hst := hw.st i hi
  have hoff : off L i < W + 1 := he.arrs "st" _ (List.mem_of_getElem? hst)
  have ha := hw.a i hi j hj
  have hval : L[i][j] < W + 1 := he.arrs "a" _ (List.mem_of_getElem? ha)
  have hidx : off L i + j < W + 1 := by
    have := (List.getElem?_eq_some_iff.1 ha).1
    rw [harr "a"] at this; exact this
  exact evalB_get (ev_add (evalB_get (ev_var hx (by omega)) hst hoff) (evalB_lit (by omega)) hidx) ha hval

/-- `oL := LL[0] + … + LL[dd - 1]`, for the word `LL` with index `3` of the library. -/
def sumLL : Com :=
  .seq (.assign "oL" (.lit 0)) (forUp "fk" (.var "dd")
    (.assign "oL" (.add (.var "oL") (.get "a" (.add (.get "st" (.lit 3)) (.var "fk"))))))

theorem ev_wd3 {W : ℕ} {L : List (List ℕ)} {τ : Env} {j : ℕ} (hw : WordsAt L τ) (hi : 3 < L.length)
    (hx : τ.vars "fk" = j) (hj : j < L[3].length) (he : EnvLt (W + 1) τ) (harr : ArrW W τ) (hW3 : 3 ≤ W) :
    (Expr.get "a" (.add (.get "st" (.lit 3)) (.var "fk"))).evalB (W + 1) τ = some L[3][j] := by
  have hst := hw.st 3 hi
  have hoff : off L 3 < W + 1 := he.arrs "st" _ (List.mem_of_getElem? hst)
  have ha := hw.a 3 hi j hj
  have hval : L[3][j] < W + 1 := he.arrs "a" _ (List.mem_of_getElem? ha)
  have hidx : off L 3 + j < W + 1 := by
    have := (List.getElem?_eq_some_iff.1 ha).1
    rw [harr "a"] at this; exact this
  exact evalB_get (ev_add (evalB_get (evalB_lit (by omega)) hst hoff) (ev_var hx (by have := he.vars "fk"; omega)) hidx) ha hval

theorem sumLL_run {W d : ℕ} {L : List (List ℕ)} {τ : Env} (hw : WordsAt L τ) (hi : 3 < L.length)
    (hd : τ.vars "dd" = d) (hdl : d ≤ L[3].length) (hsum : (L[3].take d).sum ≤ W)
    (he : EnvLt (W + 1) τ) (harr : ArrW W τ) (hW3 : 3 ≤ W) :
    ∃ τ', Run (W + 1) sumLL τ τ' (d * 20 + 10) ∧ τ'.vars "oL" = (L[3].take d).sum ∧
      (∀ y, y ≠ "oL" → y ≠ "fk" → τ'.vars y = τ.vars y) ∧ τ'.arrs = τ.arrs ∧ τ'.out = τ.out ∧
      τ'.inp = τ.inp := by
  have hdW : d < W + 1 := by rw [← hd]; exact he.vars _
  let I : ℕ → Env → Prop := fun k ρ => ρ.vars "oL" = (L[3].take k).sum ∧
    (∀ y, y ≠ "oL" → y ≠ "fk" → ρ.vars y = τ.vars y) ∧ ρ.arrs = τ.arrs ∧ ρ.out = τ.out ∧ ρ.inp = τ.inp ∧
    EnvLt (W + 1) ρ
  set τ0 := τ.setVar "oL" 0
  have r0 : Run (W + 1) (.assign "oL" (.lit 0)) τ τ0 2 := Run.assign (evalB_lit (by omega))
  have hl0 : EnvLt (W + 1) τ0 := Run.envLt r0 he
  obtain ⟨τ', r, ⟨h1, h2, h3, h4, h5, -⟩, -⟩ := forUp_run (B := W + 1) (i := "fk") (e := .var "dd")
    (body := .assign "oL" (.add (.var "oL") (.get "a" (.add (.get "st" (.lit 3)) (.var "fk"))))) (N := d)
    (K := 9) I (σ := τ0) hdW
    (fun k _ ρ hI hk => ev_var (by rw [hI.2.1 "dd" (by decide) (by decide), hd]) hdW)
    ⟨by simp [τ0], fun y h1 h2 => by simp [τ0, h1, h2], by simp [τ0], by simp [τ0], by simp [τ0],
      hl0.setVar "fk" (by omega)⟩
    (by
      rintro k hk ρ ⟨i1, i2, i3, i4, i5, i6⟩ hfk
      have hw' : WordsAt L ρ := hw.of_arrs (by rw [i3]) (by rw [i3]) (by rw [i3])
      have harr' : ArrW W ρ := fun b => by rw [i3]; exact harr b
      have hev := ev_wd3 hw' hi hfk (by omega) i6 harr' hW3
      have hsk : (L[3].take (k + 1)).sum = (L[3].take k).sum + L[3][k] := by
        rw [List.take_add_one, List.getElem?_eq_getElem (by omega)]
        simp only [Option.toList_some, List.sum_append, List.sum_singleton]
      have hle : (L[3].take (k + 1)).sum ≤ (L[3].take d).sum := by
        have : L[3].take d = L[3].take (k + 1) ++ (L[3].drop (k + 1)).take (d - (k + 1)) := by
          rw [← List.take_add, Nat.add_sub_cancel' (by omega)]
        rw [this, List.sum_append]; omega
      have r1 := Run.assign (B := W + 1) (σ := ρ) (x := "oL") (ev_add (ev_var i1 (by
        have := i6.vars "oL"; omega)) hev (by omega))
      refine ⟨_, r1.mono (by simp), by simp [hfk], ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp [hsk]
      · intro y h1 h2; simp [h1, h2, i2 y h1 h2]
      · simp [i3]
      · simp [i4]
      · simp [i5]
      · exact (Run.envLt r1 i6).setVar "fk" (by omega))
  refine ⟨τ', (Run.seq r0 r).mono (by simp only [Expr.size]; omega), h1, fun y a b => by rw [h2 y a b], h3, h4, h5⟩

end Lax185574Proofs.ResolveRam.Glue
