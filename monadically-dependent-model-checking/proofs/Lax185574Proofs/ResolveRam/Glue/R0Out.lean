import Lax185574Proofs.ResolveRam.Glue.R0

/-!
The output of the first round of the glue program of lem:resolve-lift
for `n ≥ 1`: the head of the position of the scatter type and the query
of the switch (`fill0_run`), filled into the buffer `OB`. The positions
`qa` and `ql` mark the query of slot F in the buffer, for the guard. The
scalars `P`, `Q`, the sign, `k₀` and `q₀` are read behind the end `pq`
of the word of the distance matrix.
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574Proofs.MC Lax185574Proofs.MC.Glue Lax185574Proofs.Compose
open Lax185574.WordEncoding Lax185574.PartialGraphs Lax185574.TypeTrees
open Lax185574.PartialGraphEncoding Lax185574Proofs.ResolveRam Lax185574.DistanceMatrix

variable {n : ℕ} (G : PartialGraph (Fin n)) (P Q : ℕ) (s : Bool) (k₀ q₀ : ℕ)

/-- The constant parts of the output of the first round. -/
noncomputable def mid0 : List ℕ := List.replicate 8 0 ++ [4, 0, 0, 0, 0] ++ [s3W.length, qE0.length]

/-- The size of the constants. -/
noncomputable def k0 : ℕ := s3W.length + qE0.length + maxEntry s3W + maxEntry qE0 + 64

/-- The scalars of the state that the first round writes. -/
def sc0 : List String := ["nx", "gz", "gX", "nx", "gn", "gP", "gQ", "gS", "gK", "gq"]

/-- Load the scalars of the first round. -/
def ld0 : Com :=
  .seq (.assign "gP" (.get "x" (.var "pq"))) (.seq (.assign "gQ" (.get "x" (.add (.var "pq") (.lit 1))))
  (.seq (.assign "gS" (.get "x" (.add (.var "pq") (.lit 2))))
  (.seq (.assign "gK" (.get "x" (.add (.var "pq") (.lit 4))))
  (.seq (.assign "gq" (.get "x" (.add (.var "pq") (.lit 5))))
  (.seq (.assign "gX" (.add (.add (.var "nx") (.var "mx")) (.lit 1)))
  (.seq (.assign "gz" (.lit 0)) (.assign "q1" (.sub (.var "nx") (.lit 1)))))))))

/-- Fill the buffer with the output of the first round. -/
noncomputable def fill0 : Com :=
  .seq ld0 (.seq (.assign "po" (.lit 0)) (.seq (.seq (push1 "OB" "po" (.add (.var "nx") (.lit 1))) (pushLits [22]))
  (.seq (pushL "OB" "po" (sc0.map Expr.var)) (.seq (pushLits mid0)
  (.seq (pushL "OB" "po" [.var "q1"]) (.seq (pushLits (s3W ++ qE0))
  (.seq (.assign "qa" (.var "po")) (.seq (cpSeg "x" "gz" "pp")
  (.seq (pushL "OB" "po" [.var "gK", .var "gq"]) (.seq (.assign "dl" (.sub (.var "pq") (.var "pp")))
  (.seq (cpSeg "x" "pp" "dl") (.seq (.assign "qs" (.add (.var "pq") (.lit 3)))
  (.seq (.assign "qn" (.sub (.var "nx") (.var "qs"))) (.seq (cpSeg "x" "qs" "qn")
  (.assign "ql" (.sub (.var "po") (.var "qa")))))))))))))))))

/-- The output of the first round. -/
theorem out0_eq :
    hdOf G P Q s k₀ q₀ .stp ++ rQ G k₀ q₀ .stp =
      [(xIn G k₀ q₀ P Q s).length + 1, 22] ++ [(xIn G k₀ q₀ P Q s).length, 0, ySz (xIn G k₀ q₀ P Q s), (xIn G k₀ q₀ P Q s).length,
        n, P, Q, if s then 1 else 0, k₀, q₀] ++ mid0 ++ [(xIn G k₀ q₀ P Q s).length - 1] ++
        (s3W ++ qE0) ++ toWord G ++ [k₀, q₀] ++ toWord (distMatrix G) ++ toWord (family G k₀ q₀) := by
  have hl := qF_len G P Q s k₀ q₀
  rw [qF_stp] at hl
  have hl' : (toWord G ++ [k₀, q₀] ++ toWord (distMatrix G) ++ toWord (family G k₀ q₀)).length =
      (xIn G k₀ q₀ P Q s).length - 1 := by omega
  rw [hdOf_stp, rQ_stp, qF_stp, hl']
  simp [mid0]

theorem seg_preAt {a : String} {X : List ℕ} {τ : Env} (h : PreAt a X τ) {p N : ℕ}
    (hN : p + N ≤ X.length) : seg (τ.arrs a) p N = (X.drop p).take N := by
  apply List.ext_getElem
  · have := h.get (i := p + N - 1)
    simp only [seg, List.length_take, List.length_drop]
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0; simp
    · have hl : p + N - 1 < (τ.arrs a).length := by
        have := h (p + N - 1) (by omega)
        exact (List.getElem?_eq_some_iff.1 this).1
      omega
  · intro i h1 h2
    simp only [seg, List.getElem_take, List.getElem_drop]
    simp only [List.length_take, List.length_drop] at h2
    have := h (p + i) (by omega)
    rw [List.getElem?_eq_getElem (by exact (List.getElem?_eq_some_iff.1 this).1)] at this
    exact Option.some.inj this

theorem PreAt.getD {a : String} {X : List ℕ} {τ : Env} (h : PreAt a X τ) {i : ℕ} (hi : i < X.length) :
    (τ.arrs a)[i]? = some (X.getD i 0) := by
  rw [h.get hi, List.getD_eq_getElem _ _ hi]

theorem le_ySz {X : List ℕ} {v : ℕ} (hv : v ∈ X) : v + X.length + 1 ≤ ySz X := by
  have := le_maxEntry hv; unfold ySz; omega

theorem getD_le_ySz (X : List ℕ) (i : ℕ) : X.getD i 0 + 1 ≤ ySz X := by
  rcases Nat.lt_or_ge i X.length with h | h
  · rw [List.getD_eq_getElem _ _ h]; have := le_ySz (List.getElem_mem h); omega
  · rw [List.getD_eq_default _ _ h]; unfold ySz; omega

/-- The entries of the input around the end of the word of the distance matrix. -/
theorem xIn_at (hn : 1 ≤ n) :
    let X := xIn G k₀ q₀ P Q s
    let p := (toWord G).length + (toWord (distMatrix G)).length
    X.getD p 0 = P ∧ X.getD (p + 1) 0 = Q ∧ X.getD (p + 2) 0 = (if s then 1 else 0) ∧
      X.getD (p + 4) 0 = k₀ ∧ X.getD (p + 5) 0 = q₀ ∧ p + 6 ≤ X.length := by
  intro X p
  have hX : X = (toWord G ++ toWord (distMatrix G)) ++ ([P, Q, if s then 1 else 0] ++
      toWord (family G k₀ q₀)) := by
    simp only [X, xIn_split G P Q s k₀ q₀, List.append_assoc]
  have hr := family_rank G k₀ q₀ hn
  have hfl : 3 ≤ (toWord (family G k₀ q₀)).length := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [toWord_family, List.ofFn_succ, List.flatten_cons]
    have : toWord (family G k₀ q₀ 0) = k₀ :: q₀ :: 1 :: toWord (family G k₀ q₀ 0).root := rfl
    rw [this]; simp
  have hg : ∀ j, X.getD (p + j) 0 = ([P, Q, if s then 1 else 0] ++ toWord (family G k₀ q₀)).getD j 0 := by
    intro j
    rw [hX, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by simp [p])]
    simp [p]
  refine ⟨by simpa using hg 0, by simpa using hg 1, by simpa using hg 2, ?_, ?_, ?_⟩
  · rw [hg 4]; simpa [List.getD_eq_getElem?_getD] using hr.1
  · rw [hg 5]; simpa [List.getD_eq_getElem?_getD] using hr.2
  · rw [hX]; simp [p]; omega

theorem ev_getx {B : ℕ} {X : List ℕ} {τ : Env} (hX : PreAt "x" X τ) {p c : ℕ} (hp : τ.vars "pq" = p)
    (hc : p + c < X.length) (hB : ySz X < B) :
    (Expr.get "x" (.add (.var "pq") (.lit c))).evalB B τ = some (X.getD (p + c) 0) := by
  have h1 := getD_le_ySz X (p + c)
  exact evalB_get (ev_add (ev_var hp (by unfold ySz at hB; omega)) (evalB_lit (by unfold ySz at hB; omega))
    (by unfold ySz at hB; omega)) (hX.getD hc) (by omega)

/-- Loading the scalars. -/
theorem ld0_run {B : ℕ} {X : List ℕ} {σ : Env} (hX : PreAt "x" X σ) {p : ℕ} (hp : σ.vars "pq" = p)
    (hp6 : p + 6 ≤ X.length) (hnx : σ.vars "nx" = X.length) (hmx : σ.vars "mx" = maxEntry X)
    (hB : 2 * ySz X < B) :
    ∃ σ', Run B ld0 σ σ' 60 ∧ σ'.vars "gP" = X.getD p 0 ∧ σ'.vars "gQ" = X.getD (p + 1) 0 ∧
      σ'.vars "gS" = X.getD (p + 2) 0 ∧ σ'.vars "gK" = X.getD (p + 4) 0 ∧
      σ'.vars "gq" = X.getD (p + 5) 0 ∧ σ'.vars "gX" = ySz X ∧ σ'.vars "gz" = 0 ∧
      σ'.vars "q1" = X.length - 1 ∧ OFr σ σ' ["gP", "gQ", "gS", "gK", "gq", "gX", "gz", "q1"] := by
  have hyB : ySz X < B := by omega
  have e0 : (Expr.get "x" (.var "pq")).evalB B σ = some (X.getD p 0) :=
    evalB_get (ev_var hp (by unfold ySz at hyB; omega)) (hX.getD (by omega))
      (by have := getD_le_ySz X p; omega)
  set σ1 := σ.setVar "gP" (X.getD p 0)
  have hX1 : PreAt "x" X σ1 := fun i h => by simpa [σ1] using hX i h
  set σ2 := σ1.setVar "gQ" (X.getD (p + 1) 0)
  have hX2 : PreAt "x" X σ2 := fun i h => by simpa [σ2] using hX1 i h
  set σ3 := σ2.setVar "gS" (X.getD (p + 2) 0)
  have hX3 : PreAt "x" X σ3 := fun i h => by simpa [σ3] using hX2 i h
  set σ4 := σ3.setVar "gK" (X.getD (p + 4) 0)
  have hX4 : PreAt "x" X σ4 := fun i h => by simpa [σ4] using hX3 i h
  set σ5 := σ4.setVar "gq" (X.getD (p + 5) 0)
  set σ6 := σ5.setVar "gX" (ySz X)
  set σ7 := σ6.setVar "gz" 0
  set σ8 := σ7.setVar "q1" (X.length - 1)
  have r1 : Run B (.assign "gP" (.get "x" (.var "pq"))) σ σ1 3 :=
    (Run.assign e0).mono (by simp [Expr.size])
  have r2 : Run B (.assign "gQ" (.get "x" (.add (.var "pq") (.lit 1)))) σ1 σ2 5 :=
    (Run.assign (ev_getx hX1 (by simp [σ1, hp]) (by omega) hyB)).mono (by simp [Expr.size])
  have r3 : Run B (.assign "gS" (.get "x" (.add (.var "pq") (.lit 2)))) σ2 σ3 5 :=
    (Run.assign (ev_getx hX2 (by simp [σ2, σ1, hp]) (by omega) hyB)).mono (by simp [Expr.size])
  have r4 : Run B (.assign "gK" (.get "x" (.add (.var "pq") (.lit 4)))) σ3 σ4 5 :=
    (Run.assign (ev_getx hX3 (by simp [σ3, σ2, σ1, hp]) (by omega) hyB)).mono (by simp [Expr.size])
  have r5 : Run B (.assign "gq" (.get "x" (.add (.var "pq") (.lit 5)))) σ4 σ5 5 :=
    (Run.assign (ev_getx hX4 (by simp [σ4, σ3, σ2, σ1, hp]) (by omega) hyB)).mono (by simp [Expr.size])
  have hyB' : X.length + maxEntry X + 1 < B := hyB
  have h5nx : σ5.vars "nx" = X.length := by simp [σ5, σ4, σ3, σ2, σ1, hnx]
  have h5mx : σ5.vars "mx" = maxEntry X := by simp [σ5, σ4, σ3, σ2, σ1, hmx]
  have e6 : (Expr.add (.add (.var "nx") (.var "mx")) (.lit 1)).evalB B σ5 =
      some (X.length + maxEntry X + 1) :=
    ev_add (ev_add (ev_var h5nx (by omega)) (ev_var h5mx (by omega)) (by omega))
      (evalB_lit (by omega)) (by omega)
  have r6 : Run B (.assign "gX" (.add (.add (.var "nx") (.var "mx")) (.lit 1))) σ5 σ6 6 :=
    (Run.assign e6).mono (by simp [Expr.size])
  have r7 : Run B (.assign "gz" (.lit 0)) σ6 σ7 2 := Run.assign (evalB_lit (by omega))
  have h7nx : σ7.vars "nx" = X.length := by simp [σ7, σ6, h5nx]
  have e8 : (Expr.sub (.var "nx") (.lit 1)).evalB B σ7 = some (X.length - 1) :=
    ev_sub (ev_var h7nx (by omega)) (evalB_lit (by omega)) (by omega)
  have r8 : Run B (.assign "q1" (.sub (.var "nx") (.lit 1))) σ7 σ8 4 :=
    (Run.assign e8).mono (by simp [Expr.size])
  refine ⟨σ8, ?_, by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1], by simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2],
    by simp [σ8, σ7, σ6, σ5, σ4, σ3], by simp [σ8, σ7, σ6, σ5, σ4], by simp [σ8, σ7, σ6, σ5],
    by simp [σ8, σ7, σ6], by simp [σ8, σ7], by simp [σ8],
    ⟨fun y hy => by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
      simp [σ8, σ7, σ6, σ5, σ4, σ3, σ2, σ1, hy], fun _ _ => rfl, rfl, rfl, rfl⟩⟩
  unfold ld0
  exact (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 (Run.seq r5 (Run.seq r6 (Run.seq r7 r8))))))).mono
    (by omega)

theorem ofr_assign {W : ℕ} {τ : Env} {x : String} {e : Expr} {v : ℕ} (h : e.evalB (W + 1) τ = some v) :
    Run (W + 1) (.assign x e) τ (τ.setVar x v) (1 + e.size) ∧ OFr τ (τ.setVar x v) [x] :=
  ⟨Run.assign h, OFr.setVar τ x v⟩

theorem length_mid0 : mid0.length = 15 := by simp [mid0]

theorem mem_k0 {v : ℕ} (hv : v ∈ s3W ++ qE0) : v + 64 ≤ k0 := by
  unfold k0
  rcases List.mem_append.1 hv with h | h
  · have := le_maxEntry h; omega
  · have := le_maxEntry h; omega

set_option maxHeartbeats 400000 in
/-- **The output of the first round in the buffer.** -/
theorem fill0_run {W : ℕ} {σ : Env} (hn : 1 ≤ n) (hX : PreAt "x" (xIn G k₀ q₀ P Q s) σ)
    (hpp : σ.vars "pp" = (toWord G).length)
    (hpq : σ.vars "pq" = (toWord G).length + (toWord (distMatrix G)).length) (hgn : σ.vars "gn" = n)
    (hnx : σ.vars "nx" = (xIn G k₀ q₀ P Q s).length) (hmx : σ.vars "mx" = maxEntry (xIn G k₀ q₀ P Q s))
    (hcap : (σ.arrs "OB").length = W + 1) (hW : 4 * ySz (xIn G k₀ q₀ P Q s) + k0 ≤ W) :
    ∃ σ', Run (W + 1) fill0 σ σ' (20 * (xIn G k₀ q₀ P Q s).length + 8 * k0 + 500) ∧
      Filled "OB" "po" (hdOf G P Q s k₀ q₀ .stp ++ rQ G k₀ q₀ .stp) σ' ∧
      σ'.vars "qa" + (qF G k₀ q₀ .stp).length = (hdOf G P Q s k₀ q₀ .stp ++ rQ G k₀ q₀ .stp).length ∧
      σ'.vars "ql" = (qF G k₀ q₀ .stp).length ∧ σ'.vars "gX" = ySz (xIn G k₀ q₀ P Q s) ∧
      OFr σ σ' ["gP", "gQ", "gS", "gK", "gq", "gX", "gz", "q1", "po", "ci", "qa", "dl", "qs", "qn",
        "ql"] := by
  obtain ⟨xP, xQ, xS, xK, xq, hp6⟩ := xIn_at G P Q s k₀ q₀ hn
  set X := xIn G k₀ q₀ P Q s with hXdef
  set p0 := (toWord G).length
  set p := (toWord G).length + (toWord (distMatrix G)).length
  have hyW : ySz X ≤ W := by omega
  have hXl : X.length + maxEntry X + 1 = ySz X := rfl
  have hk64 : 64 + s3W.length + qE0.length ≤ k0 := by unfold k0; omega
  have hXsp : X.length = p + 3 + (toWord (family G k₀ q₀)).length := by
    rw [hXdef, xIn_split]; simp [p]; omega
  obtain ⟨σ1, r1, v1P, v1Q, v1S, v1K, v1q, v1X, v1z, v11, o1⟩ := ld0_run (B := W + 1) hX hpq hp6 hnx hmx
    (by omega)
  -- po := 0
  have r2 : Run (W + 1) (.assign "po" (.lit 0)) σ1 (σ1.setVar "po" 0) 2 := Run.assign (evalB_lit (by omega))
  have F2 := Filled.empty "OB" "po" σ1
  set σ2 := σ1.setVar "po" 0
  have o2 := OFr.setVar σ1 "po" 0
  have c2 : (σ2.arrs "OB").length = W + 1 := by rw [o2.len, o1.len, hcap]
  -- the tag and the length of the state
  have hnx2 : σ2.vars "nx" = X.length := by rw [o2.vars _ (by decide), o1.vars _ (by decide), hnx]
  obtain ⟨σ3a, r3a, F3a, o3a⟩ := push1_ofr (W := W) (e := .add (.var "nx") (.lit 1)) (v := X.length + 1) F2
    (ev_add (ev_var hnx2 (by unfold ySz at hW; omega)) (evalB_lit (by omega)) (by unfold ySz at hW; omega))
    (by simp [c2]) (by simp only [List.length_nil]; omega)
  obtain ⟨σ3, r3b, F3, o3b⟩ := pushLits_run (W := W) (l := [22]) F3a
    (by intro v hv; simp at hv; omega) (by rw [o3a.len]; simp [c2]; omega) (by simp; omega)
  simp only [List.nil_append, List.singleton_append] at F3
  have o3 : OFr σ2 σ3 ["po"] := (o3a.trans o3b).mono (by decide)
  have r3 : Run (W + 1) (.seq (push1 "OB" "po" (.add (.var "nx") (.lit 1))) (pushLits [22])) σ2 σ3 18 :=
    (Run.seq r3a r3b).mono (by simp [Expr.size])
  -- the scalars
  have hv3 : ∀ y, y ∉ ["po"] → σ3.vars y = σ1.vars y := fun y hy => by
    rw [o3.vars y hy, o2.vars y hy]
  have hsc : sc0.map σ3.vars = [X.length, 0, ySz X, X.length, n, P, Q, if s then 1 else 0, k₀, q₀] := by
    simp only [sc0, List.map_cons, List.map_nil]
    rw [hv3 "nx" (by decide), hv3 "gz" (by decide), hv3 "gX" (by decide), hv3 "gn" (by decide),
      hv3 "gP" (by decide), hv3 "gQ" (by decide), hv3 "gS" (by decide), hv3 "gK" (by decide),
      hv3 "gq" (by decide), o1.vars "nx" (by decide), o1.vars "gn" (by decide), hnx, hgn, v1z, v1X,
      v1P, v1Q, v1S, v1K, v1q, xP, xQ, xS, xK, xq]
  obtain ⟨σ4, r4, F4, o4⟩ := pushVars_run (W := W) (xs := sc0) (by decide) F3 (by
      intro x hx
      have : σ3.vars x ∈ sc0.map σ3.vars := List.mem_map_of_mem hx
      rw [hsc] at this
      have h1 := getD_le_ySz X p
      have h2 := getD_le_ySz X (p + 1)
      have h3 := getD_le_ySz X (p + 2)
      have h4 := getD_le_ySz X (p + 4)
      have h5 := getD_le_ySz X (p + 5)
      rw [xP] at h1; rw [xQ] at h2; rw [xS] at h3; rw [xK] at h4; rw [xq] at h5
      have hnX : n ≤ X.length := by
        rw [hXdef, xIn_split]; have := StpRam.toWord_pg G; simp only [List.length_append]
        rw [this]; simp; omega
      simp only [List.mem_cons, List.not_mem_nil, or_false] at this
      rcases this with h | h | h | h | h | h | h | h | h | h <;> rw [h] <;> omega)
    (by rw [o3.len, c2]; simp [sc0]; omega) (by simp [sc0]; omega)
  rw [hsc] at F4
  -- the constant middle
  obtain ⟨σ5, r5, F5, o5⟩ := pushLits_run (W := W) (l := mid0) F4
    (by intro v hv; simp [mid0] at hv; unfold k0 at hW; omega)
    (by rw [o4.len, o3.len, c2]; simp [length_mid0]; omega) (by simp [length_mid0]; omega)
  -- the length of the query of slot F
  obtain ⟨σ6, r6, F6, o6⟩ := pushVars_run (W := W) (xs := ["q1"]) (by decide) F5
    (by intro x hx; simp at hx; subst hx
        rw [o5.vars _ (by decide), o4.vars _ (by decide), hv3 _ (by decide), v11]; omega)
    (by rw [o5.len, o4.len, o3.len, c2]; simp [length_mid0]; omega) (by simp [length_mid0]; omega)
  have hq1 : σ5.vars "q1" = X.length - 1 := by
    rw [o5.vars _ (by decide), o4.vars _ (by decide), hv3 _ (by decide), v11]
  simp only [List.map_cons, List.map_nil, hq1] at F6
  -- the fixed queries
  obtain ⟨σ7, r7, F7, o7⟩ := pushLits_run (W := W) (l := s3W ++ qE0) F6
    (by intro v hv; have := mem_k0 hv; omega)
    (by rw [o6.len, o5.len, o4.len, o3.len, c2]; simp [length_mid0]; unfold k0 at hW; omega)
    (by simp [length_mid0]; unfold k0 at hW; omega)
  set pre7 := [X.length + 1, 22] ++ [X.length, 0, ySz X, X.length, n, P, Q, if s then 1 else 0, k₀, q₀] ++ mid0 ++
    [X.length - 1] ++ (s3W ++ qE0) with hpre7
  have hl7 : pre7.length = 28 + s3W.length + qE0.length := by simp [hpre7, length_mid0]; omega
  -- qa := po
  have hpo7 : σ7.vars "po" = pre7.length := F7.pos
  obtain ⟨r8, o8⟩ := ofr_assign (W := W) (x := "qa") (ev_var hpo7 (by unfold k0 at hW; omega))
  set σ8 := σ7.setVar "qa" pre7.length
  have F8 : Filled "OB" "po" pre7 σ8 := F7.setVar (by decide) _
  -- the frames so far
  have o18 : OFr σ1 σ8 (["po"] ++ ["po"] ++ ["po"] ++ ["po"] ++ ["po"] ++ ["po"] ++ ["qa"]) :=
    (((((o2.trans o3).trans o4).trans o5).trans o6).trans o7).trans o8
  have hv8 : ∀ y, y ∉ ["po", "qa"] → σ8.vars y = σ1.vars y := fun y hy =>
    o18.vars y (by simp at hy ⊢; tauto)
  have ha8 : σ8.arrs "x" = σ.arrs "x" := by rw [o18.arrs _ (by decide), o1.arrs _ (by decide)]
  have hX8 : PreAt "x" X σ8 := fun i h => by rw [ha8]; exact hX i h
  have c8 : (σ8.arrs "OB").length = W + 1 := by rw [o18.len, o1.len, hcap]
  have hxlen : X.length ≤ (σ8.arrs "x").length := by
    rcases Nat.eq_zero_or_pos X.length with h0 | h0
    · omega
    · have := hX8 (X.length - 1) (by omega)
      have := (List.getElem?_eq_some_iff.1 this).1
      omega
  have hsegX : ∀ a N, a + N ≤ X.length → ∀ v ∈ seg (σ8.arrs "x") a N, v ≤ W := by
    intro a N h v hv
    rw [seg_preAt hX8 h] at hv
    have := le_ySz (List.mem_of_mem_drop (List.mem_of_mem_take hv))
    omega
  -- the word of the partial graph
  have hz8 : σ8.vars "gz" = 0 := by rw [hv8 _ (by decide), v1z]
  have hp8 : σ8.vars "pp" = p0 := by rw [hv8 _ (by decide), o1.vars _ (by decide), hpp]
  obtain ⟨σ9, r9, F9, o9⟩ := cpSeg_ofr (W := W) (src := "x") (s := "gz") (l := "pp") (by decide) hz8 hp8
    (by decide) (by decide) (by decide) (by decide) F8 (by omega) (by rw [c8, hl7]; unfold k0 at hW; omega)
    (by unfold ySz at hyW; omega) (by rw [hl7]; unfold k0 at hW; unfold ySz at hyW; omega)
    (hsegX 0 p0 (by omega))
  have hsegG : seg (σ8.arrs "x") 0 p0 = toWord G := by
    rw [seg_preAt hX8 (by omega), List.drop_zero, hXdef, xIn_split, List.take_left' rfl]
  rw [hsegG] at F9
  -- k₀ and q₀
  have hK9 : σ9.vars "gK" = k₀ := by rw [o9.vars _ (by decide), hv8 _ (by decide), v1K, xK]
  have hq9 : σ9.vars "gq" = q₀ := by rw [o9.vars _ (by decide), hv8 _ (by decide), v1q, xq]
  have hk0W : k₀ ≤ W := by have := getD_le_ySz X (p + 4); rw [xK] at this; omega
  have hq0W : q₀ ≤ W := by have := getD_le_ySz X (p + 5); rw [xq] at this; omega
  obtain ⟨σ10, r10, F10, o10⟩ := pushVars_run (W := W) (xs := ["gK", "gq"]) (by decide) F9
    (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> simp [hK9, hq9, hk0W, hq0W])
    (by rw [o9.len, c8]; simp; rw [hl7]; unfold k0 at hW; unfold ySz at hyW; omega)
    (by simp; rw [hl7]; unfold k0 at hW; unfold ySz at hyW; omega)
  simp only [List.map_cons, List.map_nil, hK9, hq9] at F10
  -- the distance matrix
  have hp10 : σ10.vars "pp" = p0 := by rw [o10.vars _ (by decide), o9.vars _ (by decide), hp8]
  have hq10 : σ10.vars "pq" = p := by
    rw [o10.vars _ (by decide), o9.vars _ (by decide), hv8 _ (by decide), o1.vars _ (by decide), hpq]
  obtain ⟨r10b, o10b⟩ := ofr_assign (W := W) (x := "dl")
    (ev_sub (ev_var hq10 (by omega)) (ev_var hp10 (by omega)) (by omega))
  set σ10b := σ10.setVar "dl" (p - p0)
  have F10b : Filled "OB" "po" (pre7 ++ toWord G ++ [k₀, q₀]) σ10b := F10.setVar (by decide) _
  have ha10b : σ10b.arrs "x" = σ8.arrs "x" := by
    simp only [σ10b, arrs_setVar]; rw [o10.arrs _ (by decide), o9.arrs _ (by decide)]
  have hX10b : PreAt "x" X σ10b := fun i h => by rw [ha10b]; exact hX8 i h
  have c10b : (σ10b.arrs "OB").length = W + 1 := by
    simp only [σ10b, arrs_setVar]; rw [o10.len, o9.len, c8]
  have hpd : p - p0 = (toWord (distMatrix G)).length := by omega
  obtain ⟨σ10c, r10c, F10c, o10c⟩ := cpSeg_ofr (W := W) (src := "x") (s := "pp") (l := "dl")
    (a := p0) (N := p - p0) (by decide)
    (by simp only [σ10b, vars_setVar, if_neg (show ("pp" : String) ≠ "dl" by decide)]; exact hp10)
    (by simp [σ10b]) (by decide) (by decide) (by decide) (by decide) F10b
    (by rw [ha10b]; omega) (by rw [c10b]; simp; rw [hl7]; unfold k0 at hW; unfold ySz at hyW; omega)
    (by unfold ySz at hyW; omega) (by simp; rw [hl7]; unfold k0 at hW; unfold ySz at hyW; omega)
    (by rw [ha10b]; exact hsegX p0 _ (by omega))
  have hsegD : seg (σ10b.arrs "x") p0 (p - p0) = toWord (distMatrix G) := by
    rw [seg_preAt hX10b (by omega), hpd, hXdef, xIn_split, List.drop_left, List.take_left' rfl]
  rw [hsegD] at F10c
  -- qs and qn
  have hq10c : σ10c.vars "pq" = p := by
    rw [o10c.vars _ (by decide)]; simp only [σ10b, vars_setVar]; simp; exact hq10
  obtain ⟨r11, o11⟩ := ofr_assign (W := W) (x := "qs")
    (ev_add (ev_var hq10c (by omega)) (evalB_lit (n := 3) (by omega)) (by omega))
  set σ11 := σ10c.setVar "qs" (p + 3)
  have hnx11 : σ11.vars "nx" = X.length := by
    simp only [σ11, vars_setVar, if_neg (show ("nx" : String) ≠ "qs" by decide)]
    rw [o10c.vars _ (by decide)]; simp only [σ10b, vars_setVar]; simp
    rw [o10.vars _ (by decide), o9.vars _ (by decide), hv8 _ (by decide), o1.vars _ (by decide), hnx]
  obtain ⟨r12, o12⟩ := ofr_assign (W := W) (x := "qn")
    (ev_sub (ev_var hnx11 (by unfold ySz at hyW; omega)) (ev_var (x := "qs") (v := p + 3) (by simp [σ11]) (by omega)) (by omega))
  set σ12 := σ11.setVar "qn" (X.length - (p + 3))
  have F12 : Filled "OB" "po" (pre7 ++ toWord G ++ [k₀, q₀] ++ toWord (distMatrix G)) σ12 :=
    (F10c.setVar (by decide) _).setVar (by decide) _
  have ha12 : σ12.arrs "x" = σ8.arrs "x" := by
    simp only [σ12, σ11, arrs_setVar]; rw [o10c.arrs _ (by decide), ha10b]
  have hX12 : PreAt "x" X σ12 := fun i h => by rw [ha12]; exact hX8 i h
  have c12 : (σ12.arrs "OB").length = W + 1 := by
    simp only [σ12, σ11, arrs_setVar]; rw [o10c.len, c10b]
  obtain ⟨σ13, r13, F13, o13⟩ := cpSeg_ofr (W := W) (src := "x") (s := "qs") (l := "qn")
    (a := p + 3) (N := X.length - (p + 3)) (by decide)
    (by simp [σ12, σ11]) (by simp [σ12]) (by decide) (by decide) (by decide) (by decide) F12
    (by rw [ha12]; omega) (by rw [c12]; simp; rw [hl7]; unfold k0 at hW; unfold ySz at hyW; omega)
    (by unfold ySz at hyW; omega) (by simp; rw [hl7]; unfold k0 at hW; unfold ySz at hyW; omega)
    (by rw [ha12]; exact hsegX (p + 3) _ (by omega))
  have hsegF : seg (σ12.arrs "x") (p + 3) (X.length - (p + 3)) = toWord (family G k₀ q₀) := by
    rw [seg_preAt hX12 (by omega), List.take_of_length_le (by simp), hXdef, xIn_split,
      ← List.drop_drop, ← List.drop_drop, List.drop_left, List.drop_left]
    simp
  rw [hsegF] at F13
  -- ql
  have hpo13 : σ13.vars "po" = (pre7 ++ toWord G ++ [k₀, q₀] ++ toWord (distMatrix G) ++ toWord (family G k₀ q₀)).length := F13.pos
  have hqa13 : σ13.vars "qa" = pre7.length := by
    rw [o13.vars _ (by decide)]; simp [σ12, σ11]; rw [o10c.vars _ (by decide)]; simp [σ10b]
    rw [o10.vars _ (by decide), o9.vars _ (by decide)]
    simp [σ8]
  have hO := out0_eq G P Q s k₀ q₀
  have hOl : (pre7 ++ toWord G ++ [k₀, q₀] ++ toWord (distMatrix G) ++ toWord (family G k₀ q₀)) =
      hdOf G P Q s k₀ q₀ .stp ++ rQ G k₀ q₀ .stp := by rw [hO, hpre7]
  have hlenO := congrArg List.length hOl
  obtain ⟨r14, o14⟩ := ofr_assign (W := W) (x := "ql")
    (v := (pre7 ++ toWord G ++ [k₀, q₀] ++ toWord (distMatrix G) ++ toWord (family G k₀ q₀)).length - pre7.length)
    (ev_sub (ev_var hpo13 (by
        simp only [List.length_append, List.length_cons, List.length_nil]; rw [hl7]; omega))
      (ev_var hqa13 (by rw [hl7]; unfold k0 at hW; omega)) (by simp; omega))
  refine ⟨σ13.setVar "ql" ((pre7 ++ toWord G ++ [k₀, q₀] ++ toWord (distMatrix G) ++ toWord (family G k₀ q₀)).length -
    pre7.length), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have r3' := r3
    have r4' := r4.mono (show 1 + 8 * sc0.length ≤ 81 by simp [sc0])
    have r5' := r5.mono (show 1 + 8 * mid0.length ≤ 121 by simp [length_mid0])
    have r6' := r6.mono (show 1 + 8 * ["q1"].length ≤ 9 by simp)
    have r7' := r7.mono (show 1 + 8 * (s3W ++ qE0).length ≤ 1 + 8 * (s3W.length + qE0.length) by simp)
    have r10' := r10.mono (show 1 + 8 * ["gK", "gq"].length ≤ 17 by simp)
    have r8' := r8.mono (show 1 + (Expr.var "po").size ≤ 2 by simp [Expr.size])
    have r11' := r11.mono (show 1 + (Expr.add (.var "pq") (.lit 3)).size ≤ 4 by simp [Expr.size])
    have r12' := r12.mono (show 1 + (Expr.sub (.var "nx") (.var "qs")).size ≤ 4 by simp [Expr.size])
    have r10b' := r10b.mono (show 1 + (Expr.sub (.var "pq") (.var "pp")).size ≤ 4 by simp [Expr.size])
    have r14' := r14.mono (show 1 + (Expr.sub (.var "po") (.var "qa")).size ≤ 4 by simp [Expr.size])
    unfold fill0
    exact (Run.seq r1 (Run.seq r2 (Run.seq r3' (Run.seq r4' (Run.seq r5' (Run.seq r6' (Run.seq r7'
      (Run.seq r8' (Run.seq r9 (Run.seq r10' (Run.seq r10b' (Run.seq r10c (Run.seq r11' (Run.seq r12'
      (Run.seq r13 r14'))))))))))))))).mono
      (by omega)
  · rw [← hOl]; exact F13.setVar (by decide) _
  · simp only [vars_setVar, if_neg (show ("qa" : String) ≠ "ql" by decide)]
    rw [hqa13, ← hlenO, qF_stp]; simp
  · simp only [vars_setVar, ↓reduceIte]
    rw [qF_stp]; simp
  · simp only [vars_setVar, if_neg (show ("gX" : String) ≠ "ql" by decide)]
    rw [o13.vars _ (by decide)]; simp [σ12, σ11]; rw [o10c.vars _ (by decide)]; simp [σ10b]
    rw [o10.vars _ (by decide), o9.vars _ (by decide), hv8 _ (by decide), v1X]
  · have := ((((((((o1.trans o18).trans o9).trans o10).trans o10b).trans o10c).trans o11).trans o12).trans
      o13).trans o14
    exact this.mono (by decide)

end Lax185574Proofs.ResolveRam.Glue
