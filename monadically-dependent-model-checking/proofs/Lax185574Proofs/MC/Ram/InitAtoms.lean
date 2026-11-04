import Lax185574Proofs.MC.Ram.Push
import Lax185574Proofs.MC.InitLen

/-!
The IMP+ command that appends the atoms of an initial tree to the
array `tb`, at the position in the scalar `iwp`: `wAtoms` appends
`atomsOut a rm rp c` for the values `a`, `rm`, `rp` and `c` of the
scalars `iwa`, `iwrm`, `iwrp` and `iwc`.
-/

namespace Lax185574Proofs.MC

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words

theorem evalB_var_of {B : ℕ} {x : String} {τ : Env} {v : ℕ} (h : τ.vars x = v) (hv : v < B) :
    (Expr.var x).evalB B τ = some v := by
  rw [← h]; exact evalB_var (by omega)

/-- The equality atoms. -/
def wEq : Com :=
  forUp "iwi" (.var "iwa") (forUp "iwj" (.var "iwa")
    (pushL "tb" "iwp" [.lit 3, .lit 0, .var "iwi", .var "iwj"]))

/-- The color atoms. -/
def wCol : Com :=
  forUp "iwi" (.var "iwa") (pushL "tb" "iwp" [.lit 3, .lit 3, .var "iwc", .var "iwi"])

/-- The distance atoms. -/
def wDist : Com :=
  forUp "iwr" (.add (.var "iwrm") (.lit 1)) (forUp "iwi" (.var "iwa") (forUp "iwj" (.var "iwa")
    (pushL "tb" "iwp" [.lit 4, .lit 4, .var "iwr", .var "iwi", .var "iwj"])))

/-- The color distance atoms. -/
def wCDist : Com :=
  forUp "iwr" (.var "iwrp") (forUp "iwi" (.var "iwa")
    (pushL "tb" "iwp" [.lit 4, .lit 5, .add (.var "iwr") (.lit 1), .var "iwc", .var "iwi"]))

/-- All atoms. -/
def wAtoms : Com := .seq wEq (.seq wCol (.seq wDist wCDist))

/-- The context of the atom writer. -/
structure ACtx (a rm rp c cap : ℕ) (τ : Env) : Prop where
  ha : τ.vars "iwa" = a
  hrm : τ.vars "iwrm" = rm
  hrp : τ.vars "iwrp" = rp
  hc : τ.vars "iwc" = c
  hcap : (τ.arrs "tb").length = cap

theorem ACtx.setVar {a rm rp c cap : ℕ} {τ : Env} (h : ACtx a rm rp c cap τ) {y : String}
    (h1 : y ≠ "iwa") (h2 : y ≠ "iwrm") (h3 : y ≠ "iwrp") (h4 : y ≠ "iwc") (v : ℕ) :
    ACtx a rm rp c cap (τ.setVar y v) :=
  ⟨by simp [Ne.symm h1, h.ha], by simp [Ne.symm h2, h.hrm], by simp [Ne.symm h3, h.hrp],
    by simp [Ne.symm h4, h.hc], by simp [h.hcap]⟩

/-- The context survives an append. -/
theorem ACtx.of_push {a rm rp c cap : ℕ} {τ τ' : Env} (h : ACtx a rm rp c cap τ)
    (hv : ∀ y, y ≠ "iwp" → τ'.vars y = τ.vars y) (hl : (τ'.arrs "tb").length = (τ.arrs "tb").length) :
    ACtx a rm rp c cap τ' :=
  ⟨by rw [hv _ (by decide), h.ha], by rw [hv _ (by decide), h.hrm],
    by rw [hv _ (by decide), h.hrp], by rw [hv _ (by decide), h.hc], by rw [hl, h.hcap]⟩

theorem flatMap_range_succ' {f : ℕ → List ℕ} (k : ℕ) :
    (List.range (k + 1)).flatMap f = (List.range k).flatMap f ++ f k := by
  rw [List.range_succ, List.flatMap_append]; simp

theorem length_flatMap_const {f : ℕ → List ℕ} {m : ℕ} (hf : ∀ k, (f k).length = m) (N : ℕ) :
    ((List.range N).flatMap f).length = N * m := by
  induction N with
  | zero => simp
  | succ N ih => rw [flatMap_range_succ', List.length_append, ih, hf]; ring

theorem forall₂_snoc {R : Expr → ℕ → Prop} {l₁ : List Expr} {l₂ : List ℕ} {a : Expr} {b : ℕ}
    (h : List.Forall₂ R l₁ l₂) (hr : R a b) : List.Forall₂ R (l₁ ++ [a]) (l₂ ++ [b]) := by
  induction h with
  | nil => exact .cons hr .nil
  | cons h _ ih => exact .cons h ih

/-- A counting loop over `j < N` whose body appends `vs ++ [j]`. -/
theorem loopPush {B : ℕ} {j : String} (hj : j ≠ "iwp") {e : Expr} {es : List Expr}
    {vs : List ℕ} {N cap : ℕ} (P : Env → Prop) (hPj : ∀ τ v, P τ → P (τ.setVar j v))
    (hPpush : ∀ τ τ', P τ → (∀ y, y ≠ "iwp" → τ'.vars y = τ.vars y) →
      (∀ b, b ≠ "tb" → τ'.arrs b = τ.arrs b) →
      (τ'.arrs "tb").length = (τ.arrs "tb").length → P τ')
    (hcapP : ∀ τ, P τ → (τ.arrs "tb").length = cap)
    (hev : ∀ τ τ', P τ → (∀ y, y ≠ "iwp" → τ'.vars y = τ.vars y) →
      (∀ b, b ≠ "tb" → τ'.arrs b = τ.arrs b) →
      List.Forall₂ (fun e v => e.evalB B τ' = some v) es vs)
    (he : ∀ τ, P τ → e.evalB B τ = some N) {σ : Env} {l : List ℕ} (hP : P σ)
    (hF : Filled "tb" "iwp" l σ) (hcap : l.length + N * (vs.length + 1) ≤ cap)
    (hB : l.length + N * (vs.length + 1) + N + 1 < B) :
    ∃ σ', Run B (forUp j e (pushL "tb" "iwp" (es ++ [(.var j : Expr)]))) σ σ'
      (N * ((1 + 7 * (es.length + 1) + ((es ++ [(.var j : Expr)]).map Expr.size).sum) + e.size + 7) +
        e.size + 5) ∧
      P σ' ∧ Filled "tb" "iwp" (l ++ (List.range N).flatMap fun k => vs ++ [k]) σ' := by
  have hlen : es.length = vs.length :=
    (hev σ σ hP (fun _ _ => rfl) (fun _ _ => rfl)).length_eq
  obtain ⟨σ', r, ⟨hP', -⟩, -, F⟩ := forUp_append (B := B) (i := j) (e := e)
    (body := pushL "tb" "iwp" (es ++ [.var j])) (N := N)
    (K := 1 + 7 * (es.length + 1) + ((es ++ [(.var j : Expr)]).map Expr.size).sum) (a := "tb") (pv := "iwp")
    hj (fun k => vs ++ [k]) (fun τ => P τ ∧ True) (fun τ v h => ⟨hPj τ v h.1, trivial⟩)
    (by omega) ⟨hP, trivial⟩ hF (fun τ h => he τ h.1)
    (by
      rintro k hk τ ⟨hτ, -⟩ hτk hFk
      have hl : (l ++ (List.range k).flatMap fun k => vs ++ [k]).length = l.length +
          k * (vs.length + 1) := by
        simp [List.length_flatMap, List.sum_replicate]
      have hkk : k * (vs.length + 1) + (vs.length + 1) ≤ N * (vs.length + 1) := by
        have := Nat.mul_le_mul_right (vs.length + 1) (show k + 1 ≤ N by omega)
        simpa [Nat.add_mul] using this
      obtain ⟨τ', r, F', fv, fa, fl, -, -⟩ := pushL_run (B := B) (es := es ++ [.var j])
        (vs := vs ++ [k]) hFk
        (by
          intro τ' hv ha
          exact forall₂_snoc (hev τ τ' hτ hv ha) (evalB_var_of ((hv _ hj).trans hτk) (by omega)))
        (by rw [hcapP τ hτ, hl]; simp only [List.length_append, List.length_singleton]; omega)
        (by rw [hl]; simp only [List.length_append, List.length_singleton]; omega)
      refine ⟨τ', r.mono (by simp), by rw [fv _ hj, hτk], ⟨hPpush τ τ' hτ fv fa fl, trivial⟩, ?_⟩
      rw [flatMap_range_succ', ← List.append_assoc]; exact F')
  exact ⟨σ', r, hP', F⟩

theorem ACtx.push {a rm rp c cap : ℕ} (τ τ' : Env) (h : ACtx a rm rp c cap τ)
    (hv : ∀ y, y ≠ "iwp" → τ'.vars y = τ.vars y) (_ : ∀ b, b ≠ "tb" → τ'.arrs b = τ.arrs b)
    (hl : (τ'.arrs "tb").length = (τ.arrs "tb").length) : ACtx a rm rp c cap τ' :=
  h.of_push hv hl

/-- The four blocks of the atoms, in the form the loops produce. -/
def eqRow (a i : ℕ) : List ℕ := (List.range a).flatMap fun j => [3, 0, i] ++ [j]
def eqL (a : ℕ) : List ℕ := (List.range a).flatMap fun i => eqRow a i
def colL (a c : ℕ) : List ℕ := (List.range a).flatMap fun k => [3, 3, c] ++ [k]
def distRow (a r i : ℕ) : List ℕ := (List.range a).flatMap fun j => [4, 4, r, i] ++ [j]
def distBlk (a r : ℕ) : List ℕ := (List.range a).flatMap fun i => distRow a r i
def distL (a rm : ℕ) : List ℕ := (List.range (rm + 1)).flatMap fun r => distBlk a r
def cdistRow (a c r : ℕ) : List ℕ := (List.range a).flatMap fun i => [4, 5, r + 1, c] ++ [i]
def cdistL (a rp c : ℕ) : List ℕ := (List.range rp).flatMap fun r => cdistRow a c r

theorem atomsOut_eq (a rm rp c : ℕ) :
    atomsOut a rm rp c = eqL a ++ colL a c ++ distL a rm ++ cdistL a rp c := rfl

theorem len_eqRow (a i : ℕ) : (eqRow a i).length = 4 * a := by
  rw [eqRow, length_flatMap_const (m := 4) (fun _ => rfl)]; ring
theorem len_eqL (a : ℕ) : (eqL a).length = a * (4 * a) := by
  rw [eqL, length_flatMap_const (len_eqRow a)]
theorem len_colL (a c : ℕ) : (colL a c).length = a * 4 := by
  rw [colL, length_flatMap_const (m := 4) (fun _ => rfl)]
theorem len_distRow (a r i : ℕ) : (distRow a r i).length = a * 5 := by
  rw [distRow, length_flatMap_const (m := 5) (fun _ => rfl)]
theorem len_distBlk (a r : ℕ) : (distBlk a r).length = a * (a * 5) := by
  rw [distBlk, length_flatMap_const (len_distRow a r)]
theorem len_distL (a rm : ℕ) : (distL a rm).length = (rm + 1) * (a * (a * 5)) := by
  rw [distL, length_flatMap_const (len_distBlk a)]
theorem len_cdistRow (a c r : ℕ) : (cdistRow a c r).length = a * 5 := by
  rw [cdistRow, length_flatMap_const (m := 5) (fun _ => rfl)]
theorem len_cdistL (a rp c : ℕ) : (cdistL a rp c).length = rp * (a * 5) := by
  rw [cdistL, length_flatMap_const (len_cdistRow a c)]

theorem prefix_le {k N m : ℕ} (h : k < N) : k * m + m ≤ N * m := by
  have := Nat.mul_le_mul_right m (show k + 1 ≤ N by omega); simpa [Nat.add_mul] using this

/-- **The atom writer.** -/
theorem wAtoms_run {B a rm rp c cap : ℕ} {l : List ℕ} {τ : Env} (hC : ACtx a rm rp c cap τ)
    (hF : Filled "tb" "iwp" l τ) (hcap : l.length + (atomsOut a rm rp c).length ≤ cap)
    (hB : l.length + (atomsOut a rm rp c).length + rm + rp + a + c + 8 < B) :
    ∃ τ' K, Run B wAtoms τ τ' K ∧ K ≤ 100 * ((rm + rp + 2) * ((a + 1) * (a + 1))) ∧
      ACtx a rm rp c cap τ' ∧ Filled "tb" "iwp" (l ++ atomsOut a rm rp c) τ' := by
  rw [atomsOut_eq] at hcap hB ⊢
  simp only [List.length_append, len_eqL, len_colL, len_distL, len_cdistL] at hcap hB
  -- equalities
  obtain ⟨τ₁, r₁, ⟨C₁, -⟩, -, F₁⟩ := forUp_append (B := B) (i := "iwi") (e := .var "iwa")
    (body := forUp "iwj" (.var "iwa") (pushL "tb" "iwp"
      ([.lit 3, .lit 0, .var "iwi"] ++ [(.var "iwj" : Expr)])))
    (N := a) (K := a * ((1 + 7 * 4 + 4) + 1 + 7) + 1 + 5) (a := "tb") (pv := "iwp") (by decide)
    (fun i => eqRow a i) (fun τ => ACtx a rm rp c cap τ ∧ True)
    (fun τ v h => ⟨h.1.setVar (by decide) (by decide) (by decide) (by decide) v, trivial⟩)
    (by omega) ⟨hC, trivial⟩ hF (fun τ h => evalB_var_of h.1.ha (by omega))
    (by
      rintro i hi τ ⟨hτ, -⟩ hii hFi
      have hl : (l ++ (List.range i).flatMap fun i => eqRow a i).length = l.length + i * (4 * a) := by
        rw [List.length_append, length_flatMap_const (len_eqRow a)]
      have := prefix_le (m := 4 * a) hi
      obtain ⟨τ', r', ⟨C', -⟩, F'⟩ := loopPush (B := B) (j := "iwj") (by decide)
        (e := .var "iwa") (es := [.lit 3, .lit 0, .var "iwi"]) (vs := [3, 0, i]) (N := a)
        (cap := cap) (fun τ => ACtx a rm rp c cap τ ∧ τ.vars "iwi" = i)
        (fun τ v h => ⟨h.1.setVar (by decide) (by decide) (by decide) (by decide) v,
          by simp [h.2]⟩)
        (fun τ τ' h hv ha hl => ⟨h.1.push τ τ' hv ha hl, by rw [hv _ (by decide), h.2]⟩)
        (fun τ h => h.1.hcap)
        (fun τ τ' h hv _ => .cons (evalB_lit (by omega)) (.cons (evalB_lit (by omega))
          (.cons (evalB_var_of ((hv _ (by decide)).trans h.2) (by omega)) .nil)))
        (fun τ h => evalB_var_of h.1.ha (by omega)) ⟨hτ, hii⟩ hFi
        (by rw [hl]; simp only [List.length_cons, List.length_nil]; omega)
        (by rw [hl]; simp only [List.length_cons, List.length_nil]; omega)
      refine ⟨τ', r'.mono (by simp), by rw [r'.frame_var "iwi" (by decide), hii], ⟨C', trivial⟩, ?_⟩
      rw [flatMap_range_succ', ← List.append_assoc]; exact F')
  change Filled "tb" "iwp" (l ++ eqL a) τ₁ at F₁
  -- colors
  obtain ⟨τ₂, r₂, ⟨C₂, -⟩, F₂⟩ := loopPush (B := B) (j := "iwi") (by decide)
    (e := .var "iwa") (es := [.lit 3, .lit 3, .var "iwc"]) (vs := [3, 3, c]) (N := a) (cap := cap)
    (fun τ => ACtx a rm rp c cap τ ∧ True)
    (fun τ v h => ⟨h.1.setVar (by decide) (by decide) (by decide) (by decide) v, trivial⟩)
    (fun τ τ' h hv ha hl => ⟨h.1.push τ τ' hv ha hl, trivial⟩) (fun τ h => h.1.hcap)
    (fun τ τ' h hv _ => .cons (evalB_lit (by omega)) (.cons (evalB_lit (by omega))
      (.cons (evalB_var_of ((hv _ (by decide)).trans h.1.hc) (by omega)) .nil)))
    (fun τ h => evalB_var_of h.1.ha (by omega)) ⟨C₁, trivial⟩ F₁
    (by rw [List.length_append, len_eqL]; simp only [List.length_cons, List.length_nil]; omega)
    (by rw [List.length_append, len_eqL]; simp only [List.length_cons, List.length_nil]; omega)
  change Filled "tb" "iwp" (l ++ eqL a ++ colL a c) τ₂ at F₂
  -- distances
  obtain ⟨τ₃, r₃, ⟨C₃, -⟩, -, F₃⟩ := forUp_append (B := B) (i := "iwr")
    (e := .add (.var "iwrm") (.lit 1))
    (body := forUp "iwi" (.var "iwa") (forUp "iwj" (.var "iwa") (pushL "tb" "iwp"
      ([.lit 4, .lit 4, .var "iwr", .var "iwi"] ++ [(.var "iwj" : Expr)]))))
    (N := rm + 1) (K := a * ((a * ((1 + 7 * 5 + 5) + 1 + 7) + 1 + 5) + 1 + 7) + 1 + 5)
    (a := "tb") (pv := "iwp") (by decide) (fun r => distBlk a r)
    (fun τ => ACtx a rm rp c cap τ ∧ True)
    (fun τ v h => ⟨h.1.setVar (by decide) (by decide) (by decide) (by decide) v, trivial⟩)
    (by omega) ⟨C₂, trivial⟩ F₂
    (fun τ h => evalB_bin (evalB_var_of h.1.hrm (by omega)) (evalB_lit (by omega)) (by simp; omega))
    (by
      rintro r hr τ ⟨hτ, -⟩ hrr hFr
      have hlr := prefix_le (m := a * (a * 5)) hr
      obtain ⟨τ', r', ⟨C', -⟩, -, F'⟩ := forUp_append (B := B) (i := "iwi") (e := .var "iwa")
        (body := forUp "iwj" (.var "iwa") (pushL "tb" "iwp"
          ([.lit 4, .lit 4, .var "iwr", .var "iwi"] ++ [(.var "iwj" : Expr)])))
        (N := a) (K := a * ((1 + 7 * 5 + 5) + 1 + 7) + 1 + 5) (a := "tb") (pv := "iwp")
        (by decide) (fun i => distRow a r i)
        (fun τ => ACtx a rm rp c cap τ ∧ τ.vars "iwr" = r)
        (fun τ v h => ⟨h.1.setVar (by decide) (by decide) (by decide) (by decide) v,
          by simp [h.2]⟩)
        (by omega) ⟨hτ, hrr⟩ hFr (fun τ h => evalB_var_of h.1.ha (by omega))
        (by
          rintro i hi ρ ⟨hρ, hρr⟩ hρi hFi
          have hli := prefix_le (m := a * 5) hi
          have hl : (l ++ eqL a ++ colL a c ++ (List.range r).flatMap (fun r => distBlk a r) ++
              (List.range i).flatMap fun i => distRow a r i).length =
              l.length + a * (4 * a) + a * 4 + r * (a * (a * 5)) + i * (a * 5) := by
            simp only [List.length_append, len_eqL, len_colL]
            rw [length_flatMap_const (len_distBlk a), length_flatMap_const (len_distRow a r)]
          obtain ⟨ρ', r'', ⟨C'', hr'', -⟩, F''⟩ := loopPush (B := B) (j := "iwj") (by decide)
            (e := .var "iwa") (es := [.lit 4, .lit 4, .var "iwr", .var "iwi"]) (vs := [4, 4, r, i])
            (N := a) (cap := cap)
            (fun τ => ACtx a rm rp c cap τ ∧ τ.vars "iwr" = r ∧ τ.vars "iwi" = i)
            (fun τ v h => ⟨h.1.setVar (by decide) (by decide) (by decide) (by decide) v,
              by simp [h.2.1], by simp [h.2.2]⟩)
            (fun τ τ' h hv ha hl => ⟨h.1.push τ τ' hv ha hl, by rw [hv _ (by decide), h.2.1],
              by rw [hv _ (by decide), h.2.2]⟩)
            (fun τ h => h.1.hcap)
            (fun τ τ' h hv _ => .cons (evalB_lit (by omega)) (.cons (evalB_lit (by omega))
              (.cons (evalB_var_of ((hv _ (by decide)).trans h.2.1) (by omega))
              (.cons (evalB_var_of ((hv _ (by decide)).trans h.2.2) (by omega)) .nil))))
            (fun τ h => evalB_var_of h.1.ha (by omega)) ⟨hρ, hρr, hρi⟩ hFi
            (by
              rw [hl]; simp only [List.length_cons, List.length_nil]
              have : r * (a * (a * 5)) + i * (a * 5) + a * 5 ≤ (rm + 1) * (a * (a * 5)) := by
                nlinarith
              omega)
            (by
              rw [hl]; simp only [List.length_cons, List.length_nil]
              have : r * (a * (a * 5)) + i * (a * 5) + a * 5 ≤ (rm + 1) * (a * (a * 5)) := by
                nlinarith
              omega)
          refine ⟨ρ', r''.mono (by simp), by rw [r''.frame_var "iwi" (by decide), hρi],
            ⟨C'', hr''⟩, ?_⟩
          rw [flatMap_range_succ', ← List.append_assoc]; exact F'')
      refine ⟨τ', r'.mono (by simp), by rw [r'.frame_var "iwr" (by decide), hrr], ⟨C', trivial⟩,
        ?_⟩
      rw [flatMap_range_succ', ← List.append_assoc]; exact F')
  change Filled "tb" "iwp" (l ++ eqL a ++ colL a c ++ distL a rm) τ₃ at F₃
  -- color distances
  obtain ⟨τ₄, r₄, ⟨C₄, -⟩, -, F₄⟩ := forUp_append (B := B) (i := "iwr") (e := .var "iwrp")
    (body := forUp "iwi" (.var "iwa") (pushL "tb" "iwp"
      ([.lit 4, .lit 5, .add (.var "iwr") (.lit 1), .var "iwc"] ++ [(.var "iwi" : Expr)])))
    (N := rp) (K := a * ((1 + 7 * 5 + 7) + 1 + 7) + 1 + 5) (a := "tb") (pv := "iwp") (by decide)
    (fun r => cdistRow a c r) (fun τ => ACtx a rm rp c cap τ ∧ True)
    (fun τ v h => ⟨h.1.setVar (by decide) (by decide) (by decide) (by decide) v, trivial⟩)
    (by omega) ⟨C₃, trivial⟩ F₃ (fun τ h => evalB_var_of h.1.hrp (by omega))
    (by
      rintro r hr τ ⟨hτ, -⟩ hrr hFr
      have hlr := prefix_le (m := a * 5) hr
      have hl : (l ++ eqL a ++ colL a c ++ distL a rm ++
          (List.range r).flatMap fun r => cdistRow a c r).length =
          l.length + a * (4 * a) + a * 4 + (rm + 1) * (a * (a * 5)) + r * (a * 5) := by
        simp only [List.length_append, len_eqL, len_colL, len_distL]
        rw [length_flatMap_const (len_cdistRow a c)]
      obtain ⟨τ', r', ⟨C', -⟩, F'⟩ := loopPush (B := B) (j := "iwi") (by decide)
        (e := .var "iwa") (es := [.lit 4, .lit 5, .add (.var "iwr") (.lit 1), .var "iwc"])
        (vs := [4, 5, r + 1, c]) (N := a) (cap := cap)
        (fun τ => ACtx a rm rp c cap τ ∧ τ.vars "iwr" = r)
        (fun τ v h => ⟨h.1.setVar (by decide) (by decide) (by decide) (by decide) v,
          by simp [h.2]⟩)
        (fun τ τ' h hv ha hl => ⟨h.1.push τ τ' hv ha hl, by rw [hv _ (by decide), h.2]⟩)
        (fun τ h => h.1.hcap)
        (fun τ τ' h hv _ => .cons (evalB_lit (by omega)) (.cons (evalB_lit (by omega))
          (.cons (evalB_bin (evalB_var_of ((hv _ (by decide)).trans h.2) (by omega))
            (evalB_lit (by omega)) (by simp; omega))
          (.cons (evalB_var_of ((hv _ (by decide)).trans h.1.hc) (by omega)) .nil))))
        (fun τ h => evalB_var_of h.1.ha (by omega)) ⟨hτ, hrr⟩ hFr
        (by rw [hl]; simp only [List.length_cons, List.length_nil]; omega)
        (by rw [hl]; simp only [List.length_cons, List.length_nil]; omega)
      refine ⟨τ', r'.mono (by simp), by rw [r'.frame_var "iwr" (by decide), hrr], ⟨C', trivial⟩, ?_⟩
      rw [flatMap_range_succ', ← List.append_assoc]; exact F')
  change Filled "tb" "iwp" (l ++ eqL a ++ colL a c ++ distL a rm ++ cdistL a rp c) τ₄ at F₄
  refine ⟨τ₄, _, Run.seq r₁ (Run.seq r₂ (Run.seq r₃ r₄)), ?_, C₄,
    by simpa only [List.append_assoc] using F₄⟩
  simp only [size_var, size_add, size_lit, List.length_cons, List.length_nil, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, List.map_append, List.sum_append, Expr.size]
  ring_nf
  nlinarith [Nat.zero_le (rm * a * a), Nat.zero_le (rp * a * a), Nat.zero_le (rm * a),
    Nat.zero_le (rp * a), Nat.zero_le (a * a)]

end Lax185574Proofs.MC
