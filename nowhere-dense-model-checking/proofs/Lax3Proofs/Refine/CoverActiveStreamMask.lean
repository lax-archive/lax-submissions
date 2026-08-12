import Lax3Proofs.Refine.CoverActiveStreamLoad

/-!
# Block-local masks on one streamed row

The reusable stream buffer may be larger than the carrier, even though only
`xmem[0..tail)` is executed.  `BlockLeaves.blockMapCom` fixes the logical
length of its index array to the carrier, while its range form already keeps
that allocation width separate.  This module supplies the small prefix
adapter: initialize the range to `[0,tail)`, run the verified indirect map,
and upgrade its sparse result to an exact whole-carrier equation whenever the
entry and intended result are supported by the streamed row.
-/

namespace Lax3Proofs.Refine.CoverActiveStreamMask

open Lax3.ColoredGraphs
open Lax3Proofs.RamDriver
open Lax3Proofs.RamDriverCluster
open Lax3Proofs.RamDriverDescend
open Lax3Proofs.Refine.CoverActiveStreamLoad
open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ## Arbitrary resident-width prefix map -/

/-- Run a verified indirect map on the executed prefix `idx[0..tail)`.
The two assignments are the adapter from a streamed row to the range API. -/
def streamBlockMapCom (idx dst : String) (x : Expr) : Com :=
  .seq (.assign "p" (.lit 0))
    (.seq (.assign "pend" (.var "tail"))
      (BlockLeaves.blockMapRangeCom idx dst x))

def streamBlockMapCost (tail : ℕ) (x : Expr) : ℕ :=
  (13 + x.size) * tail + 8

/-- The range map on a streamed prefix.  `na` is only an allocation width;
the word-bound obligation is `tail ≤ n < B`, exactly the executed addresses. -/
theorem streamBlockMapCom_spec {B n na tail : ℕ} {idx dst : String} {x : Expr}
    {Idx F g₀ : ℕ → ℕ} {l : List (String × ℕ × (ℕ → ℕ))}
    (h1B : 1 < B) (hnB : n < B) (htail : tail ≤ n) (hfit : tail ≤ na)
    (hIdx : ∀ q, q < tail → Idx q < n) (hdi : dst ≠ idx)
    (hdf : ∀ a ∈ l, a.1 ≠ dst)
    (hx : ∀ (σ : Env) q, q < tail → σ.vars "p" = q →
      σ.vars "cw" = Idx q →
      BlockLeaves.BlockMapRangeInv n na 0 tail idx dst Idx F g₀ l σ →
      x.evalB B σ = some (F (Idx q))) :
    Spec B
      (fun σ => σ.vars "tail" = tail ∧ σ.arrs idx = arrOf na Idx ∧
        σ.arrs dst = arrOf n g₀ ∧ BlockLeaves.BlockFrozen l σ)
      (streamBlockMapCom idx dst x)
      (fun _ σ' =>
        (∃ g, σ'.arrs dst = arrOf n g ∧
          (∀ q, q < tail → g (Idx q) = F (Idx q)) ∧
          (∀ v, v < n → (∀ q, q < tail → Idx q ≠ v) → g v = g₀ v)) ∧
        σ'.vars "tail" = tail ∧ σ'.arrs idx = arrOf na Idx ∧
        BlockLeaves.BlockFrozen l σ')
      (streamBlockMapCost tail x) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨htailVar, hidx, hdst, hfr⟩ := hσ
  have htailB : tail < B := lt_of_le_of_lt htail hnB
  set σ₁ := σ.setVar "p" 0 with hσ₁
  have r₁ : Run B (.assign "p" (.lit 0)) σ σ₁ 2 :=
    Run.assign (evalB_lit (by omega))
  have htail₁ : σ₁.vars "tail" = tail := by
    rw [hσ₁, vars_setVar, if_neg (by decide)]
    exact htailVar
  have etail : (Expr.var "tail").evalB B σ₁ = some tail := by
    have h := evalB_var (B := B) (x := "tail") (σ := σ₁) (by rw [htail₁]; exact htailB)
    rwa [htail₁] at h
  set σ₂ := σ₁.setVar "pend" tail with hσ₂
  have r₂ : Run B (.assign "pend" (.var "tail")) σ₁ σ₂ 2 :=
    Run.assign etail
  have hp₂ : σ₂.vars "p" = 0 := by
    rw [hσ₂, vars_setVar, if_neg (by decide), hσ₁, vars_setVar, if_pos rfl]
  have hpend₂ : σ₂.vars "pend" = tail := by simp [hσ₂]
  have htail₂ : σ₂.vars "tail" = tail := by
    rw [hσ₂, vars_setVar, if_neg (by decide)]
    exact htail₁
  have hidx₂ : σ₂.arrs idx = arrOf na Idx := by simp [hσ₂, hσ₁, hidx]
  have hdst₂ : σ₂.arrs dst = arrOf n g₀ := by simp [hσ₂, hσ₁, hdst]
  have hfr₂ : BlockLeaves.BlockFrozen l σ₂ := by
    intro a ha
    simp only [hσ₂, arrs_setVar, hσ₁]
    exact hfr a ha
  obtain ⟨σ₃, r₃, ⟨g, hg, hset, hkeep⟩, -, -, hidx₃, hfr₃⟩ :=
    (BlockLeaves.blockMapRangeCom_spec (B := B) (n := n) (w := na)
      (p₀ := 0) (e := tail) (idx := idx) (dst := dst) (x := x)
      (Idx := Idx) (F := F) (g₀ := g₀) (l := l)
      h1B hnB htailB hfit (by omega)
      (fun q _ hq => hIdx q hq) hdi hdf
      (fun ρ q _ hq hp hcw hI => hx ρ q hq hp hcw hI)).run
      ⟨hp₂, hpend₂, hidx₂, hdst₂, hfr₂⟩
  have htail₃ : σ₃.vars "tail" = tail := by
    rw [r₃.frame_var "tail" (by
      simp [BlockLeaves.blockMapRangeCom, Com.wvars])]
    exact htail₂
  refine ⟨σ₃, 2 + (2 + ((13 + x.size) * tail + 4)),
    r₁.seq (r₂.seq r₃), ?_, ?_⟩
  · simp only [streamBlockMapCost]
    omega
  · refine ⟨⟨g, hg, ?_, ?_⟩, htail₃, hidx₃, hfr₃⟩
    · intro q hq
      exact hset q (by omega) hq
    · intro v hv hout
      exact hkeep v hv (fun q _ hq => hout q hq)

/-- Supported entry storage upgrades the sparse streamed write to the exact
whole-carrier function, while preserving row support for the next pass. -/
theorem streamBlockMapCom_supported_spec
    {B n na tail : ℕ} {idx dst : String} {x : Expr}
    {Idx F g₀ : ℕ → ℕ} {l : List (String × ℕ × (ℕ → ℕ))}
    (h1B : 1 < B) (hnB : n < B) (htail : tail ≤ n) (hfit : tail ≤ na)
    (hIdx : ∀ q, q < tail → Idx q < n) (hdi : dst ≠ idx)
    (hdf : ∀ a ∈ l, a.1 ≠ dst)
    (hx : ∀ (σ : Env) q, q < tail → σ.vars "p" = q →
      σ.vars "cw" = Idx q →
      BlockLeaves.BlockMapRangeInv n na 0 tail idx dst Idx F g₀ l σ →
      x.evalB B σ = some (F (Idx q))) :
    Spec B
      (fun σ => σ.vars "tail" = tail ∧ σ.arrs idx = arrOf na Idx ∧
        σ.arrs dst = arrOf n g₀ ∧ BlockLeaves.BlockFrozen l σ ∧
        BlockSupported n 0 tail Idx F ∧ BlockSupported n 0 tail Idx g₀)
      (streamBlockMapCom idx dst x)
      (fun _ σ' =>
        (∃ g, σ'.arrs dst = arrOf n g ∧
          (∀ v, v < n → g v = F v) ∧ BlockSupported n 0 tail Idx g) ∧
        σ'.vars "tail" = tail ∧ σ'.arrs idx = arrOf na Idx ∧
        BlockLeaves.BlockFrozen l σ')
      (streamBlockMapCost tail x) := by
  refine (streamBlockMapCom_spec h1B hnB htail hfit hIdx hdi hdf hx).pre ?_ |>.post ?_
  · rintro σ ⟨ht, hi, hd, hf, -, -⟩
    exact ⟨ht, hi, hd, hf⟩
  · rintro σ σ' ⟨-, -, -, -, hF, hg₀⟩
      ⟨⟨g, hg, hset, hkeep⟩, ht, hi, hf⟩
    obtain ⟨hval, hsup⟩ := sparseBlock_eq_of_supported
      (p₀ := 0) (e := tail) (fun q _ hq => hset q hq)
      (fun v hv hout => hkeep v hv (fun q hq => hout q (by omega) hq)) hg₀ hF
    exact ⟨⟨g, hg, hval, hsup⟩, ht, hi, hf⟩

/-! ## The mask shapes used by descent -/

def streamBlockClearCom (idx dst : String) : Com :=
  streamBlockMapCom idx dst (.lit 0)

def streamBlockAndCom (idx a b dst : String) : Com :=
  streamBlockMapCom idx dst (.mul (.get a (.var "cw")) (.get b (.var "cw")))

def streamBlockSubCom (idx a b dst : String) : Com :=
  streamBlockMapCom idx dst
    (.mul (.get a (.var "cw")) (.sub (.lit 1) (.get b (.var "cw"))))

def streamBlockClearCost (tail : ℕ) : ℕ := 14 * tail + 8
def streamBlockAndCost (tail : ℕ) : ℕ := 18 * tail + 8
def streamBlockSubCost (tail : ℕ) : ℕ := 20 * tail + 8

theorem streamBlockClearCom_supported_spec
    {B n na tail : ℕ} {idx dst : String} {Idx g₀ : ℕ → ℕ}
    (h1B : 1 < B) (hnB : n < B) (htail : tail ≤ n) (hfit : tail ≤ na)
    (hIdx : ∀ q, q < tail → Idx q < n) (hdi : dst ≠ idx) :
    Spec B
      (fun σ => σ.vars "tail" = tail ∧ σ.arrs idx = arrOf na Idx ∧
        σ.arrs dst = arrOf n g₀ ∧ BlockSupported n 0 tail Idx g₀)
      (streamBlockClearCom idx dst)
      (fun _ σ' =>
        (∃ g, σ'.arrs dst = arrOf n g ∧
          (∀ v, v < n → g v = 0) ∧ BlockSupported n 0 tail Idx g) ∧
        σ'.vars "tail" = tail ∧ σ'.arrs idx = arrOf na Idx)
      (streamBlockClearCost tail) := by
  have h := streamBlockMapCom_supported_spec (B := B) (n := n) (na := na)
    (tail := tail) (idx := idx) (dst := dst) (x := .lit 0)
    (Idx := Idx) (F := fun _ => 0) (g₀ := g₀) (l := [])
    h1B hnB htail hfit hIdx hdi (by simp)
    (fun _ _ _ _ _ _ => evalB_lit (by omega))
  simpa [streamBlockClearCom, streamBlockClearCost, streamBlockMapCost,
    BlockLeaves.BlockFrozen, Expr.size] using h

theorem streamBlockAndCom_supported_spec
    {B n na tail : ℕ} {idx a b dst : String} {Idx A C g₀ : ℕ → ℕ}
    (h1B : 1 < B) (hnB : n < B) (htail : tail ≤ n) (hfit : tail ≤ na)
    (hIdx : ∀ q, q < tail → Idx q < n)
    (hAB : ∀ v, v < n → A v < B) (hCB : ∀ v, v < n → C v < B)
    (hACB : ∀ q, q < tail → A (Idx q) * C (Idx q) < B)
    (hdi : dst ≠ idx) (hda : dst ≠ a) (hdb : dst ≠ b) :
    Spec B
      (fun σ => σ.vars "tail" = tail ∧ σ.arrs idx = arrOf na Idx ∧
        σ.arrs dst = arrOf n g₀ ∧
        (σ.arrs a = arrOf n A ∧ σ.arrs b = arrOf n C) ∧
        BlockSupported n 0 tail Idx (fun v => A v * C v) ∧
        BlockSupported n 0 tail Idx g₀)
      (streamBlockAndCom idx a b dst)
      (fun _ σ' =>
        (∃ g, σ'.arrs dst = arrOf n g ∧
          (∀ v, v < n → g v = A v * C v) ∧ BlockSupported n 0 tail Idx g) ∧
        σ'.vars "tail" = tail ∧ σ'.arrs idx = arrOf na Idx ∧
        σ'.arrs a = arrOf n A ∧ σ'.arrs b = arrOf n C)
      (streamBlockAndCost tail) := by
  have h := streamBlockMapCom_supported_spec (B := B) (n := n) (na := na)
    (tail := tail) (idx := idx) (dst := dst)
    (x := .mul (.get a (.var "cw")) (.get b (.var "cw")))
    (Idx := Idx) (F := fun v => A v * C v) (g₀ := g₀)
    (l := [(a, n, A), (b, n, C)]) h1B hnB htail hfit hIdx hdi
    (by
      rintro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact Ne.symm hda
      · exact Ne.symm hdb)
    (by
      intro σ q hq _ hcw hI
      obtain ⟨-, -, -, -, hfr, -⟩ := hI
      have ha := hfr (a, n, A) (by simp)
      have hb := hfr (b, n, C) (by simp)
      have hqN := hIdx q hq
      have ecw : (Expr.var "cw").evalB B σ = some (Idx q) := by
        have he := evalB_var (B := B) (x := "cw") (σ := σ) (by
          rw [hcw]
          exact lt_trans hqN hnB)
        rwa [hcw] at he
      exact evalB_bin
        (evalB_get ecw (by rw [ha, getElem?_arrOf A hqN]) (hAB _ hqN))
        (evalB_get ecw (by rw [hb, getElem?_arrOf C hqN]) (hCB _ hqN))
        (hACB q hq))
  simpa [streamBlockAndCom, streamBlockAndCost, streamBlockMapCost,
    BlockLeaves.BlockFrozen, Expr.size] using h

theorem streamBlockSubCom_supported_spec
    {B n na tail : ℕ} {idx a b dst : String} {Idx A C g₀ : ℕ → ℕ}
    (h1B : 1 < B) (hnB : n < B) (htail : tail ≤ n) (hfit : tail ≤ na)
    (hIdx : ∀ q, q < tail → Idx q < n)
    (hAB : ∀ v, v < n → A v < B) (hCB : ∀ v, v < n → C v < B)
    (hACB : ∀ q, q < tail → A (Idx q) * (1 - C (Idx q)) < B)
    (hdi : dst ≠ idx) (hda : dst ≠ a) (hdb : dst ≠ b) :
    Spec B
      (fun σ => σ.vars "tail" = tail ∧ σ.arrs idx = arrOf na Idx ∧
        σ.arrs dst = arrOf n g₀ ∧
        (σ.arrs a = arrOf n A ∧ σ.arrs b = arrOf n C) ∧
        BlockSupported n 0 tail Idx (fun v => A v * (1 - C v)) ∧
        BlockSupported n 0 tail Idx g₀)
      (streamBlockSubCom idx a b dst)
      (fun _ σ' =>
        (∃ g, σ'.arrs dst = arrOf n g ∧
          (∀ v, v < n → g v = A v * (1 - C v)) ∧
          BlockSupported n 0 tail Idx g) ∧
        σ'.vars "tail" = tail ∧ σ'.arrs idx = arrOf na Idx ∧
        σ'.arrs a = arrOf n A ∧ σ'.arrs b = arrOf n C)
      (streamBlockSubCost tail) := by
  have h := streamBlockMapCom_supported_spec (B := B) (n := n) (na := na)
    (tail := tail) (idx := idx) (dst := dst)
    (x := .mul (.get a (.var "cw")) (.sub (.lit 1) (.get b (.var "cw"))))
    (Idx := Idx) (F := fun v => A v * (1 - C v)) (g₀ := g₀)
    (l := [(a, n, A), (b, n, C)]) h1B hnB htail hfit hIdx hdi
    (by
      rintro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact Ne.symm hda
      · exact Ne.symm hdb)
    (by
      intro σ q hq _ hcw hI
      obtain ⟨-, -, -, -, hfr, -⟩ := hI
      have ha := hfr (a, n, A) (by simp)
      have hb := hfr (b, n, C) (by simp)
      have hqN := hIdx q hq
      have ecw : (Expr.var "cw").evalB B σ = some (Idx q) := by
        have he := evalB_var (B := B) (x := "cw") (σ := σ) (by
          rw [hcw]
          exact lt_trans hqN hnB)
        rwa [hcw] at he
      exact evalB_bin
        (evalB_get ecw (by rw [ha, getElem?_arrOf A hqN]) (hAB _ hqN))
        (evalB_bin (evalB_lit h1B)
          (evalB_get ecw (by rw [hb, getElem?_arrOf C hqN]) (hCB _ hqN))
          (by change 1 - C (Idx q) < B; omega))
        (hACB q hq))
  simpa [streamBlockSubCom, streamBlockSubCost, streamBlockMapCost,
    BlockLeaves.BlockFrozen, Expr.size] using h

/-! ## The loaded row supplies the support premise -/

/-- The exact cluster indicator produced by the stream load vanishes off the
executed prefix.  This is the support fact consumed by all sparse masks. -/
theorem StreamLoadOut.cluster_supported
    {B n ns nt na q cap j c tail bits : ℕ}
    {G : SimpleGraph (Fin n)} {A₀ O T centre Xmem asg M Xa Mm : ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} {σ : Env}
    (h : StreamLoadOut B ns nt na q cap j c tail bits G A₀ π centre O T
      Xmem asg M Xa Mm σ) :
    BlockSupported n 0 tail Xmem Xa := by
  intro v hv hout
  by_contra hXa
  have hvX : (⟨v, hv⟩ : Fin n) ∈ markSet n Xa := hXa
  rw [h.cluster_set] at hvX
  obtain ⟨p, hp, hpv⟩ := (h.sorted.row.block v).mpr hvX
  exact hout p (by omega) hp hpv

/-- A product is supported when its right factor is supported.  The landed
descent helper records the symmetric left-factor form; the streamed retained
mask is `M * Xa`, so its cluster indicator is the right factor. -/
theorem blockSupported_mul_right
    {n p₀ e : ℕ} {Idx A C : ℕ → ℕ}
    (hC : BlockSupported n p₀ e Idx C) :
    BlockSupported n p₀ e Idx (fun v => A v * C v) := by
  intro v hv hout
  change A v * C v = 0
  rw [hC v hv hout, Nat.mul_zero]

/-! ## First concrete descent mask -/

/-- Restrict the parent work mask to the streamed cluster. -/
def streamRetainCom (j : ℕ) : Com :=
  streamBlockAndCom "xmem" "alv" (cluName j) (resName j)

structure StreamRetainOut {n : ℕ} (B ns nt na q cap j c tail bits : ℕ)
    (G : SimpleGraph (Fin n)) (A₀ : ℕ → ℕ) (π : Equiv.Perm (Fin n))
    (centre O T Xmem asg M Xa Mm Ra : ℕ → ℕ) (σ : Env) : Prop where
  loaded : StreamLoadOut B ns nt na q cap j c tail bits G A₀ π centre O T
    Xmem asg M Xa Mm σ
  retained_arr : σ.arrs (resName j) = arrOf n Ra
  retained_val : ∀ v, v < n → Ra v = M v * Xa v
  retained_bound : ∀ v, v < n → Ra v < B
  retained_supported : BlockSupported n 0 tail Xmem Ra

/-- The first old carrier pass of `descendCom` is now an exact streamed-row
map.  It preserves the loaded row interface and charges only `18·tail + 8`. -/
theorem streamRetainStep
    {B n ns nt na q cap j c tail bits : ℕ}
    {G : SimpleGraph (Fin n)} {A₀ O T centre Xmem asg M Xa Mm : ℕ → ℕ}
    {π : Equiv.Perm (Fin n)} (hB : 1 < B) (hnB : n < B) :
    Spec B
      (fun σ =>
        StreamLoadOut B ns nt na q cap j c tail bits G A₀ π centre O T
          Xmem asg M Xa Mm σ ∧
        σ.arrs (resName j) = arrOf n (fun _ => 0))
      (streamRetainCom j)
      (fun _ σ' => ∃ Ra,
        StreamRetainOut B ns nt na q cap j c tail bits G A₀ π centre O T
          Xmem asg M Xa Mm Ra σ')
      (streamBlockAndCost tail) := by
  refine Spec.of_exists fun σ hσ => ?_
  obtain ⟨hload, hres₀⟩ := hσ
  have htail := hload.sorted.row.tail_le
  have hfit : tail ≤ na := htail.trans hload.sorted.row_fit
  have hXaB : ∀ v, v < n → Xa v < B := by
    intro v hv
    exact lt_of_le_of_lt (hload.cluster_bit v hv) hB
  have hprodB : ∀ p, p < tail → M (Xmem p) * Xa (Xmem p) < B := by
    intro p hp
    have hpN := hload.sorted.row.mem_lt p hp
    calc
      M (Xmem p) * Xa (Xmem p) ≤ M (Xmem p) * 1 :=
        Nat.mul_le_mul_left _ (hload.cluster_bit _ hpN)
      _ = M (Xmem p) := by ring
      _ < B := hload.sorted.mask_bound _ hpN
  have hresSup : BlockSupported n 0 tail Xmem (fun v => M v * Xa v) :=
    blockSupported_mul_right
      (Lax3Proofs.Refine.CoverActiveStreamMask.StreamLoadOut.cluster_supported hload)
  obtain ⟨σ', hr, ⟨⟨Ra, hRa, hRaval, hRasup⟩, htail', hrow', halv', hclu'⟩,
      hfv, hfa, -, -⟩ :=
    ((streamBlockAndCom_supported_spec (B := B) (n := n) (na := na)
      (tail := tail) (idx := "xmem") (a := "alv") (b := cluName j)
      (dst := resName j) (Idx := Xmem) (A := M) (C := Xa)
      (g₀ := fun _ => 0) hB hnB htail hfit hload.sorted.row.mem_lt
      hload.sorted.mask_bound hXaB hprodB
      (by simp [resName, String.ext_iff])
      (by simp [resName, String.ext_iff])
      (by simp [cluName, resName, String.ext_iff])).frame).run
      ⟨hload.sorted.tail_var, hload.sorted.row_arr, hres₀,
        ⟨hload.sorted.mask_arr, hload.cluster_arr⟩, hresSup,
        blockSupported_zero n 0 tail Xmem⟩
  have hav : ∀ a : String, a ≠ resName j → σ'.arrs a = σ.arrs a := by
    intro a ha
    apply hfa a
    simp [streamBlockAndCom, streamBlockMapCom,
      BlockLeaves.blockMapRangeCom, Com.warrs, ha]
  have hvv : ∀ y : String, y ≠ "p" → y ≠ "pend" → y ≠ "cw" →
      σ'.vars y = σ.vars y := by
    intro y hp hpend hcw
    apply hfv y
    simp [streamBlockAndCom, streamBlockMapCom,
      BlockLeaves.blockMapRangeCom, Com.wvars, hp, hpend, hcw]
  have hsorted' :
      Lax3Proofs.Refine.CoverActiveStreamSort.StreamSortedOut
        B ns nt na q cap c tail bits G A₀ π centre O T Xmem asg M σ' := by
    refine ⟨hload.sorted.row,
      (hvv "n" (by decide) (by decide) (by decide)).trans hload.sorted.n_var,
      (hvv "qn" (by decide) (by decide) (by decide)).trans hload.sorted.q_var,
      (hvv "c" (by decide) (by decide) (by decide)).trans hload.sorted.centre_var,
      (hvv "xp" (by decide) (by decide) (by decide)).trans hload.sorted.pointer_var,
      htail',
      (hvv "rsbits" (by decide) (by decide) (by decide)).trans hload.sorted.bits_var,
      (hav "ord" (by simp [resName, String.ext_iff])).trans hload.sorted.centre_arr,
      (hav "off" (by simp [resName, String.ext_iff])).trans hload.sorted.off_arr,
      (hav "tgt" (by simp [resName, String.ext_iff])).trans hload.sorted.target_arr,
      halv', hrow', hload.sorted.row_fit,
      (hav "asg" (by simp [resName, String.ext_iff])).trans hload.sorted.asg_arr,
      ?_, ?_, ?_, hload.sorted.mask_bound⟩
    · apply Lax3Proofs.Refine.CoverActiveTurn.distClean_of_arrs_eq
        hload.sorted.dist_clean
      exact hav "dist" (by simp [resName, String.ext_iff])
    · obtain ⟨Q, hQ⟩ := hload.sorted.queue_arr
      exact ⟨Q, (hav "q" (by simp [resName, String.ext_iff])).trans hQ⟩
    · obtain ⟨QD, hQD⟩ := hload.sorted.qdist_arr
      exact ⟨QD, (hav "qd" (by simp [resName, String.ext_iff])).trans hQD⟩
  have hload' :
      StreamLoadOut B ns nt na q cap j c tail bits G A₀ π centre O T
        Xmem asg M Xa Mm σ' := by
    refine ⟨hsorted', hclu', hload.cluster_bit, hload.cluster_set,
      (hav (memName (j + 1)) (by
        simp [memName, resName, String.ext_iff])).trans hload.member_arr,
      (hvv "bq" (by decide) (by decide) (by decide)).trans hload.member_count,
      hload.member_enum⟩
  have hRaB : ∀ v, v < n → Ra v < B := by
    intro v hv
    rw [hRaval v hv]
    calc
      M v * Xa v ≤ M v * 1 := Nat.mul_le_mul_left _ (hload.cluster_bit v hv)
      _ = M v := by ring
      _ < B := hload.sorted.mask_bound v hv
  exact ⟨σ', _, hr, le_rfl, Ra, hload', hRa, hRaval, hRaB, hRasup⟩

theorem noWrite_streamBlockMapCom (idx dst : String) (x : Expr) :
    (streamBlockMapCom idx dst x).NoWrite := by
  simp [streamBlockMapCom, BlockLeaves.blockMapRangeCom, Com.NoWrite]

#print axioms streamBlockMapCom_spec
#print axioms streamBlockAndCom_supported_spec
#print axioms streamBlockSubCom_supported_spec
#print axioms StreamLoadOut.cluster_supported
#print axioms streamRetainStep

end Lax3Proofs.Refine.CoverActiveStreamMask
