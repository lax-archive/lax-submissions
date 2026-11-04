import Lax185574Proofs.ResolveRam.Glue.PCT3

/-!
The run of the tape program of the color table (`ctIn_run`): from the
input of the composite it writes the word of `ctW G P Q` with its
length in front. The tables come from the distance matrix: the least
code over a class `Y` of the codes of the distances to the class `X` is
the code of `distCls G X Y`, which is `cTab G X Y` (`clsVal_eq`).
-/

namespace Lax185574Proofs.ResolveRam.Glue

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Reasoning.Lib
open Lax808846Proofs.Reasoning.Lib.Csr Lax185574Proofs.Words Lax185574Proofs.Conversions.Ram
open Lax185574Proofs.StpRam Lax185574.PartialGraphs Lax185574.WordEncoding Lax185574Proofs.ResolveRam
open Lax185574Proofs.TreeAlgo Lax185574.PartialGraphEncoding
open Lax185574.DistanceMatrix Lax185574Proofs.DistMatrix

/-- **The color table as a tape program.** -/
def ctIn : Com := .seq ctRdIn (.seq clsCmd (.seq ctTab (.seq rounds outL)))

variable {n : ℕ}

theorem colsL_facts (G : PartialGraph (Fin n)) :
    (colsL G).Pairwise (· < ·) ∧ (∀ y, y ∈ colsL G ↔ ∃ w < n, colN G w = y) ∧ (colsL G).length ≤ n := by
  refine ⟨List.sortedLT_iff_pairwise.1 (Finset.sortedLT_sort _), fun y => ?_, ?_⟩
  · simp only [colsL, Finset.mem_sort, colsCore, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, rfl⟩; exact ⟨w.val, w.isLt, by simp [colN]⟩
    · rintro ⟨w, hw, rfl⟩; exact ⟨⟨w, hw⟩, by simp [colN, hw]⟩
  · simp only [colsL, Finset.length_sort, colsCore]
    exact (Finset.card_image_le).trans (by simp)

/-- The first vertex of a color is the label of every vertex of it. -/
theorem fstV_iff {col : ℕ → ℕ} {Y : ℕ} (hY : ∃ w < n, col w = Y) :
    ∀ y < n, leastBelow (fun u => col u = col y) n n = fstV col n Y ↔ col y = Y := by
  intro y hy
  constructor
  · intro h
    obtain ⟨-, h2, -⟩ := leastBelow_spec (d := n) (p := fun u => col u = col y) ⟨y, hy, rfl⟩
    obtain ⟨w, hw, hwY⟩ := hY
    obtain ⟨-, h4, -⟩ := leastBelow_spec (d := n) (p := fun u => col u = Y) ⟨w, hw, hwY⟩
    simp only [fstV] at h
    rw [h] at h2
    rw [← h2]; exact h4
  · intro h; simp only [fstV, h]

theorem fstV_lt {col : ℕ → ℕ} {Y : ℕ} (hY : ∃ w < n, col w = Y) : fstV col n Y < n := by
  obtain ⟨w, hw, hwY⟩ := hY
  exact (leastBelow_spec (d := n) (p := fun u => col u = Y) ⟨w, hw, hwY⟩).1

/-! ### The tables from the distance matrix -/

/-- The codes of the entries of the distance matrix of `G`, as a function
on numbers. -/
noncomputable def dF (G : PartialGraph (Fin n)) (u x : ℕ) : ℕ :=
  if h : u < n ∧ x < n then dcode (distMatrix G ⟨u, h.1⟩ ⟨x, h.2⟩) else 0

theorem getElem?_dF (G : PartialGraph (Fin n)) {u x : ℕ} (hu : u < n) (hx : x < n) :
    (toWord (distMatrix G))[2 + u * (n + 1) + x]? = some (dF G u x) := by
  have := getElem?_toWord_distMatrix G ⟨u, hu⟩ ⟨x, hx⟩
  simpa [dF, hu, hx] using this

theorem dF_le (G : PartialGraph (Fin n)) (u x : ℕ) : dF G u x ≤ n := by
  unfold dF; split_ifs
  · exact dcode_distMatrix_le G _ _
  · exact Nat.zero_le _

/-- The program value of the distance to a class is the code of
`distTo`. -/
theorem dtVal_eq (G : PartialGraph (Fin n)) (X : ℕ) {u : ℕ} (hu : u < n) :
    dtVal (colN G) (dF G) n X u = dcode (distTo G ⟨u, hu⟩ X) := by
  unfold dtVal distTo
  rw [dcode_inf]
  refine cmPre_congr fun x hx => ?_
  simp [colN, dF, hx, hu]

/-- **The tables from the distance matrix are the tables of `G`.** -/
theorem clsVal_eq (G : PartialGraph (Fin n)) (X : ℕ) {Y : ℕ} (hY : ∃ w < n, colN G w = Y) :
    clsVal (fun v => leastBelow (fun u => colN G u = colN G v) n n) (dtVal (colN G) (dF G) n X) n
      (fstV (colN G) n Y) = cTab G X Y := by
  have hc : cTab G X Y = dcode (distCls G X Y) := by
    unfold cTab; exact find_eq_dcode_distCls G X Y
  rw [hc]
  unfold clsVal distCls
  rw [dcode_inf]
  refine cmPre_congr fun y hy => ?_
  have h1 := fstV_iff hY y hy
  have h2 : colN G y = G.color ⟨y, hy⟩ := by simp [colN, hy]
  rw [dif_pos hy]
  by_cases hyY : G.color ⟨y, hy⟩ = Y
  · rw [if_pos (h1.2 (h2.trans hyY)), if_pos hyY, dtVal_eq G X hy]
  · rw [if_neg (fun h => hyY (h2.symm.trans (h1.1 h))), if_neg hyY]

/-- The parts of the input. -/
theorem xIn_len {G : PartialGraph (Fin n)} {k₀ q₀ P Q : ℕ} {s : Bool} :
    n + 1 + StpRam.offL G.edge n + StpRam.offL G.nonEdge n + (1 + n * (n + 1)) + 2 ≤
      (xIn G k₀ q₀ P Q s).length := by
  rw [toWord_xIn, toWord_ofFn_append]
  have h1 := offL_le_word G.edge
  have h2 := offL_le_word G.nonEdge
  have h3 := length_toWord_distMatrix G
  simp only [List.length_append, List.length_cons, List.length_ofFn]
  omega

theorem xIn_mem {G : PartialGraph (Fin n)} {k₀ q₀ P Q : ℕ} {s : Bool} :
    (∀ v < n, colN G v ∈ xIn G k₀ q₀ P Q s) ∧ P ∈ xIn G k₀ q₀ P Q s ∧ Q ∈ xIn G k₀ q₀ P Q s := by
  rw [toWord_xIn, toWord_ofFn_append]
  refine ⟨fun v hv => ?_, by simp, by simp⟩
  have : colN G v ∈ List.ofFn G.color := by
    rw [List.mem_ofFn]; exact ⟨⟨v, hv⟩, by simp [colN, hv]⟩
  simp [this]

/-- **The run of the color table program.** -/
theorem ctIn_run {B k₀ q₀ P Q : ℕ} {s : Bool} (G : PartialGraph (Fin n)) {σ : Env}
    (hinp : σ.inp = xIn G k₀ q₀ P Q s) (hco : (σ.arrs "co").length = n)
    (heo : (σ.arrs "eo").length = n + 1) (het : (σ.arrs "et").length = StpRam.offL G.edge n)
    (hno : (σ.arrs "no").length = n + 1) (hnt : (σ.arrs "nt").length = StpRam.offL G.nonEdge n)
    (hdd : (σ.arrs "dd").length = 1 + n * (n + 1))
    (hcl : (σ.arrs "cl").length = n) (hdm : (σ.arrs "dm").length = n)
    (hct : (σ.arrs "ct").length = n) (hc1 : (σ.arrs "c1").length = n) (hsy : (σ.arrs "sy").length = n)
    (hsu : (σ.arrs "su").length = n) (hB : 3 * ySz (xIn G k₀ q₀ P Q s) + 3 < B) :
    ∃ σ', Run B ctIn σ σ' (1000 * ((xIn G k₀ q₀ P Q s).length + 1)) ∧
      σ'.out = σ.out ++ ((ctW G P Q).length :: ctW G P Q) := by
  have hinp' : σ.inp = toWord G ++ toWord (distMatrix G) ++ [P, Q] ++
      ([if s then 1 else 0] ++ toWord (family G k₀ q₀)) := by
    rw [hinp, toWord_xIn]; simp
  obtain ⟨hmc, hmP, hmQ⟩ := xIn_mem (G := G) (k₀ := k₀) (q₀ := q₀) (P := P) (Q := Q) (s := s)
  have hlen : n + 1 + StpRam.offL G.edge n + StpRam.offL G.nonEdge n + (1 + n * (n + 1)) + 2 ≤
      (xIn G k₀ q₀ P Q s).length := xIn_len
  set x := xIn G k₀ q₀ P Q s with hx
  have hyS : x.length + maxEntry x + 1 = ySz x := rfl
  have hcB : ∀ v < n, colN G v + 1 < B := fun v hv => by
    have := le_maxEntry (hmc v hv); omega
  have hPB : P < B := by have := le_maxEntry hmP; omega
  have hQB : Q < B := by have := le_maxEntry hmQ; omega
  have hn1B : n + 1 < B := by omega
  have hEB : StpRam.offL G.edge n + 1 < B := by omega
  have hNB : StpRam.offL G.nonEdge n + 1 < B := by omega
  have hDB : 1 + n * (n + 1) < B := by omega
  have h3B : 3 * n + 3 < B := by omega
  have hcB' : ∀ v < n, colN G v < B := fun v hv => by have := hcB v hv; omega
  clear hyS hmc hmP hmQ
  -- reading
  obtain ⟨σ1, r1, hn1, hco1, hdd1, hP1, hQ1, -, ho1, ha1⟩ := ctRdIn_run (B := B) G hinp' hco heo het hno
    hnt hdd hn1B hEB hNB hDB hcB'
  -- the classes
  obtain ⟨σ2, r2, hcl2, hn2, ha2, hv2, ho2, -⟩ := clsCmd_run (B := B) (col := colN G) hn1 hco1
    (by rw [ha1 "cl" (by decide), hcl]) hn1B hcB'
  set clf := fun v => leastBelow (fun u => colN G u = colN G v) n n
  have hclc : ∀ v < n, clf v < n := fun v hv =>
    (leastBelow_spec (d := n) (p := fun u => colN G u = colN G v) ⟨v, hv, rfl⟩).1
  -- the tables
  obtain ⟨σ3, r3, hc13, hct3, hco3, hn3, ha3, -⟩ := ctTab_run (B := B) (P := P) (Q := Q) (f := dF G)
    (D := toWord (distMatrix G)) hn2
    (by rw [ha2 "co" (by decide), hco1]) hcl2 (by rw [ha2 "dd" (by decide), hdd1])
    (fun u hu x hx => getElem?_dF G hu hx)
    (by rw [hv2 "gp" (by decide), hP1]) (by rw [hv2 "gq" (by decide), hQ1])
    (by rw [ha2 "dm" (by decide), ha1 "dm" (by decide), hdm])
    (by rw [ha2 "ct" (by decide), ha1 "ct" (by decide), hct])
    (by rw [ha2 "c1" (by decide), ha1 "c1" (by decide), hc1]) hclc
    (fun u _ x _ => by have := dF_le G u x; omega) hcB' hPB hQB
    (by rw [length_toWord_distMatrix]; omega) hn1B
  -- the rounds
  obtain ⟨hLp, hLm, hLn⟩ := colsL_facts G
  obtain ⟨σ4, r4, hR4, hv4, hco4⟩ := rounds_run (B := B) (L := colsL G) (col := colN G) hLp hLm hLn hn3
    (by rw [hco3, ha2 "co" (by decide), hco1]) hcB hn1B
    (by rw [ha3 "sy" (by decide), ha2 "sy" (by decide), ha1 "sy" (by decide), hsy])
    (by rw [ha3 "su" (by decide), ha2 "su" (by decide), ha1 "su" (by decide), hsu])
  obtain ⟨hlo4, hcnt4, -, -, hj4⟩ := hR4
  have hmin : min n (colsL G).length = (colsL G).length := Nat.min_eq_right hLn
  have hfr4 : ∀ a, a ∉ rounds.warrs → σ4.arrs a = σ3.arrs a := fun a ha => r4.frame_arr a ha
  -- the output
  obtain ⟨σ5, r5, ho5⟩ := outL_run (B := B) (n := n) (L := colsL G)
    (g₁ := clsVal clf (dtVal (colN G) (dF G) n P) n) (g₂ := clsVal clf (dtVal (colN G) (dF G) n Q) n)
    (h := fstV (colN G) n) (f₁ := cTab G P) (f₂ := cTab G Q) (σ := σ4) (by rw [hcnt4, hmin])
    (fun j hj => (hj4 j (by rw [hmin]; exact hj)).1) (fun j hj => (hj4 j (by rw [hmin]; exact hj)).2)
    (by rw [hfr4 "c1" (by decide), hc13]) (by rw [hfr4 "ct" (by decide), hct3])
    (fun y hy => fstV_lt ((hLm y).1 hy))
    (fun y hy => clsVal_eq G P ((hLm y).1 hy))
    (fun y hy => clsVal_eq G Q ((hLm y).1 hy))
    (fun y hy => by
      obtain ⟨w, hw, rfl⟩ := (hLm y).1 hy
      exact ⟨Nat.lt_of_succ_lt (hcB w hw), lt_of_le_of_lt (cTab_le G P _) (Nat.lt_of_succ_lt hn1B),
        lt_of_le_of_lt (cTab_le G Q _) (Nat.lt_of_succ_lt hn1B)⟩) (Nat.lt_of_succ_lt hn1B)
    (Nat.lt_of_le_of_lt (Nat.add_le_add_right (Nat.mul_le_mul_left 3 hLn) 3) h3B)
  refine ⟨σ5, ?_, ?_⟩
  · unfold ctIn
    refine (Run.seq r1 (Run.seq r2 (Run.seq r3 (Run.seq r4 r5)))).mono ?_
    have hL : (colsL G).length ≤ n := hLn
    generalize StpRam.offL G.edge n = a at hlen
    generalize StpRam.offL G.nonEdge n = b at hlen
    generalize x.length = X at hlen
    generalize (colsL G).length = l at hL
    have h0 : n * n ≤ n * (n + 1) := Nat.mul_le_mul_left n (Nat.le_succ n)
    have h1 : n * n ≤ X := by omega
    have hn : n ≤ X := by omega
    have hl : l ≤ X := by omega
    clear * - h1 hn hl hL
    refine le_trans (le_of_eq (show _ = 295 * (n * n) + 291 * n + 30 * l + 181 by ring)) ?_
    omega
  · rw [ho5, show σ4.out = σ.out from ?_]
    · rfl
    · rw [r4.out_eq (by decide), r3.out_eq (by decide), ho2, ho1]

end Lax185574Proofs.ResolveRam.Glue
