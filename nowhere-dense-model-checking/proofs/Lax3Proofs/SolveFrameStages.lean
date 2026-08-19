import Lax3Proofs.SolveChain

/-!
# F6c7 (part 1) — the remaining per-centre stages, lifted to the windowed contract

`SolveChainBot` (self-owned scratch, one arena) and
`SolveChainRestrict` (fresh regions at data-dependent sizes, two
arenas) are the two worked `specWindow` templates; this file lifts the
remaining pipeline stages the same way, so that the frame-step
discharger consumes every stage at the one contract the chain speaks
(`ArenaStW` in, `ArenaStW` + the stage's output out, the landed budget
unchanged):

* **`bfsCom_specW`** — the shared bounded BFS (`SolveBfs`): the arena's
  CSR read through its windows, the distance scratch `da` windowed at
  the carrier; the arena regions are untouched (`warrs_bfsCom`), so the
  windowed contract survives by frame alone, and the deliverable is the
  `BallTable` read off the allocation's prefix.
* **`supportsCom_specW`** — the supports pass (`SolveBlocksSupports`):
  same reading discipline, but the stage *writes the arena's own
  channel region* (round `e`'s column); the postcondition is the
  windowed contract at the channel-updated arena
  (`MArena` with `hist` overwritten at `e` by `descendCol`), which is
  exactly the shape D6's recorded-walk update takes. The radius is a
  free parameter `d` — the frame-step discharger instantiates `2R`
  (the design §5 line 17 figure), never `S.R`.
* **`scatterCom_specW`** — the per-atom guarded greedy scatter
  (`SolveBlocksScatter`): the batch bit region enters through the
  windowed `FinBitsW`; the count lands in the `gs.c` cell; the arena is
  untouched. The `t = 0` guard is inside the landed spec (a cost
  clause, not dead code).
* **`isolateCom_specW`** — the batch isolation (`SolveBlocksRestrict`
  §isolate): the two-family case (the child's regions, and the isolated
  CSR built fresh at the deleted-edge dimensions), `restrictCom_specW`'s
  pattern. `deleteVerts` isolates, never removes: the carrier is kept,
  and the postcondition holds the windowed contract at **both** the
  input arena (at the input names) and `Bar.isolate W` (at the output
  names).

Every budget is the landed one; no landed proof is re-entered.
-/

namespace Lax3Proofs.Prog

open Lax13Proofs.Imp Lax13Proofs.Reasoning Lax13Proofs.Reasoning.Lib

/-! ## §0 Transports the lifts share -/

/-- The truncation of an array depends only on that array: agreement
transports pointwise through `winA`. -/
theorem arrs_winA_eq_of_arrs_eq {ws : String → Option ℕ} {σ σ' : Env}
    {b : String} (h : σ'.arrs b = σ.arrs b) :
    (winA ws σ').arrs b = (winA ws σ).arrs b := by
  show (match ws b with | some m => (σ'.arrs b).take m | none => σ'.arrs b)
    = (match ws b with | some m => (σ.arrs b).take m | none => σ.arrs b)
  cases ws b <;> simp [h]

/-- `GraphCsr` reads two arrays; it transports along agreement. -/
theorem graphCsr_of_eq {o t : String} {N : ℕ} {G : SimpleGraph (Fin N)}
    {ns : ℕ} {σ σ' : Env} (h : GraphCsr o t G ns σ)
    (ho : σ'.arrs o = σ.arrs o) (ht : σ'.arrs t = σ.arrs t) :
    GraphCsr o t G ns σ' := by
  obtain ⟨off, tgt, hc, h0, hnd, hadj⟩ := h
  exact ⟨off, tgt, hc.of_eq ho ht, h0, hnd, hadj⟩

/-- **The windowed contract transports along agreement on its five
arrays and two cells** — the fact that lets a stage which never writes
the arena's regions carry `ArenaStW` across itself by `Run`'s frame
data alone. -/
theorem arenaStW_of_eq {nm : ArenaNames} {Λ n₀ ℓp hb : ℕ}
    {A : Impl.MArena Λ n₀ ℓp} {σ σ' : Env} (h : ArenaStW nm hb A σ)
    (hn : σ'.vars nm.nN = σ.vars nm.nN) (hs : σ'.vars nm.nS = σ.vars nm.nS)
    (ho : σ'.arrs nm.off = σ.arrs nm.off) (ht : σ'.arrs nm.tgt = σ.arrs nm.tgt)
    (hc : σ'.arrs nm.col = σ.arrs nm.col) (hu : σ'.arrs nm.up = σ.arrs nm.up)
    (hh : σ'.arrs nm.hist = σ.arrs nm.hist) : ArenaStW nm hb A σ' := by
  constructor
  · show FitsW (arenaWs nm Λ ℓp hb A.N (σ'.vars nm.nS)) σ'
    rw [hs]
    intro b m hbm
    rcases arenaWs_some_elim hbm with rfl | rfl | rfl | rfl | rfl
    · rw [ho]; exact h.fits _ m hbm
    · rw [ht]; exact h.fits _ m hbm
    · rw [hc]; exact h.fits _ m hbm
    · rw [hu]; exact h.fits _ m hbm
    · rw [hh]; exact h.fits _ m hbm
  · show ArenaSt nm hb A (winA (arenaWs nm Λ ℓp hb A.N (σ'.vars nm.nS)) σ')
    rw [hs]
    refine arenaSt_of_eq h.st hn hs ?_ ?_ ?_ ?_ ?_
    · exact arrs_winA_eq_of_arrs_eq ho
    · exact arrs_winA_eq_of_arrs_eq ht
    · exact arrs_winA_eq_of_arrs_eq hc
    · exact arrs_winA_eq_of_arrs_eq hu
    · exact arrs_winA_eq_of_arrs_eq hh

open Classical in
/-- The windowed bit region: a valid prefix holding a set's indicator —
`FinBits` with the exact length relaxed, the form the chain's batch
region takes (allocated once at the level's maximum, holding each
batch in turn). -/
def FinBitsW (a : String) {n : ℕ} (X : Set (Fin n)) (σ : Env) : Prop :=
  n ≤ (σ.arrs a).length ∧
    ∀ v : Fin n, (σ.arrs a).getD (v : ℕ) 0 = (if v ∈ X then 1 else 0)

open Classical in
/-- Bridge (into a stage): the truncation of a windowed bit region at
the window of exactly its size satisfies the exact `FinBits`. -/
theorem finBits_win_of_W {ws : String → Option ℕ} {a : String} {n : ℕ}
    {X : Set (Fin n)} {σ : Env} (hws : ws a = some n) (h : FinBitsW a X σ) :
    FinBits a X (winA ws σ) := by
  refine ⟨length_arrs_winA hws h.1, fun v => ?_⟩
  rw [arrs_winA_some hws, getD_take_of_lt v.2]
  exact h.2 v

open Classical in
/-- Bridge (reading back): an exact `FinBits` of the truncation is a
windowed one of the allocation. -/
theorem finBitsW_of_win {ws : String → Option ℕ} {a : String} {n : ℕ}
    {X : Set (Fin n)} {σ : Env} (hws : ws a = some n) (hfit : FitsW ws σ)
    (h : FinBits a X (winA ws σ)) : FinBitsW a X σ := by
  refine ⟨hfit a n hws, fun v => ?_⟩
  have := h.2 v
  rwa [arrs_winA_some hws, getD_take_of_lt v.2] at this

/-! ## §1 The shared BFS, lifted -/

open Classical in
/-- **The bounded BFS at the windowed contract**: from the level's
windowed arena regions, the input cells (the glue copies the carrier
and slot-count cells into the stage's scratch cells) and a distance
allocation of at least the carrier, `bfsCom` leaves the windowed
contract intact — the arena regions are never written — and the
distance region's prefix holding the exact truncated distance table of
the source: every entry `≤ d + 1`, `BallTable` at the contents. Landed
budget `bfsK`, at the slot count the contract pins (`ns = Σ deg`). The
radius `d` is free — the supports pass instantiates `2R`. -/
theorem bfsCom_specW {B n₀ Λc ℓp hb d : ℕ} {A : Impl.MArena Λc n₀ ℓp}
    {nm : ArenaNames} {da : String} (s : Fin A.N)
    (hNB : A.N < B) (hNNB : A.N * A.N < B) (hdB : d + 2 < B)
    (hot : nm.tgt ≠ nm.off)
    (hda5 : da ∉ ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String))
    (hnN : nm.nN ∉ bfScalars) (hnS : nm.nS ∉ bfScalars) :
    Spec B
      (fun σ => ArenaStW nm hb A σ ∧
        σ.vars "bf.n" = A.N ∧ σ.vars "bf.m" = σ.vars nm.nS ∧
        σ.vars "bf.r" = d ∧ σ.vars "bf.v" = (s : ℕ) ∧
        A.N ≤ (σ.arrs da).length)
      (bfsCom nm.off nm.tgt da)
      (fun σ σ' => ArenaStW nm hb A σ' ∧
        σ'.vars nm.nS = σ.vars nm.nS ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ v : Fin A.N, (σ'.arrs da).getD (v : ℕ) 0 ≤ d + 1) ∧
        Lax3Proofs.Impl.BallTable A.G s d
          (fun v => (σ'.arrs da).getD (v : ℕ) 0))
      (bfsK A.N (∑ v : Fin A.N, A.G.degree v) d) := by
  -- the name disequalities, spelled out
  have hda5C := hda5
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hda5C
  obtain ⟨hda_o, hda_t, hda_c, hda_u, hda_h⟩ := hda5C
  intro σ hσ
  obtain ⟨hAW, hbn, hbm, hbr, hbv, hdaL⟩ := hσ
  -- the slot count, off the cell, and its identity and bound
  set ns := σ.vars nm.nS with hns_def
  have hnsum : ns = ∑ v : Fin A.N, A.G.degree v := hAW.st.csr.ns_eq_sum_degree
  have hnsB : ns < B := by
    have := hAW.ns_le_sq
    omega
  -- the window assignment: the CSR pair at the arena's dimensions, the
  -- distance scratch at the carrier
  set ws : String → Option ℕ := fun b =>
    if b = da then some A.N
    else if b = nm.off then some (A.N + 1)
    else if b = nm.tgt then some ns
    else none with hws_def
  have hws_da : ws da = some A.N := if_pos rfl
  have hws_off : ws nm.off = some (A.N + 1) := by
    show (if nm.off = da then _ else _) = _
    rw [if_neg (Ne.symm hda_o), if_pos rfl]
  have hws_tgt : ws nm.tgt = some ns := by
    show (if nm.tgt = da then _ else _) = _
    rw [if_neg (Ne.symm hda_t), if_neg hot, if_pos rfl]
  -- the arena's own window family, at the same values on the pair
  set aws := arenaWs nm Λc ℓp hb A.N ns with haws_def
  have haws_off : aws nm.off = some (A.N + 1) := arenaWs_off
  have haws_tgt : aws nm.tgt = some ns := arenaWs_tgt hot
  -- the allocation fits
  have hFits : FitsW ws σ := by
    intro b m hbm
    by_cases h0 : b = da
    · subst h0; rw [hws_da] at hbm; cases hbm; exact hdaL
    by_cases h1 : b = nm.off
    · subst h1
      rw [hws_off] at hbm
      cases hbm
      exact hAW.fits _ _ haws_off
    by_cases h2 : b = nm.tgt
    · subst h2
      rw [hws_tgt] at hbm
      cases hbm
      exact hAW.fits _ _ haws_tgt
    · exfalso
      have : ws b = none := by
        show (if b = da then _ else _) = _
        rw [if_neg h0, if_neg h1, if_neg h2]
      rw [this] at hbm
      cases hbm
  -- the truncation satisfies the landed precondition
  have hcsr : GraphCsr nm.off nm.tgt A.G ns (winA ws σ) :=
    graphCsr_of_eq hAW.st.csr
      (arrs_winA_congr (hws_off.trans haws_off.symm) σ)
      (arrs_winA_congr (hws_tgt.trans haws_tgt.symm) σ)
  -- run the landed seam spec on the truncation, pad back
  obtain ⟨σ', hrun, hfit', hQ, hlenEq, -⟩ :=
    (specWindow (bfsCom_spec_graphCsr (B := B) (G := A.G) (ns := ns)
      (oa := nm.off) (ta := nm.tgt) (da := da) s hNB hnsB hdB hda_o hda_t)
      ws) σ
      ⟨hFits, hcsr, hbn, hbm, hbr, hbv, length_arrs_winA hws_da hdaL⟩
  obtain ⟨-, -, hbd, hbt⟩ := hQ
  -- the arena regions and cells are untouched
  have hfa : ∀ b, b ∉ (bfsCom nm.off nm.tgt da).warrs → σ'.arrs b = σ.arrs b :=
    fun b hb => hrun.frame_arr b hb
  have hda_notin : ∀ b, b ≠ da → b ∉ (bfsCom nm.off nm.tgt da).warrs := by
    intro b hb
    rw [warrs_bfsCom]
    simp [hb]
  have hfv : ∀ y, y ∉ bfScalars → σ'.vars y = σ.vars y := fun y hy =>
    hrun.frame_var y fun hm => hy (wvars_bfsCom_subset nm.off nm.tgt da y hm)
  have hnS' : σ'.vars nm.nS = σ.vars nm.nS := hfv _ hnS
  refine ⟨σ', hrun.mono (le_of_eq (by rw [hnsum])), ?_, hnS', hlenEq, ?_, ?_⟩
  · exact arenaStW_of_eq hAW (hfv _ hnN) hnS'
      (hfa _ (hda_notin _ (Ne.symm hda_o)))
      (hfa _ (hda_notin _ (Ne.symm hda_t)))
      (hfa _ (hda_notin _ (Ne.symm hda_c)))
      (hfa _ (hda_notin _ (Ne.symm hda_u)))
      (hfa _ (hda_notin _ (Ne.symm hda_h)))
  · -- the bound, read off the allocation's prefix
    intro v
    have := hbd v
    rwa [arrs_winA_some hws_da, getD_take_of_lt v.2] at this
  · -- the table, read off the allocation's prefix
    have hfun : (fun v : Fin A.N => ((winA ws σ').arrs da).getD (v : ℕ) 0)
        = fun v : Fin A.N => (σ'.arrs da).getD (v : ℕ) 0 := by
      funext v
      rw [arrs_winA_some hws_da, getD_take_of_lt v.2]
    rwa [hfun] at hbt

/-! ## §2 The guarded greedy scatter, lifted -/

open Classical in
/-- **The per-atom scatter at the windowed contract**: from the level's
windowed arena regions, the four input cells, the batch's windowed bit
region and two scratch allocations of at least the carrier,
`scatterCom` leaves the windowed contract and the bit region intact —
the arena is never written — and the guarded greedy count in the
`gs.c` cell. Landed budget `scatterK` at the contract's slot count.
The `t = 0` guard is the landed spec's own (a cost clause, not dead
code). -/
theorem scatterCom_specW {B n₀ Λc ℓp hb r t : ℕ} {A : Impl.MArena Λc n₀ ℓp}
    {X : Set (Fin A.N)} {nm : ArenaNames} {pa ma da : String}
    (hNB : A.N < B) (hNNB : A.N * A.N < B) (hrB : r + 2 < B) (htB : t < B)
    (hot : nm.tgt ≠ nm.off)
    (hda5 : da ∉ ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String))
    (hma5 : ma ∉ ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String))
    (hpa5 : pa ∉ ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String))
    (hda_ma : da ≠ ma) (hda_pa : da ≠ pa) (hma_pa : ma ≠ pa)
    (hnN : nm.nN ∉ gsScalars) (hnS : nm.nS ∉ gsScalars) :
    Spec B
      (fun σ => ArenaStW nm hb A σ ∧
        σ.vars "gs.n" = A.N ∧ σ.vars "gs.m" = σ.vars nm.nS ∧
        σ.vars "gs.r" = r ∧ σ.vars "gs.t" = t ∧
        FinBitsW pa X σ ∧
        A.N ≤ (σ.arrs ma).length ∧ A.N ≤ (σ.arrs da).length)
      (scatterCom nm.off nm.tgt pa ma da)
      (fun σ σ' => ArenaStW nm hb A σ' ∧
        σ'.vars nm.nS = σ.vars nm.nS ∧
        σ'.vars "gs.c" = Lax3Proofs.Impl.greedyScatter A.G r X t ∧
        FinBitsW pa X σ' ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (scatterK A.N (∑ v : Fin A.N, A.G.degree v) r t) := by
  -- the name disequalities, spelled out
  have hda5C := hda5
  have hma5C := hma5
  have hpa5C := hpa5
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    at hda5C hma5C hpa5C
  obtain ⟨hda_o, hda_t, hda_c, hda_u, hda_h⟩ := hda5C
  obtain ⟨hma_o, hma_t, hma_c, hma_u, hma_h⟩ := hma5C
  obtain ⟨hpa_o, hpa_t, hpa_c, hpa_u, hpa_h⟩ := hpa5C
  intro σ hσ
  obtain ⟨hAW, hgn, hgm, hgr, hgt, hPa, hmaL, hdaL⟩ := hσ
  set ns := σ.vars nm.nS with hns_def
  have hnsum : ns = ∑ v : Fin A.N, A.G.degree v := hAW.st.csr.ns_eq_sum_degree
  have hnsB : ns < B := by
    have := hAW.ns_le_sq
    omega
  -- the window assignment
  set ws : String → Option ℕ := fun b =>
    if b = da then some A.N
    else if b = ma then some A.N
    else if b = pa then some A.N
    else if b = nm.off then some (A.N + 1)
    else if b = nm.tgt then some ns
    else none with hws_def
  have hws_da : ws da = some A.N := if_pos rfl
  have hws_ma : ws ma = some A.N := by
    show (if ma = da then _ else _) = _
    rw [if_neg (Ne.symm hda_ma), if_pos rfl]
  have hws_pa : ws pa = some A.N := by
    show (if pa = da then _ else _) = _
    rw [if_neg (Ne.symm hda_pa), if_neg (Ne.symm hma_pa), if_pos rfl]
  have hws_off : ws nm.off = some (A.N + 1) := by
    show (if nm.off = da then _ else _) = _
    rw [if_neg (Ne.symm hda_o), if_neg (Ne.symm hma_o), if_neg (Ne.symm hpa_o),
      if_pos rfl]
  have hws_tgt : ws nm.tgt = some ns := by
    show (if nm.tgt = da then _ else _) = _
    rw [if_neg (Ne.symm hda_t), if_neg (Ne.symm hma_t), if_neg (Ne.symm hpa_t),
      if_neg hot, if_pos rfl]
  set aws := arenaWs nm Λc ℓp hb A.N ns with haws_def
  have haws_off : aws nm.off = some (A.N + 1) := arenaWs_off
  have haws_tgt : aws nm.tgt = some ns := arenaWs_tgt hot
  -- the allocation fits
  have hFits : FitsW ws σ := by
    intro b m hbm
    by_cases h0 : b = da
    · subst h0; rw [hws_da] at hbm; cases hbm; exact hdaL
    by_cases h1 : b = ma
    · subst h1; rw [hws_ma] at hbm; cases hbm; exact hmaL
    by_cases h2 : b = pa
    · subst h2; rw [hws_pa] at hbm; cases hbm; exact hPa.1
    by_cases h3 : b = nm.off
    · subst h3; rw [hws_off] at hbm; cases hbm; exact hAW.fits _ _ haws_off
    by_cases h4 : b = nm.tgt
    · subst h4; rw [hws_tgt] at hbm; cases hbm; exact hAW.fits _ _ haws_tgt
    · exfalso
      have : ws b = none := by
        show (if b = da then _ else _) = _
        rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
      rw [this] at hbm
      cases hbm
  -- the truncation satisfies the landed precondition
  have hcsr : GraphCsr nm.off nm.tgt A.G ns (winA ws σ) :=
    graphCsr_of_eq hAW.st.csr
      (arrs_winA_congr (hws_off.trans haws_off.symm) σ)
      (arrs_winA_congr (hws_tgt.trans haws_tgt.symm) σ)
  -- run the landed seam spec on the truncation, pad back
  obtain ⟨σ', hrun, hfit', hQ, hlenEq, -⟩ :=
    (specWindow (scatterCom_spec_graphCsr (B := B) (G := A.G) (ns := ns)
      (r := r) (t := t) (X := X) (oa := nm.off) (ta := nm.tgt) (pa := pa)
      (ma := ma) (da := da) hNB hnsB hrB htB hda_o hda_t hda_ma hda_pa
      hma_o hma_t hma_pa) ws) σ
      ⟨hFits, hcsr, hgn, hgm, hgr, hgt, finBits_win_of_W hws_pa hPa,
        length_arrs_winA hws_ma hmaL, length_arrs_winA hws_da hdaL⟩
  obtain ⟨hcnt, -, hPa', -, -⟩ := hQ
  -- the arena regions and cells are untouched
  have hfa : ∀ b, b ∉ (scatterCom nm.off nm.tgt pa ma da).warrs →
      σ'.arrs b = σ.arrs b := fun b hb => hrun.frame_arr b hb
  have hmada_notin : ∀ b, b ≠ ma → b ≠ da →
      b ∉ (scatterCom nm.off nm.tgt pa ma da).warrs := by
    intro b hb1 hb2
    rw [warrs_scatterCom]
    simp [hb1, hb2]
  have hfv : ∀ y, y ∉ gsScalars → σ'.vars y = σ.vars y := fun y hy =>
    hrun.frame_var y fun hm =>
      hy (wvars_scatterCom_subset nm.off nm.tgt pa ma da y hm)
  have hnS' : σ'.vars nm.nS = σ.vars nm.nS := hfv _ hnS
  refine ⟨σ', hrun.mono (le_of_eq (by rw [hnsum])), ?_, hnS', hcnt, ?_, hlenEq⟩
  · exact arenaStW_of_eq hAW (hfv _ hnN) hnS'
      (hfa _ (hmada_notin _ (Ne.symm hma_o) (Ne.symm hda_o)))
      (hfa _ (hmada_notin _ (Ne.symm hma_t) (Ne.symm hda_t)))
      (hfa _ (hmada_notin _ (Ne.symm hma_c) (Ne.symm hda_c)))
      (hfa _ (hmada_notin _ (Ne.symm hma_u) (Ne.symm hda_u)))
      (hfa _ (hmada_notin _ (Ne.symm hma_h) (Ne.symm hda_h)))
  · exact finBitsW_of_win hws_pa hfit' hPa'

/-! ## §3 The supports pass, lifted -/

open Classical in
/-- **The supports pass at the windowed contract**: from the level's
windowed arena regions, the six input cells, a parent allocation of at
least the carrier (dirty is fine) and the distance region's prefix
holding the ball table `D` (the seam: verbatim `bfsCom_specW`'s
deliverable), `supportsCom` leaves the windowed contract **at the
channel-updated arena** — round `e`'s column of the arena's own `hist`
region now holds `descendCol`'s gradient walks, every other column as
inherited — with the distance prefix untouched and the least parents
in the parent prefix. Landed budget `supportsK` at the contract's slot
count. The radius `d` is free: the frame-step discharger instantiates
`2R` here (design §5 line 17), with `hdhb : d + 1 ≤ hb` the channel
bound's fit (`hb = 2R + 1`). -/
theorem supportsCom_specW {B n₀ Λc ℓp hb d : ℕ} {A : Impl.MArena Λc n₀ ℓp}
    {nm : ArenaNames} {pa da : String} {D : Fin A.N → ℕ} {s : Fin A.N}
    (e : Fin ℓp)
    (hD : Lax3Proofs.Impl.BallTable A.G s d D)
    (hDd : ∀ v : Fin A.N, D v ≤ d + 1) (hdhb : d + 1 ≤ hb)
    (hNB : A.N < B) (hNNB : A.N * A.N < B) (hdB : d + 2 < B)
    (hlB : ℓp < B) (hhB : hb + 1 < B) (hLB : A.N * ℓp * (hb + 1) < B)
    (hnd5 : ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String).Nodup)
    (hda5 : da ∉ ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String))
    (hpa5 : pa ∉ ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String))
    (hda_pa : da ≠ pa)
    (hnN : nm.nN ∉ spScalars) (hnS : nm.nS ∉ spScalars) :
    Spec B
      (fun σ => ArenaStW nm hb A σ ∧
        σ.vars "sp.n" = A.N ∧ σ.vars "sp.m" = σ.vars nm.nS ∧
        σ.vars "sp.r" = d ∧ σ.vars "sp.l" = ℓp ∧ σ.vars "sp.h" = hb ∧
        σ.vars "sp.p" = (e : ℕ) ∧
        A.N ≤ (σ.arrs pa).length ∧ A.N ≤ (σ.arrs da).length ∧
        (∀ v : Fin A.N, (σ.arrs da).getD (v : ℕ) 0 = D v))
      (supportsCom nm.off nm.tgt da pa nm.hist)
      (fun σ σ' => ArenaStW nm hb
          { A with hist := fun v p =>
              if p = e then descendCol A.G D d v else A.hist v p } σ' ∧
        σ'.vars nm.nS = σ.vars nm.nS ∧
        (∀ v : Fin A.N, (σ'.arrs da).getD (v : ℕ) 0 = D v) ∧
        (∀ v : Fin A.N, (σ'.arrs pa).getD (v : ℕ) 0 = leastParent A.G D v) ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (supportsK A.N (∑ v : Fin A.N, A.G.degree v) d) := by
  -- the name disequalities, spelled out
  have hnd5C := hnd5
  have hda5C := hda5
  have hpa5C := hpa5
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_or] at hnd5C
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hda5C hpa5C
  obtain ⟨⟨hot', hoc, hou, hoh⟩, ⟨htc, htu, hth⟩, ⟨hcu, hch⟩, huh, -⟩ := hnd5C
  obtain ⟨hda_o, hda_t, hda_c, hda_u, hda_h⟩ := hda5C
  obtain ⟨hpa_o, hpa_t, hpa_c, hpa_u, hpa_h⟩ := hpa5C
  have hot : nm.tgt ≠ nm.off := Ne.symm hot'
  intro σ hσ
  obtain ⟨hAW, hsn, hsm, hsr, hsl, hsh, hsp, hpaL, hdaL, hdaD⟩ := hσ
  set ns := σ.vars nm.nS with hns_def
  have hnsum : ns = ∑ v : Fin A.N, A.G.degree v := hAW.st.csr.ns_eq_sum_degree
  have hnsB : ns < B := by
    have := hAW.ns_le_sq
    omega
  -- the window assignment: the CSR pair, the channel at the arena's
  -- dimensions, the two scratch regions at the carrier
  set ws : String → Option ℕ := fun b =>
    if b = da then some A.N
    else if b = pa then some A.N
    else if b = nm.off then some (A.N + 1)
    else if b = nm.tgt then some ns
    else if b = nm.hist then some (A.N * ℓp * (hb + 1))
    else none with hws_def
  have hws_da : ws da = some A.N := if_pos rfl
  have hws_pa : ws pa = some A.N := by
    show (if pa = da then _ else _) = _
    rw [if_neg (Ne.symm hda_pa), if_pos rfl]
  have hws_off : ws nm.off = some (A.N + 1) := by
    show (if nm.off = da then _ else _) = _
    rw [if_neg (Ne.symm hda_o), if_neg (Ne.symm hpa_o), if_pos rfl]
  have hws_tgt : ws nm.tgt = some ns := by
    show (if nm.tgt = da then _ else _) = _
    rw [if_neg (Ne.symm hda_t), if_neg (Ne.symm hpa_t), if_neg hot, if_pos rfl]
  have hws_hist : ws nm.hist = some (A.N * ℓp * (hb + 1)) := by
    show (if nm.hist = da then _ else _) = _
    rw [if_neg (Ne.symm hda_h), if_neg (Ne.symm hpa_h), if_neg (Ne.symm hoh),
      if_neg (Ne.symm hth), if_pos rfl]
  set aws := arenaWs nm Λc ℓp hb A.N ns with haws_def
  have haws_off : aws nm.off = some (A.N + 1) := arenaWs_off
  have haws_tgt : aws nm.tgt = some ns := arenaWs_tgt hot
  have haws_hist : aws nm.hist = some (A.N * ℓp * (hb + 1)) :=
    arenaWs_hist (Ne.symm hoh) (Ne.symm hth) (Ne.symm hch) (Ne.symm huh)
  -- the allocation fits
  have hFits : FitsW ws σ := by
    intro b m hbm
    by_cases h0 : b = da
    · subst h0; rw [hws_da] at hbm; cases hbm; exact hdaL
    by_cases h1 : b = pa
    · subst h1; rw [hws_pa] at hbm; cases hbm; exact hpaL
    by_cases h2 : b = nm.off
    · subst h2; rw [hws_off] at hbm; cases hbm; exact hAW.fits _ _ haws_off
    by_cases h3 : b = nm.tgt
    · subst h3; rw [hws_tgt] at hbm; cases hbm; exact hAW.fits _ _ haws_tgt
    by_cases h4 : b = nm.hist
    · subst h4; rw [hws_hist] at hbm; cases hbm; exact hAW.fits _ _ haws_hist
    · exfalso
      have : ws b = none := by
        show (if b = da then _ else _) = _
        rw [if_neg h0, if_neg h1, if_neg h2, if_neg h3, if_neg h4]
      rw [this] at hbm
      cases hbm
  -- the truncation satisfies the landed precondition
  have hcsr : GraphCsr nm.off nm.tgt A.G ns (winA ws σ) :=
    graphCsr_of_eq hAW.st.csr
      (arrs_winA_congr (hws_off.trans haws_off.symm) σ)
      (arrs_winA_congr (hws_tgt.trans haws_tgt.symm) σ)
  have hHist : HistArr nm.hist ℓp hb A.hist (winA ws σ) :=
    histArr_congr_arrs hAW.st.hist
      (arrs_winA_congr (haws_hist.trans hws_hist.symm) σ).symm
  -- run the landed seam spec on the truncation, pad back
  obtain ⟨σ', hrun, hfit', hQ, hlenEq, -⟩ :=
    (specWindow (supportsCom_spec_graphCsr (B := B) (G := A.G) (ns := ns)
      (d := d) (ℓp := ℓp) (hb := hb) (oa := nm.off) (ta := nm.tgt) (da := da)
      (pa := pa) (ha := nm.hist) (D := D) (s := s) (e := e)
      hD hDd hdhb hNB hnsB hdB hlB hhB hLB
      hpa_o hpa_t (Ne.symm hda_pa) (Ne.symm hoh)
      (Ne.symm hth) (Ne.symm hda_h) (Ne.symm hpa_h) A.hist)
      ws) σ
      ⟨hFits, hcsr, hsn, hsm, hsr, hsl, hsh, hsp,
        length_arrs_winA hws_pa hpaL,
        length_arrs_winA hws_da hdaL,
        fun v => by
          rw [arrs_winA_some hws_da, getD_take_of_lt v.2]
          exact hdaD v,
        hHist⟩
  obtain ⟨-, -, hdaD', -, hpaP', hHist'⟩ := hQ
  -- the untouched regions and cells
  have hfa : ∀ b, b ∉ (supportsCom nm.off nm.tgt da pa nm.hist).warrs →
      σ'.arrs b = σ.arrs b := fun b hb => hrun.frame_arr b hb
  have hpahi_notin : ∀ b, b ≠ pa → b ≠ nm.hist →
      b ∉ (supportsCom nm.off nm.tgt da pa nm.hist).warrs := by
    intro b hb1 hb2
    rw [warrs_supportsCom]
    simp [hb1, hb2]
  have hfv : ∀ y, y ∉ spScalars → σ'.vars y = σ.vars y := fun y hy =>
    hrun.frame_var y fun hm =>
      hy (wvars_supportsCom_subset nm.off nm.tgt da pa nm.hist y hm)
  have hnS' : σ'.vars nm.nS = σ.vars nm.nS := hfv _ hnS
  refine ⟨σ', hrun.mono (le_of_eq (by rw [hnsum])), ?_, hnS', ?_, ?_, hlenEq⟩
  · -- the windowed contract, at the channel-updated arena
    constructor
    · show FitsW (arenaWs nm Λc ℓp hb A.N (σ'.vars nm.nS)) σ'
      rw [hnS']
      intro b m hbm
      rw [hlenEq b]
      exact hAW.fits b m hbm
    · show ArenaSt nm hb _ (winA (arenaWs nm Λc ℓp hb A.N (σ'.vars nm.nS)) σ')
      rw [hnS']
      have heqo : (winA aws σ').arrs nm.off = (winA aws σ).arrs nm.off :=
        arrs_winA_eq_of_arrs_eq
          (hfa _ (hpahi_notin _ (Ne.symm hpa_o) hoh))
      have heqt : (winA aws σ').arrs nm.tgt = (winA aws σ).arrs nm.tgt :=
        arrs_winA_eq_of_arrs_eq
          (hfa _ (hpahi_notin _ (Ne.symm hpa_t) hth))
      have heqc : (winA aws σ').arrs nm.col = (winA aws σ).arrs nm.col :=
        arrs_winA_eq_of_arrs_eq
          (hfa _ (hpahi_notin _ (Ne.symm hpa_c) hch))
      have heqwithu : (winA aws σ').arrs nm.up = (winA aws σ).arrs nm.up :=
        arrs_winA_eq_of_arrs_eq
          (hfa _ (hpahi_notin _ (Ne.symm hpa_u) huh))
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · -- the carrier cell
        show σ'.vars nm.nN = A.N
        rw [hfv _ hnN]
        exact hAW.st.n_eq
      · -- the CSR, untouched
        show GraphCsr nm.off nm.tgt A.G (σ'.vars nm.nS) (winA aws σ')
        rw [hnS']
        exact graphCsr_of_eq hAW.st.csr heqo heqt
      · -- the color rows, untouched
        obtain ⟨hl, hv⟩ := hAW.st.col
        exact ⟨by rw [heqc]; exact hl, fun v c => by rw [heqc]; exact hv v c⟩
      · -- the renaming, untouched
        obtain ⟨hl, hv⟩ := hAW.st.up
        exact ⟨by rw [heqwithu]; exact hl, fun v => by rw [heqwithu]; exact hv v⟩
      · -- the channel, updated at round `e`
        exact histArr_congr_arrs hHist'
          (arrs_winA_congr (haws_hist.trans hws_hist.symm) σ')
  · -- the distance prefix, untouched
    intro v
    have := hdaD' v
    rwa [arrs_winA_some hws_da, getD_take_of_lt v.2] at this
  · -- the least parents, in the parent prefix
    intro v
    have := hpaP' v
    rwa [arrs_winA_some hws_pa, getD_take_of_lt v.2] at this

/-! ## §4 The batch isolation, lifted -/

open Lax12.UniformQuasiWideness (deleteVerts)

open Classical in
/-- **`isolate` at the windowed contract** (the two-family case,
`restrictCom_specW`'s pattern): from the child's windowed regions, the
batch's windowed bit region and output allocations of at least the
isolated dimensions, `isolateCom` leaves the windowed contract at
**both** arenas — the output names hold `Bar.isolate W` (the isolated
CSR's valid prefixes at the deleted-edge dimensions; the carrier is
kept, `deleteVerts` isolates, never removes), the input arena is
intact, the bit region untouched. Landed budget `isolateK` at the
contract's slot count. -/
theorem isolateCom_specW {B n₀ Λc ℓp hb : ℕ} {Bar : Impl.MArena Λc n₀ ℓp}
    {W : Set (Fin Bar.N)} {nmI : ArenaNames} {oaO taO nsO ba : String}
    (hNB : Bar.N < B) (hNNB : Bar.N * Bar.N < B)
    (hnd5 : ([nmI.off, nmI.tgt, nmI.col, nmI.up, nmI.hist] : List String).Nodup)
    (hba5 : ba ∉ ([nmI.off, nmI.tgt, nmI.col, nmI.up, nmI.hist] : List String))
    (hoaO5 : oaO ∉ ([nmI.off, nmI.tgt, nmI.col, nmI.up, nmI.hist] : List String))
    (htaO5 : taO ∉ ([nmI.off, nmI.tgt, nmI.col, nmI.up, nmI.hist] : List String))
    (hoaO_ba : oaO ≠ ba) (htaO_ba : taO ≠ ba) (htaO_oaO : taO ≠ oaO)
    (hs1 : nsO ∉ rsScalars) (hs2 : nsO ≠ nmI.nN) (hs3 : nsO ≠ nmI.nS)
    (hs4 : nmI.nN ∉ rsScalars) (hs5 : nmI.nS ∉ rsScalars) :
    Spec B
      (fun σ => ArenaStW nmI hb Bar σ ∧ FinBitsW ba W σ ∧
        Bar.N ≤ (σ.arrs ba).length ∧
        Bar.N + 1 ≤ (σ.arrs oaO).length ∧
        (∑ v : Fin Bar.N, (deleteVerts Bar.G W).degree v)
          ≤ (σ.arrs taO).length)
      (isolateCom nmI oaO taO nsO ba)
      (fun σ σ' =>
        ArenaStW { nmI with off := oaO, tgt := taO, nS := nsO } hb
          (Bar.isolate W) σ' ∧
        σ'.vars nsO = ∑ v : Fin Bar.N, (deleteVerts Bar.G W).degree v ∧
        ArenaStW nmI hb Bar σ' ∧ σ'.vars nmI.nS = σ.vars nmI.nS ∧
        FinBitsW ba W σ' ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length))
      (isolateK Bar.N (∑ v : Fin Bar.N, Bar.G.degree v)) := by
  -- the name disequalities, spelled out
  have hnd5C := hnd5
  have hba5C := hba5
  have hoaO5C := hoaO5
  have htaO5C := htaO5
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_or] at hnd5C
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    at hba5C hoaO5C htaO5C
  obtain ⟨⟨hot', hoc, hou, hoh⟩, ⟨htc, htu, hth⟩, ⟨hcu, hch⟩, huh, -⟩ := hnd5C
  obtain ⟨hba_o, hba_t, hba_c, hba_u, hba_h⟩ := hba5C
  obtain ⟨hoaO_o, hoaO_t, hoaO_c, hoaO_u, hoaO_h⟩ := hoaO5C
  obtain ⟨htaO_o, htaO_t, htaO_c, htaO_u, htaO_h⟩ := htaO5C
  have hot : nmI.tgt ≠ nmI.off := Ne.symm hot'
  intro σ hσ
  obtain ⟨hAW, hbW, hbaL, hoaOL, htaOL⟩ := hσ
  set ns := σ.vars nmI.nS with hns_def
  have hnsum : ns = ∑ v : Fin Bar.N, Bar.G.degree v := hAW.st.csr.ns_eq_sum_degree
  have hnsB : ns < B := by
    have := hAW.ns_le_sq
    omega
  set cns := ∑ v : Fin Bar.N, (deleteVerts Bar.G W).degree v with hcns_def
  -- the window assignment: the batch bits, the two fresh output regions
  -- at the isolated dimensions, the input arena's five behind them
  set aws := arenaWs nmI Λc ℓp hb Bar.N ns with haws_def
  set ws : String → Option ℕ := fun b =>
    if b = ba then some Bar.N
    else if b = oaO then some (Bar.N + 1)
    else if b = taO then some cns
    else aws b with hws_def
  have hws_ba : ws ba = some Bar.N := if_pos rfl
  have hws_oaO : ws oaO = some (Bar.N + 1) := by
    show (if oaO = ba then _ else _) = _
    rw [if_neg hoaO_ba, if_pos rfl]
  have hws_taO : ws taO = some cns := by
    show (if taO = ba then _ else _) = _
    rw [if_neg htaO_ba, if_neg htaO_oaO, if_pos rfl]
  have hwsP : ∀ b, b ≠ ba → b ≠ oaO → b ≠ taO → ws b = aws b := by
    intro b h0 h1 h2
    show (if b = ba then _ else _) = _
    rw [if_neg h0, if_neg h1, if_neg h2]
  have hwsPoff : ws nmI.off = aws nmI.off :=
    hwsP _ (Ne.symm hba_o) (Ne.symm hoaO_o) (Ne.symm htaO_o)
  have hwsPtgt : ws nmI.tgt = aws nmI.tgt :=
    hwsP _ (Ne.symm hba_t) (Ne.symm hoaO_t) (Ne.symm htaO_t)
  have hwsPcol : ws nmI.col = aws nmI.col :=
    hwsP _ (Ne.symm hba_c) (Ne.symm hoaO_c) (Ne.symm htaO_c)
  have hwsPup : ws nmI.up = aws nmI.up :=
    hwsP _ (Ne.symm hba_u) (Ne.symm hoaO_u) (Ne.symm htaO_u)
  have hwsPhist : ws nmI.hist = aws nmI.hist :=
    hwsP _ (Ne.symm hba_h) (Ne.symm hoaO_h) (Ne.symm htaO_h)
  -- the input arena's window values
  have haws_off : aws nmI.off = some (Bar.N + 1) := arenaWs_off
  have haws_tgt : aws nmI.tgt = some ns := arenaWs_tgt hot
  have haws_col : aws nmI.col = some (Bar.N * Λc) :=
    arenaWs_col (Ne.symm hoc) (Ne.symm htc)
  have haws_up : aws nmI.up = some Bar.N :=
    arenaWs_up (Ne.symm hou) (Ne.symm htu) (Ne.symm hcu)
  have haws_hist : aws nmI.hist = some (Bar.N * ℓp * (hb + 1)) :=
    arenaWs_hist (Ne.symm hoh) (Ne.symm hth) (Ne.symm hch) (Ne.symm huh)
  -- the allocation fits
  have hFits : FitsW ws σ := by
    intro b m hbm
    by_cases h0 : b = ba
    · subst h0; rw [hws_ba] at hbm; cases hbm; exact hbaL
    by_cases h1 : b = oaO
    · subst h1; rw [hws_oaO] at hbm; cases hbm; exact hoaOL
    by_cases h2 : b = taO
    · subst h2; rw [hws_taO] at hbm; cases hbm; exact htaOL
    · rw [hwsP b h0 h1 h2] at hbm
      exact hAW.fits b m hbm
  -- the truncation satisfies the landed precondition
  have hstP : ArenaSt nmI hb Bar (winA ws σ) := by
    refine arenaSt_of_eq hAW.st rfl rfl ?_ ?_ ?_ ?_ ?_
    · exact arrs_winA_congr hwsPoff σ
    · exact arrs_winA_congr hwsPtgt σ
    · exact arrs_winA_congr hwsPcol σ
    · exact arrs_winA_congr hwsPup σ
    · exact arrs_winA_congr hwsPhist σ
  -- run the landed spec on the truncation, pad back
  obtain ⟨σ', hrun, hfit', hQ, hlenEq, -⟩ :=
    (specWindow (isolateCom_spec (B := B) (Bar := Bar) (W := W) (nmI := nmI)
      (oaO := oaO) (taO := taO) (nsO := nsO) (ba := ba) (nsI := ns)
      hNB hnsB
      htaO_o htaO_t htaO_ba htaO_oaO hoaO_o hoaO_t hoaO_ba
      hoaO_c hoaO_u hoaO_h htaO_c htaO_u htaO_h
      hs1 hs2 hs3 hs4 hs5) ws) σ
      ⟨hFits, hstP, rfl, finBits_win_of_W hws_ba hbW,
        length_arrs_winA hws_oaO hoaOL, length_arrs_winA hws_taO htaOL⟩
  obtain ⟨hstI', hcns', hstP', hnsI', hbb'⟩ := hQ
  refine ⟨σ', hrun.mono (le_of_eq (by rw [hnsum])), ?_, hcns', ?_, hnsI', ?_,
    hlenEq⟩
  · -- the isolated arena's windowed contract, at the output names
    have hcell : σ'.vars nsO = cns := hcns'
    constructor
    · show FitsW (arenaWs { nmI with off := oaO, tgt := taO, nS := nsO }
          Λc ℓp hb Bar.N (σ'.vars nsO)) σ'
      rw [hcell]
      intro b m hbm
      have hb5 := arenaWs_some_elim hbm
      rcases hb5 with rfl | rfl | rfl | rfl | rfl
      · rw [arenaWs_off] at hbm
        cases hbm
        rw [hlenEq]
        exact hoaOL
      · rw [arenaWs_tgt htaO_oaO] at hbm
        cases hbm
        rw [hlenEq]
        exact htaOL
      · rw [arenaWs_col (nm := { nmI with off := oaO, tgt := taO, nS := nsO }) (Ne.symm hoaO_c) (Ne.symm htaO_c)] at hbm
        cases hbm
        rw [hlenEq]
        exact hAW.fits _ _ haws_col
      · rw [arenaWs_up (nm := { nmI with off := oaO, tgt := taO, nS := nsO }) (Ne.symm hoaO_u) (Ne.symm htaO_u)
          (Ne.symm hcu)] at hbm
        cases hbm
        rw [hlenEq]
        exact hAW.fits _ _ haws_up
      · rw [arenaWs_hist (nm := { nmI with off := oaO, tgt := taO, nS := nsO }) (Ne.symm hoaO_h) (Ne.symm htaO_h) (Ne.symm hch)
          (Ne.symm huh)] at hbm
        cases hbm
        rw [hlenEq]
        exact hAW.fits _ _ haws_hist
    · show ArenaSt { nmI with off := oaO, tgt := taO, nS := nsO } hb
        (Bar.isolate W)
        (winA (arenaWs { nmI with off := oaO, tgt := taO, nS := nsO }
          Λc ℓp hb Bar.N (σ'.vars nsO)) σ')
      rw [hcell]
      refine arenaSt_of_eq hstI' rfl rfl ?_ ?_ ?_ ?_ ?_
      · exact arrs_winA_congr (arenaWs_off.trans hws_oaO.symm) σ'
      · exact arrs_winA_congr ((arenaWs_tgt htaO_oaO).trans hws_taO.symm) σ'
      · exact arrs_winA_congr ((arenaWs_col (nm := { nmI with off := oaO, tgt := taO, nS := nsO }) (Ne.symm hoaO_c)
          (Ne.symm htaO_c)).trans (hwsPcol.trans haws_col).symm) σ'
      · exact arrs_winA_congr ((arenaWs_up (nm := { nmI with off := oaO, tgt := taO, nS := nsO }) (Ne.symm hoaO_u)
          (Ne.symm htaO_u) (Ne.symm hcu)).trans
          (hwsPup.trans haws_up).symm) σ'
      · exact arrs_winA_congr ((arenaWs_hist (nm := { nmI with off := oaO, tgt := taO, nS := nsO }) (Ne.symm hoaO_h)
          (Ne.symm htaO_h) (Ne.symm hch) (Ne.symm huh)).trans
          (hwsPhist.trans haws_hist).symm) σ'
  · -- the input arena's windowed contract, preserved
    have hcell : σ'.vars nmI.nS = ns := hnsI'
    constructor
    · show FitsW (arenaWs nmI Λc ℓp hb Bar.N (σ'.vars nmI.nS)) σ'
      rw [hcell]
      intro b m hbm
      rw [hlenEq]
      exact hAW.fits b m hbm
    · show ArenaSt nmI hb Bar
        (winA (arenaWs nmI Λc ℓp hb Bar.N (σ'.vars nmI.nS)) σ')
      rw [hcell]
      refine arenaSt_of_eq hstP' rfl rfl ?_ ?_ ?_ ?_ ?_
      · exact arrs_winA_congr hwsPoff.symm σ'
      · exact arrs_winA_congr hwsPtgt.symm σ'
      · exact arrs_winA_congr hwsPcol.symm σ'
      · exact arrs_winA_congr hwsPup.symm σ'
      · exact arrs_winA_congr hwsPhist.symm σ'
  · -- the bit region, untouched
    exact finBitsW_of_win hws_ba hfit' hbb'

/-! ## §5 The profilesMS stage, lifted -/

open Classical in
/-- **The profilesMS stage at the windowed contract**: from the level's
windowed arena regions (the *pre-isolation* child — profiles are
measured in `preG` BEFORE isolation, the campaign's oldest hazard), the
batch region padded to exactly `mb` (a duplicate costs another call),
and allocations of at least the stage's dimensions for the two shared
scratch regions and the three name families, `profilesCom` leaves the
windowed contract intact — the arena regions are read-only for it —
and the `mb + (Λc+1)` table prefixes satisfying
`Impl.ProfileTablesMS` at the arena's own graph and colours, with the
landed value bounds. Landed budget `profilesK` at the contract's slot
count; the per-class `vt` windows are the only data-dependent ones
(`ns + 2·|col c|`). The stage's name discipline enters through
`ProfNames.Ok` at the literal family built from the arena's names,
plus freshness of the write targets against the two regions the stage
never reads (`up`, `hist`). -/
theorem profilesCom_specW {B n₀ Λc ℓp hb mb R : ℕ} {A : Impl.MArena Λc n₀ ℓp}
    {nm : ArenaNames} {ba xb vo : String} {pdF vtF puF : ℕ → String}
    (w : Fin mb → Fin A.N)
    (hok : ProfNames.Ok ⟨nm.off, nm.tgt, nm.col, ba, xb, vo, nm.nN, nm.nS,
      pdF, vtF, puF⟩ mb (Λc + 1))
    (hNB : A.N + 2 < B)
    (hnsB : (∑ v : Fin A.N, A.G.degree v) + 2 * A.N + 1 < B)
    (hRB : R + 3 < B) (hmbB : mb < B) (hΛB : A.N * Λc < B)
    (hnd5 : ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String).Nodup)
    (hba3 : ba ∉ ([nm.off, nm.tgt, nm.col] : List String))
    (hxbP : xb ∉ ([nm.up, nm.hist] : List String))
    (hvoP : vo ∉ ([nm.up, nm.hist] : List String))
    (hpdP : ∀ j < mb, pdF j ∉ ([nm.up, nm.hist] : List String))
    (hvtP : ∀ c < Λc, vtF c ∉ ([nm.up, nm.hist] : List String))
    (hpuP : ∀ c < Λc + 1, puF c ∉ ([nm.up, nm.hist] : List String)) :
    Spec B
      (fun σ => ArenaStW nm hb A σ ∧
        (σ.arrs ba).length = mb ∧
        (∀ j : Fin mb, (σ.arrs ba).getD (j : ℕ) 0 = (w j : ℕ)) ∧
        A.N ≤ (σ.arrs xb).length ∧ A.N + 2 ≤ (σ.arrs vo).length ∧
        (∀ j < mb, A.N ≤ (σ.arrs (pdF j)).length) ∧
        (∀ c : Fin Λc, (∑ v : Fin A.N, A.G.degree v) + 2 * (A.col c).ncard
          ≤ (σ.arrs (vtF (c : ℕ))).length) ∧
        (∀ c < Λc + 1, A.N + 1 ≤ (σ.arrs (puF c)).length))
      (profilesCom ⟨nm.off, nm.tgt, nm.col, ba, xb, vo, nm.nN, nm.nS,
        pdF, vtF, puF⟩ mb Λc R)
      (fun σ σ' => ArenaStW nm hb A σ' ∧
        σ'.vars nm.nS = σ.vars nm.nS ∧
        (∀ b, (σ'.arrs b).length = (σ.arrs b).length) ∧
        (∀ j : Fin mb, ∀ v : Fin A.N,
          (σ'.arrs (pdF (j : ℕ))).getD (v : ℕ) 0 ≤ R + 1) ∧
        (∀ c : Fin (Λc + 1), ∀ v : Fin (A.N + 1),
          (σ'.arrs (puF (c : ℕ))).getD (v : ℕ) 0 ≤ R + 2) ∧
        Impl.ProfileTablesMS A.G w (Driver.relColoring A.col Set.univ) R
          (fun j v => (σ'.arrs (pdF (j : ℕ))).getD (v : ℕ) 0)
          (fun c v => (σ'.arrs (puF (c : ℕ))).getD (v : ℕ) 0))
      (profilesK mb (Λc + 1) A.N (∑ v : Fin A.N, A.G.degree v) R) := by
  -- the name family, and its clauses at the arena's names
  set pn : ProfNames := ⟨nm.off, nm.tgt, nm.col, ba, xb, vo, nm.nN, nm.nS,
    pdF, vtF, puF⟩ with hpn_def
  have hxb_ro : xb ∉ ([nm.off, nm.tgt, nm.col, ba] : List String) := hok.xb_ro
  have hvo_ro : vo ∉ ([nm.off, nm.tgt, nm.col, ba] : List String) := hok.vo_ro
  have hpd_ro : ∀ j < mb, pdF j ∉ ([nm.off, nm.tgt, nm.col, ba] : List String) :=
    hok.pd_ro
  have hvt_ro : ∀ c, c + 1 < Λc + 1 →
      vtF c ∉ ([nm.off, nm.tgt, nm.col, ba] : List String) := hok.vt_ro
  have hpu_ro : ∀ c < Λc + 1,
      puF c ∉ ([nm.off, nm.tgt, nm.col, ba] : List String) := hok.pu_ro
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    at hxb_ro hvo_ro
  obtain ⟨hxb_o, hxb_t, hxb_c, hxb_ba⟩ := hxb_ro
  obtain ⟨hvo_o, hvo_t, hvo_c, hvo_ba⟩ := hvo_ro
  have hxb_vo : xb ≠ vo := hok.xb_vo
  -- the arena five, pairwise, and the passive-region freshness
  have hnd5C := hnd5
  have hba3C := hba3
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false,
    List.nodup_nil, and_true, not_or] at hnd5C
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hba3C
  obtain ⟨⟨hot', hoc, hou, hoh⟩, ⟨htc, htu, hth⟩, ⟨hcu, hch⟩, huh, -⟩ := hnd5C
  obtain ⟨hba_o, hba_t, hba_c⟩ := hba3C
  intro σ hσ
  obtain ⟨hAW, hbaL, hbaG, hxbL, hvoL, hpdL, hvtL, hpuL⟩ := hσ
  -- the slot count is the degree sum
  set nsc := σ.vars nm.nS with hnsc_def
  set ns := ∑ v : Fin A.N, A.G.degree v with hns_def
  have hcell : nsc = ns := hAW.st.csr.ns_eq_sum_degree
  -- the window assignment
  set ws : String → Option ℕ := fun b =>
    if b = xb then some A.N
    else if b = vo then some (A.N + 2)
    else if h : ∃ j, j < mb ∧ b = pdF j then some A.N
    else if h : ∃ c, c < Λc ∧ b = vtF c then
      some (ns + 2 * (A.col ⟨h.choose, h.choose_spec.1⟩).ncard)
    else if h : ∃ c, c < Λc + 1 ∧ b = puF c then some (A.N + 1)
    else if b = nm.off then some (A.N + 1)
    else if b = nm.tgt then some ns
    else if b = nm.col then some (A.N * Λc)
    else none with hws_def
  -- evaluating the assignment at the names in play
  have hws_xb : ws xb = some A.N := if_pos rfl
  have hws_vo : ws vo = some (A.N + 2) := by
    show (if vo = xb then _ else _) = _
    rw [if_neg (Ne.symm hxb_vo), if_pos rfl]
  have hws_pd : ∀ j, j < mb → ws (pdF j) = some A.N := by
    intro j hj
    show (if pdF j = xb then _ else _) = _
    rw [if_neg (hok.pd_xb j hj), if_neg (hok.pd_vo j hj),
      dif_pos (⟨j, hj, rfl⟩ : ∃ j', j' < mb ∧ pdF j = pdF j')]
  have hws_vt : ∀ c : Fin Λc,
      ws (vtF (c : ℕ)) = some (ns + 2 * (A.col c).ncard) := by
    intro c
    have hc1 : (c : ℕ) + 1 < Λc + 1 := by omega
    show (if vtF (c : ℕ) = xb then _ else _) = _
    rw [if_neg (hok.vt_xb _ hc1), if_neg (hok.vt_vo _ hc1),
      dif_neg (fun ⟨j, hj, hEq⟩ => hok.pd_vt j hj _ hc1 hEq.symm)]
    have hex : ∃ c', c' < Λc ∧ vtF (c : ℕ) = vtF c' := ⟨(c : ℕ), c.isLt, rfl⟩
    rw [dif_pos hex]
    have heq : (c : ℕ) = hex.choose :=
      hok.vt_inj (c : ℕ) hc1 hex.choose (by have := hex.choose_spec.1; omega)
        hex.choose_spec.2
    have hcc : (⟨hex.choose, hex.choose_spec.1⟩ : Fin Λc) = c :=
      Fin.ext heq.symm
    rw [hcc]
  have hws_pu : ∀ c, c < Λc + 1 → ws (puF c) = some (A.N + 1) := by
    intro c hc
    show (if puF c = xb then _ else _) = _
    rw [if_neg (hok.pu_xb c hc), if_neg (hok.pu_vo c hc),
      dif_neg (fun ⟨j, hj, hEq⟩ => hok.pd_pu j hj c hc hEq.symm),
      dif_neg (fun ⟨c', hc', hEq⟩ =>
        hok.vt_pu c' (by omega) c hc hEq.symm),
      dif_pos (⟨c, hc, rfl⟩ : ∃ c', c' < Λc + 1 ∧ puF c = puF c')]
  have hws_arena : ∀ b, b ≠ xb → b ≠ vo → (¬ ∃ j, j < mb ∧ b = pdF j) →
      (¬ ∃ c, c < Λc ∧ b = vtF c) → (¬ ∃ c, c < Λc + 1 ∧ b = puF c) →
      ws b = (if b = nm.off then some (A.N + 1)
        else if b = nm.tgt then some ns
        else if b = nm.col then some (A.N * Λc) else none) := by
    intro b h1 h2 h3 h4 h5
    show (if b = xb then _ else _) = _
    rw [if_neg h1, if_neg h2, dif_neg h3, dif_neg h4, dif_neg h5]
  have hnotf : ∀ b, b ∉ ([nm.off, nm.tgt, nm.col, ba] : List String) →
      b ≠ nm.off ∧ b ≠ nm.tgt ∧ b ≠ nm.col ∧ b ≠ ba := by
    intro b hbmem
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hbmem
    exact hbmem
  have hws_off : ws nm.off = some (A.N + 1) := by
    rw [hws_arena nm.off (Ne.symm hxb_o) (Ne.symm hvo_o)
      (fun ⟨j, hj, hEq⟩ => (hnotf _ (hpd_ro j hj)).1 hEq.symm)
      (fun ⟨c, hc, hEq⟩ => (hnotf _ (hvt_ro c (by omega))).1 hEq.symm)
      (fun ⟨c, hc, hEq⟩ => (hnotf _ (hpu_ro c hc)).1 hEq.symm),
      if_pos rfl]
  have hws_tgt : ws nm.tgt = some ns := by
    rw [hws_arena nm.tgt (Ne.symm hxb_t) (Ne.symm hvo_t)
      (fun ⟨j, hj, hEq⟩ => (hnotf _ (hpd_ro j hj)).2.1 hEq.symm)
      (fun ⟨c, hc, hEq⟩ => (hnotf _ (hvt_ro c (by omega))).2.1 hEq.symm)
      (fun ⟨c, hc, hEq⟩ => (hnotf _ (hpu_ro c hc)).2.1 hEq.symm),
      if_neg (Ne.symm hot'), if_pos rfl]
  have hws_col : ws nm.col = some (A.N * Λc) := by
    rw [hws_arena nm.col (Ne.symm hxb_c) (Ne.symm hvo_c)
      (fun ⟨j, hj, hEq⟩ => (hnotf _ (hpd_ro j hj)).2.2.1 hEq.symm)
      (fun ⟨c, hc, hEq⟩ => (hnotf _ (hvt_ro c (by omega))).2.2.1 hEq.symm)
      (fun ⟨c, hc, hEq⟩ => (hnotf _ (hpu_ro c hc)).2.2.1 hEq.symm),
      if_neg (Ne.symm hoc), if_neg (Ne.symm htc), if_pos rfl]
  have hws_ba : ws ba = none := by
    rw [hws_arena ba (Ne.symm hxb_ba) (Ne.symm hvo_ba)
      (fun ⟨j, hj, hEq⟩ => (hnotf _ (hpd_ro j hj)).2.2.2 hEq.symm)
      (fun ⟨c, hc, hEq⟩ => (hnotf _ (hvt_ro c (by omega))).2.2.2 hEq.symm)
      (fun ⟨c, hc, hEq⟩ => (hnotf _ (hpu_ro c hc)).2.2.2 hEq.symm),
      if_neg hba_o, if_neg hba_t, if_neg hba_c]
  -- the arena's own window family, at the same values
  set aws := arenaWs nm Λc ℓp hb A.N nsc with haws_def
  have haws_off : aws nm.off = some (A.N + 1) := arenaWs_off
  have haws_tgt : aws nm.tgt = some nsc := arenaWs_tgt (Ne.symm hot')
  have haws_col : aws nm.col = some (A.N * Λc) :=
    arenaWs_col (Ne.symm hoc) (Ne.symm htc)
  -- the allocation fits
  have hFits : FitsW ws σ := by
    intro b m hbm
    by_cases h1 : b = xb
    · subst h1; rw [hws_xb] at hbm; cases hbm; exact hxbL
    by_cases h2 : b = vo
    · subst h2; rw [hws_vo] at hbm; cases hbm; exact hvoL
    by_cases h3 : ∃ j, j < mb ∧ b = pdF j
    · obtain ⟨j, hj, rfl⟩ := h3
      rw [hws_pd j hj] at hbm
      cases hbm
      exact hpdL j hj
    by_cases h4 : ∃ c, c < Λc ∧ b = vtF c
    · obtain ⟨c, hc, rfl⟩ := h4
      rw [hws_vt ⟨c, hc⟩] at hbm
      cases hbm
      exact hvtL ⟨c, hc⟩
    by_cases h5 : ∃ c, c < Λc + 1 ∧ b = puF c
    · obtain ⟨c, hc, rfl⟩ := h5
      rw [hws_pu c hc] at hbm
      cases hbm
      exact hpuL c hc
    rw [hws_arena b h1 h2 h3 h4 h5] at hbm
    by_cases h6 : b = nm.off
    · subst h6
      rw [if_pos rfl] at hbm
      cases hbm
      exact hAW.fits _ _ haws_off
    rw [if_neg h6] at hbm
    by_cases h7 : b = nm.tgt
    · subst h7
      rw [if_pos rfl] at hbm
      cases hbm
      rw [← hcell]
      exact hAW.fits _ _ haws_tgt
    rw [if_neg h7] at hbm
    by_cases h8 : b = nm.col
    · subst h8
      rw [if_pos rfl] at hbm
      cases hbm
      exact hAW.fits _ _ haws_col
    · rw [if_neg h8] at hbm
      cases hbm
  -- the truncation satisfies the stage precondition
  have hcsr : GraphCsr nm.off nm.tgt A.G ns (winA ws σ) := by
    rw [← hcell]
    exact graphCsr_of_eq hAW.st.csr
      (arrs_winA_congr (hws_off.trans haws_off.symm) σ)
      (arrs_winA_congr ((hws_tgt.trans (by rw [hcell])).trans haws_tgt.symm) σ)
  have hcolb : ColBits nm.col A.col (winA ws σ) := by
    have heqc : (winA ws σ).arrs nm.col = (winA aws σ).arrs nm.col :=
      arrs_winA_congr (hws_col.trans haws_col.symm) σ
    obtain ⟨hl, hv⟩ := hAW.st.col
    exact ⟨by rw [heqc]; exact hl, fun v cc => by rw [heqc]; exact hv v cc⟩
  have hpre : ProfPre pn A.G A.col ns w (winA ws σ) := by
    refine ⟨hcsr, hcolb, hAW.st.n_eq, hcell, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [arrs_winA_none hws_ba]; exact hbaL
    · intro j; rw [arrs_winA_none hws_ba]; exact hbaG j
    · exact length_arrs_winA hws_xb hxbL
    · exact length_arrs_winA hws_vo hvoL
    · intro j
      exact length_arrs_winA (hws_pd (j : ℕ) j.isLt) (hpdL (j : ℕ) j.isLt)
    · intro c
      exact length_arrs_winA (hws_vt c) (hvtL c)
    · intro c hc
      exact length_arrs_winA (hws_pu c hc) (hpuL c hc)
  -- run the landed stage on the truncation, pad back
  obtain ⟨σ', hrun, hfit', hQ, hlenEq, -⟩ :=
    (specWindow (profilesCom_spec (B := B) (H := A.G) (col := A.col)
      (w := w) (pn := pn) (ns := ns) (mb := mb) (Λl := Λc) (R := R)
      hok hNB hnsB hRB hmbB hΛB) ws) σ ⟨hFits, hpre⟩
  obtain ⟨hbd1, hbd2, hpt⟩ := hQ
  -- the arena regions and cells are untouched
  have hxbPC := hxbP
  have hvoPC := hvoP
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hxbPC hvoPC
  obtain ⟨hxb_u, hxb_h⟩ := hxbPC
  obtain ⟨hvo_u, hvo_h⟩ := hvoPC
  have hframe : ∀ b,
      b ∈ ([nm.off, nm.tgt, nm.col, nm.up, nm.hist] : List String) →
      σ'.arrs b = σ.arrs b := by
    intro b hbmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hbmem
    refine hrun.frame_arr b fun hmem => ?_
    rcases warrs_profilesCom_subset pn mb Λc R b hmem with h | h | ⟨j, hj, h⟩ |
      ⟨c, hc, h⟩ | ⟨c, hc, h⟩
    · subst h
      rcases hbmem with h' | h' | h' | h' | h'
      · exact hxb_o h'
      · exact hxb_t h'
      · exact hxb_c h'
      · exact hxb_u h'
      · exact hxb_h h'
    · subst h
      rcases hbmem with h' | h' | h' | h' | h'
      · exact hvo_o h'
      · exact hvo_t h'
      · exact hvo_c h'
      · exact hvo_u h'
      · exact hvo_h h'
    · subst h
      have h4 := hnotf _ (hpd_ro j hj)
      have h5 := hpdP j hj
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h5
      rcases hbmem with h' | h' | h' | h' | h'
      · exact h4.1 h'
      · exact h4.2.1 h'
      · exact h4.2.2.1 h'
      · exact h5.1 h'
      · exact h5.2 h'
    · subst h
      have h4 := hnotf _ (hvt_ro c (by omega))
      have h5 := hvtP c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h5
      rcases hbmem with h' | h' | h' | h' | h'
      · exact h4.1 h'
      · exact h4.2.1 h'
      · exact h4.2.2.1 h'
      · exact h5.1 h'
      · exact h5.2 h'
    · subst h
      have h4 := hnotf _ (hpu_ro c hc)
      have h5 := hpuP c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at h5
      rcases hbmem with h' | h' | h' | h' | h'
      · exact h4.1 h'
      · exact h4.2.1 h'
      · exact h4.2.2.1 h'
      · exact h5.1 h'
      · exact h5.2 h'
  have hfv : ∀ y, y ∉ profScalars → σ'.vars y = σ.vars y := fun y hy =>
    hrun.frame_var y fun hm =>
      hy (wvars_profilesCom_subset pn mb Λc R y hm)
  have hnS' : σ'.vars nm.nS = σ.vars nm.nS := hfv _ hok.nS_scr
  refine ⟨σ', hrun, ?_, hnS', hlenEq, ?_, ?_, ?_⟩
  · exact arenaStW_of_eq hAW (hfv _ hok.nN_scr) hnS'
      (hframe _ (by simp)) (hframe _ (by simp)) (hframe _ (by simp))
      (hframe _ (by simp)) (hframe _ (by simp))
  · -- the batch-table bound, off the allocation's prefix
    intro j v
    have := hbd1 j v
    rwa [arrs_winA_some (hws_pd (j : ℕ) j.isLt), getD_take_of_lt v.2] at this
  · -- the class-table bound, off the allocation's prefix
    intro c v
    have := hbd2 c v
    rwa [arrs_winA_some (hws_pu (c : ℕ) c.isLt), getD_take_of_lt v.2] at this
  · -- the tables, off the allocations' prefixes (`BallTable` is
    -- pointwise in the distance function)
    obtain ⟨hp1, hp2⟩ := hpt
    refine ⟨fun j v k hk => ?_, fun c v k hk => ?_⟩
    · have := hp1 j v k hk
      simp only [hpn_def] at this
      rwa [arrs_winA_some (hws_pd (j : ℕ) j.isLt), getD_take_of_lt v.2] at this
    · have := hp2 c v k hk
      simp only [hpn_def] at this
      rwa [arrs_winA_some (hws_pu (c : ℕ) c.isLt), getD_take_of_lt v.2] at this

end Lax3Proofs.Prog
