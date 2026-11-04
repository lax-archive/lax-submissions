import Lax185574Proofs.StpRam.ScriptBounds

/-!
The rounds of the script of lem:compute-stp, for the compiled glue
program at a word length `v` with room for a value bound `Bv ≥ vB`:
the first round (`script_r0`, and `script_r0_zero` for `q = 0`), the
middle rounds (`script_mid`) and the final round (`script_fin`). Each
gives a halting run with the scripted output, and that every halting run
has this output.
-/

namespace Lax185574Proofs.StpRam

open Lax808846.Ram Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax808846Proofs.Compile
open Lax185574.WordEncoding Lax185574Proofs.Words Lax185574.TypeTrees Lax185574.PartialGraphs
open Lax185574.ScatterTypes Lax185574.PartialGraphEncoding Lax185574Proofs.Simulate
open Lax185574Proofs.RamSim Lax185574.DistanceMatrix Lax185574Proofs.DistMatrix

variable {n : ℕ}

theorem lpU_round' (x S Qr b : List ℕ) (tg w : ℕ) (hS : ∃ S', S = 0 :: S') :
    lpU x ([tg, S.length, w] ++ S ++ Qr) b = [tg, S.length] ++ x.take w ++ S ++ (b.length :: b) := by
  obtain ⟨S', rfl⟩ := hS
  exact lpU_round x S' Qr b tg w

theorem take_succ_getD (ws : List (List ℕ)) {t : ℕ} (ht : t < ws.length) :
    ws.take t ++ [ws.getD t []] = ws.take (t + 1) := by
  rw [List.take_add_one, List.getElem?_eq_getElem ht, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem ht]; simp

theorem getD_append_take (F A : List (List ℕ)) {i j : ℕ} (hi : i < F.length + j) :
    (F ++ A.take j).getD i [] = (F ++ A).getD i [] := by
  have : F ++ A.take j = (F ++ A).take (F.length + j) := by rw [List.take_append]; simp
  rw [this, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

theorem stp_zero (G : PartialGraph (Fin n)) (k : ℕ) : toWord (stp G k 0) = [0] := by
  rw [toWord_stp (fun u v => mem_adjOf_resolved G u v)]
  have : answers G k 0 = [] := by simp [answers]
  rw [this]
  have hs : sortedDistinct ([] : List (List ℕ)) = [] := by simp [sortedDistinct]
  simp [emitList, hs, toWord_words, frames]

theorem toWord_distMatrix_cons (G : PartialGraph (Fin n)) :
    toWord (distMatrix G) = n :: (toWord (distMatrix G)).tail := by
  rw [toWord_distMatrix]; rfl

theorem length_tail_distMatrix (G : PartialGraph (Fin n)) :
    (toWord (distMatrix G)).tail.length = n * (n + 1) := by
  rw [List.length_tail, length_toWord_distMatrix]; omega

theorem bv_facts {k q X Bv : ℕ} (hX : 1 ≤ X) (h : 64 * (rK k q + 1) * X ^ 3 ≤ Bv) :
    64 * X ^ 3 ≤ Bv ∧ 64 * (rK k q + 1) ≤ Bv ∧ (rK k q + 1) * X ^ 3 + 1 < Bv := by
  have h1 : 1 ≤ X ^ 3 := Nat.one_le_pow _ _ (by omega)
  refine ⟨by nlinarith, by nlinarith, by nlinarith⟩

set_option maxHeartbeats 2000000 in
/-- **The first round.** -/
theorem script_r0 {G : PartialGraph (Fin n)} {k q v Bv : ℕ} (hn : 1 ≤ n) (hq : 1 ≤ q)
    (hBv : vB G k q ≤ Bv) (hS : gsz * Bv ≤ 2 ^ v) :
    (∃ tm ≤ 10 * (winCost n + 9 * (n * (n + 1)) + n * (48 * maxTreeSize G k q + 110) +
        100 * ((toWord (family G k q)).length + n) + 1030) + 1,
      RunsTo v gProg (lpU (xIn G k q) (Ao G k q 0) (Bo G k q 0)) (Ao G k q 1) tm) ∧
    ∀ o tm, RunsTo v gProg (lpU (xIn G k q) (Ao G k q 0) (Bo G k q 0)) o tm → o = Ao G k q 1 := by
  have hs := sizes G k q
  unfold vB at hBv
  generalize (xIn G k q).length + maxEntry (xIn G k q) + 1 = X at hs hBv
  obtain ⟨hX3, hX23, hX2⟩ := X_pow hs
  obtain ⟨hb1, -, -⟩ := bv_facts hs.one hBv
  have hlen := hs.len
  have hnX := hs.nX
  set f := family G k q with hf
  set ext : String → ℕ := fun s => if s = "eo" then n + 1 else if s = "et" then offL G.edge n else
    if s = "no" then n + 1 else if s = "nt" then offL G.nonEdge n else
    if s = "x" then 8 + (toWord f).length + n else 0 with hext
  have hent : ∀ y ∈ toWord f, y < Bv := fun y hy => by
    have := hs.ent y (by rw [xIn_eq]; exact List.mem_append_right _ hy); omega
  obtain ⟨σ', r, ho⟩ := glue_round0 (B := Bv) (k := k) (q := q) (L := maxTreeSize G k q) G f hn
    (toWord_distMatrix_cons G) (length_tail_distMatrix G) ext hs.famL
    (by simp [hext]) (by simp [hext]) (by simp [hext]) (by simp [hext]) (by simp [hext])
    (by omega) (by have := hs.offE; omega) (by have := hs.offN; omega) (by omega) hent
    (by have := hs.kX; omega) (by have := hs.qX; omega)
  rw [if_neg (by omega)] at ho
  have hu : lpU (xIn G k q) (Ao G k q 0) (Bo G k q 0) =
      [0, ((toWord G ++ [k, q]) ++ toWord (distMatrix G) ++ toWord f).length] ++ ((toWord G ++ [k, q]) ++ toWord (distMatrix G) ++ toWord f) ++
        [0] := by
    simp only [Ao, Bo]; rw [ShiftRam.lpU_first, xIn_eq]
  rw [hu]
  have hu' : ∀ y ∈ [0, ((toWord G ++ [k, q]) ++ toWord (distMatrix G) ++ toWord f).length] ++
      ((toWord G ++ [k, q]) ++ toWord (distMatrix G) ++ toWord f) ++ [0],
      y < Bv := by
    intro y hy
    rcases List.mem_append.mp hy with h | h
    · rcases List.mem_append.mp h with h | h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · omega
        · simp; omega
      · have := hs.ent y (by rw [xIn_eq]; exact h); omega
    · simp at h; omega
  obtain ⟨h1, h2⟩ := glue_runsTo glue_ok (B := Bv) (v := v) (ext := ext) (by omega) hS hu' r
  have hQ : 0 < q * n := Nat.mul_pos (by omega) (by omega)
  have hout : σ'.out = Ao G k q 1 := by
    rw [ho]
    simp only [Ao, tagS, winS, if_pos hQ, stS, glW, famF, List.take_zero, qryS, idxS]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [length_famW]; omega)]
    simp only [famW, hf, List.getElem?_ofFn]
    rw [dif_pos (by omega)]; rfl
  rw [hout] at h1 h2
  obtain ⟨tm, htm, hrun⟩ := h1
  exact ⟨⟨tm, le_trans htm (by simp only [Layout.const]; omega), hrun⟩, h2⟩

set_option maxHeartbeats 2000000 in
/-- **The first round for `q = 0`.** -/
theorem script_r0_zero {G : PartialGraph (Fin n)} {k v Bv : ℕ} (hn : 1 ≤ n)
    (hBv : vB G k 0 ≤ Bv) (hS : gsz * Bv ≤ 2 ^ v) :
    (∃ tm ≤ 10 * (winCost n + 9 * (n * (n + 1)) + n * (48 * maxTreeSize G k 0 + 110) +
        100 * ((toWord (family G k 0)).length + n) + 1030) + 1,
      RunsTo v gProg (lpU (xIn G k 0) (Ao G k 0 0) (Bo G k 0 0)) (0 :: toWord (stp G k 0)) tm) ∧
    ∀ o tm, RunsTo v gProg (lpU (xIn G k 0) (Ao G k 0 0) (Bo G k 0 0)) o tm →
      o = 0 :: toWord (stp G k 0) := by
  have hs := sizes G k 0
  unfold vB at hBv
  generalize (xIn G k 0).length + maxEntry (xIn G k 0) + 1 = X at hs hBv
  obtain ⟨hX3, hX23, hX2⟩ := X_pow hs
  obtain ⟨hb1, -, -⟩ := bv_facts hs.one hBv
  have hlen := hs.len
  have hnX := hs.nX
  set f := family G k 0 with hf
  set ext : String → ℕ := fun s => if s = "eo" then n + 1 else if s = "et" then offL G.edge n else
    if s = "no" then n + 1 else if s = "nt" then offL G.nonEdge n else
    if s = "x" then 8 + (toWord f).length + n else 0 with hext
  have hent : ∀ y ∈ toWord f, y < Bv := fun y hy => by
    have := hs.ent y (by rw [xIn_eq]; exact List.mem_append_right _ hy); omega
  obtain ⟨σ', r, ho⟩ := glue_round0 (B := Bv) (k := k) (q := 0) (L := maxTreeSize G k 0) G f hn
    (toWord_distMatrix_cons G) (length_tail_distMatrix G) ext hs.famL
    (by simp [hext]) (by simp [hext]) (by simp [hext]) (by simp [hext]) (by simp [hext])
    (by omega) (by have := hs.offE; omega) (by have := hs.offN; omega) (by omega) hent
    (by have := hs.kX; omega) (by omega)
  rw [if_pos rfl] at ho
  have hu : lpU (xIn G k 0) (Ao G k 0 0) (Bo G k 0 0) =
      [0, ((toWord G ++ [k, 0]) ++ toWord (distMatrix G) ++ toWord f).length] ++ ((toWord G ++ [k, 0]) ++ toWord (distMatrix G) ++ toWord f) ++
        [0] := by
    simp only [Ao, Bo]; rw [ShiftRam.lpU_first, xIn_eq]
  rw [hu]
  have hu' : ∀ y ∈ [0, ((toWord G ++ [k, 0]) ++ toWord (distMatrix G) ++ toWord f).length] ++
      ((toWord G ++ [k, 0]) ++ toWord (distMatrix G) ++ toWord f) ++ [0],
      y < Bv := by
    intro y hy
    rcases List.mem_append.mp hy with h | h
    · rcases List.mem_append.mp h with h | h
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl
        · omega
        · simp; omega
      · have := hs.ent y (by rw [xIn_eq]; exact h); omega
    · simp at h; omega
  obtain ⟨h1, h2⟩ := glue_runsTo glue_ok (B := Bv) (v := v) (ext := ext) (by omega) hS hu' r
  have hz : σ'.out = 0 :: toWord (stp G k 0) := by rw [ho, stp_zero]
  rw [hz] at h1 h2
  obtain ⟨tm, htm, hrun⟩ := h1
  exact ⟨⟨tm, le_trans htm (by simp only [Layout.const]; omega), hrun⟩, h2⟩

set_option maxHeartbeats 4000000 in
/-- **A middle round.** -/
theorem script_mid {G : PartialGraph (Fin n)} {k q v Bv t : ℕ} (hn : 1 ≤ n) (ht : t < q * n)
    (hBv : vB G k q ≤ Bv) (hS : gsz * Bv ≤ 2 ^ v) :
    (∃ tm ≤ 10 * (100 * (stS G k q (t + 1)).length + 420) + 1,
      RunsTo v gProg (lpU (xIn G k q) (Ao G k q (t + 1)) (Bo G k q (t + 1))) (Ao G k q (t + 2)) tm) ∧
    ∀ o tm, RunsTo v gProg (lpU (xIn G k q) (Ao G k q (t + 1)) (Bo G k q (t + 1))) o tm →
      o = Ao G k q (t + 2) := by
  have hs := sizes G k q
  unfold vB at hBv
  generalize (xIn G k q).length + maxEntry (xIn G k q) + 1 = X at hs hBv
  obtain ⟨hX3, hX23, hX2⟩ := X_pow hs
  obtain ⟨hb1, -, -⟩ := bv_facts hs.one hBv
  have hQ := hs.QX
  have hAl := length_answers G k q
  have hgl : glW G ≤ X := by unfold glW; have := hs.len; omega
  have hidx : idxS (q * n) t = t := by simp [idxS, ht]
  have hb : ansS G k q t = (answers G k q).getD t [] := by rw [ansS, hidx]
  have hin : lpU (xIn G k q) (Ao G k q (t + 1)) (Bo G k q (t + 1)) =
      1 :: (stS G k q t).length :: (stS G k q t ++ ((ansS G k q t).length :: ansS G k q t)) := by
    simp only [Ao, Bo]
    rw [lpU_round' _ _ _ _ _ _ ⟨_, stS_cons G k q t⟩]
    simp [tagS, winS, ht]
  rw [hin]
  have htake := take_succ_getD (answers G k q) (t := t) (by omega)
  obtain ⟨hS1, hS2⟩ := stS_bound hs (t := t + 1) (by omega)
  obtain ⟨hS3, hS4⟩ := stS_bound hs (t := t) (by omega)
  obtain ⟨hb1', hb2'⟩ := ansS_bound hs t
  have hLX := hs.LX
  have hst1 : stState n k q (t + 1) (glW G) (famF G k q) ((answers G k q).take t ++ [ansS G k q t]) =
      stS G k q (t + 1) := by rw [hb, htake]; rfl
  set ext : String → ℕ := fun s => if s = "x" then (stS G k q (t + 1)).length else 0 with hext
  obtain ⟨σ', r, ho⟩ := glue_mid (B := Bv) (n := n) (k := k) (q := q) (j := t) (gl := glW G)
    (F := famF G k q) (A := (answers G k q).take t) (b := ansS G k q t) ext (length_famF G k q)
    (by simp; omega) hn ht (by rw [hst1]; simp [hext]) (by rw [hst1]; omega)
    (fun y hy => by
      rcases List.mem_append.mp hy with h | h
      · have := hS4 y h; omega
      · rcases List.mem_cons.mp h with h | h
        · omega
        · have := hb2' y h; omega)
  have hu' : ∀ y ∈ 1 :: (stS G k q t).length :: (stS G k q t ++ ((ansS G k q t).length :: ansS G k q t)),
      y < Bv := by
    intro y hy
    rcases List.mem_cons.mp hy with h | h
    · omega
    rcases List.mem_cons.mp h with h | h
    · omega
    rcases List.mem_append.mp h with h | h
    · have := hS4 y h; omega
    · rcases List.mem_cons.mp h with h | h
      · omega
      · have := hb2' y h; omega
  obtain ⟨h1, h2⟩ := glue_runsTo glue_ok (B := Bv) (v := v) (ext := ext) (by omega) hS hu' r
  have hout : σ'.out = Ao G k q (t + 2) := by
    rw [ho, hst1]
    simp only [Ao]
    have hi : idxS (q * n) (t + 1) < (famF G k q).length + (t + 1) := by
      rw [length_famF]; unfold idxS; split_ifs <;> omega
    rw [show (answers G k q).take t ++ [ansS G k q t] = (answers G k q).take (t + 1) by rw [hb, htake]]
    rw [show midIdx n q t = idxS (q * n) (t + 1) from rfl, getD_append_take _ _ hi]
    rfl
  rw [hout] at h1 h2
  rw [hst1] at h1
  obtain ⟨tm, htm, hrun⟩ := h1
  exact ⟨⟨tm, le_trans htm (by simp only [Layout.const]; omega), hrun⟩, h2⟩

set_option maxHeartbeats 4000000 in
/-- **The final round.** -/
theorem script_fin {G : PartialGraph (Fin n)} {k q v Bv : ℕ} (hq : 1 ≤ q)
    (hBv : vB G k q ≤ Bv) (hS : gsz * Bv ≤ 2 ^ v) :
    (∃ tm ≤ 10 * (readCost n (maxTreeSize G k q) n (toWord (answers G k q)).length +
        finalCost n k q (maxTreeSize G k q) (q * n) (radius k q 1) + 20) + 1,
      RunsTo v gProg (lpU (xIn G k q) (Ao G k q (q * n + 1)) (Bo G k q (q * n + 1)))
        (0 :: toWord (stp G k q)) tm) ∧
    ∀ o tm, RunsTo v gProg (lpU (xIn G k q) (Ao G k q (q * n + 1)) (Bo G k q (q * n + 1))) o tm →
      o = 0 :: toWord (stp G k q) := by
  have hs := sizes G k q
  unfold vB at hBv
  generalize (xIn G k q).length + maxEntry (xIn G k q) + 1 = X at hs hBv
  obtain ⟨hX3, hX23, hX2⟩ := X_pow hs
  obtain ⟨hb1, hb2, hb3⟩ := bv_facts hs.one hBv
  have hQ := hs.QX
  have hAl := length_answers G k q
  have hlen := hs.len
  have hgl : glW G ≤ X := by unfold glW; omega
  have htake : (answers G k q).take (q * n) = answers G k q := List.take_of_length_le (by omega)
  have hxt : (xIn G k q).take (glW G) = (toWord G ++ [k, q]) ++ toWord (distMatrix G) := by
    rw [xIn_eq, glW, List.take_left' (by simp; omega)]
  have hin : lpU (xIn G k q) (Ao G k q (q * n + 1)) (Bo G k q (q * n + 1)) =
      2 :: (stS G k q (q * n)).length :: ((toWord G ++ [k, q]) ++ toWord (distMatrix G) ++
        stState n k q (q * n) (glW G) (famF G k q) (answers G k q) ++
        ((ansS G k q (q * n)).length :: ansS G k q (q * n))) := by
    simp only [Ao, Bo]
    rw [lpU_round' _ _ _ _ _ _ ⟨_, stS_cons G k q _⟩]
    simp only [tagS, winS, lt_irrefl, if_false, hxt]
    rw [stS, htake]; simp
  rw [hin]
  obtain ⟨hS1, hS2⟩ := stS_bound hs (t := q * n) le_rfl
  obtain ⟨hb1', hb2'⟩ := ansS_bound hs (q * n)
  have hLX := hs.LX
  have htot := hs.totA
  have htw := hs.twA
  have hR0 : radius k q 0 + 1 < Bv := by
    have : radius k q 0 ≤ rK k q := by unfold rK; omega
    omega
  have hR1 : radius k q 1 * (answers G k q).length + 1 < Bv := by
    have h1 : radius k q 1 ≤ rK k q + 1 := by unfold rK; omega
    have h2 : radius k q 1 * (answers G k q).length ≤ (rK k q + 1) * X ^ 3 :=
      Nat.mul_le_mul h1 (by omega)
    omega
  have hAe : ∀ y ∈ toWord (answers G k q), y < Bv :=
    toWord_words_lt (by omega) (fun u hu => by have := hs.ansL u hu; omega)
      (fun u hu y hy => by have := hs.ansE u hu y hy; omega)
  set ext : String → ℕ := fun s => if s = "eo" then n + 1 else if s = "et" then offL G.edge n else
    if s = "no" then n + 1 else if s = "nt" then offL G.nonEdge n else
    if s = "a" then total (answers G k q) else if s = "st" then q * n else if s = "ln" then q * n else
    if s = "rt" then q + 1 else if s = "ord" then q * n else if s = "dd" then n * n else
    if s = "dn" then n else if s = "bl" then n else 0 with hext
  have hnX := hs.nX
  have hnn : n * n < Bv := by
    have : n * n ≤ X ^ 3 := le_trans (by rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)) hX23
    omega
  obtain ⟨σ', r, ho⟩ := glue_final (B := Bv) (n := n) (k := k) (q := q) (sl := (stS G k q (q * n)).length)
    (gl := glW G) G (F := famF G k q) (b := ansS G k q (q * n)) (L := maxTreeSize G k q) ext
    (famF_bound hs).1 hs.ansL hq (by simp [hext]) (by simp [hext]) (by simp [hext]) (by simp [hext])
    (by simp [hext]) (by simp [hext]; omega) (by simp [hext]; omega) (by simp [hext])
    (by simp [hext]; omega) (by simp [hext]) (by simp [hext]) (by simp [hext])
    ⟨by omega, fun u hu y hy => by have := hs.ansE u hu y hy; omega, by omega⟩ (by omega) hnn
    (by have := hs.offE; omega) (by have := hs.offN; omega) (by rw [length_famF]; omega) (by omega)
    (by omega) hAe hR0 (by omega) hR1 (by omega)
  have hu' : ∀ y ∈ 2 :: (stS G k q (q * n)).length :: ((toWord G ++ [k, q]) ++ toWord (distMatrix G) ++
      stState n k q (q * n) (glW G) (famF G k q) (answers G k q) ++
      ((ansS G k q (q * n)).length :: ansS G k q (q * n))), y < Bv := by
    have hst : stState n k q (q * n) (glW G) (famF G k q) (answers G k q) = stS G k q (q * n) := by
      rw [stS, htake]
    rw [hst]
    intro y hy
    rcases List.mem_cons.mp hy with h | h
    · omega
    rcases List.mem_cons.mp h with h | h
    · omega
    rcases List.mem_append.mp h with h | h
    · rcases List.mem_append.mp h with h | h
      · have := hs.ent y (by rw [xIn_eq]; exact List.mem_append_left _ h); omega
      · have := hS2 y h; omega
    · rcases List.mem_cons.mp h with h | h
      · omega
      · have := hb2' y h; omega
  obtain ⟨h1, h2⟩ := glue_runsTo glue_ok (B := Bv) (v := v) (ext := ext) (by omega) hS hu' r
  rw [ho] at h1 h2
  obtain ⟨tm, htm, hrun⟩ := h1
  refine ⟨⟨tm, le_trans htm ?_, hrun⟩, h2⟩
  rw [length_famF, length_answers]
  simp only [Layout.const]; omega

end Lax185574Proofs.StpRam
