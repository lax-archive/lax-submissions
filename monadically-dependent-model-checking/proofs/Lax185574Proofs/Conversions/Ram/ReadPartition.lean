import Lax185574Proofs.Conversions.Ram.Encode
import Lax185574Proofs.Words.FinsetRead

/-!
Reading a partition of `Fin n` into labels.

The word of a partition lists its parts, each part as its size followed
by the frames of its members in increasing order. So the first member
of a part is its least vertex. `readPartition dst` reads the word and
stores into entry `u` of `dst` the least vertex of the part of `u`. It
uses the scalars `pc`, `i`, `fl`, `k`, `e`, `x1`, `x` and `f`.
-/

namespace Lax185574Proofs.Conversions.Ram

open Lax808846Proofs.Imp Lax808846Proofs.Reasoning Lax185574Proofs.Words
open Lax185574.WordEncoding Lax185574.Partitions

/-- The least vertex recorded in the word of a part: its third entry. -/
def repOf (w : List ℕ) : ℕ := w.getD 2 0

/-- Read one element frame of a part and label the element. -/
def readPartElem (dst : String) : Com :=
  .seq (.read "x1") (.seq (.read "x")
    (.seq (.ite (.eq (.var "e") (.lit 0)) (.assign "f" (.var "x")) .skip)
      (.store dst (.var "x") (.var "f"))))

/-- Read the frame of one part. -/
def readPart (dst : String) : Com :=
  .seq (.read "fl") (.seq (.read "k") (forUp "e" (.var "k") (readPartElem dst)))

/-- Read a partition into the labels `dst`. -/
def readPartition (dst : String) : Com :=
  .seq (.read "pc") (forUp "i" (.var "pc") (readPart dst))

variable {n : ℕ}

theorem readPart_run {B : ℕ} (Q : Setoid (Fin n)) {r : ℕ} (hr : r < n) (hq : repN Q r = r)
    {rest : List ℕ} {τ : Env} {dst : String}
    (hinp : τ.inp = (partWord n (repN Q) r).length :: partWord n (repN Q) r ++ rest)
    (hlen : (τ.arrs dst).length = n) (hB : 2 * n + 2 < B) :
    ∃ τ', Run B (readPart dst) τ τ' (20 * n + 10) ∧ τ'.inp = rest ∧
      (τ'.arrs dst).length = n ∧
      ∀ u, (τ'.arrs dst)[u]? = if u ∈ members n (repN Q) r then some r else (τ.arrs dst)[u]? := by
  set mem := members n (repN Q) r with hmem
  obtain ⟨t, ht⟩ := members_eq_cons Q hr hq
  have hmemn : ∀ u ∈ mem, u < n := fun u hu => (mem_below.mp hu).1
  have hml : mem.length ≤ n := length_below_le n _
  have hpw : partWord n (repN Q) r = mem.length :: elemFrames mem := rfl
  have hinp2 : τ.inp = (1 + 2 * mem.length) :: mem.length :: (elemFrames mem ++ rest) := by
    rw [hinp, hpw]; simp [length_elemFrames]; ring
  set τa : Env := { τ.setVar "fl" (1 + 2 * mem.length) with
      inp := mem.length :: (elemFrames mem ++ rest) } with hτa
  set τ1 : Env := { τa.setVar "k" mem.length with inp := elemFrames mem ++ rest } with hτ1
  have hr1 : Run B (.read "fl") τ τa 1 := Run.read hinp2
  have hr2 : Run B (.read "k") τa τ1 1 := Run.read (by simp [hτa])
  let I : ℕ → Env → Prop := fun e ρ =>
    ρ.inp = elemFrames (mem.drop e) ++ rest ∧ ρ.vars "k" = mem.length ∧
      (0 < e → ρ.vars "f" = r) ∧ (ρ.arrs dst).length = n ∧
      ∀ u, (ρ.arrs dst)[u]? = if u ∈ mem.take e then some r else (τ.arrs dst)[u]?
  obtain ⟨ρ, hrl, ⟨hinp', -, -, hlen', hg'⟩, -⟩ :=
    forUp_run (B := B) (i := "e") (e := .var "k") (body := readPartElem dst) (N := mem.length)
      (K := 12) I (by omega)
      (fun k _ ρ hI _ => by rw [evalB_var (by rw [hI.2.1]; omega), hI.2.1])
      (σ := τ1) ⟨by simp [hτ1], by simp [hτ1], fun h => absurd h (by omega),
        by simp [hτ1, hτa, hlen], fun u => by simp [hτ1, hτa]⟩
      (by
        rintro e he ρ ⟨hi, hk, hf, hl, hg⟩ hee
        have hel : e < mem.length := he
        have hinpe : ρ.inp = 1 :: mem[e] :: (elemFrames (mem.drop (e + 1)) ++ rest) := by
          rw [hi, List.drop_eq_getElem_cons hel, elemFrames_cons]; rfl
        have hxe := hmemn _ (List.getElem_mem hel)
        have hm0 : mem[0]'(by omega) = r := by simp [hmem, ht]
        set ρ1 : Env := { ρ.setVar "x1" 1 with inp := mem[e] :: (elemFrames (mem.drop (e + 1)) ++
          rest) } with hρ1
        set ρ2 : Env := { ρ1.setVar "x" mem[e] with inp := elemFrames (mem.drop (e + 1)) ++ rest }
          with hρ2
        have hr2a : Run B (.read "x1") ρ ρ1 1 := Run.read hinpe
        have hr2b : Run B (.read "x") ρ1 ρ2 1 := Run.read (by simp [hρ1])
        have hev : (Cond.eq (.var "e") (.lit 0)).evalB B ρ2 = some (decide (e = 0)) := by
          rw [eq_lit_evalB (by simp [hρ2, hρ1, hee]; omega) (by omega)]; simp [hρ2, hρ1, hee]
        set ρ3 : Env := if e = 0 then ρ2.setVar "f" mem[e] else ρ2 with hρ3
        have hr3 : Run B (.ite (.eq (.var "e") (.lit 0)) (.assign "f" (.var "x")) .skip) ρ2 ρ3 6 := by
          by_cases h0 : e = 0
          · rw [hρ3, if_pos h0]
            exact (Run.ite_true (by rw [hev]; simp [h0]) (Run.assign (by simp [hρ2, hρ1]; omega))).mono
              (by simp)
          · rw [hρ3, if_neg h0]
            exact (Run.ite_false (by rw [hev]; simp [h0]) Run.skip).mono (by simp)
        have hf3 : ρ3.vars "f" = r := by
          by_cases h0 : e = 0
          · subst h0; simp [hρ3, hm0]
          · simp [hρ3, h0, hρ2, hρ1]; exact hf (by omega)
        have hx3 : ρ3.vars "x" = mem[e] := by by_cases h0 : e = 0 <;> simp [hρ3, h0, hρ2, hρ1]
        have ha3 : ρ3.arrs dst = ρ.arrs dst := by by_cases h0 : e = 0 <;> simp [hρ3, h0, hρ2, hρ1]
        have hinp3 : ρ3.inp = elemFrames (mem.drop (e + 1)) ++ rest := by
          by_cases h0 : e = 0 <;> simp [hρ3, h0, hρ2, hρ1]
        have he3 : ρ3.vars "e" = e := by by_cases h0 : e = 0 <;> simp [hρ3, h0, hρ2, hρ1, hee]
        have hk3 : ρ3.vars "k" = mem.length := by by_cases h0 : e = 0 <;> simp [hρ3, h0, hρ2, hρ1, hk]
        refine ⟨ρ3.setArr dst mem[e] r, (Run.seq hr2a (Run.seq hr2b (Run.seq hr3 (Run.store
          (idx := mem[e]) (v := r) (by simp [hx3]; omega) (by simp [hf3]; omega)
          (by rw [ha3, hl]; exact hxe))))).mono
          (by simp), by simp [he3], by simp [hinp3], by simp [hk3], fun _ => by simp [hf3],
          by simp [ha3, hl], fun u => ?_⟩
        have htk : mem.take (e + 1) = mem.take e ++ [mem[e]] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hel]; rfl
        simp only [arrs_setVar, arrs_setArr, if_true, ha3, List.getElem?_set, hg u, hl, htk]
        by_cases hu : mem[e] = u
        · subst hu
          have : mem[e] ∈ mem.take (e + 1) := List.mem_iff_getElem.mpr ⟨e, by simp; omega, by simp⟩
          simp [hxe, this]
        · have : (u ∈ mem.take (e + 1)) ↔ (u ∈ mem.take e) := by
            simp only [htk, List.mem_append, List.mem_singleton]
            exact ⟨fun h => h.resolve_right (fun h' => hu h'.symm), Or.inl⟩
          simp [hu, this])
  refine ⟨ρ, (Run.seq hr1 (Run.seq hr2 hrl)).mono ?_, ?_, hlen', fun u => ?_⟩
  · simp; nlinarith
  · rw [hinp', List.drop_length]; rfl
  · rw [hg' u, List.take_length]

theorem repOf_partWord (Q : Setoid (Fin n)) {r : ℕ} (hr : r < n) (hq : repN Q r = r) :
    repOf (partWord n (repN Q) r) = r := by
  obtain ⟨t, ht⟩ := partWord_eq_cons Q hr hq
  rw [ht]; rfl

theorem toWord_setoid_words (Q : Setoid (Fin n)) :
    toWord Q = (partsList n (repN Q)).length :: frames (partsList n (repN Q)) := by
  change toWord (Finset.words (parts Q)) = _
  rw [toWord_words, words_parts]

/-- **Reading a partition.** Afterwards entry `u` of `dst` is the least
vertex of the part of `u`. -/
theorem readPartition_run {B : ℕ} (Q : Setoid (Fin n)) {rest : List ℕ} {τ : Env} {dst : String}
    (hinp : τ.inp = toWord Q ++ rest) (hlen : (τ.arrs dst).length = n) (hB : 2 * n + 2 < B) :
    ∃ τ', Run B (readPartition dst) τ τ' (n * (20 * n + 18) + 7) ∧ τ'.inp = rest ∧
      Vec τ' dst n (repN Q) := by
  set ws := partsList n (repN Q) with hws
  have hwl : ws.length ≤ n := by rw [hws, length_partsList]; exact length_below_le n _
  rw [toWord_setoid_words] at hinp
  set τ1 : Env := { τ.setVar "pc" ws.length with inp := frames ws ++ rest } with hτ1
  have hr1 : Run B (.read "pc") τ τ1 1 := Run.read (by rw [hinp]; rfl)
  let I : ℕ → Env → Prop := fun i ρ =>
    ρ.inp = frames (ws.drop i) ++ rest ∧ ρ.vars "pc" = ws.length ∧ (ρ.arrs dst).length = n ∧
      ∀ u < n, (ρ.arrs dst)[u]? =
        if repN Q u ∈ (ws.take i).map repOf then some (repN Q u) else (τ.arrs dst)[u]?
  obtain ⟨ρ, hrl, ⟨hinpf, -, hl', hg'⟩, -⟩ :=
    forUp_run (B := B) (i := "i") (e := .var "pc") (body := readPart dst) (N := ws.length)
      (K := 20 * n + 10) I (by omega)
      (fun k _ ρ hI _ => by rw [evalB_var (by rw [hI.2.1]; omega), hI.2.1])
      (σ := τ1) ⟨by simp [hτ1], by simp [hτ1], by simp [hτ1, hlen], fun u _ => by simp [hτ1]⟩
      (by
        rintro i hi ρ ⟨hinpρ, hpc, hl, hg⟩ hii
        obtain ⟨r, hr, hq, hwi⟩ := (mem_partsList Q).mp (List.getElem_mem hi)
        have hinpi : ρ.inp = (partWord n (repN Q) r).length :: partWord n (repN Q) r ++
            (frames (ws.drop (i + 1)) ++ rest) := by
          rw [hinpρ, frames_drop hi, ← hwi]; simp
        obtain ⟨ρ', hr', hinp', hl', hg'⟩ := readPart_run (B := B) Q hr hq hinpi hl hB
        have hfr : ∀ y, y ∉ ["fl", "k", "e", "x1", "x", "f"] → ρ'.vars y = ρ.vars y := fun y hy =>
          hr'.frame_var y (by
            simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hy
            simp [readPart, readPartElem, forUp, Com.wvars, hy.1, hy.2.1, hy.2.2.1, hy.2.2.2.1,
              hy.2.2.2.2.1, hy.2.2.2.2.2])
        refine ⟨ρ', hr', by rw [hfr "i" (by decide), hii], by simp [hinp'],
          by simp [hfr "pc" (by decide), hpc], by simp [hl'], fun u hu => ?_⟩
        simp only [arrs_setVar, hg' u, hg u hu]
        have htk : (ws.take (i + 1)).map repOf = (ws.take i).map repOf ++ [r] := by
          rw [List.take_add_one, List.getElem?_eq_getElem hi, Option.toList_some, List.map_append,
            List.map_singleton, hwi, repOf_partWord Q hr hq]
        have hmu : u ∈ members n (repN Q) r ↔ repN Q u = r := by
          simp only [members, mem_below]; exact ⟨fun h => h.2, fun h => ⟨hu, h⟩⟩
        rw [htk]
        by_cases h1 : repN Q u = r
        · simp [hmu.mpr h1, h1]
        · simp [hmu, h1])
  refine ⟨ρ, (Run.seq hr1 hrl).mono (by simp; nlinarith), ?_, ⟨hl', fun u hu => ?_⟩⟩
  · rw [hinpf, List.drop_length]; rfl
  · rw [hg' u hu, List.take_length, if_pos]
    refine List.mem_map.mpr ⟨partWord n (repN Q) (repN Q u), ?_, ?_⟩
    · exact (mem_partsList Q).mpr ⟨_, repN_lt Q hu, repN_repN Q hu, rfl⟩
    · exact repOf_partWord Q (repN_lt Q hu) (repN_repN Q hu)

end Lax185574Proofs.Conversions.Ram
