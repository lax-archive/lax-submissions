import Lax185574Proofs.RamExec

/-!
The cells of a simulation, loading and storing simulated cells, and
reading the rewritten input of the simulated program through a table of
segments.
-/

namespace Lax185574Proofs.RamSim

open Lax808846.Ram Lax808846Proofs.Machine Lax185574Proofs.RamExec

variable {w : ℕ} {p : Program}

/-! ### Layout -/

scoped notation "rZ" => (0 : ℕ)
scoped notation "rOne" => (1 : ℕ)
scoped notation "rMask" => (2 : ℕ)
scoped notation "rBase" => (3 : ℕ)
scoped notation "rCur" => (4 : ℕ)
scoped notation "rTot" => (5 : ℕ)
scoped notation "rOB" => (6 : ℕ)
scoped notation "rOC" => (7 : ℕ)
scoped notation "rCap" => (8 : ℕ)
scoped notation "rT" => (9 : ℕ)
scoped notation "rB" => (10 : ℕ)
scoped notation "rC" => (11 : ℕ)
scoped notation "rR" => (12 : ℕ)
scoped notation "rD" => (13 : ℕ)
scoped notation "rU" => (14 : ℕ)

/-- The fixed cells of a simulation: constants zero and one, the mask
`2 ^ v - 1` and the base of the simulated memory. -/
structure Env (w v base : ℕ) (S : State) : Prop where
  word : WordMem w S.mem
  zero : S.mem rZ = 0
  one : S.mem rOne = 1
  mask : S.mem rMask = 2 ^ v - 1
  baseCell : S.mem rBase = base
  room : base + 2 ^ v ≤ 2 ^ w
  low : 16 ≤ base
  hv : v ≤ w

theorem Env.hw {w v base : ℕ} {S : State} (h : Env w v base S) : 16 < 2 ^ w := by
  have := h.room; have := h.low; have : 0 < 2 ^ v := by positivity
  omega

theorem land_mask (x v : ℕ) : Nat.land x (2 ^ v - 1) = x % 2 ^ v :=
  Nat.and_two_pow_sub_one_eq_mod x v

/-- The address of simulated cell `a` into `rT`. -/
def addrCode (a : ℕ) : Program := [.set rT a, .and rT rT rMask, .add rT rT rBase]

/-- Load simulated cell `a` into the cell `V`. -/
def ldCode (V a : ℕ) : Program := addrCode a ++ [.load V rT]

theorem ld_spec {v base V a A : ℕ} {S : State} (E : Env w v base S)
    (hf : Fits p A (ldCode V a)) (hpc : S.pc = A) (hV : V < 2 ^ w) :
    Exec w p 4 S { S with
      pc := A + 4
      mem := Function.update (Function.update S.mem rT (base + a % 2 ^ v)) V
        (S.mem (base + a % 2 ^ v)) } := by
  have hw := E.hw
  have hm := E.word
  have hav : a % 2 ^ v < 2 ^ v := Nat.mod_lt _ (by positivity)
  have room := E.room
  have low := E.low
  have e1 := (x_set (fetch hf (i := 0) (by simp [hpc]) rfl) (by omega)).trans
    (x_and (fetch hf (i := 1) (by simp [hpc]) rfl) (hm.update _ (Nat.mod_lt _ (by positivity)))
      (by omega) (by omega) (by omega))
  have e2 := e1.trans
    (x_add (fetch hf (i := 2) (by simp [hpc]) rfl) (by omega) (by omega) (by omega))
  refine (e2.trans
    (x_load (fetch hf (i := 3) (by simp [hpc]) rfl) (hm.exec e2) hV (by omega))).of_eq ?_
  simp only [State.mk.injEq, hpc, true_and, and_true]
  have h2 : (2 : ℕ) ≠ 9 := by decide
  have h3 : (3 : ℕ) ≠ 9 := by decide
  simp only [Function.update_idem, Function.update_self, Function.update_of_ne h2,
    Function.update_of_ne h3, E.mask, E.baseCell]
  rw [land_mask, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 E.hv),
    Nat.mod_eq_of_lt (by omega : a % 2 ^ v + base < 2 ^ w), Nat.add_comm]
  congr 1
  rw [Function.update_of_ne (by omega)]

/-- Store the cell `V` into simulated cell `a`. -/
def stCode (a V : ℕ) : Program := addrCode a ++ [.store rT V]

theorem st_spec {v base V a A : ℕ} {S : State} (E : Env w v base S)
    (hf : Fits p A (stCode a V)) (hpc : S.pc = A) (hV : V < 2 ^ w) (hVT : V ≠ rT) :
    Exec w p 4 S { S with
      pc := A + 4
      mem := Function.update (Function.update S.mem rT (base + a % 2 ^ v)) (base + a % 2 ^ v)
        (S.mem V) } := by
  have hw := E.hw
  have hm := E.word
  have hav : a % 2 ^ v < 2 ^ v := Nat.mod_lt _ (by positivity)
  have room := E.room
  have low := E.low
  have e1 := (x_set (fetch hf (i := 0) (by simp [hpc]) rfl) (by omega)).trans
    (x_and (fetch hf (i := 1) (by simp [hpc]) rfl) (hm.update _ (Nat.mod_lt _ (by positivity)))
      (by omega) (by omega) (by omega))
  have e2 := e1.trans
    (x_add (fetch hf (i := 2) (by simp [hpc]) rfl) (by omega) (by omega) (by omega))
  refine (e2.trans
    (x_store (fetch hf (i := 3) (by simp [hpc]) rfl) (hm.exec e2) (by omega) hV)).of_eq ?_
  simp only [State.mk.injEq, hpc, true_and, and_true]
  have h2 : (2 : ℕ) ≠ 9 := by decide
  have h3 : (3 : ℕ) ≠ 9 := by decide
  simp only [Function.update_idem, Function.update_self, Function.update_of_ne h2,
    Function.update_of_ne h3, E.mask, E.baseCell, Function.update_of_ne hVT]
  rw [land_mask, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow 2 E.hv),
    Nat.mod_eq_of_lt (by omega : a % 2 ^ v + base < 2 ^ w), Nat.add_comm]

/-! ### Reading the rewritten input

The rewritten input is a concatenation of segments. A segment is a
single precomputed value, a slice of the machine's input, or a slice of
a memory region whose base address is held by a cell `bc`. Segment `k`
is described by two table cells: its length at `tb + 2 k` and its value
or start at `tb + 2 k + 1`. -/

inductive SegKind
  | val
  | input
  | mem (bc : ℕ)

/-- Fetch entry `rD` of the segment described at `tb` into `rR`. -/
def fetchCode (tb : ℕ) : SegKind → Program
  | .val => [.add rR (tb + 1) rZ]
  | .input => [.add rT (tb + 1) rD, .inputLoad rR rT]
  | .mem bc => [.add rT (tb + 1) rD, .add rT rT bc, .load rR rT]

theorem fetchCode_length (tb tb' : ℕ) (k : SegKind) :
    (fetchCode tb k).length = (fetchCode tb' k).length := by
  cases k <;> rfl

theorem fetchCode_length_le (tb : ℕ) (k : SegKind) : (fetchCode tb k).length ≤ 3 := by
  cases k <;> simp [fetchCode]

/-- Walk the segments, subtracting their lengths from `rD`, until the
segment holding entry `rD` is found. Past the last segment the entry
is zero. `E` is the address after the chain. -/
def chainCode : List SegKind → ℕ → ℕ → ℕ → Program
  | [], _, _, _ => [.set rR 0]
  | k :: ks, tb, A, E =>
      [.sub rU tb rD, .jzero rU (A + 3 + (fetchCode tb k).length)] ++ fetchCode tb k ++
        [.jump E, .sub rD rD tb] ++ chainCode ks (tb + 2) (A + 4 + (fetchCode tb k).length) E

def chainLen : List SegKind → ℕ
  | [] => 1
  | k :: ks => 4 + (fetchCode 0 k).length + chainLen ks

theorem chainCode_length (ks : List SegKind) (tb A E : ℕ) :
    (chainCode ks tb A E).length = chainLen ks := by
  induction ks generalizing tb A with
  | nil => rfl
  | cons k ks ih =>
      simp only [chainCode, chainLen, List.length_append, List.length_cons, List.length_nil, ih,
        fetchCode_length tb 0 k]
      omega

theorem chainLen_le (ks : List SegKind) : chainLen ks ≤ 7 * ks.length + 1 := by
  induction ks with
  | nil => simp [chainLen]
  | cons k ks ih => have := fetchCode_length_le 0 k; simp only [chainLen, List.length_cons]; omega

/-- Segment `seg` of kind `k`, described by `len` and `st`, is correct in
`S`, and the cells it is read from avoid `Q`. -/
def SegOK (w : ℕ) (Q : ℕ → Prop) (S : State) (len st : ℕ) (seg : List ℕ) : SegKind → Prop
  | .val => len = 1 ∧ ∃ u, seg = [u] ∧ st = u % 2 ^ w
  | .input => seg = (S.input.drop st).take len ∧ (0 < len → st + len ≤ S.input.length) ∧
      S.input.length < 2 ^ w
  | .mem bc => seg.length = len ∧ (0 < len → S.mem bc + st + len ≤ 2 ^ w) ∧ bc < 2 ^ w ∧ ¬ Q bc ∧
      ∀ d < len, S.mem (S.mem bc + st + d) = seg.getD d 0 % 2 ^ w ∧
        ¬ Q (S.mem bc + st + d)

/-- The segment table at `tb` describes `segs`. -/
def TableOK (w : ℕ) (Q : ℕ → Prop) (S : State) : List SegKind → ℕ → List (List ℕ) → Prop
  | [], _, [] => True
  | k :: ks, tb, seg :: segs => ¬ Q tb ∧ ¬ Q (tb + 1) ∧
      SegOK w Q S (S.mem tb) (S.mem (tb + 1)) seg k ∧ TableOK w Q S ks (tb + 2) segs
  | _, _, _ => False

theorem SegOK.length {Q : ℕ → Prop} {S : State} {len st : ℕ} {seg : List ℕ} {k : SegKind}
    (h : SegOK w Q S len st seg k) : seg.length = len := by
  cases k with
  | val => obtain ⟨rfl, u, rfl, -⟩ := h; rfl
  | input =>
      obtain ⟨rfl, h1, -⟩ := h
      simp only [List.length_take, List.length_drop]
      rcases Nat.eq_zero_or_pos len with h0 | h0
      · omega
      · have := h1 h0; omega
  | mem bc => exact h.1

theorem SegOK.frame {Q : ℕ → Prop} {S S' : State} {len st : ℕ} {seg : List ℕ} {k : SegKind}
    (h : SegOK w Q S len st seg k) (hQ : ∀ a, ¬ Q a → S'.mem a = S.mem a)
    (hi : S'.input = S.input) : SegOK w Q S' len st seg k := by
  cases k with
  | val => exact h
  | input => simpa only [SegOK, hi] using h
  | mem bc =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      refine ⟨h1, fun h => by rw [hQ _ h4]; exact h2 h, h3, h4, fun d hd => ?_⟩
      rw [hQ _ h4]
      obtain ⟨h6, h7⟩ := h5 d hd
      exact ⟨by rw [hQ _ h7]; exact h6, h7⟩

theorem TableOK.frame {Q : ℕ → Prop} {S S' : State} {ks : List SegKind} {tb : ℕ}
    {segs : List (List ℕ)} (h : TableOK w Q S ks tb segs)
    (hQ : ∀ a, ¬ Q a → S'.mem a = S.mem a) (hi : S'.input = S.input) :
    TableOK w Q S' ks tb segs := by
  induction ks generalizing tb segs with
  | nil => cases segs <;> simp_all [TableOK]
  | cons k ks ih =>
      cases segs with
      | nil => simp [TableOK] at h
      | cons seg segs =>
          obtain ⟨h1, h2, h3, h4⟩ := h
          refine ⟨h1, h2, ?_, ih h4⟩
          rw [hQ _ h1, hQ _ h2]
          exact h3.frame hQ hi

theorem getD_append_flatten (seg : List ℕ) (segs : List (List ℕ)) (d : ℕ) :
    (seg :: segs).flatten.getD d 0 =
      if d < seg.length then seg.getD d 0 else segs.flatten.getD (d - seg.length) 0 := by
  rw [List.flatten_cons]
  split_ifs with h
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]

theorem fetch_spec {Q : ℕ → Prop} (hQT : Q rT) {k : SegKind} {tb A len st d : ℕ}
    {seg : List ℕ} {S : State}
    (hm : WordMem w S.mem) (hz : S.mem rZ = 0) (hw : 16 < 2 ^ w)
    (hS : SegOK w Q S len st seg k) (htb : 16 ≤ tb) (htbw : tb + 1 < 2 ^ w)
    (hlen : S.mem tb = len) (hst : S.mem (tb + 1) = st) (hd : S.mem rD = d) (hdl : d < len)
    (hf : Fits p A (fetchCode tb k)) (hpc : S.pc = A) :
    ∃ m, Exec w p (fetchCode tb k).length S
      { S with pc := A + (fetchCode tb k).length, mem := m } ∧
      m rR = seg.getD d 0 % 2 ^ w ∧ ∀ a, a ≠ rR → a ≠ rT → m a = S.mem a := by
  cases k with
  | val =>
      obtain ⟨hl1, u, rfl, hu⟩ := hS
      refine ⟨_, (x_add (fetch hf (i := 0) (by simp [hpc]) rfl) (by omega) (by omega)
        (by omega)).at_pc (by simp [hpc, fetchCode]), ?_, ?_⟩
      · have : d = 0 := by omega
        subst this
        simp [hst, hz, hu]
      · intro a ha _
        simp [Function.update_of_ne ha]
  | input =>
      obtain ⟨rfl, h1, h2⟩ := hS
      have h1 := h1 (by omega)
      have e1 := x_add (w := w) (s := S) (fetch hf (i := 0) (by simp [hpc]) rfl) (by omega) (by omega)
        (by omega)
      have e2 := e1.trans (x_inputLoad (fetch hf (i := 1) (by simp [hpc]) rfl)
        (hm.exec e1) (by omega) (by omega))
      refine ⟨_, e2.at_pc (A := A + 2) (by simp [hpc]), ?_, ?_⟩
      · have hlt : st + d < 2 ^ w := by omega
        simp only [Function.update_self, ne_eq, show (12 : ℕ) ≠ 9 by decide, not_false_eq_true,
          Function.update_of_ne, hst, hd, Nat.mod_eq_of_lt hlt]
        congr 1
        simp only [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hdl,
          List.getElem?_drop]
      · intro a ha hb
        simp [Function.update_of_ne ha, Function.update_of_ne hb]
  | mem bc =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := hS
      have h2 := h2 (by omega)
      obtain ⟨h6, h7⟩ := h5 d hdl
      have hbc : bc ≠ rT := fun h => h4 (h ▸ hQT)
      have hdat : S.mem bc + st + d ≠ rT := fun h => h7 (h ▸ hQT)
      have e1 := x_add (w := w) (s := S) (fetch hf (i := 0) (by simp [hpc]) rfl) (by omega) (by omega)
        (by omega)
      have e2 := e1.trans (x_add (fetch hf (i := 1) (by simp [hpc]) rfl) (by omega) (by omega)
        h3)
      have e3 := e2.trans (x_load (fetch hf (i := 2) (by simp [hpc]) rfl)
        (hm.exec e2) (by omega) (by omega))
      refine ⟨_, e3.at_pc (A := A + 3) (by simp [hpc]), ?_, ?_⟩
      · have hlt : st + d < 2 ^ w := by omega
        have hlt' : st + d + S.mem bc < 2 ^ w := by omega
        simp only [Function.update_self, ne_eq, show (12 : ℕ) ≠ 9 by decide, not_false_eq_true,
          Function.update_of_ne, hst, hd, Nat.mod_eq_of_lt hlt, Function.update_of_ne hbc,
          Nat.mod_eq_of_lt hlt']
        rw [show st + d + S.mem bc = S.mem bc + st + d by omega]
        simp [Function.update_of_ne hdat, h6]
      · intro a ha hb
        simp [Function.update_of_ne ha, Function.update_of_ne hb]

theorem chain_spec {Q : ℕ → Prop} (hQ : Q rR ∧ Q rT ∧ Q rU ∧ Q rD) {ks : List SegKind}
    {tb A E : ℕ} {segs : List (List ℕ)} {S : State}
    (hm : WordMem w S.mem) (hz : S.mem rZ = 0) (hw : 16 < 2 ^ w)
    (hT : TableOK w Q S ks tb segs) (htb : 16 ≤ tb) (htbw : tb + 2 * ks.length < 2 ^ w)
    (hf : Fits p A (chainCode ks tb A E)) (hpc : S.pc = A) (hE : E = A + chainLen ks) :
    ∃ n m, n ≤ 6 * ks.length + 1 ∧ Exec w p n S { S with pc := E, mem := m } ∧
      m rR = segs.flatten.getD (S.mem rD) 0 % 2 ^ w ∧
      ∀ a, a ≠ rR → a ≠ rT → a ≠ rU → a ≠ rD → m a = S.mem a := by
  obtain ⟨hQR, hQT, hQU, hQD⟩ := hQ
  induction ks generalizing tb A S segs with
  | nil =>
      cases segs with
      | cons _ _ => simp [TableOK] at hT
      | nil =>
          refine ⟨1, _, le_refl _, (x_set (fetch hf (i := 0) (by simp [hpc]) rfl)
            (by omega)).at_pc (by simp [hpc, hE, chainLen]), ?_, ?_⟩
          · simp
          · intro a ha _ _ _
            simp [Function.update_of_ne ha]
  | cons k ks ih =>
      cases segs with
      | nil => simp [TableOK] at hT
      | cons seg segs =>
          obtain ⟨hn1, hn2, hseg, hT'⟩ := hT
          simp only [List.length_cons] at htbw
          have hF := fetchCode_length tb 0 k
          simp only [chainCode] at hf
          rw [fits_append, fits_append, fits_append] at hf
          obtain ⟨⟨⟨hf1, hf2⟩, hf3⟩, hf4⟩ := hf
          simp only [List.length_append, List.length_cons, List.length_nil] at hf2 hf3 hf4
          have hlen := hseg.length
          have e1 := x_sub (w := w) (s := S) (fetch hf1 (i := 0) (by simp [hpc]) rfl) hm (by omega)
            (by omega) (by omega)
          have e2 := e1.trans (x_jzero (fetch hf1 (i := 1) (by simp [hpc]) rfl) (by omega))
          by_cases hdl : S.mem tb ≤ S.mem rD
          · -- skip this segment
            have h0 : Function.update S.mem rU (S.mem tb - S.mem rD) rU = 0 := by
              simp; omega
            simp only [h0, if_true] at e2
            have e3 := e2.trans (x_sub (fetch hf3 (i := 1) (by simp; omega) rfl)
              (hm.exec e2) (by omega) (by omega) (by omega))
            set S3 := { S with
              pc := A + 3 + (fetchCode tb k).length + 1
              mem := Function.update (Function.update S.mem rU (S.mem tb - S.mem rD)) rD
                (S.mem rD - S.mem tb) } with hS3
            have e3' : Exec w p (1 + 1 + 1) S S3 := e3.of_eq (by
              simp only [hS3, State.mk.injEq, true_and]
              simp [Function.update_of_ne, show (13 : ℕ) ≠ 14 by decide,
                show tb ≠ 14 by omega])
            have hfr : ∀ a, ¬ Q a → S3.mem a = S.mem a := by
              intro a ha
              have h1 : a ≠ rD := fun h => ha (h ▸ hQD)
              have h2 : a ≠ rU := fun h => ha (h ▸ hQU)
              simp [hS3, Function.update_of_ne h1, Function.update_of_ne h2]
            obtain ⟨n, m, hn, e4, hR, hrest⟩ := ih (S := S3) (tb := tb + 2)
              (A := A + 4 + (fetchCode tb k).length) (segs := segs)
              (hm.exec e3') (by simp [hS3, hz])
              (hT'.frame hfr rfl) (by omega) (by omega)
              (hf4.congr (by omega)) (by simp [hS3]; omega) (by rw [hE, chainLen, hF]; omega)
            refine ⟨3 + n, m, by simp only [List.length_cons]; omega, (e3'.trans e4).of_eq rfl,
              ?_, ?_⟩
            · rw [hR, getD_append_flatten, if_neg (by omega), hlen]
              simp [hS3]
            · intro a h1 h2 h3 h4
              rw [hrest a h1 h2 h3 h4]
              simp [hS3, Function.update_of_ne h3, Function.update_of_ne h4]
          · -- the entry is in this segment
            have h0 : Function.update S.mem rU (S.mem tb - S.mem rD) rU ≠ 0 := by
              simp; omega
            simp only [h0, if_false] at e2
            set S2 := { S with
              pc := A + 2
              mem := Function.update S.mem rU (S.mem tb - S.mem rD) } with hS2
            have e2' : Exec w p (1 + 1) S S2 := e2.of_eq (by
              simp only [hS2, State.mk.injEq, true_and, hpc])
            have hfr : ∀ a, ¬ Q a → S2.mem a = S.mem a := by
              intro a ha
              have h2 : a ≠ rU := fun h => ha (h ▸ hQU)
              simp [hS2, Function.update_of_ne h2]
            obtain ⟨m, e3, hR, hrest⟩ := fetch_spec hQT (hm.exec e2') (by simp [hS2]; exact hz) hw
              (hseg.frame hfr rfl) htb (by omega)
              (by simp [hS2]; rw [Function.update_of_ne (by omega)])
              (by simp [hS2]; rw [Function.update_of_ne (by omega)])
              (d := S.mem rD) (by simp [hS2]) (by omega) hf2 (by simp [hS2])
            have e4 := (e2'.trans e3).trans (x_jump (fetch hf3 (i := 0) (by simp; omega) rfl))
            refine ⟨1 + 1 + (fetchCode tb k).length + 1, m, by
              have := fetchCode_length_le tb k; simp only [List.length_cons]; omega,
              e4.of_eq rfl, ?_, ?_⟩
            · rw [hR, getD_append_flatten, if_pos (by omega)]
            · intro a h1 h2 h3 h4
              rw [hrest a h1 h2]
              simp [hS2, Function.update_of_ne h3]

end Lax185574Proofs.RamSim
