/-
**The word-level block chain is the byte-level hash** (pure spec side).

`blake2s_u32s` consumes `u32` words padded to whole 64-byte blocks with
the byte counter `min nBytes (64·(i+1))`; the spec `Blake2s.hashBlocks`
consumes bytes 64 at a time, padding only the last block. With the
word list read off the zero-padded bytes (`leWord`), the chains
coincide block by block: the non-last byte counters are `t + 64`, the
last is `nBytes`, and every message-schedule function agrees
everywhere (out-of-range words are zero on both sides).
-/
import StwoVerifier.BlakeGadgets

namespace StwoVerifier.Gadgets

open StwoVerifier

/-! ### `leWord` index plumbing -/

theorem getD_drop' {α : Type} (xs : List α) (a m : ℕ) (d : α) :
    (xs.drop a).getD m d = xs.getD (a + m) d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop,
    ← List.getD_eq_getElem?_getD]

theorem leWord_oob {b : List UInt8} {k : ℕ} (h : b.length ≤ 4 * k) :
    Blake2s.leWord b k = 0 := by
  unfold Blake2s.leWord
  rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega),
    List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  rfl

theorem leWord_drop (pb : List UInt8) (i l : ℕ) :
    Blake2s.leWord (pb.drop (64 * i)) l = Blake2s.leWord pb (16 * i + l) := by
  unfold Blake2s.leWord
  rw [getD_drop', getD_drop', getD_drop', getD_drop',
    show 64 * i + 4 * l = 4 * (16 * i + l) from by ring,
    show 64 * i + (4 * l + 1) = 4 * (16 * i + l) + 1 from by ring,
    show 64 * i + (4 * l + 2) = 4 * (16 * i + l) + 2 from by ring,
    show 64 * i + (4 * l + 3) = 4 * (16 * i + l) + 3 from by ring]

theorem leWord_take {b : List UInt8} {n k : ℕ} (h : 4 * k + 4 ≤ n) :
    Blake2s.leWord (b.take n) k = Blake2s.leWord b k := by
  unfold Blake2s.leWord
  have ht : ∀ m, m < n → (b.take n).getD m 0 = b.getD m 0 := by
    intro m hm
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hm,
      ← List.getD_eq_getElem?_getD]
  rw [ht _ (by omega), ht _ (by omega), ht _ (by omega), ht _ (by omega)]

theorem leWord_replicate_zero (m k : ℕ) :
    Blake2s.leWord (List.replicate m 0) k = 0 := by
  unfold Blake2s.leWord
  have hz : ∀ j, (List.replicate m (0 : UInt8)).getD j 0 = 0 := by
    intro j
    by_cases hj : j < m <;>
      simp [List.getD_eq_getElem?_getD, List.getElem?_replicate, hj]
  rw [hz, hz, hz, hz]
  rfl

/-! ### `hashBlocks` case equations -/

theorem hashBlocks_nil (h : ℕ → Blake2s.Word) (t : ℕ) :
    Blake2s.hashBlocks h t [] = Blake2s.compress h (fun _ => 0) t true := by
  rw [Blake2s.hashBlocks]

theorem hashBlocks_last {b : List UInt8} (hne : b ≠ [])
    (hle : b.length ≤ 64) (h : ℕ → Blake2s.Word) (t : ℕ) :
    Blake2s.hashBlocks h t b
      = Blake2s.compress h
          (Blake2s.leWord (b ++ List.replicate (64 - b.length) 0))
          (t + b.length) true := by
  cases b with
  | nil => exact absurd rfl hne
  | cons x xs =>
    rw [Blake2s.hashBlocks]
    · rw [if_pos (by simpa using hle)]
    · simp

theorem hashBlocks_step {b : List UInt8} (hgt : ¬ b.length ≤ 64)
    (h : ℕ → Blake2s.Word) (t : ℕ) :
    Blake2s.hashBlocks h t b
      = Blake2s.hashBlocks
          (fun i => ((List.range 8).map
            (Blake2s.compress h (Blake2s.leWord (b.take 64)) (t + 64)
              false)).getD i 0)
          (t + 64) (b.drop 64) := by
  cases b with
  | nil => exact absurd (by simp) hgt
  | cons x xs =>
    rw [Blake2s.hashBlocks]
    · rw [if_neg (by simpa using hgt)]
    · simp

/-! ### The message-schedule functions agree -/

/-- The gadget's per-block schedule — the 16-word slice of the padded
word list — is `leWord` of the block's padded bytes, as functions. -/
theorem slice_schedule (bytes : List UInt8) (NB : ℕ)
    (hNB : bytes.length ≤ 64 * NB) (i : ℕ) (hi : i < NB) :
    (fun l => ((((List.range (16 * NB)).map
        (Blake2s.leWord
          (bytes ++ List.replicate (64 * NB - bytes.length) 0))).drop
          (16 * i)).take 16).getD l 0)
      = Blake2s.leWord
          (((bytes ++ List.replicate (64 * NB - bytes.length) 0).drop
            (64 * i)).take 64) := by
  have hpblen : (bytes ++ List.replicate (64 * NB - bytes.length)
      (0 : UInt8)).length = 64 * NB := by
    rw [List.length_append, List.length_replicate]
    omega
  funext l
  by_cases hl : l < 16
  · rw [List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hl,
      List.getElem?_drop, List.getElem?_map,
      List.getElem?_range (by omega : 16 * i + l < 16 * NB)]
    simp only [Option.map_some, Option.getD_some]
    rw [leWord_take (by omega), leWord_drop]
  · rw [List.getD_eq_default _ _ (by
      rw [List.length_take, List.length_drop, List.length_map,
        List.length_range]
      omega)]
    rw [leWord_oob (by
      rw [List.length_take, List.length_drop, hpblen]
      omega)]

/-! ### Padded-chunk equalities -/

theorem chunk_mid {bytes : List UInt8} {NB i : ℕ}
    (hmid : 64 * (i + 1) < bytes.length) :
    ((bytes ++ List.replicate (64 * NB - bytes.length) 0).drop
      (64 * i)).take 64 = (bytes.drop (64 * i)).take 64 := by
  rw [List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by rw [List.length_drop]; omega)]

theorem chunk_last {bytes : List UInt8} {NB i : ℕ}
    (hlo : 64 * i < bytes.length) (hhi : bytes.length ≤ 64 * (i + 1))
    (hNBi : NB = i + 1) :
    ((bytes ++ List.replicate (64 * NB - bytes.length) 0).drop
      (64 * i)).take 64
      = bytes.drop (64 * i)
        ++ List.replicate (64 - (bytes.drop (64 * i)).length) 0 := by
  rw [List.drop_append_of_le_length (by omega),
    List.take_append, List.take_replicate, List.length_drop]
  subst hNBi
  rw [show min (64 - (bytes.length - 64 * i)) (64 * (i + 1) - bytes.length)
    = 64 - (bytes.length - 64 * i) from by omega]
  rw [show bytes.drop (64 * i) = (bytes.drop (64 * i)).take 64 from by
    rw [List.take_of_length_le (by rw [List.length_drop]; omega)]]
  rw [List.take_take, min_self]

/-! ### `hashWordsL` equations -/

theorem hashWordsL_zero (ws : List Blake2s.Word) (nB i : ℕ)
    (hl : List Blake2s.Word) : hashWordsL ws nB 0 i hl = hl := rfl

theorem hashWordsL_succ (ws : List Blake2s.Word) (nB k i : ℕ)
    (hl : List Blake2s.Word) :
    hashWordsL ws nB (k + 1) i hl
      = hashWordsL ws nB k (i + 1) ((List.range 8).map fun j =>
          Blake2s.compress (fun l => hl.getD l 0)
            (fun l => ((ws.drop (16 * i)).take 16).getD l 0)
            (min nB ((i + 1) * 64)) (k = 0) j) := rfl

/-! ### The chains coincide -/

/-- **The word chain is the byte chain**: with the word list read off
the zero-padded bytes, `hashWordsL` from block `i` computes
`hashBlocks` on the remaining bytes at byte counter `64·i`. -/
theorem hashWordsL_eq_hashBlocks (bytes : List UInt8) (NB : ℕ)
    (hNB : bytes.length ≤ 64 * NB)
    (hNB2 : ∀ j, j + 1 < NB → 64 * (j + 1) < bytes.length) :
    ∀ (k i : ℕ) (hl : List Blake2s.Word), 1 ≤ k → i + k = NB →
      (64 * i < bytes.length ∨ (i = 0 ∧ bytes.length = 0)) →
      hashWordsL ((List.range (16 * NB)).map
          (Blake2s.leWord
            (bytes ++ List.replicate (64 * NB - bytes.length) 0)))
          bytes.length k i hl
        = (List.range 8).map
            (Blake2s.hashBlocks (fun j => hl.getD j 0) (64 * i)
              (bytes.drop (64 * i)))
  | 0, i, hl, hk, _, _ => absurd hk (by omega)
  | 1, i, hl, _, hik, hpos => by
    rw [hashWordsL_succ, hashWordsL_zero,
      slice_schedule bytes NB hNB i (by omega)]
    rcases hpos with hlo | ⟨hi0, hb0⟩
    · -- The last, nonempty block.
      have hhi : bytes.length ≤ 64 * (i + 1) := by omega
      have hrlen : (bytes.drop (64 * i)).length = bytes.length - 64 * i := by
        rw [List.length_drop]
      rw [chunk_last hlo hhi (by omega),
        hashBlocks_last (by
          intro hnil
          rw [hnil] at hrlen
          simp at hrlen
          omega) (by omega) _ (64 * i)]
      rw [hrlen, show 64 * i + (bytes.length - 64 * i) = bytes.length from by
        omega,
        show min bytes.length ((i + 1) * 64) = bytes.length from by omega]
      rfl
    · -- The empty message: one all-zero block at counter 0.
      subst hi0
      have hbnil : bytes = [] := List.eq_nil_of_length_eq_zero hb0
      subst hbnil
      rw [show List.drop (64 * 0) ([] : List UInt8) = [] from by simp,
        hashBlocks_nil]
      have hm : Blake2s.leWord ((([] : List UInt8) ++
          List.replicate (64 * NB - ([] : List UInt8).length) 0).drop
            (64 * 0) |>.take 64)
          = fun _ => (0 : Blake2s.Word) := by
        funext l
        by_cases hl64 : 4 * l + 4 ≤ 64
        · rw [leWord_take hl64]
          have hrepl : (([] : List UInt8) ++
              List.replicate (64 * NB - ([] : List UInt8).length)
                (0 : UInt8)).drop (64 * 0)
              = List.replicate (64 * NB) (0 : UInt8) := by simp
          rw [hrepl, leWord_replicate_zero]
        · rw [leWord_oob (by rw [List.length_take]; omega)]
      rw [hm, show min ([] : List UInt8).length ((0 + 1) * 64) = 64 * 0
        from by simp]
      rfl
  | k + 2, i, hl, _, hik, hpos => by
    have hmid : 64 * (i + 1) < bytes.length := hNB2 i (by omega)
    rw [hashWordsL_succ,
      slice_schedule bytes NB hNB i (by omega), chunk_mid hmid]
    have hrgt : ¬ (bytes.drop (64 * i)).length ≤ 64 := by
      rw [List.length_drop]
      omega
    rw [hashBlocks_step hrgt, List.drop_drop,
      show 64 * i + 64 = 64 * (i + 1) from by ring]
    rw [hashWordsL_eq_hashBlocks bytes NB hNB hNB2 (k + 1) (i + 1) _
      (by omega) (by omega) (Or.inl hmid)]
    rw [show min bytes.length ((i + 1) * 64) = 64 * (i + 1) from by
      omega,
      show (bytes.drop (64 * i)).take 64 = (bytes.take (64 * (i + 1))).drop
        (64 * i) from by
        rw [List.drop_take]
        congr 1
        omega,
      show decide (k + 1 = 0) = false from by simp]

end StwoVerifier.Gadgets
