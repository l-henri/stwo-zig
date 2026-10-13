/-
**The in-circuit channel state** (`stark_verifier/channel.zig`,
stwo-zig `4afa09dbf`).

The circuit keeps the Fiat-Shamir digest as two QM31 wires holding the
eight reduced hash words; the spec keeps 32 digest bytes. `ChDigest`
is the correspondence — the wires' byte serialization is the spec
digest — and it is preserved by the mixes: `blake2s_m31`'s two-felt
result serializes to exactly `chHash true` of the hashed bytes
(`digestFelts_bytes`), because the spec's m31 digest reduction is the
word-wise `mod P` the reduce gadget computes.
-/
import StwoVerifier.BlakePack

namespace StwoVerifier.Gadgets

open StwoVerifier StwoVerifier.Gates

/-! ### The spec's digest reduction, word-wise -/

theorem reduceWord_mod {w : ℕ} (hw : w < 2 ^ 32) :
    Channel.reduceWord w = w % P := by
  unfold Channel.reduceWord P
  show (if w % 2 ^ 31 + w / 2 ^ 31 ≥ 2 ^ 31 - 1
    then w % 2 ^ 31 + w / 2 ^ 31 - (2 ^ 31 - 1)
    else w % 2 ^ 31 + w / 2 ^ 31) = w % (2 ^ 31 - 1)
  by_cases hge : w % 2 ^ 31 + w / 2 ^ 31 ≥ 2 ^ 31 - 1
  · rw [if_pos hge]
    omega
  · rw [if_neg hge]
    omega

theorem reduceWord_lt {w : ℕ} (hw : w < 2 ^ 32) :
    Channel.reduceWord w < P := by
  rw [reduceWord_mod hw]
  exact Nat.mod_lt _ (by unfold P; norm_num)

/-- `wordAt` inverts `digest`'s serialization. -/
theorem wordAt_digest (hf : ℕ → Blake2s.Word) {j : ℕ} (hj : j < 8) :
    Channel.wordAt (Blake2s.digest hf) j = (hf j).toNat := by
  unfold Blake2s.digest Channel.wordAt
  rw [show (List.range 8).flatMap (fun i => (List.range 4).map fun jj =>
      UInt8.ofNat ((hf i).toNat / 2 ^ (8 * jj)))
    = ((List.range 8).map fun i => (List.range 4).map fun jj =>
      UInt8.ofNat ((hf i).toNat / 2 ^ (8 * jj))).flatten from rfl]
  have hb : ∀ c, c < 4 →
      (((List.range 8).map fun i => (List.range 4).map fun jj =>
        UInt8.ofNat ((hf i).toNat / 2 ^ (8 * jj))).flatten).getD (4 * j + c) 0
        = UInt8.ofNat ((hf ((List.range 8).getD j default)).toNat
            / 2 ^ (8 * c)) := by
    intro c hc
    rw [flatten4_getD _ 0 (fun _ => by simp) (List.range 8) j c
      (by simpa using hj) hc]
    rw [getD_map' _ (0 : UInt8) (List.range 4) c (by simpa using hc),
      show (List.range 4).getD c default = c from by
        rw [List.getD_eq_getElem?_getD, List.getElem?_range hc]; rfl]
  have hrj : (List.range 8).getD j default = j := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_range hj]
    rfl
  rw [show 4 * j = 4 * j + 0 from by omega, hb 0 (by omega), hb 1 (by omega),
    hb 2 (by omega), hb 3 (by omega), hrj]
  have hlt := (hf j).isLt
  show ((hf j).toNat / 2 ^ (8 * 0)) % 256
      + 2 ^ 8 * (((hf j).toNat / 2 ^ (8 * 1)) % 256)
      + 2 ^ 16 * (((hf j).toNat / 2 ^ (8 * 2)) % 256)
      + 2 ^ 24 * (((hf j).toNat / 2 ^ (8 * 3)) % 256) = (hf j).toNat
  omega

/-- `wordAt` inverts a run of eight `u32Le` blocks. -/
theorem wordAt_flat_u32Le (g : ℕ → ℕ) (hg : ∀ k, k < 8 → g k < 2 ^ 32)
    {j : ℕ} (hj : j < 8) :
    Channel.wordAt ((List.range 8).flatMap fun k => Channel.u32Le (g k)) j
      = g j := by
  unfold Channel.wordAt
  rw [show (List.range 8).flatMap (fun k => Channel.u32Le (g k))
    = ((List.range 8).map fun k => Channel.u32Le (g k)).flatten from rfl]
  have hb : ∀ c, c < 4 →
      (((List.range 8).map fun k => Channel.u32Le (g k)).flatten).getD
        (4 * j + c) 0
        = (Channel.u32Le (g ((List.range 8).getD j default))).getD c 0 :=
    fun c hc => flatten4_getD _ 0 (fun _ => rfl) (List.range 8) j c
      (by simpa using hj) hc
  have hrj : (List.range 8).getD j default = j := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_range hj]
    rfl
  rw [show 4 * j = 4 * j + 0 from by omega, hb 0 (by omega), hb 1 (by omega),
    hb 2 (by omega), hb 3 (by omega), hrj]
  have hlt := hg j hj
  show g j % 256 + 2 ^ 8 * (g j / 2 ^ 8 % 256) + 2 ^ 16 * (g j / 2 ^ 16 % 256)
      + 2 ^ 24 * (g j / 2 ^ 24 % 256) = g j
  omega

/-- Every `wordAt` is a `u32`. -/
theorem wordAt_lt (b : Channel.Bytes) (j : ℕ) :
    Channel.wordAt b j < 2 ^ 32 := by
  unfold Channel.wordAt
  have h0 := (b.getD (4 * j) 0).toNat_lt
  have h1 := (b.getD (4 * j + 1) 0).toNat_lt
  have h2 := (b.getD (4 * j + 2) 0).toNat_lt
  have h3 := (b.getD (4 * j + 3) 0).toNat_lt
  omega

/-- `wordAt` inverts `reduceDigest`'s serialization. -/
theorem wordAt_reduceDigest (b : Channel.Bytes) {j : ℕ} (hj : j < 8) :
    Channel.wordAt (Channel.reduceDigest b) j
      = Channel.reduceWord (Channel.wordAt b j) := by
  unfold Channel.reduceDigest
  exact wordAt_flat_u32Le (fun k => Channel.reduceWord (Channel.wordAt b k))
    (fun k _ => lt_of_lt_of_le (reduceWord_lt (wordAt_lt b k))
      (by unfold P; norm_num)) hj

/-! ### The two-felt digest serializes to the spec digest -/

theorem fromPartialEvals_base (a b c d : F) :
    fromPartialEvals [QM31.fromBase a, QM31.fromBase b,
      QM31.fromBase c, QM31.fromBase d] = ⟨⟨a, b⟩, ⟨c, d⟩⟩ := by
  unfold fromPartialEvals
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  refine QM31.ext' ?_ ?_ <;>
    (ext <;>
      simp [QM31.fromBase, CM31.fromBase, QM31.fromM31s, QM31.mul_c0,
        QM31.mul_c1, QM31.add_c0, QM31.add_c1, QM31.R, CM31.mul_a, CM31.mul_b,
        CM31.add_a, CM31.add_b] <;> ring)

theorem qm31Bytes_mk (a b c d : F) :
    Channel.qm31Bytes ⟨⟨a, b⟩, ⟨c, d⟩⟩
      = Channel.u32Le a.val ++ Channel.u32Le b.val
        ++ Channel.u32Le c.val ++ Channel.u32Le d.val := by
  unfold Channel.qm31Bytes QM31.coords Channel.feltBytes
  simp [List.flatten]

/-- **The reduce gadget's two felts serialize to the spec's m31
digest** of the same hash. -/
theorem digestFelts_bytes (bytes : List UInt8) :
    Channel.qm31Bytes (digestFelts ((List.range 8).map
        (Blake2s.hashBlocks Blake2s.h0 0 bytes))).1
      ++ Channel.qm31Bytes (digestFelts ((List.range 8).map
        (Blake2s.hashBlocks Blake2s.h0 0 bytes))).2
      = Channel.chHash true bytes := by
  have hget : ∀ j, j < 8 →
      ((List.range 8).map (Blake2s.hashBlocks Blake2s.h0 0 bytes)).getD j 0
        = Blake2s.hashBlocks Blake2s.h0 0 bytes j := by
    intro j hj
    rw [getD_map' _ (0 : Blake2s.Word) (List.range 8) j (by simpa using hj),
      show (List.range 8).getD j default = j from by
        rw [List.getD_eq_getElem?_getD, List.getElem?_range hj]; rfl]
  have hword : ∀ j, j < 8 →
      Channel.reduceWord (Channel.wordAt (Blake2s.blake2s bytes) j)
        = (Blake2s.hashBlocks Blake2s.h0 0 bytes j).toNat % P := by
    intro j hj
    unfold Blake2s.blake2s
    rw [wordAt_digest _ hj,
      reduceWord_mod (Blake2s.hashBlocks Blake2s.h0 0 bytes j).isLt]
  have hval : ∀ j, j < 8 →
      (((((List.range 8).map (Blake2s.hashBlocks Blake2s.h0 0 bytes)).getD
        j 0).toNat : ℕ) : F).val
        = Channel.reduceWord (Channel.wordAt (Blake2s.blake2s bytes) j) := by
    intro j hj
    rw [hget j hj, hword j hj, ZMod.val_natCast]
  unfold digestFelts
  rw [show (List.range 4).map (fun j => QM31.fromBase
      (((((List.range 8).map (Blake2s.hashBlocks Blake2s.h0 0 bytes)).getD
        j 0).toNat : ℕ) : F))
      = [QM31.fromBase _, QM31.fromBase _, QM31.fromBase _, QM31.fromBase _]
    from rfl]
  rw [show (List.range 4).map (fun j => QM31.fromBase
      (((((List.range 8).map (Blake2s.hashBlocks Blake2s.h0 0 bytes)).getD
        (4 + j) 0).toNat : ℕ) : F))
      = [QM31.fromBase _, QM31.fromBase _, QM31.fromBase _, QM31.fromBase _]
    from rfl]
  rw [fromPartialEvals_base, fromPartialEvals_base, qm31Bytes_mk,
    qm31Bytes_mk]
  simp only [Nat.reduceAdd, Nat.add_zero]
  rw [hval 0 (by omega), hval 1 (by omega), hval 2 (by omega),
    hval 3 (by omega), hval 4 (by omega), hval 5 (by omega),
    hval 6 (by omega), hval 7 (by omega)]
  unfold Channel.chHash
  rw [if_pos rfl]
  unfold Channel.reduceDigest
  rw [show (List.range 8) = [0, 1, 2, 3, 4, 5, 6, 7] from rfl]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  simp [List.append_assoc]

/-! ### The channel-state correspondence and the mixes -/

/-- The circuit digest wires serialize to the spec digest. -/
def ChDigest (ρ : ℕ → QM31) (low high : ℕ) (d : Channel.Bytes) : Prop :=
  Channel.qm31Bytes (ρ low) ++ Channel.qm31Bytes (ρ high) = d

/-- `mix_qm31s`: `blake2s_m31(digest ‖ values)`. -/
noncomputable def mixQm31sG (low high : ℕ) (values : List ℕ) (n : ℕ) :
    Out (ℕ × ℕ) :=
  blake2sM31G (low :: high :: values) (16 * (2 + values.length)) n

/-- **`mix_qm31s` is `mixFelts`**: the new digest wires serialize to
the spec's post-mix digest. -/
theorem mixQm31sG_sound {ρ : ℕ → QM31} {low high : ℕ} {values : List ℕ}
    {xs : List QM31} {s : Channel.St} {n : ℕ}
    (hd : ChDigest ρ low high s.digest) (hdlen : s.digest.length = 32)
    (hvl : values.length = xs.length)
    (hvv : ∀ i, i < values.length → ρ (values.getD i 0) = xs.getD i 0)
    (h : AllHold ρ (mixQm31sG low high values n).ops) :
    ChDigest ρ (mixQm31sG low high values n).res.1
      (mixQm31sG low high values n).res.2
      (Channel.mixFelts true s xs).digest := by
  have hblen : (s.digest ++ (xs.map Channel.qm31Bytes).flatten).length
      = 16 * (2 + xs.length) := by
    rw [List.length_append, hdlen, List.length_flatten]
    rw [List.map_map, show (List.length ∘ Channel.qm31Bytes) = fun _ => 16
      from funext fun x => rfl]
    simp
    ring
  have hnb : (16 : ℕ) * (2 + values.length)
      = (s.digest ++ (xs.map Channel.qm31Bytes).flatten).length := by
    rw [hblen, hvl]
  replace h : AllHold ρ (blake2sM31G (low :: high :: values)
      (16 * (2 + values.length)) n).ops := h
  rw [hnb] at h
  show Channel.qm31Bytes (ρ (blake2sM31G (low :: high :: values)
      (16 * (2 + values.length)) n).res.1)
    ++ Channel.qm31Bytes (ρ (blake2sM31G (low :: high :: values)
      (16 * (2 + values.length)) n).res.2)
    = (Channel.mixFelts true s xs).digest
  rw [hnb]
  have hsound := blake2sM31G_sound (xs := ρ low :: ρ high :: xs)
    (bytes := s.digest ++ (xs.map Channel.qm31Bytes).flatten)
    (by simp [hvl])
    (fun i hi => by
      match i, hi with
      | 0, _ => rfl
      | 1, _ => rfl
      | (j + 2), hj =>
        show ρ (values.getD j 0) = xs.getD j 0
        exact hvv j (by simpa using hj))
    (by
      rw [List.map_cons, List.map_cons, List.flatten_cons, List.flatten_cons]
      have hcnt : 16 * (ρ low :: ρ high :: xs).length
          - (s.digest ++ (xs.map Channel.qm31Bytes).flatten).length = 0 := by
        rw [hblen, List.length_cons, List.length_cons]
        omega
      rw [hcnt, List.replicate_zero, List.append_nil, ← List.append_assoc,
        hd])
    (by
      rw [hblen, List.length_cons, List.length_cons]
      omega)
    h
  obtain ⟨h1, h2⟩ := hsound
  rw [h1, h2, digestFelts_bytes]
  rfl

end StwoVerifier.Gadgets