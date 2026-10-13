/-
**The in-circuit Blake2s, part 1: the round walk**
(`src/frontends/circuit/builder/blake.zig`, stwo-zig `4afa09dbf`).

`blake2s_u32s` runs the compression in dedicated gates: one `BlakeGGate`
per G application (the whole RFC 7693 mixing function on `u32` limb
wires), ten rounds of eight, then a `TripleXor` per chaining word. The
gates' semantics (`Circuit::check`) are stated against the spec's
`Blake2s.mix`, so the round walk here is index bookkeeping: the
register state list tracks the spec's working vector word for word
(`RegsWords`), `gStepG` is `gStep`, and `stepsG k` is `steps k`.
-/
import StwoVerifier.Gates

namespace StwoVerifier.Gadgets

open StwoVerifier StwoVerifier.Gates

/-! ### Words and limb registers -/

theorem packW_isU32 (w : Blake2s.Word) : IsU32 (packW w) := by
  refine ⟨?_, ?_, rfl⟩
  · show (((w.toNat % 65536 : ℕ) : F)).val < 65536
    rw [ZMod.val_cast_of_lt (by unfold P; omega)]
    omega
  · show (((w.toNat / 65536 : ℕ) : F)).val < 65536
    have hlt := w.isLt
    rw [ZMod.val_cast_of_lt (by unfold P; omega)]
    omega

theorem wordOf_packW (w : Blake2s.Word) : wordOf (packW w) = w := by
  have hlt := w.isLt
  show BitVec.ofNat 32 ((((w.toNat % 65536 : ℕ) : F)).val
    + 65536 * (((w.toNat / 65536 : ℕ) : F)).val) = w
  rw [ZMod.val_cast_of_lt (by unfold P; omega),
    ZMod.val_cast_of_lt (by unfold P; omega),
    Nat.mod_add_div, BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ### `getD` through `set` -/

theorem getD_set_self {α : Type} {l : List α} {i : ℕ} {a d : α}
    (h : i < l.length) : (l.set i a).getD i d = a := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, h]

theorem getD_set_ne {α : Type} {l : List α} {i j : ℕ} {a d : α}
    (h : i ≠ j) : (l.set i a).getD j d = l.getD j d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_set, h]

/-! ### The gates -/

/-- One `TripleXor` gate. -/
def tripleXorG (a b c n : ℕ) : Out ℕ := ⟨[.tripleXor n a b c], n, n + 1⟩

theorem tripleXorG_sound {ρ : ℕ → QM31} {a b c n : ℕ}
    (h : AllHold ρ (tripleXorG a b c n).ops) :
    ρ (tripleXorG a b c n).res
      = packW (wordOf (ρ a) ^^^ wordOf (ρ b) ^^^ wordOf (ρ c)) := by
  have h1 := h (.tripleXor n a b c) List.mem_cons_self
  exact h1.2.2.2

/-! ### The register ↔ word state correspondence -/

/-- The register list carries exactly these words, limb-packed. -/
structure RegsWords (ρ : ℕ → QM31) (regs : List ℕ) (ws : List Blake2s.Word) :
    Prop where
  len : regs.length = ws.length
  val : ∀ j, j < regs.length → ρ (regs.getD j 0) = packW (ws.getD j 0)

/-- The G-indices are in range and pairwise distinct. -/
theorem gIdx_facts : ∀ g, g < 8 →
    (Blake2s.gIdx g).1 < 16 ∧ (Blake2s.gIdx g).2.1 < 16 ∧
    (Blake2s.gIdx g).2.2.1 < 16 ∧ (Blake2s.gIdx g).2.2.2 < 16 ∧
    (Blake2s.gIdx g).1 ≠ (Blake2s.gIdx g).2.1 ∧
    (Blake2s.gIdx g).1 ≠ (Blake2s.gIdx g).2.2.1 ∧
    (Blake2s.gIdx g).1 ≠ (Blake2s.gIdx g).2.2.2 ∧
    (Blake2s.gIdx g).2.1 ≠ (Blake2s.gIdx g).2.2.1 ∧
    (Blake2s.gIdx g).2.1 ≠ (Blake2s.gIdx g).2.2.2 ∧
    (Blake2s.gIdx g).2.2.1 ≠ (Blake2s.gIdx g).2.2.2 := by
  decide

theorem sigma_lt : ∀ r, r < 10 → ∀ i, i < 16 → Blake2s.sigma r i < 16 := by
  decide

/-! ### One G application -/

/-- One `BlakeGGate` application at round `r`, position `g`
(`blake2s_u32s`' inner loop body): the four state registers at the
G-indices and the two scheduled message registers in, four fresh
output registers written back. -/
def gStepG (vRegs mRegs : List ℕ) (r g n : ℕ) : Out (List ℕ) :=
  ⟨[.blakeG n (vRegs.getD (Blake2s.gIdx g).1 0)
      (vRegs.getD (Blake2s.gIdx g).2.1 0)
      (vRegs.getD (Blake2s.gIdx g).2.2.1 0)
      (vRegs.getD (Blake2s.gIdx g).2.2.2 0)
      (mRegs.getD (Blake2s.sigma r (2 * g)) 0)
      (mRegs.getD (Blake2s.sigma r (2 * g + 1)) 0)],
   ((((vRegs.set (Blake2s.gIdx g).1 n).set (Blake2s.gIdx g).2.1 (n + 1)).set
      (Blake2s.gIdx g).2.2.1 (n + 2)).set (Blake2s.gIdx g).2.2.2 (n + 3)),
   n + 4⟩

theorem gStepG_sound {ρ : ℕ → QM31} {vRegs mRegs : List ℕ}
    {ws ms : List Blake2s.Word} {r g n : ℕ}
    (hv : RegsWords ρ vRegs ws) (hm : RegsWords ρ mRegs ms)
    (h16 : ws.length = 16) (hm16 : ms.length = 16)
    (hr : r < 10) (hg : g < 8)
    (h : AllHold ρ (gStepG vRegs mRegs r g n).ops) :
    RegsWords ρ (gStepG vRegs mRegs r g n).res
      (Blake2s.gStep (fun i => ms.getD i 0) ws r g) := by
  obtain ⟨hia, hib, hic, hid, hab, hac, had, hbc, hbd, hcd⟩ := gIdx_facts g hg
  have hvlen : vRegs.length = 16 := by rw [hv.len, h16]
  have hgate := h (.blakeG n (vRegs.getD (Blake2s.gIdx g).1 0)
      (vRegs.getD (Blake2s.gIdx g).2.1 0)
      (vRegs.getD (Blake2s.gIdx g).2.2.1 0)
      (vRegs.getD (Blake2s.gIdx g).2.2.2 0)
      (mRegs.getD (Blake2s.sigma r (2 * g)) 0)
      (mRegs.getD (Blake2s.sigma r (2 * g + 1)) 0)) List.mem_cons_self
  obtain ⟨-, -, -, -, -, -, ho0, ho1, ho2, ho3⟩ := hgate
  -- The gate's input words are the spec state's words.
  have hwa : wordOf (ρ (vRegs.getD (Blake2s.gIdx g).1 0))
      = ws.getD (Blake2s.gIdx g).1 0 := by
    rw [hv.val _ (by omega), wordOf_packW]
  have hwb : wordOf (ρ (vRegs.getD (Blake2s.gIdx g).2.1 0))
      = ws.getD (Blake2s.gIdx g).2.1 0 := by
    rw [hv.val _ (by omega), wordOf_packW]
  have hwc : wordOf (ρ (vRegs.getD (Blake2s.gIdx g).2.2.1 0))
      = ws.getD (Blake2s.gIdx g).2.2.1 0 := by
    rw [hv.val _ (by omega), wordOf_packW]
  have hwd : wordOf (ρ (vRegs.getD (Blake2s.gIdx g).2.2.2 0))
      = ws.getD (Blake2s.gIdx g).2.2.2 0 := by
    rw [hv.val _ (by omega), wordOf_packW]
  have hmlen : mRegs.length = 16 := by rw [hm.len, hm16]
  have hs0 : Blake2s.sigma r (2 * g) < 16 := sigma_lt r hr _ (by omega)
  have hs1 : Blake2s.sigma r (2 * g + 1) < 16 := sigma_lt r hr _ (by omega)
  have hwf0 : wordOf (ρ (mRegs.getD (Blake2s.sigma r (2 * g)) 0))
      = ms.getD (Blake2s.sigma r (2 * g)) 0 := by
    rw [hm.val _ (by omega), wordOf_packW]
  have hwf1 : wordOf (ρ (mRegs.getD (Blake2s.sigma r (2 * g + 1)) 0))
      = ms.getD (Blake2s.sigma r (2 * g + 1)) 0 := by
    rw [hm.val _ (by omega), wordOf_packW]
  rw [hwa, hwb, hwc, hwd, hwf0, hwf1] at ho0 ho1 ho2 ho3
  have hspec : Blake2s.gStep (fun i => ms.getD i 0) ws r g
      = ((((ws.set (Blake2s.gIdx g).1
            (Blake2s.mix (ws.getD (Blake2s.gIdx g).1 0)
              (ws.getD (Blake2s.gIdx g).2.1 0) (ws.getD (Blake2s.gIdx g).2.2.1 0)
              (ws.getD (Blake2s.gIdx g).2.2.2 0)
              (ms.getD (Blake2s.sigma r (2 * g)) 0)
              (ms.getD (Blake2s.sigma r (2 * g + 1)) 0)).1).set
          (Blake2s.gIdx g).2.1
            (Blake2s.mix (ws.getD (Blake2s.gIdx g).1 0)
              (ws.getD (Blake2s.gIdx g).2.1 0) (ws.getD (Blake2s.gIdx g).2.2.1 0)
              (ws.getD (Blake2s.gIdx g).2.2.2 0)
              (ms.getD (Blake2s.sigma r (2 * g)) 0)
              (ms.getD (Blake2s.sigma r (2 * g + 1)) 0)).2.1).set
          (Blake2s.gIdx g).2.2.1
            (Blake2s.mix (ws.getD (Blake2s.gIdx g).1 0)
              (ws.getD (Blake2s.gIdx g).2.1 0) (ws.getD (Blake2s.gIdx g).2.2.1 0)
              (ws.getD (Blake2s.gIdx g).2.2.2 0)
              (ms.getD (Blake2s.sigma r (2 * g)) 0)
              (ms.getD (Blake2s.sigma r (2 * g + 1)) 0)).2.2.1).set
          (Blake2s.gIdx g).2.2.2
            (Blake2s.mix (ws.getD (Blake2s.gIdx g).1 0)
              (ws.getD (Blake2s.gIdx g).2.1 0) (ws.getD (Blake2s.gIdx g).2.2.1 0)
              (ws.getD (Blake2s.gIdx g).2.2.2 0)
              (ms.getD (Blake2s.sigma r (2 * g)) 0)
              (ms.getD (Blake2s.sigma r (2 * g + 1)) 0)).2.2.2) := rfl
  rw [hspec]
  constructor
  · show ((((vRegs.set _ n).set _ (n + 1)).set _ (n + 2)).set _ (n + 3)).length
      = _
    simp [hvlen, h16]
  · intro j hj
    have hj16 : j < 16 := by
      have hlen : (gStepG vRegs mRegs r g n).res.length = 16 := by
        show ((((vRegs.set _ n).set _ (n + 1)).set _ (n + 2)).set
          _ (n + 3)).length = 16
        simp [hvlen]
      omega
    show ρ ((((((vRegs.set (Blake2s.gIdx g).1 n).set (Blake2s.gIdx g).2.1
      (n + 1)).set (Blake2s.gIdx g).2.2.1 (n + 2)).set (Blake2s.gIdx g).2.2.2
      (n + 3))).getD j 0) = _
    by_cases h3 : j = (Blake2s.gIdx g).2.2.2
    · subst h3
      rw [getD_set_self (by simp [hvlen]; omega),
        getD_set_self (by simp [h16]; omega)]
      exact ho3
    · rw [getD_set_ne (fun he => h3 he.symm),
        getD_set_ne (fun he => h3 he.symm)]
      by_cases h2 : j = (Blake2s.gIdx g).2.2.1
      · subst h2
        rw [getD_set_self (by simp [hvlen]; omega),
          getD_set_self (by simp [h16]; omega)]
        exact ho2
      · rw [getD_set_ne (fun he => h2 he.symm),
          getD_set_ne (fun he => h2 he.symm)]
        by_cases h1 : j = (Blake2s.gIdx g).2.1
        · subst h1
          rw [getD_set_self (by simp [hvlen]; omega),
            getD_set_self (by simp [h16]; omega)]
          exact ho1
        · rw [getD_set_ne (fun he => h1 he.symm),
            getD_set_ne (fun he => h1 he.symm)]
          by_cases h0 : j = (Blake2s.gIdx g).1
          · subst h0
            rw [getD_set_self (by omega), getD_set_self (by rw [h16]; omega)]
            exact ho0
          · rw [getD_set_ne (fun he => h0 he.symm),
              getD_set_ne (fun he => h0 he.symm)]
            exact hv.val j (by omega)

/-- `gStep` keeps the state length. -/
theorem gStep_length (m : ℕ → Blake2s.Word) (v : List Blake2s.Word)
    (r g : ℕ) : (Blake2s.gStep m v r g).length = v.length := by
  show ((((v.set (Blake2s.gIdx g).1 _).set (Blake2s.gIdx g).2.1 _).set
    (Blake2s.gIdx g).2.2.1 _).set (Blake2s.gIdx g).2.2.2 _).length = v.length
  simp

/-! ### The 80-step round walk -/

/-- The first `k` G applications (`blake2s_u32s`' round loops,
flattened: step `k` is round `k / 8`, position `k % 8`). -/
def stepsG (mRegs : List ℕ) : ℕ → List ℕ → ℕ → Out (List ℕ)
  | 0, vRegs, n => ⟨[], vRegs, n⟩
  | k + 1, vRegs, n =>
    let prev := stepsG mRegs k vRegs n
    let st := gStepG prev.res mRegs (k / 8) (k % 8) prev.next
    ⟨prev.ops ++ st.ops, st.res, st.next⟩

theorem stepsG_sound {ρ : ℕ → QM31} {mRegs : List ℕ}
    {ms : List Blake2s.Word} (hm : RegsWords ρ mRegs ms)
    (hm16 : ms.length = 16) :
    ∀ (k : ℕ) (vRegs : List ℕ) (ws : List Blake2s.Word) (n : ℕ),
      k ≤ 80 → RegsWords ρ vRegs ws → ws.length = 16 →
      AllHold ρ (stepsG mRegs k vRegs n).ops →
      RegsWords ρ (stepsG mRegs k vRegs n).res
        (Blake2s.steps (fun i => ms.getD i 0) ws k) ∧
      (Blake2s.steps (fun i => ms.getD i 0) ws k).length = 16
  | 0, vRegs, ws, n, _, hv, h16, _ => ⟨hv, h16⟩
  | k + 1, vRegs, ws, n, hk, hv, h16, h => by
    rw [show (stepsG mRegs (k + 1) vRegs n).ops =
      (stepsG mRegs k vRegs n).ops ++
        (gStepG (stepsG mRegs k vRegs n).res mRegs (k / 8) (k % 8)
          (stepsG mRegs k vRegs n).next).ops from rfl,
      allHold_append] at h
    obtain ⟨hprev, hst⟩ := h
    obtain ⟨ihrw, ihlen⟩ := stepsG_sound hm hm16 k vRegs ws n (by omega)
      hv h16 hprev
    have hstep := gStepG_sound ihrw hm ihlen hm16 (by omega) (by omega) hst
    refine ⟨hstep, ?_⟩
    show (Blake2s.gStep _ _ _ _).length = 16
    rw [gStep_length, ihlen]

end StwoVerifier.Gadgets
