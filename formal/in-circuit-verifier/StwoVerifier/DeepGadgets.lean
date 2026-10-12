/-
**`compute_fri_input`'s per-point accumulation**
(`src/frontends/circuit/stark_verifier/oods.zig` `OodsPointAuxiliary`,
stwo-zig `4afa09dbf`): the line coefficients `d = im P.y`, `e = im P.x`,
`f = d·P.x − e·P.y`, and the response accumulators
`a = Σ α'ᵢ·im Vᵢ`, `v = Σ α'ᵢ·Vᵢ`, `b = d·v − a·P.y`, with the per-column
coefficients `cᵢ = d·α'ᵢ`.

The soundness lemmas state each register as the corresponding sum over
the response list — exactly the shapes `Deep.num_identity_batched` and
`Deep.den_identity` consume. The remaining `compute_fri_input` work is
the per-query quotient loop and the grouping walk.

`imMask` is the interned constant `(0,0,1,1)` (`ops.im`'s coefficient),
pinned by hypothesis like the builder's interned `one`.
-/
import StwoVerifier.Gates
import StwoVerifier.DeepIdentity

namespace StwoVerifier.Gadgets

open StwoVerifier StwoVerifier.Gates

/-- `OodsPointAuxiliary.init`: `d`, `e`, `f` from the point's wires. -/
def auxInit (imMask px py n : ℕ) : Out (ℕ × ℕ × ℕ) :=
  ⟨[.pmul n py imMask,
    .pmul (n + 1) px imMask,
    .mul (n + 2) n px,
    .mul (n + 3) (n + 1) py,
    .sub (n + 4) (n + 2) (n + 3)],
   (n, n + 1, n + 4), n + 5⟩

theorem auxInit_sound {ρ : ℕ → QM31} {imMask px py n : ℕ}
    (hmask : ρ imMask = QM31.fromM31s 0 0 1 1)
    (h : AllHold ρ (auxInit imMask px py n).ops) :
    ρ (auxInit imMask px py n).res.1 = Deep.imQ (ρ py) ∧
    ρ (auxInit imMask px py n).res.2.1 = Deep.imQ (ρ px) ∧
    ρ (auxInit imMask px py n).res.2.2
      = Deep.imQ (ρ py) * ρ px - Deep.imQ (ρ px) * ρ py := by
  rw [show (auxInit imMask px py n).ops =
    .pmul n py imMask :: .pmul (n + 1) px imMask :: .mul (n + 2) n px ::
    .mul (n + 3) (n + 1) py :: [.sub (n + 4) (n + 2) (n + 3)] from rfl,
    allHold_cons, allHold_cons, allHold_cons, allHold_cons, allHold_cons] at h
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := h
  simp only [Holds] at h1 h2 h3 h4 h5
  have hd : ρ n = Deep.imQ (ρ py) := by
    rw [h1, hmask]; rfl
  have he : ρ (n + 1) = Deep.imQ (ρ px) := by
    rw [h2, hmask]; rfl
  refine ⟨hd, he, ?_⟩
  show ρ (n + 4) = _
  rw [h5, h3, h4, hd, he]

/-- One `accumulate` step: `c = d·α'`, `a += α'·im V`, `v += α'·V`. The
`c` register is recorded; the new `a`/`v` registers are returned. -/
def auxAccum (imMask d alphaPow value aReg vReg n : ℕ) : Out (ℕ × ℕ × ℕ) :=
  ⟨[.mul n d alphaPow,
    .pmul (n + 1) value imMask,
    .mul (n + 2) alphaPow (n + 1),
    .add (n + 3) aReg (n + 2),
    .mul (n + 4) alphaPow value,
    .add (n + 5) vReg (n + 4)],
   (n, n + 3, n + 5), n + 6⟩

theorem auxAccum_sound {ρ : ℕ → QM31} {imMask d alphaPow value aReg vReg n : ℕ}
    (hmask : ρ imMask = QM31.fromM31s 0 0 1 1)
    (h : AllHold ρ (auxAccum imMask d alphaPow value aReg vReg n).ops) :
    ρ (auxAccum imMask d alphaPow value aReg vReg n).res.1
      = ρ d * ρ alphaPow ∧
    ρ (auxAccum imMask d alphaPow value aReg vReg n).res.2.1
      = ρ aReg + ρ alphaPow * Deep.imQ (ρ value) ∧
    ρ (auxAccum imMask d alphaPow value aReg vReg n).res.2.2
      = ρ vReg + ρ alphaPow * ρ value := by
  rw [show (auxAccum imMask d alphaPow value aReg vReg n).ops =
    .mul n d alphaPow :: .pmul (n + 1) value imMask ::
    .mul (n + 2) alphaPow (n + 1) :: .add (n + 3) aReg (n + 2) ::
    .mul (n + 4) alphaPow value :: [.add (n + 5) vReg (n + 4)] from rfl,
    allHold_cons, allHold_cons, allHold_cons, allHold_cons, allHold_cons,
    allHold_cons] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, -⟩ := h
  simp only [Holds] at h1 h2 h3 h4 h5 h6
  refine ⟨h1, ?_, ?_⟩
  · show ρ (n + 3) = _
    rw [h4, h3, h2, hmask]
    rfl
  · show ρ (n + 5) = _
    rw [h6, h5]

/-- `finalize`: `b = d·v − a·P.y`. -/
def auxFinalize (d vSum aSum py n : ℕ) : Out ℕ :=
  ⟨[.mul n d vSum, .mul (n + 1) aSum py, .sub (n + 2) n (n + 1)],
   n + 2, n + 3⟩

theorem auxFinalize_sound {ρ : ℕ → QM31} {d vSum aSum py n : ℕ}
    (h : AllHold ρ (auxFinalize d vSum aSum py n).ops) :
    ρ (auxFinalize d vSum aSum py n).res
      = ρ d * ρ vSum - ρ aSum * ρ py := by
  rw [show (auxFinalize d vSum aSum py n).ops =
    .mul n d vSum :: .mul (n + 1) aSum py :: [.sub (n + 2) n (n + 1)] from rfl,
    allHold_cons, allHold_cons, allHold_cons] at h
  obtain ⟨h1, h2, h3, -⟩ := h
  simp only [Holds] at h1 h2 h3
  show ρ (n + 2) = _
  rw [h3, h1, h2]

end StwoVerifier.Gadgets
