/-
**Scope A / deliverable 4, first piece: the FRI fold**
(`src/frontends/circuit/stark_verifier/fri.zig` `fold_coset`, stwo-zig
`4afa09dbf`), at the pinned profile's `fold_step = 1`.

One fold is `(even + odd) + α·((even − odd)·t)` with the twiddle `t` a
gate-proven inverse (`simd.inv`: a guess constrained by `t·x = 1`). With
the QM31 field structure, the constraint pins `t = x⁻¹`, and the folded
value is exactly the spec's `Fri.foldLinePair even odd α x` — the same
formula the differentially-validated verifier runs for both the
circle-to-line layer (`x = p.y`) and every inner line layer.
-/
import StwoVerifier.Gates
import StwoVerifier.Fri
import StwoVerifier.FieldTower
import StwoVerifier.DeepIdentity

namespace StwoVerifier.Gadgets

open StwoVerifier StwoVerifier.Gates

/-- The base-field embedding as a ring homomorphism. -/
def baseHom : F →+* QM31 where
  toFun := QM31.fromBase
  map_one' := rfl
  map_mul' a b := by
    unfold QM31.fromBase CM31.fromBase
    refine QM31.ext' ?_ ?_ <;> show _ = _ <;>
      simp [QM31.mul_c0, QM31.mul_c1] <;> ext <;> simp
  map_zero' := rfl
  map_add' a b := by
    unfold QM31.fromBase CM31.fromBase
    ext <;> simp

theorem fromBase_inv (x : F) : QM31.fromBase x⁻¹ = (QM31.fromBase x)⁻¹ :=
  map_inv₀ baseHom x

theorem fromBase_ne_zero {x : F} (hx : x ≠ 0) : QM31.fromBase x ≠ 0 := by
  intro h
  exact hx (by
    have := congrArg (fun q : QM31 => q.c0.a) h
    simpa [QM31.fromBase, CM31.fromBase] using this)

/-- One `fold_coset` round at fold step 1:
`g = even + odd`, `h = (even − odd)·t`, `out = g + α·h`. -/
def foldCoset1 (even odd twiddle alpha n : ℕ) : Out ℕ :=
  ⟨[.add n even odd,
    .sub (n + 1) even odd,
    .mul (n + 2) (n + 1) twiddle,
    .mul (n + 3) alpha (n + 2),
    .add (n + 4) n (n + 3)],
   n + 4, n + 5⟩

/-- **Fold soundness.** If the gates hold and the twiddle is gate-proven
to invert the base-field point coordinate `x` (the `t·x = 1` constraint
`simd.inv` emits), the output register holds the spec's
`Fri.foldLinePair even odd α x`. -/
theorem foldCoset1_sound {ρ : ℕ → QM31} {even odd twiddle alpha n : ℕ} {x : F}
    (htw : ρ twiddle * QM31.fromBase x = 1)
    (h : AllHold ρ (foldCoset1 even odd twiddle alpha n).ops) :
    Fri.foldLinePair (ρ even) (ρ odd) (ρ alpha) x
      = .ok (ρ (foldCoset1 even odd twiddle alpha n).res) := by
  rw [show (foldCoset1 even odd twiddle alpha n).ops =
    .add n even odd :: .sub (n + 1) even odd :: .mul (n + 2) (n + 1) twiddle ::
    .mul (n + 3) alpha (n + 2) :: [.add (n + 4) n (n + 3)] from rfl,
    allHold_cons, allHold_cons, allHold_cons, allHold_cons, allHold_cons] at h
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := h
  simp only [Holds] at h1 h2 h3 h4 h5
  have hx : x ≠ 0 := by
    intro h0
    rw [h0] at htw
    simp [show QM31.fromBase 0 = 0 from rfl] at htw
  have htinv : ρ twiddle = (QM31.fromBase x)⁻¹ :=
    eq_inv_of_mul_eq_one_left htw
  unfold Fri.foldLinePair
  rw [if_neg hx]
  show Except.ok _ = Except.ok _
  congr 1
  show _ = ρ (n + 4)
  rw [h5, h1, h4, h3, h2, htinv]
  rw [show (ρ even - ρ odd).mulM31 x⁻¹
    = (ρ even - ρ odd) * QM31.fromBase x⁻¹ from by
      unfold QM31.mulM31 QM31.fromBase
      refine QM31.ext' ?_ ?_ <;> show _ = _ <;>
        simp [QM31.mul_c0, QM31.mul_c1, CM31.mulM31, CM31.fromBase] <;>
        ext <;> simp [CM31.mul_a, CM31.mul_b]]
  rw [fromBase_inv]
  try ring

end StwoVerifier.Gadgets
