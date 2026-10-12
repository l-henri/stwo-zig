/-
**Scope A / deliverable 3, first pieces: the OODS composition
reconstruction** (`src/frontends/circuit/stark_verifier/oods.zig` and
`builder/ops.zig`, stwo-zig `4afa09dbf`).

`from_partial_evals` recombines four wires on the extension basis
`1, i, u, iu`; `extract_expected_composition_eval` is
`left + doubleX^(k−2)(oods.x) · right` over the two composition halves.
Both are proven to compute the *spec's* functions:
`StwoVerifier.fromPartialEvals` and (via `reconstructChunks_two`) the
spec's `reconstructChunks` at the pinned `COMPOSITION_LOG_SPLIT = 1` —
the exact value `NativeAccepts` compares against the AIR evaluation.
-/
import StwoVerifier.CircleGadgets
import StwoVerifier.Verifier

namespace StwoVerifier.Gadgets

open StwoVerifier StwoVerifier.Gates

/-- `from_partial_evals`: interned basis constants, then the `eval!` chain
`((v0 + v1·i) + v2·u) + v3·iu`. -/
def fromPartialEvalsG (v0 v1 v2 v3 n : ℕ) : Out ℕ :=
  ⟨[.const n (QM31.fromM31s 0 1 0 0),
    .const (n + 1) (QM31.fromM31s 0 0 1 0),
    .const (n + 2) (QM31.fromM31s 0 0 0 1),
    .mul (n + 3) v1 n,
    .add (n + 4) v0 (n + 3),
    .mul (n + 5) v2 (n + 1),
    .add (n + 6) (n + 4) (n + 5),
    .mul (n + 7) v3 (n + 2),
    .add (n + 8) (n + 6) (n + 7)],
   n + 8, n + 9⟩

theorem fromPartialEvalsG_sound {ρ : ℕ → QM31} {v0 v1 v2 v3 n : ℕ}
    (h : AllHold ρ (fromPartialEvalsG v0 v1 v2 v3 n).ops) :
    ρ (fromPartialEvalsG v0 v1 v2 v3 n).res
      = fromPartialEvals [ρ v0, ρ v1, ρ v2, ρ v3] := by
  rw [show (fromPartialEvalsG v0 v1 v2 v3 n).ops =
    .const n (QM31.fromM31s 0 1 0 0) ::
    .const (n + 1) (QM31.fromM31s 0 0 1 0) ::
    .const (n + 2) (QM31.fromM31s 0 0 0 1) ::
    .mul (n + 3) v1 n ::
    .add (n + 4) v0 (n + 3) ::
    .mul (n + 5) v2 (n + 1) ::
    .add (n + 6) (n + 4) (n + 5) ::
    .mul (n + 7) v3 (n + 2) ::
    [.add (n + 8) (n + 6) (n + 7)] from rfl,
    allHold_cons, allHold_cons, allHold_cons, allHold_cons, allHold_cons,
    allHold_cons, allHold_cons, allHold_cons, allHold_cons] at h
  obtain ⟨hi, hu, hiu, hm1, ha1, hm2, ha2, hm3, ha3, -⟩ := h
  simp only [Holds] at hi hu hiu hm1 ha1 hm2 ha2 hm3 ha3
  show ρ (n + 8) = _
  rw [ha3, ha2, ha1, hm1, hm2, hm3, hi, hu, hiu]
  unfold fromPartialEvals
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  try ring

/-- `extract_expected_composition_eval`:
`left + doubleX^(k−2)(oods.x) · right` (the loop reuses the
`cosetVanishing` emitter, which is exactly iterated `doubleX`). -/
def extractExpectedCompositionEvalG (one : ℕ) (evals : Fin 8 → ℕ)
    (oodsX : ℕ) (k n : ℕ) : Out ℕ :=
  let left := fromPartialEvalsG (evals 0) (evals 1) (evals 2) (evals 3) n
  let right := fromPartialEvalsG (evals 4) (evals 5) (evals 6) (evals 7) left.next
  let x := cosetVanishing one oodsX (k - 2) right.next
  ⟨left.ops ++ right.ops ++ x.ops ++
    [.mul x.next x.res right.res, .add (x.next + 1) left.res x.next],
   x.next + 1, x.next + 2⟩

theorem extractExpectedCompositionEvalG_sound {ρ : ℕ → QM31} {one : ℕ}
    {evals : Fin 8 → ℕ} {oodsX : ℕ} {k n : ℕ}
    (hone : ρ one = 1)
    (h : AllHold ρ (extractExpectedCompositionEvalG one evals oodsX k n).ops) :
    ρ (extractExpectedCompositionEvalG one evals oodsX k n).res
      = fromPartialEvals [ρ (evals 0), ρ (evals 1), ρ (evals 2), ρ (evals 3)]
        + CPoint.doubleX^[k - 2] (ρ oodsX) *
          fromPartialEvals [ρ (evals 4), ρ (evals 5), ρ (evals 6), ρ (evals 7)] := by
  unfold extractExpectedCompositionEvalG at h ⊢
  rw [allHold_append, allHold_append, allHold_append, allHold_cons,
    allHold_cons] at h
  obtain ⟨⟨⟨hleft, hright⟩, hx⟩, hmul, hadd, -⟩ := h
  simp only [Holds] at hmul hadd
  have hl := fromPartialEvalsG_sound hleft
  have hr := fromPartialEvalsG_sound hright
  have hxv := cosetVanishing_sound hone (k - 2) _ hx
  show ρ _ = _
  rw [hadd, hmul, hxv, hl, hr]

end StwoVerifier.Gadgets
