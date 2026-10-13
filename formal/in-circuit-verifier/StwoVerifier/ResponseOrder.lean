/-
**`treesPairs` in closed form for the circuit statement's column
shapes.** Every circuit-AIR column samples either `[oods]` or
`[prev, oods]` (the cumulative sums), so the spec's push-order pair
list (`BatchesFlat.treesPairs`) decomposes into two recursions that
mirror `collect_oods_responses`' emission order exactly: one pushed
pair per single-sample column, and the periodicity duplicate, the
previous-row pair and the OODS pair — in that order — per two-sample
column, the random power advancing once per pushed pair. Matching the
emitter's response registers against these lists is then pointwise.
-/
import StwoVerifier.BatchesFlat

namespace StwoVerifier.Quotients

open StwoVerifier

/-! ### Per-column closed forms -/

theorem columnPairs_single (step : PointF) (rc pow : QM31) (fc : ℕ)
    (pt : PointQ) (v : QM31) (L : Nat) :
    columnPairs step rc pow fc [pt] [v] L = [(pt, ⟨fc, v, pow⟩)] := by
  simp [columnPairs, pushedPairs]

theorem columnPow_single (rc pow : QM31) (pt : PointQ) (v : QM31) :
    columnPow rc pow [pt] [v] = pow * rc := by
  simp [columnPow]

theorem columnPairs_double (step : PointF) (rc pow : QM31) (fc : ℕ)
    (prevPt pt : PointQ) (vp vo : QM31) (L : Nat) :
    columnPairs step rc pow fc [prevPt, pt] [vp, vo] L
      = [(pt.add (PointF.intoQ (step.repeatedDouble L)), ⟨fc, vo, pow⟩),
         (prevPt, ⟨fc, vp, pow * rc⟩), (pt, ⟨fc, vo, pow * rc * rc⟩)] := by
  simp [columnPairs, pushedPairs]

theorem columnPow_double (rc pow : QM31) (prevPt pt : PointQ) (vp vo : QM31) :
    columnPow rc pow [prevPt, pt] [vp, vo] = pow * rc ^ 3 := by
  simp [columnPow]
  ring

/-! ### Runs of single-sample columns -/

/-- The pairs of a run of single-sample columns at point `pt`: one
pushed pair per column, the power advancing once each. -/
noncomputable def singlesPairs (rc : QM31) (pt : PointQ) : List QM31 → QM31 → ℕ →
    List (PointQ × NumeratorData) × QM31 × ℕ
  | [], pow, fc => ([], pow, fc)
  | v :: rest, pow, fc =>
    let r := singlesPairs rc pt rest (pow * rc) (fc + 1)
    ((pt, ⟨fc, v, pow⟩) :: r.1, r.2)

theorem treePairs_singles (step : PointF) (rc : QM31) (pt : PointQ) :
    ∀ (vals : List QM31) (logs : List Nat) (pow : QM31) (fc : ℕ),
      vals.length ≤ logs.length →
      treePairs step rc pow fc
        ((List.replicate vals.length [pt]).zip
          ((vals.map fun v => [v]).zip logs))
        = singlesPairs rc pt vals pow fc
  | [], _, pow, fc, _ => rfl
  | v :: rest, [], pow, fc, hlen => absurd hlen (by simp)
  | v :: rest, L :: logs, pow, fc, hlen => by
    show (columnPairs step rc pow fc [pt] [v] L ++
        (treePairs step rc (columnPow rc pow [pt] [v]) (fc + 1)
          ((List.replicate rest.length [pt]).zip
            ((rest.map fun v => [v]).zip logs))).1,
      (treePairs step rc (columnPow rc pow [pt] [v]) (fc + 1)
        ((List.replicate rest.length [pt]).zip
          ((rest.map fun v => [v]).zip logs))).2) = _
    rw [columnPairs_single, columnPow_single,
      treePairs_singles step rc pt rest logs (pow * rc) (fc + 1)
        (by simpa using hlen)]
    rfl

/-! ### Runs of two-sample columns -/

/-- The pairs of a run of two-sample (cumulative-sum) columns: per
column the periodicity duplicate at `pt + step·2^log` carrying the
OODS value, the previous-row pair, then the OODS pair — the circuit's
response order — with the power advancing once per pair. -/
noncomputable def doublesPairs (step : PointF) (rc : QM31) (pt prevPt : PointQ) :
    List (QM31 × QM31) → List Nat → QM31 → ℕ →
    List (PointQ × NumeratorData) × QM31 × ℕ
  | [], _, pow, fc => ([], pow, fc)
  | _ :: _, [], pow, fc => ([], pow, fc)
  | (vp, vo) :: rest, L :: logs, pow, fc =>
    let r := doublesPairs step rc pt prevPt rest logs (pow * rc ^ 3) (fc + 1)
    ((pt.add (PointF.intoQ (step.repeatedDouble L)), ⟨fc, vo, pow⟩)
      :: (prevPt, ⟨fc, vp, pow * rc⟩) :: (pt, ⟨fc, vo, pow * rc * rc⟩)
      :: r.1, r.2)

theorem treePairs_doubles (step : PointF) (rc : QM31) (pt prevPt : PointQ) :
    ∀ (pairs : List (QM31 × QM31)) (logs : List Nat) (pow : QM31) (fc : ℕ),
      pairs.length ≤ logs.length →
      treePairs step rc pow fc
        ((List.replicate pairs.length [prevPt, pt]).zip
          ((pairs.map fun p => [p.1, p.2]).zip logs))
        = doublesPairs step rc pt prevPt pairs logs pow fc
  | [], _, pow, fc, _ => rfl
  | p :: rest, [], pow, fc, hlen => absurd hlen (by simp)
  | (vp, vo) :: rest, L :: logs, pow, fc, hlen => by
    show (columnPairs step rc pow fc [prevPt, pt] [vp, vo] L ++
        (treePairs step rc (columnPow rc pow [prevPt, pt] [vp, vo]) (fc + 1)
          ((List.replicate rest.length [prevPt, pt]).zip
            ((rest.map fun p => [p.1, p.2]).zip logs))).1,
      (treePairs step rc (columnPow rc pow [prevPt, pt] [vp, vo]) (fc + 1)
        ((List.replicate rest.length [prevPt, pt]).zip
          ((rest.map fun p => [p.1, p.2]).zip logs))).2) = _
    rw [columnPairs_double, columnPow_double,
      treePairs_doubles step rc pt prevPt rest logs (pow * rc ^ 3) (fc + 1)
        (by simpa using hlen)]
    rfl

/-! ### State-compositional appends -/

/-- `treePairs` over concatenated column runs: the second run continues
from the first run's power and counter. -/
theorem treePairs_append (step : PointF) (rc : QM31) :
    ∀ (c1 c2 : List (List PointQ × List QM31 × Nat)) (pow : QM31) (fc : ℕ),
      treePairs step rc pow fc (c1 ++ c2)
        = ((treePairs step rc pow fc c1).1
            ++ (treePairs step rc (treePairs step rc pow fc c1).2.1
                (treePairs step rc pow fc c1).2.2 c2).1,
           (treePairs step rc (treePairs step rc pow fc c1).2.1
             (treePairs step rc pow fc c1).2.2 c2).2)
  | [], c2, pow, fc => by
    show treePairs step rc pow fc c2 = ([] ++ (treePairs step rc pow fc c2).1,
      (treePairs step rc pow fc c2).2)
    rw [List.nil_append]
  | (colPoints, colValues, logSize) :: c1, c2, pow, fc => by
    show (columnPairs step rc pow fc colPoints colValues logSize ++
        (treePairs step rc (columnPow rc pow colPoints colValues) (fc + 1)
          (c1 ++ c2)).1,
      (treePairs step rc (columnPow rc pow colPoints colValues) (fc + 1)
        (c1 ++ c2)).2) = _
    rw [treePairs_append step rc c1 c2 (columnPow rc pow colPoints colValues)
      (fc + 1)]
    show (columnPairs step rc pow fc colPoints colValues logSize ++
      ((treePairs step rc (columnPow rc pow colPoints colValues) (fc + 1) c1).1
        ++ _), _) = _
    rw [← List.append_assoc]
    rfl

end StwoVerifier.Quotients
