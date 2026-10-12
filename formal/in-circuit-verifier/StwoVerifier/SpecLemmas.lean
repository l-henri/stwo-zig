/-
**Spec-side lemmas for the assembly proofs**, enabled by the functional
refactor of the verifier spec's loops.

At the pinned profile `log_last_layer_degree_bound = 0`, the last-layer
polynomial is a single coefficient, so the spec's last-layer check is
exactly "every remaining evaluation equals that coefficient" — which is
the in-circuit decommit's final battery of `eq` gates.
-/
import StwoVerifier.Fri

namespace StwoVerifier.SpecLemmas

open StwoVerifier

/-- A singleton `LinePoly` is the constant polynomial. -/
theorem linePolyEval_singleton (c x : QM31) : linePolyEval [c] x = c := rfl

/-- At last-layer degree bound 0, the spec's check is pointwise equality
with the constant coefficient (given matching lengths). -/
theorem lastLayerCheck_const (c : Fri.Committed) (c0 : QM31)
    (hpoly : c.lastLayerPoly = [c0])
    (positions : List Nat) (evals : List QM31)
    (hlen : positions.length = evals.length) :
    Fri.lastLayerCheck c positions evals = .ok ()
      ↔ ∀ e ∈ evals, e = c0 := by
  unfold Fri.lastLayerCheck
  rw [if_neg (by omega)]
  constructor
  · intro h e he
    by_contra hne
    rw [if_pos ?_] at h
    · exact absurd h (by simp)
    · rw [List.any_eq_true]
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      refine ⟨(positions.getD i 0, evals[i]), ?_, ?_⟩
      · have : (positions.zip evals)[i]? = some (positions.getD i 0, evals[i]) := by
          rw [List.getElem?_zip_eq_some]
          refine ⟨?_, ?_⟩
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
            rfl
          · exact List.getElem?_eq_getElem hi
        exact List.mem_of_getElem? this
      · simp only [decide_eq_true_eq]
        rw [hpoly, linePolyEval_singleton]
        exact hne
  · intro h
    rw [if_neg ?_]
    · rfl
    · intro hany
      rw [List.any_eq_true] at hany
      obtain ⟨pe, hmem, hviol⟩ := hany
      simp only [decide_eq_true_eq] at hviol
      apply hviol
      rw [hpoly, linePolyEval_singleton]
      exact h pe.2 (List.of_mem_zip hmem).2

end StwoVerifier.SpecLemmas
