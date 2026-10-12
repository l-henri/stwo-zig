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

/-- The numerator subtraction chain: `num − Σ cᵢ·valᵢ`. -/
def subCoeffs : List (ℕ × ℕ) → ℕ → ℕ → Out ℕ
  | [], num, n => ⟨[], num, n⟩
  | (coeff, value) :: rest, num, n =>
    let tail := subCoeffs rest (n + 1) (n + 2)
    ⟨.mul n coeff value :: .sub (n + 1) num n :: tail.ops, tail.res, tail.next⟩

theorem subCoeffs_sound {ρ : ℕ → QM31} :
    ∀ (cvs : List (ℕ × ℕ)) (num n : ℕ),
      AllHold ρ (subCoeffs cvs num n).ops →
      ρ (subCoeffs cvs num n).res
        = ρ num - (cvs.map fun (c, v) => ρ c * ρ v).sum := by
  intro cvs
  induction cvs with
  | nil => intro num n _; simp [subCoeffs]
  | cons cv rest ih =>
    intro num n h
    obtain ⟨coeff, value⟩ := cv
    rw [show (subCoeffs ((coeff, value) :: rest) num n).ops =
      .mul n coeff value :: .sub (n + 1) num n ::
        (subCoeffs rest (n + 1) (n + 2)).ops from rfl,
      allHold_cons, allHold_cons] at h
    obtain ⟨h1, h2, hrest⟩ := h
    simp only [Holds] at h1 h2
    show ρ (subCoeffs rest (n + 1) (n + 2)).res = _
    rw [ih (n + 1) (n + 2) hrest, h2, h1]
    simp only [List.map_cons, List.sum_cons]
    ring

/-- The per-point per-query quotient:
`num = a·q_y + b − Σ cᵢ·valᵢ`, `den = d·q_x − (e·q_y + f)`,
`quot = num / den` (a `div` gate: a guess with `quot·den = num`). -/
def deepQuery (aSum b d e f qx qy : ℕ) (cvs : List (ℕ × ℕ)) (n : ℕ) : Out ℕ :=
  let num0ops : List Op := [.mul n aSum qy, .add (n + 1) n b]
  let num := subCoeffs cvs (n + 1) (n + 2)
  let m := num.next
  ⟨num0ops ++ num.ops ++
    [.mul m d qx, .mul (m + 1) e qy, .add (m + 2) (m + 1) f,
     .sub (m + 3) m (m + 2),
     .guess (m + 4), .mul (m + 5) (m + 4) (m + 3), .eq (m + 5) num.res],
   m + 4, m + 6⟩

/-- The quotient gate law: the output register satisfies
`quot · den = num` with the stated numerator and denominator values. -/
theorem deepQuery_sound {ρ : ℕ → QM31} {aSum b d e f qx qy : ℕ}
    {cvs : List (ℕ × ℕ)} {n : ℕ}
    (h : AllHold ρ (deepQuery aSum b d e f qx qy cvs n).ops) :
    ρ (deepQuery aSum b d e f qx qy cvs n).res *
        (ρ d * ρ qx - (ρ e * ρ qy + ρ f))
      = ρ aSum * ρ qy + ρ b - (cvs.map fun (c, v) => ρ c * ρ v).sum := by
  unfold deepQuery at h
  rw [allHold_append, allHold_append] at h
  obtain ⟨⟨hnum0, hnum⟩, h7⟩ := h
  rw [allHold_cons, allHold_cons, allHold_cons, allHold_cons, allHold_cons,
    allHold_cons, allHold_cons] at h7
  obtain ⟨hm1, hm2, hm3, hm4, hg, hm5, heq, -⟩ := h7
  rw [allHold_cons, allHold_cons] at hnum0
  obtain ⟨h1, h2, -⟩ := hnum0
  simp only [Holds] at h1 h2 hm1 hm2 hm3 hm4 hm5 heq
  have hnumval := subCoeffs_sound cvs (n + 1) (n + 2) hnum
  show ρ ((subCoeffs cvs (n + 1) (n + 2)).next + 4) * _ = _
  rw [← hm1, ← hm2, ← hm3, ← hm4, ← hm5, heq, hnumval, h2, h1]

/-- The alpha-power chain: starting from the interned `−2u`, multiply by
`α` once per further response. Returns the power registers in order. -/
def alphaChain (start alpha : ℕ) : Nat → ℕ → Out (List ℕ)
  | 0, n => ⟨[], [], n⟩
  | k + 1, n =>
    let rest := alphaChain n alpha k (n + 1)
    ⟨.mul n start alpha :: rest.ops, start :: rest.res, rest.next⟩

theorem alphaChain_sound {ρ : ℕ → QM31} {alpha : ℕ} :
    ∀ (k : Nat) (start n : ℕ),
      AllHold ρ (alphaChain start alpha k n).ops →
      ∀ i, i < k →
        ρ ((alphaChain start alpha k n).res.getD i 0)
          = ρ start * ρ alpha ^ i := by
  intro k
  induction k with
  | zero => intro start n _ i hi; omega
  | succ k ih =>
    intro start n h i hi
    rw [show (alphaChain start alpha (k + 1) n).ops =
      .mul n start alpha :: (alphaChain n alpha k (n + 1)).ops from rfl,
      allHold_cons] at h
    obtain ⟨h1, hrest⟩ := h
    simp only [Holds] at h1
    cases i with
    | zero =>
      show ρ start = ρ start * ρ alpha ^ 0
      rw [pow_zero, mul_one]
    | succ i =>
      show ρ ((alphaChain n alpha k (n + 1)).res.getD i 0) = _
      rw [ih n (n + 1) hrest i (by omega), h1, pow_succ]
      ring

/-- The accumulate walk over one point's responses
(`(α'ᵢ, Vᵢ)` register pairs): threads the `a`/`v` registers and records
each response's coefficient register. -/
def auxAccumList (imMask d : ℕ) :
    List (ℕ × ℕ) → ℕ → ℕ → ℕ → Out (List ℕ × ℕ × ℕ)
  | [], aReg, vReg, n => ⟨[], ([], aReg, vReg), n⟩
  | (alphaPow, value) :: rest, aReg, vReg, n =>
    let st := auxAccum imMask d alphaPow value aReg vReg n
    let r := auxAccumList imMask d rest st.res.2.1 st.res.2.2 st.next
    ⟨st.ops ++ r.ops, (st.res.1 :: r.res.1, r.res.2), r.next⟩

/-- Walk soundness: the final `a`/`v` registers hold the initial values
plus the response sums, and coefficient `i` holds `d·α'ᵢ`. -/
theorem auxAccumList_sound {ρ : ℕ → QM31} {imMask d : ℕ}
    (hmask : ρ imMask = QM31.fromM31s 0 0 1 1) :
    ∀ (rs : List (ℕ × ℕ)) (aReg vReg n : ℕ),
      AllHold ρ (auxAccumList imMask d rs aReg vReg n).ops →
      (auxAccumList imMask d rs aReg vReg n).res.1.length = rs.length ∧
      (∀ i, i < rs.length →
        ρ ((auxAccumList imMask d rs aReg vReg n).res.1.getD i 0)
          = ρ d * ρ ((rs.getD i (0, 0)).1)) ∧
      ρ (auxAccumList imMask d rs aReg vReg n).res.2.1
        = ρ aReg + (rs.map fun (a, v) => ρ a * Deep.imQ (ρ v)).sum ∧
      ρ (auxAccumList imMask d rs aReg vReg n).res.2.2
        = ρ vReg + (rs.map fun (a, v) => ρ a * ρ v).sum := by
  intro rs
  induction rs with
  | nil =>
    intro aReg vReg n _
    refine ⟨rfl, fun i hi => by simp at hi, ?_, ?_⟩
    · show ρ aReg = ρ aReg + ([] : List QM31).sum
      simp
    · show ρ vReg = ρ vReg + ([] : List QM31).sum
      simp
  | cons r rest ih =>
    intro aReg vReg n h
    obtain ⟨alphaPow, value⟩ := r
    rw [show (auxAccumList imMask d ((alphaPow, value) :: rest) aReg vReg n).ops =
      (auxAccum imMask d alphaPow value aReg vReg n).ops ++
        (auxAccumList imMask d rest
          (auxAccum imMask d alphaPow value aReg vReg n).res.2.1
          (auxAccum imMask d alphaPow value aReg vReg n).res.2.2
          (auxAccum imMask d alphaPow value aReg vReg n).next).ops from rfl,
      allHold_append] at h
    obtain ⟨hstep, hrest⟩ := h
    obtain ⟨hc, ha, hv⟩ := auxAccum_sound hmask hstep
    obtain ⟨ihlen, ihc, iha, ihv⟩ := ih _ _ _ hrest
    refine ⟨?_, ?_, ?_, ?_⟩
    · show _ + 1 = _ + 1
      rw [ihlen]
    · intro i hi
      cases i with
      | zero => exact hc
      | succ i =>
        show ρ ((auxAccumList imMask d rest _ _ _).res.1.getD i 0) = _
        exact ihc i (by simpa using hi)
    · show ρ (auxAccumList imMask d rest _ _ _).res.2.1 = _
      rw [iha, ha]
      simp only [List.map_cons, List.sum_cons]
      ring
    · show ρ (auxAccumList imMask d rest _ _ _).res.2.2 = _
      rw [ihv, hv]
      simp only [List.map_cons, List.sum_cons]
      ring

/-- Pointwise-equal maps over a list have equal sums (getD form). -/
theorem map_sum_congr_getD {α : Type} [Inhabited α] (l : List α)
    (f g : α → QM31)
    (h : ∀ i, i < l.length → f (l.getD i default) = g (l.getD i default)) :
    (l.map f).sum = (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.map_cons, List.sum_cons]
    have h0 := h 0 (by simp)
    simp only [List.getD_cons_zero] at h0
    rw [h0]
    congr 1
    refine ih fun i hi => ?_
    have := h (i + 1) (by simpa using hi)
    simpa using this

instance : Inhabited (ℕ × ℕ) := ⟨(0, 0)⟩

end StwoVerifier.Gadgets
