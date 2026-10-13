/-
**The decommit base-point chain is the spec's per-layer fold points.**

`TwiddleChain.baseSeq` (what the circuit's double/translate walk
computes per lane, `twiddleChain1_sound`) is here identified with the
spec's `foldLineSubset` fold points: layer by layer, the base point is
the generator power of `foldIdx` — the inner-layer line coset's index
at the bit-reversed even folded position. Together with
`base0_eq_evenPoint` (the circle layer) this ties every fold-step-1
twiddle to the exact coordinate `Fri.decommit` folds with.
-/
import StwoVerifier.TwiddleChain
import StwoVerifier.SpecLemmas

namespace StwoVerifier.Bridge

open StwoVerifier StwoVerifier.Gadgets Finset

/-- Doubling a generator power doubles the index. -/
theorem toPoint_double (i : ℕ) :
    (PIdx.toPoint i).double = PIdx.toPoint (2 * i) := by
  rw [CPoint.double_eq_sq]
  unfold PIdx.toPoint PIdx.reduce circleOrder
  rw [CPoint.smul_eq_pow, CPoint.smul_eq_pow, ← pow_add]
  exact gen_pow_mod _ _ (by omega)

theorem toPoint_repeatedDouble (i : ℕ) :
    ∀ d, (PIdx.toPoint i).repeatedDouble d = PIdx.toPoint (2 ^ d * i)
  | 0 => by
    show PIdx.toPoint i = PIdx.toPoint (1 * i)
    rw [one_mul]
  | d + 1 => by
    show ((PIdx.toPoint i).repeatedDouble d).double = _
    rw [toPoint_repeatedDouble i d, toPoint_double,
      show 2 * (2 ^ d * i) = 2 ^ (d + 1) * i from by ring]

/-- A below-order `smul` is a `toPoint`. -/
theorem smul_eq_toPoint {m : ℕ} (hm : m < 2 ^ 31) :
    M31_CIRCLE_GEN.smul m = PIdx.toPoint m := by
  unfold PIdx.toPoint PIdx.reduce circleOrder
  rw [Nat.mod_eq_of_lt hm]

/-- The exponent walk of `baseSeq`: double `d` times, subtract the
order-2 generator when the bit is set. -/
def expSeq : ℕ → ℕ → List ℕ → List ℕ
  | _, _, [] => []
  | k, d, v :: rest =>
    PIdx.add' (2 ^ d * k) (PIdx.neg' (v * subgroupGen 1))
      :: expSeq (PIdx.add' (2 ^ d * k) (PIdx.neg' (v * subgroupGen 1))) 1 rest

/-- `baseSeq` from a generator power is `expSeq`, pointwise. -/
theorem baseSeq_toPoint :
    ∀ (vs : List ℕ) (k d : ℕ), (∀ v ∈ vs, v ≤ 1) →
      Gadgets.baseSeq (PIdx.toPoint k) d vs = (expSeq k d vs).map PIdx.toPoint
  | [], _, _, _ => rfl
  | v :: rest, k, d, hv => by
    have hnb : ((PIdx.toPoint k).repeatedDouble d).add
        ((M31_CIRCLE_GEN.smul (v * subgroupGen 1)).conjugate)
        = PIdx.toPoint (PIdx.add' (2 ^ d * k) (PIdx.neg' (v * subgroupGen 1))) := by
      rw [toPoint_repeatedDouble, smul_eq_toPoint (by
        have hvle := hv v List.mem_cons_self
        unfold subgroupGen M31_CIRCLE_LOG_ORDER
        have h30 : (2 : ℕ) ^ (31 - 1) = 1073741824 := by norm_num
        have h31 : (2 : ℕ) ^ 31 = 2147483648 := by norm_num
        have hle : v * 2 ^ (31 - 1) ≤ 1 * 2 ^ (31 - 1) :=
          Nat.mul_le_mul_right _ hvle
        omega),
        ← toPoint_neg, ← CPoint.mul_def, ← toPoint_add]
    show (((PIdx.toPoint k).repeatedDouble d).add
        ((M31_CIRCLE_GEN.smul (v * subgroupGen 1)).conjugate))
      :: Gadgets.baseSeq _ 1 rest = _
    rw [show (expSeq k d (v :: rest)).map PIdx.toPoint
      = PIdx.toPoint (PIdx.add' (2 ^ d * k) (PIdx.neg' (v * subgroupGen 1)))
        :: (expSeq (PIdx.add' (2 ^ d * k) (PIdx.neg' (v * subgroupGen 1))) 1
          rest).map PIdx.toPoint from rfl]
    rw [← baseSeq_toPoint rest _ 1 (fun x hx => hv x (List.mem_cons_of_mem _ hx)),
      ← hnb]

/-- The inner-layer fold index at layer `ℓ` (1-based): the folded even
position's domain index, as a generator exponent. -/
def foldIdx (b : ℕ → ℕ) (L ℓ : ℕ) : ℕ :=
  subgroupGen (L + 2 - ℓ)
    + ∑ t ∈ range (L - 1 - ℓ), b (t + ℓ + 1) * subgroupGen (t + 2)

/-- Geometric bound for bit-weighted descending powers. -/
theorem sum_pow_le (f : ℕ → ℕ) (hf : ∀ t, f t ≤ 1) (c : ℕ) :
    ∀ m, m ≤ c + 1 →
      ∑ t ∈ range m, f t * 2 ^ (c - t) ≤ 2 ^ (c + 1) - 2 ^ (c + 1 - m)
  | 0, _ => by simp
  | m + 1, hm => by
    rw [Finset.sum_range_succ]
    have ih := sum_pow_le f hf c m (by omega)
    have hterm : f m * 2 ^ (c - m) ≤ 2 ^ (c - m) := by
      calc f m * 2 ^ (c - m) ≤ 1 * 2 ^ (c - m) :=
        Nat.mul_le_mul_right _ (hf m)
      _ = 2 ^ (c - m) := one_mul _
    have hsplit : 2 ^ (c + 1 - m) = 2 * 2 ^ (c - m) := by
      rw [← pow_succ']
      congr 1
      omega
    have hle : 2 ^ (c + 1 - (m + 1)) = 2 ^ (c - m) := by congr 1; omega
    have hub : 2 ^ (c + 1 - m) ≤ 2 ^ (c + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    have hub2 : 2 ^ (c - m) ≤ 2 ^ (c + 1) :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem foldIdx_lt {b : ℕ → ℕ} (hb : ∀ i, b i ≤ 1) {L ℓ : ℕ}
    (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ ≤ L - 1) (hL30 : L ≤ 30) :
    foldIdx b L ℓ < 2 ^ 31 := by
  unfold foldIdx
  have hlead : subgroupGen (L + 2 - ℓ) ≤ 268435456 := by
    unfold subgroupGen M31_CIRCLE_LOG_ORDER
    calc (2 : ℕ) ^ (31 - (L + 2 - ℓ)) ≤ 2 ^ 28 :=
      Nat.pow_le_pow_right (by norm_num) (by omega)
    _ = 268435456 := by norm_num
  have hsum : ∑ t ∈ range (L - 1 - ℓ), b (t + ℓ + 1) * subgroupGen (t + 2)
      ≤ 1073741824 := by
    have h1 : ∀ t ∈ range (L - 1 - ℓ),
        b (t + ℓ + 1) * subgroupGen (t + 2) = b (t + ℓ + 1) * 2 ^ (29 - t) := by
      intro t _
      unfold subgroupGen M31_CIRCLE_LOG_ORDER
      rw [show (31 : ℕ) - (t + 2) = 29 - t from by omega]
    rw [Finset.sum_congr rfl h1]
    calc ∑ t ∈ range (L - 1 - ℓ), b (t + ℓ + 1) * 2 ^ (29 - t)
        ≤ 2 ^ 30 - 2 ^ (30 - (L - 1 - ℓ)) :=
          sum_pow_le (fun t => b (t + ℓ + 1)) (fun t => hb _) 29 _ (by omega)
      _ ≤ 2 ^ 30 := Nat.sub_le _ _
      _ = 1073741824 := by norm_num
  have h31 : (2 : ℕ) ^ 31 = 2147483648 := by norm_num
  have hcomb := Nat.add_le_add hlead hsum
  omega

theorem subgroupGen_one_lit : subgroupGen 1 = (1073741824 : ℕ) := by
  show (2 : ℕ) ^ (31 - 1) = 1073741824
  norm_num

/-- The translate-step arithmetic, stated over `ℕ` (the `PIdx`-typed
equality otherwise hides the goal from `omega`). -/
theorem mod_shift_cancel {qI F n1 : ℕ} (hq : qI < 2147483648)
    (hF : F < 2147483648) (hn : n1 ≤ 1)
    (hsplit : qI = F + n1 * 1073741824) :
    (qI + (2147483648 - n1 * 1073741824 % 2147483648) % 2147483648)
      % 2147483648 = F := by
  omega

theorem mod_double_cancel {Fl Fs n1 : ℕ} (hFs : Fs < 2147483648) (hn : n1 ≤ 1)
    (hdouble : 2 * Fl = Fs + n1 * 1073741824) :
    (2 * Fl + (2147483648 - n1 * 1073741824 % 2147483648) % 2147483648)
      % 2147483648 = Fs := by
  omega

/-- The first translate lands on `foldIdx 1`. -/
theorem foldIdx_one {b : ℕ → ℕ} (hb : ∀ i, b i ≤ 1) {L : ℕ}
    (hL2 : 2 ≤ L) (hL30 : L ≤ 30) :
    PIdx.add' (2 ^ 0 * queryIndex b L) (PIdx.neg' (b 1 * subgroupGen 1))
      = foldIdx b L 1 := by
  have hq := queryIndex_lt hb hL2 hL30
  have hsplit : queryIndex b L = foldIdx b L 1 + b 1 * subgroupGen 1 := by
    unfold queryIndex foldIdx
    rw [show L - 1 = (L - 2) + 1 from by omega, Finset.sum_range_succ',
      show L + 2 - 1 = L + 1 from by omega,
      show L - 2 + 1 - 1 = L - 2 from by omega]
    rw [Finset.sum_congr rfl fun k _ => by
      rw [show subgroupGen (k + 1 + 1) = subgroupGen (k + 2) from rfl]]
    simp only [Nat.zero_add]
    ring
  have hfl := foldIdx_lt hb (le_refl 1) (by omega) hL30
  have hb1 := hb 1
  have h31 : (2 : ℕ) ^ 31 = 2147483648 := by norm_num
  rw [subgroupGen_one_lit] at hsplit ⊢
  rw [pow_zero, one_mul]
  rw [h31] at hq hfl
  exact mod_shift_cancel hq hfl hb1 hsplit

/-- The layer step: double, then subtract the order-2 generator by the
next bit. -/
theorem foldIdx_succ {b : ℕ → ℕ} (hb : ∀ i, b i ≤ 1) {L ℓ : ℕ}
    (hL30 : L ≤ 30) (hℓ1 : 1 ≤ ℓ) (hℓ : ℓ + 1 ≤ L - 1) :
    PIdx.add' (2 ^ 1 * foldIdx b L ℓ) (PIdx.neg' (b (ℓ + 1) * subgroupGen 1))
      = foldIdx b L (ℓ + 1) := by
  have hdouble : 2 * foldIdx b L ℓ
      = foldIdx b L (ℓ + 1) + b (ℓ + 1) * subgroupGen 1 := by
    unfold foldIdx
    rw [Nat.mul_add, Finset.mul_sum]
    have hlead : 2 * subgroupGen (L + 2 - ℓ) = subgroupGen (L + 2 - (ℓ + 1)) := by
      unfold subgroupGen M31_CIRCLE_LOG_ORDER
      rw [← pow_succ']
      congr 1
      omega
    have hterm : ∀ t ∈ range (L - 1 - ℓ),
        2 * (b (t + ℓ + 1) * subgroupGen (t + 2))
          = b (t + ℓ + 1) * subgroupGen (t + 1) := by
      intro t ht
      have ht' := Finset.mem_range.mp ht
      unfold subgroupGen M31_CIRCLE_LOG_ORDER
      rw [← Nat.mul_assoc, Nat.mul_comm 2 (b (t + ℓ + 1)), Nat.mul_assoc,
        ← pow_succ', show (31 : ℕ) - (t + 2) + 1 = 31 - (t + 1) from by omega]
    rw [Finset.sum_congr rfl hterm, hlead,
      show L - 1 - ℓ = (L - 1 - (ℓ + 1)) + 1 from by omega,
      Finset.sum_range_succ']
    have hshift : ∀ t ∈ range (L - 1 - (ℓ + 1)),
        b (t + 1 + ℓ + 1) * subgroupGen (t + 1 + 1)
          = b (t + (ℓ + 1) + 1) * subgroupGen (t + 2) := by
      intro t _
      rw [show t + 1 + ℓ + 1 = t + (ℓ + 1) + 1 from by omega]
    rw [Finset.sum_congr rfl hshift]
    simp only [Nat.zero_add]
    ring
  have hfl := foldIdx_lt hb (by omega : 1 ≤ ℓ + 1) (by omega) hL30
  have hb1 := hb (ℓ + 1)
  have h31 : (2 : ℕ) ^ 31 = 2147483648 := by norm_num
  rw [subgroupGen_one_lit] at hdouble ⊢
  rw [h31] at hfl
  exact mod_double_cancel hfl hb1 hdouble

end StwoVerifier.Bridge
