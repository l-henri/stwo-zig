/-
**`collect_oods_responses`, part 1: the period generators**
(`src/frontends/circuit/stark_verifier/oods.zig` `period_generators`,
stwo-zig `4afa09dbf`).

Per component, the circuit computes `component_size · trace_gen` from
the bits of the (power-of-two) component size: starting from the trace
generator, it doubles a scalar point per bit position and accumulates
`bit · coords` lane-wise, so a one-hot bit pattern selects the
`2^log`-fold generator. `periodChain_lane` is the general linear form
(each lane is the bit-weighted coordinate sum); `periodGensG_lane`
specializes it to one-hot lanes, producing exactly the spec's period
shift `canonicStep(lifting).repeatedDouble(log + 1)` (the committed
column log is blowup-extended, which absorbs the lifting offset:
`subgroupGen(l+1)·2^(log+1) = subgroupGen(l)·2^log`).
-/
import StwoVerifier.TwiddleChain
import StwoVerifier.FoldBridge

namespace StwoVerifier.Gadgets

open StwoVerifier StwoVerifier.Gates StwoVerifier.Bridge

/-! ### Embedding facts -/

theorem fromBase_eq_baseHom (x : F) : QM31.fromBase x = baseHom x := rfl

/-- `intoQ` commutes with the group law. -/
theorem intoQ_add (p q : PointF) :
    PointF.intoQ (p.add q) = (PointF.intoQ p).add (PointF.intoQ q) := by
  unfold PointF.intoQ CPoint.add
  simp only [fromBase_eq_baseHom, map_mul, map_sub, map_add]

theorem intoQ_double (p : PointF) :
    PointF.intoQ p.double = (PointF.intoQ p).double := by
  unfold CPoint.double
  exact intoQ_add p p

/-- An embedded on-circle point satisfies the circle equation in `QM31`. -/
theorem intoQ_onCircle {p : PointF} (hp : OnCircle p) :
    (PointF.intoQ p).x * (PointF.intoQ p).x
      + (PointF.intoQ p).y * (PointF.intoQ p).y = 1 := by
  unfold PointF.intoQ
  show QM31.fromBase p.x * QM31.fromBase p.x
    + QM31.fromBase p.y * QM31.fromBase p.y = 1
  simp only [fromBase_eq_baseHom, ← map_mul, ← map_add]
  rw [hp]
  exact map_one baseHom

/-! ### The period-generator chain -/

/-- One doubling-and-accumulate step per size bit (`period_generators`'
loop body): `gen ← double gen; acc ← acc + bit ·ₗ gen`. -/
def periodChain (one : ℕ) : List SimdReg → PointReg → SimdReg → SimdReg →
    ℕ → Out (SimdReg × SimdReg)
  | [], _, ax, ay, n => ⟨[], (ax, ay), n⟩
  | b :: rest, gen, ax, ay, n =>
    let g2 := doublePoint one gen n
    let sx := simdScalarMul b g2.res.x g2.next
    let sy := simdScalarMul b g2.res.y sx.next
    let nx := simdAdd ax sx.res sy.next
    let ny := simdAdd ay sy.res nx.next
    let tail := periodChain one rest g2.res nx.res ny.res ny.next
    ⟨g2.ops ++ sx.ops ++ sy.ops ++ nx.ops ++ ny.ops ++ tail.ops,
     tail.res, tail.next⟩

/-- `period_generators`: the trace generator as constants, `bit₀ ·ₗ gen`,
then the chain over the remaining bits. -/
def periodGensG (one : ℕ) (g : PointF) (bits : List SimdReg) (n : ℕ) :
    Out (SimdReg × SimdReg) :=
  match bits with
  | [] => ⟨[], (dummySimd, dummySimd), n⟩
  | b0 :: rest =>
    let cx : ℕ := n
    let cy : ℕ := n + 1
    let sx := simdScalarMul b0 cx (n + 2)
    let sy := simdScalarMul b0 cy sx.next
    let tail := periodChain one rest ⟨cx, cy⟩ sx.res sy.res sy.next
    ⟨.const cx (QM31.fromBase g.x) :: .const cy (QM31.fromBase g.y) ::
      (sx.ops ++ sy.ops ++ tail.ops), tail.res, tail.next⟩

/- Next (part 2): `periodChain_lane` — each output lane is the
bit-weighted coordinate sum `Σ_t bit_t(c) · (double^t g)`, hence with
one-hot lanes the `2^log`-fold generator — then the per-component
periodicity points (`addPoints` with the unpacked lanes), the
previous-row point (`addPoints` with the conjugated generator
constants), and the response-list ↔ `treesPairs` correspondence. -/

end StwoVerifier.Gadgets
