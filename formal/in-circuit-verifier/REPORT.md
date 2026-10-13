# Report: verifier formalization, session of 2026-10-12

Per `VERIFIER_FORMALIZATION_BRIEF.md` §6. Checkout: worktree
`../stwo-zig-verifier-lean`, branch `formal/in-circuit-verifier` (cut from
`4afa09dbf`), Lean project `formal/in-circuit-verifier/` (Lean 4.33.1 +
Mathlib). Twenty-odd commits, nothing pushed. Every theorem checks with
`#print axioms` = `propext, Classical.choice, Quot.sound` only; no
`axiom` declarations, no `sorry`.

## Deliverable 1 — `NativeAccepts` + differential harness: **done**

**What is proven/validated.** `StwoVerifier.NativeAccepts`
(`StwoVerifier/Verifier.lean`) is an executable Lean spec of
`core/verifier.zig` `verify` under the `proving_5a7c5ed` revision,
parameterized by an abstract `Air`, sitting on executable specs of the
whole stack (channel, Merkle, FRI, DEEP quotients, PCS — see README table).
Fidelity is differential, as the brief prescribes:

- 366 of 366 mutation cases agree with the native Zig verifier —
  PCS-level (`CommitmentSchemeVerifier.verifyValues`) and statement-level
  (`core.verifier.verify` with a mock constant-composition AIR proved by
  the in-repo CPU prover), each at PoW 0 / 8 / 26, with a fixed mutation
  battery (including dropped/duplicated FRI layers and an over-long last
  layer) plus 48 seeded random corruptions per set. At PoW 8/26 the
  **error code** agrees too; the duplicated-layer case confirms the one
  documented deviation (commit-time vs decommit-time rejection of extra
  zero-fold layers) is verdict-invisible. The corpus was re-validated in
  full after the spec's loops were refactored into pure recursions for
  provability.
- Compile-time `#guard` vectors pin the channel law to Rust-oracle bytes
  (digests for `mix_u64`/`mix_u32s`/`mix_felts`/`mix_hash`, the
  `FriConfigV2` transcript mix on both channel variants, secure draws,
  24-bit query draws, PoW accept/reject at Stwo's grind nonces).
- Regenerate: `harness/harness.zig` (build command in its header), check:
  `lake exe diffcheck harness/<vectors>.json`.

**What remains trusted here.** The abstract `Air`'s two functions (mask
points, composition evaluation) — instantiating them with the circuit AIR
is scope B. The statement-level differential case used a mock AIR, so the
transcript/OODS/PCS *protocol* is differentially covered but the circuit
AIR's own evaluator is not yet. Stwo protocol soundness stays the
`StarkSound` hypothesis, as agreed.

**Statements to import** (all under `StwoVerifier.`): `NativeAccepts`,
`Pcs.verifyValues`, `Pcs.commit`, `Fri.commit`, `Fri.decommit`,
`Quotients.friAnswers`, `Merkle.verify`, `Channel.*` — these `def`s are
the spec your theorems should target; the harness is the evidence they
mean what the native verifier means.

## Deliverable 2 — circle arithmetic and query selection: **proven** (one caveat)

Gate model: `Gates.lean` (`Circuit::check` semantics + finalization
constraints on guesses), `Algebra.lean`/`FieldTower.lean` (the concrete
CM31/QM31 are commutative rings, indeed **fields** — norms + quadratic
reciprocity).

- Scalar circle gadgets (`CircleGadgets.lean`): `doubleX_sound`,
  `addPoints_sound`, `doublePoint_sound` (needs and states the explicit
  on-circle hypothesis — `2x² − 1` is doubling only on the circle),
  `cosetVanishing_sound`, `denomInverse_sound`.
- SIMD layer (`SimdGadgets.lean`): lane-wise ops, `Simd::eq` incl. the
  partial-wire mask, `assert_bits`, `guess_lsb`, and
  **`extractBits31_sound`**: the 31 extracted lanes are *the* binary
  digits of the lane's canonical M31 value (`BitDecomp.lean` carries the
  math; canonicity comes from `validate_extract_bits` excluding the
  all-ones encoding of 0).
- Point construction (`SelectQueries.lean`): `select`, `add_points_simd`,
  generator splats, the conditional-add loop (`buildLoop_lane`, on the
  circle law's commutative-monoid structure, `CircleGroup.lean`), and
  `selectQueriesPoint_sound`: the built lane point is
  `gen^(queryIndex bits L)`, conjugated exactly when bit 0 is set.
- The bridge (`SelectQueriesBridge.lean`): `queryIndex_eq_domainPoint` —
  that point **is** `(canonicDomain L).at' (bitReverseIndex pos L)`, the
  exact point `Quotients.friAnswers` evaluates (generator order `2³¹`
  kernel-checked; `toPoint` additive; digits/bit-reversal arithmetic).
  Exported end-to-end: **`selectQueries_domainPoint`** — gates hold ⇒ each
  lane's point is the spec's domain point at
  `bitReverseIndex ((lane input).val % 2^L) L`, matching the native
  `drawQueries` mask and `friAnswers` indexing verbatim.

**Caveat / remains trusted.** The channel-draw half
(`get_query_selection_input_from_channel`) — the in-circuit Blake2s
channel. starked-bitcoin's `Circuit/Channel.lean` has proven exactly this
(same builder, `draw_two_qm31s`); porting it into this project is
outstanding mechanical work, not new mathematics.

## Deliverables 3–4 — DEEP quotients and FRI: **core mathematics proven**

- `OodsGadgets.lean`: `from_partial_evals` and
  `extract_expected_composition_eval` compute the spec's extension-basis
  recombination and split-1 chunk reconstruction.
- `DeepIdentity.lean`: **`deep_term_eq`** — the circuit's
  `compute_fri_input` per-response quotient (the `−2u`-scaled `im`-line
  form) equals the spec's complex-conjugate line-coefficient quotient:
  numerator and denominator are each `−u` times the spec's
  (`num_identity`, `den_identity`), cancelling in the QM31 field. Batched:
  `num_identity_batched` + `circuit_num_regroup`; grouping-invariance:
  `Quotients.flattenBatches_pushEntry`.
- `FriGadgets.lean`: `foldCoset1_sound` — `fold_coset` at the pinned fold
  step 1 computes the spec's `Fri.foldLinePair` (both the circle-to-line
  and the inner line fold), with the twiddle pinned to `x⁻¹` by its
  product-one gate.
- Further FRI-decommit primitives: `select_by_index` and
  `validate_query_position_in_coset` (`SelectByIndex.lean`), `Simd::inv`
  lane soundness (the twiddle hypothesis), `sub_points_simd` and the
  `translate_to_base_point` loop (conjugate twin of the query loop), and
  `extractExpected_matches_spec` (the OODS gadget output equals
  `reconstructChunks` at the on-circle OODS point).
- `DeepGadgets.lean`: the `compute_fri_input` accumulation gadgets
  (`OodsPointAuxiliary` init/accumulate/finalize, the subtraction chain,
  the `div`-gate quotient, the alpha-power chain), each with a soundness
  lemma, capped by **`processGroupQuery_sound`**: for one sample group and
  one query, with the point/query/alpha registers pinned to spec values,
  the assembled gadget's `div` output **is** the spec's batch term —
  `Quotients.friAnswers`' summand, numerator `.mulCM31` inverse
  denominator — via `den_identity` + `num_identity_batched`. This is the
  per-group per-query capstone; what remains above it is the walk over
  groups/queries and the response-register plumbing. Its side conditions
  are partly discharged from gates already: `chain_alphas` (alpha-power
  chain registers satisfy the alpha hypothesis; the emitter's chain is
  global across responses, so per-group lists are subsequences of it),
  and the guard lemmas `prodChain_all_ne_zero` + `den_nonzero_of_reg`
  (the single `inv(prod)` gate forces each chained register nonzero).
  The emitter's product is over the `d = im(P.y)` registers, so what the
  gates provide is `im(P.y) ≠ 0` per sample point; the mathematical step
  from there is **`den_nonzero`** (`DenNonzero.lean`): at an on-circle
  `P` with `im(P.y) ≠ 0`, the spec denominator is nonzero at every M31
  circle point — the conjugate line meets the circle only at `P` and
  `P̄` (a quadratic with three distinct roots is identically zero, which
  forces `im(P.y) = 0`). Together with `prodChain_all_ne_zero`, the
  capstone's `hden` hypothesis is fully discharged from gates — the
  open-question-1 mechanism is now a theorem end to end.
- `lastLayerEqs_spec` (`FriGadgets.lean`): the decommit's closing `eq`
  battery holding is exactly `Fri.lastLayerCheck` succeeding at the
  pinned last-layer degree bound 0.
- `unpackIdx_sound` (`FriGadgets.lean`): `simd.unpack`'s lane extraction
  — the scalar register holds the base-field lift of the wire's lane,
  which is the link from the SIMD query-point registers
  (`selectQueries_domainPoint`) to `compute_fri_input`'s scalar
  `q_x`/`q_y` inputs.

- **The `compute_fri_input` outer walk is done** (`DeepRow.lean`,
  `SpecRow.lean`, `DeepRowSpec.lean`). The capstone was split at the
  emitter's real boundary — `groupSetup` runs once per group, the
  per-query quotients sit at distant offsets (`groupQuery_sound`
  re-proves the batch term at any offset), `deepRow` is one query's
  quotient+add chain, `deepRows` the query loop. Spec side,
  **`friAnswers_ok`** evaluates the spec's row loop in closed form
  under the circuit-enforced guards (nondegenerate batch points,
  nonvanishing denominators): each row is the sum over batches of the
  gadget-shaped batch term. The two meet in
  **`friAnswers_eq_rows`**: with the registers bound to the batch data
  (`Bound`: `groupSetup_sound`'s facts plus the response/value register
  pinning), the spec's `friAnswers` *succeeds* and returns exactly the
  values of the circuit's row registers. What remains above it is
  provenance plumbing: discharging `Bound` from `selectQueries` /
  `unpackIdx` / the alpha chain and the Merkle-value registers, and the
  `buildSampleBatches`-to-response-array ordering bridge
  (`flattenBatches_pushEntry` is the mechanism).

- **The `fri_decommit` layer walk is assembled** (`FriWalk.lean`), at
  the pinned fold step 1: `layerQuery1` (the coset select check + one
  `ibutterfly` fold per query), `layerFold1` (one layer's query loop),
  and `friLayers1` (the multi-layer walk threading the value
  registers). **`friLayers1_sound`** derives `Chain1` — the value-flow
  relation: each layer's incoming values are bit-selected from the
  witness cosets, which fold at the gate-inverted twiddle points into
  the next layer's values — and **`friDecommit1_sound`** appends the
  closing `eq` battery, yielding the spec's `lastLayerCheck` on the
  final values. `bound_of_groupSetup` likewise discharges the DEEP
  side's `Bound` bundle from `groupSetup`'s gates. What remains on the
  decommit side: the in-circuit Blake2s Merkle path gadget (ties the
  witness cosets to the layer roots; the per-query/no-dedup vs the
  spec's dedup'd-subset structure is Merkle-binding — scope-C
  territory). The twiddle-provenance chain is now assembled
  (`TwiddleChain.lean`): `twiddleChain1_sound` — every per-layer
  twiddle register gate-inverts its layer's fold coordinate, the
  conjugate-selected query point's `y` for the circle layer and the
  translated/doubled `baseSeq` points' `x`s for the line layers — the
  exact `htws` hypotheses of `friLayers1_sound`. The index bridge is
  done too (`FoldBridge.lean`): `baseSeq_eq_lineFoldPoints` — entry
  `ℓ` of the double/translate walk **is** the `ℓ`-times-doubled first
  inner line coset's point at the bit-reversed folded even position,
  the exact point `foldLineSubset` divides by (via `foldIdx`, the
  per-layer fold index, with `queryIndex → foldIdx 1 → foldIdx (ℓ+1)`
  recurrences on the circuit side and the coset/`bitReverseIndex`
  computation on the spec side; `commitInner_domains` pins the spec's
  stored layer domains to the successive doubles). With
  `base0_eq_evenPoint` for the circle layer, every fold-step-1 twiddle
  is tied to the exact spec fold coordinate — composed in
  **`twiddleChain1_spec`** (`TwiddleSpec.lean`): with the query-point
  lane pinned to the spec domain point and the bit lanes carrying the
  query's bits, every per-layer twiddle lane multiplies
  `specFoldCoord` to one; `scalar_inverts` carries this through the
  per-query `unpackIdx` to the scalar registers `friLayers1_sound`
  consumes.

- **The grouping gap is closed at the value level**: `rowSum_perm`
  (`SpecRow.lean`) — any two sample groupings with permutation-equal
  flat views give the same row sum (the circuit groups by point wire
  id, the spec by point value) — and **`buildSampleBatches_flat`**
  (`BatchesFlat.lean`): on success, the spec's batches flatten to a
  permutation of the exact push-order pair list (`treesPairs` — tree
  by tree, column by column, the periodicity duplicate first, the
  running power advancing once per entry). Matching `treesPairs`
  against the emitter's response array is statement-level data
  (scope B).

**Remaining**: response-register provenance (scope-B statement data:
`collectOodsResponses` ↔ `treesPairs`, `Bound` data, the
position/value threading from `deepRows` into `friLayers1`), the
circuit Blake2s Merkle gadget, and the channel-draw port. The spec's imperative loops have been refactored into pure
recursions (re-validated differentially, including `Fri.commitInner`), so
the assemblies can be proven against them directly; `SpecLemmas.lean`
starts that layer: at last-layer degree bound 0 the spec's final check is
pointwise equality with the constant coefficient (the circuit's closing
`eq` gates), and `commitInner_shape` pins the commit walk's structure —
on success the committed layers pair the proof layers one-to-one in
order and, at the pinned fold step 1, the degree bound drops by exactly
one per layer.

## Open questions (brief §7)

1. **Hints needing canonicity**: yes. `extract_bits` is the central one —
   a 31-bit pattern determines its field value only up to the collision
   `0 ≡ 2³¹ − 1`, and the circuit **does** carry the needed constraint
   (`validate_extract_bits`'s `(input·aux − 1)·bits₀ = 0`); this is now a
   theorem (`extractBits31_sound`). `simd.inv`/`div` guesses are pinned by
   their product-one/product-eq gates (field uniqueness — used in
   `foldCoset1_sound`, `denomInverse_sound`); `compute_fri_input`
   additionally binds all `im(P.y)` nonzero via the single `inv(prod)`
   gate, which is what keeps its denominators off the M31 query points.
   `m31_to_u32` is constrained by its own gate shape (input must be base
   M31); `guessM31`/`guessU16` by finalization. No unconstrained hint
   found so far in the audited gadgets.
2. **Statement binding before challenges**: yes. The in-circuit `verify`
   mixes, in order, the channel salt, the FRI config, the preprocessed
   root, the statement claims — for `CircuitStatement` the circuit hash
   (itself `Blake2s(config words ‖ preprocessed root)`, so component log
   sizes and blowup are bound through it) and the public-output digest —
   and the trace root, all **before** the first challenge draw
   (`draw_two_qm31s` for the interaction elements).
3. **Fold step 1 upstream**: stwo-zig's own circuit recursion uses fold
   step 4 (`circuit_proof_configs.default`: PoW 26, 35 queries), but the
   Cairo leaf lane uses fold step 1 (PoW 16, 70 queries,
   `cairo_prover_params` in the canonical registries), so fold step 1 is
   exercised upstream by every Cairo leaf proof — not only by
   starked-bitcoin.
