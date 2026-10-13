# Report: verifier formalization, sessions of 2026-10-12/13

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

## Deliverable 5 — `verify` with `CircuitStatement` (scope B): **spec + differential done**

The circuit statement is now concrete on the spec side, validated
end-to-end against real circuit proofs.

**The circuit AIR as data.** The in-circuit composition evaluation is an
interpreter over the committed projection
(`vectors/circuit/official/compiled_air_constraints_v1.bin`).
`harness/airdump.zig` replays the 11-component evaluator table and the
composition accumulator through a recording context and flattens the whole
`computeCompositionPolynomial` denotation into one 1901-node arithmetic DAG
over the composition inputs (plus 5 recorded `eq` side conditions — the
generated components' fixed-size checks — and 5 n-instances-bit atoms).
The DAG is profile-independent (static preprocessed ids, every bit read
≤ 20). `CircuitAirData.lean` (generated) carries it;
`CircuitAirEval.lean` evaluates it over `QM31` and adds the vanishing
division. `lake exe aircheck`: 7/7 against the real Zig
`computeCompositionPolynomial` running eagerly over values (5 consistent
size profiles, 2 deliberately inconsistent ones whose `eq` flags must
trip).

**`circuitAir : Air`** (`CircuitAir.lean`): mask points — every
preprocessed column `[oods]` (the circuit prover commits with
`include_all_preprocessed_columns`), base columns `[oods]`, cumulative
sums `[oods − step, oods]`; `harness/maskcheck.zig` verifies that shape
against the captured native programs (all 11 components, every eval delta
1). `evalComposition` flattens the sampled values and statement data into
the DAG inputs (component sizes as `2^log` scalars and one-hot bits, the
exact values the bit-decomposition gadgets pin).

**`circuitAccepts`** (`CircuitVerify.lean`): the statement transcript —
salt, FRI config, preprocessed-root commit, circuit hash
`Blake2s(config words ‖ root)` mixed as a root, the eight output values
mixed as felts, trace-root commit, the 20-bit interaction PoW, the
`z, alpha` draw, the public LogUp sum against the claimed sums, claimed
sums mixed, interaction-root commit — plus the statement validity checks
(5-bit log sizes under the trace log, the relation-use bound), then
`NativeAccepts` with `circuitAir`.

**Differential** (`harness/circuitharness.zig`, `lake exe circuitcheck`):
all four R7 digest-output circuits (fibonacci, triple_xor, m31_to_u32,
blake_g_gate) proved by the in-repo prover under the pinned profile
(Blake2sM31, fold step 1, blowup 1, last layer 0), judged by the shipping
acceptance predicate (`circuit_cpu.verify.verifyProofBytes`, the
verification circuit built with values) on the baseline, 17 targeted
tampers (statement fields, salt, both nonces, claimed sums, every sampled
tree, three roots, a queried value, the last layer) and 10 seeded fuzz
flips each — every tamper applied to the native proof in place and
re-serialized so both verifiers judge the same object. **112/112 agree**,
baselines accepting: the circuit hash, the whole transcript, the LogUp
sum, the composition DAG at the real OODS point, the mask geometry,
Merkle, DEEP, FRI and PoW are exact on real proofs. The comparison is
verdict-level (the in-circuit verifier rejects by unsatisfiability,
without an error code).

**Trusted boundary for scope B so far**: the recorded DAG equals the
emitter's interpretation (differentially validated, not yet a theorem);
the wire↔native proof conversion (`verifier_proof.zig`) is exercised, not
modeled; gadget-level proofs of the statement phases (channel mixes,
Blake2s circuit hash, claim checks) remain the scope-B/C port backlog
(Merkle and channel gadgets).

### Response provenance (`collect_oods_responses` ↔ `treesPairs`), in progress

The gadget and spec sides of the OODS response layer are now proven up
to the final register binding (`OodsResponses.lean`, `ResponseOrder.lean`):

- **Period generators** (`oods.zig` `period_generators`): the
  doubling-and-accumulate chain's lane is the bit-weighted coordinate
  sum (`periodChain_lane` / `periodGensG_lane`, via the step gadget's
  embedded-point invariant), and one-hot size bits select the
  `2^k`-fold trace generator (`bitCombFull_onehot`,
  `periodGensG_lane_pow`). The embedding lemmas (`intoQ_add/double/
  onCircle`: the base-field inclusion is a circle homomorphism) carry
  `double_point`'s on-circle soundness through the scalar chain.
- **Sample points**: `unpackFrom_sound` (`simd.unpack` lifts each lane),
  `periodGeneratorsG_sound`/`_getD_pow` (each component's generator
  point register embeds its bit-weighted sum; one-hot ⇒
  `2^k · traceGen`), `addPointsList_sound` (the periodicity points
  `oods + gen`), `prevPointG_sound` (`oods + conj(traceGen)`), and
  `canonicStep_double_shift`: the spec's periodicity shift at the
  blowup-extended column log, `canonicStep(l+1)·2^(k+1)`, **is** the
  circuit's `traceGen(l)·2^k` — the extension absorbs the lifting
  offset.
- **Push order** (`ResponseOrder.lean`): `treesPairs` computed into
  closed recursions for the circuit's column shapes —
  `singlesPairs`/`doublesPairs`/`componentPairs`/`interTreePairs`,
  capped by `treesPairs_circuit`: the spec's whole push-order pair list
  is `circuitPairs`, matching `collect_oods_responses`' emission order
  pair by pair (periodicity duplicate, previous row, OODS; one power
  step per pair; one global chain through the four trees).
- **Grouping**: the circuit batches by point *wire* id, the spec by
  point *value*, and these genuinely differ — two fixed-table
  components share log size 16, so their periodicity point values
  coincide under distinct wires. `partition_flatMap_perm` /
  `zip_partition_perm` close the gap through `rowSum_perm`: any stable
  partition of the response list into key fibers permutes the
  push-order pair list, so the row sums agree regardless of grouping.

- **The grouping loop, walked** (`FriGroups.lean`): `computeFriInput`'s
  phase 1 — one global power chain, `OodsPointAuxiliary` groups keyed
  by wire pair, init on first sight, accumulates interleaved in
  response order — modeled statefully with the preserved invariant
  `GInv` (`friGroups_sound`): per group, the line coefficients of its
  point and the `α'`-weighted coefficient/`a`/`v` sums over its fiber
  of the indexed response list, plus the exposed power registers
  (register `j` holds `−2u·αʲ`). The finalize loop
  (`friFinalize_sound`) carries each group into `GroupRegs` with
  `b = d·v − a·P.y`, and the closing `inv` gate on the `d`-product
  forces every `im(P.y)` nonzero. `bound_of_walk` then discharges
  `Bound` outright, and `friAnswers_eq_rows_grouped`
  (`GroupedRows.lean`) restates the deliverable-3 capstone for the
  wire-keyed grouping: any grouping whose flat view permutes the spec
  batches' gives the same rows (`rowSum_perm` + `mem_flattenBatches`
  transfer the denominator guards).

Remaining for this arc: the statement-level batch construction (the
fibers' entries against `circuitPairs` positions — pure data at the
final binding) and the composed emitter, where the `deepRows` result
registers are fed to `friDecommit1` as its first-layer values by
construction.

### The in-circuit Blake2s, proven (`BlakeGadgets.lean`, `BlakeBridge.lean`)

The gate model now carries the two dedicated Blake gates exactly as
`Circuit::check` enforces them — `Op.tripleXor` (u32-limb inputs, the
output packs the XOR) and `Op.blakeG` (four consecutive outputs packing
RFC 7693's G, stated against the spec's `Blake2s.mix`) — and the whole
`blake2s_u32s` emitter is walked on top:

- `gStepG_sound` / `stepsG_sound`: the register state tracks the spec's
  working vector word for word through one G gate and through all 80
  applications (the flattened round loops are `Blake2s.steps`).
- `compressG_sound`: one block — IV constants with byte counter and
  final flag, rounds, chaining xors — is `Blake2s.compress`.
- `blocksG_sound` + `hashWordsL_eq_hashBlocks`: the block loop is the
  word-level chain, and with the words read off the zero-padded bytes
  that chain **is** the byte-level `Blake2s.hashBlocks` (schedules agree
  as whole functions; non-last counters are `t + 64`, the last is
  `nBytes`; the empty message is one all-zero block).
- `blake2sU32sG_sound`: end to end — message registers carrying the
  byte message's words hash to registers carrying the digest words of
  `Blake2s.blake2s bytes` (`hashBlocks_congr` discharges that only the
  eight chaining words matter).

The felt ↔ word plumbing and the first channel methods are proven on
top (`BlakePack.lean`, `ChannelGadgets.lean`):

- `unpack_qm31s_to_u32_words` (`unpackFeltsG_sound`): each coordinate
  lifted and limb-converted; the word list is the felt byte
  serialization's `leWord`s (4-byte chunk lemma + LE recomposition).
- `reduce_hash_value` (`reduceHashValueG_sound`): each digest word
  folded to `low + 2¹⁶·high` — the word mod `P` — four per felt.
- `blake2sFeltsG_sound` / `blake2sM31G_sound`: end to end, felt
  registers hash to the spec digest's words and to the channel's
  two-felt reduced digest.
- **`ChDigest`**, the channel-state correspondence: the digest wires'
  byte serialization is the spec digest. `digestFelts_bytes` proves
  the reduce gadget's felts serialize to `chHash true` exactly (the
  spec's word-wise reduction *is* `mod P`; `wordAt` inverts both
  serializations).
- **`mix_qm31s` is `mixFelts`** (`mixQm31sG_sound`) and
  **`draw_two_qm31s` is `drawSecureFelts true 2`**
  (`drawTwoQm31sG_sound`): in m31 mode the first draw always lands
  (every reduced word is below `2P`), and the 37-byte draw message's
  zero separator matches the counter felt's packing tail.

- **`mix_u32s` is `mixU32s`** (`mixU32sG_sound`) and **`mix_commitment`
  is `mixRoot`** (`mixCommitmentG_sound`; a 32-byte root is the LE
  serialization of its own words, `root_reconstruct`).
- **The proof of work is sound** (`PowGadget.lean`, `powG_sound`): any
  assignment satisfying `Channel::pow`'s gates carries a nonce wire whose
  spec nonce `lo + 2³²·hi` (high coordinates masked to zero) passes
  `verifyPowNonce`, and the digest update is `mixU64`. The circuit pins
  the low `n_bits` of the first reduced word via the 31-bit
  `extract_bits`; `trailingZeroBits_ge` turns that into the spec's
  trailing-zero count over the first 16 digest bytes (a zero first word
  already gives 32). One completeness-only restriction is visible here:
  the wire form needs `lo < P`, so nonces with a low word ≥ P are not
  representable — never an issue for soundness.
- **`draw_point` is the OODS-point draw** (`drawPointG_sound`): the seed
  is `drawSecureFelt`'s, the `inv` gate forces `1 + t² ≠ 0` so
  `securePointFromSeed` succeeds, and the registers hold its point.

With these the in-circuit channel is proven method by method against
the spec `Channel`. Remaining in this port: the Merkle path gadget.

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
