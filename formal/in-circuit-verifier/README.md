# In-circuit STARK verifier formalization

Lean 4 (v4.33.1 + Mathlib) formalization of stwo-zig's verifier, per
`VERIFIER_FORMALIZATION_BRIEF.md` (repo root of the main checkout). Pinned
to stwo-zig commit `4afa09dbf` and the `proving_5a7c5ed` profile:
Blake2sM31 Fiat–Shamir channel, plain Blake2s Merkle, `PcsConfigV2` lifted
trees, FRI with `log_blowup_factor = 1`, `fold_step = 1`,
`log_last_layer_degree_bound = 0`, 70 queries, PoW 26.

## Layout

| Module | Specifies | Zig source |
|---|---|---|
| `StwoVerifier/Basic.lean` | `P = 2³¹ − 1` prime (Lucas–Lehmer) | — |
| `StwoVerifier/Fields.lean` | M31 / CM31 / QM31 coordinate arithmetic | `src/core/fields/*` |
| `StwoVerifier/Blake2s.lean` | Blake2s-256 (RFC 7693), executable, `#guard` vectors | — (copied from starked-bitcoin) |
| `StwoVerifier/Channel.lean` | both Blake2s channels: mixes, draws, PoW, query draw, M31 word reduction | `src/core/channel/blake2s.zig`, `src/core/queries.zig` |
| `StwoVerifier/ChannelVectors.lean` | compile-time `#guard`s against stwo-zig's Rust-oracle-pinned digests, draws, grind nonces | the Zig test suites |
| `StwoVerifier/Circle.lean` | circle group, cosets, circle/line domains, bit reversal, OODS point map, `LinePoly` eval | `src/core/circle.zig`, `src/core/poly/*` |
| `StwoVerifier/Merkle.lean` | lifted Merkle multiproof verifier (plain hasher) | `src/core/vcs_lifted/verifier.zig` |
| `StwoVerifier/Fri.lean` | FRI commit transcript, subset rebuild, layer Merkle, folds, last layer (fold step 1) | `src/core/fri.zig`, `src/core/fri/*` |
| `StwoVerifier/Quotients.lean` | sample batches (periodicity duplicate incl.), line coefficients, `friAnswers` | `src/core/pcs/quotients/*`, `src/core/constraints.zig` |
| `StwoVerifier/Pcs.lean` | `commit` + `verifyValues` (the whole PCS opening verification) | `src/core/pcs/verifier.zig` |
| `StwoVerifier/Verifier.lean` | **`NativeAccepts`**: the statement-level verifier over an abstract `Air` | `src/core/verifier.zig`, `src/core/proof.zig` |
| `DiffCheck.lean` | the differential runner (`lake exe diffcheck`) | — |
| `harness/harness.zig` | proof generator + native-verdict recorder (build cmd in its header) | — |

Everything is an executable `def`; the same functions are the statements the
scope-A/B theorems will be proven against.

## Differential testing (deliverable 1)

`harness/harness.zig` proves a two-tree column batch at the PCS level with
stwo-zig's own CPU prover under the pinned profile, runs the native
`CommitmentSchemeVerifier.verifyValues` on the original proof and on a fixed
battery of 11 mutations plus a seeded 48-case fuzz battery (random
single-site corruptions over every proof surface), and records each verdict.
`lake exe diffcheck <vectors.json>` replays every case through the Lean spec
and requires accept/reject to agree.

Status (2026-10-12):

- **PCS level**: 180 of 180 cases agree across PoW 0 / 8 / 26 vector sets —
  and not only the accept/reject bit: the exact error code matches on every
  case (`vectors_pow{0,8,26}.json`).
- **Statement level** (`NativeAccepts` end to end, with a one-constraint
  constant-composition mock AIR, proved by the engine's `proveEx` and
  natively verified by `core.verifier.verify`): 60 of 60 cases agree at
  PoW 0, including `OodsNotMatching` paths and the full-query-coverage edge
  case where a PoW-nonce flip at `pow_bits = 0` is *correctly accepted*
  (every leaf is opened, so the verdict is query-independent); 180 of 180
  across PoW 0 / 8 / 26 (`statement_pow{0,8,26}.json`).
- The compile-time `#guard` vectors additionally pin the channel law
  (mixes, draws, Merkle-root absorption, FriConfigV2 transcript, PoW
  accept/reject at Rust Stwo's grind nonces) to upstream bytes.

Regenerate and check:

```sh
# from the worktree root
zig build-exe ... (see harness/harness.zig header) -femit-bin=formal/in-circuit-verifier/harness/harness
./formal/in-circuit-verifier/harness/harness formal/in-circuit-verifier/harness/vectors_pow0.json 0 70 48
cd formal/in-circuit-verifier && lake exe diffcheck harness/vectors_pow0.json
```

## Trust boundary, current

- **Differentially validated**: the channel, the commit transcript, PoW,
  query selection, lifted-tree Merkle verification, DEEP quotients
  (`friAnswers`, incl. the two-sample periodicity duplicate), the full FRI
  verifier at fold step 1, and their composition in `Pcs.verifyValues`.
- **Differentially validated at the statement level** with a mock AIR:
  composition-tree commit, OODS draw, chunk reconstruction, and the OODS
  equality check. The AIR itself stays an abstract `Air` record; scope B
  instantiates it with the circuit AIR.
- **Scope A under way** (`Gates.lean`, `Algebra.lean`, `CircleGadgets.lean`,
  `SimdGadgets.lean`, `BitDecomp.lean`), all standard axioms only
  (`#print axioms` = propext, Classical.choice, Quot.sound):
  - the gate model (`Circuit::check` semantics plus finalization
    constraints) and `CommRing` instances for the concrete CM31/QM31;
  - scalar circle gadgets proven sound: `double_x`, `add_points`,
    `double_point` (with the explicit on-circle hypothesis its `2x² − 1`
    doubling needs), `coset_vanishing_poly`, `denom_inverse`;
  - the SIMD lane layer: lane-wise `sub`/`mul`/`scalar_mul`, `Simd::eq`
    with the partial-wire mask, `assert_bits`, `guess_lsb`;
  - **`extract_bits(·, 31)` + `validate_extract_bits` proven sound**
    (`extractBits31_sound`): if the emitted gates hold, each lane's 31
    output bits are *the* binary digits of the lane's canonical M31 value.
    The canonicity hinges on the `(input·aux − 1)·bits₀ = 0` constraint
    rejecting the all-ones encoding of 0 — the circuit does carry the
    constraint its prover-supplied hints need (open question 1, answered
    for this gadget).
- **Not yet started**: `select_queries`' point-building half (`select`,
  `pow2`, generator tables) atop these, FRI/DEEP gadget proofs, scope B/C.

## Deviations from Zig noted while specifying

- `FriVerifier.commit` upstream accepts extra zero-fold inner layers at
  commit time and rejects them later in `decommit`; the spec rejects at
  commit (`invalidNumFriLayers`). Accept/reject agrees; the error site
  differs. No mutation vector currently hits this path.
- `drawBaseFelts`' rejection loop is unbounded in Zig; the spec carries
  fuel 64 (`drawFuelExhausted` is unreachable in practice, and on the M31
  channel the loop never rejects at all).
