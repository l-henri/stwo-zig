//! Experimental source-derived native proof for one to eight mixed calls.
//!
//! Kept separate from fixed N=3 and N=4 adapters so their transcript and proof
//! bytes remain unchanged while the bounded scheduler is reviewed.
//!
//! Only the source-pinned S31 wrapper may admit serialized proof bytes. This
//! adapter rechecks source bytes, AIR bundle, live geometry and fixed root,
//! but cannot parse S31 or certify a caller-supplied manifest digest itself.
const std = @import("std");
const core = @import("stwo_core");
const prover = @import("stwo_prover_engine");
const circuit = @import("stwo_circuit_frontend");
const cairo = @import("stwo_cairo_frontend");
const old = @import("prove.zig");
const air = @import("air.zig");
const many = @import("private_many_boundary.zig");
const plan_admission = @import("direct_many_plan_admission.zig");
const mixed = @import("direct_mixed_schedule.zig");
const pair_chip = @import("tagged_pair_chip.zig");
const pair_bridge = @import("tagged_pair_bridge.zig");
const many_chip = @import("tagged_many_chip.zig");
const many_bridge = @import("tagged_many_bridge.zig");
const direct = @import("direct_arithmetic.zig");

const M31 = core.fields.m31.M31;
const QM31 = core.fields.qm31.QM31;
const MC = old.profiles.Blake2sM31MerkleChannel;
const H = MC.MerkleHasher;
const Engine = old.Internal.Engine;
const Scheme = Engine.Scheme;
const Channel = MC.Channel;
const ColumnEvaluation = prover.pcs.ColumnEvaluation;
const CircuitView = circuit.common.preprocessed.CircuitView;
const direct_pp = circuit.common.direct_arithmetic;
const direct_trace = circuit.witness.direct_arithmetic;
const Sha256 = std.crypto.hash.sha2.Sha256;
const profile_tag: u64 = 0x5333314d49580301; // S31MIX, profile 3.
pub const max_calls: usize = many.max_calls;
pub const max_components: usize = many.max_components;

pub const Selected = struct {
    source_sha256: [32]u8,
    manifest_sha256: [32]u8,
    fixed_root: [32]u8,
    circuit_program_sha256: [32]u8,
    plan: many.Plan,
    geometry: mixed.Geometry,

    pub fn effectiveDigest(self: *const Selected) [32]u8 {
        var h = Sha256.init(.{});
        h.update("S31-MIXED-MANIFEST-TRANSCRIPT-V3\x00");
        h.update(&self.source_sha256);
        h.update(&self.manifest_sha256);
        var result: [32]u8 = undefined;
        h.final(&result);
        return result;
    }

    pub fn circuitIdentity(self: *const Selected) [32]u8 {
        var h = Sha256.init(.{});
        h.update("S31-MIXED-CIRCUIT-IDENTITY-V3\x00");
        const effective = self.effectiveDigest();
        h.update(&effective);
        h.update(&self.fixed_root);
        hashInt(&h, self.geometry.slots[0].trace_log_size);
        hashInt(&h, self.geometry.pcs.fri_config.log_blowup_factor);
        hashInt(&h, self.plan.count);
        for (self.plan.callSlice()) |call| hashCall(&h, call);
        var result: [32]u8 = undefined;
        h.final(&result);
        return result;
    }
};

pub const Proof = struct {
    allocator: std.mem.Allocator,
    pcs_config: core.pcs.config_v2.PcsConfigV2,
    output_values: []QM31,
    interaction_pow_nonce: u64,
    claimed_sums: [many.max_components]QM31,
    sum_count: usize,
    stark_proof: core.proof.ExtendedStarkProof(H),
    circuit_hash: [32]u8,

    pub fn deinit(self: *@This()) void {
        self.stark_proof.deinit(self.allocator);
        self.allocator.free(self.output_values);
        self.* = undefined;
    }
};

pub const BorrowedProof = struct {
    output_values: []const QM31,
    interaction_pow_nonce: u64,
    claimed_sums: [many.max_components]QM31,
    sum_count: usize,
    stark_proof: *const core.proof.StarkProof(H),
    circuit_hash: [32]u8,
};

/// Optional, execution-only timing. These values never enter the transcript,
/// proof envelope, manifest, AIR, or verifier. `prove_body_ns` runs from
/// function entry to proof assembly and includes the recorder snapshot; it
/// excludes deferred cleanup after the return expression. The S31 caller's
/// outer timer remains authoritative for its complete native interval.
pub const Timing = struct {
    prove_body_ns: u64,
    interaction_pow_ns: u64,
    pcs_prove_ns: u64,
    fri_pow_ns: u64,
};

/// Explicit witness-sidecar audit of a *verified* proof. The three roots are
/// recomputed from the supplied full witness, then compared to the roots in
/// the verified PCS proof. This is deliberately opt-in and not a succinct
/// verifier claim that a proof reveals its committed polynomial evaluations.
pub const TraceAudit = struct {
    fixed_root: [32]u8,
    main_root: [32]u8,
    interaction_root: [32]u8,
    circuit_rows: usize,
    chip_rows: usize,
    bridge_rows: usize,
};

const ChipInteraction = union(enum) {
    pair: pair_chip.Interaction,
    many: many_chip.Interaction,

    fn columns(self: *const @This()) []const ColumnEvaluation {
        return switch (self.*) {
            .pair => |value| value.columns,
            .many => |value| value.columns,
        };
    }
    fn sum(self: *const @This()) QM31 {
        return switch (self.*) {
            .pair => |value| value.claimed_sum,
            .many => |value| value.claimed_sum,
        };
    }
    fn deinit(self: *@This()) void {
        switch (self.*) {
            .pair => |*value| value.deinit(),
            .many => |*value| value.deinit(),
        }
    }
};

const BridgeBase = union(enum) {
    pair: pair_bridge.Base,
    many: many_bridge.Base,

    fn columns(self: *const @This()) []const ColumnEvaluation {
        return switch (self.*) {
            .pair => |value| value.columns,
            .many => |value| value.columns,
        };
    }
    fn deinit(self: *@This()) void {
        switch (self.*) {
            .pair => |*value| value.deinit(),
            .many => |*value| value.deinit(),
        }
    }
};

const BridgeInteraction = union(enum) {
    pair: pair_bridge.Interaction,
    many: many_bridge.Interaction,

    fn columns(self: *const @This()) []const ColumnEvaluation {
        return switch (self.*) {
            .pair => |value| value.columns,
            .many => |value| value.columns,
        };
    }
    fn sum(self: *const @This()) QM31 {
        return switch (self.*) {
            .pair => |value| value.claimed_sum,
            .many => |value| value.claimed_sum,
        };
    }
    fn deinit(self: *@This()) void {
        switch (self.*) {
            .pair => |*value| value.deinit(),
            .many => |*value| value.deinit(),
        }
    }
};

fn digest(bytes: []const u8) [32]u8 {
    var result: [32]u8 = undefined;
    Sha256.hash(bytes, &result, .{});
    return result;
}

fn hashInt(h: *Sha256, value: anytype) void {
    var bytes: [@sizeOf(@TypeOf(value))]u8 = undefined;
    std.mem.writeInt(@TypeOf(value), &bytes, value, .little);
    h.update(&bytes);
}

fn hashCall(h: *Sha256, call: many.Call) void {
    hashInt(h, call.call_id);
    hashInt(h, call.rounds);
    hashInt(h, call.constant.toU32());
    for (call.input ++ call.output) |address| hashInt(h, address);
}

fn mixProfile(channel: *Channel, selected: *const Selected) void {
    channel.mixU64(profile_tag);
    const effective = selected.effectiveDigest();
    var words: [8]u32 = undefined;
    for (&words, 0..) |*word, id| word.* = std.mem.readInt(u32, effective[4 * id ..][0..4], .little);
    channel.mixU32s(&words);
    channel.mixU32s(&.{selected.plan.count});
    for (selected.plan.callSlice()) |call| {
        channel.mixU32s(&.{ call.call_id, call.rounds, call.constant.toU32() });
        channel.mixU32s(&(call.input ++ call.output));
    }
}

fn validatePublicOutputShape(source: CircuitView) !void {
    if (source.output.len != 9) return error.InvalidMixedPublicStatement;
    for (source.output, 0..) |address, index|
        if (address != @as(u32, @intCast(index + 2))) return error.InvalidMixedPublicStatement;
}

fn validateSourceAndGeometry(
    allocator: std.mem.Allocator,
    pp: *const direct_pp.Circuit,
    template: *const air.Bundle,
    selected: *const Selected,
    source_bytes: []const u8,
    air_bytes: []const u8,
) !void {
    if ((selected.plan.count == 0 or selected.plan.count > max_calls) or
        selected.geometry.slot_count != 1 + 2 * @as(usize, selected.plan.count) or
        selected.geometry.version != mixed.version or
        !std.meta.eql(selected.source_sha256, digest(source_bytes)))
        return error.InvalidMixedSelection;
    var bundle_digest: [32]u8 = undefined;
    _ = std.fmt.hexToBytes(&bundle_digest, air.bundle_sha256) catch unreachable;
    if (!std.meta.eql(digest(air_bytes), bundle_digest) or
        !std.meta.eql(try pp.preprocessedRoot(allocator, 1), selected.fixed_root))
        return error.InvalidMixedSelection;
    const rebuilt = try mixed.inspect(allocator, pp, template, selected.plan);
    if (!std.meta.eql(rebuilt, selected.geometry)) return error.InvalidMixedSelection;
    const layout = pp.layout();
    var bound = try air.bindDirectArithmetic(allocator, template, pp.traceLogSize(), &layout);
    defer bound.deinit();
    if (!std.meta.eql(try air.directProgramBindingDigest(air_bytes, &bound), selected.circuit_program_sha256))
        return error.InvalidMixedSelection;
}

fn selectedColumns(
    dst: []ColumnEvaluation,
    selected: *const Selected,
    circuit_columns: []const ColumnEvaluation,
    chips: anytype,
    bridges: anytype,
    comptime is_main: bool,
) !void {
    var at: usize = 0;
    for (selected.geometry.slotSlice(), 0..) |slot, index| {
        const columns: []const ColumnEvaluation = if (index == 0) circuit_columns else blk: {
            const id: usize = @intCast(slot.call_id orelse return error.InvalidMixedSelection);
            if (id >= selected.plan.count) return error.InvalidMixedSelection;
            break :blk if (index % 2 == 1) (if (is_main) chips[id].columns else chips[id].columns()) else bridges[id].columns();
        };
        const offset = if (is_main) slot.main_offset else slot.interaction_offset;
        const width = if (is_main) slot.main_columns else slot.interaction_columns;
        if (at != offset or columns.len != width or width > dst.len - at) return error.InvalidMixedSelection;
        @memcpy(dst[at..][0..width], columns);
        at += width;
    }
    if (at != dst.len) return error.InvalidMixedSelection;
}

fn selectedSums(selected: *const Selected, circuit_sum: QM31, chips: []const ChipInteraction, bridges: []const BridgeInteraction) ![many.max_components]QM31 {
    var sums = [_]QM31{QM31.zero()} ** many.max_components;
    for (selected.geometry.slotSlice(), 0..) |slot, index| {
        if (index == 0) {
            sums[index] = circuit_sum;
            continue;
        }
        const id: usize = @intCast(slot.call_id orelse return error.InvalidMixedSelection);
        if (id >= selected.plan.count) return error.InvalidMixedSelection;
        sums[index] = if (index % 2 == 1) chips[id].sum() else bridges[id].sum();
    }
    return sums;
}

fn commit(scheme: *Scheme, allocator: std.mem.Allocator, source: []const ColumnEvaluation, channel: *Channel) !void {
    try Engine.commit(scheme, allocator, try cloneColumns(allocator, source), null, channel);
    try Engine.flushPendingCommit(scheme, allocator, channel);
}

fn cloneColumns(allocator: std.mem.Allocator, source: []const ColumnEvaluation) ![]ColumnEvaluation {
    const columns = try allocator.alloc(ColumnEvaluation, source.len);
    var ready: usize = 0;
    errdefer {
        for (columns[0..ready]) |entry| allocator.free(entry.values);
        allocator.free(columns);
    }
    for (source, columns) |entry, *slot| {
        slot.* = .{ .log_size = entry.log_size, .values = try allocator.dupe(M31, entry.values) };
        ready += 1;
    }
    return columns;
}

fn checkRuntimeHandles(comptime T: type, allocator: std.mem.Allocator, handles: []const T, selected: *const Selected) !void {
    if (handles.len != selected.geometry.slot_count) return error.InvalidMixedRuntimeRoster;
    for (handles, selected.geometry.slotSlice()) |handle, slot| {
        if (handle.nConstraints() != slot.n_constraints or
            handle.maxConstraintLogDegreeBound() != slot.evaluation_log_size or
            handle.compositionLogSplit() != selected.geometry.composition_split)
            return error.InvalidMixedRuntimeRoster;
        const indices = try handle.preprocessedColumnIndices(allocator);
        defer allocator.free(indices);
        if (indices.len != slot.preprocessed_count) return error.InvalidMixedRuntimeRoster;
        for (indices, slot.preprocessed_indices[0..slot.preprocessed_count]) |actual, expected|
            if (actual != expected) return error.InvalidMixedRuntimeRoster;
    }
}

fn auditCircuitRows(
    allocator: std.mem.Allocator,
    source: CircuitView,
    values: []const QM31,
    pp: *const direct_pp.Circuit,
    base: *const direct_trace.Base,
    plan: many.Plan,
) !usize {
    // The selected S31 direct profile has no permutation component. Refuse a
    // future permutation-bearing source until its row semantics are audited.
    if (source.nPermutations() != 0) return error.UnsupportedMixedTraceAuditPermutation;
    const rows = source.nQm31OpsRows();
    if (values.len != source.n_vars or rows != pp.first_permutation_row or
        pp.n_outputs != 8 or base.columns.len != 12 or
        rows != (@as(usize, 1) << @intCast(base.log_size)))
        return error.InvalidMixedTraceAuditShape;
    if (!values[0].eql(QM31.zero()) or !values[1].eql(QM31.one()) or
        !values[2].eql(circuit.witness.trace.U_VALUE))
        return error.InvalidMixedTraceAuditReserved;
    const uses = try source.computeUses(allocator);
    defer allocator.free(uses);
    const gate_balance = try allocator.alloc(i64, values.len);
    defer allocator.free(gate_balance);
    @memset(gate_balance, 0);
    for (plan.callSlice()) |call| for (call.input ++ call.output) |address| {
        if (address >= uses.len) return error.InvalidMixedTraceAuditAddress;
        try circuit.common.preprocessed.addCanonicalMultiplicity(&uses[address], 1);
    };
    var fixed: [direct_pp.N_COLUMNS][]const M31 = undefined;
    for (circuit.common.preprocessed.QM31_OPS_COLUMN_IDS, &fixed) |id, *slot| {
        slot.* = pp.columnValues(id) orelse return error.InvalidMixedTraceAuditFixed;
        if (slot.*.len != rows) return error.InvalidMixedTraceAuditShape;
    }
    for (base.columns) |column|
        if (column.log_size != base.log_size or column.values.len != rows)
            return error.InvalidMixedTraceAuditShape;
    var row: usize = 0;
    inline for (.{ source.add, source.sub, source.mul, source.pointwise_mul }, 0..) |gates, opcode| {
        for (gates) |gate| {
            if (gate.in0 >= values.len or gate.in1 >= values.len or gate.out >= values.len)
                return error.InvalidMixedTraceAuditAddress;
            for (0..4) |flag|
                if (fixed[flag][row].toU32() != @intFromBool(flag == opcode))
                    return error.InvalidMixedTraceAuditFixed;
            const expected = [4]u32{ gate.in0, gate.in1, gate.out, uses[gate.out] };
            for (expected, 4..) |word, column|
                if (fixed[column][row].toU32() != word)
                    return error.InvalidMixedTraceAuditFixed;
            const actual = values[gate.out];
            const computed = switch (opcode) {
                0 => values[gate.in0].add(values[gate.in1]),
                1 => values[gate.in0].sub(values[gate.in1]),
                2 => values[gate.in0].mul(values[gate.in1]),
                3 => core.fields.qm31_pointwise.pointwiseMul(values[gate.in0], values[gate.in1]),
                else => unreachable,
            };
            if (!actual.eql(computed)) return error.InvalidMixedTraceAuditGate;
            // Compare a bag of (address, value) Gate events. Each base row is
            // already tied to values[address], so address is a canonical bag
            // key here; no global concatenation order is assumed.
            gate_balance[gate.in0] += 1;
            gate_balance[gate.in1] += 1;
            gate_balance[gate.out] -= fixed[7][row].toU32();
            const operands = [3]QM31{ values[gate.in0], values[gate.in1], actual };
            for (operands, 0..) |operand, part| for (operand.toM31Array(), 0..) |limb, lane| {
                if (!base.columns[4 * part + lane].values[row].eql(limb))
                    return error.InvalidMixedTraceAuditMain;
            };
            row += 1;
        }
    }
    if (row != rows or base.output_values.len != 8) return error.InvalidMixedTraceAuditShape;
    for (base.output_values, values[3..11]) |output, word|
        if (!output.eql(word)) return error.InvalidMixedTraceAuditPublic;
    // The public feeder consumes u and all eight output words; each bridge
    // consumes its eight source-owned endpoint words once (1/16 per row).
    for (source.output) |address| {
        if (address >= gate_balance.len) return error.InvalidMixedTraceAuditAddress;
        gate_balance[address] += 1;
    }
    for (plan.callSlice()) |call| for (call.input ++ call.output) |address| {
        if (address >= gate_balance.len) return error.InvalidMixedTraceAuditAddress;
        gate_balance[address] += 1;
    };
    for (gate_balance) |balance|
        if (balance != 0) return error.InvalidMixedTraceAuditGateBag;
    return rows;
}

fn auditChipBridgeRows(
    plan: many.Plan,
    states: [max_calls]many.States,
    chips: []const many_chip.Base,
    bridges: []const BridgeBase,
) !struct { chip: usize, bridge: usize } {
    var chip_rows: usize = 0;
    var bridge_rows: usize = 0;
    for (plan.callSlice(), states[0..plan.count], chips, bridges) |call, state, chip_base, bridge_base| {
        if (chip_base.columns.len != 9) return error.InvalidMixedTraceAuditChip;
        const log_size = try @import("repeated_step_chip.zig").validateRounds(call.rounds);
        for (chip_base.columns) |column|
            if (column.log_size != log_size or column.values.len != call.rounds)
                return error.InvalidMixedTraceAuditChip;
        var words = state.input;
        for (0..call.rounds) |step| {
            const row = @import("repeated_step_chip.zig").storageIndex(step, log_size);
            if (chip_base.columns[0].values.len != call.rounds or
                chip_base.columns[0].values[row].toU32() != step)
                return error.InvalidMixedTraceAuditChip;
            for (&words, 0..) |*word, lane| {
                if (chip_base.columns[1 + lane].values.len != call.rounds or
                    chip_base.columns[5 + lane].values.len != call.rounds or
                    !chip_base.columns[1 + lane].values[row].eql(word.*))
                    return error.InvalidMixedTraceAuditChip;
                word.* = word.*.mul(word.*).add(call.constant);
                if (!chip_base.columns[5 + lane].values[row].eql(word.*))
                    return error.InvalidMixedTraceAuditChip;
            }
        }
        if (!std.meta.eql(words, state.output) or !std.meta.eql(chip_base.final, state.output))
            return error.InvalidMixedTraceAuditChip;
        // For each call, a tagged chip row's negative `(id, step+1, out)`
        // event must equal the next row's positive `(id, step+1, in)` event.
        // The bridge cancels the two remaining endpoints below. This is a
        // per-call multiset check, not a global sequence comparison.
        for (1..call.rounds) |step| {
            const previous_row = @import("repeated_step_chip.zig").storageIndex(step - 1, log_size);
            const current_row = @import("repeated_step_chip.zig").storageIndex(step, log_size);
            for (0..4) |lane|
                if (!chip_base.columns[5 + lane].values[previous_row].eql(chip_base.columns[1 + lane].values[current_row]))
                    return error.InvalidMixedTraceAuditChipBag;
        }
        const columns = bridge_base.columns();
        if (columns.len != 8) return error.InvalidMixedTraceAuditBridge;
        const endpoints = state.input ++ state.output;
        for (columns, endpoints) |column, expected| {
            if (column.log_size != many.bridge_log_size or column.values.len != pair_bridge.rows)
                return error.InvalidMixedTraceAuditBridge;
            for (column.values) |actual|
                if (!actual.eql(expected)) return error.InvalidMixedTraceAuditBridge;
        }
        chip_rows += call.rounds;
        bridge_rows += pair_bridge.rows;
    }
    return .{ .chip = chip_rows, .bridge = bridge_rows };
}

const AuditFraction = prover.air.logup_columns.Fraction;

fn secureColumn(columns: []const ColumnEvaluation, group: usize, row: usize) QM31 {
    const offset = 4 * group;
    return QM31.fromM31(
        columns[offset].values[row],
        columns[offset + 1].values[row],
        columns[offset + 2].values[row],
        columns[offset + 3].values[row],
    );
}

/// Audit every LogUp row in the same bit-reversed circle-domain storage as
/// the committed trace. Earlier columns are per-row fraction prefixes; the
/// final one is a coset-order prefix with claimed_sum / rows subtracted.
/// Explicit inversions reject poles instead of silently accepting a fraction.
fn auditLogupRows(
    columns: []const ColumnEvaluation,
    log_size: u32,
    n_fractions: usize,
    claimed_sum: QM31,
    context: anytype,
    comptime fill: fn (@TypeOf(context), usize, []AuditFraction) anyerror!void,
) !void {
    if (n_fractions == 0 or n_fractions > 5 or columns.len != 4 * n_fractions or log_size >= @bitSizeOf(usize))
        return error.InvalidMixedTraceAuditInteractionShape;
    const rows = @as(usize, 1) << @intCast(log_size);
    for (columns) |column|
        if (column.log_size != log_size or column.values.len != rows)
            return error.InvalidMixedTraceAuditInteractionShape;
    const shift = try claimed_sum.divM31(M31.fromU64(rows));
    var total = QM31.zero();
    for (0..rows) |row| {
        var fractions: [5]AuditFraction = undefined;
        try fill(context, row, fractions[0..n_fractions]);
        var cumulative = QM31.zero();
        for (fractions[0..n_fractions], 0..) |fraction, index| {
            if (fraction.denominator.isZero()) return error.MixedTraceAuditDenominatorPole;
            cumulative = cumulative.add(fraction.numerator.mul(try fraction.denominator.inv()));
            if (index + 1 < n_fractions and !secureColumn(columns, index, row).eql(cumulative))
                return error.InvalidMixedTraceAuditInteraction;
        }
        total = total.add(cumulative);
        const previous_row = core.utils.previousBitReversedCircleDomainIndex(row, log_size, log_size);
        const current = secureColumn(columns, n_fractions - 1, row);
        const previous = secureColumn(columns, n_fractions - 1, previous_row);
        if (!current.sub(previous).add(shift).eql(cumulative))
            return error.InvalidMixedTraceAuditInteraction;
    }
    if (!total.eql(claimed_sum)) return error.InvalidMixedTraceAuditClaimedSum;
}

const CircuitFractions = struct {
    base: []const ColumnEvaluation,
    fixed: [direct_pp.N_COLUMNS][]const M31,
    elements: circuit.witness.trace.LookupElements,

    fn fill(self: @This(), row: usize, out: []AuditFraction) !void {
        if (out.len != 2) return error.InvalidMixedTraceAuditInteractionShape;
        var main: [12]M31 = undefined;
        for (self.base, &main) |column, *word| word.* = column.values[row];
        const lookups = circuit.witness.components.qm31_ops.lookups(&main, .{
            .in0 = self.fixed[4][row],
            .in1 = self.fixed[5][row],
            .out = self.fixed[6][row],
            .mults = self.fixed[7][row],
        });
        const d0 = self.elements.combine(lookups[0].values());
        const d1 = self.elements.combine(lookups[1].values());
        const d2 = self.elements.combine(lookups[2].values());
        out[0] = .{
            .numerator = d1.mulM31(lookups[0].numerator).add(d0.mulM31(lookups[1].numerator)),
            .denominator = d0.mul(d1),
        };
        out[1] = .{ .numerator = QM31.fromBase(lookups[2].numerator), .denominator = d2 };
    }
};

const ChipFractions = struct {
    base: []const ColumnEvaluation,
    call: many.Call,
    elements: many.Elements,

    fn fill(self: @This(), row: usize, out: []AuditFraction) !void {
        if (out.len != 2) return error.InvalidMixedTraceAuditInteractionShape;
        const step = self.base[0].values[row].toU32();
        if (step >= self.call.rounds) return error.InvalidMixedTraceAuditChip;
        var before: [4]M31 = undefined;
        var after: [4]M31 = undefined;
        for (0..4) |lane| {
            before[lane] = self.base[1 + lane].values[row];
            after[lane] = self.base[5 + lane].values[row];
        }
        out[0] = .{ .numerator = QM31.one(), .denominator = self.elements.combine(many.chipTuple(self.call.call_id, step, before)) };
        out[1] = .{ .numerator = QM31.one().neg(), .denominator = self.elements.combine(many.chipTuple(self.call.call_id, step + 1, after)) };
    }
};

const BridgeFractions = struct {
    base: []const ColumnEvaluation,
    call: many.Call,
    elements: many.Elements,

    fn fill(self: @This(), row: usize, out: []AuditFraction) !void {
        if (out.len != 5) return error.InvalidMixedTraceAuditInteractionShape;
        const inv_rows = try QM31.fromBase(M31.fromCanonical(pair_bridge.rows)).inv();
        var words: [8]M31 = undefined;
        for (self.base, &words) |column, *word| word.* = column.values[row];
        const addresses = self.call.input ++ self.call.output;
        for (0..4) |slot| {
            const a = 2 * slot;
            const d0 = self.elements.combineGate(many.gateTuple(addresses[a], words[a]));
            const d1 = self.elements.combineGate(many.gateTuple(addresses[a + 1], words[a + 1]));
            out[slot] = .{ .numerator = d0.add(d1).mul(inv_rows), .denominator = d0.mul(d1) };
        }
        const first = self.elements.combine(many.chipTuple(self.call.call_id, 0, words[0..4].*));
        const last = self.elements.combine(many.chipTuple(self.call.call_id, self.call.rounds, words[4..8].*));
        out[4] = .{ .numerator = first.sub(last).mul(inv_rows), .denominator = first.mul(last) };
    }
};

fn auditInteractionRows(
    pp: *const direct_pp.Circuit,
    base: *const direct_trace.Base,
    interaction: *const direct_trace.Interaction,
    plan: many.Plan,
    chips: []const many_chip.Base,
    bridges: []const BridgeBase,
    chip_interactions: []const ChipInteraction,
    bridge_interactions: []const BridgeInteraction,
    z: QM31,
    alpha: QM31,
) !void {
    var fixed: [direct_pp.N_COLUMNS][]const M31 = undefined;
    for (circuit.common.preprocessed.QM31_OPS_COLUMN_IDS, &fixed) |id, *slot|
        slot.* = pp.columnValues(id) orelse return error.InvalidMixedTraceAuditFixed;
    try auditLogupRows(interaction.columns, base.log_size, 2, interaction.claimed_sum, CircuitFractions{ .base = base.columns, .fixed = fixed, .elements = .init(z, alpha) }, CircuitFractions.fill);
    for (plan.callSlice(), chips, bridges, chip_interactions, bridge_interactions) |call, chip_base, bridge_base, chip_trace, bridge_trace| {
        try auditLogupRows(chip_trace.columns(), chip_base.columns[0].log_size, 2, chip_trace.sum(), ChipFractions{ .base = chip_base.columns, .call = call, .elements = .init(z, alpha) }, ChipFractions.fill);
        try auditLogupRows(bridge_trace.columns(), pair_bridge.log_size, 5, bridge_trace.sum(), BridgeFractions{ .base = bridge_base.columns(), .call = call, .elements = .init(z, alpha) }, BridgeFractions.fill);
    }
}

/// The allocator must be safe for concurrent use by the composition workers.
/// The S31 wrapper constructs `selected` from literal source before calling.
pub fn proveSourceBound(
    allocator: std.mem.Allocator,
    source: CircuitView,
    values: []const QM31,
    source_bytes: []const u8,
    air_bytes: []const u8,
    selected: *const Selected,
) !Proof {
    return proveSourceBoundWithTiming(allocator, source, values, source_bytes, air_bytes, selected, null);
}

/// The same source-bound proof with opt-in diagnostics. The caller-owned slot
/// is written only after a successful proof; no timing value is channel-mixed.
pub fn proveSourceBoundWithTiming(
    allocator: std.mem.Allocator,
    source: CircuitView,
    values: []const QM31,
    source_bytes: []const u8,
    air_bytes: []const u8,
    selected: *const Selected,
    timing: ?*Timing,
) !Proof {
    var total_timer: std.time.Timer = if (timing != null) try std.time.Timer.start() else undefined;
    if (selected.plan.count == 0 or selected.plan.count > max_calls)
        return error.InvalidMixedSelection;
    try plan_admission.requireResourceShape(source);
    try validatePublicOutputShape(source);
    var pp = try plan_admission.BoundedPlan.fromLegacy(selected.plan).preprocessed(allocator, source);
    defer pp.deinit(allocator);
    var template = try air.parse(allocator, air_bytes);
    defer template.deinit();
    try validateSourceAndGeometry(allocator, &pp, &template, selected, source_bytes, air_bytes);
    const pcs = selected.geometry.pcs;
    const layout = pp.layout();
    var bound = try air.bindDirectArithmetic(allocator, &template, pp.traceLogSize(), &layout);
    defer bound.deinit();
    if (bound.components.len != 1) return error.InvalidMixedRuntimeRoster;
    const states = try selected.plan.extract(values);
    var channel = Channel{};
    var order: many.TranscriptOrder = .{};
    mixProfile(&channel, selected);
    try order.accept(.profile);
    core.channel.lookup_transcript.mixChannelSalt(&channel, 0);
    try order.accept(.channel_salt);
    pcs.fri_config.mixInto(&channel);
    try order.accept(.fri_config);
    var scheme = try Engine.initRevision(allocator, pcs);
    var scheme_owned = true;
    errdefer if (scheme_owned) Engine.deinit(&scheme, allocator);
    scheme.setStorePolynomialsCoefficients();
    var pp_views: [direct_pp.N_COLUMNS]ColumnEvaluation = undefined;
    for (pp.columns, &pp_views) |entry, *view| view.* = .{ .log_size = entry.logSize(), .values = entry.values };
    try commit(&scheme, allocator, &pp_views, &channel);
    try order.accept(.preprocessed_commitment);
    const root = scheme.trees.items[0].commitment.root();
    if (!std.meta.eql(root, selected.fixed_root)) return error.InvalidMixedFixedRoot;
    var base = try direct_trace.writeBase(allocator, values, &pp);
    defer base.deinit();
    if (base.output_values.len != 8 or base.log_size != selected.geometry.slots[0].trace_log_size)
        return error.InvalidMixedPublicStatement;
    var chip_base: [max_calls]many_chip.Base = undefined;
    var bridge_base: [max_calls]BridgeBase = undefined;
    var chips_ready: usize = 0;
    var bridges_ready: usize = 0;
    defer for (chip_base[0..chips_ready]) |*item| item.deinit();
    defer for (bridge_base[0..bridges_ready]) |*item| item.deinit();
    for (selected.plan.callSlice(), states[0..selected.plan.count], 0..) |call, state, id| {
        chip_base[id] = if (id < 2)
            try pair_chip.writeBase(allocator, state.input, call.constant, call.rounds)
        else
            try many_chip.writeBase(allocator, state.input, call.constant, call.rounds);
        chips_ready += 1;
        if (!std.meta.eql(chip_base[id].final, state.output)) return error.WrongMixedChipClaim;
        bridge_base[id] = if (id < 2)
            .{ .pair = try pair_bridge.writeBase(allocator, values, call) }
        else
            .{ .many = try many_bridge.writeBase(allocator, values, call) };
        bridges_ready += 1;
    }
    const identity = selected.circuitIdentity();
    MC.mixRoot(&channel, identity);
    try order.accept(.circuit_identity);
    channel.mixFelts(base.output_values);
    try order.accept(.public_statement);
    var main_views: [mixed.max_tree_width]ColumnEvaluation = undefined;
    const main_width: usize = selected.geometry.tree_columns[1];
    try selectedColumns(main_views[0..main_width], selected, base.columns, chip_base[0..selected.plan.count], bridge_base[0..selected.plan.count], true);
    try commit(&scheme, allocator, main_views[0..main_width], &channel);
    try order.accept(.main_commitment);
    const interaction_pow_start_ns: u64 = if (timing != null) total_timer.read() else 0;
    const nonce = channel.grind(circuit.common.component_list.INTERACTION_POW_BITS);
    const interaction_pow_end_ns: u64 = if (timing != null) total_timer.read() else 0;
    channel.mixU64(nonce);
    try order.accept(.interaction_pow_nonce);
    const lookup = try core.channel.lookup_transcript.drawLookupElements(allocator, &channel);
    try order.accept(.lookup_challenge);
    var circuit_interaction = try direct_trace.writeInteraction(allocator, &base, &pp, lookup.z, lookup.alpha);
    defer circuit_interaction.deinit();
    var chip_interaction: [max_calls]ChipInteraction = undefined;
    var bridge_interaction: [max_calls]BridgeInteraction = undefined;
    var chip_interactions_ready: usize = 0;
    var bridge_interactions_ready: usize = 0;
    defer for (chip_interaction[0..chip_interactions_ready]) |*item| item.deinit();
    defer for (bridge_interaction[0..bridge_interactions_ready]) |*item| item.deinit();
    for (selected.plan.callSlice(), 0..) |call, id| {
        chip_interaction[id] = if (id < 2)
            .{ .pair = try pair_chip.writeInteraction(allocator, chip_base[id].columns, call.call_id, lookup.z, lookup.alpha) }
        else
            .{ .many = try many_chip.writeInteraction(allocator, chip_base[id].columns, call.call_id, lookup.z, lookup.alpha) };
        chip_interactions_ready += 1;
        bridge_interaction[id] = if (id < 2)
            .{ .pair = try pair_bridge.writeInteraction(allocator, bridge_base[id].columns(), call, lookup.z, lookup.alpha) }
        else
            .{ .many = try many_bridge.writeInteraction(allocator, bridge_base[id].columns(), call, lookup.z, lookup.alpha) };
        bridge_interactions_ready += 1;
    }
    const sums = try selectedSums(selected, circuit_interaction.claimed_sum, &chip_interaction, &bridge_interaction);
    var closure = try direct_trace.lookupSum(base.output_values, sums[0], lookup.z, lookup.alpha);
    for (sums[1..selected.geometry.slot_count]) |sum| closure = closure.add(sum);
    if (!closure.isZero()) return error.InvalidMixedLookupSum;
    core.channel.lookup_transcript.mixInteractionClaim(&channel, sums[0..selected.geometry.slot_count]);
    try order.accept(.claimed_sums);
    var interaction_views: [mixed.max_tree_width]ColumnEvaluation = undefined;
    const interaction_width: usize = selected.geometry.tree_columns[2];
    try selectedColumns(interaction_views[0..interaction_width], selected, circuit_interaction.columns, chip_interaction[0..selected.plan.count], bridge_interaction[0..selected.plan.count], false);
    try commit(&scheme, allocator, interaction_views[0..interaction_width], &channel);
    try order.accept(.interaction_commitment);
    var pp_logs = [_]u32{base.log_size} ** direct_pp.N_COLUMNS;
    const lifting = pcs.trace_lifting_log_size - pcs.fri_config.log_blowup_factor + 1;
    var captured = cairo.proving.air.component.Component.init(allocator, &bound.components[0], &pp_logs, lifting, lookup.z, lookup.alpha, sums[0]);
    var pc: [max_calls]pair_chip.Component = undefined;
    var pb: [max_calls]pair_bridge.Component = undefined;
    var mc: [max_calls]many_chip.Component = undefined;
    var mb: [max_calls]many_bridge.Component = undefined;
    var handles: [max_components]prover.air.component_prover.ComponentProver = undefined;
    handles[0] = captured.asProverComponent();
    for (selected.geometry.slotSlice()[1..], 1..) |slot, index| {
        const id: usize = @intCast(slot.call_id orelse return error.InvalidMixedRuntimeRoster);
        const call = selected.plan.calls[id];
        switch (slot.kind orelse return error.InvalidMixedRuntimeRoster) {
            .pair_chip => {
                pc[id] = .{ .log_size = slot.trace_log_size, .call_id = call.call_id, .constant = call.constant, .main_offset = slot.main_offset, .interaction_offset = slot.interaction_offset, .elements = .init(lookup.z, lookup.alpha), .claimed_sum = sums[index] };
                handles[index] = pc[id].asProverComponent();
            },
            .pair_bridge => {
                pb[id] = .{ .main_offset = slot.main_offset, .interaction_offset = slot.interaction_offset, .boundary = call, .elements = .init(lookup.z, lookup.alpha), .claimed_sum = sums[index] };
                handles[index] = pb[id].asProverComponent();
            },
            .many_chip => {
                mc[id] = .{ .log_size = slot.trace_log_size, .call_id = call.call_id, .constant = call.constant, .main_offset = slot.main_offset, .interaction_offset = slot.interaction_offset, .elements = .init(lookup.z, lookup.alpha), .claimed_sum = sums[index] };
                handles[index] = mc[id].asProverComponent();
            },
            .many_bridge => {
                mb[id] = .{ .main_offset = slot.main_offset, .interaction_offset = slot.interaction_offset, .boundary = call, .elements = .init(lookup.z, lookup.alpha), .claimed_sum = sums[index] };
                handles[index] = mb[id].asProverComponent();
            },
        }
    }
    try checkRuntimeHandles(prover.air.component_prover.ComponentProver, allocator, handles[0..selected.geometry.slot_count], selected);
    var recorder: prover.stage_profile.Recorder = undefined;
    if (timing != null)
        recorder = prover.stage_profile.Recorder.initWithOptions(allocator, "s31_mixed_general", "prove", .{ .capture_tasks = false });
    defer if (timing != null) recorder.deinit();
    const pcs_prove_start_ns: u64 = if (timing != null) total_timer.read() else 0;
    scheme_owned = false;
    var stark = try Engine.prove(allocator, handles[0..selected.geometry.slot_count], &channel, scheme, .{
        .include_all_preprocessed_columns = true,
        .recorder = if (timing != null) &recorder else null,
    });
    const pcs_prove_end_ns: u64 = if (timing != null) total_timer.read() else 0;
    try order.accept(.pcs_proof);
    try order.finish();
    errdefer stark.deinit(allocator);
    var fri_pow_ns: u64 = 0;
    if (timing != null) {
        var profile = try recorder.snapshot(allocator);
        defer profile.deinit(allocator);
        var count: usize = 0;
        var seconds: f64 = 0;
        collectFriPowStage(profile.stages, &count, &seconds);
        if (count != 1 or !std.math.isFinite(seconds) or seconds < 0)
            return error.InvalidMixedFriPowTiming;
        fri_pow_ns = @intFromFloat(seconds * std.time.ns_per_s);
        if (fri_pow_ns > pcs_prove_end_ns - pcs_prove_start_ns)
            return error.InvalidMixedFriPowTiming;
    }
    const output_values = try allocator.dupe(QM31, base.output_values);
    errdefer allocator.free(output_values);
    if (timing) |slot| slot.* = .{
        .prove_body_ns = total_timer.read(),
        .interaction_pow_ns = interaction_pow_end_ns - interaction_pow_start_ns,
        .pcs_prove_ns = pcs_prove_end_ns - pcs_prove_start_ns,
        .fri_pow_ns = fri_pow_ns,
    };
    return .{
        .allocator = allocator,
        .pcs_config = pcs,
        .output_values = output_values,
        .interaction_pow_nonce = nonce,
        .claimed_sums = sums,
        .sum_count = selected.geometry.slot_count,
        .stark_proof = stark,
        .circuit_hash = identity,
    };
}

fn collectFriPowStage(nodes: []const prover.stage_profile.StageNode, count: *usize, seconds: *f64) void {
    for (nodes) |node| {
        if (std.mem.eql(u8, node.id, "proof_of_work")) {
            count.* += 1;
            seconds.* = node.seconds;
        }
        if (node.children) |children| collectFriPowStage(children, count, seconds);
    }
}

/// Caller-scoped native adapter, not a standalone verifier key. This checks
/// the selected circuit geometry against the supplied circuit/source bytes,
/// but only the S31 source-embedded wrapper derives the manifest digest and
/// public words from authoritative source. Do not admit external proof bytes
/// through a caller-selected `Selected` value.
pub fn verifySourceBoundBorrowed(
    allocator: std.mem.Allocator,
    source: CircuitView,
    source_bytes: []const u8,
    air_bytes: []const u8,
    selected: *const Selected,
    public_words: [8]u32,
    proof: BorrowedProof,
) !void {
    if (selected.plan.count == 0 or selected.plan.count > max_calls)
        return error.InvalidMixedSelection;
    try plan_admission.requireResourceShape(source);
    try validatePublicOutputShape(source);
    var pp = try plan_admission.BoundedPlan.fromLegacy(selected.plan).preprocessed(allocator, source);
    defer pp.deinit(allocator);
    var template = try air.parse(allocator, air_bytes);
    defer template.deinit();
    try validateSourceAndGeometry(allocator, &pp, &template, selected, source_bytes, air_bytes);
    const pcs = selected.geometry.pcs;
    const identity = selected.circuitIdentity();
    if (proof.sum_count != selected.geometry.slot_count or !std.meta.eql(proof.circuit_hash, identity))
        return error.InvalidMixedProofIdentity;
    for (proof.claimed_sums[selected.geometry.slot_count..]) |unused|
        if (!unused.isZero()) return error.NonCanonicalMixedClaimedSums;
    var committed = try direct.PreprocessedCommitment.build(allocator, &pp, pcs);
    defer committed.deinit(allocator);
    const roots = proof.stark_proof.commitment_scheme_proof.commitments.items;
    if (roots.len != 4 or !std.meta.eql(roots[0], committed.root()))
        return error.InvalidMixedPreprocessedRoot;
    if (!std.meta.eql(proof.stark_proof.commitment_scheme_proof.config, core.protocol_revision.Revision.proving_5a7c5ed.legacyView(pcs)))
        return error.InvalidMixedPcsConfig;
    var outputs: [8]QM31 = undefined;
    for (public_words, &outputs, 0..) |word, *output, index| {
        if (word >= core.fields.m31.Modulus or proof.output_values.len != 8)
            return error.InvalidMixedPublicStatement;
        output.* = QM31.fromBase(M31.fromCanonical(word));
        if (!proof.output_values[index].eql(output.*)) return error.InvalidMixedPublicStatement;
    }
    var channel = Channel{};
    var order: many.TranscriptOrder = .{};
    mixProfile(&channel, selected);
    try order.accept(.profile);
    core.channel.lookup_transcript.mixChannelSalt(&channel, 0);
    try order.accept(.channel_salt);
    pcs.fri_config.mixInto(&channel);
    try order.accept(.fri_config);
    var scheme = try core.pcs.verifier.CommitmentSchemeVerifier(H, MC).init(allocator, pcs);
    defer scheme.deinit(allocator);
    var pp_logs = [_]u32{pp.traceLogSize()} ** direct_pp.N_COLUMNS;
    try scheme.commit(allocator, roots[0], &pp_logs, &channel);
    try order.accept(.preprocessed_commitment);
    MC.mixRoot(&channel, identity);
    try order.accept(.circuit_identity);
    channel.mixFelts(&outputs);
    try order.accept(.public_statement);
    var main_logs: [mixed.max_tree_width]u32 = undefined;
    const main_width: usize = selected.geometry.tree_columns[1];
    for (selected.geometry.columns[1][0..main_width], main_logs[0..main_width]) |column, *log| log.* = column.log_size;
    try scheme.commit(allocator, roots[1], main_logs[0..main_width], &channel);
    try order.accept(.main_commitment);
    if (!channel.verifyPowNonce(circuit.common.component_list.INTERACTION_POW_BITS, proof.interaction_pow_nonce))
        return error.InvalidMixedInteractionNonce;
    channel.mixU64(proof.interaction_pow_nonce);
    try order.accept(.interaction_pow_nonce);
    const lookup = try core.channel.lookup_transcript.drawLookupElements(allocator, &channel);
    try order.accept(.lookup_challenge);
    var closure = try direct_trace.lookupSum(&outputs, proof.claimed_sums[0], lookup.z, lookup.alpha);
    for (proof.claimed_sums[1..selected.geometry.slot_count]) |sum| closure = closure.add(sum);
    if (!closure.isZero()) return error.InvalidMixedLookupSum;
    core.channel.lookup_transcript.mixInteractionClaim(&channel, proof.claimed_sums[0..selected.geometry.slot_count]);
    try order.accept(.claimed_sums);
    var interaction_logs: [mixed.max_tree_width]u32 = undefined;
    const interaction_width: usize = selected.geometry.tree_columns[2];
    for (selected.geometry.columns[2][0..interaction_width], interaction_logs[0..interaction_width]) |column, *log| log.* = column.log_size;
    try scheme.commit(allocator, roots[2], interaction_logs[0..interaction_width], &channel);
    try order.accept(.interaction_commitment);
    const layout = pp.layout();
    var bound = try air.bindDirectArithmetic(allocator, &template, pp.traceLogSize(), &layout);
    defer bound.deinit();
    if (bound.components.len != 1 or
        !std.meta.eql(try air.directProgramBindingDigest(air_bytes, &bound), selected.circuit_program_sha256))
        return error.InvalidMixedRuntimeRoster;
    const lifting = pcs.trace_lifting_log_size - pcs.fri_config.log_blowup_factor + 1;
    var captured = cairo.proving.air.component.Component.init(allocator, &bound.components[0], &pp_logs, lifting, lookup.z, lookup.alpha, proof.claimed_sums[0]);
    var pc: [max_calls]pair_chip.Component = undefined;
    var pb: [max_calls]pair_bridge.Component = undefined;
    var mc: [max_calls]many_chip.Component = undefined;
    var mb: [max_calls]many_bridge.Component = undefined;
    var handles: [max_components]core.air.components.Component = undefined;
    handles[0] = captured.asVerifierComponent();
    for (selected.geometry.slotSlice()[1..], 1..) |slot, index| {
        const id: usize = @intCast(slot.call_id orelse return error.InvalidMixedRuntimeRoster);
        if (id >= selected.plan.count) return error.InvalidMixedRuntimeRoster;
        const call = selected.plan.calls[id];
        switch (slot.kind orelse return error.InvalidMixedRuntimeRoster) {
            .pair_chip => {
                pc[id] = .{ .log_size = slot.trace_log_size, .call_id = call.call_id, .constant = call.constant, .main_offset = slot.main_offset, .interaction_offset = slot.interaction_offset, .elements = .init(lookup.z, lookup.alpha), .claimed_sum = proof.claimed_sums[index] };
                handles[index] = pc[id].asVerifierComponent();
            },
            .pair_bridge => {
                pb[id] = .{ .main_offset = slot.main_offset, .interaction_offset = slot.interaction_offset, .boundary = call, .elements = .init(lookup.z, lookup.alpha), .claimed_sum = proof.claimed_sums[index] };
                handles[index] = pb[id].asVerifierComponent();
            },
            .many_chip => {
                mc[id] = .{ .log_size = slot.trace_log_size, .call_id = call.call_id, .constant = call.constant, .main_offset = slot.main_offset, .interaction_offset = slot.interaction_offset, .elements = .init(lookup.z, lookup.alpha), .claimed_sum = proof.claimed_sums[index] };
                handles[index] = mc[id].asVerifierComponent();
            },
            .many_bridge => {
                mb[id] = .{ .main_offset = slot.main_offset, .interaction_offset = slot.interaction_offset, .boundary = call, .elements = .init(lookup.z, lookup.alpha), .claimed_sum = proof.claimed_sums[index] };
                handles[index] = mb[id].asVerifierComponent();
            },
        }
    }
    try checkRuntimeHandles(core.air.components.Component, allocator, handles[0..selected.geometry.slot_count], selected);
    var capture: core.verifier.ProofCapture(H) = undefined;
    try core.verifier.verifyBorrowedExWithProofCapture(H, MC, allocator, handles[0..selected.geometry.slot_count], &channel, &scheme, proof.stark_proof, true, &capture);
    try order.accept(.pcs_proof);
    try order.finish();
    defer capture.deinit(allocator);
}

/// Verify the STARK first, then audit a separately supplied complete witness
/// against its authenticated fixed/main/interaction Merkle roots. Rebuilding
/// roots is expensive and exposes the witness to this caller; ordinary proof
/// admission never invokes it. Equality is a binding claim under the hash/PCS
/// assumptions, not extraction of a trace from succinct proof bytes.
pub fn auditVerifiedSourceBoundWitness(
    allocator: std.mem.Allocator,
    source: CircuitView,
    values: []const QM31,
    source_bytes: []const u8,
    air_bytes: []const u8,
    selected: *const Selected,
    public_words: [8]u32,
    proof: BorrowedProof,
) !TraceAudit {
    try verifySourceBoundBorrowed(allocator, source, source_bytes, air_bytes, selected, public_words, proof);
    var pp = try plan_admission.BoundedPlan.fromLegacy(selected.plan).preprocessed(allocator, source);
    defer pp.deinit(allocator);
    var template = try air.parse(allocator, air_bytes);
    defer template.deinit();
    try validateSourceAndGeometry(allocator, &pp, &template, selected, source_bytes, air_bytes);
    const states = try selected.plan.extract(values);
    var base = try direct_trace.writeBase(allocator, values, &pp);
    defer base.deinit();
    const circuit_rows = try auditCircuitRows(allocator, source, values, &pp, &base, selected.plan);
    for (base.output_values, public_words) |actual, expected| {
        if (!actual.eql(QM31.fromBase(M31.fromCanonical(expected))))
            return error.InvalidMixedTraceAuditPublic;
    }
    var chip_base: [max_calls]many_chip.Base = undefined;
    var bridge_base: [max_calls]BridgeBase = undefined;
    var chips_ready: usize = 0;
    var bridges_ready: usize = 0;
    defer for (chip_base[0..chips_ready]) |*item| item.deinit();
    defer for (bridge_base[0..bridges_ready]) |*item| item.deinit();
    for (selected.plan.callSlice(), states[0..selected.plan.count], 0..) |call, state, id| {
        chip_base[id] = if (id < 2)
            try pair_chip.writeBase(allocator, state.input, call.constant, call.rounds)
        else
            try many_chip.writeBase(allocator, state.input, call.constant, call.rounds);
        chips_ready += 1;
        bridge_base[id] = if (id < 2)
            .{ .pair = try pair_bridge.writeBase(allocator, values, call) }
        else
            .{ .many = try many_bridge.writeBase(allocator, values, call) };
        bridges_ready += 1;
    }
    const chip_bridge_rows = try auditChipBridgeRows(
        selected.plan,
        states,
        chip_base[0..selected.plan.count],
        bridge_base[0..selected.plan.count],
    );
    const roots = proof.stark_proof.commitment_scheme_proof.commitments.items;
    if (roots.len != 4) return error.InvalidMixedTraceAuditProofRoots;
    const pcs = selected.geometry.pcs;
    var scheme = try Engine.initRevision(allocator, pcs);
    defer Engine.deinit(&scheme, allocator);
    scheme.setStorePolynomialsCoefficients();
    var channel = Channel{};
    mixProfile(&channel, selected);
    core.channel.lookup_transcript.mixChannelSalt(&channel, 0);
    pcs.fri_config.mixInto(&channel);
    var pp_views: [direct_pp.N_COLUMNS]ColumnEvaluation = undefined;
    for (pp.columns, &pp_views) |entry, *view| view.* = .{ .log_size = entry.logSize(), .values = entry.values };
    try commit(&scheme, allocator, &pp_views, &channel);
    const fixed_root = scheme.trees.items[0].commitment.root();
    if (!std.meta.eql(fixed_root, selected.fixed_root) or !std.meta.eql(fixed_root, roots[0]))
        return error.InvalidMixedTraceAuditFixedRoot;
    MC.mixRoot(&channel, selected.circuitIdentity());
    channel.mixFelts(base.output_values);
    var main_views: [mixed.max_tree_width]ColumnEvaluation = undefined;
    const main_width: usize = selected.geometry.tree_columns[1];
    try selectedColumns(main_views[0..main_width], selected, base.columns, chip_base[0..selected.plan.count], bridge_base[0..selected.plan.count], true);
    try commit(&scheme, allocator, main_views[0..main_width], &channel);
    const main_root = scheme.trees.items[1].commitment.root();
    if (!std.meta.eql(main_root, roots[1])) return error.InvalidMixedTraceAuditMainRoot;
    if (!channel.verifyPowNonce(circuit.common.component_list.INTERACTION_POW_BITS, proof.interaction_pow_nonce))
        return error.InvalidMixedTraceAuditNonce;
    channel.mixU64(proof.interaction_pow_nonce);
    const lookup = try core.channel.lookup_transcript.drawLookupElements(allocator, &channel);
    var circuit_interaction = try direct_trace.writeInteraction(allocator, &base, &pp, lookup.z, lookup.alpha);
    defer circuit_interaction.deinit();
    var chip_interaction: [max_calls]ChipInteraction = undefined;
    var bridge_interaction: [max_calls]BridgeInteraction = undefined;
    var chip_interactions_ready: usize = 0;
    var bridge_interactions_ready: usize = 0;
    defer for (chip_interaction[0..chip_interactions_ready]) |*item| item.deinit();
    defer for (bridge_interaction[0..bridge_interactions_ready]) |*item| item.deinit();
    for (selected.plan.callSlice(), 0..) |call, id| {
        chip_interaction[id] = if (id < 2)
            .{ .pair = try pair_chip.writeInteraction(allocator, chip_base[id].columns, call.call_id, lookup.z, lookup.alpha) }
        else
            .{ .many = try many_chip.writeInteraction(allocator, chip_base[id].columns, call.call_id, lookup.z, lookup.alpha) };
        chip_interactions_ready += 1;
        bridge_interaction[id] = if (id < 2)
            .{ .pair = try pair_bridge.writeInteraction(allocator, bridge_base[id].columns(), call, lookup.z, lookup.alpha) }
        else
            .{ .many = try many_bridge.writeInteraction(allocator, bridge_base[id].columns(), call, lookup.z, lookup.alpha) };
        bridge_interactions_ready += 1;
    }
    try auditInteractionRows(
        &pp,
        &base,
        &circuit_interaction,
        selected.plan,
        chip_base[0..selected.plan.count],
        bridge_base[0..selected.plan.count],
        chip_interaction[0..selected.plan.count],
        bridge_interaction[0..selected.plan.count],
        lookup.z,
        lookup.alpha,
    );
    const sums = try selectedSums(selected, circuit_interaction.claimed_sum, &chip_interaction, &bridge_interaction);
    for (sums[0..selected.geometry.slot_count], proof.claimed_sums[0..selected.geometry.slot_count]) |actual, claimed|
        if (!actual.eql(claimed)) return error.InvalidMixedTraceAuditClaimedSum;
    var closure = try direct_trace.lookupSum(base.output_values, sums[0], lookup.z, lookup.alpha);
    for (sums[1..selected.geometry.slot_count]) |sum| closure = closure.add(sum);
    if (!closure.isZero()) return error.InvalidMixedTraceAuditLookup;
    core.channel.lookup_transcript.mixInteractionClaim(&channel, sums[0..selected.geometry.slot_count]);
    var interaction_views: [mixed.max_tree_width]ColumnEvaluation = undefined;
    const interaction_width: usize = selected.geometry.tree_columns[2];
    try selectedColumns(interaction_views[0..interaction_width], selected, circuit_interaction.columns, chip_interaction[0..selected.plan.count], bridge_interaction[0..selected.plan.count], false);
    try commit(&scheme, allocator, interaction_views[0..interaction_width], &channel);
    const interaction_root = scheme.trees.items[2].commitment.root();
    if (!std.meta.eql(interaction_root, roots[2])) return error.InvalidMixedTraceAuditInteractionRoot;
    return .{
        .fixed_root = fixed_root,
        .main_root = main_root,
        .interaction_root = interaction_root,
        .circuit_rows = circuit_rows,
        .chip_rows = chip_bridge_rows.chip,
        .bridge_rows = chip_bridge_rows.bridge,
    };
}

test "general mixed native proof uses source-derived one through eight call rosters" {
    const allocator = std.heap.smp_allocator;
    inline for (1..max_calls + 1) |n| {
        var ctx = try circuit.builder.Context(QM31).init(allocator, 8);
        defer ctx.deinit();
        var plan: many.Plan = .{ .count = n };
        var results: [n][4]circuit.builder.Var = undefined;
        for (0..n) |id| {
            var start: [4]M31 = undefined;
            for (&start, 0..) |*value, lane|
                value.* = M31.fromCanonical(@intCast(2 + 4 * id + lane));
            const constant = M31.fromCanonical(@intCast(13 + id));
            const final = try @import("repeated_step_chip.zig").direct(start, constant, 16);
            plan.calls[id].call_id = @intCast(id);
            plan.calls[id].constant = constant;
            plan.calls[id].rounds = 16;
            for (0..4) |lane| {
                const input = try ctx.guessM31(QM31.fromBase(start[lane]));
                const result = try ctx.guessM31(QM31.fromBase(final[lane]));
                plan.calls[id].input[lane] = input.idx;
                plan.calls[id].output[lane] = result.idx;
                results[id][lane] = result;
            }
        }
        var outputs: [8]circuit.builder.Var = undefined;
        for (0..4) |lane| {
            var sum = results[0][lane];
            var product = results[0][lane];
            for (1..n) |id| {
                sum = try ctx.add(sum, results[id][lane]);
                product = try ctx.mul(product, results[id][lane]);
            }
            outputs[lane] = try ctx.add(sum, results[0][lane]);
            outputs[4 + lane] = try ctx.mul(product, results[0][lane]);
        }
        try ctx.setOutputs(&outputs);
        try ctx.finalize(false);
        try circuit.common.finalize.padToTargets(QM31, &ctx, .{
            .eq = 0,
            .qm31_ops = circuit.common.finalize.paddedSize(ctx.circuit.nQm31OpsRows()),
            .triple_xor = 0,
            .m31_to_u32 = 0,
            .blake_g_gate = 0,
        });
        try std.testing.expect(try ctx.isCircuitValid());
        const source = CircuitView.fromBuilder(&ctx.circuit);
        var pp = try plan.preprocessed(allocator, source);
        defer pp.deinit(allocator);
        const bundle_bytes = try std.fs.cwd().readFileAlloc(allocator, air.bundle_path, 1 << 20);
        defer allocator.free(bundle_bytes);
        var bundle = try air.parse(allocator, bundle_bytes);
        defer bundle.deinit();
        const geometry = try mixed.inspect(allocator, &pp, &bundle, plan);
        try std.testing.expectEqual(@as(usize, 1 + 2 * n), geometry.slot_count);
        const layout = pp.layout();
        var bound = try air.bindDirectArithmetic(allocator, &bundle, pp.traceLogSize(), &layout);
        defer bound.deinit();
        const source_bytes = std.fmt.comptimePrint("s31-mixed-general-native-{d}", .{n});
        const selected: Selected = .{
            .source_sha256 = digest(source_bytes),
            .manifest_sha256 = digest(std.fmt.comptimePrint("s31-mixed-general-manifest-{d}", .{n})),
            .fixed_root = try pp.preprocessedRoot(allocator, 1),
            .circuit_program_sha256 = try air.directProgramBindingDigest(bundle_bytes, &bound),
            .plan = plan,
            .geometry = geometry,
        };
        var proof = try proveSourceBound(allocator, source, ctx.values(), source_bytes, bundle_bytes, &selected);
        defer proof.deinit();
        try std.testing.expectEqual(@as(usize, 1 + 2 * n), proof.sum_count);
        if (n == 2 or n == 6) {
            var timing: Timing = undefined;
            var timed = try proveSourceBoundWithTiming(allocator, source, ctx.values(), source_bytes, bundle_bytes, &selected, &timing);
            defer timed.deinit();
            try std.testing.expect(timing.interaction_pow_ns > 0 and timing.fri_pow_ns > 0);
            try std.testing.expect(timing.pcs_prove_ns >= timing.fri_pow_ns);
            try std.testing.expect(timing.prove_body_ns >= timing.interaction_pow_ns + timing.pcs_prove_ns);
            try std.testing.expectEqual(proof.interaction_pow_nonce, timed.interaction_pow_nonce);
            try std.testing.expectEqual(proof.sum_count, timed.sum_count);
            try std.testing.expectEqualSlices(QM31, proof.output_values, timed.output_values);
            try std.testing.expectEqualSlices(QM31, proof.claimed_sums[0..proof.sum_count], timed.claimed_sums[0..timed.sum_count]);
            try std.testing.expectEqualSlices(u8, &proof.circuit_hash, &timed.circuit_hash);
            const plain_json = try std.json.Stringify.valueAlloc(allocator, core.proof_json.ProofView(@TypeOf(proof.stark_proof.proof)){
                .proof = &proof.stark_proof.proof,
            }, .{});
            defer allocator.free(plain_json);
            const timed_json = try std.json.Stringify.valueAlloc(allocator, core.proof_json.ProofView(@TypeOf(timed.stark_proof.proof)){
                .proof = &timed.stark_proof.proof,
            }, .{});
            defer allocator.free(timed_json);
            try std.testing.expectEqualSlices(u8, plain_json, timed_json);
            var timed_words: [8]u32 = undefined;
            for (timed.output_values, &timed_words) |value, *word| word.* = value.toM31Array()[0].toU32();
            const timed_borrowed: BorrowedProof = .{
                .output_values = timed.output_values,
                .interaction_pow_nonce = timed.interaction_pow_nonce,
                .claimed_sums = timed.claimed_sums,
                .sum_count = timed.sum_count,
                .stark_proof = &timed.stark_proof.proof,
                .circuit_hash = timed.circuit_hash,
            };
            try verifySourceBoundBorrowed(allocator, source, source_bytes, bundle_bytes, &selected, timed_words, timed_borrowed);
            std.debug.print("S31_MIXED_TIMING_SAMPLE n={d} prove_body_ns={d} interaction_pow_ns={d} pcs_prove_ns={d} fri_pow_ns={d}\n", .{
                n, timing.prove_body_ns, timing.interaction_pow_ns, timing.pcs_prove_ns, timing.fri_pow_ns,
            });
        }
        var words: [8]u32 = undefined;
        for (proof.output_values, &words) |value, *word| {
            const limbs = value.toM31Array();
            try std.testing.expect(limbs[1].isZero() and limbs[2].isZero() and limbs[3].isZero());
            word.* = limbs[0].toU32();
        }
        var borrowed: BorrowedProof = .{
            .output_values = proof.output_values,
            .interaction_pow_nonce = proof.interaction_pow_nonce,
            .claimed_sums = proof.claimed_sums,
            .sum_count = proof.sum_count,
            .stark_proof = &proof.stark_proof.proof,
            .circuit_hash = proof.circuit_hash,
        };
        try verifySourceBoundBorrowed(allocator, source, source_bytes, bundle_bytes, &selected, words, borrowed);
        for (0..proof.sum_count) |index| {
            borrowed.claimed_sums[index] = borrowed.claimed_sums[index].add(QM31.one());
            try std.testing.expectError(error.InvalidMixedLookupSum, verifySourceBoundBorrowed(allocator, source, source_bytes, bundle_bytes, &selected, words, borrowed));
            borrowed.claimed_sums[index] = borrowed.claimed_sums[index].sub(QM31.one());
        }
        borrowed.claimed_sums[1] = borrowed.claimed_sums[1].add(QM31.one());
        borrowed.claimed_sums[2] = borrowed.claimed_sums[2].sub(QM31.one());
        if (verifySourceBoundBorrowed(allocator, source, source_bytes, bundle_bytes, &selected, words, borrowed)) |_| {
            return error.AcceptedCompensatedGeneralMixedSums;
        } else |_| {}
        borrowed.claimed_sums[1] = borrowed.claimed_sums[1].sub(QM31.one());
        borrowed.claimed_sums[2] = borrowed.claimed_sums[2].add(QM31.one());
        if (proof.sum_count < max_components) {
            borrowed.claimed_sums[proof.sum_count] = QM31.one();
            try std.testing.expectError(error.NonCanonicalMixedClaimedSums, verifySourceBoundBorrowed(allocator, source, source_bytes, bundle_bytes, &selected, words, borrowed));
            borrowed.claimed_sums[proof.sum_count] = QM31.zero();
        }
        var wrong_words = words;
        wrong_words[0] ^= 1;
        if (verifySourceBoundBorrowed(allocator, source, source_bytes, bundle_bytes, &selected, wrong_words, borrowed)) |_| {
            return error.AcceptedChangedGeneralMixedPublicWord;
        } else |_| {}
        var changed_role = selected;
        changed_role.geometry.slots[1].kind = .pair_bridge;
        if (verifySourceBoundBorrowed(allocator, source, source_bytes, bundle_bytes, &changed_role, words, borrowed)) |_| {
            return error.AcceptedChangedGeneralMixedRole;
        } else |_| {}
    }
}

test "mixed trace audit rejects interaction and bridge mutations" {
    const allocator = std.testing.allocator;
    const Context = struct {
        pole: bool = false,
        fn fill(self: @This(), row: usize, out: []AuditFraction) !void {
            out[0] = .{
                .numerator = QM31.fromBase(M31.fromU64(row + 1)),
                .denominator = if (self.pole and row == 3) QM31.zero() else QM31.fromBase(M31.fromCanonical(2)),
            };
            out[1] = .{
                .numerator = QM31.fromBase(M31.fromU64(row + 3)),
                .denominator = QM31.fromBase(M31.fromCanonical(7)),
            };
        }
    };
    const context = Context{};
    const logup = try prover.air.logup_columns.build(allocator, 4, 2, context, Context.fill);
    defer {
        for (logup.columns) |column| allocator.free(column.values);
        allocator.free(logup.columns);
    }
    try auditLogupRows(logup.columns, 4, 2, logup.claimed_sum, context, Context.fill);
    const row = @import("repeated_step_chip.zig").storageIndex(3, 4);
    try std.testing.expect(row != 3);
    const old_logup = logup.columns[4].values[row];
    @constCast(logup.columns[4].values)[row] = old_logup.add(M31.one());
    try std.testing.expectError(error.InvalidMixedTraceAuditInteraction, auditLogupRows(logup.columns, 4, 2, logup.claimed_sum, context, Context.fill));
    @constCast(logup.columns[4].values)[row] = old_logup;
    try std.testing.expectError(error.MixedTraceAuditDenominatorPole, auditLogupRows(logup.columns, 4, 2, logup.claimed_sum, Context{ .pole = true }, Context.fill));

    const initial = [4]M31{ M31.fromCanonical(1), M31.fromCanonical(2), M31.fromCanonical(3), M31.fromCanonical(4) };
    const constant = M31.fromCanonical(13);
    const final = try @import("repeated_step_chip.zig").direct(initial, constant, 16);
    var plan: many.Plan = .{ .count = 1 };
    plan.calls[0] = .{
        .call_id = 0,
        .rounds = 16,
        .constant = constant,
        .input = .{ 3, 4, 5, 6 },
        .output = .{ 7, 8, 9, 10 },
    };
    var values = [_]QM31{QM31.zero()} ** 11;
    for (initial, plan.calls[0].input) |value, address| values[address] = QM31.fromBase(value);
    for (final, plan.calls[0].output) |value, address| values[address] = QM31.fromBase(value);
    const states = try plan.extract(&values);
    var chip_base = try pair_chip.writeBase(allocator, initial, constant, 16);
    defer chip_base.deinit();
    var bridge_base: BridgeBase = .{ .pair = try pair_bridge.writeBase(allocator, &values, plan.calls[0]) };
    defer bridge_base.deinit();
    try std.testing.expectEqual(@as(usize, 16), (try auditChipBridgeRows(plan, states, (&chip_base)[0..1], (&bridge_base)[0..1])).chip);
    const old_chip = chip_base.columns[1].values[row];
    @constCast(chip_base.columns[1].values)[row] = old_chip.add(M31.one());
    try std.testing.expectError(error.InvalidMixedTraceAuditChip, auditChipBridgeRows(plan, states, (&chip_base)[0..1], (&bridge_base)[0..1]));
    @constCast(chip_base.columns[1].values)[row] = old_chip;
    const old_chip_log = chip_base.columns[8].log_size;
    chip_base.columns[8].log_size = old_chip_log + 1;
    try std.testing.expectError(error.InvalidMixedTraceAuditChip, auditChipBridgeRows(plan, states, (&chip_base)[0..1], (&bridge_base)[0..1]));
    chip_base.columns[8].log_size = old_chip_log;
    const bridge_columns = bridge_base.columns();
    const old_bridge = bridge_columns[0].values[1];
    @constCast(bridge_columns[0].values)[1] = old_bridge.add(M31.one());
    try std.testing.expectError(error.InvalidMixedTraceAuditBridge, auditChipBridgeRows(plan, states, (&chip_base)[0..1], (&bridge_base)[0..1]));
    @constCast(bridge_columns[0].values)[1] = old_bridge;
    const z = QM31.fromU32Unchecked(17, 2, 3, 5);
    const alpha = QM31.fromU32Unchecked(11, 7, 13, 19);
    var chip_interaction = try pair_chip.writeInteraction(allocator, chip_base.columns, 0, z, alpha);
    defer chip_interaction.deinit();
    var bridge_interaction = try pair_bridge.writeInteraction(allocator, bridge_columns, plan.calls[0], z, alpha);
    defer bridge_interaction.deinit();
    const chip_context = ChipFractions{ .base = chip_base.columns, .call = plan.calls[0], .elements = .init(z, alpha) };
    const bridge_context = BridgeFractions{ .base = bridge_columns, .call = plan.calls[0], .elements = .init(z, alpha) };
    try auditLogupRows(chip_interaction.columns, 4, 2, chip_interaction.claimed_sum, chip_context, ChipFractions.fill);
    try auditLogupRows(bridge_interaction.columns, 4, 5, bridge_interaction.claimed_sum, bridge_context, BridgeFractions.fill);
    const old_chip_interaction = chip_interaction.columns[0].values[3];
    @constCast(chip_interaction.columns[0].values)[3] = old_chip_interaction.add(M31.one());
    try std.testing.expectError(error.InvalidMixedTraceAuditInteraction, auditLogupRows(chip_interaction.columns, 4, 2, chip_interaction.claimed_sum, chip_context, ChipFractions.fill));
    @constCast(chip_interaction.columns[0].values)[3] = old_chip_interaction;
    const old_bridge_interaction = bridge_interaction.columns[8].values[1];
    @constCast(bridge_interaction.columns[8].values)[1] = old_bridge_interaction.add(M31.one());
    try std.testing.expectError(error.InvalidMixedTraceAuditInteraction, auditLogupRows(bridge_interaction.columns, 4, 5, bridge_interaction.claimed_sum, bridge_context, BridgeFractions.fill));
    @constCast(bridge_interaction.columns[8].values)[1] = old_bridge_interaction;
}

test "mixed trace audit checks reserved public and every gate row" {
    const allocator = std.testing.allocator;
    var ctx = try circuit.builder.Context(QM31).init(allocator, 8);
    defer ctx.deinit();
    const initial = [4]M31{ M31.fromCanonical(1), M31.fromCanonical(2), M31.fromCanonical(3), M31.fromCanonical(4) };
    const constant = M31.fromCanonical(13);
    const final = try @import("repeated_step_chip.zig").direct(initial, constant, 16);
    var plan: many.Plan = .{ .count = 1 };
    plan.calls[0] = .{
        .call_id = 0,
        .rounds = 16,
        .constant = constant,
        .input = undefined,
        .output = undefined,
    };
    var inputs: [4]circuit.builder.Var = undefined;
    var results: [4]circuit.builder.Var = undefined;
    for (0..4) |lane| {
        inputs[lane] = try ctx.guessM31(QM31.fromBase(initial[lane]));
        results[lane] = try ctx.guessM31(QM31.fromBase(final[lane]));
        plan.calls[0].input[lane] = inputs[lane].idx;
        plan.calls[0].output[lane] = results[lane].idx;
    }
    var outputs: [8]circuit.builder.Var = undefined;
    for (0..4) |lane| {
        outputs[lane] = try ctx.add(inputs[lane], results[lane]);
        outputs[4 + lane] = try ctx.mul(inputs[lane], results[lane]);
    }
    try ctx.setOutputs(&outputs);
    try ctx.finalize(false);
    try circuit.common.finalize.padToTargets(QM31, &ctx, .{
        .eq = 0,
        // Cross the current power-of-two boundary so this audit also sees
        // zero-multiplicity padding Gate rows.
        .qm31_ops = circuit.common.finalize.paddedSize(ctx.circuit.nQm31OpsRows() + 1),
        .triple_xor = 0,
        .m31_to_u32 = 0,
        .blake_g_gate = 0,
    });
    const source = CircuitView.fromBuilder(&ctx.circuit);
    var pp = try plan.preprocessed(allocator, source);
    defer pp.deinit(allocator);
    var base = try direct_trace.writeBase(allocator, ctx.values(), &pp);
    defer base.deinit();
    try std.testing.expectEqual(source.nQm31OpsRows(), try auditCircuitRows(allocator, source, ctx.values(), &pp, &base, plan));
    const values = try allocator.dupe(QM31, ctx.values());
    defer allocator.free(values);
    values[2] = QM31.zero();
    try std.testing.expectError(error.InvalidMixedTraceAuditReserved, auditCircuitRows(allocator, source, values, &pp, &base, plan));
    values[2] = ctx.values()[2];
    const address = source.add[0].out;
    values[address] = values[address].add(QM31.one());
    try std.testing.expectError(error.InvalidMixedTraceAuditGate, auditCircuitRows(allocator, source, values, &pp, &base, plan));
    values[address] = ctx.values()[address];
    const padding_row = source.add.len - 1;
    const padding_gate = source.add[padding_row];
    try std.testing.expectEqual(@as(u32, 1), padding_gate.in0);
    try std.testing.expectEqual(@as(u32, 1), padding_gate.in1);
    try std.testing.expectEqual(@as(u32, 0), pp.columns[7].values[padding_row].toU32());
    values[padding_gate.out] = values[padding_gate.out].add(QM31.one());
    try std.testing.expectError(error.InvalidMixedTraceAuditGate, auditCircuitRows(allocator, source, values, &pp, &base, plan));
    values[padding_gate.out] = ctx.values()[padding_gate.out];
    const original_main = base.columns[0].values[0];
    @constCast(base.columns[0].values)[0] = original_main.add(M31.one());
    try std.testing.expectError(error.InvalidMixedTraceAuditMain, auditCircuitRows(allocator, source, values, &pp, &base, plan));
    @constCast(base.columns[0].values)[0] = original_main;
    const original_mult = pp.columns[7].values[0];
    pp.columns[7].values[0] = original_mult.add(M31.one());
    try std.testing.expectError(error.InvalidMixedTraceAuditFixed, auditCircuitRows(allocator, source, values, &pp, &base, plan));
    pp.columns[7].values[0] = original_mult;
    try checkNonBitPrivateSelector();
}

fn checkNonBitPrivateSelector() !void {
    const allocator = std.testing.allocator;
    const initial = [4]M31{ M31.fromCanonical(1), M31.fromCanonical(2), M31.fromCanonical(3), M31.fromCanonical(4) };
    const constant = M31.fromCanonical(13);
    const final = try @import("repeated_step_chip.zig").direct(initial, constant, 16);
    // This is the direct S31 selector's producing gate. Both branches have
    // the same value, so even b = 2 can retain all eight honest public words.
    // The Boolean producer must reject it independently of output binding.
    for (0..2) |honest_bit| {
        var ctx = try circuit.builder.Context(QM31).init(allocator, 8);
        defer ctx.deinit();
        var plan: many.Plan = .{ .count = 1 };
        plan.calls[0] = .{
            .call_id = 0,
            .rounds = 16,
            .constant = constant,
            .input = undefined,
            .output = undefined,
        };
        var inputs: [4]circuit.builder.Var = undefined;
        var results: [4]circuit.builder.Var = undefined;
        for (0..4) |lane| {
            inputs[lane] = try ctx.guessM31(QM31.fromBase(initial[lane]));
            results[lane] = try ctx.guessM31(QM31.fromBase(final[lane]));
            plan.calls[0].output[lane] = results[lane].idx;
        }
        const bit = try ctx.newVar(QM31.fromBase(M31.fromCanonical(@intCast(honest_bit))));
        try ctx.mulInto(bit, bit, bit);
        const equal_branch_difference = try ctx.sub(inputs[0], inputs[0]);
        const selected = try ctx.add(inputs[0], try ctx.mul(bit, equal_branch_difference));
        plan.calls[0].input[0] = selected.idx;
        for (1..4) |lane| plan.calls[0].input[lane] = inputs[lane].idx;
        var outputs: [8]circuit.builder.Var = undefined;
        outputs[0] = selected;
        for (1..4) |lane| outputs[lane] = try ctx.add(inputs[lane], results[lane]);
        for (0..4) |lane| outputs[4 + lane] = try ctx.mul(inputs[lane], results[lane]);
        try ctx.setOutputs(&outputs);
        try ctx.finalize(false);
        try circuit.common.finalize.padToTargets(QM31, &ctx, .{
            .eq = 0,
            .qm31_ops = circuit.common.finalize.paddedSize(ctx.circuit.nQm31OpsRows()),
            .triple_xor = 0,
            .m31_to_u32 = 0,
            .blake_g_gate = 0,
        });
        const source = CircuitView.fromBuilder(&ctx.circuit);
        try std.testing.expectEqual(bit.idx, source.mul[0].in0);
        try std.testing.expectEqual(bit.idx, source.mul[0].in1);
        try std.testing.expectEqual(bit.idx, source.mul[0].out);
        var pp = try plan.preprocessed(allocator, source);
        defer pp.deinit(allocator);
        var honest_base = try direct_trace.writeBase(allocator, ctx.values(), &pp);
        defer honest_base.deinit();
        try std.testing.expectEqual(source.nQm31OpsRows(), try auditCircuitRows(allocator, source, ctx.values(), &pp, &honest_base, plan));

        const forged_values = try allocator.dupe(QM31, ctx.values());
        defer allocator.free(forged_values);
        forged_values[bit.idx] = QM31.fromBase(M31.fromCanonical(2));
        try std.testing.expectEqualDeep(ctx.values()[selected.idx], forged_values[selected.idx]);
        var forged_base = try direct_trace.writeBase(allocator, forged_values, &pp);
        defer forged_base.deinit();
        try std.testing.expectEqualSlices(QM31, honest_base.output_values, forged_base.output_values);
        try std.testing.expectError(error.InvalidMixedTraceAuditGate, auditCircuitRows(allocator, source, forged_values, &pp, &forged_base, plan));
    }
}
