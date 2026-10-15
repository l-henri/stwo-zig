const std = @import("std");
const semantic_authority = @import("stwo_cairo_frontend").proof_plan.semantic_authority;
const composition = @import("stwo_cairo_frontend").witness.composition_bundle;
const fixed_tables = @import("stwo_cairo_frontend").witness.fixed_table_bundle;
const topology = @import("topology.zig");

test "SN2 eval topology preserves every heterogeneous component domain" {
    const allocator = std.testing.allocator;
    var bundle = try composition.Bundle.readFile(
        allocator,
        "vectors/cairo/sn_pie_2_composition.bin",
    );
    defer bundle.deinit();
    var fixed = try fixed_tables.Bundle.readFile(
        allocator,
        "vectors/cairo/cairo_fixed_tables.bin",
    );
    defer fixed.deinit();
    const preprocessed_logs = try semantic_authority.preprocessedLogs(
        allocator,
        fixed,
    );
    defer allocator.free(preprocessed_logs);

    var first = try topology.Topology.derive(
        allocator,
        bundle,
        preprocessed_logs,
    );
    defer first.deinit();
    var second = try topology.Topology.derive(
        allocator,
        bundle,
        preprocessed_logs,
    );
    defer second.deinit();

    try std.testing.expectEqual(
        @as(u32, topology.expected_component_count),
        first.summary.component_count,
    );
    try std.testing.expectEqual(
        @as(u32, topology.expected_placement_count),
        first.summary.placement_count,
    );
    try std.testing.expectEqual(
        @as(u64, topology.expected_constraint_count),
        first.summary.constraint_count,
    );
    try std.testing.expect(first.accumulators.len > 1);
    try std.testing.expect(
        first.summary.accumulator_words >
            (@as(u64, 4) << @intCast(bundle.max_evaluation_log_size)),
    );
    try std.testing.expect(first.summary.lde_tile_words > 0);
    try std.testing.expectEqual(
        @as(u64, 37_356),
        first.summary.extended_parameter_words,
    );
    try std.testing.expectEqual(
        @as(u64, 74_712),
        first.summary.extended_parameter_descriptor_words,
    );
    try std.testing.expectEqual(
        @as(usize, 9_339),
        first.extended_parameter_descriptors.len,
    );
    try std.testing.expectEqualSlices(
        u8,
        &first.identity,
        &second.identity,
    );

    var accounted_sources: u64 = 0;
    var accounted_placements: u64 = 0;
    for (first.components) |component| {
        accounted_sources += component.source_count;
        accounted_placements += component.placement_count;
        const rows = @as(u64, 1) <<
            @intCast(component.evaluation_log_size);
        try std.testing.expect(
            @as(u64, component.source_count) * rows <=
                first.summary.lde_tile_words,
        );
    }
    try std.testing.expectEqual(
        @as(u64, first.sources.len),
        accounted_sources,
    );
    try std.testing.expectEqual(
        @as(u64, first.placements.len),
        accounted_placements,
    );

    preprocessed_logs[0] += 1;
    var mutated = try topology.Topology.derive(
        allocator,
        bundle,
        preprocessed_logs,
    );
    defer mutated.deinit();
    try std.testing.expect(!std.mem.eql(
        u8,
        &first.identity,
        &mutated.identity,
    ));
}

test "canonical eval reuses only identical commitment domains" {
    const allocator = std.testing.allocator;
    var bundle = try composition.Bundle.readFile(allocator, "vectors/cairo/sn_pie_2_composition.bin");
    defer bundle.deinit();
    var fixed = try fixed_tables.Bundle.readFile(allocator, "vectors/cairo/cairo_fixed_tables.bin");
    defer fixed.deinit();
    const logs = try semantic_authority.preprocessedLogs(allocator, fixed);
    defer allocator.free(logs);
    var dense = try topology.Topology.derive(allocator, bundle, logs);
    defer dense.deinit();
    var compact = try topology.Topology.deriveCanonical(allocator, bundle, logs);
    defer compact.deinit();
    const geometry = try @import("../resident_plan_ingress.zig").deriveEvaluationMode(bundle, [_]u8{1} ** 32, true);
    try std.testing.expectEqual(geometry.lde_tile_words, compact.summary.lde_tile_words);
    try std.testing.expectEqual(dense.sources.len, compact.sources.len);
    try std.testing.expectEqual(@as(u64, compact.sources.len) * 2, compact.summary.trace_offset_words);
    try std.testing.expectEqual(@as(u64, dense.sources.len), dense.summary.trace_offset_words);
    try std.testing.expect(compact.summary.lde_tile_words < dense.summary.lde_tile_words);
    var reused: usize = 0;
    var transformed: usize = 0;
    for (compact.components) |component| {
        var active: usize = 0;
        for (compact.sources[component.first_source..][0..component.source_count]) |source| {
            if (source.reuse_committed_lde) {
                try std.testing.expect(source.role != .preprocessed);
                try std.testing.expectEqual(component.evaluation_log_size, source.log_rows + 1);
                reused += 1;
            } else {
                try std.testing.expectEqual(@as(u64, active) << @intCast(component.evaluation_log_size), source.tile_offset);
                active += 1;
                transformed += 1;
            }
        }
        try std.testing.expectEqual(active, component.recompute_source_count);
    }
    try std.testing.expect(reused > 0 and transformed > 0);
    // A larger AIR domain must extend coefficients rather than repeating the
    // committed evaluations. Exercise that boundary on a real component.
    const original = bundle.components[0].evaluation_log_size;
    bundle.components[0].evaluation_log_size = bundle.components[0].trace_log_size + 2;
    defer bundle.components[0].evaluation_log_size = original;
    var larger = try topology.Topology.deriveCanonical(allocator, bundle, logs);
    defer larger.deinit();
    const first = larger.components[0];
    try std.testing.expectEqual(first.source_count, first.recompute_source_count);
    for (larger.sources[first.first_source..][0..first.source_count]) |source| try std.testing.expect(!source.reuse_committed_lde);
}

test "eval topology admits a component without interaction columns" {
    const allocator = std.testing.allocator;
    var bundle = try composition.Bundle.readFile(
        allocator,
        "vectors/cairo/sn_pie_2_composition.bin",
    );
    defer bundle.deinit();
    var fixed = try fixed_tables.Bundle.readFile(
        allocator,
        "vectors/cairo/cairo_fixed_tables.bin",
    );
    defer fixed.deinit();
    const preprocessed_logs = try semantic_authority.preprocessedLogs(
        allocator,
        fixed,
    );
    defer allocator.free(preprocessed_logs);

    var reference = try topology.Topology.derive(allocator, bundle, preprocessed_logs);
    defer reference.deinit();
    const removed = reference.components[0].interaction_count;
    try std.testing.expect(removed > 0);

    // An empty tree-2 span and an absent one describe the same lookup-free
    // component.
    const spans = bundle.components[0].trace_spans;
    var interaction_index: ?usize = null;
    for (spans, 0..) |span, index| {
        if (span.tree == 2) interaction_index = index;
    }
    const saved = spans[interaction_index.?];
    defer spans[interaction_index.?] = saved;
    spans[interaction_index.?].start = saved.end;
    var empty = try topology.Topology.derive(allocator, bundle, preprocessed_logs);
    defer empty.deinit();

    var kept: [64]composition.TraceSpan = undefined;
    var kept_len: usize = 0;
    for (spans) |span| {
        if (span.tree == 2) continue;
        kept[kept_len] = span;
        kept_len += 1;
    }
    bundle.components[0].trace_spans = kept[0..kept_len];
    defer bundle.components[0].trace_spans = spans;
    var absent = try topology.Topology.derive(allocator, bundle, preprocessed_logs);
    defer absent.deinit();

    for ([_]*const topology.Topology{ &empty, &absent }) |derived| {
        const component = derived.components[0];
        try std.testing.expectEqual(@as(u32, 0), component.interaction_count);
        try std.testing.expectEqual(
            reference.components[0].source_count - removed,
            component.source_count,
        );
        try std.testing.expectEqual(
            reference.sources.len - removed,
            derived.sources.len,
        );
        for (derived.sources[component.first_source..][0..component.source_count]) |source|
            try std.testing.expect(source.role != .interaction);
        try std.testing.expectEqual(
            reference.summary.interaction_offset_words,
            derived.summary.interaction_offset_words,
        );
        try std.testing.expect(!std.mem.eql(u8, &reference.identity, &derived.identity));
    }
}
