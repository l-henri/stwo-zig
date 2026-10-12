/-
**Gadget row = spec row, per group and per query.**

`groupQuery_sound` (gadget side) produces a triple-list batch term;
`friAnswers_ok` (spec side) produces `batchTerm` over a batch's
entries. This file ties them: a `GroupBinding` carries one group's
registers together with its spec batch, `Bound` pins the register
values to the batch data (exactly what `groupSetup_sound` plus the
response-register plumbing provide), and `deepRow_spec` concludes that
the row accumulator register holds the spec row's sum of batch terms.
-/
import StwoVerifier.DeepRow
import StwoVerifier.SpecRow

namespace StwoVerifier.Gadgets

open StwoVerifier StwoVerifier.Gates

instance : Inhabited Quotients.NumeratorData := ⟨⟨0, QM31.zero, QM31.zero⟩⟩
instance : Inhabited Quotients.SampleBatch := ⟨⟨CPoint.zero, []⟩⟩

/-- `getD` through a `map`, inside the length. -/
theorem getD_map {α β : Type} [Inhabited α] (f : α → β) (dflt : β)
    (l : List α) (i : ℕ) (hi : i < l.length) :
    (l.map f).getD i dflt = f (l.getD i default) := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  rfl

/-- One group's registers with its spec batch. -/
structure GroupBinding where
  g : GroupRegs
  valRegs : List ℕ
  rsReg : List (ℕ × ℕ)
  batch : Quotients.SampleBatch

instance : Inhabited GroupBinding := ⟨⟨default, [], [], default⟩⟩

/-- The register values are the batch's data: the `groupSetup_sound`
facts for the batch's point, the response registers carrying
`−2u`-scaled random coefficients and the sampled values, and the
query-value registers carrying the queried column values at `row`. -/
structure Bound (ρ : ℕ → QM31) (flatCols : List (List F)) (row : ℕ)
    (gb : GroupBinding) : Prop where
  hd : ρ gb.g.d = Deep.imQ gb.batch.point.y
  he : ρ gb.g.e = Deep.imQ gb.batch.point.x
  hf : ρ gb.g.f = Deep.imQ gb.batch.point.y * gb.batch.point.x
    - Deep.imQ gb.batch.point.x * gb.batch.point.y
  hclen : gb.g.coeffs.length = gb.rsReg.length
  hcoeff : ∀ i, i < gb.rsReg.length →
    ρ (gb.g.coeffs.getD i 0)
      = Deep.imQ gb.batch.point.y * ρ (gb.rsReg.getD i (0, 0)).1
  haSum : ρ gb.g.aSum = (gb.rsReg.map fun (a, v) => ρ a * Deep.imQ (ρ v)).sum
  hb : ρ gb.g.b
    = Deep.imQ gb.batch.point.y * (gb.rsReg.map fun (a, v) => ρ a * ρ v).sum
      - (gb.rsReg.map fun (a, v) => ρ a * Deep.imQ (ρ v)).sum * gb.batch.point.y
  hlenV : gb.valRegs.length = gb.rsReg.length
  hlenE : gb.rsReg.length = gb.batch.entries.length
  halpha : ∀ i, i < gb.rsReg.length →
    ρ (gb.rsReg.getD i (0, 0)).1
      = (-2 : QM31) * Deep.uu * (gb.batch.entries.getD i default).randomCoeff
  hV : ∀ i, i < gb.rsReg.length →
    ρ (gb.rsReg.getD i (0, 0)).2 = (gb.batch.entries.getD i default).sampleValue
  hvals : ∀ i, i < gb.rsReg.length →
    ρ (gb.valRegs.getD i 0)
      = QM31.fromBase ((flatCols.getD
          (gb.batch.entries.getD i default).columnIndex []).getD row 0)

set_option maxHeartbeats 800000 in
/-- **One group's quotient register holds the spec's `batchTerm`.** -/
theorem groupQuery_spec {ρ : ℕ → QM31} {qx qy m : ℕ}
    {flatCols : List (List F)} {row : ℕ} {xq yq : F}
    (gb : GroupBinding)
    (hB : Bound ρ flatCols row gb)
    (hqx : ρ qx = QM31.fromBase xq) (hqy : ρ qy = QM31.fromBase yq)
    (hden : Quotients.denominator gb.batch.point ⟨xq, yq⟩ ≠ 0)
    (h : AllHold ρ (groupQuery gb.g gb.valRegs qx qy m).ops) :
    ρ (groupQuery gb.g gb.valRegs qx qy m).res
      = Quotients.batchTerm gb.batch flatCols row ⟨xq, yq⟩ := by
  have hmain := groupQuery_sound (P := gb.batch.point) (xq := xq) (yq := yq)
    (rsAlpha := gb.batch.entries.map Quotients.NumeratorData.randomCoeff)
    (vals := gb.batch.entries.map fun e =>
      (flatCols.getD e.columnIndex []).getD row 0)
    hB.hd hB.he hB.hf hB.hclen hB.hcoeff hB.haSum hB.hb hqx hqy hB.hlenV
    (fun i hi => by
      rw [getD_map Quotients.NumeratorData.randomCoeff 0 gb.batch.entries i
        (hB.hlenE ▸ hi)]
      exact hB.halpha i hi)
    (fun i hi => by
      rw [getD_map (fun e => (flatCols.getD e.columnIndex []).getD row 0) 0
        gb.batch.entries i (hB.hlenE ▸ hi)]
      exact hB.hvals i hi)
    h hden
  rw [hmain]
  unfold Quotients.batchTerm
  refine congrArg (fun s => QM31.mulCM31 s _) ?_
  rw [hB.hlenE]
  rw [map_sum_eq_range gb.batch.entries]
  rw [List.map_map]
  refine congrArg List.sum ?_
  refine List.map_congr_left fun i hi' => ?_
  have hiR : i < gb.batch.entries.length := List.mem_range.mp hi'
  have hiL : i < gb.rsReg.length := by rw [hB.hlenE]; exact hiR
  simp only [Function.comp_def]
  rw [getD_map Quotients.NumeratorData.randomCoeff 0 gb.batch.entries i hiR,
    getD_map (fun e => (flatCols.getD e.columnIndex []).getD row 0) 0
      gb.batch.entries i hiR,
    hB.hV i hiL]

/-- **The row register holds the spec row's sum of batch terms** — the
per-query composition of `groupQuery_spec` over all groups, matching
`friAnswers_ok`'s per-row value. -/
theorem deepRow_spec {ρ : ℕ → QM31} {qx qy : ℕ}
    {flatCols : List (List F)} {row : ℕ} {xq yq : F}
    (bindings : List GroupBinding) (acc n : ℕ)
    (hB : ∀ gb ∈ bindings, Bound ρ flatCols row gb)
    (hqx : ρ qx = QM31.fromBase xq) (hqy : ρ qy = QM31.fromBase yq)
    (hden : ∀ gb ∈ bindings,
      Quotients.denominator gb.batch.point ⟨xq, yq⟩ ≠ 0)
    (h : AllHold ρ (deepRow qx qy
      (bindings.map fun gb => (gb.g, gb.valRegs)) acc n).ops) :
    ρ (deepRow qx qy (bindings.map fun gb => (gb.g, gb.valRegs)) acc n).res
      = ρ acc + (bindings.map fun gb =>
          Quotients.batchTerm gb.batch flatCols row ⟨xq, yq⟩).sum := by
  refine deepRow_sound (bindings.map fun gb => (gb.g, gb.valRegs))
    (bindings.map fun gb => Quotients.batchTerm gb.batch flatCols row ⟨xq, yq⟩)
    acc n (by simp) ?_ h
  intro i hi m hm
  rw [List.length_map] at hi
  have h1 : ((bindings.map fun gb => (gb.g, gb.valRegs)).getD i default)
      = ((bindings.getD i default).g, (bindings.getD i default).valRegs) :=
    getD_map _ _ _ i hi
  have h2 : ((bindings.map fun gb =>
        Quotients.batchTerm gb.batch flatCols row ⟨xq, yq⟩).getD i 0)
      = Quotients.batchTerm (bindings.getD i default).batch flatCols row
          ⟨xq, yq⟩ :=
    getD_map _ _ _ i hi
  have hgetD : bindings.getD i default = bindings[i] := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    rfl
  have hmem : bindings.getD i default ∈ bindings := by
    rw [hgetD]
    exact List.getElem_mem hi
  rw [h1] at hm
  rw [h1, h2]
  exact groupQuery_spec (bindings.getD i default) (hB _ hmem) hqx hqy
    (hden _ hmem) hm

end StwoVerifier.Gadgets
