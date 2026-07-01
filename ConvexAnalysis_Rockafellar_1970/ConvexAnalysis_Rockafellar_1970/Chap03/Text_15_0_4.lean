import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ENNReal NNReal Rockafellar

universe u

section

variable {E : Type u} [AddCommMonoid E] [Module ℝ E] [TopologicalSpace E]

local notation "γ" C => fun x : E ↦ (γ(x | C) : EReal)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.4 starts with a closed gauge `k` and its canonical unit sublevel set
  `gaugeUnitSublevel k`, then states that this set is the unique closed convex set containing `0`
  whose gauge is `k`.
- `core/canonical`: the function-side owner is the imported predicate `IsGauge`, while the
  canonical set-side gauge is mathlib's extended Minkowski functional `egauge ℝ≥0`.
- `bridge/view`: uniqueness is expressed by comparing an arbitrary closed convex set `C`
  containing `0` and satisfying the owner-level function equality `(γ C) = k` with the canonical
  unit sublevel set `gaugeUnitSublevel k`.

Domain-style sampling used here:
- `IsGauge`;
- `egauge ℝ≥0`;
- `LowerSemicontinuous`;
- `egauge_le_iff_mem_smul`;
- the imported gauge-recovery theorem `IsGauge.eq_egauge_unitSublevel`.

Primitive data vs derived API:
- primitive datum: the function `k : E → EReal`;
- derived object: the canonical unit sublevel set `gaugeUnitSublevel k`;
- derived proposition: the source closed/convex/origin/gauge conditions characterize that set.

Layer target: `bridge/view`, stated directly with the source conditions rather than a packaged
wrapper predicate.

Ambient-space refinement: the sampled gauge owners and lower-semicontinuity API already live on an
arbitrary real topological module, and the source statement uses no coordinate argument. The main
theorem therefore lives at that intrinsic layer rather than the concrete display model
`EuclideanSpace ℝ (Fin n)`.
-/

-- Proof sketch: for `→`, Corollary 9.7.1 identifies membership in a closed convex set `C`
-- containing `0` with the condition `egauge ℝ≥0 C x ≤ 1`; rewriting by the function equality
-- conjunct gives `x ∈ C ↔ x ∈ gaugeUnitSublevel k`. For `←`, lower semicontinuity makes
-- `gaugeUnitSublevel k` closed, Text 15.0.2 gives convexity and the gauge identity for that set,
-- and `k 0 = 0` puts the origin in `gaugeUnitSublevel k`.
/-- Text 15.0.4: if `k` is a closed gauge on `R^n`, then a set `C` is a closed convex set
containing `0` with gauge `γ(· | C) = k` exactly when `C` is the unit sublevel set
`gaugeUnitSublevel k`. -/
theorem isClosed_convex_zero_egauge_eq_iff_eq_unit_sublevel
    (k : E → EReal) [IsGauge k] (hk_closed : LowerSemicontinuous k) (C : Set E) :
    (IsClosed C ∧
      Convex ℝ C ∧
      (0 : E) ∈ C ∧
      (γ C) = k) ↔
        C = gaugeUnitSublevel k := sorry

end
