import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.MetricSpace.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_15_0_1 (from Chap03) -/
noncomputable section

universe u v

open scoped Pointwise

attribute [local instance] WithBotTop.instSMul

local instance instDecidableLT (α : Type*) [LT α] : DecidableLT α :=
  Classical.decRel (fun a b => a < b)

section

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.1 defines a gauge by four function-side conditions and then gives the
  equivalent epigraph-cone reformulation. The owner is stated at the scalar-generic
  additive-`SMul` layer.
- `core/canonical`: the existing owner predicates are the chapter convexity predicate
  `Function.IsConvex` for `WithTopBot 𝕜`-valued functions, the chapter
  positive-homogeneity predicate
  `Function.PositivelyHomogeneous`, the chapter source-facing cone owner
  `Set.IsConvexCone 𝕜 (epi k)`, the generated-cone owner `cone[𝕜] (epi k)`,
  and `Function.sublinearHull`.
- `bridge/view`: the canonical chapter reformulation is the fixed-point equation
  `k = sublinearHull k`, while the raw pointed-hull spelling
  `epi k = PointedCone.hull 𝕜 (epi k)` is only a bridge presentation of the owner-level
  epigraph-cone equality `epi k = cone[𝕜] (epi k)`.

Domain-style sampling used here:
- `Function.PositivelyHomogeneous`;
- `Function.IsConvex`;
- `Set.IsConvexCone`;
- `Function.sublinearHull`;
- `PointedCone.hull`;
- `Function.isCone_epi_of_positivelyHomogeneous`.

Primitive data vs derived API:
- primitive datum: the function `k : E → WithTopBot 𝕜`;
- core property: being a gauge;
- derived bridges: the fixed-point condition for the canonical owner `sublinearHull`, and
  the equivalent epigraph-cone characterizations.

Layer target: `source-facing` for the main class, with `bridge/view` companion theorems centered
first on the canonical owner `sublinearHull`, then on the source-facing epigraph cone owner
`Set.IsConvexCone 𝕜 (epi k)`, and only finally on the pointed-hull bridge view.
-/

/-- Text 15.0.1: a gauge is a `WithTopBot 𝕜`-valued function that is convex, nonnegative,
positively homogeneous of degree `1`, and vanishes at the origin. -/
class IsGauge (k : E → WithTopBot 𝕜) : Prop where
  convex : Function.IsConvex 𝕜 k
  nonneg : ∀ x : E, 0 ≤ k x
  homogeneous : Function.PositivelyHomogeneous 𝕜 k
  map_zero : k 0 = 0

attribute [simp] IsGauge.map_zero

namespace IsGauge

/-- Bridge form: a gauge has nonpositive value at the origin. -/
theorem map_zero_le (k : E → WithTopBot 𝕜) [hk : IsGauge k] :
    k 0 ≤ 0 := by
  exact hk.map_zero.le

end IsGauge

/-- The zero function is a canonical gauge. -/
instance : IsGauge (fun _ : E ↦ (0 : WithTopBot 𝕜)) where
  convex := Function.isConvex_zero
  nonneg _ := by simp
  homogeneous := by
    intro c x
    simp
  map_zero := by simp

end

section

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommMonoid E] [SMul 𝕜 E]

open PointedCone

namespace IsGauge

/-- The origin belongs to the scalar epigraph of a gauge. -/
theorem zero_mem_epi (k : E → WithTopBot 𝕜) [hk : IsGauge k] :
    (0 : E × 𝕜) ∈ epi k := by
  exact mem_epi_restrict_iff.mpr
    ⟨by simp, hk.map_zero_le⟩

-- Proof sketch: positive homogeneity gives the cone part of the epigraph condition, and convexity
-- gives the convexity part. This packages the source epigraph clause through the chapter owner
-- `Set.IsConvexCone`.
/-- The scalar epigraph of a gauge is a convex cone. -/
theorem epi_isConvexCone [PosSMulMono 𝕜 𝕜]
    [Module 𝕜 E] (k : E → WithTopBot 𝕜) [hk : IsGauge k] :
    Set.IsConvexCone 𝕜 (epi k) := by
  refine ⟨Function.isCone_epi_of_positivelyHomogeneous hk.homogeneous, ?_⟩
  simpa [epi_univ_eq_setOf_le] using hk.convex.convex_epigraph

-- Proof sketch: every point `(x, μ)` in the scalar epigraph satisfies `k x ≤ μ`, and a gauge is
-- pointwise nonnegative, so the height `μ` is nonnegative as well.
/-- Every point in the scalar epigraph of a gauge has nonnegative height. -/
theorem epi_subset_nonnegativeHeights (k : E → WithTopBot 𝕜) [hk : IsGauge k] :
    epi k ⊆ {p : E × 𝕜 | 0 ≤ p.2} := by
  intro p hp
  rcases mem_epi_restrict_iff.mp hp with ⟨-, hp⟩
  have hp_nonneg : (0 : WithTopBot 𝕜) ≤ (p.2 : WithTopBot 𝕜) := le_trans (hk.nonneg p.1) hp
  simpa using hp_nonneg

end IsGauge

end

section

variable {𝕜 : Type v} [Semifield 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable [PosMulReflectLT 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]

open PointedCone

namespace IsGauge

-- Proof sketch: apply the exact hull theorem
-- `PointedCone.cone_eq_insert_zero_positiveRay_of_convex` to the convex epigraph, then read the
-- result at the canonical owner `cone[𝕜] (epi k)`. The inclusion into the positive ray
-- uses the scalar `1`, while the reverse inclusion uses `k 0 = 0` for the distinguished origin
-- and positive homogeneity for the positive ray.
/-- The scalar epigraph of a gauge is exactly its generated epigraph cone. -/
theorem epi_eq_cone_epi
    (k : E → WithTopBot 𝕜) [hk : IsGauge k] :
    epi k = (cone[𝕜] (epi k) : Set (E × 𝕜)) := by
  have hcone :
      ((cone[𝕜] (epi k) : PointedCone 𝕜 (E × 𝕜)) : Set (E × 𝕜)) =
        insert 0 (Set.Ioi (0 : 𝕜) • epi k) := by
    simpa using
      (PointedCone.cone_eq_insert_zero_positiveRay_of_convex (epi k) hk.convex.convex_epi)
  rw [hcone]
  refine Set.Subset.antisymm ?_ ?_
  · intro p hp
    right
    exact Set.mem_smul.mpr ⟨1, by simp, p, hp, by simp⟩
  · rintro p (rfl | hp)
    · exact IsGauge.zero_mem_epi k
    · rcases Set.mem_smul.mp hp with ⟨a, ha, q, hq, rfl⟩
      exact (Function.isCone_epi_of_positivelyHomogeneous hk.homogeneous).smul_mem ha hq

end IsGauge

end

section

variable {𝕜 : Type v} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]

open PointedCone

namespace IsGauge

-- Proof sketch: `sublinearHull k` is the greatest positively homogeneous convex minorant of
-- `k` with nonpositive value at the origin. A gauge already has those properties, so maximality
-- gives `k ≤ sublinearHull k`; the opposite inequality is the owner minorant theorem
-- `Function.sublinearHull_le`.
/-- A gauge is fixed by the canonical positively homogeneous convex minorant owner
`sublinearHull`. -/
theorem eq_sublinearHull (k : E → WithTopBot 𝕜) [hk : IsGauge k] :
    k = Function.sublinearHull k := by
  apply le_antisymm
  · exact Function.le_sublinearHull_of_le
      hk.homogeneous hk.convex (IsGauge.map_zero_le k) le_rfl
  · exact Function.sublinearHull_le k

end IsGauge

-- Proof sketch: if `k` is a gauge, the owner theorem `sublinearHull_le` gives one
-- inequality, while the maximal-minorant owner theorem
-- `le_sublinearHull_of_le` supplies the converse from convexity, positive homogeneity, and
-- `k 0 = 0`. Conversely, any fixed point of `sublinearHull` inherits convexity and positive
-- homogeneity from the owner construction, and pointwise nonnegativity together with
-- `sublinearHull_apply_zero_le` forces the zero value at the origin.
/-- A gauge is equivalently a nonnegative fixed point of the canonical epigraph-cone infimum owner
`sublinearHull`. -/
theorem isGauge_iff_eq_sublinearHull_and_nonneg
    (k : E → WithTopBot 𝕜) :
    IsGauge k ↔
      k = Function.sublinearHull k ∧
      ∀ x : E, 0 ≤ k x := by
  constructor
  · intro hk
    letI : IsGauge k := hk
    exact ⟨IsGauge.eq_sublinearHull k, hk.nonneg⟩
  · rintro ⟨hk_fixed, hk_nonneg⟩
    refine ⟨?_, hk_nonneg, ?_, ?_⟩
    · rw [hk_fixed]
      simpa using Function.isConvex_sublinearHull k
    · rw [hk_fixed]
      simpa using Function.positivelyHomogeneous_sublinearHull k
    · rw [hk_fixed]
      have hzero_nonneg : (0 : WithTopBot 𝕜) ≤ Function.sublinearHull k 0 := by
        rw [← hk_fixed]
        exact hk_nonneg 0
      exact le_antisymm (Function.sublinearHull_apply_zero_le k) hzero_nonneg

-- Proof sketch: if `k` is a gauge, the previous theorem identifies `epi k` with its generated
-- cone directly from convexity, positive homogeneity, and `k 0 = 0`. Pointwise nonnegativity then
-- says every point of `epi k` has nonnegative height. Conversely, the exact hull theorem
-- `PointedCone.cone_eq_insert_zero_positiveRay_of_convex` reconstructs the owner-level
-- epigraph-cone equality from convexity, origin membership, and the cone law. That equality
-- identifies `k` with `sublinearHull k`, while the height condition recovers pointwise
-- nonnegativity.
/-- A gauge is equivalently a function whose scalar epigraph is a convex cone containing the origin
and no point with negative height. -/
theorem isGauge_iff_epi_isConvexCone_zero_mem_and_nonnegative_heights
    (k : E → WithTopBot 𝕜) :
    IsGauge k ↔
      Set.IsConvexCone 𝕜 (epi k) ∧
      (0 : E × 𝕜) ∈ epi k ∧
      epi k ⊆ {p : E × 𝕜 | 0 ≤ p.2} := by
  constructor
  · intro hk
    letI : IsGauge k := hk
    exact ⟨IsGauge.epi_isConvexCone k, IsGauge.zero_mem_epi k,
      IsGauge.epi_subset_nonnegativeHeights k⟩
  · rintro ⟨hk_epiCone, hk_zero, hk_heights⟩
    have hk_epi : epi k = (cone[𝕜] (epi k) : Set (E × 𝕜)) := by
      rw [PointedCone.cone_eq_insert_zero_positiveRay_of_convex (epi k) hk_epiCone.convex]
      refine Set.Subset.antisymm ?_ ?_
      · intro p hp
        right
        exact Set.mem_smul.mpr ⟨1, by simp, p, hp, by simp⟩
      · rintro p (rfl | hp)
        · exact hk_zero
        · rcases Set.mem_smul.mp hp with ⟨a, ha, q, hq, rfl⟩
          exact hk_epiCone.isCone.smul_mem ha hq
    have hk_fixed : k = Function.sublinearHull k := by
      have hvi : Function.verticalInfimum (cone[𝕜] (epi k)) = k := by
        rw [← hk_epi]
        exact Function.verticalInfimum_epi k
      simpa [Function.sublinearHull] using hvi.symm
    have hk_nonneg : ∀ x : E, 0 ≤ k x := by
      intro x
      have hx_nonneg : 0 ≤ Function.sublinearHull k x := by
        rw [Function.sublinearHull_eq_sInf_verticalHeights]
        refine le_sInf fun a ha ↦ ?_
        have ha' :
            a ∈
              (((↑) : 𝕜 → WithTopBot 𝕜) ''
                {μ : 𝕜 | (x, μ) ∈ (cone[𝕜] (epi k) : Set (E × 𝕜))}) := by
          simpa [Function.verticalHeights, Function.verticalSection] using ha
        rcases ha' with ⟨μ, hμ, rfl⟩
        have hμ_cone : (x, μ) ∈ (cone[𝕜] (epi k) : Set (E × 𝕜)) := by
          simpa using hμ
        have hμ_epi : (x, μ) ∈ epi k := by rwa [← hk_epi] at hμ_cone
        have hμ_nonneg : 0 ≤ μ := hk_heights hμ_epi
        simpa using hμ_nonneg
      rw [hk_fixed]
      exact hx_nonneg
    exact (isGauge_iff_eq_sublinearHull_and_nonneg k).2 ⟨hk_fixed, hk_nonneg⟩

-- Proof sketch: the generated epigraph cone owner already supplies the cone law, convexity, and
-- origin membership, so the converse direction can pass directly through
-- `cone[𝕜] (epi k)` without re-exposing the raw pointed-hull spelling.
/-- Bridge reformulation: the gauge condition can also be stated as equality between the scalar
epigraph and the canonical generated epigraph cone, together with absence of negative heights. -/
theorem isGauge_iff_epi_eq_cone_epi_and_nonnegative_heights
    (k : E → WithTopBot 𝕜) :
    IsGauge k ↔
      epi k = (cone[𝕜] (epi k) : Set (E × 𝕜)) ∧
      epi k ⊆ {p : E × 𝕜 | 0 ≤ p.2} := by
  constructor
  · intro hk
    letI : IsGauge k := hk
    exact ⟨IsGauge.epi_eq_cone_epi k, IsGauge.epi_subset_nonnegativeHeights k⟩
  · rintro ⟨hk_epi, hk_heights⟩
    have hk_zero : (0 : E × 𝕜) ∈ epi k := by
      have hzero_cone : (0 : E × 𝕜) ∈ (cone[𝕜] (epi k) : Set (E × 𝕜)) :=
        (cone[𝕜] (epi k)).zero_mem
      exact hk_epi.symm ▸ hzero_cone
    exact (isGauge_iff_epi_isConvexCone_zero_mem_and_nonnegative_heights k).2
      ⟨⟨by
          intro a p ha hp
          rw [hk_epi] at hp ⊢
          exact (cone[𝕜] (epi k)).smul_mem ha.le hp,
        by
          rw [hk_epi]
          exact (cone[𝕜] (epi k)).convex⟩,
        hk_zero, hk_heights⟩

end

/-! ### Text_15_0_2 (from Chap03) -/
noncomputable section

open scoped ENNReal NNReal Rockafellar

universe u v

section GaugeUnitSublevel

variable {𝕜 : Type v} [Semiring 𝕜] [PartialOrder 𝕜] [IsOrderedRing 𝕜]
variable {E : Type u} [AddCommMonoid E] [Module 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.2 says that every gauge on `R^n` is the gauge of some nonempty convex
  set. The reusable owner-level unit-sublevel API is scalar-generic at the `IsGauge` layer, while
  the bridge to `egauge ℝ≥0` stays on real modules; specializing to `R^n` recovers the source
  statement.
- `core/canonical`: the existing source-facing owner for the function-side notion is the imported
  declaration `IsGauge` from Text 15.0.1,
  while the canonical set-side gauge owner is mathlib's extended Minkowski functional
  `egauge ℝ≥0`, rendered in the chapter notation as `γ(· | ·)`.
- `bridge/view`: the textbook proof chooses the unit sublevel set `gaugeUnitSublevel k`, so the
  representation is most naturally stated by identifying a gauge with the extended gauge of the
  canonical preimage `k ⁻¹' Set.Iic 1`, kept under the short chapter name
  `gaugeUnitSublevel k`.

Domain-style sampling used here:
- `IsGauge`;
- `egauge`;
- `egauge_eq_sInf_nonneg_dilates`;
- the chapter/project sublevel-set style `f ⁻¹' Set.Iic a`, as in `Set.polar` and
  `supportFunction C ⁻¹' Set.Iic 1`.

Primitive data vs derived API:
- primitive datum: a gauge `k : E → WithBotTop 𝕜`;
- derived object: its canonical unit sublevel set `gaugeUnitSublevel k`, implemented as the
  high-reuse abbreviation of the owner expression `k ⁻¹' Set.Iic 1`;
- derived fact: in the real specialization, `k` is recovered from this set through `egauge ℝ≥0`.

Layer target: `bridge/view`, stated directly in terms of the canonical owner `egauge ℝ≥0` rather
than introducing a parallel local gauge wrapper.
-/

/-- The canonical unit sublevel set attached to a gauge `k`. -/
abbrev gaugeUnitSublevel (k : E → WithBotTop 𝕜) : Set E :=
  k ⁻¹' Set.Iic (1 : WithBotTop 𝕜)

namespace IsGauge

-- Proof sketch: a gauge vanishes at the origin, and `0 ≤ 1` in the ordered scalar.
/-- The canonical unit sublevel set of a gauge contains the origin. -/
theorem zero_mem_unitSublevel (k : E → WithBotTop 𝕜) [hk : IsGauge k] :
    (0 : E) ∈ gaugeUnitSublevel k := by
  change k 0 ≤ (1 : WithBotTop 𝕜)
  rw [hk.map_zero]
  exact WithBotTop.coe_le_coe.mpr (zero_le_one : (0 : 𝕜) ≤ 1)

/-- The canonical unit sublevel set of a gauge is nonempty. -/
theorem unitSublevel_nonempty (k : E → WithBotTop 𝕜) [IsGauge k] :
    (gaugeUnitSublevel k).Nonempty :=
  ⟨0, zero_mem_unitSublevel k⟩

section OrderedCodomain

variable [NoBotOrder 𝕜]

-- Proof sketch: `gaugeUnitSublevel k` is the closed sublevel set `{x | k x ≤ 1}` of the convex
-- owner `k`, so convexity is exactly the owner theorem `Function.IsConvex.convex_le`.
/-- The canonical unit sublevel set of a gauge is convex. -/
theorem convex_unitSublevel (k : E → WithBotTop 𝕜) [hk : IsGauge k] :
    Convex 𝕜 (gaugeUnitSublevel k) := by
  simpa [gaugeUnitSublevel] using hk.convex.convex_le (1 : WithBotTop 𝕜)

end OrderedCodomain

end IsGauge

end GaugeUnitSublevel

section RealEgaugeBridge

variable {E : Type u} [AddCommMonoid E] [Module ℝ E]

local notation "γ" C => fun x : E ↦ (γ(x | C) : EReal)

namespace IsGauge

-- Proof sketch: let `C = gaugeUnitSublevel k`. Positive homogeneity gives
-- `x ∈ μ • C ↔ k x ≤ μ` for `μ ≥ 0`, so the defining infimum formula for `egauge ℝ≥0 C x`
-- collapses to the infimum of the upper ray `{μ | k x ≤ μ}`, which is exactly `k x`.
/-- Text 15.0.2: every gauge is the gauge of its unit sublevel set `gaugeUnitSublevel k`.
Since `gaugeUnitSublevel k` is the canonical unit sublevel set `{x | k x ≤ 1}`, this realizes
every gauge as the gauge of a nonempty convex set. Specializing `E` to
`EuclideanSpace ℝ (Fin n)` recovers the source statement. -/
theorem eq_egauge_unitSublevel (k : E → EReal) [IsGauge k] :
    k = γ (gaugeUnitSublevel k) := sorry

end IsGauge

end RealEgaugeBridge

/-! ### Text_15_0_3 (from Chap03) -/
/- Source/core/bridge triage:
- `source-facing`: Text 15.0.3 restates the gauge-recovery formula for the unit sublevel set
  `C = {x | k x ≤ 1}` attached to a gauge `k`.
- `core/canonical`: the ambient owner abstractions are the gauge class `IsGauge` from
  Text 15.0.1 and the canonical set gauge `egauge ℝ≥0`; the exact theorem-level owner is the
  imported `IsGauge.eq_egauge_unitSublevel`.
- `bridge/view`: no new bridge is needed here; the source statement has the exact interface of the
  imported owner theorem, so introducing a local theorem shell would only duplicate upstream API.

Domain-style sampling used here:
- `IsGauge`;
- `egauge`;
- `egauge_eq_sInf_nonneg_dilates`;
- `IsGauge.eq_egauge_unitSublevel`.

Primitive data vs derived API:
- there is no new primitive datum beyond the gauge `k`;
- the displayed equality is already the canonical theorem-level API from Text 15.0.2.

Layer target: `core/canonical` direct reuse. This item adds no new mathematical content beyond the
exact upstream theorem, so the refined file should reuse that theorem verbatim rather than keep a
parallel local declaration.
-/

/- Text 15.0.3: if `k` is a gauge on `R^n` and `C = {x | k x ≤ 1}`, then the gauge
`γ(· | C)`, formalized as `egauge ℝ≥0 C` and coerced to `EReal`, agrees with `k` as a function.
This is exactly the preceding owner theorem `IsGauge.eq_egauge_unitSublevel`, so this item is a
direct canonical recall rather than a parallel local theorem shell. -/
recall IsGauge.eq_egauge_unitSublevel

/-! ### Text_15_0_4 (from Chap03) -/
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

/-! ### Text_15_0_5 (from Chap03) -/
noncomputable section

open Function
  (verticalInfimum verticalInfimum_eq_sInf verticalInfimum_le_of_mem
    le_verticalInfimum_of_subset_epi)
open scoped Rockafellar

universe u v w

section

variable {𝕜 : Type w} [ConditionallyCompleteLinearOrder 𝕜] [Zero 𝕜] [Mul 𝕜]
variable {X : Type u} {Y : Type v} [HasPairing X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.5 defines the polar of a gauge by taking the infimum of the
  nonnegative scalars `μ⋆` such that `⟪x, x⋆⟫ₚ ≤ μ⋆ k x` for every `x`.
- `core/canonical`: the public owner remains the source-facing function `gauge_polar`, but its
  implementation should reuse the Chapter 1 infimum owner `Function.verticalInfimum` applied to the
  admissible-majorant set rather than duplicating that fiber-infimum construction locally.
- `bridge/view`: the textbook `sInf` formula over nonnegative scalars is kept as a companion
  specification theorem, not as a second public owner.

Domain-style sampling used here:
- `IsGauge` from `Text_15_0_1`, identifying the owner class of functions to which the source gives
  this construction;
- `Function.verticalInfimum` from `Theorem_5_3`, for the project pattern of scalar-parameter
  infima cast into `WithBotTop 𝕜`;
- `Function.verticalInfimum_eq_sInf`, showing the exact owner-side fiber-infimum formula;
- `egauge ℝ≥0` from `Text_5_4_10`, as a nearby canonical infimum-style gauge construction.

Primitive data vs derived API:
- primitive inputs: a function `k : X → WithBotTop 𝕜` and a dual point `xStar : Y`;
- primitive source-facing owner: the function `gauge_polar`;
- primitive implementation data: the admissible-majorant subset of `Y × 𝕜` fed to
  `Function.verticalInfimum`;
- derived API: basic order facts such as admissible majorants bounding the infimum and
  nonnegativity of the resulting value, together with the intrinsic majorant-height `sInf`
  specification theorem.

Layer target: `source-facing`. The construction only needs dual evaluation, so it is owned at the
pairing layer `HasPairing X Y 𝕜` rather than the concrete inner-product self-dual model. The gauge
assumption from the prose is not needed for the bare infimum formula itself, so it is omitted from
the definition header exactly as in the project's other raw infimum-based owners.
-/

def gaugePolarMajorantsAt (k : X → WithBotTop 𝕜) (xStar : Y) : Set 𝕜 :=
  {μ : 𝕜 |
    0 ≤ μ ∧
      ∀ x : X, ((⟪x, xStar⟫ₚ : 𝕜) : WithBotTop 𝕜) ≤ (μ : WithBotTop 𝕜) * k x}

/-- The admissible majorant heights for `kᵒ xStar`, viewed in `WithBotTop 𝕜`. -/
def gaugePolarMajorantHeights (k : X → WithBotTop 𝕜) (xStar : Y) : Set (WithBotTop 𝕜) :=
  ((↑) : 𝕜 → WithBotTop 𝕜) '' gaugePolarMajorantsAt k xStar

private def gaugePolarMajorants (k : X → WithBotTop 𝕜) : Set (Y × 𝕜) :=
  {p : Y × 𝕜 |
    p.2 ∈ gaugePolarMajorantsAt k p.1}

/-- Text 15.0.5: the polar gauge `kᵒ`, written `kᵒ` after `open scoped GaugePolar`, is the
Chapter 1 vertical infimum of the admissible-majorant set. This keeps the source-facing owner
while reusing the project's canonical infimum construction. -/
def gauge_polar (k : X → WithBotTop 𝕜) : Y → WithBotTop 𝕜 :=
  verticalInfimum (gaugePolarMajorants k)

end

namespace GaugePolar

scoped postfix:max "ᵒ" => gauge_polar

end GaugePolar

section

open scoped GaugePolar

variable {𝕜 : Type w} [ConditionallyCompleteLinearOrder 𝕜] [Zero 𝕜] [Mul 𝕜]
variable {X : Type u} {Y : Type v} [HasPairing X Y 𝕜]

/-- The value of `kᵒ` at `xStar` is the infimum of the admissible nonnegative scalar majorants
from the source formula. -/
theorem gauge_polar_eq_sInf_nonneg_majorants
    (k : X → WithBotTop 𝕜) (xStar : Y) :
    kᵒ xStar =
      sInf (gaugePolarMajorantHeights k xStar) := by
  simpa [gauge_polar, gaugePolarMajorantHeights, gaugePolarMajorants, gaugePolarMajorantsAt] using
    (verticalInfimum_eq_sInf (gaugePolarMajorants k) xStar)

-- Proof sketch: `gauge_polar k xStar` is the infimum of the `WithBotTop 𝕜` image of the admissible
-- nonnegative scalar majorants, so any particular admissible nonnegative `μStar` contributes one
-- upper bound for that infimum after coercion to `WithBotTop 𝕜`.
/-- Any admissible majorant for the defining inequality bounds the polar gauge from above. -/
theorem gauge_polar_le_of_majorant
    {k : X → WithBotTop 𝕜} {xStar : Y} (μStar : 𝕜)
    (hμ : μStar ∈ gaugePolarMajorantsAt k xStar) :
    kᵒ xStar ≤ (μStar : WithBotTop 𝕜) := by
  have hmajorant : (xStar, μStar) ∈ gaugePolarMajorants k := hμ
  simpa [gauge_polar] using
    (verticalInfimum_le_of_mem hmajorant :
      verticalInfimum (gaugePolarMajorants k) xStar ≤ μStar)

-- Proof sketch: every element of the image in the defining `sInf` is nonnegative because each
-- defining scalar satisfies the explicit constraint `0 ≤ μ`. The infimum of a set of
-- nonnegative `WithBotTop 𝕜` values is therefore nonnegative; if the set is empty, the
-- infimum is `⊤`,
-- which is still nonnegative.
/-- The polar gauge takes nonnegative values in `WithBotTop 𝕜`. -/
theorem gauge_polar_nonneg (k : X → WithBotTop 𝕜) (xStar : Y) :
    0 ≤ kᵒ xStar := by
  have hmajorants :
      gaugePolarMajorants k ⊆ epi (fun _ : Y ↦ (0 : WithBotTop 𝕜)) := by
    rintro ⟨x, μ⟩ hμ
    refine mem_epi_restrict_iff.mpr ⟨by simp, ?_⟩
    change ((0 : 𝕜) : WithBotTop 𝕜) ≤ (μ : WithBotTop 𝕜)
    exact WithBotTop.coe_le_coe.mpr hμ.1
  have hnonneg := le_verticalInfimum_of_subset_epi hmajorants
  simpa [gauge_polar] using hnonneg xStar

end

/-! ### Text_15_0_6 (from Chap03) -/
noncomputable section

open scoped GaugePolar Rockafellar

universe u v w

section

variable {𝕜 : Type w}
variable {X : Type u} {Y : Type v}
variable [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [HasPairing X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.6 gives an equivalent supremum formula for the polar of a gauge that
  is finite and strictly positive away from the origin.
- `core/canonical`: the owner abstractions are the chapter declarations `IsGauge` from
  `Text_15_0_1` and `gauge_polar` from `Text_15_0_5`, with the unit-sublevel owner
  `gaugeUnitSublevel` from `Text_15_0_2` as the canonical set-side view of the same gauge.
- `bridge/view`: the displayed quotient formula is the source-facing specialization of the support
  function of the unit sublevel, written directly as a `WithBotTop 𝕜` supremum over the canonical
  indexing set `{x : X | x ≠ 0}`.

Domain-style sampling used here:
- `IsGauge` from `Text_15_0_1`;
- `gaugeUnitSublevel` from `Text_15_0_2`;
- `gauge_polar` from `Text_15_0_5`.
- `supportFunction_def` from `Text_13_0_1`.

Primitive data vs derived API:
- primitive inputs: a gauge `k : X → WithBotTop 𝕜`, a dual point `xStar : Y`, and the finiteness
  and strict-positivity hypotheses from the source, both only away from the origin because
  `IsGauge.map_zero` already fixes the zero case;
- derived formula: the supremum of the nonzero quotients `⟪x, xStar⟫ₚ / k(x)`.

Layer target: `bridge/view`; the theorem keeps `gauge_polar` as the owner and adds the textbook's
equivalent supremum expression.
- Ambient refinement: the quotient formula uses only dual evaluation and the sampled owner
  declarations, so it is stated at the canonical pairing layer rather than the concrete
  self-inner-product model. The statement is kept at the intrinsic `WithBotTop 𝕜` owner layer,
  avoiding a real-`sSup` bridge.
-/

-- Proof sketch: unfold `gauge_polar`. Because `k x` is finite and strictly positive for `x ≠ 0`,
-- the inequalities `⟪x, x⋆⟫ₚ ≤ μ⋆ k x` are equivalent on nonzero vectors to the intrinsic
-- quotient bound `((⟪x, x⋆⟫ₚ : WithBotTop 𝕜) / k x) ≤ μ⋆` in `WithBotTop 𝕜`. Equivalently, after
-- normalizing a nonzero vector by the positive scalar `k x`, the admissible-majorant condition is
-- the support-function inequality on the canonical unit sublevel `gaugeUnitSublevel k`, so the
-- polar value is the supremum of that quotient family.
/-- Text 15.0.6: if a gauge `k` is finite and positive away from the origin, then its
polar admits the equivalent formula
`kᵒ(x⋆) = sup_{x ≠ 0} ⟪x, x⋆⟫ₚ / k(x)` at the intrinsic codomain layer `WithBotTop 𝕜`.
The source hypotheses are kept as primitive finiteness and strict-positivity away from the origin;
no `EReal.toReal` bridge is exposed on the theorem surface. -/
theorem gauge_polar_eq_sSup_inner_div_off_zero
    (k : X → WithBotTop 𝕜) [IsGauge k] (xStar : Y)
    (hfinite : ∀ ⦃x : X⦄, x ≠ 0 → k x < ⊤)
    (hpos : ∀ ⦃x : X⦄, x ≠ 0 → 0 < k x) :
    kᵒ xStar =
      sSup ((fun x : X ↦ (⟪x, xStar⟫ₚ : WithBotTop 𝕜) / k x) '' {x : X | x ≠ 0}) := sorry

end

/-! ### Text_15_0_7 (from Chap03) -/
noncomputable section

open scoped GaugePolar PolarCone Rockafellar

universe u v w

section

variable {𝕜 : Type w} [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsOrderedRing 𝕜]
variable {X : Type u} [AddCommMonoid X] [Module 𝕜 X]
variable {Y : Type v} [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.7 states that for the indicator `k = δ(· | K)` of a convex cone
  `K ⊆ R^n`, the polar `kᵒ` agrees with the Fenchel conjugate `k*`, and both are the indicator
  of the polar cone `Kᵒ`.
- `core/canonical`: the existing owner declarations are the generic indicator owner
  `indicatorFunction`, the gauge polar `gauge_polar`, the set polar `polarCone`, and the Chapter
  14 owner theorem `convexConjugate_indicatorFunction_eq_indicatorFunction_polarCone`.
- `bridge/view`: the indicator-polar identity remains the source-facing Chapter 15 bridge from the
  gauge-polar owner to the Chapter 14 indicator-of-polar theorem surface. The conjugacy clause is
  then the source-facing set-level cone statement, rewriting through the existing Chapter 14
  indicator/conjugate owner theorem rather than rebuilding the support-function proof locally.

Domain-style sampling used here:
- `indicatorFunction`;
- `gauge_polar`;
- `polarCone`;
- `convexConjugate_indicatorFunction_eq_indicatorFunction_polarCone`.

Primitive data vs derived API:
- primitive datum for the main identity: a set `K : Set X`;
- primitive data for the conjugacy clause: a set `K : Set X` together with the intrinsic
  hypotheses `K.Nonempty` and `Set.IsCone 𝕜 K`;
- derived cone-specific view: a bundled cone `ConvexCone 𝕜 X`, if needed later, is only a thin
  bridge to this set-level owner data;
- source-facing functions: the canonical indicator bridge `δ[𝕜](· | K)` for the polar identity,
  and in the Chapter 14 conjugacy clause the same `WithBotTop 𝕜`-valued indicator surface;
- derived content: the indicator-of-polar-cone formula and, under the necessary nonemptiness
  hypothesis for conjugacy, the equality with the Fenchel conjugate via the existing Chapter 14
  indicator/conjugate theorem.

Layer target: the main indicator-of-polar identity is `bridge/view` from Chapter 15 gauge polarity
to the Chapter 14 indicator-of-polar owner surface, while the conjugacy equality is the
`source-facing` set-level cone clause and reuses the existing chapter owner theorem directly.
-/

-- Proof sketch: for `k = indicatorFunction (K : Set X)`, the defining admissible-majorant
-- inequality for `gauge_polar k xStar` is equivalent to `⟪x, xStar⟫ ≤ 0` for every `x ∈ K`.
-- Hence the polar value is `0` exactly on `polarCone K` and `⊤` outside it, which is precisely
-- `indicatorFunction (polarCone K)`.
/-- Text 15.0.7 (2): for any set `K`, the polar of its indicator function is the indicator
of the polar cone. The source's cone hypothesis is redundant for this identity and is therefore
omitted from the main declaration. -/
theorem gauge_polar_indicatorFunction_eq_indicatorFunction_polarCone
    (K : Set X) :
    (δ[𝕜](· | K))ᵒ =
      ((δ[𝕜](· | (Kᵒ[𝕜] : PointedCone 𝕜 Y)) : Y → WithBotTop 𝕜)) := by
  sorry

variable [HasPairing Y X 𝕜] [HasPairingSwap X Y 𝕜]

-- Proof sketch: rewrite the gauge polar of the indicator by the preceding Chapter 15
-- indicator-polar bridge, then invoke the Chapter 14 owner theorem identifying the Fenchel
-- conjugate of the indicator of a nonempty cone with the indicator of its polar cone. The
-- nonemptiness hypothesis is mathematically necessary: for the empty cone, the polar gauge is
-- identically `0` while the conjugate of the indicator is identically `⊥`.
/-- Text 15.0.7 (1): for a nonempty cone `K`, the polar of its indicator function agrees with its
Fenchel conjugate at the pairing layer. The bundled convex-cone packaging is redundant for this
equality, so the theorem is stated on the primitive set-level cone data. -/
theorem gauge_polar_indicatorFunction_eq_convexConjugate_indicatorFunction
    (K : Set X) (hK_nonempty : K.Nonempty) (hK_cone : Set.IsCone 𝕜 K) :
    (δ[𝕜](· | K))ᵒ = (δ[𝕜](· | K))⋆ := by
  sorry

end

/-! ### Text_15_0_8 (from Chap03) -/
noncomputable section

section

open scoped GaugePolar

local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.8 gives a concrete planar gauge
  `k(ξ₁, ξ₂) = √(ξ₁² + ξ₂²) + ξ₁`, computes its polar explicitly, and records that neither `k`
  nor `kᵒ` is a norm.
- `core/canonical`: the owner abstractions already present in the chapter are `IsClosedGauge`,
  `gauge_polar`, `IsGaugeNorm`, and the project's canonical planar ambient
  `R2 = EuclideanSpace ℝ (Fin 2)`.
- `bridge/view`: the file keeps the source-facing explicit primal formula as data and puts the
  displayed polar formula directly on the theorem surface, without introducing an extra polar owner
  or a second ambient-space wrapper for the example.

Domain-style sampling used here:
- `IsGauge` from `Text_15_0_1`;
- `IsGauge.eq_egauge_unitSublevel` from `Text_15_0_2`, showing the canonical set-side owner
  available for gauges after the gauge structure is known;
- `gauge_polar` from `Text_15_0_5`;
- `IsClosedGauge` from `Text_15_0_24`, the chapter owner for a closed gauge;
- `IsGaugeNorm` from `Text_15_0_12`.
- the nearby planar-example owners `R2 = EuclideanSpace ℝ (Fin 2)` in `Text_14_0_14` and
  `Text_15_0_27`, showing the chapter's canonical ambient model for source-facing `R²` formulas.

Primitive data vs derived API:
- primitive source data: the explicit planar formula `parabolicGauge`;
- derived API: the owner-predicate fact `parabolicGauge_isClosedGauge`, the theorem giving the
  displayed piecewise formula for `parabolicGaugeᵒ`, and the statements that neither the primal nor
  the polar gauge is a norm-gauge.

Layer target: `source-facing`. The explicit formula from the text remains the public core, while
the closed-gauge owner abstraction `IsClosedGauge` is reused directly for clause (1), and the
polar clause is kept as a theorem-level displayed formula rather than a second public owner. The
public ambient is the chapter's canonical planar owner layer `R2`, matching the recurring
coordinate-example API already shared elsewhere in the project.
-/

/-- The concrete gauge on `R²` given by `k(ξ₁, ξ₂) = √(ξ₁² + ξ₂²) + ξ₁`. -/
def parabolicGauge : R2 → EReal :=
  fun x ↦
    ((Real.sqrt (x 0 ^ 2 + x 1 ^ 2) + x 0 : ℝ) : EReal)

-- Proof sketch: the epigraph of `parabolicGauge` is the closed second-order cone
-- `{(ξ, t) | Real.sqrt (ξ₁^2 + ξ₂^2) + ξ₁ ≤ t}`. This gives both the gauge axioms and lower
-- semicontinuity, so clause (1) is stated directly with the Chapter 15 owner `IsClosedGauge`.
/-- Text 15.0.8 (1): the function `k(ξ₁, ξ₂) = √(ξ₁² + ξ₂²) + ξ₁` is a closed gauge on `R²`. -/
theorem parabolicGauge_isClosedGauge :
    IsClosedGauge parabolicGauge := sorry

-- Proof sketch: start from the definition of `parabolicGaugeᵒ` as the infimum of all scalar
-- majorants `μ⋆` satisfying `⟪x, x⋆⟫ ≤ μ⋆ k x`. Optimize this inequality using the explicit
-- formula for `k`; the admissible majorants are exactly the displayed piecewise family.
/-- Text 15.0.8 (2): the polar gauge of `k` is the displayed piecewise function with finite value
`((ξ₂^*)² / ξ₁^* + ξ₁^*) / 2` when `ξ₁^* > 0`, value `0` at the origin, and value `+∞`
otherwise. -/
theorem gauge_polar_parabolicGauge_eq (xStar : R2) :
    parabolicGaugeᵒ xStar =
      if 0 < xStar 0 then
        (((xStar 1 ^ 2 / xStar 0 + xStar 0) / 2 : ℝ) : EReal)
      else if xStar = 0 then
        0
      else
        ⊤ := sorry

-- Proof sketch: a norm-gauge must be symmetric. For `x = (ξ₁, ξ₂)`, one has
-- `parabolicGauge (-x) = √(ξ₁² + ξ₂²) - ξ₁`, which differs from `parabolicGauge x` whenever
-- `ξ₁ ≠ 0`. Hence `parabolicGauge` cannot satisfy the symmetry field of `IsGaugeNorm`.
/-- Text 15.0.8 (3): the gauge `k` is not a norm. -/
theorem parabolicGauge_not_isGaugeNorm :
    ¬ IsGaugeNorm parabolicGauge := sorry

-- Proof sketch: the polar formula from the preceding clause gives
-- `parabolicGaugeᵒ xStar = ⊤` whenever the first coordinate of `xStar` is negative, so
-- `parabolicGaugeᵒ` is not finite everywhere. Since finiteness at every point is required in
-- `IsGaugeNorm`, the polar gauge cannot be a norm.
/-- Text 15.0.8 (4): the polar gauge `kᵒ` is not a norm. -/
theorem gauge_polar_parabolicGauge_not_isGaugeNorm :
    ¬ IsGaugeNorm parabolicGaugeᵒ := sorry

end

/-! ### Text_15_0_9 (from Chap03) -/
noncomputable section

universe u v w

section

open scoped GaugePolar Rockafellar

variable {𝕜 : Type w} [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [DecidableLT 𝕜]
variable {X : Type u} {Y : Type v} [AddCommMonoid X] [Module 𝕜 X] [HasPairing X Y 𝕜]
variable {k : X → WithBotTop 𝕜}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.9 states the generalized Cauchy inequality for a gauge and its polar.
- `core/canonical`: the owner objects already present in the chapter are the source-facing gauge
  predicate `IsGauge` from `Text_15_0_1`, the polar gauge owner `gauge_polar`/`kᵒ` from
  `Text_15_0_5`, and the effective-domain owner `dom(·)` from `Definition_4_4`.
- `bridge/view`: the inequality is stated at the pairing layer `HasPairing X Y 𝕜`, matching the
  owner layer of `gauge_polar`.

Domain-style sampling used here:
- `IsGauge` from `Text_15_0_1`;
- `gauge_polar` and `gauge_polar_le_of_majorant` from `Text_15_0_5`;
- `dom(·)` / `mem_effectiveDomain` from `Definition_4_4`;
- `HasPairing` and `HasPairingNegLeft` from `Chap01.HasPairing`.

Primitive data vs derived API:
- primitive inputs: a gauge `k : X → WithBotTop 𝕜`, a primal vector `x`, and a dual vector
  `xStar`;
- owner-side domain conditions: membership of `x` and `xStar` in the canonical effective domains
  `dom(k)` and `dom(kᵒ)`;
- derived strengthening: the real absolute-value version under the norm-gauge hypothesis.
-/

-- Proof sketch: by the definition of `kᵒ xStar` as the infimum of admissible real
-- majorants `μStar`, every `ε > 0` yields some `μStar ≤ kᵒ xStar + ε` with
-- `⟪x, xStar⟫ ≤ μStar * k x` for all `x`. Evaluating at the chosen `x`, then letting `ε ↓ 0`,
-- gives the required bound because both domain hypotheses ensure the right-hand side is finite.
/-- Text 15.0.9 (1): for a gauge `k` and its polar `kᵒ`, the pairing `⟪x, x⋆⟫` is bounded by
`k(x) kᵒ(x⋆)` on `dom(k) × dom(kᵒ)`. -/
theorem inner_le_mul_gauge_polar
    [IsGauge k] {x : X} {xStar : Y}
    (hx : x ∈ dom(k)) (hxStar : xStar ∈ dom(kᵒ)) :
    ((⟪x, xStar⟫ₚ : 𝕜) : WithBotTop 𝕜) ≤ k x * kᵒ xStar := sorry

end

section

open scoped GaugePolar Rockafellar

variable {𝕜 : Type w} [Ring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
  [IsOrderedRing 𝕜] [DecidableLT 𝕜]
variable {X : Type u} {Y : Type v}
variable [AddCommGroup X] [Module 𝕜 X]
variable [HasPairing X Y 𝕜] [HasPairingNegLeft X Y 𝕜]
variable {k : X → WithBotTop 𝕜}

-- Proof sketch: apply the first inequality to `x` and to `-x`. The norm-gauge hypothesis gives
-- `k (-x) = k x` via the owner-side absolute homogeneity theorem
-- `IsGaugeNorm.map_smul_eq_abs`, while left-negation compatibility of the pairing gives
-- `⟪-x, xStar⟫ₚ = -⟪x, xStar⟫ₚ`; combining the two one-sided bounds yields the estimate for
-- `|⟪x, xStar⟫ₚ|`.
/-- Text 15.0.9 (2): if `k` is a norm-gauge, then the generalized Cauchy inequality holds with an
absolute value for every `x` and `x⋆`. -/
theorem abs_inner_le_mul_gauge_polar
    [IsGaugeNorm k] (x : X) (xStar : Y) :
    ((|⟪x, xStar⟫ₚ| : 𝕜) : WithBotTop 𝕜) ≤ k x * kᵒ xStar := sorry

end

/-! ### Text_15_0_10 (from Chap03) -/
noncomputable section

attribute [local instance] Classical.propDecidable

open Function (verticalInfimum verticalInfimum_eq_sInf verticalInfimum_le_of_mem)

universe u v

section

open scoped GaugePolar Rockafellar NNReal

variable {X : Type u} {Y : Type v}
variable [AddCommMonoid X] [Module ℝ X] [HasPairing X Y ℝ]

/-- The canonical `EReal` bridge for extending an `ℝ≥0`-valued function by `⊤` off a subset. -/
private def extendEReal {A : Type*} (C : Set A) (f : C → ℝ≥0) : A → EReal :=
  fun x ↦
    show EReal from
      (↑(Function.extend Subtype.val (fun y : C ↦ ((f y : ℝ≥0) : WithTop ℝ))
          (fun _ ↦ (⊤ : WithTop ℝ)) x) :
        WithBot (WithTop ℝ))

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.10 starts from a family of inequalities
  `⟪x, y⟫ ≤ h(x) j(y)` on `H × J`, with `h : H → [0, +∞)` and `j : J → [0, +∞)`, defines the
  best possible primal gauge `k` by infimizing the admissible nonnegative scalar majorants
  against the restricted function `j`, and then records the resulting primal and polar bounds
  together with the final characterization of when the original inequalities are already best
  possible.
- `core/canonical`: the nearby Section 15 owner API already uses `IsGauge`,
  `LowerSemicontinuous`, `IsClosedGauge`, `gauge_polar`, `dom(·)`, and
  `Function.verticalInfimum`.
- `bridge/view`: the final sentence uses the standard project pattern of extending restricted data
  by `⊤` off a set, rendered canonically here by `Function.extend Subtype.val`, so the remaining
  clauses are best stated as atomic comparison and characterization theorems for those concrete
  owners.

Domain-style sampling used here:
- `IsGauge` and `gauge_polar` from `Text_15_0_9`;
- `LowerSemicontinuous` as the project-wide closedness predicate for extended-real-valued
  functions;
- `IsClosedGauge` from `Text_15_0_24` as the chapter owner for closed gauges;
- `Function.verticalInfimum` and `Function.verticalInfimum_eq_sInf` from `Theorem_5_3` as the
  project owner for infimum-over-majorants constructions;
- `Function.extend Subtype.val`, `Subtype.val_injective.extend_apply`, and
  `Function.extend_apply'` from `Mathlib/Logic/Function/Basic.lean` as the canonical owner-side
  API for extending subtype functions by `⊤`;
- the `EReal` coercion of this subtype extension, used here to compare the source-facing
  restricted data with the chapter-level global gauge API.

Owner-abstraction check:
- `gauge_polar` is the first canonical candidate, but its admissible-majorant condition quantifies
  over all ambient vectors. Text 15.0.10 quantifies only over `y ∈ J`, and replacing that
  restricted family by an ambient `gauge_polar` owner would change the zero-majorant case.
  Therefore the infimum-defined envelope remains the main `source-facing` owner here, while its
  implementation should still reuse the chapter infimum owner `Function.verticalInfimum`.

Primitive data vs derived API:
- primitive source-facing data: the restricted functions `h : H → ℝ≥0` and `j : J → ℝ≥0`, the
  displayed admissible-majorant inequality on `H × J`, and the infimum over the corresponding
  nonnegative scalar majorants;
- derived API: the gauge instance and lower semicontinuity of the resulting envelope, the
  `H ⊆ dom k` and `k ≤ h` conclusions, the polar bound on `J`, and the final generalized Cauchy
  inequality for the polar pair;
- final characterization: the original inequalities are already best exactly when the canonical
  subtype extensions form a closed polar gauge pair.

Layer target: `source-facing`, because the source introduces a concrete new gauge by an explicit
infimum formula rather than merely recalling an existing owner.
-/

/-- The original majorization hypothesis `⟪x, y⟫ ≤ h(x) j(y)` on `H × J`. -/
def majorizesOn (H : Set X) (J : Set Y) (h : H → ℝ≥0) (j : J → ℝ≥0) : Prop :=
  ∀ x : H, ∀ y : J, ((⟪x, y⟫ₚ : ℝ) : EReal) ≤ (h x : EReal) * (j y : EReal)

private def majorizationEnvelopeMajorants (J : Set Y) (j : J → ℝ≥0) : Set (X × ℝ) :=
  {p : X × ℝ |
    0 ≤ p.2 ∧
      ∀ y : J, ((⟪p.1, y⟫ₚ : ℝ) : EReal) ≤ (p.2 : EReal) * (j y : EReal)}

/-- The envelope gauge generated by the family of inequalities against `J` and `j`, implemented as
the Chapter 1 vertical infimum of the admissible-majorant set. The source `sInf` formula is
recovered by `majorization_envelope_gauge_eq_sInf_nonneg_majorants`. -/
def majorization_envelope_gauge (J : Set Y) (j : J → ℝ≥0) : X → EReal :=
  verticalInfimum (majorizationEnvelopeMajorants J j)

/-- The value of the majorization envelope at `x` is the infimum of the admissible nonnegative
scalar majorants from the source formula. -/
theorem majorization_envelope_gauge_eq_sInf_nonneg_majorants
    (J : Set Y) (j : J → ℝ≥0) (x : X) :
    majorization_envelope_gauge J j x =
      sInf
        (((↑) : ℝ≥0 → EReal) ''
          {μ : ℝ≥0 |
            ∀ y : J, ((⟪x, y⟫ₚ : ℝ) : EReal) ≤ (μ : EReal) * (j y : EReal)}) := by
  rw [majorization_envelope_gauge, verticalInfimum_eq_sInf]
  change
    sInf
        (((↑) : ℝ → EReal) ''
          {μ : ℝ |
            0 ≤ μ ∧
              ∀ y : J, ((⟪x, y⟫ₚ : ℝ) : EReal) ≤ (μ : EReal) * (j y : EReal)}) =
      sInf
        (((↑) : ℝ≥0 → EReal) ''
          {μ : ℝ≥0 |
            ∀ y : J, ((⟪x, y⟫ₚ : ℝ) : EReal) ≤ (μ : EReal) * (j y : EReal)})
  congr 1
  ext a
  constructor
  · rintro ⟨μ, hμ, rfl⟩
    exact ⟨⟨μ, hμ.1⟩, hμ.2, rfl⟩
  · rintro ⟨μ, hμ, rfl⟩
    exact ⟨(μ : ℝ), ⟨μ.2, hμ⟩, rfl⟩

-- Proof sketch: `majorization_envelope_gauge J j x` is defined as the infimum of the `EReal`
-- image of the admissible nonnegative scalar majorants, so every admissible scalar majorant gives
-- an upper bound for that infimum after coercion to `EReal`.
/-- Any admissible majorant bounds the envelope gauge from above. -/
theorem majorization_envelope_gauge_le_of_majorant
    {J : Set Y} {j : J → ℝ≥0} {x : X} {μ : ℝ≥0}
    (hμ : ∀ y : J, ((⟪x, y⟫ₚ : ℝ) : EReal) ≤ (μ : EReal) * (j y : EReal)) :
    majorization_envelope_gauge J j x ≤ (μ : EReal) := by
  have hmajorant : (x, (μ : ℝ)) ∈ majorizationEnvelopeMajorants J j := ⟨μ.2, hμ⟩
  simpa [majorization_envelope_gauge] using
    (verticalInfimum_le_of_mem hmajorant :
      verticalInfimum (majorizationEnvelopeMajorants J j) x ≤ (μ : ℝ))

/-- The envelope gauge is a gauge in the sense of Text 15.0.1. -/
instance (J : Set Y) (j : J → ℝ≥0) : IsGauge (majorization_envelope_gauge J j) := sorry

-- Proof sketch: for each `y ∈ J`, the inequality
-- `⟪x, y⟫ ≤ μ j(y)` cuts out a closed halfspace in `X × ℝ`, and the epigraph of
-- `majorization_envelope_gauge J j` is the intersection of these halfspaces. Hence the epigraph is
-- a closed convex cone with no negative heights. The gauge structure is carried by the instance
-- above, and the same epigraph argument gives lower semicontinuity.
/-- Text 15.0.10: the envelope gauge is lower semicontinuous; together with the gauge instance
above, this is the closed-gauge conclusion of the source item. -/
theorem majorization_envelope_gauge_lowerSemicontinuous
    [TopologicalSpace X] (J : Set Y) (j : J → ℝ≥0) :
    LowerSemicontinuous (majorization_envelope_gauge J j) := sorry

-- Proof sketch: by definition, every admissible scalar `μ` in the defining infimum satisfies the
-- required inequality against every `y ∈ J`. Approximate the infimum in the definition of
-- `majorization_envelope_gauge J j x` from above by admissible majorants and pass to the limit
-- inside `EReal`.
/-- On the finite-value domain of the envelope gauge, the original inequality holds against every
`y ∈ J`. -/
theorem inner_le_majorization_envelope_gauge_mul
    {J : Set Y} {j : J → ℝ≥0} {x : X} {y : J}
    (hx : x ∈ dom(majorization_envelope_gauge J j)) :
    ((⟪x, y⟫ₚ : ℝ) : EReal) ≤
      majorization_envelope_gauge J j x * (j y : EReal) := sorry

-- Proof sketch: for `x ∈ H`, the given bound `⟪x, y⟫ ≤ h(x) j(y)` shows that the finite scalar
-- `h x` is an admissible majorant in the defining infimum for `majorization_envelope_gauge J j x`.
-- The preceding majorant lemma then gives `majorization_envelope_gauge J j x ≤ h x`, and
-- finiteness of `h x` puts `x` in the effective domain of the envelope gauge.
/-- Any set `H` carrying a majorizing inequality against `J` lies in the effective domain of the
envelope gauge. -/
theorem subset_dom_majorization_envelope_gauge_of_majorization
    {H : Set X} {J : Set Y} {h : H → ℝ≥0} {j : J → ℝ≥0}
    (hHJ : majorizesOn H J h j) :
    H ⊆ dom(majorization_envelope_gauge J j) := by
  intro x hx
  have hk : majorization_envelope_gauge J j x ≤ (h ⟨x, hx⟩ : EReal) :=
    majorization_envelope_gauge_le_of_majorant (hHJ ⟨x, hx⟩)
  rw [mem_effectiveDomain]
  exact lt_of_le_of_lt hk (show ((h ⟨x, hx⟩ : ℝ≥0) : EReal) < ⊤ by simp)

-- Proof sketch: fix `x ∈ H` and note that the given majorization hypothesis makes the finite
-- scalar `h x` an admissible majorant in the defining infimum for the envelope gauge. The infimum
-- is therefore bounded above by `h x`.
/-- On any set `H` satisfying the original majorization hypothesis, the envelope gauge is bounded
above by `h`. -/
theorem majorization_envelope_gauge_le_on
    {H : Set X} {J : Set Y} {h : H → ℝ≥0} {j : J → ℝ≥0}
    (hHJ : majorizesOn H J h j)
    {x : X} (hx : x ∈ H) :
    majorization_envelope_gauge J j x ≤ (h ⟨x, hx⟩ : EReal) := by
  exact majorization_envelope_gauge_le_of_majorant (hHJ ⟨x, hx⟩)

-- Proof sketch: for fixed `y ∈ J`, the previous primal inequality gives
-- `⟪x, y⟫ ≤ majorization_envelope_gauge J j x * j y` on the effective domain of the envelope
-- gauge. This is exactly the defining majorant condition for `gauge_polar`, so `j y` bounds the
-- polar from above.
/-- The polar gauge of the envelope gauge is bounded above by `j` on `J`. -/
theorem gauge_polar_majorization_envelope_gauge_le_on
    {J : Set Y} {j : J → ℝ≥0} (y : J) :
    gauge_polar (majorization_envelope_gauge J j) y ≤ (j y : EReal) := sorry

-- Proof sketch: the preceding theorem shows `gauge_polar (majorization_envelope_gauge J j) y` is
-- bounded above by the finite scalar `j y` for every `y ∈ J`, hence each such `y` belongs to the
-- effective domain of the polar gauge.
/-- Every `y ∈ J` lies in the effective domain of the polar of the envelope gauge. -/
theorem subset_dom_gauge_polar_majorization_envelope_gauge
    (J : Set Y) (j : J → ℝ≥0) :
    J ⊆ dom(gauge_polar (majorization_envelope_gauge J j)) := by
  intro y hy
  have hj : gauge_polar (majorization_envelope_gauge J j) y ≤ (j ⟨y, hy⟩ : EReal) :=
    gauge_polar_majorization_envelope_gauge_le_on ⟨y, hy⟩
  rw [mem_effectiveDomain]
  exact lt_of_le_of_lt hj (show ((j ⟨y, hy⟩ : ℝ≥0) : EReal) < ⊤ by simp)

-- Proof sketch: once `majorization_envelope_gauge J j` is known to be a gauge, this is exactly the
-- general inequality from Text 15.0.9 applied to that gauge and its polar on their effective
-- domains.
/-- The envelope gauge and its polar satisfy the generalized Cauchy inequality on the product of
their effective domains. -/
theorem inner_le_majorization_envelope_gauge_mul_polar
    {J : Set Y} {j : J → ℝ≥0} {x : X} {y : Y}
    (hx : x ∈ dom(majorization_envelope_gauge J j))
    (hy : y ∈ dom((majorization_envelope_gauge J j)ᵒ)) :
    ((⟪x, y⟫ₚ : ℝ) : EReal) ≤
      majorization_envelope_gauge J j x * (majorization_envelope_gauge J j)ᵒ y :=
  inner_le_mul_gauge_polar hx hy

section

variable [TopologicalSpace X]
variable {H : Set X} {J : Set Y} {h : H → ℝ≥0} {j : J → ℝ≥0}

local notation "h∞" =>
  extendEReal H h

local notation "j∞" =>
  extendEReal J j

-- Proof sketch: if `h∞` and `j∞` are closed gauges polar to each other, then the defining
-- majorization inequality for `h` and `j` shows that `h∞` is an admissible envelope against `j`,
-- while the mutual polar identities force the envelope-improvement process to stop exactly at
-- `h∞` and `j∞`. Conversely, if the `⊤`-extended functions already coincide with the envelope and
-- its polar, then the earlier theorems in this file supply the gauge and lower-semicontinuity
-- structure on `h∞`, while the stated polar identity identifies `j∞` with the owner-side polar of
-- a closed gauge; the reverse closedness and bipolar identity for `j∞` are therefore derived by
-- the existing polarity API. The explicit majorization hypothesis on `H × J` is omitted from the
-- public statement because either side already recovers that inequality for the restricted
-- functions.
/-- Text 15.0.10: a family of inequalities `⟪x, y⟫ ≤ h(x) j(y)` on `H × J` is already best
possible exactly when, after extending `h` and `j` by `+∞` off `H` and `J`, the resulting global
functions are a closed gauge and its polar; equivalently, they already coincide with the envelope
gauge and its polar. -/
theorem best_majorization_iff_extensions_are_closed_gauges_polar
    :
    (h∞ = majorization_envelope_gauge J j ∧
      gauge_polar h∞ = j∞) ↔
      (IsClosedGauge h∞ ∧
        gauge_polar h∞ = j∞) := sorry

end

end

/-! ### Text_15_0_11 (from Chap03) -/
noncomputable section

section

open Metric
open scoped GaugePolar RealInnerProductSpace

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.11 identifies the polar gauge of the Euclidean norm with the norm
  itself.
- `core/canonical`: the owner abstraction is the source-facing polar gauge `gauge_polar`, written
  `kᵒ` after `open scoped GaugePolar`.
- `bridge/view`: the norm function `fun x ↦ ((‖x‖ : ℝ) : WithBotTop ℝ)` is compared directly with
  its polar via
  the owner-side majorant and `sInf` formulas, while the displayed Schwarz inequality is the
  standard absolute-value Cauchy-Schwarz estimate.

Domain-style sampling used here:
- `gauge_polar_eq_sInf_nonneg_majorants`;
- `gauge_polar_le_of_majorant`;
- `abs_real_inner_le_norm`;
- `inv_norm_smul_mem_unitClosedBall`.

Primitive data vs derived API:
- primitive source object: the norm function `fun x : E ↦ ((‖x‖ : ℝ) : WithBotTop ℝ)`;
- direct owner reuse: the polar-gauge majorant theorem `gauge_polar_le_of_majorant` and the
  defining `sInf` formula `gauge_polar_eq_sInf_nonneg_majorants`;
- derived bridge: the upper bound from Cauchy-Schwarz and the lower bound from the normalized
  witness `‖x⋆‖⁻¹ • x⋆`.

Layer target: `bridge/view`, since this item does not define a new owner but identifies the norm
with its image under the canonical polar-gauge owner. The proof uses only inner-product-space data,
so the ambient is refined all the way down to arbitrary real inner-product spaces instead of the
concrete `EuclideanSpace ℝ (Fin n)` model or a finite-dimensional specialization.
-/

/- The majorant upper-bound step for `gauge_polar` is already owned upstream. -/
recall gauge_polar_le_of_majorant

/- The defining `sInf` formula for `gauge_polar` is already owned upstream. -/
recall gauge_polar_eq_sInf_nonneg_majorants

/-- Text 15.0.11, in canonical ambient form: the polar gauge of the norm is the norm itself on a
real inner-product space. -/
-- Proof sketch: the upper bound is the owner theorem `gauge_polar_le_of_majorant`, with the
-- majorant `μ⋆ = ‖x⋆‖` supplied by Cauchy-Schwarz. For the lower bound, the defining `sInf`
-- formula says it suffices to test every admissible `μ⋆`; evaluating the admissibility inequality
-- at the normalized vector `‖x⋆‖⁻¹ • x⋆` forces `‖x⋆‖ ≤ μ⋆`.
theorem gauge_polar_norm_eq_norm :
    (fun x : E ↦ ((‖x‖ : ℝ) : WithBotTop ℝ))ᵒ =
      fun x : E ↦ ((‖x‖ : ℝ) : WithBotTop ℝ) := by
  ext xStar
  apply le_antisymm
  · let k : E → WithBotTop ℝ := fun x : E ↦ ((‖x‖ : ℝ) : WithBotTop ℝ)
    let μStar : NNReal := ‖xStar‖₊
    change kᵒ xStar ≤ (μStar : WithBotTop ℝ)
    exact
      gauge_polar_le_of_majorant
        (μStar : ℝ)
        ⟨μStar.2, fun x ↦ by
          have hinner : ⟪x, xStar⟫ ≤ ‖xStar‖ * ‖x‖ := by
            calc
              ⟪x, xStar⟫ ≤ |⟪x, xStar⟫| := le_abs_self _
              _ ≤ ‖x‖ * ‖xStar‖ := abs_real_inner_le_norm x xStar
              _ = ‖xStar‖ * ‖x‖ := by ring
          have hinnerE :
              ((⟪x, xStar⟫ : ℝ) : WithBotTop ℝ) ≤
                ((‖xStar‖ * ‖x‖ : ℝ) : WithBotTop ℝ) := by
            exact WithBotTop.coe_le_coe.mpr hinner
          simpa [WithBot.coe_mul] using hinnerE⟩
  · rw [gauge_polar_eq_sInf_nonneg_majorants]
    refine le_sInf ?_
    rintro _ ⟨μStar, hμ, rfl⟩
    by_cases hx : xStar = 0
    · subst xStar
      have hμ0 : ((0 : ℝ) : WithBotTop ℝ) ≤ (μStar : WithBotTop ℝ) :=
        WithBotTop.coe_le_coe.mpr hμ.1
      simpa using hμ0
    · let y : E := ‖xStar‖⁻¹ • xStar
      have hy_mem : y ∈ Metric.closedBall (0 : E) 1 := by
        simpa [y] using inv_norm_smul_mem_unitClosedBall xStar
      have hy_norm : ‖y‖ ≤ 1 := by
        simpa using (mem_closedBall_zero_iff.mp hy_mem)
      have hyμ :
          ((⟪y, xStar⟫ : ℝ) : WithBotTop ℝ) ≤
            ((μStar * ‖y‖ : ℝ) : WithBotTop ℝ) := by
        simpa [WithBot.coe_mul] using hμ.2 y
      have hy_pair : ⟪y, xStar⟫ = ‖xStar‖ := by
        dsimp [y]
        rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
        field_simp [norm_ne_zero_iff.mpr hx]
      calc
        ((‖xStar‖ : ℝ) : WithBotTop ℝ) = ((⟪y, xStar⟫ : ℝ) : WithBotTop ℝ) := by rw [hy_pair]
        _ ≤ ((μStar * ‖y‖ : ℝ) : WithBotTop ℝ) := hyμ
        _ ≤ (μStar : WithBotTop ℝ) := by
          have hμy : μStar * ‖y‖ ≤ μStar := by
            nlinarith [hμ.1, hy_norm]
          exact WithBotTop.coe_le_coe.mpr hμy

/- The Schwarz inequality here is already the canonical absolute-value Cauchy-Schwarz estimate. -/
recall abs_real_inner_le_norm

end
