import ConvexAnalysis_Rockafellar_1970.Chap01.Corollary_2_6_3
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_10
import ConvexAnalysis_Rockafellar_1970.Chap01.EOrder.Mul
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_8

-- Declarations for this item will be appended below by the statement pipeline.

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
