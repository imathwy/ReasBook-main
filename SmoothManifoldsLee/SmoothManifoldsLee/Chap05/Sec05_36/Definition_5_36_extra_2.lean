import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import SmoothManifoldsLee.Chap01.Sec01_06.Definition_1_6_extra_2
import SmoothManifoldsLee.Chap05.Sec05_28.Definition_5_28_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ContDiff Manifold

noncomputable section

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "dimM" => Module.finrank ℝ E

/-- Definition 5.36-extra-2: A regular domain in `M` is a properly embedded codimension-`0`
submanifold with boundary. The codimension-`0` owner is the chapter's
`SmoothManifoldWithBoundary dimM S`; `Set.IsRegularDomain` adds the ambient compatibility data
that the subtype inclusion is a smooth embedding and a proper map. -/
class Set.IsRegularDomain (S : Set M) [SmoothManifoldWithBoundary dimM S] : Prop where
  /-- The subtype inclusion of a regular domain into the ambient manifold is a smooth embedding. -/
  isSmoothEmbedding_subtype_val :
    Manifold.IsSmoothEmbedding
      (leeBoundaryModelWithCorners dimM)
      I
      ∞
      (Subtype.val : S → M)
  /-- A regular domain is properly embedded in the ambient manifold. -/
  isProperlyEmbedded : S.IsProperlyEmbedded

/-- The empty subset is a regular domain for any chosen smooth manifold-with-boundary structure on
the empty subtype in the ambient dimension. -/
instance instIsRegularDomainEmpty
    [SmoothManifoldWithBoundary dimM (∅ : Set M)] :
    Set.IsRegularDomain I (∅ : Set M) where
  isSmoothEmbedding_subtype_val := by
    refine ⟨?_, ⟨Topology.IsInducing.subtypeVal, Subtype.val_injective⟩⟩
    exact ⟨PUnit, inferInstance, inferInstance, fun x ↦ False.elim x.2⟩
  isProperlyEmbedded := isClosed_empty.isProperlyEmbedded
