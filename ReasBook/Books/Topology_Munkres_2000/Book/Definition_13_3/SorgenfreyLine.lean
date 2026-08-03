module

public import Topology_Munkres_2000.Book.Definition_13_3.RealLine
public import Mathlib.Topology.Bases

public section

open Set

/-- The Sorgenfrey line, also called the real line with the lower-limit topology. -/
@[expose]
def SorgenfreyLine := ℝ

namespace SorgenfreyLine

/-- The carrier equivalence from the Sorgenfrey line to the real numbers. -/
@[expose]
def toReal : SorgenfreyLine ≃ ℝ := Equiv.refl ℝ

/-- The real preorder on the carrier of the Sorgenfrey line. -/
instance instPreorder : Preorder SorgenfreyLine :=
  inferInstanceAs (Preorder ℝ)

/-- The real zero on the carrier of the Sorgenfrey line. -/
instance instZero : Zero SorgenfreyLine :=
  inferInstanceAs (Zero ℝ)

/-- The real one on the carrier of the Sorgenfrey line. -/
instance instOne : One SorgenfreyLine :=
  inferInstanceAs (One ℝ)

/-- The lower-limit topology on `SorgenfreyLine`. -/
instance instTopologicalSpace : TopologicalSpace SorgenfreyLine := RealTopology.lowerLimit

/-- The topology on `SorgenfreyLine` is the lower-limit topology on its real carrier. -/
theorem topology_eq_lowerLimit :
    (inferInstance : TopologicalSpace SorgenfreyLine) = RealTopology.lowerLimit := rfl

/-- Helper for Definition 13.3: two lower-limit basis intervals containing a point
admit a smaller lower-limit basis interval through that point. -/
lemma lowerLimitBasis_exists_subset_inter :
    ∀ s ∈ RealTopology.lowerLimitBasis, ∀ t ∈ RealTopology.lowerLimitBasis,
      ∀ x ∈ s ∩ t, ∃ u ∈ RealTopology.lowerLimitBasis, x ∈ u ∧ u ⊆ s ∩ t := by
  -- Unpack the two basis intervals and refine them at the common point.
  rintro _ ⟨a, b, hab, rfl⟩ _ ⟨c, d, hcd, rfl⟩ x ⟨hxab, hxcd⟩
  have hxUpper : x < min b d := lt_min hxab.2 hxcd.2
  refine ⟨Ico x (min b d), ⟨x, min b d, hxUpper, rfl⟩, ⟨le_rfl, hxUpper⟩, ?_⟩
  -- The upper endpoint lies below both original upper endpoints.
  intro y hy
  exact ⟨⟨hxab.1.trans hy.1, hy.2.trans_le (min_le_left b d)⟩,
    ⟨hxcd.1.trans hy.1, hy.2.trans_le (min_le_right b d)⟩⟩

/-- Helper for Definition 13.3: the lower-limit basis covers the Sorgenfrey line. -/
lemma sUnion_lowerLimitBasis :
    ⋃₀ RealTopology.lowerLimitBasis = (Set.univ : Set SorgenfreyLine) := by
  -- Every point lies in the half-open interval from itself to its successor.
  apply sUnion_eq_univ_iff.mpr
  intro x
  refine ⟨Ico x (x + 1), ⟨x, x + 1, lt_add_one x, rfl⟩, ?_⟩
  exact ⟨le_rfl, lt_add_one x⟩

/-- The half-open intervals in `RealTopology.lowerLimitBasis` form a basis for the
Sorgenfrey line. -/
theorem isTopologicalBasis_lowerLimitBasis :
    @TopologicalSpace.IsTopologicalBasis SorgenfreyLine instTopologicalSpace
      RealTopology.lowerLimitBasis := by
  -- Supply the interval refinement, coverage, and generated-topology fields.
  refine ⟨lowerLimitBasis_exists_subset_inter, sUnion_lowerLimitBasis, ?_⟩
  calc
    instTopologicalSpace = RealTopology.lowerLimit := topology_eq_lowerLimit
    _ = TopologicalSpace.generateFrom RealTopology.lowerLimitBasis :=
      RealTopology.lowerLimit_eq_generateFrom

end SorgenfreyLine
