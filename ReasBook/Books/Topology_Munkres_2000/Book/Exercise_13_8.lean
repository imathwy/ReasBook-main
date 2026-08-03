module

public import Topology_Munkres_2000.Book.Exercise_13_8.RationalIntervals

public section

/-- Exercise 13.8. Rational-endpoint open intervals form a countable basis for the
standard topology on `ℝ`, while rational-endpoint half-open intervals form a basis for
a topology different from the lower-limit topology. -/
theorem Exercise_13_8 :
    Real.rationalOpenIntervals.Countable ∧
      TopologicalSpace.IsTopologicalBasis Real.rationalOpenIntervals ∧
      RealTopology.rationalLowerLimit.IsTopologicalBasis
        RealTopology.rationalLowerLimitBasis ∧
      RealTopology.rationalLowerLimit ≠ RealTopology.lowerLimit := by
  -- Package the basis and topology comparisons proved in the supporting API.
  exact ⟨Real.rationalOpenIntervals_countable,
    Real.rationalOpenIntervals_isTopologicalBasis,
    RealTopology.rationalLowerLimitBasis_isTopologicalBasis,
    RealTopology.rationalLowerLimit_ne_lowerLimit⟩
