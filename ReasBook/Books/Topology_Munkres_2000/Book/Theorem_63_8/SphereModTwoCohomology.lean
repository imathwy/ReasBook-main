module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Theorem_63_8.ModTwoSmallChains
public import Topology_Munkres_2000.Book.Theorem_63_8.ModTwoUniversalCoefficient

public section

noncomputable section

namespace AlgebraicTopology

/-- Helper for Theorem 63.8: positive-dimensional standard spheres have a
one-dimensional top mod-two singular cohomology group. -/
lemma standardSphereTopModTwoCohomologyLinearEquiv (n : ℕ) (hn : 0 < n) :
    Nonempty
      (ModTwoSingularCohomology (TopCat.of (StandardSphere n)) n ≃ₗ[ZMod 2]
        ZMod 2) := by
  -- TODO: use the two-puncture open cover, mod-two small-chain excision, and the
  -- connecting morphism to identify the top homology group with `ZMod 2`, then
  -- apply `nonempty_modTwoSingularCohomologyDualHomologyLinearEquiv`.
  -- The remaining blocker is the coefficient-change proof of small-chain excision.
  sorry

end AlgebraicTopology

end

end
