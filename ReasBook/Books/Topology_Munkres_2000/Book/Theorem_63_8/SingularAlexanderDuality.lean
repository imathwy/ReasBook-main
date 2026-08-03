module

public import Topology_Munkres_2000.Book.Definition_55_2.Sphere
public import Topology_Munkres_2000.Book.Theorem_62_1.ReducedHomologyZero
public import Topology_Munkres_2000.Book.Theorem_63_8.ModTwoSmallChains
public import Mathlib.Topology.Homotopy.LocallyContractible

public section

noncomputable section

namespace InvarianceOfDomainSupport

/-- Helper for Theorem 63.8: top mod-two singular cohomology of a compact
locally contractible subset of a sphere is reduced mod-two `H₀` of its complement. -/
lemma nonempty_topModTwoAlexanderDuality
    (n : ℕ) (hn : 0 < n) (K : Set (StandardSphere (n + 1)))
    [CompactSpace K] (hLocallyContractible : LocallyContractibleSpace K) :
    Nonempty
      (AlgebraicTopology.ModTwoSingularCohomology (TopCat.of K) n ≃ₗ[ZMod 2]
        reducedHomologyZeroModTwo
          (TopCat.of (Kᶜ : Set (StandardSphere (n + 1))))) := by
  -- TODO: construct the cover-small relative-chain Alexander comparison,
  -- prove compatibility with subdivision, and pass its quasi-isomorphism to
  -- homology.  Compactness and `hLocallyContractible` supply the finite control.
  sorry

end InvarianceOfDomainSupport

end

end
