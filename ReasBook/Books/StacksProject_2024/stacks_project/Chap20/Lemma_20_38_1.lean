import StacksProject_2024.Chap20.Lemma_20_37_9
import StacksProject_2024.Chap20.«20_38_0_1»

open CategoryTheory
open CategoryTheory.Limits
open DerivedCategory
open TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry.RingedSpaceCohomology

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

section

variable (X : RingedSpace.{u})
variable [HasExt.{u} (Sheaf (Opens.grothendieckTopology X.carrier) AddCommGrpCat.{u})]

/- Domain-style sampling for Lemma 20.38.1:
- primary domain: the canonical inverse-limit map attached to a lower truncation injective system
  in `Comp(𝒪_X)`;
- sampled owner declarations:
  `LowerTruncationResolutionSystem.intoLimit` and the Chapter 20 cohomology-sheaf notation
  `𝓗[q](X, E)`;
- source/core/bridge triage:
  `source-facing`: the Chapter 20 quasi-isomorphism statement for the canonical inverse-limit map;
  `core/canonical`: `LowerTruncationResolutionSystem.intoLimit`;
  `bridge/view`: the basiswise vanishing hypothesis written directly with `𝓗[q](X, Q.obj F)`.
-/

/-- Lemma 20.38.1: in the situation of `20.38.0.1`, assume `𝓑` is a basis for the topology of
`X`, and for each `U ∈ 𝓑`, each `p > d`, and each `q < 0`, the group
`((𝓗[q](X, Q.obj F)).H' p U)` is zero. Then the canonical map `F ⟶ S.intoLimit` to the
inverse-limit complex of the chosen lower truncation injective system is a quasi-isomorphism. -/
@[stacks 071B]
theorem intoLimit_quasiIso_of_basiswise_negative_cohomologySheaf_vanishing
    (F : CochainComplex (RingedSpace.Modules X) ℤ)
    (S : LowerTruncationResolutionSystem (isInjective (RingedSpace.Modules X)) F)
    (𝓑 : Set (Opens X.carrier))
    (h𝓑 : Opens.IsBasis 𝓑)
    (d : ℕ)
    (hvanish :
      ∀ ⦃U : Opens X.carrier⦄, U ∈ 𝓑 →
        ∀ p : ℕ, d < p →
          ∀ q : ℤ, q < 0 →
            IsZero ((𝓗[q](X, Q.obj F)).H' p U)) :
    QuasiIso S.intoLimit := by
  sorry

end

end AlgebraicGeometry.RingedSpace
