import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import StacksProject_2024.stacks_project.Chap24.Lemma_24_25_12

open CategoryTheory
open CategoryTheory.Limits
open ComplexShape
open DerivedCategory

noncomputable section

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace RingedSite
namespace DifferentialGradedAlgebra

section

variable {X : RingedSite.{u, v}} (𝒜 : DifferentialGradedAlgebra X)

-- Semantic search note: `lean_leansearch` surfaced the canonical coproduct/product owners
-- `HasCoproducts`, `HasProducts`, `IsColimit`, and `IsLimit`; the Chapter 24 specialization below
-- is aligned with the existing derived-category bridge file `Chap19/Lemma_19_13_4.lean`.

/-- Lemma 24.26.8 (1): let `(\mathcal C, \mathcal O)` be a ringed site, and let
`(\mathcal A, \mathrm d)` be a sheaf of differential graded algebras on it. Then the derived
category `D(\mathcal A, \mathrm d)` has direct sums, formalized as arbitrary coproducts. -/
@[stacks 0FT9]
theorem derivedCategory_hasCoproducts :
    HasCoproducts (DerivedCategory 𝒜.moduleCat) := sorry

/-- Lemma 24.26.8 (2): in the canonical derived-category API, direct sums in
`D(\mathcal A, \mathrm d)` are obtained by taking termwise direct sums of representative
complexes of differential graded `\mathcal A`-modules; equivalently, the localization functor
`Q` preserves these coproducts. -/
@[stacks 0FT9]
theorem derivedCategory_Q_preserves_coproduct
    {J : Type w} (K : J → CochainComplex 𝒜.moduleCat ℤ)
    [HasCoproduct K] :
    PreservesColimit (Discrete.functor K) DerivedCategory.Q := sorry

/-- Lemma 24.26.8 (3): let `(\mathcal C, \mathcal O)` be a ringed site, and let
`(\mathcal A, \mathrm d)` be a sheaf of differential graded algebras on it. Then the derived
category `D(\mathcal A, \mathrm d)` has products. -/
@[stacks 0FT9]
theorem derivedCategory_hasProducts :
    HasProducts (DerivedCategory 𝒜.moduleCat) := sorry

/-- Lemma 24.26.8 (4): in the canonical derived-category API, products in
`D(\mathcal A, \mathrm d)` are obtained by taking termwise products of K-injective representative
complexes of differential graded `\mathcal A`-modules; equivalently, the localization functor
`Q` preserves these products. -/
@[stacks 0FT9]
theorem derivedCategory_Q_preserves_product_of_kInjective
    {J : Type w} (I : J → CochainComplex 𝒜.moduleCat ℤ)
    [HasProduct I] [∀ j, (I j).IsKInjective] :
    PreservesLimit (Discrete.functor I) DerivedCategory.Q := sorry

end

end DifferentialGradedAlgebra
end RingedSite
