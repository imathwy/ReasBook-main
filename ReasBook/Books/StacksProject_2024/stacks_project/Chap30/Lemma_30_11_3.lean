import StacksProject_2024.Chap30.Lemma_30_11_2

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [MonoidalClosed X.Modules]
variable {ℱ 𝒢 : X.Modules} [ℱ.IsCoherent] [𝒢.IsCoherent]

attribute [local instance] isCoherent_internalHom

-- Semantic recall: `lean_leansearch` surfaced the existing scheme-module Hom owner
-- `AlgebraicGeometry.Scheme.Modules.Hom`; local Chapter 30 precedent instead exposes the closed
-- monoidal internal Hom as `((ihom ℱ).obj 𝒢)` and the source `(S_k)` condition through
-- `Scheme.Modules.satisfiesSerreConditionS`.

/-- Lemma 30.11.3 (1): if `𝒢` has property `(S_1)`, then the internal Hom sheaf
`\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F,\mathcal G)` has property `(S_1)`. -/
@[stacks 0AXQ]
theorem satisfiesSerreConditionS_one_internalHom_of_satisfiesSerreConditionS_one
    (h𝒢 : satisfiesSerreConditionS 𝒢 1) :
    satisfiesSerreConditionS ((ihom ℱ).obj 𝒢) 1 := sorry

/-- Lemma 30.11.3 (2): if `𝒢` has property `(S_2)`, then the internal Hom sheaf
`\mathcal H\!\mathit{om}_{\mathcal O_X}(\mathcal F,\mathcal G)` has property `(S_2)`. -/
@[stacks 0AXQ]
theorem satisfiesSerreConditionS_two_internalHom_of_satisfiesSerreConditionS_two
    (h𝒢 : satisfiesSerreConditionS 𝒢 2) :
    satisfiesSerreConditionS ((ihom ℱ).obj 𝒢) 2 := sorry

end AlgebraicGeometry.Scheme.Modules
