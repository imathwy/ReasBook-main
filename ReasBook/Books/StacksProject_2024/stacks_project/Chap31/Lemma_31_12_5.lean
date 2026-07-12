import Mathlib
import Mathlib.Data.List.TFAE
import StacksProject_2024.Chap31.Definition_31_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced `IsLocalRing.specializes_closedPoint` as the
-- canonical closed-point specialization theorem. Local precedent in `Chap28/Lemma_28_5_9.lean`
-- specializes this to schemes as `Scheme.specializes_closedPoint`, and Chapter 31 already fixes
-- the sheaf-side owner as `Scheme.Modules.IsReflexive`.

section

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]
variable (ℱ : X.Modules) [ℱ.IsCoherent]

/-- Lemma 31.12.5: let `X` be an integral locally Noetherian scheme and let `ℱ` be a coherent
`\mathcal O_X`-module. Then the following are equivalent: `ℱ` is reflexive; for every point
`x ∈ X`, the stalk `ℱ_x` is a reflexive `\mathcal O_{X, x}`-module; and for every closed point
`x ∈ X`, the stalk `ℱ_x` is a reflexive `\mathcal O_{X, x}`-module. -/
@[stacks 0AY3]
theorem isReflexive_tfae_stalk_and_closedPointStalk :
    List.TFAE
      [ IsReflexive ℱ
      , ∀ x : X, Module.IsReflexive (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)
      , ∀ x : X, x ∈ closedPoints X →
          Module.IsReflexive (X.presheaf.stalk x) ↑(RingedSpace.stalkModuleCat ℱ x)
      ] := sorry

end

end AlgebraicGeometry.Scheme.Modules
