import Mathlib
import StacksProject_2024.Chap17.Definition_17_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme-module restriction owners
-- `Scheme.Modules.restrict` and `Scheme.Modules.restrictFunctor`. Local extension statements
-- record agreement over an open by saying the restricted subobject inclusion is an isomorphism,
-- and record extension of morphisms by equality after applying `restrictFunctor`.

/-- Lemma 30.10.6: let `X` be a locally Noetherian scheme, let `ℱ` and `𝒢` be coherent
`\mathcal O_X`-modules, let `U ⊆ X` be open, and let
`φ : ℱ|_U ⟶ 𝒢|_U` be an `\mathcal O_U`-module map. Then there is a coherent submodule
`ℱ' ⊆ ℱ` whose restriction to `U` agrees with `ℱ|_U`, and `φ` extends to a morphism
`ℱ' ⟶ 𝒢`. -/
@[stacks 0FD0]
theorem exists_coherentSubobject_extension_of_restrict_hom
    (ℱ 𝒢 : X.Modules) [ℱ.IsCoherent] [𝒢.IsCoherent]
    (U : X.Opens)
    (φ : ((Scheme.Modules.restrictFunctor U.ι).obj ℱ) ⟶
      ((Scheme.Modules.restrictFunctor U.ι).obj 𝒢)) :
    ∃ (ℱ' : Subobject ℱ), ∃ (_ : ((ℱ' : X.Modules)).IsCoherent),
      ∃ (_ : IsIso ((Scheme.Modules.restrictFunctor U.ι).map ℱ'.arrow)),
        ∃ φ' : (ℱ' : X.Modules) ⟶ 𝒢,
          (Scheme.Modules.restrictFunctor U.ι).map φ' =
            (Scheme.Modules.restrictFunctor U.ι).map ℱ'.arrow ≫ φ := sorry

end AlgebraicGeometry.Scheme.Modules
