import Mathlib
import StacksProject_2024.Chap17.Definition_17_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory TopologicalSpace
open AlgebraicGeometry
open scoped ModuleRestriction

noncomputable section

universe u

namespace SheafOfModules

/- Domain-style sampling for Lemma 17.9.4:
- primary domain: local surjectivity criteria for morphisms of finite-type `\mathcal O_X`-module
  sheaves on a ringed space;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.IsFiniteType`,
  `AlgebraicGeometry.RingedSpace.moduleRestrictionMap`,
  `AlgebraicGeometry.RingedSpace.moduleStalkMap`;
- best owner abstraction: the bundled module category `RingedSpace.Modules X`, with restriction to
  `U` expressed by the owner notation `φ |_ U` for `RingedSpace.moduleRestrictionMap U φ` and
  stalkwise surjectivity expressed by `RingedSpace.moduleStalkMap x φ`;
- primitive data: the morphism `φ : 𝒢 ⟶ ℱ`, the point `x : X`, and stalkwise surjectivity at
  `x`;
- derived API: the restricted morphism on `U` and the resulting epimorphism witness.

Source/core/bridge triage:
- `source-facing`: after shrinking around `x`, the restricted morphism `φ |_ U` is surjective;
- `core/canonical`: `Epi (φ |_ U)`;
- `bridge/view`: `Function.Surjective (RingedSpace.moduleStalkMap x φ)`. -/

variable {X : RingedSpace.{u}}
variable {𝒢 ℱ : RingedSpace.Modules X}

-- Proof sketch: choose finitely many local generators of `ℱ` near `x`; surjectivity of the
-- underlying additive stalk map gives local lifts of the germs of those generators, and after
-- shrinking once more these lifts make the restricted morphism `φ |_ U` an epimorphism of
-- `𝒪_U`-modules.
/-- Lemma 17.9.4: if `ℱ` is of finite type and the induced map on stalks
`φ_x : 𝒢_x → ℱ_x` at `x` is surjective, then there exists an open neighbourhood `U` of `x` such
that the restricted morphism `φ |_ U : 𝒢|_U → ℱ|_U` is surjective, i.e. an epimorphism of
`𝒪|_U`-modules. -/
theorem exists_open_neighborhood_epi_restriction_of_stalk_surjective
    (φ : 𝒢 ⟶ ℱ) (x : X) [ℱ.IsFiniteType]
    (hφx : Function.Surjective (RingedSpace.moduleStalkMap x φ)) :
    ∃ (U : Opens X) (_ : x ∈ U),
      Epi (φ |_ U) := sorry

end SheafOfModules
