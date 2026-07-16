import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Stalk
import StacksProject_2024.stacks_project.Chap17.Definition_17_4_1
import StacksProject_2024.stacks_project.Chap17.ModuleRestrictionAndStalks

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

noncomputable section

universe u

open scoped ModuleRestriction

namespace SheafOfModules

/- Domain-style sampling for Lemma 17.9.4:
- primary domain: local surjectivity criteria for morphisms of finite-type `\mathcal O_X`-module
  sheaves on a ringed space;
- inspected owner declarations:
  `RingedSpace.Modules`,
  `SheafOfModules.IsFiniteType`,
  `AlgebraicGeometry.RingedSpace.moduleRestrictionMap`,
  `AlgebraicGeometry.RingedSpace.moduleStalkHom`,
  `AlgebraicGeometry.RingedSpace.moduleStalkMap`;
- best owner abstraction: the bundled module category `RingedSpace.Modules X`, with restriction to
  `U` expressed by the owner notation `φ |_ U` and the stalk morphism expressed by
  `RingedSpace.moduleStalkHom x φ`;
- primitive data: the morphism `φ : 𝒢 ⟶ ℱ`, the point `x : X`, and stalkwise surjectivity at
  `x`, equivalently epimorphy of `RingedSpace.moduleStalkHom x φ`;
- derived API: the restricted morphism on `U`, the resulting epimorphism witness, and the
  source-facing surjectivity reformulation using `RingedSpace.moduleStalkMap`.

Source/core/bridge triage:
- `source-facing`: after shrinking around `x`, the restricted morphism `φ |_ U` is surjective;
- `core/canonical`: `Epi (φ |_ U)`;
- `bridge/view`: `Function.Surjective (RingedSpace.moduleStalkMap x φ)`, derived from the stalk
  owner morphism `RingedSpace.moduleStalkHom x φ`. -/

variable {X : RingedSpace.{u}}
variable {𝒢 ℱ : RingedSpace.Modules X}

/-- Owner-level companion to Lemma 17.9.4: if `ℱ` is of finite type and the induced stalk
morphism `𝒢_x ⟶ ℱ_x` is an epimorphism in `ModuleCat (𝒪_{X,x})`, then after shrinking around `x`
the restricted morphism `φ |_ U : 𝒢|_U → ℱ|_U` is an epimorphism. -/
theorem exists_open_neighborhood_epi_restriction_of_stalk_epi
    (φ : 𝒢 ⟶ ℱ) (x : X) [ℱ.IsFiniteType]
    (hφx : Epi (RingedSpace.moduleStalkHom x φ)) :
    ∃ (U : Opens X) (_ : x ∈ U),
      Epi (φ |_ U) := by
  sorry

/-- Lemma 17.9.4: if `ℱ` is of finite type and the induced map on stalks
`φ_x : 𝒢_x → ℱ_x` at `x` is surjective, then there exists an open neighbourhood `U` of `x` such
that the restricted morphism `φ |_ U : 𝒢|_U → ℱ|_U` is surjective, i.e. an epimorphism of
`𝒪|_U`-modules. -/
theorem exists_open_neighborhood_epi_restriction_of_stalk_surjective
    (φ : 𝒢 ⟶ ℱ) (x : X) [ℱ.IsFiniteType]
    (hφx : Function.Surjective (RingedSpace.moduleStalkMap x φ)) :
    ∃ (U : Opens X) (_ : x ∈ U),
      Epi (φ |_ U) := by
  have hφx' : Epi (RingedSpace.moduleStalkHom x φ) := by
    simpa [RingedSpace.moduleStalkHom] using
      (ModuleCat.epi_iff_surjective (RingedSpace.moduleStalkHom x φ)).2 hφx
  exact exists_open_neighborhood_epi_restriction_of_stalk_epi φ x hφx'

end SheafOfModules
