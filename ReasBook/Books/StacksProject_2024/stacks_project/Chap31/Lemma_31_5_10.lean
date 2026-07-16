import Mathlib
import StacksProject_2024.stacks_project.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.stacks_project.Chap31.Definition_31_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}
variable {ℱ 𝒢 : X.Modules} [ℱ.IsQuasicoherent] [𝒢.IsQuasicoherent]

-- Semantic recall: `lean_leansearch` did not expose a sharper Chapter 31 owner than the generic
-- stalk-local injectivity surface, and local precedent `Lemma_31_2_10` fixes the source-facing
-- API here to `RingedSpace.moduleStalkHom`, `Scheme.Modules.weakAss`, and `Mono φ`.

/-- Lemma 31.5.10: let `X` be a scheme and let `φ : ℱ ⟶ 𝒢` be a morphism of quasi-coherent
`\mathcal O_X`-modules. Assume that for every point `x : X`, either the stalk map
`φ_x : ℱ_x ⟶ 𝒢_x` is injective, or `x` is not a weakly associated point of `ℱ`. Then `φ` is
injective. -/
@[stacks 0AVP]
theorem mono_of_stalkwise_injective_or_not_mem_weakAss
    (φ : ℱ ⟶ 𝒢)
    (hφ : ∀ x : X,
      Function.Injective (RingedSpace.moduleStalkHom x φ) ∨ x ∉ ℱ.weakAss) :
    Mono φ := sorry

end AlgebraicGeometry.Scheme.Modules
