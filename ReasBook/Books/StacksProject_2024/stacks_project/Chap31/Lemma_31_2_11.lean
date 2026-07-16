import StacksProject_2024.stacks_project.Chap10.Definition_10_72_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_2_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
variable {ℱ 𝒢 : X.Modules} [ℱ.IsCoherent] [𝒢.IsQuasicoherent]

-- Semantic recall: the source-facing owner here is the associated-points refinement of a
-- stalkwise isomorphism criterion. The canonical local owners reused below are
-- `RingedSpace.moduleStalkHom`, `moduleDepth`, and `associatedPoints`.

/-- Lemma 31.2.11: let `X` be a locally Noetherian scheme and let `φ : ℱ ⟶ 𝒢` be a morphism of
quasi-coherent `\mathcal O_X`-modules. Assume `ℱ` is coherent and that for every point `x : X`
either the stalk map `φ_x : ℱ_x ⟶ 𝒢_x` is an isomorphism, or the stalk `ℱ_x` has depth at least
`2` and `x` is not an associated point of `𝒢`. Then `φ` is an isomorphism. -/
@[stacks 0AVM]
theorem isIso_of_stalkwise_isIso_or_moduleDepth_ge_two_and_not_mem_associatedPoints
    (φ : ℱ ⟶ 𝒢)
    (hφ : ∀ x : X,
      IsIso (moduleStalkHom x φ) ∨
        ((2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (stalkModuleCat ℱ x) ∧
          x ∉ associatedPoints 𝒢)) :
    IsIso φ := sorry

/-- Companion bridge for Lemma 31.2.11: it is enough to know that the stalk map `φ_x` is an
isomorphism at the associated points of `\mathcal G`, and that away from those associated points
the stalk `\mathcal F_x` has depth at least `2`. -/
theorem isIso_of_stalkwise_isIso_on_associatedPoints_and_moduleDepth_ge_two_off_associatedPoints
    (φ : ℱ ⟶ 𝒢)
    (hiso : ∀ x : X, x ∈ associatedPoints 𝒢 → IsIso (moduleStalkHom x φ))
    (hdepth : ∀ x : X, x ∉ associatedPoints 𝒢 →
      (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (stalkModuleCat ℱ x)) :
    IsIso φ := by
  refine isIso_of_stalkwise_isIso_or_moduleDepth_ge_two_and_not_mem_associatedPoints φ ?_
  intro x
  by_cases hx : x ∈ associatedPoints 𝒢
  · exact Or.inl (hiso x hx)
  · exact Or.inr ⟨hdepth x hx, hx⟩

end AlgebraicGeometry.Scheme.Modules
