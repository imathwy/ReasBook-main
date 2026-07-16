import Mathlib
import StacksProject_2024.stacks_project.Chap17.ModuleRestrictionAndStalks
import StacksProject_2024.stacks_project.Chap30.Definition_30_11_1
import StacksProject_2024.stacks_project.Chap31.Lemma_31_11_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry ENat

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IsIntegral X] [IsLocallyNoetherian X]
variable {ℱ 𝒢 : X.Modules} [ℱ.IsCoherent] [𝒢.IsQuasicoherent] [IsTorsionFree 𝒢]

-- Semantic recall: this is the scheme-side source-facing bridge for the torsion-free specialization
-- of the local isomorphism criterion, so the public surface should reuse the established Chapter 31
-- stalk owners `moduleStalkHom` and `stalkModuleCat`, together with the Chapter 30 depth owner
-- `moduleDepth` and the Chapter 31 torsion-free owner `IsTorsionFree`.

/-- Lemma 31.11.13: let `X` be an integral locally Noetherian scheme. Let
`φ : \mathcal{F} \to \mathcal{G}` be a map of quasi-coherent `\mathcal{O}_X`-modules. Assume
`\mathcal{F}` is coherent, `\mathcal{G}` is torsion free, and that for every point `x : X` either
the stalk map `φ_x : \mathcal{F}_x \to \mathcal{G}_x` is an isomorphism, or the stalk
`\mathcal{F}_x` has depth at least `2`. Then `φ` is an isomorphism. -/
@[stacks 0AVS]
theorem isIso_of_stalkwise_isIso_or_moduleDepth_ge_two_of_isTorsionFree
    (φ : ℱ ⟶ 𝒢)
    (hφ : ∀ x : X,
      IsIso (moduleStalkHom x φ) ∨
        (2 : ℕ∞) ≤ moduleDepth (X.presheaf.stalk x) (stalkModuleCat ℱ x)) :
    IsIso φ := sorry

end AlgebraicGeometry.Scheme.Modules
