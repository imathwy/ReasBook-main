import StacksProject_2024.Chap30.Lemma_30_16_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Semantic recall: `lean_leansearch` surfaced the canonical `IsProper` morphism owner. Local
Chapter 30 precedent represents sheaf cohomology of a scheme module by
`schemeModuleCohomology`, with the affine-base module structure carried as an explicit typeclass
input. The tag evidence is consistent for Stacks tag `02O6`. -/

variable {A : Type u} [CommRing A] [IsNoetherianRing A]
variable {X : Scheme.{u}}

/-- Lemma 30.19.2: let `S = Spec(A)` with `A` a Noetherian ring, let `f : X ⟶ S` be a
proper morphism, and let `ℱ` be a coherent `\mathcal O_X`-module. Then
`H^i(X, ℱ)` is a finite `A`-module for all `i ≥ 0`, for the source-induced affine-base
module structure on cohomology. -/
@[stacks 02O6]
theorem properCoherentSheafCohomology_finite_of_affine_base
    (f : X ⟶ Spec (CommRingCat.of A)) [IsProper f]
    (ℱ : X.Modules) [ℱ.IsCoherent] (i : ℕ)
    [Module A (schemeModuleCohomology ℱ i)] :
    Module.Finite A (schemeModuleCohomology ℱ i) := sorry

end AlgebraicGeometry.Scheme.Modules
