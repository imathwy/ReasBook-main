import StacksProject_2024.stacks_project.Chap17.Lemma_17_12_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced the ambient coherent-module owner on
-- `RingedSpace.Modules`, and Chapter 17 introduces coherence as the source-facing owner property.
-- This item records the scheme-level recalls of that owner surface.

variable {X : Scheme.{u}}
variable {ℱ 𝒢 : X.Modules}

/-- Lemma 30.9.2 (1): if `φ : ℱ ⟶ 𝒢` is a morphism of coherent `\mathcal O_X`-modules on a
scheme `X`, then `kernel φ` is coherent. -/
theorem isCoherent_kernel
    (φ : ℱ ⟶ 𝒢) [ℱ.IsCoherent] [𝒢.IsCoherent] :
    (kernel φ).IsCoherent := by
  exact RingedSpace.isCoherent_kernel φ

/-- Lemma 30.9.2 (2): if `φ : ℱ ⟶ 𝒢` is a morphism of coherent `\mathcal O_X`-modules on a
scheme `X`, then `cokernel φ` is coherent. -/
theorem isCoherent_cokernel
    (φ : ℱ ⟶ 𝒢) [ℱ.IsCoherent] [𝒢.IsCoherent] :
    (cokernel φ).IsCoherent := by
  exact RingedSpace.isCoherent_cokernel φ

variable {S : ShortComplex X.Modules}

/-- Lemma 30.9.2 (3): in a short exact sequence of `\mathcal O_X`-modules on a scheme `X`, if the
outer terms are coherent then the middle term is coherent. -/
theorem isCoherent_of_shortExact_of_outer
    (hS : S.ShortExact) [S.X₁.IsCoherent] [S.X₃.IsCoherent] :
    S.X₂.IsCoherent := by
  exact RingedSpace.isCoherent_of_shortExact_of_outer hS

/- Lemma 30.9.2 (4): for a scheme `X`, the category `Coh(\mathcal O_X)` of coherent
`\mathcal O_X`-modules is abelian. This is the canonical instance on
`RingedSpace.Coh X.toRingedSpace`, so this item is a direct recall rather than a new wrapper. -/
example : Abelian (RingedSpace.Coh X.toRingedSpace) := by
  letI :
      (RingedSpace.SheafOfModules.isCoherent X.toRingedSpace).IsClosedUnderFiniteProducts :=
    inferInstance
  change Abelian (RingedSpace.SheafOfModules.isCoherent X.toRingedSpace).FullSubcategory
  infer_instance

end AlgebraicGeometry.Scheme.Modules
