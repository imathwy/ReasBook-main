import Mathlib
import StacksProject_2024.stacks_project.Chap17.Definition_17_12_1
import StacksProject_2024.stacks_project.Chap31.Definition_31_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

-- Semantic recall: `lean_leansearch` surfaced the full-subcategory owner API around
-- `CategoryTheory.ObjectProperty.FullSubcategory`; local Chapter 17 precedent fixes the ambient
-- coherent category as `RingedSpace.Coh X.toRingedSpace`, so coherent reflexive modules are best
-- formalized as an object-property full subcategory of `Coh(\mathcal O_X)`.

section

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]
variable [MonoidalCategory X.Modules] [BraidedCategory X.Modules] [MonoidalClosed X.Modules]

local notation "CohX" => RingedSpace.Coh X.toRingedSpace

/-- The object property on `Coh(\mathcal O_X)` selecting the reflexive coherent
`\mathcal O_X`-modules. -/
@[stacks 0EBH]
abbrev reflexiveCohProperty : ObjectProperty CohX :=
  fun ℱ : CohX ↦
    letI : ℱ.1.IsCoherent := ℱ.2
    IsReflexive ℱ.1

/-- The category of coherent reflexive `\mathcal O_X`-modules on `X`, viewed as the full
subcategory of `Coh(\mathcal O_X)` cut out by reflexivity. -/
@[stacks 0EBH]
abbrev ReflexiveCoh :=
  (reflexiveCohProperty X).FullSubcategory

/-- The inclusion of coherent reflexive `\mathcal O_X`-modules into
`Coh(\mathcal O_X)`. -/
@[stacks 0EBH]
abbrev reflexiveCohInclusion : ReflexiveCoh X ⥤ CohX :=
  (reflexiveCohProperty X).ι

/-- Remark 31.12.9: for an integral locally Noetherian scheme `X`, taking reflexive hulls gives a
left adjoint to the inclusion of the category of coherent reflexive `\mathcal O_X`-modules into
`Coh(\mathcal O_X)`. -/
@[stacks 0EBH]
theorem reflexiveHull_leftAdjoint_to_inclusion :
    ∃ L : CohX ⥤ ReflexiveCoh X,
      Nonempty (L ⊣ reflexiveCohInclusion X) := sorry

/-- The category of coherent reflexive `\mathcal O_X`-modules is preadditive. -/
@[stacks 0EBH, instance]
instance instPreadditiveReflexiveCoh :
    Preadditive (ReflexiveCoh X) :=
  inferInstance

/-- The category of coherent reflexive `\mathcal O_X`-modules has kernels. -/
@[stacks 0EBH, instance]
instance instHasKernelsReflexiveCoh :
    HasKernels (ReflexiveCoh X) := sorry

/-- The category of coherent reflexive `\mathcal O_X`-modules has cokernels. -/
@[stacks 0EBH, instance]
instance instHasCokernelsReflexiveCoh :
    HasCokernels (ReflexiveCoh X) := sorry

end

end AlgebraicGeometry.Scheme.Modules
