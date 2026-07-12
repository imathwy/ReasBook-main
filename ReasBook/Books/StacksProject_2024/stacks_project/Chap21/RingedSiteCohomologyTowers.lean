import StacksProject_2024.Chap12.Definition_12_31_2
import StacksProject_2024.Chap21.Lemma_21_20_7_core

open CategoryTheory

noncomputable section

universe u v

namespace RingedSite.Hom

section

variable (X : RingedSite.{u, v})

/-- The functor sending a complex of `𝒪_X`-modules to its degree-`i` sections over `U`. -/
abbrev complexSectionDegreeFunctor
    (U : X) (i : ℤ) :
    CochainComplex (ModuleCat X) ℤ ⥤ AddCommGrpCat.{max u v} :=
  (moduleSectionsAsAbelianFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex.eval AddCommGrpCat.{max u v} (ComplexShape.up ℤ) i

/-- For a tower of complexes and a fixed object `U`, this is the inverse system
`n ↦ 𝓕_n^i(U)`. -/
abbrev complexSectionDegreeInverseSystem
    (F : SequentialInverseSystem (CochainComplex (ModuleCat X) ℤ))
    (U : X) (i : ℤ) :
    SequentialInverseSystem AddCommGrpCat.{max u v} :=
  F ⋙ complexSectionDegreeFunctor X U i

/-- The functor sending a complex of `𝒪_X`-modules to the degree-`i` cohomology of its sections
over `U`. -/
abbrev complexSectionCohomologyFunctor
    (U : X) (i : ℤ) :
    CochainComplex (ModuleCat X) ℤ ⥤ AddCommGrpCat.{max u v} :=
  (moduleSectionsAsAbelianFunctor X U).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
    HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.up ℤ) i

/-- For a tower of complexes and a fixed object `U`, this is the inverse system
`n ↦ H^i(𝓕_n^•(U))`. -/
abbrev complexSectionCohomologyInverseSystem
    (F : SequentialInverseSystem (CochainComplex (ModuleCat X) ℤ))
    (U : X) (i : ℤ) :
    SequentialInverseSystem AddCommGrpCat.{max u v} :=
  F ⋙ complexSectionCohomologyFunctor X U i

/-- The functor sending a complex of `𝒪_X`-modules to the underlying abelian sheaf of its
degree-`i` cohomology sheaf. -/
abbrev underlyingAbelianCohomologySheafFunctor
    (i : ℤ) :
    CochainComplex (ModuleCat X) ℤ ⥤ Sheaf X.siteTopology AddCommGrpCat.{max u v} :=
  HomologicalComplex.homologyFunctor (ModuleCat X) (ComplexShape.up ℤ) i ⋙
    underlyingAbelianSheafFunctor X

/-- For a tower of complexes, this is the inverse system
`n ↦ 𝓗^i(𝓕_n^•)` after forgetting to abelian sheaves. -/
abbrev underlyingAbelianCohomologySheafInverseSystem
    (F : SequentialInverseSystem (CochainComplex (ModuleCat X) ℤ))
    (i : ℤ) :
    SequentialInverseSystem (Sheaf X.siteTopology AddCommGrpCat.{max u v}) :=
  F ⋙ underlyingAbelianCohomologySheafFunctor X i

end

end RingedSite.Hom
