import StacksProject_2024.Chap20.Lemma_20_27_1
import StacksProject_2024.Chap24.Lemma_24_28_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open ComplexShape
open AlgebraicGeometry
open DifferentialGradedModule
open SheafOfModules
open scoped RingedSpace.Hom RingedSpaceDerivedPullback

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X Y Z : RingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
variable [CategoryWithHomology (RingedSpace.Modules X)]
variable [CategoryWithHomology (RingedSpace.Modules Y)]
variable [CategoryWithHomology (RingedSpace.Modules Z)]
variable [(f^*).Additive] [(g^*).Additive]

/- Domain-style sampling for Lemma 20.27.2:
- primary domain: comparison morphisms for derived pullback on the unbounded derived category of
  `𝒪_X`-modules;
- sampled owner declarations:
  `modulePullbackToDerived`,
  `modulePullbackDerived`,
  `DifferentialGradedModule.leftDerivedPullbackCompIso`,
  `DifferentialGradedModule.leftDerivedPullback_comp_isIso`,
  `modulePullbackDerived_comp_isIso`;
- best owner abstraction: the source-facing owner is the theorem
  `modulePullbackDerived_comp_isIso`, a thin ringed-space specialization of the canonical
  DG-module comparison-is-an-isomorphism theorem, with companion public underived bridge data
  `modulePullbackCompIso`;
- primitive data: composable morphisms `f`, `g` and the canonical underived pullback comparison
  `pullbackComp`;
- derived API: the source-facing public surface is the `IsIso` instance on the canonical
  comparison morphism supplied by `DifferentialGradedModule.leftDerivedPullbackCompIso`; the file
  does not re-export that isomorphism as new public data while its witness remains upstream
  sorry-backed.

Source/core/bridge triage:
- `source-facing`: the comparison-is-an-isomorphism statement for
  `(L(g)^*) ⋙ (L(f)^*) ⟶ L((f ≫ g))^*`;
- `core/canonical`: `modulePullbackToDerived`, `modulePullbackDerived`,
  `DifferentialGradedModule.leftDerivedPullbackCompIso`, and
  `DifferentialGradedModule.leftDerivedPullback_comp_isIso`;
- `bridge/view`: the underived composite pullback isomorphism `modulePullbackCompIso`.
-/

/-- The canonical underived pullback-composition isomorphism on module sheaves over ringed
spaces. -/
noncomputable abbrev modulePullbackCompIso :
    (f ≫ g)^* ≅ g^* ⋙ f^* :=
  ((pullbackComp
      (RingedSpace.Hom.toRingCatSheafHom g)
      (RingedSpace.Hom.toRingCatSheafHom f)).symm :
    (f ≫ g)^* ≅ g^* ⋙ f^*)

noncomputable instance modulePullbackComp_additive : ((f ≫ g)^*).Additive :=
  Functor.additive_of_iso (modulePullbackCompIso f g).symm

/-- Lemma 20.27.2: for composable morphisms of ringed spaces `f : X ⟶ Y` and `g : Y ⟶ Z`, the
canonical comparison morphism `L(g)^* ⋙ L(f)^* ⟶ L((f ≫ g))^*` induced by the underived
pullback-composition isomorphism `modulePullbackCompIso f g` is an isomorphism on `D(𝒪_Z)`. -/
@[stacks 0D5S]
instance modulePullbackDerived_comp_isIso :
    IsIso
      (DifferentialGradedModule.leftDerivedPullbackCompIso
        (f^*) (g^*) ((f ≫ g)^*) (modulePullbackCompIso f g)).hom := by
  simpa using
    (DifferentialGradedModule.leftDerivedPullback_comp_isIso
      (f^*) (g^*) ((f ≫ g)^*) (modulePullbackCompIso f g))

end

end AlgebraicGeometry.RingedSpace
