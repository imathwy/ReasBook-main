import Mathlib
import Mathlib.Algebra.Homology.CochainComplexPlus
import Mathlib.Algebra.Homology.HomotopyCategory.Triangulated
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import Mathlib.CategoryTheory.Triangulated.Subcategory
import stacks_proof.stacks_project.Chap13.Definition_13_8_1
import stacks_proof.stacks_project.Chap13.Definition_13_11_3
import stacks_proof.stacks_project.Chap13.Lemma_13_10_6
import stacks_proof.stacks_project.Chap13.Lemma_13_11_6
import stacks_proof.stacks_project.Chap13.Situation_13_14_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory.TStructure
open scoped CategoryTheory

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {𝒜 : Type u₁} {ℬ : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} ℬ]
  [Abelian 𝒜] [Abelian ℬ]
  [HasDerivedCategory.{w} ℬ]
  (F : 𝒜 ⥤ ℬ) [F.Additive]

/- 
Domain-style sampling for Situation 13.15.1:
- primary domain: triangulated/localization structures attached to the three canonical functors
  `K(\mathcal A) ⥤ D(\mathcal B)`, `K^+(\mathcal A) ⥤ D^+(\mathcal B)`, and
  `K^-(\mathcal A) ⥤ D^-(\mathcal B)` induced by an additive functor `F : 𝒜 ⥤ ℬ`;
- sampled owner declarations:
  `Functor.CommShift ℤ`,
  `Functor.IsTriangulated`,
  `MorphismProperty.IsSaturatedMultiplicativeSystem`,
  `MorphismProperty.IsCompatibleWithTriangulation`;
- best owner abstraction: the source-facing mathematical content here is the construction of the
  three functors themselves. The exact-localization clauses are not new primitive data; they are
  direct owner assumptions on those functors and on the corresponding quasi-isomorphism classes.

Primitive-vs-derived split:
- primitive data: `mapHomotopyCategoryToDerived F`, together with the bounded-below and
  bounded-above homotopy lifts `mapBoundedBelowHomotopyCategory F` and
  `mapBoundedAboveHomotopyCategory F`, plus the corresponding landing theorems for the quotient
  functor;
- derived API: the bounded derived functors in this file should be expressed through those owner
  declarations, together with the resulting comparison isomorphisms to the ambient unbounded
  functor.

Source/core/bridge triage:
- `source-facing`: the three induced functors attached to `F`;
- `core/canonical`: the four owner classes listed above;
- `bridge/view`: the bounded-below homotopy lift, the bounded localization theorem
  for `DerivedCategory.Qh`, and the bounded-above landing lemma used below.
-/

/-- The composite `K(\mathcal A) ⟶ K(\mathcal B) ⟶ D(\mathcal B)` induced by the additive
functor `F`. -/
abbrev mapHomotopyCategoryToDerived :
    HomotopyCategory 𝒜 (up ℤ) ⥤ DerivedCategory ℬ :=
  F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh

/-- The composite
`K^+(\mathcal A) ⟶ K^+(\mathcal B) ⟶ D^+(\mathcal B)`
induced by the additive functor `F`. -/
abbrev mapBoundedBelowHomotopyCategoryToDerivedBelow :
    K⁺(𝒜) ⥤ D⁺(ℬ) :=
  mapBoundedBelowHomotopyCategory F ⋙ mapBoundedBelowHomotopyToDerivedBelow

/-- The canonical bounded-below comparison with the ambient functor
`K(\mathcal A) ⟶ D(\mathcal B)`. -/
noncomputable abbrev mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso :
    mapBoundedBelowHomotopyCategoryToDerivedBelow F ⋙
      ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ))) ≅
    ObjectProperty.ι (HomotopyCategory.plus 𝒜) ⋙ mapHomotopyCategoryToDerived F :=
  (Functor.associator
      (mapBoundedBelowHomotopyCategory F)
      mapBoundedBelowHomotopyToDerivedBelow
      (ObjectProperty.ι (t.plus : ObjectProperty (D(ℬ))))).symm ≪≫
    Functor.isoWhiskerLeft
      (mapBoundedBelowHomotopyCategory F)
      (ObjectProperty.liftCompιIso
        (t.plus : ObjectProperty (D(ℬ)))
        (ObjectProperty.ι (HomotopyCategory.plus ℬ) ⋙ DerivedCategory.Qh)
        (fun X ↦ by simpa using qh_obj_mem_t_plus X)) ≪≫
    Functor.associator
      (mapBoundedBelowHomotopyCategory F)
      (ObjectProperty.ι (HomotopyCategory.plus ℬ))
      DerivedCategory.Qh ≪≫
    Functor.isoWhiskerRight
      ((HomotopyCategory.plus ℬ).liftCompιIso
        ((HomotopyCategory.plus 𝒜).ι ⋙ F.mapHomotopyCategory (up ℤ))
        (mapHomotopyCategory_obj_mem_boundedBelow F))
      DerivedCategory.Qh

/-- The composite `K^-(\mathcal A) ⟶ D^-(\mathcal B)` induced by the additive functor `F`. -/
abbrev mapBoundedAboveHomotopyCategoryToDerivedAbove :
    K⁻(𝒜) ⥤ D⁻(ℬ) :=
  mapBoundedAboveHomotopyCategory F ⋙ mapBoundedAboveHomotopyToDerivedAbove

/- Situation 13.15.1 uses the canonical exact-localization owners directly on the three functors
defined above and on the corresponding quasi-isomorphism classes. -/
#check (mapHomotopyCategoryToDerived F).CommShift ℤ
#check (mapHomotopyCategoryToDerived F).IsTriangulated
#check IsSaturatedMultiplicativeSystem (HomotopyCategory.quasiIso 𝒜 (up ℤ))
#check (HomotopyCategory.quasiIso 𝒜 (up ℤ)).IsCompatibleWithTriangulation
#check (mapBoundedBelowHomotopyCategoryToDerivedBelow F).CommShift ℤ
#check (mapBoundedBelowHomotopyCategoryToDerivedBelow F).IsTriangulated
#check IsSaturatedMultiplicativeSystem (Qis⁺(𝒜))
#check (Qis⁺(𝒜)).IsCompatibleWithTriangulation
#check (mapBoundedAboveHomotopyCategoryToDerivedAbove F).CommShift ℤ
#check (mapBoundedAboveHomotopyCategoryToDerivedAbove F).IsTriangulated
#check IsSaturatedMultiplicativeSystem (Qis⁻(𝒜))
#check (Qis⁻(𝒜)).IsCompatibleWithTriangulation

end

end CategoryTheory
