import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import stacks_proof.stacks_project.Chap13.Definition_13_15_3

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.ObjectProperty
open ComplexShape
open DerivedCategory.TStructure

noncomputable section

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory

/- Domain-style sampling for Definition 13.16.2:
- primary domain: bounded-below derived categories and right derived functors.
- inspected owner declarations:
  `boundedBelowDerivedCategory`,
  `single0ToDplus`,
  `single0Plus`,
  `mapBoundedBelowHomotopyCategoryToDerivedBelow`,
  `DerivedCategory.homologyFunctor`.
- owner abstraction: the bounded-below owner `D⁺(-)`, with the chapter’s canonical degree-zero
  bridge `single0ToDplus 𝒜 : 𝒜 ⥤ D⁺(𝒜)`, followed by the canonical inclusion
  `D⁺(𝒝) ⥤ D(𝒝)` and
  `DerivedCategory.homologyFunctor 𝒝 i`.
- primitive data: a chosen bounded-below right derived functor `RF : D⁺(𝒜) ⥤ D⁺(𝒝)`.
- derived API: the source-facing owner `RF.boundedBelowRightDerived i`, whose value on `A` is
  `H^i((RF(A[0])) : D(𝒝))`, together with the canonical degree-zero comparison
  `F ⟶ RF.boundedBelowRightDerived 0`.

Source/core/bridge triage:
- `source-facing`: the textbook functor `R^iF`;
- `core/canonical`: `boundedBelowDerivedCategory`, `DerivedCategory.singleFunctor`,
  `ObjectProperty.ι`, and `DerivedCategory.homologyFunctor`;
- `bridge/view`: the realization `R^iF(A) = H^i((RF(A[0])) : D(𝒝))`.

This item is a source-facing bridge built from the canonical derived-category owners, so the
file should expose the named bounded-below owner `RF.boundedBelowRightDerived i` and derive its
degree-zero input directly from the chapter’s existing `single0ToDplus` bridge and
bounded-localization
owners, rather than adding a second public bridge functor just to package their composite. -/

section

variable {𝒜 : Type u₁} {𝒝 : Type u₂}
  [Category.{v₁} 𝒜] [Category.{v₂} 𝒝]
  [Abelian 𝒜] [Abelian 𝒝]
  [HasDerivedCategory.{w} 𝒜] [HasDerivedCategory.{w} 𝒝]

local notation "plusι" => ObjectProperty.ι (t.plus : ObjectProperty (D(𝒝)))
local notation "H" => DerivedCategory.homologyFunctor 𝒝
local notation "single0" => HomotopyCategory.singleFunctor 𝒜 0

namespace Functor

variable (F : 𝒜 ⥤ 𝒝) [F.Additive]

/-- Definition 13.16.2: for a chosen bounded-below right derived functor model
`RF : D^+(\mathcal A) ⥤ D^+(\mathcal B)`, the `i`-th right derived functor on degree-zero objects
is the canonical composite sending `A` to `H^i((RF(A[0])) : D(\mathcal B))`. Its public owner is
the object-prefix form `RF.boundedBelowRightDerived i`; the degree-zero input remains the chapter's
canonical composite into `D^+(\mathcal A)`, not a second public bridge functor. -/
@[stacks 015A]
abbrev boundedBelowRightDerived (RF : D⁺(𝒜) ⥤ D⁺(𝒝)) (i : ℤ) : 𝒜 ⥤ 𝒝 :=
  single0ToDplus 𝒜 ⋙ RF ⋙ plusι ⋙ DerivedCategory.homologyFunctor 𝒝 i

private noncomputable def single0PlusCompιIso :
    single0Plus 𝒜 ⋙ ObjectProperty.ι (HomotopyCategory.plus 𝒜) ≅ single0 :=
  (HomotopyCategory.plus 𝒜).liftCompιIso single0
    (fun A ↦ by
      simpa using
        (show CochainComplex.plus 𝒜 ((CochainComplex.singleFunctor 𝒜 0).obj A) from
          ⟨0, inferInstance⟩))

/-- The canonical comparison identifying the bounded-below degree-zero object `A[0]` sent through
`F` with the degree-zero object `F(A)[0]` in the derived category. -/
noncomputable def single0PlusToSingleFunctorIso :
    single0Plus 𝒜 ⋙ mapBoundedBelowHomotopyCategoryToDerivedBelow F ⋙ plusι ≅
      F ⋙ DerivedCategory.singleFunctor 𝒝 0 :=
  Functor.isoWhiskerLeft (single0Plus 𝒜)
      (mapBoundedBelowHomotopyCategoryToDerivedBelowCompιIso F) ≪≫
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
          (single0PlusCompιIso (𝒜 := 𝒜))
          (mapHomotopyCategoryToDerived F) ≪≫
        Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerRight (HomotopyCategory.singleFunctorPostcompQuotientIso 𝒜 0)
            (F.mapHomotopyCategory (up ℤ) ⋙ DerivedCategory.Qh) ≪≫
        Functor.associator _ _ _ ≪≫
          Functor.isoWhiskerLeft (CochainComplex.singleFunctor 𝒜 0)
            (Functor.isoWhiskerRight (Functor.mapHomotopyCategoryFactors F (up ℤ))
              DerivedCategory.Qh) ≪≫
          (Functor.associator _ _ _).symm ≪≫
            Functor.isoWhiskerLeft
              (CochainComplex.singleFunctor 𝒜 0 ⋙ F.mapHomologicalComplex (up ℤ))
              (DerivedCategory.quotientCompQhIso 𝒝) ≪≫
            Functor.associator _ _ _ ≪≫
              Functor.isoWhiskerRight
                (HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0)
                DerivedCategory.Q ≪≫
              Functor.associator _ _ _ ≪≫
                Functor.isoWhiskerLeft F (DerivedCategory.singleFunctorIsoCompQ 𝒝 0).symm

section BoundedBelow

variable [(mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜)).IsLocalization
  (boundedBelowHomotopyQuasiIso 𝒜)]
variable (RF : D⁺(𝒜) ⥤ D⁺(𝒝))
variable (α : mapBoundedBelowHomotopyCategoryToDerivedBelow F ⟶
  mapBoundedBelowHomotopyCategoryToDerivedBelow (𝟭 𝒜) ⋙ RF)
variable [RF.IsRightDerivedFunctor α (boundedBelowHomotopyQuasiIso 𝒜)]

/-- The canonical degree-zero comparison
`F ⟶ (A ↦ H^0(RF(A[0])))`
attached to a bounded-below right derived functor `RF`. -/
noncomputable def toBoundedBelowRightDerivedZero :
    F ⟶ RF.boundedBelowRightDerived 0 :=
  (Functor.isoWhiskerLeft F (DerivedCategory.singleFunctorCompHomologyFunctorIso 𝒝 0).symm).hom ≫
    Functor.whiskerRight
      (F.single0PlusToSingleFunctorIso.inv ≫
        Functor.whiskerRight (Functor.whiskerLeft (single0Plus 𝒜) α) plusι)
      (H 0)

end BoundedBelow

end Functor

end

end CategoryTheory
