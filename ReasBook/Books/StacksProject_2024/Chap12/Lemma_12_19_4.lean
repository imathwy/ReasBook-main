import StacksProject_2024.Chap12.Definition_12_19_3

open CategoryTheory
open CategoryTheory.Limits

universe v u

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace FilteredObject

variable (A : FilteredObject C)

-- Internal bridge: transport a filtered object structure across an isomorphism of underlying
-- objects so the public `image` owner can reuse `subobjectFilteredObject` rather than rebuilding
-- its filtration entrywise.
private abbrev ofIso {X : C} (e : A.obj ≅ X) : FilteredObject C where
  obj := X
  filtration := ((Subobject.mapIsoToOrderIso e : Subobject A.obj →o Subobject X)).comp A.filtration

section Pullbacks

variable [HasPullbacks C]
variable (X : Subobject A.obj)

/-- The induced filtered object on a subobject `X ⊆ A`. -/
def subobjectFilteredObject : FilteredObject C where
  obj := X
  filtration := A.filtration.induced X

/-- The inclusion of a filtered subobject into the ambient filtered object. -/
def subobjectInclusion : A.subobjectFilteredObject X ⟶ A where
  hom := X.arrow
  preserves := by
    intro p
    sorry

end Pullbacks

section Quotients

variable [HasZeroMorphisms C] [HasImages C] [HasCokernels C]
variable (X : Subobject A.obj)

/-- The quotient filtered object `A / X`. -/
def quotientFilteredObject : FilteredObject C where
  obj := cokernel X.arrow
  filtration := A.filtration.quotient (cokernel.π X.arrow)

/-- The quotient map from a filtered object to the quotient by a subobject. -/
def toQuotient : A ⟶ A.quotientFilteredObject X where
  hom := cokernel.π X.arrow
  preserves := by
    intro p
    sorry

end Quotients

section PullbacksQuotients

variable [HasPullbacks C] [HasZeroMorphisms C] [HasImages C] [HasCokernels C]
variable (X : Subobject A.obj)

/-- The inclusion of a filtered subobject followed by the quotient map is zero. -/
theorem subobjectInclusion_comp_toQuotient :
    A.subobjectInclusion X ≫ A.toQuotient X = 0 := sorry

end PullbacksQuotients

section Abelian

variable [Abelian C]

namespace Hom

variable {A B : FilteredObject C}

open FilteredObject

/-
Source/core/bridge triage for Lemma 12.19.4:
- source-facing: strictness of a filtered morphism
- core/canonical owners: `FilteredObject.subobjectFilteredObject`,
  `FilteredObject.quotientFilteredObject`, and `Abelian.coimageImageComparison f.hom`
- bridge/view: the filtered `coimage`, filtered `image`, and their lifted comparison morphism
- primitive data: filtration-preserving morphisms are built from stagewise factorization data
- derived API: the filtered comparison morphism and the strictness/isomorphism criterion
-/

/-- The filtered coimage of a morphism, equipped with the quotient filtration coming from the
source via the canonical projection `Abelian.coimage.π`. -/
abbrev coimage (f : A ⟶ B) : FilteredObject C :=
  { obj := Abelian.coimage f.hom
    filtration := A.filtration.quotient (Abelian.coimage.π f.hom) }

/-- The filtered image of a morphism, equipped with the induced filtration coming from the target.
-/
abbrev image (f : A ⟶ B) : FilteredObject C :=
  (B.subobjectFilteredObject (imageSubobject f.hom)).ofIso
    (imageSubobjectIso f.hom ≪≫ (Abelian.imageIsoImage f.hom).symm)

-- Proof sketch: by construction, the filtration on `coim(f)` is the quotient filtration from the
-- source and the filtration on `im(f)` is the induced filtration from the target, so the canonical
-- comparison map yields the stagewise factorization needed for a filtered morphism.
private theorem coimageImageComparison_preserves (f : A ⟶ B) (i : ℤ) :
    ((image f).filtration i).Factors
      (((coimage f).filtration i).arrow ≫ Abelian.coimageImageComparison f.hom) :=
  sorry

/-- The canonical morphism from the filtered coimage of `f` to the filtered image of `f`. -/
def coimageImageComparison (f : A ⟶ B) : coimage f ⟶ image f where
  hom := Abelian.coimageImageComparison f.hom
  preserves := coimageImageComparison_preserves f

-- Proof sketch: the quotient filtration on `coim(f)` and the induced filtration on `im(f)` agree
-- exactly when the stagewise image/intersection equality defining strictness holds. Thus `f` is
-- strict precisely when the canonical comparison is an isomorphism in the filtered category.
/-- Lemma 12.19.4: for a morphism of filtered objects in an abelian category, strictness is
equivalent to the canonical comparison morphism `coim(f) ⟶ im(f)` being an isomorphism of
filtered objects. -/
theorem strict_iff_coimageImageComparison_isIso (f : A ⟶ B) :
    Strict f ↔ IsIso (coimageImageComparison f) := sorry

end Hom
end Abelian
end FilteredObject

end CategoryTheory
