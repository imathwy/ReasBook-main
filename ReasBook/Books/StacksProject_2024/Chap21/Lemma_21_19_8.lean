import Mathlib
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksProject_2024.Chap12.Lemma_12_10_3
import StacksProject_2024.Chap13.Lemma_13_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Opposite

noncomputable section

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.Sheaf

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

/- Domain-style sampling for Lemma 21.19.8 in the abelian-sheaf/derived-category domain:
- sampled owner declarations:
  `derivedCategoryCohomologyInProperty`,
  `DerivedCategoryWithCohomologyIn`,
  `ObjectProperty.lift`,
  `ObjectProperty.weakSerreSubcategory_inclusion_exact`;
- best owner abstraction: the Chapter 13 owner
  `derivedCategoryCohomologyInProperty` together with its full-subcategory owner
  `DerivedCategoryWithCohomologyIn`;
- primitive data: the source-facing torsion object property on `Sheaf J AddCommGrpCat`;
- derived API: the full subcategory of torsion sheaves, its exact inclusion into all abelian
  sheaves, and the lifted derived comparison functor into `DerivedCategoryWithCohomologyIn`;
- source/core/bridge triage:
  `source-facing`: `torsionAbelianSheafProperty` and the torsion derived comparison equivalence;
  `core/canonical`: `derivedCategoryCohomologyInProperty`, `DerivedCategoryWithCohomologyIn`, and
    `weakSerreSubcategory_inclusion_exact`;
  `bridge/view`: the comparison functor built from `Functor.mapDerivedCategory` and
    `ObjectProperty.lift`.

Accordingly, the local duplicate definitions of
`derivedCategoryCohomologyInProperty` and `DerivedCategoryWithCohomologyIn` are removed in favor
of the chapter-level owners. -/

/-- The object property on `Ab(\mathcal C)` consisting of torsion abelian sheaves, i.e. sheaves
whose section groups over every object of the site are torsion abelian groups. -/
abbrev torsionAbelianSheafProperty (J : GrothendieckTopology C) :
    ObjectProperty (Sheaf J AddCommGrpCat.{max u v}) :=
  fun F ↦ ∀ U : C, AddMonoid.IsTorsion (F.obj.obj (op U))

local notation "TorsionProperty" => torsionAbelianSheafProperty J
local notation "TorsionSheaf" => TorsionProperty.FullSubcategory

-- Proof sketch: unfold `torsionAbelianSheafProperty`; the displayed equivalence is definitional.
/-- Membership in `torsionAbelianSheafProperty J` means that every section group of the sheaf is
torsion. -/
theorem mem_torsionAbelianSheafProperty_iff
    (F : Sheaf J AddCommGrpCat.{max u v}) :
    TorsionProperty F ↔
      ∀ U : C, AddMonoid.IsTorsion (F.obj.obj (op U)) :=
  Iff.rfl

/-- Torsion abelian sheaves form a LinearRepresentations_Serre_1977 subcategory of `Ab(\mathcal C)`. -/
instance torsionAbelianSheafProperty_isSerreClass :
    TorsionProperty.IsSerreClass := sorry

/-- Torsion abelian sheaves are closed under finite products. -/
instance torsionAbelianSheafProperty_isClosedUnderFiniteProducts :
    TorsionProperty.IsClosedUnderFiniteProducts := sorry

/-- Torsion abelian sheaves are closed under finite coproducts. -/
instance torsionAbelianSheafProperty_isClosedUnderFiniteCoproducts :
    TorsionProperty.IsClosedUnderFiniteCoproducts := sorry

/-- The inclusion of torsion abelian sheaves preserves finite limits. -/
instance torsionAbelianSheafInclusion_preservesFiniteLimits :
    PreservesFiniteLimits TorsionProperty.ι :=
  (exactFunctor_iff TorsionProperty.ι).1
    (weakSerreSubcategory_inclusion_exact TorsionProperty : _)
    |>.1

/-- The inclusion of torsion abelian sheaves preserves finite colimits. -/
instance torsionAbelianSheafInclusion_preservesFiniteColimits :
    PreservesFiniteColimits TorsionProperty.ι :=
  (exactFunctor_iff TorsionProperty.ι).1
    (weakSerreSubcategory_inclusion_exact TorsionProperty : _)
    |>.2

-- Proof sketch: the inclusion `TorsionSheaf ⥤ AbSheaf` is exact, so the induced functor on
-- derived categories commutes with cohomology. Since every object of `TorsionSheaf` is torsion,
-- every cohomology sheaf of the image again lies in `TorsionProperty`.
/-- The derived image of a complex of torsion abelian sheaves has torsion cohomology sheaves. -/
theorem torsionAbelianSheafDerivedComparisonFunctor_obj_mem
    (K : DerivedCategory TorsionSheaf) :
    derivedCategoryCohomologyInProperty TorsionProperty
      ((Functor.mapDerivedCategory TorsionProperty.ι).obj K) := sorry

/-- The canonical functor `D(\mathcal A) \to D_\mathcal A(\mathcal C)` induced by the inclusion of
torsion abelian sheaves into all abelian sheaves on the site. -/
abbrev torsionAbelianSheafDerivedComparisonFunctor :
    DerivedCategory TorsionSheaf ⥤
      DerivedCategoryWithCohomologyIn TorsionProperty :=
  ObjectProperty.lift
    (derivedCategoryCohomologyInProperty TorsionProperty)
    (Functor.mapDerivedCategory TorsionProperty.ι)
    torsionAbelianSheafDerivedComparisonFunctor_obj_mem

-- Proof sketch: represent derived objects by K-injective complexes of injective abelian sheaves.
-- Injective abelian sheaves are divisible, so the termwise torsion subsheaf of such a complex is
-- again K-injective and computes the right derived functor of torsion. This gives a right adjoint
-- to the inclusion `D(\mathcal A) ⥤ D_\mathcal A(\mathcal C)`, and the unit and counit are
-- isomorphisms because torsion complexes are unchanged by torsion and a complex with torsion
-- cohomology is quasi-isomorphic to the torsion subcomplex of an injective representative.
/-- Lemma 21.19.8: if `\mathcal A ⊂ \operatorname{Ab}(\mathcal C)` is the LinearRepresentations_Serre_1977 subcategory of
torsion abelian sheaves on a site `\mathcal C`, then the canonical functor
`D(\mathcal A) \to D_\mathcal A(\mathcal C)` is an equivalence. -/
theorem torsionAbelianSheafDerivedComparisonFunctor_isEquivalence :
    Functor.IsEquivalence torsionAbelianSheafDerivedComparisonFunctor := sorry

end

end CategoryTheory.Sheaf
