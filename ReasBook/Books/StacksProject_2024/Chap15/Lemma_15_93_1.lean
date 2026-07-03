import Mathlib
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
import stacks_project.Chap12.Lemma_12_10_3
import stacks_project.Chap15.Definition_15_92_4
import stacks_project.Chap15.Lemma_15_92_6

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty

universe u

noncomputable section

attribute [local instance] HasDerivedCategory.standard

namespace ModuleCat

section

variable {A : Type u} [CommRing A] (I : Ideal A)

local notation "P" => derivedCompleteObjectProperty I
local notation "PSub" => ObjectProperty.FullSubcategory P
local notation "Pι" => ObjectProperty.ι P

/- Domain-style sampling:
- primary domain: object properties and their full subcategories in abelian categories;
- sampled owner-side declarations:
  `ModuleCat.IsDerivedCompleteWithRespectTo`,
  `ObjectProperty.FullSubcategory`,
  `ObjectProperty.ι`,
  `derivedCompleteObjectProperty_isWeakSerreClass`,
  `Limits.hasLimitsOfShape_of_closedUnderLimits`,
  `Limits.hasColimitsOfShape_of_closedUnderColimits`,
  `ObjectProperty.weakSerreSubcategory_inclusion_exact`;
- best owner abstraction: the project owner
  `P : ObjectProperty (ModuleCat A)`;
- primitive data: the module-level predicate `ModuleCat.IsDerivedCompleteWithRespectTo`;
- derived API:
  `P.FullSubcategory` and its canonical inclusion `P.ι`,
  together with the owner-level closure theorems below that let the canonical
  full-subcategory machinery produce limits and colimits.

Layer triage:
- `source-facing`: the category of derived-complete modules and its inclusion into `Mod_A`;
- `core/canonical`: the owner surface `P`, the full subcategory `P.FullSubcategory`, and the
  inclusion `P.ι`;
- `bridge/view`: the weak-Serre package from Lemma `15.92.6` and the owner-level closure
  theorems below, which feed the canonical `ObjectProperty` transfer results. -/

local instance : IsWeakSerreClass P :=
  derivedCompleteObjectProperty_isWeakSerreClass I

-- Proof sketch: the preceding discussion identifies derived-complete modules as a full
-- subcategory of `ModuleCat A` that is stable under kernels, cokernels, and extensions, so the
-- standard abelian-structure transfer to a full subcategory applies.
/- Lemma 15.93.1 (1): the category of derived complete `A`-modules with respect to `I` is
abelian. -/
#check (inferInstance : Abelian PSub)

-- Proof sketch: the earlier limit-closure results show that the defining property of derived
-- completeness is stable under all ambient limits. This is the owner-level limit-closure
-- theorem feeding the generic full-subcategory machinery.
/-- Derived-complete modules are closed under arbitrary small limits in `Mod_A`. -/
theorem derivedCompleteObjectProperty_isClosedUnderLimits
    (J : Type*) [Category J] :
    IsClosedUnderLimitsOfShape P J := by
  sorry

/-- Derived-complete modules carry the canonical owner-level
`ObjectProperty.IsClosedUnderLimitsOfShape` instance. -/
instance derivedCompleteObjectProperty_isClosedUnderLimitsOfShape
    (J : Type*) [Category J] :
    IsClosedUnderLimitsOfShape P J :=
  derivedCompleteObjectProperty_isClosedUnderLimits I J

instance derivedCompleteSubcategory_hasLimits : HasLimits PSub where
  has_limits_of_shape J _ := by
    let _ : IsClosedUnderLimitsOfShape P J :=
      derivedCompleteObjectProperty_isClosedUnderLimits I J
    infer_instance

/- Lemma 15.93.1 (2): the category of derived complete `A`-modules with respect to `I` has
arbitrary small limits. -/
#check (inferInstance : HasLimits PSub)

-- Proof sketch: once the full subcategory is abelian and kernels/cokernels are computed by the
-- inclusion, the inclusion preserves finite limits and finite colimits, hence is exact.
/- Lemma 15.93.1 (3): the inclusion functor from derived complete `A`-modules to `Mod_A` is
exact. -/
#check (weakSerreSubcategory_inclusion_exact P : exactFunctor PSub (ModuleCat A) Pι)

/- Lemma 15.93.1 (4): the inclusion functor from derived complete `A`-modules to `Mod_A`
commutes with arbitrary small limits. -/
instance derivedCompleteSubcategory_inclusion_preservesLimits : PreservesLimits Pι where
  preservesLimitsOfShape := by
    intro J _
    let _ : IsClosedUnderLimitsOfShape P J :=
      derivedCompleteObjectProperty_isClosedUnderLimits I J
    infer_instance

#check (inferInstance : PreservesLimits Pι)

section

-- Proof sketch: for finitely generated `I`, the discussion above shows that derived completeness
-- is stable under all ambient colimits. This is the owner-level colimit-closure theorem feeding
-- the canonical full-subcategory machinery.
/-- If `I` is finitely generated, then derived-complete modules are closed under arbitrary small
colimits in `Mod_A`. -/
theorem derivedCompleteObjectProperty_isClosedUnderColimits_of_fg
    (hI : I.FG)
    (J : Type*) [Category J] :
    IsClosedUnderColimitsOfShape P J := by
  sorry

/- Lemma 15.93.1 (5): if `I` is finitely generated, then the category of derived complete
`A`-modules with respect to `I` has arbitrary small colimits. -/
theorem derivedCompleteSubcategory_hasColimits_of_fg
    (hI : I.FG) :
    HasColimits PSub := by
  refine { has_colimits_of_shape := ?_ }
  intro J _
  let _ : IsClosedUnderColimitsOfShape P J :=
    derivedCompleteObjectProperty_isClosedUnderColimits_of_fg I hI J
  infer_instance

-- Proof sketch: once `I` is finitely generated, the derived-completion construction discussed
-- above provides the reflector onto derived-complete objects in the derived category. Restricting
-- that source-facing construction to degree-zero objects yields the corresponding left adjoint to
-- the module-level inclusion `P.ι`.
theorem derivedCompleteSubcategory_inclusion_isRightAdjoint_of_fg
    (hI : I.FG) :
    (Pι).IsRightAdjoint := by
  sorry

/- Lemma 15.93.1 (6): if `I` is finitely generated, then the inclusion functor from derived
complete `A`-modules to `Mod_A` has a left adjoint. -/
section

variable (hI : I.FG)

#check (show ModuleCat A ⥤ PSub from by
  letI : (Pι).IsRightAdjoint := derivedCompleteSubcategory_inclusion_isRightAdjoint_of_fg I hI
  exact Functor.leftAdjoint Pι)

end

end

end

end ModuleCat
