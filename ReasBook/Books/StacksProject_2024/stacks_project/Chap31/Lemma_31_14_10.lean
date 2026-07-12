import StacksProject_2024.Chap31.ClosedImmersionIdealSubobject
import StacksProject_2024.Chap18.Lemma_18_32_4
import StacksProject_2024.Chap31.Definition_31_13_1
import StacksProject_2024.Chap31.Definition_31_14_1
import StacksProject_2024.Chap31.Definition_31_14_6
import StacksProject_2024.Chap31.Definition_31_14_8

open CategoryTheory
open CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed
open AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` did not surface a ready-made owner for the correspondence
-- between effective Cartier divisors and regular sections, so the statement follows the local
-- Chapter 31 owners `effectiveCartierDivisorAssociatedSheaf`, `effectiveCartierDivisorCanonicalSection`,
-- `zeroIdealSheaf`, and `closedImmersionIdealSubobject`; regularity of a section is expressed on
-- the canonical morphism `𝒪_X ⟶ ℒ` given by `unitHomEquiv.symm`.

variable {X : Scheme.{u}}

variable [MonoidalCategory X.Modules]
variable [SymmetricCategory X.Modules]
variable [MonoidalClosed X.Modules]

local notation "ModX" => X.Modules
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)
local notation "EffectiveCartierIdeal" =>
  (fun I : Subobject 𝒪X ↦
    Functor.IsEquivalence (tensorRight (Subobject.underlying.obj I)))

local instance schemeToSheafOfModulesMonoidal :
    MonoidalCategory (SheafOfModules X.ringCatSheaf) := by
  simpa using (inferInstance : MonoidalCategory X.Modules)

local instance schemeToSheafOfModulesSymmetric :
    SymmetricCategory (SheafOfModules X.ringCatSheaf) := by
  simpa using (inferInstance : SymmetricCategory X.Modules)

local instance schemeToSheafOfModulesMonoidalClosed :
    MonoidalClosed (SheafOfModules X.ringCatSheaf) := by
  simpa using (inferInstance : MonoidalClosed X.Modules)

local instance schemeToRingedSpaceModulesMonoidal :
    MonoidalCategory (RingedSpace.Modules X.toRingedSpace) := by
  simpa using (inferInstance : MonoidalCategory X.Modules)

local instance schemeToRingedSpaceModulesSymmetric :
    SymmetricCategory (RingedSpace.Modules X.toRingedSpace) := by
  simpa using (inferInstance : SymmetricCategory X.Modules)

local instance schemeToRingedSpaceModulesMonoidalClosed :
    MonoidalClosed (RingedSpace.Modules X.toRingedSpace) := by
  simpa using (inferInstance : MonoidalClosed X.Modules)

local instance schemeToSheafOfModulesTensorRightIsEquivalence (ℒ : ModX)
    [Functor.IsEquivalence (tensorRight ℒ)] :
    Functor.IsEquivalence
      (tensorRight (show SheafOfModules X.ringCatSheaf from ℒ)) := by
  simpa using (inferInstance : Functor.IsEquivalence (tensorRight ℒ))

local instance schemeToRingedSpaceTensorRightIsEquivalence (ℒ : ModX)
    [Functor.IsEquivalence (tensorRight ℒ)] :
    Functor.IsEquivalence
      (tensorRight (show RingedSpace.Modules X.toRingedSpace from ℒ)) := by
  simpa using (inferInstance : Functor.IsEquivalence (tensorRight ℒ))

omit [SymmetricCategory X.Modules] [MonoidalClosed X.Modules] in
private theorem effectiveCartierIdeal_to_sheafOfModules
    (I : Subobject 𝒪X) [Fact (EffectiveCartierIdeal I)] :
    Functor.IsEquivalence
      (tensorRight (Subobject.underlying.obj I : SheafOfModules X.ringCatSheaf)) := by
  have hI : EffectiveCartierIdeal I := Fact.out
  simpa using hI

private instance instIsInvertible_effectiveCartierDivisorAssociatedSheafSheaf
    (I : Subobject 𝒪X) [Fact (EffectiveCartierIdeal I)] :
    Functor.IsEquivalence
      (tensorRight
        (effectiveCartierDivisorAssociatedSheaf I : SheafOfModules X.ringCatSheaf)) := by
  let _ :
      Functor.IsEquivalence
        (tensorRight (Subobject.underlying.obj I : SheafOfModules X.ringCatSheaf)) :=
    effectiveCartierIdeal_to_sheafOfModules I
  simpa [effectiveCartierDivisorAssociatedSheaf] using
    (SheafOfModules.RingedSite.isInvertible_internalHom_unit_of_isInvertible
      (Subobject.underlying.obj I : SheafOfModules X.ringCatSheaf))

private instance instIsInvertible_effectiveCartierDivisorAssociatedSheaf
    (I : Subobject 𝒪X) [Fact (EffectiveCartierIdeal I)] :
    Functor.IsEquivalence (tensorRight (effectiveCartierDivisorAssociatedSheaf I : ModX)) := by
  simpa using
    (inferInstance :
      Functor.IsEquivalence
        (tensorRight
          (effectiveCartierDivisorAssociatedSheaf I : SheafOfModules X.ringCatSheaf)))

private instance instIsInvertible_effectiveCartierDivisorAssociatedSheafRaw
    (I : Subobject 𝒪X) [Fact (EffectiveCartierIdeal I)] :
    Functor.IsEquivalence (tensorRight (effectiveCartierDivisorAssociatedSheaf I)) := by
  simpa using
    (instIsInvertible_effectiveCartierDivisorAssociatedSheaf I :
      Functor.IsEquivalence (tensorRight (effectiveCartierDivisorAssociatedSheaf I : ModX)))

private abbrev effectiveCartierDivisorAssociatedSheafX
    (I : Subobject 𝒪X) [Fact (EffectiveCartierIdeal I)] : ModX :=
  effectiveCartierDivisorAssociatedSheaf I

private instance instIsInvertible_effectiveCartierDivisorAssociatedSheafX
    (I : Subobject 𝒪X) [Fact (EffectiveCartierIdeal I)] :
    Functor.IsEquivalence (tensorRight (effectiveCartierDivisorAssociatedSheafX I)) := by
  simpa [effectiveCartierDivisorAssociatedSheafX] using
    (instIsInvertible_effectiveCartierDivisorAssociatedSheaf I :
      Functor.IsEquivalence (tensorRight (effectiveCartierDivisorAssociatedSheaf I : ModX)))

/-- Lemma 31.14.10 (1): for an effective Cartier divisor on `X` represented by the ideal-sheaf
subobject `I`, the canonical section `1_D` of `\mathcal O_X(D)` is regular. -/
@[stacks 01X0]
theorem isRegularSection_effectiveCartierDivisorCanonicalSection
    (I : Subobject 𝒪X) [Fact (EffectiveCartierIdeal I)] :
    LocallyRingedSpace.IsRegularSection
      (effectiveCartierDivisorAssociatedSheaf I)
      (effectiveCartierDivisorCanonicalSection I) := sorry

/-- Lemma 31.14.10 (2): if `s` is a regular global section of an invertible sheaf `\mathcal L`
on `X`, then the canonical closed immersion `Z(s) ⟶ X` of its zero scheme is an effective Cartier
divisor. Here `Z(s)` is formalized by the ideal sheaf datum `zeroIdealSheaf ℒ s`. -/
@[stacks 01X0]
theorem isEffectiveCartierDivisor_zeroIdealSheaf_of_isRegularSection
    (ℒ : ModX) [Functor.IsEquivalence (tensorRight ℒ)] (s : ℒ.sections)
    (hs : LocallyRingedSpace.IsRegularSection ℒ s) :
    AlgebraicGeometry.IsEffectiveCartierDivisor (zeroSchemeι ℒ s) := sorry

/-- Lemma 31.14.10 (3): if `s` is a regular global section of an invertible sheaf `\mathcal L`
on `X`, then there exists a unique isomorphism `\mathcal O_X(Z(s)) \cong \mathcal L` sending the
canonical section `1_{Z(s)}` to `s`, stated on the canonical ideal subobject of the zero-scheme
closed immersion used by `effectiveCartierDivisorAssociatedSheaf`. -/
@[stacks 01X0]
theorem existsUnique_associatedSheafIso_zeroIdealSheaf_of_isRegularSection
    (ℒ : ModX) [Functor.IsEquivalence (tensorRight ℒ)] (s : ℒ.sections)
    (hs : LocallyRingedSpace.IsRegularSection ℒ s)
    (I : Subobject 𝒪X) [Fact (EffectiveCartierIdeal I)]
    (hI : closedImmersionIdealSubobject (zeroSchemeι ℒ s) = I) :
    ∃! e : effectiveCartierDivisorAssociatedSheaf I ≅ ℒ,
      SheafOfModules.sectionsMap e.hom
          (effectiveCartierDivisorCanonicalSection I) = s := sorry

/-- Lemma 31.14.10 (4): the zero divisor of the canonical section `1_D` recovers the original
effective Cartier divisor `D`. In the chosen owner, this says that the ideal-sheaf subobject
attached to the zero scheme of `1_D` is exactly the original ideal-sheaf subobject `I`; the
invertibility of `\mathcal O_X(D)` is implicit in the associated-sheaf owner from
`Definition_31_14_1`. -/
@[stacks 01X0]
theorem closedImmersionIdealSubobject_zeroIdealSheaf_associatedSheaf_canonicalSection
    (I : Subobject 𝒪X) [Fact (EffectiveCartierIdeal I)] :
    closedImmersionIdealSubobject
        (zeroIdealSheaf
          (effectiveCartierDivisorAssociatedSheafX I)
          (effectiveCartierDivisorCanonicalSection I)).subschemeι = I := sorry

end AlgebraicGeometry.Scheme
