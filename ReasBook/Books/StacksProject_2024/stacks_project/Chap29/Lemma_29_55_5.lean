import StacksProject_2024.Chap29.Lemma_29_55_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/- Semantic recall: `lean_leansearch` surfaced the canonical
`CategoryTheory.Factorisation` category and its initial-object API. Local Chapter 29 precedent
uses `ObjectProperty.FullSubcategory` for universal-homeomorphism and seminormalization
categories, and `Scheme.Opens.ι`/`f ∣_ U` for restriction to open subschemes. The Stacks tag
evidence is consistent: item tag `0H3N` agrees with the source URL ending in `/tag/0H3N`. -/

/-- The object property on the factorization category of `f : Y ⟶ X` selecting factorizations
whose second map is a universal homeomorphism. -/
@[stacks 0H3N]
abbrev relativeWeakNormalizationFactorizationProperty {X Y : Scheme.{u}} (f : Y ⟶ X) :
    ObjectProperty (CategoryTheory.Factorisation f) :=
  fun F ↦ UniversalHomeomorphism F.π

/-- Membership in the relative weak-normalization factorization property is exactly the
universal-homeomorphism condition on the second map of the factorization. -/
@[stacks 0H3N]
theorem relativeWeakNormalizationFactorizationProperty_iff
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : CategoryTheory.Factorisation f) :
    relativeWeakNormalizationFactorizationProperty f F ↔ UniversalHomeomorphism F.π := sorry

/-- The category of factorizations `Y ⟶ X' ⟶ X` of `f : Y ⟶ X` such that `X' ⟶ X` is a
universal homeomorphism. -/
@[stacks 0H3N]
abbrev RelativeWeakNormalizationFactorizations {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Type (u + 1) :=
  (relativeWeakNormalizationFactorizationProperty f).FullSubcategory

/-- An object of the relative weak-normalization factorization category has a universal
homeomorphism as its second map. -/
@[stacks 0H3N]
theorem RelativeWeakNormalizationFactorizations.property
    {X Y : Scheme.{u}} {f : Y ⟶ X} (F : RelativeWeakNormalizationFactorizations f) :
    UniversalHomeomorphism F.1.π := sorry

/-- The object property on the factorization category of `f : Y ⟶ X` selecting factorizations
whose second map is a universal homeomorphism inducing isomorphisms on residue fields. -/
@[stacks 0H3N]
abbrev relativeSeminormalizationFactorizationProperty {X Y : Scheme.{u}} (f : Y ⟶ X) :
    ObjectProperty (CategoryTheory.Factorisation f) :=
  fun F ↦
    UniversalHomeomorphism F.π ∧
      ∀ x : F.mid, IsIso (Scheme.Hom.residueFieldMap F.π x)

/-- Membership in the relative seminormalization factorization property is exactly the
universal-homeomorphism condition together with residue-field isomorphisms for the second map. -/
@[stacks 0H3N]
theorem relativeSeminormalizationFactorizationProperty_iff
    {X Y : Scheme.{u}} (f : Y ⟶ X) (F : CategoryTheory.Factorisation f) :
    relativeSeminormalizationFactorizationProperty f F ↔
      UniversalHomeomorphism F.π ∧
        ∀ x : F.mid, IsIso (Scheme.Hom.residueFieldMap F.π x) := sorry

/-- The category of factorizations `Y ⟶ X' ⟶ X` of `f : Y ⟶ X` such that `X' ⟶ X` is a
universal homeomorphism inducing isomorphisms on residue fields. -/
@[stacks 0H3N]
abbrev RelativeSeminormalizationFactorizations {X Y : Scheme.{u}} (f : Y ⟶ X) :
    Type (u + 1) :=
  (relativeSeminormalizationFactorizationProperty f).FullSubcategory

/-- An object of the relative seminormalization factorization category has a universal
homeomorphism as its second map and induces isomorphisms on all residue fields. -/
@[stacks 0H3N]
theorem RelativeSeminormalizationFactorizations.property
    {X Y : Scheme.{u}} {f : Y ⟶ X} (F : RelativeSeminormalizationFactorizations f) :
    UniversalHomeomorphism F.1.π ∧
      ∀ x : F.1.mid, IsIso (Scheme.Hom.residueFieldMap F.1.π x) := sorry

/-- Lemma 29.55.5 (1): for a quasi-compact, quasi-separated, dominant morphism of schemes
`f : Y ⟶ X`, the category of factorizations `Y ⟶ X' ⟶ X` whose second map is a universal
homeomorphism has an initial object, denoted in the source by
`Y ⟶ X^{Y/wn} ⟶ X`. -/
@[stacks 0H3N, instance]
instance instHasInitialRelativeWeakNormalizationFactorizations
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] [IsDominant f] :
    HasInitial (RelativeWeakNormalizationFactorizations f) := sorry

/-- Lemma 29.55.5 (2): for a quasi-compact, quasi-separated, dominant morphism of schemes
`f : Y ⟶ X`, the category of factorizations `Y ⟶ X' ⟶ X` whose second map is a universal
homeomorphism inducing isomorphisms on residue fields has an initial object, denoted in the source
by `Y ⟶ X^{Y/sn} ⟶ X`. -/
@[stacks 0H3N, instance]
instance instHasInitialRelativeSeminormalizationFactorizations
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] [IsDominant f] :
    HasInitial (RelativeSeminormalizationFactorizations f) := sorry

/-- Lemma 29.55.5 (3): formation of the relative weak-normalization factorization commutes with
base change to an open subscheme. Concretely, if `WU` is the pullback of the initial
factorization `Y ⟶ X^{Y/wn} ⟶ X` along `U.ι : U.toScheme ⟶ X`, then `WU` has the initial
universal property for the restricted morphism `f ∣_ U`. -/
@[stacks 0H3N]
theorem relativeWeakNormalization_openRestrict_existsUnique
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] [IsDominant f]
    (U : X.Opens) (WU : RelativeWeakNormalizationFactorizations (f ∣_ U))
    (toGlobal : WU.1.mid ⟶ (⊥_ (RelativeWeakNormalizationFactorizations f)).1.mid)
    (hpullback :
      IsPullback toGlobal WU.1.π (⊥_ (RelativeWeakNormalizationFactorizations f)).1.π U.ι)
    (hι : WU.1.ι ≫ toGlobal =
      (f ⁻¹ᵁ U).ι ≫ (⊥_ (RelativeWeakNormalizationFactorizations f)).1.ι) :
    ∀ Z : RelativeWeakNormalizationFactorizations (f ∣_ U), ∃! h : WU ⟶ Z, True := sorry

/-- Lemma 29.55.5 (4): formation of the relative seminormalization factorization commutes with
base change to an open subscheme. Concretely, if `SU` is the pullback of the initial
factorization `Y ⟶ X^{Y/sn} ⟶ X` along `U.ι : U.toScheme ⟶ X`, then `SU` has the initial
universal property for the restricted morphism `f ∣_ U`. -/
@[stacks 0H3N]
theorem relativeSeminormalization_openRestrict_existsUnique
    {X Y : Scheme.{u}} (f : Y ⟶ X) [QuasiCompact f] [QuasiSeparated f] [IsDominant f]
    (U : X.Opens) (SU : RelativeSeminormalizationFactorizations (f ∣_ U))
    (toGlobal : SU.1.mid ⟶ (⊥_ (RelativeSeminormalizationFactorizations f)).1.mid)
    (hpullback :
      IsPullback toGlobal SU.1.π (⊥_ (RelativeSeminormalizationFactorizations f)).1.π U.ι)
    (hι : SU.1.ι ≫ toGlobal =
      (f ⁻¹ᵁ U).ι ≫ (⊥_ (RelativeSeminormalizationFactorizations f)).1.ι) :
    ∀ Z : RelativeSeminormalizationFactorizations (f ∣_ U), ∃! h : SU ⟶ Z, True := sorry

end Scheme.Hom
end AlgebraicGeometry
