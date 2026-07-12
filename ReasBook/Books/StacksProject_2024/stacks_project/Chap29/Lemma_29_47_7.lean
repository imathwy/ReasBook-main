import Mathlib
import StacksProject_2024.Chap29.Definition_29_45_1
import StacksProject_2024.Chap29.Definition_29_47_3

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

-- Semantic recall: `lean_leansearch` recalled the canonical `HasInitial`/`initial.to`
-- initial-object API, while local Chapter 29 precedent uses `ObjectProperty.FullSubcategory` for
-- restricted universal-homeomorphism categories. The Stacks tag evidence is consistent: item tag
-- `0EUS` agrees with the source URL ending in `/tag/0EUS`.

/-- The object property on `Over X` selecting universal homeomorphisms `Y ⟶ X`. -/
@[stacks 0EUS]
abbrev absoluteWeakNormalizationOverProperty (X : Scheme.{u}) : ObjectProperty (Over X) :=
  fun Y : Over X ↦ UniversalHomeomorphism Y.hom

/-- Membership in the absolute-weak-normalization over-category is exactly the source-facing
universal-homeomorphism condition. -/
theorem absoluteWeakNormalizationOverProperty_iff (X : Scheme.{u}) (Y : Over X) :
    absoluteWeakNormalizationOverProperty X Y ↔ UniversalHomeomorphism Y.hom := sorry

/-- The category of universal homeomorphisms `Y ⟶ X`. -/
@[stacks 0EUS]
abbrev AbsoluteWeakNormalizationOver (X : Scheme.{u}) : Type (u + 1) :=
  (absoluteWeakNormalizationOverProperty X).FullSubcategory

/-- An object of the category of universal homeomorphisms over `X` has the defining
universal-homeomorphism property. -/
theorem AbsoluteWeakNormalizationOver.property
    (X : Scheme.{u}) (Y : AbsoluteWeakNormalizationOver X) :
    UniversalHomeomorphism Y.1.hom := sorry

/-- The object property on `Over X` selecting universal homeomorphisms `Y ⟶ X` that induce
isomorphisms on all residue fields. -/
@[stacks 0EUS]
abbrev seminormalizationOverProperty (X : Scheme.{u}) : ObjectProperty (Over X) :=
  fun Y : Over X ↦
    UniversalHomeomorphism Y.hom ∧
      ∀ y : Y.left, IsIso (Scheme.Hom.residueFieldMap Y.hom y)

/-- Membership in the seminormalization over-category is exactly the conjunction of
universal-homeomorphism and residue-field-isomorphism conditions. -/
theorem seminormalizationOverProperty_iff (X : Scheme.{u}) (Y : Over X) :
    seminormalizationOverProperty X Y ↔
      UniversalHomeomorphism Y.hom ∧
        ∀ y : Y.left, IsIso (Scheme.Hom.residueFieldMap Y.hom y) := sorry

/-- The category of universal homeomorphisms `Y ⟶ X` that induce isomorphisms on all residue
fields. -/
@[stacks 0EUS]
abbrev SeminormalizationOver (X : Scheme.{u}) : Type (u + 1) :=
  (seminormalizationOverProperty X).FullSubcategory

/-- An object of the seminormalization category over `X` has the defining universal-homeomorphism
and residue-field-isomorphism properties. -/
theorem SeminormalizationOver.property
    (X : Scheme.{u}) (Y : SeminormalizationOver X) :
    UniversalHomeomorphism Y.1.hom ∧
      ∀ y : Y.1.left, IsIso (Scheme.Hom.residueFieldMap Y.1.hom y) := sorry

/-- Lemma 29.47.7 (1): the category of universal homeomorphisms `Y ⟶ X` has an initial object,
denoted in the source by `X^{awn} ⟶ X`. -/
@[stacks 0EUS, instance]
instance instHasInitialAbsoluteWeakNormalizationOver (X : Scheme.{u}) :
    HasInitial (AbsoluteWeakNormalizationOver X) := sorry

/-- Lemma 29.47.7 (2): for a universal homeomorphism `Y ⟶ X`, the induced morphism
`X^{awn} ⟶ Y` from the initial object is an isomorphism if and only if `Y` is absolutely weakly
normal. -/
@[stacks 0EUS]
theorem isIso_initialTo_iff_absolutelyWeaklyNormal
    (X : Scheme.{u}) (Y : AbsoluteWeakNormalizationOver X) :
    IsIso (initial.to Y : (⊥_ (AbsoluteWeakNormalizationOver X)) ⟶ Y) ↔
      AbsolutelyWeaklyNormal Y.1.left := sorry

/-- Lemma 29.47.7 (3): the category of universal homeomorphisms `Y ⟶ X` inducing isomorphisms on
residue fields has an initial object, denoted in the source by `X^{sn} ⟶ X`. -/
@[stacks 0EUS, instance]
instance instHasInitialSeminormalizationOver (X : Scheme.{u}) :
    HasInitial (SeminormalizationOver X) := sorry

/-- Lemma 29.47.7 (4): for a universal homeomorphism `Y ⟶ X` inducing isomorphisms on residue
fields, the induced morphism `X^{sn} ⟶ Y` from the initial object is an isomorphism if and only if
`Y` is seminormal. -/
@[stacks 0EUS]
theorem isIso_initialTo_iff_seminormal
    (X : Scheme.{u}) (Y : SeminormalizationOver X) :
    IsIso (initial.to Y : (⊥_ (SeminormalizationOver X)) ⟶ Y) ↔
      Seminormal Y.1.left := sorry

/-- Lemma 29.47.7 (5): every morphism `h : X' ⟶ X` induces a unique compatible morphism
`h^{awn} : (X')^{awn} ⟶ X^{awn}` between the initial universal-homeomorphism objects. -/
@[stacks 0EUS]
theorem existsUnique_absoluteWeakNormalizationMap
    {X X' : Scheme.{u}} (h : X' ⟶ X) :
    ∃! hawn : (⊥_ (AbsoluteWeakNormalizationOver X')).1.left ⟶
        (⊥_ (AbsoluteWeakNormalizationOver X)).1.left,
      hawn ≫ (⊥_ (AbsoluteWeakNormalizationOver X)).1.hom =
        (⊥_ (AbsoluteWeakNormalizationOver X')).1.hom ≫ h := sorry

/-- Lemma 29.47.7 (6): every morphism `h : X' ⟶ X` induces a unique compatible morphism
`h^{sn} : (X')^{sn} ⟶ X^{sn}` between the initial seminormalization objects. -/
@[stacks 0EUS]
theorem existsUnique_seminormalizationMap
    {X X' : Scheme.{u}} (h : X' ⟶ X) :
    ∃! hsn : (⊥_ (SeminormalizationOver X')).1.left ⟶
        (⊥_ (SeminormalizationOver X)).1.left,
      hsn ≫ (⊥_ (SeminormalizationOver X)).1.hom =
        (⊥_ (SeminormalizationOver X')).1.hom ≫ h := sorry

end AlgebraicGeometry.Scheme
