import Mathlib
import Mathlib.Tactic.Recall
import stacks_project.Chap13.Situation_13_14_1
import stacks_project.Chap13.Lemma_13_5_7
import stacks_project.Chap13.Lemma_13_5_8
import stacks_project.Chap13.Lemma_13_14_3
import stacks_project.Chap13.Lemma_13_14_4
import stacks_project.Chap13.Lemma_13_14_6
import stacks_project.Chap13.Lemma_13_14_7

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Localization
open CategoryTheory.MorphismProperty
open CategoryTheory.ObjectProperty

noncomputable section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/- 
Domain-style sampling:
- primary domain: pointwise right-derived functors on a localization, restricted to the full
  subcategory where the pointwise construction is defined, together with its left-derived dual;
- relevant owner declarations reused here:
  `ObjectProperty.FullSubcategory`,
  `fullSubcategoryLocalizationSystem`,
  `fullSubcategoryLocalizationFunctor`,
  `Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem`,
  `Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem`,
  `rightDerivedDefinedObjectProperty_isStableUnderRetracts`,
  `leftDerivedDefinedObjectProperty_isStableUnderRetracts`,
  `rightDerivedValueMap`,
  `leftDerivedValueMap`.

Source/core/bridge triage:
- `source-facing`: the full subcategory `𝓔` and the restricted multiplicative system `S_𝓔`;
- `core/canonical`: the upstream object-property owners `rightDerivedDefinedObjectProperty` and
  `leftDerivedDefinedObjectProperty` from `Lemma_13_14_5`, the transport owners
  `Functor.hasPointwise...DerivedFunctorAt_iff_of_mem`, the Karoubian retract-stability owners
  from `Lemma_13_14_7`, together with the chapter owner `fullSubcategoryLocalizationSystem`;
- `bridge/view`: the restricted functors and localizations obtained from `𝓔` and `S_𝓔`.

Primitive data are the object property saying where the pointwise right-derived functor is
defined, and its left-derived analogue. The subcategories and restricted localization systems are
derived owners built from those primitive predicates and reused throughout the proposition.
-/

section Basic

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']

/-- The full subcategory `𝓔 ⊆ D` consisting of objects at which the pointwise right derived
functor of `F` with respect to `S` is defined. -/
abbrev rightDerivedDefinedSubcategory (F : D ⥤ D') (S : MorphismProperty D) :=
  (rightDerivedDefinedObjectProperty F S).FullSubcategory

/-- The restricted multiplicative system `S_𝓔` on the full subcategory `𝓔`. -/
abbrev rightDerivedDefinedLocalizationSystem (F : D ⥤ D') (S : MorphismProperty D) :
    MorphismProperty (rightDerivedDefinedSubcategory F S) :=
  fullSubcategoryLocalizationSystem (rightDerivedDefinedObjectProperty F S) S

notation "𝓔[" F ", " S "]" => rightDerivedDefinedSubcategory F S
notation "S_𝓔[" F ", " S "]" => rightDerivedDefinedLocalizationSystem F S

/- Proposition 13.14.8 companion recall: for a denominator `s : X ⟶ Y` in `S`, the source and
target belong to `𝓔[F, S]` simultaneously. This is exactly the source-facing clause that any
`s ∈ S` whose source or target lies in `𝓔` is already a morphism of `𝓔`. -/
recall Functor.hasPointwiseRightDerivedFunctorAt_iff_of_mem

/-- An object of the full subcategory `𝓔` canonically carries the hypothesis that `RF` is
pointwise defined there. -/
instance rightDerivedDefinedSubcategory_hasPointwiseRightDerivedFunctorAt
    (F : D ⥤ D') (S : MorphismProperty D)
    (X : 𝓔[F, S]) :
    F.HasPointwiseRightDerivedFunctorAt S X.obj :=
  X.property

/-- The functor `RF : 𝓔 ⥤ D'` obtained by restricting the pointwise right derived construction to
the full subcategory where it is defined. -/
noncomputable def rightDerivedDefinedFunctor (F : D ⥤ D') (S : MorphismProperty D) :
    𝓔[F, S] ⥤ D' where
  obj X :=
    rightDerivedValue S F X.obj
  map f :=
    rightDerivedValueMap S F f.hom
  map_id X :=
    by
      sorry
  map_comp f g :=
    by
      sorry

-- Proof sketch: if a morphism of `S_𝓔` lies over an ambient arrow `s ∈ S`, then the two objects
-- of `𝓔` remain in the right-derived domain and Lemma `13.14.4` identifies the induced map on
-- pointwise right-derived values as an isomorphism.
/-- Every denominator in the restricted multiplicative system `S_𝓔` is sent to an isomorphism by
the restricted functor `RF : 𝓔 ⥤ D'`. -/
theorem rightDerivedDefinedFunctor_isInvertedBy
    (F : D ⥤ D') (S : MorphismProperty D) :
    (S_𝓔[F, S]).IsInvertedBy (rightDerivedDefinedFunctor F S) := sorry

/-- The localized right-derived functor `RF : S_𝓔^{-1}𝓔 ⥤ D'` induced by the restricted functor
`RF : 𝓔 ⥤ D'`. -/
noncomputable abbrev rightDerivedLocalizationFactorization
    (F : D ⥤ D') (S : MorphismProperty D) :
    (S_𝓔[F, S]).Localization ⥤ D' :=
  Localization.lift (rightDerivedDefinedFunctor F S)
    (rightDerivedDefinedFunctor_isInvertedBy F S) (S_𝓔[F, S]).Q

/-- The full subcategory `𝓔ₗ ⊆ D` consisting of objects at which the pointwise left derived
functor of `F` with respect to `S` is defined. -/
abbrev leftDerivedDefinedSubcategory (F : D ⥤ D') (S : MorphismProperty D) :=
  (leftDerivedDefinedObjectProperty F S).FullSubcategory

/-- The restricted multiplicative system `S_𝓔ₗ` on the full subcategory `𝓔ₗ`. -/
abbrev leftDerivedDefinedLocalizationSystem (F : D ⥤ D') (S : MorphismProperty D) :
    MorphismProperty (leftDerivedDefinedSubcategory F S) :=
  fullSubcategoryLocalizationSystem (leftDerivedDefinedObjectProperty F S) S

notation "𝓔ₗ[" F ", " S "]" => leftDerivedDefinedSubcategory F S
notation "S_𝓔ₗ[" F ", " S "]" => leftDerivedDefinedLocalizationSystem F S

/- Left-derived companion recall: a denominator `s : X ⟶ Y` in `S` has source in `𝓔ₗ[F, S]` if
and only if it has target in `𝓔ₗ[F, S]`. -/
recall Functor.hasPointwiseLeftDerivedFunctorAt_iff_of_mem

/-- An object of the full subcategory `𝓔ₗ` canonically carries the hypothesis that `LF` is
pointwise defined there. -/
instance leftDerivedDefinedSubcategory_hasPointwiseLeftDerivedFunctorAt
    (F : D ⥤ D') (S : MorphismProperty D)
    (X : 𝓔ₗ[F, S]) :
    F.HasPointwiseLeftDerivedFunctorAt S X.obj :=
  X.property

/-- The functor `LF : 𝓔ₗ ⥤ D'` obtained by restricting the pointwise left derived construction to
the full subcategory where it is defined. -/
noncomputable def leftDerivedDefinedFunctor (F : D ⥤ D') (S : MorphismProperty D) :
    𝓔ₗ[F, S] ⥤ D' where
  obj X :=
    leftDerivedValue S F X.obj
  map f :=
    leftDerivedValueMap S F f.hom
  map_id X :=
    by
      sorry
  map_comp f g :=
    by
      sorry

-- Proof sketch: if a morphism of `S_𝓔ₗ` lies over an ambient arrow `s ∈ S`, then the two
-- objects of `𝓔ₗ` remain in the left-derived domain and Lemma `13.14.4` identifies the induced
-- map on pointwise left-derived values as an isomorphism.
/-- Every denominator in the restricted multiplicative system `S_𝓔ₗ` is sent to an isomorphism by
the restricted functor `LF : 𝓔ₗ ⥤ D'`. -/
theorem leftDerivedDefinedFunctor_isInvertedBy
    (F : D ⥤ D') (S : MorphismProperty D) :
    (S_𝓔ₗ[F, S]).IsInvertedBy (leftDerivedDefinedFunctor F S) := sorry

/-- The localized left-derived functor `LF : S_𝓔ₗ^{-1}𝓔ₗ ⥤ D'` induced by the restricted functor
`LF : 𝓔ₗ ⥤ D'`. -/
noncomputable abbrev leftDerivedLocalizationFactorization
    (F : D ⥤ D') (S : MorphismProperty D) :
    (S_𝓔ₗ[F, S]).Localization ⥤ D' :=
  Localization.lift (leftDerivedDefinedFunctor F S)
    (leftDerivedDefinedFunctor_isInvertedBy F S) (S_𝓔ₗ[F, S]).Q

end Basic

section RestrictedLocalization

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  (F : D ⥤ D') (S : MorphismProperty D)

/- The restricted system `S_𝓔[F, S]` inherits saturation directly from the owner instance
`fullSubcategoryLocalizationSystem_isSaturatedMultiplicativeSystem`; no local reexport is needed.
-/

/- The restricted system `S_𝓔ₗ[F, S]` likewise inherits saturation from
`fullSubcategoryLocalizationSystem_isSaturatedMultiplicativeSystem`.
-/

end RestrictedLocalization

section Triangulated

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [Limits.HasZeroObject D]
  [HasShift D ℤ]
  [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated D]
  [IsTriangulated D]
  (F : D ⥤ D') (S : MorphismProperty D)

-- Proof sketch: apply Lemmas `13.14.4`, `13.14.6`, and `13.14.7` to show that the object
-- property “`RF` is defined” is closed under isomorphisms, shifts, cones, and the zero object;
-- this is exactly the canonical `ObjectProperty.IsTriangulated` interface.
/-- Proposition 13.14.8: the full subcategory `𝓔 ⊆ D` consisting of objects at which the
pointwise right derived functor of `F` with respect to `S` is defined is strictly full and
triangulated. The companion declarations below record the restricted functor `RF : 𝓔 ⥤ D'`, the
restricted multiplicative system `S_𝓔`, its localization factorization, and the Karoubian
saturation conclusion. -/
instance rightDerivedDefinedObjectProperty_isTriangulated
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (rightDerivedDefinedObjectProperty F S).IsTriangulated := sorry

/-- The restricted right-derived functor `RF : 𝓔[F, S] ⥤ D'` commutes with shifts. -/
noncomputable instance rightDerivedDefinedFunctor_commShift
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (rightDerivedDefinedFunctor F S).CommShift ℤ := by
  sorry

/-- The restricted right-derived functor `RF : 𝓔[F, S] ⥤ D'` is exact. -/
instance rightDerivedDefinedFunctor_isTriangulated
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (rightDerivedDefinedFunctor F S).IsTriangulated := by
  sorry

-- Strict fullness is already the owner instance
-- `rightDerivedDefinedObjectProperty_isClosedUnderIsomorphisms` from `Lemma_13_14_5`.

/- Once `rightDerivedDefinedObjectProperty F S` is triangulated, the restricted system `S_𝓔[F, S]`
inherits `IsCompatibleWithTriangulation` from the generic owner instance
`fullSubcategoryLocalizationSystem_isCompatibleWithTriangulation`.
-/

/-- The localized inclusion `S_𝓔[F, S]⁻¹𝓔[F, S] ⥤ S.Localization` is fully faithful. -/
instance rightDerivedDefinedLocalizationFunctor_full
    [hsat : IsSaturatedMultiplicativeSystem S] :
    (fullSubcategoryLocalizationFunctor (rightDerivedDefinedObjectProperty F S) S).Full := by
  sorry

/-- The localized inclusion `S_𝓔[F, S]⁻¹𝓔[F, S] ⥤ S.Localization` is faithful. -/
instance rightDerivedDefinedLocalizationFunctor_faithful
    [hsat : IsSaturatedMultiplicativeSystem S] :
    (fullSubcategoryLocalizationFunctor (rightDerivedDefinedObjectProperty F S) S).Faithful := by
  sorry

/-- The localized inclusion `S_𝓔[F, S]⁻¹𝓔[F, S] ⥤ S.Localization` commutes with shifts. -/
noncomputable instance rightDerivedDefinedLocalizationFunctor_commShift
    [hsat : IsSaturatedMultiplicativeSystem S]
    [htriE : (rightDerivedDefinedObjectProperty F S).IsTriangulated]
    [hcompat : S.IsCompatibleWithTriangulation] :
    (fullSubcategoryLocalizationFunctor (rightDerivedDefinedObjectProperty F S) S).CommShift ℤ := by
  sorry

/-- The localized inclusion `S_𝓔[F, S]⁻¹𝓔[F, S] ⥤ S.Localization` is exact. -/
noncomputable instance rightDerivedDefinedLocalizationFunctor_isTriangulated
    [hsat : IsSaturatedMultiplicativeSystem S]
    [htriE : (rightDerivedDefinedObjectProperty F S).IsTriangulated]
    [hcompat : S.IsCompatibleWithTriangulation] :
    (fullSubcategoryLocalizationFunctor (rightDerivedDefinedObjectProperty F S) S).IsTriangulated := by
  sorry

/-- The localized right-derived functor `RF : S_𝓔[F, S]⁻¹𝓔[F, S] ⥤ D'` commutes with shifts. -/
noncomputable instance rightDerivedLocalizationFactorization_commShift
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (rightDerivedLocalizationFactorization F S).CommShift ℤ :=
  Functor.commShiftOfLocalization (S_𝓔[F, S]).Q (S_𝓔[F, S]) ℤ
    (rightDerivedDefinedFunctor F S) (rightDerivedLocalizationFactorization F S)

/-- The localized right-derived functor `RF : S_𝓔[F, S]⁻¹𝓔[F, S] ⥤ D'` is exact. -/
instance rightDerivedLocalizationFactorization_isTriangulated
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (rightDerivedLocalizationFactorization F S).IsTriangulated :=
  exact_factorization_isTriangulated (S_𝓔[F, S]) (rightDerivedDefinedFunctor F S)
    (rightDerivedDefinedFunctor_isInvertedBy F S)

-- Proof sketch: if `RF` is defined at a biproduct `X ⊞ Y`, Lemma `13.14.7` shows that in a
-- Karoubian target the two direct summands also lie in the domain. This is exactly stability
-- under retracts of the corresponding object property.
/- Proposition 13.14.8 companion recall: if `D'` is Karoubian, then the right-derived-defined
object property is stable under retracts. Together with
`rightDerivedDefinedObjectProperty_isTriangulated`, this is exactly the source-facing statement
that `𝓔[F, S]` is a saturated triangulated subcategory. -/
recall rightDerivedDefinedObjectProperty_isStableUnderRetracts

-- Proof sketch: apply the left-derived clauses of Lemmas `13.14.4`, `13.14.6`, and `13.14.7` to
-- show that the object property “`LF` is defined” is closed under isomorphisms, shifts, cones,
-- and the zero object; this is exactly the canonical `ObjectProperty.IsTriangulated` interface.
/-- The full subcategory `𝓔ₗ ⊆ D` consisting of objects at which the pointwise left derived
functor of `F` with respect to `S` is defined is strictly full and triangulated, with the same
localized-factorization companion picture as on the right-derived side. -/
instance leftDerivedDefinedObjectProperty_isTriangulated
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (leftDerivedDefinedObjectProperty F S).IsTriangulated := sorry

/-- The restricted left-derived functor `LF : 𝓔ₗ[F, S] ⥤ D'` commutes with shifts. -/
noncomputable instance leftDerivedDefinedFunctor_commShift
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (leftDerivedDefinedFunctor F S).CommShift ℤ := by
  sorry

/-- The restricted left-derived functor `LF : 𝓔ₗ[F, S] ⥤ D'` is exact. -/
instance leftDerivedDefinedFunctor_isTriangulated
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (leftDerivedDefinedFunctor F S).IsTriangulated := by
  sorry

-- Strict fullness is already the owner instance
-- `leftDerivedDefinedObjectProperty_isClosedUnderIsomorphisms` from `Lemma_13_14_5`.

/- Once `leftDerivedDefinedObjectProperty F S` is triangulated, the restricted system `S_𝓔ₗ[F, S]`
inherits `IsCompatibleWithTriangulation` from
`fullSubcategoryLocalizationSystem_isCompatibleWithTriangulation`.
-/

/-- The localized inclusion `S_𝓔ₗ[F, S]⁻¹𝓔ₗ[F, S] ⥤ S.Localization` is fully faithful. -/
instance leftDerivedDefinedLocalizationFunctor_full
    [hsat : IsSaturatedMultiplicativeSystem S] :
    (fullSubcategoryLocalizationFunctor (leftDerivedDefinedObjectProperty F S) S).Full := by
  sorry

/-- The localized inclusion `S_𝓔ₗ[F, S]⁻¹𝓔ₗ[F, S] ⥤ S.Localization` is faithful. -/
instance leftDerivedDefinedLocalizationFunctor_faithful
    [hsat : IsSaturatedMultiplicativeSystem S] :
    (fullSubcategoryLocalizationFunctor (leftDerivedDefinedObjectProperty F S) S).Faithful := by
  sorry

/-- The localized inclusion `S_𝓔ₗ[F, S]⁻¹𝓔ₗ[F, S] ⥤ S.Localization` commutes with shifts. -/
noncomputable instance leftDerivedDefinedLocalizationFunctor_commShift
    [hsat : IsSaturatedMultiplicativeSystem S]
    [htriE : (leftDerivedDefinedObjectProperty F S).IsTriangulated]
    [hcompat : S.IsCompatibleWithTriangulation] :
    (fullSubcategoryLocalizationFunctor (leftDerivedDefinedObjectProperty F S) S).CommShift ℤ := by
  sorry

/-- The localized inclusion `S_𝓔ₗ[F, S]⁻¹𝓔ₗ[F, S] ⥤ S.Localization` is exact. -/
noncomputable instance leftDerivedDefinedLocalizationFunctor_isTriangulated
    [hsat : IsSaturatedMultiplicativeSystem S]
    [htriE : (leftDerivedDefinedObjectProperty F S).IsTriangulated]
    [hcompat : S.IsCompatibleWithTriangulation] :
    (fullSubcategoryLocalizationFunctor (leftDerivedDefinedObjectProperty F S) S).IsTriangulated := by
  sorry

/-- The localized left-derived functor `LF : S_𝓔ₗ[F, S]⁻¹𝓔ₗ[F, S] ⥤ D'` commutes with shifts. -/
noncomputable instance leftDerivedLocalizationFactorization_commShift
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (leftDerivedLocalizationFactorization F S).CommShift ℤ :=
  Functor.commShiftOfLocalization (S_𝓔ₗ[F, S]).Q (S_𝓔ₗ[F, S]) ℤ
    (leftDerivedDefinedFunctor F S) (leftDerivedLocalizationFactorization F S)

/-- The localized left-derived functor `LF : S_𝓔ₗ[F, S]⁻¹𝓔ₗ[F, S] ⥤ D'` is exact. -/
instance leftDerivedLocalizationFactorization_isTriangulated
    [hzero' : Limits.HasZeroObject D'] [hshift' : HasShift D' ℤ] [hpreadd' : Preadditive D']
    [hadd' : ∀ n : ℤ, (shiftFunctor D' n).Additive]
    [hpretri' : Pretriangulated D'] [htri' : IsTriangulated D']
    [hcomm : F.CommShift ℤ] [hexact : F.IsTriangulated]
    [hsat : IsSaturatedMultiplicativeSystem S] [hcompat : S.IsCompatibleWithTriangulation] :
    (leftDerivedLocalizationFactorization F S).IsTriangulated :=
  exact_factorization_isTriangulated (S_𝓔ₗ[F, S]) (leftDerivedDefinedFunctor F S)
    (leftDerivedDefinedFunctor_isInvertedBy F S)

-- Proof sketch: if `LF` is defined at a biproduct `X ⊞ Y`, Lemma `13.14.7` shows that in a
-- Karoubian target the two direct summands also lie in the domain. This is exactly stability
-- under retracts of the corresponding object property.
/- Left-derived companion recall: if `D'` is Karoubian, then the left-derived-defined object
property is stable under retracts, so `𝓔ₗ[F, S]` is saturated once it is triangulated. -/
recall leftDerivedDefinedObjectProperty_isStableUnderRetracts

end Triangulated

end CategoryTheory
