import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

noncomputable section

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

section

variable {D : Type u₁} [Category.{v₁} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
variable (S : MorphismProperty D) [S.HasLeftCalculusOfFractions] [S.IsCompatibleWithTriangulation]
variable {A : Type u₂} [Category.{v₂} A] [Abelian A]
variable {D' : Type u₃} [Category.{v₃} D'] [Limits.HasZeroObject D'] [HasShift D' ℤ]
  [Preadditive D'] [∀ n : ℤ, (shiftFunctor D' n).Additive] [Pretriangulated D']

/- Domain-style sampling:
- primary domain: localization of pretriangulated categories and induced homological/triangulated
  structures on localized factorizations;
- inspected owner declarations:
  `Localization.lift`,
  `Localization.fac`,
  `Functor.isHomological_of_localization`,
  `Functor.commShiftOfLocalization`,
  `Functor.isTriangulated_of_precomp_iso`;
- source/core/bridge triage:
  `source-facing`: the two statements of Lemma 13.5.7 about the canonical factorization through
    `S.Q`;
  `core/canonical`: the localization lift `Localization.lift ... S.Q` and the induced
    homological/triangulated owner theorems in mathlib;
  `bridge/view`: the canonical factorization isomorphism `Localization.fac ... S.Q`.

Primitive data here is just the localization functor `S.Q`, a functor that inverts `S`, and the
canonical comparison isomorphism of its factorization. Homologicality, shift-commutation of the
lift, and triangulatedness are all derived owner API and should be reused directly.
-/

-- Proof sketch: equip `S.Localization` with the pretriangulated structure of Proposition 13.5.6
-- so that `S.Q` is triangulated. Then use `Localization.essSurj_mapArrow S.Q S` together with the
-- factorization isomorphism `Localization.fac H hH S.Q` and
-- apply `Functor.isHomological_of_localization`.
/-- Lemma 13.5.7 (1): if `H : D ⥤ A` is a homological functor that inverts every morphism of the
multiplicative system `S`, then its canonical factorization through the localization functor
`S.Q : D ⥤ S.Localization` is homological as well. -/
@[stacks 05R7]
theorem homological_factorization_isHomological
    (H : D ⥤ A) [H.IsHomological] (hH : S.IsInvertedBy H) :
    (Localization.lift H hH S.Q).IsHomological := by
  letI : Functor.EssSurj ((S.Q).mapArrow) := Localization.essSurj_mapArrow S.Q S
  exact Functor.isHomological_of_localization S.Q (Localization.lift H hH S.Q) H
    (Localization.fac H hH S.Q)

-- The induced shift-commuting structure on a localization lift is the canonical owner instance
-- `Functor.commShiftOfLocalization`, specialized to the factorization through `S.Q`.
noncomputable instance (F : D ⥤ D') [F.CommShift ℤ] (hF : S.IsInvertedBy F) :
    (Localization.lift F hF S.Q).CommShift ℤ :=
  Functor.commShiftOfLocalization S.Q S ℤ F (Localization.lift F hF S.Q)

-- Proof sketch: endow the localized factorization `F' := Localization.lift F hF S.Q` with the
-- canonical shift-commuting structure `Functor.commShiftOfLocalization S.Q S ℤ F F'`. The
-- canonical lifting isomorphism `Localization.Lifting.iso S.Q S F (Localization.lift F hF S.Q)`
-- is compatible with shifts, and
-- `Localization.essSurj_mapArrow S.Q S` makes `S.Q` essentially surjective on arrows; then apply
-- `Functor.isTriangulated_of_precomp_iso`.
/-- Lemma 13.5.7 (2): if `F : D ⥤ D'` is an exact functor between pretriangulated categories that
inverts every morphism of the multiplicative system `S`, then its canonical factorization through
`S.Q : D ⥤ S.Localization` is exact too; in Lean, exactness is encoded by the induced
shift-commuting structure together with `Functor.IsTriangulated`. -/
@[stacks 05R7]
theorem exact_factorization_isTriangulated
    (F : D ⥤ D') [F.CommShift ℤ] [F.IsTriangulated] (hF : S.IsInvertedBy F) :
    (Localization.lift F hF S.Q).IsTriangulated := by
  letI : (Localization.lift F hF S.Q).CommShift ℤ := inferInstance
  letI : Functor.EssSurj ((S.Q).mapArrow) := Localization.essSurj_mapArrow S.Q S
  exact Functor.isTriangulated_of_precomp_iso
    (Localization.Lifting.iso S.Q S F (Localization.lift F hF S.Q))

end

end CategoryTheory
