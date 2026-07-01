import Mathlib
import stacks_project.Chap15.Definition_15_92_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModB" => DerivedCategory (ModuleCat B)

/- Domain-style sampling:
- primary domain: derived completeness in derived module categories under restriction of scalars;
- sampled owner-side declarations:
  `CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingCondition`,
  `CategoryTheory.DerivedCategory.localizationAwayDerivedHomVanishingIdeal`,
  `CategoryTheory.DerivedCategory.IsDerivedCompleteWithRespectTo`,
  `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`;
- best owner abstraction: the source-facing predicate
  `K.IsDerivedCompleteWithRespectTo I`, whose core/canonical owner is the ideal
  `K.localizationAwayDerivedHomVanishingIdeal`, together with the canonical derived
  restriction-of-scalars functor;
- primitive data: the object `L : D(B)`, the ideal `I : Ideal A`, and the algebra map `A → B`;
- derived API: this restriction/base-change equivalence for the source-facing completeness
  predicate.

Layer triage:
- `source-facing`: `isDerivedCompleteWithRespectTo_iff_restrictScalars`;
- `core/canonical`: `K.localizationAwayDerivedHomVanishingIdeal`;
- `bridge/view`: restriction of scalars along `(ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory`. -/

-- Proof sketch: by Definition `15.92.4`, derived completeness with respect to an ideal is the
-- vanishing of all morphisms from localization-derived categories `D(A_f)` or `D(B_g)` after
-- restriction of scalars. Using Lemma `15.92.2`, test membership in the relevant radical ideal by
-- the generators coming from `I`; the localization-away derived-Hom condition is computed in
-- abelian groups and is unchanged when `f ∈ A` is viewed in `B`, so the two vanishing conditions
-- are equivalent.
/-- Lemma 15.92.24: a derived `B`-complex lies in the inverse image of `D_{comp}(A, I)` under the
restriction functor `D(B) ⥤ D(A)` exactly when it is derived complete with respect to the
extended ideal `I B = I.map (algebraMap A B)`. -/
theorem isDerivedCompleteWithRespectTo_iff_restrictScalars
    (L : DModB) (I : Ideal A) :
    (((ModuleCat.restrictScalars (algebraMap A B)).mapDerivedCategory).obj L).IsDerivedCompleteWithRespectTo I ↔
      L.IsDerivedCompleteWithRespectTo (I.map (algebraMap A B)) := sorry

end

end CategoryTheory
