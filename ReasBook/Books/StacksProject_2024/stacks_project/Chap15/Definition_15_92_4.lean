import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

namespace CategoryTheory.DerivedCategory

/- Domain-style sampling:
- primary domain: derived completeness in `D(A)` via localization-away derived-Hom vanishing;
- sampled owner-side declarations:
  `localizationAwayDerivedHomVanishingCondition`,
  the downstream object-property owner `derivedCompleteObjectProperty`,
  and the module bridge `ModuleCat.IsDerivedCompleteWithRespectTo`;
- best owner abstraction: the source-facing predicate `K.IsDerivedCompleteWithRespectTo I`,
  stated directly in the textbook pointwise form;
- primitive data: `K : DMod` and `I : Ideal A`;
- derived API: the pointwise criterion `isDerivedCompleteWithRespectTo_iff` and the module bridge
  `ModuleCat.IsDerivedCompleteWithRespectTo`.

Layer triage:
- `source-facing`: `CategoryTheory.DerivedCategory.IsDerivedCompleteWithRespectTo`;
- `core/canonical`: `localizationAwayDerivedHomVanishingCondition`;
- `bridge/view`: the pointwise criterion and `ModuleCat.IsDerivedCompleteWithRespectTo`. -/

/-- Helper for Definition 15.92.4: after restriction of scalars along `A → A_f`, every morphism
from an object of `D(A_f)` to `K` is zero. -/
def localizationAwayDerivedHomVanishingCondition (f : A) (K : DMod) : Prop :=
  ∀ E : DerivedCategory (ModuleCat (Localization.Away f)),
    Subsingleton
      (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory.obj E) ⟶
        K)

/-- Definition 15.92.4: an object `K` of `D(A)` is derived complete with respect to an ideal
`I ⊆ A` if, for every `f ∈ I`, every morphism from an object of `D(A_f)` to `K` is zero after
restriction of scalars along `A → A_f`. By Lemma `15.92.1`, this is equivalent to the textbook
condition `T(K, f) = 0` for all `f ∈ I`. -/
def IsDerivedCompleteWithRespectTo (K : DMod) (I : Ideal A) : Prop :=
  ∀ f ∈ I, localizationAwayDerivedHomVanishingCondition f K

/-- An object of `D(A)` is derived complete with respect to `I` exactly when the
localization-away derived-Hom vanishing condition holds for every `f ∈ I`. -/
theorem isDerivedCompleteWithRespectTo_iff
    (K : DMod) (I : Ideal A) :
    K.IsDerivedCompleteWithRespectTo I ↔
      ∀ f ∈ I, localizationAwayDerivedHomVanishingCondition f K :=
  Iff.rfl

/-- The object property on `D(A)` selecting the complexes that are derived complete with respect
to the ideal `I`. -/
abbrev derivedCompleteObjectProperty (I : Ideal A) : ObjectProperty DMod :=
  fun K ↦ K.IsDerivedCompleteWithRespectTo I

end CategoryTheory.DerivedCategory

namespace ModuleCat

/-- The module-theoretic notion of derived completeness with respect to `I`, obtained by applying
the derived-category predicate to the degree-zero object `M[0]`. -/
abbrev IsDerivedCompleteWithRespectTo (M : ModuleCat A) (I : Ideal A) : Prop :=
  ((DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)).obj M).IsDerivedCompleteWithRespectTo I

/-- The object property on `Mod_A` selecting the modules that are derived complete with respect
to `I`. -/
abbrev derivedCompleteObjectProperty (I : Ideal A) : ObjectProperty (ModuleCat A) :=
  fun M ↦ M.IsDerivedCompleteWithRespectTo I

end ModuleCat

end
