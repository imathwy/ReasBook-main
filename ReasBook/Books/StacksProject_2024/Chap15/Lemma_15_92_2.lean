import Mathlib
import StacksProject_2024.Chap15.Lemma_15_92_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.DerivedCategory

universe u

attribute [local instance] HasDerivedCategory.standard

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

namespace CategoryTheory.DerivedCategory

/- Domain-style sampling:
- primary domain: localization-away vanishing loci in the derived category of `A`-modules;
- sampled owner-side declarations:
  `localizationAwayDerivedHomVanishingCondition`,
  `Ideal`,
  `Ideal.IsRadical`,
  the downstream containment owner `IsDerivedCompleteWithRespectTo`;
- best owner abstraction: the source-facing ideal
  `K.localizationAwayDerivedHomVanishingIdeal`, built from the primitive predicate
  `localizationAwayDerivedHomVanishingCondition f K`;
- primitive data: `K : DMod` and the vanishing predicate in the scalar `f : A`;
- derived API: membership rewriting and the downstream containment formulation of derived
  completeness.

Layer triage:
- `source-facing`: `K.localizationAwayDerivedHomVanishingIdeal`;
- `core/canonical`: the primitive predicate `localizationAwayDerivedHomVanishingCondition`;
- `bridge/view`: the membership iff and the derived-completeness containment API. -/

-- Proof sketch: for `f = 0`, the localization `A_0` is the zero ring, so `D(A_0)` is the zero
-- derived category and every morphism out of an object of `D(A_0)` is zero.
/-- The vanishing condition holds for the zero element. -/
theorem localizationAwayDerivedHomVanishingCondition_zero (K : DMod) :
    localizationAwayDerivedHomVanishingCondition 0 K := sorry

-- Proof sketch: use the standard Mayer-Vietoris short exact sequence
-- `0 → A_{f + g} → A_{f(f + g)} ⊕ A_{g(f + g)} → A_{fg(f + g)} → 0`, then apply the long exact
-- sequence of derived `Hom` groups and the multiplicative stability of the vanishing condition.
/-- The vanishing condition is stable under addition of elements. -/
theorem localizationAwayDerivedHomVanishingCondition_add
    {f g : A} {K : DMod}
    (hf : localizationAwayDerivedHomVanishingCondition f K)
    (hg : localizationAwayDerivedHomVanishingCondition g K) :
    localizationAwayDerivedHomVanishingCondition (f + g) K := sorry

-- Proof sketch: `A_{r • f}` is an `A_f`-module via the localization map, so restriction of
-- scalars from `D(A_{r • f})` factors through `D(A_f)`. The vanishing for `f` therefore implies
-- vanishing for `r • f`.
/-- The vanishing condition is stable under multiplication by arbitrary elements of `A`. -/
theorem localizationAwayDerivedHomVanishingCondition_smul
    (r : A) {f : A} {K : DMod}
    (hf : localizationAwayDerivedHomVanishingCondition f K) :
    localizationAwayDerivedHomVanishingCondition (r • f) K := sorry

/-- The ideal of elements `f ∈ A` such that the textbook object `T(K, f)` vanishes, expressed via
the equivalent derived-Hom vanishing condition from Lemma `15.92.1`. -/
def localizationAwayDerivedHomVanishingIdeal (K : DMod) : Ideal A where
  carrier := {f : A | localizationAwayDerivedHomVanishingCondition f K}
  zero_mem' := localizationAwayDerivedHomVanishingCondition_zero K
  add_mem' := fun hf hg ↦ localizationAwayDerivedHomVanishingCondition_add hf hg
  smul_mem' := fun r _ hf ↦ localizationAwayDerivedHomVanishingCondition_smul r hf

-- Proof sketch: this is immediate from the definition of
-- `localizationAwayDerivedHomVanishingIdeal`.
/-- Membership in `K.localizationAwayDerivedHomVanishingIdeal` is exactly the localization-away
derived-Hom vanishing condition. -/
theorem mem_localizationAwayDerivedHomVanishingIdeal_iff (K : DMod) (f : A) :
    f ∈ K.localizationAwayDerivedHomVanishingIdeal ↔
      localizationAwayDerivedHomVanishingCondition f K := Iff.rfl

-- Proof sketch: the multiplicative closure above shows ideal membership. For radicality, if
-- `f^n` lies in the ideal with `n > 0`, then `A_f ≅ A_{f^n}`, so the vanishing condition for
-- `f^n` is equivalent to the vanishing condition for `f`. This proves that the radical is
-- contained in the ideal.
/-- Lemma 15.92.2: for a commutative ring `A` and `K ∈ D(A)`, the set of elements `f ∈ A` such
that `T(K, f) = 0` is a radical ideal of `A`, formalized through the equivalent localization-away
derived-Hom vanishing condition of Lemma `15.92.1`. -/
theorem localizationAwayDerivedHomVanishingIdeal_isRadical (K : DMod) :
    K.localizationAwayDerivedHomVanishingIdeal.IsRadical := sorry

end CategoryTheory.DerivedCategory

end
