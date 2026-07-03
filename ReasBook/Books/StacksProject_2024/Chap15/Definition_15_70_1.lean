import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling:
- primary domain: derived-category amplitude conditions for `DerivedCategory (ModuleCat R)`,
  together with the canonical injective-dimension invariant on `ModuleCat R`;
- inspected owner declarations:
  `CategoryTheory.injectiveDimension`,
  `CategoryTheory.injectiveDimension_ne_top_iff`,
  `CategoryTheory.HasProjectiveAmplitudeIn`,
  `CategoryTheory.HasFiniteProjectiveDimension`;
- best owner abstraction:
  `source-facing`: `HasInjectiveAmplitudeIn` and `HasFiniteInjectiveDimension` for objects of
    `D(R)`;
  `core/canonical`: `injectiveDimension` for module-level finite injective dimension;
  `bridge/view`: the representative-complex unpacking lemmas for the derived-category owners;
- primitive vs. derived:
  the primitive data for the source-facing definition are the representative cochain complex,
  support bounds, injective terms, and the isomorphism in `D(R)`;
  the module-level predicate is not primitive data here, since mathlib already owns that notion
  through `injectiveDimension`. -/

/-- Definition 15.70.1 (2): an object `K` of `D(R)` has injective-amplitude in `[a, b]` if it is
isomorphic in the derived category to a cochain complex of injective `R`-modules supported in
degrees `a` through `b`. -/
def HasInjectiveAmplitudeIn (K : DMod) (a b : ℤ) : Prop :=
  ∃ I : CochainComplex (ModuleCat R) ℤ,
    I.IsStrictlyGE a ∧ I.IsStrictlyLE b ∧
      (∀ i : ℤ, Injective (I.X i)) ∧ Nonempty (K ≅ DerivedCategory.Q.obj I)

/-- Definition 15.70.1 (1): an object `K` of `D(R)` has finite injective dimension if it has
injective-amplitude in some finite interval `[a, b]`. -/
def HasFiniteInjectiveDimension (K : DMod) : Prop :=
  ∃ a b : ℤ, HasInjectiveAmplitudeIn K a b

-- Proof sketch: unfold `HasInjectiveAmplitudeIn`; the right-hand side is exactly the existence of
-- a representing cochain complex of injective modules supported in degrees `[a, b]`.
/-- An object of `D(R)` has injective-amplitude in `[a, b]` exactly when it admits a
representative complex of injective `R`-modules supported in those degrees. -/
theorem hasInjectiveAmplitudeIn_iff_exists_representative
    (K : DMod) (a b : ℤ) :
    HasInjectiveAmplitudeIn K a b ↔
      ∃ I : CochainComplex (ModuleCat R) ℤ,
        I.IsStrictlyGE a ∧ I.IsStrictlyLE b ∧
          (∀ i : ℤ, Injective (I.X i)) ∧ Nonempty (K ≅ DerivedCategory.Q.obj I) :=
  Iff.rfl

-- Proof sketch: unfold `HasFiniteInjectiveDimension`; this is definitionally the existence of
-- some finite interval in which `K` has injective-amplitude.
/-- An object of `D(R)` has finite injective dimension exactly when it has injective-amplitude in
some finite interval. -/
theorem hasFiniteInjectiveDimension_iff
    (K : DMod) :
    HasFiniteInjectiveDimension K ↔
      ∃ a b : ℤ, HasInjectiveAmplitudeIn K a b :=
  Iff.rfl

/- Module-level finite injective dimension is already expressed by the canonical invariant
`CategoryTheory.injectiveDimension`. -/
#check (injectiveDimension : ModuleCat R → WithBot ℕ∞)

/- Companion recall: `injectiveDimension M ≠ ⊤` is the canonical finite-injective-dimension
criterion, and with `injectiveDimension_le_iff` it is equivalent to the existence of a natural
number bound. -/
recall injectiveDimension_ne_top_iff
recall injectiveDimension_le_iff

end

end CategoryTheory
