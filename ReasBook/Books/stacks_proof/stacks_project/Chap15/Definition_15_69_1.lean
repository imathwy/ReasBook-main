import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [Ring R]

local notation "Cpx" => CochainComplex (ModuleCat R) ℤ
local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling:
- primary domain: projective-amplitude conditions for objects of `DerivedCategory (ModuleCat R)`,
  together with the canonical module-level projective-dimension invariant;
- inspected owner declarations:
  `CategoryTheory.projectiveDimension`,
  `CategoryTheory.projectiveDimension_ne_top_iff`,
  `CategoryTheory.projectiveDimension_le_iff`,
  `CategoryTheory.DerivedCategory.IsPerfect`;
- best owner abstraction:
  `source-facing`: `HasProjectiveAmplitudeIn` and `HasFiniteProjectiveDimension` for objects of
    `D(R)`;
  `core/canonical`: `projectiveDimension` for module-level finite projective dimension;
  `bridge/view`: the representative-complex unpacking theorem for `HasProjectiveAmplitudeIn`;
- primitive vs. derived:
  the primitive data for projective amplitude are a representative complex `P`, an isomorphism
  `K ≅ DerivedCategory.Q.obj P`, support bounds, and termwise projectivity;
  finite projective dimension in `D(R)` is derived from the amplitude owner by existentially
  forgetting the interval, while module-level finite projective dimension is already owned by
  `projectiveDimension`. -/

/-- Definition 15.69.1 (2): an object `K` of `D(R)` has projective-amplitude in `[a, b]` if it is
isomorphic in the derived category to a cochain complex of projective `R`-modules concentrated in
degrees `a` through `b`. -/
@[stacks 0A5N]
def HasProjectiveAmplitudeIn (K : DMod) (a b : ℤ) : Prop :=
  ∃ (P : Cpx) (_ : K ≅ DerivedCategory.Q.obj P),
    P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ ∀ i : ℤ, Projective (P.X i)

-- Proof sketch: this is just the direct expansion of the definition of projective-amplitude in
-- terms of a bounded representative with projective terms and a chosen isomorphism in `D(R)`.
/-- An object of `D(R)` has projective-amplitude in `[a, b]` exactly when it admits a
representative by a cochain complex of projective `R`-modules concentrated in degrees `a`
through `b`. -/
theorem hasProjectiveAmplitudeIn_iff_exists_representative (K : DMod) (a b : ℤ) :
    HasProjectiveAmplitudeIn K a b ↔
      ∃ (P : Cpx) (_ : K ≅ DerivedCategory.Q.obj P),
        P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧ ∀ i : ℤ, Projective (P.X i) :=
  Iff.rfl

/-- Definition 15.69.1 (1): an object `K` of `D(R)` has finite projective dimension if it has
projective-amplitude in some finite interval `[a, b]`. -/
@[stacks 0A5N]
def HasFiniteProjectiveDimension (K : DMod) : Prop :=
  ∃ a b : ℤ, HasProjectiveAmplitudeIn K a b

-- Proof sketch: one direction forgets the specified amplitude interval from a projective
-- representative, while the other direction records the interval furnished by
-- `HasProjectiveAmplitudeIn`.
/-- An object of `D(R)` has finite projective dimension exactly when it has projective-amplitude in
some finite interval `[a, b]`. -/
theorem hasFiniteProjectiveDimension_iff (K : DMod) :
    HasFiniteProjectiveDimension K ↔ ∃ a b : ℤ, HasProjectiveAmplitudeIn K a b :=
  Iff.rfl

end

end CategoryTheory
