import Mathlib
import stacks_project.Chap16.Definition_16_2_3

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalization

universe u v w

namespace Algebra

section

variable {R : Type u} {A : Type v} {Λ : Type w}
variable [CommRing R] [CommRing A] [CommRing Λ]
variable [Algebra R A] [Algebra R Λ] [Algebra A Λ] [IsScalarTower R A Λ]
variable [FinitePresentation R A]

section

variable (S : Submonoid R)

local notation:max "Rₛ" => Localization S
local notation:max "Aₛ" => Localization (Algebra.algebraMapSubmonoid A S)
local notation:max "Λₛ" => Localization (Algebra.algebraMapSubmonoid Λ S)
local notation:max "φₛ" =>
  IsLocalization.mapₐ S Rₛ Aₛ Λₛ (IsScalarTower.toAlgHom R A Λ)

/- Domain-style sampling:
- primary domain: localized smooth commutative algebra and descent from standard smooth
  localizations to elementary standard global elements;
- sampled owner declarations:
  `Smooth`,
  `IsLocalization.mapₐ`,
  `IsStandardSmooth`,
  `IsStandardSmooth.exists_submersivePresentation_with_prescribed_generators`;
- best owner abstraction:
  `IsElementaryStandard R` is the source-facing owner for the descended Jacobian element, while
  the localized comparison map should be expressed directly by the canonical owner
  `IsLocalization.mapₐ`;
- primitive vs. derived:
  primitive public data are the localized smooth factorization and the descended global
  factorization with an elementary standard element. The standard smooth refinement and
  submersive presentation from Lemmas `16.3.4` and `16.3.6` are proof-level bridge data and
  should not appear as parallel wrapper structure in the public API.

Source/core/bridge triage:
- `source-facing`: the existence of a factorization `A → B → Λ` whose distinguished element from
  `S` becomes elementary standard in `B`;
- `core/canonical`: `Smooth`, `IsElementaryStandard`, and the localized comparison morphism
  `IsLocalization.mapₐ`;
- `bridge/view`: the intermediate standard smooth algebra and submersive presentation used to
  descend the Jacobian data from the localized factorization.
-/
-- Proof sketch: apply Lemma 16.3.4 over `Rₛ` to replace the given smooth factorization by one
-- through a standard smooth `Rₛ`-algebra. Then use Lemma 16.3.6 to choose a submersive
-- presentation whose first generators come from `A`, clear denominators in the extra generators,
-- the defining equations, and the Jacobian relation, and descend the presentation to a quotient
-- `B` of a polynomial algebra over `R`. The product of the cleared denominators is an element of
-- `S` whose image in `B` satisfies Definition 16.2.3.
/-- Lemma 16.8.3: from a factorization of the localized map `S⁻¹A → S⁻¹Λ` through a smooth
`Localization S`-algebra, one can descend to a factorization `A → B → Λ` such that some
`s ∈ S` maps to an elementary standard element of `B` over `R`. -/
theorem exists_factorization_with_elementaryStandard_of_localized_smooth_factorization
    {B' : Type (max u v w)} [CommRing B'] [Algebra Rₛ B'] [Smooth Rₛ B']
    (f' : Aₛ →ₐ[Rₛ] B') (g' : B' →ₐ[Rₛ] Λₛ)
    (hfactor : g'.comp f' = φₛ) :
    ∃ (B : Type (max u v w)) (_ : CommRing B) (_ : Algebra R B)
      (f : A →ₐ[R] B) (g : B →ₐ[R] Λ) (s : S),
      g.comp f = IsScalarTower.toAlgHom R A Λ ∧
      IsElementaryStandard R (algebraMap R B s) := sorry

end

end

end Algebra
