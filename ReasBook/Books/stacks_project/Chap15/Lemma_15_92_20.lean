import Mathlib
import stacks_project.Chap15.Definition_15_59_13
import stacks_project.Chap15.Definition_15_92_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits
open scoped DerivedTensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)
local notation "single₀" => DerivedCategory.singleFunctor (ModuleCat A) (0 : ℤ)

/- Domain-style sampling for Lemma 15.92.20:
- primary domain: vanishing criteria for derived-complete objects of `D(A)` with respect to a
  finitely generated ideal, expressed through the canonical derived tensor product with the quotient
  object `(A ⧸ I)[0]`;
- sampled owner-side declarations:
  `DerivedCategory.IsDerivedCompleteWithRespectTo`,
  `CategoryTheory.derivedTensorProduct`,
  `DerivedTensorProduct` notation `K ⊗[A]^L L`,
  `derivedTensorProduct_isZero_of_modIdealPow_of_modIdeal_isZero`,
  `derivedLimitOfKoszulPowerTensorFunctorAdjunction`;
- best owner abstraction: the source-facing owner remains the predicate
  `K.IsDerivedCompleteWithRespectTo I`; the quotient tensor object `K ⊗[A]^L (A ⧸ I)[0]` is
  derived API and should use the chapter's canonical tensor notation rather than raw functor
  application;
- primitive data: the ideal `I`, finite generation `hI`, the derived object `K`, derived
  completeness of `K` with respect to `I`, and vanishing of the quotient tensor;
- derived API: the powered-Koszul tower comparison and its adjunction consequences, which belong in
  the proof route rather than in this theorem's public surface.

Source/core/bridge triage:
- `source-facing`: the vanishing criterion below for a derived-complete object annihilated modulo
  `I`;
- `core/canonical`: `K.IsDerivedCompleteWithRespectTo I` and the derived tensor owner
  `K ⊗[A]^L L`;
- `bridge/view`: finite-generator presentations of `I` and the powered-Koszul comparison machinery
  from Lemmas `15.89.8` and `15.92.18`. -/

-- Proof sketch: choose generators of the finitely generated ideal `I`, apply Lemma `15.89.8` to
-- deduce that tensoring `K` with each powered Koszul stage is zero from the vanishing modulo `I`,
-- and then use the derived-complete comparison from Lemma `15.92.18` to identify `K` with the
-- derived limit of that zero inverse system.
/-- Lemma 15.92.20: let `I` be a finitely generated ideal of a commutative ring `A`, and let
`K ∈ D(A)` be derived complete with respect to `I`. If
`K \otimes_A^{\mathbf L} (A ⧸ I)[0]` is the zero object, then `K` is the zero object. -/
theorem isZero_of_isDerivedCompleteWithRespectTo_of_derivedTensorProduct_modIdeal_isZero
    (I : Ideal A) (hI : I.FG) (K : DMod)
    (hK : K.IsDerivedCompleteWithRespectTo I)
    (hKI : IsZero (K ⊗[A]^L (single₀).obj (ModuleCat.of A (A ⧸ I)))) :
    IsZero K := sorry

end

end CategoryTheory
