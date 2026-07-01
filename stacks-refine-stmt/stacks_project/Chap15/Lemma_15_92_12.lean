import Mathlib
import stacks_project.Chap15.Remark_15_92_11

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

universe u

attribute [local instance] HasDerivedCategory.standard

namespace DerivedCategory

section

variable {A : Type u} [CommRing A]

local notation "DMod" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.92.12:
- primary domain: essential-image statements for the derived restriction-of-scalars functor
  `D(A_f) ⥤ D(A)` and derived completion in `D(A)`;
- sampled owner declarations:
  `Functor.essImage`,
  `Functor.obj_mem_essImage`,
  `Functor.EssSurj.mem_essImage`,
  `derivedCompletionOf`;
- best owner abstraction: the canonical object property
  `((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory).essImage`
  on `D(A)`, rather than an explicit witness `∃ E, Nonempty (F.obj E ≅ K)`;
- primitive data: the ideal `I`, the finitely generated hypothesis `hI`, the element `f ∈ I`, the
  object `K : D(A)`, and membership of `K` in the essential image of the localization-away
  restriction functor;
- derived API: the existential witness model of an essential-image proof, which should stay
  internal to the canonical owner `Functor.essImage`.

Source/core/bridge triage:
- `source-facing`: the vanishing of the derived completion of an object coming from `D(A_f)`;
- `core/canonical`: `Functor.essImage` for the restriction functor and `derivedCompletionOf`;
- `bridge/view`: the existential witness formulation of essential-image membership, which is
  subsumed by the owner predicate. -/

-- Proof sketch: by Lemma `15.92.1`, any object of `D(A_f)` has zero morphisms into every
-- `I`-derived-complete object when `f ∈ I`. Therefore the object `K`, which comes from `D(A_f)`,
-- has zero morphisms into every object of the reflective subcategory. Applying the universal
-- property of the left adjoint from Lemma `15.92.10` to the zero object shows that the reflector
-- of `K` is itself zero.
/-- Lemma 15.92.12: let `A` be a commutative ring and let `I ⊆ A` be a finitely generated ideal.
If `K` comes from `D(A_f)` for some `f ∈ I`, formalized canonically as membership in the
essential image of the restriction functor
`D(A_f) ⥤ D(A)`, then the derived completion of `K` with respect to `I` is zero. -/
theorem derivedCompletion_isZero_of_mem_essImage_localizationAway
    (I : Ideal A) (hI : I.FG) {f : A} (hf : f ∈ I) {K : DMod}
    (hK :
      (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory).essImage
        K)) :
    IsZero (derivedCompletionOf I hI K) := sorry

end

end DerivedCategory
