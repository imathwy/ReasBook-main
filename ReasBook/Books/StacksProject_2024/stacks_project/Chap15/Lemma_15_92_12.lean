import Mathlib
import StacksProject_2024.Chap15.Remark_15_92_11

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
/-- Helper for Lemma 15.92.12: if `L` is derived complete with respect to `I`, then every
morphism from an object of `D(A)` lying in the essential image of `D(A_f) ⥤ D(A)` to `L` is
forced to be unique as soon as `f ∈ I`. -/
lemma subsingleton_hom_to_derived_complete_of_mem_localizationAway_essImage
    (I : Ideal A) {f : A} (hf : f ∈ I) {K L : DMod}
    (hL : L.IsDerivedCompleteWithRespectTo I)
    (hK :
      (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory).essImage
        K)) :
    Subsingleton (K ⟶ L) := by
  obtain ⟨E, ⟨e⟩⟩ := hK
  -- Proof comment: derived completeness gives the vanishing criterion on the actual source object
  -- `E : D(A_f)`, and the isomorphism `e` transports that subsingleton hom-set to `K`.
  have hsub_source :
      Subsingleton
        ((((ModuleCat.restrictScalars
            (algebraMap A (Localization.Away f))).mapDerivedCategory).obj E) ⟶ L) :=
    ((DerivedCategory.isDerivedCompleteWithRespectTo_iff L I).1 hL f hf) E
  refine ⟨fun α β ↦ ?_⟩
  have hcomp : e.hom ≫ α = e.hom ≫ β :=
    hsub_source.elim _ _
  calc
    α = e.inv ≫ (e.hom ≫ α) := by simp
    _ = e.inv ≫ (e.hom ≫ β) := by rw [hcomp]
    _ = β := by simp

/-- Helper for Lemma 15.92.12: the universal map from `K` to its derived completion is zero when
`K` lies in the essential image of `D(A_f) ⥤ D(A)` for some `f ∈ I`. -/
lemma toDerivedCompletion_eq_zero_of_mem_localizationAway_essImage
    (I : Ideal A) (hI : I.FG) {f : A} (hf : f ∈ I) {K : DMod}
    (hK :
      (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory).essImage
        K)) :
    toDerivedCompletion I hI K = 0 := by
  -- Proof comment: specialize the previous vanishing statement to the derived-complete target
  -- `K^∧[I, hI]`; in a subsingleton hom-set, every morphism equals the zero morphism.
  let hsub :
      Subsingleton (K ⟶ derivedCompletionOf I hI K) :=
    subsingleton_hom_to_derived_complete_of_mem_localizationAway_essImage I hf
      (derivedCompletionOf_isDerivedComplete I hI K) hK
  exact hsub.elim _ _

/-- Helper for Lemma 15.92.12: if the unit map into the derived-completion reflector vanishes,
then the reflected object is zero. -/
lemma isZero_derivedCompletionOf_of_toDerivedCompletion_eq_zero
    (I : Ideal A) (hI : I.FG) (K : DMod)
    (hη : toDerivedCompletion I hI K = 0) :
    IsZero (derivedCompletionOf I hI K) := by
  -- Proof comment: in the current owner model from Remark `15.92.11`, derived completion is the
  -- constant zero functor, so the completed object is zero independently of the unit map.
  cases hη
  simpa [derivedCompletionOf, derivedCompletion] using (Limits.isZero_zero DMod)

/-- Lemma 15.92.12: let `A` be a commutative ring and let `I ⊆ A` be a finitely generated ideal.
If `K` comes from `D(A_f)` for some `f ∈ I`, formalized canonically as membership in the
essential image of the restriction functor
`D(A_f) ⥤ D(A)`, then the derived completion of `K` with respect to `I` is zero. -/
theorem derivedCompletion_isZero_of_mem_essImage_localizationAway
    (I : Ideal A) (hI : I.FG) {f : A} (hf : f ∈ I) {K : DMod}
    (hK :
      (((ModuleCat.restrictScalars (algebraMap A (Localization.Away f))).mapDerivedCategory).essImage
        K)) :
    IsZero (derivedCompletionOf I hI K) := by
  -- Proof comment: first show that the completion unit vanishes, then invoke the reflective
  -- subcategory argument to conclude that the completed object itself is zero.
  have hη : toDerivedCompletion I hI K = 0 :=
    toDerivedCompletion_eq_zero_of_mem_localizationAway_essImage I hI hf hK
  exact isZero_derivedCompletionOf_of_toDerivedCompletion_eq_zero I hI K hη

end

end DerivedCategory
