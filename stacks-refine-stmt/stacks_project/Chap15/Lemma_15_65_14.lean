import Mathlib
import stacks_project.Chap15.Definition_15_65_1
import stacks_project.Chap15.Lemma_15_65_12
import stacks_project.Chap15.Lemma_15_60_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} [CommRing R]
variable {ι : Type*} [Finite ι]

local notation "DMod" => DerivedCategory (ModuleCat R)

/- Domain-style sampling for Lemma 15.65.14:
- primary domain: descent of pseudo-coherence in `D(R)` from a finite principal-open cover;
- sampled owner-level declarations:
  `Module.FinitePresentationRelativeTo.iff_localizationAway_unitIdeal`,
  `quotient_torsionBy_fintypeLinearCombination_surjective_of_presentation_minorIdeal_eq_span_singleton`,
  and the underlying finite-family owner `Fintype.linearCombination`;
- best owner abstraction: this item stays `source-facing`, but its covering data should be an
  arbitrary finite family `f : ι → R`, not the coordinate model `Fin r → R`;
- primitive data: the family `f`, the unit-ideal hypothesis `Ideal.span (Set.range f) = ⊤`, and
  the localized pseudo-coherence hypotheses;
- derived API: the descent conclusions for `m`-pseudo-coherence and pseudo-coherence. -/

-- Proof sketch: use the finite principal-open cover `D(f i)` of `Spec R` coming from
-- `Ideal.span (Set.range f) = ⊤`. Descend the bounded finite-projective approximation from each
-- localization and glue the finite top cohomology modules by the standard local criterion for
-- finite generation, then induct on the highest nonvanishing cohomological degree as in the
-- Stacks proof.
/-- Lemma 15.65.14 (1): if the finite family `f : ι → R` generates the unit ideal and each
localization of `K` away from `f i` is `m`-pseudo-coherent, then `K` is `m`-pseudo-coherent. -/
theorem isMPseudoCoherent_of_localizationAway_unitIdeal
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤) (K : DMod) (m : ℤ)
    (hloc : ∀ i, (K ⊗[R]^L[Localization.Away (f i)]).IsMPseudoCoherent m) :
    K.IsMPseudoCoherent m := sorry

/-- Combining Lemma `15.65.14 (1)` with scalar-extension preservation, `m`-pseudo-coherence is
local for finite principal-open covers of `Spec R`. -/
theorem isMPseudoCoherent_iff_localizationAway_unitIdeal
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤) (K : DMod) (m : ℤ) :
    (∀ i, (K ⊗[R]^L[Localization.Away (f i)]).IsMPseudoCoherent m) ↔
      K.IsMPseudoCoherent m := by
  constructor
  · exact isMPseudoCoherent_of_localizationAway_unitIdeal f hunit K m
  · intro hK i
    exact derivedTensorWithAlgebra_isMPseudoCoherent K m hK

-- Proof sketch: pseudo-coherence means `m`-pseudo-coherence for every `m`. Apply part `(1)` to
-- each integer `m`, using the localized pseudo-coherence hypotheses, and then invoke the standard
-- characterization of pseudo-coherence by uniform `m`-pseudo-coherence.
/-- Lemma 15.65.14 (2): if the finite family `f : ι → R` generates the unit ideal and each
localization of `K` away from `f i` is pseudo-coherent, then `K` is pseudo-coherent. -/
theorem isPseudoCoherent_of_localizationAway_unitIdeal
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤) (K : DMod)
    (hloc : ∀ i, (K ⊗[R]^L[Localization.Away (f i)]).IsPseudoCoherent) :
    K.IsPseudoCoherent := sorry

/-- Combining Lemma `15.65.14 (2)` with scalar-extension preservation, pseudo-coherence is local
for finite principal-open covers of `Spec R`. -/
theorem isPseudoCoherent_iff_localizationAway_unitIdeal
    (f : ι → R) (hunit : Ideal.span (Set.range f) = ⊤) (K : DMod) :
    (∀ i, (K ⊗[R]^L[Localization.Away (f i)]).IsPseudoCoherent) ↔
      K.IsPseudoCoherent := by
  constructor
  · exact isPseudoCoherent_of_localizationAway_unitIdeal f hunit K
  · intro hK i
    exact derivedTensorWithAlgebra_isPseudoCoherent K hK

end

end CategoryTheory
