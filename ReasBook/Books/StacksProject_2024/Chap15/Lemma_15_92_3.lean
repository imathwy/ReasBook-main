import Mathlib
import StacksProject_2024.Chap15.Definition_15_92_4

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {A : Type u} [CommRing A]

namespace ModuleCat

variable {I : Ideal A} (M : ModuleCat A)

/- Domain-style sampling:
- primary domain: adic completeness and derived completeness for modules over a commutative ring;
- sampled owner-side declarations:
  `IsAdicComplete`,
  `ModuleCat.IsDerivedCompleteWithRespectTo`,
  `isAdicComplete_of_le_of_fg`,
  `surjective_adicCompletion_of_span_eq_of_generatorwise_surjective`;
- best owner abstraction: the chapter owner predicate `M.IsDerivedCompleteWithRespectTo I`,
  whose pointwise expansion in terms of `T(M, f)` is already derived API from
  `Definition_15_92_4`;
- primitive data: the ideal `I`, the module `M`, and the completion map `AdicCompletion.of I M`;
- derived API: the pointwise `T(M, f)` vanishing criterion for each `f ∈ I` and the
  finitely-generated reduction to principal completion maps.

Layer triage:
- `source-facing`: surjectivity of the completion map `M → lim M / I^n M`;
- `core/canonical`: `IsAdicComplete`, `AdicCompletion.of I M`, and
  `M.IsDerivedCompleteWithRespectTo I`;
- `bridge/view`: the generatorwise `T(M, f)` vanishing criterion coming from
  `Definition_15_92_4`. -/

-- Proof sketch: for each `f ∈ I`, the principal ideal `(f)` is finitely generated and contained
-- in `I`, so `M` is also `(f)`-adically complete by `isAdicComplete_of_le_of_fg`. The pointwise
-- vanishing criterion from Definition `15.92.4` then shows that `M` is derived complete with
-- respect to `I`.
/-- Lemma 15.92.3 (1): an `I`-adically complete `A`-module is derived complete with respect to
`I`. Equivalently, for every `f ∈ I` the textbook object `T(M, f)` vanishes. -/
theorem isDerivedCompleteWithRespectTo_of_isAdicComplete
    (hcomplete : IsAdicComplete I M) :
    M.IsDerivedCompleteWithRespectTo I := sorry

-- Proof sketch: choose finitely many generators of `I`. The hypothesis gives the vanishing
-- condition `T(M, f_i) = 0` for each chosen generator because
-- `M.IsDerivedCompleteWithRespectTo I` is exactly the generatorwise localization-away vanishing
-- criterion. Lemma `10.96.7` then reduces surjectivity of `M → lim M / I^n M` to the principal
-- generator cases.
/-- Lemma 15.92.3 (2): if `I` is finitely generated and `M` is derived complete with respect to
`I`, then the canonical map `M → lim M / I^n M` is surjective. Equivalently, it is enough that
`T(M, f) = 0` for every `f ∈ I`. -/
theorem surjective_adicCompletion_of_isDerivedCompleteWithRespectTo
    (hfg : I.FG) (hM : M.IsDerivedCompleteWithRespectTo I) :
    Function.Surjective (AdicCompletion.of I M) := sorry

end ModuleCat

end
