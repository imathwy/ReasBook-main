import Mathlib
import stacks_project.Chap15.Lemma_15_81_1
import stacks_project.Chap15.Lemma_15_81_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

section

open scoped TensorProduct

variable {R : Type u} {A : Type v} {M : Type w}
variable [CommRing R] [CommRing A] [Algebra R A]
variable [AddCommGroup M] [Module A M]

local notation "Away" => LocalizedModule.Away

/- Domain-style sampling:
- primary domain: relative finite presentation of modules and locality on a finite principal-open
  cover;
- sampled owner declarations:
  `Module.FinitePresentationRelativeTo`,
  `Module.FinitePresentationRelativeTo.iff_overAnyFinitelyPresentedCover`,
  `Module.finitePresentationRelativeTo_baseChange_of_finitePresentation`,
  `module_finitePresentation_of_localizationAway`;
- best owner abstraction: the source-facing owner predicate
  `Module.FinitePresentationRelativeTo R A M`;
- primitive data: a finitely presented `R`-algebra cover of `A` together with a finite
  presentation of `M` after restricting scalars to that cover;
- derived API: localization and descent lemmas that turn that owner data into ordinary finite
  presentation on local charts and back.

Source/core/bridge triage:
- `source-facing`: the locality theorem below for `Module.FinitePresentationRelativeTo`;
- `core/canonical`: `Module.FinitePresentation` and the principal-open descent theorem
  `module_finitePresentation_of_localizationAway`;
- `bridge/view`: Lemma `15.81.1`, which converts between the relative owner and finite
  presentation over finitely presented covers of `A`.

The public API should stay centered on `Module.FinitePresentationRelativeTo`; the ordinary
finite-presentation theorem is auxiliary descent data, not a second owner for this notion. -/

-- Proof sketch: for `→`, a source-facing relative presentation already implies
-- `Algebra.FiniteType R A`; localize that presentation and apply the chapter's
-- finite-presentation base-change theorem
-- `Module.finitePresentationRelativeTo_baseChange_of_finitePresentation`, then identify the
-- resulting tensor product with `LocalizedModule.Away` via `LocalizedModule.equivTensorProduct`.
-- For `←`, each local hypothesis implies `Algebra.FiniteType R (Localization.Away f.1)`, so
-- `Algebra.FiniteType.of_span_eq_top_source hs` recovers `Algebra.FiniteType R A`. Then choose a
-- finitely presented cover of `A`; the local hypotheses and Lemma `15.81.1` make each induced
-- localized module finitely presented over the corresponding localized cover, Lemma `10.23.2`
-- descends finite presentation over that cover, and Lemma `15.81.1` packages the result back
-- into `FinitePresentationRelativeTo`, with the ordinary finite-presentation descent step routed
-- through the chapter's principal-open locality theorem
-- `module_finitePresentation_of_localizationAway`.

namespace Module.FinitePresentationRelativeTo

/-- Lemma 15.81.8: for an `R`-algebra `A`, an `A`-module `M`, and finitely many elements of `A`
generating the unit ideal, `M` is finitely presented relative to `R` if and only if each
principal localization `M_f` is finitely presented relative to `R`; the localized hypotheses
already force `A` to be finite type over `R`. -/
theorem iff_localizationAway_unitIdeal
    (s : Finset A) (hs : Ideal.span (s : Set A) = ⊤) :
    FinitePresentationRelativeTo R A M ↔
      ∀ f : s, FinitePresentationRelativeTo R (Localization.Away f.1) (Away f.1 M) := by
  sorry

end Module.FinitePresentationRelativeTo

end
