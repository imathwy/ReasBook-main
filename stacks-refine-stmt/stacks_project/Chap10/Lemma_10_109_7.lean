import stacks_project.Chap10.Lemma_10_109_5
import stacks_project.Chap10.Lemma_10_109_6

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open CategoryTheory

section

variable {R : Type u} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
variable {M : Type v} [AddCommGroup M] [Module R M] [Module.Finite R M]

/- Domain-style sampling:
* primary domain: bounded finite free resolutions of finite modules over local Noetherian rings;
* sampled declarations:
  `ChainComplex.IsFiniteFreeResolution`,
  `HasFiniteFreeResolutionLengthLE`,
  `ModuleCat.HasFiniteProjectiveResolutionLengthLEWithFiniteTerms`,
  `ChainComplex.IsFiniteFreeResolution`,
  `projective_module_free_of_isLocalRing`;
* best owner abstraction: `HasFiniteFreeResolutionLengthLE R M d`, built from
  `ChainComplex.IsFiniteFreeResolution`;
* layer triage: `HasFiniteFreeResolutionLengthLE` is `source-facing`, while this item is the
  `bridge/view` from projective dimension to that owner;
* primitive data: a bounded augmented chain complex with `IsFiniteFreeResolution`;
* derived API: the coordinate-level finite-projective exact sequence of Lemma `10.109.6` is only a
  bridge into this owner abstraction.
-/

-- Proof sketch: Lemma `10.109.6` provides a bounded finite-projective resolution with finite
-- terms. Over a local ring, Theorem `10.85.4` upgrades each projective term to a free term, so
-- the same bounded resolution yields a bounded finite free resolution. Conversely, a bounded
-- finite free resolution is in particular a bounded free resolution, hence gives projective
-- dimension at most `d`.
/-- Lemma 10.109.7: for a finite module over a local Noetherian ring, having projective dimension
at most `d` is equivalent to admitting a finite free resolution of length at most `d`. -/
theorem hasProjectiveDimensionLE_iff_hasFiniteFreeResolutionLengthLE
    (d : ℕ) :
    HasProjectiveDimensionLE (ModuleCat.of R M) d ↔
      HasFiniteFreeResolutionLengthLE R M d := sorry

end
