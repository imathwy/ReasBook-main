import Mathlib
import StacksProject_2024.Chap10.Definition_10_109_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open IsLocalRing

universe u v

section

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
variable {I : Ideal R}
variable {E : Type v} [AddCommGroup E] [Module (R ⧸ I) E] [Module.Finite (R ⧸ I) E]

/-
Domain-style sampling:
* primary domain: projective dimension and the Auslander--Buchsbaum formula for finite modules over
  Noetherian local rings, together with restriction of scalars along a quotient map;
* sampled owner declarations:
  `projectiveDimension`,
  `projectiveDimension_ne_top_iff`,
  `projectiveDimension_le_iff`,
  `projectiveDimension_eq_bot_iff`,
  `ringDepth_eq_projectiveDimension_add_moduleDepth`,
  `ModuleCat.restrictScalars`,
  `ModuleCat.isPerfect_iff_exists_finiteProjectiveResolutionLengthLEWithFiniteTerms`;
* source/core/bridge triage:
  `source-facing`: the additive change-of-rings formula for a finite `(R ⧸ I)`-module;
  `core/canonical`: `projectiveDimension` on `ModuleCat` objects and `moduleDepth`;
  `bridge/view`: the categorical restriction functor `ModuleCat.restrictScalars
    (Ideal.Quotient.mk I)`, used directly through the canonical object
    `((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of (R ⧸ I) E))`;
* primitive data: the canonical module-category objects `ModuleCat.of R (R ⧸ I)`,
  `ModuleCat.of (R ⧸ I) E`, and the restricted object
  `((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of (R ⧸ I) E))`;
* derived API: the hypotheses `projectiveDimension _ ≠ ⊤`, the zero-module fallback via
  `projectiveDimension_eq_bot_iff`, and the resulting additive equality.
-/

-- Proof sketch: reinterpret finite projective dimension as perfectness for finite modules, use the
-- finiteness of `R ⧸ I` over `R` together with the perfectness of `E` over `R ⧸ I`, and then apply
-- the change-of-rings result from the perfect derived category to conclude that `E` is perfect,
-- hence has finite projective dimension over `R` after viewing `E` as an `R`-module by
-- restriction of scalars along `Ideal.Quotient.mk I`.
/- Internal finiteness step used in the additive formula below. -/
theorem projectiveDimension_ne_top_of_idealQuotient_module
    (hRQuot : projectiveDimension (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (hEQuot : projectiveDimension (ModuleCat.of (R ⧸ I) E) ≠ ⊤) :
    projectiveDimension
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of (R ⧸ I) E)) ≠
      ⊤ := sorry

-- Proof sketch: first use the companion theorem to know that `E` has finite projective dimension
-- over `R`. Then apply Auslander--Buchsbaum to `E` over `R`, to `E` over `R ⧸ I`, and to the
-- quotient ring `R ⧸ I` over `R`; finally use that the depth of `E` computed over `R` agrees with
-- the depth computed over `R ⧸ I` to eliminate the depth terms and obtain the stated sum formula;
-- when `E = 0`, both projective dimensions of `E` are `⊥`, so the identity reduces to the
-- canonical `WithBot` arithmetic.
/-- Lemma 15.103.4: for a finite `(R ⧸ I)`-module `E` over a Noetherian local ring `R`, if `R ⧸ I`
has finite projective dimension as an `R`-module and `E` has finite projective dimension as an
`(R ⧸ I)`-module, then the projective dimension of the restricted `R`-module
`RestrictScalars R (R ⧸ I) E` is the sum of the projective dimension of `R ⧸ I` over `R` and the
projective dimension of `E` over `R ⧸ I`. -/
theorem projectiveDimension_idealQuotient_module_eq_add
    (hRQuot : projectiveDimension (ModuleCat.of R (R ⧸ I)) ≠ ⊤)
    (hEQuot : projectiveDimension (ModuleCat.of (R ⧸ I) E) ≠ ⊤) :
    projectiveDimension
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj (ModuleCat.of (R ⧸ I) E)) =
      projectiveDimension (ModuleCat.of R (R ⧸ I)) +
        projectiveDimension (ModuleCat.of (R ⧸ I) E) := sorry

end
