import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the canonical scheme-side owners `AlgebraicGeometry.IsEtale` and
  `AlgebraicGeometry.LocallyQuasiFinite`;
- local Chapter 29 precedent already records the unramified-to-locally-quasi-finite bridge in
  `Lemma_29_35_10.lean`, so this item is stated as the source-facing étale specialization.
-/

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- Lemma 29.36.6: an étale morphism is locally quasi-finite. -/
@[stacks 03WS]
theorem etale_locallyQuasiFinite (hf : Etale f) :
    LocallyQuasiFinite f := sorry

end AlgebraicGeometry
