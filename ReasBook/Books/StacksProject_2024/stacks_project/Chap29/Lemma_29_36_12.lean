import Mathlib.AlgebraicGeometry.Morphisms.Etale

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

/- Semantic recall / analogue check:
- mathlib's canonical scheme-side owners for this item are `AlgebraicGeometry.Etale` and
  `AlgebraicGeometry.Flat`;
- the consequence `[Etale f] : Flat f` is already available directly by typeclass inference, so the
  Stacks item is kept as a thin source-facing theorem with an explicit `Etale f` premise on the
  canonical owners rather than a new local bridge layer.
-/

/-- Lemma 29.36.12: an étale morphism is flat. -/
@[stacks 02GS]
theorem etale_flat (hf : Etale f) :
    Flat f := by
  letI := hf
  infer_instance

end AlgebraicGeometry
