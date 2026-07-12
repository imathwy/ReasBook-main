import Mathlib
import StacksProject_2024.Chap29.Lemma_29_34_7

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} {f : X ⟶ Y}

/- Semantic recall / analogue check:
- `lean_leansearch` recalled the canonical scheme-side instance
  `AlgebraicGeometry.IsEtale.instIsSmooth`;
- the local Chapter 29 bridge `smooth_syntomic` already upgrades the canonical smooth owner to the
  source-facing syntomic owner `Syntomic f`.
-/

/-- Lemma 29.36.10: an étale morphism is syntomic. -/
@[stacks 02GQ]
theorem etale_syntomic (hf : Etale f) :
    Syntomic f := by
  letI : Etale f := hf
  exact smooth_syntomic (inferInstance : Smooth f)

end AlgebraicGeometry
