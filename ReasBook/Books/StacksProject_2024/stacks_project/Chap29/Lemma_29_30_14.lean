import Mathlib
import StacksProject_2024.Chap29.Lemma_29_28_4
import StacksProject_2024.Chap29.Lemma_29_30_10
import StacksProject_2024.Chap29.Lemma_29_30_13

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

/- Semantic recall / analogue check:
- `lean_leansearch` recalled `IsLocallyConstant` as the canonical topological owner;
- local Chapter 29 precedent already packages the source quantity `dim_x(X_{f(x)})` as
  `Scheme.Hom.fiberDimensionAt`, while syntomicity on schemes is tracked through
  `LocallyOfType RingHom.Syntomic`.
-/

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- Lemma 29.30.14: if `f : X ⟶ S` is syntomic, then the function sending `x` to the local
dimension `dim_x(X_{f(x)})` of the fiber over `f(x)` is locally constant on `X`. In the Chapter 29
scheme-level owner, this is the local constancy of `f.fiberDimensionAt`. -/
@[stacks 02K1]
theorem isLocallyConstant_fiberDimensionAt_of_syntomic
    (hf : LocallyOfType RingHom.Syntomic f) :
    IsLocallyConstant (fun x : X ↦ f.fiberDimensionAt x) := sorry

end Scheme.Hom

end AlgebraicGeometry
