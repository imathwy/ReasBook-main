import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

universe u

namespace AlgebraicGeometry

variable {X S : Scheme.{u}} {f : X ⟶ S}

/- Semantic recall:
- `lean_leansearch` found `AlgebraicGeometry.Scheme.Hom.isOpenMap`, the canonical bridge from
  `UniversallyOpen f` to openness of the underlying map `f.base`;
- nearby Chapter 29 entries record the dependency chain `Etale f` gives flatness and local finite
  presentation, and flat plus locally finite presentation gives universal openness. The
  source-facing conclusion here is therefore the weaker textbook claim `IsOpenMap f.base`.
-/

/-- Lemma 29.36.13: an étale morphism is open. -/
@[stacks 03WT]
theorem etale_isOpenMap (hf : Etale f) :
    IsOpenMap f.base := sorry

end AlgebraicGeometry
