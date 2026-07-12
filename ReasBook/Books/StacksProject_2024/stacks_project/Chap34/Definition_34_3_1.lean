import Mathlib
import Mathlib.Tactic.Recall

open AlgebraicGeometry

namespace AlgebraicGeometry

variable (T : Scheme)

/- Domain-style sampling for Definition 34.3.1:
- semantic recall hits: `Scheme.OpenCover`, `Scheme.OpenCover.isOpenCover_opensRange`;
- best owner abstraction: the canonical mathlib owner `T.OpenCover`;
- source/core/bridge triage:
  `source-facing`: a family of morphisms into `T` by open immersions whose images cover `T`;
  `core/canonical`: `T.OpenCover`;
  `bridge/view`: the theorem that the open ranges of the covering morphisms cover `T`, while the
    open-immersion condition is built into the owner by instance inference.

This item is therefore a pure canonical recall, not a place for a parallel alias such as
`ZariskiCovering`. -/

/- Definition 34.3.1: for a scheme `T`, a Zariski covering of `T` is the canonical owner
`T.OpenCover`. Its members are morphisms into `T`, each component is an open immersion, and their
images cover `T`. -/
recall Scheme.OpenCover

/- Companion recall: for `𝒰 : T.OpenCover`, the open subsets `Scheme.Hom.opensRange (𝒰.f i)` form
an open cover of `T`. -/
recall Scheme.OpenCover.isOpenCover_opensRange

end AlgebraicGeometry
