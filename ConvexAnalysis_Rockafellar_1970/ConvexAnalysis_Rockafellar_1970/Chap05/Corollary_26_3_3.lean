import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_16_3_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_26_1_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Text_26_0_1

noncomputable section

open scoped Rockafellar

universe u v

section

variable {E : Type u} {F : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 26.3.3 says that if `f` is closed proper convex and essentially
  smooth, and if a surjective linear map `A` satisfies the source qualification
  `A* y* ∈ ri(dom f*)` for some `y*`, then the linear image `Af` is essentially smooth.
- `core/canonical`: the project owners already present are `Function.IsClosedProperConvex`,
  `Function.IsEssentiallySmooth`, Fenchel conjugation `f⋆`, the relative-domain notation
  `riDom(·)`, the linear-image owner `Function.linearImage` with notation `A ◁ f`, and the
  Euclidean adjoint `A.adjoint`.
- `bridge/view`: the source notation `Af` is rendered directly by `A ◁ f`, and the qualification
  `A* y* ∈ ri(dom f*)` is rendered as `A.adjoint yStar ∈ riDom(f⋆)`.

Domain-style sampling used here:
- `Function.linearImage` and the notation `A ◁ f` from `Theorem_16_3_1`;
- `Function.IsEssentiallySmooth` from `Definition_26_1_1`;
- `Function.IsClosedProperConvex.
  isEssentiallyStrictlyConvex_iff_convexConjugate_isEssentiallySmooth`
  from `Theorem_26_3`;
- `Function.subdifferentialAt_comp_linearMap_eq_adjoint_image_of_riDom_or_polyhedral`
  from `Theorem_23_9`;
- Fenchel conjugation `f⋆` and adjoints `A.adjoint`.

Primitive data vs derived API:
- primitive inputs: the function `f`, the surjective linear map `A`, the canonical closed-proper-
  convex owner rebuilt from the genuinely extra closedness hypothesis `LowerSemicontinuous f`
  together with the convexity and properness fields already carried by `f.IsEssentiallySmooth`,
  and the source qualification `∃ yStar, A.adjoint yStar ∈ riDom(f⋆)`;
- derived API: essential smoothness of the source-facing linear image `A ◁ f`.

Layer target: `source-facing`, stated directly on the canonical owner `A ◁ f` rather than on a
surrogate package built from `(f⋆ ∘ A.adjoint)⋆`, and with the closed/proper/convex input carried
by the Chapter 26 owner pattern `LowerSemicontinuous f` plus `f.IsEssentiallySmooth`, rather
than by a redundant `f.IsClosedProperConvex` binder in the theorem surface.
-/

namespace Function.IsClosedProperConvex

-- Proof sketch: combine `hclosed` with the convexity and properness fields already carried by
-- `hess` to build the canonical owner `hf : f.IsClosedProperConvex`. Apply Theorem 26.3 to turn
-- essential smoothness of `f` into
-- essential strict convexity of `f⋆`. Theorem 16.3.1 identifies the conjugate of the linear image
-- `A ◁ f` with the precomposition `f⋆ ∘ A.adjoint`. Using Theorem 23.9 and surjectivity of `A`
-- (hence injectivity of `A.adjoint`), show that `f⋆ ∘ A.adjoint` is essentially strictly convex
-- under the source qualification `∃ yStar, A.adjoint yStar ∈ riDom(f⋆)`. Apply Theorem 26.3 again
-- to conclude that `A ◁ f` is essentially smooth.
/-- Corollary 26.3.3: let `f` be a closed proper convex function on the ambient finite-dimensional
real inner-product space `E`, and let `A : E →ₗ[ℝ] F` be surjective. If `f` is essentially smooth
and there exists `yStar : F` with `A.adjoint yStar ∈ ri(dom f⋆)`, rendered by
`A.adjoint yStar ∈ riDom(f⋆)`, then the linear image `A ◁ f` is essentially smooth. -/
theorem linearImage_isEssentiallySmooth_of_isEssentiallySmooth_of_exists_adjoint_mem_riDom_conjugate
    {f : E → WithBotTop ℝ} (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth)
    (A : E →ₗ[ℝ] F) (hA : Function.Surjective A)
    (hri : ∃ yStar : F, A.adjoint yStar ∈ riDom(f⋆)) :
    (A ◁ f).IsEssentiallySmooth := sorry

end Function.IsClosedProperConvex

end
