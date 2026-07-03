import Nesterov.Chap01.Definition_1_4_16
import Nesterov.Chap03.Definition_3_1_1_3
import Nesterov.Chap05.Definition_5_0_27

-- Declarations for this item will be appended below by the statement pipeline.

open scoped ConvexAnalysis Gradient WithTopConvexAnalysis

noncomputable section

universe u

/- Proposition 5.0.29 lies in the chapter's Fenchel-conjugacy / gradient-Hessian duality domain.

Primary domain:
- differentiability of the finite real part of the canonical Fenchel dual under a globally unique
  Fenchel-support maximizer hypothesis, together with the inverse-Hessian duality at interior
  maximizing primal points.

Relevant owner-style declarations sampled before refinement:
- `dom` and `extendedRealRealPart` in `Chap03/Definition_3_1_1_3`, the chapter owners for the
  effective domain and finite real part of an `EReal`-valued function;
- `fenchelDual` / notation `f⋆` in `Chap05/Definition_5_0_27`, the chapter owner for the
  Fenchel conjugate of a `WithTop ℝ`-valued function;
- `hessian` in `Chap01/Definition_1_4_16`, the chapter owner for second derivatives of real-valued
  functions on complete real inner-product spaces;
- `IsMaxOn`, the canonical maximizer predicate for the Fenchel support functional
  `y ↦ ⟪s, y⟫ - f y` on `dom f`.

Best owner abstraction:
- source-facing: the unique Fenchel-support maximizer realization of the canonical Fenchel dual
  value and the resulting gradient / inverse-Hessian conclusions, with primal interiority entering
  only in the second-order part;
- core/canonical: `f⋆`, `dom (f⋆)`, `extendedRealRealPart (f⋆)`, `hessian`, and
  `IsMaxOn`;
- bridge/view: the derived Fenchel-dual value identity at a support maximizer.

Primitive data:
- a `WithTop ℝ`-valued primal function `f`;
- for the source-facing gradient statement, a primal-dual point pair `(x, s)` with a unique
  owner-level Fenchel-support maximizer at slope `s`;
- for the second-order bridge statements, a candidate maximizing-point field `xStar` together
  with interior membership of the chosen maximizing points.

Derived API:
- the value identity `extendedRealRealPart (f⋆) s = inner ℝ s (xStar s) - withTopRealPart f
  (xStar s)` at a maximizing point;
- the pointwise gradient and branchwise Hessian-identification conclusions of
  Proposition 5.0.29.

The previous version rebuilt a parallel dual-function parameter `fStar : E → WithTop ℝ` and a
local wrapper around the canonical support-maximizer predicate. Those notions are already owned
upstream by `f⋆`, `dom (f⋆)`, `extendedRealRealPart (f⋆)`, `hessian`, and `IsMaxOn`. This
refinement deletes the duplicate dual layer, rewrites the inverse-Hessian surface through the
chapter owner `hessian`, and states the proposition directly on the canonical support-maximizer
surface. The redundant dual-value equality and raw value-based uniqueness clause are also removed
from the primitive input data: they are downstream consequences of the maximizer hypotheses, not
separate source-level structure. The Euclidean model `EuclideanSpace ℝ (Fin n)` and
finite-dimensionality are not the same issue: the Euclidean display model is unnecessary, but the
chapter's available differentiability bridge for this Fenchel-maximizer argument is only
finite-dimensional. The file therefore stays on the canonical owner level of a finite-dimensional
real inner-product space rather than claiming a new infinite-dimensional theorem. -/

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section

variable {f : E → WithTop ℝ} {xStar : E → E}

-- Proof sketch: use the unique active Fenchel-support maximizer `x` at slope `s` to identify the
-- supporting affine function that realizes `(f⋆) s`; the finite real part of `f⋆` is then
-- differentiable at `s` with gradient `x`. The dual-domain membership is derived from the
-- maximizer hypothesis via the owner-level Fenchel value identity rather than stored as primitive
-- input.
/-- Proposition 5.0.29 (1): if `x` is the unique Fenchel-support maximizer of `f` on `dom f` at
the slope `s`, then the finite real part of `f⋆` has gradient `x` at `s`. This is the
source-facing owner statement: the uniqueness of the active maximizer is the mathematical input,
while primal-side first-order or interior hypotheses belong only to later proof routes and
second-order bridge theorems. The ambient finite-dimensionality is part of the justified owner
layer here, because the project's subgradient-to-gradient bridge is only developed in that
setting. -/
theorem fenchelConjugate_hasGradientAt
    {s x : E}
    (hx : x ∈ dom f)
    (hmax : IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x)
    (hunique :
      ∀ ⦃y : E⦄, y ∈ dom f →
        IsMaxOn (fun z : E ↦ inner ℝ s z - withTopRealPart f z) (dom f) y → y = x) :
    HasGradientAt (extendedRealRealPart (f⋆)) x s := sorry

section HessianTransfer

-- Proof sketch: differentiate the first-order condition `∇ (withTopRealPart f) (xStar s) = s`
-- at the unique maximizing point and use the invertibility of the primal Hessian at `xStar s` to
-- identify the dual Hessian with the inverse Hessian operator of `f` there.
/-- Proposition 5.0.29 (2): under the same unique Fenchel-support maximizer hypotheses, and
assuming `withTopRealPart f` is `C²` on `interior (dom f)` and the primal Hessian is invertible
at those maximizing points, the Hessian of the finite real part of `f⋆` at `s` is the inverse
Hessian operator of `f` at `xStar s`. As in part (1), this theorem stays at the
finite-dimensional owner level justified by the chapter's first-order differentiability bridge. -/
theorem fenchelConjugate_hessian_eq_inverse
    (hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)))
    (hxStar_mem : ∀ ⦃s : E⦄, s ∈ dom (f⋆) → xStar s ∈ interior (dom f))
    (hxStar_isMaximizer :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) (xStar s))
    (hxStar_unique :
      ∀ ⦃s x : E⦄, s ∈ dom (f⋆) → x ∈ dom f →
        IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x → x = xStar s)
    (hxStar_hessian_invertible :
      ∀ ⦃s : E⦄, s ∈ dom (f⋆) →
        (hessian (withTopRealPart f) (xStar s)).IsInvertible)
    {s : E} (hs : s ∈ dom (f⋆)) :
    hessian (extendedRealRealPart (f⋆)) s =
      (hessian (withTopRealPart f) (xStar s)).inverse := sorry

-- Proof sketch: derive `s ∈ dom (f⋆)` from the Fenchel-support maximizer hypothesis at `x`, use
-- first-order optimality on the interior point `x` to recover `s = ∇ (withTopRealPart f) x`,
-- and then apply the owner-level inverse-Hessian identity. Global uniqueness identifies the
-- interior primal point `x` with `xStar s`, so the primal Hessian term rewrites directly at `x`.
/-- Proposition 5.0.29 (2), gradient-point form: if `withTopRealPart f` is `C²` on
`interior (dom f)`, `x ∈ interior (dom f)` is the unique Fenchel-support maximizer for the slope
`s`, and the primal Hessian is invertible at `x`, then the Hessian of the finite real part of
`f⋆` at `s` is the inverse Hessian operator of `f` at `x`. The dual-domain membership and
first-order identity are derived internally from the interior maximizer hypothesis, so they do
not appear as primitive inputs. -/
theorem fenchelConjugate_hessian_eq_inverse_of_fenchelSupport_isMaxOn {s x : E}
    (hf_contDiff : ContDiffOn ℝ 2 (withTopRealPart f) (interior (dom f)))
    (hx : x ∈ interior (dom f))
    (hx_isMaximizer :
      IsMaxOn (fun y : E ↦ inner ℝ s y - withTopRealPart f y) (dom f) x)
    (hx_unique :
      ∀ ⦃y : E⦄, y ∈ dom f →
        IsMaxOn (fun z : E ↦ inner ℝ s z - withTopRealPart f z) (dom f) y → y = x)
    (hx_hessian_invertible : (hessian (withTopRealPart f) x).IsInvertible) :
    hessian (extendedRealRealPart (f⋆)) s =
      (hessian (withTopRealPart f) x).inverse := sorry

end HessianTransfer

end
