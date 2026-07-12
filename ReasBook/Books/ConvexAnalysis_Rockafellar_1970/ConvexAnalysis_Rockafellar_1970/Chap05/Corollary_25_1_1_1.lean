import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap02.Text_7_0_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_7_4
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Gradient Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 25.1.1.1 compares differentiability of a convex function with
  differentiability of its closure at a point of `interior (dom f)`, and then identifies the two
  gradients.
- `core/canonical`: the Chapter 2 closure owner is `lowerSemicontinuousHull`, written `cl(·)`,
  while the finite real branch used by the calculus API is `Function.realBranch`.
- `bridge/view`: the textbook phrase "`cl f` is differentiable at `x`" is rendered by the
  differentiability of the canonical real branch `((cl(f)).realBranch)` at `x`.

Domain-style sampling used here:
- `lowerSemicontinuousHull` / `cl(·)` from `Chap02.Text_7_0_4`;
- `Function.realBranch` from `Chap02.Theorem_10_4`;
- `Function.IsConvex.lowerSemicontinuousHull_eqOn_off_intrinsicFrontier_dom_of_isProper` from
  `Chap02.Theorem_7_4`, which is the closure-comparison owner behind the corollary;
- `HasFDerivAt.congr_of_eventuallyEq` from mathlib's Fréchet derivative API;
- `HasGradientAt.congr_of_eventuallyEq` and `HasGradientAt.gradient` from mathlib's gradient API.

Primitive data vs derived API:
- primitive inputs: a proper convex function `f : E → WithBotTop ℝ` and a point
  `x ∈ interior (dom f)`;
- bridge data: the real branches of `f` and `cl(f)` agree on a neighborhood of every
  `x ∈ interior (dom f)`;
- core/canonical API: equivalence of `HasFDerivAt` and differentiability for the real branches of
  `f` and `cl(f)`;
- derived bridge API: `HasGradientAt` and gradient equality for the same branch pair in the
  inner-product specialization.

Layer target: `core/canonical` first on `HasFDerivAt`, with `HasGradientAt`/`∇` kept as
`bridge/view` consequences in the inner-product specialization.
-/

namespace Function.IsConvex

variable {f : E → WithBotTop ℝ}

/-- At every point of `interior (dom f)`, the real branches of `f` and its closure `cl(f)` agree
on a neighborhood of that point. This is the local branch form of Theorem 7.4. -/
theorem closure_realBranch_eventuallyEq_realBranch
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) {x : E}
    (hx : x ∈ interior (dom(f))) :
    ((cl(f)).realBranch) =ᶠ[nhds x] f.realBranch := by
  have hEqOn : Set.EqOn (cl(f)) f (rb[ℝ](dom(f)))ᶜ :=
    hf_convex.lowerSemicontinuousHull_eqOn_off_intrinsicFrontier_dom_of_isProper hf_proper
  have hx_dom : x ∈ dom(f) := interior_subset hx
  have hx_not_rb : x ∉ rb[ℝ](dom(f)) := by
    intro hx_rb
    exact ((mem_interior_iff_notMem_frontier hx_dom).1 hx) <|
      intrinsicFrontier_subset_frontier hx_rb
  have h_open : IsOpen ((rb[ℝ](dom(f)))ᶜ) := by
    exact
      (isClosed_intrinsicFrontier
        (affineSpan ℝ (dom(f))).closed_of_finiteDimensional).isOpen_compl
  have hEqOnRealBranch : Set.EqOn ((cl(f)).realBranch) f.realBranch (rb[ℝ](dom(f)))ᶜ := by
    intro y hy
    simpa [Function.realBranch] using congrArg EReal.toReal (hEqOn hy)
  exact hEqOnRealBranch.eventuallyEq_of_mem <| h_open.mem_nhds hx_not_rb

-- Proof sketch: `HasFDerivAt` is stable under eventual equality on a neighborhood, and the
-- closure theorem provides the needed eventual equality of the two real branches near `x`.
/-- At an interior point of `dom f`, `HasFDerivAt` for the closure branch
`((cl(f)).realBranch)` is equivalent to `HasFDerivAt` for the original branch `f.realBranch`. -/
theorem hasFDerivAt_closure_realBranch_iff_hasFDerivAt_realBranch
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) {x : E} {f' : E →L[ℝ] ℝ}
    (hx : x ∈ interior (dom(f))) :
    HasFDerivAt ((cl(f)).realBranch) f' x ↔ HasFDerivAt f.realBranch f' x := by
  have hEq :
      ((cl(f)).realBranch) =ᶠ[nhds x] f.realBranch :=
    hf_convex.closure_realBranch_eventuallyEq_realBranch hf_proper hx
  constructor
  · intro hfd
    exact hfd.congr_of_eventuallyEq hEq.symm
  · intro hfd
    exact hfd.congr_of_eventuallyEq hEq

-- Proof sketch: the local closure theorem gives eventual equality of `((cl(f)).realBranch)` and
-- `f.realBranch` near `x`. Differentiability is invariant under eventual equality in neighborhoods.
/-- Corollary 25.1.1.1: for a proper convex function `f : E → WithBotTop ℝ` on a
finite-dimensional real normed space and a point `x ∈ interior (dom f)`, differentiability of the
finite real branch `f.realBranch` at `x` is equivalent to differentiability of the closure branch
`((cl(f)).realBranch)` at `x`. This is the canonical branchwise form of the textbook statement
that `f` is differentiable at `x` if and only if `cl f` is differentiable there. -/
theorem differentiableAt_realBranch_iff_differentiableAt_closure_realBranch
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) {x : E}
    (hx : x ∈ interior (dom(f))) :
    DifferentiableAt ℝ f.realBranch x ↔
      DifferentiableAt ℝ ((cl(f)).realBranch) x := by
  have hEq :
      ((cl(f)).realBranch) =ᶠ[nhds x] f.realBranch :=
    hf_convex.closure_realBranch_eventuallyEq_realBranch hf_proper hx
  simpa [iff_comm] using
    (hEq.differentiableAt_iff : DifferentiableAt ℝ ((cl(f)).realBranch) x ↔
      DifferentiableAt ℝ f.realBranch x)

-- Proof sketch: use the core `HasFDerivAt` equivalence and recover equality of the canonical
-- Fréchet derivatives at `x`.
/-- At an interior point of `dom f`, the Fréchet derivatives of `f.realBranch` and
`((cl(f)).realBranch)` are equal whenever `f.realBranch` is differentiable there. -/
theorem fderiv_closure_realBranch_eq_fderiv_realBranch
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) {x : E}
    (hx : x ∈ interior (dom(f))) (hfd : DifferentiableAt ℝ f.realBranch x) :
    fderiv ℝ ((cl(f)).realBranch) x = fderiv ℝ f.realBranch x := by
  have hfd_real : HasFDerivAt f.realBranch (fderiv ℝ f.realBranch x) x := hfd.hasFDerivAt
  have hfd_closure : HasFDerivAt ((cl(f)).realBranch) (fderiv ℝ f.realBranch x) x :=
    (hf_convex.hasFDerivAt_closure_realBranch_iff_hasFDerivAt_realBranch hf_proper hx).2 hfd_real
  exact hfd_closure.fderiv

end Function.IsConvex

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace Function.IsConvex

variable {f : E → WithBotTop ℝ}

/-- At an interior point of `dom f`, `HasGradientAt` for the closure branch
`((cl(f)).realBranch)` is equivalent to `HasGradientAt` for the original branch `f.realBranch`. -/
theorem hasGradientAt_closure_realBranch_iff_hasGradientAt_realBranch
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) {x g : E}
    (hx : x ∈ interior (dom(f))) :
    HasGradientAt ((cl(f)).realBranch) g x ↔ HasGradientAt f.realBranch g x := by
  simpa [hasGradientAt_iff_hasFDerivAt] using
    (hf_convex.hasFDerivAt_closure_realBranch_iff_hasFDerivAt_realBranch
      (hf_proper := hf_proper) (x := x) (f' := (InnerProductSpace.toDual ℝ E) g) hx)

-- Proof sketch: the `HasGradientAt` bridge transfers the canonical gradient witness of
-- `f.realBranch` at `x` to `((cl(f)).realBranch)`, and `HasGradientAt.gradient` then identifies
-- the closure gradient with the original one.
/-- At an interior point of the effective domain of a proper convex function, the gradient of the
closure branch `((cl(f)).realBranch)` agrees with the gradient of the original real branch
`f.realBranch` whenever these branch functions are differentiable there. -/
theorem gradient_closure_realBranch_eq_gradient_realBranch
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) {x : E}
    (hx : x ∈ interior (dom(f))) (hfd : DifferentiableAt ℝ f.realBranch x) :
    ∇ ((cl(f)).realBranch) x = ∇ f.realBranch x := by
  have hgrad : HasGradientAt f.realBranch (∇ f.realBranch x) x := hfd.hasGradientAt
  have hcl_grad : HasGradientAt ((cl(f)).realBranch) (∇ f.realBranch x) x :=
    (hf_convex.hasGradientAt_closure_realBranch_iff_hasGradientAt_realBranch hf_proper hx).2 hgrad
  exact hcl_grad.gradient

end Function.IsConvex

end
