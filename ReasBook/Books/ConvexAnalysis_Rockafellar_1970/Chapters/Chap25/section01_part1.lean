import Mathlib
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_25_1_1 (from Chap05) -/
noncomputable section

open scoped Gradient RealInnerProductSpace Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [Sub E]
variable {U : Set E} {f : E → 𝕜}

/-!
Source/core/bridge triage:

- `core/canonical`: Corollary 25.1.1 is first recorded on the intrinsic relative
  subdifferential owner `∂ᵣ[Y]f(· | U)` at pairing level.
- `source-facing`: the Fréchet-derivative monotonicity statement is derived from the canonical
  owner using singleton subdifferential identification from Theorem 25.1.
- `bridge/view`: Euclidean gradient (`∇`) and Fréchet-Riesz (`toDual`) forms are derived
  companion views in later sections.

Domain-style sampling used here:
- `_root_.mem_subdifferentialWithinAt_pairing` from `Definition_25_1`;
- `Function.subdifferentialWithinAt_eq_singleton_fderiv` from `Theorem_25_1`
  for the scalar Fréchet bridge below;
- `InnerProductSpace.toDualMap`, `InnerProductSpace.toDual`, and `StrongDual` for Euclidean
  bridge theorems in later sections.

Primitive data vs derived API:
- primitive data: two owner-membership hypotheses
  `xStar ∈ ∂ᵣ[Y]f(x | U)` and `yStar ∈ ∂ᵣ[Y]f(y | U)` at points `x, y ∈ U`;
- source-facing derivative data: in the scalar Fréchet section below, convexity plus
  relative-interior differentiability assumptions giving singleton owner descriptions at `x` and
  `y`;
- derived API: the Euclidean inner-product and `toDual` monotonicity forms and their stronger
  on-set differentiability corollaries.

Layer target: intrinsic owner theorem first, then derivative and Euclidean bridge companions.
-/

namespace Function

/-- Corollary 25.1.1, intrinsic owner form: any two points of the relative subdifferential
multifunction satisfy the pairing-monotonicity inequality. This is the canonical pairing-level
owner statement; derivative and gradient versions are bridge corollaries. -/
theorem pairing_sub_nonneg_of_mem_subdifferentialWithinAt
    {Y : Type (max u v)} [Sub Y] [HasPairing E Y 𝕜]
    [HasPairingSubLeft E Y 𝕜] [HasPairingSubRight E Y 𝕜]
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) {xStar yStar : Y}
    (hxStar : xStar ∈ ∂ᵣ[Y]f(x | U)) (hyStar : yStar ∈ ∂ᵣ[Y]f(y | U)) :
    0 ≤ (⟪x - y, xStar - yStar⟫ₚ : 𝕜) := by
  have hxy' :
      toWithTopBotOn f U y ≥
        toWithTopBotOn f U x + (((⟪y - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜)) :=
    (_root_.mem_subdifferentialWithinAt_pairing
      (f := f) (U := U) (x := x) (Y := Y) (xStar := xStar)).1 hxStar y
  have hyx' :
      toWithTopBotOn f U x ≥
        toWithTopBotOn f U y + (((⟪x - y, yStar⟫ₚ : 𝕜) : WithTopBot 𝕜)) :=
    (_root_.mem_subdifferentialWithinAt_pairing
      (f := f) (U := U) (x := y) (Y := Y) (xStar := yStar)).1 hyStar x
  have hxy_coe :
      ((f x + (⟪y - x, xStar⟫ₚ : 𝕜) : 𝕜) : WithTopBot 𝕜) ≤
        (f y : WithTopBot 𝕜) := by
    simpa [ge_iff_le, toWithTopBotOn_of_mem, hx, hy, add_comm, add_left_comm, add_assoc] using hxy'
  have hyx_coe :
      ((f y + (⟪x - y, yStar⟫ₚ : 𝕜) : 𝕜) : WithTopBot 𝕜) ≤
        (f x : WithTopBot 𝕜) := by
    simpa [ge_iff_le, toWithTopBotOn_of_mem, hx, hy, add_comm, add_left_comm, add_assoc] using hyx'
  have hxy : f x + (⟪y - x, xStar⟫ₚ : 𝕜) ≤ f y := (WithTopBot.coe_le_coe).1 hxy_coe
  have hyx : f y + (⟪x - y, yStar⟫ₚ : 𝕜) ≤ f x := (WithTopBot.coe_le_coe).1 hyx_coe
  have hsum : (⟪y - x, xStar⟫ₚ : 𝕜) + (⟪x - y, yStar⟫ₚ : 𝕜) ≤ 0 := by
    linarith
  have hrewrite :
      (⟪y - x, xStar⟫ₚ + ⟪x - y, yStar⟫ₚ : 𝕜) =
        -(⟪x - y, xStar - yStar⟫ₚ : 𝕜) := by
    calc
      (⟪y - x, xStar⟫ₚ + ⟪x - y, yStar⟫ₚ : 𝕜)
          = (⟪y, xStar⟫ₚ - ⟪x, xStar⟫ₚ) + (⟪x, yStar⟫ₚ - ⟪y, yStar⟫ₚ) := by
              rw [HasPairingSubLeft.pairing_sub_left y x xStar,
                HasPairingSubLeft.pairing_sub_left x y yStar]
      _ = -((⟪x, xStar⟫ₚ - ⟪y, xStar⟫ₚ) - (⟪x, yStar⟫ₚ - ⟪y, yStar⟫ₚ)) := by
            abel
      _ = -((⟪x - y, xStar⟫ₚ : 𝕜) - ⟪x - y, yStar⟫ₚ) := by
            rw [HasPairingSubLeft.pairing_sub_left x y xStar,
              HasPairingSubLeft.pairing_sub_left x y yStar]
      _ = -(⟪x - y, xStar - yStar⟫ₚ : 𝕜) := by
            rw [← HasPairingSubRight.pairing_sub_right (x - y) xStar yStar]
  have hneg : -(⟪x - y, xStar - yStar⟫ₚ : 𝕜) ≤ 0 := by
    simpa [hrewrite] using hsum
  exact neg_nonpos.mp hneg

end Function

end

section

variable {𝕜 : Type v}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {U : Set E} {f : E → 𝕜}

namespace Function

/-- Corollary 25.1.1, canonical primitive-derivative form: if `f` is convex on `U` and has
prescribed Fréchet derivatives at two relative-interior points
`x, y ∈ ri[𝕜](U)`, then those derivatives are monotone under evaluation
`StrongDual 𝕜 E × E → 𝕜`. -/
theorem fderiv_monotone_dual_of_hasFDerivAt
    (hf_convex : ConvexOn 𝕜 U f) {x y : E}
    (hx : x ∈ ri[𝕜](U)) (hy : y ∈ ri[𝕜](U))
    {f'x f'y : E →L[𝕜] 𝕜}
    (hfdx : HasFDerivAt f f'x x) (hfdy : HasFDerivAt f f'y y) :
    0 ≤ ((f'x - f'y) (x - y) : 𝕜) := by
  have hxU : x ∈ U := intrinsicInterior_subset hx
  have hyU : y ∈ U := intrinsicInterior_subset hy
  have hsubx : ∂ᵣf(x | U) = ({f'x} : Set (StrongDual 𝕜 E)) :=
    subdifferentialWithinAt_eq_singleton_fderiv hf_convex hx hfdx
  have hsuby : ∂ᵣf(y | U) = ({f'y} : Set (StrongDual 𝕜 E)) :=
    subdifferentialWithinAt_eq_singleton_fderiv hf_convex hy hfdy
  have hxStar : f'x ∈ ∂ᵣf(x | U) := by simp [hsubx]
  have hyStar : f'y ∈ ∂ᵣf(y | U) := by simp [hsuby]
  have hpair :
      0 ≤ (⟪x - y, ((f'x : StrongDual 𝕜 E) - (f'y : StrongDual 𝕜 E))⟫ₚ : 𝕜) :=
    pairing_sub_nonneg_of_mem_subdifferentialWithinAt hxU hyU hxStar hyStar
  have hpair_eq :
      (⟪x - y, ((f'x : StrongDual 𝕜 E) - (f'y : StrongDual 𝕜 E))⟫ₚ : 𝕜) =
        ((f'x - f'y) (x - y) : 𝕜) := rfl
  exact hpair_eq ▸ hpair

/-- Corollary 25.1.1, canonical owner form: if `f` is convex on `U` and differentiable at
two relative-interior points `x, y ∈ ri[𝕜](U)`, then the Fréchet-derivative map is monotone under
evaluation `StrongDual 𝕜 E × E → 𝕜`. -/
theorem fderiv_monotone_dual
    (hf_convex : ConvexOn 𝕜 U f) {x y : E}
    (hx : x ∈ ri[𝕜](U)) (hy : y ∈ ri[𝕜](U))
    (hfdx : DifferentiableAt 𝕜 f x) (hfdy : DifferentiableAt 𝕜 f y) :
    0 ≤ ((fderiv 𝕜 f x - fderiv 𝕜 f y) (x - y) : 𝕜) := by
  simpa [hfdx.hasFDerivAt.fderiv, hfdy.hasFDerivAt.fderiv] using
    (fderiv_monotone_dual_of_hasFDerivAt
      (E := E) (U := U) (f := f) hf_convex hx hy hfdx.hasFDerivAt hfdy.hasFDerivAt)

/-- Corollary 25.1.1, canonical owner form under ambient differentiability at every point of
`U`. -/
theorem fderiv_monotone_dual_of_differentiableAtOn
    (hf_convex : ConvexOn 𝕜 U f) (hfd : ∀ z ∈ U, DifferentiableAt 𝕜 f z)
    {x y : E} (hx : x ∈ ri[𝕜](U)) (hy : y ∈ ri[𝕜](U)) :
    0 ≤ ((fderiv 𝕜 f x - fderiv 𝕜 f y) (x - y) : 𝕜) := by
  exact fderiv_monotone_dual hf_convex hx hy (hfd x (intrinsicInterior_subset hx))
    (hfd y (intrinsicInterior_subset hy))

end Function

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {U : Set E} {f : E → ℝ}

namespace Function

/-- Corollary 25.1.1, Euclidean primitive-gradient bridge form: if `f` is convex on `U` and has
prescribed gradients at two relative-interior points `x, y ∈ ri[ℝ](U)`, then those gradients are
monotone under the canonical dual pairing `StrongDual ℝ E × E → ℝ`. -/
theorem gradient_monotone_dual_of_hasGradientAt
    (hf_convex : ConvexOn ℝ U f) {x y gx gy : E}
    (hx : x ∈ ri[ℝ](U)) (hy : y ∈ ri[ℝ](U))
    (hgx : HasGradientAt f gx x) (hgy : HasGradientAt f gy y) :
    0 ≤
      ((InnerProductSpace.toDualMap ℝ E gx -
          InnerProductSpace.toDualMap ℝ E gy) (x - y) : ℝ) := by
  have hfdx : HasFDerivAt f (InnerProductSpace.toDualMap ℝ E gx) x := by
    simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hgx.hasFDerivAt
  have hfdy : HasFDerivAt f (InnerProductSpace.toDualMap ℝ E gy) y := by
    simpa [InnerProductSpace.toDual_apply_eq_toDualMap_apply] using hgy.hasFDerivAt
  simpa using
    (fderiv_monotone_dual_of_hasFDerivAt
      (E := E) (U := U) (f := f) hf_convex hx hy hfdx hfdy)

/-- Corollary 25.1.1, Euclidean dual-pairing bridge form: if `f` is convex on `U` and
differentiable at two relative-interior points `x, y ∈ ri[ℝ](U)`, then the gradient map is monotone under
the canonical pairing `StrongDual ℝ E × E → ℝ`. -/
theorem gradient_monotone_dual
    (hf_convex : ConvexOn ℝ U f) {x y : E}
    (hx : x ∈ ri[ℝ](U)) (hy : y ∈ ri[ℝ](U))
    (hfdx : DifferentiableAt ℝ f x) (hfdy : DifferentiableAt ℝ f y) :
    0 ≤
      ((InnerProductSpace.toDualMap ℝ E (∇ f x) -
          InnerProductSpace.toDualMap ℝ E (∇ f y)) (x - y) : ℝ) := by
  simpa [hfdx.hasGradientAt.gradient, hfdy.hasGradientAt.gradient] using
    (gradient_monotone_dual_of_hasGradientAt
      (E := E) (U := U) (f := f) hf_convex hx hy hfdx.hasGradientAt hfdy.hasGradientAt)

/-- Corollary 25.1.1, source-facing primitive-gradient bridge form. -/
theorem gradient_monotone_of_hasGradientAt
    (hf_convex : ConvexOn ℝ U f) {x y gx gy : E}
    (hx : x ∈ ri[ℝ](U)) (hy : y ∈ ri[ℝ](U))
    (hgx : HasGradientAt f gx x) (hgy : HasGradientAt f gy y) :
    0 ≤ ⟪gx - gy, x - y⟫ := by
  simpa [InnerProductSpace.toDualMap_apply_apply, inner_sub_left] using
    (gradient_monotone_dual_of_hasGradientAt hf_convex hx hy hgx hgy)

/-- Corollary 25.1.1, source-facing bridge form: if `f` is convex on `U` and differentiable at
two relative-interior points `x, y ∈ ri[ℝ](U)`, then `⟪∇ f x - ∇ f y, x - y⟫ ≥ 0`. -/
theorem gradient_monotone
    (hf_convex : ConvexOn ℝ U f) {x y : E}
    (hx : x ∈ ri[ℝ](U)) (hy : y ∈ ri[ℝ](U))
    (hfdx : DifferentiableAt ℝ f x) (hfdy : DifferentiableAt ℝ f y) :
    0 ≤ ⟪∇ f x - ∇ f y, x - y⟫ := by
  simpa [hfdx.hasGradientAt.gradient, hfdy.hasGradientAt.gradient] using
    (gradient_monotone_of_hasGradientAt hf_convex hx hy hfdx.hasGradientAt hfdy.hasGradientAt)

/-- Corollary 25.1.1, Euclidean dual-pairing bridge form under ambient differentiability at every
point of `U`. -/
theorem gradient_monotone_dual_of_differentiableAtOn
    (hf_convex : ConvexOn ℝ U f) (hfd : ∀ z ∈ U, DifferentiableAt ℝ f z)
    {x y : E} (hx : x ∈ ri[ℝ](U)) (hy : y ∈ ri[ℝ](U)) :
    0 ≤
      ((InnerProductSpace.toDualMap ℝ E (∇ f x) -
          InnerProductSpace.toDualMap ℝ E (∇ f y)) (x - y) : ℝ) := by
  exact gradient_monotone_dual hf_convex hx hy (hfd x (intrinsicInterior_subset hx))
    (hfd y (intrinsicInterior_subset hy))

/-- Corollary 25.1.1, derived textbook-input form: if `f` is convex and ambient-differentiable at
 every point of `U`, then the monotonicity inequality holds for all
`x, y ∈ ri[ℝ](U)`. -/
theorem gradient_monotone_of_differentiableAtOn
    (hf_convex : ConvexOn ℝ U f) (hfd : ∀ z ∈ U, DifferentiableAt ℝ f z)
    {x y : E} (hx : x ∈ ri[ℝ](U)) (hy : y ∈ ri[ℝ](U)) :
    0 ≤ ⟪∇ f x - ∇ f y, x - y⟫ := by
  simpa [InnerProductSpace.toDualMap_apply_apply, inner_sub_left] using
    (gradient_monotone_dual_of_differentiableAtOn hf_convex hfd hx hy)

end Function

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {U : Set E} {f : E → ℝ}

namespace Function

/-- Corollary 25.1.1, Fréchet-Riesz companion form: if `f` is convex on `U` and differentiable at
 two relative-interior points `x, y ∈ ri[ℝ](U)`, then the gradient map is monotone there when
evaluated through the canonical dual pairing. -/
theorem gradient_monotone_toDual
    (hf_convex : ConvexOn ℝ U f) {x y : E}
    (hx : x ∈ ri[ℝ](U)) (hy : y ∈ ri[ℝ](U))
    (hfdx : DifferentiableAt ℝ f x) (hfdy : DifferentiableAt ℝ f y) :
    0 ≤
      (InnerProductSpace.toDual ℝ E (∇ f x) - InnerProductSpace.toDual ℝ E (∇ f y))
        (x - y) := by
  simpa [InnerProductSpace.toDual_apply_apply, InnerProductSpace.toDualMap_apply_apply] using
    (gradient_monotone_dual hf_convex hx hy hfdx hfdy)

/-- Corollary 25.1.1, derived `toDual` form under ambient differentiability at every point of
 `U`. -/
theorem gradient_monotone_toDual_of_differentiableAtOn
    (hf_convex : ConvexOn ℝ U f) (hfd : ∀ z ∈ U, DifferentiableAt ℝ f z)
    {x y : E} (hx : x ∈ ri[ℝ](U)) (hy : y ∈ ri[ℝ](U)) :
    0 ≤
      (InnerProductSpace.toDual ℝ E (∇ f x) - InnerProductSpace.toDual ℝ E (∇ f y))
        (x - y) := by
  simpa [InnerProductSpace.toDual_apply_apply, InnerProductSpace.toDualMap_apply_apply] using
    (gradient_monotone_dual_of_differentiableAtOn hf_convex hfd hx hy)

end Function

end

/-! ### Corollary_25_1_1_1 (from Chap05) -/
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

/-! ### Definition_25_1 (from Chap05) -/
noncomputable section

open scoped Rockafellar
open Function

universe u v

section

variable {𝕜 : Type v} [Add 𝕜] [LE 𝕜]
variable {E : Type u} [Sub E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 25.1 repeatedly uses the subdifferential of a scalar-valued branch
  `f` on a domain `U`, understood through its canonical extension by `+∞` off `U`.
- `core/canonical`: the primitive owner is the pairing-parametric Chapter 23 owner
  `_root_.subdifferentialAt` applied to the canonical extension `Function.toWithTopBotOn f U`.
- `bridge/view`: a Euclidean vector-valued owner is kept separately in the next section as a thin
  Fréchet-Riesz transport bridge.

Domain-style sampling used here:
- `Function.toWithTopBotOn` from `Chap01.Remark_4_4_5`;
- `_root_.subdifferentialAt` and `_root_.mem_subdifferentialAt_pairing` from
  `Chap05.Definition_23_0_6`.

Primitive data vs derived API:
- primitive source data: `f`, `U`, and `x`;
- primitive owner surface: `_root_.subdifferentialWithinAt f U x Y`;
- derived API: pointwise membership in that owner.

Layer target: `core/canonical` owner surface for Chapter 25 statements, with no
inner-product/completeness assumptions in the main owner.
-/

/-- Definition 25.1, canonical owner form: the relative subdifferential of a scalar-valued branch
`f` on `U` at `x` is the Chapter 23 subdifferential of the canonical extension
`Function.toWithTopBotOn f U` at `x`. The codomain is pairing-parametric. -/
abbrev subdifferentialWithinAt (f : E → 𝕜) (U : Set E) (x : E)
    {Y : Type (max u v)} [HasPairing E Y 𝕜] : Set Y :=
  _root_.subdifferentialAt (Y := Y) (toWithTopBotOn f U) x

scoped[Rockafellar] notation "∂ᵣ[" Y "]" f "(" x " | " U ")" =>
  subdifferentialWithinAt f U x Y

@[simp] theorem mem_subdifferentialWithinAt_pairing
    {f : E → 𝕜} {U : Set E} {x : E} {Y : Type (max u v)} [HasPairing E Y 𝕜] {xStar : Y} :
    xStar ∈ ∂ᵣ[Y]f(x | U) ↔
      ∀ z, toWithTopBotOn f U z ≥
        toWithTopBotOn f U x + ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) :=
  Iff.rfl

end

section

variable {𝕜 : Type v} [Semiring 𝕜] [TopologicalSpace 𝕜] [LE 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [HasPairing E (StrongDual 𝕜 E) 𝕜]

/-- Canonical default-dual bridge for Definition 25.1. -/
abbrev subdifferentialWithinAtDual (f : E → 𝕜) (U : Set E) (x : E) : Set (StrongDual 𝕜 E) :=
  _root_.subdifferentialWithinAt (Y := StrongDual 𝕜 E) f U x

scoped[Rockafellar] notation "∂ᵣ" f "(" x " | " U ")" =>
  subdifferentialWithinAtDual f U x

/-- Pairing-level membership form on the default dual codomain `StrongDual 𝕜 E`. -/
theorem mem_subdifferentialWithinAt_default_pairing
    {f : E → 𝕜} {U : Set E} {x : E} {xStar : StrongDual 𝕜 E} :
    xStar ∈ ∂ᵣf(x | U) ↔
      ∀ z, toWithTopBotOn f U z ≥
        toWithTopBotOn f U x + ((⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) :=
  Iff.rfl

end

section

variable {𝕜 : Type v} [NormedField 𝕜] [LE 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Pointwise membership in `subdifferentialWithinAt` specialized to the canonical dual model
`StrongDual 𝕜 E`. -/
@[simp] theorem mem_subdifferentialWithinAt
    {f : E → 𝕜} {U : Set E} {x : E} {xStar : StrongDual 𝕜 E} :
    xStar ∈ ∂ᵣf(x | U) ↔
      ∀ z, toWithTopBotOn f U z ≥
        toWithTopBotOn f U x + ((xStar (z - x) : 𝕜) : WithTopBot 𝕜) := by
  rw [mem_subdifferentialWithinAt_default_pairing (f := f) (U := U) (x := x) (xStar := xStar)]
  change
      (∀ z, toWithTopBotOn f U z ≥ toWithTopBotOn f U x +
        (((HasLinearPairing.pairingLinear (z - x)) xStar : 𝕜) : WithTopBot 𝕜)) ↔
      ∀ z, toWithTopBotOn f U z ≥
        toWithTopBotOn f U x + ((xStar (z - x) : 𝕜) : WithTopBot 𝕜)
  rfl

end

section

variable {𝕜 : Type v} [RCLike 𝕜] [LE 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [InnerProductSpace 𝕜 E]

namespace Function

/-- Euclidean bridge owner for Definition 25.1: transport the canonical dual-valued owner
`_root_.subdifferentialWithinAt` through the Fréchet-Riesz map
`InnerProductSpace.toDualMap 𝕜 E`. -/
abbrev subdifferentialWithinAt (f : E → 𝕜) (U : Set E) (x : E) : Set E :=
  (InnerProductSpace.toDualMap 𝕜 E) ⁻¹' (∂ᵣf(x | U))

scoped[Rockafellar] notation "∂ᵥᵣ" f "(" x " | " U ")" =>
  Function.subdifferentialWithinAt f U x

/-- Membership in the Euclidean bridge owner is equivalent to the source inequality form from
Definition 25.1. -/
@[simp] theorem mem_subdifferentialWithinAt
    {f : E → 𝕜} {U : Set E} {x g : E} :
    g ∈ ∂ᵥᵣf(x | U) ↔
      ∀ z, toWithTopBotOn f U z ≥
        toWithTopBotOn f U x + ((inner 𝕜 g (z - x) : 𝕜) : WithTopBot 𝕜) := by
  change InnerProductSpace.toDualMap 𝕜 E g ∈ ∂ᵣf(x | U) ↔
      ∀ z, toWithTopBotOn f U z ≥
        toWithTopBotOn f U x + ((inner 𝕜 g (z - x) : 𝕜) : WithTopBot 𝕜)
  rw [_root_.mem_subdifferentialWithinAt (f := f) (U := U) (x := x)
    (xStar := InnerProductSpace.toDualMap 𝕜 E g)]
  simp

end Function

end

/-! ### Theorem_25_1 (from Chap05) -/
noncomputable section

open scoped Gradient RealInnerProductSpace Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {U : Set E} {f : E → 𝕜}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 25.1 identifies the Fréchet derivative of a differentiable convex
  scalar-valued function at an interior point of a convex set with the unique subgradient of its
  canonical extension by `+∞` outside the domain, then records the supporting-hyperplane
  inequality on the domain.
- `core/canonical`: the primitive owner is
  `∂ᵣf(x | U) : Set (StrongDual 𝕜 E)` from Definition 25.1, and the
  derivative-side primitive data are `HasFDerivAt` / `fderiv`.
- `bridge/view`: gradient and inner-product formulations are Euclidean companion views obtained
  from the canonical dual owner through Fréchet-Riesz.

Domain-style sampling used here:
- `isConvex_toWithBotTopOn_iff` from `Chap01.Remark_4_4_5`;
- `∂ᵣf(x | U)` from `Chap05.Definition_25_1`;
- `_root_.mem_subdifferentialAt_iff_le_directionalDerivativeAt` from `Chap05.Theorem_23_2`;
- `Function.directionalDerivativeAt_toWithTopBot_eq_fderiv_apply_of_hasFDerivAt` from
  `Chap05.Lemma_23_0_4`.

Primitive data vs derived API:
- primitive source data: the convex set `U`, the scalar-valued branch `f`, its convexity on
  `U`, pointwise differentiability/Fréchet differentiability at `x`, and a base point
  `x ∈ ri[𝕜](U)`;
- primitive owner surface: `∂ᵣf(x | U)`;
- derived API: singleton descriptions by `fderiv 𝕜` and by the Euclidean gradient, supporting
  inequalities, and the finite-dimensional converse under uniqueness of the owner subdifferential.

Layer target:
- `subdifferentialWithinAt_eq_singleton_fderiv`: `core/canonical`;
- `fderiv_affine_le`: `core/canonical`;
- gradient forms below: `bridge/view`.

Ambient-assumption minimization:
- the canonical owner statements below avoid inner-product/completeness assumptions;
- the gradient forms are kept as Euclidean bridges in the next section.
-/

namespace Function

-- Proof sketch: rewrite `∂ᵣf(x | U)` through the canonical extension
-- `Function.toWithBotTopOn f U`, use convexity of that extension via
-- `isConvex_toWithBotTopOn_iff`, identify its directional derivative by
-- `directionalDerivativeAt_toWithTopBot_eq_fderiv_apply_of_hasFDerivAt`, and apply
-- `_root_.mem_subdifferentialAt_iff_le_directionalDerivativeAt` to obtain the singleton owner.
/-- Theorem 25.1, canonical owner form: for a convex scalar-valued function on `U`, Fréchet
differentiability at a relative-interior point forces the relative subdifferential owner to be the
singleton containing that Fréchet derivative. -/
theorem subdifferentialWithinAt_eq_singleton_fderiv
    (hf_convex : ConvexOn 𝕜 U f) {x : E} (hx : x ∈ ri[𝕜](U)) {f' : E →L[𝕜] 𝕜}
    (hfdx : HasFDerivAt f f' x) :
    ∂ᵣf(x | U) = {f'} := by
  sorry

-- Proof sketch: extract the unique owner subgradient `fderiv 𝕜 f x` from the previous theorem and
-- evaluate the defining support inequality at `z ∈ U`.
/-- Theorem 25.1, canonical affine-support companion: at a relative-interior differentiability point of a
convex scalar-valued branch, the affine functional defined by `fderiv 𝕜 f x` supports `f` on `U`. -/
theorem fderiv_affine_le
    (hf_convex : ConvexOn 𝕜 U f) {x : E} (hx : x ∈ ri[𝕜](U))
    (hfdx : DifferentiableAt 𝕜 f x) {z : E} (hz : z ∈ U) :
    f x + fderiv 𝕜 f x (z - x) ≤ f z := by
  sorry

end Function

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {U : Set E} {f : E → ℝ}

namespace Function

-- Proof sketch: specialize the canonical owner theorem
-- `subdifferentialWithinAt_eq_singleton_fderiv` to `f' = fderiv ℝ f x`, then transport across
-- the Fréchet-Riesz bridge from `StrongDual` to vectors.
/-- Theorem 25.1, canonical dual-owner Euclidean form: for a convex real-valued branch
differentiable at a relative-interior point, the relative dual-valued owner subdifferential is the
singleton containing `InnerProductSpace.toDual ℝ E (∇ f x)`. -/
theorem subdifferentialWithinAt_eq_singleton_toDual_gradient
    (hf_convex : ConvexOn ℝ U f) {x : E} (hx : x ∈ ri[ℝ](U))
    (hfdx : DifferentiableAt ℝ f x) :
    ∂ᵣf(x | U) = {InnerProductSpace.toDual ℝ E (∇ f x)} := by
  sorry

-- Proof sketch: rewrite the Euclidean bridge owner `∂ᵥᵣf(x | U)` as the preimage of
-- `∂ᵣf(x | U)` under `InnerProductSpace.toDualMap`, then use
-- `subdifferentialWithinAt_eq_singleton_toDual_gradient`.
/-- Theorem 25.1, Euclidean bridge owner form: for a convex real-valued function on `U`
differentiable at a relative-interior point `x`, the vector-valued bridge owner
`∂ᵥᵣf(x | U)` is the singleton `{∇ f x}`. -/
theorem subdifferentialWithinAt_eq_singleton_gradient
    (hf_convex : ConvexOn ℝ U f) {x : E} (hx : x ∈ ri[ℝ](U))
    (hfdx : DifferentiableAt ℝ f x) :
    ∂ᵥᵣf(x | U) = {∇ f x} := by
  sorry

-- Proof sketch: either transport `fderiv_affine_le` through Fréchet-Riesz or read off membership
-- of `∇ f x` from the singleton bridge theorem and unfold `mem_subdifferentialWithinAt`.
/-- Theorem 25.1, source-facing Euclidean companion: on a convex set, a real-valued function
differentiable at a relative-interior point `x ∈ ri[ℝ](U)` lies above the affine support determined by
its gradient at every comparison point of the domain. -/
theorem gradient_affine_le
    (hf_convex : ConvexOn ℝ U f) {x z : E} (hx : x ∈ ri[ℝ](U))
    (hfdx : DifferentiableAt ℝ f x) (hz : z ∈ U) :
    f x + ⟪∇ f x, z - x⟫ ≤ f z := by
  sorry

end Function

end

section

variable {𝕜 : Type v}
variable [NontriviallyNormedField 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {U : Set E} {f : E → 𝕜}

namespace Function

-- Proof sketch: uniqueness of the canonical dual-valued owner
-- `∂ᵣf(x | U)` forces first-order support data to be linear in
-- direction; in finite-dimensional normed spaces this upgrades to differentiability of `f`
-- at `x`.
/-- Theorem 25.1, canonical finite-dimensional converse: if the canonical dual-valued relative
subdifferential owner of a convex scalar-valued branch is singleton at a relative-interior point, then the
branch is differentiable there. -/
theorem differentiableAt_of_existsUnique_mem_subdifferentialWithinAt
    (hf_convex : ConvexOn 𝕜 U f) {x : E} (hx : x ∈ ri[𝕜](U))
    (hsub : ∃! xStar : StrongDual 𝕜 E, xStar ∈ ∂ᵣf(x | U)) :
    DifferentiableAt 𝕜 f x := by
  sorry

end Function

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {U : Set E} {f : E → ℝ}

namespace Function

-- Proof sketch: uniqueness of `∂ᵥᵣf(x | U)` forces the Chapter 23 directional
-- derivative map of `Function.toWithBotTopOn f U` at `x` to be linear in the direction variable.
-- In finite dimensions, Rockafellar's
-- converse argument upgrades that linear first-order support data to differentiability of the
-- real-valued branch `f` at the interior point `x`.
/-- Theorem 25.1, Euclidean bridge converse: if the vector-valued bridge owner
`∂ᵥᵣf(x | U)` is singleton at a relative-interior point, then `f` is
differentiable there. -/
theorem differentiableAt_of_existsUnique_mem_subdifferentialWithinAt_vector
    (hf_convex : ConvexOn ℝ U f) {x : E} (hx : x ∈ ri[ℝ](U))
    (hsub : ∃! g : E, g ∈ ∂ᵥᵣf(x | U)) :
    DifferentiableAt ℝ f x := by
  sorry

end Function

end

/-! ### Theorem_25_1_1 (from Chap05) -/
noncomputable section

universe u v

section

variable {𝕜 : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [T2Space (WithBotTop 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 25.1.1 says that if a scalar-valued function is differentiable at `x`,
  then the Rockafellar directional derivative `f'(x; y)` exists in every direction `y`.
- `core/canonical`: the primitive owner layer is `Function.HasDirectionalDerivativeAt` /
  `Function.directionalDerivativeAt`, where differentiability first produces the Fréchet-derivative
  value `fderiv 𝕜 f x y` over a plain normed space.
- `bridge/view`: the gradient pairing `⟪∇ f x, y⟫` is a Euclidean specialization of that
  primitive owner formula, recalled from the upstream Chapter 23 theorem.
- `bridge/view`: mathlib's `lineDeriv` is only a comparison view for the same first-order datum,
  so any `lineDeriv` statement here must remain a thin companion rather than a second owner.

Domain-style sampling used here:
- `Function.HasDirectionalDerivativeAt`;
- `Function.directionalDerivativeAt`;
- `Function.hasDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt`;
- `Function.directionalDerivativeAt_toWithTopBot_eq_fderiv_apply_of_hasFDerivAt`;
- `DifferentiableAt.lineDeriv_eq_fderiv`;

Upstream Euclidean bridge sampling:
- `Function.hasDirectionalDerivativeAt_toWithTopBot_of_hasGradientAt`;
- `Function.directionalDerivativeAt_toWithTopBot_eq_inner_gradient`;

Primitive data vs derived API:
- primitive source input: a differentiable scalar-valued function `f` at `x`;
- primitive owner outputs: the Chapter 23 existence/value statements on `f.toWithBotTop` with
  value `fderiv 𝕜 f x y`;
- derived API: Euclidean gradient pairing formulas and the comparison identity with mathlib's
  scalar-valued `lineDeriv`.

Layer target:
- `Function.hasDirectionalDerivativeAt_toWithBotTop_of_differentiableAt`: `core/canonical`;
- `Function.directionalDerivativeAt_toWithBotTop_eq_fderiv_apply`: `core/canonical`;
- `Function.lineDeriv_toWithBotTop_eq_directionalDerivativeAt`: `core/canonical`;
- `Function.directionalDerivativeAt_toWithTopBot_eq_inner_gradient`: recalled
  `bridge/view` value theorem from Chapter 23.

Ambient-assumption minimization:
- the imported Chapter 23 derivative owners used here are available at the Hausdorff codomain
  layer, so theorem surfaces stay at `[T2Space (WithBotTop 𝕜)]` rather than requiring the stronger
  `[OrderTopology (WithBotTop 𝕜)]`.
-/

namespace Function

/-- Theorem 25.1.1, canonical owner form at the primitive derivative layer: differentiability at
`x` gives the Chapter 23 directional-derivative owner for `f.toWithBotTop`, with value
`fderiv 𝕜 f x y`. -/
theorem hasDirectionalDerivativeAt_toWithBotTop_of_differentiableAt
    {f : E → 𝕜} {x y : E} (hf : DifferentiableAt 𝕜 f x) :
    HasDirectionalDerivativeAt f.toWithBotTop x y (fderiv 𝕜 f x y : WithBotTop 𝕜) := by
  simpa using hasDirectionalDerivativeAt_toWithTopBot_of_hasFDerivAt hf.hasFDerivAt

-- Proof sketch: specialize the Chapter 23 Fréchet-derivative value theorem using
-- `DifferentiableAt.hasFDerivAt`.
/-- Theorem 25.1.1, value form at the primitive derivative layer: for a differentiable
scalar-valued function, the Chapter 23 directional derivative of `f.toWithBotTop` is exactly the
Fréchet derivative evaluation `fderiv 𝕜 f x y`. -/
theorem directionalDerivativeAt_toWithBotTop_eq_fderiv_apply
    {f : E → 𝕜} {x y : E} (hf : DifferentiableAt 𝕜 f x) :
    directionalDerivativeAt f.toWithBotTop x y = (fderiv 𝕜 f x y : WithBotTop 𝕜) := by
  simpa using directionalDerivativeAt_toWithTopBot_eq_fderiv_apply_of_hasFDerivAt hf.hasFDerivAt

-- Proof sketch: compare `lineDeriv` with `fderiv`, then use the Chapter 23 owner-value theorem
-- at the Fréchet derivative layer.
/-- Canonical comparison owner for Theorem 25.1.1: for a differentiable scalar-valued function,
mathlib's `lineDeriv` agrees (after coercion to `WithBotTop 𝕜`) with the Chapter 23 owner
`Function.directionalDerivativeAt` on `f.toWithBotTop`. -/
theorem lineDeriv_toWithBotTop_eq_directionalDerivativeAt
    {f : E → 𝕜} {x y : E} (hf : DifferentiableAt 𝕜 f x) :
    (↑(lineDeriv 𝕜 f x y) : WithBotTop 𝕜) = directionalDerivativeAt f.toWithBotTop x y := by
  calc
    (↑(lineDeriv 𝕜 f x y) : WithBotTop 𝕜) = (↑(fderiv 𝕜 f x y) : WithBotTop 𝕜) := by
      rw [hf.lineDeriv_eq_fderiv]
    _ = directionalDerivativeAt f.toWithBotTop x y := by
      simpa using
        (directionalDerivativeAt_toWithBotTop_eq_fderiv_apply (f := f) (x := x) (y := y) hf).symm

end Function

end

/- Theorem 25.1.1 is already owned upstream by the exact Chapter 23 value theorem for
`Function.directionalDerivativeAt` on `f.toWithBotTop`. -/
recall Function.directionalDerivativeAt_toWithTopBot_eq_inner_gradient

end

/-! ### Corollary_25_1_2 (from Chap05) -/
noncomputable section

open scoped Gradient RealInnerProductSpace Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [Sub E]
variable {U : Set E} {f : E → 𝕜}
variable {Y : Type (max u v)} [HasPairing E Y 𝕜] [HasPairingSubLeft E Y 𝕜]

local notation "fExt" => Function.toWithTopBotOn f U
local notation "fStar" => (fExt⋆ : Y → WithTopBot 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 25.1.2 identifies the geometric consequence of a singleton relative
  subdifferential owner at `x`: the boundary point of the conjugate epigraph `epi fStar` determined
  by that unique subgradient is an exposed point.
- `core/canonical`: this file now uses the canonical Chapter 25 owner
  `∂ᵣ[Y]f(x | U) : Set Y` directly at pairing level; no inner-product model is
  needed at this layer.
- `bridge/view`: the Euclidean gradient specialization appears later as a thin Fréchet-Riesz
  bridge via `InnerProductSpace.toDual`.

Primary mathematical domain:
- exposed points of conjugate epigraphs arising from unique subgradients.

Domain-style sampling used here:
- `epi` / `mem_epi_iff` from `Chap01.Definition_4_1`;
- `Set.exposedPoints` and `mem_exposedPoints_iff_exposed_singleton` from
  `Mathlib.Analysis.Convex.Exposed`;
- `convexConjugate` / `f⋆` from `Chap03.Defn_12_2`;
- `∂ᵣ[·]·(· | ·)` from `Chap05.Definition_25_1`.

Primitive data vs derived API:
- primitive source data: the canonical extension `fExt`, a base point `x ∈ U`, and
  a singleton owner identity `∂ᵣ[Y]f(x | U) = {xStar}`;
- source-facing owner statement: the Fenchel-Young contact point of the conjugate epigraph is
  exposed;
- derived companions: the Fenchel-Young height identity
  `fStar xStar = ⟪x, xStar⟫ₚ - f x`, and its `EReal.toReal` epigraph-height bridge.

Layer target:
- `convexConjugate_eq_apply_sub_of_mem_subdifferentialWithinAt`: `source-facing`;
- `mem_exposedPoints_epi_convexConjugate_of_subdifferentialWithinAt_eq_singleton`:
  `source-facing`;
- `mem_exposedPoints_epi_convexConjugate_of_subdifferentialWithinAt_eq_singleton_toRealHeight`:
  `bridge/view`.
-/

/-- If `xStar` is a relative subgradient of `f` at `x`, then the conjugate of the canonical
extension `fExt` attains the Fenchel-Young equality value `⟪x, xStar⟫ₚ - f x` at `xStar`. -/
theorem convexConjugate_eq_apply_sub_of_mem_subdifferentialWithinAt
    {x : E} {xStar : Y} (hxU : x ∈ U)
    (hxStar : xStar ∈ ∂ᵣ[Y]f(x | U)) :
    fStar xStar = (⟪x, xStar⟫ₚ - f x : 𝕜) := by
  rw [convexConjugate_eq_iSup_pairing_sub]
  apply le_antisymm
  · refine iSup_le ?_
    intro z
    by_cases hzU : z ∈ U
    · have hzineqW :
          (((f x + ⟪z - x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) ≤ (f z : WithTopBot 𝕜)) := by
        have hzineq := (_root_.mem_subdifferentialWithinAt_pairing
            (f := f) (U := U) (x := x) (Y := Y) (xStar := xStar)).1 hxStar z
        simpa [Function.toWithTopBotOn_of_mem (f := f) (C := U) hxU,
          Function.toWithTopBotOn_of_mem (f := f) (C := U) hzU, sub_eq_add_neg,
          add_assoc, add_comm, add_left_comm] using hzineq
      have hzineq : (⟪z, xStar⟫ₚ - f z : 𝕜) ≤ ⟪x, xStar⟫ₚ - f x := by
        have hpair : (⟪z - x, xStar⟫ₚ : 𝕜) = ⟪z, xStar⟫ₚ - ⟪x, xStar⟫ₚ :=
          HasPairingSubLeft.pairing_sub_left z x xStar
        have hzineqW' : (f x + (⟪z, xStar⟫ₚ - ⟪x, xStar⟫ₚ : 𝕜) : 𝕜) ≤ f z := by
          simpa [hpair] using (WithTopBot.coe_le_coe.mp hzineqW)
        linarith
      rw [Function.toWithTopBotOn_of_mem (f := f) (C := U) hzU]
      have hzcoew :
          (((⟪z, xStar⟫ₚ - f z : 𝕜) : WithTopBot 𝕜) ≤ ((⟪x, xStar⟫ₚ - f x : 𝕜) : WithTopBot 𝕜)) :=
        WithTopBot.coe_le_coe.mpr hzineq
      change (((⟪z, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) + -((f z : 𝕜) : WithTopBot 𝕜)) ≤
        ((⟪x, xStar⟫ₚ - f x : 𝕜) : WithTopBot 𝕜)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hzcoew
    · simp [Function.toWithTopBotOn_of_notMem (f := f) (C := U) hzU, sub_eq_add_neg]
  · have hxterm :
      (⟪x, xStar⟫ₚ : 𝕜) - fExt x ≤
        ⨆ z : E, (⟪z, xStar⟫ₚ : 𝕜) - fExt z := by
      exact le_iSup (fun z : E ↦ (⟪z, xStar⟫ₚ : 𝕜) - fExt z) x
    have hxterm_simpl :
        (-((f x : 𝕜) : WithTopBot 𝕜) + ((⟪x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜)) ≤
          ⨆ z : E, -fExt z + ((⟪z, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) := by
      simpa [Function.toWithTopBotOn_of_mem (f := f) (C := U) hxU,
        sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using hxterm
    have hiSup_comm :
        (⨆ z : E, -fExt z + ((⟪z, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜)) =
          ⨆ z : E, ((⟪z, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) + -fExt z := by
      refine iSup_congr ?_
      intro z
      exact add_comm (-fExt z) (((⟪z, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜))
    calc
      ((⟪x, xStar⟫ₚ - f x : 𝕜) : WithTopBot 𝕜)
          = -((f x : 𝕜) : WithTopBot 𝕜) + ((⟪x, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) := by
            simp [sub_eq_add_neg, add_comm]
      _ ≤ ⨆ z : E, -fExt z + ((⟪z, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) := hxterm_simpl
      _ = ⨆ z : E, ((⟪z, xStar⟫ₚ : 𝕜) : WithTopBot 𝕜) + -fExt z := hiSup_comm
      _ = ⨆ z : E, (⟪z, xStar⟫ₚ : 𝕜) - fExt z := by
            simp [sub_eq_add_neg]

end

section

variable {𝕜 : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {Y : Type (max u v)} [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [HasLinearPairing E Y 𝕜] [HasPairingSubLeft E Y 𝕜]
variable [HasPairing Y E 𝕜] [HasPairingSwap E Y 𝕜] [HasContinuousPairing Y E 𝕜]
variable {U : Set E} {f : E → 𝕜}

local notation "fExt" => Function.toWithTopBotOn f U
local notation "fStar" => (fExt⋆ : Y → WithTopBot 𝕜)

/-- If `∂ᵣ[Y]f(x | U) = {xStar}`, then the corresponding
Fenchel-Young contact point of the conjugate epigraph is exposed. -/
theorem mem_exposedPoints_epi_convexConjugate_of_subdifferentialWithinAt_eq_singleton
    {x : E} {xStar : Y} (hxU : x ∈ U)
    (hsub : ∂ᵣ[Y]f(x | U) = {xStar}) :
    (xStar, ⟪x, xStar⟫ₚ - f x) ∈ (epi fStar).exposedPoints 𝕜 := by
  have hxStar : xStar ∈ ∂ᵣ[Y]f(x | U) := by
    simpa [hsub]
  have hvalue : fStar xStar = (⟪x, xStar⟫ₚ - f x : 𝕜) :=
    convexConjugate_eq_apply_sub_of_mem_subdifferentialWithinAt
      (f := f) (U := U) (Y := Y) hxU hxStar
  have hp0_epi : (xStar, ⟪x, xStar⟫ₚ - f x) ∈ epi fStar :=
    (mem_epi_iff).2 (le_of_eq hvalue)
  let pairingAtX : Y →L[𝕜] 𝕜 :=
    { toLinearMap := HasLinearPairing.pairingLinear x
      cont := by
        refine (HasContinuousPairing.continuous_pairing_left (X := Y) (Y := E) (𝕜 := 𝕜) x).congr ?_
        intro y
        simpa using (HasPairingSwap.pairing_swap (X := E) (Y := Y) x y).symm }
  let l : StrongDual 𝕜 (Y × 𝕜) :=
    (pairingAtX.comp (ContinuousLinearMap.fst 𝕜 Y 𝕜)) - ContinuousLinearMap.snd 𝕜 Y 𝕜
  have hl_p0 : l (xStar, ⟪x, xStar⟫ₚ - f x) = f x := by
    change (⟪x, xStar⟫ₚ : 𝕜) - (⟪x, xStar⟫ₚ - f x) = f x
    ring
  rw [exposed_point_def]
  refine ⟨hp0_epi, l, ?_⟩
  intro p hp
  rcases p with ⟨y, μ⟩
  have hyμ : fStar y ≤ μ := (mem_epi_iff.mp hp)
  have hFenchel_x : (((⟪x, y⟫ₚ - f x : 𝕜) : WithTopBot 𝕜) ≤ fStar y) := by
    rw [convexConjugate_eq_iSup_pairing_sub]
    have hxterm :
        (⟪x, y⟫ₚ : 𝕜) - fExt x ≤
          ⨆ z : E, (⟪z, y⟫ₚ : 𝕜) - fExt z := by
      exact le_iSup (fun z : E ↦ (⟪z, y⟫ₚ : 𝕜) - fExt z) x
    rw [Function.toWithTopBotOn_of_mem (f := f) (C := U) hxU] at hxterm
    change (((⟪x, y⟫ₚ - f x : 𝕜) : WithTopBot 𝕜) ≤
      ⨆ z : E, (⟪z, y⟫ₚ : 𝕜) - fExt z)
    have hco :
        (((⟪x, y⟫ₚ - f x : 𝕜) : WithTopBot 𝕜) =
          ((⟪x, y⟫ₚ : WithTopBot 𝕜) - (f x : WithTopBot 𝕜))) := by
      simpa [sub_eq_add_neg, WithTopBot.coe_add, WithTopBot.coe_neg]
    calc
      ((⟪x, y⟫ₚ - f x : 𝕜) : WithTopBot 𝕜) =
          ((⟪x, y⟫ₚ : WithTopBot 𝕜) - (f x : WithTopBot 𝕜)) := hco
      _ = (⟪x, y⟫ₚ : 𝕜) - (f x : WithTopBot 𝕜) := by rfl
      _ ≤ ⨆ z : E, (⟪z, y⟫ₚ : 𝕜) - fExt z := hxterm
  have hxy : (⟪x, y⟫ₚ - f x : 𝕜) ≤ μ :=
    WithTopBot.coe_le_coe.mp (hFenchel_x.trans hyμ)
  have hle_main : l (y, μ) ≤ l (xStar, ⟪x, xStar⟫ₚ - f x) := by
    rw [hl_p0]
    change (⟪x, y⟫ₚ : 𝕜) - μ ≤ f x
    have hle_fx : (⟪x, y⟫ₚ - μ : 𝕜) ≤ f x := by
      linarith [hxy]
    exact hle_fx
  refine ⟨hle_main, ?_⟩
  intro hrev
  have hle_fx : l (y, μ) ≤ f x := by
    rw [hl_p0] at hle_main
    exact hle_main
  have hge_fx : f x ≤ l (y, μ) := by
    rw [hl_p0] at hrev
    exact hrev
  have hl_eq : l (y, μ) = f x := le_antisymm hle_fx hge_fx
  have hmu_eq : μ = ⟪x, y⟫ₚ - f x := by
    have htmp : (⟪x, y⟫ₚ - μ : 𝕜) = f x := by
      have hl_eq' : l (y, μ) = f x := hl_eq
      change ⟪x, y⟫ₚ - μ = f x at hl_eq'
      exact hl_eq'
    have htmp' : μ = ⟪x, y⟫ₚ - f x := by
      linarith [htmp]
    exact htmp'
  have hyEqStar : fStar y = (⟪x, y⟫ₚ - f x : 𝕜) := by
    have hmu_eqW : (μ : WithTopBot 𝕜) = ((⟪x, y⟫ₚ - f x : 𝕜) : WithTopBot 𝕜) :=
      congrArg (fun t : 𝕜 => ((t : 𝕜) : WithTopBot 𝕜)) hmu_eq
    apply le_antisymm
    · exact le_trans hyμ (le_of_eq hmu_eqW)
    · exact hFenchel_x
  have hy_sub : y ∈ ∂ᵣ[Y]f(x | U) := by
    rw [_root_.mem_subdifferentialWithinAt_pairing]
    intro z
    by_cases hzU : z ∈ U
    · have hzSup :
          ((⟪z, y⟫ₚ - f z : 𝕜) : WithTopBot 𝕜) ≤ fStar y := by
        rw [convexConjugate_eq_iSup_pairing_sub]
        have hzterm :
            (⟪z, y⟫ₚ : 𝕜) - fExt z ≤
              ⨆ w : E, (⟪w, y⟫ₚ : 𝕜) - fExt w := by
          exact le_iSup (fun w : E ↦ (⟪w, y⟫ₚ : 𝕜) - fExt w) z
        rw [Function.toWithTopBotOn_of_mem (f := f) (C := U) hzU] at hzterm
        change (((⟪z, y⟫ₚ - f z : 𝕜) : WithTopBot 𝕜) ≤
          ⨆ w : E, (⟪w, y⟫ₚ : 𝕜) - fExt w)
        have hco :
            (((⟪z, y⟫ₚ - f z : 𝕜) : WithTopBot 𝕜) =
              ((⟪z, y⟫ₚ : WithTopBot 𝕜) - (f z : WithTopBot 𝕜))) := by
          simpa [sub_eq_add_neg, WithTopBot.coe_add, WithTopBot.coe_neg]
        calc
          ((⟪z, y⟫ₚ - f z : 𝕜) : WithTopBot 𝕜) =
              ((⟪z, y⟫ₚ : WithTopBot 𝕜) - (f z : WithTopBot 𝕜)) := hco
          _ = (⟪z, y⟫ₚ : 𝕜) - (f z : WithTopBot 𝕜) := by rfl
          _ ≤ ⨆ w : E, (⟪w, y⟫ₚ : 𝕜) - fExt w := hzterm
      have hzSup' : ((⟪z, y⟫ₚ - f z : 𝕜) : WithTopBot 𝕜) ≤ ((⟪x, y⟫ₚ - f x : 𝕜) : WithTopBot 𝕜) := by
        calc
          ((⟪z, y⟫ₚ - f z : 𝕜) : WithTopBot 𝕜) ≤ fStar y := hzSup
          _ = ((⟪x, y⟫ₚ - f x : 𝕜) : WithTopBot 𝕜) := hyEqStar
      have hzSup'' : (⟪z, y⟫ₚ - f z : 𝕜) ≤ ⟪x, y⟫ₚ - f x :=
        WithTopBot.coe_le_coe.mp hzSup'
      have hzineq : (f x + ⟪z - x, y⟫ₚ : 𝕜) ≤ f z := by
        have hpair : (⟪z - x, y⟫ₚ : 𝕜) = ⟪z, y⟫ₚ - ⟪x, y⟫ₚ :=
          HasPairingSubLeft.pairing_sub_left z x y
        linarith [hzSup'', hpair]
      have hzineqW :
          (((f x + ⟪z - x, y⟫ₚ : 𝕜) : WithTopBot 𝕜) ≤ (f z : WithTopBot 𝕜)) :=
        WithTopBot.coe_le_coe.mpr hzineq
      rw [Function.toWithTopBotOn_of_mem (f := f) (C := U) hxU,
        Function.toWithTopBotOn_of_mem (f := f) (C := U) hzU]
      exact hzineqW
    · rw [Function.toWithTopBotOn_of_notMem (f := f) (C := U) hzU]
      exact le_top
  have hy_eq_xStar : y = xStar := by
    simpa [hsub]
      using hy_sub
  have hmu_target : μ = ⟪x, xStar⟫ₚ - f x := by
    calc
      μ = ⟪x, y⟫ₚ - f x := hmu_eq
      _ = ⟪x, xStar⟫ₚ - f x := by rw [hy_eq_xStar]
  exact Prod.ext hy_eq_xStar hmu_target

end

section

variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
variable {U : Set E} {f : E → ℝ}

local instance : HasPairing E (StrongDual ℝ E) ℝ :=
  instHasPairingOfHasLinearPairing

local instance : HasPairingSubLeft E (StrongDual ℝ E) ℝ :=
  instHasPairingSubLeftOfHasLinearPairing

local instance : HasPairing (StrongDual ℝ E) E ℝ :=
  instHasPairingStrongDualPrimal

local instance : HasPairingSwap E (StrongDual ℝ E) ℝ where
  pairing_swap x xStar := rfl

local instance : HasContinuousPairing (StrongDual ℝ E) E ℝ where
  continuous_pairing_left x := by
    simpa using (ContinuousLinearMap.continuous (ContinuousLinearMap.apply ℝ ℝ x))

local notation "fExt" => Function.toWithTopBotOn f U
local notation "fStar" => (fExt⋆ : StrongDual ℝ E → WithTopBot ℝ)

/-- Bridge form of the previous theorem on the canonical real-height epigraph surface:
`EReal.toReal (fStar xStar)` equals the Fenchel-Young height `⟪x, xStar⟫ₚ - f x`. -/
theorem mem_exposedPoints_epi_convexConjugate_of_subdifferentialWithinAt_eq_singleton_toRealHeight
    {x : E} {xStar : StrongDual ℝ E} (hxU : x ∈ U)
    (hsub : ∂ᵣf(x | U) = {xStar}) :
    (xStar, EReal.toReal (fStar xStar)) ∈ (epi fStar).exposedPoints ℝ := by
  have hmain :
      (xStar, ⟪x, xStar⟫ₚ - f x) ∈ (epi fStar).exposedPoints ℝ :=
    mem_exposedPoints_epi_convexConjugate_of_subdifferentialWithinAt_eq_singleton
      hxU hsub
  have hxStar : xStar ∈ ∂ᵣf(x | U) := by
    simp [hsub]
  have hheight : EReal.toReal (fStar xStar) = ⟪x, xStar⟫ₚ - f x := by
    have hheight' :
        EReal.toReal (fStar xStar) = EReal.toReal (⟪x, xStar⟫ₚ - f x : ℝ) :=
      congrArg EReal.toReal
        (convexConjugate_eq_apply_sub_of_mem_subdifferentialWithinAt
          hxU hxStar)
    exact hheight'.trans (EReal.toReal_coe (⟪x, xStar⟫ₚ - f x))
  rw [hheight]
  exact hmain

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
variable {U : Set E} {f : E → ℝ}

local instance : HasPairing E (StrongDual ℝ E) ℝ :=
  instHasPairingOfHasLinearPairing

local instance : HasPairingSubLeft E (StrongDual ℝ E) ℝ :=
  instHasPairingSubLeftOfHasLinearPairing

local instance : HasPairing (StrongDual ℝ E) E ℝ :=
  instHasPairingStrongDualPrimal

local instance : HasPairingSwap E (StrongDual ℝ E) ℝ where
  pairing_swap x xStar := rfl

local instance : HasContinuousPairing (StrongDual ℝ E) E ℝ where
  continuous_pairing_left x := by
    simpa using (ContinuousLinearMap.continuous (ContinuousLinearMap.apply ℝ ℝ x))

namespace Function

local notation "fExt" => toWithTopBotOn f U
local notation "fStar" => (fExt⋆ : StrongDual ℝ E → WithTopBot ℝ)

/-- Corollary 25.1.2 as a Euclidean bridge: if `f` is convex on `U` and differentiable at a
relative-interior point `x ∈ ri[ℝ](U)`, then the dual representative of the gradient determines an
exposed Fenchel-Young contact point on the conjugate epigraph. -/
theorem gradient_mem_exposedPoints_epi_convexConjugate
    (hf_convex : ConvexOn ℝ U f) {x : E} (hx : x ∈ ri[ℝ](U))
    (hfdx : DifferentiableAt ℝ f x) :
    (InnerProductSpace.toDual ℝ E (∇ f x),
      ⟪x, InnerProductSpace.toDual ℝ E (∇ f x)⟫ₚ - f x) ∈
      (epi fStar).exposedPoints ℝ := by
  have hsub :
      ∂ᵣf(x | U) =
        {InnerProductSpace.toDual ℝ E (∇ f x)} :=
    subdifferentialWithinAt_eq_singleton_toDual_gradient hf_convex hx hfdx
  exact mem_exposedPoints_epi_convexConjugate_of_subdifferentialWithinAt_eq_singleton
    (f := f) (U := U)
    (x := x) (xStar := InnerProductSpace.toDual ℝ E (∇ f x))
    (intrinsicInterior_subset hx) hsub

/-- Bridge form of Corollary 25.1.2 on the canonical real-height epigraph surface:
`EReal.toReal (fStar (toDual (∇ f x)))` equals the Fenchel-Young height
`⟪x, toDual (∇ f x)⟫ₚ - f x`. -/
theorem gradient_mem_exposedPoints_epi_convexConjugate_toRealHeight
    (hf_convex : ConvexOn ℝ U f) {x : E} (hx : x ∈ ri[ℝ](U))
    (hfdx : DifferentiableAt ℝ f x) :
    (InnerProductSpace.toDual ℝ E (∇ f x),
      EReal.toReal (fStar (InnerProductSpace.toDual ℝ E (∇ f x)))) ∈
      (epi fStar).exposedPoints ℝ := by
  have hmain :
      (InnerProductSpace.toDual ℝ E (∇ f x),
        ⟪x, InnerProductSpace.toDual ℝ E (∇ f x)⟫ₚ - f x) ∈
        (epi fStar).exposedPoints ℝ :=
    gradient_mem_exposedPoints_epi_convexConjugate hf_convex hx hfdx
  have hsub :
      ∂ᵣf(x | U) =
        {InnerProductSpace.toDual ℝ E (∇ f x)} :=
    subdifferentialWithinAt_eq_singleton_toDual_gradient hf_convex hx hfdx
  have hgrad :
      InnerProductSpace.toDual ℝ E (∇ f x) ∈ ∂ᵣf(x | U) := by
    simp [hsub]
  have hheight :
      EReal.toReal (fStar (InnerProductSpace.toDual ℝ E (∇ f x))) =
        ⟪x, InnerProductSpace.toDual ℝ E (∇ f x)⟫ₚ - f x := by
    have hheight' := congrArg EReal.toReal
      (convexConjugate_eq_apply_sub_of_mem_subdifferentialWithinAt
        (f := f) (U := U) (x := x) (xStar := InnerProductSpace.toDual ℝ E (∇ f x))
        (intrinsicInterior_subset hx) hgrad)
    have hco :
        EReal.toReal (⟪x, InnerProductSpace.toDual ℝ E (∇ f x)⟫ₚ - f x : ℝ) =
          ⟪x, InnerProductSpace.toDual ℝ E (∇ f x)⟫ₚ - f x :=
      EReal.toReal_coe (⟪x, InnerProductSpace.toDual ℝ E (∇ f x)⟫ₚ - f x)
    exact hheight'.trans hco
  rw [hheight]
  exact hmain

end Function

end

/-! ### Theorem_25_1_2 (from Chap05) -/
noncomputable section

open scoped Gradient RealInnerProductSpace

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 25.1.2 is the standard-basis partial-derivative identity on Euclidean
  coordinates: for differentiable `f`, the `j`-th partial derivative is `fderiv` applied to the
  coordinate direction `e_j`; the canonical orthonormal basis vector
  `EuclideanSpace.basisFun ι 𝕜 j` is used as a bridge view.
- `core/canonical`: the ambient owner abstractions are mathlib's `DifferentiableAt`,
  `DifferentiableAt.lineDeriv_eq_fderiv`, and `LineDifferentiableAt` / `lineDeriv`.
- `bridge/view`: the real inner-product gradient formulas are thin corollaries via the
  recalled Chapter 23 gradient-value theorem
  `Function.directionalDerivativeAt_toWithTopBot_eq_inner_gradient`,
  the comparison theorem `Function.lineDeriv_toWithBotTop_eq_directionalDerivativeAt`,
  `∇`, and `EuclideanSpace.inner_basisFun_real`.
- `bridge/view`: this file owns the thin source-facing bridge
  `Function.partialDeriv f x j` for the
  textbook partial derivative `∂f/∂ξ_j (x)`, obtained by specializing the canonical line
  derivative to the coordinate direction `PiLp.single`.

Domain-style sampling used here:
- `DifferentiableAt`;
- `LineDifferentiableAt`;
- `lineDeriv`;
- `DifferentiableAt.lineDeriv_eq_fderiv`;
- `fderiv`;
- `PiLp.single`;
- `Function.lineDeriv_toWithBotTop_eq_directionalDerivativeAt`;
- `Function.directionalDerivativeAt_toWithTopBot_eq_inner_gradient`;
- `∇`;
- `EuclideanSpace.basisFun`.

Primitive data vs derived API:
- primitive input: a differentiable function `f` at `x`;
- derived API: the partial-derivative owner `Function.partialDeriv f x j`, the existence predicate
  `Function.HasPartialDerivAt f x j`, the differentiability-to-existence bridge
  `DifferentiableAt.hasPartialDerivAt`, the canonical basis-value bridge theorem
  `partialDeriv_eq_fderiv_basisFun`, and the real gradient bridge formulas.

Layer target: the owner theorem is `core/canonical` at the `fderiv` layer via
`DifferentiableAt.lineDeriv_eq_fderiv`; Euclidean basis and gradient-coordinate formulas are
`bridge/view`
corollaries.

Notation evaluation:
- the textbook symbol `∂f / ∂ξ_j (x)` is not introduced as Lean notation: `∂` already has heavy
  derivative-related parser use in mathlib, and the short owner
  `Function.partialDeriv f x j`
  gives a cleaner stable theorem surface than a custom parameterized notation.

Scalar/ambient minimality note:
- the core partial-derivative owner layer (`Function.partialDeriv`,
  `Function.HasPartialDerivAt`, `DifferentiableAt.hasPartialDerivAt`) is
  scalar/codomain-generic on finite Euclidean coordinates (`𝕜` with
  `[NontriviallyNormedField 𝕜]`, codomain `F` with `[NormedSpace 𝕜 F]`),
  because only line-derivative primitives are needed there.
- the basis theorem `partialDeriv_eq_fderiv_basisFun` and real gradient formulas are bridge-only
  consequences from Theorem 25.1.1.
-/

section

namespace Function

/-- The textbook `j`-th partial derivative of `f` at `x`. -/
abbrev partialDeriv {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : EuclideanSpace 𝕜 ι → F)
    (x : EuclideanSpace 𝕜 ι) (j : ι) : F := by
  classical
  exact lineDeriv 𝕜 f x ((PiLp.single (p := (2 : ENNReal)) j (1 : 𝕜)) : EuclideanSpace 𝕜 ι)

/-- The `j`-th partial derivative of `f` exists at `x`. -/
abbrev HasPartialDerivAt {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (f : EuclideanSpace 𝕜 ι → F)
    (x : EuclideanSpace 𝕜 ι) (j : ι) : Prop := by
  classical
  exact LineDifferentiableAt 𝕜 f x
    ((PiLp.single (p := (2 : ENNReal)) j (1 : 𝕜)) : EuclideanSpace 𝕜 ι)

end Function

-- Proof sketch: apply mathlib's canonical differentiability-to-line-differentiability owner
-- theorem in the intrinsic coordinate direction given by `PiLp.single`.
/-- Differentiability at `x` implies existence of each textbook standard-basis partial derivative
at `x`. -/
theorem DifferentiableAt.hasPartialDerivAt
    {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : EuclideanSpace 𝕜 ι → F} {x : EuclideanSpace 𝕜 ι}
    (hf : DifferentiableAt 𝕜 f x) (j : ι) :
    Function.HasPartialDerivAt f x j := by
  classical
  simpa [Function.HasPartialDerivAt] using
    (show LineDifferentiableAt 𝕜 f x
        ((PiLp.single (p := (2 : ENNReal)) j (1 : 𝕜)) : EuclideanSpace 𝕜 ι) from
      hf.lineDifferentiableAt)

-- Proof sketch: rewrite `Function.partialDeriv` using the canonical `PiLp` basis vector, then
-- apply `DifferentiableAt.lineDeriv_eq_fderiv` in that primitive direction.
/-- Primitive bridge form of Theorem 25.1.2: for a differentiable map on finite Euclidean
coordinates, the `j`-th textbook partial derivative is `fderiv` applied to the coordinate
direction from `PiLp.basisFun`. -/
theorem partialDeriv_eq_fderiv_piLpBasisFun
    {𝕜 ι F : Type*} [NontriviallyNormedField 𝕜] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : EuclideanSpace 𝕜 ι → F} {x : EuclideanSpace 𝕜 ι}
    (hf : DifferentiableAt 𝕜 f x) (j : ι) :
    Function.partialDeriv f x j =
      fderiv 𝕜 f x (((PiLp.basisFun (2 : ENNReal) 𝕜 ι) j) : EuclideanSpace 𝕜 ι) := by
  classical
  simpa [Function.partialDeriv] using
    (show lineDeriv 𝕜 f x (((PiLp.basisFun (2 : ENNReal) 𝕜 ι) j) : EuclideanSpace 𝕜 ι) =
        fderiv 𝕜 f x (((PiLp.basisFun (2 : ENNReal) 𝕜 ι) j) : EuclideanSpace 𝕜 ι) from
      by simpa [PiLp.basisFun_apply] using hf.lineDeriv_eq_fderiv)

-- Proof sketch: rewrite `Function.partialDeriv` by `PiLp.single`, then use
-- `DifferentiableAt.lineDeriv_eq_fderiv` and identify `PiLp.single` with
-- `EuclideanSpace.basisFun ι 𝕜 j`.
/-- Theorem 25.1.2 as the standard-orthonormal-basis bridge: for a differentiable map on
Euclidean coordinates, the `j`-th textbook partial derivative is `fderiv` applied to
`EuclideanSpace.basisFun ι 𝕜 j`. -/
theorem partialDeriv_eq_fderiv_basisFun
    {𝕜 ι F : Type*} [RCLike 𝕜] [Fintype ι]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    {f : EuclideanSpace 𝕜 ι → F} {x : EuclideanSpace 𝕜 ι}
    (hf : DifferentiableAt 𝕜 f x) (j : ι) :
    Function.partialDeriv f x j = fderiv 𝕜 f x (EuclideanSpace.basisFun ι 𝕜 j) := by
  classical
  simpa [Function.partialDeriv, EuclideanSpace.basisFun_apply] using
    (show lineDeriv 𝕜 f x ((PiLp.single (p := (2 : ENNReal)) j (1 : 𝕜)) : EuclideanSpace 𝕜 ι) =
        fderiv 𝕜 f x (EuclideanSpace.basisFun ι 𝕜 j) from
      by simpa [EuclideanSpace.basisFun_apply] using hf.lineDeriv_eq_fderiv)

end

section

-- Proof sketch: compare `lineDeriv` with the Chapter 23 owner, then rewrite by the recalled
-- gradient-value theorem, specialized to `e_j`.
/-- Real-gradient bridge companion to Theorem 25.1.2: for real Euclidean coordinates, the
`j`-th partial derivative equals the gradient pairing with the `j`-th basis vector. -/
theorem partialDeriv_eq_inner_gradient
    {ι : Type*} [Fintype ι] {f : EuclideanSpace ℝ ι → ℝ}
    {x : EuclideanSpace ℝ ι} (hf : DifferentiableAt ℝ f x) (j : ι) :
    Function.partialDeriv f x j = ⟪∇ f x, EuclideanSpace.basisFun ι ℝ j⟫ := by
  classical
  apply WithBotTop.coe_eq_coe_iff.mp
  calc
    (↑(Function.partialDeriv f x j) : WithBotTop ℝ) =
        (↑(lineDeriv ℝ f x (EuclideanSpace.basisFun ι ℝ j)) : WithBotTop ℝ) := by
      simp [Function.partialDeriv, EuclideanSpace.basisFun_apply]
    _ = Function.directionalDerivativeAt f.toWithBotTop x
          (EuclideanSpace.basisFun ι ℝ j) := by
      simpa using
        (Function.lineDeriv_toWithBotTop_eq_directionalDerivativeAt
          (f := f) (x := x) (y := EuclideanSpace.basisFun ι ℝ j) hf)
    _ = (⟪∇ f x, EuclideanSpace.basisFun ι ℝ j⟫ : WithBotTop ℝ) := by
      simpa using
        (Function.directionalDerivativeAt_toWithTopBot_eq_inner_gradient
          (f := f) (x := x) (y := EuclideanSpace.basisFun ι ℝ j) hf)

-- Proof sketch: combine the inner-product bridge above with
-- `EuclideanSpace.inner_basisFun_real`.
/-- Real-coordinate bridge companion to Theorem 25.1.2: at each coordinate index `j`, the
partial derivative is the `j`-th coordinate of the Euclidean gradient. -/
theorem partialDeriv_eq_gradient_apply
    {ι : Type*} [Fintype ι] {f : EuclideanSpace ℝ ι → ℝ}
    {x : EuclideanSpace ℝ ι} (hf : DifferentiableAt ℝ f x) (j : ι) :
    Function.partialDeriv f x j = ∇ f x j := by
  calc
    Function.partialDeriv f x j = ⟪∇ f x, EuclideanSpace.basisFun ι ℝ j⟫ :=
      partialDeriv_eq_inner_gradient hf j
    _ = ∇ f x j := by
      simp [EuclideanSpace.inner_basisFun_real]

end
