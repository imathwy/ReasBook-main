import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_25_1

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
