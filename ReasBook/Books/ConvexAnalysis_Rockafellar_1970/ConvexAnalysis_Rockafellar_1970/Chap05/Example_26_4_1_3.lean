import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_4_5
import ConvexAnalysis_Rockafellar_1970.Chap01.Remark_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_7
import ConvexAnalysis_Rockafellar_1970.Chap02.Theorem_10_1_4

noncomputable section

open scoped Rockafellar

section Owners

variable {𝕜 : Type*}

local notation "R2" => 𝕜 × 𝕜

/-!
Source/core/bridge triage for this item.

- `source-facing`: Example 26.4.1.3 uses the open upper half-plane
  `C = {(ξ₁, ξ₂) | ξ₂ > 0}`, the branch `f(ξ₁, ξ₂) = ξ₁² / (4 ξ₂)` on `C`, and the gradient-image
  parabola `D = {(η₁, η₂) | η₂ = -η₁²}`.
- `core/canonical`: the source-facing owners are scalar-generic and declared at the primitive
  typeclass layer each owner needs; no Euclidean-model owner is introduced.
- `bridge/view`: convexity is derived below from the Chapter 10 owner
  `quadraticOverLinearFunction` through a linear coordinate change.
-/

/-- The open upper half-plane in `R² = 𝕜 × 𝕜`. -/
def upperHalfPlane [Zero 𝕜] [LT 𝕜] : Set R2 :=
  {ξ : R2 | 0 < ξ.2}

/-- The branch from Example 26.4.1.3, viewed on `R²`; the intended source domain is
`upperHalfPlane`. -/
def upperHalfPlaneQuadratic [DivisionRing 𝕜] : R2 → 𝕜 :=
  fun ξ ↦ ξ.1 ^ 2 / ((4 : 𝕜) * ξ.2)

/-- The downward parabola
`D = {(η₁, η₂) | η₂ = -η₁²}` appearing as the gradient image in Example 26.4.1.3. -/
def upperHalfPlaneGradientParabola [Ring 𝕜] : Set R2 :=
  {η : R2 | η.2 = -(η.1) ^ 2}

/-- The source-facing gradient-map formula
`(ξ₁, ξ₂) ↦ (ξ₁ / (2 ξ₂), -ξ₁² / (4 ξ₂²))` from Example 26.4.1.3, as a map on the
intrinsic source domain `upperHalfPlane`. -/
def upperHalfPlaneQuadraticGradientMap [DivisionRing 𝕜] [LT 𝕜] :
    upperHalfPlane → R2 :=
  fun ξ ↦ (ξ.1.1 / (2 * ξ.1.2), -(ξ.1.1 ^ 2) / (4 * ξ.1.2 ^ 2))

end Owners

section Generic

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

local notation "R2" => 𝕜 × 𝕜

local notation "D" => upperHalfPlaneGradientParabola
local notation "g" => (upperHalfPlaneQuadraticGradientMap : upperHalfPlane → R2)

/-- The source gradient-map image of the upper-half-plane example is exactly the parabola owner
`D = {(η₁, η₂) | η₂ = -η₁²}`. -/
theorem gradientImage_upperHalfPlaneQuadratic :
    Set.range g = D := by
  apply Set.Subset.antisymm
  · rintro y ⟨⟨ξ, hξC⟩, rfl⟩
    have hξ2 : 0 < ξ.2 := hξC
    change (-(ξ.1 ^ 2) / (4 * ξ.2 ^ 2)) = -((ξ.1 / (2 * ξ.2)) ^ 2)
    have hne : ξ.2 ≠ 0 := ne_of_gt hξ2
    field_simp [hne]
    ring
  · intro η hη
    refine ⟨⟨(2 * η.1, 1), by simp [upperHalfPlane]⟩, ?_⟩
    ext
    · simp [upperHalfPlaneQuadraticGradientMap]
    · have hSecond : (-(2 * η.1) ^ 2 / 4 : 𝕜) = η.2 := by
        calc
          (-(2 * η.1) ^ 2 / 4 : 𝕜) = -(η.1 ^ 2) := by ring
          _ = η.2 := by simpa using hη.symm
      simpa [upperHalfPlaneQuadraticGradientMap] using hSecond

/-- Consequently, the gradient image in Example 26.4.1.3 is not convex. -/
theorem not_convex_gradientImage_upperHalfPlaneQuadratic :
    ¬ Convex 𝕜 (Set.range g) := by
  rw [gradientImage_upperHalfPlaneQuadratic]
  intro hConv
  have hp : ((0 : 𝕜), (0 : 𝕜)) ∈ D := by
    norm_num [upperHalfPlaneGradientParabola]
  have hq : ((2 : 𝕜), (-4 : 𝕜)) ∈ D := by
    norm_num [upperHalfPlaneGradientParabola]
  have hmid :
      midpoint 𝕜 ((0 : 𝕜), (0 : 𝕜)) ((2 : 𝕜), (-4 : 𝕜)) ∈ D :=
    hConv.midpoint_mem hp hq
  have hmid_eq :
      midpoint 𝕜 ((0 : 𝕜), (0 : 𝕜)) ((2 : 𝕜), (-4 : 𝕜)) = ((1 : 𝕜), (-2 : 𝕜)) := by
    ext <;> norm_num [midpoint, AffineMap.lineMap_apply]
  have hm_mem : ((1 : 𝕜), (-2 : 𝕜)) ∈ D := by
    simpa [hmid_eq] using hmid
  have hm_not_mem : ((1 : 𝕜), (-2 : 𝕜)) ∉ D := by
    norm_num [upperHalfPlaneGradientParabola]
  exact hm_not_mem hm_mem

end Generic

section ConvexBridge

variable {𝕜 : Type*} [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

local notation "R2" => 𝕜 × 𝕜
local notation "C" => (upperHalfPlane : Set R2)
local notation "f" => (upperHalfPlaneQuadratic : R2 → 𝕜)
local notation "qol" => (quadraticOverLinearFunction : R2 → WithTopBot 𝕜)

private def toQuadraticOverLinear : R2 →ₗ[𝕜] R2 :=
  LinearMap.prod (((2 : 𝕜) • LinearMap.snd 𝕜 𝕜 𝕜)) (LinearMap.fst 𝕜 𝕜 𝕜)

omit [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜] in
@[simp] private theorem toQuadraticOverLinear_apply (ξ : R2) :
    toQuadraticOverLinear ξ = (2 * ξ.2, ξ.1) := by
  ext <;> simp [toQuadraticOverLinear]

private theorem upperHalfPlaneQuadratic_toWithTopBot_eq_comp_quadraticOverLinearFunction
    {ξ : R2} (hξ : ξ ∈ C) :
    (f ξ : WithTopBot 𝕜) = qol (toQuadraticOverLinear ξ) := by
  have hξ2 : 0 < ξ.2 := hξ
  have hfirst : 0 < (2 : 𝕜) * ξ.2 := by
    have htwo : (0 : 𝕜) < 2 := by norm_num
    exact mul_pos htwo hξ2
  have hdenom : ((4 : 𝕜) * ξ.2) = 2 * (2 * ξ.2) := by ring
  rw [quadraticOverLinearFunction, toQuadraticOverLinear_apply, if_pos hfirst]
  simp [upperHalfPlaneQuadratic, hdenom]

/- The canonical extension of Example 26.4.1.3 is the pullback of the Chapter 10
quadratic-over-linear owner through the linear coordinate change `(ξ₁, ξ₂) ↦ (2 ξ₂, ξ₁)`, with
the upper-half-plane cutoff reimposed. -/
/-- Canonical codomain bridge: the source branch `f : R2 → 𝕜` extends to the chapter owner layer
`WithTopBot 𝕜` via the linear pullback of `quadraticOverLinearFunction` plus the indicator cutoff
to `C`. -/
theorem upperHalfPlaneQuadratic_toWithTopBotOn_eq :
    f.toWithTopBotOn C =
      qol ∘ toQuadraticOverLinear + (δ[𝕜](· | C) : R2 → WithTopBot 𝕜) := by
  rw [Function.toWithTopBotOn_eq_add_indicator]
  funext ξ
  by_cases hξ : ξ ∈ C
  · simpa [hξ, Function.comp] using
      upperHalfPlaneQuadratic_toWithTopBot_eq_comp_quadraticOverLinearFunction hξ
  · simp [hξ]
    simpa [Function.comp] using
      (WithBotTop.add_top_of_ne_bot
        (quadraticOverLinearFunction_neBot (toQuadraticOverLinear ξ))).symm

/-- Example 26.4.1.3: the branch `(ξ₁, ξ₂) ↦ ξ₁² / (4 ξ₂)` is convex on the open upper
half-plane `ξ₂ > 0`, in canonical owner form: the extension-by-`+∞` owner
`f.toWithTopBotOn C` is convex on `R2`. -/
theorem upperHalfPlaneQuadratic_toWithTopBotOn_isConvex :
    (f.toWithTopBotOn C).IsConvex 𝕜 := by
  rw [upperHalfPlaneQuadratic_toWithTopBotOn_eq]
  have hUpper : Convex 𝕜 C := by
    simpa [upperHalfPlane] using convex_halfSpace_gt (LinearMap.snd 𝕜 𝕜 𝕜).isLinear (0 : 𝕜)
  have hIndicator :
      ((δ[𝕜](· | C) : R2 → WithTopBot 𝕜)).IsConvex 𝕜 :=
    (indicator_isConvex_iff C).2 hUpper
  refine
    (quadraticOverLinearFunction_isConvex.comp_linearMap
      toQuadraticOverLinear).add_of_bot_lt hIndicator ?_ ?_
  · intro ξ
    simpa [Function.comp] using
      (WithBot.bot_lt_iff_ne_bot.2
        (quadraticOverLinearFunction_neBot (toQuadraticOverLinear ξ)))
  · intro ξ
    by_cases hξ : ξ ∈ C
    · simp [hξ]
    · simp [hξ]

/-- Example 26.4.1.3: the branch `(ξ₁, ξ₂) ↦ ξ₁² / (4 ξ₂)` is convex on the open upper
half-plane `ξ₂ > 0`. This source-facing open-domain statement is recovered from the canonical
`WithTopBot` owner convexity theorem above. -/
theorem convexOn_upperHalfPlaneQuadratic :
    ConvexOn 𝕜 C f :=
  (isConvex_toWithTopBotOn_iff).1 upperHalfPlaneQuadratic_toWithTopBotOn_isConvex

end ConvexBridge
