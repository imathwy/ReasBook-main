import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_26_4_0_1 (from Chap05) -/
/-!
Definition 26.4.0.1 is a textbook-location recall node.

The canonical/source-facing owner remains
`Function.IsEssentiallyStrictlyConvex` from `Definition_26_2_1`.
This file intentionally introduces no parallel owner, notation, or bridge API.
-/

namespace Function

/- Definition 26.4.0.1 reuses the source-facing Chapter 26 owner from Definition 26.2.1. -/
recall IsEssentiallyStrictlyConvex

end Function

/-! ### Definition_26_4_0_2 (from Chap05) -/
/-!
Source/core/bridge triage for this item.

- `source-facing`: Definition 26.4.0.2 identifies the textbook Legendre-transform values of a
  differentiable pair `(C, f)` along the derivative image `fderivWithin 𝕜 f C '' C`.
- `core/canonical`: the owner data already present upstream are the canonical extension
  `Function.toWithTopBotOn f C`, its Fenchel conjugate `(Function.toWithTopBotOn f C)⋆`, and the
  pointwise value theorem
  `Function.convexConjugate_toWithTopBotOn_fderivWithin_eq_apply_sub`.
- `bridge/view`: this file stays a recall/bridge node for the canonical owner layer and does not
  introduce a second public owner.

Domain-style sampling used here:
- `convexConjugate`;
- `Function.convexConjugate_toWithTopBotOn_imageFactorization_intrinsicInterior_eq_apply_sub`;
- `Function.mem_dom_convexConjugate_toWithTopBotOn_fderiv`;
- `Function.mapsTo_fderiv_dom_convexConjugate_toWithTopBotOn_intrinsicInterior`;
- `Function.image_fderiv_subset_dom_convexConjugate_toWithTopBotOn_intrinsicInterior`;
- `Function.convexConjugate_toWithTopBotOn_imageFactorization_eq_apply_sub`;
- `Function.mem_dom_convexConjugate_toWithTopBotOn_fderivWithin`;
- `Function.mapsTo_fderivWithin_dom_convexConjugate_toWithTopBotOn`;
- `Function.image_fderivWithin_subset_dom_convexConjugate_toWithTopBotOn`;
- `Function.convexConjugate_toWithTopBotOn_fderivWithin_eq_apply_sub`.

Primitive data vs derived API:
- primitive owner surface: the Fenchel conjugate `(Function.toWithTopBotOn f C)⋆`;
- derived API: the owner-level derivative-image affine-defect evaluation theorem, together with
  pointwise, `Set.MapsTo`, and image-level finiteness corollaries on the same canonical owner.

Layer target:
- `core/canonical`: `convexConjugate`;
- `bridge/view`: recall existing derivative-image/value and finiteness bridges on that canonical
  owner layer.
-/

namespace Function

/- Definition 26.4.0.2 uses the chapter's canonical Fenchel-conjugate owner. -/
#check convexConjugate

/- The derivative-image and finiteness formulas already live upstream on the canonical owner. -/
recall convexConjugate_toWithTopBotOn_fderivWithin_eq_apply_sub
recall convexConjugate_toWithTopBotOn_imageFactorization_intrinsicInterior_eq_apply_sub
recall mem_dom_convexConjugate_toWithTopBotOn_fderiv
recall mapsTo_fderiv_dom_convexConjugate_toWithTopBotOn_intrinsicInterior
recall image_fderiv_subset_dom_convexConjugate_toWithTopBotOn_intrinsicInterior
recall convexConjugate_toWithTopBotOn_imageFactorization_eq_apply_sub
recall mem_dom_convexConjugate_toWithTopBotOn_fderivWithin
recall mapsTo_fderivWithin_dom_convexConjugate_toWithTopBotOn
recall image_fderivWithin_subset_dom_convexConjugate_toWithTopBotOn

end Function

/-! ### Text_26_4_0_2 (from Chap05) -/
noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable [NontriviallyNormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {C : Set E} {f : E → 𝕜}
local notation "fExt" => Function.toWithTopBotOn f C
local notation "riC" => ri[𝕜](C)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 26.4.0.2 says that, after extending a convex scalar-valued function on an
  open convex set `C` by `+∞` outside `C`, the Legendre-side values are obtained from the ordinary
  Fenchel conjugate of that canonical extension.
- `core/canonical`: the live owner abstractions already present upstream are the Chapter 3 Fenchel
  conjugate `convexConjugate`, the Chapter 1 effective-domain owner `dom(·)`, and the
  derivative value formulas
  `Function.convexConjugate_toWithTopBotOn_fderiv_eq_apply_sub` and
  `Function.convexConjugate_toWithTopBotOn_fderivWithin_eq_apply_sub`.
- `bridge/view`: this file does not introduce a second Legendre-transform owner. It records the
  intrinsic-interior (`ri[𝕜](C)`) and open-set (`C`) image-factorization/domain consequences on
  the canonical `WithTopBot` owner, together with their `Set.MapsTo`/image reformulations.

Domain-style sampling used here:
- `convexConjugate` from Chapter 3;
- `Function.convexConjugate_toWithTopBotOn_fderiv_eq_apply_sub`;
- `Function.convexConjugate_toWithTopBotOn_fderivWithin_eq_apply_sub`;
- `dom(·)` and `mem_effectiveDomain` from `Chap01.Definition_4_4`.

Primitive data vs derived API:
- primitive data: the open convex set `C`, the convex branch `f`, and its canonical extension
  `Function.toWithTopBotOn f C`;
- primitive owner surface: the Fenchel conjugate `(Function.toWithTopBotOn f C)⋆`;
- derived API: the image-factorization `WithTopBot`-valued derivative formula and the
  pointwise/map/image finiteness theorems on `dom((Function.toWithTopBotOn f C)⋆)`.

Layer target: `bridge/view`. The text is about derivative-image/value and finiteness views of the
existing Fenchel-conjugate owner, not about introducing a second root owner.
-/

/- Text 26.4.0.2 uses the ambient Fenchel conjugate of the canonical extension. -/
#check convexConjugate

/- Text 26.0.1 already provides the derivative-value formulas used below. -/

namespace Function

/-- Canonical `toWithTopBotOn`-spelled intrinsic-interior image-factorization corollary. -/
theorem convexConjugate_toWithTopBotOn_imageFactorization_intrinsicInterior_eq_apply_sub
    (hf_convex : ConvexOn 𝕜 C f) (x : riC) (hfdx : DifferentiableAt 𝕜 f x) :
    (fExt⋆) (↑(riC.imageFactorization (fderiv 𝕜 f) x) : StrongDual 𝕜 E) =
      (((fderiv 𝕜 f x) x - f x : 𝕜) : WithTopBot 𝕜) := by
  simpa [Set.imageFactorization] using
    (convexConjugate_toWithTopBotOn_fderiv_eq_apply_sub
      (hf_convex := hf_convex) (x := x) (hx := x.2) (hfdx := hfdx))

/-- Canonical `toWithTopBotOn`-spelled open-set image-factorization corollary. -/
theorem convexConjugate_toWithTopBotOn_imageFactorization_eq_apply_sub
    (hC_open : IsOpen C) (hf_convex : ConvexOn 𝕜 C f)
    (x : C) (hfdx : DifferentiableAt 𝕜 f x) :
    (fExt⋆) (↑(C.imageFactorization (fderivWithin 𝕜 f C) x) : StrongDual 𝕜 E) =
      (((fderivWithin 𝕜 f C x) x - f x : 𝕜) : WithTopBot 𝕜) := by
  simpa [Set.imageFactorization] using
    (convexConjugate_toWithTopBotOn_fderivWithin_eq_apply_sub
      (hC_open := hC_open) (hf_convex := hf_convex) (hx := x.2) (hfdx := hfdx))

/-- Canonical `toWithTopBotOn`-spelled intrinsic-interior pointwise domain consequence. -/
theorem mem_dom_convexConjugate_toWithTopBotOn_fderiv
    (hf_convex : ConvexOn 𝕜 C f)
    {x : E} (hx : x ∈ riC) (hfdx : DifferentiableAt 𝕜 f x) :
    fderiv 𝕜 f x ∈ dom(fExt⋆) := by
  rw [mem_effectiveDomain]
  rw [convexConjugate_toWithTopBotOn_fderiv_eq_apply_sub
      (hf_convex := hf_convex) (hx := hx) (hfdx := hfdx)]
  exact WithTopBot.coe_lt_top _

/-- Canonical `toWithTopBotOn`-spelled open-set pointwise domain consequence. -/
theorem mem_dom_convexConjugate_toWithTopBotOn_fderivWithin
    (hC_open : IsOpen C) (hf_convex : ConvexOn 𝕜 C f)
    {x : E} (hx : x ∈ C) (hfdx : DifferentiableAt 𝕜 f x) :
    fderivWithin 𝕜 f C x ∈ dom(fExt⋆) := by
  have hxri : x ∈ riC := by
    exact interior_subset_intrinsicInterior (𝕜 := 𝕜)
      (mem_interior_iff_mem_nhds.2 (hC_open.mem_nhds hx))
  have hmem : fderiv 𝕜 f x ∈ dom(fExt⋆) :=
    mem_dom_convexConjugate_toWithTopBotOn_fderiv
      (hf_convex := hf_convex) (hx := hxri) (hfdx := hfdx)
  simpa [fderivWithin_of_isOpen hC_open hx] using hmem

/-- Canonical `toWithTopBotOn`-spelled intrinsic-interior map-owner reformulation. -/
theorem mapsTo_fderiv_dom_convexConjugate_toWithTopBotOn_intrinsicInterior
    (hf_convex : ConvexOn 𝕜 C f)
    (hfd : ∀ x ∈ riC, DifferentiableAt 𝕜 f x) :
    Set.MapsTo (fderiv 𝕜 f) riC (dom(fExt⋆)) := by
  intro x hx
  exact mem_dom_convexConjugate_toWithTopBotOn_fderiv
    (hf_convex := hf_convex) (hx := hx) (hfdx := hfd x hx)

/-- Canonical `toWithTopBotOn`-spelled open-set map-owner reformulation. -/
theorem mapsTo_fderivWithin_dom_convexConjugate_toWithTopBotOn
    (hC_open : IsOpen C) (hf_convex : ConvexOn 𝕜 C f) (hfd : DifferentiableOn 𝕜 f C) :
    Set.MapsTo (fderivWithin 𝕜 f C) C (dom(fExt⋆)) := by
  intro x hx
  exact mem_dom_convexConjugate_toWithTopBotOn_fderivWithin
    (hC_open := hC_open) (hf_convex := hf_convex) (hx := hx)
    (hfdx := (hfd x hx).differentiableAt (hC_open.mem_nhds hx))

/-- Canonical `toWithTopBotOn`-spelled intrinsic-interior image-subset corollary. -/
theorem image_fderiv_subset_dom_convexConjugate_toWithTopBotOn_intrinsicInterior
    (hf_convex : ConvexOn 𝕜 C f)
    (hfd : ∀ x ∈ riC, DifferentiableAt 𝕜 f x) :
    (fderiv 𝕜 f) '' riC ⊆ dom(fExt⋆) := by
  intro xStar hxStar
  rcases hxStar with ⟨x, hx, rfl⟩
  exact mapsTo_fderiv_dom_convexConjugate_toWithTopBotOn_intrinsicInterior
    (hf_convex := hf_convex) (hfd := hfd) hx

/-- Canonical `toWithTopBotOn`-spelled open-set image-subset corollary. -/
theorem image_fderivWithin_subset_dom_convexConjugate_toWithTopBotOn
    (hC_open : IsOpen C) (hf_convex : ConvexOn 𝕜 C f) (hfd : DifferentiableOn 𝕜 f C) :
    (fderivWithin 𝕜 f C) '' C ⊆ dom(fExt⋆) := by
  intro xStar hxStar
  rcases hxStar with ⟨x, hx, rfl⟩
  exact mapsTo_fderivWithin_dom_convexConjugate_toWithTopBotOn
    (hC_open := hC_open) (hf_convex := hf_convex) (hfd := hfd) hx

end Function

end

/-! ### Corollary_26_4_1 (from Chap05) -/
noncomputable section

open scoped Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 26.4.1 identifies the Legendre-side domain
  `D = dom∂[E](fStar)` for `fStar = (f⋆ : StrongDual ℝ E → WithBotTop ℝ)`, records the
  almost-convex sandwich
  `riDom(fStar) ⊆ D ⊆ dom(fStar)`, and packages the strict-convexity clause on convex subsets of `D`
  through the canonical owner `Function.IsEssentiallyStrictlyConvex (Y := E) fStar`.
- `core/canonical`: the chapter owners already present are `dom∂(·)`, `riDom(·)`, `dom(·)`, and
  `Function.IsEssentiallyStrictlyConvex`.
- `bridge/view`: the textbook set `{xStar | ∂f⋆(xStar) ≠ ∅}` is already the canonical owner
  `dom∂[E](fStar)`; the Euclidean graph-domain view `(Function.subdifferentialGraph f⋆).dom` is
  only a companion reformulation.

Domain-style sampling used here:
- `Function.IsEssentiallySmooth` from `Definition_26_1_1`;
- `Function.IsEssentiallyStrictlyConvex` from `Definition_26_2_1`;
- `domSubdifferential_between_riDom_and_dom_of_convex_proper` from `Remark_5_24_1`;
- `Function.IsClosedProperConvex
    .isEssentiallyStrictlyConvex_iff_convexConjugate_isEssentiallySmooth` from `Theorem_26_3`.

Primitive data vs derived API:
- primitive inputs: the genuinely extra closedness hypothesis `LowerSemicontinuous f` and the
  source hypothesis `f.IsEssentiallySmooth`, whose owner already carries convexity and properness;
- primitive source-facing owner set: the Legendre-side domain `D = dom∂[E](fStar)`;
- derived API: the conjugate-side owner `Function.IsEssentiallyStrictlyConvex (Y := E) fStar` and
  domain sandwich.

Layer target: `source-facing`, stated directly through the chapter owner set `dom∂[E](fStar)` and the
canonical Chapter 26 owner `Function.IsEssentiallyStrictlyConvex (Y := E) fStar`, rather than
through the Euclidean graph-domain view or an unpacked strict-convexity clause.
-/

namespace Function.IsClosedProperConvex

variable {f : E → WithBotTop ℝ}
local notation "fStar" => (f⋆ : StrongDual ℝ E → WithBotTop ℝ)

local notation "D" => dom∂[E](fStar)

-- Proof sketch: combine `hclosed` with the convexity and properness fields already carried by
-- `hess` to build the closed-proper-convex owner for `f`. Apply Theorem 26.3 on the conjugate
-- side to obtain `Function.IsEssentiallyStrictlyConvex (Y := E) fStar`. Then apply Remark 5.24.1 to
-- the closed proper convex conjugate `f⋆` to obtain the sandwich
-- `riDom(fStar) ⊆ dom∂[E](fStar) ⊆ dom(fStar)`.
/-- Corollary 26.4.1: if `f` is essentially smooth and closed proper convex, then on the canonical
Legendre-side domain `D = dom∂[E](fStar)` for `fStar = (f⋆ : StrongDual ℝ E → WithBotTop ℝ)`,
equivalently `D = {xStar | (∂[E]fStar(xStar)).Nonempty}`, the conjugate-side Chapter 26 owner
`Function.IsEssentiallyStrictlyConvex (Y := E) fStar` holds, and one has the almost-convex
sandwich `ri(dom fStar) ⊆ D ⊆ dom(fStar)`. -/
theorem convexConjugate_isEssentiallyStrictlyConvex_and_subgradientDom_between
    (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth) :
    Function.IsEssentiallyStrictlyConvex (Y := E) fStar ∧
      riDom(fStar) ⊆ D ∧
      D ⊆ dom(fStar) := by
  sorry

end Function.IsClosedProperConvex

end

/-! ### Definition_26_4_1_4 (from Chap05) -/
universe u

section

open scoped Rockafellar

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
local notation "IsClosedProperConvexℝ" => Function.IsClosedProperConvex (𝕜 := ℝ)

/- Definition 26.4.1.4: the project owner for a convex function of Legendre type is the
canonical Chapter 26 class `Function.IsLegendreTypeOn`. It records exactly that `C` is nonempty
and open, and that `f` is strictly convex and essentially smooth on `C`. -/
recall Function.IsLegendreTypeOn

-- Proof sketch: Corollary 26.3.1 identifies one-to-one-ness of the subdifferential graph with
-- strict convexity of `f.realBranch` on `interior (dom(f))` together with essential smoothness of
-- `f`. Via `riDom(f) = interior (dom(f))` under essential smoothness, this yields the intrinsic
-- owner surface `Function.IsLegendreTypeOn (riDom(f)) f.realBranch`.
/-- For a closed proper convex function, the subdifferential mapping is one-to-one exactly when
its intrinsic-domain pair `(riDom(f), f.realBranch)` is of Legendre type. -/
theorem biUnique_subdifferentialGraph_iff_isLegendreTypeOn_riDom
    {f : E → WithBotTop ℝ} (hf : IsClosedProperConvexℝ f) :
    (gph∂(f)).BiUnique ↔
      Function.IsLegendreTypeOn (riDom(f)) f.realBranch := by
  rw [biUnique_subdifferentialGraph_iff_strictConvexOn_interior_dom_and_isEssentiallySmooth hf,
    Function.isLegendreTypeOn_iff]
  constructor
  · rintro ⟨hstrict, hess⟩
    have hri_eq : riDom(f) = interior (dom(f)) := hess.riDom_eq_interior_dom
    exact
      ⟨hess.toIsEssentiallySmoothOn_riDom, by simp [hri_eq],
        by simpa [hri_eq] using hstrict⟩
  · rintro ⟨hessOn, hri_open, hstrict⟩
    have hri_subset_dom : riDom(f) ⊆ dom(f) := by
      intro x hx
      exact intrinsicInterior_subset (by simpa [riDom_real_eq_intrinsicInterior_dom] using hx)
    have hinterior_nonempty : (interior (dom(f))).Nonempty := by
      rcases hessOn.nonempty with ⟨x, hx⟩
      exact ⟨x, (interior_maximal hri_subset_dom hri_open) hx⟩
    have hess : f.IsEssentiallySmooth :=
      Function.isEssentiallySmooth_of_isEssentiallySmoothOn_riDom
        hf.convex hf.proper hessOn hinterior_nonempty
    exact ⟨by simpa [hess.riDom_eq_interior_dom] using hstrict, hess⟩

end

/-! ### Example_26_4_1_3 (from Chap05) -/
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

/-! ### Proposition_26_4_1_5 (from Chap05) -/
/-!
Source/core/bridge triage:

- `source-facing`: Proposition 26.4.1.5 says that for a closed proper convex function `f`, the
  multivalued subdifferential `∂f` is one-to-one if and only if the restriction
  `(riDom(f), f.realBranch)` is of Legendre type.
- `core/canonical`: the project already owns this content as the theorem
  `biUnique_subdifferentialGraph_iff_isLegendreTypeOn_riDom`, built from the canonical
  relation owner `(_root_.subdifferentialGraph f).BiUnique` and the Chapter 26 owner
  `Function.IsLegendreTypeOn`.
- `bridge/view`: this numbered proposition adds no new primitive data beyond that earlier theorem;
  it is only a textbook-location recall of the same owner-level statement.

Domain-style sampling used here:
- `Function.IsLegendreTypeOn` from `Definition_26_4_1_4`;
- `biUnique_subdifferentialGraph_iff_strictConvexOn_interior_dom_and_isEssentiallySmooth` from
  `Corollary_26_3_1`;
- `(_root_.subdifferentialGraph f).BiUnique` from `Definition_26_0_3`;
- `Function.realBranch` together with the domain owner `dom(f)`.

Primitive data vs derived API:
- primitive source input: a closed proper convex function `f`;
- primitive owner surface: bi-uniqueness of `_root_.subdifferentialGraph f` and the Legendre-type
  predicate on `riDom(f)`;
- derived API here: none. The earlier theorem already has the exact target interface.

Layer target: `bridge/view`. This file is a direct canonical recall rather than a second
exact-interface theorem shell.
-/

/- Proposition 26.4.1.5 is exactly the earlier chapter theorem
`biUnique_subdifferentialGraph_iff_isLegendreTypeOn_riDom`; this file reuses that canonical owner
result directly instead of maintaining a parallel theorem name. -/
recall biUnique_subdifferentialGraph_iff_isLegendreTypeOn_riDom

/-! ### Text_26_4_1_1 (from Chap05) -/
noncomputable section

open AffineMap Filter
open scoped Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 26.4.1.1 explains how, for an essentially smooth closed proper convex
  function `f`, the Fenchel conjugate `f⋆` is the closed proper convex extension of its
  Legendre-side restriction to the canonical set `D = dom∂((f⋆ : E → EReal))`.
- `core/canonical`: the owner declarations already present upstream are Fenchel conjugation `f⋆`,
  the canonical Legendre-side set owner `dom∂(·)`, the conjugate-side sandwich theorem
  `Function.IsClosedProperConvex
    .convexConjugate_isEssentiallyStrictlyConvex_and_subgradientDom_between`,
  the relative-domain notation `riDom(·)`, and the segment-limit theorem
  `Function.IsConvex.tendsto_lineMap_to_lowerSemicontinuousHull`.
- `bridge/view`: the source wording about the Legendre conjugate `g` on `D` is interpreted as the
  restriction of `f⋆` to `D`; the nontrivial extension content is therefore the boundary-limit
  behavior and the `+∞` value outside `closure D`, rather than a new wrapper around that
  restriction.

Domain-style sampling used here:
- `Function.IsClosedProperConvex
    .convexConjugate_isEssentiallyStrictlyConvex_and_subgradientDom_between`;
- `Function.IsConvex.tendsto_lineMap_to_lowerSemicontinuousHull` from Theorem 7.5;
- `dom(·)` and `riDom(·)` from Definition 4.4;
- `closure` and `frontier` on the canonical set owner `D`.

Primitive data vs derived API:
- primitive source data: a closed proper convex function `f`, its conjugate `f⋆`, and the
  canonical Legendre-side set `D = dom∂((f⋆ : E → EReal))`;
- derived API: the exterior formula `f⋆ = +∞` off `closure D`, together with the segment-limit
  formula from points of `ri(dom f⋆)` to arbitrary endpoints; the source frontier hypothesis is a
  redundant specialization of that second statement.

Layer target: `bridge/view`. The item does not introduce a new Legendre-transform owner; it
records the extension behavior of the already canonical conjugate owner `f⋆`.
-/

namespace Function.IsClosedProperConvex

variable {f : E → EReal}

local notation "fStar" => (f⋆ : E → EReal)
local notation "D" => dom∂(fStar)

-- Proof sketch: build the canonical owner `hf : f.IsClosedProperConvex` from `hclosed` and the
-- convexity/properness fields already carried by `hess`. Then `hf.convexConjugate` makes `fStar`
-- closed proper convex. Corollary 26.4.1 gives the exact conjugate-side sandwich
-- `riDom(fStar) ⊆ D ⊆ dom(fStar)` under these hypotheses, so
-- `closure D = closure (dom(fStar))` by convexity of `dom(fStar)`. Use the standard closed
-- proper convex exterior formula for points outside that closure.
/-- Text 26.4.1.1, exterior clause: for an essentially smooth closed proper convex function `f`,
let `D = dom∂(fStar)` for `fStar = f⋆`. Then the conjugate takes the value `+∞` at every point
outside `closure D`. -/
theorem convexConjugate_eq_top_outside_closure_conjugateSubgradientDom
    (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth) {xStar : E}
    (hxStar : xStar ∉ closure D) :
    fStar xStar = ⊤ := sorry

-- Proof sketch: with `hf : f.IsClosedProperConvex` as above, the canonical conjugate owner
-- `hf.convexConjugate` makes `fStar` closed proper convex. Apply Theorem 7.5 to `fStar`, using
-- the base point `uStar ∈ riDom(fStar)` and the arbitrary endpoint `xStar`. Since `fStar` is
-- closed, `cl(fStar) = fStar`, so the segment values converge to the actual conjugate value at
-- `xStar`; the source frontier condition is therefore redundant in the Lean API.
/-- Text 26.4.1.1, boundary clause: for `fStar = f⋆` and `D = dom∂(fStar)`, if
`uStar ∈ riDom(fStar)`, then the values of `fStar` along the segment
`t ↦ lineMap uStar xStar t` converge to `fStar xStar` as `t → 1` from the left. The source
specialization `xStar ∈ frontier D` is redundant for this conclusion. -/
theorem tendsto_convexConjugate_lineMap_to_frontier_conjugateSubgradientDom
    (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth) {uStar xStar : E}
    (huStar : uStar ∈ riDom(fStar)) :
    Tendsto (fun t : ℝ ↦ fStar (lineMap uStar xStar t))
      (nhdsWithin (1 : ℝ) (Set.Iio (1 : ℝ)))
      (nhds (fStar xStar)) := sorry

end Function.IsClosedProperConvex

end

/-! ### Text_26_4_1_2 (from Chap05) -/
noncomputable section

open scoped Gradient RealInnerProductSpace Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace Function.IsClosedProperConvex

variable {f : E → EReal}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 26.4.1.2 says that for an essentially smooth closed proper convex
  function, the gradient map on `C = interior (dom(f))` continuously parameterizes the Legendre
  side `D`, and under this parameterization the conjugate value is the affine defect
  `⟪x, ∇ f(x)⟫ - f(x)`.
- `core/canonical`: the chapter owners already present are `LowerSemicontinuous`,
  `Function.IsEssentiallySmooth`, `interior (dom(f))`, `dom∂(·)`, `f.realBranch`, the conjugate
  `f⋆`, its canonical finite branch `(fStar).realBranch`, and the set-mapping owners
  `Set.MapsTo` / `Set.SurjOn`
  already used elsewhere in the chapter for raw owner maps between canonical domains.
- `bridge/view`: the declarations below keep the source parameterization on the raw gradient map
  `x ↦ ∇ f.realBranch x`, recording that it maps `C` onto the canonical Legendre-side domain
  `D = dom∂((f⋆ : E → EReal))`, is continuous on the intrinsic subtype `C`, and satisfies the
  conjugate-value formula pointwise through the conjugate's canonical finite branch
  `(fStar).realBranch` along that owner map.

Domain-style sampling used here:
- `Function.subdifferentialAt_eq_singleton_gradient_of_mem_interior_dom` from `Theorem_26_1`;
- `Function.IsClosedProperConvex.mem_subdifferentialAt_convexConjugate_iff` from
  `Corollary_23_5_1`;
- `Function.continuous_gradient_realBranch_on_open_convex` from `Corollary_25_5_1`;
- the Corollary 26.4.1 conjugate strict-convexity/domain theorem
  `convexConjugate_isEssentiallyStrictlyConvex_and_subgradientDom_between`.

Primitive data vs derived API:
- primitive inputs: the genuinely extra lower-semicontinuity hypothesis
  `hclosed : LowerSemicontinuous f` together with the source hypothesis
  `hess : f.IsEssentiallySmooth`, whose owner already carries convexity and properness;
- primitive source-facing object: the raw gradient branch `x ↦ ∇ f.realBranch x` on
  `C = interior (dom(f))`;
- derived API: the `Set.MapsTo` / `Set.SurjOn` description of its Legendre-side image
  `D = dom∂((f⋆ : E → EReal))`, continuity of the restricted gradient branch on the subtype `C`,
  and the conjugate-value identity stated on the canonical branch `(fStar).realBranch`.

Layer target: `bridge/view`, organized under the canonical closed-proper-convex owner namespace
already used by the neighboring Chapter 26 Legendre results.
-/

local notation "C" => interior (dom(f))
local notation "fStar" => ((f⋆ : E → EReal))
local notation "D" => dom∂(fStar)

-- Proof sketch: for `x ∈ C`, Theorem 26.1 identifies `∂f(x)` with the singleton
-- `{∇ f.realBranch x}`. Corollary 23.5.1 then transfers this membership across Fenchel conjugacy
-- to `x ∈ ∂f⋆(∇ f.realBranch x)`, which is exactly the statement that the gradient value belongs
-- to the canonical Legendre-side domain `D`.
/-- The raw gradient branch `x ↦ ∇ f.realBranch x` maps the primal interior domain
`C = interior (dom(f))` into the canonical Legendre-side domain
`D = dom∂((f⋆ : E → EReal))`. -/
theorem mapsTo_gradient_realBranch_interior_dom_conjugateSubgradientDom
    (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth) :
    Set.MapsTo (fun x ↦ ∇ f.realBranch x) C D := sorry

-- Proof sketch: take any `xStar` in the canonical Legendre-side domain
-- `D`, so some `x` satisfies `x ∈ ∂f⋆(xStar)`. By
-- Corollary 23.5.1 this means `xStar ∈ ∂f(x)`. Essential smoothness and Theorem 26.1 force
-- `x ∈ C` and identify that subgradient fiber with the singleton `{∇ f.realBranch x}`, so
-- `xStar` is exactly the value of the raw gradient branch at some point of `C`.
/-- The raw gradient branch `x ↦ ∇ f.realBranch x` maps `C = interior (dom(f))` onto the
canonical Legendre-side domain `D = dom∂((f⋆ : E → EReal))`. -/
theorem surjOn_gradient_realBranch_interior_dom_conjugateSubgradientDom
    (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth) :
    Set.SurjOn (fun x ↦ ∇ f.realBranch x) C D := sorry

section FiniteDimensional

variable [FiniteDimensional ℝ E]

-- Proof sketch: this is the exact Chapter 25 owner theorem
-- `Function.continuous_gradient_realBranch_on_open_convex` specialized to
-- `C = interior (dom(f))`. Essential smoothness already supplies convexity of `f`, finiteness of
-- `f` on `C`, and differentiability of `f.realBranch` on `C`.
/-- The raw gradient branch `x ↦ ∇ f.realBranch x` is continuous on the intrinsic subtype
`C = interior (dom(f))`. Combined with the maps-to theorem above, this is the source-facing
continuous parameterization of the canonical Legendre-side domain `D`. -/
theorem continuous_gradient_realBranch_on_interior_dom_of_isEssentiallySmooth
    (hess : f.IsEssentiallySmooth) :
    Continuous (fun x : C ↦ ∇ f.realBranch (x : E)) := by
  have hdom_convex : Convex ℝ dom(f) := hess.convex.convex_dom
  have hC_convex : Convex ℝ C := hdom_convex.interior
  refine Function.continuous_gradient_realBranch_on_open_convex
    isOpen_interior hC_convex hess.convex ?_ hess.differentiableOn_realBranch
  intro x hx
  exact ⟨interior_subset hx, hess.proper.ne_bot x⟩

end FiniteDimensional

-- Proof sketch: for `x ∈ interior (dom(f))`, Theorem 26.1 gives
-- `∇ f.realBranch x ∈ ∂f(x)`. Corollary 23.5.1 moves this to the conjugate side, so Fenchel-Young
-- equality from Theorem 23.5 applies at `(x, ∇ f.realBranch x)`, yielding the stated affine
-- defect formula directly on the owner gradient branch.
/-- Text 26.4.1.2: for `x ∈ C = interior (dom(f))`, the canonical Legendre-side branch value of
the Fenchel conjugate at the gradient point `xStar = ∇ f.realBranch x ∈ D = dom∂((f⋆ : E →
EReal))` is the affine defect `⟪x, xStar⟫ - f(x)`. Equivalently, the Legendre conjugate may be
viewed as a generally nonconvex function on `C` itself through the raw gradient branch. -/
theorem convexConjugate_realBranch_gradient_eq_inner_sub_of_mem_interior_dom
    (hclosed : LowerSemicontinuous f) (hess : f.IsEssentiallySmooth)
    {x : E} (hx : x ∈ C) :
    (fStar).realBranch (∇ f.realBranch x) =
      ⟪x, ∇ f.realBranch x⟫ - f.realBranch x := sorry

end Function.IsClosedProperConvex

end

/-! ### Theorem_26_4 (from Chap05) -/
noncomputable section

open scoped Rockafellar SetRel

universe u v

section

variable {𝕜 : Type v} [Semiring 𝕜] [TopologicalSpace 𝕜] [PartialOrder 𝕜]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable {Y : Type (max u v)} [HasPairing E Y 𝕜]
local notation "IsClosedProperConvex" => Function.IsClosedProperConvex (𝕜 := 𝕜)
local notation "IsEssentiallyStrictlyConvex[" Y "]" =>
  Function.IsEssentiallyStrictlyConvex (Y := Y)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 26.4 identifies essential strict convexity of a closed proper convex
  function with the inverse-single-valued clause for its subdifferential mapping.
- `core/canonical`: the owner abstractions already present in the chapter are
  `Function.IsEssentiallyStrictlyConvex`, the intrinsic graph owner
  `_root_.subdifferentialGraph (Y := Y) f : SetRel E Y`, the Chapter 26
  inverse-single-valued owner `(_root_.subdifferentialGraph (Y := Y) f).LeftUnique`, and the
  chapter's one-to-one owner `(_root_.subdifferentialGraph (Y := Y) f).BiUnique` from
  `Definition_26_0_3`.
- `bridge/view`: the Fréchet-Riesz transport `Function.subdifferentialGraph f` gives the
  vector-valued graph view of the same intrinsic owner on inner-product spaces.

Domain-style sampling used here:
- `Function.IsEssentiallyStrictlyConvex` from `Definition_26_2_1`;
- `_root_.subdifferentialGraph` from `Definition_5_24_3`;
- `SetRel.injOn_snd_iff` from `Lemma_26_1`, the chapter's canonical second-projection bridge for
  inverse single-valuedness;
- `(_root_.subdifferentialGraph f).dom` in `Definition_26_2_1`, which already makes the
  essential-strict-convexity owner intrinsic rather than Fréchet-Riesz-dependent;
- `Function.subdifferentialGraph` from `Definition_5_24_3`.

Primitive data vs derived API:
- primitive source data: a closed proper convex function `f` and its canonical graph relation
  `_root_.subdifferentialGraph f`;
- primitive owner theorem surface: inverse-single-valuedness of that intrinsic graph relation and
  the class `f.IsEssentiallyStrictlyConvex`;
- derived API: the vector-valued Fréchet-Riesz restatement.

Layer target:
- `leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex`: `source-facing`, stated
  directly on the intrinsic pairing-codomain graph owner of the subdifferential;
- `rightUnique_inv_subdifferentialGraph_iff_isEssentiallyStrictlyConvex`: `bridge/view`,
  the source inverse-wording restated from the canonical `LeftUnique` owner;
- `injOn_snd_subdifferentialGraph_iff_isEssentiallyStrictlyConvex`: `bridge/view`, the graph
  projection reformulation of the source inverse-single-valuedness clause;
- the inner-product-space theorems below: `bridge/view`, because they transport the source
  sentence through Fréchet-Riesz identification.
-/

/-- Theorem 26.4, canonical graph-owner form: for a closed proper convex function, the intrinsic
subdifferential graph is left-unique exactly when the function is essentially strictly convex.
This is the Chapter 26 inverse-single-valued owner clause, stated directly on
`(_root_.subdifferentialGraph (Y := Y) f).LeftUnique`.

Abstraction note: this intrinsic owner theorem is stated on the chapter's validated source layer
(`WithTopBot 𝕜` codomain with explicit pairing codomain `Y`); the vector-valued inner-product
form appears below only as a Fréchet-Riesz bridge. -/
theorem leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex
    {f : E → WithTopBot 𝕜} (hf : IsClosedProperConvex f) :
    (gph∂[Y](f)).LeftUnique ↔
      IsEssentiallyStrictlyConvex[Y] f := by
  sorry

/-- Inverse-wording bridge companion to Theorem 26.4: inverse right-uniqueness of the intrinsic
subdifferential graph is exactly the canonical `LeftUnique` owner. -/
theorem rightUnique_inv_subdifferentialGraph_iff_isEssentiallyStrictlyConvex
    {f : E → WithTopBot 𝕜} (hf : IsClosedProperConvex f) :
    (gph∂[Y](f))⁻¹.RightUnique ↔
      IsEssentiallyStrictlyConvex[Y] f := by
  change Relator.RightUnique (· ~[(gph∂[Y](f))⁻¹] ·) ↔ IsEssentiallyStrictlyConvex[Y] f
  exact (SetRel.rightUnique_inv_iff_leftUnique (ρ := gph∂[Y](f))).trans
    (leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex hf)

/-- Projection-criterion companion to Theorem 26.4: inverse single-valuedness of the intrinsic
subdifferential graph is equivalently injectivity of `Prod.snd` on that graph. -/
theorem injOn_snd_subdifferentialGraph_iff_isEssentiallyStrictlyConvex
    {f : E → WithTopBot 𝕜} (hf : IsClosedProperConvex f) :
    Set.InjOn Prod.snd (gph∂[Y](f)) ↔
      IsEssentiallyStrictlyConvex[Y] f := by
  rw [← SetRel.leftUnique_iff_injOn_snd]
  exact leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex hf

end

section

variable {𝕜 : Type v} [RCLike 𝕜]
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)
local notation "IsEssentiallyStrictlyConvex[" 𝕜 "]" =>
  Function.IsEssentiallyStrictlyConvex (𝕜 := 𝕜)

private theorem injOn_snd_functionSubdifferentialGraph_iff
    (f : E → WithTopBot 𝕜) :
    Set.InjOn Prod.snd (Function.subdifferentialGraph f) ↔
      Set.InjOn Prod.snd (_root_.subdifferentialGraph f) := by
  let e := InnerProductSpace.toDual 𝕜 E
  constructor
  · intro h p hp q hq hpq
    let p' : E × E := (p.1, e.symm p.2)
    let q' : E × E := (q.1, e.symm q.2)
    have hpDual : p.2 ∈ _root_.subdifferentialAt f p.1 :=
      _root_.mem_subdifferentialGraph.mp hp
    have hqDual : q.2 ∈ _root_.subdifferentialAt f q.1 :=
      _root_.mem_subdifferentialGraph.mp hq
    have hp' : p' ∈ Function.subdifferentialGraph f := by
      rw [Function.mem_subdifferentialGraph]
      change e (e.symm p.2) ∈ _root_.subdifferentialAt f p.1
      rwa [LinearIsometryEquiv.apply_symm_apply]
    have hq' : q' ∈ Function.subdifferentialGraph f := by
      rw [Function.mem_subdifferentialGraph]
      change e (e.symm q.2) ∈ _root_.subdifferentialAt f q.1
      rwa [LinearIsometryEquiv.apply_symm_apply]
    have hpq' : Prod.snd p' = Prod.snd q' := by
      simpa [p', q'] using congrArg e.symm hpq
    have hEq' : p' = q' := h hp' hq' hpq'
    apply Prod.ext
    · simpa [p', q'] using congrArg Prod.fst hEq'
    · have hsnd : e.symm p.2 = e.symm q.2 := by
        simpa [p', q'] using congrArg Prod.snd hEq'
      exact by simpa using congrArg e hsnd
  · intro h p hp q hq hpq
    have hpVec : p.2 ∈ Function.subdifferentialAt f p.1 :=
      Function.mem_subdifferentialGraph.mp hp
    have hqVec : q.2 ∈ Function.subdifferentialAt f q.1 :=
      Function.mem_subdifferentialGraph.mp hq
    have hp' : (p.1, e p.2) ∈ _root_.subdifferentialGraph f := by
      rw [_root_.mem_subdifferentialGraph]
      change p.2 ∈ Function.subdifferentialAt f p.1
      exact hpVec
    have hq' : (q.1, e q.2) ∈ _root_.subdifferentialGraph f := by
      rw [_root_.mem_subdifferentialGraph]
      change q.2 ∈ Function.subdifferentialAt f q.1
      exact hqVec
    have hEq : (p.1, e p.2) = (q.1, e q.2) := by
      exact h hp' hq' (by simpa using congrArg e hpq)
    apply Prod.ext
    · simpa using congrArg Prod.fst hEq
    · exact e.injective (by simpa using congrArg Prod.snd hEq)

private theorem leftUnique_functionSubdifferentialGraph_iff
    (f : E → WithTopBot 𝕜) :
    (Function.subdifferentialGraph f).LeftUnique ↔
      (_root_.subdifferentialGraph f).LeftUnique := by
  rw [SetRel.leftUnique_iff_injOn_snd, SetRel.leftUnique_iff_injOn_snd]
  exact injOn_snd_functionSubdifferentialGraph_iff f

namespace Function

/-- Theorem 26.4, vector-valued owner bridge form: on a complete inner-product space, the
Fréchet-Riesz realization of the subdifferential graph is left-unique exactly when the function is
essentially strictly convex. -/
theorem leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex
    {f : E → WithTopBot 𝕜} (hf : IsClosedProperConvex[𝕜] f) :
    (subdifferentialGraph f).LeftUnique ↔ IsEssentiallyStrictlyConvex[𝕜] f := by
  rw [leftUnique_functionSubdifferentialGraph_iff f]
  exact _root_.leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex hf

/-- Inverse-wording companion on the Fréchet-Riesz graph owner. -/
theorem rightUnique_inv_subdifferentialGraph_iff_isEssentiallyStrictlyConvex
    {f : E → WithTopBot 𝕜} (hf : IsClosedProperConvex[𝕜] f) :
    (subdifferentialGraph f)⁻¹.RightUnique ↔
      IsEssentiallyStrictlyConvex[𝕜] f := by
  change Relator.RightUnique (· ~[(subdifferentialGraph f)⁻¹] ·) ↔
      IsEssentiallyStrictlyConvex[𝕜] f
  exact (SetRel.rightUnique_inv_iff_leftUnique (ρ := subdifferentialGraph f)).trans
    (leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex hf)

/-- Theorem 26.4, vector-valued projection companion: on a complete inner-product space, the
Fréchet-Riesz realization of the subdifferential has injective second projection exactly when the
function is essentially strictly convex. This is the inner-product graph-coordinate restatement
of the owner theorem above. -/
theorem injOn_snd_subdifferentialGraph_iff_isEssentiallyStrictlyConvex
    {f : E → WithTopBot 𝕜} (hf : IsClosedProperConvex[𝕜] f) :
    Set.InjOn Prod.snd (subdifferentialGraph f) ↔ IsEssentiallyStrictlyConvex[𝕜] f := by
  rw [← SetRel.leftUnique_iff_injOn_snd]
  exact leftUnique_subdifferentialGraph_iff_isEssentiallyStrictlyConvex hf
end Function

end
