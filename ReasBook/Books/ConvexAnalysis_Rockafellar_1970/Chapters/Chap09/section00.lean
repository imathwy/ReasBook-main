import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Example_9_0_0_2 (from Chap02) -/
noncomputable section

section

open scoped Rockafellar
open Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: the example fixes a specific closed proper convex function `h` on `R²`,
  projects it to the scalar first coordinate, studies the owner image function
  `(Prod.fst : ℝ × ℝ → ℝ) ◁ orthantExponential : ℝ → WithTopBot ℝ`, and concludes both
  that the image of `epi h` under `((x, μ) ↦ (x.1, μ))` need not be
  closed and that the
  projected scalar image is not lower semicontinuous at `0`.
- `core/canonical`: the owner abstractions already present in the project are the chapter
  construction `Function.linearImage` for the image of a `WithTopBot`-valued function under a
  map, the canonical convex-owner `ConvexOn ℝ Set.univ`, the chapter properness predicate
  `Function.IsProper`, and mathlib's
  `LowerSemicontinuous` / `LowerSemicontinuousAt`.
- `bridge/view`: the textbook three-branch formula is a companion pointwise description of the
  owner-side scalar image function `(Prod.fst : ℝ × ℝ → ℝ) ◁ orthantExponential`, and
  the image-set conclusion is stated directly through the corresponding owner bridge
  `linearImageEpigraph`.
- Primitive data vs derived API: the primitive source data are the explicit function `h` and the
  first-coordinate projection; the closedness, convexity, properness, and failure of lower
  semicontinuity are companion properties of these canonical objects.
- Layer target: the explicit function remains `source-facing`; the projected image is used directly
  through the `core/canonical` owner `Function.linearImage`, and the three-branch scalar formula
  is the main `bridge/view` result.

Domain-style sampling used here:
- `Function.linearImage` and `Function.linearImage_eq_sInf_image` from Theorem 5.7;
- `Function.isConvex_linearImage` from the same owner file;
- `Prod.fst` as the canonical first-coordinate projection map;
- `LowerSemicontinuousAt` and `lowerSemicontinuousAt_iff_le_liminf` from the Section 7
  semicontinuity API.
-/

local notation "π₁" => (Prod.fst : ℝ × ℝ → ℝ)

/-- The explicit function from the example, written on `R²` in owner coordinates. It equals
`exp (-sqrt (x₀ x₁))` on the nonnegative orthant and `+∞` elsewhere; the companion theorems below
state its lower semicontinuity, convexity, and properness. -/
def orthantExponential : (ℝ × ℝ) → WithTopBot ℝ :=
  fun x ↦
    if 0 ≤ x.1 ∧ 0 ≤ x.2 then
      Real.exp (-(Real.sqrt (x.1 * x.2)))
    else
      ⊤

-- Proof sketch: on the fiber above `ξ₁ < 0`, the nonnegative-orthant condition fails for every
-- point, so the infimum is `⊤`. On the fiber above `0`, every admissible point has value
-- `exp 0 = 1`. On the fiber above `ξ₁ > 0`, the values are `exp (-sqrt ξ₁ * sqrt ξ₂)` along
-- `ξ₂ ≥ 0`, and these decrease to `0` as `ξ₂ → +∞`, so the infimum is `0`.
/-- The projected image of the example function is the three-branch function described in the
textbook. -/
theorem orthantExponential_linearImage_fst_eq (ξ₁ : ℝ) :
    (π₁ ◁ orthantExponential) ξ₁ =
      if 0 < ξ₁ then
        (0 : WithTopBot ℝ)
      else if ξ₁ = 0 then
        (1 : WithTopBot ℝ)
      else
        ⊤ := sorry

-- Proof sketch: the nonnegative orthant is closed, and on that orthant the map
-- `(x₀, x₁) ↦ exp (-sqrt (x₀ x₁))` is continuous. The explicit piecewise formula therefore gives a
-- closed epigraph, i.e. lower semicontinuity of the source function.
/-- The source function in the example is lower semicontinuous. -/
theorem orthantExponential_lowerSemicontinuous :
    LowerSemicontinuous orthantExponential := sorry

-- Proof sketch: the real epigraph of the source function is the region above the graph of the
-- convex orthant exponential on the nonnegative quadrant, together with the vertical rays over the
-- complement. Check convexity directly from the explicit formula, or identify the defining
-- inequality with a convex epigraph condition on the orthant.
/-- The source function is convex on the whole ambient space, at the canonical owner layer
`ConvexOn ℝ Set.univ`. -/
theorem orthantExponential_convexOn_univ :
    ConvexOn ℝ (Set.univ : Set (ℝ × ℝ)) orthantExponential := sorry

/-- Bridge to the chapter whole-space owner form of convexity. -/
theorem orthantExponential_isConvex :
    orthantExponential.IsConvex ℝ := by
  simpa [Function.IsConvex, Function.IsConvexOn] using orthantExponential_convexOn_univ

-- Proof sketch: `orthantExponential` is not identically `⊤`, because it takes the value
-- `1` at the origin, and it never takes the value `⊥`. These are exactly the chapter properness
-- conditions.
/-- The source function in the example is proper. -/
theorem orthantExponential_isProper :
    orthantExponential.IsProper := sorry

-- Proof sketch: identify
-- `linearImageEpigraph π₁ orthantExponential`
-- with the real
-- epigraph of `π₁ ◁ orthantExponential` using
-- `Function.linearImageEpigraph_eq_epi_linearImage`. If this image set were closed, the
-- corresponding scalar image function would be lower semicontinuous at `0`, contradicting the
-- explicit three-branch formula.
/-- Example 9.0.0.2: although the source function is closed proper convex, the image of its real
epigraph under `((x, μ) ↦ (x.1, μ))` is not closed. -/
theorem orthantExponential_linearImageEpigraph_fst_not_closed :
    ¬ IsClosed (linearImageEpigraph π₁ orthantExponential) :=
  sorry

-- Proof sketch: use the explicit formula from `orthantExponential_linearImage_fst_eq`. Along any
-- sequence `ξ₁ₙ ↓ 0` with `ξ₁ₙ > 0`, the projected image values are constantly `0`, so their
-- liminf is `0`, while the value at `0` is `1`. This violates the sequential criterion
-- `lowerSemicontinuousAt_iff_le_liminf`.
/-- Example 9.0.0.2: for the explicit closed proper convex function on `R²` given by
`exp (-sqrt (ξ₁ ξ₂))` on the nonnegative orthant and `+∞` elsewhere, the projected image under
`(ξ₁, ξ₂) ↦ ξ₁` is not lower semicontinuous at `0`. -/
theorem orthantExponential_linearImage_fst_not_lowerSemicontinuousAt_zero :
    ¬ LowerSemicontinuousAt (π₁ ◁ orthantExponential) 0 :=
  sorry

end

/-! ### Example_9_0_0_4 (from Chap02) -/
section

open Set
open Function

variable {𝕜 : Type*}
variable [Inv 𝕜] [Zero 𝕜]

local notation "π₁" => (Prod.fst : 𝕜 × 𝕜 → 𝕜)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Example 9.0.0.4 is the projection statement that the concrete closed convex
  set `hyperbolaEpigraph` has nonclosed first-coordinate image.
- `core/canonical`: the reusable owner object for projections of sets in `𝕜 × 𝕜` is the effective
  domain of `Function.verticalInfimum`; for this example that owner is
  `dom(verticalInfimum hyperbolaEpigraph)`.
- `bridge/view`: the textbook projection onto `ξ₁` is recovered through
  `Function.effectiveDomain_verticalInfimum_eq_image_fst`.
- Primitive data vs derived API: the primitive data now live upstream in
  `Chap02.HyperbolaEpigraph`; this file contributes the example-specific projection computation at
  the primitive set-image layer, then exports owner-form corollaries via the
  vertical-infimum bridge.
- Layer target: `source-facing`, reusing the shared owner instead of redefining it locally.

Domain-style sampling used here:
- the shared Chapter 2 owner `hyperbolaEpigraph`;
- `mem_hyperbolaEpigraph_iff`;
- `Function.effectiveDomain_verticalInfimum_eq_image_fst` as the set-projection/effective-domain
  bridge;
- `closure_Ioi` for the nonclosedness of the projected image.
-/

section

variable [Preorder 𝕜]

-- Proof sketch: compute the first-coordinate projection directly: a projected point `(x, y)` in
-- `hyperbolaEpigraph` has `x > 0`; conversely, each `x > 0` has witness `(x, x⁻¹)`.
/-- The first-coordinate projection of `hyperbolaEpigraph` is exactly `(0, +∞)`. -/
theorem image_fst_hyperbolaEpigraph_eq_Ioi :
    π₁ '' hyperbolaEpigraph = Ioi (0 : 𝕜) := by
  ext x
  constructor
  · rintro ⟨⟨x, y⟩, hp, rfl⟩
    exact (mem_hyperbolaEpigraph_iff.mp hp).1
  · intro hx
    exact ⟨(x, x⁻¹), mem_hyperbolaEpigraph_iff.mpr ⟨hx, le_rfl⟩, rfl⟩

end

section

variable [LinearOrder 𝕜] [TopologicalSpace 𝕜] [OrderTopology 𝕜] [DenselyOrdered 𝕜]
  [NoMaxOrder 𝕜]

-- Proof sketch: rewrite the projection as `Ioi (0 : 𝕜)`, whose closure is `Ici 0`.
/-- Example 9.0.0.4 (source-facing form): the projection `π₁ '' hyperbolaEpigraph` is not
closed. -/
theorem image_fst_hyperbolaEpigraph_not_closed :
    ¬ IsClosed (π₁ '' hyperbolaEpigraph) := by
  rw [image_fst_hyperbolaEpigraph_eq_Ioi]
  intro hclosed
  have h0 : (0 : 𝕜) ∈ closure (Ioi (0 : 𝕜)) := by
    have hclosure : closure (Ioi (0 : 𝕜)) = Ici (0 : 𝕜) := closure_Ioi (a := (0 : 𝕜))
    rw [hclosure]
    simp
  rw [hclosed.closure_eq] at h0
  simp at h0

end

section

variable [ConditionallyCompleteLattice 𝕜]

-- Proof sketch: this is the local specialization of the global projection/domain bridge
-- `effectiveDomain_verticalInfimum_eq_image_fst`.
/-- Bridge form: the first-coordinate projection of `hyperbolaEpigraph` equals
`dom(verticalInfimum hyperbolaEpigraph)`. -/
theorem image_fst_hyperbolaEpigraph_eq_dom_verticalInfimum :
    π₁ '' hyperbolaEpigraph = dom(verticalInfimum hyperbolaEpigraph) := by
  symm
  simpa [π₁] using
    (effectiveDomain_verticalInfimum_eq_image_fst (F := hyperbolaEpigraph))

-- Proof sketch: use the global bridge
-- `effectiveDomain_verticalInfimum_eq_image_fst`, then the direct projection computation.
/-- The effective domain of `verticalInfimum hyperbolaEpigraph` is exactly `(0, +∞)`. -/
theorem dom_verticalInfimum_hyperbolaEpigraph_eq_Ioi :
    dom(verticalInfimum hyperbolaEpigraph) = Ioi (0 : 𝕜) := by
  calc
    dom(verticalInfimum hyperbolaEpigraph) = π₁ '' hyperbolaEpigraph := by
      exact image_fst_hyperbolaEpigraph_eq_dom_verticalInfimum.symm
    _ = Ioi (0 : 𝕜) := image_fst_hyperbolaEpigraph_eq_Ioi

-- Proof sketch: rewrite `dom(verticalInfimum hyperbolaEpigraph)` as `Ioi (0 : 𝕜)`.
/-- Owner-membership form: `x` belongs to `dom(verticalInfimum hyperbolaEpigraph)` exactly when
`x > 0`. -/
theorem mem_dom_verticalInfimum_hyperbolaEpigraph_iff {x : 𝕜} :
    x ∈ dom(verticalInfimum hyperbolaEpigraph) ↔ 0 < x := by
  rw [dom_verticalInfimum_hyperbolaEpigraph_eq_Ioi]
  simp [mem_Ioi]

end

section

variable [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [DenselyOrdered 𝕜] [NoMaxOrder 𝕜]

-- Proof sketch: rewrite `dom(verticalInfimum hyperbolaEpigraph)` as the first-coordinate
-- projection via `effectiveDomain_verticalInfimum_eq_image_fst`, then apply the source-facing
-- nonclosedness theorem for that projection.
/-- Example 9.0.0.4 in owner form: `dom(verticalInfimum hyperbolaEpigraph)` is not closed. -/
theorem dom_verticalInfimum_hyperbolaEpigraph_not_closed :
    ¬ IsClosed (dom(verticalInfimum hyperbolaEpigraph)) := by
  simpa [image_fst_hyperbolaEpigraph_eq_dom_verticalInfimum] using
    (image_fst_hyperbolaEpigraph_not_closed : ¬ IsClosed (π₁ '' hyperbolaEpigraph))

end

end

/-! ### Proposition_9_0_0_1 (from Chap02) -/
/-
Source/core/bridge triage:
- `source-facing`: Proposition 9.0.0.1 contrasts two image behaviors: exact preservation of
  relative interior for convex sets under linear maps, and one-sided preservation of closure under
  continuous maps.
- `core/canonical`: both clauses already live upstream at the right owners:
  `Convex.intrinsicInterior_linear_image` and `image_closure_subset_closure_image`.
- `bridge/view`: Rockafellar's `ri (A C) = A (ri C)` and `cl (A C) ⊇ A (cl C)` are therefore kept
  as direct recalls of those canonical owners, instead of introducing local wrapper names.
- Primitive data vs derived API: this file introduces no new primitive notion, so adding duplicate
  theorem wrappers would only overgrow the public API.
- Layer target: recall-only item; no compatibility aliases for already-canonical owners.
- Abstraction checks:
  - codomain/ambient layer: no codomain owner is introduced here; both clauses reuse existing
    set-level canonical owners directly;
  - scalar/ambient assumptions: this file adds no local assumptions and therefore does not
    overconstrain any theorem surface;
  - owner choice: no concrete-model owner is introduced; the item reuses intrinsic owner APIs;
  - topology phrasing: the relative-interior clause is already intrinsic (`ri`), while the closure
    clause is the canonical ambient continuity theorem;
  - naming/notation: no long local owner names or wrapper notation are added.
-/

/- The relative-interior clause quoted in Proposition 9.0.0.1 is exactly Theorem 6.6 (1), namely
that a linear map sends the relative interior of a convex set onto the relative interior of its
image. -/
recall Convex.intrinsicInterior_linear_image

/- The closure clause quoted in Proposition 9.0.0.1 is exactly the canonical continuity theorem:
for a continuous map `A`, one has `A '' closure C ⊆ closure (A '' C)`, equivalently
`cl (A C) ⊇ A (cl C)`. -/
recall image_closure_subset_closure_image

/-! ### Proposition_9_0_0_3 (from Chap02) -/
noncomputable section

open scoped Rockafellar
open Function

section

variable {𝕜 : Type*} {E F : Type*}
variable [ConditionallyCompleteLinearOrder 𝕜]

variable (A : E → F) (h : E → WithTopBot 𝕜)

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: the proposition considers the image `F` of the scalar epigraph of `h`
  under the map `(x, r) ↦ (A x, r)`, identifies the closure of its vertical section
  above a fixed `y` with the scalar heights above `(A ◁ h)(y)`, and records the resulting
  attainment criterion under closedness plus exclusion of the downward recession direction.
- `core/canonical`: the owner abstraction for `(Ah)(y)` is the chapter declaration
  `Function.linearImage A h` from Theorem 5.7, viewed through the owner
  `Function.verticalInfimum` on subsets of `F × 𝕜`, while recession directions are already
  organized by the chapter owner `recessionCone`.
- `bridge/view`: the textbook set `F` is the Chapter 5 bridge object
  `linearImageEpigraph A h`, and part (1) is refined to the sectionwise closure identity
  `closure (verticalSection (linearImageEpigraph A h) y) =
    verticalSection (epi (Function.linearImage A h)) y`, with the global epigraph equality
  kept only as the closed-image specialization in part (2). Part (3) is likewise stated first
  from the local section-closed hypothesis at `y`, with the global closed-image form kept as a
  derived specialization. Both parts use the owner-side effective-domain condition
  `y ∈ dom(Function.linearImage A h)`, which is equivalent to section nonemptiness by the
  vertical-infimum description from Theorem 5.7 and the effective-domain API of
  `Function.verticalInfimum`.
- Primitive data vs derived API: the primitive inputs are the map `A`, the function `h`,
  and the image set of its scalar epigraph. The sectionwise closure identity, its closed-image
  specialization, and the attainment statement are derived consequences and should remain theorem-
  level API, while any fiber-membership unpacking needed to prove them is internal.
- Ambient minimization: the primitive section-equality and attainment surfaces for parts (2) and
  (3) are order-theoretic (`WithTopBot` + `dom`) and do not require topological closure data; only
  the closure-identification bridge in part (1) and its derived closed-section specializations use
  order-topological hypotheses on `𝕜`. No topology on `F` is required at the primitive sectionwise
  layer. The concrete `R^n → R^m` display model is therefore demoted to a downstream
  specialization.

Domain-style sampling used here:
- `Function.verticalInfimum`;
- `Function.linearImage`;
- `linearImageEpigraph`;
- `Function.linearImage_eq_sInf_image`;
- `Function.linearImage_eq_verticalInfimum_linearImageEpigraph`;
- `recessionCone`.
-/

/-!
Sectionwise API for Proposition 9.0.0.3 (2) and (3), with closedness and global-closedness
specializations below.
-/

/-- Primitive sectionwise owner bridge for Proposition 9.0.0.3 (2): if every scalar section of
`linearImageEpigraph A h` agrees with the corresponding section of `epi (A ◁ h)`, then the two
sets are equal. -/
theorem linearImageEpigraph_eq_epi_linearImage_of_sections_eq
    (hsection_eq :
      ∀ y : F,
        verticalSection (linearImageEpigraph A h) y =
          verticalSection (epi (A ◁ h)) y) :
    linearImageEpigraph A h = epi (A ◁ h) := by
  ext p
  change p.2 ∈ verticalSection (linearImageEpigraph A h) p.1 ↔
    p.2 ∈ verticalSection (epi (A ◁ h)) p.1
  simpa [hsection_eq p.1]

/-- Primitive sectionwise attainment bridge for Proposition 9.0.0.3 (3): if the scalar section of
`linearImageEpigraph A h` above `y` agrees with the section of `epi (A ◁ h)` and `(A ◁ h) y` is
finite and not `⊥`, then the infimum value is attained along the fiber `A x = y`. -/
theorem linearImage_attains_of_section_eq_of_ne_bot_of_mem_dom
    (y : F)
    (hsection_eq :
      verticalSection (linearImageEpigraph A h) y =
        verticalSection (epi (A ◁ h)) y)
    (hy : y ∈ dom(A ◁ h))
    (hy_ne_bot : (A ◁ h) y ≠ ⊥) :
    ∃ x : E, A x = y ∧ h x = (A ◁ h) y := by
  have hy_ne_top : (A ◁ h) y ≠ ⊤ := ne_of_lt hy
  lift (A ◁ h) y to 𝕜 using ⟨hy_ne_top, hy_ne_bot⟩ with μ hμ
  have hμ_mem_epi : (y, μ) ∈ epi (A ◁ h) := by
    simp [hμ]
  have hμ_mem_section : μ ∈ verticalSection (linearImageEpigraph A h) y := by
    rw [hsection_eq]
    simpa [verticalSection] using hμ_mem_epi
  have hμ_mem_image : (y, μ) ∈ linearImageEpigraph A h := by
    simpa [verticalSection] using hμ_mem_section
  rcases (mem_linearImageEpigraph_iff A h).1 hμ_mem_image with ⟨x, hxy, hx_le⟩
  have hfx_le_hx : (A ◁ h) y ≤ h x := by
    rw [linearImage_eq_sInf_image]
    exact sInf_le ⟨x, hxy, rfl⟩
  have hμ_le_hx : (μ : WithTopBot 𝕜) ≤ h x := by
    simpa [hμ] using hfx_le_hx
  have hhx_eq_hμ : h x = (μ : WithTopBot 𝕜) := le_antisymm hx_le hμ_le_hx
  exact ⟨x, hxy, hhx_eq_hμ⟩

section

variable [TopologicalSpace 𝕜] [OrderTopology 𝕜] [DenselyOrdered 𝕜]
variable [NoBotOrder 𝕜] [NoMaxOrder 𝕜]

/-- Proposition 9.0.0.3 (1): for a fixed base point `y`, the closure of the vertical section of
the image set `F` of the scalar epigraph of `h` under `(x, r) ↦ (A x, r)` is exactly the
corresponding vertical section of `epi (A ◁ h)`. -/
theorem closure_section_linearImageEpigraph_eq_section_epi_linearImage
    (y : F) :
    closure (verticalSection (linearImageEpigraph A h) y) =
      verticalSection (epi (A ◁ h)) y := by
  have hupper :
      ∀ {μ ν : 𝕜}, μ ∈ verticalSection (linearImageEpigraph A h) y → μ ≤ ν →
        ν ∈ verticalSection (linearImageEpigraph A h) y := by
    intro μ ν hμ hμν
    rcases (mem_linearImageEpigraph_iff A h).1 (by simpa [verticalSection] using hμ) with
      ⟨x, hxy, hxμ⟩
    have hν : (y, ν) ∈ linearImageEpigraph A h :=
      (mem_linearImageEpigraph_iff A h).2 ⟨x, hxy, le_trans hxμ (by simpa using hμν)⟩
    simpa [verticalSection] using hν
  simpa [linearImage_eq_verticalInfimum_linearImageEpigraph, verticalSection, Set.preimage,
    Set.Ici] using
    (closure_verticalSection_eq_preimage_Ici_of_upward_closed
      (F := linearImageEpigraph A h) (x := y) hupper)

/-- Proposition 9.0.0.3 (2), closed-section specialization: if every scalar section
`verticalSection (linearImageEpigraph A h) y` is closed, then the image epigraph equals
`epi (A ◁ h)`. -/
theorem linearImageEpigraph_eq_epi_linearImage_of_sections_closed
    (hsection_closed :
      ∀ y : F, IsClosed (verticalSection (linearImageEpigraph A h) y)) :
    linearImageEpigraph A h = epi (A ◁ h) := by
  refine linearImageEpigraph_eq_epi_linearImage_of_sections_eq (A := A) (h := h) ?_
  intro y
  rw [← (hsection_closed y).closure_eq,
    closure_section_linearImageEpigraph_eq_section_epi_linearImage A h y]

/-- Proposition 9.0.0.3 (3), closed-section specialization: if the section
`verticalSection (linearImageEpigraph A h) y` is closed and `(A ◁ h) y` is finite and not `⊥`,
then the infimum value `(A ◁ h) y` is attained
by some point in the fiber `A x = y`.

The source-facing no-downward-recession hypothesis is a global recognition criterion that implies
this local non-`⊥` premise in typical convex-closed settings; the attainment mechanism itself only
needs the local premise. -/
theorem linearImage_attains_of_section_closed_of_ne_bot_of_mem_dom
    (y : F)
    (hsection_closed : IsClosed (verticalSection (linearImageEpigraph A h) y))
    (hy : y ∈ dom(A ◁ h))
    (hy_ne_bot : (A ◁ h) y ≠ ⊥) :
    ∃ x : E, A x = y ∧ h x = (A ◁ h) y := by
  refine linearImage_attains_of_section_eq_of_ne_bot_of_mem_dom (A := A) (h := h) y ?_ hy hy_ne_bot
  rw [← hsection_closed.closure_eq,
    closure_section_linearImageEpigraph_eq_section_epi_linearImage A h y]

section

variable [TopologicalSpace F]

/-- If `linearImageEpigraph A h` is closed, then Proposition 9.0.0.3 (2) identifies it
directly with the scalar epigraph of `A ◁ h`. -/
theorem linearImageEpigraph_eq_epi_linearImage
    (hF_closed : IsClosed (linearImageEpigraph A h)) :
    linearImageEpigraph A h = epi (A ◁ h) := by
  refine linearImageEpigraph_eq_epi_linearImage_of_sections_closed (A := A) (h := h) ?_
  intro y
  simpa [verticalSection] using hF_closed.preimage (Continuous.prodMk_right y)

/-- Proposition 9.0.0.3 (3), closed-image specialization of
`linearImage_attains_of_section_closed_of_ne_bot_of_mem_dom`. -/
theorem linearImage_attains_of_closed_imageEpigraph_of_ne_bot_of_mem_dom
    (y : F)
    (hF_closed : IsClosed (linearImageEpigraph A h))
    (hy : y ∈ dom(A ◁ h))
    (hy_ne_bot : (A ◁ h) y ≠ ⊥) :
    ∃ x : E, A x = y ∧ h x = (A ◁ h) y := by
  refine linearImage_attains_of_section_closed_of_ne_bot_of_mem_dom
    (A := A) (h := h) y ?_ hy hy_ne_bot
  simpa [verticalSection] using hF_closed.preimage (Continuous.prodMk_right y)

end

end

end Function

end
