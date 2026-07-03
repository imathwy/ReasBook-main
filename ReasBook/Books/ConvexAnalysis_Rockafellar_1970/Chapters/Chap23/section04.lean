import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_23_4_1 (from Chap05) -/
noncomputable section

open scoped RealInnerProductSpace

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 23.4.1 specializes Theorem 23.4 to the finite case: a real-valued
  convex function on a finite-dimensional real inner-product space has, at every point, a
  nonempty bounded closed convex subdifferential; its directional derivative is finite-valued,
  positively homogeneous, and convex; and in each direction the directional derivative is attained
  as a maximum inner product over the subdifferential.
- `core/canonical`: the relevant chapter owners already exist as `Function.toEReal`,
  `Function.subdifferentialAt`, and `Function.directionalDerivativeAt`.
- `bridge/view`: the source's “finite convex function on `ℝⁿ`” is expressed here as a real-valued
  function `f : E → ℝ` with `ConvexOn ℝ Set.univ f`, while the chapter's subdifferential and
  directional-derivative owners are applied to the canonical codomain lift `f.toEReal`.

Domain-style sampling used here:
- `Function.isConvex_coe_of_convexOn_univ` from `Chap01.Theorem_4_2`;
- `Function.subdifferentialAt_nonempty_and_bounded_iff_mem_interior_dom` from `Chap05.Theorem_23_4`;
- `Function.directionalDerivativeAt_finite_everywhere_of_mem_interior_dom` from
  `Chap05.Theorem_23_4`;
- `Function.positivelyHomogeneous_directionalDerivativeAt_of_finite_point` and
  `Function.isConvex_directionalDerivativeAt_of_finite_point` from `Chap05.Theorem_23_1`;
- the Chapter 23 support-function owner theorem
  `Function.directionalDerivativeAt_eq_supportFunction_subdifferentialAt_of_mem_riDom` from
  `Chap05.Theorem_23_4`;
- the Chapter 23 support-function maximizer theorem
  `Function.mem_subdifferentialAt_supportFunction_iff_mem_and_isMaxOn` from
  `Chap05.Corollary_23_5_3`.

Primitive data vs derived API:
- primitive source data: a finite real-valued convex function `f : E → ℝ`, encoded by
  `ConvexOn ℝ Set.univ f`;
- canonical bridge data: the codomain lift `f.toEReal`;
- derived API: the shape of `subdifferentialAt f.toEReal x`, regularity of
  `directionalDerivativeAt f.toEReal x`, and the maximizing subgradient statement.

Layer target: `source-facing`, stated on the finite real-valued surface and routed through the
canonical Chapter 23 owners only where the project already organizes the mathematics that way.

Ambient-assumption minimization:
- the source's `ℝⁿ` is represented by an arbitrary finite-dimensional real inner-product space,
  not the coordinate model `EuclideanSpace ℝ (Fin n)`, because only the finite-dimensional
  Euclidean structure matters here;
- the vector-valued bridge `Function.subdifferentialAt` is owned over complete real
  inner-product spaces upstream, but in this finite-dimensional specialization completeness is
  supplied canonically by typeclass inference from `FiniteDimensional ℝ E`, so it is not kept as a
  public binder here.
-/

namespace Function

variable {f : E → ℝ} (x : E)
variable (hf_convex : ConvexOn ℝ Set.univ f)

-- Proof sketch: specialize Theorem 23.4 (5) to the canonical lift `f.toEReal`. Since `f` is
-- finite-valued on all of `E`, its effective domain is all of `E`, so every point lies in the
-- interior of the domain and the subdifferential is nonempty.
/-- Corollary 23.4.1 (1): for a finite convex function, the subdifferential at every point is
nonempty. -/
theorem subdifferentialAt_nonempty_of_convexOn_univ
    :
    (subdifferentialAt f.toEReal x).Nonempty := sorry

-- Proof sketch: the same specialization of Theorem 23.4 (5) gives boundedness of the
-- subdifferential at every point because `interior (dom(f.toEReal)) = Set.univ`.
/-- Corollary 23.4.1 (2): for a finite convex function, the subdifferential at every point is
bounded. -/
theorem subdifferentialAt_bounded_of_convexOn_univ
    :
    Bornology.IsBounded (subdifferentialAt f.toEReal x) := sorry

-- Proof sketch: subdifferentials of convex functions are intersections of closed affine halfspaces
-- defined by the supporting-inequality owner, hence are closed in the finite-dimensional Euclidean
-- setting used here.
/-- Corollary 23.4.1 (3): for a finite convex function, the subdifferential at every point is
closed. -/
theorem subdifferentialAt_isClosed_of_convexOn_univ
    :
    IsClosed (subdifferentialAt f.toEReal x) := sorry

-- Proof sketch: the defining supporting inequalities are preserved under convex combinations of
-- subgradients, so the subdifferential is convex.
/-- Corollary 23.4.1 (4): for a finite convex function, the subdifferential at every point is a
convex set. -/
theorem subdifferentialAt_convex_of_convexOn_univ
    :
    Convex ℝ (subdifferentialAt f.toEReal x) := sorry

-- Proof sketch: specialize Theorem 23.4 (6) to `f.toEReal`; finiteness of `f` on all of `E`
-- forces the directional derivative at every point and in every direction to be represented by a
-- real number.
/-- Corollary 23.4.1 (5): for a finite convex function, every directional derivative is
finite-valued. -/
theorem directionalDerivativeAt_finite_of_convexOn_univ
    (y : E) :
    ∃ r : ℝ, directionalDerivativeAt f.toEReal x y = (r : EReal) := sorry

-- Proof sketch: view `f.toEReal` as a convex extended-real-valued function finite at `x`, then
-- apply the Chapter 23 positive-homogeneity theorem for directional derivatives at finite points.
/-- Corollary 23.4.1 (6): for a finite convex function, the directional derivative at a point is a
positively homogeneous function of the direction. -/
theorem positivelyHomogeneous_directionalDerivativeAt_of_convexOn_univ
    :
    (directionalDerivativeAt f.toEReal x).PositivelyHomogeneous ℝ := sorry

-- Proof sketch: the same finite-point specialization of Theorem 23.1 makes the direction
-- function `y ↦ directionalDerivativeAt f.toEReal x y` convex.
/-- Corollary 23.4.1 (7): for a finite convex function, the directional derivative at a point is
convex as a function of the direction. -/
theorem isConvex_directionalDerivativeAt_of_convexOn_univ
    :
    (directionalDerivativeAt f.toEReal x).IsConvex ℝ := sorry

-- Proof sketch: by clauses (1) through (4), the subdifferential is a nonempty compact convex set.
-- The canonical Chapter 23 owner theorem
-- `Function.directionalDerivativeAt_eq_supportFunction_subdifferentialAt_of_mem_riDom`
-- identifies the directional derivative with its support function, and the linear functional
-- `xStar ↦ ⟪xStar, y⟫` attains its maximum on that compact set. The source's maximizing clause is
-- therefore stated on the canonical extrema owner `IsMaxOn`.
/-- Corollary 23.4.1 (8): for every direction `y`, the directional derivative is the maximum inner
product with vectors in the subdifferential at `x`. -/
theorem exists_subgradient_maximizing_inner_of_convexOn_univ
    (y : E) :
    ∃ xStar ∈ subdifferentialAt f.toEReal x,
      directionalDerivativeAt f.toEReal x y = ((⟪xStar, y⟫ : ℝ) : EReal) ∧
        IsMaxOn (fun zStar : E ↦ ⟪zStar, y⟫) (subdifferentialAt f.toEReal x) xStar := sorry

end Function

end

/-! ### Example_23_4_2 (from Chap05) -/
noncomputable section

open scoped Convex RealInnerProductSpace Rockafellar

local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Example 23.4.2 exhibits a function on `R²` whose subdifferential-domain set is
  not convex.
- `core/canonical`: the relevant chapter owners are `dom(·)`, the relative-interior notation
  `ri[ℝ](·)`, the segment owner `[x -[ℝ] y]`, the Chapter 12 regularity owner
  `Function.IsClosedProperConvex`, and the subgradient-domain owner
  `(Function.subdifferentialGraph f).dom`.
- `bridge/view`: the example-specific half-plane and exceptional segment remain source-facing
  subsets of `R²`, while the “subdifferentiability locus” itself is not kept as a parallel local
  wrapper around the canonical graph-domain owner.

Domain-style sampling used here:
- `dom(·)` from `Chap01.Definition_4_4`;
- `ri[𝕜](·)` from `Chap02.Text_6_8`;
- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`;
- the segment owner `[x -[𝕜] y]` from mathlib / `Chap01.Definition_2_0_2`;
- `Function.subdifferentialGraph` from `Chap05.Definition_5_24_3`.

Primitive data vs derived API:
- primitive owner-level object for the locus: `(Function.subdifferentialGraph f).dom`;
- derived/example-specific data: the explicit half-plane and exceptional segment describing that
  owner in this concrete counterexample, together with the owner-level regularity fact that the
  example itself is a closed proper convex function.

Layer target: `source-facing`, stated directly on the chapter owner surfaces rather than through
one-off local aliases for relation domains or relative interiors of segments.
-/

/-- The one-variable branch `g(ξ₁) = 1 - sqrt ξ₁` on `ξ₁ ≥ 0`, extended by `+∞` to `ξ₁ < 0`. -/
def sqrtBranch (x1 : ℝ) : WithBotTop ℝ :=
  if 0 ≤ x1 then ((1 - Real.sqrt x1 : ℝ) : WithBotTop ℝ) else ⊤

/-- The Example 23.4.2 counterexample function
`f(ξ₁, ξ₂) = max {g(ξ₁), |ξ₂|}` on `R²`. -/
def subdifferentiabilityCounterexample (xi : R2) : WithBotTop ℝ :=
  max (sqrtBranch (xi 0)) (((|xi 1|) : ℝ) : WithBotTop ℝ)

-- Proof sketch: `sqrtBranch` is the sum of the indicator of the closed half-line `[0, ∞)` and
-- the continuous convex branch `x₁ ↦ 1 - sqrt x₁` on that half-line, so it is closed proper
-- convex as a one-variable extended-real function. The map `ξ ↦ |ξ₂|` is a finite continuous
-- convex function on `R²`, hence also closed proper convex after the canonical codomain lift.
-- Taking the pointwise maximum preserves convexity and lower semicontinuity, and properness holds
-- because `(0, 0)` is a finite point while neither branch ever attains `⊥`.
/-- Example 23.4.2: the explicit counterexample function itself lies in the canonical convex-
analysis owner layer of closed proper convex functions. -/
theorem subdifferentiabilityCounterexample_isClosedProperConvex :
    subdifferentiabilityCounterexample.IsClosedProperConvex (𝕜 := ℝ) := sorry

/-- The closed right half-plane `ξ₁ ≥ 0` in `R²`. -/
def rightHalfPlane : Set R2 :=
  {xi | 0 ≤ xi 0}

private def upperEndpoint : R2 :=
  EuclideanSpace.single (1 : Fin 2) (1 : ℝ)

private def lowerEndpoint : R2 :=
  EuclideanSpace.single (1 : Fin 2) (-1 : ℝ)

/-- The relative interior of the segment joining `(0, 1)` and `(0, -1)`. -/
def exceptionalSegment : Set R2 :=
  ri[ℝ]([upperEndpoint -[ℝ] lowerEndpoint])

-- Proof sketch: the first-coordinate branch is finite exactly on `x1 ≥ 0`, while the second
-- branch `|ξ₂|` is finite everywhere. Therefore the pointwise maximum is finite exactly on the
-- closed right half-plane.
/-- The effective domain of the Example 23.4.2 counterexample is the closed right half-plane. -/
theorem dom_subdifferentiabilityCounterexample :
    dom(subdifferentiabilityCounterexample) = rightHalfPlane := sorry

-- Proof sketch: combine the explicit domain computation above with the Chapter 23
-- subdifferentiability criterion for maxima. On the boundary line `ξ₁ = 0`, the one-variable
-- branch `1 - sqrt ξ₁` has no supporting subgradient for `|ξ₂| < 1`, producing exactly the
-- relative interior of the vertical segment as the exceptional set; elsewhere on the domain a
-- supporting vector exists.
/-- Example 23.4.2: for the function `f(ξ₁, ξ₂) = max {g(ξ₁), |ξ₂|}` with
`g(ξ₁) = 1 - sqrt ξ₁` on `ξ₁ ≥ 0` and `g(ξ₁) = +∞` on `ξ₁ < 0`, the subdifferentiability locus is
the effective domain minus the relative interior of the segment joining `(0, 1)` and `(0, -1)`. -/
theorem subdifferentialGraph_dom_eq_dom_diff_exceptionalSegment :
    (Function.subdifferentialGraph subdifferentiabilityCounterexample).dom =
      dom(subdifferentiabilityCounterexample) \ exceptionalSegment := sorry

-- Proof sketch: by the theorem above, both endpoints `(0, 1)` and `(0, -1)` lie in the
-- subdifferentiability locus, while their midpoint `(0, 0)` lies in the exceptional segment and
-- therefore does not. Hence the locus fails the midpoint test for convexity.
/-- The subdifferentiability locus in Example 23.4.2 is not convex. -/
theorem not_convex_subdifferentialGraph_dom :
    ¬ Convex ℝ (Function.subdifferentialGraph subdifferentiabilityCounterexample).dom := sorry

/-! ### Theorem_23_4 (from Chap05) -/
noncomputable section

open Bornology
open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v} [NormedField 𝕜] [Preorder 𝕜]
variable {E : Type u} [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f : E → WithBotTop 𝕜} {x : E}
variable {Y : Type (max u v)} [HasPairing E Y 𝕜]

/-!
Theorem 23.4 at the canonical owner layer.

- codomain generalized from `WithBotTop ℝ` to `WithBotTop 𝕜`;
- subdifferential-facing clauses exposed at the pairing level `Y`;
- real inner-product vector-subdifferential theorems kept below as bridge views.
-/

-- Proof sketch: if `x ∉ dom(f)`, then `f x = ⊤`. A subgradient inequality at `x` would force
-- every finite point of `f` to have value `⊤`, contradicting properness.
/-- Theorem 23.4 (1), intrinsic owner form: for a proper function, the dual-valued
subdifferential is empty at every point outside the effective domain. -/
theorem subdifferentialAt_eq_empty_of_not_mem_dom
    (hf_proper : f.IsProper) (hx : x ∉ dom(f)) :
    (∂[Y]f(x)) = ∅ := sorry

end

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {f : E → WithBotTop 𝕜} {x : E}
variable {Y : Type (max u v)} [HasPairing E Y 𝕜]

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)

-- Proof sketch: combine convexity/properness with Theorem 23.3's emptiness consequence on
-- `riDom(f)` to rule out empty subdifferential at `x`.
/-- Theorem 23.4 (2), intrinsic owner form: for a proper convex function, every point of
`ri[𝕜] (dom f)` has a nonempty dual-valued subdifferential. -/
theorem subdifferentialAt_nonempty_of_mem_riDom
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) (hx : x ∈ riDom[𝕜](f)) :
    (∂[Y]f(x)).Nonempty := sorry

-- Proof sketch: clause (2) supplies nonemptiness of `∂ f at x`; Lemma 23.0.1 then gives the
-- support-function formula for the directional derivative, yielding closed/proper/convexity.
/-- Theorem 23.4 (3), intrinsic owner form: for a proper convex function and `x ∈ ri (dom f)`,
the directional-derivative function is closed proper convex. -/
theorem isClosedProperConvex_directionalDerivativeAt_of_mem_riDom
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) (hx : x ∈ riDom[𝕜](f)) :
    IsClosedProperConvex[𝕜] (Function.directionalDerivativeAt f x) := sorry

-- Proof sketch: apply the canonical owner theorem
-- `Function.directionalDerivativeAt_eq_supportFunction_subdifferentialAt` to `∂ f at x`.
/-- Theorem 23.4 (4), intrinsic owner form: for a proper convex function and `x ∈ ri (dom f)`,
the directional derivative at `x` equals the support function of `∂ f at x`. -/
theorem directionalDerivativeAt_eq_supportFunction_subdifferentialAt_of_mem_riDom
    (hf_convex : f.IsConvex 𝕜) (hf_proper : f.IsProper) (hx : x ∈ riDom[𝕜](f)) :
    Function.directionalDerivativeAt f x =
      (δᵛ(· | ∂[Y]f(x)) : E → WithBotTop 𝕜) := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {f : E → WithBotTop ℝ} {x : E}

-- Proof sketch: combine clause (4) with the bounded-support-function characterization and the
-- interior criterion on finite-dimensional spaces.
/-- Theorem 23.4 (5), intrinsic owner form: for a proper convex function on a finite-dimensional
real normed space, `∂[StrongDual ℝ E]f(x)` is nonempty and bounded iff
`x ∈ interior (dom f)`. -/
theorem subdifferentialAt_nonempty_and_bounded_iff_mem_interior_dom
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) :
    ((∂[StrongDual ℝ E]f(x)).Nonempty ∧ IsBounded (∂[StrongDual ℝ E]f(x))) ↔
      x ∈ interior (dom(f)) := sorry

-- Proof sketch: from clause (5), interior points give bounded nonempty subdifferential; combine
-- with clause (4) to show finiteness of the support value in every direction.
/-- Theorem 23.4 (6), intrinsic owner form: if `x ∈ interior (dom f)`, then all directional
derivatives at `x` are finite-valued. -/
theorem directionalDerivativeAt_finite_everywhere_of_mem_interior_dom
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) (hx : x ∈ interior (dom(f))) :
    ∀ y : E, ∃ r : ℝ, Function.directionalDerivativeAt f x y = (r : WithBotTop ℝ) := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {f : E → WithBotTop ℝ} {x : E}

namespace Function

/-! Euclidean bridge view of clause (1) through `Function.subdifferentialAt`. -/

-- Proof sketch: this is the Fréchet-Riesz preimage bridge of the intrinsic emptiness theorem.
/-- Theorem 23.4 (1), Euclidean bridge form: outside `dom(f)`, the vector-valued
subdifferential is empty. -/
theorem subdifferentialAt_eq_empty_of_not_mem_dom
    (hf_proper : f.IsProper) (hx : x ∉ dom(f)) :
    (∂ᵥf(x)) = ∅ := by
  have hroot : (∂[StrongDual ℝ E]f(x) : Set (StrongDual ℝ E)) = ∅ :=
    _root_.subdifferentialAt_eq_empty_of_not_mem_dom (f := f) (x := x) hf_proper hx
  simp [Function.subdifferentialAt, hroot]

end Function

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {f : E → WithBotTop ℝ} {x : E}

namespace Function

local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

/-! Euclidean bridge view of clauses (2)–(6). -/

-- Proof sketch: Euclidean bridge form of the intrinsic nonemptiness clause.
/-- Theorem 23.4 (2), Euclidean bridge form: for a proper convex function, every point of
`ri (dom f)` has a nonempty vector-valued subdifferential. -/
theorem subdifferentialAt_nonempty_of_mem_riDom
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) (hx : x ∈ riDom(f)) :
    (∂ᵥf(x)).Nonempty := sorry

-- Proof sketch: Euclidean bridge form of clause (3).
/-- Theorem 23.4 (3), Euclidean bridge form: for a proper convex function and `x ∈ ri (dom f)`,
the directional-derivative function is closed proper convex. -/
theorem isClosedProperConvex_directionalDerivativeAt_of_mem_riDom
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) (hx : x ∈ riDom(f)) :
    IsClosedProperConvex[ℝ] (directionalDerivativeAt f x) := sorry

-- Proof sketch: Euclidean bridge form of clause (4).
/-- Theorem 23.4 (4), Euclidean bridge form: for a proper convex function and `x ∈ ri (dom f)`,
the directional derivative at `x` equals the support function of `∂ᵥf(x)`. -/
theorem directionalDerivativeAt_eq_supportFunction_subdifferentialAt_of_mem_riDom
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) (hx : x ∈ riDom(f)) :
    directionalDerivativeAt f x =
      (δᵛ(· | ∂ᵥf(x)) : E → WithBotTop ℝ) := sorry

-- Proof sketch: Euclidean bridge form of clause (5).
/-- Theorem 23.4 (5), Euclidean bridge form: for a proper convex function on a finite-dimensional
real inner-product space, `∂ᵥf(x)` is nonempty and bounded iff `x ∈ interior (dom f)`. -/
theorem subdifferentialAt_nonempty_and_bounded_iff_mem_interior_dom
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) :
    ((∂ᵥf(x)).Nonempty ∧ IsBounded (∂ᵥf(x))) ↔ x ∈ interior (dom(f)) := sorry

-- Proof sketch: Euclidean bridge form of clause (6).
/-- Theorem 23.4 (6), Euclidean bridge form: if `x ∈ interior (dom f)`, then every directional
derivative at `x` is finite-valued. -/
theorem directionalDerivativeAt_finite_everywhere_of_mem_interior_dom
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) (hx : x ∈ interior (dom(f))) :
    ∀ y : E, ∃ r : ℝ, directionalDerivativeAt f x y = (r : WithBotTop ℝ) := sorry

end Function

end
