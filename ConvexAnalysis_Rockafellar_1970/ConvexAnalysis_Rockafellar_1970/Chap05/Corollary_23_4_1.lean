import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_4
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_23_1
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_23_4

-- Declarations for this item will be appended below by the statement pipeline.

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
