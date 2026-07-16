import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_2_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_2_3
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_1

open Convexity

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

variable {E : Type u} {𝕜 : Type v}
variable [Semiring 𝕜] [Preorder 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.5.4 identifies the already-defined convex hull `conv(g)` with the
  infimum of weighted sums of function values over all finite convex-combination representations
  of `x`.
- `core/canonical`: the owner abstraction already introduced earlier in the chapter is
  `conv(g)`. On the point side, the canonical finite convex-combination owners already present
  upstream are `StdSimplex 𝕜 ι` for the weights, the owner-side finite sum `w.sum`,
  `convexCombination` for the represented point, and the `StdSimplex` owner packaging from
  Definition 2.2.10 / Theorem 2.3.
- `bridge/view`: Theorem 2.3 identifies membership in
  `convexHull 𝕜 {p : E × 𝕜 | g p.1 ≤ p.2}` with finite convex combinations of epigraph points.
  Rewriting the point coordinate through `convexCombination_eq_sum` turns the vertical-fiber
  formula from Text 5.5.1 into the displayed infimum over simplex finite sums.
- Primitive data vs derived API: the primitive input is the function `g`; the finite
  convex-combination value formula is a derived specification of `conv(g)`, while the
  simplex coefficients and the point-side convex-hull certificate are reused upstream owners.

Domain-style sampling used here:
- `Function.convexHull_eq_sInf_verticalHeights`;
- `Finset.mem_convexHull'`;
- `StdSimplex`;
- `StdSimplex.sum`;
- `convexCombination_eq_sum`.
- Ambient minimization: the finite-convex-combination formula only uses the module structure
  already present in `Function.convexHull`, so the canonical ambient owner level is an arbitrary
  `𝕜`-module `E`, not the concrete coordinate model `EuclideanSpace ℝ (Fin n)`. Using the
  stronger affine-space owner `ConvexSpace.convexCombination` here would force
  `[AddCommGroup E]`, so the public point equation stays in the sum form compatible with the
  weaker source-faithful ambient assumptions.
- Layer target: `bridge/view`; this file reuses the owner declarations from Text 5.5.1 and keeps
  only the new convex-combination formula.
-/

-- Proof sketch: start from `Function.convexHull_eq_sInf_verticalHeights` and unfold the intrinsic
-- height owner. By Theorem 2.3,
-- membership of `(x, μ)` in `convexHull 𝕜 {p : E × 𝕜 | g p.1 ≤ p.2}` is equivalent to a finite
-- convex combination of epigraph points with intrinsically finite simplex
-- weights `w : StdSimplex 𝕜 ι` and points `z : ι → E`. Rewriting the point coordinate with
-- `convexCombination_eq_sum` gives the textbook weighted-sum condition.
-- Minimizing the individual heights down to `g i` yields the displayed infimum, and the formula
-- remains meaningful in `WithBotTop 𝕜` even when some summands are `⊥`.

/-- Canonical owner for admissible finite convex-combination values of `g` at `x`. -/
def Function.convexCombinationValues (g : E → WithBotTop 𝕜) (x : E) : Set (WithBotTop 𝕜) :=
  {r : WithBotTop 𝕜 |
    ∃ (ι : Type*) (w : StdSimplex 𝕜 ι) (z : ι → E),
      x = w.sum (fun i a ↦ a • z i) ∧
        r = (by
          classical
          exact w.sum (fun i a ↦ (a : WithBotTop 𝕜) * g (z i)) : WithBotTop 𝕜)}

end

section

variable {E : Type u} {𝕜 : Type v}
variable [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

/-- Text 5.5.4: `conv(g)(x)` is the infimum of the weighted sums `∑ i, λ i * g (x i)` over all
finite convex-combination representations `x = ∑ i, λ i • x i`. -/
theorem Function.convexHull_eq_sInf_convexCombination_values
    (g : E → WithBotTop 𝕜) (x : E) :
    Function.convexHull (𝕜 := 𝕜) g x =
      sInf (Function.convexCombinationValues g x) := sorry

/-- Expanded set-builder view of
`Function.convexHull_eq_sInf_convexCombination_values`. -/
theorem Function.convexHull_eq_sInf_convexCombination_values_set
    (g : E → WithBotTop 𝕜) (x : E) :
    Function.convexHull (𝕜 := 𝕜) g x =
      sInf
        {r : WithBotTop 𝕜 |
          ∃ (ι : Type*) (w : StdSimplex 𝕜 ι) (z : ι → E),
            x = w.sum (fun i a ↦ a • z i) ∧
              r = (by
                classical
                exact w.sum (fun i a ↦ (a : WithBotTop 𝕜) * g (z i)) : WithBotTop 𝕜)} := by
  simpa [Function.convexCombinationValues] using
    Function.convexHull_eq_sInf_convexCombination_values (g := g) x

end
