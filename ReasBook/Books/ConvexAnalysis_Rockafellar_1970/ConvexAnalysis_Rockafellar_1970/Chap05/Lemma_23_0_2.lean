import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_8
import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_4_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_1_3
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_13_2_3
import ConvexAnalysis_Rockafellar_1970.Chap05.Lemma_23_0_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v

section

open scoped Rockafellar
open Filter

variable {𝕜 : Type v}
variable [Field 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [TopologicalSpace 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [T2Space (WithTopBot 𝕜)]
variable [NeBot (𝓝[>] (0 : 𝕜))]
variable {E : Type u} [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable {Y : Type (max u v)} [AddCommMonoid Y] [Module 𝕜 Y] [HasLinearPairing E Y 𝕜]

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Lemma 23.0.2 packages the direction-side regularity of
  `y ↦ directionalDerivativeAt f x y` (convexity, positive homogeneity, and subadditivity) at a
  fixed base point `x` of a convex function `f`.
- `core/canonical`: the owner abstractions are already upstream:
  `Function.directionalDerivativeAt` from `Lemma_23_0_1`,
  `Function.IsConvex` from `Theorem_4_2`, and
  `Function.PositivelyHomogeneous` from `Definition_4_8`.
- `bridge/view`: the source wording “`f'(x; ·)` is sublinear” is represented by the canonical
  owner predicates plus the explicit two-point inequality
  `directionalDerivativeAt f x (d₁ + d₂) ≤ ...`.

Primitive data vs derived API:
- primitive data: a convex function `f`, a finite base point `x ∈ dom(f)` with `f x ≠ ⊥`, and a
  nonempty subdifferential `∂[Y]f(x)`;
- primitive owner reused from upstream: `directionalDerivativeAt f x`;
- derived API: convexity, positive homogeneity, and subadditivity of that owner in the direction
  variable.

Layer target: `source-facing` on the canonical chapter owner surface.

Ambient-assumption minimization:
- this file keeps exactly the additive-topological module layer needed by the upstream owners
  `directionalDerivativeAt` and `∂[Y]f(x)`, and no norm, inner-product, completeness, or
  finite-dimensional assumptions are exposed.

Codomain normalization:
- theorem surfaces use the chapter canonical codomain layer `WithTopBot 𝕜`,
  and now consume that codomain directly from the upstream owner in `Lemma_23_0_1` with no local
  concrete-codomain scalar-action glue.
- the support-function scaling bridge is consumed from the generic pairing owner theorem
  `supportFunction_smul_left_of_nonempty_apply`, and the support-function subadditivity bridge is
  consumed from `supportFunction_add_le`, both at the same ordered-field pairing layer.
-/

-- Proof sketch: identify `directionalDerivativeAt f x` with the support-function owner
-- `δᵛ(· | ∂[Y]f(x))` from Lemma 23.0.1, then reuse the canonical owner theorem
-- `Function.isConvex_supportFunction`.
/-- Lemma 23.0.2, convexity form: for convex `f` finite at `x`, the map
`d ↦ directionalDerivativeAt f x d` is convex. -/
theorem isConvex_directionalDerivativeAt
    {f : E → WithTopBot 𝕜} {x : E}
    (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (hsub : (∂[Y]f(x)).Nonempty) :
    (directionalDerivativeAt f x).IsConvex 𝕜 := by
  have hEq := directionalDerivativeAt_eq_supportFunction_subdifferentialAt_fun
    hf_convex hx hx_bot hsub
  simpa [hEq] using isConvex_supportFunction (∂[Y]f(x))

-- Proof sketch: the same direction-side owner is positively homogeneous in the direction
-- variable because it is identified with the support-function owner.
/-- Lemma 23.0.2, homogeneity form: for convex `f` finite at `x`,
`d ↦ directionalDerivativeAt f x d` is positively homogeneous. -/
theorem positivelyHomogeneous_directionalDerivativeAt
    {f : E → WithTopBot 𝕜} {x : E}
    (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (hsub : (∂[Y]f(x)).Nonempty) :
    (directionalDerivativeAt f x).PositivelyHomogeneous 𝕜 := by
  have hsupport :
      (δᵛ(· | ∂[Y]f(x)) : E → WithTopBot 𝕜).PositivelyHomogeneous 𝕜 := by
    intro c d
    simpa [smul_eq_mul] using
      supportFunction_smul_left_of_nonempty_apply
        (∂[Y]f(x)) hsub (le_of_lt c.2) d
  have hEq := directionalDerivativeAt_eq_supportFunction_subdifferentialAt_fun
    hf_convex hx hx_bot hsub
  simpa [hEq] using hsupport

/-- Positive-scalar owner form of
`positivelyHomogeneous_directionalDerivativeAt`. -/
theorem directionalDerivativeAt_smul_pos
    {f : E → WithTopBot 𝕜} {x : E}
    (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (hsub : (∂[Y]f(x)).Nonempty)
    (c : PositiveScalars 𝕜) (d : E) :
    directionalDerivativeAt f x (c • d) = c • directionalDerivativeAt f x d := by
  exact
    (positivelyHomogeneous_directionalDerivativeAt hf_convex hx hx_bot hsub).map_smul_pos c d

/-- Positive-scalar evaluation form of
`positivelyHomogeneous_directionalDerivativeAt`. -/
theorem directionalDerivativeAt_smul
    {f : E → WithTopBot 𝕜} {x : E}
    (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (hsub : (∂[Y]f(x)).Nonempty)
    {c : 𝕜} (hc : 0 < c) (d : E) :
    directionalDerivativeAt f x (c • d) = c • directionalDerivativeAt f x d := by
  simpa using directionalDerivativeAt_smul_pos hf_convex hx hx_bot hsub ⟨c, hc⟩ d

-- Proof sketch: rewrite the directional derivative by Lemma 23.0.1 as the support-function owner
-- of the subdifferential and apply the canonical support-function subadditivity theorem from
-- Text 13.2.3.
/-- Lemma 23.0.2, subadditivity form: for convex `f` finite at `x`, the directional-derivative
map in the direction variable satisfies
`directionalDerivativeAt f x (d₁ + d₂) ≤ directionalDerivativeAt f x d₁ +
  directionalDerivativeAt f x d₂`.
-/
theorem directionalDerivativeAt_add_le
    {f : E → WithTopBot 𝕜} {x : E}
    (hf_convex : f.IsConvex 𝕜) (hx : x ∈ dom(f)) (hx_bot : f x ≠ ⊥)
    (hsub : (∂[Y]f(x)).Nonempty)
    (d₁ d₂ : E) :
    directionalDerivativeAt f x (d₁ + d₂) ≤
      directionalDerivativeAt f x d₁ + directionalDerivativeAt f x d₂ := by
  have hEq := directionalDerivativeAt_eq_supportFunction_subdifferentialAt_fun
    hf_convex hx hx_bot hsub
  simpa [hEq] using supportFunction_add_le (∂[Y]f(x)) d₁ d₂

end Function

end
