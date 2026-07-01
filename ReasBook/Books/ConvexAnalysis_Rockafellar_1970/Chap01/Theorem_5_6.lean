import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_2_10
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u v w

section

variable {E : Type u} {𝕜 : Type w}
variable [Semiring 𝕜] [ConditionallyCompleteLattice 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E] {I : Sort v}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 5.6 is a formula for the convex hull of a *family* of proper convex
  functions: at `x`, take the infimum over finite convex-combination representations
  `x = ∑ λ_j x_j` and finite choices of family members `i_j`, of the values
  `∑ λ_j f_{i_j}(x_j)`.
- `core/canonical`: the owner below is a family-indexed convex-hull value function.  It is not the
  single-function owner applied to the pointwise infimum `⨅ i, f i`; that loses the source's
  finite choice of an index for each point in the combination.
- `bridge/view`: the theorem is kept as an explicit set of admissible finite weighted values.
-/

namespace Function

/-- Helper for Theorem 5.6: admissible weighted sums obtained from finite convex combinations of
points, where each point may use a separately chosen member of the family. -/
private def familyConvexCombinationValues
    (f : I → E → WithTopBot 𝕜) (x : E) : Set (WithTopBot 𝕜) :=
  {r : WithTopBot 𝕜 |
    ∃ (ι : Type max u w) (idx : ι → I) (w : StdSimplex 𝕜 ι) (z : ι → E) (μ : ι → 𝕜),
      x = w.sum (fun j a ↦ a • z j) ∧
        (∀ j, f (idx j) (z j) ≤ (μ j : WithTopBot 𝕜)) ∧
        r = ((w.sum (fun j a ↦ a * μ j) : 𝕜) : WithTopBot 𝕜)}

/-- Helper for Theorem 5.6: the family convex-hull value at `x` is the infimum of the finite
family-indexed convex-combination values above `x`. -/
private def familyConvexHullValue (f : I → E → WithTopBot 𝕜) : E → WithTopBot 𝕜 :=
  fun x ↦ sInf (familyConvexCombinationValues f x)

local notation:max "convFamily(" f ")" => familyConvexHullValue f

/-- Theorem 5.6, pointwise owner form: the convex hull of a family is the infimum over all finite
family-indexed convex-combination representations of the point. -/
theorem convexHull_family_apply_eq_sInf_convexCombination_values
    (f : I → E → WithTopBot 𝕜) (x : E) :
    convFamily(f) x = sInf (familyConvexCombinationValues f x) := by
  simp [familyConvexHullValue]

/-- Theorem 5.6, function owner form. -/
theorem convexHull_family_eq_sInf_convexCombination_values
    (f : I → E → WithTopBot 𝕜) :
    convFamily(f) = sInf ∘ familyConvexCombinationValues f := by
  funext x
  simp [familyConvexHullValue, Function.comp_apply]

/-- Set-builder view of the pointwise Theorem 5.6 formula. -/
theorem convexHull_family_apply_eq_sInf_convexCombination_values_set
    (f : I → E → WithTopBot 𝕜) (x : E) :
    convFamily(f) x =
      sInf {r : WithTopBot 𝕜 | r ∈ familyConvexCombinationValues f x} := by
  simp [familyConvexHullValue]

end Function

end
