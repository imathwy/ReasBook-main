import Mathlib.Tactic.Recall
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_36
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_15_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ConvexFunctionPolar Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.39 states that for a nonnegative closed convex function `f` with
  `f 0 = 0`, the polar `fᵒ` is the obverse of the conjugate `f*`, and then records the resulting
  reciprocal-level sublevel-set identity.
- `core/canonical`: the owner declarations already present in the Chapter 15 API are
  the Chapter 15 polar owner `fᵒ`, `obverse`, `f⋆`, and
  `Function.IsNonnegativeClosedConvexZero`, together with the owner exchange theorem
  `obverse_convex_function_polar_eq_convexConjugate_of_nonnegative_closed_convex_zero`.
- `bridge/view`: the main theorem below is the symmetric source-facing restatement of that owner
  exchange theorem, and the second sentence reuses the exact reciprocal-sublevel theorem from the
  preceding item instead of restating a parallel declaration.

Domain-style sampling used here:
- `Function.IsNonnegativeClosedConvexZero` as the owner hypothesis package for the standing
  nonnegative closed convex zero-normalized assumptions;
- `obverse_convex_function_polar_eq_convexConjugate_of_nonnegative_closed_convex_zero` from the
  Section 15 owner API;
- the exact source-faithful reciprocal-sublevel theorem already present in `Text_15_0_36`.

Primitive data vs derived API:
- primitive input: a function `f : E → EReal` with owner hypothesis
  `f.IsNonnegativeClosedConvexZero`;
- derived API: the source-facing symmetric obverse identity and the recalled reciprocal-sublevel
  equality.

Layer target: the theorem is a thin `bridge/view` from the Section 15 owner theorem to the
source-facing wording of Text 15.0.39, while the sublevel-set identity is reused by direct recall.
-/

-- Proof sketch: Theorem 15.5 identifies `obverse fᵒ` with
-- `f⋆`, and the same theorem makes `obverse` involutive on the standing Chapter 15
-- class. Rewriting `fᵒ` as the double obverse of itself then gives the
-- symmetric source wording exactly.
/-- Text 15.0.39: if `f : E → [0, +∞]` is closed convex and satisfies `f 0 = 0` on a
finite-dimensional real inner-product space, then its polar `fᵒ` is the obverse of its Fenchel
conjugate `f*`, i.e. `fᵒ = obverse f⋆`. Specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers
the source statement on `R^n`. -/
theorem convex_function_polar_eq_obverse_convexConjugate_of_nonnegative_closed_convex_zero
    (f : E → EReal) (hf : f.IsNonnegativeClosedConvexZero) :
    fᵒ = obverse f⋆ := by
  letI : f.IsNonnegativeClosedConvexZero := hf
  refine (obverse_obverse_eq_of_nonnegative_closed_convex_zero
    fᵒ inferInstance).symm.trans ?_
  exact
    congrArg obverse
      (obverse_convex_function_polar_eq_convexConjugate_of_nonnegative_closed_convex_zero
        f hf)

/- The reciprocal sublevel-set identity for the polar and Fenchel conjugate of a nonnegative
closed convex zero-normalized function is already available, with the exact statement shape used
here, from the preceding item. -/
recall polar_sublevelSet_eq_inv_smul_conjugate_sublevelSet_of_nonnegative_closed_convex_zero

end
