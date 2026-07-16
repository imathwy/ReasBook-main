import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap05.Theorem_23_5

-- Declarations for this item were appended by the statement pipeline.

noncomputable section

open scoped RealInnerProductSpace Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Corollary 23.5.2 says that if a proper convex function is subdifferentiable at
  `x`, then `cl(f)` agrees with `f` at `x`, and the subdifferential at `x` is unchanged by
  passing from `f` to `cl(f)`.
- `core/canonical`: the relevant project owners are `Function.subdifferentialAt`,
  `Function.IsConvex`, `Function.IsProper`, and Rockafellar's closure notation `cl(·)`.
- `bridge/view`: the source phrase “subdifferentiable at `x`” is rendered directly by
  `(subdifferentialAt f x).Nonempty`, so no auxiliary predicate or wrapper is introduced.

Domain-style sampling used here:
- `Function.subdifferentialAt` from `Chap05/Definition_23_0_6`;
- the closure-normalized TFAE theorem
  `Function.subdifferentialAt_tfae_isMaxOn_fenchelYoung_and_`
  `conjugate_subdifferentialAt_of_closure_eq` from `Chap05/Theorem_23_5`;
- Rockafellar's closure notation `cl(·)` already used throughout the Chapter 23 development.

Primitive data vs derived API:
- primitive inputs: the convexity and properness hypotheses on `f`, the base point `x`, and the
  nonemptiness of `subdifferentialAt f x`;
- derived API: the pointwise closure normalization `cl(f) x = f x`, the pointwise membership
  equivalence for `subdifferentialAt (cl(f)) x`, and the resulting set equality.

Layer target: `source-facing`, stated directly on the canonical Euclidean subdifferential owner.
-/

variable {f : E → EReal} {x : E}

-- Proof sketch: choose `xStar ∈ subdifferentialAt f x`. Theorem 23.5 places that membership in
-- the same Fenchel-Young equivalence class as equality at `(x, xStar)`. Combining the resulting
-- equality with the general inequalities `f x ≥ cl(f) x = f⋆⋆ x` forces the value normalization
-- `cl(f) x = f x`. The closure-normalized form of Theorem 23.5 then identifies the original and
-- closure-side subgradient clauses for every `xStar`, yielding equality of the two
-- subdifferentials.
/-- Corollary 23.5.2: if `f` is a proper convex function and is subdifferentiable at `x`, then
`cl(f)` agrees with `f` at `x`, and the subdifferential at `x` is unchanged by passing from `f`
to `cl(f)`. -/
theorem lowerSemicontinuousHull_apply_eq_and_subdifferentialAt_eq_of_subdifferentialAt_nonempty
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    (hsub : (subdifferentialAt f x).Nonempty) :
    cl(f) x = f x ∧ subdifferentialAt (cl(f)) x = subdifferentialAt f x := sorry

-- Proof sketch: use the first clause of the corollary above, obtained from a witness
-- `xStar ∈ subdifferentialAt f x` and the Fenchel-Young equality criterion in Theorem 23.5.
/-- At any point where a proper convex function has a nonempty Chapter 23 subdifferential, its
lower-semicontinuous hull has the same value. -/
theorem lowerSemicontinuousHull_apply_eq_of_subdifferentialAt_nonempty
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    (hsub : (subdifferentialAt f x).Nonempty) :
    cl(f) x = f x :=
  (lowerSemicontinuousHull_apply_eq_and_subdifferentialAt_eq_of_subdifferentialAt_nonempty
    hf_convex hf_proper hsub).1

-- Proof sketch: the preceding set-equality clause already lives on the canonical owner
-- `subdifferentialAt`, so the owner-friendly pointwise form is obtained by rewriting membership
-- across that equality.
/-- At a point where `subdifferentialAt f x` is nonempty, passing to `cl(f)` preserves the Chapter
23 subgradient condition pointwise. -/
theorem mem_subdifferentialAt_lowerSemicontinuousHull_iff_of_subdifferentialAt_nonempty
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    (hsub : (subdifferentialAt f x).Nonempty)
    {xStar : E} :
    xStar ∈ subdifferentialAt (cl(f)) x ↔ xStar ∈ subdifferentialAt f x := by
  rw [(lowerSemicontinuousHull_apply_eq_and_subdifferentialAt_eq_of_subdifferentialAt_nonempty
    hf_convex hf_proper hsub).2]

-- Proof sketch: first obtain `cl(f) x = f x` from the preceding companion theorem. Then apply the
-- closure-normalized equivalence theorem
-- `subdifferentialAt_tfae_isMaxOn_fenchelYoung_and_conjugate_subdifferentialAt_of_closure_eq`
-- from Theorem 23.5 to identify the original and closure-side subgradient clauses pointwise.
/-- Passing from a proper convex function to its lower-semicontinuous hull does not change the
Chapter 23 subdifferential at a point where the original subdifferential is nonempty. -/
theorem subdifferentialAt_lowerSemicontinuousHull_eq_of_subdifferentialAt_nonempty
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper)
    (hsub : (subdifferentialAt f x).Nonempty) :
    subdifferentialAt (cl(f)) x = subdifferentialAt f x :=
  (lowerSemicontinuousHull_apply_eq_and_subdifferentialAt_eq_of_subdifferentialAt_nonempty
    hf_convex hf_proper hsub).2

end Function

end
