import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Theorem_12_2
import ConvexAnalysis_Rockafellar_1970.Chap05.Definition_23_0_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped RealInnerProductSpace Rockafellar

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {f : E → EReal} {x : E} {xStar : StrongDual ℝ E}

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 23.5 is the Fenchel-Young equality criterion for a proper convex
  function, stated in terms of subgradients, attainment of the primal and dual conjugate suprema,
  and equality in the Fenchel-Young inequality.
- `core/canonical`: the intrinsic owner for the unstarred four-clause theorem is the dual-valued
  `_root_.subdifferentialAt`, together with the Fenchel conjugate `f⋆`, the chapter pairing
  notation `⟪·, ·⟫ₚ`, and `List.TFAE`.
- `bridge/view`: the Euclidean vector-valued subdifferential `Function.subdifferentialAt` and the
  starred dual-side clause `x ∈ subdifferentialAt (f⋆) xStar` are Fréchet-Riesz bridge surfaces on
  top of that intrinsic owner, so they belong only to the second theorem below.

Domain-style sampling used here:
- `_root_.subdifferentialAt` and the Euclidean bridge `Function.subdifferentialAt` from
  `Chap05/Definition_23_0_6`;
- `convexConjugate` / `f⋆` from `Chap03/Defn_12_2`;
- `Function.IsConvex.biconjugate_eq_lowerSemicontinuousHull` and
  `Function.IsClosedProperConvex.biconjugate_eq` from `Chap03/Theorem_12_2`;
- `List.TFAE` as the canonical owner for “the following conditions are mutually equivalent”.

Primitive data vs derived API:
- primitive inputs: the proper convex function `f`, the primal point `x`, and the dual point
  `xStar`;
- primitive owner surface: `xStar ∈ subdifferentialAt f x` and the Fenchel conjugate evaluations
  `f x`, `f⋆ xStar`;
- derived surface: the attainment clauses, the Fenchel-Young inequality/equality clauses, and in
  the Euclidean bridge theorem below the extra dual-side and closure-side subgradient clauses.

Layer target:
- the first theorem is `core/canonical`: it keeps only the intrinsic unstarred Fenchel-Young
  equivalence and removes the unnecessary Euclidean self-duality assumptions;
- the second theorem is `bridge/view`: it adds back the vector-valued dual-side and closure-side
  clauses under the explicit Euclidean self-duality hypothesis `cl(f) x = f x`.
-/

-- Proof sketch: clause `(a)` is the supporting-hyperplane inequality at `x`, so it rewrites
-- directly to the statement that `z ↦ ⟪z, xStar⟫ₚ - f z` is maximized at `z = x`, giving
-- `(a) ↔ (b)`.
-- The defining supremum formula for `f⋆ xStar` identifies the maximum value in `(b)` with
-- `f⋆ xStar`, so `(b)` is equivalent to the reverse Fenchel-Young inequality `(c)`. The general
-- Fenchel-Young inequality always gives the opposite inequality, hence `(c)` is equivalent to the
-- equality clause `(d)`.
/-- Theorem 23.5, intrinsic owner form: for a proper convex function, the following are
equivalent: `xStar` is a subgradient of `f` at `x`, the Fenchel supremum
`z ↦ ⟪z, xStar⟫ₚ - f z` is attained at `x`, and the Fenchel-Young inequality at `(x, xStar)` holds
with inequality or equality. -/
theorem subdifferentialAt_tfae_isMaxOn_fenchelYoung
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) :
    List.TFAE
      [ xStar ∈ subdifferentialAt f x,
        IsMaxOn (fun z : E ↦ ⟪z, xStar⟫ₚ - f z) Set.univ x,
        f x + f⋆ xStar ≤ ⟪x, xStar⟫ₚ,
        f x + f⋆ xStar = ⟪x, xStar⟫ₚ ] := sorry

end

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

namespace Function

variable {f : E → EReal} {x xStar : E}

-- Proof sketch: combine the four-way equivalence above for `f` with the same argument applied to
-- the conjugate `f⋆`. Biconjugacy identifies `f⋆⋆` with `cl(f)`, and the normalization
-- hypothesis `cl(f) x = f x` turns equality in the Fenchel-Young formula for `(f, x, xStar)` into
-- the same equality for `(f⋆, xStar, x)` and for `cl(f)` at `x`. This yields a single seven-way
-- TFAE covering the unstarred, starred, and closure-side subgradient clauses.
/-- Theorem 23.5, Euclidean bridge form: under the pointwise closure normalization
`cl(f) x = f x`, the dual-side subgradient and attainment conditions for `f⋆`, together with the
subgradient condition for `cl(f)`, join the same Fenchel-Young equivalence class as the intrinsic
four clauses from Theorem 23.5. -/
theorem subdifferentialAt_tfae_isMaxOn_fenchelYoung_and_conjugate_subdifferentialAt_of_closure_eq
    (hf_convex : f.IsConvex ℝ) (hf_proper : f.IsProper) (hclx : cl(f) x = f x) :
    List.TFAE
      [ xStar ∈ subdifferentialAt f x,
        IsMaxOn (fun z : E ↦ ⟪z, xStar⟫ₚ - f z) Set.univ x,
        f x + f⋆ xStar ≤ ⟪x, xStar⟫ₚ,
        f x + f⋆ xStar = ⟪x, xStar⟫ₚ,
        x ∈ subdifferentialAt (f⋆) xStar,
        IsMaxOn (fun zStar : E ↦ ⟪x, zStar⟫ₚ - f⋆ zStar) Set.univ xStar,
        xStar ∈ subdifferentialAt (cl(f)) x ] := sorry

end Function

end
