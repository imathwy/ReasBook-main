import ConvexAnalysis_Rockafellar_1970.Chap01.Theorem_5_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Pointwise
open Function

variable {E : Type*}
variable {𝕜 : Type*}

local notation "𝕜≥0" => Set.Ici (0 : 𝕜)

section

variable {α : Type*}

variable [Zero 𝕜] [Preorder 𝕜]
variable [ConditionallyCompleteLattice α]
variable [SMul 𝕜 E] [SMul 𝕜 α]

namespace Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 5.4.2 defines the right scalar multiple `f λ` by applying Theorem 5.3 to
  the scaled epigraph `λ (epi f)`.
- `core/canonical`: the owner abstraction for this construction is the vertical-infimum function
  `Function.verticalInfimum` on subsets of `E × α`, with the chapter epigraph owner
  `epi f` and convexity recorded by `Function.IsConvex`.
- `bridge/view`: the textbook set `λ (epi f)` is represented directly by the canonical set scalar
  multiple `(lam : 𝕜) • epi f` of the chapter epigraph owner.
- Primitive data vs derived API: the source-facing operation `rightScalarMul` is the bridge
  to the owner `Function.verticalInfimum`; its `sInf` formula and convexity preservation are
  derived API.

Domain-style sampling used here:
- `Function.verticalInfimum`;
- `Function.verticalInfimum_eq_sInf`;
- `Function.IsConvex`;
- `Function.IsConvex.convex_epigraph`;
- `Function.isConvex_verticalInfimum`;
- `sInf` on `WithBotTop α`;
- `Convex.smul`.

The source assumes `f` is convex, but the construction itself depends only on `f` and the
nonnegative scalar `λ`, so the convexity assumption is kept as a derived theorem rather than a
binder in the definition.
- Ambient minimization: the source-facing owner `rightScalarMul` and its `sInf` formula use only
  the ordered scalar layer for nonnegative parameters, together with the ambient `𝕜`-actions
  needed to scale epigraph points in `E × α`, so they are stated for an arbitrary `𝕜`-smul base
  and codomain. The stronger additive and module assumptions appear only in the derived convexity
  theorem.
- Layer target: `source-facing`; `rightScalarMul` remains the public owner for Text 5.4.2, and
  its bridge/view layer is kept as the direct canonical scaled-epigraph expression `(lam : 𝕜) •
  epi f` reused by the immediate downstream scalar-rescaling formulas.
-/

/-- Text 5.4.2: for a nonnegative scalar `λ`, the right scalar multiple `f λ` is the function
obtained by applying Theorem 5.3 to the scaled scalar epigraph `λ (epi f)`. -/
abbrev rightScalarMul (lam : 𝕜≥0) (f : E → WithBotTop α) : E → WithBotTop α :=
  verticalInfimum ((lam : 𝕜) • epi f)

local infixr:73 " •ʳ " => rightScalarMul

-- Proof sketch: `rightScalarMul` is `Function.verticalInfimum` applied to the scaled
-- epigraph, so this is exactly
-- `Function.verticalInfimum_eq_sInf_verticalHeights` for that set.
/-- The value of `lam •ʳ f` at `x` is the infimum of the intrinsic scalar-height owner
`verticalHeights` for the scaled epigraph `λ (epi f)` above `x`. -/
theorem rightScalarMul_eq_sInf (lam : 𝕜≥0) (f : E → WithBotTop α) (x : E) :
    (lam •ʳ f) x =
    sInf (verticalHeights ((lam : 𝕜) • epi f) x) := by
  simpa [rightScalarMul] using
    verticalInfimum_eq_sInf_verticalHeights ((lam : 𝕜) • epi f) x

end Function

end

infixr:73 " •ʳ " => Function.rightScalarMul

section

variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid E] [Module 𝕜 E]

namespace Function.IsConvex

-- Proof sketch: rewrite `hf` as convexity of the scalar epigraph of `f`. Scalar multiplication by
-- the nonnegative scalar `(lam : 𝕜)` preserves convexity of that subset of `E × 𝕜`. Apply Theorem
-- 5.3 to the scaled epigraph and unfold `rightScalarMul`.
/-- The right scalar multiple of a convex function is again convex. -/
theorem rightScalarMul {f : E → WithBotTop 𝕜} (hf : f.IsConvex 𝕜) (lam : 𝕜≥0) :
    (lam •ʳ f).IsConvex 𝕜 := by
  have hF : Convex 𝕜 ((lam : 𝕜) • epi f) := by
    simpa [epi_univ_eq_setOf_le] using hf.convex_epigraph.smul (lam : 𝕜)
  simpa [Function.rightScalarMul] using Function.isConvex_verticalInfimum hF

end Function.IsConvex

end
