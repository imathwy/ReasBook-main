import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_4_5
import ConvexAnalysis_Rockafellar_1970.Chap02.Definition_8_9_2
import ConvexAnalysis_Rockafellar_1970.Chap03.Corollary_12_2_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open ConvexERealFunction
open Submodule
open scoped RealInnerProductSpace Rockafellar

local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

local instance : HasPairing E E ℝ := instHasPairingOfHasLinearPairing
local instance : HasPairing E E (WithTopBot ℝ) := instHasPairingWithBotTop

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 13.4 identifies the lineality space of the Fenchel conjugate `f*` with
  the orthogonal complement of the subspace parallel to `aff (dom f)`, gives the dual closed-case
  statement for `dom f*`, and records the corresponding dimension formulas.
- `core/canonical`: the owner abstractions already present in the project are `convexConjugate`,
  `recessionFunction`, `Function.constancySpace`, `Function.lineality`,
  `IsClosedProperConvex[ℝ]`, `AffineSubspace.direction`, `Submodule.orthogonal`, and
  the chapter function-dimension owner `dim(·)`.
- `bridge/view`: Rockafellar's `dom f` and `dom f*` are rendered canonically by the finite-value
  sets `dom(f)` and `dom(convexConjugate f)`.

Domain-style sampling used here:
- `supportFunction_effectiveDomain_eq_recessionFunction_convexConjugate` and
  `supportFunction_effectiveDomain_convexConjugate_eq_recessionFunction` from `Theorem_13_3`;
- `Function.constancySpace` from `Definiton_8_7_0`;
- `Function.lineality` from `Definition_8_9_2`;
- the canonical owner constructions `AffineSubspace.direction` and `Submodule.orthogonal`.

Primitive data vs derived API:
- primitive input: a function `f : E → WithTopBot ℝ`;
- owner hypotheses: `f.IsConvex` and `f.IsProper` for the first clause on the base inner-product
  layer, and `FiniteDimensional ℝ E` together with those hypotheses or `f.IsClosedProperConvex`
  for the later numerical and dual closed-case clauses;
- derived API: the orthogonal-complement identifications and the two numerical formulas expressed
  through `lineality` and `dim(·)`.

Layer target: this item stays `source-facing`, stated directly in the canonical conjugation,
lineality, affine-hull, and orthogonality language without introducing a surrogate wrapper.
-/

variable (f : E → WithTopBot ℝ)

-- Proof sketch: by Theorem 13.3, `recessionFunction (convexConjugate f)` is the support function
-- of `dom f`. A vector lies in `Function.constancySpace` of that support function exactly when the
-- corresponding linear functional is both bounded above and bounded below on `dom f`, equivalently
-- when it vanishes on the direction subspace of `affineSpan ℝ (dom f)`.
/-- Theorem 13.4: for a proper convex function `f` on a real inner-product space, the lineality
space of the Fenchel conjugate `f*` is the orthogonal complement of the subspace parallel to the
affine hull of its effective domain `dom f`. The canonical owner statement only uses the real
inner-product-space structure, so it is formulated at that level and specializes in particular to
`R^n`. -/
theorem constancySpace_convexConjugate_eq_orthogonal_effectiveDomain_direction
    (hf_convex : f.IsConvex ℝ)
    (hf_proper : f.IsProper) :
    Function.constancySpace (((f⋆ : E → WithTopBot ℝ))₀⁺) =
      ((affineSpan ℝ dom(f)).directionᗮ : Set E) := sorry

section

variable [FiniteDimensional ℝ E]

-- Proof sketch: apply the first orthogonal-complement clause to `convexConjugate f`, then use the
-- closed proper convex biconjugacy input to identify `convexConjugate (convexConjugate f)` with
-- `f`. The orthogonal complement of the lineality space is rendered canonically as the
-- orthogonal complement of the direction subspace of its affine hull.
/-- For a closed proper convex function, the subspace parallel to the affine hull of `dom f*`
coincides with the orthogonal complement of the lineality space of `f`. -/
theorem effectiveDomain_convexConjugate_direction_eq_orthogonal_constancySpace_direction
    (hf : IsClosedProperConvex[ℝ] f) :
    (affineSpan ℝ dom((f⋆ : E → WithTopBot ℝ))).direction =
      (((affineSpan ℝ (Function.constancySpace (f0⁺))).direction)ᗮ : Submodule ℝ E) := sorry

-- Proof sketch: combine the first orthogonal-complement identification with the definition of
-- `Function.lineality` as the affine dimension of the lineality space, then use the
-- finite-dimensional identity for the orthogonal complement of a direction subspace.
/-- The lineality of the Fenchel conjugate equals the ambient dimension minus the affine dimension
of the effective domain of the original function, written canonically as `dim(f)`. -/
theorem lineality_convexConjugate_eq_ambientDim_sub_effectiveDomain_affineDim
    (hf_convex : f.IsConvex ℝ)
    (hf_proper : f.IsProper) :
    lineality[ℝ]((f⋆ : E → WithTopBot ℝ)) = (Module.finrank ℝ E : ℤ) - dim(f) := sorry

end

end

section

variable {E : Type*}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
variable [FiniteDimensional ℝ E]
variable [HasLinearPairing E E ℝ] [HasContinuousPairing E E ℝ]

open ConvexERealFunction
open scoped Rockafellar

local notation "IsClosedProperConvex[ℝ]" => Function.IsClosedProperConvex (𝕜 := ℝ)

variable (f : E → WithTopBot ℝ)

-- Proof sketch: identify `dim(f⋆)` with ambient dimension minus the affine dimension loss coming
-- from lineality, using the Chapter 13.4 orthogonality/dimension bridge in pairing form.
/-- For a closed proper convex function on a finite-dimensional real topological vector space
equipped with a continuous linear self-pairing, the affine dimension of the effective domain of
`f*` equals the ambient dimension minus the lineality of `f`, written canonically as `dim(f⋆)`. -/
theorem effectiveDomain_convexConjugate_affineDim_eq_ambientDim_sub_lineality
    (hf : IsClosedProperConvex[ℝ] f) :
    dim((f⋆ : E → WithTopBot ℝ)) = (Module.finrank ℝ E : ℤ) - lineality[ℝ](f) := sorry

end
