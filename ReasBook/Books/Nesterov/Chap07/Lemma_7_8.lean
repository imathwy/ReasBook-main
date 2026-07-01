import Mathlib
import Nesterov.Chap03.Definition_3_9
import Nesterov.Chap07.Definition_7_29
import Nesterov.Chap07.Definition_7_35

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open EuclideanSpace (nonnegativeOrthant)
open Matrix
open scoped EllipsoidNotation PositiveDefMatrixNorm SupportFunction SymmetricBox

variable {m n : ℕ}

local notation "Eₙ" => EuclideanSpace ℝ (Fin n)
local notation "Matₙ" => Matrix (Fin n) (Fin n) ℝ

/- Lemma 7.8 lies in Chapter 7's orthant-box / support-function / diagonal-ellipsoid domain.

Sampled owner-style declarations:
- `ξ[Q]` and `supportFunction_convexHull_eq` in `Chap03/Definition_3_9`, the chapter owner for
  support functions;
- `supportFunction_range_toReal_eq_sSup_inner` in `Chap07/Lemma_7_1`, the finite-range support
  function bridge already available upstream for families `a : Fin m → Eₙ`;
- `signSymmetricConvexHull` in `Chap07/Definition_7_35`, the source-facing Chapter 7 owner for
  the box hull `convexHull ℝ (⋃ i, B(a i))`;
- `EuclideanSpace.nonnegativeOrthant` and `EuclideanSpace.mem_nonnegativeOrthant_iff` in
  `Chap01/Definition_1_10_2`, the canonical orthant owner;
- `IsEllipsoidalRounding` in `Chap07/Definition_7_29`, the centered-rounding owner packaging the
  unit and outer ellipsoid containments together with positive definiteness.

Best owner abstraction:
- source-facing: the box hull owner `signSymmetricConvexHull a`;
- core/canonical: `ξ[Q]`, `nonnegativeOrthant`, `IsEllipsoidalRounding`, and the
  positive-definite norm owner `‖x‖[G]`;
- bridge/view: the orthant-restricted identification of `ξ[signSymmetricConvexHull a]` with the
  finite-range support function `ξ[Set.range a]`.

Primitive data:
- a family `a : Fin m → Eₙ`.

Derived API:
- the orthant bridge from the source-facing box-hull owner to the canonical finite-range support
  function;
- the centered rounding datum `IsEllipsoidalRounding (signSymmetricConvexHull a) γ D`;
- the support-function sandwich theorem below, derived from that owner.

Source/core/bridge triage:
- source-facing: the two theorems below about `signSymmetricConvexHull a`;
- core/canonical: `IsEllipsoidalRounding`;
- bridge/view: passing from `hrounding : IsEllipsoidalRounding (signSymmetricConvexHull a) γ D`
  to the inner/outer containments with `hrounding.unit_ellipsoid_subset` and
  `hrounding.subset_outer_ellipsoid`.

This refinement deletes the raw-set duplication in the public theorem surface. The box hull is now
named by its Chapter 7 owner `signSymmetricConvexHull`, and the main sandwich theorem is stated
through the centered-rounding owner `IsEllipsoidalRounding` instead of keeping its fields as
parallel hypotheses.
-/

/-- On the nonnegative orthant, the support function of the symmetric box `B(a)` with nonnegative
generator `a` is the linear form `x ↦ ⟪a, x⟫`. -/
theorem supportFunction_symmetricBox_toReal_eq_inner_of_mem_nonnegativeOrthant
    {a x : Eₙ} (ha : a ∈ nonnegativeOrthant n) (hx : x ∈ nonnegativeOrthant n) :
    (ξ[(B(a))] x).toReal = inner ℝ a x := sorry

/-- On the nonnegative orthant, the support function of the Chapter 7 box-hull owner
`signSymmetricConvexHull a` agrees with the canonical finite-range support function
`ξ[Set.range a]`. -/
theorem supportFunction_signSymmetricConvexHull_eq_range_on_nonnegativeOrthant
    (a : Fin m → Eₙ) (ha_nonneg : ∀ i : Fin m, a i ∈ nonnegativeOrthant n)
    {x : Eₙ} (hx : x ∈ nonnegativeOrthant n) :
    (ξ[signSymmetricConvexHull a] x).toReal = (ξ[Set.range a] x).toReal := sorry

-- Proof sketch: on the nonnegative orthant, the support function of each coordinate box
-- `coordinateBox (a i)` is `⟪a_i, x⟫` because `a_i` has nonnegative coordinates. Hence the support
-- function of `signSymmetricConvexHull a` agrees with the canonical finite-range owner
-- `ξ[Set.range a]`. Monotonicity of support functions under the inclusions
-- `W[1](D) ⊆ signSymmetricConvexHull a ⊆ W[γ √n](D)` supplied by
-- `hrounding : IsEllipsoidalRounding (signSymmetricConvexHull a) γ D` then give the lower and
-- upper bounds, and the support function of `W[ρ](D)` is `ρ * ‖x‖[⟨D, hrounding.posDef⟩]`.
/-- Lemma 7.8: if the convex hull of the boxes `B(a_i)` with nonnegative generators contains
`W₁(D)` and is contained in `W_{γ √n}(D)`, then on the nonnegative orthant the support function of
that box hull is sandwiched between `‖x‖_D` and `γ √n ‖x‖_D`. -/
theorem supportFunction_signSymmetricConvexHull_bounds_on_nonnegativeOrthant
    (a : Fin m → Eₙ) {D : Matₙ} {γ : ℝ}
    (ha_nonneg : ∀ i : Fin m, a i ∈ nonnegativeOrthant n)
    (hrounding : IsEllipsoidalRounding (signSymmetricConvexHull a) γ D)
    (x : Eₙ) (hx_nonneg : x ∈ nonnegativeOrthant n) :
    ‖x‖[⟨D, hrounding.posDef⟩] ≤
        (ξ[signSymmetricConvexHull a] x).toReal ∧
      (ξ[signSymmetricConvexHull a] x).toReal ≤
        γ * Real.sqrt (n : ℝ) * ‖x‖[⟨D, hrounding.posDef⟩] := sorry

end
