import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_0_3
import ConvexAnalysis_Rockafellar_1970.Chap04.Definition_17_2_4
import ConvexAnalysis_Rockafellar_1970.Chap04.Lemma_17_2_9

-- Declarations for this item will be appended below by the statement pipeline.

section

open scoped BigOperators Rockafellar

-- Scalar layer minimization: this item needs a `DivisionRing` (not a full `Field`) because the
-- statement uses `FiniteDimensional`/`affineSpan` and `K⋆[R]` membership.
variable {X Y : Type*}
  {R : Type*} [DivisionRing R] [PartialOrder R] [IsOrderedRing R]
  [AddCommGroup X] [Module R X]
  [AddCommMonoid Y] [Module R Y]
  [HasPairing X Y R]

local notation "YStar" => Y × R
local notation "solutionSet[" SStar "]" =>
  linearInequalitySolutionSet (E := X) (SStar : Set YStar)
local notation "halfSpace[" yStar ", " μStar "]" =>
  (closedHalfSpaceLE yStar μStar : Set X)

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 17.2.11 characterizes when a closed half-space in the primal space `X`
  contains the convex set cut out by a closed bounded dual family `S* ⊆ Y × R`; specializing
  `X = Y = EuclideanSpace ℝ (Fin n)` recovers the textbook `ℝ^n` statement.
  This keeps the owner at the pairing layer instead of forcing a self-dual model `X = Y`.
- `core/canonical`: the owner abstractions are the source-facing set
  `linearInequalitySolutionSet SStar` in `X`, the half-space constructor `closedHalfSpaceLE`,
  the full-dimensionality condition `affineSpan R C = ⊤`, and the generated-cone owner on dual
  data `K⋆[R] SStar` in `Y × R`.
- `bridge/view`: the source-facing bridge theorem adds the Caratheodory cardinality bound
  `s.card ≤ Module.finrank R X` to the canonical generated-cone witness on a finite support
  `SStar`; the companion theorem is the same finite weighted witness surface.

Domain-style sampling used here:
- `linearInequalitySolutionSet` from `Chap04.Definition_17_2_4`;
- `closedHalfSpaceLE` from `Chap01.Definition_2_0_3`;
- `K⋆[R]` from `Chap04.Definition_17_2_5`;
- `mem_generated_cone_iff_exists_conicCombination` from `Chap04.Lemma_17_2_9`;
- finite sums over `Fin m` via `BigOperators`;
- affine-hull fullness via `affineSpan R C = ⊤`;
- ambient dimension measured canonically by `Module.finrank R X`.

-/

-- Proof sketch: adjoin `((0 : Y), 1)` to `SStar`, pass to the cone it generates in `Y × R`,
-- use closedness of that cone together with the half-space containment criterion, and then apply
-- the Caratheodory reduction in ambient dimension `Module.finrank R X + 1`. The
-- full-dimensionality assumption on `linearInequalitySolutionSet SStar` removes the extra
-- vertical generator and leaves at most `Module.finrank R X` generators from `SStar`.
/-- Canonical owner form of Theorem 17.2.11: under closedness/boundedness of `SStar` and
full-dimensionality of `solutionSet[SStar]`, containment in the half-space
`closedHalfSpaceLE yStar μStar` is equivalent to generated-cone membership of the dual pair
`(yStar, μStar)` in `K⋆[R] SStar`. -/
theorem subset_closedHalfSpaceLE_iff_mem_generatedCone
    [FiniteDimensional R X] [TopologicalSpace YStar] [Bornology YStar]
    {SStar : Set YStar} (hSStar_closed : IsClosed SStar)
    (hSStar_bounded : Bornology.IsBounded SStar)
    (hfull : affineSpan R (solutionSet[SStar]) = ⊤)
    (yStar : Y) (μStar : R) :
    solutionSet[SStar] ⊆ halfSpace[yStar, μStar] ↔
      (yStar, μStar) ∈ (K⋆[R] SStar) := sorry

/-- Source-facing finite-support certificate form of Theorem 17.2.11: under the same hypotheses as
`subset_closedHalfSpaceLE_iff_mem_generatedCone`, containment of `solutionSet[SStar]` in
`closedHalfSpaceLE yStar μStar` is equivalent to a finite nonnegative conic-combination witness
for `(yStar, μStar)` with support size at most `Module.finrank R X`. -/
theorem subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_certificate
    [FiniteDimensional R X] [TopologicalSpace YStar] [Bornology YStar]
    {SStar : Set YStar} (hSStar_closed : IsClosed SStar)
    (hSStar_bounded : Bornology.IsBounded SStar)
    (hfull : affineSpan R (solutionSet[SStar]) = ⊤)
    (yStar : Y) (μStar : R) :
    solutionSet[SStar] ⊆ halfSpace[yStar, μStar] ↔
      ∃ s : Finset YStar,
        s.card ≤ Module.finrank R X ∧
          (∀ y ∈ s, y ∈ SStar) ∧
            ∃ weights : {y // y ∈ s} → R,
              (∀ y, 0 ≤ weights y) ∧
                yStar = s.attach.sum (fun y ↦ weights y • (y : YStar).1) ∧
                s.attach.sum (fun y ↦ weights y * (y : YStar).2) ≤ μStar := sorry

/-- Companion source-facing form of Theorem 17.2.11: the generated-cone witness is equivalently a
finite nonnegative combination of inequalities from a subset of `SStar` of cardinality at most
`Module.finrank R X`, with combined scalar part at most `μStar`. -/
theorem subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_conicCombination
    [FiniteDimensional R X] [TopologicalSpace YStar] [Bornology YStar]
    {SStar : Set YStar} (hSStar_closed : IsClosed SStar)
    (hSStar_bounded : Bornology.IsBounded SStar)
    (hfull : affineSpan R (solutionSet[SStar]) = ⊤)
    (yStar : Y) (μStar : R) :
    solutionSet[SStar] ⊆ halfSpace[yStar, μStar] ↔
      ∃ s : Finset YStar,
        s.card ≤ Module.finrank R X ∧
          (∀ y ∈ s, y ∈ SStar) ∧
            ∃ weights : {y // y ∈ s} → R,
              (∀ y, 0 ≤ weights y) ∧
                yStar = s.attach.sum (fun y ↦ weights y • (y : YStar).1) ∧
                s.attach.sum (fun y ↦ weights y * (y : YStar).2) ≤ μStar := by
  simpa using
    (subset_closedHalfSpaceLE_iff_exists_dualCaratheodory_certificate
      (SStar := SStar) hSStar_closed hSStar_bounded hfull yStar μStar)

end
