import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_5_11
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_31_4

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Rockafellar

section

variable {ι : Type*} [Fintype ι]
variable {𝕜 : Type*}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [LinearOrder 𝕜]
  [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithBotTop 𝕜)] [OrderTopology (WithBotTop 𝕜)]
variable [CompleteSpace 𝕜]

variable {f : (ι → 𝕜) → WithBotTop 𝕜}

local notation "IsClosedProperConvex[𝕜]" => @Function.IsClosedProperConvex 𝕜
local notation "orthant" => (ConvexCone.positive 𝕜 (ι → 𝕜) : Set (ι → 𝕜))
local notation "convexDual" => (f⋆ : (ι → 𝕜) → WithBotTop 𝕜)

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 31.4.1 is the nonnegative-orthant specialization of Fenchel duality
  on a finite coordinate space `𝕜^ι`, together with the two branchwise attainment
  conclusions and the coordinatewise complementary-slackness optimality criterion.
- `core/canonical`: the owner abstraction is the cone-duality package in `Theorem_31_4`,
  specialized to the canonical chapter orthant owner `orthant`,
  together with `f.IsClosedProperConvex`, the Fenchel conjugate `convexDual`, `riDom[𝕜](·)`,
  `IsMinOn`, and the pairing-level Chapter 23 subgradient owner `_root_.subdifferentialAt`
  (surface notation: `∂[(ι → 𝕜)]f(x)`).
- `bridge/view`: the source inequalities `x ≥ 0` and `x⋆ ≥ 0` are rendered by membership in the
  canonical orthant owner in the intrinsic coordinate ambient `X = ι → 𝕜`;
  `mem_nonnegativeOrthant_iff` therefore
  recovers the source reading `∀ i, 0 ≤ x i`, and the source coordinatewise complementarity
  condition is kept explicitly as `∀ i, x i * xStar i = 0`.

Domain-style sampling used here:

- `ConvexCone.positive` and `mem_nonnegativeOrthant_iff` from `Chap01.Definition_2_5_11`;
- `polarCone_nonnegativeOrthant_eq_neg` from `Chap03.Text_14_0_10`;
- `iInf_on_cone_eq_neg_iInf_on_dualCone_of_polyhedral_fenchel_cone_qualification`,
  `exists_mem_isMinOn_convexConjugate_on_dualCone_of_polyhedral_primal_qualification`,
  `exists_mem_isMinOn_on_cone_of_polyhedral_dual_qualification`, and
  `optimalValue_pair_iff_mem_subdifferential_and_dualCone_complementarity` from
  `Chap06.Theorem_31_4`.
- the canonical pointwise-order instances on `ι → 𝕜`, which make `0 ≤ x` equivalent to
  `∀ i, 0 ≤ x i`.

Primitive data vs derived API:

- primitive inputs: the closed proper convex function `f` on the finite coordinate space `𝕜^ι`
  and the two source
  qualification clauses on `riDom[𝕜](f)` and `riDom[𝕜](convexDual)`;
- derived API: the zero-duality-gap identity on the nonnegative orthant, the two attainment
  conclusions, and the orthant-specialized optimality criterion.

Layer target: `bridge/view`, implemented as the orthant specialization of the existing cone
duality owner rather than by introducing a parallel local orthant owner.
-/

-- Proof sketch: specialize the polyhedral cone theorem from `Theorem_31_4` to the nonnegative
-- orthant owner `orthant`. The source coordinatewise reading is a
-- companion view supplied by `mem_nonnegativeOrthant_iff`.
/-- Corollary 31.4.1: for a closed proper convex function `f` on the finite coordinate space
`𝕜^ι`, the infimum of `f` over the nonnegative orthant equals the negative of the infimum of
`f⋆` over the nonnegative orthant whenever either some `x ∈ riDom[𝕜](f)` satisfies `x ≥ 0`
or some `x⋆ ∈ riDom[𝕜](f⋆)` satisfies
`x⋆ ≥ 0`. -/
theorem
    iInf_on_nonnegativeOrthant_eq_neg_iInf_convexConjugate_of_fenchel_qualification
    (hf : IsClosedProperConvex[𝕜] f)
    (hqual :
      ((riDom[𝕜](f) : Set (ι → 𝕜)) ∩ orthant).Nonempty ∨
        ((riDom[𝕜](convexDual) : Set (ι → 𝕜)) ∩ orthant).Nonempty) :
    (⨅ x : orthant, f x) = -(⨅ xStar : orthant, convexDual xStar) := sorry

-- Proof sketch: specialize the polyhedral attainment clause (a) of `Theorem_31_4` to the orthant
-- cone. After identifying the sign-twisted dual cone with the orthant again, the dual minimizer
-- lies in the same nonnegative orthant as in the source statement.
/-- Under the primal qualification `∃ x ∈ riDom[𝕜](f), x ≥ 0`, the infimum of `f⋆` over the
nonnegative orthant is attained. -/
theorem exists_mem_isMinOn_convexConjugate_on_nonnegativeOrthant_of_primal_qualification
    (hf : IsClosedProperConvex[𝕜] f)
    (hqual : ((riDom[𝕜](f) : Set (ι → 𝕜)) ∩ orthant).Nonempty) :
    ∃ xStar ∈ orthant, IsMinOn convexDual orthant xStar := sorry

-- Proof sketch: specialize the polyhedral attainment clause (b) of `Theorem_31_4` to the orthant
-- cone. The orthant is self-dual up to the chapter sign convention, so the primal minimizer is
-- exactly a point of the nonnegative orthant.
/-- Under the dual qualification `∃ x⋆ ∈ riDom[𝕜](f⋆), x⋆ ≥ 0`, the infimum of `f` over the
nonnegative orthant is attained. -/
theorem exists_mem_isMinOn_on_nonnegativeOrthant_of_dual_qualification
    (hf : IsClosedProperConvex[𝕜] f)
    (hqual : ((riDom[𝕜](convexDual) : Set (ι → 𝕜)) ∩ orthant).Nonempty) :
    ∃ x ∈ orthant, IsMinOn f orthant x := sorry

-- Proof sketch: specialize the orthant instance of `Theorem_31_4`'s optimality criterion. The
-- feasibility conditions are `x ∈ orthant` and `x⋆ ∈ orthant`; `mem_nonnegativeOrthant_iff`
-- recovers the coordinatewise nonnegativity reading, and the self-dual orthant specialization
-- turns complementary slackness into the coordinatewise relations `x i * xStar i = 0`.
/-- The orthant specialization of Fenchel optimality: the two orthant infima are negatives of one
another and are attained at `x` and `x⋆` exactly when `x⋆ ∈ ∂[(ι → 𝕜)]f(x)` and the
coordinates of `x` and `x⋆` satisfy nonnegativity and complementary slackness. -/
theorem optimalValue_pair_iff_mem_subdifferential_and_nonnegative_coordinate_complementarity
    (hf : IsClosedProperConvex[𝕜] f)
    (x xStar : ι → 𝕜) :
    IsMinOn f orthant x ∧
      IsMinOn convexDual orthant xStar ∧
      f x = -(convexDual xStar) ↔
      xStar ∈ ∂[(ι → 𝕜)]f(x) ∧
        x ∈ orthant ∧
          xStar ∈ orthant ∧
            ∀ i : ι, x i * xStar i = (0 : 𝕜) := sorry

end
