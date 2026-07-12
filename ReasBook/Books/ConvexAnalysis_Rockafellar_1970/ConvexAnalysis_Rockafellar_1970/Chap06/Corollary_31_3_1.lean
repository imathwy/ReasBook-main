import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_31_1
import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_31_3

noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable [NormedField 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
variable {E : Type u} {EStar : Type*}
variable [NormedAddCommGroup E] [NormedSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable [AddCommGroup EStar] [Module 𝕜 EStar] [TopologicalSpace EStar]
variable [HasPairing E EStar 𝕜]
variable {f g : E → WithTopBot 𝕜}

local notation "IsClosedProperConvex[" 𝕜 "]" => @Function.IsClosedProperConvex 𝕜
local notation "IsClosedProperConcave[" 𝕜 "]" => @Function.IsClosedProperConcave 𝕜
local notation "primalRiQualification" => Set.Nonempty (riDom[𝕜](f) ∩ riDom[𝕜](-g))
local notation "primalObjective" => fun z : E ↦ f z - g z

/-!
Source/core/bridge triage:

- `source-facing`: Corollary 31.3.1 is the identity-map primal-attainment criterion under the
  Corollary 31.2.1 qualification `riDom[𝕜](f) ∩ riDom[𝕜](-g) ≠ ∅`: a point `x` minimizes
  `z ↦ f z - g z` exactly when the convex and concave subdifferentials at `x` have nonempty
  intersection.
- `core/canonical`: the owner abstractions already upstream are the qualification and dual
  attainment owners from `Theorem_31_1` together with the identity-map equality-case criterion
  `primalDualOptimality_iff_subdifferential_conditions` from `Theorem_31_3`.
- `bridge/view`: the Euclidean vector-witness form belongs in a separate bridge theorem obtained
  by transporting the intrinsic dual witness through `InnerProductSpace.toDualMap`.

Domain-style sampling used here:
- `exists_isMaxOn_concaveConjugate_sub_convexConjugate_of_riDom_inter_nonempty` and
  `iInf_sub_eq_iSup_concaveConjugate_sub_convexConjugate_of_fenchel_qualification` from
  `Theorem_31_1`;
- `primalDualOptimality_iff_subdifferential_conditions` from `Theorem_31_3`;
- `subdifferentialAt` from `Chap05/Definition_23_0_6`;
- `concaveSubdifferentialAt` from `Definition_6_30_5`.

Primitive data vs derived API:
- primitive source data: the functions `f`, `g`, the qualification witness
  `riDom[𝕜](f) ∩ riDom[𝕜](-g)`, and the candidate primal point `x`;
- primitive owner theorem reused here: the identity-map zero-gap and dual-attainment results from
  `Theorem_31_1`, and the identity-map pairwise equality-case criterion from `Theorem_31_3`;
- derived API in this file: the nonempty-intersection characterization of primal optimality.

Layer target: `source-facing`.
-/

-- Proof sketch: if `x` minimizes `z ↦ f z - g z`, the qualification hypothesis gives a dual
-- maximizer via `Theorem_31_1`, and the same theorem gives zero duality gap; applying
-- `primalDualOptimality_iff_subdifferential_conditions` to the minimizing/maximizing pair yields
-- the desired witness. Conversely, any witness satisfying the two subdifferential conditions gives
-- a primal-dual optimal pair by `Theorem_31_3`, hence `x` is a primal minimizer.
/-- Corollary 31.3.1, intrinsic dual-owner form: under the qualification
`riDom[𝕜](f) ∩ riDom[𝕜](-g) ≠ ∅`, a point `x` minimizes `z ↦ f z - g z` if and only if the
pairing-level convex and concave subdifferentials at `x` have nonempty intersection. -/
theorem isMinOn_sub_iff_exists_dual_subgradients_of_riDom_inter_nonempty
    (hf : IsClosedProperConvex[𝕜] f)
    (hg : IsClosedProperConcave[𝕜] g)
    (hqual : primalRiQualification)
    (x : E) :
    IsMinOn primalObjective Set.univ x ↔
      Set.Nonempty ((∂[EStar]f(x)) ∩ (∂⁺[EStar]g(x))) := by
  sorry

end

section

variable {𝕜 : Type*}
variable [RCLike 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)] [OrderTopology (WithTopBot 𝕜)]
variable {E : Type u}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
variable {f g : E → WithTopBot 𝕜}

local notation "IsClosedProperConvex[" 𝕜 "]" => @Function.IsClosedProperConvex 𝕜
local notation "IsClosedProperConcave[" 𝕜 "]" => @Function.IsClosedProperConcave 𝕜
local notation "primalRiQualification" => Set.Nonempty (riDom[𝕜](f) ∩ riDom[𝕜](-g))
local notation "primalObjective" => fun z : E ↦ f z - g z

-- Proof sketch: transport the intrinsic dual-witness theorem above through the Euclidean bridge
-- owners `∂ᵥf(x)` and `∂ᵥ⁺ g(x)`, specialized to
-- `EStar = StrongDual 𝕜 E`.
/-- Corollary 31.3.1, Euclidean bridge form: under the same qualification, `x` minimizes
`z ↦ f z - g z` if and only if the intersection of the vector-valued convex and concave
subdifferentials at `x` is nonempty. -/
theorem isMinOn_sub_iff_exists_vector_subgradients_of_riDom_inter_nonempty
    (hf : IsClosedProperConvex[𝕜] f)
    (hg : IsClosedProperConcave[𝕜] g)
    (hqual : primalRiQualification)
    (x : E) :
    IsMinOn primalObjective Set.univ x ↔
      Set.Nonempty (∂ᵥf(x) ∩ ∂ᵥ⁺ g(x)) := by
  sorry

end
