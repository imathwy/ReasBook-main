import ConvexAnalysis_Rockafellar_1970.Chap03.Text_12_3_6
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_2
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_4
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_5
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14
import ConvexAnalysis_Rockafellar_1970.Chap06.Lemma_31_0_6

noncomputable section

open scoped Rockafellar
open Bifunction

universe u v w

section

variable {𝕜 : Type w}
variable [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type u} {U : Type v}
variable {EStar : Type*} {UStar : Type*}
variable [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [AddCommGroup U] [TopologicalSpace U] [Module 𝕜 U]
variable [HasPairing E EStar 𝕜] [HasPairing U UStar 𝕜]
variable [Zero EStar] [Neg UStar]

local notation "IsClosedProperConvex[" 𝕜 "]" => @Function.IsClosedProperConvex 𝕜
local notation "IsClosedProperConcave[" 𝕜 "]" => @Function.IsClosedProperConcave 𝕜

/-!
Source/core/bridge triage:

- `source-facing`: Theorem 31.3 is the equality-case criterion in Fenchel duality with a linear
  map `A`, characterizing when a primal point `x` and a dual point `u⋆` simultaneously attain the
  primal infimum and dual supremum with zero duality gap.
- `core/canonical`: the owner abstractions already present in the project are `convexConjugate`,
  `concaveConjugate`, `subdifferentialAt`, and `concaveSubdifferentialAt`,
  together with the Chapter 6 perturbation-side owners `fenchelPerturbation`, `objective`, and
  `adjoint`.
- `bridge/view`: the source's Kuhn--Tucker conditions are expressed canonically as the two
  subdifferential memberships `A⋆ u⋆ ∈ ∂[EStar]f(x)` and
  `u⋆ ∈ ∂⁺ g at (A x)`, rather than by
  introducing a second packaged `KuhnTucker` predicate.

Domain-style sampling used here:
- `convexConjugate` and the notation `f⋆` from `Chap03.Defn_12_2`;
- `Function.IsClosedProperConvex` from `Chap03.Text_12_3_6`;
- `Function.IsClosedProperConcave` from `Definition_6_30_2`;
- `_root_.subdifferentialAt` from `Chap05.Definition_23_0_6`;
- `_root_.concaveSubdifferentialAt` and `concaveConjugate` from `Definition_6_30_4` and
  `Definition_6_30_5`.

Primitive data vs derived API:
- primitive inputs: the linear map `A`, the functions `f` and `g`, and the candidate primal/dual
  points `x` and `u⋆`, together with a dual-side map `A⋆ : UStar → EStar` satisfying
  `⟪A x, u⋆⟫ = ⟪x, A⋆ u⋆⟫`;
- primitive owner-side primal object: `(fenchelPerturbation A f g)₀`;
- primitive owner-side dual object:
  `((adjoint EStar UStar (fenchelPerturbation A f g))₀)`;
- derived source-facing API: the attained-infimum / attained-supremum wording, expressed
  canonically via `IsMinOn` and `IsMaxOn`;
- canonical optimality conditions: the convex and concave subdifferential memberships.

Ambient abstraction check:
- the theorem surface is on the intrinsic topological-module + pairing layer;
- no normed-space or `OrderTopology` structure is required on the theorem API.

Layer target: `source-facing`. The theorem keeps the textbook primal/dual equality surface, but
  it is refined to the chapter owner abstractions instead of introducing a parallel
  Kuhn--Tucker-data structure.
-/

section

variable (A : E →ₗ[𝕜] U) (Astar : UStar → EStar)
variable (f : E → WithTopBot 𝕜) (g : U → WithTopBot 𝕜)

local notation "F" => fenchelPerturbation A f g
local notation "F⋆" => (adjoint EStar UStar F : EStar → UStar → WithTopBot 𝕜)
local notation "primalObjective" => (F₀)
local notation "dualObjective" => ((F⋆)₀)
local notation "A⋆" => Astar

-- Proof sketch: by Theorem 23.5 on the convex side and its concave-side analogue from
-- `∂⁺ g at (A x)`, the subdifferential conditions are equivalent to the two
-- Fenchel-Young equalities `f x + f⋆ (A⋆ uStar) = ⟪x, A⋆ uStar⟫` and
-- `g (A x) + concaveConjugate g uStar = ⟪A x, uStar⟫`.
-- Subtracting yields equality of the primal and dual objective values at `(x, uStar)`, while the
-- general Fenchel inequality gives `⨅ primalObjective ≥ ⨆ dualObjective`, so that equality at the
-- chosen pair is equivalent to attainment of both extrema with zero gap.
/-- Theorem 31.3, in canonical owner form: for a closed proper convex function `f`, a closed
proper concave function `g`, and a linear map `A`, a primal point `x` and a dual point
`u⋆` attain the primal minimum and dual maximum with zero gap exactly when they satisfy the
canonical subdifferential Kuhn--Tucker conditions `A⋆ u⋆ ∈ ∂[EStar]f(x)` and
`u⋆ ∈ ∂⁺ g at (A x)`, where `A⋆` is pairing-compatible with `A`.
-/
theorem primalDualOptimality_iff_subdifferential_conditions
    (hf : IsClosedProperConvex[𝕜] f)
    (hg : IsClosedProperConcave[𝕜] g)
    (hA : ∀ x : E, ∀ uStar : UStar, (⟪A x, uStar⟫ₚ : 𝕜) = ⟪x, A⋆ uStar⟫ₚ)
    (x : E) (uStar : UStar) :
    IsMinOn primalObjective Set.univ x ∧
      IsMaxOn dualObjective Set.univ uStar ∧
      primalObjective x = dualObjective uStar ↔
        A⋆ uStar ∈ (∂[EStar]f(x)) ∧
          uStar ∈ (∂⁺ g at (A x)) := by
  sorry

end

end
