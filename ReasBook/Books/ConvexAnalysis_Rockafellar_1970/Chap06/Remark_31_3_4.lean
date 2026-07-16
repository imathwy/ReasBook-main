import ConvexAnalysis_Rockafellar_1970.Chap06.Theorem_31_3

noncomputable section

open scoped Rockafellar

universe u v

section

variable {𝕜 : Type v}
variable [Semiring 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [TopologicalSpace (WithTopBot 𝕜)]
variable {E : Type u} {EStar : Type (max u v)}
variable [AddCommGroup E] [TopologicalSpace E] [Module 𝕜 E]
variable [HasPairing E EStar 𝕜]
local instance : HasPairing EStar E 𝕜 := HasPairing.swap (X := E) (Y := EStar) (L := 𝕜)
variable {f g : E → WithTopBot 𝕜}

local notation "IsClosedProperConvex[" 𝕜 "]" => Function.IsClosedProperConvex (𝕜 := 𝕜)
local notation "IsClosedProperConcave[" 𝕜 "]" => Function.IsClosedProperConcave (𝕜 := 𝕜)

local notation "primalObjective" => fun x : E ↦ f x - g x
local notation "dualObjective" =>
  fun xStar : EStar ↦ g∗ xStar - (f⋆ : EStar → WithTopBot 𝕜) xStar

/-!
Source/core/bridge triage:

- `source-facing`: Remark 31.3.4 rewrites the identity-map Kuhn--Tucker conditions in Fenchel
  duality so that the concave-side condition is stated on the conjugate `g*`.
- `core/canonical`: the owner abstraction for the identity-map problem is already
  `primalDualOptimality_iff_subdifferential_conditions` from `Theorem_31_3`.
- `bridge/view`: this file only transports the concave-side subdifferential condition
  `x⋆ ∈ ∂[EStar]f(x)` and `x⋆ ∈ ∂⁺[EStar]g(x)` to the conjugate-side condition
  `x ∈ ∂⁺[E](g∗)(x⋆)`, i.e. the same Kuhn--Tucker system expressed on the intrinsic
  primal/dual pairing rather than a concrete `StrongDual` realization; it does not introduce a
  second Kuhn--Tucker owner.

Domain-style sampling used here:
- `primalDualOptimality_iff_subdifferential_conditions` from `Theorem_31_3`;
- `concaveConjugate_eq_neg_convexConjugate_neg_apply` from `Theorem_6_30_4`;
- `concaveSubdifferentialAt` from `Definition_6_30_5`.

Primitive data vs derived API:
- primitive source data: the functions `f`, `g`, and the candidate primal/dual points `x`, `x⋆`;
- primitive owner theorem: `primalDualOptimality_iff_subdifferential_conditions` at `A = id`;
- derived API: the conjugate-side reformulation of the right-hand Kuhn--Tucker condition on the
  canonical pairing between `E` and `EStar`.

Layer target: `bridge/view`.

Ambient-assumption check:
- this remark is a bridge/view reformulation of `Theorem_31_3` at `A = id`, so it should stay at
  the same scalar/order/topology/pairing layer as that first owner theorem, rather than
  introducing extra concrete-dual assumptions.
- codomain minimality: this file surfaces codomains as `WithTopBot 𝕜`, the canonical extended
  codomain owner layer used by Chapter 6 conjugate/subdifferential APIs.
- scalar minimality: this statement is now carried by the weakest scalar layer already exposed by
  the upstream owner `primalDualOptimality_iff_subdifferential_conditions`.
- intrinsic/relative-topology check: non-applicable here, since the statement has no ambient
  `closure`/`interior`/open/closed surface to replace.
-/

/-- Remark 31.3.4: in the identity-map specialization of Fenchel duality, the Kuhn--Tucker
conditions may be written on any paired dual carrier `EStar` as
`x⋆ ∈ ∂[EStar]f(x)` and
`x ∈ ∂⁺[E](g∗)(x⋆)`, where `g*` is `g∗`.
Equivalently, a primal point `x` and a dual point `x⋆` attain the primal
minimum and dual maximum with zero duality gap exactly when those two subdifferential conditions
hold. -/
theorem primalDualOptimality_id_iff_subdifferential_concaveConjugate_conditions
    (hf : IsClosedProperConvex[𝕜] f)
    (hg : IsClosedProperConcave[𝕜] g)
    (x : E) (xStar : EStar) :
    IsMinOn primalObjective Set.univ x ∧
      IsMaxOn dualObjective Set.univ xStar ∧
      primalObjective x = dualObjective xStar ↔
        xStar ∈ (∂[EStar]f(x)) ∧
          x ∈ (∂⁺[E](g∗)(xStar)) := by
  sorry

end
