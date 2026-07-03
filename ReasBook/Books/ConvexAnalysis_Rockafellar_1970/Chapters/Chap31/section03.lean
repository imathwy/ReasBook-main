

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_31_3_1 (from Chap06) -/
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

/-! ### Example_31_3_2 (from Chap06) -/
noncomputable section

open scoped Pointwise Rockafellar
attribute [local instance] Classical.propDecidable
universe u v

/-!
Source/core/bridge triage:

- `source-facing`: Example 31.3.2 computes the primal and dual Kuhn--Tucker subgradient sets at
  owner level as orthant-normal-cone translations.
- `core/canonical`: the owner abstractions used here are the dual-valued owners
  `∂[Y](·)(·)` and `∂⁺[Y](·)(·)`, together with the orthant
  owner `orthant` and the pairing-based normal-cone owner `normalCone`.

Domain-style sampling used here:
- `orthant` and `mem_orthant_iff` from `Chap01.Definition_2_5_11`;
- `normalCone` and `mem_normalCone_iff` from `Chap01.Definition_2_7_10`;
- `subdifferentialAt` notation `∂[Y]f(x)` from `Chap05.Definition_23_0_6`;
- `concaveSubdifferentialAt` notation `∂⁺[Y]g(x)` from `Chap06.Definition_6_30_5`.

Primitive data vs derived API:
- primitive source data: dual coefficients in an arbitrary paired dual carrier for the owner-level
  LP branches;
- primitive owner surface: the dual-valued owner sets `∂[Y](·)(·)` and `∂⁺[Y](·)(·)`;
- derived API: the normal-cone translation formulas.

Ambient/codomain layer notes:
- owner-level statements are pairing-based (paired dual carrier + normal cone), not hard-coded to
  vector-inner-product owners;
- primal codomain is at the weaker `WithTopBot 𝕜` layer;
- dual branch is also stated on `WithTopBot 𝕜`: this branch is an orthant-restricted affine map
  with value `⊥` outside the feasible region, so no extra `EReal` specialization is needed.

Layer target: `source-facing` owner theorems only, with no Euclidean coordinate bridge API and no
parallel LP-specific wrapper API.
-/

section PrimalOwner

variable {𝕜 : Type v} [Ring 𝕜] [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜] [AddLeftMono 𝕜]
variable {X : Type u} [AddCommGroup X] [Module 𝕜 X]
  [PartialOrder X] [IsOrderedAddMonoid X] [PosSMulMono 𝕜 X]

variable {Y : Type (max u v)} [AddCommGroup Y] [HasPairing X Y 𝕜]
  [HasPairingZeroLeft X Y 𝕜] [HasPairingAddRight X Y 𝕜]
  [HasPairingSubLeft X Y 𝕜] [HasPairingSubRight X Y 𝕜]
private def primalOwnerBranch (aStar : Y) : X → WithTopBot 𝕜 :=
  fun z : X ↦ ((⟪z, aStar⟫ₚ : 𝕜) : WithTopBot 𝕜) + δ[𝕜](z | orthant[𝕜](X))

-- Proof sketch: the primal branch is the affine functional `z ↦ ⟪z, a⋆⟫ₚ` plus the orthant
-- indicator in the canonical `WithTopBot 𝕜` codomain. Applying the Chapter 23 owner for affine
-- perturbations together with the Chapter 1 normal-cone owner for the indicator gives the
-- translated cone `{a⋆} + N[𝕜](x | orthant)`.
/-- Example 31.3.2, primal side at owner level: for
`f x = ⟪x, a⋆⟫ₚ + δ[𝕜](x | orthant[𝕜](X))`, the pairing-level
subdifferential in any paired dual carrier is the
translate of the orthant normal cone by `a⋆`. -/
theorem subdifferentialAt_apply_add_indicator_orthant
    (aStar : Y)
    (x : X) :
    ∂[Y] (primalOwnerBranch aStar : X → WithTopBot 𝕜)(x) =
      ({aStar} : Set Y) + N[𝕜](x | orthant[𝕜](X)) := by
  sorry

end PrimalOwner

section DualOwner

variable {𝕜 : Type v} [Ring 𝕜] [PartialOrder 𝕜] [IsOrderedAddMonoid 𝕜] [AddLeftMono 𝕜]
variable {U : Type u} [AddCommGroup U] [Module 𝕜 U]
  [PartialOrder U] [IsOrderedAddMonoid U] [PosSMulMono 𝕜 U]

variable {Y : Type (max u v)} [AddCommGroup Y] [HasPairing U Y 𝕜]
  [HasPairingZeroLeft U Y 𝕜] [HasPairingNegRight U Y 𝕜]
  [HasPairingAddRight U Y 𝕜] [HasPairingSubLeft U Y 𝕜]
  [HasPairingSubRight U Y 𝕜]
private def dualOwnerBranch (a : Y) : U → WithTopBot 𝕜 :=
  fun v : U ↦
    if v ∈ orthant[𝕜](U) then ((⟪v, a⟫ₚ : 𝕜) : WithTopBot 𝕜) else (⊥ : WithTopBot 𝕜)

-- Proof sketch: rewrite the dual branch as the affine functional `u⋆ ↦ ⟪u⋆, a⟫ₚ` restricted to
-- the nonnegative orthant and equal to `⊥` off the orthant, then apply the canonical concave
-- subdifferential owner formula together with the orthant normal-cone description.
/-- Example 31.3.2, dual side at owner level: for the orthant-restricted affine branch
`u⋆ ↦ if u⋆ ∈ orthant[𝕜](U) then ⟪u⋆, a⟫ₚ else ⊥`, the pairing-level
concave subdifferential in
any paired dual carrier is the translate by `a` of the negative orthant normal cone. -/
theorem concaveSubdifferentialAt_apply_on_orthant
    (a : Y)
    (uStar : U) :
    ∂⁺[Y] (dualOwnerBranch a : U → WithTopBot 𝕜)(uStar) =
      ({a} : Set Y) + (-N[𝕜](uStar | orthant[𝕜](U))) := by
  sorry

end DualOwner

/-! ### Theorem_31_3 (from Chap06) -/
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

/-! ### Remark_31_3_4 (from Chap06) -/
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
