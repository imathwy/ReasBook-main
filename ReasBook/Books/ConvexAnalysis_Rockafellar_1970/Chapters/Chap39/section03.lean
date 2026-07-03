import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Theorem_39_3 (from Chap08) -/
noncomputable section

open scoped Rockafellar SetRel

universe u v w

namespace SetRel

/-!
Source/core/bridge triage for this item.

- `source-facing`: Theorem 39.3 studies the two process pairings `⟨Au, x⋆⟩` and `⟨u, A⋆ x⋆⟩`
  for a convex process `A`, in both the supremum and infimum orientations.
- `core/canonical`: the built support layer already owns the Chapter 34 representatives
  `Bifunction.lowerPairing`, `Bifunction.upperAdjointPairing`, `concaveConjugate`,
  `Bifunction.closure1`, and `Bifunction.closure2`, while Definition 39.2.1 already owns the
  source-facing supremum process pairing `supremumProcessPairing 𝕜 XStar :
  SetRel U X → U → XStar →
  WithBotTop 𝕜`.
- `bridge/view`: this file introduces only the remaining source-facing pairings, reusing the
  Chapter 34 convex-side representatives for the supremum orientation and the Chapter 6 concave
  conjugate of the negative indicator for the infimum orientation.

Primary mathematical domain:
- convex processes and their Chapter 34 pairing representatives.

Domain-style sampling used here:
- the Chapter 6 canonical bifunction surface
  `#check (fun u ↦ (δ[𝕜](· | S u)) : U → X → WithBotTop 𝕜)` from `Chap06.Definition_6_29_3`;
- `supremumProcessPairing` from `Definition_39_2_1`;
- `SetRel.adjoint` / `A∗[XStar, UStar; 𝕜]` from `Definition_39_0_14`;
- `concaveConjugate` from `Chap06.Definition_6_30_4` and the infimum-oriented set-pairing bridge
  `concaveConjugate_neg_indicatorFunction_eq_sInf_image_pairing` from `Definition_39_0_12`;
- `Function.PositivelyHomogeneous`;
- `Bifunction.lowerPairing`, `Bifunction.upperAdjointPairing`, and
  `Bifunction.IsConvexClosed`;
- `SaddleFunction.IsConcaveConvex`, `SaddleFunction.IsConvexConcave`,
  `SaddleFunction.eq_of_equivalent_of_isConcaveConvex_of_isClosed_of_mem_ri_dom₁_or_mem_ri_dom₂`;
- `HasLinearPairing`, `HasContinuousPairing`, and `SetRel.IsClosed`.

Primitive data vs derived API:
- primitive source data: a convex process `A : SetRel U X`;
- reused source-facing owner from the immediate upstream definition file:
  `supremumProcessPairing 𝕜 XStar A`;
- primitive source-facing owners introduced here:
  `supremumAdjointProcessPairing 𝕜 XStar UStar A`, `infimumProcessPairing 𝕜 XStar A`, and
  `infimumAdjointProcessPairing 𝕜 XStar UStar A`;
- derived API: the slice-wise homogeneity and shape/closedness clauses, the two partial-closure
  identities, and the closed-case pointwise equality on the relative interiors of `dom A` and the
  relevant supremum- or infimum-oriented adjoint-process domain.

Layer target: `source-facing`.
-/

section Pairings

variable {𝕜 : Type*}
variable {U : Type u} {X : Type v} {XStar : Type w} {UStar : Type*}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]

private abbrev negIndicatorFibers (A : SetRel U X) : U → X → WithBotTop 𝕜 :=
  -(indicatorFibers 𝕜 A)

private abbrev negOrderDualAdjointIndicatorFibers
    (UStar : Type*) [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]
    (A : SetRel U X) : XStar → UStar → WithBotTop 𝕜 :=
  fun xStar ↦
    -(δ[𝕜](· | (A∗[XStar, UStar; 𝕜ᵒᵈ]).image ({xStar} : Set XStar)) :
      UStar → WithBotTop 𝕜)

/-- The Chapter 39 supremum-oriented adjoint pairing `⟨u, A⋆ x⋆⟩`, expressed through the same
fiber-indicator bridge. -/
abbrev supremumAdjointProcessPairing (𝕜 : Type*) [CommRing 𝕜]
    [ConditionallyCompleteLinearOrder 𝕜] (XStar : Type w) (UStar : Type*)
    [Neg UStar] [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]
    (A : SetRel U X) : U → XStar → WithBotTop 𝕜 :=
  Bifunction.upperAdjointPairing XStar UStar (indicatorFibers 𝕜 A)

/-- The Chapter 39 infimum-oriented process pairing `⟨Au, x⋆⟩`, expressed through the negative
fiber-indicator bridge. -/
abbrev infimumProcessPairing (𝕜 : Type*) [CommRing 𝕜]
    [ConditionallyCompleteLinearOrder 𝕜] (XStar : Type w) [HasPairing X XStar 𝕜]
    (A : SetRel U X) : U → XStar → WithBotTop 𝕜 :=
  fun u xStar ↦ concaveConjugate (negIndicatorFibers A u) xStar

/-- The Chapter 39 infimum-oriented adjoint pairing `⟨u, A⋆ x⋆⟩`, expressed through the same
negative-indicator bridge on the order-dual adjoint fibers. -/
abbrev infimumAdjointProcessPairing (𝕜 : Type*) [CommRing 𝕜]
    [ConditionallyCompleteLinearOrder 𝕜] (XStar : Type w) (UStar : Type*)
    [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]
    (A : SetRel U X) : U → XStar → WithBotTop 𝕜 :=
  fun u xStar ↦
    let _ : HasPairing UStar U 𝕜 := HasPairing.swap
    concaveConjugate (negOrderDualAdjointIndicatorFibers UStar A xStar) u

end Pairings

section Theorem39_3

variable {𝕜 : Type*}
variable {U : Type u} {X : Type v} {XStar : Type w}

section Homogeneity

variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable [AddCommMonoid U] [Module 𝕜 U]
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid XStar] [Module 𝕜 XStar]
variable [HasLinearPairing X XStar 𝕜] [HasLinearPairing XStar X 𝕜] [HasPairingSwap X XStar 𝕜]

-- Proof sketch: for the supremum branch, the canonical slice-wise indicator expression
-- `indicatorFibers 𝕜 A` is the indicator of the cone-valued fiber map of a
-- convex process. Slice conjugation of indicator functions yields support functions, which are
-- positively homogeneous in the dual variable, while the convex-cone graph condition gives
-- positive homogeneity in the parameter variable.
/-- Theorem 39.3 (1): for a supremum-oriented convex process `A`, the pairing `⟨Au, x⋆⟩` is
positively homogeneous in `x⋆` for each `u` and positively homogeneous in `u` for each `x⋆`. -/
theorem supremumProcessPairing_positivelyHomogeneous
    {A : SetRel U X} (hA : A.IsConvexProcess 𝕜) :
    (∀ u : U, (supremumProcessPairing 𝕜 XStar A u).PositivelyHomogeneous 𝕜) ∧
      ∀ xStar : XStar,
        Function.PositivelyHomogeneous 𝕜
          (fun u : U ↦ supremumProcessPairing 𝕜 XStar A u xStar) :=
      sorry

-- Proof sketch: for the infimum branch, replace the indicator by its negative. The same cone
-- argument gives positive homogeneity of the resulting slice conjugates in both variables.
/-- Theorem 39.3 (3): for an infimum-oriented convex process `A`, the pairing `⟨Au, x⋆⟩` is
positively homogeneous in `x⋆` for each `u` and positively homogeneous in `u` for each `x⋆`. -/
theorem infimumProcessPairing_positivelyHomogeneous
    {A : SetRel U X} (hA : A.IsConvexProcess 𝕜) :
    (∀ u : U, (infimumProcessPairing 𝕜 XStar A u).PositivelyHomogeneous 𝕜) ∧
      ∀ xStar : XStar,
        Function.PositivelyHomogeneous 𝕜 (fun u : U ↦ infimumProcessPairing 𝕜 XStar A u xStar) :=
      sorry

end Homogeneity

section ShapeAndClosure

variable {UStar : Type*}
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
variable [AddCommGroup U] [Module 𝕜 U] [TopologicalSpace U]
variable [AddCommGroup X] [Module 𝕜 X] [TopologicalSpace X]
variable [AddCommGroup XStar] [Module 𝕜 XStar] [TopologicalSpace XStar]
variable [AddCommMonoid UStar] [Module 𝕜 UStar]
variable [Neg UStar] [HasLinearPairing U UStar 𝕜] [HasContinuousPairing U UStar 𝕜]
variable [HasLinearPairing X XStar 𝕜] [HasContinuousPairing X XStar 𝕜]
variable [HasLinearPairing XStar X 𝕜] [HasContinuousPairing XStar X 𝕜]
variable [HasPairingSwap X XStar 𝕜]
variable [Module 𝕜 (WithBotTop 𝕜)] [PosSMulMono 𝕜 (WithBotTop 𝕜)]

-- Proof sketch: apply the Chapter 33 convex-bifunction theorem to the canonical slice-wise
-- indicator expression `fun u ↦ δ[𝕜](· | A.image ({u} : Set U))`.
-- graph-function convexity comes from `hA`, the resulting lower representative is concave-convex,
-- and Theorem 33.1.1 identifies its second-variable closure as closed-convex.
/-- Theorem 39.3 (2): for a supremum-oriented convex process `A`, the pairing bifunction
`(u, x⋆) ↦ ⟨Au, x⋆⟩` is concave-convex and is closed in the `x⋆` variable. -/
theorem supremumProcessPairing_isConcaveConvex_and_isConvexClosed
    {A : SetRel U X} (hA : A.IsConvexProcess 𝕜) :
    SaddleFunction.IsConcaveConvex 𝕜 (supremumProcessPairing 𝕜 XStar A) ∧
      Bifunction.IsConvexClosed (supremumProcessPairing 𝕜 XStar A) := sorry

-- Proof sketch: apply the Chapter 33 saddle-shape theorem to the negative fiber indicator
-- bifunction of `A`.
-- negative indicator reverses the two slice-convexity roles, so the resulting pairing is
-- convex-concave. Closed concavity in the `x⋆` variable is expressed by convex closedness of the
-- negated pairing.
/-- Theorem 39.3 (4): for an infimum-oriented convex process `A`, the pairing bifunction
`(u, x⋆) ↦ ⟨Au, x⋆⟩` is convex-concave and is closed-concave in the `x⋆` variable. -/
theorem infimumProcessPairing_isConvexConcave_and_neg_isConvexClosed
    {A : SetRel U X} (hA : A.IsConvexProcess 𝕜) :
    SaddleFunction.IsConvexConcave 𝕜 (infimumProcessPairing 𝕜 XStar A) ∧
      Bifunction.IsConvexClosed (-(infimumProcessPairing 𝕜 XStar A)) := sorry

-- Proof sketch: in both orientations, Chapter 33 identifies the upper representative of a
-- saddle kernel as the first-variable partial closure `cl₁` of the lower representative.
/-- Theorem 39.3 (5): in both the supremum and infimum orientations, the adjoint pairing
`⟨u, A⋆ x⋆⟩` is the first-variable partial closure of the process pairing `⟨Au, x⋆⟩`. -/
theorem adjointProcessPairing_eq_closure1_processPairing
    {A : SetRel U X} (hA : A.IsConvexProcess 𝕜) :
    supremumAdjointProcessPairing 𝕜 XStar UStar A = cl₁ (supremumProcessPairing 𝕜 XStar A) ∧
      infimumAdjointProcessPairing 𝕜 XStar UStar A = cl₁ (infimumProcessPairing 𝕜 XStar A) := sorry

-- Proof sketch: if `A` is graph-closed, the source pairings are already closed in the dual
-- variable. The Chapter 34 second-variable closure therefore fixes the adjoint representatives and
-- recovers the original lower representatives in both orientations.
/-- Theorem 39.3 (6): if `A` is closed, then in both orientations the process pairing
`⟨Au, x⋆⟩` is the second-variable partial closure of `⟨u, A⋆ x⋆⟩`. -/
theorem processPairing_eq_closure2_adjointProcessPairing_of_isClosed
    {A : SetRel U X} (hA : A.IsConvexProcess 𝕜) (hA_closed : A.IsClosed) :
    supremumProcessPairing 𝕜 XStar A = cl₂ (supremumAdjointProcessPairing 𝕜 XStar UStar A) ∧
      infimumProcessPairing 𝕜 XStar A = cl₂ (infimumAdjointProcessPairing 𝕜 XStar UStar A) := sorry

-- Proof sketch: combine the previous closure identities with the Chapter 33 relative-interior
-- equality theorem on `ri(dom A)` for the primal side and on the relative interior of the
-- supremum-oriented adjoint-process domain `(A∗[XStar, UStar; 𝕜]).dom` for the dual side.
/-- Theorem 39.3 (7): if `A` is closed, then in the supremum orientation the two pairings
`⟨Au, x⋆⟩` and `⟨u, A⋆ x⋆⟩` agree whenever `u ∈ ri (dom A)` or
`x⋆ ∈ ri (dom A⋆)`, with `dom A⋆` rendered by the canonical adjoint-process owner
`(A∗[XStar, UStar; 𝕜]).dom`. -/
theorem supremumProcessPairing_eq_adjointProcessPairing_of_mem_ri_dom_or_mem_ri_dom_adjoint
    {A : SetRel U X} (hA : A.IsConvexProcess 𝕜) (hA_closed : A.IsClosed)
    {u : U} {xStar : XStar}
    (hmem : u ∈ intrinsicInterior 𝕜 (A.dom) ∨
      xStar ∈ intrinsicInterior 𝕜 ((A∗[XStar, UStar; 𝕜]).dom)) :
    supremumProcessPairing 𝕜 XStar A u xStar =
      supremumAdjointProcessPairing 𝕜 XStar UStar A u xStar := sorry

-- Proof sketch: the same Chapter 33 relative-interior equality applies to the infimum-oriented
-- kernel `negIndicatorFibers A`. The adjoint-process domain is now the order-dual process
-- adjoint relation `(A∗[XStar, UStar; 𝕜ᵒᵈ]).dom`, which is the Chapter 39 infimum-oriented
-- reading of
-- `A⋆`.
/-- Theorem 39.3 (8): if `A` is closed, then in the infimum orientation the two pairings
`⟨Au, x⋆⟩` and `⟨u, A⋆ x⋆⟩` agree whenever `u ∈ ri (dom A)` or
`x⋆ ∈ ri (dom A⋆)`, with `dom A⋆` rendered by the order-dual adjoint-process owner
`(A∗[XStar, UStar; 𝕜ᵒᵈ]).dom`. -/
theorem infimumProcessPairing_eq_adjointProcessPairing_of_mem_ri_dom_or_mem_ri_dom_adjoint
    {A : SetRel U X} (hA : A.IsConvexProcess 𝕜) (hA_closed : A.IsClosed)
    {u : U} {xStar : XStar}
    (hmem : u ∈ intrinsicInterior 𝕜 (A.dom) ∨
      xStar ∈ intrinsicInterior 𝕜 ((A∗[XStar, UStar; 𝕜ᵒᵈ]).dom)) :
    infimumProcessPairing 𝕜 XStar A u xStar =
      infimumAdjointProcessPairing 𝕜 XStar UStar A u xStar := sorry

end ShapeAndClosure

end Theorem39_3

end SetRel
