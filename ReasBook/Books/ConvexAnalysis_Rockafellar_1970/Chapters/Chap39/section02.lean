import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_39_2_1 (from Chap08) -/
noncomputable section

open scoped Rockafellar

universe u v w

/-!
Source/core/bridge triage:

- `source-facing`: Definition 39.2.1 introduces the process pairing `⟨Au, x⋆⟩`, namely the
  support value of the fiber `Au` at `x⋆`.
- `core/canonical`: the owner abstraction underneath is the support-function surface
  `δᵛ[WithBotTop 𝕜](xStar | C)`.
- `bridge/view`: the companion theorem identifies this source-facing process pairing with the
  convex pairing of the corresponding indicator slice, via
  `convexConjugate_indicatorFunction_eq_supportFunction_pointwise`.

Primary mathematical domain:
- support functions and indicator-function conjugacy on convex-process fibers.

Domain-style sampling used here:
- `supportFunction` from `Chap01.Defintion_4_8_2`;
- `convexConjugate_indicatorFunction_eq_supportFunction_pointwise` from
  `Chap03.Text_13_1_4`;
- the Chapter 33 raw owner `convexConjugate`.

Primitive data vs derived API:
- primitive source-facing owner introduced here:
  `supremumProcessPairing 𝕜 XStar A u xStar = δᵛ[WithBotTop 𝕜](xStar | A.image ({u} : Set U))`;
- primitive reused owners: the fiber set `A.image ({u} : Set U)` and the indicator
  `δ[𝕜](· | A.image ({u} : Set U))`;
- derived API: the source-facing process-pairing versus indicator-pairing identity below.

Layer target: `source-facing`.

Notation evaluation:
- the source writes contextual bracket notation `⟨Au, x⋆⟩`, but this chapter already uses bracket
  notation for conjugate pairings;
- to avoid a second overloaded bracket surface with different owners and elaboration behavior, the
  source-facing public owner here is the explicit name `supremumProcessPairing`.
-/

namespace SetRel

section Pairing

variable {U : Type u} {X : Type v} {XStar : Type w}

/-- Definition 39.2.1: the supremum-oriented Chapter 39 process pairing `⟨Au, x⋆⟩` is the
support value of the fiber `Au` at `x⋆`. The dual carrier `XStar` is part of the owner because it
is not recoverable from `A : SetRel U X` alone. -/
abbrev supremumProcessPairing (𝕜 : Type*) [ConditionallyCompleteLattice 𝕜]
    (XStar : Type w) [HasPairing XStar X 𝕜] (A : SetRel U X) :
    U → XStar → WithBotTop 𝕜 :=
  fun u xStar ↦ δᵛ[WithBotTop 𝕜](xStar | A.image ({u} : Set U))

section Bridge

variable {𝕜 : Type*}
variable [ConditionallyCompleteLattice 𝕜]
variable [AddGroup 𝕜]
variable [HasPairing XStar X 𝕜] [HasPairing X XStar 𝕜] [HasPairingSwap X XStar 𝕜]

-- Proof sketch: this is exactly
-- `convexConjugate_indicatorFunction_eq_supportFunction_pointwise` specialized to the fiber
-- `A.image ({u} : Set U)`.
/-- The Chapter 39 process pairing is the convex pairing of the indicator slice of the
corresponding fiber. -/
theorem supremumProcessPairing_eq_convexPairing_indicator
    (A : SetRel U X) (u : U) (xStar : XStar) :
    supremumProcessPairing 𝕜 XStar A u xStar =
      (δ[𝕜](· | A.image ({u} : Set U)))⋆ xStar := by
  simpa [supremumProcessPairing] using
    (convexConjugate_indicatorFunction_eq_supportFunction_pointwise
      (E := X) (EStar := XStar) (α := 𝕜)
      (C := A.image ({u} : Set U)) (xStar := xStar)).symm

end Bridge

end Pairing

end SetRel

/-! ### Theorem_39_2 (from Chap08) -/
noncomputable section

open scoped Rockafellar SetRel

universe u v w z

namespace SetRel

/-!
Source/core/bridge triage for this item.

  a closed convex process, that `A**` is the ambient graph closure of `A`, and that the adjoint
  of the indicator bifunction of `A` is the negative indicator bifunction of `A*`.
- `core/canonical`: Chapter 39 already owns convex processes on `A : SetRel U X` via
  `A.IsConvexProcess 𝕜`, process adjoints via `A∗[XStar, UStar; 𝕜]`, and indicator-bifunction
  adjoints via `Bifunction.adjoint`; the source-facing indicator bifunction is the chapter's short
  canonical owner `indicatorFibers 𝕜 A`, so clause (3) is stated directly on that owner. This
  file also uses the relation-closure owner `cl(·)` instead of re-spelling graph closure
  pointwise. Clause (1) stays at the minimal forward pairing layer needed to form
  `A∗[XStar, UStar; 𝕜]`, together with the reverse-orientation linear/continuous pairing data
  needed to control the adjoint graph on the dual side. Clause (2) is stated at the real
  continuous-perfect-pairing bipolar owner layer supplied upstream in Chapter 14.
- `bridge/view`: no new wrapper owner is introduced; all three clauses are stated directly on the
  canonical adjoint owner and the Chapter 1 indicator notation.

Primary mathematical domain:
- convex processes, adjoint-process duality, and indicator-bifunction adjunction.

Domain-style sampling used here:
- `SetRel.IsConvexProcess` from `Chap08.Definition_39_0_1`;
- the process-adjoint owner/notation `A∗[XStar, UStar; 𝕜]` from `Chap08.Definition_39_0_14`;
- the Chapter 6 canonical bifunction surface
  `#check (fun u ↦ (δ[𝕜](· | S u)) : U → X → WithBotTop 𝕜)` from `Chap06.Definition_6_29_3`;
- `HasPairing`, `HasLinearPairing`, `HasContinuousPairing`, and `HasPairingSwap` from
  `Chap01.HasPairing`, with clause (1) using only the raw forward pairings plus the
  reverse-orientation linear/continuous/swap layer on the dual variables;
- `isClosed_polarCone` from `Chap03.Text_14_0_7`, which shows that codomain-side closedness is
  controlled by continuity in the dual variable;
- `polarCone_polarCone_eq_closure` from `Chap03.Text_14_0_4`, whose owner proof factors through
  the real continuous perfect-pairing class `IsContPerfPair`;
- `Bifunction.adjoint` from `Chap06.Definition_6_30_14`;
- `SetRel.closure` / `cl(·)` from `Chap08.Definition_39_0_5`;
- the Chapter 39 indicator-fiber owner `indicatorFibers 𝕜 A`.

Primitive data vs derived API:
- primitive source data: `A : SetRel U X`;
- primitive reused owners: `A∗[XStar, UStar; 𝕜]`, graph closure `cl(A)`, and
  `indicatorFibers 𝕜 A`;
- derived API: closedness/convexity of `A*`, the biconjugate-style identity `A** = cl(A)`,
  and the indicator-bifunction adjoint identity.

Topology owner decision:
- clause (2) intentionally stays on ambient `closure` of the full graph owner `A : SetRel U X`;
  no relative/intrinsic closure owner is introduced because the theorem compares whole graph sets
  in `U × X`.

Layer target: `source-facing`, on the pairing-level relation owners.

Ambient-layer split:
- clause (1) keeps only the raw forward pairings needed to form `A∗[XStar, UStar; 𝕜]`, together
  with the reverse-orientation linear/continuous/swap layer needed to make the defining dual-side
  half-spaces closed and to transport convex-cone structure to the adjoint graph;
- clause (2) is intentionally specialized to the real continuous-perfect-pairing layer because the
  chapter's canonical bipolar owner `polarCone_polarCone_eq_closure` lives there; it keeps the
  continuous perfect-pairing class on the product graph pairing, together with the
  reverse-orientation pairings needed to form `A**`.
-/

section AdjointClosedConvex

variable {𝕜 : Type*}
variable [CommRing 𝕜] [PartialOrder 𝕜] [TopologicalSpace 𝕜] [ClosedIciTopology 𝕜]
variable [IsOrderedRing 𝕜]

variable {U : Type u}
variable [AddCommMonoid U] [Module 𝕜 U] [TopologicalSpace U]

variable {X : Type v}
variable [AddCommMonoid X] [Module 𝕜 X] [TopologicalSpace X]

variable {UStar : Type w}
variable [AddCommMonoid UStar] [Module 𝕜 UStar] [TopologicalSpace UStar]

variable {XStar : Type z}
variable [AddCommMonoid XStar] [Module 𝕜 XStar] [TopologicalSpace XStar]

variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]
variable [HasLinearPairing UStar U 𝕜] [HasContinuousPairing UStar U 𝕜] [HasPairingSwap U UStar 𝕜]
variable [HasLinearPairing XStar X 𝕜] [HasContinuousPairing XStar X 𝕜] [HasPairingSwap X XStar 𝕜]

-- Proof sketch: identify the graph of `A∗[XStar, UStar; 𝕜]` with a pairing-polar graph cone of
-- `A`, now read in the reverse pairing orientation on the dual variables. The reverse-orientation
-- continuity makes the defining half-spaces closed, and the reverse-orientation linearity
-- transports convex-cone structure back to the adjoint relation.
/-- Theorem 39.2 (1): the adjoint relation `A*` of a convex process `A` is a closed convex
process: its graph is closed, and it is again a convex process. -/
theorem isClosed_and_isConvexProcess_adjoint
    {A : SetRel U X} (hA : A.IsConvexProcess 𝕜) :
    (A∗[XStar, UStar; 𝕜]).IsClosed ∧
      (A∗[XStar, UStar; 𝕜]).IsConvexProcess 𝕜 := sorry

end AdjointClosedConvex

section LinearContinuousPairingDuality

variable {U : Type u}
variable [NormedAddCommGroup U] [NormedSpace ℝ U]

variable {X : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]

variable {UStar : Type w}
variable [NormedAddCommGroup UStar] [NormedSpace ℝ UStar]

variable {XStar : Type z}
variable [NormedAddCommGroup XStar] [NormedSpace ℝ XStar]

variable [HasLinearPairing U UStar ℝ] [HasLinearPairing X XStar ℝ]

section Biadjoint

variable [HasLinearPairing UStar U ℝ] [HasLinearPairing XStar X ℝ]
variable [HasPairingSwap U UStar ℝ] [HasPairingSwap X XStar ℝ]
variable
  [((HasLinearPairing.pairingLinear :
      (U × X) →ₗ[ℝ] (UStar × XStar) →ₗ[ℝ] ℝ)).IsContPerfPair]

-- Proof sketch: identify one adjoint with a pairing-polar graph cone and apply bipolarity at the
-- product graph-pairing owner level. The continuous perfect-pairing hypothesis is the chapter's
-- canonical bipolarity layer, and the resulting graph equality is then translated back to `SetRel`.
/-- Theorem 39.2 (2): under compatible reverse pairings and a continuous perfect pairing on the
ambient graph pairing, the double adjoint of a convex process is its ambient graph closure. -/
theorem adjoint_adjoint_eq_closure
    {A : SetRel U X} (hA : A.IsConvexProcess ℝ) :
    (A∗[XStar, UStar; ℝ])∗[U, X; ℝ] = cl(A) := sorry

end Biadjoint

end LinearContinuousPairingDuality

section IndicatorAdjoint

variable {𝕜 : Type*}
variable [AddCommGroup 𝕜] [ConditionallyCompleteLinearOrder 𝕜]
variable {U : Type u} {X : Type v} {UStar : Type w} {XStar : Type z}
variable [Neg UStar]
variable [HasPairing U UStar 𝕜] [HasPairing X XStar 𝕜]

-- Proof sketch: expand `Bifunction.adjoint` on the canonical indicator-fiber owner
-- `indicatorFibers 𝕜 A`. The finiteness condition for the conjugate is exactly membership in
-- `A∗[XStar, UStar; 𝕜]`, yielding the negative indicator-fiber owner of the adjoint relation.
/-- Theorem 39.2 (3): the adjoint of the indicator bifunction of `A` is the negative indicator
bifunction of `A*` (the opposite-orientation indicator formula). -/
theorem adjointFunction_indicator_eq_neg_indicator_adjoint
    (A : SetRel U X) :
    (indicatorFibers 𝕜 A)⋆ =
      -(indicatorFibers 𝕜 (A∗[XStar, UStar; 𝕜])) := sorry

end IndicatorAdjoint

end SetRel
