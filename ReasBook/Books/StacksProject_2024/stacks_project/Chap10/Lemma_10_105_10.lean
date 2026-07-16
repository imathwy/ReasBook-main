import Mathlib
import StacksProject_2024.stacks_project.Chap05.Definition_5_20_1
import StacksProject_2024.stacks_project.Chap10.Lemma_10_105_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

/- Domain-style sampling in the catenary/dimension-function API:
- ring owner: `IsCatenaryRing A`
- topological owner: `IsDimensionFunction δ`
- bridge/view: the source function `p ↦ dim (A / p)` on `Spec A`, expressed here through
  `ringKrullDim (A ⧸ p.asIdeal)`

Layer triage:
- `source-facing`: Lemma 10.105.10 is the local Noetherian criterion for catenarity
- `core/canonical`: the owner abstractions are already `IsCatenaryRing` and `IsDimensionFunction`
- `bridge/view`: the quotient-dimension function is derived API and should stay scoped to the
  Noetherian-local setting of the theorem, rather than as a global owner declaration

Primitive data belongs to the existing owner abstractions. The quotient-dimension expression is
kept inline below because `ringKrullDim` is `WithBot`-valued in general, so truncating it with
`unbotD 0` is only source-faithful in the finite-dimensional local setting of this lemma.
-/

-- Proof sketch: for the forward implication, transport catenarity from prime-ideal intervals to the
-- specialization order on `Spec A` and use the local-ring codimension formula at the closed point to
-- identify the resulting dimension function with `p ↦ dim (A / p)`. For the reverse implication,
-- apply the dimension-function criterion for catenarity on the prime spectrum and translate back to
-- the ring-theoretic formulation.
/-- Lemma 10.105.10: for a Noetherian local ring, the ring is catenary if and only if the function
`p ↦ dim (A / p)` is a dimension function on `Spec A`. -/
theorem isCatenaryRing_iff_primeQuotientKrullDimension_isDimensionFunction
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] :
    IsCatenaryRing A ↔
      IsDimensionFunction
        (fun p : PrimeSpectrum A ↦ (((ringKrullDim (A ⧸ p.asIdeal)).unbotD 0).toNat : ℤ)) := sorry
