import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_29_8
import ConvexAnalysis_Rockafellar_1970.Chap06.Definition_6_30_14
import ConvexAnalysis_Rockafellar_1970.Chap07.Definition33_0_31
import ConvexAnalysis_Rockafellar_1970.Chap07.Defn_34_2

noncomputable section

universe u v u' v' w

open scoped Rockafellar

namespace Bifunction

section Owner

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {L : Type w}
variable [Sub L] [Neg L] [SupSet L] [InfSet L]
variable [Neg UStar]
variable [HasPairing U UStar L] [HasPairing X XStar L]
variable [HasPairing (U × X) (UStar × XStar) L]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Proposition 38.7.2 studies co-finite convex bifunctions through the global
  agreement of the two Chapter 34 pairing representatives attached to `F`.
- `core/canonical`: the upstream owner layer already provides the global pairing owners
  `Bifunction.lowerPairing` and `Bifunction.upperAdjointPairing`, together with the pointwise
  owner `Bifunction.PairingEquationAt`, the adjoint owner `Bifunction.adjoint`, the
  slice-domain owner `Bifunction.dom`, and the closed-convex owner `Bifunction.IsClosedConvex`.
- `bridge/view`: this file owns only the source-facing property owner `Bifunction.IsCofinite`,
  whose primitive field is the canonical global owner equality
  `lowerPairing XStar F = upperAdjointPairing XStar UStar F`; the universal Chapter 33
  pairing-equation formulation is derived API.

Primary mathematical domain:
- convex bifunction duality and co-finiteness via adjoint-slice pairings.

Domain-style sampling used here:
- `Bifunction.lowerPairing` and `Bifunction.upperAdjointPairing` from `Chap07.Defn_34_2`;
- `Bifunction.adjoint` from `Chap06.Definition_6_30_14`;
- `Bifunction.PairingEquationAt` from `Chap07.Definition33_0_31`;
- `Bifunction.dom` from `Chap06.Definition_6_29_8`;
- `Bifunction.IsClosedConvex` from `Chap07.Defn_34_2`.

Primitive data vs derived API:
- primitive source data: a bifunction `F : U → X → L`;
- primitive global owners reused here: `Bifunction.lowerPairing XStar F` and
  `Bifunction.upperAdjointPairing XStar UStar F`;
- primitive global owner introduced here: the reusable property class
  `Bifunction.IsCofinite XStar UStar F`, defined directly by equality of those two canonical
  pairing maps and keeping the dual ambient types explicit because they are not recoverable from
  `F` alone;
- derived pointwise API: `Bifunction.PairingEquationAt F u xStar`;
- derived API: adjoint stability of co-finiteness, the graph-properness bridge needed by
  Section 38.2, and the closed-convex/full-domain characterization.

Layer target: `source-facing`.
-/

/-- A convex bifunction is co-finite when its two canonical Chapter 34 pairing representatives
agree globally. -/
@[mk_iff isCofinite_iff]
class IsCofinite (XStar : Type v') (UStar : Type u')
    [Neg UStar] [HasPairing U UStar L] [HasPairing X XStar L]
    [HasPairing (U × X) (UStar × XStar) L] (F : U → X → L) : Prop where
  lowerPairing_eq_upperAdjointPairing :
    lowerPairing XStar F = upperAdjointPairing XStar UStar F

/-- The global Chapter 34 owner equality defining co-finiteness specializes pointwise to the
Chapter 33 pairing equation. -/
theorem IsCofinite.pairingEquationAt {F : U → X → L} (hF : IsCofinite XStar UStar F)
    (u : U) (xStar : XStar) :
    PairingEquationAt F u xStar := by
  simpa [PairingEquationAt, lowerPairing_apply, upperAdjointPairing_apply] using
    congrFun (congrFun hF.lowerPairing_eq_upperAdjointPairing u) xStar

/-- Companion pointwise form of co-finiteness: the canonical global owner equality is equivalent
to the universal Chapter 33 pairing equation. -/
theorem isCofinite_iff_forall_pairingEquationAt {F : U → X → L} :
    IsCofinite XStar UStar F ↔ ∀ u : U, ∀ xStar : XStar, PairingEquationAt F u xStar := by
  constructor
  · intro hF u xStar
    exact hF.pairingEquationAt u xStar
  · intro hF
    rw [isCofinite_iff XStar UStar F]
    funext u xStar
    simpa [PairingEquationAt, lowerPairing_apply, upperAdjointPairing_apply] using hF u xStar

end Owner

section Adjoint

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'} {L : Type w}
variable [Sub L] [Neg L] [SupSet L] [InfSet L]
variable [Neg UStar] [Neg X]
variable [HasPairing U UStar L] [HasPairing X XStar L]
variable [HasPairing UStar U L] [HasPairing XStar X L]
variable [HasPairing (U × X) (UStar × XStar) L]
variable [HasPairing (XStar × UStar) (X × U) L]

-- Proof sketch: invoke the Chapter 33 symmetry theorem pointwise on the adjoint slices, then
-- reassemble the resulting equations into the canonical owner equality
-- `lowerPairing = upperAdjointPairing`.
/-- The adjoint of a co-finite convex bifunction is again co-finite. -/
theorem isCofinite_adjointFunction_of_isCofinite
    {F : U → X → L} (hF : IsCofinite XStar UStar F) :
    IsCofinite U X (adjoint XStar UStar F) := by
  sorry

end Adjoint

section Characterization

variable {U : Type u} {X : Type v} {UStar : Type u'} {XStar : Type v'}
variable [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
variable [NormedAddCommGroup UStar] [NormedSpace ℝ UStar] [FiniteDimensional ℝ UStar]
variable [NormedAddCommGroup XStar] [NormedSpace ℝ XStar] [FiniteDimensional ℝ XStar]
variable [HasLinearPairing U UStar ℝ] [HasContinuousPairing U UStar ℝ]
variable [HasLinearPairing X XStar ℝ] [HasContinuousPairing X XStar ℝ]
variable {F : U → X → WithBotTop ℝ}

local notation "F⋆" => (adjoint XStar UStar F : XStar → UStar → WithBotTop ℝ)

-- Proof sketch: Proposition 38.7.2 forces `dom F = Set.univ`, so the graph function has a
-- finite point over `u = 0`, while the Chapter 33 pairing equation rules out any `⊥`-value on
-- the graph. This is exactly the graph-properness owner reused by Theorem 38.2.
/-- Bridge/view lemma for Proposition 38.7.3: a closed convex co-finite bifunction has proper
graph function in the Chapter 6 owner sense `(Function.uncurry F).IsProper`. -/
theorem uncurry_isProper_of_isClosedConvex_of_isCofinite
    (hF : IsClosedConvex F) (hcof : IsCofinite XStar UStar F) :
    (Function.uncurry F).IsProper := by
  sorry

-- Proof sketch: if `F` is co-finite, the global pairing equation excludes any missing point in
-- either the primal domain or the Chapter 33 adjoint-side source domain `dom (-F⋆)`.
-- Conversely, for a closed convex bifunction, the Chapter 34
-- closure theory upgrades the two full-domain hypotheses to the universal pairing equation.
/-- Proposition 38.7.2: for a closed convex bifunction `F`, co-finiteness is equivalent to the
full-domain conditions on the primal source domain and the adjoint-side source domain, rendered
here in the established Chapter 33/34 owner language as `dom F = Set.univ` and
`dom (-F⋆) = Set.univ`. -/
theorem isCofinite_iff_dom_eq_univ_and_dom_neg_adjointFunction_eq_univ
    (hF : IsClosedConvex F) :
    IsCofinite XStar UStar F ↔
      dom F = Set.univ ∧
        dom (-F⋆) = Set.univ := by
  sorry

end Characterization

end Bifunction
