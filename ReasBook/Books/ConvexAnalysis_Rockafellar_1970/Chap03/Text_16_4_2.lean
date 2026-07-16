import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap01.Definition_2_1_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_1
import ConvexAnalysis_Rockafellar_1970.Chap01.Defintion_4_8_2
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_1_6
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_4_0
import ConvexAnalysis_Rockafellar_1970.Chap01.Text_5_5_0_5

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open scoped Rockafellar

section

variable {ι κ 𝕜 : Type*} [Fintype ι]
variable [CommRing 𝕜] [ConditionallyCompleteLinearOrder 𝕜]

local notation "E" => ι → 𝕜
local notation "D" => (coordinateL1Ball : Set E)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 16.4.2 fixes a finite family `a : κ → E`, with `E = ι → 𝕜`, and studies
  the function
  `x ↦ inf {‖x - ∑ t c t • a t‖∞ | c : κ → 𝕜}` together with the dual set `D ∩ Lᗮₚ`.
- `core/canonical`: the owner abstractions already present in the project are
  `coordinateL1Ball`, `linftyNorm`, `Submodule.span`, `Submodule.pairingOrthogonal`,
  `infimal_convolution`, `indicator`, `supportFunction`, and `Set.IsPolyhedral`.
- `bridge/view`: the source's coordinate tuple `(ξ₁, …, ξ_m)` is a coefficient function
  `c : κ → 𝕜`; the source dual set is rendered by `linftyApproximationDualSet`.

Primitive data vs derived API:
- primitive inputs: the family `a : κ → E`, the canonical set owner `coordinateL1Ball`, and the
  pairing annihilator of the span;
- owner-level function data: `linftyDistanceToSpan` is stated directly as an infimal-convolution
  owner on the chapter codomain layer `WithBotTop 𝕜`, rather than through a private bridge;
- derived API: the coordinate `sInf` companion formula, polyhedrality, and the support-function
  identity.

Layer target: `source-facing`, with the main function owner now at the codomain layer
`WithBotTop 𝕜` and scalar layer `𝕜`, specialized to textbook `ℝ^n` by taking `𝕜 = ℝ` and
finite index types.
-/

private def spanFamily (a : κ → E) : Submodule 𝕜 E :=
  Submodule.span 𝕜 (Set.range a)

/-- The explicit dual set from Text 16.4.2, with canonical owner `D ∩ Lᗮₚ`,
where `D = coordinateL1Ball` and `L` is the span of the family `a`. -/
def linftyApproximationDualSet (a : κ → E) : Set E :=
  {x | x ∈ D ∧ x ∈ (spanFamily a)ᗮₚ}

/-- Canonical owner for the source function in Text 16.4.2: the infimal convolution of the
support function of `D` and the indicator of `spanFamily a`. -/
def linftyDistanceToSpan (a : κ → E) : E → WithBotTop 𝕜 :=
  infimal_convolution
    (δᵛ[WithBotTop 𝕜](· | D))
    (δ[𝕜](· | spanFamily a))

/-- Unfolding form of `linftyDistanceToSpan` at the canonical owner layer. -/
theorem linftyDistanceToSpan_def (a : κ → E) :
    linftyDistanceToSpan a =
      infimal_convolution
        (δᵛ[WithBotTop 𝕜](· | D))
        (δ[𝕜](· | spanFamily a)) :=
  rfl

/-- Source-facing coordinate companion for Text 16.4.2:
`linftyDistanceToSpan` agrees pointwise with
`x ↦ inf {‖x - ∑ t c t • a t‖∞ | c : κ → 𝕜}`. -/
theorem linftyDistanceToSpan_eq_sInf_coefficients [Fintype κ] (a : κ → E) (x : E) :
    linftyDistanceToSpan a x =
      sInf
        (Set.range fun c : κ → 𝕜 ↦
          ((linftyNorm (x - ∑ t, c t • a t) : 𝕜) : WithBotTop 𝕜)) := by
  sorry

-- Proof sketch: `D = coordinateL1Ball` is polyhedral convex by coordinate half-space inequalities,
-- and `spanFamily a` is a linear subspace, so its pairing annihilator is a linear-equality slice;
-- finite intersections of polyhedral sets are polyhedral.
/-- The explicit dual set from Text 16.4.2 is polyhedral convex. -/
theorem linftyApproximationDualSet_isPolyhedral (a : κ → E) :
    (linftyApproximationDualSet a).IsPolyhedral 𝕜 := by
  sorry

/-- The coordinate `ℓ¹` unit ball is polyhedral convex. This is the empty-family specialization of
Text 16.4.2's dual-set construction. -/
theorem coordinateL1Ball_isPolyhedral :
    (coordinateL1Ball : Set E).IsPolyhedral 𝕜 := by
  sorry

-- Proof sketch: combine `linftyDistanceToSpan_def` with the finite infimal-convolution conjugacy
-- pattern from Section 16 and the indicator-conjugate bridge for pairing annihilators, yielding
-- the support function of `D ∩ Lᗮₚ`.
/-- Text 16.4.2 at the canonical codomain layer: for a family `a : κ → (ι → 𝕜)`, and hence in
particular for finite real coordinates, the source function
`x ↦ inf {‖x - ∑ t c t • a t‖∞ | c : κ → 𝕜}` is the support function of
`linftyApproximationDualSet a = D ∩ Lᗮₚ`. -/
theorem supportFunction_linftyApproximationDualSet_eq_linftyDistanceToSpan (a : κ → E) :
    (δᵛ[WithBotTop 𝕜](· | linftyApproximationDualSet a) : E → WithBotTop 𝕜) =
      linftyDistanceToSpan a := by
  sorry

end
