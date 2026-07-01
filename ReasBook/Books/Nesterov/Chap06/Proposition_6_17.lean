import Nesterov.Chap02.Definition_2_32
import Nesterov.Chap06.Definition_6_16

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Metric
open scoped BigOperators SeminormOperatorNorm

universe u v

variable {ι : Type v}

/- Proposition 6.17 lies in the induced operator-norm domain for the weighted tuple geometry of
the continuous location model.

Sampled owner declarations:
* `Seminorm.primalDualOperatorNorm`, the chapter owner for induced norms between source and target
  seminorm geometries;
* `Seminorm.primalDualOperatorNorm_eq_sSup_dualPairing`, the owner-side source formula for the
  two-ball pairing supremum;
* `continuousLocationSmoothingMap`, the chapter owner for the weighted pairing
  `(x, u) ↦ ∑_j m_j ⟪u_j, x⟫`;
* `continuousLocationDualTupleNorm`, the source-facing weighted tuple norm on `ι → E`.

Best owner abstraction:
* source-facing: the textbook supremum of `∑_j m_j ⟪u_j, x⟫` over unit vectors `x` in the ambient
  real inner-product space `E` and weighted-dual unit tuples `u : ι → E`;
* core/canonical: `Seminorm.primalDualOperatorNorm` applied to the `PiLp`-transport of
  `continuousLocationSmoothingMap E weights` and the pullback seminorm
  `continuousLocationDualTupleSeminorm E weights`;
* bridge/view kept in this file: the weighted scaling map on `PiLp 2 (fun _ : ι ↦ E)` and the
  transported smoothing operator `continuousLocationSmoothingMapPiLp E weights`.

Primitive data:
* the population weights `weights`;
* the ambient real inner-product space `E`;
* the weighted tuple scaling linear map on `PiLp 2 (fun _ : ι ↦ E)`.

Derived API:
* the pairing map `continuousLocationSmoothingMap`;
* the transported pairing map `continuousLocationSmoothingMapPiLp`;
* the pullback seminorm owner `continuousLocationDualTupleSeminorm`;
* the canonical primal-dual operator norm of `continuousLocationSmoothingMap`;
* the source-facing sphere formula of Proposition 6.17 as a thin bridge.
-/

section Scale

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "E₂" => PiLp 2 fun _ : ι ↦ E

/-- The componentwise scaling `u_j ↦ √m_j • u_j` on the Hilbert product
`PiLp 2 (fun _ : ι ↦ E)` behind the weighted tuple geometry. -/
def continuousLocationDualTupleScale
    (E : Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (weights : ContinuousLocationWeights ι) :
    PiLp 2 (fun _ : ι ↦ E) →L[ℝ] PiLp 2 (fun _ : ι ↦ E) :=
  (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ E)).symm.toContinuousLinearMap) :
      (ι → E) →L[ℝ] PiLp 2 (fun _ : ι ↦ E)).comp
    ((ContinuousLinearMap.pi fun j ↦
      Real.sqrt (weights j : ℝ) • PiLp.proj 2 (fun _ : ι ↦ E) j) :
      PiLp 2 (fun _ : ι ↦ E) →L[ℝ] (ι → E))

/-- The `j`-th coordinate of `continuousLocationDualTupleScale E weights u` is
`√m_j • u_j`. -/
theorem continuousLocationDualTupleScale_apply
    (weights : ContinuousLocationWeights ι) (u : E₂) (j : ι) :
    continuousLocationDualTupleScale E weights u j =
      Real.sqrt (weights j : ℝ) • u j := by
  simp [continuousLocationDualTupleScale]

end Scale

section Geometry

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [Fintype ι]

local notation "E₂" => PiLp 2 fun _ : ι ↦ E

/-- The weighted tuple geometry of Proposition 6.17, owned canonically as the pullback of the
ambient Hilbert norm on `PiLp 2 (fun _ : ι ↦ E)` along `continuousLocationDualTupleScale
E weights`. -/
def continuousLocationDualTupleSeminorm
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (weights : ContinuousLocationWeights ι) : Seminorm ℝ (PiLp 2 fun _ : ι ↦ E) :=
  Seminorm.comp
    (normSeminorm ℝ (PiLp 2 fun _ : ι ↦ E))
    (continuousLocationDualTupleScale E weights).toLinearMap

/-- Evaluating `continuousLocationDualTupleSeminorm E weights` gives the ambient norm of the
weighted scaling of the tuple. -/
theorem continuousLocationDualTupleSeminorm_eq_norm_scale
    (weights : ContinuousLocationWeights ι) (u : E₂) :
    continuousLocationDualTupleSeminorm E weights u =
      ‖continuousLocationDualTupleScale E weights u‖ :=
  rfl

/-- The seminorm owner `continuousLocationDualTupleSeminorm E weights` recovers the textbook
weighted tuple norm `continuousLocationDualTupleNorm E weights` after identifying coordinate
tuples with the Hilbert product `PiLp 2 (fun _ : ι ↦ E)`. -/
theorem continuousLocationDualTupleSeminorm_apply
    (weights : ContinuousLocationWeights ι) (u : ι → E) :
    continuousLocationDualTupleSeminorm E weights (WithLp.toLp 2 u) =
      continuousLocationDualTupleNorm E weights u := by
  sorry

/-- Positive weights make the pullback seminorm `continuousLocationDualTupleSeminorm E weights`
nondegenerate, so the weighted tuple geometry is a genuine norm. -/
instance continuousLocationDualTupleSeminorm.isNorm
    (weights : ContinuousLocationWeights ι) :
    Seminorm.IsNorm (continuousLocationDualTupleSeminorm E weights : Seminorm ℝ E₂) := by
  sorry

/-- The canonical `PiLp` transport of `continuousLocationSmoothingMap E weights`, viewed in the
weighted tuple geometry on `PiLp 2 (fun _ : ι ↦ E)`. This is a thin bridge from the
source-facing coordinate-tuple owner to the Hilbert-product realization used by
`continuousLocationDualTupleSeminorm E weights`. -/
abbrev continuousLocationSmoothingMapPiLp
    (E : Type u) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (weights : ContinuousLocationWeights ι) :=
  (ContinuousLinearMap.precomp ℝ
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ E)).toContinuousLinearMap).comp
    (continuousLocationSmoothingMap E weights)

/-- Evaluating the transported smoothing operator on a `PiLp` tuple recovers the same weighted
pairing formula as `continuousLocationSmoothingMap_apply`. -/
theorem continuousLocationSmoothingMapPiLp_apply
    (weights : ContinuousLocationWeights ι) (x : E) (u : E₂) :
    continuousLocationSmoothingMapPiLp E weights x u =
      ∑ j, (weights j : ℝ) * inner ℝ (u j) x := by
  simpa [continuousLocationSmoothingMapPiLp] using
    continuousLocationSmoothingMap_apply weights x
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : ι ↦ E)).toContinuousLinearMap u)

/-- Canonical owner form of Proposition 6.17: the induced norm of the continuous-location
smoothing map from the ambient norm on `E` to the weighted dual-tuple geometry is `√P`, where
`P = \sum_j m_j` is the total population weight. The `PiLp` realization is exposed through the
thin bridge `continuousLocationSmoothingMapPiLp E weights`, so the public theorem stays on
`Seminorm.primalDualOperatorNorm` without leaking the transport term. -/
theorem continuousLocationSmoothingMap_primalDualOperatorNorm_eq_sqrt_totalPopulation
    [FiniteDimensional ℝ E] [Nontrivial E] (weights : ContinuousLocationWeights ι) :
    ‖(continuousLocationSmoothingMapPiLp E weights).toLinearMap‖[
        normSeminorm ℝ E ⇀ continuousLocationDualTupleSeminorm E weights,*] =
      Real.sqrt (continuousLocationTotalPopulation weights) := by
  sorry

/-- Proposition 6.17: rewriting the canonical induced-norm statement through
`continuousLocationSmoothingMap_primalDualOperatorNorm_eq_sqrt_totalPopulation`,
`Seminorm.primalDualOperatorNorm_eq_sSup_dualPairing`, `continuousLocationSmoothingMap_apply`, and
`continuousLocationDualTupleSeminorm_apply`, and then transporting back along
`PiLp.continuousLinearEquiv`, gives the source-facing unit-sphere formula for the weighted
pairing. -/
theorem continuousLocation_sSup_pairing_unitSpheres_eq_sqrt_totalPopulation
    [FiniteDimensional ℝ E] [Nontrivial E] (weights : ContinuousLocationWeights ι) :
    sSup ((fun xu : E × (ι → E) ↦ ∑ j, (weights j : ℝ) * inner ℝ (xu.2 j) xu.1) ''
      Set.prod (sphere (0 : E) 1) {u | continuousLocationDualTupleNorm E weights u = 1}) =
      Real.sqrt (continuousLocationTotalPopulation weights) := by
  sorry

end Geometry

end
