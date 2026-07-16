import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_5
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_12
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_22

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators GaugePolar RealInnerProductSpace

universe u

section

variable {E : Type u}

/-- The reusable source expression `(p f)^(1/p)` attached to an extended-real-valued function `f`.
On nonnegative finite values this is `((p * f(x)) : ℝ)^(1/p)`, while negative values and `⊤` are
sent to `⊤`. -/
def powerGaugeTransform (p : ℝ) (f : E → EReal) : E → EReal :=
  fun x ↦
    if f x < 0 then
      ⊤
    else if f x = ⊤ then
      ⊤
    else
      ((Real.rpow (p * (f x).toReal) (1 / p) : ℝ) : EReal)

-- Proof sketch: under the nonnegativity and finiteness hypotheses, the negative branch and the
-- `⊤` branch in `powerGaugeTransform` are both excluded, so only the explicit real `rpow` formula
-- remains.
/-- On a nonnegative finite value of `f`, the transform `(p f)^(1/p)` is given by the expected
real power formula. -/
theorem powerGaugeTransform_apply_of_nonneg_lt_top
    {p : ℝ} {f : E → EReal} {x : E}
    (hx_nonneg : 0 ≤ f x) (hx_top : f x < ⊤) :
    powerGaugeTransform p f x =
      ((Real.rpow (p * (f x).toReal) (1 / p) : ℝ) : EReal) := sorry

end

section

variable {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

/-- A closed gauge is a gauge that is also lower semicontinuous. -/
class IsClosedGauge (k : E → EReal) : Prop extends IsGauge k where
  lowerSemicontinuous : LowerSemicontinuous k

end

section

variable {ι : Type*} [Fintype ι]

local notation "E" => EuclideanSpace ℝ ι

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.24 specializes the Chapter 15 polarity theory to the concrete
  coordinate `ℓ_p` gauge
  `x ↦ (|ξ₁|^p + ··· + |ξₙ|^p)^(1/p)` and identifies its polar with the dual `ℓ_q` gauge.
  The public owner lives on the finite-coordinate layer `EuclideanSpace ℝ ι`, with the textbook
  `R^n` statement recovered by `ι = Fin n`.
- `core/canonical`: the owner abstractions already used in nearby Chapter 15 items are
  `lpCoordinatePower`, `powerGaugeTransform`, `IsClosedGauge`, `IsGaugeNorm`, and
  `gauge_polar`.
- `bridge/view`: `powerGaugeTransform` is the reusable owner for expressions of the form
  `(p f)^(1/p)`, while the concrete coordinate formula remains the primitive source-facing gauge
  and is related to the earlier owner `lpCoordinatePower` by the thin bridge theorem
  `lpCoordinateGauge_eq_powerGaugeTransform_lpCoordinatePower`.

Domain-style sampling used here:
- `lpCoordinatePower` and its closed proper convexity statement from Text 15.0.22;
- `lpCoordinatePower_convexConjugate_eq` from Text 15.0.23;
- the reusable transform `(p f)^(1/p)`, introduced here as `powerGaugeTransform` and reused
  downstream in Corollary 15.3.2;
- `IsGaugeNorm` from Text 15.0.12 as the chapter owner for norm-gauges.
- `coordinateL1Gauge` from Text 15.0.13, showing the same finite-coordinate owner level for
  coordinate gauges.

Primitive data vs derived API:
- primitive bridge datum: the reusable transform `powerGaugeTransform p f`;
- primitive source-facing object: the explicit coordinate gauge `lpCoordinateGauge ι p`;
- primitive upstream owner reused by a bridge theorem: `lpCoordinatePower E ι p`;
- derived outputs: the concrete coordinate formula for `lpCoordinateGauge`, its closed-gauge
  structure, the explicit `ℓ_q` polar formula, and the fact that both the primal and dual gauges
  are norm-gauges.

Layer target:
- the main `ℓ_p` declarations remain `source-facing`, stated directly for the explicit coordinate
  gauge rather than via an auxiliary package or wrapper;
- the ambient owner is refined upward from the concrete display model `Fin n` to the canonical
  finite-family layer already used by `lpCoordinatePower` and `coordinateL1Gauge`;
- the reusable bridge owner `powerGaugeTransform` is reused explicitly instead of motivating any
  parallel local transform API.
-/

/-- The coordinate `ℓ_p` gauge on a finite coordinate space, viewed as an `EReal`-valued
function. Specializing `ι = Fin n` recovers the textbook function on `R^n`. -/
def lpCoordinateGauge (ι : Type*) [Fintype ι] (p : ℝ) : EuclideanSpace ℝ ι → EReal :=
  fun x ↦ ((Real.rpow (∑ i : ι, |x i| ^ p) (1 / p) : ℝ) : EReal)

-- Proof sketch: unfold `lpCoordinateGauge`; this is exactly its defining coordinate formula.
/-- Evaluating `lpCoordinateGauge ι p` at `x` gives the `p`-root of the sum of the `p`th powers of
the coordinate absolute values. -/
@[simp] theorem lpCoordinateGauge_apply (p : ℝ) (x : E) :
    lpCoordinateGauge ι p x =
      ((Real.rpow (∑ i : ι, |x i| ^ p) (1 / p) : ℝ) : EReal) := rfl

-- Proof sketch: for `f = (lpCoordinatePower E ι p).toEReal`, Text 15.0.22 gives
-- `f x = ((1 / p) * ∑ i, |x i| ^ p : ℝ)`. When `0 < p`, this value is nonnegative and finite, so
-- `powerGaugeTransform_apply_of_nonneg_lt_top` reduces `powerGaugeTransform p f x` to the explicit
-- real `rpow` formula. The scalar factor `p * (1 / p)` then simplifies to `1`, recovering exactly
-- the defining coordinate expression of `lpCoordinateGauge ι p`.
/-- For positive exponents, the coordinate `ℓ_p` gauge is exactly the Chapter 15 owner
`powerGaugeTransform` applied to the coordinate power-sum owner `lpCoordinatePower`. Negative
exponents are excluded because `lpCoordinatePower E ι p` takes negative values away from the origin,
so the transform enters its `⊤` branch there. -/
theorem lpCoordinateGauge_eq_powerGaugeTransform_lpCoordinatePower
    {p : ℝ} (hp : 0 < p) :
    lpCoordinateGauge ι p = powerGaugeTransform p (lpCoordinatePower E ι p).toEReal := sorry

-- Proof sketch: apply Corollary 15.3.2 to the function
-- `x ↦ ((1 / p) * ∑ i, |x i| ^ p : ℝ)`, using Text 15.0.22 for closed proper convexity and
-- degree-`p` homogeneity. Then rewrite the resulting owner
-- `powerGaugeTransform p (lpCoordinatePower E ι p).toEReal` by the bridge theorem
-- `lpCoordinateGauge_eq_powerGaugeTransform_lpCoordinatePower`.
/-- The coordinate `ℓ_p` gauge is a closed gauge for `1 < p` on any finite coordinate space, hence
in particular on `R^n`. -/
theorem lpCoordinateGauge_isClosedGauge
    {p : ℝ} (hp : 1 < p) :
    IsClosedGauge (lpCoordinateGauge ι p) := sorry

-- Proof sketch: the coordinate `ℓ_p` formula is finite everywhere, even under `x ↦ -x`, and
-- positive away from the origin because some coordinate of a nonzero vector has strictly positive
-- absolute value. Together with the closed-gauge structure above and the standard convexity and
-- positive-homogeneity of the `ℓ_p` norm, this supplies the fields of `IsGaugeNorm`.
/-- The coordinate `ℓ_p` gauge is a norm-gauge for `1 < p`. -/
theorem lpCoordinateGauge_isGaugeNorm
    {p : ℝ} (hp : 1 < p) :
    IsGaugeNorm (lpCoordinateGauge ι p) := sorry

-- Proof sketch: apply Corollary 15.3.2 to the concrete power-sum profile from Text 15.0.22 and
-- rewrite both the primal and dual owners by
-- `lpCoordinateGauge_eq_powerGaugeTransform_lpCoordinatePower` together with
-- `lpCoordinatePower_convexConjugate_eq`. The Hölder-conjugacy hypothesis already gives `1 < p`,
-- so this identifies the polar of the `ℓ_p` coordinate gauge with the `ℓ_q` coordinate gauge as
-- an equality of owners.
/-- Text 15.0.24: if `p.HolderConjugate q`, then the coordinate `ℓ_p` gauge
`x ↦ (|ξ₁|^p + ··· + |ξₙ|^p)^(1/p)` is a closed gauge whose polar is the coordinate `ℓ_q` gauge
`x⋆ ↦ (|ξ₁⋆|^q + ··· + |ξₙ⋆|^q)^(1/q)`. -/
theorem gauge_polar_lpCoordinateGauge_eq_dualLpCoordinateGauge
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    (lpCoordinateGauge ι p)ᵒ = lpCoordinateGauge ι q := sorry

-- Proof sketch: interchange the Hölder-conjugate exponents in the previous polar formula. The
-- canonical norm-gauge owner for `lpCoordinateGauge ι q` is `lpCoordinateGauge_isGaugeNorm`
-- applied to `hpq.symm.lt`, so its polar is again a norm-gauge and the previous owner equality
-- recovers the original gauge.
/-- The coordinate `ℓ_p` and `ℓ_q` gauges form a mutual polar pair. -/
theorem gauge_polar_dualLpCoordinateGauge_eq_lpCoordinateGauge
    {p q : ℝ} (hpq : p.HolderConjugate q) :
    (lpCoordinateGauge ι q)ᵒ = lpCoordinateGauge ι p := sorry

end
