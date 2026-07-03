import Mathlib
import Mathlib.Tactic.Recall
import Mathlib.Topology.MetricSpace.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Text_15_0_24 (from Chap03) -/
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

/-! ### Text_15_0_25 (from Chap03) -/
noncomputable section

section

open Matrix
open LinearMap.BilinMap
open scoped GaugePolar RealInnerProductSpace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-- The quadratic function `x ↦ (1 / 2) ⟪x, Qx⟫`, viewed in the chapter's `EReal` codomain. -/
abbrev matrixQuadratic (Q : Matrix (Fin n) (Fin n) ℝ) : E → EReal :=
  (⇑((1 / 2 : ℝ) • toQuadraticMap ((innerₗ E).compl₂ Q.toEuclideanLin))).toEReal

/-- The square-root gauge `x ↦ ⟪x, Qx⟫^(1 / 2)` attached to a matrix, viewed in the chapter's
`EReal` codomain. -/
def matrixQuadraticGauge (Q : Matrix (Fin n) (Fin n) ℝ) : E → EReal :=
  fun x ↦ ((Real.sqrt ⟪x, Q.toEuclideanLin x⟫ : ℝ) : EReal)

/-- Evaluating `matrixQuadraticGauge Q` at `x` gives the square root of the quadratic form
`⟪x, Qx⟫`. -/
@[simp] theorem matrixQuadraticGauge_apply (Q : Matrix (Fin n) (Fin n) ℝ) (x : E) :
    matrixQuadraticGauge Q x =
      ((Real.sqrt ⟪x, Q.toEuclideanLin x⟫ : ℝ) : EReal) :=
  rfl

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.25 records the quadratic example `matrixQuadratic Q`,
  i.e. `f x = (1 / 2) ⟪x, Qx⟫`, its inverse-matrix conjugate in the positive-definite case, the
  associated square-root gauge `matrixQuadraticGauge Q = (fun x ↦ ⟪x, Qx⟫^(1 / 2))` on the
  positive-semidefinite locus, and the inverse-matrix formula for its polar.
- `core/canonical`: the ambient owners are `convexConjugate`, the canonical quadratic-form owner
  `LinearMap.BilinMap.toQuadraticMap`, and the Chapter 15 owners `powerGaugeTransform`,
  `IsClosedGauge`, `IsGaugeNorm`, and `gauge_polar`.
- `bridge/view`: `matrixQuadratic Q` is the canonical quadratic owner coerced to the chapter's
  `EReal` codomain, while `powerGaugeTransform 2 (matrixQuadratic Q)` is the Chapter 15 bridge
  back to the source-facing owner `matrixQuadraticGauge Q` under the primitive hypothesis
  `Q.PosSemidef`. The nonsingular conjugate formula is the inverse-matrix specialization of the
  earlier quadratic-owner conjugate API.

Domain-style sampling used here:
- `LinearMap.BilinMap.toQuadraticMap`;
- `convexConjugate_matrixQuadraticMap_eq_inverse`;
- `powerGaugeTransform`;
- `IsGaugeNorm`.

Primitive data vs derived API:
- primitive source-facing data: the matrix `Q`;
- reused owner data: the quadratic owner `matrixQuadratic Q`, the Chapter 15 owner
  `powerGaugeTransform 2 (matrixQuadratic Q)` on the positive-semidefinite locus, the conjugate
  owner `convexConjugate`, the source-facing owner `matrixQuadraticGauge Q`, and the Chapter 15
  gauge owners;
- derived API: the bridge theorems from `powerGaugeTransform` to `matrixQuadraticGauge`, together
  with the closed-proper-convex, conjugate, closed-gauge, norm-gauge, and polar formulas for this
  quadratic specialization.

Layer target: `source-facing`, with the public owner surface centered on the textbook square-root
gauge `matrixQuadraticGauge Q`, while `matrixQuadratic Q` is kept only as the short codomain-lift
bridge needed to state the Chapter 15 owner theorems.
-/

-- Proof sketch: the quadratic form
-- `((1 / 2 : ℝ) • toQuadraticMap ((innerₗ E).compl₂ Q.toEuclideanLin))` scales by `c^2` under
-- `x ↦ c • x` because `toQuadraticMap` is quadratic. Coercing that scaling law to `EReal` gives
-- degree-`2` positive homogeneity.
/-- The quadratic function attached to a matrix is positively homogeneous of degree `2`. -/
theorem matrixQuadratic_positivelyHomogeneousOfDegree_two
    (Q : Matrix (Fin n) (Fin n) ℝ) :
    (matrixQuadratic Q).PositivelyHomogeneousOfDegree 2 :=
  sorry

-- Proof sketch: for a positive semidefinite matrix,
-- `⟪x, Matrix.toEuclideanLin Q x⟫` is nonnegative, so the negative and `⊤` branches in
-- `powerGaugeTransform 2` never occur. On finite real values,
-- the formula from `powerGaugeTransform_apply_of_nonneg_lt_top` reduces to
-- `sqrt (2 * (1 / 2) * ⟪x, Qx⟫) = sqrt ⟪x, Qx⟫`.
/-- For a positive semidefinite matrix, the Chapter 15 bridge owner
`powerGaugeTransform 2 (matrixQuadratic Q)` is exactly the source-facing square-root gauge
`matrixQuadraticGauge Q`. -/
theorem powerGaugeTransform_two_matrixQuadratic_eq_matrixQuadraticGauge
    {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosSemidef) :
    powerGaugeTransform 2 (matrixQuadratic Q) =
      matrixQuadraticGauge Q := sorry

-- Proof sketch: apply the previous square-root identification to the inverse matrix. Positive
-- definiteness is preserved by inversion, so the same power-gauge argument gives the dual formula
-- with `Q⁻¹`.
/-- For a positive definite matrix, the same square-root formula identifies the degree-`2`
power-gauge transform of the inverse quadratic function. -/
theorem powerGaugeTransform_two_inverse_matrixQuadratic_eq_matrixQuadraticGauge
    {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) :
    powerGaugeTransform 2 (matrixQuadratic Q⁻¹) =
      matrixQuadraticGauge Q⁻¹ := sorry

-- Proof sketch: a positive semidefinite quadratic form on Euclidean space has a closed epigraph,
-- is finite everywhere, and is convex, hence proper. This is the standard quadratic example of a
-- closed proper convex function.
/-- Text 15.0.25 (1): for a symmetric positive semidefinite matrix `Q`, the quadratic function
`f(x) = (1 / 2) ⟪x, Qx⟫`, represented here by `matrixQuadratic Q`,
is a closed proper convex function on `R^n`. -/
theorem matrixQuadratic_isClosedProperConvex
    {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosSemidef) :
    (matrixQuadratic Q).IsClosedProperConvex :=
  sorry

-- Proof sketch: apply the nonsingular quadratic-conjugate formula from the quadratic-function
-- item directly to the owner `convexConjugate`. Positive definiteness supplies the invertibility
-- and the inverse quadratic is again given by `Q⁻¹`.
/- Text 15.0.25 (2): the conjugate of `f(x) = (1 / 2) ⟪x, Qx⟫` is
`f*(xStar) = (1 / 2) ⟪xStar, Q⁻¹ xStar⟫`. This is exactly the owner theorem already established in
Text 12.3.2. -/
recall convexConjugate_matrixQuadraticMap_eq_inverse

-- Proof sketch: the preceding closed-proper-convex statement and the degree-`2` homogeneity of the
-- quadratic function put the matrix quadratic exactly in the scope of Corollary 15.3.2. Rewriting
-- its power-gauge transform by the square-root bridge theorem yields the closed-gauge claim for
-- `matrixQuadraticGauge Q`.
/-- Text 15.0.25 (3): the square-root gauge `matrixQuadraticGauge Q`, i.e.
`k(x) = ⟨x, Qx⟩^{1/2}`, is a closed gauge. -/
theorem matrixQuadraticGauge_isClosedGauge
    {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosSemidef) :
    IsClosedGauge (matrixQuadraticGauge Q) := sorry

-- Proof sketch: positive definiteness makes `x ↦ ⟨x, Qx⟩^{1/2}` finite everywhere, symmetric, and
-- strictly positive away from the origin. Combined with the previous closed-gauge theorem, these
-- are exactly the extra clauses required for the norm-gauge predicate.
/-- Text 15.0.25 (4): the square-root gauge `matrixQuadraticGauge Q`, i.e.
`k(x) = ⟨x, Qx⟩^{1/2}`, is in fact a norm-gauge. -/
theorem matrixQuadraticGauge_isGaugeNorm
    {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) :
    IsGaugeNorm (matrixQuadraticGauge Q) := sorry

-- Proof sketch: apply Corollary 15.3.2 to the quadratic function and use the explicit conjugate
-- formula from clause (2). The resulting polar identity is then rewritten on both sides by the two
-- square-root bridge lemmas, producing the inverse-matrix square-root formula.
/-- Text 15.0.25 (5): the polar of `matrixQuadraticGauge Q`, i.e. `k(x) = ⟨x, Qx⟩^{1/2}`, is
`matrixQuadraticGauge Q⁻¹`, i.e. `kᵒ(xStar) = ⟨xStar, Q⁻¹ xStar⟩^{1/2}`. -/
theorem gauge_polar_matrixQuadraticGauge_eq_inverse
    {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) :
    (matrixQuadraticGauge Q)ᵒ =
      matrixQuadraticGauge Q⁻¹ := sorry

end

/-! ### Text_15_0_26 (from Chap03) -/
noncomputable section

section

open Matrix
open LinearMap.BilinMap
open scoped RealInnerProductSpace

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.26 identifies the polar of the quadratic unit sublevel set
  `{x | ⟪x, Qx⟫ ≤ 1}`.
- `core/canonical`: the owner theorem already present upstream is
  the Chapter 15 polar-set owner theorem from `Corollary_15_3_2`,
  together with the source-facing quadratic owner `matrixQuadratic`,
  `matrixQuadratic_isClosedProperConvex`, and
  `matrixQuadratic_positivelyHomogeneousOfDegree_two`.
- `bridge/view`: this item is the explicit quadratic-matrix specialization of that owner theorem,
  obtained by rewriting the `1 / 2`-sublevel sets of `matrixQuadratic Q` and its
  inverse-matrix
  counterpart as the displayed quadratic unit sublevel sets.

Domain-style sampling used here:
- `LinearMap.BilinMap.toQuadraticMap` from `Text_12_3_2`;
- `matrixQuadratic_isClosedProperConvex` from `Text_15_0_25`;
- `matrixQuadratic_positivelyHomogeneousOfDegree_two` from `Text_15_0_25`;
- the Chapter 15 polar-set owner theorem;
- `Corollary_15_3_2`.

Primitive data vs derived API:
- primitive source-facing data: the positive definite matrix `Q` and its quadratic unit sublevel
  set;
- reused owner data: `matrixQuadratic Q` and the chapter polar-set owner theorem;
- derived API: the explicit inverse-matrix formula for the polar quadratic unit sublevel set.

Layer target: `source-facing`, stated directly as an equality of polar sets and quadratic
sublevel sets, without introducing any new wrapper around ellipsoids or quadratic gauges.
-/

-- Proof sketch: apply the Chapter 15 owner theorem
-- the Chapter 15 polar-set owner theorem to
-- `f = matrixQuadratic Q`
-- with the quadratic
-- closed-proper-convex
-- and degree-`2` homogeneity results from Text 15.0.25 and the canonical Hölder-conjugate pair
-- `2, 2`. Then rewrite the `1 / 2`-sublevel conditions
-- `((1 / 2 : ℝ) • toQuadraticMap ((innerₗ E).compl₂ Q.toEuclideanLin)) x ≤ 1 / 2` and
-- `((1 / 2 : ℝ) • toQuadraticMap ((innerₗ E).compl₂ (Q⁻¹).toEuclideanLin)) xStar ≤ 1 / 2` as
-- `⟪x, toEuclideanLin Q x⟫ ≤ 1` and `⟪xStar, toEuclideanLin Q⁻¹ xStar⟫ ≤ 1`.
/-- Text 15.0.26: if `Q` is a positive definite real matrix, then the polar of the quadratic unit
sublevel set `{x | ⟪x, Qx⟫ ≤ 1}` is the inverse-quadratic unit sublevel set
`{xStar | ⟪xStar, Q⁻¹ xStar⟫ ≤ 1}`. -/
theorem polar_matrixQuadraticSublevel_eq_inverse_matrixQuadraticSublevel
    {Q : Matrix (Fin n) (Fin n) ℝ} (hQ : Q.PosDef) :
    Set.polar {x : E | ⟪x, toEuclideanLin Q x⟫ ≤ 1} =
      {xStar : E | ⟪xStar, toEuclideanLin Q⁻¹ xStar⟫ ≤ 1} := by
  have htwo : (0 : ℝ) ≤ 2 := by
    norm_num
  have hhalf_nonneg : (0 : ℝ) ≤ 1 / 2 := by
    norm_num
  have hsublevel (A : Matrix (Fin n) (Fin n) ℝ) :
      {x : E |
        ((1 / 2 : ℝ) • toQuadraticMap ((innerₗ E).compl₂ A.toEuclideanLin)) x ≤ (1 / 2 : ℝ)} =
        {x : E | ⟪x, toEuclideanLin A x⟫ ≤ (1 : ℝ)} := by
    ext x
    change ((1 / 2 : ℝ) * ⟪x, toEuclideanLin A x⟫ ≤ (1 / 2 : ℝ)) ↔ _
    constructor
    · intro hx
      have h' := mul_le_mul_of_nonneg_left hx htwo
      simpa [mul_assoc] using h'
    · intro hx
      simpa using mul_le_mul_of_nonneg_left hx hhalf_nonneg
  have hsublevelEReal (A : Matrix (Fin n) (Fin n) ℝ) :
      {x : E | matrixQuadratic A x ≤ (1 / 2 : ℝ)} =
        {x : E | ⟪x, toEuclideanLin A x⟫ ≤ (1 : ℝ)} := by
    ext x
    change
      (((((1 / 2 : ℝ) • toQuadraticMap ((innerₗ E).compl₂ A.toEuclideanLin)) x : ℝ) :
          EReal) ≤
        ((1 / 2 : ℝ) : EReal)) ↔
      (⟪x, toEuclideanLin A x⟫ ≤ (1 : ℝ))
    rw [EReal.coe_le_coe_iff]
    change ((1 / 2 : ℝ) * ⟪x, toEuclideanLin A x⟫ ≤ (1 / 2 : ℝ)) ↔
      (⟪x, toEuclideanLin A x⟫ ≤ (1 : ℝ))
    constructor
    · intro hx
      have h' := mul_le_mul_of_nonneg_left hx htwo
      simpa [mul_assoc] using h'
    · intro hx
      simpa using mul_le_mul_of_nonneg_left hx hhalf_nonneg
  have hpolar :=
    polar_powerSublevel_eq_conjugatePowerSublevel
      Real.HolderConjugate.two_two
      (matrixQuadratic_isClosedProperConvex hQ.posSemidef)
      (matrixQuadratic_positivelyHomogeneousOfDegree_two Q)
  have hconj : convexConjugate (matrixQuadratic Q) = matrixQuadratic Q⁻¹ := by
    simpa [Function.toEReal, matrixQuadratic] using
      convexConjugate_matrixQuadraticMap_eq_inverse hQ
  calc
    Set.polar {x : E | ⟪x, toEuclideanLin Q x⟫ ≤ 1} =
        Set.polar {x : E | matrixQuadratic Q x ≤ (1 / 2 : ℝ)} := by
          rw [hsublevelEReal Q]
    _ = {xStar : E | convexConjugate (matrixQuadratic Q) xStar ≤ (1 / 2 : ℝ)} := hpolar
    _ = {xStar : E | matrixQuadratic Q⁻¹ xStar ≤ (1 / 2 : ℝ)} := by
          rw [hconj]
    _ = {xStar : E | ⟪xStar, toEuclideanLin Q⁻¹ xStar⟫ ≤ (1 : ℝ)} := by
          rw [hsublevelEReal Q⁻¹]

end

/-! ### Text_15_0_27 (from Chap03) -/
noncomputable section

section

open Matrix
open scoped RealInnerProductSpace

local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.27 is the explicit planar example of the polar of the axis-aligned
  elliptic disk with semiaxes `α1` and `α2`.
- `core/canonical`: the owner abstraction is the chapter polar-set operator `Set.polar`, and the
  preceding quadratic item already gives the canonical ellipsoid-polar formula for quadratic unit
  sublevel sets.
- `bridge/view`: this item specializes that quadratic owner formula to the diagonal quadratic form
  whose coordinate expression is `(x 0)^2 / α1^2 + (x 1)^2 / α2^2`.

Domain-style sampling used here:
- `Set.polar` from `Text_14_0_5`;
- the nearby owner theorem
  `polar_matrixQuadraticSublevel_eq_inverse_matrixQuadraticSublevel` from `Text_15_0_26`.

Layer target: `source-facing`, stated directly as an equality between the polar of the concrete
elliptic disk and the corresponding dual elliptic disk, without introducing any auxiliary wrapper
for planar ellipses.
-/

private theorem inner_toEuclideanLin_diagonal_fin2 (β1 β2 : ℝ) (x : R2) :
    ⟪x, toEuclideanLin (Matrix.diagonal ![β1, β2]) x⟫ =
      β1 * (x 0) ^ 2 + β2 * (x 1) ^ 2 := by
  have hdot :
      ⟪x, toEuclideanLin (Matrix.diagonal ![β1, β2]) x⟫ =
        (toEuclideanLin (Matrix.diagonal ![β1, β2]) x).ofLp ⬝ᵥ star x.ofLp := by
    simpa using EuclideanSpace.inner_eq_star_dotProduct x
      (toEuclideanLin (Matrix.diagonal ![β1, β2]) x)
  rw [hdot, Matrix.toEuclideanLin, Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  simp [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two, pow_two]
  ring

-- Proof sketch: apply
-- `polar_matrixQuadraticSublevel_eq_inverse_matrixQuadraticSublevel` to the diagonal positive
-- definite quadratic form with coefficients `α1⁻²` and `α2⁻²`. In coordinates, the source
-- quadratic inequality becomes `(x 0)^2 / α1^2 + (x 1)^2 / α2^2 ≤ 1`, while the inverse diagonal
-- form gives the dual inequality `α1^2 * (xStar 0)^2 + α2^2 * (xStar 1)^2 ≤ 1`.
/-- Text 15.0.27: for nonzero axis parameters `α1` and `α2`, the polar of the axis-aligned
elliptic disk `{x | (x 0)^2 / α1^2 + (x 1)^2 / α2^2 ≤ 1}` is the dual elliptic disk
`{xStar | α1^2 * (xStar 0)^2 + α2^2 * (xStar 1)^2 ≤ 1}`. Since only `α1^2` and `α2^2` appear,
the public statement needs only the nondegeneracy assumptions `α1 ≠ 0` and `α2 ≠ 0`. -/
theorem polar_axis_aligned_elliptic_disk_eq_dual_elliptic_disk
    {α1 α2 : ℝ} (hα1 : α1 ≠ 0) (hα2 : α2 ≠ 0) :
    Set.polar {x : R2 | (x 0) ^ 2 / (α1 ^ 2) + (x 1) ^ 2 / (α2 ^ 2) ≤ (1 : ℝ)} =
      {xStar : R2 | α1 ^ 2 * (xStar 0) ^ 2 + α2 ^ 2 * (xStar 1) ^ 2 ≤ (1 : ℝ)} := by
  let Q : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![(α1 ^ 2)⁻¹, (α2 ^ 2)⁻¹]
  have hQ : Q.PosDef := by
    dsimp [Q]
    exact Matrix.PosDef.diagonal fun i ↦ by
      fin_cases i
      · exact inv_pos.mpr (sq_pos_iff.mpr hα1)
      · exact inv_pos.mpr (sq_pos_iff.mpr hα2)
  have hsource :
      {x : R2 | ⟪x, toEuclideanLin Q x⟫ ≤ 1} =
        {x : R2 | (x 0) ^ 2 / (α1 ^ 2) + (x 1) ^ 2 / (α2 ^ 2) ≤ (1 : ℝ)} := by
    ext x
    simp [Q, inner_toEuclideanLin_diagonal_fin2, div_eq_mul_inv, mul_comm]
  have hQdiagInv :
      Ring.inverse ![(α1 ^ 2)⁻¹, (α2 ^ 2)⁻¹] = ![α1 ^ 2, α2 ^ 2] := by
    have hdiagUnit : IsUnit ![(α1 ^ 2)⁻¹, (α2 ^ 2)⁻¹] := by
      refine Pi.isUnit_iff.mpr ?_
      intro i
      fin_cases i
      · exact isUnit_iff_ne_zero.mpr (inv_ne_zero <| pow_ne_zero 2 hα1)
      · exact isUnit_iff_ne_zero.mpr (inv_ne_zero <| pow_ne_zero 2 hα2)
    have hRingInv :
        Ring.inverse ![(α1 ^ 2)⁻¹, (α2 ^ 2)⁻¹] = ![(α1 ^ 2)⁻¹, (α2 ^ 2)⁻¹]⁻¹ := by
      simpa using Ring.inverse_unit hdiagUnit.unit
    rw [hRingInv]
    ext i
    fin_cases i <;> simp [Pi.inv_apply]
  have hQinv : Q⁻¹ = Matrix.diagonal ![α1 ^ 2, α2 ^ 2] := by
    simpa [Q, Matrix.inv_diagonal] using congrArg Matrix.diagonal hQdiagInv
  have htarget :
      {xStar : R2 | ⟪xStar, toEuclideanLin Q⁻¹ xStar⟫ ≤ 1} =
        {xStar : R2 | α1 ^ 2 * (xStar 0) ^ 2 + α2 ^ 2 * (xStar 1) ^ 2 ≤ (1 : ℝ)} := by
    ext xStar
    simp [hQinv, inner_toEuclideanLin_diagonal_fin2]
  rw [← hsource, ← htarget]
  exact polar_matrixQuadraticSublevel_eq_inverse_matrixQuadraticSublevel hQ

end

/-! ### Text_15_0_28 (from Chap03) -/
noncomputable section

open Matrix
open scoped GaugePolar ProfileConjugate RealInnerProductSpace Rockafellar

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.28 specializes Theorem 15.3 to the quadratic gauge
  `matrixQuadraticGauge Q = (fun x ↦ ⟨x, Qx⟩^(1 / 2))` attached to a positive definite matrix `Q`.
- `core/canonical`: the owner abstractions already present in the chapter are
  `IsClosedGauge`, `kᵒ`, `Function.IsClosedProperConvex`, `f⋆`, and the
  profile-side owners `rayProfileConjugate` and `rayProfileExtension` together with the theorem
  `convexConjugate_eq_rayProfileConjugate_comp_gauge_polar_of_eq_comp_closedGauge_profile`.
- `bridge/view`: `powerGaugeTransform 2 (matrixQuadratic Q)` is only the Chapter 15 bridge
  to the source-facing owner `matrixQuadraticGauge Q`, together with the bridge theorem
  `powerGaugeTransform_two_matrixQuadratic_eq_matrixQuadraticGauge`, the closed-gauge
  theorem `matrixQuadraticGauge_isClosedGauge`, and the polar theorem
  `gauge_polar_matrixQuadraticGauge_eq_inverse` from `Text_15_0_25`, so this file should keep
  only the resulting specialization theorem instead of parallel local wrappers.

Domain-style sampling used here:
- `matrixQuadraticGauge_isClosedGauge`;
- `gauge_polar_matrixQuadraticGauge_eq_inverse`;
- `convexConjugate_eq_rayProfileConjugate_comp_gauge_polar_of_eq_comp_closedGauge_profile`.

Primitive data vs derived API:
- primitive inputs: the positive definite matrix `Q` and the scalar profile `g`;
- derived quadratic data: the source-facing owner `matrixQuadraticGauge Q` and its inverse-matrix
  polar, both already provided upstream;
- derived output here: the closed-proper-convex and conjugate formula for the specialized
  composite `x ↦ g (⟨x, Qx⟩^(1 / 2))`.

Layer target: `source-facing`; the file records only the quadratic specialization of the Chapter
15 owner theorem, but its theorem surface is stated directly with `matrixQuadraticGauge Q` and
uses `powerGaugeTransform` only through upstream bridge theorems.
-/

-- Proof sketch: apply Theorem 15.3 to the closed gauge `matrixQuadraticGauge Q`. The closed-gauge
-- hypothesis is supplied by `matrixQuadraticGauge_isClosedGauge`, and its polar is rewritten by
-- `gauge_polar_matrixQuadraticGauge_eq_inverse`.
/-- Text 15.0.28: if `Q` is positive definite and `g` satisfies the scalar-profile hypotheses of
Theorem 15.3, then the function `f(x) = g(⟨x, Qx⟩^(1 / 2))` is closed proper convex and its
conjugate is `g⁺(⟨x⋆, Q⁻¹ x⋆⟩^(1 / 2))`, formalized through the source-facing owner
`matrixQuadraticGauge Q`. -/
theorem comp_matrixQuadraticGauge_isClosedProperConvex_and_convexConjugate_eq
    (Q : Matrix (Fin n) (Fin n) ℝ) (hQ : Q.PosDef) {g : NNReal → EReal}
    (hg_ray : g.IsMonotoneClosedConvexOnNonnegativeRay)
    (hg_finite_pos : ∃ ζ : NNReal, 0 < ζ.1 ∧ g ζ < ⊤)
    (hg_nonconstant : ∃ s t : NNReal, g s ≠ g t) :
    (rayProfileExtension g ∘ matrixQuadraticGauge Q).IsClosedProperConvex ∧
      (rayProfileExtension g ∘ matrixQuadraticGauge Q)⋆ =
        rayProfileExtension (g⁺) ∘ matrixQuadraticGauge Q⁻¹ := by
  let k : E → EReal := matrixQuadraticGauge Q
  let f : E → EReal := rayProfileExtension g ∘ k
  have hk : IsClosedGauge k := by
    simpa [k] using matrixQuadraticGauge_isClosedGauge hQ.posSemidef
  have hf : IsGaugeLike[ℝ] f ∧ f.IsClosedProperConvex :=
    (isGaugeLike_and_isClosedProperConvex_iff_exists_closedGauge_profile f).2
      ⟨k, hk, g, hg_ray, hg_finite_pos, hg_nonconstant, rfl⟩
  have hf_conj : f⋆ = rayProfileExtension (g⁺) ∘ kᵒ :=
    convexConjugate_eq_rayProfileConjugate_comp_gauge_polar_of_eq_comp_closedGauge_profile
      hk hg_ray rfl
  constructor
  · simpa [f, k] using hf.2
  · simpa [f, k, gauge_polar_matrixQuadraticGauge_eq_inverse hQ] using hf_conj

end

/-! ### Text_15_0_29 (from Chap03) -/
noncomputable section

open Function
  (verticalInfimum verticalInfimum_eq_sInf verticalInfimum_le_of_mem
    le_verticalInfimum_of_subset_epi)
open scoped Rockafellar

universe u v w

section

-- Assumption layer minimized to the primitive data used by the statement:
-- ordered codomain operations for `WithBotTop 𝕜` and a pairing, with no field or linear structure.
variable {𝕜 : Type w} [ConditionallyCompleteLinearOrder 𝕜] [Zero 𝕜] [One 𝕜] [Add 𝕜] [Mul 𝕜]
variable {X : Type u} {Y : Type v} [HasPairing X Y 𝕜]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.29 extends the polar-gauge construction from gauges to convex
  functions by replacing the gauge inequality `⟪x, x⋆⟫ ≤ μ⋆ f x` with
  `⟪x, x⋆⟫ ≤ 1 + μ⋆ f x`.
- `core/canonical`: as in the earlier owner `gauge_polar`, the implementation should reuse the
  Chapter 1 fiber-infimum owner `Function.verticalInfimum` instead of duplicating a raw `sInf`
  definition. The same-kind neighboring owners are `gauge_polar`, `indicatorFunction`, and
  `Set.polar`.
- `bridge/view`: the companion theorems below identify this function polar with `gauge_polar`
  under positive homogeneity and with the set-polar bridge on indicator inputs,
  while the final inequality is stated directly on finite-value points of `f` and its polar.

Domain-style sampling used here:
- `IsGauge` from `Text_15_0_1`;
- `gauge_polar` from `Text_15_0_5`;
- `Function.verticalInfimum` and `Function.verticalInfimum_eq_sInf` from `Theorem_5_3`;
- `indicatorFunction` from `Defintion_4_8_1`;
- `Set.polar` from `Text_14_0_5`.

Primitive data vs derived API:
- primitive inputs: a function `f : X → WithBotTop 𝕜` and a dual point `xStar : Y`;
- primitive source-facing owner: `convex_function_polar`;
- primitive implementation data: the admissible-majorant subset of `Y × 𝕜` fed to
  `Function.verticalInfimum`;
- derived API: the owner-facing majorant bound, nonnegativity, the positive-homogeneous
  specialization to `gauge_polar`, the companion `sInf` formula over nonnegative scalars, the
  indicator
  specialization, and the source inequality on finite-value points.

Layer target: `source-facing`. There is no existing project owner for this exact affine-majorant
polar construction, so the public owner remains local, but its implementation should still reuse
the chapter's canonical infimum abstraction. The construction only needs dual evaluation, so it
is stated at the pairing layer `HasPairing X Y 𝕜` rather than a concrete inner-product model.
-/

def convexFunctionPolarMajorantsAt (f : X → WithBotTop 𝕜) (xStar : Y) : Set 𝕜 :=
  {μ : 𝕜 |
    0 ≤ μ ∧
      ∀ x : X, ((⟪x, xStar⟫ₚ : 𝕜) : WithBotTop 𝕜) ≤ (1 : WithBotTop 𝕜) + (μ : WithBotTop 𝕜) * f x}

/-- The admissible affine-majorant heights for `fᵒ xStar`, viewed in `WithBotTop 𝕜`. -/
def convexFunctionPolarMajorantHeights (f : X → WithBotTop 𝕜) (xStar : Y) : Set (WithBotTop 𝕜) :=
  ((↑) : 𝕜 → WithBotTop 𝕜) '' convexFunctionPolarMajorantsAt f xStar

private def convexFunctionPolarMajorants (f : X → WithBotTop 𝕜) : Set (Y × 𝕜) :=
  {p : Y × 𝕜 |
    p.2 ∈ convexFunctionPolarMajorantsAt f p.1}

/-- Text 15.0.29: the polar `fᵒ` of a convex function `f` is the Chapter 1 vertical infimum of
the admissible affine-majorant set. It is written `fᵒ` after
`open scoped ConvexFunctionPolar`. -/
def convex_function_polar (f : X → WithBotTop 𝕜) : Y → WithBotTop 𝕜 :=
  verticalInfimum (convexFunctionPolarMajorants f)

namespace ConvexFunctionPolar

scoped postfix:max "ᵒ" => convex_function_polar

end ConvexFunctionPolar

open scoped ConvexFunctionPolar

/-- The value of `fᵒ` at `xStar` is the infimum of the admissible
nonnegative affine majorants from the source formula. -/
theorem convex_function_polar_eq_sInf_nonneg_affine_majorants
    (f : X → WithBotTop 𝕜) (xStar : Y) :
    fᵒ xStar = sInf (convexFunctionPolarMajorantHeights f xStar) := by
  simpa
      [convex_function_polar, convexFunctionPolarMajorantHeights, convexFunctionPolarMajorants,
        convexFunctionPolarMajorantsAt] using
    (verticalInfimum_eq_sInf (convexFunctionPolarMajorants f) xStar)

-- Proof sketch: `convex_function_polar f xStar` is the infimum of the `WithBotTop 𝕜` image of
-- the admissible affine majorants, so every particular nonnegative majorant contributes one upper
-- bound for that infimum after coercion to `WithBotTop 𝕜`.
/-- Any admissible affine majorant bounds the polar function from above. -/
theorem convex_function_polar_le_of_majorant
    {f : X → WithBotTop 𝕜} {xStar : Y} {μStar : 𝕜}
    (hμ : μStar ∈ convexFunctionPolarMajorantsAt f xStar) :
    fᵒ xStar ≤ (μStar : WithBotTop 𝕜) := by
  have hmajorant : (xStar, μStar) ∈ convexFunctionPolarMajorants f := hμ
  simpa [convex_function_polar] using
    (verticalInfimum_le_of_mem hmajorant :
      verticalInfimum (convexFunctionPolarMajorants f) xStar ≤ μStar)

-- Proof sketch: every element of the image in the defining `sInf` is nonnegative because the
-- defining scalar satisfies `0 ≤ μStar`. The infimum of a set of nonnegative `WithBotTop 𝕜`
-- values is therefore nonnegative; if the set is empty, the infimum is `⊤`, which is still
-- nonnegative.
/-- The polar of a convex function takes nonnegative values in `WithBotTop 𝕜`. -/
theorem convex_function_polar_nonneg (f : X → WithBotTop 𝕜) (xStar : Y) :
    0 ≤ fᵒ xStar := by
  have hmajorants :
      convexFunctionPolarMajorants f ⊆ epi (fun _ : Y ↦ (0 : WithBotTop 𝕜)) := by
    rintro ⟨x, μ⟩ hμ
    refine mem_epi_restrict_iff.mpr ⟨by simp, ?_⟩
    change ((0 : 𝕜) : WithBotTop 𝕜) ≤ (μ : WithBotTop 𝕜)
    exact WithBotTop.coe_le_coe.mpr hμ.1
  have hnonneg := le_verticalInfimum_of_subset_epi hmajorants
  simpa [convex_function_polar] using hnonneg xStar

end

open scoped ConvexFunctionPolar

section

variable {𝕜 : Type w} [ConditionallyCompleteLinearOrder 𝕜] [Field 𝕜] [IsStrictOrderedRing 𝕜]
variable {X : Type u} {Y : Type v}
variable [AddCommMonoid X] [Module 𝕜 X]
variable [AddCommMonoid Y] [Module 𝕜 Y]
variable [HasLinearPairing X Y 𝕜]

-- Proof sketch: positive homogeneity lets one scale the defining inequality
-- `⟪x, x⋆⟫ ≤ 1 + μ⋆ k x` along rays and send the scale to `+∞`, eliminating the constant term `1`
-- and recovering exactly the majorant condition from `gauge_polar`. The converse implication is
-- immediate because `⟪x, x⋆⟫ ≤ μ⋆ k x` implies `⟪x, x⋆⟫ ≤ 1 + μ⋆ k x`.
/-- For a positively homogeneous function, hence in particular for a gauge, the present polar
agrees with the earlier polar gauge `gauge_polar`. -/
theorem convex_function_polar_eq_gauge_polar
    {k : X → WithBotTop 𝕜} (hk_hom : k.PositivelyHomogeneous 𝕜) (xStar : Y) :
    kᵒ xStar = gauge_polar k xStar := sorry

end

section

variable {𝕜 : Type w} [ConditionallyCompleteLinearOrder 𝕜]
variable [Zero 𝕜] [One 𝕜] [Add 𝕜] [Mul 𝕜]
variable {X : Type u} {Y : Type v} [HasPairing X Y 𝕜] [HasPairing Y X 𝕜]

-- Proof sketch: for `indicatorFunction C`, the defining inequality is automatic outside `C`
-- because the right-hand side is `⊤`, while on `C` it becomes `⟪x, x⋆⟫ ≤ 1`. Hence admissibility
-- no longer depends on `μ⋆`: either `xStar ∈ Set.polar C`, in which case `μ⋆ = 0` is admissible
-- and the infimum is `0`, or else no admissible majorant exists and the infimum is `⊤`.
/-- The polar of a set indicator is the indicator of the polar set. -/
theorem convex_function_polar_indicatorFunction_eq_indicatorFunction_polar
    (C : Set X) :
    (δ[𝕜](· | C))ᵒ = (fun y : Y ↦ δ[𝕜](y | (Cᵒ[𝕜]))) := sorry

end

section

variable {𝕜 : Type w} [ConditionallyCompleteLinearOrder 𝕜] [Zero 𝕜] [One 𝕜] [Add 𝕜] [Mul 𝕜]
variable {X : Type u} {Y : Type v} [HasPairing X Y 𝕜]

-- Proof sketch: fix `x` and use the defining infimum for `convex_function_polar f xStar`. For any
-- admissible `μ⋆`, the displayed inequality gives `⟪x, x⋆⟫ ≤ 1 + μ⋆ f x`. Since `f x` is assumed
-- finite and nonnegative, one can pass from all admissible `μ⋆` to their infimum, obtaining the
-- same inequality with `μ⋆ = convex_function_polar f xStar`.
/-- If `x` is a finite-value point of a nonnegative `WithBotTop 𝕜`-valued function `f` and
`xStar` is a finite-value point of its polar `fᵒ`, then
`⟪x, x⋆⟫ ≤ 1 + f x * fᵒ x⋆`. -/
theorem inner_le_one_add_mul_convex_function_polar
    {f : X → WithBotTop 𝕜} {x : X} {xStar : Y} (hx_nonneg : 0 ≤ f x)
    (hx_dom : f x < ⊤) (hxStar_dom : fᵒ xStar < ⊤) :
    (((⟪x, xStar⟫ₚ : 𝕜) : WithBotTop 𝕜) ≤
      (1 : WithBotTop 𝕜) + f x * fᵒ xStar) := sorry

end

/-! ### Text_15_0_30 (from Chap03) -/
open scoped ConvexFunctionPolar

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.30 states the Young-type inequality
  `⟪x, x⋆⟫ ≤ 1 + f x * fᵒ x⋆` for points in the effective domains of a nonnegative closed convex
  function `f` with `f 0 = 0` and of its polar.
- `core/canonical`: the preceding Chapter 15 item introduces the polar by the affine-majorant
  infimum formula and proves exactly this inequality for finite-value points.
- `bridge/view`: this item is therefore a direct recall of that owner theorem rather than a second
  local theorem shell.

Domain-style sampling used here:
- `gauge_polar` from `Text_15_0_5`;
- `convex_function_polar` from `Text_15_0_29`;
- `inner_le_one_add_mul_convex_function_polar` from `Text_15_0_29`.

Layer target: `core/canonical` direct recall. This item adds no new owner abstraction and no new
bridge theorem beyond the existing Chapter 15 owner statement.
-/

/- Text 15.0.30: if `x` is a finite-value point of a nonnegative `WithBotTop 𝕜`-valued function
`f` and `x⋆` is a finite-value point of its polar, then
`⟪x, x⋆⟫ ≤ 1 + f x * fᵒ x⋆`. This is exactly
`inner_le_one_add_mul_convex_function_polar` from `Text_15_0_29`. -/
recall inner_le_one_add_mul_convex_function_polar

/-! ### Text_15_0_31 (from Chap03) -/
noncomputable section

open scoped ConvexFunctionPolar Rockafellar

universe u

section

variable {E : Type u} [SMul ℝ E]

/-- The obverse of `f` sends `x` to the infimum of the positive scalars `λ` for which the scaled
perspective `f_λ x`, rendered by the positive right scalar multiple of `f`, is at most `1`.
The positive parameter is packaged canonically as `a : NNRealˣ`, so the construction lives on an
arbitrary real `ℝ`-scaled space. -/
def obverse (f : E → WithBotTop ℝ) : E → WithBotTop ℝ :=
  fun x ↦
    sInf
      (((↑) : NNRealˣ → WithBotTop ℝ) ''
        {a : NNRealˣ | ((a : NNReal) •ʳ f) x ≤ (1 : WithBotTop ℝ)})

end

section

variable {E : Type u} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

namespace Function

/-- The standing Chapter 15 hypothesis package keeps the primitive source data:
closedness, convexity, nonnegativity, and the normalization `f 0 = 0`.
The Chapter 12 properness clause is derived from nonnegativity together with the finite value at
the origin, so it is not stored as primitive public data. This owner already lives on the
intrinsic real topological-module layer with codomain `WithBotTop ℝ`; later source bridges may
specialize the ambient further, but this owner keeps only the primitive data. -/
class IsNonnegativeClosedConvexZero (f : E → WithBotTop ℝ) : Prop where
  convex : f.IsConvex ℝ
  closed : LowerSemicontinuous f
  nonneg : ∀ x : E, (0 : WithBotTop ℝ) ≤ f x
  map_zero : f 0 = 0

namespace IsNonnegativeClosedConvexZero

/-- Properness is derived from pointwise nonnegativity and the finite value `f 0 = 0`. -/
theorem proper {f : E → WithBotTop ℝ} (hf : f.IsNonnegativeClosedConvexZero) :
    f.IsProper := by
  rw [Function.isProper_iff_nonempty_dom_and_bot_lt]
  refine ⟨⟨0, ?_⟩, ?_⟩
  · rw [mem_effectiveDomain, hf.map_zero]
    exact show (0 : WithBotTop ℝ) < ⊤ from WithBotTop.coe_lt_top (0 : ℝ)
  · intro x
    exact
      lt_of_lt_of_le
        (show (⊥ : WithBotTop ℝ) < (0 : WithBotTop ℝ) by simp)
        (hf.nonneg x)

/-- The standing Chapter 15 owner canonically upgrades to the Chapter 12 owner
`f.IsClosedProperConvex`. -/
theorem isClosedProperConvex {f : E → WithBotTop ℝ} (hf : f.IsNonnegativeClosedConvexZero) :
    f.IsClosedProperConvex (𝕜 := ℝ) :=
  { convex := hf.convex, proper := hf.proper, closed := hf.closed }

instance instIsClosedProperConvex (f : E → WithBotTop ℝ) [hf : f.IsNonnegativeClosedConvexZero] :
    f.IsClosedProperConvex (𝕜 := ℝ) :=
  hf.isClosedProperConvex

end IsNonnegativeClosedConvexZero

end Function

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.31 states that for a nonnegative closed convex function `f` with
  `f 0 = 0`, the extended polar of its Fenchel conjugate `f⋆` is given pointwise by the infimum
  over the positive dilations `f_λ`.
- `core/canonical`: the existing owner constructions are `f⋆`,
  `convex_function_polar`, the earlier scaled-epigraph owner `rightScalarMul`, the
  source-facing infimum owner `obverse`, the Chapter 12 owner `Function.IsClosedProperConvex`,
  the closed-proper-convex biconjugacy theorem `Function.IsClosedProperConvex.biconjugate_eq`,
  and the standing Chapter 15 refinement `Function.IsNonnegativeClosedConvexZero`.
- `bridge/view`: the source's positive-dilation notation `f_λ` is rendered directly by the
  existing owner `rightScalarMul` with the canonical positive parameter `a : NNRealˣ`, so no
  parallel local wrapper is kept. The Chapter 12 properness owner is derived from the source data
  rather than stored primitively. The main theorem keeps the textbook's explicit infimum formula,
  and the companion theorem below identifies that formula with the existing source-facing owner
  `obverse`.

Domain-style sampling used here:
- `convex_function_polar`;
- `rightScalarMul`;
- `rightScalarMul_apply_eq_mul_comp_inv_smul_of_pos`;
- `Function.IsClosedProperConvex.biconjugate_eq`;
- `obverse`;
- `f⋆`.

Primitive data vs derived API:
- primitive inputs: a function `f : E → WithBotTop ℝ`, the source-specific fields `f.IsConvex ℝ`,
  `LowerSemicontinuous f`, `∀ x, 0 ≤ f x`, `f 0 = 0`, and a point `x : E`;
- primitive source formula: the infimum over the positive parameters `a : NNRealˣ` with
  `((a : NNReal) •ʳ f) x ≤ 1`;
- derived owner bridge: `hf.proper` and `hf.isClosedProperConvex` from the standing Chapter 15
  owner `hf : f.IsNonnegativeClosedConvexZero`;
- derived API: the bridge identifying that formula with `obverse f`.

Layer target: `source-facing` for the main labeled theorem, with a `bridge/view` companion to the
existing `obverse` abstraction. The owner `obverse` itself lives on the weaker real-scaling
layer above; the conjugate/polar comparison theorem below is stated at the finite-dimensional
real pairing layer.
-/

end

section

variable {E : Type u}
variable [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
variable [FiniteDimensional ℝ E]
variable [HasLinearPairing E E ℝ] [HasContinuousPairing E E ℝ]

-- Proof sketch: start from the defining infimum formula for `convex_function_polar
-- (convexConjugate f) x`. For `λ > 0`, rewrite the admissibility condition
-- `∀ y, ⟪y, x⟫ ≤ 1 + λ (convexConjugate f) y` as
-- `sup_y (⟪y, x⟫ - λ (convexConjugate f) y) ≤ 1`, identify that supremum with
-- `λ * convexConjugate (convexConjugate f) (λ⁻¹ • x)`, and then use closed-convex biconjugacy
-- through the canonical Chapter 12 owner theorem `hf.isClosedProperConvex.biconjugate_eq`,
-- together with the standing normalization hypotheses, to replace `f**` by `f`.
/-- Text 15.0.31: if `f : E → [0, +∞]` is convex, lower semicontinuous, and satisfies `f 0 = 0`
on a finite-dimensional real vector space with continuous linear self-pairing, then the polar of
its Fenchel conjugate `f*`,
rendered as `(f⋆)ᵒ`, is given at
each `x` by the infimum of the positive scalars `λ` for which the dilated perspective
`f_λ x = λ f (λ⁻¹ x)` is at most `1`. Specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers
the source statement on `R^n`. -/
theorem
    convex_function_polar_convexConjugate_eq_sInf_rightScalarMul_of_nonnegative_closed_convex_zero
    (f : E → WithBotTop ℝ) (hf : f.IsNonnegativeClosedConvexZero) (x : E) :
    ((f⋆ : E → WithBotTop ℝ)ᵒ) x =
      sInf
        (((↑) : NNRealˣ → WithBotTop ℝ) ''
          {a : NNRealˣ | ((a : NNReal) •ʳ f) x ≤ (1 : WithBotTop ℝ)}) := sorry

-- Proof sketch: unfold `obverse f x` and compare the resulting right-hand side with the main
-- theorem's infimum formula.
/-- The perspective-infimum formula from the main theorem is exactly the obverse construction
`obverse f`, under the same finite-dimensional real pairing hypotheses. -/
theorem
    convex_function_polar_convexConjugate_eq_obverse_of_nonnegative_closed_convex_zero
    (f : E → WithBotTop ℝ) (hf : f.IsNonnegativeClosedConvexZero) (x : E) :
    ((f⋆ : E → WithBotTop ℝ)ᵒ) x = obverse f x := by
  simpa [obverse] using
    convex_function_polar_convexConjugate_eq_sInf_rightScalarMul_of_nonnegative_closed_convex_zero
      f hf x

end

/-! ### Text_15_0_32 (from Chap03) -/
noncomputable section

open scoped Rockafellar Pointwise ENNReal NNReal

universe u

section

variable {E : Type u} [Zero E] [SMul ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.32 identifies the obverse construction on indicator and gauge
  functions.
- `core/canonical`: the existing owner APIs are the Chapter 15 declarations
  `Function.rightScalarMul` and `obverse` from `Text_15_0_31`, together with the chapter
  indicator owner `δ(· | C)` and the chapter gauge notation `γ(· | C)` for mathlib's owner
  `egauge ℝ≥0 C`.
- `bridge/view`: the theorem-level content is exactly the comparison between the source-facing
  obverse construction and those canonical owners.

Domain-style sampling used here:
- `rightScalarMul`;
- `obverse`;
- `indicatorFunction`;
- `egauge`;
- `egauge_le_iff_mem_smul`.
- `supportFunction_isClosedGauge_of_zero_mem`;
- `gauge_polar_supportFunction_eq_egauge_of_isClosedConvexZero`.

Primitive data vs derived API:
- primitive data: the chapter owner declarations `Function.rightScalarMul` and `obverse f`;
- derived API: the two identifications exchanging indicator and gauge, with the support-function
  closed-gauge package and its polar relation reused from Corollary 15.1.2 rather than rebuilt
  locally. The only codomain bridge needed here is the canonical coercion from
  `γ(· | C) : E → ℝ≥0∞` to `E → WithBotTop ℝ`, so no local gauge wrapper is kept.

Layer target: `bridge/view`, reusing the upstream Chapter 15 owner declarations and keeping only
the indicator/gauge comparison theorems in this file. The first bridge theorem uses only the real
action layer needed for `obverse` and `γ(· | C)`, while the converse bridge theorem below
inherits the stronger topological ambient from the imported owner API
`egauge_le_iff_mem_smul` and Corollary 15.1.2. Both therefore stay coordinate-free and only
specialize to `R^n` when desired.
-/

-- Proof sketch: for `f = indicatorFunction C`, the positive right scalar multiple condition
-- corresponding to `f_λ x ≤ 1` is equivalent to `x ∈ (λ : ℝ) • C`, because the indicator is `0`
-- on `C` and `⊤` off `C`. Taking the infimum over positive `λ` then gives the canonical extended
-- gauge of `C`; the hypothesis `0 ∈ C` ensures the positive-scalar and nonnegative-scalar
-- formulations agree at the origin.
/-- Text 15.0.32: for a set `C` containing the origin, the obverse of its indicator function
`δ(· | C)` is the extended gauge `γ(· | C)`, viewed in `WithBotTop ℝ`. Specializing `E` to
`EuclideanSpace ℝ (Fin n)` recovers the source ambient `R^n`. -/
theorem obverse_indicatorFunction_eq_egauge
    {C : Set E} (h0C : (0 : E) ∈ C) :
    obverse (δ(· | C)) = (γ(· | C) : E → WithBotTop ℝ) := sorry

end

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

-- Proof sketch: positive homogeneity makes the positive right scalar multiple of
-- `fun x ↦ (egauge ℝ≥0 C x : WithBotTop ℝ)` independent of `λ`, so the obverse condition reduces
-- to
-- `egauge ℝ≥0 C x ≤ 1`. For a closed convex set containing `0`, Corollary 9.7.1 identifies this
-- sublevel set with `C`, hence the infimum is `0` on `C` and `⊤` outside `C`, which is exactly
-- `indicatorFunction C`.
/-- For a closed convex set containing the origin, the obverse of the extended gauge `egauge ℝ≥0
C`, written on the theorem surface as `γ(· | C)` and viewed in `WithBotTop ℝ`, is the indicator
`δ(· | C)`. Specializing `E` to `EuclideanSpace ℝ (Fin n)` recovers the source ambient `R^n`. -/
theorem obverse_egauge_eq_indicatorFunction
    {C : Set E} (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (h0C : (0 : E) ∈ C) :
    obverse ((γ(· | C) : E → WithBotTop ℝ)) = (δ(· | C) : E → WithBotTop ℝ) := sorry

end

/-! ### Text_15_0_33 (from Chap03) -/
noncomputable section

universe u

open ConvexERealFunction
open scoped Rockafellar

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

local notation "P" => ℝ × E

/-!
Source/core/bridge triage for this item.

- `source-facing`: under the standing Chapter 15 convexity/closedness/nonnegativity
  normalization hypotheses, the item identifies the epigraph of the obverse `g` with the unit
  sublevel set of the closed perspective of `f`.
- `core/canonical`: the owner layer is the existing chapter API `perspective`,
  `ConvexERealFunction.lowerSemicontinuousHull`, the owner formula
  `lowerSemicontinuousHull_perspective_apply`, and the Chapter 15 declarations
  `Function.rightScalarMul` and `obverse` from Text 15.0.31.
- `bridge/view`: the epigraph statement is written directly in the source coordinates
  `(λ, x) ∈ ℝ × E`, so no swapped-coordinate wrapper is introduced.

Domain-style sampling used here:
- `perspective`;
- `lowerSemicontinuousHull_perspective_apply`;
- `rightScalarMul`;
- `obverse`;

Primitive data vs derived API:
- primitive imported owners: `perspective`, `cl(·)`, `rightScalarMul`, and `obverse`;
- derived API in this file: the source-facing epigraph/sublevel-set identification theorem under
  the standing hypotheses from Text 15.0.31.

Layer target: `source-facing`; the main theorem keeps the textbook epigraph statement while
reusing the existing closed-perspective owner instead of introducing a parallel local three-branch
wrapper.
-/

-- Proof sketch: `lowerSemicontinuousHull_perspective_apply` identifies `cl(perspective f)` with
-- the textbook three-branch function whose positive branch is the scaled perspective `f_λ`, whose
-- boundary branch is `f0⁺`, and whose negative branch is `+∞`. Under the Chapter 15 owner
-- hypothesis `f.IsNonnegativeClosedConvexZero`, the admissible set in `obverse f x` is a
-- closed upper ray, so `obverse f x ≤ λ` is equivalent to the condition that this three-branch
-- value at `(λ, x)` is at most `1`. Thus the source-coordinate epigraph of `obverse f` is exactly
-- the unit sublevel set of the closed perspective of `f`.
/-- Text 15.0.33: the epigraph of the obverse `g` of `f`, written in the source coordinates
`(λ, x) ∈ ℝ × E`, is the unit sublevel set of the closed perspective `cl(perspective f)`.
Equivalently, the set `{(λ, x) | g x ≤ λ}` is exactly the set where `cl(perspective f) (λ, x) ≤
1`, under the standing Chapter 15 hypothesis package `f.IsNonnegativeClosedConvexZero`.
The textbook three-branch profile `h(λ, x)` is therefore reused here through the existing owner
`cl(perspective f)` rather than a parallel local wrapper. -/
theorem obverse_epigraph_eq_one_sublevel_closedPerspective
    (f : E → EReal) (hf : f.IsNonnegativeClosedConvexZero) :
    {p : P | cl(perspective f) p ≤ (1 : EReal)} =
      {p : P | obverse f p.2 ≤ p.1} := sorry

end

/-! ### Text_15_0_34 (from Chap03) -/
noncomputable section

universe u

open ConvexERealFunction
open scoped Rockafellar

section

/-!
Source/core/bridge triage for this item.

- `source-facing`: the item views the epigraph `P = epi h` of the closed perspective from
  Text 15.0.33 as the closed convex cone generated by the height-one epigraph slice of `f`, then
  reads off the slices `λ = 1` and `μ = 1`.
- `core/canonical`: the owner abstractions already available are `cl(perspective f)`, the
  epigraph owner `epi`, `obverse`, the recalled source-coordinate epigraph theorem from
  Text 15.0.33, and the generated-cone owner `ConvexCone.hull`.
- `bridge/view`: Theorem 14.4 keeps a `WithLp` model for the Chapter 14 polarity argument, but
  this item itself only needs the intrinsic textbook triple space `ℝ × E × ℝ`, so the public
  statements are written directly in those coordinates.

Domain-style sampling used here:
- `epi`;
- `lowerSemicontinuousHull_perspective_apply`;
- `obverse_epigraph_eq_one_sublevel_closedPerspective`;
- `ConvexCone.hull`.

Primitive data vs derived API:
- primitive source-facing owner: `closedPerspectiveRealEpigraph f` in the triple coordinates
  `(λ, x, μ)`;
- primitive slice owners: the height-one slice `({(1 : ℝ)} ×ˢ epi f : Set (ℝ × E × ℝ))` and
  `obverseEpigraphSlice f`;
- derived API: the cone-closure theorem and the two section-identification theorems.

Layer target: `source-facing`. The current item records the cone generated by the
height-one epigraph slice and the two geometric slices of that cone, stated directly with the
closed-perspective epigraph owner on `ℝ × E × ℝ` and already living on the same real
topological-module layer as the upstream owners it reuses.
-/

section ClosedPerspectiveRealEpigraph

variable {E : Type u} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- The epigraph of the closed perspective `cl(perspective f)` written in the textbook triple
coordinates `(λ, x, μ)`. -/
def closedPerspectiveRealEpigraph (f : E → EReal) : Set (ℝ × E × ℝ) :=
  {p | cl(perspective f) (p.1, p.2.1) ≤ p.2.2}

/-- Membership in `closedPerspectiveRealEpigraph f` is exactly the defining epigraph inequality in
the triple coordinates `(λ, x, μ)`. -/
@[simp] theorem mem_closedPerspectiveRealEpigraph_iff (f : E → EReal) (p : ℝ × E × ℝ) :
    p ∈ closedPerspectiveRealEpigraph f ↔ cl(perspective f) (p.1, p.2.1) ≤ p.2.2 :=
  Iff.rfl

end ClosedPerspectiveRealEpigraph

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

local notation "P" => ℝ × E

-- Proof sketch: the positive slices of `cl(perspective f)` are the scaled perspectives `f_λ`,
-- and the `λ = 0` slice is the recession function from Text 15.0.33. For a closed proper
-- convex function, Corollary 8.5.2 identifies that boundary slice with the closure of the
-- positive dilations of the height-one epigraph slice. The cone generated by the slice
-- `{(1, x, μ) | μ ≥ f x}` therefore has closure exactly `epi h`.
/-- Text 15.0.34 (1): for a closed proper convex function `f`, the epigraph `P = epi h` of the
closed perspective `h = cl(perspective f)` from Text 15.0.33 is exactly the closure of the convex
cone generated by the points
`(1, x, μ)` with `μ ≥ f x`; equivalently, it is the smallest closed convex cone containing the
source-facing height-one slice `({(1 : ℝ)} ×ˢ epi f : Set (ℝ × E × ℝ))`. -/
theorem closedPerspectiveRealEpigraph_eq_closure_convexConeHull_primalEpigraphSlice
    (f : E → EReal) (hf : f.IsClosedProperConvex) :
    closedPerspectiveRealEpigraph f =
      closure
        (ConvexCone.hull ℝ ({(1 : ℝ)} ×ˢ epi f : Set (ℝ × E × ℝ)) : Set (ℝ × E × ℝ)) := sorry

-- Proof sketch: specialize the positive-parameter formula
-- `lowerSemicontinuousHull_perspective_apply` at `λ = 1`. Since `1 > 0`, the closed perspective
-- value becomes `f x`, so the height-one section of `epi h` is exactly the ordinary real
-- epigraph of `f`.
/-- Text 15.0.34 (2): intersecting `P = epi h` with the hyperplane `λ = 1` recovers the real
epigraph of `f`, namely the source-facing height-one slice
`({(1 : ℝ)} ×ˢ epi f : Set (ℝ × E × ℝ))`. -/
theorem closedPerspectiveRealEpigraph_lambda_one_section_eq_primalEpigraphSlice
    (f : E → EReal) (hf : f.IsClosedProperConvex) :
    {p : ℝ × E × ℝ | p.1 = 1 ∧ p ∈ closedPerspectiveRealEpigraph f} =
      ({(1 : ℝ)} ×ˢ epi f : Set (ℝ × E × ℝ)) := sorry

end

section ObverseEpigraphSlice

variable {E : Type u} [SMul ℝ E]

local notation "P" => ℝ × E

/-- The `μ = 1` slice of the obverse epigraph, written in the source-facing triple coordinates
`(λ, x, μ)`. This is the `μ = 1` lift of the source-coordinate epigraph
`{q : P | obverse f q.2 ≤ q.1}` from Text 15.0.33. -/
def obverseEpigraphSlice (f : E → EReal) : Set (ℝ × E × ℝ) :=
  {p | p.2.2 = 1 ∧ obverse f p.2.1 ≤ p.1}

/-- Membership in `obverseEpigraphSlice f` is exactly the condition `μ = 1` and
`λ ≥ obverse f x` in the triple coordinates `(λ, x, μ)`. -/
@[simp]
theorem mem_obverseEpigraphSlice_iff (f : E → EReal) (p : ℝ × E × ℝ) :
    p ∈ obverseEpigraphSlice f ↔
      p.2.2 = 1 ∧ obverse f p.2.1 ≤ p.1 :=
  Iff.rfl

end ObverseEpigraphSlice

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

local notation "P" => ℝ × E

-- Proof sketch: on the section `μ = 1`, the defining inequality for `epi h` becomes
-- `cl(perspective f) (λ, x) ≤ 1`. Text 15.0.33 identifies that unit sublevel set with the
-- epigraph `{(λ, x) | obverse f x ≤ λ}`, which is exactly `obverseEpigraphSlice f` after
-- reintroducing the fixed third coordinate `μ = 1`.
/-- Text 15.0.34 (3): intersecting `P = epi h` with the hyperplane `μ = 1` recovers the epigraph
of the obverse `g = obverse f` in the source coordinates `(λ, x)`, viewed inside the triple
coordinates as `obverseEpigraphSlice f`. -/
theorem closedPerspectiveRealEpigraph_mu_one_section_eq_obverseEpigraphSlice
    (f : E → EReal) (hf : f.IsNonnegativeClosedConvexZero) :
    {p : ℝ × E × ℝ | p.2.2 = 1 ∧ p ∈ closedPerspectiveRealEpigraph f} =
      obverseEpigraphSlice f := by
  ext p
  let q : P := (p.1, p.2.1)
  have hslice :
      q ∈ {r : P | cl(perspective f) r ≤ (1 : EReal)} ↔
        q ∈ {r : P | obverse f r.2 ≤ r.1} := by
    simpa [q] using
      congrArg (fun s : Set P ↦ q ∈ s)
        (obverse_epigraph_eq_one_sublevel_closedPerspective f hf)
  constructor
  · intro hp
    rcases hp with ⟨hp_mu, hp_epi⟩
    constructor
    · exact hp_mu
    · have hp_sublevel : q ∈ {r : P | cl(perspective f) r ≤ (1 : EReal)} := by
        rw [mem_closedPerspectiveRealEpigraph_iff] at hp_epi
        simpa [hp_mu] using hp_epi
      exact hslice.mp hp_sublevel
  · intro hp
    rcases hp with ⟨hp_mu, hp_obv⟩
    constructor
    · exact hp_mu
    · have hp_sublevel : q ∈ {r : P | cl(perspective f) r ≤ (1 : EReal)} :=
        hslice.mpr hp_obv
      rw [mem_closedPerspectiveRealEpigraph_iff]
      rw [hp_mu]
      simpa [q] using hp_sublevel

end

/-! ### Text_15_0_35 (from Chap03) -/
noncomputable section

universe u

open ConvexERealFunction
open scoped Rockafellar

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]
variable [TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: the text says that the same cone `P = epi h` from Text 15.0.34 is also the
  smallest closed convex cone containing the `μ = 1` slice of `g = obverse f`.
- `core/canonical`: the owner API is already present in `Text_15_0_34`, namely
  `closedPerspectiveRealEpigraph`, the source-facing height-one slice
  `({(1 : ℝ)} ×ˢ epi f : Set (ℝ × E × ℝ))`, the source-facing owner
  `obverseEpigraphSlice` for the `μ = 1` slice of `g`, the bundled Chapter 15 owner
  `Function.IsNonnegativeClosedConvexZero`, and the generated closed cone
  `closure (ConvexCone.hull ℝ S : Set (ℝ × E × ℝ))`.
- `bridge/view`: no extra bridge owner is needed here; the source statement is written directly in
  the intrinsic triple coordinates `(λ, x, μ)`.

Domain-style sampling used here:
- `epi`;
- `closedPerspectiveRealEpigraph`;
- `closedPerspectiveRealEpigraph_eq_closure_convexConeHull_primalEpigraphSlice`;
- `obverseEpigraphSlice`;
- `ConvexCone.hull`.

Layer target: `source-facing`. The main labeled theorem states directly that `P` is the smallest
closed convex cone containing the source-facing owner slice `obverseEpigraphSlice f` of `g`, and
the companion theorem records that the canonical `f`-slice and this `g`-slice therefore generate
the same closed cone.

Ambient minimization: the public statements only use the same owner layer as
`Text_15_0_34`, namely a real topological module with additive-group structure. The concrete
`EuclideanSpace ℝ (Fin n)` model is a downstream specialization, not the owner level of this item.
-/

-- Proof sketch: Text 15.0.34 identifies `P = epi h` as a closed convex cone. Its `μ = 1` slice
-- is the source-facing owner `obverseEpigraphSlice f`. Under the standing Chapter
-- 15 hypotheses, including the normalization `f 0 = 0` already bundled by
-- `f.IsNonnegativeClosedConvexZero`, the text shows that `P` is the closure of its
-- intersection with the half-space `μ > 0`, so the closed convex cone generated by that slice is
-- all of `P`.
/-- Text 15.0.35: if `f` is convex, proper, lower semicontinuous, nonnegative, and satisfies
`f 0 = 0`, then the cone `P = epi h` from Text 15.0.34 is the smallest closed convex cone
containing the points `(λ, x, 1)` with `λ ≥ g(x)` for the obverse `g = obverse f`; equivalently,
`P` is the closure of the convex cone generated by the owner slice `obverseEpigraphSlice f`. -/
theorem closedPerspectiveRealEpigraph_eq_closure_convexConeHull_obverseEpigraphSlice
    (f : E → EReal) (hf : f.IsNonnegativeClosedConvexZero) :
    closedPerspectiveRealEpigraph f =
      closure (ConvexCone.hull ℝ (obverseEpigraphSlice f) : Set (ℝ × E × ℝ)) := sorry

-- Proof sketch: Text 15.0.34 already identifies `P` with the closed convex cone generated by the
-- `λ = 1` slice `({(1 : ℝ)} ×ˢ epi f)` from Text 15.0.34. The main theorem above identifies the
-- same cone `P` with the closed convex cone generated by the owner `μ = 1` slice
-- `obverseEpigraphSlice f`, so the two generated closed cones are equal. This is exactly the
-- statement that passing from `f` to `g` reverses the roles of `λ` and `μ` without changing the
-- underlying closed convex cone.
/-- The source-facing `λ = 1` slice `({(1 : ℝ)} ×ˢ epi f : Set (ℝ × E × ℝ))` of `f` and the
unit-`μ` slice of `g = obverse f`, namely `obverseEpigraphSlice f`, generate the same closed
convex cone in the triple coordinates `(λ, x, μ)`. -/
theorem closure_convexConeHull_primalEpigraphSlice_eq_closure_convexConeHull_obverseEpigraphSlice
    (f : E → EReal) (hf : f.IsNonnegativeClosedConvexZero) :
    closure
        (ConvexCone.hull ℝ ({(1 : ℝ)} ×ˢ epi f : Set (ℝ × E × ℝ)) : Set (ℝ × E × ℝ)) =
      closure (ConvexCone.hull ℝ (obverseEpigraphSlice f) : Set (ℝ × E × ℝ)) := by
  calc
    closure (ConvexCone.hull ℝ ({(1 : ℝ)} ×ˢ epi f : Set (ℝ × E × ℝ)) : Set (ℝ × E × ℝ)) =
        closedPerspectiveRealEpigraph f := by
      symm
      exact
        closedPerspectiveRealEpigraph_eq_closure_convexConeHull_primalEpigraphSlice
          f hf.isClosedProperConvex
    _ =
        closure (ConvexCone.hull ℝ (obverseEpigraphSlice f) : Set (ℝ × E × ℝ)) :=
      closedPerspectiveRealEpigraph_eq_closure_convexConeHull_obverseEpigraphSlice f hf

end

/-! ### Text_15_0_36 (from Chap03) -/
noncomputable section

open scoped ConvexFunctionPolar Pointwise RealInnerProductSpace Rockafellar

section

variable {E : Type*} [TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]

/-!
Source/core/bridge triage for this item.

- `source-facing`: the proposition identifies the positive sublevel sets of the obverse `g` of a
  Chapter 15 function `f` as homothetic copies of the reciprocal-level sublevel sets of `f`, and
  then, under the stronger polarity ambient, applies the same statement to the pair `(f*, fᵒ)`.
- `core/canonical`: the owner abstractions are `obverse`, `Function.rightScalarMul`,
  `f⋆`, `convex_function_polar`, and the class
  `Function.IsNonnegativeClosedConvexZero`, imported through `Text_15_0_38`.
- `bridge/view`: `Text_15_0_38` already supplies the two atomic equalities used here: the
  unit-scalar specialization from the obverse sublevel set to the unit sublevel set of
  the positive right scalar multiple corresponding to `f_α`, under the standing Chapter 15
  assumptions, and the general
  perspective-level rewrite of that unit sublevel set as a homothetic image.

Domain-style sampling used here:
- `obverse_sublevelSet_eq_perspectiveScale_unitSublevelSet`;
- `perspectiveScale_unitSublevelSet_eq_smul_sublevelSet`;
- `obverse`;
- `f⋆`;
- `convex_function_polar`;
- `Function.IsNonnegativeClosedConvexZero`.

Primitive data vs derived API:
- primitive inputs: the positive scalar `α` and the existing owner constructions `obverse`,
  `Function.rightScalarMul`, `f⋆`, and `convex_function_polar`; the standing Chapter 15
  hypothesis class enters both the main obverse-sublevel theorem and the later
  polar/conjugate specialization.
- derived API: the first theorem composes the two upstream atomic equalities from `Text_15_0_38`,
  and the second theorem specializes that source-facing result to the polar/conjugate pair.

Layer target: the first theorem is `source-facing`, derived directly from the existing owner-level
Chapter 15 module API, while the second theorem is the corresponding source-facing
polar/conjugate specialization on the finite-dimensional real inner-product layer required by
Theorem 15.5.
Ambient minimization: the sublevel-set identity for `obverse` itself lives on
`[TopologicalSpace E] [AddCommMonoid E] [Module ℝ E]`, matching `Text_15_0_37`; only the
polar/conjugate specialization uses the stronger ambient from `Theorem_15_5`.
-/

-- Proof sketch: compose the two atomic equalities already isolated in `Text_15_0_38`. Under the
-- Chapter 15 standing hypotheses on `f`, the `α`-sublevel set of `obverse f` is the unit
-- sublevel set of the positive right scalar multiple corresponding to `f_α`; for every `f`,
-- that unit sublevel set is
-- `α • {u | f u ≤ α⁻¹}`.
/-- Text 15.0.36: if `f : R^n → [0, +∞]` is convex, lower semicontinuous, and satisfies `f 0 = 0`,
then for every positive scalar `α`, the `α`-sublevel set of the obverse of `f` is the homothetic
image by `α` of the `α⁻¹`-sublevel set of `f`. Specializing `E` to
`EuclideanSpace ℝ (Fin n)` recovers the source statement on `R^n`. -/
theorem obverse_sublevelSet_eq_smul_sublevelSet
    (f : E → EReal) (hf : f.IsNonnegativeClosedConvexZero) (α : NNRealˣ) :
    {x : E | obverse f x ≤ ((α : ℝ) : EReal)} =
      (α : ℝ) • {x : E | f x ≤ (((α⁻¹ : NNRealˣ) : ℝ) : EReal)} := by
  have h₁ :
      {x : E | obverse f x ≤ ((α : ℝ) : EReal)} =
        {x : E | ((α : NNReal) •ʳ f) x ≤ (1 : EReal)} :=
    obverse_sublevelSet_eq_perspectiveScale_unitSublevelSet f hf α
  have h₂ :
      {x : E | ((α : NNReal) •ʳ f) x ≤ (1 : EReal)} =
        (α : ℝ) • {x : E | f x ≤ (((α⁻¹ : NNRealˣ) : ℝ) : EReal)} :=
    perspectiveScale_unitSublevelSet_eq_smul_sublevelSet f α
  exact h₁.trans h₂

end

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- Proof sketch: Theorem 15.5 identifies `fᵒ` with the obverse of
-- `f⋆`. Theorems 12.2 and 14.7 show that `f⋆` again belongs to the
-- standing Chapter 15 class. Applying the first theorem to `f⋆` at the positive
-- scalar `α⁻¹` then rewrites the left-hand side to the displayed reciprocal-level statement.
/-- For a function `f` in the class of Theorem 15.5, the `α⁻¹`-sublevel set of the polar `fᵒ` is
the homothetic image by `α⁻¹` of the `α`-sublevel set of the Fenchel conjugate `f*`. Specializing
`E` to `EuclideanSpace ℝ (Fin n)` recovers the source statement on `R^n`. -/
theorem polar_sublevelSet_eq_inv_smul_conjugate_sublevelSet_of_nonnegative_closed_convex_zero
    (f : E → EReal) (hf : f.IsNonnegativeClosedConvexZero) (α : NNRealˣ) :
    {xStar : E | fᵒ xStar ≤ (((α⁻¹ : NNRealˣ) : ℝ) : EReal)} =
      (((α⁻¹ : NNRealˣ) : ℝ)) • {xStar : E | f⋆ xStar ≤ ((α : ℝ) : EReal)} := by
  letI : f.IsNonnegativeClosedConvexZero := hf
  letI : (f⋆ : E → EReal).IsNonnegativeClosedConvexZero := inferInstance
  have hpolar : fᵒ = obverse f⋆ := by
    refine (obverse_obverse_eq_of_nonnegative_closed_convex_zero fᵒ inferInstance).symm.trans ?_
    exact
      congrArg obverse
        (obverse_convex_function_polar_eq_convexConjugate_of_nonnegative_closed_convex_zero
          f hf)
  rw [hpolar]
  simpa using obverse_sublevelSet_eq_smul_sublevelSet f⋆ inferInstance (α⁻¹)

end
