import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import SmoothManifolds_Lee_2012.Chap03.Sec03_17.Definition_3_17_extra_1

open scoped ContDiff Manifold

noncomputable section

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A smooth curve based at `p`, specified on some open interval `(-r, r)` around `0`. -/
structure SmoothCurveAt (p : M) where
  /-- The positive radius of the interval on which the curve is assumed smooth. -/
  radius : Set.Ioi (0 : ℝ)
  /-- The underlying parametrized curve. -/
  toFun : ℝ → M
  /-- The curve starts at the base point `p` at time `0`. -/
  source : toFun 0 = p
  /-- The curve is smooth on the interval `(-radius, radius)`. -/
  smooth : ContMDiffOn 𝓘(ℝ) I ∞ toFun (Set.Ioo (-radius) radius)

/-- A based smooth curve can be used as an ordinary function `ℝ → M`. -/
instance {p : M} : CoeFun (SmoothCurveAt I p) (fun _ ↦ ℝ → M) := ⟨SmoothCurveAt.toFun⟩

namespace SmoothCurveAt

/-- The open interval on which a based smooth curve is assumed smooth. -/
def sourceSet {p : M} (γ : SmoothCurveAt I p) : Set ℝ :=
  Set.Ioo (-γ.radius) γ.radius

/-- The tangent vector represented by a smooth curve based at `p`, computed within its defining
interval. -/
def tangentVector {p : M} (γ : SmoothCurveAt I p) : TangentSpace I p :=
  γ.source ▸ curve_velocityWithin I γ γ.sourceSet 0

end SmoothCurveAt

/-- Two based smooth curves are equivalent when every smooth real-valued test function smooth at
`p` has the same derivative at `0` along them. -/
def SmoothCurveEqv {p : M} (γ₁ γ₂ : SmoothCurveAt I p) : Prop :=
  ∀ ⦃f : M → ℝ⦄, ContMDiffAt I 𝓘(ℝ) ∞ f p →
    derivWithin (f ∘ γ₁) γ₁.sourceSet 0 = derivWithin (f ∘ γ₂) γ₂.sourceSet 0

omit [IsManifold I ∞ M] in
/-- Reflexivity of the smooth-curve velocity relation. -/
theorem smoothCurveEqv_refl {p : M} (γ : SmoothCurveAt I p) : SmoothCurveEqv I γ γ := by
  intro f hf
  rfl

omit [IsManifold I ∞ M] in
/-- Symmetry of the smooth-curve velocity relation. -/
theorem smoothCurveEqv_symm {p : M} {γ₁ γ₂ : SmoothCurveAt I p}
    (h : SmoothCurveEqv I γ₁ γ₂) : SmoothCurveEqv I γ₂ γ₁ := by
  intro f hf
  symm
  exact h hf

omit [IsManifold I ∞ M] in
/-- Transitivity of the smooth-curve velocity relation. -/
theorem smoothCurveEqv_trans {p : M} {γ₁ γ₂ γ₃ : SmoothCurveAt I p}
    (h₁ : SmoothCurveEqv I γ₁ γ₂) (h₂ : SmoothCurveEqv I γ₂ γ₃) :
    SmoothCurveEqv I γ₁ γ₃ := by
  intro f hf
  exact (h₁ hf).trans (h₂ hf)

/-- The setoid on based smooth curves coming from equality of all test-function derivatives at
time `0`. -/
def smoothCurveSetoid (p : M) : Setoid (SmoothCurveAt I p) where
  r := SmoothCurveEqv I
  iseqv := ⟨smoothCurveEqv_refl I, smoothCurveEqv_symm I, smoothCurveEqv_trans I⟩

/-- Definition 3.18-extra-3: the tangent vectors at `p` can be realized as the equivalence classes
of smooth curves based at `p`, where two curves are equivalent when every smooth real-valued
function smooth at `p` has the same derivative at `0` along them. -/
def CurveVelocityClass (p : M) : Type uM :=
  Quotient (smoothCurveSetoid I p)

/-- Equivalent smooth curves based at `p` determine the same tangent vector. -/
theorem smoothCurveAt_tangentVector_eq_of_eqv {p : M} (γ₁ γ₂ : SmoothCurveAt I p)
    (hγ : SmoothCurveEqv I γ₁ γ₂) : γ₁.tangentVector = γ₂.tangentVector := sorry

/-- The canonical map from local smooth-curve classes at `p` to the tangent space at `p`. -/
def curveVelocityClassToTangentSpace (p : M) : CurveVelocityClass I p → TangentSpace I p :=
  Quotient.lift (fun γ : SmoothCurveAt I p ↦ γ.tangentVector)
    (fun γ₁ γ₂ hγ ↦ smoothCurveAt_tangentVector_eq_of_eqv I γ₁ γ₂ hγ)

/-- The canonical map from local smooth-curve classes at `p` to the tangent space at `p` is a
bijection. -/
theorem curveVelocityClassToTangentSpace_bijective (p : M) :
    Function.Bijective (curveVelocityClassToTangentSpace I p) := sorry

/-- The local smooth-curve realization of tangent vectors at `p` is canonically equivalent to the
usual tangent space. -/
noncomputable def curveVelocityClassEquivTangentSpace (p : M) :
    CurveVelocityClass I p ≃ TangentSpace I p :=
  Equiv.ofBijective (curveVelocityClassToTangentSpace I p)
    (curveVelocityClassToTangentSpace_bijective I p)

@[simp] theorem curveVelocityClassEquivTangentSpace_apply {p : M} (x : CurveVelocityClass I p) :
    curveVelocityClassEquivTangentSpace I p x = curveVelocityClassToTangentSpace I p x := rfl
