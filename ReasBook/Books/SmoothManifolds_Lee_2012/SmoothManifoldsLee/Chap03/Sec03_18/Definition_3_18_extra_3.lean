import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import SmoothManifolds_Lee_2012.Chap03.Sec03_18.Definition_3_18_extra_1
import SmoothManifolds_Lee_2012.Chap03.Sec03_18.Definition_3_18_extra_2
import SmoothManifolds_Lee_2012.Chap03.Sec03_17.Proposition_3_23

open TopologicalSpace
open scoped ContDiff Manifold

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "𝒪∞" => smoothSheafCommRing I 𝓘(ℝ) M ℝ

-- Domain sampling pass:
-- `source-facing`: curve classes modulo first-order agreement at the base point.
-- `core/canonical`: the germ ring `C^∞_[p](I)` and its derivation space `𝒟_[p](I)`.
-- `bridge/view`: a curve represents a germ derivation by matching all smooth-germ derivatives.

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

omit [IsManifold I ∞ M] in
@[simp] theorem zero_mem_sourceSet {p : M} (γ : SmoothCurveAt I p) : (0 : ℝ) ∈ γ.sourceSet := by
  constructor
  · exact neg_lt_zero.mpr γ.radius.2
  · exact γ.radius.2

omit [IsManifold I ∞ M] in
theorem uniqueMDiffWithinAt_sourceSet {p : M} (γ : SmoothCurveAt I p) :
    UniqueMDiffWithinAt 𝓘(ℝ) γ.sourceSet 0 :=
  isOpen_Ioo.uniqueMDiffWithinAt γ.zero_mem_sourceSet

/-- The tangent vector represented by a smooth curve based at `p`, computed within its defining
interval. -/
def tangentVector {p : M} (γ : SmoothCurveAt I p) : TangentSpace I p :=
  γ.source ▸ curve_velocityWithin I γ γ.sourceSet 0

/-- The derivative at `0` obtained by testing a based smooth curve against an ambient real-valued
function. -/
def testDerivative {p : M} (γ : SmoothCurveAt I p) (F : M → ℝ) : ℝ :=
  derivWithin (F ∘ γ) γ.sourceSet 0

end SmoothCurveAt

/-- Auxiliary representative-level datum: a smooth ambient extension near `p` of a local smooth
test function on `U`. -/
def IsLocalExtensionAt (p : M) {U : Opens M}
    (f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯) (F : M → ℝ) : Prop :=
  p ∈ U ∧ ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ ContMDiffOn I 𝓘(ℝ) ∞ F V ∧
    ∀ x : U, x.1 ∈ V → F x = f x

namespace SmoothCurveAt

/-- A based smooth curve has germ derivative `r` on `φ : C^∞_[p](I)` if every local representative
of `φ` and every smooth ambient extension near `p` have derivative `r` at `0` along the curve. -/
def HasGermDerivative {p : M} (γ : SmoothCurveAt I p) (φ : C^∞_[p](I)) (r : ℝ) : Prop :=
  ∀ ⦃U : Opens M⦄ (hpU : p ∈ U) (f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯),
    𝒪∞.presheaf.germ U p hpU f = φ →
      ∀ ⦃F : M → ℝ⦄, IsLocalExtensionAt I p f F →
        testDerivative I γ F = r

/-- A based smooth curve represents the germ derivation `v` when the curve's derivative relation on
smooth germs is exactly evaluation by `v`. -/
def RepresentsDerivation {p : M} (γ : SmoothCurveAt I p) (v : 𝒟_[p](I)) : Prop :=
  ∀ φ : C^∞_[p](I), ∀ r : ℝ, HasGermDerivative I γ φ r ↔ v φ = r

/-- A germ derivation represented by a based smooth curve is unique. -/
theorem representsDerivation_unique {p : M} {γ : SmoothCurveAt I p} {v₁ v₂ : 𝒟_[p](I)}
    (hv₁ : SmoothCurveAt.RepresentsDerivation I γ v₁)
    (hv₂ : SmoothCurveAt.RepresentsDerivation I γ v₂) :
    v₁ = v₂ := sorry

/-- Every based smooth curve induces a germ derivation on the smooth-germ ring at the base point. -/
theorem exists_representingDerivation {p : M} (γ : SmoothCurveAt I p) :
    ∃ v : 𝒟_[p](I), SmoothCurveAt.RepresentsDerivation I γ v := sorry

end SmoothCurveAt

/-- Two based smooth curves are equivalent when they represent the same germ derivation at `p`. -/
def SmoothCurveEqv {p : M} (γ₁ γ₂ : SmoothCurveAt I p) : Prop :=
  ∃ v : 𝒟_[p](I),
    SmoothCurveAt.RepresentsDerivation I γ₁ v ∧
      SmoothCurveAt.RepresentsDerivation I γ₂ v

omit [IsManifold I ∞ M] in
/-- Reflexivity of the smooth-curve velocity relation. -/
theorem smoothCurveEqv_refl {p : M} (γ : SmoothCurveAt I p) : SmoothCurveEqv I γ γ := by
  sorry

omit [IsManifold I ∞ M] in
/-- Symmetry of the smooth-curve velocity relation. -/
theorem smoothCurveEqv_symm {p : M} {γ₁ γ₂ : SmoothCurveAt I p}
    (h : SmoothCurveEqv I γ₁ γ₂) : SmoothCurveEqv I γ₂ γ₁ := by
  rcases h with ⟨v, hv₁, hv₂⟩
  exact ⟨v, hv₂, hv₁⟩

omit [IsManifold I ∞ M] in
/-- Transitivity of the smooth-curve velocity relation. -/
theorem smoothCurveEqv_trans {p : M} {γ₁ γ₂ γ₃ : SmoothCurveAt I p}
    (h₁ : SmoothCurveEqv I γ₁ γ₂) (h₂ : SmoothCurveEqv I γ₂ γ₃) :
    SmoothCurveEqv I γ₁ γ₃ := sorry

/-- The setoid on based smooth curves coming from equality of the represented germ derivation at
time `0`. -/
def smoothCurveSetoid (p : M) : Setoid (SmoothCurveAt I p) where
  r := SmoothCurveEqv I
  iseqv := ⟨smoothCurveEqv_refl I, smoothCurveEqv_symm I, smoothCurveEqv_trans I⟩

/-- Definition 3.18-extra-3: the curve-velocity classes at `p` are equivalence classes of based
smooth curves under equality of the germ derivation they represent at `0`. -/
def CurveVelocityClass (p : M) :=
  Quotient (smoothCurveSetoid I p)

section Boundaryless

variable [BoundarylessManifold I M]

/-- Every tangent vector on a boundaryless smooth manifold is represented by a based smooth curve
through the base point on some open interval around `0`. -/
theorem exists_smoothCurveAt_tangentVector_eq (p : M) (v : TangentSpace I p) :
    ∃ γ : SmoothCurveAt I p, γ.tangentVector = v := by
  rcases exists_open_interval_curve_with_velocity_of_isInteriorPoint p v
      BoundarylessManifold.isInteriorPoint with
    ⟨r, γ, hγsmooth, hγ0, hγv⟩
  refine ⟨⟨r, γ, hγ0, hγsmooth⟩, ?_⟩
  simpa [SmoothCurveAt.tangentVector, SmoothCurveAt.sourceSet] using hγv

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

end Boundaryless
