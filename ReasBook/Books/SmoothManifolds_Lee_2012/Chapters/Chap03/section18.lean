import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.Sheaf.Smooth
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.RingTheory.Derivation.Basic

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_3_18_extra_1 (from Chap03/Sec03_18) -/
noncomputable section

open TopologicalSpace CategoryTheory

open scoped ContDiff Manifold

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type} [TopologicalSpace H]
variable (I : ModelWithCorners ℝ E H)
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]

local notation "𝒪∞" => smoothSheafCommRing I 𝓘(ℝ) M ℝ

/-- The germ ring of smooth real-valued functions at `p`, identified with the canonical stalk of
`smoothSheafCommRing I 𝓘(ℝ) M ℝ` at `p`. -/
abbrev smoothGermRing (I : ModelWithCorners ℝ E H) (p : M) :=
  ↑((smoothSheafCommRing I 𝓘(ℝ) M ℝ).presheaf.stalk p)

set_option quotPrecheck false in
scoped[Manifold] notation "C^∞_[" x "](" IM ")" =>
  smoothGermRing IM x

/- Definition 3.18-extra-1 (core/canonical recall): the textbook germ ring `C_p^∞(M)` is the
canonical stalk `(smoothSheafCommRing I 𝓘(ℝ) M ℝ).presheaf.stalk p`, written `C^∞_[p](I)` in the
`Manifold` scope. -/
#check (smoothSheafCommRing I 𝓘(ℝ) M ℝ).presheaf.stalk

/-- Constant smooth functions endow `C_p^∞(M)` with its natural `ℝ`-algebra structure. -/
instance smooth_function_germs_at_algebra (p : M) :
    Algebra ℝ C^∞_[p](I) :=
  letI : Algebra ℝ C^∞⟮I, (⊤ : Opens M); 𝓘(ℝ), ℝ⟯ := inferInstance
  RingHom.toAlgebra
    ((𝒪∞.presheaf.Γgerm p).hom.comp (algebraMap ℝ C^∞⟮I, (⊤ : Opens M); 𝓘(ℝ), ℝ⟯))

namespace smoothSheafCommRing

-- Proof sketch: use `TopCat.Presheaf.germ_eq` to pass from equality in the stalk to equality after
-- restricting to a smaller open neighborhood, and use `TopCat.Presheaf.germ_ext` for the converse.
/-- Two smooth local functions determine the same element of `C^∞_[p](I)` exactly when their
restrictions agree on some smaller neighborhood of `p`. -/
theorem germ_eq_iff {p : M} {U V : Opens M} (hpU : p ∈ U) (hpV : p ∈ V)
    (f : C^∞⟮I, U; 𝓘(ℝ), ℝ⟯) (g : C^∞⟮I, V; 𝓘(ℝ), ℝ⟯) :
    𝒪∞.presheaf.germ U p hpU f = 𝒪∞.presheaf.germ V p hpV g ↔
      ∃ (W : Opens M) (_ : p ∈ W) (iWU : W ⟶ U) (iWV : W ⟶ V),
        𝒪∞.presheaf.map iWU.op f = 𝒪∞.presheaf.map iWV.op g := by
  constructor
  · intro h
    exact 𝒪∞.presheaf.germ_eq p hpU hpV f g h
  · rintro ⟨W, hpW, iWU, iWV, hfg⟩
    exact 𝒪∞.presheaf.germ_ext W hpW iWU iWV hfg

end smoothSheafCommRing

/-! ### Definition_3_18_extra_2 (from Chap03/Sec03_18) -/
-- This file uses the smooth-germ stalk API from
-- `Definition_3_18_extra_1`.

noncomputable section

open scoped ContDiff Manifold

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]

/-- Evaluation at `p` gives the stalk `C_p^∞(M)` its natural algebra structure on `ℝ`. -/
instance smooth_function_germs_at_evalAlgebra (p : M) :
    Algebra C^∞_[p](I) ℝ :=
  (smoothSheafCommRing.eval I 𝓘(ℝ) M ℝ p).toAlgebra

/-- Definition 3.18-extra-2: the textbook vector space `𝒟_p M` of derivations of `C_p^∞(M)` is
the type of `ℝ`-derivations from the germ ring at `p` to `ℝ`, where `ℝ` is viewed as a
`C_p^∞(M)`-algebra by evaluation at `p`. The model-with-corners parameter is explicit because it
is not recoverable from `p` alone. -/
abbrev smooth_germ_derivation_at (I : ModelWithCorners ℝ E H) (p : M) :=
  Derivation ℝ C^∞_[p](I) ℝ

/-- A smooth germ derivation satisfies the Leibniz rule on the smooth germ ring. -/
theorem smooth_germ_derivation_at_map_mul (I : ModelWithCorners ℝ E H) (p : M)
    (v : smooth_germ_derivation_at I p) (f g : C^∞_[p](I)) :
    v (f * g) = f • v g + g • v f := sorry

/-! ### Definition_3_18_extra_3 (from Chap03/Sec03_18) -/
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

/-! ### Definition_3_18_extra_4 (from Chap03/Sec03_18) -/
noncomputable section

open Bundle
open scoped Manifold

universe u𝕜 uE uH uM

variable
  {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

variable (I)

/-- Definition 3.18-extra-4: a coordinate tangent vector at `p` is a choice of model-space
component in every preferred chart containing `p`, compatible under the tangent-coordinate change
maps on overlaps. This is the coordinate-family view of the canonical tangent space
`TangentSpace I p`, not a second owner type. -/
def IsCoordinateTangentVector (p : M)
    (component : {x : M // p ∈ (chartAt H x).source} → E) : Prop :=
  ∀ x y : {x : M // p ∈ (chartAt H x).source},
    tangentCoordChange I x.1 y.1 p (component x) = component y

/-- The coordinate-family realization of `TangentSpace I p` as compatible preferred-chart
components. -/
structure CoordinateTangentVector (p : M) where
  component : {x : M // p ∈ (chartAt H x).source} → E
  compatible : IsCoordinateTangentVector I p component

namespace CoordinateTangentVector

instance {p : M} : CoeFun (CoordinateTangentVector I p)
    (fun _ ↦ {x : M // p ∈ (chartAt H x).source} → E) := ⟨component⟩

@[simp] theorem component_apply {p : M} (v : CoordinateTangentVector I p)
    (x : {x : M // p ∈ (chartAt H x).source}) : v.component x = v x := rfl

theorem compatible_apply {p : M} (v : CoordinateTangentVector I p)
    (x y : {x : M // p ∈ (chartAt H x).source}) :
    tangentCoordChange I x.1 y.1 p (v x) = v y :=
  v.compatible x y

@[ext] theorem ext {p : M} {v w : CoordinateTangentVector I p}
    (h : ∀ x, v x = w x) : v = w := by
  cases v with
  | mk componentv hv =>
      cases w with
      | mk componentw hw =>
          have hcomponent : componentv = componentw := funext h
          cases hcomponent
          have hproof : hv = hw := Subsingleton.elim _ _
          cases hproof
          rfl

end CoordinateTangentVector

variable {I}

namespace TangentSpace

/-- The component of a tangent vector in the preferred chart centered at `x`, written in the model
vector space. -/
def coordinateComponent {p : M} (v : TangentSpace I p)
    (x : {x : M // p ∈ (chartAt H x).source}) : E :=
  (trivializationAt E (TangentSpace I) x.1).linearEquivAt 𝕜 p x.2 v

/-- The chart components of a tangent vector satisfy the usual coordinate transformation rule on
overlapping charts. -/
theorem coordinateComponent_isCoordinateTangentVector {p : M} (v : TangentSpace I p) :
    IsCoordinateTangentVector I p (coordinateComponent v) := by
  intro x y
  let ex := trivializationAt E (TangentSpace I) x.1
  let ey := trivializationAt E (TangentSpace I) y.1
  have hp : p ∈ ex.baseSet ∩ ey.baseSet := by
    change p ∈ (chartAt H x.1).source ∩ (chartAt H y.1).source
    exact ⟨x.2, y.2⟩
  have hchange : ex.coordChangeL 𝕜 ey p = tangentCoordChange I x.1 y.1 p := by
    simpa [ex, ey] using tangent_coordinates_change hp
  calc
    tangentCoordChange I x.1 y.1 p (coordinateComponent v x)
      = ex.coordChangeL 𝕜 ey p (coordinateComponent v x) := by
          simpa using congrArg (fun f : E →L[𝕜] E ↦ f (coordinateComponent v x)) hchange.symm
    _ = coordinateComponent v y := by
          rw [Bundle.Trivialization.coordChangeL_apply ex ey hp]
          have hx : ex.symm p (coordinateComponent v x) = v := by
            simpa [coordinateComponent, ex] using
              (ex.symm_apply_apply_mk x.2 v : ex.symm p (ex ⟨p, v⟩).2 = v)
          simpa [coordinateComponent, ey] using
            congrArg (fun w : TangentSpace I p ↦ (ey ⟨p, w⟩).2) hx

/-- The compatible preferred-chart components of a tangent vector. -/
def toCoordinateTangentVector {p : M} (v : TangentSpace I p) : CoordinateTangentVector I p :=
  ⟨coordinateComponent v, coordinateComponent_isCoordinateTangentVector v⟩

end TangentSpace

namespace CoordinateTangentVector

/-- Reconstruct a tangent vector from a compatible family of preferred-chart components by reading
the family in the preferred chart centered at the base point. -/
def toTangentSpace {p : M} (v : CoordinateTangentVector I p) : TangentSpace I p :=
  let x : {x : M // p ∈ (chartAt H x).source} := ⟨p, mem_chart_source H p⟩
  (trivializationAt E (TangentSpace I) p).symm p (v x)

@[simp] theorem coordinateComponent_toTangentSpace {p : M} (v : CoordinateTangentVector I p)
    (y : {x : M // p ∈ (chartAt H x).source}) :
    TangentSpace.coordinateComponent (toTangentSpace v) y = v y := by
  let x : {x : M // p ∈ (chartAt H x).source} := ⟨p, mem_chart_source H p⟩
  let ep := trivializationAt E (TangentSpace I) p
  let ey := trivializationAt E (TangentSpace I) y.1
  have hpy : p ∈ ep.baseSet ∩ ey.baseSet := by
    change p ∈ (chartAt H p).source ∩ (chartAt H y.1).source
    exact ⟨mem_chart_source H p, y.2⟩
  have hchange : ep.coordChangeL 𝕜 ey p = tangentCoordChange I p y.1 p := by
    simpa [ep, ey] using tangent_coordinates_change hpy
  calc
    TangentSpace.coordinateComponent (toTangentSpace v) y
      = (ey ⟨p, ep.symm p (v x)⟩).2 := by
          simp [TangentSpace.coordinateComponent, toTangentSpace, ep, ey, x]
    _ = ep.coordChangeL 𝕜 ey p (v x) := by
          symm
          exact Bundle.Trivialization.coordChangeL_apply ep ey hpy (v x)
    _ = tangentCoordChange I p y.1 p (v x) := by
          simpa using congrArg (fun f : E →L[𝕜] E ↦ f (v x)) hchange
    _ = v y := v.compatible x y

@[simp] theorem toTangentSpace_toCoordinateTangentVector {p : M} (v : TangentSpace I p) :
    toTangentSpace (TangentSpace.toCoordinateTangentVector v) = v := by
  let x : {x : M // p ∈ (chartAt H x).source} := ⟨p, mem_chart_source H p⟩
  let ep := trivializationAt E (TangentSpace I) p
  change ep.symm p ((ep ⟨p, v⟩).2) = v
  exact ep.symm_apply_apply_mk x.2 v

@[simp] theorem toCoordinateTangentVector_toTangentSpace {p : M} (v : CoordinateTangentVector I p) :
    TangentSpace.toCoordinateTangentVector (toTangentSpace v) = v := by
  ext y
  exact coordinateComponent_toTangentSpace v y

/-- The coordinate-family realization of tangent vectors is canonically equivalent to the tangent
space itself. -/
noncomputable def equivTangentSpace (p : M) : CoordinateTangentVector I p ≃ TangentSpace I p where
  toFun := toTangentSpace
  invFun := TangentSpace.toCoordinateTangentVector
  left_inv := toCoordinateTangentVector_toTangentSpace
  right_inv := toTangentSpace_toCoordinateTangentVector

end CoordinateTangentVector

/-! ### Proposition_3_18 (from Chap03/Sec03_16) -/
open Bundle
open scoped Manifold ContDiff

universe u v

variable {n : ℕ}
variable {H : Type u} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) H}
variable {M : Type v} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (∞ : ℕ∞ω) M]

-- `lean_leansearch` was unavailable in this session, so this file uses the local Section 3.16
-- tangent-bundle precedent together with the canonical mathlib tangent-bundle API.

#synth TopologicalSpace (TangentBundle I M)
#synth ChartedSpace (ModelProd H (EuclideanSpace ℝ (Fin n))) (TangentBundle I M)
#synth IsManifold I.tangent (∞ : ℕ∞ω) (TangentBundle I M)

/-- Proposition 3.18: mathlib's canonical tangent bundle `TangentBundle I M` carries its natural
topology and smooth manifold structure modeled on `I.tangent`, which corresponds to the textbook's
`2n`-dimensional smooth structure when `M` is an `n`-manifold, and its projection to `M` is
smooth. -/
theorem tangentBundle_contMDiff_proj :
    ContMDiff I.tangent I (∞ : ℕ∞ω) (TotalSpace.proj : TangentBundle I M → M) := sorry
