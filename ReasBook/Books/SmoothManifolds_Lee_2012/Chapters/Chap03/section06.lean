import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Problem_3_6 (from Chap03/Sec03_20) -/
open scoped Manifold ContDiff RealInnerProductSpace

noncomputable section

-- Local API note: semantic `lean_leansearch` was unavailable in this session; mathlib's sphere
-- manifold instance for the Euclidean `ℂ²` model uses the `L²` product type `WithLp 2 (ℂ × ℂ)`.
local notation "C2" => WithLp 2 (ℂ × ℂ)
local notation "unitSphere3" => Metric.sphere (0 : C2) 1

-- Proof sketch: identify `ℂ` with `ℝ²`, use additivity of `finrank` on products, and simplify.
/-- The real vector space underlying `ℂ²` has dimension `4`. -/
theorem finrank_real_complex_pair : Module.finrank ℝ C2 = 3 + 1 := sorry

/-- The standard sphere in `ℂ²` uses the real-dimension-four sphere manifold structure. -/
local instance complex_pair_finrank_fact : Fact (Module.finrank ℝ C2 = 3 + 1) :=
  ⟨finrank_real_complex_pair⟩

-- Proof sketch: `|exp (tI)| = 1`, so multiplying each complex coordinate by `exp (tI)` preserves
-- the sum of squared norms that defines the unit sphere in `ℂ²`.
/-- Rotating both complex coordinates of a point of `S³ ⊆ ℂ²` by the same phase keeps the point on
the sphere. -/
theorem sphere3_phase_curve_mem (z : unitSphere3) (t : ℝ) :
    WithLp.toLp 2
        (Complex.exp (t * Complex.I) * (z : C2).fst,
          Complex.exp (t * Complex.I) * (z : C2).snd) ∈
      unitSphere3 := sorry

/-- The phase-rotation curve on `S³` through `z`, obtained by multiplying both complex coordinates
by `exp (it)`. -/
def sphere3_phase_curve (z : unitSphere3) : ℝ → unitSphere3 :=
  fun t ↦ ⟨WithLp.toLp 2
      (Complex.exp (t * Complex.I) * (z : C2).fst,
        Complex.exp (t * Complex.I) * (z : C2).snd),
    sphere3_phase_curve_mem z t⟩

-- Proof sketch: unfold `sphere3_phase_curve`; the underlying ambient point is the ordered pair
-- used in its definition.
/-- The ambient-value formula for the phase-rotation curve on `S³`. -/
theorem sphere3_phase_curve_coe (z : unitSphere3) (t : ℝ) :
    ((sphere3_phase_curve z t : unitSphere3) : C2) =
      WithLp.toLp 2
        (Complex.exp (t * Complex.I) * (z : C2).fst,
          Complex.exp (t * Complex.I) * (z : C2).snd) := sorry

-- Proof sketch: first view the curve as the codomain restriction of the smooth ambient map
-- `t ↦ exp (tI) • z`; smoothness follows from smoothness of `Complex.exp` and multiplication.
-- For the velocity, compute the derivative in `ℂ²`, note that it equals multiplication by
-- `I * exp (tI)`, and use injectivity of the sphere inclusion differential together with `z ≠ 0`.
/-- Problem 3-6: for each `z ∈ S³ ⊆ ℂ²`, the curve `t ↦ (e^{it} z¹, e^{it} z²)` is smooth and its
velocity is nonzero at every parameter value. -/
theorem sphere3_phase_curve_smooth_and_velocity_ne_zero (z : unitSphere3) :
    ContMDiff 𝓘(ℝ) (𝓡 3) ∞ (sphere3_phase_curve z) ∧
      ∀ t : ℝ,
        mfderiv (𝓘(ℝ)) (𝓡 3) (sphere3_phase_curve z) t
          (show TangentSpace 𝓘(ℝ) t from (1 : ℝ)) ≠ 0 := sorry

/-! ### Proposition_3_6 (from Chap03/Sec03_14) -/
noncomputable section

open scoped Manifold ContDiff

section CompositionAndIdentity

universe u𝕜 uE uE' uE'' uH uH' uH'' uM uN uP

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {E'' : Type uE''} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {H'' : Type uH''} [TopologicalSpace H'']
variable {I : ModelWithCorners 𝕜 E H}
variable {I' : ModelWithCorners 𝕜 E' H'}
variable {I'' : ModelWithCorners 𝕜 E'' H''}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]
variable {P : Type uP} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold I'' ∞ P]
variable {F : M → N} {G : N → P} {p : M}

/- Proposition 3.6 (1): the differential `dFₚ` is linear; in mathlib this is the manifold
derivative `mfderiv I I' F p`, already typed as a continuous linear map
`TangentSpace I p →L[𝕜] TangentSpace I' (F p)`. -/
#check (mfderiv I I' F p : TangentSpace I p →L[𝕜] TangentSpace I' (F p))

-- Proof sketch: smoothness gives manifold differentiability at `p` for `F` and at `F p` for `G`;
-- then apply the chain rule theorem `mfderiv_comp`.
/- Proposition 3.6 (1): the differential of a composite is the composite of the differentials at
the relevant points. -/
theorem mfderiv_comp_of_smooth (hF : ContMDiff I I' ∞ F) (hG : ContMDiff I' I'' ∞ G) :
    mfderiv I I'' (G ∘ F) p = (mfderiv I' I'' G (F p)).comp (mfderiv I I' F p) := by
  have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
  exact mfderiv_comp p (hG.contMDiffAt.mdifferentiableAt hn) (hF.contMDiffAt.mdifferentiableAt hn)

/- Proposition 3.6 (3): the differential of the identity map is the identity linear map on the
tangent space. -/
#check mfderiv_id

end CompositionAndIdentity

section Diffeomorphisms

universe u𝕜 uE uE' uH uH' uM uN

variable {𝕜 : Type u𝕜} [NontriviallyNormedField 𝕜]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
variable {H : Type uH} [TopologicalSpace H]
variable {H' : Type uH'} [TopologicalSpace H']
variable {I : ModelWithCorners 𝕜 E H}
variable {I' : ModelWithCorners 𝕜 E' H'}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]
variable {n : ℕ∞ω}

/- Proposition 3.6 (2): the differential of a `C^1` diffeomorphism is the forward map of the
canonical tangent-space equivalence `Φ.mfderivToContinuousLinearEquiv one_ne_zero p`. -/
#check Diffeomorph.mfderivToContinuousLinearEquiv
#check Diffeomorph.mfderivToContinuousLinearEquiv_coe

-- Proof sketch: the inverse of `Φ.mfderivToContinuousLinearEquiv hn p` is defined using
-- the derivative of `Φ.symm`, so the inverse linear map is exactly `mfderiv I' I Φ.symm (Φ p)`.
/-- Proposition 3.6 (3), in the canonical `C^n` form used later: for a diffeomorphism with
`n ≠ 0`, the inverse of the differential is the differential of the inverse diffeomorphism.
The source proposition is the specialization `n = 1`. -/
theorem diffeomorph_mfderiv_symm_eq_symm
    (Φ : M ≃ₘ^n⟮I, I'⟯ N) (hn : n ≠ 0) (p : M) :
    mfderiv I' I Φ.symm (Φ p) =
      ((Φ.mfderivToContinuousLinearEquiv hn p).symm :
        TangentSpace I' (Φ p) →L[𝕜] TangentSpace I p) := by
  have hΦ : IsLocalDiffeomorphAt I I' n Φ p := Φ.isLocalDiffeomorph p
  have hlocalInverse : hΦ.localInverse =ᶠ[nhds (Φ p)] Φ.symm := by
    refine Filter.eventuallyEq_of_mem
      (hΦ.localInverse_open_source.mem_nhds hΦ.localInverse_mem_source) ?_
    intro y hy
    apply Φ.injective
    simpa using hΦ.localInverse_right_inv hy
  have h₁ : mfderiv I' I Φ.symm (Φ p) = mfderiv I' I hΦ.localInverse (Φ p) := by
    symm
    exact hlocalInverse.mfderiv_eq
  have h₂ : mfderiv I' I hΦ.localInverse (Φ p) =
      ((hΦ.mfderivToContinuousLinearEquiv hn).symm :
        TangentSpace I' (Φ p) →L[𝕜] TangentSpace I p) := rfl
  have h₃ : ((hΦ.mfderivToContinuousLinearEquiv hn).symm :
      TangentSpace I' (Φ p) →L[𝕜] TangentSpace I p) =
      ((Φ.mfderivToContinuousLinearEquiv hn p).symm :
        TangentSpace I' (Φ p) →L[𝕜] TangentSpace I p) := rfl
  exact h₁.trans (h₂.trans h₃)

end Diffeomorphisms
