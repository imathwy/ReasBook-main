import SmoothManifolds_Lee_2012.SmoothManifoldsLee.Chap03.Sec03_17.Definition_3_17_extra_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped Manifold ContDiff

universe uE uH uM uE' uH' uN

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type uH'} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold I' ∞ N]

-- Proof sketch: apply `mfderiv_comp_mfderivWithin` to `F ∘ γ` along `J`, then evaluate the
-- resulting linear-map identity at the unit tangent vector at `t₀`.
omit [IsManifold I ∞ M] [IsManifold I' ∞ N] in
/-- Helper for Proposition 3.24: the velocity of a composite curve is obtained by applying the
differential of `F` to the velocity of `γ` at the same parameter value once the needed
pointwise differentiability hypotheses are available. -/
theorem composite_curve_velocity {J : Set ℝ} {t₀ : ℝ} {F : M → N} {γ : ℝ → M}
    (hJ : UniqueMDiffWithinAt 𝓘(ℝ) J t₀) (hF : MDifferentiableAt I I' F (γ t₀))
    (hγ : MDifferentiableWithinAt 𝓘(ℝ) I γ J t₀) :
    curve_velocityWithin I' (F ∘ γ) J t₀ =
      mfderiv I I' F (γ t₀) (curve_velocityWithin I γ J t₀) := by
  simpa using
    DFunLike.congr_fun (mfderiv_comp_mfderivWithin t₀ hF hγ hJ)
      (show TangentSpace 𝓘(ℝ) t₀ from (1 : ℝ))

-- The textbook smoothness hypotheses imply the pointwise differentiability assumptions used in
-- `composite_curve_velocity`.
omit [IsManifold I ∞ M] [IsManifold I' ∞ N] in
/-- Proposition 3.24 (The Velocity of a Composite Curve): if `F : M → N` is smooth and
`γ : J → M` is a smooth curve, then the velocity of the composite curve `F ∘ γ` at `t₀`
is the differential of `F` applied to the velocity of `γ` at `t₀`. -/
theorem composite_curve_velocity_of_contMDiff {J : Set ℝ} {t₀ : ℝ} {F : M → N} {γ : ℝ → M}
    (ht₀ : t₀ ∈ J) (hJ : UniqueMDiffWithinAt 𝓘(ℝ) J t₀) (hF : ContMDiff I I' ∞ F)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ J) :
    curve_velocityWithin I' (F ∘ γ) J t₀ =
      mfderiv I I' F (γ t₀) (curve_velocityWithin I γ J t₀) := by
  exact composite_curve_velocity hJ (hF.mdifferentiableAt (by simp))
    (hγ.mdifferentiableOn (by simp) t₀ ht₀)

end
