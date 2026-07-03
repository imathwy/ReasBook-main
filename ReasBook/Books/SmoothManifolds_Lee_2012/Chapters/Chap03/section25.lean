

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Corollary_3_25 (from Chap03/Sec03_17) -/
-- Semantic search note: no `lean_leansearch` MCP tool was available in this session; the
-- statement shape was checked against local `Proposition_3_24` and the curve-velocity convention.

open scoped Manifold ContDiff

universe uE uH uM uE' uH' uN

section

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable {E' : Type uE'} [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable {H' : Type uH'} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
variable {N : Type uN} [TopologicalSpace N] [ChartedSpace H' N]

/-- Corollary 3.25 (Computing the Differential Using a Velocity Vector): if `γ` is a smooth curve
through `p` with velocity `v` at `0`, then applying the differential of `F` at `p` to `v` gives
the velocity of the composite curve `F ∘ γ` at `0`. -/
theorem differential_eq_velocity_of_composite_curve {J : Set ℝ} {F : M → N} {p : M}
    {v : TangentSpace I p} {γ : ℝ → M} (h0 : 0 ∈ J)
    (hJ : UniqueMDiffWithinAt 𝓘(ℝ) J 0) (hF : ContMDiff I I' ∞ F)
    (hγ : ContMDiffOn 𝓘(ℝ) I ∞ γ J) (hγ0 : γ 0 = p)
    (hv : curve_velocityWithin I γ J 0 = v) :
    mfderiv I I' F p v = curve_velocityWithin I' (F ∘ γ) J 0 := by
  subst p
  simpa [hv] using (composite_curve_velocity_of_contMDiff h0 hJ hF hγ).symm

end
