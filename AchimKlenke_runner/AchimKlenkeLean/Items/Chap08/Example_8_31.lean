import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- The `x`-marginal density obtained by integrating a joint density on `ℝ × ℝ` over the second
coordinate. -/
noncomputable def first_marginal_density (f : ℝ → ℝ → ℝ≥0∞) : ℝ → ℝ≥0∞ :=
  fun x ↦ ∫⁻ y, f x y ∂(volume : Measure ℝ)

section JointDensity

variable (P : Measure Ω)
variable {X Y : Ω → ℝ} {f : ℝ → ℝ → ℝ≥0∞}
variable (hf : Measurable fun z : ℝ × ℝ ↦ f z.1 z.2)
variable
  (hXY_law : HasLaw (fun ω ↦ (X ω, Y ω))
    (((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity
      fun z : ℝ × ℝ ↦ f z.1 z.2) P)

-- Proof sketch: rewrite the joint law of `(X, Y)` as the density measure on `ℝ × ℝ`, then push
-- forward along `Prod.fst` and use Fubini/product-measure identities to identify the resulting
-- marginal with `volume.withDensity (first_marginal_density f)`.
/-- The first marginal of a joint Lebesgue density is obtained by integrating out the second
coordinate. -/
theorem hasLaw_fst_withDensity_first_marginal
    :
    HasLaw X ((volume : Measure ℝ).withDensity (first_marginal_density f)) P := sorry

-- Proof sketch: use the previous marginal-law statement to replace `P.map X` by
-- `volume.withDensity (first_marginal_density f)`, then show that the set where
-- `first_marginal_density f = 0` has zero mass for this density measure.
/-- Under the marginal law determined by a joint density, the marginal density is positive for
`P.map X`-almost every `x`. -/
theorem first_marginal_density_pos_ae_of_hasLaw_prod_withDensity
    :
    ∀ᵐ x ∂P.map X, 0 < first_marginal_density f x := sorry

variable [IsFiniteMeasure P]

-- Proof sketch: first identify the law of `(X, Y)` with the density measure
-- `((volume : Measure ℝ).prod (volume : Measure ℝ)).withDensity (fun z ↦ f z.1 z.2)`. Then apply
-- `condDistrib_ae_eq_of_measure_eq_compProd` to the canonical candidate kernel
-- `Kernel.withDensity (Kernel.const ℝ volume) (fun x y ↦ f x y / first_marginal_density f x)`,
-- using Fubini to show that its composition-product with `P.map X` recovers the joint law. The
-- previous positivity statement identifies the normalizing marginal factor on `P.map X`-almost
-- every `x`.
/-- Example 8.31: if `(X, Y)` has joint Lebesgue density `f`, then the regular conditional
distribution kernel of `Y` given `X` is, for `P.map X`-almost every `x`, the Lebesgue-density
kernel with density `y ↦ f x y / first_marginal_density f x`. -/
theorem condDistrib_ae_eq_withDensity_density_ratio_of_jointDensity :
    condDistrib Y X P =ᵐ[P.map X]
      Kernel.withDensity (Kernel.const ℝ (volume : Measure ℝ))
        (fun x y ↦ f x y / first_marginal_density f x) := sorry

-- Proof sketch: apply the kernel-valued conditional-density statement above and evaluate both
-- sides on `s` using `Kernel.withDensity_apply'`.
/-- For every measurable `s`, the conditional probability of `Y ∈ s` given `X = x` is the
integral of the conditional density over `s`, for `P.map X`-almost every `x`. -/
theorem condDistrib_ae_eq_lintegral_density_ratio_of_jointDensity
    {s : Set ℝ} (hs : MeasurableSet s) :
    (fun x ↦ condDistrib Y X P x s) =ᵐ[P.map X]
      fun x ↦ ∫⁻ y in s, f x y / first_marginal_density f x ∂(volume : Measure ℝ) := by
  sorry

end JointDensity
