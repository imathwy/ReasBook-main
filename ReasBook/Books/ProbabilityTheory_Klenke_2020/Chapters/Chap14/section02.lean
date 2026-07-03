import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Exercise_14_2_1 (from Items/Chap14) -/
/- Exercise 14.2.1 (1): Item (i). The Gaussian convolution identity is the mathlib owner theorem
`ProbabilityTheory.gaussianReal_conv_gaussianReal`. -/
recall ProbabilityTheory.gaussianReal_conv_gaussianReal

/- Exercise 14.2.1 (2): Item (ii). The common-rate Gamma convolution identity is already
formalized in the project as `gammaMeasure_conv_same_rate`. -/
recall gammaMeasure_conv_same_rate

/- Exercise 14.2.1 (3): Item (iii). The centered Cauchy convolution identity is already
formalized in the project as `cauchyMeasure_conv_centered`. -/
recall cauchyMeasure_conv_centered

/-! ### Example_14_2 (from Items/Chap14) -/
universe u

/-- Example 14.2 (1): The product of `{1, ..., 6}` and `{1,2,3}` is the set of pairs whose
coordinates lie in the respective factors. -/
-- Proof sketch: unfold membership in the product set and compare it with the explicit set-builder.
lemma one_to_six_prod_one_to_three_eq_set_of_pair_mem :
    (({1, 2, 3, 4, 5, 6} : Set ℕ) ×ˢ ({1, 2, 3} : Set ℕ)) =
      {ω : ℕ × ℕ | ω.1 ∈ ({1, 2, 3, 4, 5, 6} : Set ℕ) ∧ ω.2 ∈ ({1, 2, 3} : Set ℕ)} := by
  ext ω
  rfl

/-- Example 14.2 (2): Real-valued functions on the index set `{1,2,3}` are canonically equivalent
to the usual three-dimensional real coordinate space. -/
noncomputable def real_functions_on_one_two_three_equiv_real_cube :
    (({1, 2, 3} : Finset ℕ) → ℝ) ≃ ℝ × ℝ × ℝ :=
  (Equiv.piCongrLeft (fun _ : Fin 3 ↦ ℝ)
      (({1, 2, 3} : Finset ℕ).equivFinOfCardEq
        (by decide : ({1, 2, 3} : Finset ℕ).card = 3))).trans <|
    (Equiv.piCongrLeft (fun _ : Option (Fin 2) ↦ ℝ) (finSuccEquiv 2)).trans <|
      Equiv.piOptionEquivProd.trans <|
        Equiv.prodCongr (Equiv.refl ℝ) (finTwoArrowEquiv ℝ)

/- Example 14.2 (3): When the index set is `ℕ` and every factor is `ℝ`, the product space is the
space of real sequences. -/
#check (ℕ → ℝ)

/- Example 14.2 (4): When both the index set and the common factor are `ℝ`, the product space is
the type of maps `ℝ → ℝ`. -/
#check (ℝ → ℝ)

/-! ### Exercise_14_2_2 (from Items/Chap14) -/
open scoped ENNReal
open MeasureTheory MeasureTheory.Lp ContinuousLinearMap

attribute [local instance] Classical.propDecidable

noncomputable section

universe u₁ u₂

variable {Ω₁ : Type u₁} {Ω₂ : Type u₂}
variable [MeasurableSpace Ω₁] [MeasurableSpace Ω₂]
variable (μ₁ : Measure Ω₁) (μ₂ : Measure Ω₂)
variable [SFinite μ₁] [SFinite μ₂]

/-- Turn the kernel row `a (t₁, ·)` into an `L²(μ₂)` class when that row is square-integrable,
and use `0` otherwise. -/
private def kernelSection (a : Ω₁ × Ω₂ → ℝ) (t₁ : Ω₁) : Ω₂ →₂[μ₂] ℝ :=
  if h : MemLp (fun t₂ ↦ a (t₁, t₂)) 2 μ₂ then
    h.toLp (fun t₂ ↦ a (t₁, t₂))
  else
    0

-- Proof sketch: on rows that belong to `L²(μ₂)`, the definition unfolds to `MemLp.toLp`, whose
-- coercion is almost everywhere equal to the original section.
/-- The row section agrees almost everywhere with the original kernel whenever the row belongs to
`L²(μ₂)`. -/
private theorem kernelSection_ae_eq (a : Ω₁ × Ω₂ → ℝ)
    (ha : ∀ᵐ t₁ ∂μ₁, MemLp (fun t₂ ↦ a (t₁, t₂)) 2 μ₂) :
    ∀ᵐ t₁ ∂μ₁, kernelSection μ₂ a t₁ =ᵐ[μ₂] fun t₂ ↦ a (t₁, t₂) := sorry

-- Proof sketch: apply Fubini/Tonelli to the square-integrable kernel to show that almost every row
-- is in `L²(μ₂)`, then use the previous sectionwise identification to obtain an `L²(μ₁; L²(μ₂))`
-- function.
/-- A square-integrable kernel on `Ω₁ × Ω₂` gives an `L²(μ₁)` family of `L²(μ₂)` rows. -/
private theorem kernelSection_memLp (a : Ω₁ × Ω₂ → ℝ)
    (ha : MemLp a 2 (μ₁.prod μ₂)) :
    MemLp (kernelSection μ₂ a) 2 μ₁ := sorry

/-- The rowwise `L²(μ₂)` family attached to an `L²(μ₁ ⊗ μ₂)` kernel, viewed as an element of
`L²(μ₁; L²(μ₂))`. This is the bridge from the source-level kernel to the canonical `lpPairing`
owner construction. -/
private def kernelRows (a : Ω₁ × Ω₂ → ℝ) (ha : MemLp a 2 (μ₁.prod μ₂)) :
    Ω₁ →₂[μ₁] (Ω₂ →₂[μ₂] ℝ) :=
  (kernelSection_memLp μ₁ μ₂ a ha).toLp (kernelSection μ₂ a)

/-- The continuous linear operator associated with an `L²` kernel, obtained from the canonical
`L²`-pairing `ContinuousLinearMap.lpPairing` applied to the rowwise `L²(μ₂)` family of the
kernel. -/
def hilbertSchmidtOperator (a : Ω₁ × Ω₂ → ℝ)
    (ha : MemLp a 2 (μ₁.prod μ₂)) :
    (Ω₁ →₂[μ₁] ℝ) →L[ℝ] (Ω₂ →₂[μ₂] ℝ) :=
  ((lsmul ℝ ℝ).flip.lpPairing μ₁ 2 2 (kernelRows μ₁ μ₂ a ha))

-- Proof sketch: rewrite `hilbertSchmidtOperator` via `lpPairing_eq_integral`, replace the row
-- representative by the original kernel section almost everywhere, and conclude with Fubini.
/-- Exercise 14.2.2: a square-integrable measurable kernel defines a continuous linear operator
from `L²(μ₁)` to `L²(μ₂)` by the usual integral formula. -/
theorem hilbertSchmidtOperator_ae_eq (a : Ω₁ × Ω₂ → ℝ)
    (ha : MemLp a 2 (μ₁.prod μ₂)) (f : Ω₁ →₂[μ₁] ℝ) :
    hilbertSchmidtOperator μ₁ μ₂ a ha f =ᵐ[μ₂]
      fun t₂ ↦ ∫ t₁, a (t₁, t₂) * f t₁ ∂μ₁ := sorry

/-! ### Exercise_14_2_3 (from Items/Chap14) -/
open Function MeasureTheory Set

open scoped BigOperators Topology

noncomputable section

-- Proof sketch: apply Stieltjes integration by parts on `(a, b]` for the two Stieltjes measures
-- associated to `Fμ` and `Fν`, and use the boundary terms together with the left-limit version of
-- the Stieltjes integral.
/-- Exercise 14.2.3: for two distribution functions `F_μ` and `F_ν` of locally finite measures on
`ℝ`, partial integration on `(a, b]` identifies the integral of `F_μ` against `dν` with the
boundary term `F_μ(b) F_ν(b) - F_μ(a) F_ν(a)` minus the integral of the left limit `F_ν(x-)`
against `dμ`. -/
theorem partialIntegration_stieltjes_eq_boundary_sub_leftLimIntegral
    (Fμ Fν : StieltjesFunction ℝ) {a b : ℝ} (hab : a < b) :
    ∫ x in Ioc a b, Fμ x ∂Fν.measure =
      Fμ b * Fν b - Fμ a * Fν a -
        ∫ x in Ioc a b, leftLim Fν x ∂Fμ.measure := sorry

-- Proof sketch: start from the partial-integration identity with the left-limit integral, then
-- decompose `∫ Fν(x-) dμ` into `∫ Fν dμ` minus the sum of the products of the jumps, using the
-- singleton-mass formula for Stieltjes measures.
/-- A companion reformulation of partial integration replaces the left-limit integral by the
ordinary integral of `F_ν` against `dμ` plus the sum of the products of the jump heights on
`(a, b]`. -/
theorem partialIntegration_stieltjes_eq_boundary_sub_integral_add_jumpSum
    (Fμ Fν : StieltjesFunction ℝ) {a b : ℝ} (hab : a < b) :
    ∫ x in Ioc a b, Fμ x ∂Fν.measure =
      Fμ b * Fν b - Fμ a * Fν a -
        ∫ x in Ioc a b, Fν x ∂Fμ.measure +
          ∑' x : Ioc a b, (Fμ x - leftLim Fμ x) * (Fν x - leftLim Fν x) := sorry

end
