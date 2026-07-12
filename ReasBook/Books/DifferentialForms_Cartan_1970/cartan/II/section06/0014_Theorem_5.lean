import Mathlib
import DifferentialForms_Cartan_1970.II.section05.«0026_Definition_II_1_extra_16»
import DifferentialForms_Cartan_1970.II.section05.«0033_Definition_II_1_extra_20»
import DifferentialForms_Cartan_1970.II.section06.«0005_Corollary_1»
import DifferentialForms_Cartan_1970.III.section11.frozen_0003_Theorem_III_5_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators

noncomputable section

universe u

section

variable {ι : Type u} [Fintype ι] {K D : Set ℂ} (Γ : ι → ClosedPath ℂ)
variable (hΓ : IsOrientedBoundaryOf K Γ) (hKD : K ⊆ D) (hD : IsOpen D) (f : ℂ → ℂ)
variable (hf : DifferentiableOn ℂ f D)

include hΓ hKD hD f hf

omit hΓ hKD hD f hf in
/-- Helper for Theorem 5: an interior point of `K` is the center of some closed ball still
contained in `interior K`. -/
private lemma exists_closed_ball_subset_interior {a : ℂ} (ha : a ∈ interior K) :
    ∃ r : ℝ, 0 < r ∧ Metric.closedBall a r ⊆ interior K := by
  -- Choose an open ball inside `interior K`, then shrink it so its closed ball still fits.
  rcases Metric.isOpen_iff.mp isOpen_interior a ha with ⟨R, hR, hRsub⟩
  refine ⟨R / 2, half_pos hR, ?_⟩
  exact (Metric.closedBall_subset_ball (half_lt_self hR)).trans hRsub

-- Proof sketch: decompose the oriented boundary into its finitely many closed piecewise
-- differentiable components, apply the holomorphic rectangle-integral theorem inside the compact
-- region bounded by them, and cancel the contributions of the auxiliary interior cuts.
/-- Theorem 5 (1): if `Γ` is the oriented boundary of a compact subset `K` of an open set `D` and
`f` is holomorphic on `D`, then the sum of the integrals of `f(z) dz` over the boundary components
of `Γ` is zero. -/
theorem orientedBoundary_sum_curveIntegral_eq_zero
    : ∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z = 0 := by
  -- Specialize the residue theorem to the empty singular set.
  have hboundary_disjoint :
      ∀ i, Disjoint (Set.range (Γ i).toPath) ((↑(∅ : Finset ℂ) : Set ℂ)) := by
    intro i
    simp
  have hres :
      ∀ z ∈ (∅ : Finset ℂ), IsolatedLocalResidueCircle K D (∅ : Finset ℂ) f z (0 : ℂ) := by
    intro z hz
    simp at hz
  have hzero :
      ∑ i, ∫ᶜ z in (Γ i).toPath, (f dz) z =
        (2 * Real.pi * Complex.I : ℂ) * Finset.sum (∅ : Finset ℂ) (fun _ ↦ (0 : ℂ)) := by
    exact orientedBoundary_sum_curveIntegral_eq_two_pi_I_mul_sum_residue
      (Γ := Γ) (f := f) (s := (∅ : Finset ℂ)) (residue := fun _ ↦ (0 : ℂ))
      hΓ hKD hD hboundary_disjoint (by simpa) hres
  simpa using hzero

omit hΓ hKD hD in
/-- Helper for Theorem 5: the positively oriented small circle centered at `a` evaluates the
Cauchy kernel integral to `2π i f(a)` once the closed disc lies in `D`. -/
private theorem small_circle_integral_div_sub_eq_two_pi_I_mul {a : ℂ} {r : ℝ}
    (hr : 0 < r) (hclosed : Metric.closedBall a r ⊆ D) :
    (∮ z in C(a, r), f z / (z - a)) = (2 * Real.pi * Complex.I : ℂ) * f a := by
  -- Restrict holomorphicity to the closed disc and invoke the circle Cauchy formula there.
  have hfd : DifferentiableOn ℂ f (Metric.closedBall a r) := hf.mono hclosed
  have ha_ball : a ∈ Metric.ball a r := by
    exact Metric.mem_ball_self hr
  simpa [smul_eq_mul, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
    hfd.circleIntegral_sub_inv_smul ha_ball

omit hΓ hKD hD hf in
/-- Helper for Theorem 5: the meromorphic kernel written as `((f / (· - a)) dz)` is exactly the
logarithmic form `f • indexForm a` used in the textbook statement. -/
private lemma kernelForm_eq_indexForm {a z : ℂ} :
    ((fun z ↦ f z / (z - a)) dz) z = f z • indexForm a z := by
  -- Expand both complex-linear forms once and rewrite division as multiplication by the inverse.
  ext
  simp [indexForm, div_eq_mul_inv]

-- Proof sketch: remove a small positively oriented circle around the interior point `a`, apply the
-- first part to `z ↦ f z / (z - a)` on the punctured compact region, then evaluate the circle term
-- by the Cauchy integral formula.
/-- Cartan section06 0014_Theorem_5: Theorem 5 (2): if `Γ` is the oriented boundary of a compact
subset `K` of an open set `D`,
`f` is holomorphic on `D`, and `a` lies in the interior of `K`, then the sum of the integrals of
`f(z) dz / (z - a)` over the boundary components of `Γ` is `2πif(a)`. -/
theorem orientedBoundary_sum_curveIntegral_div_sub_eq_two_pi_I_mul
    {a : ℂ} (ha : a ∈ interior K) :
    ∑ i, ∫ᶜ z in (Γ i).toPath, f z • indexForm a z =
      2 * Real.pi * Complex.I * f a := by
  classical
  -- Follow the source proof: excise a small disc around `a` that stays inside `interior K`.
  obtain ⟨r, hr, hclosedInterior⟩ := exists_closed_ball_subset_interior (K := K) ha
  have hclosedD : Metric.closedBall a r ⊆ D := by
    exact ((hclosedInterior.trans interior_subset).trans hKD)
  have hcircle :
      (∮ z in C(a, r), f z / (z - a)) = (2 * Real.pi * Complex.I : ℂ) * f a :=
    small_circle_integral_div_sub_eq_two_pi_I_mul (D := D) (f := f) hf hr hclosedD
  have hfpunct :
      DifferentiableOn ℂ f (D \ ((↑({a} : Finset ℂ) : Set ℂ))) := by
    -- Restrict the original holomorphicity to the punctured domain.
    exact hf.mono (by
      intro z hz
      exact hz.1)
  have hhol :
      DifferentiableOn ℂ (fun z ↦ f z / (z - a)) (D \ ((↑({a} : Finset ℂ) : Set ℂ))) := by
    -- On the punctured domain, the quotient has no pole because `z - a ≠ 0`.
    refine hfpunct.div (differentiableOn_id.sub (differentiableOn_const a)) ?_
    intro z hz
    exact sub_ne_zero.mpr (by
      intro hza
      have hzmem : z ∈ ((↑({a} : Finset ℂ) : Set ℂ)) := by
        simp [hza]
      exact hz.2 hzmem)
  have hboundary_disjoint :
      ∀ i, Disjoint (Set.range (Γ i).toPath) ((↑({a} : Finset ℂ) : Set ℂ)) := by
    intro i
    -- Every boundary component lies on `frontier K`, while `a` lies strictly inside `K`.
    refine Set.disjoint_left.2 ?_
    intro z hz hzsing
    change z ∈ ({a} : Finset ℂ) at hzsing
    rw [Finset.mem_singleton] at hzsing
    subst z
    have haFrontier : a ∈ frontier K := hΓ.range_toPath_subset_frontier i hz
    exact (Set.disjoint_left.1 disjoint_interior_frontier) ha haFrontier
  have hres :
      ∀ z ∈ ({a} : Finset ℂ),
        IsolatedLocalResidueCircle K D ({a} : Finset ℂ) (fun z ↦ f z / (z - a)) z (f a) := by
    intro z hz
    have hz' : z = a := by
      simpa using hz
    subst z
    -- Package the excision circle around `a` into the isolated-residue datum required by the
    -- frozen residue theorem.
    refine ⟨r, hr, hclosedInterior, hclosedD, ?_, ?_, hcircle⟩
    · -- No other singularity remains once the support is the singleton `{a}`.
      intro w hw hwne hwball
      have hw' : w = a := by
        simpa using hw
      exact hwne hw'
    · -- Restrict the punctured-domain holomorphicity to the punctured small ball around `a`.
      refine hhol.mono ?_
      intro w hw
      have hwnot : w ∉ ((↑({a} : Finset ℂ) : Set ℂ)) := by
        simpa using hw.2
      exact ⟨hclosedD (Metric.ball_subset_closedBall hw.1), hwnot⟩
  have hkernel :
      ∑ i, ∫ᶜ z in (Γ i).toPath, ((fun z ↦ f z / (z - a)) dz) z =
        (2 * Real.pi * Complex.I : ℂ) * Finset.sum ({a} : Finset ℂ) (fun _ ↦ f a) := by
    -- Apply the singleton residue theorem to the punctured kernel.
    exact orientedBoundary_sum_curveIntegral_eq_two_pi_I_mul_sum_residue
      (Γ := Γ) (f := fun z ↦ f z / (z - a)) ({a} : Finset ℂ) (fun _ ↦ f a)
      hΓ hKD hD hboundary_disjoint hhol hres
  have hkernel' := hkernel
  -- Rewrite the kernel form back to the textbook logarithmic form and collapse the singleton sum.
  simp_rw [kernelForm_eq_indexForm (f := f) (a := a)] at hkernel'
  simpa using hkernel'

end
