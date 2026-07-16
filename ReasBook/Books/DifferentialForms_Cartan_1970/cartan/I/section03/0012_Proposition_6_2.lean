import DifferentialForms_Cartan_1970.cartan.I.section03.«frozen_0008_Definition_I_3_extra_8»

-- Declarations for this item will be appended below by the statement pipeline.

namespace Complex

/-- Helper for Proposition 6.2: a logarithm branch is continuous at every point of its domain. -/
lemma IsLogBranchOn.continuousAt {f : ℂ → ℂ} {D : Set ℂ} (hf : IsLogBranchOn f D) {t : ℂ}
    (ht : t ∈ D) :
    ContinuousAt f t := by
  rcases hf with ⟨hDopen, _, hcont, _⟩
  -- Turn continuity on the open domain into ordinary continuity at `t`.
  exact hcont.continuousAt (hDopen.mem_nhds ht)

/-- Helper for Proposition 6.2: the identity `exp ∘ f = id` on the domain becomes a local
left-inverse relation near each point of the domain. -/
lemma IsLogBranchOn.eventuallyEq_exp_comp_id {f : ℂ → ℂ} {D : Set ℂ} (hf : IsLogBranchOn f D)
    {t : ℂ} (ht : t ∈ D) :
    ∀ᶠ z in nhds t, Complex.exp (f z) = z := by
  rcases hf with ⟨hDopen, _, _, hexp⟩
  -- Upgrade the pointwise identity on `D` to an eventual identity near `t`.
  simpa [Function.comp] using Set.EqOn.eventuallyEq_of_mem hexp (hDopen.mem_nhds ht)

-- Proof sketch: apply `HasDerivAt.of_local_left_inverse` to the local inverse relation
-- `Complex.exp ∘ f = id` near `t`, using the openness of `D`, continuity of the branch,
-- and `Complex.hasDerivAt_exp (f t)`.
/-- Proposition 6.2: every branch of the complex logarithm on a connected open set has
complex derivative `1 / t` at each point of its domain. -/
theorem IsLogBranchOn.hasDerivAt {f : ℂ → ℂ} {D : Set ℂ} (hf : IsLogBranchOn f D) {t : ℂ}
    (ht : t ∈ D) :
    HasDerivAt f (1 / t) t := by
  -- The branch is continuous at `t`, which is one hypothesis of the local inverse theorem.
  have hcont : ContinuousAt f t := hf.continuousAt ht
  -- The defining identity `exp (f z) = z` holds in a neighborhood of `t`.
  have hleft : ∀ᶠ z in nhds t, Complex.exp (f z) = z := hf.eventuallyEq_exp_comp_id ht
  -- Differentiate the local inverse relation `exp ∘ f = id` near `t`.
  have hderiv : HasDerivAt f (Complex.exp (f t))⁻¹ t :=
    (Complex.hasDerivAt_exp (f t)).of_local_left_inverse hcont
      (Complex.exp_ne_zero (f t)) hleft
  rcases hf with ⟨_, _, _, hexp⟩
  -- Rewrite the inverse derivative using the branch identity at the base point.
  have hexp_t : Complex.exp (f t) = t := by
    simpa [Function.comp] using hexp ht
  simpa [one_div, hexp_t] using hderiv

-- Proof sketch: take `HasDerivAt.deriv` of `IsLogBranchOn.hasDerivAt`.
/-- The derivative of a logarithm branch equals `1 / t` on its domain. -/
theorem IsLogBranchOn.deriv_eq {f : ℂ → ℂ} {D : Set ℂ} (hf : IsLogBranchOn f D) {t : ℂ}
    (ht : t ∈ D) :
    deriv f t = 1 / t := by
  -- Once the derivative exists with value `1 / t`, `deriv` returns that same value.
  simpa using (hf.hasDerivAt ht).deriv

end Complex
