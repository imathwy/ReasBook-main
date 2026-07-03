import DifferentialForms_Cartan_1970.I.section02.«0010_Proposition_5_1»

-- Declarations for this item will be appended below by the statement pipeline.

open PowerSeries
open scoped PowerSeries

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]

-- Semantic recall note: `lean_leansearch` is unavailable in this environment, so the API choice
-- was checked against the local `PowerSeries.radius`/`PowerSeries.sum` owner and section02
-- Proposition 5.1.

section

variable [CompleteSpace 𝕜]

/-- Remark I.2-extra-6 (1): if `T` has zero constant term and the scalar power series `S` and `T`
have nonzero radii of convergence, then on some sufficiently small closed disk the summed function
`z ↦ T(z)` takes values strictly inside the convergence disk of `S`. -/
theorem exists_small_radius_for_scalar_series_comp_defined
    (S T : 𝕜⟦X⟧) (hT0 : T.constantCoeff = 0)
    (hS : S.radius ≠ 0)
    (hT : T.radius ≠ 0) :
    ∃ r : NNReal, 0 < r ∧
      ∀ z : 𝕜, ‖z‖₊ ≤ r →
        ENNReal.ofNNReal ‖T.sum z‖₊ < S.radius := by
  rcases exists_radius_for_scalar_series_composition hT0 hS hT with ⟨r, hr0, hsum, hr⟩
  refine ⟨r, hr0, fun z hz ↦ ?_⟩
  simpa using norm_sum_right_lt_radius_left hsum hr hz

/-- Remark I.2-extra-6 (2): if `T` has zero constant term and the scalar power series `S` and `T`
have nonzero radii of convergence, then on some sufficiently small closed disk the equality of
formal compositions `U = S ∘ T` induces the functional equality `\tilde U = \tilde S ∘ \tilde T`. -/
theorem exists_small_radius_for_scalar_series_comp_sum
    (S T : 𝕜⟦X⟧) (hT0 : T.constantCoeff = 0)
    (hS : S.radius ≠ 0)
    (hT : T.radius ≠ 0) :
    ∃ r : NNReal, 0 < r ∧
      ∀ z : 𝕜, ‖z‖₊ ≤ r →
        S.sum (T.sum z) = sum (S.subst T) z := by
  rcases exists_radius_for_scalar_series_composition hT0 hS hT with ⟨r, hr0, hsum, hr⟩
  refine ⟨r, hr0, fun z hz ↦ ?_⟩
  simpa using sum_comp_eq_comp_sum hT0 hsum hr hz

end
