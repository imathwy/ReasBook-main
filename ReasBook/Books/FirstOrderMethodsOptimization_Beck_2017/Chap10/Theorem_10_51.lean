import FirstOrderMethodsOptimization_Beck_2017.Chap10.Theorem_10_51_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]

/- Theorem 10.51 is `source-facing` in the Chapter 10 smoothing API. The repository already owns
the faithful reusable theorem under the canonical name
`moreau_envelope_real_is_smooth_approximation`; this numbered file reuses that owner directly
instead of restating an exact-interface duplicate. -/

/- Theorem 10.51: if a real-valued convex function `h` is globally `ℓ_h`-Lipschitz, then for
every `μ > 0` its real-valued Moreau envelope is a `1 / μ`-smooth approximation of `h` with
nonnegative parameters `(1, ℓ_h^2 / 2)`. -/
recall moreau_envelope_real_is_smooth_approximation

end
