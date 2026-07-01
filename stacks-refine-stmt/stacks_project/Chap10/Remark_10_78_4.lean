import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold ContDiff

local notation "SmoothRealFunctionRing" => C^∞⟮𝓘(ℝ), ℝ; ℝ⟯

/-- The ideal of smooth real-valued functions vanishing at the origin. -/
def smoothRealFunctionsVanishingAtZeroIdeal : Ideal SmoothRealFunctionRing :=
  RingHom.ker (ContMDiffMap.evalRingHom (0 : ℝ))

/-- The ideal of smooth real-valued functions that vanish on a neighborhood of the origin. -/
def smoothRealFunctionsVanishingNearZeroIdeal : Ideal SmoothRealFunctionRing where
  carrier := { f | ∃ ε : ℝ, 0 < ε ∧ ∀ x : ℝ, |x| < ε → f x = 0 }
  zero_mem' := by
    refine ⟨1, zero_lt_one, ?_⟩
    intro x hx
    rfl
  add_mem' := by
    rintro f g ⟨εf, hεf, hf⟩ ⟨εg, hεg, hg⟩
    refine ⟨min εf εg, lt_min hεf hεg, ?_⟩
    intro x hx
    have hxf : |x| < εf := lt_of_lt_of_le hx (min_le_left _ _)
    have hxg : |x| < εg := lt_of_lt_of_le hx (min_le_right _ _)
    simp [hf x hxf, hg x hxg]
  smul_mem' := by
    rintro f g ⟨ε, hε, hg⟩
    refine ⟨ε, hε, ?_⟩
    intro x hx
    simp [hg x hx]

-- Proof sketch: a smooth function that vanishes on some neighborhood of `0` in particular vanishes
-- at `0`, so it lies in the kernel of evaluation at the origin.
/-- Any smooth function vanishing near the origin also vanishes at the origin. -/
theorem smoothRealFunctionsVanishingNearZeroIdeal_le_vanishingAtZeroIdeal :
    smoothRealFunctionsVanishingNearZeroIdeal ≤ smoothRealFunctionsVanishingAtZeroIdeal := sorry

/-- The ideal of functions vanishing at the origin is maximal. -/
theorem smoothRealFunctionsVanishingAtZeroIdeal_isMaximal :
    smoothRealFunctionsVanishingAtZeroIdeal.IsMaximal := sorry

attribute [instance] smoothRealFunctionsVanishingAtZeroIdeal_isMaximal

instance smoothRealFunctionsVanishingAtZeroIdeal_isPrime :
    smoothRealFunctionsVanishingAtZeroIdeal.IsPrime :=
  smoothRealFunctionsVanishingAtZeroIdeal_isMaximal.isPrime

/-- The source-facing module `M = R_𝔪` from Remark 10.78.4, where `𝔪` is the maximal ideal of
smooth functions vanishing at the origin. -/
abbrev smoothRealFunctionLocalizationAtZero :=
  Localization.AtPrime smoothRealFunctionsVanishingAtZeroIdeal

/-- The quotient model `R / I` from Remark 10.78.4, where `I` consists of smooth functions
vanishing on a neighborhood of the origin. -/
abbrev smoothRealFunctionQuotientAtZero :=
  SmoothRealFunctionRing ⧸ smoothRealFunctionsVanishingNearZeroIdeal

/-- The quotient model `R / I` is a localization of `R` at the maximal ideal of functions
vanishing at `0`. -/
instance smoothRealFunctionQuotientAtZero_isLocalizationAtVanishingAtZeroIdeal :
    IsLocalization smoothRealFunctionsVanishingAtZeroIdeal.primeCompl
      smoothRealFunctionQuotientAtZero := sorry

/-- The source-facing localization `R_𝔪` and the quotient model `R / I` are canonically
equivalent. -/
noncomputable abbrev smoothRealFunctionLocalizationAtZeroEquivQuotient :
    smoothRealFunctionLocalizationAtZero ≃ₐ[SmoothRealFunctionRing]
      smoothRealFunctionQuotientAtZero :=
  IsLocalization.algEquiv smoothRealFunctionsVanishingAtZeroIdeal.primeCompl _ _

/-- The module `M = R_𝔪` is finite over `R`. -/
instance smoothRealFunctionLocalizationAtZero_finite :
    Module.Finite SmoothRealFunctionRing smoothRealFunctionLocalizationAtZero :=
  Module.Finite.equiv smoothRealFunctionLocalizationAtZeroEquivQuotient.symm.toLinearEquiv

/-- The source-facing localization `M = R_𝔪` is flat over `R = C^\infty(\mathbf R, \mathbf R)`. -/
instance smoothRealFunctionLocalizationAtZero_flat :
    Module.Flat SmoothRealFunctionRing smoothRealFunctionLocalizationAtZero :=
  inferInstance

-- Proof sketch: use the standard smooth-function counterexample: the localization `R_𝔪`,
-- equivalently the quotient `R / I`, is finite and flat but not projective.
/-- Remark 10.78.4: for `R = C^\infty(\mathbf R, \mathbf R)` and
`M = R_𝔪 = R / I`, where `𝔪` is the maximal ideal of functions vanishing at `0` and `I` consists
of smooth functions vanishing on a neighborhood of `0`, the module `M` is not projective.
Together with the companion instances asserting that `M` is finite and flat, this gives the stated
counterexample to the implication "finite flat implies projective". -/
theorem smoothRealFunctionLocalizationAtZero_not_projective :
    ¬ Module.Projective SmoothRealFunctionRing smoothRealFunctionLocalizationAtZero := sorry
