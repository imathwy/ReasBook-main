import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

/- Exercise 15.4.2 is `source-facing`: the textbook content is the joint law of the splitting
transform `(B, Z) ↦ (B * Z, (1 - B) * Z)`.
The owner abstraction is therefore the joint `HasLaw` statement for that transformed pair; the
independence and one-coordinate laws below are derived API from this owner theorem. -/
section

variable (P : Measure Ω) {B Z : Ω → ℝ} {r s : ℝ}
variable (hr : 0 < r) (hs : 0 < s)
variable (hB : HasLaw B (betaMeasure r s) P)
variable (hZ : HasLaw Z (gammaMeasure (r + s) 1) P)
variable (hBZ : IndepFun B Z P)

-- The textbook notation `I_{1, a}` is interpreted as the Gamma law with shape `a` and unit rate,
-- namely `gammaMeasure a 1`. The source's `T_{1, r}` is treated as the same OCR-corrupted
-- notation.
-- Proof sketch: apply Exercise 15.4.1 to the change of variables `(b, z) ↦ (bz, (1 - b)z)` on
-- `(0,1) × (0,∞)`, identify the transported joint density with the product of the Gamma densities
-- of shapes `r` and `s`, and then use independence of `B` and `Z` to pass from the product law of
-- `(B, Z)` to the law of the transformed pair.
/-- Exercise 15.4.2: if `B` has Beta law `betaMeasure r s` and `Z` has Gamma law
`gammaMeasure (r + s) 1`, independently, then the pair `(B * Z, (1 - B) * Z)` has the product
Gamma law with shapes `r` and `s` and unit rate. -/
theorem beta_gamma_unit_rate_split_hasLaw_prod
    :
    HasLaw
      (fun ω ↦ (B ω * Z ω, (1 - B ω) * Z ω))
      ((gammaMeasure r 1).prod (gammaMeasure s 1)) P := sorry

-- Proof sketch: combine the main joint-law statement with
-- `indepFun_iff_map_prod_eq_prod_map_map`; the product target measure is exactly the criterion for
-- independence of the two coordinates.
/-- The Beta-Gamma splitting transform sends an independent Beta/Gamma pair to two independent
unit-rate Gamma random variables. -/
theorem beta_gamma_unit_rate_split_indepFun
    :
    IndepFun (fun ω ↦ B ω * Z ω) (fun ω ↦ (1 - B ω) * Z ω) P := sorry

-- Proof sketch: compose the joint-law statement with the first-coordinate projection and use that
-- the first marginal of a product measure is the first factor.
/-- The first coordinate in the Beta-Gamma splitting transform has Gamma law with shape `r` and
unit rate. -/
theorem beta_gamma_unit_rate_split_fst_hasLaw
    :
    HasLaw (fun ω ↦ B ω * Z ω) (gammaMeasure r 1) P := sorry

-- Proof sketch: compose the joint-law statement with the second-coordinate projection and use
-- that the second marginal of a product measure is the second factor.
/-- The second coordinate in the Beta-Gamma splitting transform has Gamma law with shape `s` and
unit rate. -/
theorem beta_gamma_unit_rate_split_snd_hasLaw
    :
    HasLaw (fun ω ↦ (1 - B ω) * Z ω) (gammaMeasure s 1) P := sorry

end
