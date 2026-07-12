import ProbabilityTheory_Klenke_2020.Items.Chap13.Definition_13_3

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

/-- Corollary 13.7 (1): Lebesgue measure on `ℝ^d`, formalized as `volume` on
`EuclideanSpace ℝ (Fin d)`, is a regular measure in the sense of Definition 13.3. -/
theorem lebesgueMeasure_isRegular (d : ℕ) :
    IsRegularMeasure (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  IsRegularMeasure.of_owner volume

/-- Corollary 13.7 (2): Lebesgue measure on `ℝ^d`, formalized as `volume` on
`EuclideanSpace ℝ (Fin d)`, is a Radon measure in the sense of Definition 13.3. -/
theorem lebesgueMeasure_isRadon (d : ℕ) :
    IsRadonMeasure (volume : Measure (EuclideanSpace ℝ (Fin d))) :=
  IsRadonMeasure.of_owner volume

/-- Corollary 13.7 (3): in positive dimension, there exists a `σ`-finite measure on `ℝ^d`
that is not regular in the textbook sense, i.e. it does not satisfy `IsRegularMeasure`. -/
-- Proof sketch: place counting mass on a countable dense subset supported on one coordinate axis
-- of `ℝ^d`; this measure is `σ`-finite but fails outer regularity, so it cannot satisfy the
-- conjunction of inner regularity and outer regularity.
theorem exists_sigmaFinite_not_regular_measure_on_euclidean (d : ℕ) (hd : 0 < d) :
    ∃ μ : Measure (EuclideanSpace ℝ (Fin d)),
      SigmaFinite μ ∧ ¬ IsRegularMeasure μ := sorry
