import ProbabilityTheory_Klenke_2020.Chap13.Definition_13_12
import ProbabilityTheory_Klenke_2020.Chap16.Theorem_16_14
import ProbabilityTheory_Klenke_2020.Chap16.Remark_16_18

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory MeasureTheory.ProbabilityMeasure
open scoped CompactlySupported ENNReal Topology

noncomputable section

/-- The Lévy density `x ↦ x⁻¹ e^{-θ x}` for the Gamma law, expressed on `[0, ∞)` in the owner
space `NNReal`. -/
def gammaLevyDensity (θ : ℝ) (x : NNReal) : ℝ :=
  Real.exp (-θ * (x : ℝ)) / (x : ℝ)

/-- The Gamma Lévy measure on `[0, ∞)`, expressed in the owner space `NNReal`. -/
def gammaLevyMeasure (θ : ℝ) : Measure NNReal :=
  (Measure.map Real.toNNReal ((volume : Measure ℝ).restrict (Set.Ici (0 : ℝ)))).withDensity
    (fun x ↦ ENNReal.ofReal (gammaLevyDensity θ x))

/-- The real-line view of `gammaLevyMeasure`, written with the usual density on `(0, ∞)` and zero
on `(-∞, 0]`. -/
def gammaLevyMeasureReal (θ : ℝ) : Measure ℝ :=
  volume.withDensity
    (fun x ↦ ENNReal.ofReal (if 0 < x then Real.exp (-θ * x) / x else 0))

/-- The `ℕ`-indexed version of the scaled positive-part Gamma convolution roots from Example
16.15, obtained by reindexing the textbook family `n Γ_{θ,1/n}|_(0,∞)` as
`(n + 1) Γ_{θ,1/(n + 1)}|_(0,∞)`. -/
def gammaRootRestrictedMeasure (θ : ℝ) (n : ℕ) : Measure ℝ :=
  (n + 1 : ℕ) • (gammaMeasure (1 / (n + 1 : ℝ)) θ).restrict (Set.Ioi 0)

-- Proof sketch: this is the canonical subordinator Lévy measure for the Gamma law `Γ_{θ,1}`,
-- obtained by identifying its log-Laplace transform with the Bernstein exponent
-- `t ↦ log (1 + t / θ)` and matching the integral kernel from Theorem 16.14.
/-- The Gamma law `Γ_{θ,1}`, viewed on `[0, ∞)`, has the canonical subordinator
Lévy--Khinchin representation with zero drift and Lévy measure `gammaLevyMeasure θ`. -/
theorem gammaMeasure_shapeOne_hasSubordinatorLevyKhinchinRepresentation
    (θ : ℝ) (hθ : 0 < θ) :
    HasSubordinatorLevyKhinchinRepresentation
      (ProbabilityMeasure.map
        (⟨gammaMeasure 1 θ, isProbabilityMeasure_gammaMeasure zero_lt_one hθ⟩ :
          ProbabilityMeasure ℝ)
        measurable_real_toNNReal.aemeasurable)
      0
      (gammaLevyMeasure θ) := sorry

-- Proof sketch: both measures encode the same positive-support Lévy density; one is written in
-- the owner space `NNReal`, the other in the ambient real line used by the chapter's vague-
-- convergence interface.
/-- The real-line view `gammaLevyMeasureReal θ` is exactly the image of the owner-space measure
`gammaLevyMeasure θ` under the inclusion `NNReal ↪ ℝ`. -/
theorem gammaLevyMeasureReal_eq_map_gammaLevyMeasure
    (θ : ℝ) :
    gammaLevyMeasureReal θ = Measure.map ((↑) : NNReal → ℝ) (gammaLevyMeasure θ) := sorry

-- Proof sketch: take the explicit convolution roots `Γ_{θ,1/n}` from Example 16.2, reindex them
-- as the `ℕ`-sequence `gammaRootRestrictedMeasure θ`, and apply the owner-level vague
-- convergence predicate `radonMeasureVaguelyConvergesTo` together with the Lévy-measure recovery
-- theorem from Remark 16.18. The limit measure is the real-line view of the canonical
-- subordinator Lévy measure from
-- `gammaMeasure_shapeOne_hasSubordinatorLevyKhinchinRepresentation`.
/-- Example 16.15: the reindexed scaled Gamma roots `gammaRootRestrictedMeasure θ n`, i.e.
`(n + 1) Γ_{θ,1/(n + 1)}|_(0,∞)`, converge vaguely in the chapter's canonical sense to the
real-line Gamma Lévy measure. Equivalently, the limit measure has density
`x ↦ x⁻¹ e^{-θ x}` on `(0, ∞)`. -/
theorem gammaRootMeasure_vaguelyConvergesTo_gammaLevyMeasureReal
    (θ : ℝ) (hθ : 0 < θ) :
    radonMeasureVaguelyConvergesTo (gammaRootRestrictedMeasure θ) (gammaLevyMeasureReal θ) :=
  sorry
