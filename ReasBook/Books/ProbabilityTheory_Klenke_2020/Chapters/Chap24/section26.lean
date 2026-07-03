import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Definition_24_26 (from Items/Chap24) -/
open MeasureTheory
open scoped BigOperators

noncomputable section

namespace ProbabilityTheory

/- Layering for Definition 24.26:
- `dirichletDistribution` on `dirichletSimplex n` is the source-facing owner.
- `dirichletDensity` together with `dirichletSimplexVolume` gives the textbook simplex-density
  presentation.
- `dirichletNormalize` and `dirichletGammaProduct` form the normalized-Gamma bridge/view used by
  later chapter items. -/

/-- The simplex `Δ_n` underlying the Dirichlet law. This is the canonical mathlib simplex
`stdSimplex ℝ (Fin n)` under the chapter vocabulary. -/
abbrev dirichletSimplex (n : ℕ) : Type :=
  stdSimplex ℝ (Fin n)

/-- The standard simplex is measurable as a subset of `Fin n → ℝ`. -/
theorem measurableSet_dirichletSimplex (n : ℕ) : MeasurableSet (stdSimplex ℝ (Fin n)) :=
  (isClosed_stdSimplex ℝ (Fin n)).measurableSet

/-- The ambient Lebesgue measure on `Δ_n`, obtained by restricting `volume` to the simplex and
transporting it to the subtype. -/
noncomputable def dirichletSimplexVolume (n : ℕ) : Measure (dirichletSimplex n) :=
  Measure.comap ((↑) : dirichletSimplex n → Fin n → ℝ)
    (volume.restrict (stdSimplex ℝ (Fin n)))

/-- Evaluating the ambient simplex-volume measure amounts to evaluating restricted Lebesgue
measure on the image of the corresponding subtype set. -/
theorem dirichletSimplexVolume_apply {n : ℕ} (A : Set (dirichletSimplex n)) :
    dirichletSimplexVolume n A =
      volume.restrict (stdSimplex ℝ (Fin n)) (((↑) : dirichletSimplex n → Fin n → ℝ) '' A) := by
  simpa [dirichletSimplexVolume] using
    comap_subtype_coe_apply (measurableSet_dirichletSimplex n)
      (volume.restrict (stdSimplex ℝ (Fin n))) A

/-- The distinguished simplex vertex used when a normalization denominator vanishes. -/
def dirichletSimplexVertexFun (n : ℕ) (hn : 2 ≤ n) : Fin n → ℝ :=
  fun i ↦ if i = ⟨0, Nat.lt_of_lt_of_le (Nat.succ_pos 1) hn⟩ then 1 else 0

-- Proof sketch: exactly one coordinate of the distinguished vertex is `1` and all others are `0`,
-- so every coordinate is nonnegative and the total sum is `1`.
/-- The fallback vertex belongs to the simplex. -/
theorem dirichletSimplexVertexFun_property (n : ℕ) (hn : 2 ≤ n) :
    (∀ i, 0 ≤ dirichletSimplexVertexFun n hn i) ∧
      (∑ i, dirichletSimplexVertexFun n hn i = 1) := sorry

/-- A canonical simplex vertex, used as the zero-denominator branch of the normalization map. -/
def dirichletSimplexVertex (n : ℕ) (hn : 2 ≤ n) : dirichletSimplex n :=
  ⟨dirichletSimplexVertexFun n hn, dirichletSimplexVertexFun_property n hn⟩

/-- The positive-part sum used to normalize a vector into the simplex. -/
def dirichletPositivePartSum {n : ℕ} (x : Fin n → ℝ) : ℝ :=
  ∑ i, max (x i) 0

/-- Coordinatewise positive-part normalization of a vector in `ℝ^n`. -/
def dirichletNormalizedCoords {n : ℕ} (x : Fin n → ℝ) : Fin n → ℝ :=
  fun i ↦ max (x i) 0 / dirichletPositivePartSum x

-- Proof sketch: under a nonzero normalization denominator, each positive-part coordinate remains
-- nonnegative and the normalized coordinates sum to `1` by construction.
/-- Positive-part normalization lands in the simplex when the normalizing sum is nonzero. -/
theorem dirichletNormalizedCoords_property {n : ℕ} (x : Fin n → ℝ)
    (hs : dirichletPositivePartSum x ≠ 0) :
    (∀ i, 0 ≤ dirichletNormalizedCoords x i) ∧
      (∑ i, dirichletNormalizedCoords x i = 1) := sorry

/-- The normalization map from `ℝ^n` to the simplex `Δ_n`. -/
def dirichletNormalize (n : ℕ) (hn : 2 ≤ n) (x : Fin n → ℝ) : dirichletSimplex n :=
  if hs : dirichletPositivePartSum x = 0 then
    dirichletSimplexVertex n hn
  else
    ⟨dirichletNormalizedCoords x, dirichletNormalizedCoords_property x hs⟩

-- Proof sketch: measurability follows from the measurability of coordinatewise `max`, finite sums,
-- scalar division on the nonzero branch, and the piecewise definition at the zero branch.
/-- The normalization map to the simplex is measurable. -/
theorem measurable_dirichletNormalize (n : ℕ) (hn : 2 ≤ n) :
    Measurable (dirichletNormalize n hn) := sorry

/-- The Dirichlet density
`Γ(∑ᵢ θᵢ) / (∏ᵢ Γ(θᵢ)) * ∏ᵢ xᵢ^(θᵢ - 1)` on the simplex `Δ_n`. -/
noncomputable def dirichletDensity {n : ℕ} (θ : Fin n → ℝ) (x : dirichletSimplex n) : ℝ :=
  (Real.Gamma (∑ i, θ i) / ∏ i, Real.Gamma (θ i)) *
    ∏ i, ((x : Fin n → ℝ) i) ^ (θ i - 1)

/-- The Dirichlet distribution on `Δ_n`, presented in source-facing form by its simplex density. -/
noncomputable def dirichletDistribution {n : ℕ} (θ : Fin n → ℝ) (hθ : ∀ i, 0 < θ i) :
    ProbabilityMeasure (dirichletSimplex n) :=
  ⟨(dirichletSimplexVolume n).withDensity
      (fun x ↦ ENNReal.ofReal (dirichletDensity θ x)),
    by
      sorry⟩

/-- The Dirichlet law evaluates measurable simplex sets by integrating the textbook density over
the induced simplex volume. -/
theorem dirichletDistribution_apply {n : ℕ} (θ : Fin n → ℝ) (hθ : ∀ i, 0 < θ i)
    {A : Set (dirichletSimplex n)} (hA : MeasurableSet A) :
    (dirichletDistribution θ hθ : Measure (dirichletSimplex n)) A =
      ∫⁻ x in A, ENNReal.ofReal (dirichletDensity θ x) ∂dirichletSimplexVolume n := by
  change ((dirichletSimplexVolume n).withDensity
      fun x ↦ ENNReal.ofReal (dirichletDensity θ x)) A =
    ∫⁻ x in A, ENNReal.ofReal (dirichletDensity θ x) ∂dirichletSimplexVolume n
  simpa using withDensity_apply (fun x ↦ ENNReal.ofReal (dirichletDensity θ x)) hA

/-- The product law of independent gamma coordinates used to build the Dirichlet law. -/
noncomputable def dirichletGammaProduct {n : ℕ} (θ : Fin n → ℝ) (hθ : ∀ i, 0 < θ i) :
    ProbabilityMeasure (Fin n → ℝ) :=
  ProbabilityMeasure.pi fun i ↦
    ⟨gammaMeasure (θ i) 1, isProbabilityMeasure_gammaMeasure (hθ i) zero_lt_one⟩

/-- The normalized-Gamma construction recovers the source-facing Dirichlet law. This is a bridge
from the canonical owner to the later chapter realization. -/
theorem dirichletDistribution_eq_map_dirichletGammaProduct {n : ℕ} (hn : 2 ≤ n)
    (θ : Fin n → ℝ) (hθ : ∀ i, 0 < θ i) :
    dirichletDistribution θ hθ =
      ProbabilityMeasure.map (dirichletGammaProduct θ hθ)
        (measurable_dirichletNormalize n hn).aemeasurable := sorry

end ProbabilityTheory
