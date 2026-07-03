import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.


/-! ### Remark_21_7 (from Items/Chap21) -/
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [MetricSpace E]

/-- The closed cube `[-T, T]^d` in `ℝ^d`, viewed as a subset of `EuclideanSpace ℝ (Fin d)`. -/
def euclideanClosedCube (d : ℕ) (T : ℝ) : Set (EuclideanSpace ℝ (Fin d)) :=
  {x | ∀ i : Fin d, x i ∈ Set.Icc (-T) T}

-- Proof sketch: unfold `euclideanClosedCube`; membership is defined coordinatewise by the
-- condition that every component belongs to `[-T, T]`.
/-- Membership in `euclideanClosedCube d T` means that every coordinate lies in `[-T, T]`. -/
theorem mem_euclideanClosedCube_iff {d : ℕ} {T : ℝ} {x : EuclideanSpace ℝ (Fin d)} :
    x ∈ euclideanClosedCube d T ↔ ∀ i : Fin d, x i ∈ Set.Icc (-T) T :=
  Iff.rfl

/-- The source-facing multidimensional Kolmogorov condition on the cube `[-T, T]^d`: after
restricting the index space to the cube subtype, the process is a
`ProbabilityTheory.IsKolmogorovProcess` with exponent `d + β`. This is the thin bridge from the
textbook cube formulation to the canonical owner abstraction. -/
def IsKolmogorovProcessOnEuclideanClosedCube
    (μ : Measure Ω) {d : ℕ} (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    (T α β C : ℝ≥0) : Prop :=
  IsKolmogorovProcess (fun t : euclideanClosedCube d (T : ℝ) ↦ X t) μ (α : ℝ)
    (((d : ℝ≥0) + β : ℝ)) C

/-- A cube-restricted Kolmogorov process gives the stated increment estimate for points of
`[-T, T]^d`. -/
theorem IsKolmogorovProcessOnEuclideanClosedCube.increment_lintegral_le
    {μ : Measure Ω} {d : ℕ} {X : EuclideanSpace ℝ (Fin d) → Ω → E}
    {T α β C : ℝ≥0}
    (h : IsKolmogorovProcessOnEuclideanClosedCube μ X T α β C)
    {s t : EuclideanSpace ℝ (Fin d)}
    (hs : s ∈ euclideanClosedCube d (T : ℝ))
    (ht : t ∈ euclideanClosedCube d (T : ℝ)) :
    ∫⁻ ω, edist (X t ω) (X s ω) ^ (α : ℝ) ∂μ ≤
      (C : ℝ≥0∞) * edist t s ^ (((d : ℝ≥0) + β : ℝ)) := by
  simpa [edist_comm] using h.kolmogorovCondition ⟨s, hs⟩ ⟨t, ht⟩

variable [PolishSpace E]

/-- Remark 21.7, first clause: Theorem 21.6 remains valid for processes with values in an
arbitrary Polish space. -/
theorem exists_modification_with_locally_holder_paths_polishSpace
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : NNReal → Ω → E)
    (hbound :
      ∀ T : NNReal,
        ∃ α β C : ℝ≥0, IsKolmogorovProcessOnIcc μ X T α β C) :
    ∃ Xtilde : NNReal → Ω → E,
      AreModifications μ X Xtilde ∧
        (∀ γ : ℝ≥0, 0 < γ →
          (∀ T : NNReal,
            ∃ α β C : ℝ≥0, IsKolmogorovProcessOnIcc μ X T α β C ∧ (γ : ℝ) < β / α) →
              ∀ ω : Ω, LocallyHolderWith γ (fun t : NNReal ↦ Xtilde t ω)) ∧
        ∀ (T α β C γ : ℝ≥0),
          IsKolmogorovProcessOnIcc μ X T α β C →
          0 < γ →
          (γ : ℝ) < β / α →
            ∀ ε : ℝ, 0 < ε → ∃ K : ℝ≥0,
              ENNReal.ofReal (1 - ε) ≤
                μ {
                  ω | HolderOnWith K γ (fun t : NNReal ↦ Xtilde t ω) (Set.Icc (0 : NNReal) T)
                } := sorry

-- Proof sketch: translate the cube hypothesis to the Euclidean moment-bound theorem
-- `exists_locallyHolderWith_version_of_euclidean_moment_bound`, which already packages the
-- path-regularity conclusion via the owner predicate `HasLocallyHolderPaths`.
/-- Remark 21.7, second clause: for an `ℝ^d`-indexed process with values in a complete separable
metric space, if every cube restriction `[-T, T]^d` satisfies the multidimensional Kolmogorov
condition with exponents `α` and `d + β`, then for every Hölder exponent `γ < β / α` there exists
a version whose sample paths are locally Hölder-continuous of order `γ`. -/
theorem exists_locallyHolderContinuous_version_of_moment_bound_on_euclideanSpace
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {d : ℕ} {α β : ℝ≥0}
    (γ : Set.Ioc (0 : ℝ≥0) 1)
    (hγ : (γ : ℝ) < β / α)
    (X : EuclideanSpace ℝ (Fin d) → Ω → E)
    (hX : ∀ T : ℝ≥0, 0 < T → ∃ C : ℝ≥0, IsKolmogorovProcessOnEuclideanClosedCube μ X T α β C) :
    ∃ Y : EuclideanSpace ℝ (Fin d) → Ω → E,
      AreModifications μ X Y ∧
      HasLocallyHolderPaths (γ : ℝ≥0) Y := sorry

end ProbabilityTheory
