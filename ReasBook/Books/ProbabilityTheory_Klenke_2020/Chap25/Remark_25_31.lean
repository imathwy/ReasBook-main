import ProbabilityTheory_Klenke_2020.Chap25.Theorem_25_25
import ProbabilityTheory_Klenke_2020.Chap25.Theorem_25_30

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped BigOperators

variable {d : ℕ}

local notation "State" => EuclideanSpace ℝ (Fin d)

-- Proof sketch: expand both dyadic sums, evaluate the coordinate-path terms, and interchange the
-- two finite summations.
/-- Expanding the multidimensional dyadic Itô sum shows that it is the finite sum of the dyadic
coordinate integrals of `∂ₖ F (X_s)` against the coordinate paths `Xᵏ`. -/
theorem dyadicMultidimensionalItoApproximationUpTo_eq_sum_coordinateIntegrals
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal) (n : ℕ) :
    dyadicMultidimensionalItoApproximationUpTo F X T n =
      ∑ k : Fin d,
        partitionPathwiseItoApproximationUpTo
          (fun t ↦ (∂[k] F) (X t))
          (vectorPathComponent X k)
          dyadicPartitionSequence
          T
          n := by
  rw [dyadicMultidimensionalItoApproximationUpTo, Finset.sum_comm]
  simp [partitionPathwiseItoApproximationUpTo]

-- Proof sketch: the previous identity rewrites the multidimensional dyadic approximations as a
-- finite sum of the coordinate dyadic approximations. The coordinate convergence hypotheses then
-- give convergence of the whole finite sum, and `pathwiseMultidimensionalItoIntegral` is the
-- corresponding `limUnder`.
/-- If one chooses dyadic pathwise Itô realizations of the coordinate integrals
`∫₀ᵀ ∂ₖ F (Xₛ) dXₛᵏ`, then the multidimensional dyadic integral `∫₀ᵀ ∇F(Xₛ) dXₛ`
is the finite sum of those chosen realizations. -/
theorem pathwiseMultidimensionalItoIntegral_eq_sum_of_coordinateRealizations
    (F : State → ℝ) (X : VectorPathSpace d)
    (Ito : Fin d → NNReal → ℝ)
    (hIto :
      ∀ k : Fin d,
        HasPathwiseItoIntegralAlong
          (fun t ↦ (∂[k] F) (X t))
          (vectorPathComponent X k)
          dyadicPartitionSequence
          (Ito k))
    :
    pathwiseMultidimensionalItoIntegral F X = fun T ↦ ∑ k : Fin d, Ito k T := by
  ext T
  let H : Fin d → NNReal → ℝ := fun k t ↦ (∂[k] F) (X t)
  have hsum :
      Tendsto
        (fun n ↦
          ∑ k : Fin d,
            partitionPathwiseItoApproximationUpTo
              (H k)
              (vectorPathComponent X k)
              dyadicPartitionSequence
              T
              n)
        atTop
        (nhds (∑ k : Fin d, Ito k T)) := by
    refine tendsto_finset_sum Finset.univ fun k _ ↦ ?_
    simpa [H] using (hIto k).tendsto T
  have hEq :
      (fun n ↦ dyadicMultidimensionalItoApproximationUpTo F X T n) =
        fun n ↦
          ∑ k : Fin d,
            partitionPathwiseItoApproximationUpTo
              (H k)
              (vectorPathComponent X k)
              dyadicPartitionSequence
              T
              n := by
    funext n
    simpa [H] using dyadicMultidimensionalItoApproximationUpTo_eq_sum_coordinateIntegrals F X T n
  simpa [pathwiseMultidimensionalItoIntegral_def, hEq] using hsum.limUnder_eq

-- Proof sketch: choose a realization of each coordinate integral, apply the previous theorem,
-- and then rewrite each chosen realization to the canonical owner `pathwiseItoIntegralAlong`.
/-- Remark 25.31: if the coordinate dyadic pathwise Itô integrals
`∫₀ᵀ ∂ₖ F (Xₛ) dXₛᵏ` exist, then the multidimensional dyadic integral
`∫₀ᵀ ∇F(Xₛ) dXₛ` is the finite sum of the canonical coordinate integrals. -/
theorem pathwiseMultidimensionalItoIntegral_eq_sum_of_coordinateIntegrals
    (F : State → ℝ) (X : VectorPathSpace d)
    (hIto :
      ∀ k : Fin d,
        ∃ I : NNReal → ℝ,
          HasPathwiseItoIntegralAlong
            (fun t ↦ (∂[k] F) (X t))
            (vectorPathComponent X k)
            dyadicPartitionSequence
            I)
    :
    pathwiseMultidimensionalItoIntegral F X =
      fun T ↦
        ∑ k : Fin d,
          pathwiseItoIntegralAlong
            (fun t ↦ (∂[k] F) (X t))
            (vectorPathComponent X k)
            dyadicPartitionSequence
            T := by
  classical
  choose Ito hIto using hIto
  rw [pathwiseMultidimensionalItoIntegral_eq_sum_of_coordinateRealizations F X Ito hIto]
  funext T
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simpa using
    (congrArg (fun I : NNReal → ℝ ↦ I T) ((hIto k).eq_pathwiseItoIntegralAlong)).symm

/-- Remark 25.31 (converse failure): there are examples where the dyadic multidimensional
left-point sums for `∇F(X)` converge for every horizon, while at least one coordinate integrand
`∂ₖ F (X)` does not admit a dyadic pathwise Itô integral realization along the corresponding
coordinate path. Hence existence of the multidimensional integral does not imply existence of all
coordinate integrals. -/
theorem exists_pathwiseMultidimensionalItoIntegral_without_all_coordinateIntegrals :
    ∃ (d : ℕ) (F : EuclideanSpace ℝ (Fin d) → ℝ) (X : VectorPathSpace d),
      (∀ T : NNReal,
        Tendsto
          (fun n ↦ dyadicMultidimensionalItoApproximationUpTo F X T n)
          atTop
          (nhds (pathwiseMultidimensionalItoIntegral F X T))) ∧
        ¬ ∀ k : Fin d,
          ∃ I : NNReal → ℝ,
            HasPathwiseItoIntegralAlong
              (fun t ↦ (∂[k] F) (X t))
              (vectorPathComponent X k)
              dyadicPartitionSequence
              I := by
  sorry
