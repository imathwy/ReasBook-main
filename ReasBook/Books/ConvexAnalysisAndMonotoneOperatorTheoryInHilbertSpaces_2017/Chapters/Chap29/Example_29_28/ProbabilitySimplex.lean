import BauschkeLean.Chap07.Exercise_7_9
import BauschkeLean.Chap29.Proposition_29_2

open scoped BigOperators

noncomputable section

section

variable {N : ℕ}

local notation "C" => Set.lpClosedUnitBall N 1
local notation "Δ" => stdSimplex ℝ (Fin N)

/-- The source probability simplex viewed inside `EuclideanSpace ℝ (Fin N)`, exposed as a thin
bridge to the canonical owner `stdSimplex ℝ (Fin N)` through `EuclideanSpace.equiv`. -/
abbrev probabilitySimplex : Set (EuclideanSpace ℝ (Fin N)) :=
  (EuclideanSpace.equiv (Fin N) ℝ) ⁻¹' stdSimplex ℝ (Fin N)

local notation "Δₚ" => (probabilitySimplex : Set (EuclideanSpace ℝ (Fin N)))

/-- Membership in `probabilitySimplex` is exactly coordinatewise nonnegativity together with unit
mass. -/
@[simp] theorem mem_probabilitySimplex {ξ : EuclideanSpace ℝ (Fin N)} :
    ξ ∈ Δₚ ↔ (∀ i, 0 ≤ ξ i) ∧ ∑ i, ξ i = 1 :=
  by
  simp [probabilitySimplex, stdSimplex]

/-- The `ℓ¹` closed unit ball in `EuclideanSpace ℝ (Fin N)` is Chebyshev. -/
theorem isChebyshev_lpClosedUnitBall_one (N : ℕ) :
    IsChebyshev (Set.lpClosedUnitBall N 1) := by
  refine isChebyshev_of_nonempty_isClosed_convex ?_ ?_ ?_
  · refine ⟨0, ?_⟩
    simp [Set.mem_lpClosedUnitBall_iff, EuclideanSpace.lpNorm]
  · let L :=
      ((PiLp.continuousLinearEquiv 1 ℝ (fun _ : Fin N ↦ ℝ)).symm.toContinuousLinearMap).comp
        (EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap
    have hcont :
        Continuous (fun u : EuclideanSpace ℝ (Fin N) ↦ ‖u‖_[1]) := by
      simpa [EuclideanSpace.lpNorm, L] using
        (continuous_norm.comp L.continuous :
          Continuous (fun u : EuclideanSpace ℝ (Fin N) ↦ ‖L u‖))
    simpa [Set.lpClosedUnitBall, Set.preimage, Set.setOf_mem_eq] using
      isClosed_Iic.preimage hcont
  · let L :=
      ((PiLp.continuousLinearEquiv 1 ℝ (fun _ : Fin N ↦ ℝ)).symm.toContinuousLinearMap).comp
        (EuclideanSpace.equiv (Fin N) ℝ).toContinuousLinearMap
    have hnorm_conv :
        ConvexOn ℝ Set.univ (fun u : EuclideanSpace ℝ (Fin N) ↦ ‖u‖_[1]) := by
      simpa [EuclideanSpace.lpNorm, L] using
        (convexOn_univ_norm :
          ConvexOn ℝ Set.univ (fun z : PiLp 1 (fun _ : Fin N ↦ ℝ) ↦ ‖z‖)).comp_linearMap
          L.toLinearMap
    simpa [Set.lpClosedUnitBall, Set.setOf_mem_eq] using hnorm_conv.convex_le (1 : ℝ)

/-- The canonical coefficient simplex `stdSimplex ℝ (Fin N)`, viewed in
`EuclideanSpace ℝ (Fin N)` through `EuclideanSpace.equiv`, is Chebyshev whenever `Fin N` is
nonempty. -/
theorem isChebyshev_stdSimplex_fin (N : ℕ) (hN : 0 < N) :
    IsChebyshev (probabilitySimplex (N := N)) := by
  refine isChebyshev_of_nonempty_isClosed_convex ?_ ?_ ?_
  · let i : Fin N := ⟨0, hN⟩
    refine ⟨(EuclideanSpace.equiv (Fin N) ℝ).symm (Pi.single i 1), ?_⟩
    simpa [probabilitySimplex] using single_mem_stdSimplex ℝ i
  · simpa [probabilitySimplex] using
      (isClosed_stdSimplex ℝ (Fin N)).preimage (EuclideanSpace.equiv (Fin N) ℝ).continuous
  · simpa [probabilitySimplex] using
      (convex_stdSimplex ℝ (Fin N)).linear_preimage
        (EuclideanSpace.equiv (Fin N) ℝ).toLinearMap

/-- The source probability simplex in `EuclideanSpace ℝ (Fin N)` is Chebyshev whenever `Fin N` is
nonempty. -/
theorem isChebyshev_probabilitySimplex_fin (N : ℕ) (hN : 0 < N) :
    IsChebyshev (probabilitySimplex (N := N)) := by
  simpa using isChebyshev_stdSimplex_fin N hN

end
