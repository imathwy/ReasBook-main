import BauschkeLean.Chap23.ResolventRealizer
import BauschkeLean.Chap23.Proposition_23_38
import BauschkeLean.Chap23.Proposition_23_39
import BauschkeLean.Chap30.Corollary_30_10
import BauschkeLean.Chap30.UnitIndexing

-- Semantic recall: this corollary is the single-operator specialization of the Chapter 30
-- Haugazeau owner `haugazeauIteration`, with the Chapter 23 resolvent realizer
-- `resolventMap A hA 1`, the fixed-point/zero-set bridge for the resolvent, and the canonical
-- zero-set surface `A.zeros`.

open Filter Function
open scoped InnerProductSpace Pointwise SetValuedOperator Topology
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable section

/-- The fixed-point set of the resolvent map `J_A` is exactly the zero set `A.zeros`. -/
@[simp] theorem resolventMap_fixedPoints_eq_zeros
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    fixedPoints (resolventMap A hA (1 : PosReal)) = A.zeros := by
  ext x
  rw [← fixedPointSet_resolvent_smul_eq_zeros (1 : PosReal)]
  rw [Set.mem_setOf_eq, mem_fixedPoints_iff,
    resolvent_smul_eq_singleton_resolventMap_of_maximal A hA (1 : PosReal) x]
  simp [eq_comm]

/-- The Chapter 30 common fixed-point set of the constant resolvent family `J_A` is exactly the
zero set `A.zeros`. -/
@[simp] theorem commonFixedPointSet_resolventMap_eq_zeros
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) :
    commonFixedPointSet (fun _ : Unit ↦ resolventMap A hA (1 : PosReal)) = A.zeros := by
  rw [commonFixedPointSet_unit_eq_fixedPoints, resolventMap_fixedPoints_eq_zeros A hA]

/-- The Haugazeau orbit from Corollary 30.11, realized as the single-resolvent specialization of
`haugazeauIteration`. -/
abbrev haugazeauResolventOrbit
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x0 : H) : ℕ → H :=
  haugazeauIteration
    (fun _ : Unit ↦ resolventMap A hA (1 : PosReal))
    (fun _ : ℕ ↦ ()) x0

/-- The Haugazeau resolvent orbit starts at the prescribed initial point. -/
@[simp] theorem haugazeauResolventOrbit_zero
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x0 : H) :
    haugazeauResolventOrbit A hA x0 0 = x0 := by
  simp [haugazeauResolventOrbit]

/-- The Haugazeau resolvent orbit satisfies the source recursion
`xₙ₊₁ = Q(x₀, xₙ, J_A xₙ)`. -/
@[simp] theorem haugazeauResolventOrbit_succ
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A) (x0 : H) (n : ℕ) :
    haugazeauResolventOrbit A hA x0 (n + 1) =
      specialPolyhedronQ x0
        (haugazeauResolventOrbit A hA x0 n)
        (resolventMap A hA (1 : PosReal) (haugazeauResolventOrbit A hA x0 n)) := by
  simp [haugazeauResolventOrbit]

/-- If `A.zeros` is nonempty, the Haugazeau resolvent orbit converges strongly to the metric
projection of `x₀` onto `A.zeros`. -/
theorem haugazeauResolventOrbit_tendsto_projection_zeros_of_zeros_nonempty
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (hzeros : A.zeros.Nonempty) (x0 : H) :
    Tendsto (haugazeauResolventOrbit A hA x0) atTop
      (𝓝 (P[A.zeros, Maximal.zeros_isChebyshev hA hzeros] x0)) := by
  let T : Unit → H → H := fun _ ↦ resolventMap A hA (1 : PosReal)
  have hT : ∀ i : Unit, FirmlyNonexpansiveOn (Set.univ : Set H) (T i) := by
    intro i
    cases i
    simpa [T] using resolventMap_firmlyNonexpansiveOn_univ A hA (1 : PosReal)
  have hC_nonempty : (commonFixedPointSet T).Nonempty := by
    rw [commonFixedPointSet_resolventMap_eq_zeros A hA]
    exact hzeros
  let hCommonCheb :=
    iInter_fixedPoints_isChebyshev_of_firmlyQuasinonexpansive T
      (fun i ↦ firmlyQuasinonexpansive_of_firmlyNonexpansive (hT i)) hC_nonempty
  let hZeroCheb := Maximal.zeros_isChebyshev hA hzeros
  have hbest :
      IsBestApproximation x0 A.zeros (P[commonFixedPointSet T, hCommonCheb] x0) := by
    rw [← commonFixedPointSet_resolventMap_eq_zeros A hA]
    exact projectionPoint_isBestApproximation (commonFixedPointSet T) hCommonCheb x0
  have hproj_eq :
      P[commonFixedPointSet T, hCommonCheb] x0 = P[A.zeros, hZeroCheb] x0 := by
    apply eq_projectionPoint_of_isBestApproximation A.zeros hZeroCheb
    exact hbest
  have hlimit :
      Tendsto (haugazeauIteration T (fun _ : ℕ ↦ ()) x0) atTop
        (𝓝 (P[commonFixedPointSet T, hCommonCheb] x0)) := by
    simpa [hCommonCheb] using
      haugazeau_iteration_tendsto_projection_iInter_fixedPoints_of_firmlyNonexpansive
        T hT hC_nonempty
        (fun _ : ℕ ↦ ()) visitsEveryIndexInEachBlock_unit x0
  rw [hproj_eq] at hlimit
  simpa [T, haugazeauResolventOrbit, hZeroCheb] using hlimit

/-- Corollary 30.11: let `A : H → 2^H` be maximally monotone with `0 ∈ ran A`,
let `x₀ : H`, and set `xₙ₊₁ = Q(x₀, xₙ, J_A xₙ)`, realized here by the canonical
Chapter 30 orbit `haugazeauResolventOrbit A hA x₀`. Then
`xₙ → P_(zer A) x₀`, written on the project API as convergence to the metric
projection of `x₀` onto `A.zeros`. -/
theorem haugazeauResolventOrbit_tendsto_projection_zeros
    (A : SetValuedOperator H H) (hA : Maximal IsMonotone A)
    (hzero_range : (0 : H) ∈ A.range) (x0 : H) :
    Tendsto (haugazeauResolventOrbit A hA x0) atTop
      (𝓝 (P[A.zeros,
        Maximal.zeros_isChebyshev hA
          (by
            rcases (SetValuedOperator.mem_range_iff A (0 : H)).1 hzero_range with ⟨x, hx⟩
            exact ⟨x, hx⟩)] x0)) := by
  have hzeros : A.zeros.Nonempty := by
    rcases (SetValuedOperator.mem_range_iff A (0 : H)).1 hzero_range with ⟨x, hx⟩
    exact ⟨x, hx⟩
  have hproj_eq :
      P[A.zeros, Maximal.zeros_isChebyshev hA hzeros] x0 =
        P[A.zeros,
          Maximal.zeros_isChebyshev hA
            (by
              rcases (SetValuedOperator.mem_range_iff A (0 : H)).1 hzero_range with ⟨x, hx⟩
              exact ⟨x, hx⟩)] x0 := by
    apply eq_projectionPoint_of_isBestApproximation A.zeros
      (Maximal.zeros_isChebyshev hA
        (by
          rcases (SetValuedOperator.mem_range_iff A (0 : H)).1 hzero_range with ⟨x, hx⟩
          exact ⟨x, hx⟩))
    exact projectionPoint_isBestApproximation A.zeros
      (Maximal.zeros_isChebyshev hA hzeros) x0
  have hlimit :=
    haugazeauResolventOrbit_tendsto_projection_zeros_of_zeros_nonempty A hA hzeros x0
  rw [hproj_eq] at hlimit
  exact hlimit

end

end SetValuedOperator
