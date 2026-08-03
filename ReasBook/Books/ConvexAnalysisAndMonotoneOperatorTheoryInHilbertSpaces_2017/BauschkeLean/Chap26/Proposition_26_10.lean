import BauschkeLean.Chap23.Proposition_23_2
import BauschkeLean.Chap26.Proposition_26_4
import BauschkeLean.Chap26.Theorem_26_9

open ERealFunction
open Filter
open scoped BigOperators InnerProductSpace Pointwise SetValuedOperator Topology

universe u

noncomputable section

namespace SetValuedOperator

-- Source/core/bridge triage:
-- - `source-facing`: `IsFiniteFamilySpingarnOrbit` and Proposition 26.10 itself.
-- - `core/canonical`: `IsSpingarnPartialInverseOrbit` from Theorem 26.9, specialized to the
--   product-space operator `familyOperator A` and the diagonal submodule `diagonalSubmodule`.
-- - `bridge/view`: `IsFiniteFamilySpingarnOrbit.toPartialInverseOrbit`.

variable {m : ℕ}
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

local notation "ProductSpace" => lp (fun _ : Fin m ↦ H) 2

/-- The finite-family Spingarn recursion `(26.24)` from Proposition 26.10, started at `x0` and
`u0` with `∑ i, u0 i = 0`. -/
structure IsFiniteFamilySpingarnOrbit
    (A : Fin m → SetValuedOperator H H) (x0 : H) (u0 : ProductSpace)
    (x : ℕ → H) (u y v : ℕ → ProductSpace) : Prop where
  /-- The primal sequence starts at `x0`. -/
  x_zero : x 0 = x0
  /-- The dual family starts at `u0`. -/
  u_zero : u 0 = u0
  /-- The initial dual family belongs to the diagonal orthogonal complement, expressed as
  `∑ i, u0 i = 0`. -/
  u_zero_sum : ∑ i, u0 i = (0 : H)
  /-- Each coordinate resolvent step is the singleton value `{yₙᵢ}`. -/
  resolvent_eq :
    ∀ n : ℕ, ∀ i : Fin m, J[(A i)] (x n + u n i) = ({y n i} : Set H)
  /-- Each residual coordinate is `xₙ + uₙᵢ - yₙᵢ`. -/
  residual_eq :
    ∀ n : ℕ, ∀ i : Fin m, v n i = x n + u n i - y n i
  /-- The next primal iterate is the diagonal average of `y n`. -/
  x_succ_eq :
    ∀ n : ℕ, x (n + 1) = (m : ℝ)⁻¹ • ∑ i, y n i
  /-- The next dual family subtracts the diagonal average of `v n`. -/
  u_succ_eq :
    ∀ n : ℕ, ∀ i : Fin m, u (n + 1) i = v n i - (m : ℝ)⁻¹ • ∑ j, v n j

namespace IsFiniteFamilySpingarnOrbit

/-- The finite-family recursion is exactly the product-space Spingarn orbit from Theorem 26.9 for
the family operator `familyOperator A` and the diagonal submodule. -/
theorem toPartialInverseOrbit
    {A : Fin m → SetValuedOperator H H} {x0 : H} {u0 : ProductSpace}
    {x : ℕ → H} {u y v : ℕ → ProductSpace}
    (hOrbit : IsFiniteFamilySpingarnOrbit A x0 u0 x u y v) :
    IsSpingarnPartialInverseOrbit (familyOperator A) diagonalSubmodule
      (diagonalPoint x0) u0 (fun n ↦ diagonalPoint (x n)) u y v := by
  refine
    { x0_mem := ?_
      u0_mem := ?_
      x_zero := ?_
      u_zero := hOrbit.u_zero
      v_eq := ?_
      v_mem := ?_
      x_succ_eq := ?_
      u_succ_eq := ?_ }
  · rw [mem_diagonalSubmodule_iff]
    intro i j
    simp [diagonalPoint_apply]
  · have hu0_sum : u0 ∈ (sumZeroSubmodule : Submodule ℝ ProductSpace) := by
      simpa [sumZeroSubmodule] using hOrbit.u_zero_sum
    simpa [diagonalSubmodule_orthogonal_eq_sumZeroSubmodule] using hu0_sum
  · simp [hOrbit.x_zero]
  · intro n
    ext i
    simpa [Pi.add_apply, Pi.sub_apply, diagonalPoint_apply] using hOrbit.residual_eq n i
  · intro n
    rw [mem_familyOperator_iff]
    intro i
    have hy_mem : y n i ∈ J[(A i)] (x n + u n i) := by
      rw [hOrbit.resolvent_eq n i]
      simp
    have hy_mem_one : y n i ∈ J[((1 : ℝ) • A i)] (x n + u n i) := by
      simpa using hy_mem
    have hv_mem :
        x n + u n i - y n i ∈ ((1 : ℝ) • A i (y n i)) :=
      (mem_resolvent_smul_iff_sub_mem_smul
        (A i) (1 : ERealFunction.PosReal) (x n + u n i) (y n i)).1 hy_mem_one
    simpa [hOrbit.residual_eq n i] using hv_mem
  · intro n
    simpa [hOrbit.x_succ_eq n] using
      (starProjection_diagonalSubmodule_eq_diagonalPoint_average (y n)).symm
  · intro n
    ext i
    rw [hOrbit.u_succ_eq n i]
    symm
    simpa [diagonalPoint_apply] using
      congrArg (fun z : ProductSpace ↦ z i)
        (starProjection_orthogonal_diagonalSubmodule_eq_sub_diagonalPoint_average (v n))

end IsFiniteFamilySpingarnOrbit

omit [CompleteSpace H] in
private theorem exists_partialInverseSolution_familyOperator_diagonalSubmodule
    (A : Fin m → SetValuedOperator H H) (hzero : ((∑ i, A i).zeros).Nonempty) :
    ∃ x u, IsSpingarnPartialInverseSolution (familyOperator A) diagonalSubmodule x u := by
  rcases hzero with ⟨x, hx⟩
  rcases (mem_zeros_sum_iff_exists_mem_familyOperator_diagonalPoint A x).1 hx with
    ⟨u, hu_orth, hu_mem⟩
  refine ⟨diagonalPoint x, u, ?_⟩
  refine ⟨?_, hu_orth, hu_mem⟩
  rw [mem_diagonalSubmodule_iff]
  intro i j
  simp [diagonalPoint_apply]

/-- Proposition 26.10: let `m ≥ 2`, let `A : Fin m → SetValuedOperator H H` be maximally
monotone with `zer (∑ i, A i) ≠ ∅`, formalized as `((∑ i, A i).zeros).Nonempty`, and let
`x`, `u`, `y`, and `v` satisfy the finite-family Spingarn recursion `(26.24)` from initial
data `x0` and `u0` with `∑ i, u0 i = 0`, formalized by
`IsFiniteFamilySpingarnOrbit A x0 u0 x u y v`. Then `(x n)` converges weakly to a point of
`zer (∑ i, A i)`, formalized as `(∑ i, A i).zeros`. -/
theorem exists_weakLimit_mem_zeros_sum_of_spingarn_recursion
    (A : Fin m → SetValuedOperator H H) (hm : 2 ≤ m)
    (hA : ∀ i, Maximal IsMonotone (A i))
    (hzero : ((∑ i, A i).zeros).Nonempty)
    (x0 : H) (u0 : ProductSpace)
    (x : ℕ → H) (u y v : ℕ → ProductSpace)
    (hOrbit : IsFiniteFamilySpingarnOrbit A x0 u0 x u y v) :
    ∃ xLim ∈ (∑ i, A i).zeros,
      Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H xLim)) := by
  have hfamilyA : Maximal IsMonotone (familyOperator A) :=
    familyOperator_maximal_of_maximal A hA
  have hsol :
      ∃ xProd uProd,
        IsSpingarnPartialInverseSolution (familyOperator A) diagonalSubmodule xProd uProd :=
    exists_partialInverseSolution_familyOperator_diagonalSubmodule A hzero
  obtain ⟨xProdLim, uLim, hLimSol, hweakProd, _⟩ :=
    exists_weakLimit_isSpingarnPartialInverseSolution_of_isSpingarnPartialInverseOrbit
      hfamilyA diagonalSubmodule hsol hOrbit.toPartialInverseOrbit
  have hxProd_mem : xProdLim ∈ (diagonalSubmodule : Submodule ℝ ProductSpace) := hLimSol.1
  have huLim_orth :
      uLim ∈ (((diagonalSubmodule : Submodule ℝ ProductSpace)ᗮ : Submodule ℝ ProductSpace)) :=
    hLimSol.2.1
  have huLim_mem : uLim ∈ familyOperator A xProdLim := hLimSol.2.2
  have hm_pos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  let i0 : Fin m := ⟨0, hm_pos⟩
  let xLim : H := xProdLim i0
  have hxProd_eq : xProdLim = diagonalPoint xLim := by
    ext i
    have hdiag := (mem_diagonalSubmodule_iff xProdLim).1 hxProd_mem i i0
    simp [xLim, hdiag]
  have hxLim_mem : xLim ∈ (∑ i, A i).zeros := by
    refine (mem_zeros_sum_iff_exists_mem_familyOperator_diagonalPoint A xLim).2 ?_
    have huLim_diag : uLim ∈ familyOperator A (diagonalPoint xLim) := by
      simpa [hxProd_eq] using huLim_mem
    exact ⟨uLim, huLim_orth, huLim_diag⟩
  have hweak :
      Tendsto (fun n ↦ toWeakSpace ℝ H (x n)) atTop (𝓝 (toWeakSpace ℝ H xLim)) := by
    let eval0 : ProductSpace →L[ℝ] H := coordinateCLM i0
    have hmap :
        Tendsto
          (fun n ↦ WeakSpace.map eval0 (toWeakSpace ℝ ProductSpace (diagonalPoint (x n))))
          atTop (𝓝 (WeakSpace.map eval0 (toWeakSpace ℝ ProductSpace xProdLim))) := by
      exact ((WeakSpace.map eval0).continuous.tendsto (toWeakSpace ℝ ProductSpace xProdLim)).comp
        hweakProd
    have hmap' :
        Tendsto
          (fun n ↦ toWeakSpace ℝ H (eval0 (diagonalPoint (x n))))
          atTop (𝓝 (toWeakSpace ℝ H (eval0 xProdLim))) := by
      simpa [WeakSpace.map_apply] using hmap
    simpa [eval0, xLim, coordinateCLM_apply, diagonalPoint_apply] using hmap'
  exact ⟨xLim, hxLim_mem, hweak⟩

end SetValuedOperator
