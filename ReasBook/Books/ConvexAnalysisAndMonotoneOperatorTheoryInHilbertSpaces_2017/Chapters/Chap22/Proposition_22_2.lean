import BauschkeLean.Chap01.Text_1_0_11
import BauschkeLean.Chap16.Proposition_16_6
import BauschkeLean.Chap20.Proposition_20_10
import BauschkeLean.Chap22.Definition_22_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped InnerProductSpace Pointwise SetValuedOperator

universe u v

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Proposition 22.2 (1): the inverse of a paramonotone set-valued operator on a real Hilbert
space is paramonotone. -/
theorem IsParamonotone.inverse {A : SetValuedOperator H H} (hA : A.IsParamonotone) :
    A⁻¹.IsParamonotone := by
  refine ⟨SetValuedOperator.IsMonotone.inverse hA.isMonotone, ?_⟩
  intro x u y v hu hv hinner
  rw [SetValuedOperator.mem_inverse_iff] at hu hv
  have hswap : y ∈ A u ∧ x ∈ A v := hA.swap_mem hu hv (by simpa [real_inner_comm] using hinner)
  exact ⟨by simpa [SetValuedOperator.mem_inverse_iff] using hswap.2,
    by simpa [SetValuedOperator.mem_inverse_iff] using hswap.1⟩

variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℝ K]

private theorem inner_sub_add_adjoint_sub_eq
    [CompleteSpace H] [CompleteSpace K]
    (L : H →L[ℝ] K) {x y a b : H} {p q : K} :
    ⟪x - y, (a + L.adjoint p) - (b + L.adjoint q)⟫_ℝ =
      ⟪x - y, a - b⟫_ℝ + ⟪L x - L y, p - q⟫_ℝ := by
  have hsplit :
      (a + L.adjoint p) - (b + L.adjoint q) = (a - b) + L.adjoint (p - q) := by
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  calc
    ⟪x - y, (a + L.adjoint p) - (b + L.adjoint q)⟫_ℝ
        = ⟪x - y, a - b⟫_ℝ + ⟪x - y, L.adjoint (p - q)⟫_ℝ := by
            rw [hsplit, inner_add_right]
    _ = ⟪x - y, a - b⟫_ℝ + ⟪L (x - y), p - q⟫_ℝ := by
          rw [(ContinuousLinearMap.adjoint_inner_right L (x - y) (p - q)).symm]
    _ = ⟪x - y, a - b⟫_ℝ + ⟪L x - L y, p - q⟫_ℝ := by
          simp [ContinuousLinearMap.map_sub]

private theorem mem_adjointImage_iff_exists
    [CompleteSpace H] [CompleteSpace K]
    (L : H →L[ℝ] K) {B : SetValuedOperator K K} {x : H} {u : H} :
    u ∈ L.adjointImage B x ↔ ∃ p ∈ B (L x), L.adjoint p = u := by
  rw [ContinuousLinearMap.adjointImage_apply, Set.mem_image]

/-- Proposition 22.2 (2): if `A` and `B` are paramonotone set-valued operators on real Hilbert
spaces and `L : H →L[ℝ] K` is bounded linear, then `A + L^* ∘ B ∘ L`, realized as
`A + L.adjointImage B`, is paramonotone. -/
theorem IsParamonotone.add_adjointImage
    [CompleteSpace H] [CompleteSpace K]
    {A : SetValuedOperator H H} (hA : A.IsParamonotone)
    (L : H →L[ℝ] K) {B : SetValuedOperator K K} (hB : B.IsParamonotone) :
    (A + L.adjointImage B).IsParamonotone := by
  refine ⟨SetValuedOperator.IsMonotone.add_adjointImage hA.isMonotone L hB.isMonotone, ?_⟩
  intro x u y v hu hv hinner
  rcases Set.mem_add.mp hu with ⟨a, ha, uL, huL, rfl⟩
  rcases Set.mem_add.mp hv with ⟨b, hb, vL, hvL, rfl⟩
  rw [mem_adjointImage_iff_exists L] at huL hvL
  rcases huL with ⟨p, hp, rfl⟩
  rcases hvL with ⟨q, hq, rfl⟩
  have hAineq : 0 ≤ ⟪x - y, a - b⟫_ℝ := hA.isMonotone ha hb
  have hBineq : 0 ≤ ⟪L x - L y, p - q⟫_ℝ := hB.isMonotone hp hq
  rw [inner_sub_add_adjoint_sub_eq L] at hinner
  have hAeq : ⟪x - y, a - b⟫_ℝ = 0 := by linarith
  have hBeq : ⟪L x - L y, p - q⟫_ℝ = 0 := by linarith
  have hswapA : b ∈ A x ∧ a ∈ A y := hA.swap_mem ha hb hAeq
  have hswapB : q ∈ B (L x) ∧ p ∈ B (L y) := hB.swap_mem hp hq hBeq
  constructor
  · exact Set.mem_add.2 ⟨b, hswapA.1, L.adjoint q,
      (mem_adjointImage_iff_exists L).2 ⟨q, hswapB.1, rfl⟩, by simp⟩
  · exact Set.mem_add.2 ⟨a, hswapA.2, L.adjoint p,
      (mem_adjointImage_iff_exists L).2 ⟨p, hswapB.2, rfl⟩, by simp⟩

end SetValuedOperator
