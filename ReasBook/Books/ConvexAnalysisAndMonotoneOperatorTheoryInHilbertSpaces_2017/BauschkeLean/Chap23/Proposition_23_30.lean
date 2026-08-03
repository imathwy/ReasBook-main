import BauschkeLean.Chap20.Definition_20_42
import BauschkeLean.Chap23.Proposition_23_2

-- Semantic recall note: the reusable owners for this item are the Chapter 20 partial-inverse API
-- `A₍V₎`, `mem_partialInverse_iff` and the Chapter 23 resolvent graph criterion
-- `mem_resolvent_smul_iff_mem_graph`, so the source-facing proposition is refined as a thin
-- bridge between those canonical repository surfaces.

open scoped InnerProductSpace Pointwise SetValuedOperator
open ERealFunction

universe u

namespace SetValuedOperator

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Helper for Proposition 23.30: clause (1) identifies membership in the scaled partial-inverse
resolvent for a set-valued operator `A`, a closed subspace `V`, `γ ∈ ℝ_{++}`,
and `x p : H`, membership in the resolvent `J[γ • (A₍V₎)] x` is equivalent to the graph-membership
condition
`(γ⁻¹ • P_V (x - p) + P_{Vᗮ} p) ∈ A (P_V p + γ⁻¹ • P_{Vᗮ} (x - p))`.

The source states this under maximal monotonicity, but the equivalence itself depends only on the
canonical resolvent and partial-inverse owners. -/
theorem mem_resolvent_smul_partialInverse_iff
    {A : SetValuedOperator H H} (V : Submodule ℝ H)
    [V.HasOrthogonalProjection] (x p : H) (γ : PosReal) :
    p ∈ J[((γ : ℝ) • (A₍V₎))] x ↔
      (γ : ℝ)⁻¹ • V.starProjection (x - p) + Vᗮ.starProjection p ∈
        A (V.starProjection p + (γ : ℝ)⁻¹ • Vᗮ.starProjection (x - p)) := by
  rw [mem_resolvent_smul_iff_mem_graph, mem_graph, mem_partialInverse_iff]
  simp [add_comm]

/-- Helper for Proposition 23.30: the residual of the Spingarn point
`P_V p + P_{Vᗮ} (x - p)` is the complementary Spingarn residual
`P_V (x - p) + P_{Vᗮ} p`. -/
private lemma sub_spingarnPoint_eq_spingarnResidual
    (V : Submodule ℝ H) [V.HasOrthogonalProjection] (x p : H) :
    x - (V.starProjection p + Vᗮ.starProjection (x - p)) =
      V.starProjection (x - p) + Vᗮ.starProjection p := by
  have hOrth :
      Vᗮ.starProjection x - Vᗮ.starProjection (x - p) = Vᗮ.starProjection p := by
    -- Push the identity `x - (x - p) = p` through the orthogonal-complement projector.
    have hSub : Vᗮ.starProjection (x - (x - p)) = Vᗮ.starProjection p :=
      congrArg Vᗮ.starProjection (sub_sub_cancel x p)
    rw [← ContinuousLinearMap.map_sub]
    exact hSub
  -- Split `x` into its orthogonal components and regroup the two projected differences.
  calc
    x - (V.starProjection p + Vᗮ.starProjection (x - p))
        = (V.starProjection x + Vᗮ.starProjection x) -
            (V.starProjection p + Vᗮ.starProjection (x - p)) := by
              rw [V.starProjection_add_starProjection_orthogonal]
    _ = (V.starProjection x - V.starProjection p) +
          (Vᗮ.starProjection x - Vᗮ.starProjection (x - p)) := by
            abel_nf
    _ = V.starProjection (x - p) +
          (Vᗮ.starProjection x - Vᗮ.starProjection (x - p)) := by
            rw [← ContinuousLinearMap.map_sub]
    _ = V.starProjection (x - p) + Vᗮ.starProjection p := by
            rw [hOrth]

/-- Proposition 23.30 (2): for a set-valued operator `A`, a closed subspace `V`, and `x p : H`,
membership in `J[A₍V₎] x` is equivalent to membership of the transformed point
`P_V p + P_{Vᗮ} (x - p)` in `J[A] x`.

As in clause (1), the source states this under maximal monotonicity, but the equivalence is a
direct bridge between the Chapter 20 partial inverse and the Chapter 23 resolvent owner API. -/
theorem mem_resolvent_partialInverse_iff_mem_resolvent
    {A : SetValuedOperator H H} (V : Submodule ℝ H)
    [V.HasOrthogonalProjection] (x p : H) :
    p ∈ J[(A₍V₎)] x ↔
      V.starProjection p + Vᗮ.starProjection (x - p) ∈ J[A] x := by
  set q := V.starProjection p + Vᗮ.starProjection (x - p)
  have hPartialRaw :
      p ∈ J[(A₍V₎)] x ↔
        V.starProjection (x - p) + Vᗮ.starProjection p ∈ A q := by
    -- First record clause (1) at `γ = 1` in the normalized Spingarn coordinates.
    simpa only [q, posReal_coe_one, one_smul, inv_one] using
      (mem_resolvent_smul_partialInverse_iff (A := A) V x p (1 : PosReal))
  have hResidual : V.starProjection (x - p) + Vᗮ.starProjection p = x - q := by
    -- This is the normalization bridge between the Spingarn residual and the actual difference.
    simpa [q] using
      (sub_spingarnPoint_eq_spingarnResidual (V := V) (x := x) (p := p)).symm
  have hPartial : p ∈ J[(A₍V₎)] x ↔ x - q ∈ A q := by
    -- Rewrite the normalized Spingarn residual into the actual difference `x - q`.
    rw [hResidual] at hPartialRaw
    exact hPartialRaw
  have hPlain : q ∈ J[A] x ↔ x - q ∈ A q := by
    -- The ordinary resolvent criterion has the same residual form when `γ = 1`.
    simpa only [posReal_coe_one, one_smul] using
      (mem_resolvent_smul_iff_sub_mem_smul A (1 : PosReal) x q)
  -- Both sides are equivalent to the same residual membership statement.
  exact hPartial.trans hPlain.symm

end SetValuedOperator
