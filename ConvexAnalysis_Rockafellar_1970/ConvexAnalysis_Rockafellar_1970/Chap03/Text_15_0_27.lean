import Mathlib
import ConvexAnalysis_Rockafellar_1970.Chap03.Text_15_0_26

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

section

open Matrix
open scoped RealInnerProductSpace

local notation "R2" => EuclideanSpace ℝ (Fin 2)

/-!
Source/core/bridge triage for this item.

- `source-facing`: Text 15.0.27 is the explicit planar example of the polar of the axis-aligned
  elliptic disk with semiaxes `α1` and `α2`.
- `core/canonical`: the owner abstraction is the chapter polar-set operator `Set.polar`, and the
  preceding quadratic item already gives the canonical ellipsoid-polar formula for quadratic unit
  sublevel sets.
- `bridge/view`: this item specializes that quadratic owner formula to the diagonal quadratic form
  whose coordinate expression is `(x 0)^2 / α1^2 + (x 1)^2 / α2^2`.

Domain-style sampling used here:
- `Set.polar` from `Text_14_0_5`;
- the nearby owner theorem
  `polar_matrixQuadraticSublevel_eq_inverse_matrixQuadraticSublevel` from `Text_15_0_26`.

Layer target: `source-facing`, stated directly as an equality between the polar of the concrete
elliptic disk and the corresponding dual elliptic disk, without introducing any auxiliary wrapper
for planar ellipses.
-/

private theorem inner_toEuclideanLin_diagonal_fin2 (β1 β2 : ℝ) (x : R2) :
    ⟪x, toEuclideanLin (Matrix.diagonal ![β1, β2]) x⟫ =
      β1 * (x 0) ^ 2 + β2 * (x 1) ^ 2 := by
  have hdot :
      ⟪x, toEuclideanLin (Matrix.diagonal ![β1, β2]) x⟫ =
        (toEuclideanLin (Matrix.diagonal ![β1, β2]) x).ofLp ⬝ᵥ star x.ofLp := by
    simpa using EuclideanSpace.inner_eq_star_dotProduct x
      (toEuclideanLin (Matrix.diagonal ![β1, β2]) x)
  rw [hdot, Matrix.toEuclideanLin, Matrix.ofLp_toLpLin, Matrix.toLin'_apply]
  simp [Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two, pow_two]
  ring

-- Proof sketch: apply
-- `polar_matrixQuadraticSublevel_eq_inverse_matrixQuadraticSublevel` to the diagonal positive
-- definite quadratic form with coefficients `α1⁻²` and `α2⁻²`. In coordinates, the source
-- quadratic inequality becomes `(x 0)^2 / α1^2 + (x 1)^2 / α2^2 ≤ 1`, while the inverse diagonal
-- form gives the dual inequality `α1^2 * (xStar 0)^2 + α2^2 * (xStar 1)^2 ≤ 1`.
/-- Text 15.0.27: for nonzero axis parameters `α1` and `α2`, the polar of the axis-aligned
elliptic disk `{x | (x 0)^2 / α1^2 + (x 1)^2 / α2^2 ≤ 1}` is the dual elliptic disk
`{xStar | α1^2 * (xStar 0)^2 + α2^2 * (xStar 1)^2 ≤ 1}`. Since only `α1^2` and `α2^2` appear,
the public statement needs only the nondegeneracy assumptions `α1 ≠ 0` and `α2 ≠ 0`. -/
theorem polar_axis_aligned_elliptic_disk_eq_dual_elliptic_disk
    {α1 α2 : ℝ} (hα1 : α1 ≠ 0) (hα2 : α2 ≠ 0) :
    Set.polar {x : R2 | (x 0) ^ 2 / (α1 ^ 2) + (x 1) ^ 2 / (α2 ^ 2) ≤ (1 : ℝ)} =
      {xStar : R2 | α1 ^ 2 * (xStar 0) ^ 2 + α2 ^ 2 * (xStar 1) ^ 2 ≤ (1 : ℝ)} := by
  let Q : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![(α1 ^ 2)⁻¹, (α2 ^ 2)⁻¹]
  have hQ : Q.PosDef := by
    dsimp [Q]
    exact Matrix.PosDef.diagonal fun i ↦ by
      fin_cases i
      · exact inv_pos.mpr (sq_pos_iff.mpr hα1)
      · exact inv_pos.mpr (sq_pos_iff.mpr hα2)
  have hsource :
      {x : R2 | ⟪x, toEuclideanLin Q x⟫ ≤ 1} =
        {x : R2 | (x 0) ^ 2 / (α1 ^ 2) + (x 1) ^ 2 / (α2 ^ 2) ≤ (1 : ℝ)} := by
    ext x
    simp [Q, inner_toEuclideanLin_diagonal_fin2, div_eq_mul_inv, mul_comm]
  have hQdiagInv :
      Ring.inverse ![(α1 ^ 2)⁻¹, (α2 ^ 2)⁻¹] = ![α1 ^ 2, α2 ^ 2] := by
    have hdiagUnit : IsUnit ![(α1 ^ 2)⁻¹, (α2 ^ 2)⁻¹] := by
      refine Pi.isUnit_iff.mpr ?_
      intro i
      fin_cases i
      · exact isUnit_iff_ne_zero.mpr (inv_ne_zero <| pow_ne_zero 2 hα1)
      · exact isUnit_iff_ne_zero.mpr (inv_ne_zero <| pow_ne_zero 2 hα2)
    have hRingInv :
        Ring.inverse ![(α1 ^ 2)⁻¹, (α2 ^ 2)⁻¹] = ![(α1 ^ 2)⁻¹, (α2 ^ 2)⁻¹]⁻¹ := by
      simpa using Ring.inverse_unit hdiagUnit.unit
    rw [hRingInv]
    ext i
    fin_cases i <;> simp [Pi.inv_apply]
  have hQinv : Q⁻¹ = Matrix.diagonal ![α1 ^ 2, α2 ^ 2] := by
    simpa [Q, Matrix.inv_diagonal] using congrArg Matrix.diagonal hQdiagInv
  have htarget :
      {xStar : R2 | ⟪xStar, toEuclideanLin Q⁻¹ xStar⟫ ≤ 1} =
        {xStar : R2 | α1 ^ 2 * (xStar 0) ^ 2 + α2 ^ 2 * (xStar 1) ^ 2 ≤ (1 : ℝ)} := by
    ext xStar
    simp [hQinv, inner_toEuclideanLin_diagonal_fin2]
  rw [← hsource, ← htarget]
  exact polar_matrixQuadraticSublevel_eq_inverse_matrixQuadraticSublevel hQ

end
