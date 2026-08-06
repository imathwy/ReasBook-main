import Mathlib.Data.Nat.ModEq
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Proposition_21_1_2

open scoped Manifold

noncomputable section

-- Semantic recall via `lean_leansearch` did not surface a ready-made compact-oriented-manifold
-- parity theorem for Euler characteristic in the current environment. This chapter already uses
-- `manifoldEulerCharacteristic` for `χ(M)` and `ROrientedManifold` for orientation data.

section

variable {K : Type} [Field K]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace H M] [CompactSpace M] [IsManifold I ⊤ M]

/-- Proposition 21.1.3: If `M` is compact oriented and `dim M ≡ 2 [MOD 4]`, then `χ(M)` is even.
Here `n` records the manifold dimension via `Fact (Module.finrank ℝ E = n)`, the oriented
manifold structure is `[ROrientedManifold ℤ I n M]`, and `χ(M)` is
`manifoldEulerCharacteristic K M`. -/
theorem even_manifoldEulerCharacteristic_of_oriented_dim_modEq_two {n : ℕ}
    [Fact (Module.finrank ℝ E = n)] [ROrientedManifold ℤ I n M]
    (h_dim : n ≡ 2 [MOD 4]) :
    Even (manifoldEulerCharacteristic K M) := by
  sorry

/-- Arithmetic companion to Proposition 21.1.3, for the common dimension presentation
`Module.finrank ℝ E = 4 * m + 2`. -/
theorem even_manifoldEulerCharacteristic_of_oriented_dim_eq_four_mul_add_two (m : ℕ)
    [Fact (Module.finrank ℝ E = 4 * m + 2)]
    [ROrientedManifold ℤ I (4 * m + 2) M] :
    Even (manifoldEulerCharacteristic K M) := by
  sorry

end
