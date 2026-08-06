import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap21.Proposition_21_1_2

open scoped Manifold

noncomputable section

-- Semantic recall via `lean_leansearch` did not surface a ready-made Poincare-duality theorem for
-- this chapter context. The current repository already uses `manifoldBettiNumber`,
-- `manifoldEulerCharacteristic`, and `ROrientedManifold` as the source-facing owners.

section

variable {K : Type} [Field K]
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [ChartedSpace H M] [CompactSpace M] [IsManifold I ⊤ M]
variable {n : ℕ} [Fact (Module.finrank ℝ E = n)]

/-- Remark 21.1.5: for a compact oriented `n`-manifold, Poincare duality forces the Betti
numbers to be symmetric:
`manifoldBettiNumber K i M = manifoldBettiNumber K (n - i) M` for `i ≤ n`. Here orientability is
recorded by `Nonempty (ROrientedManifold ℤ I n M)`, and `n` is the manifold dimension coming from
`Fact (Module.finrank ℝ E = n)`. -/
theorem manifoldBettiNumber_symm_of_oriented
    (h_oriented : Nonempty (ROrientedManifold ℤ I n M)) (i : ℕ) (hi : i ≤ n) :
    manifoldBettiNumber K i M = manifoldBettiNumber K (n - i) M := sorry

/-- If the orientation on `M` is already available as an instance, the Betti-number symmetry of
Remark 21.1.5 can be used without passing an explicit `Nonempty` witness. -/
theorem manifoldBettiNumber_symm [ROrientedManifold ℤ I n M] (i : ℕ) (hi : i ≤ n) :
    manifoldBettiNumber K i M = manifoldBettiNumber K (n - i) M := by
  have h_oriented : Nonempty (ROrientedManifold ℤ I n M) := ⟨inferInstance⟩
  exact manifoldBettiNumber_symm_of_oriented h_oriented i hi

/- Remark 21.1.5 also notes that Betti-number symmetry imposes restrictions on Euler
characteristics. In this chapter, one such consequence is already recorded by the existing theorem:
-/
#check manifoldEulerCharacteristic_eq_zero_of_oddDimension

end
