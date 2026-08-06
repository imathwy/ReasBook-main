import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap20.Definition_20_1_1
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Definition_23_3_3
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_4_5
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Problem_23_9_2
import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Problem_23_9_3

open scoped Manifold Topology

noncomputable section

section

variable {n : ℕ}
variable {M : Type} [TopologicalSpace M]
variable [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
variable [Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) = n)]
variable [IsManifold (𝓡 n) ⊤ M]
variable
  [TopologicalSpace
    (Bundle.TotalSpace (Fin n → ℝ) (TangentSpace (𝓡 n) : M → Type _))]
variable [FiberBundle (Fin n → ℝ) (TangentSpace (𝓡 n) : M → Type _)]
variable [VectorBundle ℝ (Fin n → ℝ) (TangentSpace (𝓡 n) : M → Type _)]

/-- A smooth `n`-manifold is orientable exactly when its first tangential Stiefel-Whitney class
vanishes. This is the source-facing orientability bridge behind Remark 23.3.5. -/
theorem orientable_iff_firstTangentialStiefelWhitneyClass_eq_zero
    (H2 : ModTwoCohomologyTheory) (normalizationData : StiefelWhitneyNormalization H2)
    (w : StiefelWhitneyClassFamily H2)
    (h_stiefelWhitney : IsStiefelWhitneyTheory H2 normalizationData w) :
    Nonempty (ROrientedManifold ℤ (𝓡 n) n M) ↔
      tangentialStiefelWhitneyClass n M H2 w 1 = 0 := sorry

end

/- Remark 23.3.5. Stiefel-Whitney classes detect orientability, immersions, and cobordism
information. In this development, that role is recorded by the nearby APIs for
`tangentialStiefelWhitneyClass`, the first-class criterion for orientability, immersion
obstructions for real projective spaces, tangential Stiefel-Whitney numbers, and the Chapter 23
vanishing criterion forcing a smooth closed manifold to bound, which is the source-facing
precursor of the later cobordism relation. -/

#check tangentialStiefelWhitneyClass
#check orientable_iff_firstTangentialStiefelWhitneyClass_eq_zero
#check realProjectiveSpace_pow_two_not_immerses
#check realProjectiveSpaceTangentialStiefelWhitneyNumbers_vanish_iff_odd
#check boundsCompactSmoothManifold_of_allNormalStiefelWhitneyNumbersVanish
