import Books.AConciseCourseInAlgebraicTopology_May_1999.Chapters.Chap23.Theorem_23_5_4

noncomputable section

universe u w

-- Semantic recall via `lean_leansearch` did not surface a canonical imported Euler-class owner in
-- the current environment. Chapter 23 already fixes `ThomClass`, `thomBasedSpace`, and the
-- existence of Thom-isomorphism equivalences in Theorem 23.5.4, so the definition below keeps the
-- chosen Thom class, Thom-space cup product, and inverse Thom image explicit.

section

variable {R : Type w} [CommRing R]
variable {B : Type u} {n : ℕ} {E : B → Type u}
variable [TopologicalSpace B]
variable [TopologicalSpace (Bundle.TotalSpace (Fin n → ℝ) E)]
variable [∀ b, TopologicalSpace (E b)] [FiberBundle (Fin n → ℝ) E]
variable [∀ b, NormedAddCommGroup (E b)] [∀ b, NormedSpace ℝ (E b)]
variable [VectorBundle ℝ (Fin n → ℝ) E]
variable (H : ℤ → (X : TopCat.{u}) → Set X → Type w)
variable [∀ q (X : TopCat.{u}) (A : Set X), AddCommGroup (H q X A)]
variable [∀ q (X : TopCat.{u}) (A : Set X), Module R (H q X A)]
variable
  (fiberRestriction :
    ∀ b : B,
      thomReducedCohomology n E H (n : ℤ) →ₗ[R]
        reducedCohomology H (n : ℤ) (compactifiedFiberSphere (E b)))
  (μ : ThomClass H fiberRestriction)
  (thomCup :
    thomReducedCohomology n E H (n : ℤ) →
      thomReducedCohomology n E H (n : ℤ) →
        thomReducedCohomology n E H ((n : ℤ) + (n : ℤ)))
  (thomIsomorphism :
    H (n : ℤ) (TopCat.of B) (∅ : Set B) ≃ₗ[R]
      thomReducedCohomology n E H ((n : ℤ) + (n : ℤ)))

/-- Definition 23.7.8. For an `R`-oriented real `n`-plane bundle `ξ`, represented here by a
chosen Thom class `μ`, a chosen cup product on the reduced cohomology of `Tξ`, and a chosen Thom
isomorphism in degree `n`, the Euler class is the inverse Thom image of the square `μ ∪ μ` of the
Thom class. -/
def eulerClass :
    H (n : ℤ) (TopCat.of B) (∅ : Set B) :=
  thomIsomorphism.symm
    (thomCup μ μ)

/-- Unfolding `eulerClass` recovers the inverse Thom image of the cup-square of the chosen Thom
class. -/
@[simp] theorem eulerClass_def :
    eulerClass H fiberRestriction μ thomCup thomIsomorphism =
      thomIsomorphism.symm (thomCup μ μ) :=
  rfl

/-- Applying the chosen Thom isomorphism to `eulerClass` recovers the cup-square `μ ∪ μ`. -/
@[simp] theorem thomIsomorphism_eulerClass :
    thomIsomorphism (eulerClass H fiberRestriction μ thomCup thomIsomorphism) =
      thomCup μ μ := by
  simp [eulerClass]

end
