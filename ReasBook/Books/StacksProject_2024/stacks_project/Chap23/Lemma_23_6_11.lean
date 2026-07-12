import StacksProject_2024.Chap23.Lemma_23_6_9

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe uR uA uB uH0A uH0B

open DifferentialGradedAlgebra

/- Semantic search note: the reusable owner for compatible graded divided-power differential
graded algebras now lives upstream in `Lemma_23_6_9` alongside the source-facing Tate-resolution
specialization. This file therefore keeps only the lifting statement of Lemma 23.6.11 and reuses
that shared owner, its polynomial-presentation bridge, and its `H₀`-compatibility predicate. -/

section

variable {R : Type uR} [CommRing R]

/-- Lemma 23.6.11: let `(A, d, γ)` and `(B, d, γ)` be compatible differential graded
divided-power `R`-algebras as in Definition 23.6.5. If `A` is a graded divided-power polynomial
algebra over `R`, the positive homology of `B` vanishes, and
`φbar : H₀(A) → H₀(B)` is an `R`-algebra map, then there exists a compatible differential graded
divided-power `R`-algebra map `φ : A → B` whose induced map on degree-zero homology is `φbar`. -/
@[stacks 09PP]
theorem exists_compatibleDividedPowerDGAHom_lifting_h0AlgHom
    (A : GradedDividedPowerDGAlgebra.{uR, uA} R)
    (B : GradedDividedPowerDGAlgebra.{uR, uB} R)
    (presentationA : A.PolynomialPresentation)
    {H0A : Type uH0A} [CommRing H0A] [Algebra R H0A]
    (qA : A →ₐ[R] H0A)
    (qA_d : ∀ x : A, qA (A.d x) = 0)
    (qA_positive :
      ∀ ⦃n : ℕ⦄ ⦃x : A⦄, 0 < n → x ∈ A.grading n → qA x = 0)
    (qA_surjective :
      ∀ z : H0A, ∃ x : A, x ∈ A.grading 0 ∧ qA x = z)
    (qA_eq_zero_iff_boundary :
      ∀ ⦃x : A⦄, x ∈ A.grading 0 →
        (qA x = 0 ↔ ∃ y : A, y ∈ A.grading 1 ∧ A.d y = x))
    {H0B : Type uH0B} [CommRing H0B] [Algebra R H0B]
    (qB : B →ₐ[R] H0B)
    (qB_d : ∀ x : B, qB (B.d x) = 0)
    (qB_positive :
      ∀ ⦃n : ℕ⦄ ⦃x : B⦄, 0 < n → x ∈ B.grading n → qB x = 0)
    (qB_surjective :
      ∀ z : H0B, ∃ x : B, x ∈ B.grading 0 ∧ qB x = z)
    (qB_eq_zero_iff_boundary :
      ∀ ⦃x : B⦄, x ∈ B.grading 0 →
        (qB x = 0 ↔ ∃ y : B, y ∈ B.grading 1 ∧ B.d y = x))
    (hBpos : B.PositiveHomologyVanishes)
    (φbar : H0A →ₐ[R] H0B) :
    ∃ φ : GradedDividedPowerDGAlgebraHom R A B,
      φ.InducesH0 qA qB φbar := sorry

end
