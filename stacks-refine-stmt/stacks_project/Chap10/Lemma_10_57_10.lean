import Mathlib
import stacks_project.Chap10.Lemma_10_57_9

-- Declarations for this item will be appended below by the statement pipeline.

open scoped DirectSum
open HomogeneousLocalization

universe u u' v

section

variable {R : Type u} {R' : Type u'} {M : Type v}
variable [CommRing R] [CommRing R'] [Algebra R R']
variable [AddCommGroup M] [Module R' M]

attribute [local instance] RingHomInvPair.of_ringEquiv

-- Proof sketch: choose finitely many generators of the finite type algebra `R'`, homogenize the
-- defining ideal inside a polynomial ring with one extra variable of degree `1`, and then
-- homogenize a finite presentation of `M` to obtain a finite graded `S`-module whose localization
-- away from the extra variable recovers `M`.
/- Source-facing existence form of Lemma 10.57.10: keep the chapter’s canonical owner condition
`Algebra.adjoin S₀ S₁ = ⊤` as the main graded-ring conclusion. The explicit finite set of
degree-one generators is derived source-facing API, not primitive owner data. The source equality
`S₀ = R` is identified with the canonical algebra isomorphism `R ≃ₐ[R] S₀`. -/
/-- A graded localization model whose ring is generated in degree `1`, is finite type over its
degree-zero part, and whose graded module is finite over the ring. -/
class IsDegreeOneGeneratedFiniteTypeModel
    {S : Type _} [CommRing S] [Algebra R S] (grading : ℕ → Submodule R S)
    [GradedAlgebra grading] (N : Type _) [AddCommGroup N] [Module S N] : Prop where
  degreeOne_adjoin_eq_top : Algebra.adjoin (grading 0) (grading 1 : Set S) = ⊤
  finiteType : Algebra.FiniteType (grading 0) S
  moduleFinite : Module.Finite S N

/-- Lemma 10.57.10: if `R'` is a finite type `R`-algebra and `M` is a finite `R'`-module, then
there exist a graded `R`-algebra `S`, a graded `S`-module `N`, and a degree-one homogeneous
element `f` such that `R'` is `R`-algebra isomorphic to `S_(f)`, `M` is semilinearly equivalent
to `N_(f)` over this algebra isomorphism, `R ≃ₐ[R] S₀`, `S` is generated in degree `1` over
`S₀`, `S` is of finite type over `S₀`, and `N` is finite over `S`. The explicit finite set of
degree-one generators from the source is kept below as a companion consequence, while the main
theorem records the chapter-owner finite-type condition `Algebra.FiniteType (S₀) S`. This is the
degree-zero-piece form of the source conditions `S₀ = R` and “`S` is generated over `R` by
finitely many degree-one elements”. -/
@[stacks 052N]
-- Proof sketch: choose finitely many generators of the finite type algebra `R'`, homogenize the
-- defining ideal inside a polynomial ring with one extra variable of degree `1`, and then
-- homogenize a finite presentation of `M` to obtain a finite graded `S`-module whose localization
-- away from the extra variable recovers `M`.
theorem exists_graded_localization_model_of_finite_module
    [Algebra.FiniteType R R'] [Module.Finite R' M] :
    ∃ (S : Type _) (_ : CommRing S) (_ : Algebra R S)
      (grading : ℕ → Submodule R S) (_ : GradedAlgebra grading)
      (N : Type _) (_ : AddCommGroup N) (_ : Module S N)
      (_ : Module R N) (_ : IsScalarTower R S N)
      (gradingN : ℕ → Submodule R N) (_ : DirectSum.Decomposition gradingN)
      (_ : SetLike.GradedSMul grading gradingN) (f : grading 1),
      ∃ zeroIso : R ≃ₐ[R] grading 0,
          ∃ ringIso : R' ≃ₐ[R] Away grading (f : S),
          ∃ moduleIso :
              M ≃ₛₗ[(ringIso.toRingEquiv : R' →+* Away grading (f : S))]
                awayDegreeZeroPart grading gradingN f,
            IsDegreeOneGeneratedFiniteTypeModel grading N :=
  sorry

/-- A degree-one generated finite type graded ring admits a finite set of degree-one generators. -/
-- Proof sketch: choose finitely many algebra generators of `S` over `grading 0`, write each one
-- using the degree-one generating hypothesis, and collect the finitely many homogeneous degree-one
-- elements appearing in those expressions into a single finite generating set.
theorem exists_finset_degreeOne_generators_of_model
    {S : Type _} [CommRing S] [Algebra R S] (grading : ℕ → Submodule R S)
    [GradedAlgebra grading] (N : Type _) [AddCommGroup N] [Module S N]
    (hmodel : IsDegreeOneGeneratedFiniteTypeModel grading N) :
    ∃ s : Finset S,
      Algebra.adjoin (grading 0) (s : Set S) = ⊤ ∧
        ∀ x ∈ s, x ∈ grading 1 :=
  sorry

end
