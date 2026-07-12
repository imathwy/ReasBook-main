import StacksProject_2024.Chap13.Lemma_13_15_4_Support

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open HomologicalComplex ComplexShape
open scoped ZeroObject

universe v u

variable {A : Type u} [Category.{v} A]

section

variable [Abelian A]
variable (P : ObjectProperty A) [P.ContainsZero] [P.HasEpiCover]

/-- Lemma 13.15.4 (1): if a cochain complex `K` is zero in degrees above `a`, then there exists a
bounded-above cochain complex `Q` whose terms satisfy the object property `P`, together with a
quasi-isomorphism `Q ⟶ K` that is termwise epimorphic. -/
@[stacks 05T7]
theorem exists_termwiseEpi_quasiIso_with_terms_in_of_isStrictlyLE
    (a : ℤ) (K : CochainComplex A ℤ) (hK : K.IsStrictlyLE a) :
    ∃ (Q : CochainComplex A ℤ) (α : Q ⟶ K),
      IsTermwiseEpiStrictlyLEQuasiIsoWithTermsIn P a K Q α := by
  -- Route correction: the source-faithful descending construction now lives in the support
  -- module, so the public item file should expose it through the cached auxiliary theorem.
  exact exists_termwiseEpi_quasiIso_with_terms_in_of_isStrictlyLE_aux
    P a K hK

/-- Lemma 13.15.4 (2): if the homology of a cochain complex `K` vanishes in degrees above `a`,
then there exists a bounded-above cochain complex `Q` whose terms satisfy the object property `P`,
together with a quasi-isomorphism `Q ⟶ K`. -/
@[stacks 05T7]
theorem exists_quasiIso_with_terms_in_of_isZero_homology_above
    (a : ℤ) (K : CochainComplex A ℤ)
    (hK : ∀ n : ℤ, a < n → IsZero (K.homology n)) :
    ∃ (Q : CochainComplex A ℤ) (α : Q ⟶ K),
      IsStrictlyLEQuasiIsoWithTermsIn P a K Q α := by
  -- Route correction: the truncation-plus-part-(1) argument is already packaged in the support
  -- module, so the public theorem remains a thin wrapper over that established construction.
  exact exists_quasiIso_with_terms_in_of_isZero_homology_above_aux
    P a K hK

end
