import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_2_3.ScalarExtensionLocalization
import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_2_3.SubgroupRestriction
import LinearRepresentations_Serre_1977.Serre.Chap16.Exercise_16_16_1_11

noncomputable section

universe u

open scoped MonoidAlgebra Representation
open scoped Pointwise
open CategoryTheory

namespace Representation

section SwanExercise

namespace FiniteProjectiveGroupAlgebraModule

variable (Λ : Type u) [CommRing Λ]
variable (F : Type u) [Field F] [Algebra Λ F]
variable (G : Type u) [Group G]
variable [IsDedekindDomain Λ] [IsFractionRing Λ F] [Finite G]

omit [IsDedekindDomain Λ] in
/-- Helper for Exercise 16-16.2-3: the localization at a residue-characteristic maximal ideal has
residue field of that same characteristic. -/
theorem localized_residueField_charP_of_nonzeroResidualCharacteristicMaximalIdeal
    {p : ℕ} [Fact p.Prime]
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p) :
    CharP (IsLocalRing.ResidueField (Localization.AtPrime (M.1.asIdeal))) p := by
  -- `Ideal.ResidueField` is definitionally the residue field of the localization at that ideal.
  change CharP (M.1.asIdeal.ResidueField) p
  exact M.2.2

/-- Helper for Exercise 16-16.2-3: localizing at a nonzero residue-characteristic maximal ideal
keeps the original quotient field as a fraction field of the local ring. -/
theorem localizationAtPrime_isFractionRing
    {p : ℕ} [Fact p.Prime]
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p)
    [Algebra (Localization.AtPrime (M.1.asIdeal)) F]
    [IsScalarTower Λ (Localization.AtPrime (M.1.asIdeal)) F] :
    IsFractionRing (Localization.AtPrime (M.1.asIdeal)) F := by
  -- A localization of a domain has the same fraction field after inverting all nonzero elements.
  exact IsFractionRing.isFractionRing_of_isDomain_of_isLocalization
    (M.1.asIdeal.primeCompl) (Localization.AtPrime (M.1.asIdeal)) F

/-- Helper for Exercise 16-16.2-3: the local ring at a nonzero prime of a Dedekind domain is a
discrete valuation ring. -/
theorem localizationAtPrime_isDiscreteValuationRing
    {p : ℕ} [Fact p.Prime]
    (M : NonzeroResidualCharacteristicMaximalIdeal Λ p) :
    IsDiscreteValuationRing (Localization.AtPrime (M.1.asIdeal)) := by
  -- Dedekind domains are DVRs after localization at every nonzero prime ideal.
  exact IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain Λ M.2.1 _

/-- Helper for Exercise 16-16.2-3: if a module is free over a finite group algebra, then the
underlying base-linear trace of any nonidentity group element is zero. -/
theorem trace_action_eq_zero_of_free_over_groupAlgebra
    {R : Type u} [CommRing R] {H : Type u} [Group H] [Finite H]
    {M : Type u} [AddCommGroup M] [Module R M] [Module (MonoidAlgebra R H) M]
    [IsScalarTower R (MonoidAlgebra R H) M]
    [Module.Free (MonoidAlgebra R H) M] [Module.Finite (MonoidAlgebra R H) M]
    {h : H} (hh : h ≠ 1) :
    LinearMap.trace R M ((Representation.ofModule' M : Representation R H M) h) = 0 := by
  classical
  let α : Type u := Module.Free.ChooseBasisIndex (MonoidAlgebra R H) M
  letI : Fintype α := Fintype.ofFinite α
  let bRH : Module.Basis H R (MonoidAlgebra R H) := MonoidAlgebra.basis H R
  let bM : Module.Basis α (MonoidAlgebra R H) M :=
    Module.Free.chooseBasis (MonoidAlgebra R H) M
  let b : Module.Basis (H × α) R M := bRH.smulTower bM
  -- In the tensor-product basis `H × α`, left multiplication by `h` shifts the `H` coordinate,
  -- so no diagonal term survives when `h` is not the identity.
  rw [LinearMap.trace_eq_matrix_trace R b ((Representation.ofModule' M : Representation R H M) h)]
  rw [Matrix.trace]
  apply Finset.sum_eq_zero
  intro i _hi
  rcases i with ⟨x, a⟩
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
  have hmap :
      ((Representation.ofModule' M : Representation R H M) h) (b (x, a)) = b (h * x, a) := by
    simp [b, bRH, bM, Representation.ofModule', smul_smul]
  rw [hmap]
  have hne : (h * x, a) ≠ (x, a) := by
    intro hp
    have hx : h * x = x := congrArg Prod.fst hp
    have hx' : h * x = 1 * x := by
      simpa using hx
    exact hh (mul_right_cancel hx')
  simp [hne]

end FiniteProjectiveGroupAlgebraModule

end SwanExercise

end Representation
