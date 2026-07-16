import Mathlib
import stacks_proof.stacks_project.Chap10.Definition_10_136_5
import stacks_proof.stacks_project.Chap10.Definition_10_137_10
import stacks_proof.stacks_project.Chap16.Definition_16_2_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace Algebra

open Presentation

variable {R : Type u} [CommRing R]
variable {n c : ℕ}

section

variable (f : Fin c → MvPolynomial (Fin n) R)

/- Domain-style sampling:
- primary domain: Jacobian criteria for smoothness of explicit polynomial-quotient presentations of
  relative global complete intersections;
- sampled owner declarations:
  `Algebra.SmoothAtPrime`,
  `Algebra.smoothAtPrime_iff_isSmoothAt`,
  `Algebra.Presentation.naive`,
  `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`,
  `Algebra.Presentation.jacobianColumnMinor`;
- best owner abstraction: the public source-facing smoothness owner in this chapter is
  `Algebra.SmoothAtPrime`, while the presentation-theoretic primitive data for the displayed
  quotient `R[x₁, …, xₙ] / (f₁, …, f_c)` already live on the canonical owner
  `Algebra.Presentation`; the Jacobian-minor criterion should therefore be exposed as a theorem
  about `SmoothAtPrime`, with `IsSmoothAt` used only as the internal bridge;
- primitive vs. derived:
  the primitive source-facing data are the relations `f` and the induced naive presentation of the
  quotient; the quotient type and the Jacobian minors are derived owner API coming from
  `Algebra.Presentation`, and `IsSmoothAt` is derived bridge API coming from
  `smoothAtPrime_iff_isSmoothAt`.

Source/core/bridge triage:
- `source-facing`: Lemma `10.137.15`, the Jacobian criterion for smoothness at a prime of the
  explicit quotient, stated using `SmoothAtPrime`;
- `core/canonical`: `Algebra.Presentation.IsRelativeGlobalCompleteIntersection`,
  `Algebra.Presentation.jacobianColumnMinor`, and `IsSmoothAt`;
- `bridge/view`: `smoothAtPrime_iff_isSmoothAt`, which passes between the source-facing smoothness
  predicate and the canonical local owner.
-/

local notation "PresentedIdeal" => Ideal.span (Set.range f)
local notation "PresentedAlgebra" => MvPolynomial (Fin n) R ⧸ PresentedIdeal

/- The final source-side statement phrases nonvanishing in the quotient prime. The residue-field
linear algebra naturally sees nonzero images in the residue field at that prime. -/
/-- Helper for Chap10 Lemma 10 137 15: an element has nonzero image in the residue field of a
prime exactly when it is not a member of that prime. -/
private theorem residueField_ne_zero_iff_not_mem {A : Type*} [CommRing A]
    (q : PrimeSpectrum A) (x : A) :
    algebraMap A q.asIdeal.ResidueField x ≠ 0 ↔ x ∉ q.asIdeal := by
  -- Proof comment: the kernel of the residue-field map at a prime ideal is exactly the prime.
  constructor
  · intro hx hxmem
    exact hx (Ideal.algebraMap_residueField_eq_zero.mpr hxmem)
  · intro hx hzero
    exact hx (Ideal.algebraMap_residueField_eq_zero.mp hzero)

/- This specialization is the exact transport needed after the determinant of a Jacobian minor has
been identified with the corresponding residue-field matrix determinant. -/
/-- Helper for Chap10 Lemma 10 137 15: a Jacobian column minor is nonzero in the residue field at
`q` exactly when its image in the presented quotient avoids `q`. -/
private theorem residueField_jacobianColumnMinor_ne_zero_iff_notMem
    (q : PrimeSpectrum PresentedAlgebra) (I : Set.powersetCard (Fin n) c) :
    algebraMap PresentedAlgebra q.asIdeal.ResidueField
        (algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra
          (Presentation.jacobianColumnMinor
            (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
            le_rfl I)) ≠ 0 ↔
      algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra
          (Presentation.jacobianColumnMinor
            (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
            le_rfl I) ∉ q.asIdeal := by
  -- Proof comment: apply the prime-residue-field kernel computation to this specific minor.
  exact residueField_ne_zero_iff_not_mem q _

/- The localized exact-sequence route produces units in the localization at `q`. This bridge
translates those units back to the source-side nonmembership condition. -/
/-- Helper for Chap10 Lemma 10 137 15: the image of an element in the localization at a prime is a
unit exactly when the element avoids the prime. -/
private theorem localizedUnit_iff_notMem_prime {A : Type*} [CommRing A]
    (q : PrimeSpectrum A) (x : A) :
    IsUnit (algebraMap A (Localization.AtPrime q.asIdeal) x) ↔ x ∉ q.asIdeal := by
  -- Proof comment: in the localization at `q`, precisely the complement of `q` is inverted.
  simpa [Ideal.primeCompl] using
    (IsLocalization.AtPrime.isUnit_to_map_iff
      (S := Localization.AtPrime q.asIdeal) (I := q.asIdeal) x)

/- This is the exact specialization needed after the local minor-ideal criterion finds an
invertible localized Jacobian minor. -/
/-- Helper for Chap10 Lemma 10 137 15: a Jacobian column minor becomes a unit in the localization
at `q` exactly when its image in the presented quotient avoids `q`. -/
private theorem localizedJacobianColumnMinor_isUnit_iff_notMem
    (q : PrimeSpectrum PresentedAlgebra) (I : Set.powersetCard (Fin n) c) :
    IsUnit
        (algebraMap PresentedAlgebra (Localization.AtPrime q.asIdeal)
          (algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra
            (Presentation.jacobianColumnMinor
              (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
              le_rfl I))) ↔
      algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra
          (Presentation.jacobianColumnMinor
            (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
            le_rfl I) ∉
        q.asIdeal := by
  -- Proof comment: apply the generic localization-at-prime unit criterion to this minor.
  exact localizedUnit_iff_notMem_prime q _

/- The local-ring route uses the same Jacobian matrix as the residue-field route, but evaluated in
the prime localization. Keeping this as a named object avoids repeatedly unfolding the presentation
minor in the main criterion. -/
/-- Helper for Chap10 Lemma 10 137 15: the Jacobian matrix of the displayed quotient presentation
after evaluation in the localization at a fixed prime. -/
private noncomputable def localizedJacobianMatrix
    (q : PrimeSpectrum PresentedAlgebra) :
    Matrix (Fin c) (Fin n) (Localization.AtPrime q.asIdeal) :=
  fun j i ↦
    algebraMap PresentedAlgebra (Localization.AtPrime q.asIdeal)
      (algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra (MvPolynomial.pderiv i (f j)))

/-- Helper for Chap10 Lemma 10 137 15: the localized image of a presentation-level Jacobian
column minor is the determinant of the corresponding localized Jacobian submatrix. -/
private theorem localizedJacobianColumnMinor_eq_det_localizedJacobianMatrix
    (q : PrimeSpectrum PresentedAlgebra) (I : Set.powersetCard (Fin n) c) :
    algebraMap PresentedAlgebra (Localization.AtPrime q.asIdeal)
        (algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra
          (Presentation.jacobianColumnMinor
            (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
            le_rfl I)) =
      Matrix.det
        ((localizedJacobianMatrix f q).submatrix (fun i ↦ i) (I.1.orderEmbOfFin I.2)) := by
  classical
  -- Proof comment: unfold the two Jacobian spellings once and push the localization map through
  -- the determinant; downstream proofs can now rewrite by this lemma directly.
  unfold Presentation.jacobianColumnMinor Presentation.jacobianMatrix localizedJacobianMatrix
  simp only [RingHom.map_det]
  rfl

/- The reverse direction of the final Jacobian criterion only needs the elementary fact that an
invertible square column minor lets us project to those columns and invert the resulting square
matrix. -/
/-- Helper for Chap10 Lemma 10 137 15: if a `c × n` matrix has an invertible `c × c` column
minor, then the transpose matrix map `A^c → A^n` is split injective. -/
private theorem matrixTranspose_splitInjective_of_columnMinor_unit {A : Type*} [CommRing A]
    (J : Matrix (Fin c) (Fin n) A) (I : Set.powersetCard (Fin n) c)
    (hI : IsUnit (Matrix.det (J.submatrix (fun i ↦ i) (I.1.orderEmbOfFin I.2)))) :
    ∃ l : (Fin n → A) →ₗ[A] (Fin c → A),
      l ∘ₗ Matrix.toLin' J.transpose = LinearMap.id := by
  classical
  let e := I.1.orderEmbOfFin I.2
  let M : Matrix (Fin c) (Fin c) A := J.submatrix (fun i ↦ i) e
  have hMt : IsUnit M.transpose.det := by
    -- Proof comment: the chosen square submatrix and its transpose have the same determinant.
    exact Matrix.isUnit_det_transpose M (by simpa [M] using hI)
  let E : (Fin c → A) ≃ₗ[A] (Fin c → A) :=
    Matrix.toLinearEquiv (Pi.basisFun A (Fin c)) M.transpose hMt
  refine ⟨E.symm.toLinearMap.comp (LinearMap.funLeft A A e), ?_⟩
  have hselect :
      LinearMap.funLeft A A e ∘ₗ Matrix.toLin' J.transpose =
        Matrix.toLin' M.transpose := by
    -- Proof comment: selecting the minor columns after applying `Jᵀ` is exactly the square
    -- transpose minor map.
    ext x i
    simp [M, Matrix.toLin'_apply, Matrix.mulVec, dotProduct, e, Pi.single_apply]
  have hE : E.toLinearMap = Matrix.toLin' M.transpose := by
    -- Proof comment: for the standard basis, the matrix equivalence has the expected matrix map.
    ext x i
    simp [E, Matrix.toLinearEquiv, Matrix.toLin_eq_toLin', Matrix.toLin'_apply, Matrix.mulVec,
      dotProduct, Pi.single_apply]
  calc
    E.symm.toLinearMap.comp (LinearMap.funLeft A A e) ∘ₗ Matrix.toLin' J.transpose
        = E.symm.toLinearMap.comp (Matrix.toLin' M.transpose) := by
          rw [LinearMap.comp_assoc, hselect]
    _ = E.symm.toLinearMap.comp E.toLinearMap := by
          rw [hE]
    _ = LinearMap.id := by
          -- Proof comment: the inverse of the selected square minor is the desired retraction.
          apply LinearMap.ext
          intro v
          exact E.symm_apply_apply v

/- Route correction: the principal-open route required a global Jacobian-minor span theorem before
the local Jacobian criterion had been proved. The direct route keeps the linear algebra at the
residue field of the fixed prime. -/
/-- Helper for Chap10 Lemma 10 137 15: the residue-field Jacobian matrix at a prime of the
presented quotient. -/
private noncomputable def residueJacobianMatrix
    (q : PrimeSpectrum PresentedAlgebra) : Matrix (Fin c) (Fin n) q.asIdeal.ResidueField :=
  fun j i ↦
    algebraMap PresentedAlgebra q.asIdeal.ResidueField
      (algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra (MvPolynomial.pderiv i (f j)))

/-- Helper for Chap10 Lemma 10 137 15: the residue image of a presentation-level Jacobian column
minor is the determinant of the corresponding residue Jacobian submatrix. -/
private theorem residueJacobianColumnMinor_eq_det_residueJacobianMatrix
    (q : PrimeSpectrum PresentedAlgebra) (I : Set.powersetCard (Fin n) c) :
    algebraMap PresentedAlgebra q.asIdeal.ResidueField
        (algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra
          (Presentation.jacobianColumnMinor
            (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
            le_rfl I)) =
      Matrix.det
        ((residueJacobianMatrix f q).submatrix (fun i ↦ i) (I.1.orderEmbOfFin I.2)) := by
  classical
  -- Proof comment: unfold the presentation Jacobian once and push the quotient-residue map through
  -- the determinant, so later steps can rewrite by this lemma rather than repeating the expansion.
  unfold Presentation.jacobianColumnMinor Presentation.jacobianMatrix residueJacobianMatrix
  simp only [RingHom.map_det]
  rfl

/-- Helper for Chap10 Lemma 10 137 15: nonvanishing of a residue Jacobian determinant is
equivalent to the corresponding Jacobian column minor avoiding the prime. -/
private theorem det_residueJacobianMatrix_ne_zero_iff_notMem
    (q : PrimeSpectrum PresentedAlgebra) (I : Set.powersetCard (Fin n) c) :
    Matrix.det
          ((residueJacobianMatrix f q).submatrix (fun i ↦ i) (I.1.orderEmbOfFin I.2)) ≠ 0 ↔
      algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra
          (Presentation.jacobianColumnMinor
            (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
            le_rfl I) ∉
        q.asIdeal := by
  -- Proof comment: rewrite the determinant as the residue image of the minor, then use the
  -- residue-field kernel criterion for the prime ideal.
  rw [← residueJacobianColumnMinor_eq_det_residueJacobianMatrix f q I]
  exact residueField_jacobianColumnMinor_ne_zero_iff_notMem f q I

/- The selected-column pre-submersive presentation has Jacobian exactly the selected column minor
used in the source-facing statement. -/
/-- Helper for Chap10 Lemma 10 137 15: the Jacobian of the naive pre-submersive presentation
attached to a selected set of columns is the corresponding presentation-level Jacobian column
minor in the quotient algebra. -/
private theorem naivePreSubmersive_jacobian_eq_jacobianColumnMinor
    (I : Set.powersetCard (Fin n) c) :
    (PreSubmersivePresentation.naive (R := R) (v := f)
      (I.1.orderEmbOfFin I.2) (I.1.orderEmbOfFin I.2).injective).jacobian =
      algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra
        (Presentation.jacobianColumnMinor
          (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
          le_rfl I) := by
  classical
  -- Proof comment: unfold the two Jacobian descriptions once; the selected-column map is exactly
  -- the column embedding used by `Presentation.jacobianColumnMinor`.
  rw [PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
  unfold Presentation.jacobianColumnMinor Presentation.jacobianMatrix
  simp only [RingHom.map_det]
  rw [← Matrix.det_transpose]
  apply congrArg Matrix.det
  ext i j
  simp only [Matrix.transpose_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.submatrix_apply]
  rw [PreSubmersivePresentation.jacobiMatrix_naive]
  rw [Generators.algebraMap_apply]
  have hmap :
      MvPolynomial.aeval
          (PreSubmersivePresentation.naive (R := R) (v := f)
            (I.1.orderEmbOfFin I.2) (I.1.orderEmbOfFin I.2).injective).val =
        Ideal.Quotient.mkₐ R PresentedIdeal := by
    ext k
    simp [PreSubmersivePresentation.naive]
  rw [hmap]
  simp [Presentation.naive_relation_apply]

/- Localizing a pre-submersive presentation away from its Jacobian makes the composite
presentation submersive. This isolates the proof field needed below. -/
/-- Helper for Chap10 Lemma 10 137 15: after localizing a pre-submersive presentation away from
its Jacobian, the composite presentation has a unit Jacobian. -/
private theorem preSubmersiveLocalizationAway_comp_jacobian_isUnit
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {ι σ : Type*} [Finite σ] (P : PreSubmersivePresentation A B ι σ) :
    IsUnit
      (((SubmersivePresentation.localizationAway (Localization.Away P.jacobian) P.jacobian).toPreSubmersivePresentation.comp P).jacobian) := by
  let S := Localization.Away P.jacobian
  let Q : SubmersivePresentation B S Unit Unit :=
    SubmersivePresentation.localizationAway S P.jacobian
  -- Proof comment: the composite Jacobian is the product of the old Jacobian, now inverted, and
  -- the localization presentation's unit Jacobian.
  have hΔ : IsUnit (algebraMap B S P.jacobian) :=
    IsLocalization.Away.algebraMap_isUnit P.jacobian
  rw [PreSubmersivePresentation.comp_jacobian_eq_jacobian_smul_jacobian, Algebra.smul_def]
  exact hΔ.mul Q.jacobian_isUnit

/- The easy half of the Jacobian criterion is a basic-open construction: invert a nonvanishing
minor and use the resulting submersive presentation. -/
/-- Helper for Chap10 Lemma 10 137 15: if one Jacobian column minor avoids the prime `q`, then
the presented algebra is smooth at `q`. -/
private theorem smoothAtPrime_of_jacobianColumnMinor_notMem
    (q : PrimeSpectrum PresentedAlgebra) (I : Set.powersetCard (Fin n) c)
    (hI : algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra
        (Presentation.jacobianColumnMinor
          (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
          le_rfl I) ∉ q.asIdeal) :
    SmoothAtPrime R PresentedAlgebra q := by
  classical
  let P : PreSubmersivePresentation R PresentedAlgebra (Fin n) (Fin c) :=
    PreSubmersivePresentation.naive (R := R) (v := f)
      (I.1.orderEmbOfFin I.2) (I.1.orderEmbOfFin I.2).injective
  -- Proof comment: use the selected minor itself as the basic-open denominator.
  refine ⟨P.jacobian, ?_, ?_⟩
  · rwa [naivePreSubmersive_jacobian_eq_jacobianColumnMinor (f := f) I]
  · let S := Localization.Away P.jacobian
    let Q : SubmersivePresentation PresentedAlgebra S Unit Unit :=
      SubmersivePresentation.localizationAway S P.jacobian
    letI : Module PresentedAlgebra PresentedAlgebra := Semiring.toModule
    letI : DistribMulAction PresentedAlgebra PresentedAlgebra :=
      { (Semiring.toModule : Module PresentedAlgebra PresentedAlgebra) with }
    let Ploc : SubmersivePresentation R S (Unit ⊕ Fin n) (Unit ⊕ Fin c) :=
      { toPreSubmersivePresentation := Q.toPreSubmersivePresentation.comp P
        jacobian_isUnit := preSubmersiveLocalizationAway_comp_jacobian_isUnit P }
    -- Proof comment: a submersive presentation is standard smooth, hence smooth on the basic open.
    letI : IsStandardSmooth R S := Ploc.isStandardSmooth
    exact inferInstance

/- The forward direction is now factored into a residue-field bridge and the elementary
nonzero/not-in-prime transport. The first helper is the precise remaining cotangent/Jacobian
comparison; the second helper is the completed residue-field assembly. -/
/-- Helper for Chap10 Lemma 10 137 15: smoothness at `q` should force some Jacobian column minor
to have nonzero image in the residue field at `q`. -/
private theorem exists_residueJacobianColumnMinor_ne_zero_of_isSmoothAt
    (hc : c ≤ n)
    (hP : Presentation.IsRelativeGlobalCompleteIntersection
      (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c)))
    (q : PrimeSpectrum PresentedAlgebra) (hSmooth : IsSmoothAt R q.asIdeal) :
    ∃ I : Set.powersetCard (Fin n) c,
      algebraMap PresentedAlgebra q.asIdeal.ResidueField
          (algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra
            (Presentation.jacobianColumnMinor
              (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
              le_rfl I)) ≠ 0 := by
  -- TODO: prove the smooth-to-residue-minor bridge by importing or proving the earlier
  -- conormal-basis theorem for relative-GCI naive presentations, identifying the base-changed
  -- cotangent-complex map with `residueJacobianMatrix f q`, and applying the maximal-minor
  -- linear-algebra criterion over `q.asIdeal.ResidueField`.
  sorry

/-- Helper for Chap10 Lemma 10 137 15: a nonzero residue-field Jacobian minor gives a source-side
Jacobian column minor outside the prime `q`. -/
private theorem exists_jacobianColumnMinor_notMem_of_residue_ne_zero
    (q : PrimeSpectrum PresentedAlgebra)
    (h :
      ∃ I : Set.powersetCard (Fin n) c,
        algebraMap PresentedAlgebra q.asIdeal.ResidueField
            (algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra
              (Presentation.jacobianColumnMinor
                (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
                le_rfl I)) ≠ 0) :
    ∃ I : Set.powersetCard (Fin n) c,
      algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra
          (Presentation.jacobianColumnMinor
            (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
            le_rfl I) ∉
        q.asIdeal := by
  -- Proof comment: choose the residue-nonzero minor and translate through the residue-field
  -- kernel computation for a prime ideal.
  rcases h with ⟨I, hI⟩
  exact ⟨I, (residueField_jacobianColumnMinor_ne_zero_iff_notMem f q I).mp hI⟩

/-- Helper for Chap10 Lemma 10 137 15: smoothness at `q`, once converted to a nonzero
residue-field Jacobian minor, gives a Jacobian column minor outside `q`. -/
private theorem exists_jacobianColumnMinor_notMem_of_isSmoothAt
    (hc : c ≤ n)
    (hP : Presentation.IsRelativeGlobalCompleteIntersection
      (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c)))
    (q : PrimeSpectrum PresentedAlgebra) (hSmooth : IsSmoothAt R q.asIdeal) :
    ∃ I : Set.powersetCard (Fin n) c,
      algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra
          (Presentation.jacobianColumnMinor
            (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
            le_rfl I) ∉
        q.asIdeal := by
  -- Proof comment: keep the deep cotangent/Jacobian comparison in the residue-field normal form,
  -- then apply the already proved residue-field nonzero/not-in-prime bridge.
  exact exists_jacobianColumnMinor_notMem_of_residue_ne_zero f q
    (exists_residueJacobianColumnMinor_ne_zero_of_isSmoothAt f hc hP q hSmooth)

/- The source proof first proves the source-facing statement, then translates the canonical local
predicate through `smoothAtPrime_iff_isSmoothAt`. -/
/-- Helper for Chap10 Lemma 10 137 15: for the canonical naive presentation
`R[x₁, …, xₙ] / (f₁, …, f_c)`, formal smoothness at `q` is equivalent to the existence of a
Jacobian minor indexed by a `c`-element subset of the variables whose image in the quotient avoids
`q`. -/
private theorem isSmoothAt_iff_exists_jacobian_minor_not_mem_core
    (hc : c ≤ n)
    (hP : Presentation.IsRelativeGlobalCompleteIntersection
      (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c)))
    (q : PrimeSpectrum PresentedAlgebra) :
    IsSmoothAt R q.asIdeal ↔
      ∃ I : Set.powersetCard (Fin n) c,
        algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra
            (Presentation.jacobianColumnMinor
              (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
              le_rfl I) ∉
          q.asIdeal := by
  -- Route correction: the old proof tried to prove a global principal-open span criterion first.
  -- The remaining missing step is the prime-local cotangent/Jacobian comparison: use
  -- `relativeGCI_conormalModule_has_basis`, identify the residue conormal map with
  -- `residueJacobianMatrix f q`, then apply the finite-dimensional minor criterion and the
  -- residue-field nonzero/not-in-prime bridge above.
  constructor
  · intro hSmooth
    -- Proof comment: the residue-field bridge supplies the nonzero minor; the helper above
    -- translates it into the source-side nonmembership statement.
    exact exists_jacobianColumnMinor_notMem_of_isSmoothAt f hc hP q hSmooth
  · rintro ⟨I, hI⟩
    -- Proof comment: the nonvanishing minor gives a smooth basic open, then the finite
    -- presentation bridge translates `SmoothAtPrime` back to the canonical `IsSmoothAt`.
    let _ : FinitePresentation R PresentedAlgebra :=
      Presentation.finitePresentation_of_isFinite
        (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
    exact (smoothAtPrime_iff_isSmoothAt R PresentedAlgebra q).mp
      (smoothAtPrime_of_jacobianColumnMinor_notMem f q I hI)

/-- Lemma 10.137.15: for a relative global complete intersection presentation
`S = R[x₁, …, xₙ] / (f₁, …, f_c)` with `c ≤ n` and a prime `q` of `S`, the map `R → S` is smooth
at `q` in the source-facing Stacks sense if and only if some Jacobian minor
`det(∂f_j / ∂x_i)` indexed by a `c`-element subset of the variables avoids `q`. -/
@[stacks 00TE]
theorem smoothAtPrime_iff_exists_jacobian_minor_not_mem
    (hc : c ≤ n)
    (hP : Presentation.IsRelativeGlobalCompleteIntersection
      (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c)))
    (q : PrimeSpectrum PresentedAlgebra) :
    SmoothAtPrime R PresentedAlgebra q ↔
      ∃ I : Set.powersetCard (Fin n) c,
        algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra
            (Presentation.jacobianColumnMinor
              (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
              le_rfl I) ∉
          q.asIdeal := by
  -- Proof comment: finite presentation comes from the displayed finite naive presentation.
  let _ : FinitePresentation R PresentedAlgebra :=
    Presentation.finitePresentation_of_isFinite
      (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
  -- Proof comment: translate the source-facing predicate to the canonical local smoothness owner
  -- and consume the prime-local Jacobian criterion.
  rw [smoothAtPrime_iff_isSmoothAt]
  exact isSmoothAt_iff_exists_jacobian_minor_not_mem_core f hc hP q

-- Proof sketch: use Lemma `10.136.12` to identify the naive cotangent complex of the quotient
-- presentation with the Jacobian matrix `(∂f_j/∂x_i)`. By Lemma `10.134.13`, smoothness at `q`
-- is equivalent to the localized conormal map becoming split injective. For a map between free
-- modules of ranks `c` and `n`, this happens exactly when some `c × c` minor is invertible in the
-- localization at `q`, i.e. when one Jacobian minor avoids `q`.
/-- Companion bridge for Lemma `10.137.15`: for the canonical naive presentation
`R[x₁, …, xₙ] / (f₁, …, f_c)`, formal smoothness at `q` is equivalent to the existence of a
Jacobian minor indexed by a `c`-element subset of the variables whose image in the quotient avoids
`q`. -/
theorem isSmoothAt_iff_exists_jacobian_minor_not_mem
    (hc : c ≤ n)
    (hP : Presentation.IsRelativeGlobalCompleteIntersection
      (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c)))
    (q : PrimeSpectrum PresentedAlgebra) :
    IsSmoothAt R q.asIdeal ↔
      ∃ I : Set.powersetCard (Fin n) c,
        algebraMap (MvPolynomial (Fin n) R) PresentedAlgebra
            (Presentation.jacobianColumnMinor
              (Presentation.naive : Presentation R PresentedAlgebra (Fin n) (Fin c))
              le_rfl I) ∉
          q.asIdeal := by
  -- Proof comment: reuse the canonical local criterion directly, avoiding a circular dependence on
  -- the public `SmoothAtPrime` bridge above.
  exact isSmoothAt_iff_exists_jacobian_minor_not_mem_core f hc hP q

end

end Algebra
