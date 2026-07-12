import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.FiniteType

open AlgebraicGeometry CategoryTheory Opposite
open scoped AlgebraicGeometry

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace AlgebraicGeometry

/-- The standard grading on `R[T_0, \ldots, T_n]`, used to model projective `n`-space over an
affine base ring `R` by `Proj`. -/
abbrev projectiveSpaceGrading (R : Type u) [CommRing R] (n : ℕ) :
    ℕ → Submodule R (MvPolynomial (Fin (n + 1)) R) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R

/-- The standard projective `n`-space over an affine base ring `R`, realized as `Proj` of the
standard graded polynomial ring. -/
abbrev projectiveSpace (R : Type u) [CommRing R] (n : ℕ) : Scheme :=
  Proj (projectiveSpaceGrading R n)

/-- The degree-zero piece of the standard grading on `R[T_0, \ldots, T_n]` is canonically `R`,
via constant polynomials. -/
private noncomputable def projectiveSpaceDegreeZeroRingEquiv
    (R : Type u) [CommRing R] (n : ℕ) :
    ↥(projectiveSpaceGrading R n 0) ≃+* R where
  toFun p := MvPolynomial.constantCoeff p.1
  invFun r := ⟨MvPolynomial.C r, by
    exact (MvPolynomial.mem_homogeneousSubmodule 0 _).2
      (show MvPolynomial.IsHomogeneous
          (MvPolynomial.C r : MvPolynomial (Fin (n + 1)) R) 0 from
        @MvPolynomial.isHomogeneous_C (Fin (n + 1)) R _ r)⟩
  left_inv p := by
    apply Subtype.ext
    have hp : p.1.totalDegree = 0 := by
      exact (show p.1.totalDegree = 0 ↔ MvPolynomial.IsHomogeneous p.1 0 from
          @MvPolynomial.totalDegree_zero_iff_isHomogeneous (Fin (n + 1)) R _ p.1).2 <| by
        exact (MvPolynomial.mem_homogeneousSubmodule 0 _).1 p.2
    simpa [MvPolynomial.constantCoeff_eq] using
      ((show p.1.totalDegree = 0 ↔ p.1 = MvPolynomial.C (p.1.coeff 0) from
          @MvPolynomial.totalDegree_eq_zero_iff_eq_C R (Fin (n + 1)) _ p.1).1 hp).symm
  right_inv r := by
    simp
  map_mul' p q := by
    simp
  map_add' p q := by
    simp

/-- The canonical identification of the degree-zero affine base of the standard `Proj`
construction with `Spec R`. -/
private noncomputable def projectiveSpaceDegreeZeroSpecIso
    (R : Type u) [CommRing R] (n : ℕ) :
    Spec (.of ↥(projectiveSpaceGrading R n 0)) ≅ Spec (.of R) :=
  (Scheme.Spec.mapIso
    (projectiveSpaceDegreeZeroRingEquiv R n).toCommRingCatIso.op).symm

/-- The canonical structure morphism from the standard projective `n`-space over `R` to
`Spec R`. -/
abbrev projectiveSpaceToSpec (R : Type u) [CommRing R] (n : ℕ) :
    projectiveSpace R n ⟶ Spec (.of R) :=
  Proj.toSpecZero (projectiveSpaceGrading R n) ≫ (projectiveSpaceDegreeZeroSpecIso R n).hom

instance instIsProperProjectiveSpaceToSpec (R : Type u) [CommRing R] (n : ℕ) :
    IsProper (projectiveSpaceToSpec R n) := by
  let f : ↥(projectiveSpaceGrading R n 0) →+* R :=
    (projectiveSpaceDegreeZeroRingEquiv R n).toRingHom
  have hf : f.FiniteType :=
    RingHom.FiniteType.of_surjective f (projectiveSpaceDegreeZeroRingEquiv R n).surjective
  have hg : (algebraMap R (MvPolynomial (Fin (n + 1)) R)).FiniteType :=
    (RingHom.finiteType_algebraMap).2 inferInstance
  have hmap :
      algebraMap ↥(projectiveSpaceGrading R n 0) (MvPolynomial (Fin (n + 1)) R) =
        (algebraMap R (MvPolynomial (Fin (n + 1)) R)).comp f := by
    ext p m
    have hconst :
        algebraMap R (MvPolynomial (Fin (n + 1)) R) (f p) = p.1 := by
      have hp := (projectiveSpaceDegreeZeroRingEquiv R n).left_inv p
      change
        ⟨algebraMap R (MvPolynomial (Fin (n + 1)) R) (f p), by
          simpa [f] using p.2⟩ = p at hp
      exact congrArg Subtype.val hp
    change MvPolynomial.coeff m p.1 =
      MvPolynomial.coeff m (algebraMap R (MvPolynomial (Fin (n + 1)) R) (f p))
    exact congrArg (MvPolynomial.coeff m) hconst.symm
  have hfg : (algebraMap ↥(projectiveSpaceGrading R n 0)
      (MvPolynomial (Fin (n + 1)) R)).FiniteType := by
    rw [hmap]
    exact RingHom.FiniteType.comp hg hf
  letI : Algebra.FiniteType ↥(projectiveSpaceGrading R n 0)
      (MvPolynomial (Fin (n + 1)) R) :=
    (RingHom.finiteType_algebraMap).mp hfg
  letI : IsProper (Proj.toSpecZero (projectiveSpaceGrading R n)) :=
    Proj.instIsProperToSpecZeroOfFiniteTypeSubtypeMemOfNatNat (projectiveSpaceGrading R n)
  simpa [projectiveSpaceToSpec] using
    (IsProper.instCompScheme
      (Proj.toSpecZero (projectiveSpaceGrading R n))
      ((projectiveSpaceDegreeZeroSpecIso R n).hom) : IsProper
        (Proj.toSpecZero (projectiveSpaceGrading R n) ≫
          (projectiveSpaceDegreeZeroSpecIso R n).hom))

section

variable {X S : Scheme.{u}} {f : X ⟶ S}

/-- The canonical map from the standard projective `n`-space over `Γ(S, U)` to the affine open
subscheme `U ⊆ S`. -/
abbrev projectiveSpaceToAffineOpen (U : S.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    projectiveSpace Γ(S, U) n ⟶ U.toScheme :=
  projectiveSpaceToSpec Γ(S, U) n ≫ hU.isoSpec.inv

end

end AlgebraicGeometry
