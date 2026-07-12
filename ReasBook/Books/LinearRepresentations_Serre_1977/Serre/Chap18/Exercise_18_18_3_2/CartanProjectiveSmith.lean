import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanSmithRange
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.CartanCokernelSmith
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.ProjectiveTriangle
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.BrauerCoordinateReadback
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.DiagonalQuotient
import LinearRepresentations_Serre_1977.Chap18.Exercise_18_18_3_2.RegularIntegerDiagonalQuotient

noncomputable section

open CategoryTheory
open scoped BigOperators MonoidAlgebra Representation TensorProduct ZeroObject

universe u

namespace Representation

section CartanProjectiveSmith

variable {p : ℕ}
variable {k : Type u} [Field k] [IsAlgClosed k] [CharP k p]
variable {G : Type u} [Group G] [Finite G]
variable [Fact p.Prime]

local instance cartanProjectiveSmithFintypePRegularConjClass :
    Fintype (PRegularConjClass G p) :=
  Fintype.ofFinite (PRegularConjClass G p)

local instance cartanProjectiveSmithDecidableEqPRegularConjClass :
    DecidableEq (PRegularConjClass G p) :=
  Classical.decEq _

/-- Helper for Exercise 18-18.3-2: the Cartan image has full ambient integral rank. -/
theorem cartanProjectiveSmith_cartanRange_toIntSubmodule_finrank_eq :
    Module.finrank ℤ ((cartanHom k G).range.toIntSubmodule) =
      Module.finrank ℤ (R₀[k](G)) := by
  let hfreeFinite := cartan_source_target_free_and_finite_support (k := k) (G := G)
  letI : Module.Free ℤ (P₀[k](G)) := hfreeFinite.1
  letI : Module.Finite ℤ (P₀[k](G)) := hfreeFinite.2.1
  letI : Module.Free ℤ (R₀[k](G)) := hfreeFinite.2.2.1
  letI : Module.Finite ℤ (R₀[k](G)) := hfreeFinite.2.2.2
  let eRange : P₀[k](G) ≃+ (cartanHom k G).range :=
    AddMonoidHom.ofInjective (cartanHom_injective (k := k) (G := G))
  have hRangeSource :
      Module.finrank ℤ ↥((cartanHom k G).range) =
        Module.finrank ℤ (P₀[k](G)) := by
    simpa using (AddEquiv.toIntLinearEquiv eRange.symm).finrank_eq
  calc
    Module.finrank ℤ ((cartanHom k G).range.toIntSubmodule) =
        Module.finrank ℤ ↥((cartanHom k G).range) := rfl
    _ = Module.finrank ℤ (P₀[k](G)) := hRangeSource
    _ = Module.finrank ℤ (R₀[k](G)) :=
      cartan_source_target_finrank_eq_support (k := k) (G := G)

/-- First missing statement for the integral Smith descent: after restricting projective
characters to the `p`-regular classes and transporting through the Cartan triangle, the Cartan
range should be identified with the regular centralizer-`p`-part diagonal lattice.

This is deliberately only a `Prop` statement: the current file records the exact input that the
projective-character lattice branch must provide without importing or editing
`CartanFormalRange.lean`. -/
def cartanRange_projectiveCharacterLattice_diagonalCoordinateStatement : Prop :=
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup

/-- Minimal missing pure-integral statement for the final Smith package.

Given the projective-character lattice coordinate description of the Cartan range, the missing
Smith-rigidity step is to show that mathlib's chosen full-rank Smith diagonal for some ambient
integral basis has absolute entries equal, up to reindexing, to the same centralizer `p`-parts.
This avoids any fixed `regularClassCoordinateAddEquiv` column-by-column Cartan diagonalization. -/
def cartanRange_regularIntegerDiagonal_smithCoefficientRigidity
    (hfull :
      Module.finrank ℤ ((cartanHom k G).range.toIntSubmodule) =
        Module.finrank ℤ (R₀[k](G))) : Prop :=
  (∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) →
    ∃ (b : Module.Basis (PRegularConjClass G p) ℤ (R₀[k](G)))
      (σ : PRegularConjClass G p ≃ PRegularConjClass G p),
      ∀ c : PRegularConjClass G p,
        Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := (cartanHom k G).range.toIntSubmodule) b hfull c) =
          ConjClasses.centralizerPPart p (σ c).1

/-- The projective-character diagonal coordinate description determines the Smith coefficients.

This is the pure finite-abelian uniqueness step for Serre 18.5(b): quotient the transported
diagonal lattice, use the intrinsic `p`-primary uniqueness of the displayed cyclic product, then
replace the generated full-rank proof by the caller's `hfull` using proof irrelevance. -/
theorem cartanRange_regularIntegerDiagonal_smithCoefficientRigidity_holds
    (hfull :
      Module.finrank ℤ ((cartanHom k G).range.toIntSubmodule) =
        Module.finrank ℤ (R₀[k](G))) :
    cartanRange_regularIntegerDiagonal_smithCoefficientRigidity
      (p := p) (k := k) (G := G) hfull := by
  classical
  intro hCoordinate
  rcases hCoordinate with ⟨e, he⟩
  let hbasis : Nonempty (Module.Basis (PRegularConjClass G p) ℤ (R₀[k](G))) :=
    ⟨Classical.choose (simple_basis_on_pRegular_classes_ring_owner (p := p) (k := k) (G := G))⟩
  have hquot :
      Nonempty
        (R₀[k](G) ⧸ (cartanHom k G).range ≃+
          ∀ c : PRegularConjClass G p, ZMod (ConjClasses.centralizerPPart p c.1)) := by
    refine ⟨?_⟩
    let eQuot :
        R₀[k](G) ⧸ (cartanHom k G).range ≃+
          ((PRegularConjClass G p → ℤ) ⧸
            (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup) :=
      QuotientAddGroup.congr
        ((cartanHom k G).range)
        ((regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup)
        e he
    exact
      eQuot.trans
        (regularIntegerDiagonalQuotient_addEquiv_pi_centralizerPPart
          (p := p) (G := G))
  rcases
      addSubgroup_exists_smith_coeffs_natAbs_perm_of_quotientEquivPiZMod
        (N := (cartanHom k G).range)
        (hbasis := hbasis)
        (d := fun c : PRegularConjClass G p ↦ ConjClasses.centralizerPPart p c.1)
        (hd := centralizerPPart_pRegular_ne_zero (p := p) (G := G))
        (hquot := hquot)
        (hunique := cartanCokernelCentralizerPPartProductUniqueness_holds (p := p) (G := G)) with
    ⟨b, hfull', σ, hcoeff⟩
  refine ⟨b, σ, ?_⟩
  intro c
  have hproof : hfull' = hfull := Subsingleton.elim hfull' hfull
  simpa [hproof] using hcoeff c

omit [CharP k p] in
/-- Intermediate Smith package for the Cartan range: the projective-character lattice gives the
correct diagonal lattice, and the remaining pure-integral Smith-rigidity statement turns that
lattice identification into the requested Smith coefficient package. -/
theorem
    cartanRange_exists_smith_coeffs_perm_via_projectiveCharacterLattice_of_smithCoefficientRigidity
    (hCoordinate :
      cartanRange_projectiveCharacterLattice_diagonalCoordinateStatement
        (p := p) (k := k) (G := G))
    (hRigidity :
      cartanRange_regularIntegerDiagonal_smithCoefficientRigidity
        (p := p) (k := k) (G := G)
        (cartanProjectiveSmith_cartanRange_toIntSubmodule_finrank_eq (k := k) (G := G))) :
    ∃ (b : Module.Basis (PRegularConjClass G p) ℤ (R₀[k](G)))
      (hfull :
        Module.finrank ℤ ((cartanHom k G).range.toIntSubmodule) =
          Module.finrank ℤ (R₀[k](G)))
      (σ : PRegularConjClass G p ≃ PRegularConjClass G p),
      ∀ c : PRegularConjClass G p,
        Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := (cartanHom k G).range.toIntSubmodule) b hfull c) =
          ConjClasses.centralizerPPart p (σ c).1 := by
  let hfull := cartanProjectiveSmith_cartanRange_toIntSubmodule_finrank_eq (k := k) (G := G)
  rcases hRigidity hCoordinate with ⟨b, σ, hcoeff⟩
  exact ⟨b, hfull, σ, hcoeff⟩

/-- Intermediate Smith package for the Cartan range using only the projective-character diagonal
coordinate statement. The Smith-rigidity step is discharged by finite `p`-primary cyclic-product
uniqueness rather than left as an additional input. -/
theorem cartanRange_exists_smith_coeffs_perm_via_projectiveCharacterLattice
    (hCoordinate :
      cartanRange_projectiveCharacterLattice_diagonalCoordinateStatement
        (p := p) (k := k) (G := G)) :
    ∃ (b : Module.Basis (PRegularConjClass G p) ℤ (R₀[k](G)))
      (hfull :
        Module.finrank ℤ ((cartanHom k G).range.toIntSubmodule) =
          Module.finrank ℤ (R₀[k](G)))
      (σ : PRegularConjClass G p ≃ PRegularConjClass G p),
      ∀ c : PRegularConjClass G p,
        Int.natAbs
            (Submodule.smithNormalFormCoeffs
              (N := (cartanHom k G).range.toIntSubmodule) b hfull c) =
          ConjClasses.centralizerPPart p (σ c).1 :=
  cartanRange_exists_smith_coeffs_perm_via_projectiveCharacterLattice_of_smithCoefficientRigidity
    (p := p) (k := k) (G := G)
    hCoordinate
    (cartanRange_regularIntegerDiagonal_smithCoefficientRigidity_holds
      (p := p) (k := k) (G := G)
      (cartanProjectiveSmith_cartanRange_toIntSubmodule_finrank_eq (k := k) (G := G)))

omit [CharP k p] in
/-- The same intermediate package, immediately fed through the existing Smith-range adapter. This
checks that the missing Smith-rigidity statement has exactly the shape expected by
`CartanSmithRange.lean`. -/
theorem
    cartanRange_exists_coordinateEquiv_of_projectiveSmithPackage
    (hCoordinate :
      cartanRange_projectiveCharacterLattice_diagonalCoordinateStatement
        (p := p) (k := k) (G := G))
    (hRigidity :
      cartanRange_regularIntegerDiagonal_smithCoefficientRigidity
        (p := p) (k := k) (G := G)
        (cartanProjectiveSmith_cartanRange_toIntSubmodule_finrank_eq (k := k) (G := G))) :
    ∃ e : R₀[k](G) ≃+ (PRegularConjClass G p → ℤ),
      (cartanHom k G).range.map e.toAddMonoidHom =
        (regularIntegerDiagonalSubmodule (p := p) (G := G)).toAddSubgroup :=
  existsCartanRangeCoordinateEquiv_of_exists_smith_coeffs_perm
    (p := p) (k := k) (G := G)
    (cartanRange_exists_smith_coeffs_perm_via_projectiveCharacterLattice_of_smithCoefficientRigidity
      (p := p) (k := k) (G := G) hCoordinate hRigidity)

end CartanProjectiveSmith

end Representation
