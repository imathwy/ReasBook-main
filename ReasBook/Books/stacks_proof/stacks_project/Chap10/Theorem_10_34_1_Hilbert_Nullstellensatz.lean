import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable (k : Type u) [Field k]
variable {A : Type v} [CommRing A] [Algebra k A] [Algebra.FiniteType k A]

/-- Theorem 10.34.1 (Hilbert Nullstellensatz) (3): for a maximal ideal `m` of a finite type
`k`-algebra `A`, the residue field `m.ResidueField` is finite as a `k`-module; equivalently, the
field extension `m.ResidueField / k` is finite. -/
@[stacks 00FV]
theorem finite_residueField_of_isMaximal_of_finiteType
    (m : Ideal A) [m.IsMaximal] :
    Module.Finite k m.ResidueField := by
  let _ : Algebra.FiniteType k m.ResidueField :=
    Algebra.FiniteType.of_surjective
      (IsScalarTower.toAlgHom k (A ⧸ m) m.ResidueField)
      (Ideal.bijective_algebraMap_quotient_residueField m).surjective
  simpa using (finite_of_finite_type_of_isJacobsonRing k m.ResidueField)

/- Theorem 10.34.1 (Hilbert Nullstellensatz) (4): any finite type `k`-algebra is a Jacobson ring;
equivalently, every radical ideal is the intersection of the maximal ideals containing it. This is
the canonical theorem `isJacobsonRing_of_finiteType`. -/
recall isJacobsonRing_of_finiteType

end

section

variable {k : Type u} [Field k]
variable {n : ℕ}

-- Proof sketch: first note that the residue field of a maximal ideal of
-- `MvPolynomial (Fin n) k` is again a finite type `k`-algebra, using the surjective algebra map
-- from the quotient by the maximal ideal to its residue field. Then apply
-- `finite_of_finite_type_of_isJacobsonRing` over the Jacobson base field `k`.
/-- Theorem 10.34.1 (Hilbert Nullstellensatz) (1): for a maximal ideal `m` of the polynomial ring
`k[x_1, \ldots, x_n]`, formalized as `MvPolynomial (Fin n) k`, the residue field `m.ResidueField`
is finite as a `k`-module; equivalently, the field extension `m.ResidueField / k` is finite. -/
@[stacks 00FV]
theorem finite_residueField_of_isMaximal_mvPolynomial
    (m : Ideal (MvPolynomial (Fin n) k)) [m.IsMaximal] :
    Module.Finite k m.ResidueField :=
  finite_residueField_of_isMaximal_of_finiteType k m

/- Theorem 10.34.1 (Hilbert Nullstellensatz) (2): the polynomial ring `k[x_1, \ldots, x_n]`,
formalized as `MvPolynomial (Fin n) k`, is a Jacobson ring; equivalently, every radical ideal is
the intersection of the maximal ideals containing it. This is the canonical theorem
`MvPolynomial.isJacobsonRing_MvPolynomial_fin`. -/
recall MvPolynomial.isJacobsonRing_MvPolynomial_fin

end
