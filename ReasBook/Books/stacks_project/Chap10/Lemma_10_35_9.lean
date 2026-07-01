import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

section

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]

/-- Lemma 10.35.9: if `q` is a prime ideal of `S` lying over a maximal ideal `m` of `R` and the
residue field extension `κ(q) / κ(m)` is algebraic, then `q` is maximal. -/
-- Proof sketch: `S ⧸ q` is a domain and canonically an `(R ⧸ m)`-algebra because `q` lies over
-- `m`. The quotient map `S ⧸ q → κ(q)` is injective, so algebraicity of `κ(q) / κ(m)` together
-- with the canonical equivalence `R ⧸ m ≃ κ(m)` makes `S ⧸ q` algebraic, hence integral, over the
-- field `R ⧸ m`. Therefore `S ⧸ q` is a field, so `q` is maximal.
theorem isMaximal_of_liesOver_of_isAlgebraic_residueField
    (m : Ideal R) [m.IsMaximal] (q : Ideal S) [q.IsPrime] [q.LiesOver m]
    [Algebra.IsAlgebraic m.ResidueField q.ResidueField] :
    q.IsMaximal := by
  letI := Ideal.Quotient.field m
  letI : Algebra (R ⧸ m) (S ⧸ q) := Ideal.Quotient.algebraOfLiesOver q m
  letI : Algebra (R ⧸ m) q.ResidueField :=
    ((Ideal.ResidueField.map m q (algebraMap R S) (q.over_def m)).comp
      (algebraMap (R ⧸ m) m.ResidueField)).toAlgebra
  letI : IsScalarTower (R ⧸ m) (S ⧸ q) q.ResidueField := by
    refine IsScalarTower.of_algebraMap_eq fun x ↦ ?_
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.algebraMap_mk_of_liesOver, Ideal.algebraMap_quotient_residueField_mk]
    change
      Ideal.ResidueField.map m q (algebraMap R S) (q.over_def m)
          (algebraMap (R ⧸ m) m.ResidueField (Ideal.Quotient.mk m x)) =
        algebraMap S q.ResidueField (algebraMap R S x)
    simp [Ideal.algebraMap_quotient_residueField_mk, Ideal.ResidueField.map_algebraMap]
  letI : IsScalarTower (R ⧸ m) m.ResidueField q.ResidueField :=
    IsScalarTower.of_algebraMap_eq' rfl
  let _ : Algebra.IsAlgebraic (R ⧸ m) q.ResidueField :=
    Algebra.IsAlgebraic.trans (R ⧸ m) m.ResidueField q.ResidueField
  let _ : Algebra.IsAlgebraic (R ⧸ m) (S ⧸ q) :=
    Algebra.IsAlgebraic.of_injective
      (IsScalarTower.toAlgHom (R ⧸ m) (S ⧸ q) q.ResidueField)
      q.injective_algebraMap_quotient_residueField
  exact Ideal.Quotient.maximal_of_isField q
    (isField_of_isIntegral_of_isField' (Field.toIsField (R ⧸ m)))

end
