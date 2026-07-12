import StacksProject_2024.Chap10.«10_69_0_1_Core»
import StacksProject_2024.Chap10.Definition_10_70_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

open Polynomial

variable {R : Type u} [CommRing R]
variable (I : Ideal R)

local notation "grI" => idealAssociatedGradedRing I

local instance : Module R grI :=
  Algebra.toModule

local instance : Module (R ⧸ I) grI :=
  Algebra.toModule

local instance : IsScalarTower R (R ⧸ I) grI :=
  IsScalarTower.of_algebraMap_eq' rfl

local instance : IsScalarTower R (R ⧸ I) I.Cotangent :=
  Module.IsTorsionBySet.isScalarTower (Ideal.isTorsionBySet_cotangent I)

private def reesAlgebraDegreeOneLinear :
    I →ₗ[R] reesAlgebra I where
  toFun := reesAlgebraDegreeOne I
  map_add' x y := by
    apply Subtype.ext
    exact (monomial 1).map_add x.1 y.1
  map_smul' a x := by
    apply Subtype.ext
    exact (monomial 1).map_smul a x.1

private def idealAssociatedGradedDegreeOneLinear :
    I →ₗ[R] grI :=
  (Ideal.Quotient.mkₐ R (Ideal.map (algebraMap R (reesAlgebra I)) I)).toLinearMap.comp
    (reesAlgebraDegreeOneLinear I)

@[simp] private theorem idealAssociatedGradedDegreeOneLinear_apply
    (x : I) :
    idealAssociatedGradedDegreeOneLinear I x = idealAssociatedGradedDegreeOne x :=
  rfl

private theorem idealAssociatedGradedDegreeOneLinear_mul
    (x y : I) :
    idealAssociatedGradedDegreeOneLinear I (x * y) = 0 := by
  rw [idealAssociatedGradedDegreeOneLinear_apply, idealAssociatedGradedDegreeOne,
    Ideal.Quotient.eq_zero_iff_mem]
  have hx :
      algebraMap R (reesAlgebra I) (x : R) ∈
        Ideal.map (algebraMap R (reesAlgebra I)) I :=
    Ideal.mem_map_of_mem (algebraMap R (reesAlgebra I)) x.2
  have hmul :
      reesAlgebraDegreeOne I (x * y) =
        algebraMap R (reesAlgebra I) (x : R) * reesAlgebraDegreeOne I y := by
    apply Subtype.ext
    simp [reesAlgebraDegreeOne, Polynomial.C_mul_monomial, mul_comm]
  change reesAlgebraDegreeOne I (x * y) ∈ Ideal.map (algebraMap R (reesAlgebra I)) I
  rw [hmul]
  exact Ideal.mul_mem_right _ _ hx

private noncomputable def idealConormalDegreeOneLinearR :
    I.Cotangent →ₗ[R] grI :=
  Ideal.Cotangent.lift
    (idealAssociatedGradedDegreeOneLinear I)
    (idealAssociatedGradedDegreeOneLinear_mul I)

/-- The degree-`1` classes in the associated graded ring define the canonical linear map from the
conormal module `I / I²` to `⊕_{n ≥ 0} I^n / I^(n + 1)`. This is the `(R ⧸ I)`-linear view of the
underlying `R`-linear cotangent map. -/
private noncomputable def idealConormalDegreeOneLinear :
    I.Cotangent →ₗ[R ⧸ I] grI :=
  let f : I.Cotangent →ₗ[R] grI := idealConormalDegreeOneLinearR I
  { toFun := fun x ↦ f x
    map_add' := f.map_add
    map_smul' := by
      intro a x
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
      change f (r • x) = r • f x
      simpa using f.map_smul r x }

@[simp] private theorem idealConormalDegreeOneLinear_toCotangent
    (x : I) :
    idealConormalDegreeOneLinear I (I.toCotangent x) =
      idealAssociatedGradedDegreeOne x := by
  change idealConormalDegreeOneLinearR I (I.toCotangent x) =
    idealAssociatedGradedDegreeOne x
  exact
    Ideal.Cotangent.lift_toCotangent
      (idealAssociatedGradedDegreeOneLinear I)
      (idealAssociatedGradedDegreeOneLinear_mul I)
      x

/-- 31.19.1.2: affine algebra core of the canonical conormal-algebra quotient map
`Sym^*(\mathcal{C}_{Z/X}) ⟶ \mathcal{C}_{Z/X,*}`. For an immersion modeled on an ideal
`I ⊆ R`, this is the canonical algebra map from the symmetric algebra of the conormal module
`I.Cotangent = I / I²` to the associated graded ring `⊕_{n ≥ 0} I^n / I^(n + 1)`. -/
@[stacks 0632]
noncomputable def idealConormalAlgebraQuotient
    : SymmetricAlgebra (R ⧸ I) I.Cotangent →ₐ[R ⧸ I] grI :=
  SymmetricAlgebra.lift (idealConormalDegreeOneLinear I)

/-- On generators coming from elements of `I`, the affine conormal-algebra quotient sends the
degree-`1` symmetric generator to the corresponding degree-`1` class in the associated graded
ring. -/
@[simp] theorem idealConormalAlgebraQuotient_ι_toCotangent
    (x : I) :
    idealConormalAlgebraQuotient I
        ((SymmetricAlgebra.ι (R ⧸ I) I.Cotangent) (I.toCotangent x)) =
      idealAssociatedGradedDegreeOne x := by
  rw [idealConormalAlgebraQuotient, SymmetricAlgebra.lift_ι_apply]
  exact idealConormalDegreeOneLinear_toCotangent I x

end
