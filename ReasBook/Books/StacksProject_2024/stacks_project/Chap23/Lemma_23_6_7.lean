import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.TensorProduct.Basic
import StacksProject_2024.stacks_project.Chap23.Definition_23_6_5

-- Declarations for this item will be appended below by the statement pipeline.

universe uR uR' uA

open scoped TensorProduct

namespace DifferentialGradedAlgebra

section

variable {R : Type uR} {R' : Type uR'} {A : Type uA}
variable [CommRing R] [CommRing R'] [CommRing A] [Algebra R A] [Algebra R R']

-- Semantic Lean search hits used here: `Submodule.baseChange`,
-- `Submodule.tmul_mem_baseChange_of_mem`, and `LinearMap.baseChange`, matching the tensor-product
-- base-change surface for the local `CompatibleDividedPowers` owner from `Definition_23_6_5`.

/-- The base-changed grading on `R' ⊗[R] A`, obtained by extending scalars on each homogeneous
piece. -/
abbrev baseChangeGrading (grading : ℕ → Submodule R A) :
    ℕ → Submodule R' (TensorProduct R R' A) :=
  fun n ↦ Submodule.baseChange R' (grading n)

/-- Pure tensors with homogeneous right factor lie in the corresponding base-changed graded
piece. -/
theorem tmul_mem_baseChangeGrading
    (grading : ℕ → Submodule R A) {n : ℕ} (r : R') {x : A} (hx : x ∈ grading n) :
    r ⊗ₜ[R] x ∈ baseChangeGrading grading n := sorry

/-- The linear differential induced on the tensor-product base change `R' ⊗[R] A`. -/
abbrev baseChangeDifferential (d : Derivation R A A) :
    TensorProduct R R' A →ₗ[R'] TensorProduct R R' A :=
  LinearMap.baseChange R' (d : A →ₗ[R] A)

/-- The differential induced on the tensor-product base change `R' ⊗[R] A`. -/
def baseChangeDerivation (d : Derivation R A A) :
    Derivation R' (TensorProduct R R' A) (TensorProduct R R' A) :=
  Derivation.mk (baseChangeDifferential d) (by sorry) (by sorry)

/-- The base-changed differential acts on pure tensors by applying the original differential to
the `A`-factor. -/
theorem baseChangeDifferential_tmul
    (d : Derivation R A A) (r : R') (x : A) :
    baseChangeDifferential d (r ⊗ₜ[R] x) = r ⊗ₜ[R] d x := sorry

namespace CompatibleDividedPowers

variable {grading : ℕ → Submodule R A} {d : Derivation R A A} {γ : ℕ → A → A}

/-- A candidate divided-power family on `R' ⊗[R] A` is the base change of `γ` if it satisfies the
defining tensor formula on pure tensors and is compatible with the base-changed grading and
differential. -/
def IsBaseChange
    (grading : ℕ → Submodule R A) (d : Derivation R A A) (γ : ℕ → A → A)
    (γ' : ℕ → TensorProduct R R' A → TensorProduct R R' A) : Prop :=
  (∀ (n : ℕ) (r : R') {x : A}, x ∈ evenPositivePart grading →
      γ' n (r ⊗ₜ[R] x) = r ^ n • (1 ⊗ₜ[R] γ n x)) ∧
    CompatibleDividedPowers
      (baseChangeGrading grading)
      (baseChangeDerivation d)
      γ'

namespace IsBaseChange

/-- The defining tensor formula for a base-changed divided-power family. -/
theorem tmul_eq
    {γ' : ℕ → TensorProduct R R' A → TensorProduct R R' A}
    (hγ' : IsBaseChange grading d γ γ')
    (n : ℕ) (r : R') {x : A} (hx : x ∈ evenPositivePart grading) :
    γ' n (r ⊗ₜ[R] x) = r ^ n • (1 ⊗ₜ[R] γ n x) :=
  hγ'.1 n r hx

/-- A base-changed divided-power family is compatible with the base-changed grading and
differential. -/
theorem compatible
    {γ' : ℕ → TensorProduct R R' A → TensorProduct R R' A}
    (hγ' : IsBaseChange grading d γ γ') :
    CompatibleDividedPowers
      (baseChangeGrading grading)
      (baseChangeDerivation d)
      γ' :=
  hγ'.2

end IsBaseChange

end CompatibleDividedPowers

/-- Lemma 23.6.7: if `(A, d, γ)` is as in Definition 23.6.5 and `R → R'` is a ring map, then on
the tensor-product base change `A' := R' ⊗[R] A` the differential `d` and the divided powers `γ`
induce a base-changed divided-power extension compatible with the base-changed grading and the
base-changed differential. -/
@[stacks 09PL]
theorem exists_baseChangeCompatibleDividedPowers
    (grading : ℕ → Submodule R A) (d : Derivation R A A) (γ : ℕ → A → A)
    (hγ : CompatibleDividedPowers grading d γ) :
    ∃ γ' : ℕ → TensorProduct R R' A → TensorProduct R R' A,
      CompatibleDividedPowers.IsBaseChange grading d γ γ' := sorry

end

end DifferentialGradedAlgebra
