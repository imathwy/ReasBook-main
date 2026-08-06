import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.RingTheory.Coalgebra.TensorProduct

open scoped TensorProduct
open Coalgebra

section

variable {C V : Type}
variable [AddCommMonoid C] [Module (ZMod 2) C]
variable [AddCommMonoid V] [Module (ZMod 2) V]

/-- The image of `C₀ ⊗ V` inside `C ⊗ V`. -/
abbrev degreeZeroTensorSubmodule (C₀ : Submodule (ZMod 2) C) :
    Submodule (ZMod 2) (C ⊗[(ZMod 2)] V) :=
  LinearMap.range (C₀.subtype.rTensor V)

@[simp] theorem mem_degreeZeroTensorSubmodule_iff (C₀ : Submodule (ZMod 2) C)
    {y : C ⊗[(ZMod 2)] V} :
    y ∈ degreeZeroTensorSubmodule C₀ ↔ ∃ z, C₀.subtype.rTensor V z = y :=
  Iff.rfl

variable [Coalgebra (ZMod 2) C]

/-- Source-facing data saying that a coalgebra is graded and connected in the sense used by May:
`C` is the direct sum of its homogeneous pieces, the negative pieces vanish, the counit on `C₀`
is an isomorphism, and comultiplication preserves total degree.

The last condition is expressed by a finite pure-tensor representation of the comultiplication of
each homogeneous element.  In particular, this structure does not assume the primitive-element
conclusion of Lemma 25.4.10. -/
structure ConnectedGradedCoalgebraData (C : Type) [AddCommMonoid C] [Module (ZMod 2) C]
    [Coalgebra (ZMod 2) C] where
  /-- The degree-`n` homogeneous subspace `Cₙ`. -/
  component : ℤ → Submodule (ZMod 2) C
  /-- Every element is a finite sum of homogeneous elements. -/
  decompose : ∀ c : C, ∃ (degrees : Finset ℤ) (part : ℤ → C),
    (∀ n ∈ degrees, part n ∈ component n) ∧ ∑ n ∈ degrees, part n = c
  /-- A finite sum of homogeneous elements of distinct degrees is unique. -/
  independent : ∀ (degrees : Finset ℤ) (part : ℤ → C),
    (∀ n ∈ degrees, part n ∈ component n) →
      (∑ n ∈ degrees, part n = 0) → ∀ n ∈ degrees, part n = 0
  /-- Connected graded coalgebras have no negative-degree part. -/
  negative_eq_bot : ∀ n : ℤ, n < 0 → component n = ⊥
  /-- Connectedness: the counit restricts to an isomorphism `C₀ ≃ ZMod 2`. -/
  counit_degreeZero_bijective :
    Function.Bijective
      (Coalgebra.counit (R := ZMod 2) (A := C) ∘ₗ (component 0).subtype)
  /-- The coalgebra grading: a degree-`n` element has comultiplication terms only in
  `C_p ⊗ C_q` with `p + q = n`. -/
  comul_homogeneous : ∀ (n : ℤ) (c : C), c ∈ component n →
    ∃ (m : ℕ) (left right : Fin m → C) (leftDegree rightDegree : Fin m → ℤ),
      Coalgebra.comul c = ∑ i, left i ⊗ₜ[(ZMod 2)] right i ∧
      (∀ i, left i ∈ component (leftDegree i)) ∧
      (∀ i, right i ∈ component (rightDegree i)) ∧
      (∀ i, leftDegree i + rightDegree i = n)

namespace ConnectedGradedCoalgebraData

/-- The distinguished element `1 ∈ C₀` of a connected graded coalgebra, defined as the unique
degree-zero element whose counit is `1 ∈ ZMod 2`. -/
noncomputable def one (connected : ConnectedGradedCoalgebraData C) : C :=
  ((connected.counit_degreeZero_bijective.2 (1 : ZMod 2)).choose : connected.component 0)

/-- The distinguished element of a connected graded coalgebra belongs to `C₀`. -/
theorem one_mem_degreeZero (connected : ConnectedGradedCoalgebraData C) :
    connected.one ∈ connected.component 0 :=
  (connected.counit_degreeZero_bijective.2 (1 : ZMod 2)).choose.property

/-- The counit of the distinguished degree-zero element is `1`. -/
@[simp] theorem counit_one (connected : ConnectedGradedCoalgebraData C) :
    Coalgebra.counit (R := ZMod 2) connected.one = 1 := by
  exact (connected.counit_degreeZero_bijective.2 (1 : ZMod 2)).choose_spec

end ConnectedGradedCoalgebraData

/-- Helper for Lemma 25.4.10: extracting a basis coefficient after `Coalgebra.comul.rTensor V`
applies `Coalgebra.comul` to that coefficient. -/
lemma equivFinsuppOfBasisRight_comul_rTensor_apply
    {κ : Type} [DecidableEq κ] (𝒞 : Module.Basis κ (ZMod 2) V)
    (y : C ⊗[(ZMod 2)] V) (i : κ) :
    (TensorProduct.equivFinsuppOfBasisRight 𝒞) (Coalgebra.comul.rTensor V y) i =
      Coalgebra.comul ((TensorProduct.equivFinsuppOfBasisRight 𝒞) y i) := by
  -- Reduce to pure tensors, where both sides are definitionally the same coefficient formula.
  induction y using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul c v =>
      simp
  | add y z hy hz =>
      -- The coefficient extractor and `Coalgebra.comul.rTensor V` are both linear.
      simp [hy, hz]

omit [Coalgebra (ZMod 2) C] in
/-- Helper for Lemma 25.4.10: extracting a basis coefficient after reassociating `oneC ⊗ₜ y`
produces `oneC ⊗ₜ` the corresponding coefficient of `y`. -/
lemma equivFinsuppOfBasisRight_assocSymm_one_tmul_apply
    {κ : Type} [DecidableEq κ] (𝒞 : Module.Basis κ (ZMod 2) V)
    (oneC : C) (y : C ⊗[(ZMod 2)] V) (i : κ) :
    (TensorProduct.equivFinsuppOfBasisRight 𝒞)
        ((TensorProduct.assoc (ZMod 2) C C V).symm (oneC ⊗ₜ[(ZMod 2)] y)) i =
      oneC ⊗ₜ[(ZMod 2)] ((TensorProduct.equivFinsuppOfBasisRight 𝒞) y i) := by
  -- Reduce to pure tensors, where the associator sends `oneC ⊗ₜ (c ⊗ₜ v)` to `(oneC ⊗ₜ c) ⊗ₜ v`.
  induction y using TensorProduct.induction_on with
  | zero =>
      simp
  | tmul c v =>
      simp
  | add y z hy hz =>
      -- Linearity on the tensor coordinate turns the sum case into the inductive hypotheses.
      simp [TensorProduct.tmul_add, hy, hz]

omit [Coalgebra (ZMod 2) C] in
/-- Helper for Lemma 25.4.10: a pure tensor whose left factor lies in `C₀` belongs to the image of
`C₀ ⊗ V` inside `C ⊗ V`. -/
lemma tmul_mem_degreeZeroTensorSubmodule (C₀ : Submodule (ZMod 2) C)
    {c : C} (hc : c ∈ C₀) (v : V) :
    c ⊗ₜ[(ZMod 2)] v ∈ degreeZeroTensorSubmodule (C := C) (V := V) C₀ := by
  -- Use the obvious preimage tensor in `C₀ ⊗ V`.
  refine ⟨((⟨c, hc⟩ : C₀) ⊗ₜ[(ZMod 2)] v), ?_⟩
  simp

omit [Coalgebra (ZMod 2) C] in
/-- Helper for Lemma 25.4.10: if every basis coefficient of a tensor lies in `C₀`, then the tensor
itself lies in the image of `C₀ ⊗ V`. -/
lemma coeffSum_mem_degreeZeroTensorSubmodule
    {κ : Type} [DecidableEq κ] (C₀ : Submodule (ZMod 2) C)
    (𝒞 : Module.Basis κ (ZMod 2) V) (b : κ →₀ C)
    (hb : ∀ i, b i ∈ C₀) :
    (TensorProduct.equivFinsuppOfBasisRight 𝒞).symm b ∈
      degreeZeroTensorSubmodule (C := C) (V := V) C₀ := by
  -- Rewrite the tensor in basis coordinates and check each pure tensor summand separately.
  rw [TensorProduct.equivFinsuppOfBasisRight_symm_apply]
  refine Submodule.sum_mem _ ?_
  intro i hi
  -- Each coefficient contributes a pure tensor with left factor already known to lie in `C₀`.
  exact tmul_mem_degreeZeroTensorSubmodule (C := C) (V := V) C₀ (hb i) (𝒞 i)

/-- Lemma 25.4.10: for a connected graded coalgebra `C`, an element of `C ⊗ V` satisfies the
primitive-type equation `(ψ ⊗ id) y = 1 ⊗ y` if and only if it lies in `C₀ ⊗ V`.

Here `connected.one` is canonically defined as the unique degree-zero element whose counit is
`1`. Crucially, the primitive-element characterization is the conclusion rather than a
connectedness hypothesis. -/
theorem primitiveType_eq_one_tmul_mem_degreeZeroTensor
    (connected : ConnectedGradedCoalgebraData C)
    {y : C ⊗[(ZMod 2)] V} :
    (
      Coalgebra.comul.rTensor V y =
        (TensorProduct.assoc (ZMod 2) C C V).symm
          (connected.one ⊗ₜ[(ZMod 2)] y)) ↔
      y ∈ degreeZeroTensorSubmodule (connected.component 0) := by
  sorry

end
