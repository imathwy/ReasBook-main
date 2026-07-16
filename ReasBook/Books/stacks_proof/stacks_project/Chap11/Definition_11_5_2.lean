import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Azumaya.Basic
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Unique
import stacks_proof.stacks_project.Chap11.Lemma_11_4_8
import stacks_proof.stacks_project.Chap11.Lemma_11_4_10
import Mathlib.Tactic.StacksAttribute

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Matrix
open scoped TensorProduct

universe u v

/- Domain-style sampling for Definition 11.5.2:
- primary domain: Brauer equivalence classes of finite-dimensional central simple algebras over a
  field, with tensor product and opposite algebra as the source-facing group operations;
- sampled owner declarations:
  `CSA`,
  `IsBrauerEquivalent`,
  `BrauerGroup`,
  `Br`,
  `CSA.tensorProduct`,
  `Aᵐᵒᵖ`;
- best owner abstraction: the core/canonical owner remains the quotient `BrauerGroup k`, and the
  source-facing owner notation is `Br(k) := BrauerGroup.{u, max u v} k`, which removes the
  auxiliary size hypothesis from the public group interface while keeping the same quotient owner;
- primitive data: the quotient owner `BrauerGroup k`, the representative-level tensor product
  `CSA.tensorProduct`, the opposite-algebra representative `Aᵐᵒᵖ`, and the canonical `ULift`
  representative of the neutral Brauer class;
- derived API: the quotient-level `1`, `*`, and `⁻¹` on `Br(k)`, together with the resulting
  `CommGroup` structure and the quotient computation lemmas below.

Source/core/bridge triage:
- `source-facing`: the Brauer group `Br(k)` with multiplication induced by tensor product and
  inverse induced by the opposite algebra;
- `core/canonical`: the quotient owner `BrauerGroup k`;
- `bridge/view`: the representative-level `CSA` constructions below (`unit`, `opposite`) and
  the Brauer-equivalence compatibility theorems that descend them to the quotient. -/

/-- Textbook surface notation for the Brauer group of `k`, realized on the canonical quotient
universe `max u v` so the base field itself has a size-independent neutral representative. -/
abbrev Br (k : Type u) [Field k] := BrauerGroup.{u, max u v} k

notation "Br(" k ")" => Br k

namespace CSA

variable {k : Type u} [Field k]

/-- Helper for Chap11 Definition 11 5 2: the canonical `1 × 1` matrix algebra is algebraically
equivalent to the underlying `k`-algebra. -/
def matrixOneAlgEquiv (A : Type v) [Semiring A] [Algebra k A] :
    Matrix (Fin 1) (Fin 1) A ≃ₐ[k] A :=
  (Matrix.reindexAlgEquiv k A finOneEquiv).trans uniqueAlgEquiv

/-- Helper for Chap11 Definition 11 5 2: an actual algebra equivalence already gives a Brauer
equivalence by using `1 × 1` matrix stabilizations on both sides. -/
theorem brauerEquivalentOfAlgEquiv {A B : CSA.{u, v} k} (e : A ≃ₐ[k] B) :
    IsBrauerEquivalent A B := by
  -- Package the given algebra equivalence into the defining matrix witness for Brauer equivalence.
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  refine ⟨(matrixOneAlgEquiv (k := k) A).trans <| e.trans <| (matrixOneAlgEquiv (k := k) B).symm⟩

/-- The opposite algebra of a finite-dimensional central simple `k`-algebra, repackaged as the
canonical corresponding object of `CSA k`. -/
def opposite (A : CSA.{u, v} k) : CSA.{u, v} k where
  toAlgCat := AlgCat.of k Aᵐᵒᵖ

variable (k : Type u) [Field k]

/-- The canonical `ULift` representative of the neutral Brauer class in carrier universe
`max u v`. -/
def unit : CSA.{u, max u v} k where
  toAlgCat := AlgCat.of k (ULift.{v, u} k)
  isCentral := by
    refine ⟨fun x _ ↦ ?_⟩
    exact ⟨x.down, rfl⟩
  isSimple := inferInstance
  fin_dim := by
    simpa using
      (ULift.algEquiv : ULift.{v, u} k ≃ₐ[k] k).symm.toLinearEquiv.finiteDimensional

/-- Helper for Chap11 Definition 11 5 2: the carrier of the neutral representative is canonically
identified with the base field. -/
private def unitCarrierAlgEquiv (k : Type u) [Field k] :
    ↑(unit k).toAlgCat ≃ₐ[k] k :=
  ULift.algEquiv

/-- Helper for Chap11 Definition 11 5 2: `A ⊗[k] Aᵐᵒᵖ` is identified with a full matrix algebra
over the canonical neutral representative through the Azumaya endomorphism model of `A`. -/
theorem tensorProductOppositeMatrixWitness (A : CSA.{u, v} k) :
    Nonempty <|
      A ⊗[k] Aᵐᵒᵖ ≃ₐ[k]
        Matrix (Fin (Module.finrank k A)) (Fin (Module.finrank k A)) ↑(unit k).toAlgCat := by
  -- First move to the endomorphism algebra via the Azumaya left-right action map.
  let eEnd : A ⊗[k] Aᵐᵒᵖ ≃ₐ[k] Module.End k A :=
    AlgEquiv.ofBijective (AlgHom.mulLeftRight k A) (IsAzumaya.AlgHom.mulLeftRight_bij (R := k) (A := A))
  let b : Module.Basis (Fin (Module.finrank k A)) k A := Module.finBasis k A
  let eMatrix : Module.End k A ≃ₐ[k] Matrix (Fin (Module.finrank k A)) (Fin (Module.finrank k A)) k :=
    algEquivMatrix b
  let eULift :
    Matrix (Fin (Module.finrank k A)) (Fin (Module.finrank k A)) k ≃ₐ[k]
        Matrix (Fin (Module.finrank k A)) (Fin (Module.finrank k A)) ↑(unit k).toAlgCat :=
    (unitCarrierAlgEquiv (k := k)).symm.mapMatrix
  -- Then rewrite the coefficient ring from `k` to the `ULift` model of the neutral Brauer class.
  exact ⟨eEnd.trans <| eMatrix.trans eULift⟩

variable {k}

/-- Brauer equivalence is compatible with passage to opposite algebras. -/
theorem brauerEquivalent_opposite {A B : CSA.{u, v} k} (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent A.opposite B.opposite := by
  -- Reuse the same stabilization sizes and transport the witness across opposite-matrix equivalences.
  obtain ⟨n, m, hn, hm, ⟨e⟩⟩ := h
  refine ⟨n, m, hn, hm, ?_⟩
  refine ⟨AlgEquiv.mopMatrix.trans <| (AlgEquiv.op e).trans AlgEquiv.mopMatrix.symm⟩

/-- Brauer equivalence is compatible with tensor product on representatives. -/
theorem brauerEquivalent_tensorProduct {A A' B B' : CSA.{u, v} k}
    (hAA' : IsBrauerEquivalent A A') (hBB' : IsBrauerEquivalent B B') :
    IsBrauerEquivalent (A.tensorProduct B) (A'.tensorProduct B') := by
  -- Tensor the two matrix witnesses and identify the tensor of matrix algebras with a matrix algebra.
  obtain ⟨n, m, hn, hm, ⟨eA⟩⟩ := hAA'
  obtain ⟨p, q, hp, hq, ⟨eB⟩⟩ := hBB'
  refine ⟨n * p, m * q, Nat.mul_ne_zero hn hp, Nat.mul_ne_zero hm hq, ?_⟩
  refine ⟨(Matrix.reindexAlgEquiv k (A.tensorProduct B) finProdFinEquiv).symm.trans <|
    (Matrix.kroneckerTMulAlgEquiv (Fin n) (Fin p) k k A B).symm.trans <|
    (Algebra.TensorProduct.congr eA eB).trans <|
    (Matrix.kroneckerTMulAlgEquiv (Fin m) (Fin q) k k A' B').trans <|
    Matrix.reindexAlgEquiv k (A'.tensorProduct B') finProdFinEquiv⟩

/-- Tensor product on representatives induces the associative law in the Brauer group. -/
theorem brauerEquivalent_tensorProduct_assoc (A B C : CSA.{u, v} k) :
    IsBrauerEquivalent ((A.tensorProduct B).tensorProduct C) (A.tensorProduct (B.tensorProduct C)) :=
  by
  -- The associator is already an algebra equivalence between the two representative tensor products.
  exact brauerEquivalentOfAlgEquiv
    (Algebra.TensorProduct.assoc k k k A B C)

/-- Tensor product on representatives induces the commutative law in the Brauer group. -/
theorem brauerEquivalent_tensorProduct_comm (A B : CSA.{u, v} k) :
    IsBrauerEquivalent (A.tensorProduct B) (B.tensorProduct A) := by
  -- The tensor-product braiding directly identifies the two representatives.
  exact brauerEquivalentOfAlgEquiv (Algebra.TensorProduct.comm k A B)

/-- Tensoring with the canonical neutral representative leaves a Brauer class unchanged. -/
theorem brauerEquivalent_tensorProduct_unit (A : CSA.{u, v} k) :
    IsBrauerEquivalent (A.tensorProduct (unit k)) A := by
  -- First rewrite the neutral representative to the literal base field, then remove the tensor
  -- factor with the canonical right-unit equivalence.
  let eUnit : A.tensorProduct (unit k) ≃ₐ[k] A :=
    (Algebra.TensorProduct.congr ((AlgEquiv.refl : A ≃ₐ[k] A))
      (unitCarrierAlgEquiv (k := k))).trans <|
        Algebra.TensorProduct.rid k k A
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  exact ⟨(matrixOneAlgEquiv (k := k) (A.tensorProduct (unit k))).trans <|
    eUnit.trans <| (matrixOneAlgEquiv (k := k) A).symm⟩

/-- The canonical neutral representative is a left unit for tensor product on Brauer classes. -/
theorem brauerEquivalent_unit_tensorProduct (A : CSA.{u, v} k) :
    IsBrauerEquivalent ((unit k).tensorProduct A) A := by
  -- First rewrite the neutral representative to the literal base field, then remove the tensor
  -- factor with the canonical left-unit equivalence.
  let eUnit : (unit k).tensorProduct A ≃ₐ[k] A :=
    (Algebra.TensorProduct.congr (unitCarrierAlgEquiv (k := k))
      ((AlgEquiv.refl : A ≃ₐ[k] A))).trans <|
        Algebra.TensorProduct.lid k A
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  exact ⟨(matrixOneAlgEquiv (k := k) ((unit k).tensorProduct A)).trans <|
    eUnit.trans <| (matrixOneAlgEquiv (k := k) A).symm⟩

/-- The opposite algebra represents the inverse Brauer class. -/
theorem brauerEquivalent_tensorProduct_opposite (A : CSA.{u, v} k) :
    IsBrauerEquivalent (A.tensorProduct A.opposite) (unit k) := by
  -- Use the Azumaya endomorphism model to identify `A ⊗[k] Aᵐᵒᵖ` with a full matrix algebra over `ULift k`.
  obtain ⟨e⟩ := tensorProductOppositeMatrixWitness (k := k) A
  have hfinrank : Module.finrank k A ≠ 0 := by
    exact Nat.ne_of_gt (Module.finrank_pos (R := k) (M := A))
  refine ⟨1, Module.finrank k A, one_ne_zero, hfinrank, ?_⟩
  exact ⟨(matrixOneAlgEquiv (k := k) (A.tensorProduct A.opposite)).trans e⟩

end CSA

namespace BrauerGroup

variable {k : Type u} [Field k]

/-- Definition 11.5.2: the Brauer group `Br(k)` of `k` is the quotient `BrauerGroup k` of finite
central simple `k`-algebras by Brauer equivalence, endowed with multiplication induced by tensor
product and inverse induced by the opposite algebra. -/
@[stacks 074L]
noncomputable instance : One (Br(k)) :=
  ⟨Quotient.mk _ (CSA.unit k)⟩

/-- Multiplication in the Brauer group is induced by tensor product of representatives. -/
noncomputable instance : Mul (Br(k)) :=
  ⟨Quotient.map₂ CSA.tensorProduct
      fun {_ _} h₁ {_ _} h₂ ↦ CSA.brauerEquivalent_tensorProduct h₁ h₂⟩

/-- Inversion in the Brauer group is induced by passage to the opposite algebra. -/
noncomputable instance : Inv (Br(k)) :=
  ⟨Quotient.map CSA.opposite fun _ _ h ↦ CSA.brauerEquivalent_opposite h⟩

/-- The source-facing owner `Br(k)` carries the canonical commutative-group structure described in
Definition 11.5.2. -/
@[stacks 074L]
noncomputable instance : CommGroup (Br(k)) where
  one := 1
  mul := (· * ·)
  inv := Inv.inv
  mul_assoc a b c := by
    refine Quotient.inductionOn₃ a b c fun A B C ↦ ?_
    exact Quotient.sound (CSA.brauerEquivalent_tensorProduct_assoc A B C)
  one_mul a := by
    refine Quotient.inductionOn a fun A ↦ ?_
    exact Quotient.sound (CSA.brauerEquivalent_unit_tensorProduct A)
  mul_one a := by
    refine Quotient.inductionOn a fun A ↦ ?_
    exact Quotient.sound (CSA.brauerEquivalent_tensorProduct_unit A)
  inv_mul_cancel a := by
    refine Quotient.inductionOn a fun A ↦ ?_
    exact Quotient.sound <|
      IsBrauerEquivalent.trans (CSA.brauerEquivalent_tensorProduct_comm A.opposite A)
        (CSA.brauerEquivalent_tensorProduct_opposite A)
  mul_comm a b := by
    refine Quotient.inductionOn₂ a b fun A B ↦ ?_
    exact Quotient.sound (CSA.brauerEquivalent_tensorProduct_comm A B)

@[simp] theorem one_def :
    (1 : Br(k)) = Quotient.mk _ (CSA.unit k) :=
  rfl

@[simp] theorem mk_mul_mk (A B : CSA.{u, max u v} k) :
    (Quotient.mk _ A : Br(k)) * Quotient.mk _ B =
      Quotient.mk _ (A.tensorProduct B) :=
  rfl

@[simp] theorem mk_inv (A : CSA.{u, max u v} k) :
    (Quotient.mk _ A : Br(k))⁻¹ = Quotient.mk _ A.opposite :=
  rfl

end BrauerGroup
