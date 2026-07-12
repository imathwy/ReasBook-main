import Mathlib.Algebra.BrauerGroup.Defs
import Mathlib.Algebra.Algebra.Equiv
import StacksProject_2024.Chap11.Lemma_11_4_8

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

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

variable {k}

/-- Brauer equivalence is compatible with passage to opposite algebras. -/
theorem brauerEquivalent_opposite {A B : CSA.{u, v} k} (h : IsBrauerEquivalent A B) :
    IsBrauerEquivalent A.opposite B.opposite := by
  sorry

/-- Brauer equivalence is compatible with tensor product on representatives. -/
theorem brauerEquivalent_tensorProduct {A A' B B' : CSA.{u, v} k}
    (hAA' : IsBrauerEquivalent A A') (hBB' : IsBrauerEquivalent B B') :
    IsBrauerEquivalent (A.tensorProduct B) (A'.tensorProduct B') := by
  sorry

/-- Tensor product on representatives induces the associative law in the Brauer group. -/
theorem brauerEquivalent_tensorProduct_assoc (A B C : CSA.{u, v} k) :
    IsBrauerEquivalent ((A.tensorProduct B).tensorProduct C) (A.tensorProduct (B.tensorProduct C)) :=
  by
  sorry

/-- Tensor product on representatives induces the commutative law in the Brauer group. -/
theorem brauerEquivalent_tensorProduct_comm (A B : CSA.{u, v} k) :
    IsBrauerEquivalent (A.tensorProduct B) (B.tensorProduct A) := by
  sorry

/-- Tensoring with the canonical neutral representative leaves a Brauer class unchanged. -/
theorem brauerEquivalent_tensorProduct_unit (A : CSA.{u, max u v} k) :
    IsBrauerEquivalent (A.tensorProduct (unit k)) A := by
  sorry

/-- The canonical neutral representative is a left unit for tensor product on Brauer classes. -/
theorem brauerEquivalent_unit_tensorProduct (A : CSA.{u, max u v} k) :
    IsBrauerEquivalent ((unit k).tensorProduct A) A := by
  sorry

/-- The opposite algebra represents the inverse Brauer class. -/
theorem brauerEquivalent_tensorProduct_opposite (A : CSA.{u, max u v} k) :
    IsBrauerEquivalent (A.tensorProduct A.opposite) (unit k) := by
  sorry

end CSA

namespace BrauerGroup

variable {k : Type u} [Field k]

/-- Definition 11.5.2: the Brauer group `Br(k)` of `k` is the quotient `BrauerGroup k` of finite
central simple `k`-algebras by Brauer equivalence, endowed with multiplication induced by tensor
product and inverse induced by the opposite algebra. -/
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
