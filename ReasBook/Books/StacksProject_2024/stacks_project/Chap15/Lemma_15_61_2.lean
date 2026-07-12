import Mathlib
import StacksProject_2024.Chap15.«15_61_0_1»

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory
open scoped TensorProduct DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

section

variable {A R Aprime : Type u} [CommRing A] [CommRing R] [CommRing Aprime]
variable [Algebra A R] [Algebra A Aprime]

local notation "Rprime" => (Aprime ⊗[A] R)
local notation "DModR" => DerivedCategory (ModuleCat R)
local notation "DModA" => DerivedCategory (ModuleCat A)
local notation "DModAprime" => DerivedCategory (ModuleCat Aprime)
local notation "DModRprime" => DerivedCategory (ModuleCat Rprime)

/- Domain-style sampling for Lemma 15.61.2:
- primary domain: derived tensor base change for commutative algebras;
- sampled owner declarations:
  `derivedTensorBaseChange`,
  `derivedTensorBaseChangeIso`,
  `Functor.leftDerivedNatIso`;
- best owner abstraction: the canonical public owner is the isomorphism
  `derivedTensorBaseChangeIso`, whose hom is the source-facing comparison morphism
  `derivedTensorBaseChange`;
- primitive vs. derived:
  primitive data are the rings `A`, `R`, `A'`, their algebra structures, and
  `K : D(R)`;
  the comparison morphism and its `IsIso` consequence are derived API from the owner isomorphism;
- source/core/bridge triage:
  `source-facing`: the comparison between the two derived base-change constructions at `K`;
  `core/canonical`: `derivedTensorBaseChangeIso`;
  `bridge/view`: the underlying morphism `derivedTensorBaseChange A Aprime K`.

The Tor-independence hypothesis from the source statement is redundant here: the owner comparison
is already the hom of a canonical isomorphism. -/

/- Lemma 15.61.2: the derived base-change comparison is the canonical isomorphism
`derivedTensorBaseChangeIso`. -/
recall derivedTensorBaseChangeIso

end

end CategoryTheory
