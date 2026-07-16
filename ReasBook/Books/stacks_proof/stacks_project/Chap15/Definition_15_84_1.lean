import Mathlib
import stacks_proof.stacks_project.Chap15.Definition_15_65_1
import stacks_proof.stacks_project.Chap15.Definition_15_67_1

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Definition 15.84.1:
- primary domain: relative perfectness in derived categories of modules over a base algebra;
- sampled owner declarations:
  `DerivedCategory.IsPseudoCoherent`,
  `HasFiniteTorDimension`,
  `DerivedCategory.IsPerfect`,
  `RingHom.IsPerfectRingMap`;
- best owner abstraction: this file is the `source-facing` owner for the relative object
  predicate `K.IsPerfectOver R` on `D(A)`, built from the chapter owners `K.IsPseudoCoherent`
  and finite tor dimension after restricting scalars to the base ring;
- primitive vs. derived:
  primitive data are exactly those two owner predicates;
  derived API is the downstream closure, tensor-product, and base-change theory for
  `K.IsPerfectOver R`;
- source/core/bridge triage:
  `source-facing`: `DerivedCategory.IsPerfectOver`;
  `core/canonical`: `DerivedCategory.IsPseudoCoherent`, `HasFiniteTorDimension`, and the
    canonical derived restriction-of-scalars functor;
  `bridge/view`: regarding an object of `D(A)` as an object of `D(R)` via restriction of scalars.
-/

namespace DerivedCategory

/-- Definition 15.84.1: for a flat ring map of finite presentation `R → A`, an object `K` of
`D(A)` is `R`-perfect, or perfect relative to `R`, if it is pseudo-coherent over `A` and has
finite tor dimension over `R`. -/
@[stacks 0DHS]
def IsPerfectOver (R : Type u) [CommRing R] {A : Type u} [CommRing A] [Algebra R A]
    (K : DerivedCategory (ModuleCat A)) : Prop :=
  K.IsPseudoCoherent ∧
    HasFiniteTorDimension ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K)

end DerivedCategory

end

end CategoryTheory
