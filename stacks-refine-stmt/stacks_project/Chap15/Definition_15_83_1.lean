import Mathlib
import stacks_project.Chap15.Definition_15_67_1
import stacks_project.Chap15.Definition_15_82_4

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe u

namespace RingHom

variable {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B)

/- Domain-style sampling:
* primary domain: commutative algebra of pseudo-coherent and perfect ring maps;
* sampled owner declarations:
  `RingHom.FiniteType`,
  `ModuleCat.IsPseudoCoherentRelativeTo`,
  `ModuleHasFiniteTorDimension`,
  `RingHom.IsRegularRingMap`;
* best owner abstraction: this file is the `source-facing` owner for predicates on an actual ring
  hom `f : A →+* B`, matching the chapter owner style of `RingHom.IsRegularRingMap`; the
  module-level owners above provide the canonical primitive data;
* primitive vs. derived:
  primitive data are finite type, relative pseudo-coherence of the target ring over the base, and
  finite tor dimension of the target as a base module;
  derived API is any later polynomial-presentation or perfect-module characterization.

Source/core/bridge triage:
* `source-facing`: `RingHom.IsPseudoCoherentRingMap` and `RingHom.IsPerfectRingMap`;
* `core/canonical`: `RingHom.FiniteType`, `ModuleCat.IsPseudoCoherentRelativeTo`, and
  `ModuleHasFiniteTorDimension`;
* `bridge/view`: for `f = algebraMap A B`, the target ring regarded as the canonical module
  objects `ModuleCat.of B B` and `ModuleCat.of A B`.
-/

/-- Definition 15.83.1 (1): a ring map `f : A →+* B` is pseudo-coherent if it is of finite type
and `B`, viewed as a `B`-module, is pseudo-coherent relative to `A`. -/
@[mk_iff isPseudoCoherentRingMap_iff_finiteType_and_isPseudoCoherentRelativeTo]
class IsPseudoCoherentRingMap : Prop where
  /-- A pseudo-coherent ring map is of finite type. -/
  finiteType : f.FiniteType
  /-- The target ring, viewed as a module over itself, is pseudo-coherent relative to the base. -/
  isPseudoCoherentRelativeTo :
    let _ := f.toAlgebra
    let _ : Algebra.FiniteType A B := RingHom.finiteType_algebraMap.mp finiteType
    (ModuleCat.of B B).IsPseudoCoherentRelativeTo A

/-- Definition 15.83.1 (2): a ring map `f : A →+* B` is perfect if it is pseudo-coherent and `B`,
viewed as an `A`-module, has finite tor dimension. -/
@[mk_iff isPerfectRingMap_iff_isPseudoCoherentRingMap_and_hasFiniteTorDimension]
class IsPerfectRingMap : Prop extends IsPseudoCoherentRingMap f where
  /-- The target ring has finite tor dimension as a module over the base ring. -/
  hasFiniteTorDimension :
    let _ := f.toAlgebra
    ModuleHasFiniteTorDimension (ModuleCat.of A B)

attribute [instance] IsPseudoCoherentRingMap.isPseudoCoherentRelativeTo
attribute [instance] IsPerfectRingMap.hasFiniteTorDimension

section

variable (A : Type u) [CommRing A]

/-- The identity map of a commutative ring is pseudo-coherent. -/
instance : (RingHom.id A).IsPseudoCoherentRingMap where
  finiteType := RingHom.FiniteType.id A
  isPseudoCoherentRelativeTo := by
    sorry

/-- The identity map of a commutative ring is perfect. -/
instance : (RingHom.id A).IsPerfectRingMap where
  toIsPseudoCoherentRingMap := inferInstance
  hasFiniteTorDimension := by
    sorry

end

end RingHom

namespace Algebra

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable [(algebraMap A B).IsPseudoCoherentRingMap]

instance finiteType_of_isPseudoCoherentRingMap : Algebra.FiniteType A B := by
  exact
    RingHom.finiteType_algebraMap.mp
      (inferInstance : (algebraMap A B).IsPseudoCoherentRingMap).finiteType

attribute [instance 100] finiteType_of_isPseudoCoherentRingMap

end

end Algebra
