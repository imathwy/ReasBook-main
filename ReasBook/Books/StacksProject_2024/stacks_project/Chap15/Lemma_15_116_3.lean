import StacksProject_2024.stacks_project.Chap15.Definition_15_112_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_112_7

-- Declarations for this item will be appended below by the statement pipeline.

open Ideal IsLocalRing
open scoped TensorProduct

universe u v w

open IsExtensionOfDiscreteValuationRings

section

/-
Domain-style sampling for Lemma 15.116.3:
- primary domain: weakly unramified extensions of discrete valuation rings after base change along
  a finite separable totally ramified fraction-field extension;
- sampled owner declarations:
  `IsExtensionOfDiscreteValuationRings`,
  `WeaklyUnramified`,
  `IsTotallyRamifiedWithRespectTo`,
  `integralClosure`;
- best owner abstraction: the chapter owners `IsExtensionOfDiscreteValuationRings`,
  `WeaklyUnramified`, and `IsTotallyRamifiedWithRespectTo`, with the integral closure
  `A1 = integralClosure A K1` as the owner ring for clause `(2)` and the tensor-product rings
  `L1 = L ⊗[K] K1` and `B1 = A1 ⊗[A] B` as the bridge objects for the base-change clauses;
- primitive-vs-derived split: the primitive data for clause `(2)` are the DVR `A`, the finite
  separable totally ramified extension `K1 / K`, and the integral closure `A1`; the additional DVR
  extension `A ⊆ B`, fraction field `L`, and the field/domain/DVR structures on `L1` and `B1` are
  only needed for clauses `(1)`, `(3)`, and `(4)`.

Source/core/bridge triage:
- `source-facing`: the four clauses of Lemma 15.116.3;
- `core/canonical`: `IsExtensionOfDiscreteValuationRings`, `WeaklyUnramified`,
  `IsTotallyRamifiedWithRespectTo`, and `integralClosure`;
- `bridge/view`: the tensor-product rings `L1` and `B1`.
-/

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section IntegralClosure

variable {A : Type u} {K1 : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [Field K1] [Algebra A K1]
variable [Algebra (FractionRing A) K1] [IsScalarTower A (FractionRing A) K1]
variable [FiniteDimensional (FractionRing A) K1]
variable [Algebra.IsSeparable (FractionRing A) K1]
variable [IsTotallyRamifiedWithRespectTo A K1]

local notation "A1" => integralClosure A K1

/-- Lemma 15.116.3 (2): for a finite separable extension `K1 / FractionRing A` totally ramified
with respect to `A`, the integral closure `A1 = integralClosure A K1` is a discrete valuation
ring. -/
instance integralClosure_isDiscreteValuationRing_of_totallyRamified :
    IsDiscreteValuationRing A1 := sorry

end IntegralClosure

section WeaklyUnramifiedBaseChange

variable {A : Type u} {B : Type v} {K1 : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable {L : Type v} [Field L] [Algebra B L] [IsFractionRing B L]
variable [Algebra A L] [Algebra (FractionRing A) L]
variable [IsScalarTower A B L] [IsScalarTower A (FractionRing A) L]
variable [Field K1] [Algebra A K1]
variable [Algebra (FractionRing A) K1] [IsScalarTower A (FractionRing A) K1]
variable [FiniteDimensional (FractionRing A) K1]
variable [Algebra.IsSeparable (FractionRing A) K1]
variable [IsTotallyRamifiedWithRespectTo A K1] [WeaklyUnramified A B]

local notation "K" => FractionRing A
local notation "A1" => integralClosure A K1
local notation "L1" => L ⊗[K] K1
local notation "B1" => A1 ⊗[A] B

-- Proof sketch: a finite separable totally ramified extension of the fraction field of a DVR has
-- trivial residue-field extension, so after tensoring with a weakly unramified extension the
-- tensor product stays local on the generic fiber. Equivalently, the unique prolongation of the
-- valuation from `K` to `K1` forces `L ⊗[K] K1` to have a single factor, hence it is a field.
/-- Lemma 15.116.3 (1): if `A ⊆ B` is a weakly unramified extension of discrete valuation rings
with fraction fields `K ⊆ L`, and `K1 / K` is finite separable and totally ramified with respect
to `A`, then `L1 = L ⊗[K] K1` is a field. -/
instance tensorProduct_fractionField_isField_of_weaklyUnramified_of_totallyRamified :
    IsField L1 := sorry

/-- The base-changed tensor product `B1 = A1 ⊗[A] B` is a domain when `A ⊆ B` is weakly
unramified. -/
instance tensorProduct_integralClosure_isDomain_of_weaklyUnramified_of_totallyRamified :
    IsDomain B1 := sorry

/-- Lemma 15.116.3 (3): if `A ⊆ B` is weakly unramified and `K1 / K` is totally ramified with
respect to `A`, then the base change `B1 = A1 ⊗[A] B` is a discrete valuation ring. -/
instance tensorProduct_integralClosure_isDiscreteValuationRing_of_weaklyUnramified_of_totallyRamified :
    IsDiscreteValuationRing B1 := sorry

/-- The canonical map `A1 → B1` obtained by base-changing `A → B` along `A → A1` is again an
extension of discrete valuation rings when `A ⊆ B` is weakly unramified. -/
instance isExtensionOfDiscreteValuationRings_integralClosure_tensorProduct_of_weaklyUnramified_of_totallyRamified :
    IsExtensionOfDiscreteValuationRings A1 B1 := sorry

-- Proof sketch: after (2) and (3), the extension `A1 ⊆ B1` is an extension of discrete valuation
-- rings by the preceding theorem. Total ramification of `K1 / K` leaves the ramification index
-- of `A ⊆ B` unchanged, so the ramification index remains `1` after passing to `A1 ⊆ B1`.
/-- Lemma 15.116.3 (4): with `A1 = integralClosure A K1` and `B1 = A1 ⊗[A] B`, the base-changed
extension `A1 ⊆ B1` is weakly unramified. -/
theorem weaklyUnramified_tensorProduct_integralClosure_of_totallyRamified :
    WeaklyUnramified A1 B1 := sorry

end WeaklyUnramifiedBaseChange

end
