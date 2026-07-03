import Mathlib
import StacksProject_2024.Chap15.Definition_15_37_3
import StacksProject_2024.Chap15.Remark_15_115_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing
open RingHom
open scoped TensorProduct

universe u v w x y

section

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable {A : Type u} {B : Type v} {K : Type w} {L : Type x} {K1 : Type y}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K] [Algebra A K] [IsFractionRing A K]
variable [Field L] [Algebra A L] [Algebra B L] [Algebra K L]
variable [IsScalarTower A B L] [IsScalarTower A K L] [IsFractionRing B L]
variable [Field K1] [Algebra A K1] [Algebra K K1] [IsScalarTower A K K1]
variable [FiniteDimensional K K1]

local notation "A1" => integralClosure A K1
local notation "L1" => (L ⊗[K] K1) ⧸ nilradical (L ⊗[K] K1)
local notation "B1" => integralClosure B L1

local instance : CommRing L1 :=
  Ideal.Quotient.commRing _

/- Domain-style sampling:
- primary domain: reduced tensor-product base change for extensions of discrete valuation rings,
  together with formal smoothness on the localized branches;
- sampled owner declarations:
  `reducedTensorBaseChangeIntegralClosureMap`,
  `tensorBaseChangeToReducedTensorBaseChangeIntegralClosure`,
  `isExtensionOfDiscreteValuationRings_localizationBranch`,
  `RingHom.formally_smooth_for_adic_baseChange`;
- best owner abstraction: the canonical owner is the reduced tensor-product integral closure
  `B₁ = integralClosure B ((L ⊗[K] K₁)_red)` from Remark `15.115.1`, with the tensor product
  `A₁ ⊗[A] B` only as a source-facing bridge/view;
- primitive vs. derived: the primitive data are the DVR extension `A ⊂ B`, fraction fields
  `K ⊂ L`, and the finite extension `K₁ / K`; the comparison map
  `A₁ ⊗[A] B → B₁` and the formal smoothness of localized branches are derived API.

Source/core/bridge triage:
- `source-facing`: the localized formally smooth branch map, using the tensor-product
  identification from Remark `15.115.1` as the bridge;
- `core/canonical`: `reducedTensorBaseChangeIntegralClosureMap`,
  `tensorBaseChangeIntegralClosureEquivOfFormallySmoothForAdic`, and
  `RingHom.formally_smooth_for_adic`;
- `bridge/view`: the tensor-product presentation `A₁ ⊗[A] B` of the canonical owner `B₁`.
-/

-- Proof sketch: transport the formal smoothness of the base-changed tensor product
-- `A₁ → A₁ ⊗[A] B` across the identification
-- `tensorBaseChangeIntegralClosureEquivOfFormallySmoothForAdic` from Remark `15.115.1`, then
-- localize at a maximal ideal `m` of `A₁` and a maximal ideal `n` of `B₁` lying over `m`.
-- Formal smoothness for the maximal-ideal adic topology is preserved on these localized branches.
/-- Lemma 15.115.3: let `A → B` be an extension of discrete valuation rings, let `K` and `L` be
the fraction fields of `A` and `B`, and let `K₁ / K` be a finite extension. Writing
`A₁ = integralClosure A K₁` and `B₁ = integralClosure B ((L ⊗[K] K₁)_red)`, every localized branch
`(A₁)_m → (B₁)_n` with `m` a maximal ideal of `A₁` and `n` a maximal ideal of `B₁` lying over
`m` is formally smooth for the maximal-ideal-adic topology on `(B₁)_n`. -/
theorem formallySmoothForAdic_localization_baseChange_integralClosure
    (hfs : (algebraMap A B).formally_smooth_for_adic (maximalIdeal B))
    (m : Ideal A1) [m.IsMaximal]
    (n : Ideal B1) [n.IsMaximal] [n.LiesOver m] :
    (Localization.localRingHom m n (algebraMap A1 B1) (n.over_def m)).formally_smooth_for_adic
      (maximalIdeal (Localization.AtPrime n)) := by
  sorry

end
