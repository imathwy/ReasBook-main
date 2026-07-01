import stacks_project.Chap10.Example_10_162_17
import stacks_project.Chap15.Definition_15_112_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/-
Domain-style sampling for Lemma 15.117.2:
- primary domain: Nagata and `N-2` descent for extensions of discrete valuation rings through
  finite purely inseparable fraction-field tests and faithfully flat finite descent;
- sampled owner declarations in this domain:
  `IsExtensionOfDiscreteValuationRings`,
  `NagataRing`,
  `IsN2Ring`,
  `nagataRing_iff_isN2Ring_of_isDiscreteValuationRing`,
  `IsN2Ring.integralClosure_finite_of_finiteDimensional`,
  `isN2Ring_iff_integralClosure_finite_for_finite_purelyInseparable_extensions`,
  `Module.Finite.of_finite_tensorProduct_of_faithfullyFlat`,
  `reducedTensorBaseChangeIntegralClosureMap`,
  `integralClosure_isDiscreteValuationRing_of_finite_purelyInseparable`;
- best owner abstraction: the source-facing theorem should stay stated for
  `IsExtensionOfDiscreteValuationRings A B`, while the core/canonical companion below should land
  in `IsN2Ring A`; the source-facing Nagata statement is then derived from the DVR equivalence
  `NagataRing A ↔ IsN2Ring A` instead of introducing a parallel local wrapper;
- primitive data: the two discrete valuation rings, their extension structure, the Nagata
  hypothesis on `B`, and the separability of the induced fraction-field extension;
- derived API: finite normalization over the Nagata target, the `N-2` reformulation on DVRs, the
  purely inseparable integral-closure test, the DVR structure on those integral closures, and
  faithful-flat finite descent.

Source/core/bridge triage:
- `source-facing`: the theorem below, which is the textbook Nagata descent statement for DVR
  extensions;
- `core/canonical`: `IsExtensionOfDiscreteValuationRings`, `NagataRing`, `IsN2Ring`, and
  `integralClosure`;
- `bridge/view`: finite normalization over Nagata rings, the Chapter 10 equivalence between
  Nagata and `N-2` for DVRs, and the faithfully flat finite-descent theorem for tensor base
  change.
-/

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]

attribute [local instance]
  FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

namespace IsExtensionOfDiscreteValuationRings

variable [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

-- Proof sketch: by Example `10.162.17 (1)`, a discrete valuation ring is Nagata exactly when it
-- is `N-2`. Let `K1 / FractionRing A` be a finite purely inseparable extension. Convert the
-- Nagata hypothesis on `B` to the canonical owner `[IsN2Ring B]`, so
-- `IsN2Ring.integralClosure_finite_of_finiteDimensional` gives finite normalization over `B`
-- in the generic fiber `FractionRing B ⊗[FractionRing A] K1`, which is a field because a
-- separable extension and a finite purely inseparable extension are linearly disjoint. The
-- reduced tensor-product comparison map from Remark `15.115.1` packages the corresponding
-- base-changed normalization canonically. The integral closure of `A` in `K1` base changes into
-- this finite `B`-algebra, and faithful flatness of the extension of discrete valuation rings `A → B`
-- descends module-finiteness back to `A`. Applying Lemma `10.161.12` again gives that `A` is
-- `N-2`, hence Nagata.
variable (A B) in
/-- Core companion to Lemma 15.117.2: with the canonical `N-2` owner hypothesis on the target
discrete valuation ring, the source discrete valuation ring is also `N-2`. -/
theorem isN2Ring_of_separable_fractionRingExtension
    [IsN2Ring B]
    : IsN2Ring A := by
  sorry

variable (A B) in
/-- Lemma 15.117.2: for an extension `A ⊆ B` of discrete valuation rings, if `B` is a Nagata ring
and the induced extension of fraction fields `FractionRing B / FractionRing A` is separable, then
`A` is a Nagata ring. This is the source-facing reformulation of the preceding canonical
`IsN2Ring` companion using the DVR equivalence `NagataRing A ↔ IsN2Ring A`. -/
theorem nagataRing_of_separable_fractionRingExtension
    [NagataRing B]
    : NagataRing A := by
  haveI : IsN2Ring B := (nagataRing_iff_isN2Ring_of_isDiscreteValuationRing B).mp inferInstance
  have hA : IsN2Ring A := isN2Ring_of_separable_fractionRingExtension A B
  exact
    (nagataRing_iff_isN2Ring_of_isDiscreteValuationRing A).mpr
      hA

end IsExtensionOfDiscreteValuationRings

end
