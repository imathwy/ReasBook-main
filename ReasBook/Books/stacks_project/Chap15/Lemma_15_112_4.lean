import Mathlib
import stacks_project.Chap15.Definition_15_112_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsExtensionOfDiscreteValuationRings

universe u v

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]

attribute [local instance]
  FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

/- Domain-style sampling:
- primary domain: ramification theory for extensions of discrete valuation rings with purely
  inseparable fraction-field extension;
- sampled owner declarations:
  `FractionRing.liftAlgebra`,
  `FractionRing.isScalarTower_liftAlgebra`,
  `IsExtensionOfDiscreteValuationRings.ramificationIndex`,
  `isPurelyInseparable_iff_pow_mem`;
- best owner abstraction: the source-facing owner remains `ramificationIndex A B`, while the
  induced fraction-field algebra `FractionRing A → FractionRing B` and its scalar-tower
  compatibility with `A → B` are canonical derived infrastructure exported by the DVR-extension
  owner rather than installed locally in this file;
- primitive vs. derived: the primitive public data are the DVR extension owner together with the
  characteristic-`p` and purely inseparable hypotheses on the induced fraction-field extension;
  the fraction-field algebra/scalar-tower instances and the `p`-power conclusion are derived API.

Source/core/bridge triage:
- `source-facing`: the conclusion that the ramification index of `A ⊆ B` is a power of `p`;
- `core/canonical`: `IsExtensionOfDiscreteValuationRings.ramificationIndex`,
  `FractionRing.liftAlgebra`, and
  `isPurelyInseparable_iff_pow_mem`;
- `bridge/view`: direct unfolding of `ramificationIndex`, used only to compare the chapter owner
  with the underlying ideal-theoretic invariant.
-/

-- Proof sketch: write a uniformizer of `A` as a unit times a power of a uniformizer of `B`, then
-- use pure inseparability to find a `p`-power of the target uniformizer lying in `FractionRing A`.
-- Comparing valuations gives an equality `k * e = p ^ n` for some `k` and `n`, forcing the
-- ramification index `e` to be a power of `p`.
/-- Lemma 15.112.4: if `A ⊆ B` is an extension of discrete valuation rings, the induced extension
of fraction fields `FractionRing A ⊆ FractionRing B` has characteristic `p > 0`, and
`FractionRing B` is purely inseparable over `FractionRing A`, then the ramification index of
`A ⊆ B` is a power of `p`. -/
theorem ramificationIndex_eq_pow_of_isPurelyInseparable
    (p : ℕ) [Fact p.Prime] [CharP (FractionRing A) p]
    [IsPurelyInseparable (FractionRing A) (FractionRing B)] :
    ∃ n : ℕ,
      ramificationIndex A B = p ^ n := sorry

end
