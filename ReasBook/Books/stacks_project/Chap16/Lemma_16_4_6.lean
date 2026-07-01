import Mathlib
import stacks_project.Chap10.Definition_10_42_1
import stacks_project.Chap10.Lemma_10_147_5
import stacks_project.Chap15.Definition_15_112_1
import stacks_project.Chap16.Situation_16_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open IsLocalRing

universe u

namespace Algebra

section

attribute [local instance]
  FractionRing.liftAlgebra
  FractionRing.isScalarTower_liftAlgebra

variable {R : Type u} {Λ : Type u}
variable [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
variable [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ]
variable [Algebra R Λ] [_root_.IsExtensionOfDiscreteValuationRings R Λ]

-- Proof sketch: by Lemma `10.127.4`, it is enough to factor every finite-presentation
-- `R`-algebra map `A → Λ` through a smooth `R`-algebra. Replace `A` by its image in `Λ` so that
-- `A` is a domain inside `FractionRing Λ`; the assumed separability of `FractionRing Λ` over
-- `FractionRing R` and Lemma `10.140.9` make `R → A` smooth at the generic point. Lemma `16.4.5`
-- then yields, after finitely many Néron blowups, a stage smooth at the center over the closed
-- point, and localizing away from that center gives the required smooth factorization through
-- `Λ`.
/-- Lemma 16.4.6: let `R ⊂ Λ` be an extension of discrete valuation rings with ramification index
`1`. If the induced extension of residue fields is separable and the induced extension of
fraction fields is separable in the Stacks Project sense, then `Λ` is a filtered colimit of
smooth `R`-algebras. -/
theorem isFilteredColimitOfSmooth_of_ramificationIndexOne_dvrExtension
    (hweak : _root_.IsExtensionOfDiscreteValuationRings.WeaklyUnramified R Λ)
    [Algebra.IsSeparable (ResidueField R) (ResidueField Λ)]
    [IsSeparableOver (FractionRing R) (FractionRing Λ)] :
    (algebraMap R Λ).IsFilteredColimitOfSmooth := sorry

end

end Algebra
