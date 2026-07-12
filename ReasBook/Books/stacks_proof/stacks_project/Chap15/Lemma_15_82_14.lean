import Mathlib
import StacksProject_2024.Chap15.Lemma_15_82_13

noncomputable section

open CategoryTheory

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A B : Type u}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable [Algebra.FiniteType R A]
variable [(algebraMap A B).IsPseudoCoherentRingMap]

/- Domain-style sampling for Lemma 15.82.14:
- primary domain: relative pseudo-coherence for modules under ordinary scalar extension along a
  flat pseudo-coherent ring map;
- sampled owner declarations:
  `ModuleCat.IsMPseudoCoherentRelativeTo`,
  `ModuleCat.IsPseudoCoherentRelativeTo`,
  `derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap`,
  `RingHom.IsPseudoCoherentRingMap`;
- best owner abstraction: the core/canonical owner is the derived scalar-extension theorem
  `derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap`; this file is
  only the module-level `bridge/view` specialization obtained from a degree-zero complex and the
  flat identification of derived with ordinary scalar extension;
- primitive vs. derived:
  primitive data are the finite-type hypothesis on `R → A`, the pseudo-coherent ring-map owner on
  `A → B`, and the flatness hypothesis on `A → B`;
  the finite-type structure on `R → B` is derived canonically and should not remain ambient public
  data in this bridge file.
-/

-- Proof sketch: regard `M` as the degree-zero object of `D(A)`, apply
-- `derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap`, and use
-- flatness of `A → B` to identify the derived tensor product with ordinary extension of scalars on
-- a module concentrated in degree `0`.
/-- Lemma 15.82.14: if `R → A → B` are finite type ring maps, `A → B` is flat, and `A → B` is
pseudo-coherent, then relative `m`-pseudo-coherence over `R` is preserved by extension of scalars
from `A` to `B`. -/
@[stacks 067C]
theorem isMPseudoCoherentRelativeTo_extendScalars
    (hflat : (algebraMap A B).Flat) (M : ModuleCat A) (m : ℤ)
    (hM : M.IsMPseudoCoherentRelativeTo R m) :
    by
      letI : Algebra.FiniteType R B :=
        Algebra.FiniteType.trans
          (inferInstance : Algebra.FiniteType R A)
          (inferInstance : Algebra.FiniteType A B)
      exact
        ((ModuleCat.extendScalars (algebraMap A B)).obj M).IsMPseudoCoherentRelativeTo R m := sorry

-- Proof sketch: unfold relative pseudo-coherence as relative `m`-pseudo-coherence for every
-- integer `m`, and apply the previous theorem to each bound.
/-- Ordinary scalar extension along a flat pseudo-coherent finite type ring map preserves relative
pseudo-coherent modules over the base ring. -/
theorem isPseudoCoherentRelativeTo_extendScalars
    (hflat : (algebraMap A B).Flat) (M : ModuleCat A)
    (hM : M.IsPseudoCoherentRelativeTo R) :
    by
      letI : Algebra.FiniteType R B :=
        Algebra.FiniteType.trans
          (inferInstance : Algebra.FiniteType R A)
          (inferInstance : Algebra.FiniteType A B)
      exact
        ((ModuleCat.extendScalars (algebraMap A B)).obj M).IsPseudoCoherentRelativeTo R := sorry

end

end CategoryTheory
