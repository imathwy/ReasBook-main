import Mathlib
import StacksProject_2024.Chap15.«15_60_1_1»
import StacksProject_2024.Chap15.Lemma_15_82_10

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R : Type u} {A : Type v} [CommRing R] [CommRing A]
variable (f : R) [Algebra R A] [Algebra (Localization.Away f) A]
variable [IsScalarTower R (Localization.Away f) A]
variable [Algebra.FiniteType (Localization.Away f) A]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.82.11:
- primary domain: relative pseudo-coherence in `D(A)` under localization of the target algebra;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`,
  `derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap`,
  `derivedTensorWithAlgebra_isPseudoCoherentRelativeTo_of_torIndependent`;
- best owner abstraction: the chapter owner is the derived-category predicate
  `DerivedCategory.IsMPseudoCoherentRelativeTo` / `IsPseudoCoherentRelativeTo`, with the ambient
  finite-type algebra inferred from the derived object;
- primitive vs. derived:
  primitive data are the localized derived object `K ⊗[A]^L[Localization.Away g]` and the
  finite-type descent from `R_f → A` to `R → A`;
  derived API is the relative pseudo-coherence statement for that localized object;
- source/core/bridge triage:
  `source-facing`: Lemma `15.82.11` itself;
  `core/canonical`: the derived-category relative pseudo-coherence owners;
  `bridge/view`: the finite-type descent `R_f → A` to `R → A`, after which the localized target
    uses the canonical finite-type localization instance.
- layer: source-facing statement using the canonical owner, with the localized target handled by
  the canonical localization API rather than a parallel local finite-type bridge.
-/

include f in
private theorem finiteType_base_over_base : Algebra.FiniteType R A :=
  Algebra.FiniteType.trans
    (inferInstance : Algebra.FiniteType R (Localization.Away f))
    (inferInstance : Algebra.FiniteType (Localization.Away f) A)

-- Proof sketch: first replace each surjective polynomial presentation over `Localization.Away f`
-- by one over `R` with one extra variable inverting `f`, which shows `K` is already
-- `m`-pseudo-coherent relative to `R`. Then apply derived scalar extension along `A → A_g`, and
-- use that `A_g` is finite type over `R`.
/-- Lemma 15.82.11: if `R_f → A` is finite type and a derived `A`-complex `K` is
`m`-pseudo-coherent relative to `Localization.Away f`, then its localization
`K ⊗_A A_g` is `m`-pseudo-coherent relative to `R`. -/
theorem isMPseudoCoherentRelativeTo_localizationAway_from_localizedBase
    (g : A) (K : DModA) (m : ℤ)
    (hK : K.IsMPseudoCoherentRelativeTo (Localization.Away f) m) :
    by
      letI : Algebra.FiniteType R (Localization.Away g) :=
        Algebra.FiniteType.trans
          (finiteType_base_over_base f)
          (inferInstance : Algebra.FiniteType A (Localization.Away g))
      exact (K ⊗[A]^L[Localization.Away g]).IsMPseudoCoherentRelativeTo R m := sorry

-- Proof sketch: pseudo-coherence is relative `m`-pseudo-coherence for all integers `m`, so apply
-- the preceding theorem to each degree bound after unfolding the hypothesis.
/-- Localization away from `g` carries pseudo-coherent derived `A`-complexes relative to
`Localization.Away f` to pseudo-coherent complexes relative to `R`. -/
theorem isPseudoCoherentRelativeTo_localizationAway_from_localizedBase
    (g : A) (K : DModA)
    (hK : K.IsPseudoCoherentRelativeTo (Localization.Away f)) :
    by
      letI : Algebra.FiniteType R (Localization.Away g) :=
        Algebra.FiniteType.trans
          (finiteType_base_over_base f)
          (inferInstance : Algebra.FiniteType A (Localization.Away g))
      exact (K ⊗[A]^L[Localization.Away g]).IsPseudoCoherentRelativeTo R := sorry

end

end CategoryTheory
