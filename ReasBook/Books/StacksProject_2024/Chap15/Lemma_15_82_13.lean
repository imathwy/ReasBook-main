import Mathlib
import StacksProject_2024.Chap15.«15_60_1_1»
import StacksProject_2024.Chap15.Definition_15_83_1
import StacksProject_2024.Chap15.Lemma_15_82_10

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section

variable {R A B : Type u}
variable [CommRing R] [CommRing A] [CommRing B]
variable [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
variable [Algebra.FiniteType R A]
variable [(algebraMap A B).IsPseudoCoherentRingMap]

local notation "DModA" => DerivedCategory (ModuleCat A)

/- Domain-style sampling for Lemma 15.82.13:
- primary domain: relative pseudo-coherence in derived categories under derived scalar extension
  along a pseudo-coherent ring map;
- sampled owner declarations:
  `DerivedCategory.IsMPseudoCoherentRelativeTo`,
  `DerivedCategory.IsPseudoCoherentRelativeTo`,
  `derivedTensorWithAlgebra`,
  `RingHom.IsPseudoCoherentRingMap`;
- best owner abstraction: this file is `source-facing`, while the canonical owners are the
  relative pseudo-coherence predicates on `DerivedCategory (ModuleCat A)` together with the
  derived scalar-extension owner `derivedTensorWithAlgebra`;
- primitive vs. derived:
  primitive data are the finite-type hypothesis on `R → A` and the pseudo-coherent ring-map
  hypothesis on `A → B`;
  the finite-type structure on `R → B` is derived by transitivity and should not remain primitive
  public data.
-/

-- Proof sketch: fix a surjective polynomial presentation of `A` over `R`, adjoin finitely many
-- variables to obtain a polynomial presentation of `B`, and use the pseudo-coherent ring-map
-- hypothesis to choose a finite free resolution of `B` over that intermediate polynomial algebra.
-- Rewrite derived tensor product with `B` as the total complex of tensoring `K` with this
-- resolution, then combine Lemma `15.82.12` with the distinguished-triangle closure of relative
-- `m`-pseudo-coherence from Lemma `15.82.6`.
/-- Lemma 15.82.13 (1): if `R → A` is finite type, `A → B` is a pseudo-coherent ring map, and a
derived `A`-complex `K^•` is `m`-pseudo-coherent relative to `R`, then
`K^• \otimes_A^{\mathbf L} B` is `m`-pseudo-coherent relative to `R`. -/
theorem derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap
    (K : DModA) (m : ℤ) (hK : K.IsMPseudoCoherentRelativeTo R m) :
    by
      letI : Algebra.FiniteType R B :=
        Algebra.FiniteType.trans
          (inferInstance : Algebra.FiniteType R A)
          (inferInstance : Algebra.FiniteType A B)
      exact (K ⊗[A]^L[B]).IsMPseudoCoherentRelativeTo R m := sorry

-- Proof sketch: unfold relative pseudo-coherence as relative `m`-pseudo-coherence for every
-- integer `m`, and apply part `(1)` to each bound.
/-- Lemma 15.82.13 (2): if `R → A` is finite type, `A → B` is a pseudo-coherent ring map, and a
derived `A`-complex `K^•` is pseudo-coherent relative to `R`, then
`K^• \otimes_A^{\mathbf L} B` is pseudo-coherent relative to `R`. -/
theorem derivedTensorWithAlgebra_isPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap
    (K : DModA) (hK : K.IsPseudoCoherentRelativeTo R) :
    by
      letI : Algebra.FiniteType R B :=
        Algebra.FiniteType.trans
          (inferInstance : Algebra.FiniteType R A)
          (inferInstance : Algebra.FiniteType A B)
      exact (K ⊗[A]^L[B]).IsPseudoCoherentRelativeTo R := by
        intro m
        exact
          derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_isPseudoCoherentRingMap
            K m (hK m)

end

end CategoryTheory
