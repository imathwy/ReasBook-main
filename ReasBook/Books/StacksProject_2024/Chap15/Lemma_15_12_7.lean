import Mathlib
import StacksProject_2024.Chap10.Definition_10_17_1
import StacksProject_2024.Chap15.Lemma_15_12_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open PrimeSpectrum
open RingPairCat
open scoped PrimeSpectrum
open scoped TensorProduct

universe u

noncomputable section

section

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
variable (I : Ideal A) (J : Ideal B)

/- Domain-style sampling for Lemma 15.12.7:
- primary domain: pair henselization and its canonical base-change comparison map along a morphism
  of ring pairs;
- sampled owner declarations:
  `RingPairCat.henselianPairInclusion_isRightAdjoint`,
  `RingPairCat.henselizationRingMap`,
  `RingPairCat.toHenselization_naturality`,
  `RingPairCat.pairOfIdealMap`;
- owner abstraction: the core owner is the pair-henselization adjunction for
  `henselianPairInclusion`, already supplied by Lemma `15.12.1`;
- primitive data: a map of pairs `(A, I) → (B, J)` and the chosen henselization rings attached to
  that adjunction;
- derived API: the induced map on henselization rings, the tensor-product comparison map, and the
  bijectivity/algebra-equivalence statements.

Source/core/bridge triage:
- `source-facing`: the canonical comparison map `A^h ⊗[A] B → B^h` and its bijectivity under the
  hypotheses of Lemma 15.12.7;
- `core/canonical`: `henselianPairInclusion` together with its chosen left adjoint from
  `henselianPairInclusion_isRightAdjoint`;
- `bridge/view`: the tensor-product comparison map derived from the source pair morphism and the
  adjunction unit naturality. -/

local instance : henselianPairInclusion.IsRightAdjoint :=
  henselianPairInclusion_isRightAdjoint

/-- The henselization ring of `(B, J)` inherits its `A`-algebra structure by composition with the
map `A → B`. -/
instance pairOfIdeal_henselizationRing_comp_algebra :
    Algebra A (henselizationRing (pairOfIdeal J)) :=
  (RingHom.comp (toHenselization (pairOfIdeal J)) (algebraMap A B)).toAlgebra

/-- The composed `A`- and `B`-algebra structures on the henselization ring of `(B, J)` form a
scalar tower. -/
instance pairOfIdeal_henselizationRing_isScalarTower :
    IsScalarTower A B (henselizationRing (pairOfIdeal J)) := sorry

-- Proof sketch: apply naturality of the adjunction unit for pair henselization to the morphism
-- `(A, I) → (B, J)`; on underlying rings this says the induced henselization map commutes with
-- the original `A`-algebra maps.
/-- The induced map on henselization rings is compatible with the `A`-algebra structures coming
from the original map `A → B`. -/
lemma henselizationRingMap_commutes (hIJ : I ≤ Ideal.comap (algebraMap A B) J) (a : A) :
    henselizationRingMap (pairOfIdealMap I J hIJ)
        (algebraMap A (henselizationRing (pairOfIdeal I)) a) =
      algebraMap A (henselizationRing (pairOfIdeal J)) a := sorry

/-- The comparison map `A^h ⊗[A] B → B^h` induced by the map of pairs `(A, I) → (B, J)`. -/
abbrev henselizationBaseChangeComparison (hIJ : I ≤ Ideal.comap (algebraMap A B) J) :
    (henselizationRing (pairOfIdeal I) ⊗[A] B) →ₐ[A] henselizationRing (pairOfIdeal J) :=
  Algebra.TensorProduct.productMap
    { toRingHom := henselizationRingMap (pairOfIdealMap I J hIJ)
      commutes' := henselizationRingMap_commutes I J hIJ }
    ((Algebra.ofId B (henselizationRing (pairOfIdeal J))).restrictScalars A)

-- Proof sketch: use Lemma `15.12.6` to replace `J` by `IB`, then apply Lemma `15.11.8` to see
-- that `(A^h ⊗[A] B, I^h (A^h ⊗[A] B))` is henselian. The universal property of the henselization
-- of `(B, J)` yields a map in the opposite direction, and the two comparison maps are inverse by
-- uniqueness in the henselization adjunction.
/-- Lemma 15.12.7: for a map of pairs `(A, I) → (B, J)` with `V(J) = V(IB)` and integral ring map
`A → B`, the canonical comparison map `A^h ⊗[A] B → B^h` on chosen pair-henselization rings is
bijective. -/
theorem henselizationBaseChangeComparison_bijective_of_isIntegral
    (hIJ : I ≤ Ideal.comap (algebraMap A B) J)
    (hV : V((J : Set B)) = V((Ideal.map (algebraMap A B) I : Set B)))
    [Algebra.IsIntegral A B] :
    Function.Bijective (henselizationBaseChangeComparison I J hIJ) := sorry

/-- The canonical algebra equivalence induced by Lemma 15.12.7. -/
noncomputable def henselizationBaseChangeAlgEquiv_of_isIntegral
    (hIJ : I ≤ Ideal.comap (algebraMap A B) J)
    (hV : V((J : Set B)) = V((Ideal.map (algebraMap A B) I : Set B)))
    [Algebra.IsIntegral A B] :
    (henselizationRing (pairOfIdeal I) ⊗[A] B) ≃ₐ[A] henselizationRing (pairOfIdeal J) :=
  AlgEquiv.ofBijective (henselizationBaseChangeComparison I J hIJ)
    (henselizationBaseChangeComparison_bijective_of_isIntegral I J hIJ hV)

/-- The algebra equivalence of Lemma 15.12.7 is the canonical comparison map equipped with its
inverse. -/
theorem henselizationBaseChangeAlgEquiv_of_isIntegral_toAlgHom
    (hIJ : I ≤ Ideal.comap (algebraMap A B) J)
    (hV : V((J : Set B)) = V((Ideal.map (algebraMap A B) I : Set B)))
    [Algebra.IsIntegral A B] :
    (henselizationBaseChangeAlgEquiv_of_isIntegral I J hIJ hV).toAlgHom =
      henselizationBaseChangeComparison I J hIJ := rfl

end
