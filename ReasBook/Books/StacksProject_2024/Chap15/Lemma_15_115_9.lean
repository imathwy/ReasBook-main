import Mathlib
import StacksProject_2024.Chap15.Definition_15_112_1
import StacksProject_2024.Chap15.Definition_15_112_7

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v w

section

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {A : Type u} {B : Type v} {K1 : Type w}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
variable [Algebra A B] [IsExtensionOfDiscreteValuationRings A B]
variable [Field K1] [Algebra A K1] [Algebra (FractionRing A) K1]
variable [IsScalarTower A (FractionRing A) K1]
variable [FiniteDimensional (FractionRing A) K1]
variable [Algebra.IsSeparable (FractionRing A) K1]

local notation "K" => FractionRing A
local notation "L" => FractionRing B
local notation "KL" => K1 ⊗[K] L

-- Proof sketch: `K1 / K` is finite separable, so `KL = K1 ⊗[K] L` is a finite étale `L`-algebra
-- and hence a finite product of finite separable field extensions of `L`. Let `A1` be the
-- integral closure of `A` in `K1`. Unramifiedness of `K1 / K` identifies `A1` as finite étale
-- over `A`; base change to `B` preserves finite étaleness, so the integral closure of `B` in each
-- factor of `KL` is étale over `B`, which is exactly unramifiedness with respect to `B`.
/-- Lemma 15.115.9: if `A ⊂ B` is an extension of discrete valuation rings and
`K1 / FractionRing A` is a finite separable extension that is unramified with respect to `A`,
then `K1 ⊗[FractionRing A] FractionRing B` is a finite product of fields, and each field factor
is unramified with respect to `B`. -/
theorem exists_fractionRingTensorProduct_decomposition_with_unramifiedFactors
    (hK1 : IsUnramifiedWithRespectTo A K1) :
    ∃ (ι : Type u) (_ : Fintype ι) (L1 : ι → Type (max u v w))
      (_ : ∀ i, Field (L1 i))
      (_ : ∀ i, Algebra B (L1 i))
      (_ : ∀ i, Algebra L (L1 i))
      (_ : ∀ i, IsScalarTower B L (L1 i))
      (_ : ∀ i, FiniteDimensional L (L1 i))
      (_ : ∀ i, Algebra.IsSeparable L (L1 i)),
      Nonempty (KL ≃ₐ[L] ∀ i, L1 i) ∧
        ∀ i, IsUnramifiedWithRespectTo B (L1 i) := sorry

-- Proof sketch: write `KL = K1 ⊗[K] L` as a finite product of fields as above. By Lemma
-- `15.115.6`, after enlarging `K1` if necessary one reduces to the Kummer description from Lemma
-- `15.115.7`; then Abhyankar's lemma gives tame ramification for the intermediate factors over
-- `B`, and Lemma `15.115.5` passes tameness from the localized branches back to each global field
-- factor of `KL`.
/-- If `K1 / FractionRing A` is tamely ramified with respect to `A`, then the field factors of
`K1 ⊗[FractionRing A] FractionRing B` can be chosen tamely ramified with respect to `B`. -/
theorem exists_fractionRingTensorProduct_decomposition_with_tamelyRamifiedFactors
    (hK1 : IsTamelyRamifiedWithRespectTo A K1) :
    ∃ (ι : Type u) (_ : Fintype ι) (L1 : ι → Type (max u v w))
      (_ : ∀ i, Field (L1 i))
      (_ : ∀ i, Algebra B (L1 i))
      (_ : ∀ i, Algebra L (L1 i))
      (_ : ∀ i, IsScalarTower B L (L1 i))
      (_ : ∀ i, FiniteDimensional L (L1 i))
      (_ : ∀ i, Algebra.IsSeparable L (L1 i)),
      Nonempty (KL ≃ₐ[L] ∀ i, L1 i) ∧
        ∀ i, IsTamelyRamifiedWithRespectTo B (L1 i) := sorry

end
