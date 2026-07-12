import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v y

section

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]
variable {N₁ : Type v} [AddCommGroup N₁] [Module R N₁]
variable {N₂ : Type v} [AddCommGroup N₂] [Module R N₂]

namespace LinearMap

private abbrev baseChangePairMap (s : M →ₗ[R] N₁ × N₂) (B : Type y)
    [CommRing B] [Algebra R B] :
    B ⊗[R] M →ₗ[B] (B ⊗[R] N₁) × (B ⊗[R] N₂) :=
  (TensorProduct.prodRight R B B N₁ N₂).toLinearMap ∘ₗ s.baseChange B

/-- A pair-valued linear map identifies its source with a direct sum of submodules of the two
ambient summands. -/
def identifiesWithProdSubmodules (s : M →ₗ[R] N₁ × N₂) : Prop :=
  ∃ P₁ : Submodule R N₁,
    ∃ P₂ : Submodule R N₂,
      Function.Injective s ∧ LinearMap.range s = P₁.prod P₂

/-- After base change along `R → B`, the pair-valued map `s` identifies its source with a direct
sum of submodules of the two ambient base-changed summands. -/
def baseChangeIdentifiesWithProdSubmodules (s : M →ₗ[R] N₁ × N₂) (B : Type y)
    [CommRing B] [Algebra R B] : Prop :=
  (baseChangePairMap s B).identifiesWithProdSubmodules

end LinearMap

end
