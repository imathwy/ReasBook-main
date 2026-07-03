import Mathlib
import StacksProject_2024.Chap15.Definition_15_61_1
import StacksProject_2024.Chap15.Lemma_15_60_1
import StacksProject_2024.Chap15.Lemma_15_82_10

noncomputable section

open CategoryTheory
open scoped DerivedTensorWithAlgebra TensorProduct

universe u

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Algebra.TensorProduct.leftAlgebra
attribute [local instance] Algebra.TensorProduct.rightAlgebra

namespace CategoryTheory

section

variable {R A R' : Type u} [CommRing R] [CommRing A] [CommRing R']
variable [Algebra R A] [Algebra R R']
variable [Algebra.FiniteType R A]

local notation "Aprime" => A ⊗[R] R'
local notation "DModA" => DerivedCategory (ModuleCat A)

/-- The base-changed algebra `A ⊗[R] R'` is finite type over the new base ring `R'`. -/
local instance instFiniteTypeAprime : Algebra.FiniteType R' Aprime :=
  Algebra.FiniteType.equiv
    (inferInstance : Algebra.FiniteType R' (R' ⊗[R] A))
    (Algebra.TensorProduct.commRight R R' A)

-- Proof sketch: for each surjective polynomial presentation `P → A`, base change to the
-- surjective presentation `P ⊗[R] R' → A ⊗[R] R'`, use Lemma `15.61.2` to identify the derived
-- base change of the restricted complex with restriction of the base-changed complex to
-- `P ⊗[R] R'`, then apply Lemma `15.65.12` over the polynomial ring over `R'`.
/-- Lemma 15.82.12 (1): if `K^•` is `m`-pseudo-coherent relative to `R` and `A` and `R'` are Tor
independent over `R`, then the derived base change
`K^• \otimes_A^{\mathbf L} (A ⊗[R] R')` is `m`-pseudo-coherent relative to `R'`. -/
theorem derivedTensorWithAlgebra_isMPseudoCoherentRelativeTo_of_torIndependent
    (K : DModA) (m : ℤ) (hTor : IsTorIndependent R A R')
    (hK : K.IsMPseudoCoherentRelativeTo R m) :
    (K ⊗[A]^L[Aprime]).IsMPseudoCoherentRelativeTo R' m :=
    sorry

-- Proof sketch: apply part `(1)` presentationwise for every integer `m`, or equivalently replace
-- Lemma `15.65.12` by its pseudo-coherent variant after the same Tor-independent base-change
-- comparison from Lemma `15.61.2`.
/-- Lemma 15.82.12 (2): if `K^•` is pseudo-coherent relative to `R` and `A` and `R'` are Tor
independent over `R`, then the derived base change
`K^• \otimes_A^{\mathbf L} (A ⊗[R] R')` is pseudo-coherent relative to `R'`. -/
theorem derivedTensorWithAlgebra_isPseudoCoherentRelativeTo_of_torIndependent
    (K : DModA) (hTor : IsTorIndependent R A R')
    (hK : K.IsPseudoCoherentRelativeTo R) :
    (K ⊗[A]^L[Aprime]).IsPseudoCoherentRelativeTo R' :=
    sorry

end

end CategoryTheory
