import Mathlib
import StacksProject_2024.stacks_project.Chap10.Definition_10_54_1
import StacksProject_2024.stacks_project.Chap15.Definition_15_67_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

namespace Algebra

section

/- Semantic search note: `lean_leansearch` surfaced the canonical smooth-owner `RingHom.Smooth`,
and local precedent for localization conclusions was taken from `Lemma_15_108_3`; the source
parenthetical identifies diagonal perfectness with finite tor dimension of `B` over
`B ⊗[A] B`, so the main hypothesis is stated in that explicit module-theoretic form. -/

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsLocalRing A] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable [Algebra.EssFiniteType A B] [Module.Flat A B]

/-- Lemma 23.10.1: let `A → B` be a local ring homomorphism of Noetherian local rings such that
`B` is flat and essentially of finite type over `A`. If `B` has finite tor dimension over
`B ⊗[A] B` via the tensor-square multiplication map, then `B` is the localization of a smooth
`A`-algebra. -/
@[stacks 0FCW]
theorem exists_smooth_localization_of_perfect_tensorSquareMultiplication
    (hTor :
      let _ : Algebra (B ⊗[A] B) B :=
        (Algebra.TensorProduct.lmul' A).toAlgebra
      CategoryTheory.ModuleHasFiniteTorDimension (ModuleCat.of (B ⊗[A] B) B)) :
    ∃ (C : Type (max u v)) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra C B)
      (_ : IsScalarTower A C B) (M : Submonoid C), Algebra.Smooth A C ∧ IsLocalization M B := sorry

end

end Algebra
