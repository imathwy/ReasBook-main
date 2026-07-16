import Mathlib
import StacksProject_2024.stacks_project.Chap15.Definition_15_67_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped TensorProduct

universe u v

namespace Algebra

section

variable {A : Type u} {B : Type v}
variable [CommRing A] [CommRing B] [Algebra A B]
variable [IsNoetherianRing A] [IsNoetherianRing B]
variable [Algebra.FiniteType A B] [Module.Flat A B]

/- Semantic search note: `lean_leansearch` surfaced the canonical smooth algebra owner
`Algebra.Smooth`, and local Chapter 23 precedent in Lemma 23.10.1 uses
`CategoryTheory.ModuleHasFiniteTorDimension` for the tensor-square multiplication hypothesis. -/

/-- Lemma 23.10.2: let `A → B` be a flat finite type ring map of Noetherian rings. If the
multiplication map `B ⊗[A] B → B` is perfect, equivalently if `B` has finite tor dimension over
`B ⊗[A] B`, then `B` is a smooth `A`-algebra. -/
@[stacks 0FCX]
theorem smooth_of_flat_finiteType_of_tensorSquareMultiplication_finiteTorDimension
    (hTor :
      let _ : Algebra (B ⊗[A] B) B :=
        (Algebra.TensorProduct.lmul' A).toAlgebra
      CategoryTheory.ModuleHasFiniteTorDimension (ModuleCat.of (B ⊗[A] B) B)) :
    Algebra.Smooth A B := sorry

end

end Algebra
