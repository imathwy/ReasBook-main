import Mathlib
import StacksProject_2024.Chap20.Definition_20_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory

noncomputable section

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RingedSpace

section

variable {X : RingedSpace.{u}}
variable [MonoidalCategory (DerivedCategory (RingedSpace.Modules X))]

local notation "DMod" => DerivedCategory (RingedSpace.Modules X)

-- Proof sketch: by Lemma `20.49.5`, it is enough to prove that `K ⊗^L L` is pseudo-coherent and
-- locally of finite tor dimension. Lemma `20.47.5 (2)` gives pseudo-coherence of the derived
-- tensor product of pseudo-coherent objects, and Lemma `20.48.7` gives finite tor-amplitude after
-- tensoring; applying Lemma `20.49.5` again yields perfection.
/-- Lemma 20.49.8: let `(X, \mathcal O_X)` be a ringed space. If `K` and `L` are perfect objects
of `D(\mathcal O_X)`, then so is `K \otimes_{\mathcal O_X}^{\mathbf L} L`. -/
theorem tensor_isPerfect_of_isPerfect
    (K L : DMod) (hK : DerivedCategory.IsPerfect K) (hL : DerivedCategory.IsPerfect L) :
    DerivedCategory.IsPerfect (K ⊗ L) := sorry

end

end AlgebraicGeometry.RingedSpace
