import Mathlib
import StacksProject_2024.Chap20.Definition_20_49_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry.RingedSpace

variable {X : RingedSpace.{u}}

local notation "DModX" => DerivedCategory (RingedSpace.Modules X)

-- Proof sketch: apply Lemma `20.49.5` to rewrite perfection of `K ⊞ L` as pseudo-coherence plus
-- local finite tor dimension, then use Lemmas `20.47.6 (3)` and `20.48.8 (1)` to descend these
-- two properties to `K`, and finally reassemble them with Lemma `20.49.5`.
/-- Lemma 20.49.9 (1): if `K ⊞ L` is a perfect object of `D(\mathcal O_X)`, then `K` is
perfect. -/
theorem isPerfect_left_of_biprod
    (K L : DModX) (hKL : DerivedCategory.IsPerfect (K ⊞ L)) :
    DerivedCategory.IsPerfect K := sorry

-- Proof sketch: as in part `(1)`, use Lemma `20.49.5` to pass to pseudo-coherence and local
-- finite tor dimension, then apply Lemmas `20.47.6 (4)` and `20.48.8 (2)` to the right summand
-- and conclude again via Lemma `20.49.5`.
/-- Lemma 20.49.9 (2): if `K ⊞ L` is a perfect object of `D(\mathcal O_X)`, then `L` is
perfect. -/
theorem isPerfect_right_of_biprod
    (K L : DModX) (hKL : DerivedCategory.IsPerfect (K ⊞ L)) :
    DerivedCategory.IsPerfect L := sorry

end AlgebraicGeometry.RingedSpace
