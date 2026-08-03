module

import Mathlib.GroupTheory.Abelianization.Defs

/-
Lemma 69.3. For a group `G`, the commutator subgroup `commutator G` is normal and
the quotient `Abelianization G = G ⧸ commutator G` is abelian. Every homomorphism
from `G` to a commutative group kills `commutator G` and hence factors through the
quotient map `Abelianization.of : G →* Abelianization G`. Mathlib's canonical lift
also records the uniqueness of this factorization.
-/
#check instNormalCommutator
#check Abelianization
#check Abelianization.commGroup
#check Abelianization.of
#check Abelianization.ker_of
#check Abelianization.commutator_subset_ker
#check Abelianization.lift
#check Abelianization.lift_apply_of
#check Abelianization.lift_unique
