module

import Mathlib.Algebra.Group.Subgroup.Ker

universe u v

/- Definition 52.2. For groups `G` and `G'`, a homomorphism `f : G →* G'`
preserves multiplication and therefore preserves the identity and inverses. Its kernel and image
(`f.range` in mathlib) are subgroups. It is a monomorphism exactly when it is injective,
equivalently when `f.ker = ⊥`;
it is an epimorphism exactly when it is surjective, equivalently when `f.range = ⊤`; and a
bijective homomorphism determines a multiplicative equivalence `G ≃* G'`. -/

variable {G : Type u} {G' : Type v} [Group G] [Group G']

#check (G →* G')

variable (f : G →* G')

#check f.map_mul
#check f.map_one
#check f.map_inv
#check f.ker
#check fun x : G ↦ (f.mem_ker : x ∈ f.ker ↔ f x = 1)
#check f.range
#check fun y : G' ↦ (f.mem_range : y ∈ f.range ↔ ∃ x, f x = y)
#check f.ker_eq_bot_iff
#check f.range_eq_top
#check MulEquiv.ofBijective f
