import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

/- Definition 1.1.28: mathlib's canonical owner for group homomorphisms is `MonoidHom`; in the
group case it is written `G₁ →* G₂`, and the kernel of such a homomorphism is the canonical
subgroup `MonoidHom.ker`. -/
recall MonoidHom (M : Type u) (N : Type v) [MulOne M] [MulOne N] : Type (max u v)

variable {G₁ : Type u} {G₂ : Type v} [Group G₁] [Group G₂]

#check (G₁ →* G₂)
#check (MonoidHom.ker : (G₁ →* G₂) → Subgroup G₁)
