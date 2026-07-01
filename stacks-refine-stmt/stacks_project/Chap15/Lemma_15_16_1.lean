import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace Ideal

variable {R : Type u} [CommRing R]

/-- An ideal `J` has flat quotient for `M` if `M / JM` is flat over `R ⧸ J`. -/
abbrev IsFlatQuotient (J : Ideal R) (M : Type v) [AddCommGroup M] [Module R M] : Prop :=
  Module.Flat (R ⧸ J) (M ⧸ (J • ⊤ : Submodule R M))

section

variable {M : Type v} [AddCommGroup M] [Module R M]
variable {I₁ I₂ : Ideal R}

/- Domain triage:
- primary domain: commutative algebra of flatness for quotient modules over quotient rings;
- sampled owner declarations of the same kind:
  `Module.Flat`,
  `Ideal.IsFlatQuotient`,
  `SurjectiveRingPullbackSituation`,
  `surjectiveRingPullbackModuleFiberProduct_flat`;
- best owner abstraction: `Ideal.IsFlatQuotient` is the source-facing owner in this chapter, while
  the canonical upstream owner for the closure argument is the Chapter 15 pullback-flatness
  theorem `surjectiveRingPullbackModuleFiberProduct_flat`;
- primitive data: the ring `R`, the module `M`, and the ideals `I₁`, `I₂`;
- derived API: the closure of `Ideal.IsFlatQuotient` under binary intersections.

Layering:
- `source-facing`: the Stacks lemma about combining two flat quotient thickenings;
- `core/canonical`: `Module.Flat` together with the pullback owner
  `surjectiveRingPullbackModuleFiberProduct_flat`;
- `bridge/view`: this theorem identifies the quotient by `I₁ ⊓ I₂` with the fibre product of the
  two quotient modules over the quotient-ring pullback square.
-/

-- Proof sketch: form the surjective pullback square
-- `R ⧸ (I₁ ⊓ I₂) → R ⧸ I₁`, `R ⧸ (I₁ ⊓ I₂) → R ⧸ I₂`, `R ⧸ I₁ → R ⧸ (I₁ ⊔ I₂)`,
-- `R ⧸ I₂ → R ⧸ (I₁ ⊔ I₂)`. The quotient module `M ⧸ ((I₁ ⊓ I₂) • ⊤)` identifies with the fibre
-- product of `M ⧸ (I₁ • ⊤)` and `M ⧸ (I₂ • ⊤)` over `M ⧸ ((I₁ ⊔ I₂) • ⊤)`, so the Chapter 15
-- pullback-flatness owner `surjectiveRingPullbackModuleFiberProduct_flat` turns the two flat
-- quotient hypotheses into flatness of the quotient by the intersection.
/-- Lemma 15.16.1: the ideals cutting out flat quotients of `M` are closed under binary intersections. -/
theorem IsFlatQuotient.inf
    (hflat₁ : I₁.IsFlatQuotient M)
    (hflat₂ : I₂.IsFlatQuotient M) :
    (I₁ ⊓ I₂).IsFlatQuotient M := sorry

end

end Ideal
