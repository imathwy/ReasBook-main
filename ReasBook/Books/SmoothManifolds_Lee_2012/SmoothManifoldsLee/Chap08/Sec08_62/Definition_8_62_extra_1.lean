import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

universe u𝕜 u𝔤 uV

variable {𝕜 : Type u𝕜} [Field 𝕜]
variable {𝔤 : Type u𝔤} [LieRing 𝔤] [LieAlgebra 𝕜 𝔤]
variable {V : Type uV} [AddCommGroup V] [Module 𝕜 V]
variable [FiniteDimensional 𝕜 𝔤] [FiniteDimensional 𝕜 V]
variable [LieRingModule 𝔤 V] [LieModule 𝕜 𝔤 V]

-- Domain sampling pass:
-- * primary domain: finite-dimensional representations of Lie algebras;
-- * core/canonical owners inspected: `LieModule`, `LieModule.toEnd`,
--   `LieModule.IsFaithful`, `LieEquiv.ofInjective`;
-- * layer choice: `core/canonical`, so this file recalls the upstream owner abstraction and its
--   canonical derived maps rather than introducing a local wrapper.

/- Definition 8.62-extra-1: a finite-dimensional representation of a finite-dimensional Lie
algebra `𝔤` over a field `𝕜` on a finite-dimensional `𝕜`-vector space `V` is the canonical
mathlib notion `LieModule 𝕜 𝔤 V`. The corresponding Lie algebra homomorphism `𝔤 → 𝔤𝔩(V)` is
`LieModule.toEnd 𝕜 𝔤 V : 𝔤 →ₗ⁅𝕜⁆ Module.End 𝕜 V`; faithfulness is
`LieModule.IsFaithful 𝕜 𝔤 V`, and an injective such homomorphism identifies `𝔤` with its Lie
subalgebra image via `LieEquiv.ofInjective`. The real case in Lee is the specialization `𝕜 = ℝ`.
-/
recall LieModule
recall LieModule.toEnd
recall LieModule.IsFaithful
#check (LieModule.toEnd 𝕜 𝔤 V).range
#check LieEquiv.ofInjective (LieModule.toEnd 𝕜 𝔤 V)
