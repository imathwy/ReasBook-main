import Mathlib
import StacksProject_2024.Chap10.Definition_10_42_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

namespace Algebra

section

variable {k : Type u} {K : Type v} [Field k] [Field K] [Algebra k K]
variable [Algebra.EssFiniteType k K]

-- Domain-style sampling:
-- * primary domain: finitely generated field extensions, smooth algebras, and fraction fields;
-- * sampled owners: `Algebra.IsSeparableOver`, `Algebra.Smooth.exists_subalgebra_fg`,
--   `Algebra.EssFiniteType.subalgebra`, and `IsFractionRing` for subalgebras obtained from
--   localizations inside a field;
-- * best owner abstraction here: the source-facing pair consisting of a `k`-subalgebra
--   `A : Subalgebra k K` together with the canonical fraction-field condition `IsFractionRing A K`;
--   smoothness of `A` is the extra geometric property, while the inclusion `A →ₐ[k] K` is derived
--   from the owner `A` itself.
--
-- Proof sketch: choose a domain `A` of finite type over `k` whose fraction field is `K`, using
-- that `K / k` is essentially of finite type, and replace it by its image in `K`, viewed as a
-- `k`-subalgebra. By Lemma `10.140.9`, the extension `K / k` is separable exactly when `A` is
-- smooth at the generic point `(0)`. Since smoothness is local on the source, smoothness at `(0)`
-- is equivalent to replacing `A` by a localization `A_g` that is smooth over `k`, and inside the
-- ambient field `K` that localization is again represented by a smooth `k`-subalgebra whose
-- fraction field is `K`.
/-- Lemma 10.158.10: a finitely generated field extension `K / k` is separable in the Stacks
Project sense if and only if `K` is the fraction field of some smooth domain over `k`. In the
canonical owner formulation below, that domain is represented by a smooth `k`-subalgebra of the
ambient field `K` together with the canonical condition that `K` is its fraction field. -/
theorem isSeparableOver_iff_exists_smooth_domain_with_fractionRing :
    IsSeparableOver k K ↔
      ∃ A : Subalgebra k K, Smooth k A ∧ IsFractionRing A K := sorry

end

end Algebra
