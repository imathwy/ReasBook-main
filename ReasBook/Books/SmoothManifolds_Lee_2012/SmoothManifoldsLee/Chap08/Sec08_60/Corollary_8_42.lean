import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped Manifold

universe u

-- Domain sampling pass:
-- * source-facing layer: identify `Lie(GL(V))` with `𝔤𝔩(V)` for a
--   finite-dimensional real vector space `V`;
-- * core/canonical owners: `GroupLieAlgebra` for `Lie(GL(V))`,
--   `Module.End.toContinuousLinearMap V` for the finite-dimensional comparison
--   `Module.End ℝ V ≃ₐ[ℝ] (V →L[ℝ] V)`, and `AlgEquiv.toLieEquiv`
--   for passing to Lie algebras;
-- * chapter owner already using this bridge: `general_linear_group_lie_equiv_end` in
--   `Proposition_8_41.lean`, specialized there to the coordinate model `Fin n → ℝ`;
-- * bridge/view here: no new owner is needed, since the corollary is exactly the general-space
--   instance of the canonical Lie equivalence
--   `(Module.End.toContinuousLinearMap V).symm.toLieEquiv`.

section

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

local instance :
    LieGroup (𝓘(ℝ, V →L[ℝ] V)) (minSmoothness ℝ 3) (V →L[ℝ] V)ˣ := inferInstance

/- Corollary 8.42: for a finite-dimensional real vector space `V`, the Lie algebra of `GL(V)`
is canonically identified with `𝔤𝔩(V) = Module.End ℝ V` by the finite-dimensional comparison
between continuous and algebraic endomorphisms. This is the direct canonical bridge below, so
the corollary does not introduce a second owner declaration parallel to Proposition 8.41. -/
#check
  (show
      GroupLieAlgebra (𝓘(ℝ, V →L[ℝ] V)) ((V →L[ℝ] V)ˣ) ≃ₗ⁅ℝ⁆
        Module.End ℝ V from
    (Module.End.toContinuousLinearMap V).symm.toLieEquiv)

end
