import Mathlib
import LinearRepresentations_Serre_1977.Chap14.Corollary_14_14_4_4
import LinearRepresentations_Serre_1977.Chap15.Exercise_15_15_5_3.SameUniverseModel

open CategoryTheory
open scoped MonoidAlgebra

universe u

namespace Representation

section

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]
variable {W : Type u} [AddCommGroup W] [Module k[G] W]
variable [Module.Finite k[G] W] [Module.Projective k[G] W]

/-- Helper for Exercise 15-15.5-3: a same-universe finite projective `k[G]`-module can be
packaged once as a `FiniteProjectiveGroupAlgebraModule`, so later proofs can consume the compiled
owner instead of rebuilding the full-subcategory term inline. -/
  theorem same_universe_model_finiteProjective_owner :
    ∃ F : FiniteProjectiveGroupAlgebraModule k G,
      Nonempty (F.V ≃ₗ[MonoidAlgebra k G] W) := by
  let Wfg : FGModuleCat (MonoidAlgebra k G) := FGModuleCat.of (MonoidAlgebra k G) W
  let F : FiniteProjectiveGroupAlgebraModule k G := ⟨Wfg, inferInstance⟩
  -- The owner is built from the given module surface, so the underlying module is unchanged.
  exact ⟨F, ⟨LinearEquiv.refl (MonoidAlgebra k G) W⟩⟩

end

end Representation
