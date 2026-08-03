module

public import Mathlib.GroupTheory.FreeGroup.GeneratorEquiv

public section

noncomputable section

universe u v

variable {ι : Type v} {G : Type u} [Group G]

namespace FreeGroupBasis

/-- The basis of the additive abelianization induced by a chosen free-group basis. -/
noncomputable def abelianizationBasis (b : FreeGroupBasis ι G) :
    Module.Basis ι ℤ (Additive (Abelianization G)) :=
  (FreeAbelianGroup.basis ι).map
    (MulEquiv.toAdditive b.repr.symm.abelianizationCongr).toIntLinearEquiv

/-- The induced abelianization basis consists of the cosets of the free generators. -/
@[simp]
theorem abelianizationBasis_apply (b : FreeGroupBasis ι G) (i : ι) :
    b.abelianizationBasis i = Additive.ofMul (Abelianization.of (b i)) := by
  -- First identify the canonical basis vector without unfolding its ambient additive group.
  have canonicalBasis_apply :
      (FreeAbelianGroup.basis ι) i = FreeAbelianGroup.of i := by
    simp [FreeAbelianGroup.basis]
  -- Evaluate the mapped basis while retaining its inferred integer-module structures.
  rw [abelianizationBasis, Module.Basis.map_apply, canonicalBasis_apply]
  -- The abelianization equivalence sends a generator coset to its image generator coset.
  exact congrArg Additive.ofMul
    (abelianizationCongr_of b.repr.symm (FreeGroup.of i))

end FreeGroupBasis
