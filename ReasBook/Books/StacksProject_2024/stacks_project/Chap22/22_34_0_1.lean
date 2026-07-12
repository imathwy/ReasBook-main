import StacksProject_2024.Chap13.Definition_13_14_10

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open CategoryTheory

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

section

variable {ModdgB : Type u₁} {ModdgC : Type u₂}
variable [Category.{v₁} ModdgB] [Category.{v₂} ModdgC]
variable (QisB : MorphismProperty ModdgB) [QisB.ContainsIdentities]
variable (tensorRightN : ModdgB ⥤ ModdgC) (N' : ModdgB)
variable [tensorRightN.HasPointwiseLeftDerivedFunctorAt QisB N']

-- Semantic recall via `lean_leansearch` was not informative for this project-local owner, so the
-- owner choice was verified locally against the Chapter `13` derived-functor API
-- `leftDerivedValueProjection`, which is the canonical generic source of maps from a left-derived
-- value to the corresponding underived value.

/- 22.34.0.1: for the underived tensor functor represented by `N_B ⊗_B -`, the displayed map
`N_B ⊗_Bᴸ N' ⟶ (N_B ⊗_B N')_C`
is the canonical identity-denominator projection from the left-derived value of that tensor
functor at `N'` to its underived value. In the current Lean environment, where the specific
DG-module owner for this Stacks section has not yet been introduced, this item is therefore the
identity-denominator specialization of `leftDerivedValueProjection` at `N'`. -/
#check leftDerivedValueProjection QisB tensorRightN (𝟙 N') (QisB.id_mem N')

/-- The displayed plain-versus-derived tensor comparison is an isomorphism exactly when `N'`
computes the pointwise left-derived value of the tensor functor. This canonical instance exposes
the Chapter `13` source-facing owner for the same identity-denominator condition. -/
instance computesLeftDerivedAtOfIsIsoLeftDerivedValueProjection
    (h : IsIso (leftDerivedValueProjection QisB tensorRightN (𝟙 N') (QisB.id_mem N'))) :
    tensorRightN.ComputesLeftDerivedAt QisB N' :=
  { toHasPointwiseLeftDerivedFunctorAt := inferInstance
    isIso_leftDerivedValueProjection := h }

end

end CategoryTheory
