import Mathlib.AlgebraicGeometry.Modules.Tilde

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open scoped AlgebraicGeometry

-- Semantic recall: `SheafOfModules.IsFiniteType` is the canonical sheaf-side owner, while
-- `Module.Finite R M` is the canonical affine algebra-side owner. For an affine scheme, the
-- source is therefore stated directly as the bridge between `tilde M` and finite generation of
-- the underlying `R`-module.

/-- Lemma 28.16.1: for an affine scheme `Spec(R)`, the associated quasi-coherent
`𝒪_(Spec R)`-module `M^~` is of finite type if and only if `M` is a finite `R`-module. -/
@[stacks 01PB]
theorem tilde_isFiniteType_iff_module_finite
    {R : CommRingCat} (M : ModuleCat R) :
    SheafOfModules.IsFiniteType (tilde M) ↔ Module.Finite R M := sorry
