import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced `SheafOfModules.IsFinitePresentation` as the
-- canonical sheaf-side owner; for an affine scheme, the source is therefore stated directly as the
-- bridge between `tilde M` and `Module.FinitePresentation R M`.

/-- Lemma 28.16.2: for an affine scheme `Spec(R)`, the associated quasi-coherent
`𝒪_(Spec R)`-module `M^~` is of finite presentation if and only if `M` is an `R`-module of finite
presentation. -/
@[stacks 01PC]
theorem tilde_isFinitePresentation_iff_module_finitePresentation
    {R : CommRingCat} (M : ModuleCat R) :
    SheafOfModules.IsFinitePresentation (tilde M) ↔ Module.FinitePresentation R M := sorry
