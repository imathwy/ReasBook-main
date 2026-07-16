import Mathlib.AlgebraicGeometry.Modules.Tilde
import StacksProject_2024.stacks_project.Chap17.Definition_17_17_1

open AlgebraicGeometry
open scoped AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the affine associated-module sheaf owner
-- `ModuleCat.tilde`, while the local flatness criteria already live in Chapter 10 for modules and
-- Chapter 17 for sheaves. The Stacks item is therefore stated directly as the affine
-- `\widetilde M` bridge between those canonical owners.

/-- Lemma 28.19.1: for the affine scheme `X = Spec(R)` and the quasi-coherent sheaf
`\widetilde M`, the sheaf `\widetilde M` is a flat `\mathcal O_X`-module if and only if the
`R`-module `M` is flat. -/
@[stacks 05P0]
theorem tilde_isFlat_iff_module_flat
    {R : CommRingCat} (M : ModuleCat R) :
    SheafOfModules.IsFlat (tilde M) ↔ Module.Flat R M := sorry
