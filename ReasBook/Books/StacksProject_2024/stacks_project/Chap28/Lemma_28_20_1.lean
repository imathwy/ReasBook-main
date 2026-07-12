import Mathlib
import StacksProject_2024.Chap10.Definition_10_78_1
import StacksProject_2024.Chap17.Definition_17_14_1

open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

-- Semantic recall: `lean_leansearch` surfaced the affine-module sheaf owner
-- `AlgebraicGeometry.tilde`
-- together with the Chapter 10 and Chapter 17 locally free owners, so the Stacks item is stated
-- directly as the affine `~M` bridge between those canonical notions.

/-- Lemma 28.20.1 (1): for the affine scheme `X = Spec(R)` and the quasi-coherent sheaf
`\widetilde M = M^~`, local freeness of `\widetilde M` is equivalent to local freeness of the
`R`-module `M`. -/
@[stacks 05P1]
theorem tilde_isLocallyFree_iff_module_locallyFree
    {R : CommRingCat.{u}} (M : ModuleCat R) :
    SheafOfModules.IsLocallyFree (tilde M) ↔
      Module.LocallyFree R M := sorry

/-- Lemma 28.20.1 (2): for the affine scheme `X = Spec(R)` and the quasi-coherent sheaf
`\widetilde M = M^~`, finite local freeness of `\widetilde M` is equivalent to finite local
freeness of the `R`-module `M`. -/
@[stacks 05P1]
theorem tilde_isFiniteLocallyFree_iff_module_finiteLocallyFree
    {R : CommRingCat.{u}} (M : ModuleCat R) :
    SheafOfModules.IsFiniteLocallyFree (tilde M) ↔
      Module.FiniteLocallyFree R M := sorry
