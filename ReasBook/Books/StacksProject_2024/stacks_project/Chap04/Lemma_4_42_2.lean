import Mathlib
import StacksProject_2024.stacks_project.Chap04.Lemma_4_32_5
import StacksProject_2024.stacks_project.Chap04.Definition_4_35_6
import StacksProject_2024.stacks_project.Chap04.Lemma_4_35_7
import StacksProject_2024.stacks_project.Chap04.Lemma_4_35_13

-- Declarations for this item will be appended below by the statement pipeline.

universe v u

namespace CategoryTheory

open CategoryOver

variable {C : Type u} [Category.{v} C]
variable {U : C}
variable {X Y : BasedCategory C}

/- Domain-style sampling for Lemma 4.42.2:
- primary domain: slice-level base change of categories fibred in groupoids, with the explicit
  `2`-fibre product from `Cat/C` viewed over the slice category `C/U`;
- inspected owner-level declarations:
  `explicitTwoFibreProduct`,
  `explicitTwoFibreProductLeftProjection`,
  `explicitTwoFibreProductProjection_isFibredInGroupoids`,
  `Functor.isFibredInGroupoids_of_comp_over_forget`,
  `FibredInGroupoidsOver.twoFibreProduct`;
- best owner abstraction: the source-facing object is the canonical explicit left projection
  `explicitTwoFibreProductLeftProjection G F : (C/U) ×_Y X ⥤ᵇ C/U`, and the main property should
  live directly on its underlying functor via `IsFibredInGroupoids`;
- primitive data: the based functors `F : X ⥤ᵇ Y` and
  `G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ Y`, together with the explicit pullback total
  category `explicitTwoFibreProduct G F`;
- derived API: the fibred-in-groupoids theorem for the explicit left projection; the bundled
  owner object is already supplied upstream by `FibredInGroupoidsOver.twoFibreProduct`.

Source/core/bridge triage:
- `source-facing`: `explicitTwoFibreProductLeftProjection_isFibredInGroupoids`;
- `core/canonical`: `explicitTwoFibreProductLeftProjection` and `IsFibredInGroupoids`;
- `bridge/view`: the bundled owner rebundling `FibredInGroupoidsOver.twoFibreProduct`. -/

-- Proof sketch: compose `(explicitTwoFibreProductLeftProjection G F).toFunctor` with
-- `Over.forget U` to recover the projection to `C` from Lemma `4.35.7`, which is fibred in
-- groupoids because the pullback source `X` is fibred in groupoids and the target projection
-- `Y.p` is fibred over `C`. Then apply
-- Lemma `4.35.13` to lift the fibred-in-groupoids structure along `Over.forget U`.
/-- Lemma 4.42.2: if `F : X ⥤ᵇ Y` has source fibred in groupoids over `C`, if the target
projection `Y.p` is fibred over `C`, and if `G : (C/U) ⥤ Y` lies over `C`, then the projection
from the explicit `2`-fibre product `(C/U) ×_Y X` to `C/U` is a category fibred in groupoids. In
particular this applies to a morphism between categories fibred in groupoids over `C`. -/
theorem explicitTwoFibreProductLeftProjection_isFibredInGroupoids
    (F : X ⥤ᵇ Y) (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ Y)
    [IsFibredInGroupoids X.p] [Y.p.IsFibered] :
    IsFibredInGroupoids (explicitTwoFibreProductLeftProjection G F).toFunctor := by
  let p : (explicitTwoFibreProduct G F).obj ⥤ Over U :=
    (explicitTwoFibreProductLeftProjection G F).toFunctor
  letI : IsFibredInGroupoids (BasedCategory.ofFunctor (Over.forget U)).p := by
    change IsFibredInGroupoids (Over.forget U)
    infer_instance
  have hp : p ⋙ Over.forget U = (explicitTwoFibreProduct G F).p := by
    simpa [p] using (explicitTwoFibreProductLeftProjection G F).w
  letI : IsFibredInGroupoids (p ⋙ Over.forget U) := by
    rw [hp]
    exact explicitTwoFibreProductProjection_isFibredInGroupoids G F
  simpa [p] using Functor.isFibredInGroupoids_of_comp_over_forget p

instance (F : X ⥤ᵇ Y) (G : BasedCategory.ofFunctor (Over.forget U) ⥤ᵇ Y)
    [IsFibredInGroupoids X.p] [Y.p.IsFibered] :
    IsFibredInGroupoids (explicitTwoFibreProductLeftProjection G F).toFunctor :=
  explicitTwoFibreProductLeftProjection_isFibredInGroupoids F G

end CategoryTheory
