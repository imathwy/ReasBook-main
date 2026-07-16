import Mathlib
import stacks_proof.stacks_project.Chap06.Lemma_6_26_4
import stacks_proof.stacks_project.Chap17.Definition_17_17_1

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry.RingedSpace
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry

/- Domain-style sampling for Lemma 17.17.4:
- primary domain: pullback of module sheaves on a morphism of ringed spaces and preservation of
  flatness;
- sampled owner declarations:
  `RingedSpace.Hom.pullback`,
  `RingedSpace.Hom.pullbackStalkIso`,
  `SheafOfModules.IsFlat`,
  `SheafOfModules.isFlat_of_stalkwise`,
  `SheafOfModules.isFlat_stalk`,
  `Module.Flat.baseChange`;
- best owner abstraction: the canonical pullback functor `f^*` acts on `Y.Modules`, while
  the Chapter 17 public owner for flatness on ringed spaces is `SheafOfModules.IsFlat`, with
  underlying definitional core `SheafOfModules.RingedSite.IsFlat`;
- primitive data: a morphism `f : X ⟶ Y` and a module sheaf `𝒢 : Y.Modules`;
- derived API: the flatness-preservation theorem and instance below.

Source/core/bridge triage:
- `source-facing`: pullback preserves flatness;
- `core/canonical`: `Y.Modules`, `f^*`, and `SheafOfModules.IsFlat`;
- `bridge/view`: the stalkwise flatness argument from Lemma `6.26.4`.

This file should therefore reuse the canonical Chapter 6 pullback owner `f^*` together with the
chapter flatness owner from `Definition_17_17_1`, rather than restating flatness through the
underlying site-level predicate or restating pullback through an
explicit bridge decomposition or depending on a separate characterization wrapper.
-/

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

-- Proof sketch: by Lemma `17.17.2`, flatness is stalkwise. For `x : X`, identify the stalk of
-- `f^* 𝒢` with the base change of the stalk of `𝒢` along `\mathcal O_{Y,f(x)} → \mathcal O_{X,x}`
-- using Lemma `6.26.4`, then apply the module-theoretic base-change stability of flatness.
/-- Lemma 17.17.4: for a morphism of ringed spaces `f : (X, \mathcal O_X) ⟶ (Y, \mathcal O_Y)`,
if `𝒢` is a flat `\mathcal O_Y`-module, then its pullback `f^* 𝒢` is a flat
`\mathcal O_X`-module. -/
@[stacks 0H97]
theorem pullback_isFlat (𝒢 : Y.Modules)
    [𝒢.IsFlat] :
    ((f^*).obj 𝒢).IsFlat := by
  refine SheafOfModules.isFlat_of_stalkwise ((f^*).obj 𝒢) ?_
  intro x
  let _ : Module.Flat (X.presheaf.stalk x)
      ↑((ModuleCat.extendScalars (f.hom.stalkMap x).hom).obj
        (stalkModuleCat 𝒢 (f.hom.base x))) := by
    let _ : Algebra (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x) :=
      (f.hom.stalkMap x).hom.toAlgebra
    let _ : Module.Flat (Y.presheaf.stalk (f.hom.base x))
        ↑(stalkModuleCat 𝒢 (f.hom.base x)) :=
      by
        have h𝒢 : 𝒢.IsFlat := inferInstance
        simpa [SheafOfModules.flat_at] using
          SheafOfModules.isFlat_stalk h𝒢 (f.hom.base x)
    change Module.Flat (X.presheaf.stalk x)
      (TensorProduct (Y.presheaf.stalk (f.hom.base x)) (X.presheaf.stalk x)
        ↑(stalkModuleCat 𝒢 (f.hom.base x)))
    infer_instance
  exact Module.Flat.of_linearEquiv ((RingedSpace.Hom.pullbackStalkIso f 𝒢 x).symm.toLinearEquiv)

/-- Pullback along a morphism of ringed spaces preserves flat module sheaves. -/
instance (𝒢 : Y.Modules) [𝒢.IsFlat] : ((f^*).obj 𝒢).IsFlat :=
  pullback_isFlat f 𝒢

end AlgebraicGeometry
