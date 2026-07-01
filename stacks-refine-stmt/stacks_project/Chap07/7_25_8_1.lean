import Mathlib.Tactic.Recall
import stacks_project.Chap07.Definition_7_25_1

open CategoryTheory Opposite
open scoped MorphismOfTopoiIn

universe u v

noncomputable section

namespace CategoryTheory

section

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable {U V : C} (f : V ⟶ U)

/- Domain-style sampling for 7.25.8.1:
- primary domain: localization and relocalization morphisms of topoi attached to the slice-site
  functors `Over.forget` and `Over.map`;
- sampled owner API:
  `Functor.morphismOfTopoiInOfCocontinuous`,
  `MorphismOfTopoiIn.comp`,
  `Functor.morphismOfTopoiInOfCocontinuous_inverseImage`,
  `Functor.sheafPushforwardContinuousComp'`;
- source/core/bridge triage:
  `source-facing`: the commutative triangle `j_V = j_U ∘ j` of morphisms of topoi for
  relocalization along `f : V ⟶ U`;
  `core/canonical`: the localization and relocalization morphisms of topoi built from
  `Over.forget U`, `Over.forget V`, and `Over.map f`, together with `MorphismOfTopoiIn.comp`;
  `bridge/view`: the inverse-image comparison
  `j_U⁻¹ ⋙ j⁻¹ ≅ j_V⁻¹`, specialized from `Functor.sheafPushforwardContinuousComp'`.

Primitive data are only the site `J` and the morphism `f`. The morphisms of topoi themselves are
already canonically owned by `Functor.morphismOfTopoiInOfCocontinuous`, so this file should make
the triangle live at `MorphismOfTopoiIn.comp` and treat the inverse-image comparison as derived
API rather than as the main public entry.
-/

variable [HasSheafify (J.over U) (Type (max u v))]
variable [HasSheafify (J.over V) (Type (max u v))]
variable [∀ P : (Over U)ᵒᵖ ⥤ Type (max u v), (Over.forget U).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Over V)ᵒᵖ ⥤ Type (max u v), (Over.map f).op.HasPointwiseRightKanExtension P]
variable [∀ P : (Over V)ᵒᵖ ⥤ Type (max u v), (Over.forget V).op.HasPointwiseRightKanExtension P]

-- Proof sketch: both sides are the morphism of topoi induced by the cocontinuous triangle
-- `Over.map f ⋙ Over.forget U ≅ Over.forget V`, so the result follows by comparing the canonical
-- owner constructions attached to `Over.mapForget f`.
/-- 7.25.8.1: the relocalization morphism
`Sh(C/V, J.over V) ⟶ Sh(C/U, J.over U)` followed by localization at `U` equals the localization
morphism at `V`. -/
theorem relocalization_comp_localization_eq_localization :
    MorphismOfTopoiIn.comp
        ((Over.forget U).morphismOfTopoiInOfCocontinuous (J.over U) J)
        ((Over.map f).morphismOfTopoiInOfCocontinuous (J.over V) (J.over U)) =
      ((Over.forget V).morphismOfTopoiInOfCocontinuous (J.over V) J) := sorry

end

end CategoryTheory
