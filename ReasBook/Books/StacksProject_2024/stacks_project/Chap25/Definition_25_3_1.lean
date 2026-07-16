import StacksProject_2024.stacks_project.Chap25.Definition_25_2_2

-- Declarations for this item will be appended below by the statement pipeline.

universe w v u

namespace CategoryTheory

open Opposite
open CategoryTheory.Limits
open scoped CategoryTheory.SemiRepresentableFamily

variable {C : Type u} [Category.{v} C]

namespace Limits
namespace FormalCoproduct

/- Domain-style sampling for Definition 25.3.1:
- primary domain: formal coproducts in the slice `C / U` and the canonical comparison from the
  coproduct of the corresponding representables to the representable presheaf of `U`;
- sampled owner declarations:
  `FormalCoproduct`,
  `FormalCoproduct.toPresheaf`,
  `CategoryTheory.uliftYoneda`,
  `CategoryTheory.Limits.Sigma.desc`;
- best owner abstraction: this namespace supplies the core/canonical implementation of the
  augmentation, while the chapter's source-facing owner is the fixed-target family specialization
  `SemiRepresentableFamily.Over.augmentation`;
- primitive data: only the fixed-target family `K : FormalCoproduct (Over U)`;
- derived API: the canonical forgetful functor `forgetOver`, the induced natural transformation
  `augmentation`, and its component formulas.

Source/core/bridge triage:
- `source-facing`: `SemiRepresentableFamily.Over.augmentation`;
- `core/canonical`: the augmentation
  `toPresheaf.obj ((forgetOver U).obj K) ⟶ uliftYoneda.obj U`;
- `bridge/view`: `forgetOver` and the fixed-target-family specialization.
-/

/-- Forgetting the structure maps to `U` sends a formal coproduct in `C / U` to its underlying
formal coproduct in `C`. -/
def forgetOver (U : C) : FormalCoproduct.{w} (CategoryTheory.Over U) ⥤ FormalCoproduct.{w} C where
  obj K := ⟨K.I, fun i ↦ (K.obj i).left⟩
  map φ := ⟨φ.f, fun i ↦ (φ.φ i).left⟩

/-- Core/canonical augmentation attached to a formal coproduct of arrows with fixed target `U`. -/
noncomputable def augmentation {U : C} (K : FormalCoproduct.{w} (CategoryTheory.Over U)) :
    toPresheaf.obj ((forgetOver U).obj K) ⟶ uliftYoneda.obj U :=
  Sigma.desc fun i : K.I ↦ uliftYoneda.{w}.map (K.obj i).hom

/-- The core augmentation is natural in formal coproducts over the fixed target. -/
@[reassoc] theorem augmentation_naturality {U : C}
    {K L : FormalCoproduct.{w} (CategoryTheory.Over U)} (φ : K ⟶ L) :
    toPresheaf.map ((forgetOver U).map φ) ≫ augmentation L = augmentation K := by
  apply Limits.Sigma.hom_ext
  intro i
  ext X g
  rw [Category.assoc, FunctorToTypes.comp_apply, FormalCoproduct.toPresheaf_map_objMk]
  simp [augmentation, Category.assoc]
  simpa [Category.assoc] using congrArg (fun k ↦ ULift.up (g.down ≫ k)) (Over.w (φ.φ i))

end FormalCoproduct
end Limits

namespace SemiRepresentableFamily
namespace Over

open CategoryTheory.Limits

/- Definition 25.3.1 at the chapter owner level:
- `source-facing`: the fixed-target family augmentation `augmentation K`;
- `core/canonical`: `FormalCoproduct.augmentation`;
- `bridge/view`: `SemiRepresentableFamily.Over.toFormalCoproduct`.
-/

/-- Definition 25.3.1: a family of arrows with fixed target `U` induces a canonical map from the
associated coproduct of representable presheaves to the representable presheaf `h_U`. -/
noncomputable abbrev augmentation {U : C} (K : SR(C, U)) :
    SemiRepresentableFamily.toPresheaf.obj ((forget).obj K) ⟶ uliftYoneda.obj U :=
  FormalCoproduct.augmentation (toFormalCoproduct.obj K)

/-- The fixed-target augmentation is natural in the semi-representable family. -/
@[reassoc] theorem augmentation_naturality {U : C} {K L : SR(C, U)} (φ : K ⟶ L) :
    SemiRepresentableFamily.toPresheaf.map (forget.map φ) ≫ augmentation L = augmentation K := by
  simpa only [SemiRepresentableFamily.toPresheaf, SemiRepresentableFamily.Over.augmentation,
    SemiRepresentableFamily.Over.forget, SemiRepresentableFamily.map,
    SemiRepresentableFamily.Over.toFormalCoproduct, SemiRepresentableFamily.toFormalCoproduct]
    using FormalCoproduct.augmentation_naturality φ

end Over
end SemiRepresentableFamily

end CategoryTheory
