import Mathlib
import StacksProject_2024.stacks_project.Chap07.«7_32_1_1»
import StacksProject_2024.stacks_project.Chap07.Definition_7_8_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory CategoryTheory.Limits Opposite
open GrothendieckTopology.Point
open CategoryTheory.SemiRepresentableFamily.Over

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

attribute [local instance] initiallySmall_of_essentiallySmall

/- Domain-style sampling for Lemma 7.39.1:
- primary domain: fibers of cofiltered inverse systems and the induced raw stalk functors on
  sheaves, together with explicit finite covering families on a fixed target;
- sampled owner API:
  `GrothendieckTopology.Point.ofIsCofiltered.fiber`,
  `GrothendieckTopology.Point.ofIsCofiltered.fiberMk`,
  `GrothendieckTopology.Point.ofIsCofiltered.refinementFiber`,
  `Functor.presheafFiber`,
  `GrothendieckTopology.Point.presheafFiber`,
  `GrothendieckTopology.Point.Hom.presheafFiber`,
  `SemiRepresentableFamily.Over`,
  `SemiRepresentableFamily.Over.toSieve`;
- source/core/bridge triage:
  `source-facing`: a directed inverse system `S : ιᵒᵖ ⥤ C`, its associated set-valued functor
  `u`, a fixed-target finite covering family `𝒰 : SemiRepresentableFamily.Over W`, and a
  refinement datum `S ≅ (j.toOrderHom.toFunctor).op ⋙ T`;
  `core/canonical`: `GrothendieckTopology.Point.ofIsCofiltered.fiber`, with raw stalk layer
  `sheafToPresheaf J (Type _) ⋙ (ofIsCofiltered.fiber S).presheafFiber`;
  `bridge/view`: `SemiRepresentableFamily.Over.toSieve` for finite covering families, together
  with the refinement-induced natural transformation `ofIsCofiltered.refinementFiber` between
  these canonical inverse-system fibers and its objectwise/raw-stalk projections.

Primitive data are only the inverse systems and the refinement datum. The covering-surjectivity
data needed to upgrade an inverse system to a site point are absent, so the source-facing theorem
must stay at the inverse-system fiber layer rather than be promoted to `Point.ofIsCofiltered`.
The sheaf-fiber layer is derived API of `Functor.presheafFiber`, and Chapter 7 already packages
explicit fixed-target families by `SemiRepresentableFamily.Over`, so this file should reuse those
owners instead of parallel local inverse-system-fiber or covering-family encodings.
-/
namespace GrothendieckTopology.Point.ofIsCofiltered

variable {ι : Type w} [Preorder ι]

private noncomputable abbrev refinementFiberDiagram (S : ιᵒᵖ ⥤ C) (W : C) :
    ιᵒᵖᵒᵖ ⥤ Type (max u v w) :=
  S.op ⋙ shrinkYoneda.{max u v w}.obj W

variable {ι' : Type w} [Preorder ι'] {S : ιᵒᵖ ⥤ C}
  (j : ι ↪o ι') (T : ι'ᵒᵖ ⥤ C) (e : S ≅ (j.toOrderHom.toFunctor).op ⋙ T)

private noncomputable abbrev refinementIndexFunctor :
    ιᵒᵖᵒᵖ ⥤ ι'ᵒᵖᵒᵖ :=
  show ιᵒᵖᵒᵖ ⥤ ι'ᵒᵖᵒᵖ from (j.toOrderHom.toFunctor).op.op

private noncomputable abbrev refinementDiagramHom :
    S.op ⟶ refinementIndexFunctor j ⋙ T.op :=
  show S.op ⟶ refinementIndexFunctor j ⋙ T.op from
    NatTrans.op e.inv ≫ (Functor.opComp (j.toOrderHom.toFunctor).op T).hom

private noncomputable def refinementFiberDiagramMap (W : C) :
    refinementFiberDiagram S W ⟶ refinementIndexFunctor j ⋙ refinementFiberDiagram T W :=
  Functor.whiskerRight (refinementDiagramHom j T e) (shrinkYoneda.{max u v w}.obj W)

/-- The natural transformation on inverse-system fiber functors induced by a refinement datum
`S ≅ (j.toOrderHom.toFunctor).op ⋙ T`. -/
noncomputable def refinementFiber :
    fiber.{max u v w} S ⟶ fiber.{max u v w} T where
  app W :=
    colim.map (refinementFiberDiagramMap j T e W) ≫
      colimit.pre (refinementFiberDiagram T W) (refinementIndexFunctor j)
  naturality := by
    intro X Y f
    sorry

@[simp]
theorem refinementFiber_app_fiberMk {U : ιᵒᵖ} {W : C} (f : S.obj U ⟶ W) :
    (refinementFiber j T e).app W (fiberMk f) =
      (show (fiber.{max u v w} T).obj W from fiberMk (e.inv.app U ≫ f)) := by
  sorry

end GrothendieckTopology.Point.ofIsCofiltered

section

variable {J : GrothendieckTopology C}

open GrothendieckTopology.Point.ofIsCofiltered

-- Proof sketch: represent `f` by a map from one stage of the original inverse system to `W`,
-- pull back the finite covering family `𝒰` to that stage, and use the sheaf condition together with
-- filtered-colimit commutation with finite products to find one cover member on which the images
-- of `s` and `s'` are still distinct. Adjoining those pullback stages yields a further directed
-- inverse system refining the original one, and the induced canonical maps on the associated
-- fibers still separate `s` and `s'` while making `f` come from one of the `u(𝒰ᵢ)`.
/-- Lemma 7.39.1: for a directed inverse system on a site, two distinct elements of the canonical
raw sheaf fiber
`(sheafToPresheaf J (Type _) ⋙ (GrothendieckTopology.Point.ofIsCofiltered.fiber S').presheafFiber).obj ℱ`
of a sheaf can be separated after passing to a refinement of the inverse system, and a chosen
element of the source-facing set-valued functor
`(GrothendieckTopology.Point.ofIsCofiltered.fiber S').obj W` can simultaneously be made to come
from one member of a given finite covering family `𝒰 : SemiRepresentableFamily.Over W`. The
refinement data is given directly by a larger directed inverse system together with an order
embedding and an identification of the old system with the restriction of the new one. -/
theorem exists_refined_inverse_system_separating_sections_and_lifting_cover
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] (S' : ιᵒᵖ ⥤ C)
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (hss' : s ≠ s')
    {W : C} (𝒰 : SemiRepresentableFamily.Over W) [Finite 𝒰.index]
    (h𝒰 : 𝒰.toSieve ∈ J W)
    (f : (fiber.{max u v w} S').obj W) :
    ∃ (ι' : Type w) (_ : Preorder ι') (_ : IsDirected ι' (· ≤ ·))
      (T : ι'ᵒᵖ ⥤ C) (j : ι ↪o ι') (e : S' ≅ (j.toOrderHom.toFunctor).op ⋙ T),
      ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s' ∧
        ∃ i : 𝒰.index, ∃ y : (fiber.{max u v w} T).obj (𝒰.obj i).left,
          ((fiber.{max u v w} T).map (𝒰.obj i).hom) y =
            (refinementFiber j T e).app W f := sorry

end

end CategoryTheory
