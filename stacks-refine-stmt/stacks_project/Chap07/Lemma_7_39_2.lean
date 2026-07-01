import Mathlib
import stacks_project.Chap07.Definition_7_8_2
import stacks_project.Chap07.Lemma_7_39_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.SemiRepresentableFamily.Over

universe u v w

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

attribute [local instance] initiallySmall_of_essentiallySmall

section

variable {J : GrothendieckTopology C}

/-
Domain-style sampling for Lemma 7.39.2:
- primary domain: fibers of cofiltered inverse systems on a site and lifting along finite covering
  families;
- sampled owner API:
  `Functor.presheafFiber`,
  `GrothendieckTopology.Point.ofIsCofiltered.fiber`,
  `GrothendieckTopology.Point.ofIsCofiltered.refinementFiber`,
  `SemiRepresentableFamily.Over`,
  `SemiRepresentableFamily.Over.toSieve`;
- source/core/bridge triage:
  `source-facing`: a directed inverse system together with the requirement that, after refinement,
  every finite covering family lifts elements of its canonical fiber functor;
  `core/canonical`: `ofIsCofiltered.fiber` for the inverse-system fiber and
  `SemiRepresentableFamily.Over` for explicit fixed-target covering families;
  `bridge/view`: the refinement datum
  `S' ≅ (j.toOrderHom.toFunctor).op ⋙ T` and the induced natural transformation
  `refinementFiber`, together with its objectwise and raw-stalk applications.

Primitive data are only the inverse systems, the refinement datum, and the finite covering family
itself. The chapter already treats explicit covering families through `SemiRepresentableFamily.Over`
rather than the raw triple `(κ, Wk, π)`, so this file should reuse that owner and derive the
lifting clause from it instead of keeping a parallel coordinate-level encoding.
-/
open GrothendieckTopology.Point.ofIsCofiltered

-- Proof sketch: well-order the class of pairs consisting of a finite covering family and an
-- element of `u'(W)`, then iterate Lemma 7.39.1 by transfinite recursion so that each stage
-- preserves the separation of `s` and `s'` while forcing the lifting condition for the next pair.
-- The directed union of the resulting chain is again a refinement of the original directed system,
-- and the induced canonical maps still separate `s` and `s'` while satisfying the required
-- finite-cover lifting property for every stage of the well-order.
/-- Lemma 7.39.2: given a directed inverse system on a site and two distinct elements of the
canonical raw sheaf fiber
`(sheafToPresheaf J (Type _) ⋙ (GrothendieckTopology.Point.ofIsCofiltered.fiber S').presheafFiber).obj ℱ`
of a sheaf, there exists a refinement of the inverse system whose induced canonical map on sheaf
fibers still separates those elements and whose refined object fiber functor has the property that
every element over an object lifts through some member of any finite covering family of that
object. -/
theorem exists_refined_inverse_system_separating_sections_and_lifting_all_finite_covers
    {ι : Type w} [Preorder ι] [IsDirected ι (· ≤ ·)] (S' : ιᵒᵖ ⥤ C)
    {ℱ : Sheaf J (Type (max u v w))}
    {s s' : (sheafToPresheaf J (Type (max u v w)) ⋙
      (fiber.{max u v w} S').presheafFiber).obj ℱ}
    (hss' : s ≠ s') :
    ∃ (ι' : Type w) (_ : Preorder ι') (_ : IsDirected ι' (· ≤ ·))
      (T : ι'ᵒᵖ ⥤ C) (j : ι ↪o ι') (e : S' ≅ (j.toOrderHom.toFunctor).op ⋙ T),
      let u := fiber.{max u v w} T
      ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
        (Type (max u v w))).obj ℱ) s ≠
        ((refinementFiber j T e).presheafFiber).app ((sheafToPresheaf J
          (Type (max u v w))).obj ℱ) s' ∧
        ∀ {W : C} (𝒰 : SemiRepresentableFamily.Over.{v, u, w} W) [Finite 𝒰.index]
          (h𝒰 : 𝒰.toSieve ∈ J W) (f : u.obj W),
            ∃ i : 𝒰.index, ∃ y : u.obj (𝒰.obj i).left, u.map (𝒰.obj i).hom y = f := sorry

end

end CategoryTheory
