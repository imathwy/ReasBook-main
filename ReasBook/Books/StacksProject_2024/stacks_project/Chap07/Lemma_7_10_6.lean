import Mathlib.CategoryTheory.Sites.ConcreteSheafification

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe w v u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type u} [Category.{v} C]
variable (J : GrothendieckTopology C)
variable {P : Cᵒᵖ ⥤ Type w}

/- Domain-style sampling for Lemma 7.10.6:
- primary domain: matching families for set-valued presheaves on a Grothendieck site;
- sampled owner API:
  `CategoryTheory.GrothendieckTopology.Meq`,
  `CategoryTheory.GrothendieckTopology.Meq.refine`,
  `CategoryTheory.GrothendieckTopology.Meq.pullback`,
  `CategoryTheory.GrothendieckTopology.Meq.pullback_refine`,
  `CategoryTheory.GrothendieckTopology.Cover.pullback`;
- source-facing layer: the Stacks lemma says that the induced pullback map on matching families
  depends only on the base morphism `h : U ⟶ V`, not on a chosen refinement witness;
- core/canonical owner: matching families `Meq P 𝒱` with the canonical operations `refine`,
  `pullback`, and the interchange theorem `pullback_refine`;
- bridge/view layer: the textbook pullback statement below is a specialization of the owner-level
  witness-independence of `Meq.refine`;
- primitive data: a matching family `x : Meq P 𝒱` and a refinement morphism between covers;
- derived API: the pullback specialization along `h : U ⟶ V`.

No extra wrapper structure is warranted: the statement should live directly on the owner namespace
`Meq`.
-/

namespace Meq

-- Proof sketch: a morphism of covers is unique when it exists, so refining along two such
-- morphisms gives the same matching family.
/-- Refining a matching family along a morphism of covers depends only on the source and target
covers, not on the chosen morphism. -/
theorem refine_eq {U : C} {𝒰 𝒱 : J.Cover U} (x : Meq P 𝒱) (e e' : 𝒰 ⟶ 𝒱) :
    x.refine e = x.refine e' := by
  simpa using congrArg (fun φ ↦ x.refine φ) (Subsingleton.elim e e')

-- Lemma 7.10.6 is the pullback specialization of `refine_eq`.
/-- Lemma 7.10.6: for a matching family on `𝒱`, refining its pullback along `h : U ⟶ V` is
independent of the chosen morphism `𝒰 ⟶ 𝒱.pullback h`. -/
theorem pullback_refine_eq
    {U V : C} {𝒰 : J.Cover U} {𝒱 : J.Cover V}
    (x : Meq P 𝒱) (h : U ⟶ V) (e e' : 𝒰 ⟶ 𝒱.pullback h) :
    (x.pullback h).refine e = (x.pullback h).refine e' := by
  simpa using congrArg (fun φ ↦ (x.pullback h).refine φ) (Subsingleton.elim e e')

end Meq

end CategoryTheory.GrothendieckTopology
