import stacks_proof.stacks_project.Chap08.Lemma_8_8_3.LiftBasedFunctor

universe u v uS vS w wD vD

namespace CategoryTheory

open BasedFunctor
open Opposite

section

variable {C : Type u} [Category.{v} C]
variable {J : GrothendieckTopology C}
variable {S : FibredCategoryOver.{u, v, uS, vS} C} {S' X : StackOver.{u, v, uS, vS} J}

/-- Helper for Chap08 Lemma 8 8 3: an admissible descended based functor determines the
corresponding stack morphism. -/
private noncomputable def stackificationLiftStackMorOfBasedFunctor
    (Hbf : S'.toBasedCategory ⥤ᵇ X.toBasedCategory)
    (hcart : BasedFunctor.PreservesStronglyCartesian Hbf) :
    S' ⟶ X :=
  InducedCategory.Hom.ofFibredCategoryMor (FibredCategoryMor.ofBasedFunctor Hbf hcart)

/-- Helper for Chap08 Lemma 8 8 3: a based-functor comparison for a descended admissible functor
packages as the owner isomorphism required by precomposition. -/
private theorem stackificationLiftStackMorOfBasedFunctor_precompose_iso
    (G : S ⟶ S')
    (F : S ⟶ X)
    (Hbf : S'.toBasedCategory ⥤ᵇ X.toBasedCategory)
    (hcart : BasedFunctor.PreservesStronglyCartesian Hbf)
    (e : BasedFunctor.comp G.toHom Hbf ≅ FibredCategoryMor.toBasedFunctor F) :
    Nonempty
      ((stackification_precompose_functor X G).obj
        (stackificationLiftStackMorOfBasedFunctor Hbf hcart) ≅ F) := by
  -- The item-local precomposition functor was built by forgetting to based functors, whiskering by
  -- `G`, and repackaging through the full owner hom-category.
  refine ⟨FibredCategoryMor.ownerIsoOfBasedFunctorIso ?_⟩
  change BasedFunctor.comp G.toHom Hbf ≅ FibredCategoryMor.toBasedFunctor F
  exact e

/-- Helper for Chap08 Lemma 8 8 3: the concrete object-and-arrow descent statement needed for
essential surjectivity of precomposition by a stackification. -/
private theorem stackificationLiftStackMor_exists_core
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X) :
    ∃ H : S' ⟶ X, Nonempty ((stackification_precompose_functor X G).obj H ≅ F) := by
  -- Route correction: the previous owner-`EssSurj` hole hid the real mathematical task. The
  -- remaining blocker is now the concrete descent construction of `H`, using local source
  -- models from `hG`, object gluing in `X`, and forced-Hom gluing for arrows.
  -- The presheaf-level Hom extension for the fixed `F` is established above. The unresolved
  -- piece is to turn that extension into object descent data, glue fiber objects in `X`, define
  -- cartesian-target arrow maps, and package the resulting based functor with a comparison iso.
  obtain ⟨Hbf, hcart, hIso⟩ := stackificationLiftBasedFunctor_exists X G hG F
  rcases hIso with ⟨e⟩
  refine ⟨stackificationLiftStackMorOfBasedFunctor Hbf hcart, ?_⟩
  -- The remaining owner-level step is pure packaging: the descended based-functor comparison
  -- induces the requested isomorphism in the stack-morphism hom-category.
  exact stackificationLiftStackMorOfBasedFunctor_precompose_iso G F Hbf hcart e

/-- Helper for Chap08 Lemma 8 8 3: the owner-level precomposition functor is essentially
surjective on stack morphisms into a stack target. -/
private theorem local_stackification_precompose_functor_essSurj
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G) :
    (local_stackification_precompose_functor (J := J) (G := G) :
      (S' ⟶ X) ⥤ (S ⟶ X)).EssSurj := by
  -- Essential surjectivity is only a packaging layer: use the concrete descended-lift theorem
  -- and transport from the item-local precomposition spelling to the owner spelling.
  exact
    local_stackification_precompose_functor_essSurj_of_lift X G
      (stackificationLiftStackMor_exists_core X G hG)

/-- Helper for Chap08 Lemma 8 8 3: every stack morphism out of `S` is locally glued to a stack
morphism out of `S'` whose precomposition is isomorphic to it. -/
private theorem stackificationLiftStackMor_exists
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G)
    (F : S ⟶ X) :
    ∃ H : S' ⟶ X, Nonempty ((stackification_precompose_functor X G).obj H ≅ F) := by
  -- The concrete descent theorem is the source-facing lift statement; keep this public helper as
  -- a stable name for downstream uses.
  exact stackificationLiftStackMor_exists_core X G hG F

/-- Helper for Chap08 Lemma 8 8 3: every morphism from `S` to a stack target descends along a
stackification morphism `G : S ⟶ S'`. -/
private theorem stackification_precompose_essSurj
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G) :
    (stackification_precompose_functor X G :
      (S' ⟶ X) ⥤ (S ⟶ X)).EssSurj := by
  -- Essential surjectivity is the stack-morphism lifting helper, repackaged in the functor API.
  constructor
  intro F
  exact stackificationLiftStackMor_exists X G hG F

/-- Lemma 8.8.3: if `G : S ⟶ S'` is a stackification morphism, then precomposition with `G`
induces an equivalence on morphism categories into any stack `X`. The canonical owner statement is
that `stackification_precompose_functor X G` is an equivalence of categories. -/
@[stacks 04W9]
instance stackification_precompose_functor_isEquivalence
    (X : StackOver J)
    (G : S ⟶ S')
    (hG : FibredCategoryMor.IsStackification G) :
    Functor.IsEquivalence
      (stackification_precompose_functor X G :
        (S' ⟶ X) ⥤ (S ⟶ X)) := by
  -- The owner equivalence criterion reduces the universal property to full faithfulness on
  -- `2`-morphisms and essential surjectivity on morphisms into the stack target.
  exact
    (Functor.isEquivalence_iff_full_faithful_essSurj
      (stackification_precompose_functor X G :
        (S' ⟶ X) ⥤ (S ⟶ X))).2
      ⟨fun H K ↦ stackification_precompose_map_bijective X G hG H K,
        stackification_precompose_essSurj X G hG⟩

end

end CategoryTheory
