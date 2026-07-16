import Mathlib
import StacksProject_2024.stacks_project.Chap04.Definition_4_33_9
import StacksProject_2024.stacks_project.Chap04.Lemma_4_32_3

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

namespace CategoryTheory

open CategoryOver
open FibredCategoryMor
open scoped Bicategory

/-
Domain-style sampling for Lemma 4.33.10:
- primary domain: fibred categories over a fixed base together with bicategorical `2`-fibre
  products in the fibred full sub-`2`-category of `Cat/C`;
- sampled owner declarations:
  `explicitTwoFibreProduct`,
  `explicitTwoFibreProductSquareOver`,
  `explicitTwoFibreProduct_isTwoFibreProduct`,
  `FibredCategoryOver.ofFunctor`,
  `FibredCategoryMor.ofBasedFunctor`;
- best owner abstraction: `FibredCategoryOver C`, viewed through the owner sub-`2`-category
  `fibredCategoryOverSubTwoCategory C`, with `explicitTwoFibreProduct` supplying the canonical
  source-facing pullback model in `Cat/C`;
- primitive data: entirely owned upstream by `explicitTwoFibreProduct` and its two projection
  based functors;
- derived API kept here: the fibredness of the explicit apex, the upgraded projection morphisms in
  `FibredCategoryOver C`, and the resulting `BicategoricalTwoCommutativeSquare`.

Source/core/bridge triage:
- `source-facing`: the square `FibredCategoryOver.twoFibreProductSquare F G` and its
  `2`-fibre-product property in `FibredCategoryOver C`;
- `core/canonical`: `FibredCategoryOver C`, the ambient owner homs `X ⟶ Y`, and
  `Bicategory.IsFinal (FibredCategoryOver.twoFibreProductSquare F G)`;
- `bridge/view`: the bundled apex `FibredCategoryOver.twoFibreProduct F G` and the ambient
  `Cat/C` square
  `(explicitTwoFibreProductSquareOver F.toBasedFunctor G.toBasedFunctor).toBicategoricalSquare`;
- exact-interface wrapper eliminated here: downstream ambient uses should call
  `explicitTwoFibreProduct_isTwoFibreProduct` directly rather than through a renamed local shell. -/

variable {C : Type u} [Category.{v} C]
variable {Xf Yf Sf : FibredCategoryOver C}

private theorem explicitTwoFibreProductProjection_isFibered
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p.IsFibered := by
  sorry

namespace FibredCategoryOver

open FibredCategoryMor

/-- The explicit `2`-fibre-product category of Lemma 4.32.3, bundled as a fibred category over
`C` when the legs are morphisms of fibred categories. -/
noncomputable abbrev twoFibreProduct
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    FibredCategoryOver C :=
  let p := (explicitTwoFibreProduct (toBasedFunctor F) (toBasedFunctor G)).p
  letI : p.IsFibered := explicitTwoFibreProductProjection_isFibered F G
  ofFunctor p

private noncomputable abbrev twoFibreProductLeftBased
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    (twoFibreProduct F G).toBasedCategory ⥤ᵇ Xf.toBasedCategory :=
  show (twoFibreProduct F G).toBasedCategory ⥤ᵇ Xf.toBasedCategory from
    explicitTwoFibreProductLeftProjection (toBasedFunctor F) (toBasedFunctor G)

private noncomputable abbrev twoFibreProductRightBased
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    (twoFibreProduct F G).toBasedCategory ⥤ᵇ Yf.toBasedCategory :=
  show (twoFibreProduct F G).toBasedCategory ⥤ᵇ Yf.toBasedCategory from
    explicitTwoFibreProductRightProjection (toBasedFunctor F) (toBasedFunctor G)

private theorem twoFibreProductLeftProjection_preservesStronglyCartesian
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    BasedFunctor.PreservesStronglyCartesian (twoFibreProductLeftBased F G) := by
  sorry

private theorem twoFibreProductRightProjection_preservesStronglyCartesian
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    BasedFunctor.PreservesStronglyCartesian (twoFibreProductRightBased F G) := by
  sorry

/-- The left projection from the canonical fibred `2`-fibre product. -/
noncomputable abbrev twoFibreProductLeftProjection
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    twoFibreProduct F G ⟶ Xf :=
  ofBasedFunctor
    (twoFibreProductLeftBased F G)
    (twoFibreProductLeftProjection_preservesStronglyCartesian F G)

/-- The right projection from the canonical fibred `2`-fibre product. -/
noncomputable abbrev twoFibreProductRightProjection
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    twoFibreProduct F G ⟶ Yf :=
  ofBasedFunctor
    (twoFibreProductRightBased F G)
    (twoFibreProductRightProjection_preservesStronglyCartesian F G)

/-- The canonical `2`-commutative square in the bicategory of fibred categories over `C`
underlying Lemma 4.33.10. -/
noncomputable def twoFibreProductSquare
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    BicategoricalTwoCommutativeSquare F G :=
  { obj := twoFibreProduct F G
    p := twoFibreProductLeftProjection F G
    q := twoFibreProductRightProjection F G
    ψ := by
      let e :
          (twoFibreProductLeftProjection F G ≫ F).obj ≅
            (twoFibreProductRightProjection F G ≫ G).obj := by
        exact
          ObjectProperty.isoMk
            (show ObjectProperty
                ((twoFibreProduct F G).toBasedCategory ⥤ᵇ Sf.toBasedCategory) from
              BasedFunctor.PreservesStronglyCartesian)
            (show BasedFunctor.comp (twoFibreProductLeftBased F G) F.toHom ≅
                BasedFunctor.comp (twoFibreProductRightBased F G) G.toHom from
              explicitTwoFibreProductComparisonIsoOver (toBasedFunctor F) (toBasedFunctor G))
      exact CategoryTheory.isoMk e trivial trivial }

-- Proof sketch: the explicit apex from Lemma `4.32.3` is fibred by
-- `explicitTwoFibreProductProjection_isFibered`, and the two ambient projection functors are
-- upgraded here to `FibredCategoryMor`s by the strongly-cartesian-preservation results above.
-- The terminal factorization in the bicategory of fibred categories is then obtained by refining
-- the ambient `Cat/C` factorization so that the induced apex map also preserves strongly
-- cartesian morphisms.
/-- Lemma 4.33.10: for morphisms of fibred categories over `C`, the canonical explicit square of
Lemma 4.32.3 is a bicategorical `2`-fibre product square in `FibredCategoryOver C`. -/
theorem twoFibreProduct_isTwoFibreProduct
    (F : Xf ⟶ Sf) (G : Yf ⟶ Sf) :
    Bicategory.IsFinal (twoFibreProductSquare F G) := by
  sorry

end FibredCategoryOver

end CategoryTheory
