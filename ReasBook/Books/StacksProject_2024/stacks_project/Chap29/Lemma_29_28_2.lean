import Mathlib
import StacksProject_2024.stacks_project.Chap29.Definition_29_25_1
import StacksProject_2024.stacks_project.Chap29.Lemma_29_28_4

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits

noncomputable section

universe u

namespace AlgebraicGeometry

namespace Scheme.Hom

/- Semantic recall:
- `lean_leansearch` surfaced the canonical scheme-fiber owners `Scheme.Hom.fiber`,
  `Scheme.Hom.stalkMap`, and the flatness owner `AlgebraicGeometry.Flat.stalkMap`;
- local Chapter 29 precedent already packages the source-side pointwise fiber dimension as
  `Scheme.Hom.fiberDimensionAt` and ordinary stalk flatness as `Scheme.Hom.flatAt`.
-/

variable {X Y S : Scheme.{u}}

/-- The commutativity needed to map the fiber of `f ≫ g` over `s` to the fiber of `g` over `s`. -/
theorem compFiberToBaseFiber_condition (f : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    Scheme.Hom.fiberι (f ≫ g) s ≫ f ≫ g =
      Scheme.Hom.fiberToSpecResidueField (f ≫ g) s ≫ S.fromSpecResidueField s := sorry

/-- The canonical morphism from the fiber of `f ≫ g` over `s` to the fiber of `g` over `s`. -/
def compFiberToBaseFiber (f : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    Scheme.Hom.fiber (f ≫ g) s ⟶ Scheme.Hom.fiber g s :=
  pullback.lift
    (Scheme.Hom.fiberι (f ≫ g) s ≫ f)
    (Scheme.Hom.fiberToSpecResidueField (f ≫ g) s)
    (compFiberToBaseFiber_condition f g s)

/-- The canonical map from the composite fiber to the base fiber preserves the structure map to
`Spec κ(s)`. -/
theorem compFiberToBaseFiber_fiberToSpecResidueField (f : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    compFiberToBaseFiber f g s ≫ Scheme.Hom.fiberToSpecResidueField g s =
      Scheme.Hom.fiberToSpecResidueField (f ≫ g) s := sorry

/-- The canonical map from the composite fiber to the base fiber sends the structural inclusion to
the original morphism `f`. -/
theorem compFiberToBaseFiber_fiberι (f : X ⟶ Y) (g : Y ⟶ S) (s : S) :
    compFiberToBaseFiber f g s ≫ Scheme.Hom.fiberι g s =
      Scheme.Hom.fiberι (f ≫ g) s ≫ f := sorry

/-- Lemma 29.28.2 (1): for locally finite type morphisms `f : X ⟶ Y` and `g : Y ⟶ S`, the local
dimension of the fiber of `f ≫ g` at `x` is at most the sum of the local dimensions of the fiber
of `f` at `x` and of the fiber of `g` at `f x`. -/
theorem fiberDimensionAt_comp_le
    (f : X ⟶ Y) (g : Y ⟶ S) [LocallyOfFiniteType f] [LocallyOfFiniteType g] (x : X) :
    (f ≫ g).fiberDimensionAt x ≤ f.fiberDimensionAt x + g.fiberDimensionAt (f x) := sorry

/-- Lemma 29.28.2 (2): in the same situation, equality holds if the local ring
`\mathcal O_{X_s, x}` is flat over `\mathcal O_{Y_s, y}`, expressed as flatness of the stalk map
of the canonical morphism `(f ≫ g).fiber s ⟶ g.fiber s` at the point `x`, where `y = f x` and
`s = g y`. -/
theorem fiberDimensionAt_comp_eq_add_of_flatAt_compFiberToBaseFiber
    (f : X ⟶ Y) (g : Y ⟶ S) [LocallyOfFiniteType f] [LocallyOfFiniteType g] (x : X)
    (hflat :
      Scheme.Hom.flatAt
        (compFiberToBaseFiber f g (g (f x)))
        (Scheme.Hom.asFiber (f ≫ g) x)) :
    (f ≫ g).fiberDimensionAt x = f.fiberDimensionAt x + g.fiberDimensionAt (f x) := sorry

/-- Lemma 29.28.2 (3): the equality above holds in particular if the ordinary stalk map
`\mathcal O_{Y, y} → \mathcal O_{X, x}` is flat at `x`, where `y = f x`. -/
theorem fiberDimensionAt_comp_eq_add_of_flatAt
    (f : X ⟶ Y) (g : Y ⟶ S) [LocallyOfFiniteType f] [LocallyOfFiniteType g] (x : X)
    (hflat : Scheme.Hom.flatAt f x) :
    (f ≫ g).fiberDimensionAt x = f.fiberDimensionAt x + g.fiberDimensionAt (f x) := sorry

end Scheme.Hom

end AlgebraicGeometry
