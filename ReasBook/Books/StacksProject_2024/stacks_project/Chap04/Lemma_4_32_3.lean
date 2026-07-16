import Mathlib
import StacksProject_2024.stacks_project.Chap04.Definition_4_31_2
import StacksProject_2024.stacks_project.Chap04.Lemma_4_32_5

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped Bicategory

universe u v

namespace CategoryTheory
namespace CategoryOver

/- Domain-style sampling for Lemma 4.32.3:
- primary domain: bicategorical `2`-fibre products in `Cat/C`;
- sampled owner-level declarations:
  `explicitTwoFibreProduct`,
  `explicitTwoFibreProductSquareOver`,
  `explicitTwoFibreProductLeftProjection`,
  `explicitTwoFibreProductRightProjection`,
  `CatCommSqOver.toBicategoricalSquare`,
  `Bicategory.IsFinal`;
- best owner abstraction: the source-facing over-`C` pullback owner is
  `explicitTwoFibreProductSquareOver`, already defined in Lemma 4.32.5 from the fibrewise
  pullback construction;
- primitive data: owned upstream by the explicit over-`C` pullback construction and its canonical
  categorical square;
- derived API kept here: only the bicategorical `2`-fibre-product property of the canonical square.

Source/core/bridge triage:
- `source-facing`: `explicitTwoFibreProductSquareOver F G`;
- `core/canonical`: `Bicategory.IsFinal ((explicitTwoFibreProductSquareOver F G).toBicategoricalSquare)`;
- `bridge/view`: `CatCommSqOver.toBicategoricalSquare`. -/

variable {C : Type u} [Category.{v} C]

section

variable {X Y S : BasedCategory C}
variable (F : X ⟶ S) (G : Y ⟶ S)

/-- Lemma 4.32.3: for morphisms `F : X ⟶ S` and `G : Y ⟶ S` in `Cat/C`, the explicit square
constructed from the fibrewise pullback owner is a strict `2`-fibre product. This is stated on
the canonical bridge from `CatCommSqOver` to the chapter bicategorical square owner. In
particular, `Cat/C` has `2`-fibre products. -/
theorem explicitTwoFibreProduct_isTwoFibreProduct :
    Bicategory.IsFinal ((explicitTwoFibreProductSquareOver F G).toBicategoricalSquare) := sorry

end

end CategoryOver
end CategoryTheory
