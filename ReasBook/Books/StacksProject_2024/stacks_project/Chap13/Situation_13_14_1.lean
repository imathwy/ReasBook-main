import Mathlib.Tactic.Recall
import StacksProject_2024.Chap04.Definition_4_27_20
import StacksProject_2024.Chap13.Definition_13_3_3
import StacksProject_2024.Chap13.Definition_13_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory.MorphismProperty

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

/-
Domain-style sampling:
- primary domain: exact-localization situations for triangulated categories, assembled from the
  chapter owners in Definitions `13.3.3`, `4.27.20`, and `13.5.1`;
- inspected canonical declarations in that domain:
  `Functor.CommShift ℤ`,
  `Functor.IsTriangulated`,
  `MorphismProperty.IsSaturatedMultiplicativeSystem`,
  `MorphismProperty.IsCompatibleWithTriangulation`;
- best owner abstraction: no new bundled “situation” structure is mathematically present here.
  Situation `13.14.1` is just the simultaneous availability of those four existing owners for the
  pair `(F, S)`.

Primitive-vs-derived split:
- primitive data: exactly those four owner classes, with no extra situation wrapper;
- derived API: all localization and derived-functor consequences proved later in Chapter `13`,
  which should take these owner assumptions directly rather than through a parallel wrapper.

Source/core/bridge triage:
- `source-facing`: the textbook setup consisting of an exact functor `F` and a saturated
  triangulation-compatible multiplicative system `S`;
- `core/canonical`: the four owner classes listed above;
- `bridge/view`: downstream constructions such as the restricted derived functors and induced
  triangulated-localization structures.
-/

section

variable {D : Type u₁} {D' : Type u₂}
  [Category.{v₁} D] [Category.{v₂} D']
  [HasShift D ℤ] [HasShift D' ℤ]

/- Situation 13.14.1 begins with the shift-compatibility datum in the exact-functor owner from
Definition `13.3.3`. -/
recall Functor.CommShift

section

variable [Limits.HasZeroObject D] [Limits.HasZeroObject D']
  [Preadditive D] [Preadditive D']
  [∀ n : ℤ, (shiftFunctor D n).Additive]
  [∀ n : ℤ, (shiftFunctor D' n).Additive]
  [Pretriangulated D] [Pretriangulated D']
  (F : D ⥤ D') [F.CommShift ℤ]

/- Once the shift-compatibility data is fixed, the exactness clause in Situation `13.14.1` is
the canonical owner `Functor.IsTriangulated`. -/
recall Functor.IsTriangulated

end
end

section

variable {D : Type u₁} [Category.{v₁} D]
  (S : MorphismProperty D)

/- The localization class in Situation `13.14.1` is required to be a saturated multiplicative
system in the sense of Definition `4.27.20`. -/
recall IsSaturatedMultiplicativeSystem

section

variable [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]

/- The triangulation-compatibility clause in Situation `13.14.1` is the canonical owner from
Definition `13.5.1`. -/
recall IsCompatibleWithTriangulation

end
end

end CategoryTheory
