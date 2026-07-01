import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open scoped CategoryTheory.ObjectProperty

noncomputable section

universe v u

namespace CategoryTheory.ObjectProperty

/-
Domain-style sampling for Definition `13.6.7`:
- primary domain: Verdier localization of a triangulated category by the cone-defined morphism
  property attached to a triangulated object property;
- sampled owner declarations:
  `ObjectProperty.trW`,
  `MorphismProperty.Localization`,
  `MorphismProperty.Q`,
  `Functor.IsLocalization`;
- best owner abstraction: for a triangulated object property `P`, the quotient is owned by the
  canonical localization API of the morphism property `P.trW`, while the source-facing bridge
  layer should expose the standard Verdier quotient notation `D / P` and quotient functor
  `P.trW.Q`;
- primitive data: the object property `P`, from which the Verdier morphism property `P.trW` is
  derived;
- derived API: the quotient category `D / P`, the quotient functor `P.trW.Q`, and the owner fact
  that `P.trW.Q` localizes at `P.trW`;
- source/core/bridge triage:
  `source-facing`: the textbook quotient category `D / P` of `D` by the triangulated
    subcategory `P`, together with the quotient functor `P.trW.Q`;
  `core/canonical`: `P.trW.Localization`, `P.trW.Q`, and `Functor.IsLocalization`;
  `bridge/view`: the identification of the textbook quotient with localization at the cone-defined
    morphism property `P.trW`.

Definition `13.6.7` is therefore a `bridge/view` item: it should recall the canonical
localization owner through the source-facing Verdier quotient surface rather than introduce
parallel local owners.
-/

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D]

/-- The Verdier quotient `D / P` is the canonical localization `P.trW.Localization`. -/
scoped instance verdierQuotientHDiv : HDiv (Type u) (ObjectProperty D) (Type u) where
  hDiv _ P := P.trW.Localization

scoped instance verdierQuotientCategory (P : ObjectProperty D) : Category (D / P) :=
  inferInstanceAs (Category P.trW.Localization)

end

section

variable {D : Type u} [Category.{v} D] [Limits.HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, Functor.Additive (shiftFunctor D n)] [Pretriangulated D] [IsTriangulated D]
  (P : ObjectProperty D) [P.IsTriangulated]

instance verdierQuotientFunctorIsLocalization :
    (P.trW.Q : D ⥤ D / P).IsLocalization P.trW := by
  exact Functor.q_isLocalization P.trW

noncomputable instance verdierQuotientPreadditive : Preadditive (D / P) := by
  change Preadditive P.trW.Localization
  infer_instance

noncomputable instance verdierQuotientFunctorAdditive : (P.trW.Q : D ⥤ D / P).Additive := by
  infer_instance

noncomputable instance verdierQuotientHasZeroObject : Limits.HasZeroObject (D / P) := by
  change Limits.HasZeroObject P.trW.Localization
  infer_instance

noncomputable instance verdierQuotientHasShift : HasShift (D / P) ℤ := by
  change HasShift P.trW.Localization ℤ
  infer_instance

noncomputable instance verdierQuotientFunctorCommShift : (P.trW.Q : D ⥤ D / P).CommShift ℤ := by
  infer_instance

noncomputable instance verdierQuotientShiftAdditive (n : ℤ) :
    Functor.Additive (shiftFunctor (D / P) n) := by
  change Functor.Additive (shiftFunctor P.trW.Localization n)
  infer_instance

noncomputable instance verdierQuotientPretriangulated : Pretriangulated (D / P) := by
  change Pretriangulated P.trW.Localization
  infer_instance

noncomputable instance verdierQuotientFunctorIsTriangulated :
    (P.trW.Q : D ⥤ D / P).IsTriangulated := by
  infer_instance

noncomputable instance verdierQuotientIsTriangulated : IsTriangulated (D / P) := by
  change IsTriangulated P.trW.Localization
  infer_instance

/- Definition 13.6.7: the source-facing Verdier quotient of `D` by `P` is the canonical
localization `P.trW.Localization` of the cone-defined morphism property `P.trW`. -/
#check (D / P)

/- Companion recall: the quotient functor to this Verdier quotient is the canonical localization
functor on `P.trW`. -/
#check
  (P.trW.Q : D ⥤ D / P)

/- Companion recall: the quotient functor on `P.trW` localizes at the Verdier morphism
property `P.trW`. -/
#check (Functor.q_isLocalization P.trW)

end

end CategoryTheory.ObjectProperty
