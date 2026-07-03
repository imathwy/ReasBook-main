import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.ObjectProperty
open Opposite
open scoped ZeroObject

universe w v u

namespace CategoryTheory

section

/- Domain-style sampling for Definition 13.37.1:
- primary domain: object predicates in preadditive categories defined through the represented
  functor `Hom(K,-)`, together with the full subcategories cut out by such predicates;
- sampled owner declarations:
  `HasCoproducts`,
  `preadditiveCoyoneda.obj`,
  `preservesColimitsOfShape_of_equiv`,
  `preservesColimitsOfShape_of_isZero`,
  `ObjectProperty.FullSubcategory`;
- best owner abstraction: the source-facing owner is the reusable object predicate
  `IsCompactObject`, while the compact subcategory `D_c` should be only the direct full
  subcategory attached to that predicate, matching the existing project pattern where source
  predicates own the mathematics and full subcategories are derived views;
  `preadditiveCoyoneda.obj (op K)` together with preservation of ambient
  `Type (max u v)`-indexed discrete coproduct shapes in a category with arbitrary coproducts;
  preservation for smaller discrete shapes via `Shrink`/equivalence, and the source-facing
  full-subcategory notation `D_c(D)`;
- source/core/bridge triage:
  `source-facing`: `IsCompactObject K`;
  `core/canonical`: `PreservesColimitsOfShape (Discrete I) (preadditiveCoyoneda.obj (op K))`;
  `bridge/view`: the direct full subcategory `(IsCompactObject : ObjectProperty D).FullSubcategory`,
    used with the source notation `D_c(D)`.

There is no need for a second public owner-level wrapper `compactObjectProperty`, `compactObjects`,
or any other owner parallel to `IsCompactObject`: the predicate `IsCompactObject` is the owner,
and the compact subcategory is only its direct object-property full subcategory bridge/view. -/

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasCoproducts.{max u v} D]

/-- Definition 13.37.1: in the source setting of an additive category with arbitrary direct sums,
an object `K` is compact when the preadditive Hom functor `Hom(K, -)` preserves arbitrary
coproducts. In Lean, the owner is phrased through preservation of `Type (max u v)`-indexed
discrete colimits by `preadditiveCoyoneda.obj (op K)`, with smaller shapes recovered by shrink. -/
@[mk_iff isCompactObject_iff]
class IsCompactObject (K : D) : Prop where
  preservesCoproducts (I : Type (max u v)) :
    PreservesColimitsOfShape (Discrete I) (preadditiveCoyoneda.obj (op K))

/-- A compact object represents a functor preserving coproducts of any fixed small shape. -/
instance (K : D) [hK : IsCompactObject K] (I : Type w) [UnivLE.{w, max u v}] :
    PreservesColimitsOfShape (Discrete I) (preadditiveCoyoneda.obj (op K)) :=
  by
    let h :
        PreservesColimitsOfShape (Discrete (Shrink.{max u v} I))
          (preadditiveCoyoneda.obj (op K)) :=
      hK.preservesCoproducts (Shrink.{max u v} I)
    exact
      preservesColimitsOfShape_of_equiv
        (Discrete.equivalence (equivShrink.{max u v} I)).symm
        (preadditiveCoyoneda.obj (op K))

/-- The source notation `D_c(D)` for the full subcategory of compact objects. -/
scoped notation "D_c(" D:arg ")" =>
  ObjectProperty.FullSubcategory (IsCompactObject : ObjectProperty D)

end

section

variable {D : Type u} [Category.{v} D] [HasZeroObject D] [Preadditive D]
  [HasCoproducts.{max u v} D]

/-- The zero object is a compact object. -/
instance isCompactObject_zero : IsCompactObject (0 : D) where
  preservesCoproducts I := by
    let F := preadditiveCoyoneda.obj (op (0 : D))
    have hzero : IsZero F := by
      dsimp [F]
      exact Functor.map_isZero preadditiveCoyoneda (IsZero.op (isZero_zero D))
    simpa using
      F.preservesColimitsOfShape_of_isZero hzero (Discrete I)

end

end CategoryTheory
