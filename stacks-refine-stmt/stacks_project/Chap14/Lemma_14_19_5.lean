import Mathlib
import Mathlib.Tactic.Recall

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.Limits.IsLimit.OfNatIso
open CategoryTheory.SimplicialObject
open Opposite
open SimplexCategory.Truncated
open scoped Simplicial

noncomputable section

universe u v

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/- Domain-style sampling for Lemma 14.19.5:
- primary domain: representable cone functors and limits of the matching diagram for truncated
  simplicial objects;
- sampled owner API:
  `Functor.ranObjObjIsoLimit` (the earlier Chapter 14 limit owner for the same structured-arrow
  matching diagram),
  `Functor.cones`,
  `IsLimit.OfNatIso.limitCone`,
  `IsLimit.ofRepresentableBy`;
- best owner abstraction: the matching diagram
  `StructuredArrow.proj (op ⦋n + 1⦌) (inclusion n).op ⋙ U` together with its cone functor
  `matchingFamilyFunctor U`;
- primitive data: the truncated simplicial object `U` and the structured-arrow diagram indexing
  `(\Delta / [n + 1])_{\le n}^{opp}`;
- derived API: the matching-family presheaf and the canonical limit-cone theorem
  `IsLimit.ofRepresentableBy` specialized to that diagram.

Source/core/bridge triage:
- `source-facing`: the matching-family functor of `U`;
- `core/canonical`: `Functor.cones`, `IsLimit.ofRepresentableBy`, and
  `IsLimit.OfNatIso.limitCone`;
- `bridge/view`: the numbered lemma is just the owner theorem
  `IsLimit.ofRepresentableBy` applied to `matchingFamilyFunctor U`, so no separate bridge theorem
  should survive.
-/

section

variable {n : ℕ}

/-- The structured-arrow indexing category for the matching diagram in degree `n + 1`. -/
abbrev matchingIndex (n : ℕ) :=
  StructuredArrow (op ⦋n + 1⦌) (SimplexCategory.Truncated.inclusion n).op

/-- The source matching-family functor of Lemma 14.19.5, expressed canonically as the cone functor
on the matching diagram. -/
abbrev matchingFamilyFunctor (U : SimplicialObject.Truncated C n) :=
  (StructuredArrow.proj (op ⦋n + 1⦌) (SimplexCategory.Truncated.inclusion n).op ⋙ U).cones

/- Lemma 14.19.5: if the matching-family functor of `U` is representable by `U_succ`, then the
canonical cone on the structured-arrow matching diagram with cone point `U_succ` is a limit cone.
This is the direct owner theorem `IsLimit.ofRepresentableBy`, specialized to the cone functor
`matchingFamilyFunctor U`. -/
recall IsLimit.ofRepresentableBy

#check (IsLimit.ofRepresentableBy :
  {U : SimplicialObject.Truncated C n} → {U_succ : C} →
    (hrep : (matchingFamilyFunctor U).RepresentableBy U_succ) →
      IsLimit (limitCone hrep))

end

end CategoryTheory
