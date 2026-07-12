import Mathlib
import StacksProject_2024.Chap29.Definition_29_50_1

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry
namespace Scheme.Hom

/- Semantic recall: `lean_leansearch` returned the canonical open-restriction API
`AlgebraicGeometry.morphismRestrict` and the instance `instIsIsoSchemeMorphismRestrict`.
Local Chapter 29 precedent uses `IsBirational` for birational morphisms and `f ∣_ V` for the
preimage of an open subscheme. The tag evidence is consistent: item tag `0BAJ` matches the source
URL tag `0BAJ`. -/

/-- Lemma 29.51.6: let `f : X ⟶ Y` be a birational morphism of schemes with finitely many
irreducible components. If `f` is quasi-compact or separated, and if either `f` is locally of
finite type with `Y` reduced or `f` is locally of finite presentation, then there is a dense open
`V ⊆ Y` such that the restriction `f⁻¹(V) ⟶ V` is an isomorphism. -/
@[stacks 0BAJ]
theorem exists_dense_open_isIso_restrict_of_isBirational
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Finite (irreducibleComponents X)] [Finite (irreducibleComponents Y)]
    [IsBirational f]
    (hqc_or_sep : QuasiCompact f ∨ IsSeparated f)
    (hfiniteType_or_finitePresentation :
      (LocallyOfFiniteType f ∧ IsReduced Y) ∨ LocallyOfFinitePresentation f) :
    ∃ V : {V : Y.Opens // Dense (V : Set Y)}, IsIso (f ∣_ (V : Y.Opens)) := sorry

end Scheme.Hom
end AlgebraicGeometry
