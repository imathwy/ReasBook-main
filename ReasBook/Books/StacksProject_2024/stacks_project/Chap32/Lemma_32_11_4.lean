import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Z : Scheme.{u}}

/- Semantic recall: `lean_leansearch` found `AlgebraicGeometry.IsClosedImmersion` as a canonical
scheme-side owner for the closed immersion hypothesis.  Local Chapter 28 precedent uses
`Scheme.Modules.IsAmple`, `Scheme.Modules.Invertible`, and the pullback notation `i^*` for
ampleness of invertible sheaves, but importing that local ampleness owner currently forces Lake to
rebuild upstream Chapter 17 nonvanishing-locus files before this target is elaborated, where the
read-only Lake state fails.  This item is therefore kept as a source-faithful recall block rather
than introducing a fake replacement for ampleness. -/

/- Lemma 32.11.4: let `i : Z ⟶ X` be a closed immersion of schemes inducing a homeomorphism of
underlying topological spaces. For an invertible sheaf `L` on `X`, the pullback `i^* L` is ample on
`Z` if and only if `L` is ample on `X`.

When the local ampleness owner is dependency-closed, the intended statement is the equivalence
between `Scheme.Modules.IsAmple ((Scheme.Modules.pullback i).obj L)` and
`Scheme.Modules.IsAmple L`, with invertibility represented by the local
`Scheme.Modules.Invertible` bridge from Definition 28.26.1. -/
#check fun (i : Z ⟶ X) ↦ IsClosedImmersion i
#check fun (i : Z ⟶ X) ↦ IsHomeomorph i
#check fun (i : Z ⟶ X) ↦ Scheme.Modules.pullback i
#check fun [MonoidalCategory X.Modules] (L : X.Modules) ↦
  Functor.IsEquivalence (tensorRight L)

end AlgebraicGeometry.Scheme.Modules
