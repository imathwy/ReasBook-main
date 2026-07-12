import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Noetherian

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X Z : Scheme.{u}}

/- Semantic recall: `lean_leansearch` surfaced `AlgebraicGeometry.IsClosedImmersion` and
local Chapter 28/30 precedent represents inverse image by `Scheme.Modules.pullback` and invertible
modules by the canonical tensor-right equivalence owner.  The local Chapter 28 ampleness owner is
`Scheme.Modules.IsAmple`, but importing `stacks_project.Chap28.Definition_28_26_1` currently
forces Lake to rebuild upstream Chapter 17 nonvanishing-locus files before this target is
elaborated, where the read-only Lake state fails.  This item is therefore kept as a
source-faithful recall block rather than introducing a fake replacement for ampleness. -/

/- Lemma 30.17.5: for a closed immersion of Noetherian schemes inducing a homeomorphism on
underlying topological spaces, an invertible sheaf is ample if and only if its pullback is ample.

When the local ampleness owner is dependency-closed, the intended statement is the equivalence
between `Scheme.Modules.IsAmple L` and `Scheme.Modules.IsAmple ((Scheme.Modules.pullback i).obj L)`,
with invertibility of the pulled-back module supplied by the pullback tensor API. -/
#check fun (i : Z ⟶ X) ↦ IsClosedImmersion i
#check fun (X : Scheme.{u}) ↦ IsNoetherian X
#check fun (i : Z ⟶ X) ↦ IsHomeomorph i
#check fun (i : Z ⟶ X) ↦ Scheme.Modules.pullback i
#check fun [MonoidalCategory X.Modules] (L : X.Modules) ↦
  Functor.IsEquivalence (tensorRight L)

end AlgebraicGeometry.Scheme.Modules
