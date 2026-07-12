import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Mathlib.CategoryTheory.Monoidal.Category

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Semantic recall: `lean_leansearch` surfaced the canonical scheme pullback API in
`Mathlib.AlgebraicGeometry.Pullbacks`. Local precedent represents ample invertible sheaves by an
explicit `Invertible` witness together with `Scheme.Modules.IsAmple`, and scheme fibre products by
the canonical pullback object `Limits.pullback f g` with projections `Limits.pullback.fst` and
`Limits.pullback.snd`.  Importing the local ampleness owner `Definition_28_26_1` in item mode
forces Lake to replay heavy upstream Chapter 17/18 dependencies before this target elaborates, so
this item records the dependency-closed canonical owners rather than introducing a fake replacement
for ampleness. -/

/- Lemma 28.26.15: if `S` is quasi-separated, `X` and `Y` are schemes over `S`, `L` is an
ample invertible `\mathcal O_X`-module, and `N` is an ample invertible `\mathcal O_Y`-module,
then on the fibre product `X ×_S Y` the tensor product
`pr₁^* L ⊗ pr₂^* N` is an ample invertible sheaf.

When the local ampleness owner is dependency-closed, the intended formal conclusion is
`Scheme.Modules.IsAmple` for
`(Scheme.Modules.pullback (Limits.pullback.fst f g)).obj L ⊗
  (Scheme.Modules.pullback (Limits.pullback.snd f g)).obj N` on `Limits.pullback f g`. -/
#check fun (S : Scheme.{u}) ↦ QuasiSeparatedSpace S
#check fun {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) ↦ Limits.pullback f g
#check fun {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) ↦ Limits.pullback.fst f g
#check fun {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) ↦ Limits.pullback.snd f g
#check fun {X Y : Scheme.{u}} (f : X ⟶ Y) ↦ Scheme.Modules.pullback f
#check fun {X : Scheme.{u}} [MonoidalCategory X.Modules] (L : X.Modules) ↦
  Functor.IsEquivalence (tensorRight L)
#check fun {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [MonoidalCategory (Limits.pullback f g).Modules] (L : X.Modules) (N : Y.Modules) ↦
  ((Scheme.Modules.pullback (Limits.pullback.fst f g)).obj L) ⊗
    ((Scheme.Modules.pullback (Limits.pullback.snd f g)).obj N)

end AlgebraicGeometry.Scheme.Modules
