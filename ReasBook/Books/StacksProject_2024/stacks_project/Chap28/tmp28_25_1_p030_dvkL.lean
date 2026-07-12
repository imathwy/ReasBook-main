import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory Limits Opposite
open AlgebraicGeometry
open PrimeSpectrum
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {A : Type u} [CommRing A]

-- Semantic recall: `lean_leansearch` surfaced `ModuleCat.tilde` and the affine `Spec`/`Γ` API; the
-- concrete owner here is therefore the actual sheaf of `A`-modules
-- `AlgebraicGeometry.modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)` over `Spec A`, together
-- with a chosen finite basic-open cover coming from `I.FG`.

/-- The canonical sheaf of `A`-modules attached to `\widetilde M` on `Spec(A)`. -/
private noncomputable def tildeSheaf (M : ModuleCat A) :
    TopCat.Sheaf (ModuleCat (CommRingCat.of A)) (Spec (.of A)) :=
  AlgebraicGeometry.modulesSpecToSheaf.obj (AlgebraicGeometry.tilde M)

private noncomputable def tildePresheaf (M : ModuleCat A) :
    TopCat.Presheaf (ModuleCat (CommRingCat.of A)) (Spec (.of A)) :=
  (tildeSheaf M).1

end AlgebraicGeometry.Scheme.Modules
