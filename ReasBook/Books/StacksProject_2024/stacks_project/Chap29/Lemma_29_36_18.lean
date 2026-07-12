import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry
open CategoryTheory
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the canonical scheme morphism owner
-- `AlgebraicGeometry.Etale`/`IsEtale` and the postcomposition cancellation API for étale maps.
-- Local Chapter 29 files state étaleness directly as `Etale f`.

/-- Lemma 29.36.18: let `f : X ⟶ Y` be a morphism of schemes over `S`. If `X` and `Y`
are étale over `S`, then `f` is étale. -/
@[stacks 02GW]
theorem etale_of_etale_over {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y)
    (hX : Etale X.hom) (hY : Etale Y.hom) :
    Etale f.left := sorry

end AlgebraicGeometry
