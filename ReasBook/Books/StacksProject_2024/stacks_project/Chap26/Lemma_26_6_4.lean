import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

-- Semantic recall: `lean_leansearch` surfaced `ΓSpec.locallyRingedSpaceAdjunction` and the
-- fully faithful affine-spectrum owner `Spec`; for an affine target `Y`, the source map
-- `Mor(X, Y) → Hom(Γ(Y), Γ(X))` is the global-sections map on `Y.toLocallyRingedSpace`,
-- with bijectivity supplied by the `Γ ⊣ Spec` adjunction after identifying `Y` with `Spec Γ(Y)`.

/-- Lemma 26.6.4: if `X` is a locally ringed space and `Y` is an affine scheme, then sending a
morphism `f : X ⟶ Y.toLocallyRingedSpace` to the induced map on global sections
`Γ(Y, ⊤) ⟶ Γ(X, ⊤)` is bijective. -/
@[stacks 01I1]
theorem bijective_homToAffineSchemeGlobalSectionsMap
    {X : LocallyRingedSpace.{u}} {Y : Scheme.{u}} [IsAffine Y] :
    Function.Bijective (fun f : X ⟶ Y.toLocallyRingedSpace ↦
      (LocallyRingedSpace.Γ.map f.op :
        Scheme.Γ.obj (op Y) ⟶ LocallyRingedSpace.Γ.obj (op X))) := sorry

end AlgebraicGeometry.LocallyRingedSpace
