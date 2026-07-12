import StacksProject_2024.Chap29.Lemma_29_26_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace AlgebraicGeometry
namespace Scheme

/- Semantic recall / analogue check:
- `lean_leansearch` recalled `isClosed_connectedComponent`, `AlgebraicGeometry.IsClosedImmersion`,
  and `AlgebraicGeometry.Flat.generalizingMap`.
- Lemma `29.26.1` is already formalized as `flat_closed_subscheme_support_bijective`, so the
  source-facing entry below is stated on the canonical owner `_root_.connectedComponent x` rather
  than by introducing a wrapper for a chosen witness.
-/

/-- Definition 29.26.3: for a scheme `X` and a point `x : X`, there exists a unique ideal sheaf
data whose associated closed immersion is flat and whose underlying closed subset is the connected
component of `x`. This is the canonical scheme structure on that connected component. -/
@[stacks 04PX]
theorem existsUnique_connectedComponentIdeal
    (X : Scheme.{u}) (x : X) :
    ∃! I : X.IdealSheafData,
      Flat I.subschemeι ∧ (I.support : Set X) = _root_.connectedComponent x := sorry

/-- A flat closed subscheme of `X` supported on the connected component of `x` is uniquely
determined by that support. -/
@[stacks 04PX]
theorem eq_of_flat_subscheme_support_eq_connectedComponent
    {X : Scheme.{u}} {x : X} {I J : X.IdealSheafData}
    (hI : Flat I.subschemeι) (hJ : Flat J.subschemeι)
    (hI_support : (I.support : Set X) = _root_.connectedComponent x)
    (hJ_support : (J.support : Set X) = _root_.connectedComponent x) :
    I = J := sorry

end Scheme
end AlgebraicGeometry
