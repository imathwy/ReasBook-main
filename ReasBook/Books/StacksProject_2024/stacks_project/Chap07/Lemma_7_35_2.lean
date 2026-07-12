import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory

universe w v u

namespace CategoryTheory

open GrothendieckTopology

section

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
variable [LocallySmall.{w} C]

/- Domain-style sampling for Lemma 7.35.2:
- primary domain: points of Grothendieck sites, their localization to slice sites, and comparison
  of points under the localization functor `Over.forget U`;
- sampled owner API:
  `GrothendieckTopology.Point.over`,
  `GrothendieckTopology.Point.map`,
  `GrothendieckTopology.Point.sheafFiberMapIso`,
  `Over.mkIdTerminal`;
- best owner abstraction: the site-point owner `GrothendieckTopology.Point`, with the localized
  point `p.over x` and the image point `q.map (Over.forget U) J` as derived canonical
  constructions.

Source/core/bridge triage:
- `source-facing`: the classification of points of `(C / U, J.over U)` lying over a fixed point
  `p` by elements `x : p.fiber.obj U`;
- `core/canonical`: the owners `Point.over`, `Point.map`, the induced comparison of stalk functors
  via `Point.sheafFiberMapIso`, and the terminal object `Over.mk (𝟙 U)` supplied by
  `Over.mkIdTerminal`;
- `bridge/view`: the theorem below, which translates the source statement into the canonical point
  owners without introducing any parallel wrapper API.

Primitive data are only the point `p`, the object `U`, and the localized-site point `q`. The
fiber element `x : p.fiber.obj U` is derived by evaluating at the terminal object of `Over U`,
while the comparison with `p.over x` is derived from the owner-level localized-point construction.
-/
-- Proof sketch: if `q` lies over `p`, apply the defining isomorphism
-- `(q.map (Over.forget U) J) ≅ p` to the distinguished point of the terminal object
-- `Over.mk (𝟙 U)` (owned by `Over.mkIdTerminal`); this produces the corresponding element
-- `x : p.fiber.obj U`. Then compare the induced fiber functors using the owner-level point
-- constructions `Point.map` and `Point.over` to show that `q` is isomorphic to `p.over x`.
-- Conversely, Lemma `7.35.1` shows that every `p.over x` maps back to a point lying over `p`, and
-- uniqueness again comes from evaluating at the terminal object of `Over U`.
/-- Lemma 7.35.2: for a point `p` of `(C, J)`, an object `U : C`, and a point `q` of the
localized site `(C/U, J.over U)`, the point `q` lies over `p` precisely when there is a unique
element `x : p.fiber.obj U` such that `q` is isomorphic to the canonical localized point
`p.over x`. This is the site-theoretic form of the bijection between points of `C/U` over `p`
and elements of `u(U) = p.fiber.obj U`. -/
theorem localized_point_lies_over_iff_unique_fiber_element
    (p : Point.{w} J) (U : C) (q : Point.{w} (J.over U)) :
    IsIsomorphic (q.map (Over.forget U) J) p ↔
      ∃! x : p.fiber.obj U, IsIsomorphic q (p.over x) := sorry

end

end CategoryTheory
