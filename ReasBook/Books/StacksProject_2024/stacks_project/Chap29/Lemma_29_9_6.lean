import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open TopologicalSpace

universe u

namespace AlgebraicGeometry

-- Source/core/bridge triage:
-- - `source-facing`: the commutative-triangle descent statement of Lemma 29.9.6.
-- - `core/canonical`: quasi-compactness descends along a surjective left factor in a composite.
-- - `bridge/view`: the triangle statement is a thin rewrite of the core theorem along
--   `hcomm : f ≫ q = p`.

namespace QuasiCompact

/-- A quasi-compact composite with surjective left factor has quasi-compact right factor. -/
theorem of_comp_surjective
    {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    [Surjective f] (hfg : QuasiCompact (f ≫ g)) : QuasiCompact g := by
  constructor
  intro U hU hU'
  have hpre : IsCompact ((f ≫ g) ⁻¹' U) :=
    hfg.isCompact_preimage U hU hU'
  have himage : f '' ((f ≫ g) ⁻¹' U) = g ⁻¹' U := by
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp, Set.image_preimage_eq]
    exact f.surjective
  rw [← himage]
  exact hpre.image f.continuous

end QuasiCompact

/-- Lemma 29.9.6: in a commutative triangle of scheme morphisms `X -f-> Y -q-> Z` and `X -p-> Z`,
if `f` is surjective and `p` is quasi-compact, then `q` is quasi-compact. -/
@[stacks 04ZD]
theorem quasiCompact_of_surjective_of_comp_eq
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z)
    [Surjective f] (hp : QuasiCompact p) (hcomm : f ≫ q = p) : QuasiCompact q := by
  exact QuasiCompact.of_comp_surjective (hcomm.symm ▸ hp)

end AlgebraicGeometry
