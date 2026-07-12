import Mathlib
import StacksProject_2024.Chap29.Lemma_29_35_13

-- Declarations for this item will be appended below by the statement pipeline.

open AlgebraicGeometry CategoryTheory

universe u

namespace AlgebraicGeometry

/- Semantic recall / API check:
- `lean_leansearch` surfaced `FormallyUnramified.isOpenImmersion_diagonal`, matching the
  proof route through the open diagonal recorded locally in `Lemma_29_35_13`.
- Local Chapter 29 precedent uses `Unramified` for scheme morphisms and expresses agreement on an
  open neighbourhood by an open subscheme `U : X.Opens` with `U.ι ≫ f = U.ι ≫ g`.
- The Stacks tag evidence is consistent: `04HB` is the source URL tag for `Lemma 29.35.17`.
-/

section

variable {S X Y : Scheme.{u}} {fX : X ⟶ S} {fY : Y ⟶ S}
variable {f g : X ⟶ Y} {x : X} {y : Y}

/-- Lemma 29.35.17: for two morphisms `f, g : X ⟶ Y` over `S`, if the structure morphism
`Y ⟶ S` is unramified, `f` and `g` have the same value `y` at `x`, and the induced
residue-field maps `κ(y) ⟶ κ(x)` agree, then `f` and `g` agree on an open neighbourhood of `x`. -/
@[stacks 04HB]
theorem exists_open_eq_of_unramified_of_residueFieldMap_eq
    [Unramified fY]
    (hf_over : f ≫ fY = fX) (hg_over : g ≫ fY = fX)
    (hfxy : f x = y) (hgxy : g x = y)
    (hres :
      (Scheme.residueFieldCongr hfxy).inv ≫ f.residueFieldMap x =
        (Scheme.residueFieldCongr hgxy).inv ≫ g.residueFieldMap x) :
    ∃ U : X.Opens, x ∈ U ∧ U.ι ≫ f = U.ι ≫ g := sorry

end

end AlgebraicGeometry
