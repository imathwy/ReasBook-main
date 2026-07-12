import Mathlib.Geometry.RingedSpace.OpenImmersion

open CategoryTheory

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

-- Semantic recall: `lean_leansearch` surfaced
-- `LocallyRingedSpace.IsOpenImmersion.isoRestrict` as the canonical image-open isomorphism for an
-- open immersion, with `LocallyRingedSpace.IsOpenImmersion.isoRestrict_hom_ofRestrict` giving the
-- factorization through the inclusion of the image open.

section

open LocallyRingedSpace.IsOpenImmersion

variable {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) [H : LocallyRingedSpace.IsOpenImmersion f]

local notation "Yf" => Y.restrict H.base_open
local notation "j" => Y.ofRestrict H.base_open

/-- A candidate identification of an open immersion with its image-open restriction is determined
by its composite with the inclusion of the image open. -/
theorem hom_eq_isoRestrict_hom_iff
    (f' : X ≅ Yf) :
    f'.hom = (isoRestrict f).hom ↔
      f'.hom ≫ j = f := by
  constructor
  · intro hf'
    simpa [hf'] using isoRestrict_hom_ofRestrict f
  · intro hf'
    apply (cancel_mono j).1
    calc
      f'.hom ≫ j = f := hf'
      _ = (isoRestrict f).hom ≫ j := by
        symm
        exact isoRestrict_hom_ofRestrict f

/-- Lemma 26.3.4: if `f : X ⟶ Y` is an open immersion of locally ringed spaces, then there is a
unique isomorphism from `X` to the canonical restriction of `Y` along the image-open embedding
`H.base_open` whose composite with the canonical inclusion into `Y` is `f`. -/
@[stacks 01HH]
theorem existsUnique_isoRestrict_of_isOpenImmersion
    : ∃! f' : X ≅ Yf, f'.hom ≫ j = f := by
  refine ⟨isoRestrict f, ?_, ?_⟩
  · simpa using isoRestrict_hom_ofRestrict f
  · intro f' hf'
    apply Iso.ext
    exact (hom_eq_isoRestrict_hom_iff f f').2 hf'

end

end AlgebraicGeometry.LocallyRingedSpace
