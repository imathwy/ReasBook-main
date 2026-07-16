import Mathlib
import StacksProject_2024.stacks_project.Chap26.Lemma_26_4_2
import StacksProject_2024.stacks_project.Chap26.Lemma_26_8_2

-- Declarations for this item will be appended below by the statement pipeline.

open CategoryTheory
open AlgebraicGeometry
open TopologicalSpace

noncomputable section

universe u

namespace AlgebraicGeometry

-- Semantic recall: `lean_leansearch` surfaced the scheme-level closed-immersion owner
-- `AlgebraicGeometry.IsClosedImmersion`, the affine quotient criterion
-- `AlgebraicGeometry.IsClosedImmersion.Spec_iff`, and the local construction
-- `LocallyRingedSpace.IsOpenImmersion.scheme`. Nearby Chapter 26 files use the locally-ringed
-- space owner `LocallyRingedSpace.IsClosedImmersion` and the restricted morphism
-- `LocallyRingedSpace.pullbackToPreimageOpenMorphism`.

/-- Lemma 26.10.1 (1): if a locally ringed space `Z` maps by a closed immersion to a scheme `X`,
then `Z` is a scheme; in particular, any closed subspace of a scheme is a scheme. -/
@[stacks 01IN]
theorem exists_scheme_iso_of_isClosedImmersion_toScheme
    {X : Scheme.{u}} {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ X.toLocallyRingedSpace)
    [_root_.AlgebraicGeometry.LocallyRingedSpace.IsClosedImmersion i] :
    ∃ Z' : Scheme.{u}, Nonempty (Z'.toLocallyRingedSpace ≅ Z) := sorry

/-- Lemma 26.10.1 (2): for a closed immersion of locally ringed spaces `i : Z -> X` into a
scheme, the kernel ideal sheaf of `\mathcal O_X -> i_*\mathcal O_Z` is quasi-coherent. -/
@[stacks 01IN]
theorem closedImmersionIdealSheaf_isQuasicoherent_toScheme
    {X : Scheme.{u}} {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ X.toLocallyRingedSpace)
    [_root_.AlgebraicGeometry.LocallyRingedSpace.IsClosedImmersion i] :
    (LocallyRingedSpace.closedImmersionIdealSheaf i).IsQuasicoherent := sorry

/-- Lemma 26.10.1 (3): on an affine open `U` of `X`, identified with `Spec R`, the restricted
closed immersion `i^{-1}(U) -> U` is identified over `Spec R` with `Spec(R/I) -> Spec R`,
and the corresponding kernel ideal sheaf is `\widetilde I`. -/
@[stacks 01IN]
theorem exists_ideal_affineOpen_quotient_tilde_kernel
    {X : Scheme.{u}} {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ X.toLocallyRingedSpace)
    [_root_.AlgebraicGeometry.LocallyRingedSpace.IsClosedImmersion i]
    (U : Opens X.toLocallyRingedSpace) (R : Type u) [CommRing R]
    (eU :
      X.toLocallyRingedSpace.restrict U.isOpenEmbedding ≅
        (Spec (CommRingCat.of R)).toLocallyRingedSpace) :
    ∃ I : Ideal R,
      Nonempty
          (Over.mk ((LocallyRingedSpace.pullbackToPreimageOpenMorphism i U) ≫ eU.hom) ≅
            Over.mk
              (Scheme.Hom.toLRSHom
                (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))))) ∧
        Nonempty
          (LocallyRingedSpace.closedImmersionIdealSheaf
              ((LocallyRingedSpace.pullbackToPreimageOpenMorphism i U) ≫ eU.hom) ≅
            (AlgebraicGeometry.tilde (ModuleCat.of R I) :
              (Spec (CommRingCat.of R)).Modules)) := sorry

/-- Lemma 26.10.1 (4): the restriction of the original kernel ideal sheaf to an affine open is
the kernel of the restricted closed immersion. -/
@[stacks 01IN]
theorem closedImmersionIdealSheaf_restrict_affineOpen_kernel
    {X : Scheme.{u}} {Z : LocallyRingedSpace.{u}}
    (i : Z ⟶ X.toLocallyRingedSpace)
    [_root_.AlgebraicGeometry.LocallyRingedSpace.IsClosedImmersion i]
    (U : Opens X.toLocallyRingedSpace) :
    Nonempty
      (((RingedSpace.Hom.pullback
          (X.toLocallyRingedSpace.ofRestrict U.isOpenEmbedding).toShHom).obj
          (LocallyRingedSpace.closedImmersionIdealSheaf i)) ≅
        LocallyRingedSpace.closedImmersionIdealSheaf
          (LocallyRingedSpace.pullbackToPreimageOpenMorphism i U)) := sorry

section

variable {X : Scheme.{u}}

local notation "ModX" => X.Modules
local notation "𝒪X" => (SheafOfModules.unit X.ringCatSheaf : ModX)

/-- Lemma 26.10.1 (5): for a scheme `X`, an ideal sheaf of `\mathcal O_X` is locally generated
by sections if and only if it is quasi-coherent. -/
@[stacks 01IN]
theorem schemeIdealSheaf_locallyGenerated_iff_isQuasicoherent
    (I : Subobject 𝒪X) :
    Nonempty ((Subobject.underlying.obj I : ModX).LocalGeneratorsData) ↔
      ((Subobject.underlying.obj I : ModX).IsQuasicoherent) := sorry

end

end AlgebraicGeometry
