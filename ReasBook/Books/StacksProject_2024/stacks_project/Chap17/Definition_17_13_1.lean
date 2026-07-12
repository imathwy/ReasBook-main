import Mathlib
import StacksProject_2024.Chap17.Definition_17_13_1_Owner

open CategoryTheory TopCat TopCat.Sheaf
open AlgebraicGeometry
open TopCat.Presheaf

noncomputable section

universe u

namespace AlgebraicGeometry.RingedSpace

section Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

local notation "φf" => f.toShHom

/-- Bridge/view: for morphisms of schemes, the source-facing ringed-space closed-immersion owner
refines to mathlib's canonical scheme-level `AlgebraicGeometry.IsClosedImmersion`. -/
instance scheme_isClosedImmersion_of_ringedSpace_isClosedImmersion
    [RingedSpace.IsClosedImmersion φf] : AlgebraicGeometry.IsClosedImmersion f where
  isClosedEmbedding := by
    let hf : RingedSpace.IsClosedImmersion φf := inferInstance
    simpa using hf.isClosedEmbedding
  stalkMap_surjective x := by
    let hf : RingedSpace.IsClosedImmersion φf := inferInstance
    let hloc :
        Sheaf.IsLocallySurjective (Hom.commRingSheafPushforwardMap φf) :=
      inferInstance
    have hsurj :
        Function.Surjective
          ((TopCat.Presheaf.stalkFunctor CommRingCat (f x)).map
            (Hom.commRingSheafPushforwardMap φf).hom) :=
      (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks
        (Hom.commRingSheafPushforwardMap φf).hom).1
        (show TopCat.Presheaf.IsLocallySurjective
            (Hom.commRingSheafPushforwardMap φf).hom from hloc) (f x)
    haveI :
        IsIso (X.presheaf.stalkPushforward CommRingCat f.base x) :=
      TopCat.Presheaf.stalkPushforward.stalkPushforward_iso_of_isInducing CommRingCat
        hf.isClosedEmbedding.isInducing X.presheaf x
    have hpush :
        Function.Surjective (X.presheaf.stalkPushforward CommRingCat f.base x) :=
      (ConcreteCategory.bijective_of_isIso _).2
    simpa [Scheme.Hom.stalkMap, LocallyRingedSpace.Hom.stalkMap] using hpush.comp hsurj

end Scheme

end AlgebraicGeometry.RingedSpace
